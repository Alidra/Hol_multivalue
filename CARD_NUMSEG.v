Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_NUMSEG_term_abbrevs.
Require Import CARD_CLAUSES_spec.
Require Import CARD_NUMSEG_LEMMA_spec.
Require Import DISJ_ACI_spec.
Require Import INT_POS_spec.
Require Import LEFT_IMP_EXISTS_THM_spec.
Require Import LE_EXISTS_spec.
Require Import NUMSEG_EMPTY_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1032092_spec.
Require Import thm1032098_spec.
Require Import thm1032781_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367770_spec.
Require Import thm1367771_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
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
Require Import thm1982709_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982749_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988293_spec.
Require Import thm1988332_spec.
Require Import thm1988336_spec.
Require Import thm1988342_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
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
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm2318495_spec.
Require Import thm2318496_spec.
Require Import thm2318497_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318574_spec.
Require Import thm2318575_spec.
Require Import thm2318604_spec.
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841401_spec.
Require Import thm2841402_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm2841413_spec.
Require Import thm2841414_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Require Import thm996238_spec.
Lemma lem5382461 (m : nat) : term0 m.
Proof. exact (@lem5382460 m). Qed.
Lemma lem5382462 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem5382463 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem5382462 m) (@lem5382461 m)). Qed.
Lemma lem5382464 (m : nat) (d : nat) : term2 m d.
Proof. exact (@lem5382463 m d). Qed.
Lemma lem5382465 (m : nat) (d : nat) : (term2 m d) = ((term3 m d) = (term4 d)).
Proof. exact (eq_refl (term2 m d)). Qed.
Lemma lem5382467 {A : Type'} (P : A -> Prop) : term5 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem5382468 {A : Type'} (P : A -> Prop) : (term5 A P) = (term6 A P).
Proof. exact (eq_refl (term5 A P)). Qed.
Lemma lem5382469 {A : Type'} (P : A -> Prop) : term6 A P.
Proof. exact (EQ_MP (@lem5382468 A P) (@lem5382467 A P)). Qed.
Lemma lem5382470 {A : Type'} (P : A -> Prop) (Q : Prop) : term7 A P Q.
Proof. exact (@lem5382469 A P Q). Qed.
Lemma lem5382471 {A : Type'} (P : A -> Prop) (Q : Prop) : (term7 A P Q) = ((term8 A P Q) = (term9 A P Q)).
Proof. exact (eq_refl (term7 A P Q)). Qed.
Lemma lem5382473 (m : nat) : term10 m.
Proof. exact (@lem99708 m). Qed.
Lemma lem5382474 (m : nat) : (term10 m) = (term11 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem5382475 (m : nat) : term11 m.
Proof. exact (EQ_MP (@lem5382474 m) (@lem5382473 m)). Qed.
Lemma lem5382476 (m : nat) (n : nat) : term12 m n.
Proof. exact (@lem5382475 m n). Qed.
Lemma lem5382477 (n : nat) (m : nat) : (term12 m n) = ((Peano.le m n) = (term13 n m)).
Proof. exact (eq_refl (term12 m n)). Qed.
Lemma lem5382497 (n : nat) (m : nat) : (term14 n m) = (term15 n m).
Proof. exact (@lem17265 (Peano.lt n m) ((term16 n m) = (NUMERAL 0))). Qed.
Lemma lem5382498 (n : nat) (m : nat) : (term17 n m) = (term18 n m).
Proof. exact (@lem1032781 (term4 n) m (term19 n m)). Qed.
Lemma lem5382499 (n : nat) (m : nat) (d : nat) : (term20 n m d) = (term21 n m d).
Proof. exact (eq_refl (term20 n m d)). Qed.
Lemma lem5382500 (n : nat) (m : nat) (d : nat) : (term22 n m d) = (term22 n m d).
Proof. exact (eq_refl (term22 n m d)). Qed.
Lemma lem5382501 (n : nat) (m : nat) (d : nat) : (term23 n m d) = (term24 n m d).
Proof. exact (MK_COMB (@lem5382500 n m d) (@lem5382499 n m d)). Qed.
Lemma lem5382502 (n : nat) (m : nat) : (term25 n m) = (term26 n m).
Proof. exact (fun_ext (fun d : nat => @lem5382501 n m d)). Qed.
Lemma lem5382503 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5382504 (n : nat) (m : nat) : (term18 n m) = (term27 n m).
Proof. exact (MK_COMB (@lem5382503) (@lem5382502 n m)). Qed.
Lemma lem5382505 (n : nat) (m : nat) : (term17 n m) = (term15 n m).
Proof. exact (eq_refl (term17 n m)). Qed.
Lemma lem5382506 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5382507 (n : nat) (m : nat) : (term28 n m) = (term29 n m).
Proof. exact (MK_COMB (@lem5382506) (@lem5382505 n m)). Qed.
Lemma lem5382508 (n : nat) (m : nat) : ((term17 n m) = (term18 n m)) = ((term15 n m) = (term27 n m)).
Proof. exact (MK_COMB (@lem5382507 n m) (@lem5382504 n m)). Qed.
Lemma lem5382509 (n : nat) (m : nat) : (term15 n m) = (term27 n m).
Proof. exact (EQ_MP (@lem5382508 n m) (@lem5382498 n m)). Qed.
Lemma lem5382510 (n : nat) (m : nat) (d : nat) : (term24 n m d) = (term24 n m d).
Proof. exact (eq_refl (term24 n m d)). Qed.
Lemma lem5382511 (n : nat) (m : nat) : (term26 n m) = (term26 n m).
Proof. exact (fun_ext (fun d : nat => @lem5382510 n m d)). Qed.
Lemma lem5382512 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5382513 (n : nat) (m : nat) : (term27 n m) = (term27 n m).
Proof. exact (MK_COMB (@lem5382512) (@lem5382511 n m)). Qed.
Lemma lem5382514 (n : nat) (m : nat) : (term29 n m) = (term29 n m).
Proof. exact (eq_refl (term29 n m)). Qed.
Lemma lem5382515 (n : nat) (m : nat) : ((term15 n m) = (term27 n m)) = ((term15 n m) = (term27 n m)).
Proof. exact (MK_COMB (@lem5382514 n m) (@lem5382513 n m)). Qed.
Lemma lem5382516 (n : nat) (m : nat) : (term15 n m) = (term27 n m).
Proof. exact (EQ_MP (@lem5382515 n m) (@lem5382509 n m)). Qed.
Lemma lem5382541 (n : nat) (m : nat) : (term14 n m) = (term27 n m).
Proof. exact (TRANS (@lem5382497 n m) (@lem5382516 n m)). Qed.
Lemma lem5382556 (n : nat) (m : nat) (d : nat) : (term21 n m d) = (term21 n m d).
Proof. exact (eq_refl (term21 n m d)). Qed.
Lemma lem5382579 (n : nat) (m : nat) (d : nat) : (term30 n m d) = (term30 n m d).
Proof. exact (eq_refl (term30 n m d)). Qed.
Lemma lem5382586 (d : nat) (m : nat) : (Nat.add m d) = (Nat.add d m).
Proof. exact (@lem1032098 d m). Qed.
Lemma lem5382595 (n : nat) : (term31 n) = (term31 n).
Proof. exact (eq_refl (term31 n)). Qed.
Lemma lem5382596 (n : nat) (d : nat) (m : nat) : ((term4 n) = (Nat.add m d)) = ((term4 n) = (Nat.add d m)).
Proof. exact (MK_COMB (@lem5382595 n) (@lem5382586 d m)). Qed.
Lemma lem5382597 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5382598 (n : nat) (d : nat) (m : nat) : (term32 n m d) = (term32 n d m).
Proof. exact (MK_COMB (@lem5382597) (@lem5382596 n d m)). Qed.
Lemma lem5382599 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5382600 (n : nat) (d : nat) (m : nat) : (term33 n m d) = (term33 n d m).
Proof. exact (MK_COMB (@lem5382599) (@lem5382598 n d m)). Qed.
Lemma lem5382601 (n : nat) (m : nat) (d : nat) : (term34 n m d) = (term35 n m d).
Proof. exact (MK_COMB (@lem5382600 n d m) (@lem5382579 n m d)). Qed.
Lemma lem5382602 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5382603 (n : nat) (m : nat) (d : nat) : (term22 n m d) = (term36 n m d).
Proof. exact (MK_COMB (@lem5382602) (@lem5382601 n m d)). Qed.
Lemma lem5382604 (n : nat) (m : nat) (d : nat) : (term24 n m d) = (term37 n m d).
Proof. exact (MK_COMB (@lem5382603 n m d) (@lem5382556 n m d)). Qed.
Lemma lem5382605 (n : nat) (m : nat) : (term26 n m) = (term38 n m).
Proof. exact (fun_ext (fun d : nat => @lem5382604 n m d)). Qed.
Lemma lem5382606 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5382607 (n : nat) (m : nat) : (term27 n m) = (term39 n m).
Proof. exact (MK_COMB (@lem5382606) (@lem5382605 n m)). Qed.
Lemma lem5382610 (n : nat) (m : nat) : (term14 n m) = (term39 n m).
Proof. exact (TRANS (@lem5382541 n m) (@lem5382607 n m)). Qed.
Lemma lem5382612 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem5382613 (n : nat) (d : nat) (m : nat) : ((term4 n) = (Nat.add d m)) = ((term40 n) = (term41 d m)).
Proof. exact (@lem5382612 (term4 n) (Nat.add d m)). Qed.
Lemma lem5382617 (m : nat) (n : nat) : (term41 m n) = (term42 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5382618 (n : nat) : (term40 n) = (term43 n).
Proof. exact (@lem5382617 n term44). Qed.
Lemma lem5382619 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem5382620 (n : nat) : (term45 n) = (term46 n).
Proof. exact (MK_COMB (@lem5382619) (@lem5382618 n)). Qed.
Lemma lem5382622 (m : nat) (n : nat) : (term41 m n) = (term42 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5382623 (d : nat) (m : nat) : (term41 d m) = (term42 d m).
Proof. exact (@lem5382622 d m). Qed.
Lemma lem5382624 (n : nat) (d : nat) (m : nat) : ((term40 n) = (term41 d m)) = ((term43 n) = (term42 d m)).
Proof. exact (MK_COMB (@lem5382620 n) (@lem5382623 d m)). Qed.
Lemma lem5382625 (n : nat) (d : nat) (m : nat) : ((term4 n) = (Nat.add d m)) = ((term43 n) = (term42 d m)).
Proof. exact (TRANS (@lem5382613 n d m) (@lem5382624 n d m)). Qed.
Lemma lem5382626 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5382627 (n : nat) (d : nat) (m : nat) : (term32 n d m) = (term47 n d m).
Proof. exact (MK_COMB (@lem5382626) (@lem5382625 n d m)). Qed.
Lemma lem5382628 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5382629 (n : nat) (d : nat) (m : nat) : (term33 n d m) = (term48 n d m).
Proof. exact (MK_COMB (@lem5382628) (@lem5382627 n d m)). Qed.
Lemma lem5382631 (m : nat) (n : nat) : (Peano.lt m n) = (term49 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem5382632 (n : nat) (m : nat) : (term50 n m) = (term51 n m).
Proof. exact (@lem5382631 (term4 n) m). Qed.
Lemma lem5382634 (m : nat) (n : nat) : (term41 m n) = (term42 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5382635 (n : nat) : (term40 n) = (term43 n).
Proof. exact (@lem5382634 n term44). Qed.
Lemma lem5382636 : int_lt = int_lt.
Proof. exact (eq_refl int_lt). Qed.
Lemma lem5382637 (n : nat) : (term52 n) = (term53 n).
Proof. exact (MK_COMB (@lem5382636) (@lem5382635 n)). Qed.
Lemma lem5382638 (m : nat) : (int_of_num m) = (int_of_num m).
Proof. exact (eq_refl (int_of_num m)). Qed.
Lemma lem5382639 (n : nat) (m : nat) : (term51 n m) = (term54 n m).
Proof. exact (MK_COMB (@lem5382637 n) (@lem5382638 m)). Qed.
Lemma lem5382640 (n : nat) (m : nat) : (term50 n m) = (term54 n m).
Proof. exact (TRANS (@lem5382632 n m) (@lem5382639 n m)). Qed.
Lemma lem5382641 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5382642 (n : nat) (m : nat) : (term55 n m) = (term56 n m).
Proof. exact (MK_COMB (@lem5382641) (@lem5382640 n m)). Qed.
Lemma lem5382643 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5382644 (n : nat) (m : nat) : (term57 n m) = (term58 n m).
Proof. exact (MK_COMB (@lem5382643) (@lem5382642 n m)). Qed.
Lemma lem5382646 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem5382647 (d : nat) : (d = (NUMERAL 0)) = ((int_of_num d) = term59).
Proof. exact (@lem5382646 d (NUMERAL 0)). Qed.
Lemma lem5382650 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5382651 (d : nat) : (term60 d) = (term61 d).
Proof. exact (MK_COMB (@lem5382650) (@lem5382647 d)). Qed.
Lemma lem5382652 (n : nat) (m : nat) (d : nat) : (term30 n m d) = (term62 n m d).
Proof. exact (MK_COMB (@lem5382644 n m) (@lem5382651 d)). Qed.
Lemma lem5382653 (n : nat) (m : nat) (d : nat) : (term35 n m d) = (term63 n m d).
Proof. exact (MK_COMB (@lem5382629 n d m) (@lem5382652 n m d)). Qed.
Lemma lem5382654 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5382655 (n : nat) (m : nat) (d : nat) : (term36 n m d) = (term64 n m d).
Proof. exact (MK_COMB (@lem5382654) (@lem5382653 n m d)). Qed.
Lemma lem5382657 (m : nat) (n : nat) : (Peano.lt m n) = (term49 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem5382658 (n : nat) (m : nat) : (Peano.lt n m) = (term49 n m).
Proof. exact (@lem5382657 n m). Qed.
Lemma lem5382659 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5382660 (n : nat) (m : nat) : (term65 n m) = (term66 n m).
Proof. exact (MK_COMB (@lem5382659) (@lem5382658 n m)). Qed.
Lemma lem5382661 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5382662 (n : nat) (m : nat) : (term67 n m) = (term68 n m).
Proof. exact (MK_COMB (@lem5382661) (@lem5382660 n m)). Qed.
Lemma lem5382664 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem5382665 (d : nat) : (d = (NUMERAL 0)) = ((int_of_num d) = term59).
Proof. exact (@lem5382664 d (NUMERAL 0)). Qed.
Lemma lem5382668 (n : nat) (m : nat) (d : nat) : (term21 n m d) = (term69 n m d).
Proof. exact (MK_COMB (@lem5382662 n m) (@lem5382665 d)). Qed.
Lemma lem5382669 (n : nat) (m : nat) (d : nat) : (term37 n m d) = (term70 n m d).
Proof. exact (MK_COMB (@lem5382655 n m d) (@lem5382668 n m d)). Qed.
Lemma lem5382670 (n : nat) (m : nat) : (term38 n m) = (term71 n m).
Proof. exact (fun_ext (fun d : nat => @lem5382669 n m d)). Qed.
Lemma lem5382671 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5382672 (n : nat) (m : nat) : (term39 n m) = (term72 n m).
Proof. exact (MK_COMB (@lem5382671) (@lem5382670 n m)). Qed.
Lemma lem5382673 (n : nat) (m : nat) : (term14 n m) = (term72 n m).
Proof. exact (TRANS (@lem5382610 n m) (@lem5382672 n m)). Qed.
Lemma lem5382674 (d : nat) : term73 d.
Proof. exact (@lem2307535 d). Qed.
Lemma lem5382675 (d : nat) : (term73 d) = (term74 d).
Proof. exact (eq_refl (term73 d)). Qed.
Lemma lem5382676 (d : nat) : term74 d.
Proof. exact (EQ_MP (@lem5382675 d) (@lem5382674 d)). Qed.
Lemma lem5382677 (m : nat) : term73 m.
Proof. exact (@lem2307535 m). Qed.
Lemma lem5382678 (m : nat) : (term73 m) = (term74 m).
Proof. exact (eq_refl (term73 m)). Qed.
Lemma lem5382679 (m : nat) : term74 m.
Proof. exact (EQ_MP (@lem5382678 m) (@lem5382677 m)). Qed.
Lemma lem5382680 (n : nat) : term73 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem5382681 (n : nat) : (term73 n) = (term74 n).
Proof. exact (eq_refl (term73 n)). Qed.
Lemma lem5382682 (n : nat) : term74 n.
Proof. exact (EQ_MP (@lem5382681 n) (@lem5382680 n)). Qed.
Lemma lem5382683 (_69795 : int) (_69794 : int) (_69793 : int) : (term75 _69795 _69794 _69793) = (term76 _69795 _69794 _69793).
Proof. exact (@lem2318604 (term76 _69795 _69794 _69793)). Qed.
Lemma lem5382708 (_69795 : int) (_69793 : int) (_69794 : int) : (term77 _69795 _69793 _69794) = ((term78 _69795) = (int_add _69793 _69794)).
Proof. exact (@lem16933 ((term78 _69795) = (int_add _69793 _69794))). Qed.
Lemma lem5382711 (_69795 : int) (_69794 : int) : (term79 _69795 _69794) = (term80 _69795 _69794).
Proof. exact (@lem16933 (term80 _69795 _69794)). Qed.
Lemma lem5382714 (_69793 : int) : (term81 _69793) = (_69793 = term59).
Proof. exact (@lem16933 (_69793 = term59)). Qed.
Lemma lem5382715 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5382716 (_69795 : int) (_69794 : int) : (term82 _69795 _69794) = (term83 _69795 _69794).
Proof. exact (MK_COMB (@lem5382715) (@lem5382711 _69795 _69794)). Qed.
Lemma lem5382717 (_69795 : int) (_69794 : int) (_69793 : int) : (term84 _69795 _69794 _69793) = (term85 _69795 _69794 _69793).
Proof. exact (MK_COMB (@lem5382716 _69795 _69794) (@lem5382714 _69793)). Qed.
Lemma lem5382718 (_69795 : int) (_69794 : int) (_69793 : int) : (term86 _69795 _69794 _69793) = (term84 _69795 _69794 _69793).
Proof. exact (@lem17160 (term87 _69795 _69794) (term88 _69793)). Qed.
Lemma lem5382719 (_69795 : int) (_69794 : int) (_69793 : int) : (term86 _69795 _69794 _69793) = (term85 _69795 _69794 _69793).
Proof. exact (TRANS (@lem5382718 _69795 _69794 _69793) (@lem5382717 _69795 _69794 _69793)). Qed.
Lemma lem5382720 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5382721 (_69795 : int) (_69793 : int) (_69794 : int) : (term89 _69795 _69793 _69794) = (term90 _69795 _69793 _69794).
Proof. exact (MK_COMB (@lem5382720) (@lem5382708 _69795 _69793 _69794)). Qed.
Lemma lem5382722 (_69795 : int) (_69794 : int) (_69793 : int) : (term91 _69795 _69794 _69793) = (term92 _69795 _69794 _69793).
Proof. exact (MK_COMB (@lem5382721 _69795 _69793 _69794) (@lem5382719 _69795 _69794 _69793)). Qed.
Lemma lem5382723 (_69795 : int) (_69794 : int) (_69793 : int) : (term93 _69795 _69794 _69793) = (term91 _69795 _69794 _69793).
Proof. exact (@lem17045 (term94 _69795 _69793 _69794) (term95 _69795 _69794 _69793)). Qed.
Lemma lem5382724 (_69795 : int) (_69794 : int) (_69793 : int) : (term93 _69795 _69794 _69793) = (term92 _69795 _69794 _69793).
Proof. exact (TRANS (@lem5382723 _69795 _69794 _69793) (@lem5382722 _69795 _69794 _69793)). Qed.
Lemma lem5382727 (_69795 : int) (_69794 : int) : (term96 _69795 _69794) = (int_lt _69795 _69794).
Proof. exact (@lem16933 (int_lt _69795 _69794)). Qed.
Lemma lem5382728 (_69793 : int) : (term88 _69793) = (term88 _69793).
Proof. exact (eq_refl (term88 _69793)). Qed.
Lemma lem5382729 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5382730 (_69795 : int) (_69794 : int) : (term97 _69795 _69794) = (term98 _69795 _69794).
Proof. exact (MK_COMB (@lem5382729) (@lem5382727 _69795 _69794)). Qed.
Lemma lem5382731 (_69795 : int) (_69794 : int) (_69793 : int) : (term99 _69795 _69794 _69793) = (term100 _69795 _69794 _69793).
Proof. exact (MK_COMB (@lem5382730 _69795 _69794) (@lem5382728 _69793)). Qed.
Lemma lem5382732 (_69795 : int) (_69794 : int) (_69793 : int) : (term101 _69795 _69794 _69793) = (term99 _69795 _69794 _69793).
Proof. exact (@lem17160 (term102 _69795 _69794) (_69793 = term59)). Qed.
Lemma lem5382733 (_69795 : int) (_69794 : int) (_69793 : int) : (term101 _69795 _69794 _69793) = (term100 _69795 _69794 _69793).
Proof. exact (TRANS (@lem5382732 _69795 _69794 _69793) (@lem5382731 _69795 _69794 _69793)). Qed.
Lemma lem5382734 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5382735 (_69795 : int) (_69794 : int) (_69793 : int) : (term103 _69795 _69794 _69793) = (term104 _69795 _69794 _69793).
Proof. exact (MK_COMB (@lem5382734) (@lem5382724 _69795 _69794 _69793)). Qed.
Lemma lem5382736 (_69795 : int) (_69794 : int) (_69793 : int) : (term105 _69795 _69794 _69793) = (term106 _69795 _69794 _69793).
Proof. exact (MK_COMB (@lem5382735 _69795 _69794 _69793) (@lem5382733 _69795 _69794 _69793)). Qed.
Lemma lem5382737 (_69795 : int) (_69794 : int) (_69793 : int) : (term107 _69795 _69794 _69793) = (term105 _69795 _69794 _69793).
Proof. exact (@lem17160 (term108 _69795 _69794 _69793) (term109 _69795 _69794 _69793)). Qed.
Lemma lem5382738 (_69795 : int) (_69794 : int) (_69793 : int) : (term107 _69795 _69794 _69793) = (term106 _69795 _69794 _69793).
Proof. exact (TRANS (@lem5382737 _69795 _69794 _69793) (@lem5382736 _69795 _69794 _69793)). Qed.
Lemma lem5382740 (_69795 : int) : (term110 _69795) = (term110 _69795).
Proof. exact (eq_refl (term110 _69795)). Qed.
Lemma lem5382741 (_69795 : int) (_69794 : int) (_69793 : int) : (term111 _69795 _69794 _69793) = (term112 _69795 _69794 _69793).
Proof. exact (MK_COMB (@lem5382740 _69795) (@lem5382738 _69795 _69794 _69793)). Qed.
Lemma lem5382742 (_69795 : int) (_69794 : int) (_69793 : int) : (term113 _69795 _69794 _69793) = (term111 _69795 _69794 _69793).
Proof. exact (@lem17362 (term114 _69795) (term115 _69795 _69794 _69793)). Qed.
Lemma lem5382743 (_69795 : int) (_69794 : int) (_69793 : int) : (term113 _69795 _69794 _69793) = (term112 _69795 _69794 _69793).
Proof. exact (TRANS (@lem5382742 _69795 _69794 _69793) (@lem5382741 _69795 _69794 _69793)). Qed.
Lemma lem5382745 (_69794 : int) : (term110 _69794) = (term110 _69794).
Proof. exact (eq_refl (term110 _69794)). Qed.
Lemma lem5382746 (_69795 : int) (_69794 : int) (_69793 : int) : (term116 _69795 _69794 _69793) = (term117 _69795 _69794 _69793).
Proof. exact (MK_COMB (@lem5382745 _69794) (@lem5382743 _69795 _69794 _69793)). Qed.
Lemma lem5382747 (_69795 : int) (_69794 : int) (_69793 : int) : (term118 _69795 _69794 _69793) = (term116 _69795 _69794 _69793).
Proof. exact (@lem17362 (term114 _69794) (term119 _69795 _69794 _69793)). Qed.
Lemma lem5382748 (_69795 : int) (_69794 : int) (_69793 : int) : (term118 _69795 _69794 _69793) = (term117 _69795 _69794 _69793).
Proof. exact (TRANS (@lem5382747 _69795 _69794 _69793) (@lem5382746 _69795 _69794 _69793)). Qed.
Lemma lem5382750 (_69793 : int) : (term110 _69793) = (term110 _69793).
Proof. exact (eq_refl (term110 _69793)). Qed.
Lemma lem5382751 (_69795 : int) (_69794 : int) (_69793 : int) : (term120 _69795 _69794 _69793) = (term121 _69795 _69794 _69793).
Proof. exact (MK_COMB (@lem5382750 _69793) (@lem5382748 _69795 _69794 _69793)). Qed.
Lemma lem5382752 (_69795 : int) (_69794 : int) (_69793 : int) : (term122 _69795 _69794 _69793) = (term120 _69795 _69794 _69793).
Proof. exact (@lem17362 (term114 _69793) (term123 _69795 _69794 _69793)). Qed.
Lemma lem5382786 (_69795 : int) (_69794 : int) (_69793 : int) : (term122 _69795 _69794 _69793) = (term121 _69795 _69794 _69793).
Proof. exact (TRANS (@lem5382752 _69795 _69794 _69793) (@lem5382751 _69795 _69794 _69793)). Qed.
Lemma lem5382789 (x : int) (y : int) : (int_le x y) = (term124 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5382790 (_69793 : int) : (term114 _69793) = (term125 _69793).
Proof. exact (@lem5382789 term59 _69793). Qed.
Lemma lem5382792 (n : nat) : (term126 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5382793 : term127 = term128.
Proof. exact (@lem5382792 (NUMERAL 0)). Qed.
Lemma lem5382794 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5382795 : term129 = term130.
Proof. exact (MK_COMB (@lem5382794) (@lem5382793)). Qed.
Lemma lem5382796 (_69793 : int) : (real_of_int _69793) = (real_of_int _69793).
Proof. exact (eq_refl (real_of_int _69793)). Qed.
Lemma lem5382797 (_69793 : int) : (term125 _69793) = (term131 _69793).
Proof. exact (MK_COMB (@lem5382795) (@lem5382796 _69793)). Qed.
Lemma lem5382799 (_69793 : int) : (term114 _69793) = (term131 _69793).
Proof. exact (TRANS (@lem5382790 _69793) (@lem5382797 _69793)). Qed.
Lemma lem5382802 (x : int) (y : int) : (int_le x y) = (term124 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5382803 (_69794 : int) : (term114 _69794) = (term125 _69794).
Proof. exact (@lem5382802 term59 _69794). Qed.
Lemma lem5382805 (n : nat) : (term126 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5382806 : term127 = term128.
Proof. exact (@lem5382805 (NUMERAL 0)). Qed.
Lemma lem5382807 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5382808 : term129 = term130.
Proof. exact (MK_COMB (@lem5382807) (@lem5382806)). Qed.
Lemma lem5382809 (_69794 : int) : (real_of_int _69794) = (real_of_int _69794).
Proof. exact (eq_refl (real_of_int _69794)). Qed.
Lemma lem5382810 (_69794 : int) : (term125 _69794) = (term131 _69794).
Proof. exact (MK_COMB (@lem5382808) (@lem5382809 _69794)). Qed.
Lemma lem5382812 (_69794 : int) : (term114 _69794) = (term131 _69794).
Proof. exact (TRANS (@lem5382803 _69794) (@lem5382810 _69794)). Qed.
Lemma lem5382815 (x : int) (y : int) : (int_le x y) = (term124 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5382816 (_69795 : int) : (term114 _69795) = (term125 _69795).
Proof. exact (@lem5382815 term59 _69795). Qed.
Lemma lem5382818 (n : nat) : (term126 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5382819 : term127 = term128.
Proof. exact (@lem5382818 (NUMERAL 0)). Qed.
Lemma lem5382820 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5382821 : term129 = term130.
Proof. exact (MK_COMB (@lem5382820) (@lem5382819)). Qed.
Lemma lem5382822 (_69795 : int) : (real_of_int _69795) = (real_of_int _69795).
Proof. exact (eq_refl (real_of_int _69795)). Qed.
Lemma lem5382823 (_69795 : int) : (term125 _69795) = (term131 _69795).
Proof. exact (MK_COMB (@lem5382821) (@lem5382822 _69795)). Qed.
Lemma lem5382825 (_69795 : int) : (term114 _69795) = (term131 _69795).
Proof. exact (TRANS (@lem5382816 _69795) (@lem5382823 _69795)). Qed.
Lemma lem5382828 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem5382829 (_69795 : int) (_69793 : int) (_69794 : int) : ((term78 _69795) = (int_add _69793 _69794)) = ((term132 _69795) = (term133 _69793 _69794)).
Proof. exact (@lem5382828 (term78 _69795) (int_add _69793 _69794)). Qed.
Lemma lem5382833 (x : int) (y : int) : (term133 x y) = (term134 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5382834 (_69795 : int) : (term132 _69795) = (term135 _69795).
Proof. exact (@lem5382833 _69795 term136). Qed.
Lemma lem5382836 (n : nat) : (term126 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5382837 : term137 = term138.
Proof. exact (@lem5382836 term44). Qed.
Lemma lem5382838 (_69795 : int) : (term139 _69795) = (term139 _69795).
Proof. exact (eq_refl (term139 _69795)). Qed.
Lemma lem5382839 (_69795 : int) : (term135 _69795) = (term140 _69795).
Proof. exact (MK_COMB (@lem5382838 _69795) (@lem5382837)). Qed.
Lemma lem5382840 (_69795 : int) : (term132 _69795) = (term140 _69795).
Proof. exact (TRANS (@lem5382834 _69795) (@lem5382839 _69795)). Qed.
Lemma lem5382841 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5382842 (_69795 : int) : (term141 _69795) = (term142 _69795).
Proof. exact (MK_COMB (@lem5382841) (@lem5382840 _69795)). Qed.
Lemma lem5382844 (x : int) (y : int) : (term133 x y) = (term134 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5382845 (_69793 : int) (_69794 : int) : (term133 _69793 _69794) = (term134 _69793 _69794).
Proof. exact (@lem5382844 _69793 _69794). Qed.
Lemma lem5382846 (_69795 : int) (_69793 : int) (_69794 : int) : ((term132 _69795) = (term133 _69793 _69794)) = ((term140 _69795) = (term134 _69793 _69794)).
Proof. exact (MK_COMB (@lem5382842 _69795) (@lem5382845 _69793 _69794)). Qed.
Lemma lem5382848 (_69795 : int) (_69793 : int) (_69794 : int) : ((term78 _69795) = (int_add _69793 _69794)) = ((term140 _69795) = (term134 _69793 _69794)).
Proof. exact (TRANS (@lem5382829 _69795 _69793 _69794) (@lem5382846 _69795 _69793 _69794)). Qed.
Lemma lem5382850 (x : int) (y : int) : (int_lt x y) = (term143 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem5382851 (_69795 : int) (_69794 : int) : (term80 _69795 _69794) = (term144 _69795 _69794).
Proof. exact (@lem5382850 (term78 _69795) _69794). Qed.
Lemma lem5382853 (x : int) (y : int) : (int_le x y) = (term124 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5382854 (_69795 : int) (_69794 : int) : (term144 _69795 _69794) = (term145 _69795 _69794).
Proof. exact (@lem5382853 (term146 _69795) _69794). Qed.
Lemma lem5382856 (x : int) (y : int) : (term133 x y) = (term134 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5382857 (_69795 : int) : (term147 _69795) = (term148 _69795).
Proof. exact (@lem5382856 (term78 _69795) term136). Qed.
Lemma lem5382859 (x : int) (y : int) : (term133 x y) = (term134 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5382860 (_69795 : int) : (term132 _69795) = (term135 _69795).
Proof. exact (@lem5382859 _69795 term136). Qed.
Lemma lem5382862 (n : nat) : (term126 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5382863 : term137 = term138.
Proof. exact (@lem5382862 term44). Qed.
Lemma lem5382864 (_69795 : int) : (term139 _69795) = (term139 _69795).
Proof. exact (eq_refl (term139 _69795)). Qed.
Lemma lem5382865 (_69795 : int) : (term135 _69795) = (term140 _69795).
Proof. exact (MK_COMB (@lem5382864 _69795) (@lem5382863)). Qed.
Lemma lem5382866 (_69795 : int) : (term132 _69795) = (term140 _69795).
Proof. exact (TRANS (@lem5382860 _69795) (@lem5382865 _69795)). Qed.
Lemma lem5382867 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5382868 (_69795 : int) : (term149 _69795) = (term150 _69795).
Proof. exact (MK_COMB (@lem5382867) (@lem5382866 _69795)). Qed.
Lemma lem5382870 (n : nat) : (term126 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5382871 : term137 = term138.
Proof. exact (@lem5382870 term44). Qed.
Lemma lem5382872 (_69795 : int) : (term148 _69795) = (term151 _69795).
Proof. exact (MK_COMB (@lem5382868 _69795) (@lem5382871)). Qed.
Lemma lem5382873 (_69795 : int) : (term147 _69795) = (term151 _69795).
Proof. exact (TRANS (@lem5382857 _69795) (@lem5382872 _69795)). Qed.
Lemma lem5382874 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5382875 (_69795 : int) : (term152 _69795) = (term153 _69795).
Proof. exact (MK_COMB (@lem5382874) (@lem5382873 _69795)). Qed.
Lemma lem5382876 (_69794 : int) : (real_of_int _69794) = (real_of_int _69794).
Proof. exact (eq_refl (real_of_int _69794)). Qed.
Lemma lem5382877 (_69795 : int) (_69794 : int) : (term145 _69795 _69794) = (term154 _69795 _69794).
Proof. exact (MK_COMB (@lem5382875 _69795) (@lem5382876 _69794)). Qed.
Lemma lem5382878 (_69795 : int) (_69794 : int) : (term144 _69795 _69794) = (term154 _69795 _69794).
Proof. exact (TRANS (@lem5382854 _69795 _69794) (@lem5382877 _69795 _69794)). Qed.
Lemma lem5382879 (_69795 : int) (_69794 : int) : (term80 _69795 _69794) = (term154 _69795 _69794).
Proof. exact (TRANS (@lem5382851 _69795 _69794) (@lem5382878 _69795 _69794)). Qed.
Lemma lem5382882 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem5382883 (_69793 : int) : (_69793 = term59) = ((real_of_int _69793) = term127).
Proof. exact (@lem5382882 _69793 term59). Qed.
Lemma lem5382887 (n : nat) : (term126 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5382888 : term127 = term128.
Proof. exact (@lem5382887 (NUMERAL 0)). Qed.
Lemma lem5382889 (_69793 : int) : (term155 _69793) = (term155 _69793).
Proof. exact (eq_refl (term155 _69793)). Qed.
Lemma lem5382890 (_69793 : int) : ((real_of_int _69793) = term127) = ((real_of_int _69793) = term128).
Proof. exact (MK_COMB (@lem5382889 _69793) (@lem5382888)). Qed.
Lemma lem5382892 (_69793 : int) : (_69793 = term59) = ((real_of_int _69793) = term128).
Proof. exact (TRANS (@lem5382883 _69793) (@lem5382890 _69793)). Qed.
Lemma lem5382893 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5382894 (_69795 : int) (_69794 : int) : (term83 _69795 _69794) = (term156 _69795 _69794).
Proof. exact (MK_COMB (@lem5382893) (@lem5382879 _69795 _69794)). Qed.
Lemma lem5382895 (_69795 : int) (_69794 : int) (_69793 : int) : (term85 _69795 _69794 _69793) = (term157 _69795 _69794 _69793).
Proof. exact (MK_COMB (@lem5382894 _69795 _69794) (@lem5382892 _69793)). Qed.
Lemma lem5382896 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5382897 (_69795 : int) (_69793 : int) (_69794 : int) : (term90 _69795 _69793 _69794) = (term158 _69795 _69793 _69794).
Proof. exact (MK_COMB (@lem5382896) (@lem5382848 _69795 _69793 _69794)). Qed.
Lemma lem5382898 (_69795 : int) (_69794 : int) (_69793 : int) : (term92 _69795 _69794 _69793) = (term159 _69795 _69794 _69793).
Proof. exact (MK_COMB (@lem5382897 _69795 _69793 _69794) (@lem5382895 _69795 _69794 _69793)). Qed.
Lemma lem5382900 (x : int) (y : int) : (int_lt x y) = (term143 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem5382901 (_69795 : int) (_69794 : int) : (int_lt _69795 _69794) = (term143 _69795 _69794).
Proof. exact (@lem5382900 _69795 _69794). Qed.
Lemma lem5382903 (x : int) (y : int) : (int_le x y) = (term124 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5382904 (_69795 : int) (_69794 : int) : (term143 _69795 _69794) = (term160 _69795 _69794).
Proof. exact (@lem5382903 (term78 _69795) _69794). Qed.
Lemma lem5382906 (x : int) (y : int) : (term133 x y) = (term134 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5382907 (_69795 : int) : (term132 _69795) = (term135 _69795).
Proof. exact (@lem5382906 _69795 term136). Qed.
Lemma lem5382909 (n : nat) : (term126 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5382910 : term137 = term138.
Proof. exact (@lem5382909 term44). Qed.
Lemma lem5382911 (_69795 : int) : (term139 _69795) = (term139 _69795).
Proof. exact (eq_refl (term139 _69795)). Qed.
Lemma lem5382912 (_69795 : int) : (term135 _69795) = (term140 _69795).
Proof. exact (MK_COMB (@lem5382911 _69795) (@lem5382910)). Qed.
Lemma lem5382913 (_69795 : int) : (term132 _69795) = (term140 _69795).
Proof. exact (TRANS (@lem5382907 _69795) (@lem5382912 _69795)). Qed.
Lemma lem5382914 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5382915 (_69795 : int) : (term161 _69795) = (term162 _69795).
Proof. exact (MK_COMB (@lem5382914) (@lem5382913 _69795)). Qed.
Lemma lem5382916 (_69794 : int) : (real_of_int _69794) = (real_of_int _69794).
Proof. exact (eq_refl (real_of_int _69794)). Qed.
Lemma lem5382917 (_69795 : int) (_69794 : int) : (term160 _69795 _69794) = (term163 _69795 _69794).
Proof. exact (MK_COMB (@lem5382915 _69795) (@lem5382916 _69794)). Qed.
Lemma lem5382918 (_69795 : int) (_69794 : int) : (term143 _69795 _69794) = (term163 _69795 _69794).
Proof. exact (TRANS (@lem5382904 _69795 _69794) (@lem5382917 _69795 _69794)). Qed.
Lemma lem5382919 (_69795 : int) (_69794 : int) : (int_lt _69795 _69794) = (term163 _69795 _69794).
Proof. exact (TRANS (@lem5382901 _69795 _69794) (@lem5382918 _69795 _69794)). Qed.
Lemma lem5382921 (y : int) (x : int) : (term164 x y) = (term165 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem5382922 (_69793 : int) : (term88 _69793) = (term166 _69793).
Proof. exact (@lem5382921 term59 _69793). Qed.
Lemma lem5382924 (x : int) (y : int) : (int_le x y) = (term124 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5382925 (_69793 : int) : (term167 _69793) = (term168 _69793).
Proof. exact (@lem5382924 (term78 _69793) term59). Qed.
Lemma lem5382927 (x : int) (y : int) : (term133 x y) = (term134 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5382928 (_69793 : int) : (term132 _69793) = (term135 _69793).
Proof. exact (@lem5382927 _69793 term136). Qed.
Lemma lem5382930 (n : nat) : (term126 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5382931 : term137 = term138.
Proof. exact (@lem5382930 term44). Qed.
Lemma lem5382932 (_69793 : int) : (term139 _69793) = (term139 _69793).
Proof. exact (eq_refl (term139 _69793)). Qed.
Lemma lem5382933 (_69793 : int) : (term135 _69793) = (term140 _69793).
Proof. exact (MK_COMB (@lem5382932 _69793) (@lem5382931)). Qed.
Lemma lem5382934 (_69793 : int) : (term132 _69793) = (term140 _69793).
Proof. exact (TRANS (@lem5382928 _69793) (@lem5382933 _69793)). Qed.
Lemma lem5382935 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5382936 (_69793 : int) : (term161 _69793) = (term162 _69793).
Proof. exact (MK_COMB (@lem5382935) (@lem5382934 _69793)). Qed.
Lemma lem5382938 (n : nat) : (term126 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5382939 : term127 = term128.
Proof. exact (@lem5382938 (NUMERAL 0)). Qed.
Lemma lem5382940 (_69793 : int) : (term168 _69793) = (term169 _69793).
Proof. exact (MK_COMB (@lem5382936 _69793) (@lem5382939)). Qed.
Lemma lem5382941 (_69793 : int) : (term167 _69793) = (term169 _69793).
Proof. exact (TRANS (@lem5382925 _69793) (@lem5382940 _69793)). Qed.
Lemma lem5382942 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5382943 (_69793 : int) : (term170 _69793) = (term171 _69793).
Proof. exact (MK_COMB (@lem5382942) (@lem5382941 _69793)). Qed.
Lemma lem5382945 (x : int) (y : int) : (int_le x y) = (term124 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5382946 (_69793 : int) : (term172 _69793) = (term173 _69793).
Proof. exact (@lem5382945 term174 _69793). Qed.
Lemma lem5382948 (x : int) (y : int) : (term133 x y) = (term134 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5382949 : term175 = term176.
Proof. exact (@lem5382948 term59 term136). Qed.
Lemma lem5382951 (n : nat) : (term126 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5382952 : term127 = term128.
Proof. exact (@lem5382951 (NUMERAL 0)). Qed.
Lemma lem5382953 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5382954 : term177 = term178.
Proof. exact (MK_COMB (@lem5382953) (@lem5382952)). Qed.
Lemma lem5382956 (n : nat) : (term126 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5382957 : term137 = term138.
Proof. exact (@lem5382956 term44). Qed.
Lemma lem5382958 : term176 = term179.
Proof. exact (MK_COMB (@lem5382954) (@lem5382957)). Qed.
Lemma lem5382959 : term175 = term179.
Proof. exact (TRANS (@lem5382949) (@lem5382958)). Qed.
Lemma lem5382960 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5382961 : term180 = term181.
Proof. exact (MK_COMB (@lem5382960) (@lem5382959)). Qed.
Lemma lem5382962 (_69793 : int) : (real_of_int _69793) = (real_of_int _69793).
Proof. exact (eq_refl (real_of_int _69793)). Qed.
Lemma lem5382963 (_69793 : int) : (term173 _69793) = (term182 _69793).
Proof. exact (MK_COMB (@lem5382961) (@lem5382962 _69793)). Qed.
Lemma lem5382964 (_69793 : int) : (term172 _69793) = (term182 _69793).
Proof. exact (TRANS (@lem5382946 _69793) (@lem5382963 _69793)). Qed.
Lemma lem5382965 (_69793 : int) : (term166 _69793) = (term183 _69793).
Proof. exact (MK_COMB (@lem5382943 _69793) (@lem5382964 _69793)). Qed.
Lemma lem5382966 (_69793 : int) : (term88 _69793) = (term183 _69793).
Proof. exact (TRANS (@lem5382922 _69793) (@lem5382965 _69793)). Qed.
Lemma lem5382967 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5382968 (_69795 : int) (_69794 : int) : (term98 _69795 _69794) = (term184 _69795 _69794).
Proof. exact (MK_COMB (@lem5382967) (@lem5382919 _69795 _69794)). Qed.
Lemma lem5382969 (_69795 : int) (_69794 : int) (_69793 : int) : (term100 _69795 _69794 _69793) = (term185 _69795 _69794 _69793).
Proof. exact (MK_COMB (@lem5382968 _69795 _69794) (@lem5382966 _69793)). Qed.
Lemma lem5382970 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5382971 (_69795 : int) (_69794 : int) (_69793 : int) : (term104 _69795 _69794 _69793) = (term186 _69795 _69794 _69793).
Proof. exact (MK_COMB (@lem5382970) (@lem5382898 _69795 _69794 _69793)). Qed.
Lemma lem5382972 (_69795 : int) (_69794 : int) (_69793 : int) : (term106 _69795 _69794 _69793) = (term187 _69795 _69794 _69793).
Proof. exact (MK_COMB (@lem5382971 _69795 _69794 _69793) (@lem5382969 _69795 _69794 _69793)). Qed.
Lemma lem5382973 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5382974 (_69795 : int) : (term110 _69795) = (term188 _69795).
Proof. exact (MK_COMB (@lem5382973) (@lem5382825 _69795)). Qed.
Lemma lem5382975 (_69795 : int) (_69794 : int) (_69793 : int) : (term112 _69795 _69794 _69793) = (term189 _69795 _69794 _69793).
Proof. exact (MK_COMB (@lem5382974 _69795) (@lem5382972 _69795 _69794 _69793)). Qed.
Lemma lem5382976 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5382977 (_69794 : int) : (term110 _69794) = (term188 _69794).
Proof. exact (MK_COMB (@lem5382976) (@lem5382812 _69794)). Qed.
Lemma lem5382978 (_69795 : int) (_69794 : int) (_69793 : int) : (term117 _69795 _69794 _69793) = (term190 _69795 _69794 _69793).
Proof. exact (MK_COMB (@lem5382977 _69794) (@lem5382975 _69795 _69794 _69793)). Qed.
Lemma lem5382979 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5382980 (_69793 : int) : (term110 _69793) = (term188 _69793).
Proof. exact (MK_COMB (@lem5382979) (@lem5382799 _69793)). Qed.
Lemma lem5382981 (_69795 : int) (_69794 : int) (_69793 : int) : (term121 _69795 _69794 _69793) = (term191 _69795 _69794 _69793).
Proof. exact (MK_COMB (@lem5382980 _69793) (@lem5382978 _69795 _69794 _69793)). Qed.
Lemma lem5382982 (_69795 : int) (_69794 : int) (_69793 : int) : (term122 _69795 _69794 _69793) = (term191 _69795 _69794 _69793).
Proof. exact (TRANS (@lem5382786 _69795 _69794 _69793) (@lem5382981 _69795 _69794 _69793)). Qed.
Lemma lem5382986 (t : Prop) : (term192 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5383072 (_69795 : int) (_69794 : int) (_69793 : int) : (term193 _69795 _69794 _69793) = (term191 _69795 _69794 _69793).
Proof. exact (@lem5382986 (term191 _69795 _69794 _69793)). Qed.
Lemma lem5383073 (_69793 : int) : (term131 _69793) = (term194 _69793).
Proof. exact (@lem1988287 (real_of_int _69793) term128). Qed.
Lemma lem5383079 (_69793 : int) : (term195 _69793) = (term196 _69793).
Proof. exact (@lem1982792 (real_of_int _69793) term128). Qed.
Lemma lem5383081 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5383082 : term128 = term198.
Proof. exact (@lem5383081 (NUMERAL 0)). Qed.
Lemma lem5383084 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5383085 : term201 = term202.
Proof. exact (@lem5383084 term44). Qed.
Lemma lem5383086 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5383087 : term203 = term204.
Proof. exact (MK_COMB (@lem5383086) (@lem5383085)). Qed.
Lemma lem5383088 : term205 = term206.
Proof. exact (MK_COMB (@lem5383087) (@lem5383082)). Qed.
Lemma lem5383089 : term206 = term207.
Proof. exact (@lem1981613 term201 term128 term138 term138). Qed.
Lemma lem5383091 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5383092 : term210 = term211.
Proof. exact (@lem5383091 term44 term44). Qed.
Lemma lem5383093 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5383094 : term213 = term44.
Proof. exact (EQ_MP (@lem5383093) (@lem940073)). Qed.
Lemma lem5383095 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5383096 : term211 = term138.
Proof. exact (MK_COMB (@lem5383095) (@lem5383094)). Qed.
Lemma lem5383097 : term210 = term138.
Proof. exact (TRANS (@lem5383092) (@lem5383096)). Qed.
Lemma lem5383099 (x : nat) : (term214 x) = term128.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5383100 : term205 = term128.
Proof. exact (@lem5383099 term44). Qed.
Lemma lem5383101 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5383102 : term215 = term216.
Proof. exact (MK_COMB (@lem5383101) (@lem5383100)). Qed.
Lemma lem5383103 : term207 = term198.
Proof. exact (MK_COMB (@lem5383102) (@lem5383097)). Qed.
Lemma lem5383104 : term206 = term198.
Proof. exact (TRANS (@lem5383089) (@lem5383103)). Qed.
Lemma lem5383105 : term205 = term198.
Proof. exact (TRANS (@lem5383088) (@lem5383104)). Qed.
Lemma lem5383107 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5383108 : term198 = term128.
Proof. exact (@lem5383107 term128). Qed.
Lemma lem5383109 : term205 = term128.
Proof. exact (TRANS (@lem5383105) (@lem5383108)). Qed.
Lemma lem5383110 (_69793 : int) : (term139 _69793) = (term139 _69793).
Proof. exact (eq_refl (term139 _69793)). Qed.
Lemma lem5383111 (_69793 : int) : (term196 _69793) = (term218 _69793).
Proof. exact (MK_COMB (@lem5383110 _69793) (@lem5383109)). Qed.
Lemma lem5383112 (_69793 : int) : (term218 _69793) = (real_of_int _69793).
Proof. exact (@lem1982723 (real_of_int _69793)). Qed.
Lemma lem5383113 (_69793 : int) : (term196 _69793) = (real_of_int _69793).
Proof. exact (TRANS (@lem5383111 _69793) (@lem5383112 _69793)). Qed.
Lemma lem5383115 (_69793 : int) : (term195 _69793) = (real_of_int _69793).
Proof. exact (TRANS (@lem5383079 _69793) (@lem5383113 _69793)). Qed.
Lemma lem5383116 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5383117 (_69793 : int) : (term219 _69793) = (term220 _69793).
Proof. exact (MK_COMB (@lem5383116) (@lem5383115 _69793)). Qed.
Lemma lem5383118 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5383119 (_69793 : int) : (term194 _69793) = (term221 _69793).
Proof. exact (MK_COMB (@lem5383117 _69793) (@lem5383118)). Qed.
Lemma lem5383120 (_69793 : int) : (term131 _69793) = (term221 _69793).
Proof. exact (TRANS (@lem5383073 _69793) (@lem5383119 _69793)). Qed.
Lemma lem5383121 (_69794 : int) : (term131 _69794) = (term194 _69794).
Proof. exact (@lem1988287 (real_of_int _69794) term128). Qed.
Lemma lem5383127 (_69794 : int) : (term195 _69794) = (term196 _69794).
Proof. exact (@lem1982792 (real_of_int _69794) term128). Qed.
Lemma lem5383129 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5383130 : term128 = term198.
Proof. exact (@lem5383129 (NUMERAL 0)). Qed.
Lemma lem5383132 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5383133 : term201 = term202.
Proof. exact (@lem5383132 term44). Qed.
Lemma lem5383134 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5383135 : term203 = term204.
Proof. exact (MK_COMB (@lem5383134) (@lem5383133)). Qed.
Lemma lem5383136 : term205 = term206.
Proof. exact (MK_COMB (@lem5383135) (@lem5383130)). Qed.
Lemma lem5383137 : term206 = term207.
Proof. exact (@lem1981613 term201 term128 term138 term138). Qed.
Lemma lem5383139 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5383140 : term210 = term211.
Proof. exact (@lem5383139 term44 term44). Qed.
Lemma lem5383141 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5383142 : term213 = term44.
Proof. exact (EQ_MP (@lem5383141) (@lem940073)). Qed.
Lemma lem5383143 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5383144 : term211 = term138.
Proof. exact (MK_COMB (@lem5383143) (@lem5383142)). Qed.
Lemma lem5383145 : term210 = term138.
Proof. exact (TRANS (@lem5383140) (@lem5383144)). Qed.
Lemma lem5383147 (x : nat) : (term214 x) = term128.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5383148 : term205 = term128.
Proof. exact (@lem5383147 term44). Qed.
Lemma lem5383149 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5383150 : term215 = term216.
Proof. exact (MK_COMB (@lem5383149) (@lem5383148)). Qed.
Lemma lem5383151 : term207 = term198.
Proof. exact (MK_COMB (@lem5383150) (@lem5383145)). Qed.
Lemma lem5383152 : term206 = term198.
Proof. exact (TRANS (@lem5383137) (@lem5383151)). Qed.
Lemma lem5383153 : term205 = term198.
Proof. exact (TRANS (@lem5383136) (@lem5383152)). Qed.
Lemma lem5383155 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5383156 : term198 = term128.
Proof. exact (@lem5383155 term128). Qed.
Lemma lem5383157 : term205 = term128.
Proof. exact (TRANS (@lem5383153) (@lem5383156)). Qed.
Lemma lem5383158 (_69794 : int) : (term139 _69794) = (term139 _69794).
Proof. exact (eq_refl (term139 _69794)). Qed.
Lemma lem5383159 (_69794 : int) : (term196 _69794) = (term218 _69794).
Proof. exact (MK_COMB (@lem5383158 _69794) (@lem5383157)). Qed.
Lemma lem5383160 (_69794 : int) : (term218 _69794) = (real_of_int _69794).
Proof. exact (@lem1982723 (real_of_int _69794)). Qed.
Lemma lem5383161 (_69794 : int) : (term196 _69794) = (real_of_int _69794).
Proof. exact (TRANS (@lem5383159 _69794) (@lem5383160 _69794)). Qed.
Lemma lem5383163 (_69794 : int) : (term195 _69794) = (real_of_int _69794).
Proof. exact (TRANS (@lem5383127 _69794) (@lem5383161 _69794)). Qed.
Lemma lem5383164 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5383165 (_69794 : int) : (term219 _69794) = (term220 _69794).
Proof. exact (MK_COMB (@lem5383164) (@lem5383163 _69794)). Qed.
Lemma lem5383166 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5383167 (_69794 : int) : (term194 _69794) = (term221 _69794).
Proof. exact (MK_COMB (@lem5383165 _69794) (@lem5383166)). Qed.
Lemma lem5383168 (_69794 : int) : (term131 _69794) = (term221 _69794).
Proof. exact (TRANS (@lem5383121 _69794) (@lem5383167 _69794)). Qed.
Lemma lem5383169 (_69795 : int) : (term131 _69795) = (term194 _69795).
Proof. exact (@lem1988287 (real_of_int _69795) term128). Qed.
Lemma lem5383175 (_69795 : int) : (term195 _69795) = (term196 _69795).
Proof. exact (@lem1982792 (real_of_int _69795) term128). Qed.
Lemma lem5383177 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5383178 : term128 = term198.
Proof. exact (@lem5383177 (NUMERAL 0)). Qed.
Lemma lem5383180 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5383181 : term201 = term202.
Proof. exact (@lem5383180 term44). Qed.
Lemma lem5383182 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5383183 : term203 = term204.
Proof. exact (MK_COMB (@lem5383182) (@lem5383181)). Qed.
Lemma lem5383184 : term205 = term206.
Proof. exact (MK_COMB (@lem5383183) (@lem5383178)). Qed.
Lemma lem5383185 : term206 = term207.
Proof. exact (@lem1981613 term201 term128 term138 term138). Qed.
Lemma lem5383187 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5383188 : term210 = term211.
Proof. exact (@lem5383187 term44 term44). Qed.
Lemma lem5383189 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5383190 : term213 = term44.
Proof. exact (EQ_MP (@lem5383189) (@lem940073)). Qed.
Lemma lem5383191 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5383192 : term211 = term138.
Proof. exact (MK_COMB (@lem5383191) (@lem5383190)). Qed.
Lemma lem5383193 : term210 = term138.
Proof. exact (TRANS (@lem5383188) (@lem5383192)). Qed.
Lemma lem5383195 (x : nat) : (term214 x) = term128.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5383196 : term205 = term128.
Proof. exact (@lem5383195 term44). Qed.
Lemma lem5383197 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5383198 : term215 = term216.
Proof. exact (MK_COMB (@lem5383197) (@lem5383196)). Qed.
Lemma lem5383199 : term207 = term198.
Proof. exact (MK_COMB (@lem5383198) (@lem5383193)). Qed.
Lemma lem5383200 : term206 = term198.
Proof. exact (TRANS (@lem5383185) (@lem5383199)). Qed.
Lemma lem5383201 : term205 = term198.
Proof. exact (TRANS (@lem5383184) (@lem5383200)). Qed.
Lemma lem5383203 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5383204 : term198 = term128.
Proof. exact (@lem5383203 term128). Qed.
Lemma lem5383205 : term205 = term128.
Proof. exact (TRANS (@lem5383201) (@lem5383204)). Qed.
Lemma lem5383206 (_69795 : int) : (term139 _69795) = (term139 _69795).
Proof. exact (eq_refl (term139 _69795)). Qed.
Lemma lem5383207 (_69795 : int) : (term196 _69795) = (term218 _69795).
Proof. exact (MK_COMB (@lem5383206 _69795) (@lem5383205)). Qed.
Lemma lem5383208 (_69795 : int) : (term218 _69795) = (real_of_int _69795).
Proof. exact (@lem1982723 (real_of_int _69795)). Qed.
Lemma lem5383209 (_69795 : int) : (term196 _69795) = (real_of_int _69795).
Proof. exact (TRANS (@lem5383207 _69795) (@lem5383208 _69795)). Qed.
Lemma lem5383211 (_69795 : int) : (term195 _69795) = (real_of_int _69795).
Proof. exact (TRANS (@lem5383175 _69795) (@lem5383209 _69795)). Qed.
Lemma lem5383212 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5383213 (_69795 : int) : (term219 _69795) = (term220 _69795).
Proof. exact (MK_COMB (@lem5383212) (@lem5383211 _69795)). Qed.
Lemma lem5383214 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5383215 (_69795 : int) : (term194 _69795) = (term221 _69795).
Proof. exact (MK_COMB (@lem5383213 _69795) (@lem5383214)). Qed.
Lemma lem5383216 (_69795 : int) : (term131 _69795) = (term221 _69795).
Proof. exact (TRANS (@lem5383169 _69795) (@lem5383215 _69795)). Qed.
Lemma lem5383217 (_69795 : int) (_69793 : int) (_69794 : int) : ((term140 _69795) = (term134 _69793 _69794)) = ((term222 _69795 _69793 _69794) = term128).
Proof. exact (@lem1988293 (term140 _69795) (term134 _69793 _69794)). Qed.
Lemma lem5383235 (_69795 : int) (_69793 : int) (_69794 : int) : (term222 _69795 _69793 _69794) = (term223 _69795 _69793 _69794).
Proof. exact (@lem1982792 (term140 _69795) (term134 _69793 _69794)). Qed.
Lemma lem5383242 (_69793 : int) (_69794 : int) : (term224 _69793 _69794) = (term225 _69793 _69794).
Proof. exact (@lem1982781 (real_of_int _69793) term201 (real_of_int _69794)). Qed.
Lemma lem5383243 (_69795 : int) : (term150 _69795) = (term150 _69795).
Proof. exact (eq_refl (term150 _69795)). Qed.
Lemma lem5383244 (_69795 : int) (_69793 : int) (_69794 : int) : (term223 _69795 _69793 _69794) = (term226 _69795 _69793 _69794).
Proof. exact (MK_COMB (@lem5383243 _69795) (@lem5383242 _69793 _69794)). Qed.
Lemma lem5383245 (_69793 : int) (_69795 : int) (_69794 : int) : (term226 _69795 _69793 _69794) = (term227 _69793 _69795 _69794).
Proof. exact (@lem1982757 (term228 _69793) (term140 _69795) (term228 _69794)). Qed.
Lemma lem5383246 (_69794 : int) (_69795 : int) : (term229 _69795 _69794) = (term230 _69794 _69795).
Proof. exact (@lem1982761 (term228 _69794) (term140 _69795)). Qed.
Lemma lem5383247 (_69793 : int) : (term231 _69793) = (term231 _69793).
Proof. exact (eq_refl (term231 _69793)). Qed.
Lemma lem5383248 (_69793 : int) (_69794 : int) (_69795 : int) : (term227 _69793 _69795 _69794) = (term232 _69793 _69794 _69795).
Proof. exact (MK_COMB (@lem5383247 _69793) (@lem5383246 _69794 _69795)). Qed.
Lemma lem5383249 (_69793 : int) (_69794 : int) (_69795 : int) : (term226 _69795 _69793 _69794) = (term232 _69793 _69794 _69795).
Proof. exact (TRANS (@lem5383245 _69793 _69795 _69794) (@lem5383248 _69793 _69794 _69795)). Qed.
Lemma lem5383250 (_69793 : int) (_69794 : int) (_69795 : int) : (term223 _69795 _69793 _69794) = (term232 _69793 _69794 _69795).
Proof. exact (TRANS (@lem5383244 _69795 _69793 _69794) (@lem5383249 _69793 _69794 _69795)). Qed.
Lemma lem5383252 (_69793 : int) (_69794 : int) (_69795 : int) : (term222 _69795 _69793 _69794) = (term232 _69793 _69794 _69795).
Proof. exact (TRANS (@lem5383235 _69795 _69793 _69794) (@lem5383250 _69793 _69794 _69795)). Qed.
Lemma lem5383253 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5383254 (_69793 : int) (_69794 : int) (_69795 : int) : (term233 _69795 _69793 _69794) = (term234 _69793 _69794 _69795).
Proof. exact (MK_COMB (@lem5383253) (@lem5383252 _69793 _69794 _69795)). Qed.
Lemma lem5383255 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5383256 (_69793 : int) (_69794 : int) (_69795 : int) : ((term222 _69795 _69793 _69794) = term128) = ((term232 _69793 _69794 _69795) = term128).
Proof. exact (MK_COMB (@lem5383254 _69793 _69794 _69795) (@lem5383255)). Qed.
Lemma lem5383257 (_69793 : int) (_69794 : int) (_69795 : int) : ((term140 _69795) = (term134 _69793 _69794)) = ((term232 _69793 _69794 _69795) = term128).
Proof. exact (TRANS (@lem5383217 _69795 _69793 _69794) (@lem5383256 _69793 _69794 _69795)). Qed.
Lemma lem5383258 (_69794 : int) (_69795 : int) : (term154 _69795 _69794) = (term235 _69794 _69795).
Proof. exact (@lem1988287 (real_of_int _69794) (term151 _69795)). Qed.
Lemma lem5383270 (_69795 : int) : (term151 _69795) = (term236 _69795).
Proof. exact (@lem1982755 (real_of_int _69795) term138 term138). Qed.
Lemma lem5383272 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5383273 : term138 = term237.
Proof. exact (@lem5383272 term44). Qed.
Lemma lem5383275 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5383276 : term138 = term237.
Proof. exact (@lem5383275 term44). Qed.
Lemma lem5383277 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5383278 : term238 = term239.
Proof. exact (MK_COMB (@lem5383277) (@lem5383276)). Qed.
Lemma lem5383279 : term240 = term241.
Proof. exact (MK_COMB (@lem5383278) (@lem5383273)). Qed.
Lemma lem5383280 : term242.
Proof. exact (@lem1981473 term138 term138 term138 term138 term243 term138). Qed.
Lemma lem5383282 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5383283 : term245 = term246.
Proof. exact (@lem5383282 (NUMERAL 0) term44). Qed.
Lemma lem5383284 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5383285 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5383286 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5383285 h1) (fun h1 : term246 = True => @lem5383284)). Qed.
Lemma lem5383287 : term246 = True.
Proof. exact (EQ_MP (@lem5383286) (@lem5383284)). Qed.
Lemma lem5383288 : term245 = True.
Proof. exact (TRANS (@lem5383283) (@lem5383287)). Qed.
Lemma lem5383289 : True = term245.
Proof. exact (SYM (@lem5383288)). Qed.
Lemma lem5383290 : term245.
Proof. exact (EQ_MP (@lem5383289) (@lem0)). Qed.
Lemma lem5383291 : term248.
Proof. exact (@lem5383280 (@lem5383290)). Qed.
Lemma lem5383293 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5383294 : term245 = term246.
Proof. exact (@lem5383293 (NUMERAL 0) term44). Qed.
Lemma lem5383295 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5383296 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5383297 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5383296 h1) (fun h1 : term246 = True => @lem5383295)). Qed.
Lemma lem5383298 : term246 = True.
Proof. exact (EQ_MP (@lem5383297) (@lem5383295)). Qed.
Lemma lem5383299 : term245 = True.
Proof. exact (TRANS (@lem5383294) (@lem5383298)). Qed.
Lemma lem5383300 : True = term245.
Proof. exact (SYM (@lem5383299)). Qed.
Lemma lem5383301 : term245.
Proof. exact (EQ_MP (@lem5383300) (@lem0)). Qed.
Lemma lem5383302 : term249.
Proof. exact (@lem5383291 (@lem5383301)). Qed.
Lemma lem5383304 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5383305 : term245 = term246.
Proof. exact (@lem5383304 (NUMERAL 0) term44). Qed.
Lemma lem5383306 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5383307 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5383308 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5383307 h1) (fun h1 : term246 = True => @lem5383306)). Qed.
Lemma lem5383309 : term246 = True.
Proof. exact (EQ_MP (@lem5383308) (@lem5383306)). Qed.
Lemma lem5383310 : term245 = True.
Proof. exact (TRANS (@lem5383305) (@lem5383309)). Qed.
Lemma lem5383311 : True = term245.
Proof. exact (SYM (@lem5383310)). Qed.
Lemma lem5383312 : term245.
Proof. exact (EQ_MP (@lem5383311) (@lem0)). Qed.
Lemma lem5383313 : term250.
Proof. exact (@lem5383302 (@lem5383312)). Qed.
Lemma lem5383315 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5383316 : term210 = term211.
Proof. exact (@lem5383315 term44 term44). Qed.
Lemma lem5383317 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5383318 : term213 = term44.
Proof. exact (EQ_MP (@lem5383317) (@lem940073)). Qed.
Lemma lem5383319 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5383320 : term211 = term138.
Proof. exact (MK_COMB (@lem5383319) (@lem5383318)). Qed.
Lemma lem5383321 : term210 = term138.
Proof. exact (TRANS (@lem5383316) (@lem5383320)). Qed.
Lemma lem5383323 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5383324 : term210 = term211.
Proof. exact (@lem5383323 term44 term44). Qed.
Lemma lem5383325 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5383326 : term213 = term44.
Proof. exact (EQ_MP (@lem5383325) (@lem940073)). Qed.
Lemma lem5383327 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5383328 : term211 = term138.
Proof. exact (MK_COMB (@lem5383327) (@lem5383326)). Qed.
Lemma lem5383329 : term210 = term138.
Proof. exact (TRANS (@lem5383324) (@lem5383328)). Qed.
Lemma lem5383330 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5383331 : term251 = term238.
Proof. exact (MK_COMB (@lem5383330) (@lem5383329)). Qed.
Lemma lem5383332 : term252 = term240.
Proof. exact (MK_COMB (@lem5383331) (@lem5383321)). Qed.
Lemma lem5383333 : term240 = term253.
Proof. exact (@lem1367770 term44 term44). Qed.
Lemma lem5383334 : term254 = term255.
Proof. exact (@lem706885). Qed.
Lemma lem5383335 : (term254 = term255) = (term256 = term257).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term255). Qed.
Lemma lem5383336 : term256 = term257.
Proof. exact (EQ_MP (@lem5383335) (@lem5383334)). Qed.
Lemma lem5383337 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5383338 : term253 = term243.
Proof. exact (MK_COMB (@lem5383337) (@lem5383336)). Qed.
Lemma lem5383339 : term240 = term243.
Proof. exact (TRANS (@lem5383333) (@lem5383338)). Qed.
Lemma lem5383340 : term252 = term243.
Proof. exact (TRANS (@lem5383332) (@lem5383339)). Qed.
Lemma lem5383341 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5383342 : term258 = term259.
Proof. exact (MK_COMB (@lem5383341) (@lem5383340)). Qed.
Lemma lem5383343 : term138 = term138.
Proof. exact (eq_refl term138). Qed.
Lemma lem5383344 : term260 = term261.
Proof. exact (MK_COMB (@lem5383342) (@lem5383343)). Qed.
Lemma lem5383346 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5383347 : term261 = term262.
Proof. exact (@lem5383346 term257 term44). Qed.
Lemma lem5383348 : term263 = term255.
Proof. exact (@lem996237 term255). Qed.
Lemma lem5383349 : (term263 = term255) = (term264 = term257).
Proof. exact (@lem1007663 term255 (BIT1 0) term255). Qed.
Lemma lem5383350 : term264 = term257.
Proof. exact (EQ_MP (@lem5383349) (@lem5383348)). Qed.
Lemma lem5383351 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5383352 : term262 = term243.
Proof. exact (MK_COMB (@lem5383351) (@lem5383350)). Qed.
Lemma lem5383353 : term261 = term243.
Proof. exact (TRANS (@lem5383347) (@lem5383352)). Qed.
Lemma lem5383354 : term260 = term243.
Proof. exact (TRANS (@lem5383344) (@lem5383353)). Qed.
Lemma lem5383356 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5383357 : term210 = term211.
Proof. exact (@lem5383356 term44 term44). Qed.
Lemma lem5383358 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5383359 : term213 = term44.
Proof. exact (EQ_MP (@lem5383358) (@lem940073)). Qed.
Lemma lem5383360 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5383361 : term211 = term138.
Proof. exact (MK_COMB (@lem5383360) (@lem5383359)). Qed.
Lemma lem5383362 : term210 = term138.
Proof. exact (TRANS (@lem5383357) (@lem5383361)). Qed.
Lemma lem5383363 : term259 = term259.
Proof. exact (eq_refl term259). Qed.
Lemma lem5383364 : term265 = term261.
Proof. exact (MK_COMB (@lem5383363) (@lem5383362)). Qed.
Lemma lem5383366 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5383367 : term261 = term262.
Proof. exact (@lem5383366 term257 term44). Qed.
Lemma lem5383368 : term263 = term255.
Proof. exact (@lem996237 term255). Qed.
Lemma lem5383369 : (term263 = term255) = (term264 = term257).
Proof. exact (@lem1007663 term255 (BIT1 0) term255). Qed.
Lemma lem5383370 : term264 = term257.
Proof. exact (EQ_MP (@lem5383369) (@lem5383368)). Qed.
Lemma lem5383371 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5383372 : term262 = term243.
Proof. exact (MK_COMB (@lem5383371) (@lem5383370)). Qed.
Lemma lem5383373 : term261 = term243.
Proof. exact (TRANS (@lem5383367) (@lem5383372)). Qed.
Lemma lem5383374 : term265 = term243.
Proof. exact (TRANS (@lem5383364) (@lem5383373)). Qed.
Lemma lem5383375 : term243 = term265.
Proof. exact (SYM (@lem5383374)). Qed.
Lemma lem5383376 : term260 = term265.
Proof. exact (TRANS (@lem5383354) (@lem5383375)). Qed.
Lemma lem5383377 : term241 = term266.
Proof. exact (@lem5383313 (@lem5383376)). Qed.
Lemma lem5383378 : term240 = term266.
Proof. exact (TRANS (@lem5383279) (@lem5383377)). Qed.
Lemma lem5383380 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5383381 : term266 = term243.
Proof. exact (@lem5383380 term243). Qed.
Lemma lem5383382 : term240 = term243.
Proof. exact (TRANS (@lem5383378) (@lem5383381)). Qed.
Lemma lem5383383 (_69795 : int) : (term139 _69795) = (term139 _69795).
Proof. exact (eq_refl (term139 _69795)). Qed.
Lemma lem5383384 (_69795 : int) : (term236 _69795) = (term267 _69795).
Proof. exact (MK_COMB (@lem5383383 _69795) (@lem5383382)). Qed.
Lemma lem5383386 (_69795 : int) : (term151 _69795) = (term267 _69795).
Proof. exact (TRANS (@lem5383270 _69795) (@lem5383384 _69795)). Qed.
Lemma lem5383389 (_69794 : int) : (term268 _69794) = (term268 _69794).
Proof. exact (eq_refl (term268 _69794)). Qed.
Lemma lem5383390 (_69794 : int) (_69795 : int) : (term269 _69794 _69795) = (term270 _69794 _69795).
Proof. exact (MK_COMB (@lem5383389 _69794) (@lem5383386 _69795)). Qed.
Lemma lem5383391 (_69794 : int) (_69795 : int) : (term270 _69794 _69795) = (term271 _69794 _69795).
Proof. exact (@lem1982792 (real_of_int _69794) (term267 _69795)). Qed.
Lemma lem5383392 (_69795 : int) : (term272 _69795) = (term273 _69795).
Proof. exact (@lem1982781 (real_of_int _69795) term201 term243). Qed.
Lemma lem5383394 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5383395 : term243 = term266.
Proof. exact (@lem5383394 term257). Qed.
Lemma lem5383397 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5383398 : term201 = term202.
Proof. exact (@lem5383397 term44). Qed.
Lemma lem5383399 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5383400 : term203 = term204.
Proof. exact (MK_COMB (@lem5383399) (@lem5383398)). Qed.
Lemma lem5383401 : term274 = term275.
Proof. exact (MK_COMB (@lem5383400) (@lem5383395)). Qed.
Lemma lem5383402 : term275 = term276.
Proof. exact (@lem1981613 term201 term243 term138 term138). Qed.
Lemma lem5383404 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5383405 : term210 = term211.
Proof. exact (@lem5383404 term44 term44). Qed.
Lemma lem5383406 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5383407 : term213 = term44.
Proof. exact (EQ_MP (@lem5383406) (@lem940073)). Qed.
Lemma lem5383408 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5383409 : term211 = term138.
Proof. exact (MK_COMB (@lem5383408) (@lem5383407)). Qed.
Lemma lem5383410 : term210 = term138.
Proof. exact (TRANS (@lem5383405) (@lem5383409)). Qed.
Lemma lem5383412 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5383413 : term274 = term279.
Proof. exact (@lem5383412 term44 term257). Qed.
Lemma lem5383414 : term280 = term255.
Proof. exact (@lem996238 term255). Qed.
Lemma lem5383415 : (term280 = term255) = (term281 = term257).
Proof. exact (@lem1007663 (BIT1 0) term255 term255). Qed.
Lemma lem5383416 : term281 = term257.
Proof. exact (EQ_MP (@lem5383415) (@lem5383414)). Qed.
Lemma lem5383417 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5383418 : term282 = term243.
Proof. exact (MK_COMB (@lem5383417) (@lem5383416)). Qed.
Lemma lem5383419 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5383420 : term279 = term283.
Proof. exact (MK_COMB (@lem5383419) (@lem5383418)). Qed.
Lemma lem5383421 : term274 = term283.
Proof. exact (TRANS (@lem5383413) (@lem5383420)). Qed.
Lemma lem5383422 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5383423 : term284 = term285.
Proof. exact (MK_COMB (@lem5383422) (@lem5383421)). Qed.
Lemma lem5383424 : term276 = term286.
Proof. exact (MK_COMB (@lem5383423) (@lem5383410)). Qed.
Lemma lem5383425 : term275 = term286.
Proof. exact (TRANS (@lem5383402) (@lem5383424)). Qed.
Lemma lem5383426 : term274 = term286.
Proof. exact (TRANS (@lem5383401) (@lem5383425)). Qed.
Lemma lem5383428 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5383429 : term286 = term283.
Proof. exact (@lem5383428 term283). Qed.
Lemma lem5383430 : term274 = term283.
Proof. exact (TRANS (@lem5383426) (@lem5383429)). Qed.
Lemma lem5383433 (_69795 : int) : (term231 _69795) = (term231 _69795).
Proof. exact (eq_refl (term231 _69795)). Qed.
Lemma lem5383434 (_69795 : int) : (term273 _69795) = (term287 _69795).
Proof. exact (MK_COMB (@lem5383433 _69795) (@lem5383430)). Qed.
Lemma lem5383435 (_69795 : int) : (term272 _69795) = (term287 _69795).
Proof. exact (TRANS (@lem5383392 _69795) (@lem5383434 _69795)). Qed.
Lemma lem5383436 (_69794 : int) : (term139 _69794) = (term139 _69794).
Proof. exact (eq_refl (term139 _69794)). Qed.
Lemma lem5383439 (_69794 : int) (_69795 : int) : (term271 _69794 _69795) = (term288 _69794 _69795).
Proof. exact (MK_COMB (@lem5383436 _69794) (@lem5383435 _69795)). Qed.
Lemma lem5383440 (_69794 : int) (_69795 : int) : (term270 _69794 _69795) = (term288 _69794 _69795).
Proof. exact (TRANS (@lem5383391 _69794 _69795) (@lem5383439 _69794 _69795)). Qed.
Lemma lem5383441 (_69794 : int) (_69795 : int) : (term269 _69794 _69795) = (term288 _69794 _69795).
Proof. exact (TRANS (@lem5383390 _69794 _69795) (@lem5383440 _69794 _69795)). Qed.
Lemma lem5383442 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5383443 (_69794 : int) (_69795 : int) : (term289 _69794 _69795) = (term290 _69794 _69795).
Proof. exact (MK_COMB (@lem5383442) (@lem5383441 _69794 _69795)). Qed.
Lemma lem5383444 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5383445 (_69794 : int) (_69795 : int) : (term235 _69794 _69795) = (term291 _69794 _69795).
Proof. exact (MK_COMB (@lem5383443 _69794 _69795) (@lem5383444)). Qed.
Lemma lem5383446 (_69794 : int) (_69795 : int) : (term154 _69795 _69794) = (term291 _69794 _69795).
Proof. exact (TRANS (@lem5383258 _69794 _69795) (@lem5383445 _69794 _69795)). Qed.
Lemma lem5383447 (_69793 : int) : ((real_of_int _69793) = term128) = ((term195 _69793) = term128).
Proof. exact (@lem1988293 (real_of_int _69793) term128). Qed.
Lemma lem5383453 (_69793 : int) : (term195 _69793) = (term196 _69793).
Proof. exact (@lem1982792 (real_of_int _69793) term128). Qed.
Lemma lem5383455 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5383456 : term128 = term198.
Proof. exact (@lem5383455 (NUMERAL 0)). Qed.
Lemma lem5383458 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5383459 : term201 = term202.
Proof. exact (@lem5383458 term44). Qed.
Lemma lem5383460 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5383461 : term203 = term204.
Proof. exact (MK_COMB (@lem5383460) (@lem5383459)). Qed.
Lemma lem5383462 : term205 = term206.
Proof. exact (MK_COMB (@lem5383461) (@lem5383456)). Qed.
Lemma lem5383463 : term206 = term207.
Proof. exact (@lem1981613 term201 term128 term138 term138). Qed.
Lemma lem5383465 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5383466 : term210 = term211.
Proof. exact (@lem5383465 term44 term44). Qed.
Lemma lem5383467 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5383468 : term213 = term44.
Proof. exact (EQ_MP (@lem5383467) (@lem940073)). Qed.
Lemma lem5383469 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5383470 : term211 = term138.
Proof. exact (MK_COMB (@lem5383469) (@lem5383468)). Qed.
Lemma lem5383471 : term210 = term138.
Proof. exact (TRANS (@lem5383466) (@lem5383470)). Qed.
Lemma lem5383473 (x : nat) : (term214 x) = term128.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5383474 : term205 = term128.
Proof. exact (@lem5383473 term44). Qed.
Lemma lem5383475 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5383476 : term215 = term216.
Proof. exact (MK_COMB (@lem5383475) (@lem5383474)). Qed.
Lemma lem5383477 : term207 = term198.
Proof. exact (MK_COMB (@lem5383476) (@lem5383471)). Qed.
Lemma lem5383478 : term206 = term198.
Proof. exact (TRANS (@lem5383463) (@lem5383477)). Qed.
Lemma lem5383479 : term205 = term198.
Proof. exact (TRANS (@lem5383462) (@lem5383478)). Qed.
Lemma lem5383481 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5383482 : term198 = term128.
Proof. exact (@lem5383481 term128). Qed.
Lemma lem5383483 : term205 = term128.
Proof. exact (TRANS (@lem5383479) (@lem5383482)). Qed.
Lemma lem5383484 (_69793 : int) : (term139 _69793) = (term139 _69793).
Proof. exact (eq_refl (term139 _69793)). Qed.
Lemma lem5383485 (_69793 : int) : (term196 _69793) = (term218 _69793).
Proof. exact (MK_COMB (@lem5383484 _69793) (@lem5383483)). Qed.
Lemma lem5383486 (_69793 : int) : (term218 _69793) = (real_of_int _69793).
Proof. exact (@lem1982723 (real_of_int _69793)). Qed.
Lemma lem5383487 (_69793 : int) : (term196 _69793) = (real_of_int _69793).
Proof. exact (TRANS (@lem5383485 _69793) (@lem5383486 _69793)). Qed.
Lemma lem5383489 (_69793 : int) : (term195 _69793) = (real_of_int _69793).
Proof. exact (TRANS (@lem5383453 _69793) (@lem5383487 _69793)). Qed.
Lemma lem5383490 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5383491 (_69793 : int) : (term292 _69793) = (term155 _69793).
Proof. exact (MK_COMB (@lem5383490) (@lem5383489 _69793)). Qed.
Lemma lem5383492 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5383493 (_69793 : int) : ((term195 _69793) = term128) = ((real_of_int _69793) = term128).
Proof. exact (MK_COMB (@lem5383491 _69793) (@lem5383492)). Qed.
Lemma lem5383494 (_69793 : int) : ((real_of_int _69793) = term128) = ((real_of_int _69793) = term128).
Proof. exact (TRANS (@lem5383447 _69793) (@lem5383493 _69793)). Qed.
Lemma lem5383495 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5383496 (_69794 : int) (_69795 : int) : (term156 _69795 _69794) = (term293 _69794 _69795).
Proof. exact (MK_COMB (@lem5383495) (@lem5383446 _69794 _69795)). Qed.
Lemma lem5383497 (_69794 : int) (_69795 : int) (_69793 : int) : (term157 _69795 _69794 _69793) = (term294 _69794 _69795 _69793).
Proof. exact (MK_COMB (@lem5383496 _69794 _69795) (@lem5383494 _69793)). Qed.
Lemma lem5383498 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5383499 (_69793 : int) (_69794 : int) (_69795 : int) : (term158 _69795 _69793 _69794) = (term295 _69793 _69794 _69795).
Proof. exact (MK_COMB (@lem5383498) (@lem5383257 _69793 _69794 _69795)). Qed.
Lemma lem5383500 (_69794 : int) (_69795 : int) (_69793 : int) : (term159 _69795 _69794 _69793) = (term296 _69794 _69795 _69793).
Proof. exact (MK_COMB (@lem5383499 _69793 _69794 _69795) (@lem5383497 _69794 _69795 _69793)). Qed.
Lemma lem5383501 (_69794 : int) (_69795 : int) : (term163 _69795 _69794) = (term297 _69794 _69795).
Proof. exact (@lem1988287 (real_of_int _69794) (term140 _69795)). Qed.
Lemma lem5383513 (_69794 : int) (_69795 : int) : (term298 _69794 _69795) = (term299 _69794 _69795).
Proof. exact (@lem1982792 (real_of_int _69794) (term140 _69795)). Qed.
Lemma lem5383514 (_69795 : int) : (term300 _69795) = (term301 _69795).
Proof. exact (@lem1982781 (real_of_int _69795) term201 term138). Qed.
Lemma lem5383516 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5383517 : term138 = term237.
Proof. exact (@lem5383516 term44). Qed.
Lemma lem5383519 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5383520 : term201 = term202.
Proof. exact (@lem5383519 term44). Qed.
Lemma lem5383521 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5383522 : term203 = term204.
Proof. exact (MK_COMB (@lem5383521) (@lem5383520)). Qed.
Lemma lem5383523 : term302 = term303.
Proof. exact (MK_COMB (@lem5383522) (@lem5383517)). Qed.
Lemma lem5383524 : term303 = term304.
Proof. exact (@lem1981613 term201 term138 term138 term138). Qed.
Lemma lem5383526 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5383527 : term210 = term211.
Proof. exact (@lem5383526 term44 term44). Qed.
Lemma lem5383528 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5383529 : term213 = term44.
Proof. exact (EQ_MP (@lem5383528) (@lem940073)). Qed.
Lemma lem5383530 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5383531 : term211 = term138.
Proof. exact (MK_COMB (@lem5383530) (@lem5383529)). Qed.
Lemma lem5383532 : term210 = term138.
Proof. exact (TRANS (@lem5383527) (@lem5383531)). Qed.
Lemma lem5383534 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5383535 : term302 = term305.
Proof. exact (@lem5383534 term44 term44). Qed.
Lemma lem5383536 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5383537 : term213 = term44.
Proof. exact (EQ_MP (@lem5383536) (@lem940073)). Qed.
Lemma lem5383538 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5383539 : term211 = term138.
Proof. exact (MK_COMB (@lem5383538) (@lem5383537)). Qed.
Lemma lem5383540 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5383541 : term305 = term201.
Proof. exact (MK_COMB (@lem5383540) (@lem5383539)). Qed.
Lemma lem5383542 : term302 = term201.
Proof. exact (TRANS (@lem5383535) (@lem5383541)). Qed.
Lemma lem5383543 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5383544 : term306 = term307.
Proof. exact (MK_COMB (@lem5383543) (@lem5383542)). Qed.
Lemma lem5383545 : term304 = term202.
Proof. exact (MK_COMB (@lem5383544) (@lem5383532)). Qed.
Lemma lem5383546 : term303 = term202.
Proof. exact (TRANS (@lem5383524) (@lem5383545)). Qed.
Lemma lem5383547 : term302 = term202.
Proof. exact (TRANS (@lem5383523) (@lem5383546)). Qed.
Lemma lem5383549 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5383550 : term202 = term201.
Proof. exact (@lem5383549 term201). Qed.
Lemma lem5383551 : term302 = term201.
Proof. exact (TRANS (@lem5383547) (@lem5383550)). Qed.
Lemma lem5383554 (_69795 : int) : (term231 _69795) = (term231 _69795).
Proof. exact (eq_refl (term231 _69795)). Qed.
Lemma lem5383555 (_69795 : int) : (term301 _69795) = (term308 _69795).
Proof. exact (MK_COMB (@lem5383554 _69795) (@lem5383551)). Qed.
Lemma lem5383556 (_69795 : int) : (term300 _69795) = (term308 _69795).
Proof. exact (TRANS (@lem5383514 _69795) (@lem5383555 _69795)). Qed.
Lemma lem5383557 (_69794 : int) : (term139 _69794) = (term139 _69794).
Proof. exact (eq_refl (term139 _69794)). Qed.
Lemma lem5383560 (_69794 : int) (_69795 : int) : (term299 _69794 _69795) = (term309 _69794 _69795).
Proof. exact (MK_COMB (@lem5383557 _69794) (@lem5383556 _69795)). Qed.
Lemma lem5383562 (_69794 : int) (_69795 : int) : (term298 _69794 _69795) = (term309 _69794 _69795).
Proof. exact (TRANS (@lem5383513 _69794 _69795) (@lem5383560 _69794 _69795)). Qed.
Lemma lem5383563 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5383564 (_69794 : int) (_69795 : int) : (term310 _69794 _69795) = (term311 _69794 _69795).
Proof. exact (MK_COMB (@lem5383563) (@lem5383562 _69794 _69795)). Qed.
Lemma lem5383565 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5383566 (_69794 : int) (_69795 : int) : (term297 _69794 _69795) = (term312 _69794 _69795).
Proof. exact (MK_COMB (@lem5383564 _69794 _69795) (@lem5383565)). Qed.
Lemma lem5383567 (_69794 : int) (_69795 : int) : (term163 _69795 _69794) = (term312 _69794 _69795).
Proof. exact (TRANS (@lem5383501 _69794 _69795) (@lem5383566 _69794 _69795)). Qed.
Lemma lem5383568 (_69793 : int) : (term169 _69793) = (term313 _69793).
Proof. exact (@lem1988287 term128 (term140 _69793)). Qed.
Lemma lem5383580 (_69793 : int) : (term314 _69793) = (term315 _69793).
Proof. exact (@lem1982792 term128 (term140 _69793)). Qed.
Lemma lem5383581 (_69793 : int) : (term300 _69793) = (term301 _69793).
Proof. exact (@lem1982781 (real_of_int _69793) term201 term138). Qed.
Lemma lem5383583 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5383584 : term138 = term237.
Proof. exact (@lem5383583 term44). Qed.
Lemma lem5383586 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5383587 : term201 = term202.
Proof. exact (@lem5383586 term44). Qed.
Lemma lem5383588 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5383589 : term203 = term204.
Proof. exact (MK_COMB (@lem5383588) (@lem5383587)). Qed.
Lemma lem5383590 : term302 = term303.
Proof. exact (MK_COMB (@lem5383589) (@lem5383584)). Qed.
Lemma lem5383591 : term303 = term304.
Proof. exact (@lem1981613 term201 term138 term138 term138). Qed.
Lemma lem5383593 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5383594 : term210 = term211.
Proof. exact (@lem5383593 term44 term44). Qed.
Lemma lem5383595 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5383596 : term213 = term44.
Proof. exact (EQ_MP (@lem5383595) (@lem940073)). Qed.
Lemma lem5383597 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5383598 : term211 = term138.
Proof. exact (MK_COMB (@lem5383597) (@lem5383596)). Qed.
Lemma lem5383599 : term210 = term138.
Proof. exact (TRANS (@lem5383594) (@lem5383598)). Qed.
Lemma lem5383601 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5383602 : term302 = term305.
Proof. exact (@lem5383601 term44 term44). Qed.
Lemma lem5383603 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5383604 : term213 = term44.
Proof. exact (EQ_MP (@lem5383603) (@lem940073)). Qed.
Lemma lem5383605 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5383606 : term211 = term138.
Proof. exact (MK_COMB (@lem5383605) (@lem5383604)). Qed.
Lemma lem5383607 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5383608 : term305 = term201.
Proof. exact (MK_COMB (@lem5383607) (@lem5383606)). Qed.
Lemma lem5383609 : term302 = term201.
Proof. exact (TRANS (@lem5383602) (@lem5383608)). Qed.
Lemma lem5383610 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5383611 : term306 = term307.
Proof. exact (MK_COMB (@lem5383610) (@lem5383609)). Qed.
Lemma lem5383612 : term304 = term202.
Proof. exact (MK_COMB (@lem5383611) (@lem5383599)). Qed.
Lemma lem5383613 : term303 = term202.
Proof. exact (TRANS (@lem5383591) (@lem5383612)). Qed.
Lemma lem5383614 : term302 = term202.
Proof. exact (TRANS (@lem5383590) (@lem5383613)). Qed.
Lemma lem5383616 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5383617 : term202 = term201.
Proof. exact (@lem5383616 term201). Qed.
Lemma lem5383618 : term302 = term201.
Proof. exact (TRANS (@lem5383614) (@lem5383617)). Qed.
Lemma lem5383621 (_69793 : int) : (term231 _69793) = (term231 _69793).
Proof. exact (eq_refl (term231 _69793)). Qed.
Lemma lem5383622 (_69793 : int) : (term301 _69793) = (term308 _69793).
Proof. exact (MK_COMB (@lem5383621 _69793) (@lem5383618)). Qed.
Lemma lem5383623 (_69793 : int) : (term300 _69793) = (term308 _69793).
Proof. exact (TRANS (@lem5383581 _69793) (@lem5383622 _69793)). Qed.
Lemma lem5383624 : term178 = term178.
Proof. exact (eq_refl term178). Qed.
Lemma lem5383625 (_69793 : int) : (term315 _69793) = (term316 _69793).
Proof. exact (MK_COMB (@lem5383624) (@lem5383623 _69793)). Qed.
Lemma lem5383626 (_69793 : int) : (term316 _69793) = (term308 _69793).
Proof. exact (@lem1982721 (term308 _69793)). Qed.
Lemma lem5383627 (_69793 : int) : (term315 _69793) = (term308 _69793).
Proof. exact (TRANS (@lem5383625 _69793) (@lem5383626 _69793)). Qed.
Lemma lem5383629 (_69793 : int) : (term314 _69793) = (term308 _69793).
Proof. exact (TRANS (@lem5383580 _69793) (@lem5383627 _69793)). Qed.
Lemma lem5383630 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5383631 (_69793 : int) : (term317 _69793) = (term318 _69793).
Proof. exact (MK_COMB (@lem5383630) (@lem5383629 _69793)). Qed.
Lemma lem5383632 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5383633 (_69793 : int) : (term313 _69793) = (term319 _69793).
Proof. exact (MK_COMB (@lem5383631 _69793) (@lem5383632)). Qed.
Lemma lem5383634 (_69793 : int) : (term169 _69793) = (term319 _69793).
Proof. exact (TRANS (@lem5383568 _69793) (@lem5383633 _69793)). Qed.
Lemma lem5383635 (_69793 : int) : (term182 _69793) = (term320 _69793).
Proof. exact (@lem1988287 (real_of_int _69793) term179). Qed.
Lemma lem5383642 : term179 = term138.
Proof. exact (@lem1982721 term138). Qed.
Lemma lem5383645 (_69793 : int) : (term268 _69793) = (term268 _69793).
Proof. exact (eq_refl (term268 _69793)). Qed.
Lemma lem5383646 (_69793 : int) : (term321 _69793) = (term322 _69793).
Proof. exact (MK_COMB (@lem5383645 _69793) (@lem5383642)). Qed.
Lemma lem5383647 (_69793 : int) : (term322 _69793) = (term323 _69793).
Proof. exact (@lem1982792 (real_of_int _69793) term138). Qed.
Lemma lem5383649 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5383650 : term138 = term237.
Proof. exact (@lem5383649 term44). Qed.
Lemma lem5383652 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5383653 : term201 = term202.
Proof. exact (@lem5383652 term44). Qed.
Lemma lem5383654 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5383655 : term203 = term204.
Proof. exact (MK_COMB (@lem5383654) (@lem5383653)). Qed.
Lemma lem5383656 : term302 = term303.
Proof. exact (MK_COMB (@lem5383655) (@lem5383650)). Qed.
Lemma lem5383657 : term303 = term304.
Proof. exact (@lem1981613 term201 term138 term138 term138). Qed.
Lemma lem5383659 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5383660 : term210 = term211.
Proof. exact (@lem5383659 term44 term44). Qed.
Lemma lem5383661 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5383662 : term213 = term44.
Proof. exact (EQ_MP (@lem5383661) (@lem940073)). Qed.
Lemma lem5383663 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5383664 : term211 = term138.
Proof. exact (MK_COMB (@lem5383663) (@lem5383662)). Qed.
Lemma lem5383665 : term210 = term138.
Proof. exact (TRANS (@lem5383660) (@lem5383664)). Qed.
Lemma lem5383667 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5383668 : term302 = term305.
Proof. exact (@lem5383667 term44 term44). Qed.
Lemma lem5383669 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5383670 : term213 = term44.
Proof. exact (EQ_MP (@lem5383669) (@lem940073)). Qed.
Lemma lem5383671 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5383672 : term211 = term138.
Proof. exact (MK_COMB (@lem5383671) (@lem5383670)). Qed.
Lemma lem5383673 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5383674 : term305 = term201.
Proof. exact (MK_COMB (@lem5383673) (@lem5383672)). Qed.
Lemma lem5383675 : term302 = term201.
Proof. exact (TRANS (@lem5383668) (@lem5383674)). Qed.
Lemma lem5383676 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5383677 : term306 = term307.
Proof. exact (MK_COMB (@lem5383676) (@lem5383675)). Qed.
Lemma lem5383678 : term304 = term202.
Proof. exact (MK_COMB (@lem5383677) (@lem5383665)). Qed.
Lemma lem5383679 : term303 = term202.
Proof. exact (TRANS (@lem5383657) (@lem5383678)). Qed.
Lemma lem5383680 : term302 = term202.
Proof. exact (TRANS (@lem5383656) (@lem5383679)). Qed.
Lemma lem5383682 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5383683 : term202 = term201.
Proof. exact (@lem5383682 term201). Qed.
Lemma lem5383684 : term302 = term201.
Proof. exact (TRANS (@lem5383680) (@lem5383683)). Qed.
Lemma lem5383685 (_69793 : int) : (term139 _69793) = (term139 _69793).
Proof. exact (eq_refl (term139 _69793)). Qed.
Lemma lem5383688 (_69793 : int) : (term323 _69793) = (term324 _69793).
Proof. exact (MK_COMB (@lem5383685 _69793) (@lem5383684)). Qed.
Lemma lem5383689 (_69793 : int) : (term322 _69793) = (term324 _69793).
Proof. exact (TRANS (@lem5383647 _69793) (@lem5383688 _69793)). Qed.
Lemma lem5383690 (_69793 : int) : (term321 _69793) = (term324 _69793).
Proof. exact (TRANS (@lem5383646 _69793) (@lem5383689 _69793)). Qed.
Lemma lem5383691 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5383692 (_69793 : int) : (term325 _69793) = (term326 _69793).
Proof. exact (MK_COMB (@lem5383691) (@lem5383690 _69793)). Qed.
Lemma lem5383693 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5383694 (_69793 : int) : (term320 _69793) = (term327 _69793).
Proof. exact (MK_COMB (@lem5383692 _69793) (@lem5383693)). Qed.
Lemma lem5383695 (_69793 : int) : (term182 _69793) = (term327 _69793).
Proof. exact (TRANS (@lem5383635 _69793) (@lem5383694 _69793)). Qed.
Lemma lem5383696 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5383697 (_69793 : int) : (term171 _69793) = (term328 _69793).
Proof. exact (MK_COMB (@lem5383696) (@lem5383634 _69793)). Qed.
Lemma lem5383698 (_69793 : int) : (term183 _69793) = (term329 _69793).
Proof. exact (MK_COMB (@lem5383697 _69793) (@lem5383695 _69793)). Qed.
Lemma lem5383699 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5383700 (_69794 : int) (_69795 : int) : (term184 _69795 _69794) = (term330 _69794 _69795).
Proof. exact (MK_COMB (@lem5383699) (@lem5383567 _69794 _69795)). Qed.
Lemma lem5383701 (_69794 : int) (_69795 : int) (_69793 : int) : (term185 _69795 _69794 _69793) = (term331 _69794 _69795 _69793).
Proof. exact (MK_COMB (@lem5383700 _69794 _69795) (@lem5383698 _69793)). Qed.
Lemma lem5383702 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5383703 (_69794 : int) (_69795 : int) (_69793 : int) : (term186 _69795 _69794 _69793) = (term332 _69794 _69795 _69793).
Proof. exact (MK_COMB (@lem5383702) (@lem5383500 _69794 _69795 _69793)). Qed.
Lemma lem5383704 (_69794 : int) (_69795 : int) (_69793 : int) : (term187 _69795 _69794 _69793) = (term333 _69794 _69795 _69793).
Proof. exact (MK_COMB (@lem5383703 _69794 _69795 _69793) (@lem5383701 _69794 _69795 _69793)). Qed.
Lemma lem5383705 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5383706 (_69795 : int) : (term188 _69795) = (term334 _69795).
Proof. exact (MK_COMB (@lem5383705) (@lem5383216 _69795)). Qed.
Lemma lem5383707 (_69794 : int) (_69795 : int) (_69793 : int) : (term189 _69795 _69794 _69793) = (term335 _69794 _69795 _69793).
Proof. exact (MK_COMB (@lem5383706 _69795) (@lem5383704 _69794 _69795 _69793)). Qed.
Lemma lem5383708 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5383709 (_69794 : int) : (term188 _69794) = (term334 _69794).
Proof. exact (MK_COMB (@lem5383708) (@lem5383168 _69794)). Qed.
Lemma lem5383710 (_69794 : int) (_69795 : int) (_69793 : int) : (term190 _69795 _69794 _69793) = (term336 _69794 _69795 _69793).
Proof. exact (MK_COMB (@lem5383709 _69794) (@lem5383707 _69794 _69795 _69793)). Qed.
Lemma lem5383711 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5383712 (_69793 : int) : (term188 _69793) = (term334 _69793).
Proof. exact (MK_COMB (@lem5383711) (@lem5383120 _69793)). Qed.
Lemma lem5383713 (_69794 : int) (_69795 : int) (_69793 : int) : (term191 _69795 _69794 _69793) = (term337 _69794 _69795 _69793).
Proof. exact (MK_COMB (@lem5383712 _69793) (@lem5383710 _69794 _69795 _69793)). Qed.
Lemma lem5383720 (_69794 : int) (_69795 : int) (_69793 : int) : (term193 _69795 _69794 _69793) = (term337 _69794 _69795 _69793).
Proof. exact (TRANS (@lem5383072 _69795 _69794 _69793) (@lem5383713 _69794 _69795 _69793)). Qed.
Lemma lem5383737 (_69794 : int) (_69795 : int) (_69793 : int) : (term331 _69794 _69795 _69793) = (term338 _69794 _69795 _69793).
Proof. exact (@lem19158 (term319 _69793) (term312 _69794 _69795) (term327 _69793)). Qed.
Lemma lem5383750 (_69794 : int) (_69795 : int) (_69793 : int) : (term332 _69794 _69795 _69793) = (term332 _69794 _69795 _69793).
Proof. exact (eq_refl (term332 _69794 _69795 _69793)). Qed.
Lemma lem5383751 (_69794 : int) (_69795 : int) (_69793 : int) : (term333 _69794 _69795 _69793) = (term339 _69794 _69795 _69793).
Proof. exact (MK_COMB (@lem5383750 _69794 _69795 _69793) (@lem5383737 _69794 _69795 _69793)). Qed.
Lemma lem5383752 (_69794 : int) (_69795 : int) (_69793 : int) : (term339 _69794 _69795 _69793) = (term340 _69794 _69795 _69793).
Proof. exact (@lem19158 (term341 _69794 _69795 _69793) (term296 _69794 _69795 _69793) (term342 _69794 _69795 _69793)). Qed.
Lemma lem5383759 (_69794 : int) (_69795 : int) (_69793 : int) : (term343 _69794 _69795 _69793) = (term344 _69794 _69795 _69793).
Proof. exact (@lem19367 ((term232 _69793 _69794 _69795) = term128) (term294 _69794 _69795 _69793) (term342 _69794 _69795 _69793)). Qed.
Lemma lem5383766 (_69794 : int) (_69795 : int) (_69793 : int) : (term345 _69794 _69795 _69793) = (term346 _69794 _69795 _69793).
Proof. exact (@lem19367 ((term232 _69793 _69794 _69795) = term128) (term294 _69794 _69795 _69793) (term341 _69794 _69795 _69793)). Qed.
Lemma lem5383767 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5383768 (_69794 : int) (_69795 : int) (_69793 : int) : (term347 _69794 _69795 _69793) = (term348 _69794 _69795 _69793).
Proof. exact (MK_COMB (@lem5383767) (@lem5383766 _69794 _69795 _69793)). Qed.
Lemma lem5383769 (_69794 : int) (_69795 : int) (_69793 : int) : (term340 _69794 _69795 _69793) = (term349 _69794 _69795 _69793).
Proof. exact (MK_COMB (@lem5383768 _69794 _69795 _69793) (@lem5383759 _69794 _69795 _69793)). Qed.
Lemma lem5383770 (_69794 : int) (_69795 : int) (_69793 : int) : (term339 _69794 _69795 _69793) = (term349 _69794 _69795 _69793).
Proof. exact (TRANS (@lem5383752 _69794 _69795 _69793) (@lem5383769 _69794 _69795 _69793)). Qed.
Lemma lem5383771 (_69794 : int) (_69795 : int) (_69793 : int) : (term333 _69794 _69795 _69793) = (term349 _69794 _69795 _69793).
Proof. exact (TRANS (@lem5383751 _69794 _69795 _69793) (@lem5383770 _69794 _69795 _69793)). Qed.
Lemma lem5383774 (_69795 : int) : (term334 _69795) = (term334 _69795).
Proof. exact (eq_refl (term334 _69795)). Qed.
Lemma lem5383775 (_69794 : int) (_69795 : int) (_69793 : int) : (term335 _69794 _69795 _69793) = (term350 _69794 _69795 _69793).
Proof. exact (MK_COMB (@lem5383774 _69795) (@lem5383771 _69794 _69795 _69793)). Qed.
Lemma lem5383776 (_69794 : int) (_69795 : int) (_69793 : int) : (term350 _69794 _69795 _69793) = (term351 _69794 _69795 _69793).
Proof. exact (@lem19158 (term346 _69794 _69795 _69793) (term221 _69795) (term344 _69794 _69795 _69793)). Qed.
Lemma lem5383783 (_69794 : int) (_69795 : int) (_69793 : int) : (term352 _69794 _69795 _69793) = (term353 _69794 _69795 _69793).
Proof. exact (@lem19158 (term354 _69794 _69795 _69793) (term221 _69795) (term355 _69794 _69795 _69793)). Qed.
Lemma lem5383790 (_69794 : int) (_69795 : int) (_69793 : int) : (term356 _69794 _69795 _69793) = (term357 _69794 _69795 _69793).
Proof. exact (@lem19158 (term358 _69794 _69795 _69793) (term221 _69795) (term359 _69794 _69795 _69793)). Qed.
Lemma lem5383791 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5383792 (_69794 : int) (_69795 : int) (_69793 : int) : (term360 _69794 _69795 _69793) = (term361 _69794 _69795 _69793).
Proof. exact (MK_COMB (@lem5383791) (@lem5383790 _69794 _69795 _69793)). Qed.
Lemma lem5383793 (_69794 : int) (_69795 : int) (_69793 : int) : (term351 _69794 _69795 _69793) = (term362 _69794 _69795 _69793).
Proof. exact (MK_COMB (@lem5383792 _69794 _69795 _69793) (@lem5383783 _69794 _69795 _69793)). Qed.
Lemma lem5383794 (_69794 : int) (_69795 : int) (_69793 : int) : (term350 _69794 _69795 _69793) = (term362 _69794 _69795 _69793).
Proof. exact (TRANS (@lem5383776 _69794 _69795 _69793) (@lem5383793 _69794 _69795 _69793)). Qed.
Lemma lem5383795 (_69794 : int) (_69795 : int) (_69793 : int) : (term335 _69794 _69795 _69793) = (term362 _69794 _69795 _69793).
Proof. exact (TRANS (@lem5383775 _69794 _69795 _69793) (@lem5383794 _69794 _69795 _69793)). Qed.
Lemma lem5383798 (_69794 : int) : (term334 _69794) = (term334 _69794).
Proof. exact (eq_refl (term334 _69794)). Qed.
Lemma lem5383799 (_69794 : int) (_69795 : int) (_69793 : int) : (term336 _69794 _69795 _69793) = (term363 _69794 _69795 _69793).
Proof. exact (MK_COMB (@lem5383798 _69794) (@lem5383795 _69794 _69795 _69793)). Qed.
Lemma lem5383800 (_69794 : int) (_69795 : int) (_69793 : int) : (term363 _69794 _69795 _69793) = (term364 _69794 _69795 _69793).
Proof. exact (@lem19158 (term357 _69794 _69795 _69793) (term221 _69794) (term353 _69794 _69795 _69793)). Qed.
Lemma lem5383807 (_69794 : int) (_69795 : int) (_69793 : int) : (term365 _69794 _69795 _69793) = (term366 _69794 _69795 _69793).
Proof. exact (@lem19158 (term367 _69794 _69795 _69793) (term221 _69794) (term368 _69794 _69795 _69793)). Qed.
Lemma lem5383814 (_69794 : int) (_69795 : int) (_69793 : int) : (term369 _69794 _69795 _69793) = (term370 _69794 _69795 _69793).
Proof. exact (@lem19158 (term371 _69794 _69795 _69793) (term221 _69794) (term372 _69794 _69795 _69793)). Qed.
Lemma lem5383815 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5383816 (_69794 : int) (_69795 : int) (_69793 : int) : (term373 _69794 _69795 _69793) = (term374 _69794 _69795 _69793).
Proof. exact (MK_COMB (@lem5383815) (@lem5383814 _69794 _69795 _69793)). Qed.
Lemma lem5383817 (_69794 : int) (_69795 : int) (_69793 : int) : (term364 _69794 _69795 _69793) = (term375 _69794 _69795 _69793).
Proof. exact (MK_COMB (@lem5383816 _69794 _69795 _69793) (@lem5383807 _69794 _69795 _69793)). Qed.
Lemma lem5383818 (_69794 : int) (_69795 : int) (_69793 : int) : (term363 _69794 _69795 _69793) = (term375 _69794 _69795 _69793).
Proof. exact (TRANS (@lem5383800 _69794 _69795 _69793) (@lem5383817 _69794 _69795 _69793)). Qed.
Lemma lem5383819 (_69794 : int) (_69795 : int) (_69793 : int) : (term336 _69794 _69795 _69793) = (term375 _69794 _69795 _69793).
Proof. exact (TRANS (@lem5383799 _69794 _69795 _69793) (@lem5383818 _69794 _69795 _69793)). Qed.
Lemma lem5383822 (_69793 : int) : (term334 _69793) = (term334 _69793).
Proof. exact (eq_refl (term334 _69793)). Qed.
Lemma lem5383823 (_69794 : int) (_69795 : int) (_69793 : int) : (term337 _69794 _69795 _69793) = (term376 _69794 _69795 _69793).
Proof. exact (MK_COMB (@lem5383822 _69793) (@lem5383819 _69794 _69795 _69793)). Qed.
Lemma lem5383824 (_69794 : int) (_69795 : int) (_69793 : int) : (term376 _69794 _69795 _69793) = (term377 _69794 _69795 _69793).
Proof. exact (@lem19158 (term370 _69794 _69795 _69793) (term221 _69793) (term366 _69794 _69795 _69793)). Qed.
Lemma lem5383831 (_69794 : int) (_69795 : int) (_69793 : int) : (term378 _69794 _69795 _69793) = (term379 _69794 _69795 _69793).
Proof. exact (@lem19158 (term380 _69794 _69795 _69793) (term221 _69793) (term381 _69794 _69795 _69793)). Qed.
Lemma lem5383838 (_69794 : int) (_69795 : int) (_69793 : int) : (term382 _69794 _69795 _69793) = (term383 _69794 _69795 _69793).
Proof. exact (@lem19158 (term384 _69794 _69795 _69793) (term221 _69793) (term385 _69794 _69795 _69793)). Qed.
Lemma lem5383839 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5383840 (_69794 : int) (_69795 : int) (_69793 : int) : (term386 _69794 _69795 _69793) = (term387 _69794 _69795 _69793).
Proof. exact (MK_COMB (@lem5383839) (@lem5383838 _69794 _69795 _69793)). Qed.
Lemma lem5383841 (_69794 : int) (_69795 : int) (_69793 : int) : (term377 _69794 _69795 _69793) = (term388 _69794 _69795 _69793).
Proof. exact (MK_COMB (@lem5383840 _69794 _69795 _69793) (@lem5383831 _69794 _69795 _69793)). Qed.
Lemma lem5383842 (_69794 : int) (_69795 : int) (_69793 : int) : (term376 _69794 _69795 _69793) = (term388 _69794 _69795 _69793).
Proof. exact (TRANS (@lem5383824 _69794 _69795 _69793) (@lem5383841 _69794 _69795 _69793)). Qed.
Lemma lem5383843 (_69794 : int) (_69795 : int) (_69793 : int) : (term337 _69794 _69795 _69793) = (term388 _69794 _69795 _69793).
Proof. exact (TRANS (@lem5383823 _69794 _69795 _69793) (@lem5383842 _69794 _69795 _69793)). Qed.
Lemma lem5383844 (_69794 : int) (_69795 : int) (_69793 : int) : (term193 _69795 _69794 _69793) = (term388 _69794 _69795 _69793).
Proof. exact (TRANS (@lem5383720 _69794 _69795 _69793) (@lem5383843 _69794 _69795 _69793)). Qed.
Lemma lem5383866 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term388 _69794 _69795 _69793) : term388 _69794 _69795 _69793.
Proof. exact (h1). Qed.
Lemma lem5383867 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term383 _69794 _69795 _69793) : term383 _69794 _69795 _69793.
Proof. exact (h1). Qed.
Lemma lem5383868 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term389 _69794 _69795 _69793) : term389 _69794 _69795 _69793.
Proof. exact (h1). Qed.
Lemma lem5383869 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term389 _69794 _69795 _69793) : term384 _69794 _69795 _69793.
Proof. exact (proj2 (@lem5383868 _69794 _69795 _69793 h1)). Qed.
Lemma lem5383870 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term389 _69794 _69795 _69793) : term221 _69793.
Proof. exact (proj1 (@lem5383868 _69794 _69795 _69793 h1)). Qed.
Lemma lem5383871 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term389 _69794 _69795 _69793) : term371 _69794 _69795 _69793.
Proof. exact (proj2 (@lem5383869 _69794 _69795 _69793 h1)). Qed.
Lemma lem5383873 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term389 _69794 _69795 _69793) : term358 _69794 _69795 _69793.
Proof. exact (proj2 (@lem5383871 _69794 _69795 _69793 h1)). Qed.
Lemma lem5383875 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term389 _69794 _69795 _69793) : term341 _69794 _69795 _69793.
Proof. exact (proj2 (@lem5383873 _69794 _69795 _69793 h1)). Qed.
Lemma lem5383877 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term389 _69794 _69795 _69793) : term319 _69793.
Proof. exact (proj2 (@lem5383875 _69794 _69795 _69793 h1)). Qed.
Lemma lem5383880 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5383881 : term390 = term245.
Proof. exact (@lem5383880 term128 term138). Qed.
Lemma lem5383883 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5383884 : term138 = term237.
Proof. exact (@lem5383883 term44). Qed.
Lemma lem5383886 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5383887 : term128 = term198.
Proof. exact (@lem5383886 (NUMERAL 0)). Qed.
Lemma lem5383888 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5383889 : term391 = term392.
Proof. exact (MK_COMB (@lem5383888) (@lem5383887)). Qed.
Lemma lem5383890 : term245 = term393.
Proof. exact (MK_COMB (@lem5383889) (@lem5383884)). Qed.
Lemma lem5383891 : term394.
Proof. exact (@lem1980255 term128 term138 term138 term138). Qed.
Lemma lem5383893 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5383894 : term245 = term246.
Proof. exact (@lem5383893 (NUMERAL 0) term44). Qed.
Lemma lem5383895 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5383896 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5383897 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5383896 h1) (fun h1 : term246 = True => @lem5383895)). Qed.
Lemma lem5383898 : term246 = True.
Proof. exact (EQ_MP (@lem5383897) (@lem5383895)). Qed.
Lemma lem5383899 : term245 = True.
Proof. exact (TRANS (@lem5383894) (@lem5383898)). Qed.
Lemma lem5383900 : True = term245.
Proof. exact (SYM (@lem5383899)). Qed.
Lemma lem5383901 : term245.
Proof. exact (EQ_MP (@lem5383900) (@lem0)). Qed.
Lemma lem5383902 : term395.
Proof. exact (@lem5383891 (@lem5383901)). Qed.
Lemma lem5383904 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5383905 : term245 = term246.
Proof. exact (@lem5383904 (NUMERAL 0) term44). Qed.
Lemma lem5383906 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5383907 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5383908 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5383907 h1) (fun h1 : term246 = True => @lem5383906)). Qed.
Lemma lem5383909 : term246 = True.
Proof. exact (EQ_MP (@lem5383908) (@lem5383906)). Qed.
Lemma lem5383910 : term245 = True.
Proof. exact (TRANS (@lem5383905) (@lem5383909)). Qed.
Lemma lem5383911 : True = term245.
Proof. exact (SYM (@lem5383910)). Qed.
Lemma lem5383912 : term245.
Proof. exact (EQ_MP (@lem5383911) (@lem0)). Qed.
Lemma lem5383913 : term393 = term396.
Proof. exact (@lem5383902 (@lem5383912)). Qed.
Lemma lem5383915 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5383916 : term210 = term211.
Proof. exact (@lem5383915 term44 term44). Qed.
Lemma lem5383917 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5383918 : term213 = term44.
Proof. exact (EQ_MP (@lem5383917) (@lem940073)). Qed.
Lemma lem5383919 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5383920 : term211 = term138.
Proof. exact (MK_COMB (@lem5383919) (@lem5383918)). Qed.
Lemma lem5383921 : term210 = term138.
Proof. exact (TRANS (@lem5383916) (@lem5383920)). Qed.
Lemma lem5383923 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5383924 : term398 = term128.
Proof. exact (@lem5383923 term44). Qed.
Lemma lem5383925 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5383926 : term399 = term391.
Proof. exact (MK_COMB (@lem5383925) (@lem5383924)). Qed.
Lemma lem5383927 : term396 = term245.
Proof. exact (MK_COMB (@lem5383926) (@lem5383921)). Qed.
Lemma lem5383929 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5383930 : term245 = term246.
Proof. exact (@lem5383929 (NUMERAL 0) term44). Qed.
Lemma lem5383931 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5383932 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5383933 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5383932 h1) (fun h1 : term246 = True => @lem5383931)). Qed.
Lemma lem5383934 : term246 = True.
Proof. exact (EQ_MP (@lem5383933) (@lem5383931)). Qed.
Lemma lem5383935 : term245 = True.
Proof. exact (TRANS (@lem5383930) (@lem5383934)). Qed.
Lemma lem5383936 : term396 = True.
Proof. exact (TRANS (@lem5383927) (@lem5383935)). Qed.
Lemma lem5383937 : term393 = True.
Proof. exact (TRANS (@lem5383913) (@lem5383936)). Qed.
Lemma lem5383938 : term245 = True.
Proof. exact (TRANS (@lem5383890) (@lem5383937)). Qed.
Lemma lem5383939 : term390 = True.
Proof. exact (TRANS (@lem5383881) (@lem5383938)). Qed.
Lemma lem5383940 : True = term390.
Proof. exact (SYM (@lem5383939)). Qed.
Lemma lem5383941 : term390.
Proof. exact (EQ_MP (@lem5383940) (@lem0)). Qed.
Lemma lem5383942 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term389 _69794 _69795 _69793) : term400 _69793.
Proof. exact (conj (@lem5383941) (@lem5383870 _69794 _69795 _69793 h1)). Qed.
Lemma lem5383944 (x : real) (y : real) : term401 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5383945 (_69793 : int) : term402 _69793.
Proof. exact (@lem5383944 term138 (real_of_int _69793)). Qed.
Lemma lem5383946 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term389 _69794 _69795 _69793) : term403 _69793.
Proof. exact (@lem5383945 _69793 (@lem5383942 _69794 _69795 _69793 h1)). Qed.
Lemma lem5383947 (_69793 : int) : (term404 _69793) = (real_of_int _69793).
Proof. exact (@lem1982733 (real_of_int _69793)). Qed.
Lemma lem5383948 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5383949 (_69793 : int) : (term405 _69793) = (term220 _69793).
Proof. exact (MK_COMB (@lem5383948) (@lem5383947 _69793)). Qed.
Lemma lem5383950 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5383951 (_69793 : int) : (term403 _69793) = (term221 _69793).
Proof. exact (MK_COMB (@lem5383949 _69793) (@lem5383950)). Qed.
Lemma lem5383952 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term389 _69794 _69795 _69793) : term221 _69793.
Proof. exact (EQ_MP (@lem5383951 _69793) (@lem5383946 _69794 _69795 _69793 h1)). Qed.
Lemma lem5383954 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5383955 : term390 = term245.
Proof. exact (@lem5383954 term128 term138). Qed.
Lemma lem5383957 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5383958 : term138 = term237.
Proof. exact (@lem5383957 term44). Qed.
Lemma lem5383960 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5383961 : term128 = term198.
Proof. exact (@lem5383960 (NUMERAL 0)). Qed.
Lemma lem5383962 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5383963 : term391 = term392.
Proof. exact (MK_COMB (@lem5383962) (@lem5383961)). Qed.
Lemma lem5383964 : term245 = term393.
Proof. exact (MK_COMB (@lem5383963) (@lem5383958)). Qed.
Lemma lem5383965 : term394.
Proof. exact (@lem1980255 term128 term138 term138 term138). Qed.
Lemma lem5383967 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5383968 : term245 = term246.
Proof. exact (@lem5383967 (NUMERAL 0) term44). Qed.
Lemma lem5383969 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5383970 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5383971 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5383970 h1) (fun h1 : term246 = True => @lem5383969)). Qed.
Lemma lem5383972 : term246 = True.
Proof. exact (EQ_MP (@lem5383971) (@lem5383969)). Qed.
Lemma lem5383973 : term245 = True.
Proof. exact (TRANS (@lem5383968) (@lem5383972)). Qed.
Lemma lem5383974 : True = term245.
Proof. exact (SYM (@lem5383973)). Qed.
Lemma lem5383975 : term245.
Proof. exact (EQ_MP (@lem5383974) (@lem0)). Qed.
Lemma lem5383976 : term395.
Proof. exact (@lem5383965 (@lem5383975)). Qed.
Lemma lem5383978 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5383979 : term245 = term246.
Proof. exact (@lem5383978 (NUMERAL 0) term44). Qed.
Lemma lem5383980 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5383981 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5383982 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5383981 h1) (fun h1 : term246 = True => @lem5383980)). Qed.
Lemma lem5383983 : term246 = True.
Proof. exact (EQ_MP (@lem5383982) (@lem5383980)). Qed.
Lemma lem5383984 : term245 = True.
Proof. exact (TRANS (@lem5383979) (@lem5383983)). Qed.
Lemma lem5383985 : True = term245.
Proof. exact (SYM (@lem5383984)). Qed.
Lemma lem5383986 : term245.
Proof. exact (EQ_MP (@lem5383985) (@lem0)). Qed.
Lemma lem5383987 : term393 = term396.
Proof. exact (@lem5383976 (@lem5383986)). Qed.
Lemma lem5383989 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5383990 : term210 = term211.
Proof. exact (@lem5383989 term44 term44). Qed.
Lemma lem5383991 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5383992 : term213 = term44.
Proof. exact (EQ_MP (@lem5383991) (@lem940073)). Qed.
Lemma lem5383993 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5383994 : term211 = term138.
Proof. exact (MK_COMB (@lem5383993) (@lem5383992)). Qed.
Lemma lem5383995 : term210 = term138.
Proof. exact (TRANS (@lem5383990) (@lem5383994)). Qed.
Lemma lem5383997 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5383998 : term398 = term128.
Proof. exact (@lem5383997 term44). Qed.
Lemma lem5383999 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5384000 : term399 = term391.
Proof. exact (MK_COMB (@lem5383999) (@lem5383998)). Qed.
Lemma lem5384001 : term396 = term245.
Proof. exact (MK_COMB (@lem5384000) (@lem5383995)). Qed.
Lemma lem5384003 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5384004 : term245 = term246.
Proof. exact (@lem5384003 (NUMERAL 0) term44). Qed.
Lemma lem5384005 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5384006 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5384007 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5384006 h1) (fun h1 : term246 = True => @lem5384005)). Qed.
Lemma lem5384008 : term246 = True.
Proof. exact (EQ_MP (@lem5384007) (@lem5384005)). Qed.
Lemma lem5384009 : term245 = True.
Proof. exact (TRANS (@lem5384004) (@lem5384008)). Qed.
Lemma lem5384010 : term396 = True.
Proof. exact (TRANS (@lem5384001) (@lem5384009)). Qed.
Lemma lem5384011 : term393 = True.
Proof. exact (TRANS (@lem5383987) (@lem5384010)). Qed.
Lemma lem5384012 : term245 = True.
Proof. exact (TRANS (@lem5383964) (@lem5384011)). Qed.
Lemma lem5384013 : term390 = True.
Proof. exact (TRANS (@lem5383955) (@lem5384012)). Qed.
Lemma lem5384014 : True = term390.
Proof. exact (SYM (@lem5384013)). Qed.
Lemma lem5384015 : term390.
Proof. exact (EQ_MP (@lem5384014) (@lem0)). Qed.
Lemma lem5384016 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term389 _69794 _69795 _69793) : term406 _69793.
Proof. exact (conj (@lem5384015) (@lem5383877 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384018 (x : real) (y : real) : term401 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5384019 (_69793 : int) : term407 _69793.
Proof. exact (@lem5384018 term138 (term308 _69793)). Qed.
Lemma lem5384020 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term389 _69794 _69795 _69793) : term408 _69793.
Proof. exact (@lem5384019 _69793 (@lem5384016 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384021 (_69793 : int) : (term409 _69793) = (term308 _69793).
Proof. exact (@lem1982733 (term308 _69793)). Qed.
Lemma lem5384022 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5384023 (_69793 : int) : (term410 _69793) = (term318 _69793).
Proof. exact (MK_COMB (@lem5384022) (@lem5384021 _69793)). Qed.
Lemma lem5384024 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5384025 (_69793 : int) : (term408 _69793) = (term319 _69793).
Proof. exact (MK_COMB (@lem5384023 _69793) (@lem5384024)). Qed.
Lemma lem5384026 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term389 _69794 _69795 _69793) : term319 _69793.
Proof. exact (EQ_MP (@lem5384025 _69793) (@lem5384020 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384027 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term389 _69794 _69795 _69793) : term411 _69793.
Proof. exact (conj (@lem5384026 _69794 _69795 _69793 h1) (@lem5383952 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384029 (x : real) (y : real) : term412 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5384030 (_69793 : int) : term413 _69793.
Proof. exact (@lem5384029 (term308 _69793) (real_of_int _69793)). Qed.
Lemma lem5384031 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term389 _69794 _69795 _69793) : term414 _69793.
Proof. exact (@lem5384030 _69793 (@lem5384027 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384032 (_69793 : int) : (term415 _69793) = (term416 _69793).
Proof. exact (@lem1982759 (term228 _69793) (real_of_int _69793) term201). Qed.
Lemma lem5384033 (_69793 : int) : (term417 _69793) = (term418 _69793).
Proof. exact (@lem1982713 term201 (real_of_int _69793)). Qed.
Lemma lem5384035 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5384036 : term138 = term237.
Proof. exact (@lem5384035 term44). Qed.
Lemma lem5384038 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5384039 : term201 = term202.
Proof. exact (@lem5384038 term44). Qed.
Lemma lem5384040 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5384041 : term419 = term420.
Proof. exact (MK_COMB (@lem5384040) (@lem5384039)). Qed.
Lemma lem5384042 : term421 = term422.
Proof. exact (MK_COMB (@lem5384041) (@lem5384036)). Qed.
Lemma lem5384043 : term423.
Proof. exact (@lem1981473 term201 term138 term138 term138 term128 term138). Qed.
Lemma lem5384045 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5384046 : term245 = term246.
Proof. exact (@lem5384045 (NUMERAL 0) term44). Qed.
Lemma lem5384047 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5384048 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5384049 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5384048 h1) (fun h1 : term246 = True => @lem5384047)). Qed.
Lemma lem5384050 : term246 = True.
Proof. exact (EQ_MP (@lem5384049) (@lem5384047)). Qed.
Lemma lem5384051 : term245 = True.
Proof. exact (TRANS (@lem5384046) (@lem5384050)). Qed.
Lemma lem5384052 : True = term245.
Proof. exact (SYM (@lem5384051)). Qed.
Lemma lem5384053 : term245.
Proof. exact (EQ_MP (@lem5384052) (@lem0)). Qed.
Lemma lem5384054 : term424.
Proof. exact (@lem5384043 (@lem5384053)). Qed.
Lemma lem5384056 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5384057 : term245 = term246.
Proof. exact (@lem5384056 (NUMERAL 0) term44). Qed.
Lemma lem5384058 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5384059 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5384060 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5384059 h1) (fun h1 : term246 = True => @lem5384058)). Qed.
Lemma lem5384061 : term246 = True.
Proof. exact (EQ_MP (@lem5384060) (@lem5384058)). Qed.
Lemma lem5384062 : term245 = True.
Proof. exact (TRANS (@lem5384057) (@lem5384061)). Qed.
Lemma lem5384063 : True = term245.
Proof. exact (SYM (@lem5384062)). Qed.
Lemma lem5384064 : term245.
Proof. exact (EQ_MP (@lem5384063) (@lem0)). Qed.
Lemma lem5384065 : term425.
Proof. exact (@lem5384054 (@lem5384064)). Qed.
Lemma lem5384067 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5384068 : term245 = term246.
Proof. exact (@lem5384067 (NUMERAL 0) term44). Qed.
Lemma lem5384069 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5384070 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5384071 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5384070 h1) (fun h1 : term246 = True => @lem5384069)). Qed.
Lemma lem5384072 : term246 = True.
Proof. exact (EQ_MP (@lem5384071) (@lem5384069)). Qed.
Lemma lem5384073 : term245 = True.
Proof. exact (TRANS (@lem5384068) (@lem5384072)). Qed.
Lemma lem5384074 : True = term245.
Proof. exact (SYM (@lem5384073)). Qed.
Lemma lem5384075 : term245.
Proof. exact (EQ_MP (@lem5384074) (@lem0)). Qed.
Lemma lem5384076 : term426.
Proof. exact (@lem5384065 (@lem5384075)). Qed.
Lemma lem5384078 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5384079 : term210 = term211.
Proof. exact (@lem5384078 term44 term44). Qed.
Lemma lem5384080 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5384081 : term213 = term44.
Proof. exact (EQ_MP (@lem5384080) (@lem940073)). Qed.
Lemma lem5384082 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5384083 : term211 = term138.
Proof. exact (MK_COMB (@lem5384082) (@lem5384081)). Qed.
Lemma lem5384084 : term210 = term138.
Proof. exact (TRANS (@lem5384079) (@lem5384083)). Qed.
Lemma lem5384086 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5384087 : term302 = term305.
Proof. exact (@lem5384086 term44 term44). Qed.
Lemma lem5384088 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5384089 : term213 = term44.
Proof. exact (EQ_MP (@lem5384088) (@lem940073)). Qed.
Lemma lem5384090 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5384091 : term211 = term138.
Proof. exact (MK_COMB (@lem5384090) (@lem5384089)). Qed.
Lemma lem5384092 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5384093 : term305 = term201.
Proof. exact (MK_COMB (@lem5384092) (@lem5384091)). Qed.
Lemma lem5384094 : term302 = term201.
Proof. exact (TRANS (@lem5384087) (@lem5384093)). Qed.
Lemma lem5384095 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5384096 : term427 = term419.
Proof. exact (MK_COMB (@lem5384095) (@lem5384094)). Qed.
Lemma lem5384097 : term428 = term421.
Proof. exact (MK_COMB (@lem5384096) (@lem5384084)). Qed.
Lemma lem5384099 (m : nat) : (term429 m) = term128.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5384100 : term421 = term128.
Proof. exact (@lem5384099 term44). Qed.
Lemma lem5384101 : term428 = term128.
Proof. exact (TRANS (@lem5384097) (@lem5384100)). Qed.
Lemma lem5384102 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5384103 : term430 = term431.
Proof. exact (MK_COMB (@lem5384102) (@lem5384101)). Qed.
Lemma lem5384104 : term138 = term138.
Proof. exact (eq_refl term138). Qed.
Lemma lem5384105 : term432 = term398.
Proof. exact (MK_COMB (@lem5384103) (@lem5384104)). Qed.
Lemma lem5384107 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5384108 : term398 = term128.
Proof. exact (@lem5384107 term44). Qed.
Lemma lem5384109 : term432 = term128.
Proof. exact (TRANS (@lem5384105) (@lem5384108)). Qed.
Lemma lem5384111 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5384112 : term210 = term211.
Proof. exact (@lem5384111 term44 term44). Qed.
Lemma lem5384113 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5384114 : term213 = term44.
Proof. exact (EQ_MP (@lem5384113) (@lem940073)). Qed.
Lemma lem5384115 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5384116 : term211 = term138.
Proof. exact (MK_COMB (@lem5384115) (@lem5384114)). Qed.
Lemma lem5384117 : term210 = term138.
Proof. exact (TRANS (@lem5384112) (@lem5384116)). Qed.
Lemma lem5384118 : term431 = term431.
Proof. exact (eq_refl term431). Qed.
Lemma lem5384119 : term433 = term398.
Proof. exact (MK_COMB (@lem5384118) (@lem5384117)). Qed.
Lemma lem5384121 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5384122 : term398 = term128.
Proof. exact (@lem5384121 term44). Qed.
Lemma lem5384123 : term433 = term128.
Proof. exact (TRANS (@lem5384119) (@lem5384122)). Qed.
Lemma lem5384124 : term128 = term433.
Proof. exact (SYM (@lem5384123)). Qed.
Lemma lem5384125 : term432 = term433.
Proof. exact (TRANS (@lem5384109) (@lem5384124)). Qed.
Lemma lem5384126 : term422 = term198.
Proof. exact (@lem5384076 (@lem5384125)). Qed.
Lemma lem5384127 : term421 = term198.
Proof. exact (TRANS (@lem5384042) (@lem5384126)). Qed.
Lemma lem5384129 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5384130 : term198 = term128.
Proof. exact (@lem5384129 term128). Qed.
Lemma lem5384131 : term421 = term128.
Proof. exact (TRANS (@lem5384127) (@lem5384130)). Qed.
Lemma lem5384132 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5384133 : term434 = term431.
Proof. exact (MK_COMB (@lem5384132) (@lem5384131)). Qed.
Lemma lem5384134 (_69793 : int) : (real_of_int _69793) = (real_of_int _69793).
Proof. exact (eq_refl (real_of_int _69793)). Qed.
Lemma lem5384135 (_69793 : int) : (term418 _69793) = (term435 _69793).
Proof. exact (MK_COMB (@lem5384133) (@lem5384134 _69793)). Qed.
Lemma lem5384136 (_69793 : int) : (term417 _69793) = (term435 _69793).
Proof. exact (TRANS (@lem5384033 _69793) (@lem5384135 _69793)). Qed.
Lemma lem5384137 (_69793 : int) : (term435 _69793) = term128.
Proof. exact (@lem1982719 (real_of_int _69793)). Qed.
Lemma lem5384138 (_69793 : int) : (term417 _69793) = term128.
Proof. exact (TRANS (@lem5384136 _69793) (@lem5384137 _69793)). Qed.
Lemma lem5384139 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5384140 (_69793 : int) : (term436 _69793) = term178.
Proof. exact (MK_COMB (@lem5384139) (@lem5384138 _69793)). Qed.
Lemma lem5384141 : term201 = term201.
Proof. exact (eq_refl term201). Qed.
Lemma lem5384142 (_69793 : int) : (term416 _69793) = term437.
Proof. exact (MK_COMB (@lem5384140 _69793) (@lem5384141)). Qed.
Lemma lem5384143 (_69793 : int) : (term415 _69793) = term437.
Proof. exact (TRANS (@lem5384032 _69793) (@lem5384142 _69793)). Qed.
Lemma lem5384144 : term437 = term201.
Proof. exact (@lem1982721 term201). Qed.
Lemma lem5384145 (_69793 : int) : (term415 _69793) = term201.
Proof. exact (TRANS (@lem5384143 _69793) (@lem5384144)). Qed.
Lemma lem5384146 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5384147 (_69793 : int) : (term438 _69793) = term439.
Proof. exact (MK_COMB (@lem5384146) (@lem5384145 _69793)). Qed.
Lemma lem5384148 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5384149 (_69793 : int) : (term414 _69793) = term440.
Proof. exact (MK_COMB (@lem5384147 _69793) (@lem5384148)). Qed.
Lemma lem5384150 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term389 _69794 _69795 _69793) : term440.
Proof. exact (EQ_MP (@lem5384149 _69793) (@lem5384031 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384152 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5384153 : term440 = term441.
Proof. exact (@lem5384152 term128 term201). Qed.
Lemma lem5384155 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5384156 : term201 = term202.
Proof. exact (@lem5384155 term44). Qed.
Lemma lem5384158 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5384159 : term128 = term198.
Proof. exact (@lem5384158 (NUMERAL 0)). Qed.
Lemma lem5384160 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5384161 : term130 = term442.
Proof. exact (MK_COMB (@lem5384160) (@lem5384159)). Qed.
Lemma lem5384162 : term441 = term443.
Proof. exact (MK_COMB (@lem5384161) (@lem5384156)). Qed.
Lemma lem5384163 : term444.
Proof. exact (@lem1980026 term128 term138 term201 term138). Qed.
Lemma lem5384165 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5384166 : term245 = term246.
Proof. exact (@lem5384165 (NUMERAL 0) term44). Qed.
Lemma lem5384167 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5384168 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5384169 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5384168 h1) (fun h1 : term246 = True => @lem5384167)). Qed.
Lemma lem5384170 : term246 = True.
Proof. exact (EQ_MP (@lem5384169) (@lem5384167)). Qed.
Lemma lem5384171 : term245 = True.
Proof. exact (TRANS (@lem5384166) (@lem5384170)). Qed.
Lemma lem5384172 : True = term245.
Proof. exact (SYM (@lem5384171)). Qed.
Lemma lem5384173 : term245.
Proof. exact (EQ_MP (@lem5384172) (@lem0)). Qed.
Lemma lem5384174 : term445.
Proof. exact (@lem5384163 (@lem5384173)). Qed.
Lemma lem5384176 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5384177 : term245 = term246.
Proof. exact (@lem5384176 (NUMERAL 0) term44). Qed.
Lemma lem5384178 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5384179 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5384180 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5384179 h1) (fun h1 : term246 = True => @lem5384178)). Qed.
Lemma lem5384181 : term246 = True.
Proof. exact (EQ_MP (@lem5384180) (@lem5384178)). Qed.
Lemma lem5384182 : term245 = True.
Proof. exact (TRANS (@lem5384177) (@lem5384181)). Qed.
Lemma lem5384183 : True = term245.
Proof. exact (SYM (@lem5384182)). Qed.
Lemma lem5384184 : term245.
Proof. exact (EQ_MP (@lem5384183) (@lem0)). Qed.
Lemma lem5384185 : term443 = term446.
Proof. exact (@lem5384174 (@lem5384184)). Qed.
Lemma lem5384187 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5384188 : term302 = term305.
Proof. exact (@lem5384187 term44 term44). Qed.
Lemma lem5384189 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5384190 : term213 = term44.
Proof. exact (EQ_MP (@lem5384189) (@lem940073)). Qed.
Lemma lem5384191 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5384192 : term211 = term138.
Proof. exact (MK_COMB (@lem5384191) (@lem5384190)). Qed.
Lemma lem5384193 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5384194 : term305 = term201.
Proof. exact (MK_COMB (@lem5384193) (@lem5384192)). Qed.
Lemma lem5384195 : term302 = term201.
Proof. exact (TRANS (@lem5384188) (@lem5384194)). Qed.
Lemma lem5384197 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5384198 : term398 = term128.
Proof. exact (@lem5384197 term44). Qed.
Lemma lem5384199 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5384200 : term447 = term130.
Proof. exact (MK_COMB (@lem5384199) (@lem5384198)). Qed.
Lemma lem5384201 : term446 = term441.
Proof. exact (MK_COMB (@lem5384200) (@lem5384195)). Qed.
Lemma lem5384203 (m : nat) (n : nat) : (term448 m n) = (term449 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5384204 : term441 = term450.
Proof. exact (@lem5384203 (NUMERAL 0) term44). Qed.
Lemma lem5384205 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5384206 (h1 : term247 = (BIT1 0)) : (term44 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5384207 : (term247 = (BIT1 0)) = ((term44 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5384206 h1) (fun h1 : (term44 = (NUMERAL 0)) = False => @lem5384205)). Qed.
Lemma lem5384208 : (term44 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5384207) (@lem5384205)). Qed.
Lemma lem5384209 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5384210 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5384211 : term451 = (and True).
Proof. exact (MK_COMB (@lem5384210) (@lem5384209)). Qed.
Lemma lem5384212 : term450 = (True /\ False).
Proof. exact (MK_COMB (@lem5384211) (@lem5384208)). Qed.
Lemma lem5384214 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5384215 : term450 = False.
Proof. exact (TRANS (@lem5384212) (@lem5384214)). Qed.
Lemma lem5384216 : term441 = False.
Proof. exact (TRANS (@lem5384204) (@lem5384215)). Qed.
Lemma lem5384217 : term446 = False.
Proof. exact (TRANS (@lem5384201) (@lem5384216)). Qed.
Lemma lem5384218 : term443 = False.
Proof. exact (TRANS (@lem5384185) (@lem5384217)). Qed.
Lemma lem5384219 : term441 = False.
Proof. exact (TRANS (@lem5384162) (@lem5384218)). Qed.
Lemma lem5384220 : term440 = False.
Proof. exact (TRANS (@lem5384153) (@lem5384219)). Qed.
Lemma lem5384221 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term389 _69794 _69795 _69793) : False.
Proof. exact (EQ_MP (@lem5384220) (@lem5384150 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384222 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term452 _69794 _69795 _69793) : term452 _69794 _69795 _69793.
Proof. exact (h1). Qed.
Lemma lem5384223 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term452 _69794 _69795 _69793) : term385 _69794 _69795 _69793.
Proof. exact (proj2 (@lem5384222 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384225 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term452 _69794 _69795 _69793) : term372 _69794 _69795 _69793.
Proof. exact (proj2 (@lem5384223 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384227 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term452 _69794 _69795 _69793) : term359 _69794 _69795 _69793.
Proof. exact (proj2 (@lem5384225 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384229 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term452 _69794 _69795 _69793) : term341 _69794 _69795 _69793.
Proof. exact (proj2 (@lem5384227 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384230 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term452 _69794 _69795 _69793) : term294 _69794 _69795 _69793.
Proof. exact (proj1 (@lem5384227 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384231 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term452 _69794 _69795 _69793) : (real_of_int _69793) = term128.
Proof. exact (proj2 (@lem5384230 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384233 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term452 _69794 _69795 _69793) : term319 _69793.
Proof. exact (proj2 (@lem5384229 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384236 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5384237 : term390 = term245.
Proof. exact (@lem5384236 term128 term138). Qed.
Lemma lem5384239 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5384240 : term138 = term237.
Proof. exact (@lem5384239 term44). Qed.
Lemma lem5384242 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5384243 : term128 = term198.
Proof. exact (@lem5384242 (NUMERAL 0)). Qed.
Lemma lem5384244 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5384245 : term391 = term392.
Proof. exact (MK_COMB (@lem5384244) (@lem5384243)). Qed.
Lemma lem5384246 : term245 = term393.
Proof. exact (MK_COMB (@lem5384245) (@lem5384240)). Qed.
Lemma lem5384247 : term394.
Proof. exact (@lem1980255 term128 term138 term138 term138). Qed.
Lemma lem5384249 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5384250 : term245 = term246.
Proof. exact (@lem5384249 (NUMERAL 0) term44). Qed.
Lemma lem5384251 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5384252 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5384253 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5384252 h1) (fun h1 : term246 = True => @lem5384251)). Qed.
Lemma lem5384254 : term246 = True.
Proof. exact (EQ_MP (@lem5384253) (@lem5384251)). Qed.
Lemma lem5384255 : term245 = True.
Proof. exact (TRANS (@lem5384250) (@lem5384254)). Qed.
Lemma lem5384256 : True = term245.
Proof. exact (SYM (@lem5384255)). Qed.
Lemma lem5384257 : term245.
Proof. exact (EQ_MP (@lem5384256) (@lem0)). Qed.
Lemma lem5384258 : term395.
Proof. exact (@lem5384247 (@lem5384257)). Qed.
Lemma lem5384260 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5384261 : term245 = term246.
Proof. exact (@lem5384260 (NUMERAL 0) term44). Qed.
Lemma lem5384262 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5384263 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5384264 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5384263 h1) (fun h1 : term246 = True => @lem5384262)). Qed.
Lemma lem5384265 : term246 = True.
Proof. exact (EQ_MP (@lem5384264) (@lem5384262)). Qed.
Lemma lem5384266 : term245 = True.
Proof. exact (TRANS (@lem5384261) (@lem5384265)). Qed.
Lemma lem5384267 : True = term245.
Proof. exact (SYM (@lem5384266)). Qed.
Lemma lem5384268 : term245.
Proof. exact (EQ_MP (@lem5384267) (@lem0)). Qed.
Lemma lem5384269 : term393 = term396.
Proof. exact (@lem5384258 (@lem5384268)). Qed.
Lemma lem5384271 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5384272 : term210 = term211.
Proof. exact (@lem5384271 term44 term44). Qed.
Lemma lem5384273 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5384274 : term213 = term44.
Proof. exact (EQ_MP (@lem5384273) (@lem940073)). Qed.
Lemma lem5384275 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5384276 : term211 = term138.
Proof. exact (MK_COMB (@lem5384275) (@lem5384274)). Qed.
Lemma lem5384277 : term210 = term138.
Proof. exact (TRANS (@lem5384272) (@lem5384276)). Qed.
Lemma lem5384279 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5384280 : term398 = term128.
Proof. exact (@lem5384279 term44). Qed.
Lemma lem5384281 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5384282 : term399 = term391.
Proof. exact (MK_COMB (@lem5384281) (@lem5384280)). Qed.
Lemma lem5384283 : term396 = term245.
Proof. exact (MK_COMB (@lem5384282) (@lem5384277)). Qed.
Lemma lem5384285 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5384286 : term245 = term246.
Proof. exact (@lem5384285 (NUMERAL 0) term44). Qed.
Lemma lem5384287 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5384288 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5384289 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5384288 h1) (fun h1 : term246 = True => @lem5384287)). Qed.
Lemma lem5384290 : term246 = True.
Proof. exact (EQ_MP (@lem5384289) (@lem5384287)). Qed.
Lemma lem5384291 : term245 = True.
Proof. exact (TRANS (@lem5384286) (@lem5384290)). Qed.
Lemma lem5384292 : term396 = True.
Proof. exact (TRANS (@lem5384283) (@lem5384291)). Qed.
Lemma lem5384293 : term393 = True.
Proof. exact (TRANS (@lem5384269) (@lem5384292)). Qed.
Lemma lem5384294 : term245 = True.
Proof. exact (TRANS (@lem5384246) (@lem5384293)). Qed.
Lemma lem5384295 : term390 = True.
Proof. exact (TRANS (@lem5384237) (@lem5384294)). Qed.
Lemma lem5384296 : True = term390.
Proof. exact (SYM (@lem5384295)). Qed.
Lemma lem5384297 : term390.
Proof. exact (EQ_MP (@lem5384296) (@lem0)). Qed.
Lemma lem5384298 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term452 _69794 _69795 _69793) : term406 _69793.
Proof. exact (conj (@lem5384297) (@lem5384233 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384300 (x : real) (y : real) : term401 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5384301 (_69793 : int) : term407 _69793.
Proof. exact (@lem5384300 term138 (term308 _69793)). Qed.
Lemma lem5384302 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term452 _69794 _69795 _69793) : term408 _69793.
Proof. exact (@lem5384301 _69793 (@lem5384298 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384303 (_69793 : int) : (term409 _69793) = (term308 _69793).
Proof. exact (@lem1982733 (term308 _69793)). Qed.
Lemma lem5384304 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5384305 (_69793 : int) : (term410 _69793) = (term318 _69793).
Proof. exact (MK_COMB (@lem5384304) (@lem5384303 _69793)). Qed.
Lemma lem5384306 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5384307 (_69793 : int) : (term408 _69793) = (term319 _69793).
Proof. exact (MK_COMB (@lem5384305 _69793) (@lem5384306)). Qed.
Lemma lem5384308 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term452 _69794 _69795 _69793) : term319 _69793.
Proof. exact (EQ_MP (@lem5384307 _69793) (@lem5384302 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384310 (y : real) : term453 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5384311 (_69793 : int) : term454 _69793.
Proof. exact (@lem5384310 (real_of_int _69793)). Qed.
Lemma lem5384312 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term452 _69794 _69795 _69793) : term455 _69793.
Proof. exact (@lem5384311 _69793 (@lem5384231 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384313 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term452 _69794 _69795 _69793) : term456 _69793.
Proof. exact (@lem5384312 _69794 _69795 _69793 h1 term138). Qed.
Lemma lem5384314 (_69793 : int) : (term456 _69793) = ((term404 _69793) = term128).
Proof. exact (eq_refl (term456 _69793)). Qed.
Lemma lem5384315 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term452 _69794 _69795 _69793) : (term404 _69793) = term128.
Proof. exact (EQ_MP (@lem5384314 _69793) (@lem5384313 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384316 (_69793 : int) : (term404 _69793) = (real_of_int _69793).
Proof. exact (@lem1982733 (real_of_int _69793)). Qed.
Lemma lem5384317 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5384318 (_69793 : int) : (term457 _69793) = (term155 _69793).
Proof. exact (MK_COMB (@lem5384317) (@lem5384316 _69793)). Qed.
Lemma lem5384319 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5384320 (_69793 : int) : ((term404 _69793) = term128) = ((real_of_int _69793) = term128).
Proof. exact (MK_COMB (@lem5384318 _69793) (@lem5384319)). Qed.
Lemma lem5384321 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term452 _69794 _69795 _69793) : (real_of_int _69793) = term128.
Proof. exact (EQ_MP (@lem5384320 _69793) (@lem5384315 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384322 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term452 _69794 _69795 _69793) : term458 _69793.
Proof. exact (conj (@lem5384321 _69794 _69795 _69793 h1) (@lem5384308 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384324 (x : real) (y : real) : term459 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5384325 (_69793 : int) : term460 _69793.
Proof. exact (@lem5384324 (real_of_int _69793) (term308 _69793)). Qed.
Lemma lem5384326 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term452 _69794 _69795 _69793) : term461 _69793.
Proof. exact (@lem5384325 _69793 (@lem5384322 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384327 (_69793 : int) : (term462 _69793) = (term463 _69793).
Proof. exact (@lem1982763 (real_of_int _69793) (term228 _69793) term201). Qed.
Lemma lem5384328 (_69793 : int) : (term464 _69793) = (term418 _69793).
Proof. exact (@lem1982715 term201 (real_of_int _69793)). Qed.
Lemma lem5384330 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5384331 : term138 = term237.
Proof. exact (@lem5384330 term44). Qed.
Lemma lem5384333 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5384334 : term201 = term202.
Proof. exact (@lem5384333 term44). Qed.
Lemma lem5384335 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5384336 : term419 = term420.
Proof. exact (MK_COMB (@lem5384335) (@lem5384334)). Qed.
Lemma lem5384337 : term421 = term422.
Proof. exact (MK_COMB (@lem5384336) (@lem5384331)). Qed.
Lemma lem5384338 : term423.
Proof. exact (@lem1981473 term201 term138 term138 term138 term128 term138). Qed.
Lemma lem5384340 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5384341 : term245 = term246.
Proof. exact (@lem5384340 (NUMERAL 0) term44). Qed.
Lemma lem5384342 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5384343 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5384344 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5384343 h1) (fun h1 : term246 = True => @lem5384342)). Qed.
Lemma lem5384345 : term246 = True.
Proof. exact (EQ_MP (@lem5384344) (@lem5384342)). Qed.
Lemma lem5384346 : term245 = True.
Proof. exact (TRANS (@lem5384341) (@lem5384345)). Qed.
Lemma lem5384347 : True = term245.
Proof. exact (SYM (@lem5384346)). Qed.
Lemma lem5384348 : term245.
Proof. exact (EQ_MP (@lem5384347) (@lem0)). Qed.
Lemma lem5384349 : term424.
Proof. exact (@lem5384338 (@lem5384348)). Qed.
Lemma lem5384351 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5384352 : term245 = term246.
Proof. exact (@lem5384351 (NUMERAL 0) term44). Qed.
Lemma lem5384353 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5384354 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5384355 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5384354 h1) (fun h1 : term246 = True => @lem5384353)). Qed.
Lemma lem5384356 : term246 = True.
Proof. exact (EQ_MP (@lem5384355) (@lem5384353)). Qed.
Lemma lem5384357 : term245 = True.
Proof. exact (TRANS (@lem5384352) (@lem5384356)). Qed.
Lemma lem5384358 : True = term245.
Proof. exact (SYM (@lem5384357)). Qed.
Lemma lem5384359 : term245.
Proof. exact (EQ_MP (@lem5384358) (@lem0)). Qed.
Lemma lem5384360 : term425.
Proof. exact (@lem5384349 (@lem5384359)). Qed.
Lemma lem5384362 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5384363 : term245 = term246.
Proof. exact (@lem5384362 (NUMERAL 0) term44). Qed.
Lemma lem5384364 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5384365 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5384366 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5384365 h1) (fun h1 : term246 = True => @lem5384364)). Qed.
Lemma lem5384367 : term246 = True.
Proof. exact (EQ_MP (@lem5384366) (@lem5384364)). Qed.
Lemma lem5384368 : term245 = True.
Proof. exact (TRANS (@lem5384363) (@lem5384367)). Qed.
Lemma lem5384369 : True = term245.
Proof. exact (SYM (@lem5384368)). Qed.
Lemma lem5384370 : term245.
Proof. exact (EQ_MP (@lem5384369) (@lem0)). Qed.
Lemma lem5384371 : term426.
Proof. exact (@lem5384360 (@lem5384370)). Qed.
Lemma lem5384373 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5384374 : term210 = term211.
Proof. exact (@lem5384373 term44 term44). Qed.
Lemma lem5384375 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5384376 : term213 = term44.
Proof. exact (EQ_MP (@lem5384375) (@lem940073)). Qed.
Lemma lem5384377 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5384378 : term211 = term138.
Proof. exact (MK_COMB (@lem5384377) (@lem5384376)). Qed.
Lemma lem5384379 : term210 = term138.
Proof. exact (TRANS (@lem5384374) (@lem5384378)). Qed.
Lemma lem5384381 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5384382 : term302 = term305.
Proof. exact (@lem5384381 term44 term44). Qed.
Lemma lem5384383 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5384384 : term213 = term44.
Proof. exact (EQ_MP (@lem5384383) (@lem940073)). Qed.
Lemma lem5384385 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5384386 : term211 = term138.
Proof. exact (MK_COMB (@lem5384385) (@lem5384384)). Qed.
Lemma lem5384387 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5384388 : term305 = term201.
Proof. exact (MK_COMB (@lem5384387) (@lem5384386)). Qed.
Lemma lem5384389 : term302 = term201.
Proof. exact (TRANS (@lem5384382) (@lem5384388)). Qed.
Lemma lem5384390 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5384391 : term427 = term419.
Proof. exact (MK_COMB (@lem5384390) (@lem5384389)). Qed.
Lemma lem5384392 : term428 = term421.
Proof. exact (MK_COMB (@lem5384391) (@lem5384379)). Qed.
Lemma lem5384394 (m : nat) : (term429 m) = term128.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5384395 : term421 = term128.
Proof. exact (@lem5384394 term44). Qed.
Lemma lem5384396 : term428 = term128.
Proof. exact (TRANS (@lem5384392) (@lem5384395)). Qed.
Lemma lem5384397 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5384398 : term430 = term431.
Proof. exact (MK_COMB (@lem5384397) (@lem5384396)). Qed.
Lemma lem5384399 : term138 = term138.
Proof. exact (eq_refl term138). Qed.
Lemma lem5384400 : term432 = term398.
Proof. exact (MK_COMB (@lem5384398) (@lem5384399)). Qed.
Lemma lem5384402 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5384403 : term398 = term128.
Proof. exact (@lem5384402 term44). Qed.
Lemma lem5384404 : term432 = term128.
Proof. exact (TRANS (@lem5384400) (@lem5384403)). Qed.
Lemma lem5384406 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5384407 : term210 = term211.
Proof. exact (@lem5384406 term44 term44). Qed.
Lemma lem5384408 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5384409 : term213 = term44.
Proof. exact (EQ_MP (@lem5384408) (@lem940073)). Qed.
Lemma lem5384410 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5384411 : term211 = term138.
Proof. exact (MK_COMB (@lem5384410) (@lem5384409)). Qed.
Lemma lem5384412 : term210 = term138.
Proof. exact (TRANS (@lem5384407) (@lem5384411)). Qed.
Lemma lem5384413 : term431 = term431.
Proof. exact (eq_refl term431). Qed.
Lemma lem5384414 : term433 = term398.
Proof. exact (MK_COMB (@lem5384413) (@lem5384412)). Qed.
Lemma lem5384416 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5384417 : term398 = term128.
Proof. exact (@lem5384416 term44). Qed.
Lemma lem5384418 : term433 = term128.
Proof. exact (TRANS (@lem5384414) (@lem5384417)). Qed.
Lemma lem5384419 : term128 = term433.
Proof. exact (SYM (@lem5384418)). Qed.
Lemma lem5384420 : term432 = term433.
Proof. exact (TRANS (@lem5384404) (@lem5384419)). Qed.
Lemma lem5384421 : term422 = term198.
Proof. exact (@lem5384371 (@lem5384420)). Qed.
Lemma lem5384422 : term421 = term198.
Proof. exact (TRANS (@lem5384337) (@lem5384421)). Qed.
Lemma lem5384424 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5384425 : term198 = term128.
Proof. exact (@lem5384424 term128). Qed.
Lemma lem5384426 : term421 = term128.
Proof. exact (TRANS (@lem5384422) (@lem5384425)). Qed.
Lemma lem5384427 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5384428 : term434 = term431.
Proof. exact (MK_COMB (@lem5384427) (@lem5384426)). Qed.
Lemma lem5384429 (_69793 : int) : (real_of_int _69793) = (real_of_int _69793).
Proof. exact (eq_refl (real_of_int _69793)). Qed.
Lemma lem5384430 (_69793 : int) : (term418 _69793) = (term435 _69793).
Proof. exact (MK_COMB (@lem5384428) (@lem5384429 _69793)). Qed.
Lemma lem5384431 (_69793 : int) : (term464 _69793) = (term435 _69793).
Proof. exact (TRANS (@lem5384328 _69793) (@lem5384430 _69793)). Qed.
Lemma lem5384432 (_69793 : int) : (term435 _69793) = term128.
Proof. exact (@lem1982719 (real_of_int _69793)). Qed.
Lemma lem5384433 (_69793 : int) : (term464 _69793) = term128.
Proof. exact (TRANS (@lem5384431 _69793) (@lem5384432 _69793)). Qed.
Lemma lem5384434 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5384435 (_69793 : int) : (term465 _69793) = term178.
Proof. exact (MK_COMB (@lem5384434) (@lem5384433 _69793)). Qed.
Lemma lem5384436 : term201 = term201.
Proof. exact (eq_refl term201). Qed.
Lemma lem5384437 (_69793 : int) : (term463 _69793) = term437.
Proof. exact (MK_COMB (@lem5384435 _69793) (@lem5384436)). Qed.
Lemma lem5384438 (_69793 : int) : (term462 _69793) = term437.
Proof. exact (TRANS (@lem5384327 _69793) (@lem5384437 _69793)). Qed.
Lemma lem5384439 : term437 = term201.
Proof. exact (@lem1982721 term201). Qed.
Lemma lem5384440 (_69793 : int) : (term462 _69793) = term201.
Proof. exact (TRANS (@lem5384438 _69793) (@lem5384439)). Qed.
Lemma lem5384441 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5384442 (_69793 : int) : (term466 _69793) = term439.
Proof. exact (MK_COMB (@lem5384441) (@lem5384440 _69793)). Qed.
Lemma lem5384443 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5384444 (_69793 : int) : (term461 _69793) = term440.
Proof. exact (MK_COMB (@lem5384442 _69793) (@lem5384443)). Qed.
Lemma lem5384445 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term452 _69794 _69795 _69793) : term440.
Proof. exact (EQ_MP (@lem5384444 _69793) (@lem5384326 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384447 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5384448 : term440 = term441.
Proof. exact (@lem5384447 term128 term201). Qed.
Lemma lem5384450 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5384451 : term201 = term202.
Proof. exact (@lem5384450 term44). Qed.
Lemma lem5384453 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5384454 : term128 = term198.
Proof. exact (@lem5384453 (NUMERAL 0)). Qed.
Lemma lem5384455 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5384456 : term130 = term442.
Proof. exact (MK_COMB (@lem5384455) (@lem5384454)). Qed.
Lemma lem5384457 : term441 = term443.
Proof. exact (MK_COMB (@lem5384456) (@lem5384451)). Qed.
Lemma lem5384458 : term444.
Proof. exact (@lem1980026 term128 term138 term201 term138). Qed.
Lemma lem5384460 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5384461 : term245 = term246.
Proof. exact (@lem5384460 (NUMERAL 0) term44). Qed.
Lemma lem5384462 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5384463 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5384464 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5384463 h1) (fun h1 : term246 = True => @lem5384462)). Qed.
Lemma lem5384465 : term246 = True.
Proof. exact (EQ_MP (@lem5384464) (@lem5384462)). Qed.
Lemma lem5384466 : term245 = True.
Proof. exact (TRANS (@lem5384461) (@lem5384465)). Qed.
Lemma lem5384467 : True = term245.
Proof. exact (SYM (@lem5384466)). Qed.
Lemma lem5384468 : term245.
Proof. exact (EQ_MP (@lem5384467) (@lem0)). Qed.
Lemma lem5384469 : term445.
Proof. exact (@lem5384458 (@lem5384468)). Qed.
Lemma lem5384471 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5384472 : term245 = term246.
Proof. exact (@lem5384471 (NUMERAL 0) term44). Qed.
Lemma lem5384473 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5384474 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5384475 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5384474 h1) (fun h1 : term246 = True => @lem5384473)). Qed.
Lemma lem5384476 : term246 = True.
Proof. exact (EQ_MP (@lem5384475) (@lem5384473)). Qed.
Lemma lem5384477 : term245 = True.
Proof. exact (TRANS (@lem5384472) (@lem5384476)). Qed.
Lemma lem5384478 : True = term245.
Proof. exact (SYM (@lem5384477)). Qed.
Lemma lem5384479 : term245.
Proof. exact (EQ_MP (@lem5384478) (@lem0)). Qed.
Lemma lem5384480 : term443 = term446.
Proof. exact (@lem5384469 (@lem5384479)). Qed.
Lemma lem5384482 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5384483 : term302 = term305.
Proof. exact (@lem5384482 term44 term44). Qed.
Lemma lem5384484 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5384485 : term213 = term44.
Proof. exact (EQ_MP (@lem5384484) (@lem940073)). Qed.
Lemma lem5384486 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5384487 : term211 = term138.
Proof. exact (MK_COMB (@lem5384486) (@lem5384485)). Qed.
Lemma lem5384488 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5384489 : term305 = term201.
Proof. exact (MK_COMB (@lem5384488) (@lem5384487)). Qed.
Lemma lem5384490 : term302 = term201.
Proof. exact (TRANS (@lem5384483) (@lem5384489)). Qed.
Lemma lem5384492 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5384493 : term398 = term128.
Proof. exact (@lem5384492 term44). Qed.
Lemma lem5384494 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5384495 : term447 = term130.
Proof. exact (MK_COMB (@lem5384494) (@lem5384493)). Qed.
Lemma lem5384496 : term446 = term441.
Proof. exact (MK_COMB (@lem5384495) (@lem5384490)). Qed.
Lemma lem5384498 (m : nat) (n : nat) : (term448 m n) = (term449 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5384499 : term441 = term450.
Proof. exact (@lem5384498 (NUMERAL 0) term44). Qed.
Lemma lem5384500 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5384501 (h1 : term247 = (BIT1 0)) : (term44 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5384502 : (term247 = (BIT1 0)) = ((term44 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5384501 h1) (fun h1 : (term44 = (NUMERAL 0)) = False => @lem5384500)). Qed.
Lemma lem5384503 : (term44 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5384502) (@lem5384500)). Qed.
Lemma lem5384504 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5384505 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5384506 : term451 = (and True).
Proof. exact (MK_COMB (@lem5384505) (@lem5384504)). Qed.
Lemma lem5384507 : term450 = (True /\ False).
Proof. exact (MK_COMB (@lem5384506) (@lem5384503)). Qed.
Lemma lem5384509 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5384510 : term450 = False.
Proof. exact (TRANS (@lem5384507) (@lem5384509)). Qed.
Lemma lem5384511 : term441 = False.
Proof. exact (TRANS (@lem5384499) (@lem5384510)). Qed.
Lemma lem5384512 : term446 = False.
Proof. exact (TRANS (@lem5384496) (@lem5384511)). Qed.
Lemma lem5384513 : term443 = False.
Proof. exact (TRANS (@lem5384480) (@lem5384512)). Qed.
Lemma lem5384514 : term441 = False.
Proof. exact (TRANS (@lem5384457) (@lem5384513)). Qed.
Lemma lem5384515 : term440 = False.
Proof. exact (TRANS (@lem5384448) (@lem5384514)). Qed.
Lemma lem5384516 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term452 _69794 _69795 _69793) : False.
Proof. exact (EQ_MP (@lem5384515) (@lem5384445 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384517 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term383 _69794 _69795 _69793) : False.
Proof. exact (or_elim (@lem5383867 _69794 _69795 _69793 h1) (fun h0 : term389 _69794 _69795 _69793 => @lem5384221 _69794 _69795 _69793 h0) (fun h0 : term452 _69794 _69795 _69793 => @lem5384516 _69794 _69795 _69793 h0)). Qed.
Lemma lem5384518 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term379 _69794 _69795 _69793) : term379 _69794 _69795 _69793.
Proof. exact (h1). Qed.
Lemma lem5384519 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term467 _69794 _69795 _69793) : term467 _69794 _69795 _69793.
Proof. exact (h1). Qed.
Lemma lem5384520 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term467 _69794 _69795 _69793) : term380 _69794 _69795 _69793.
Proof. exact (proj2 (@lem5384519 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384522 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term467 _69794 _69795 _69793) : term367 _69794 _69795 _69793.
Proof. exact (proj2 (@lem5384520 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384524 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term467 _69794 _69795 _69793) : term354 _69794 _69795 _69793.
Proof. exact (proj2 (@lem5384522 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384526 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term467 _69794 _69795 _69793) : term342 _69794 _69795 _69793.
Proof. exact (proj2 (@lem5384524 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384527 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term467 _69794 _69795 _69793) : (term232 _69793 _69794 _69795) = term128.
Proof. exact (proj1 (@lem5384524 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384528 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term467 _69794 _69795 _69793) : term327 _69793.
Proof. exact (proj2 (@lem5384526 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384529 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term467 _69794 _69795 _69793) : term312 _69794 _69795.
Proof. exact (proj1 (@lem5384526 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384531 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5384532 : term390 = term245.
Proof. exact (@lem5384531 term128 term138). Qed.
Lemma lem5384534 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5384535 : term138 = term237.
Proof. exact (@lem5384534 term44). Qed.
Lemma lem5384537 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5384538 : term128 = term198.
Proof. exact (@lem5384537 (NUMERAL 0)). Qed.
Lemma lem5384539 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5384540 : term391 = term392.
Proof. exact (MK_COMB (@lem5384539) (@lem5384538)). Qed.
Lemma lem5384541 : term245 = term393.
Proof. exact (MK_COMB (@lem5384540) (@lem5384535)). Qed.
Lemma lem5384542 : term394.
Proof. exact (@lem1980255 term128 term138 term138 term138). Qed.
Lemma lem5384544 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5384545 : term245 = term246.
Proof. exact (@lem5384544 (NUMERAL 0) term44). Qed.
Lemma lem5384546 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5384547 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5384548 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5384547 h1) (fun h1 : term246 = True => @lem5384546)). Qed.
Lemma lem5384549 : term246 = True.
Proof. exact (EQ_MP (@lem5384548) (@lem5384546)). Qed.
Lemma lem5384550 : term245 = True.
Proof. exact (TRANS (@lem5384545) (@lem5384549)). Qed.
Lemma lem5384551 : True = term245.
Proof. exact (SYM (@lem5384550)). Qed.
Lemma lem5384552 : term245.
Proof. exact (EQ_MP (@lem5384551) (@lem0)). Qed.
Lemma lem5384553 : term395.
Proof. exact (@lem5384542 (@lem5384552)). Qed.
Lemma lem5384555 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5384556 : term245 = term246.
Proof. exact (@lem5384555 (NUMERAL 0) term44). Qed.
Lemma lem5384557 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5384558 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5384559 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5384558 h1) (fun h1 : term246 = True => @lem5384557)). Qed.
Lemma lem5384560 : term246 = True.
Proof. exact (EQ_MP (@lem5384559) (@lem5384557)). Qed.
Lemma lem5384561 : term245 = True.
Proof. exact (TRANS (@lem5384556) (@lem5384560)). Qed.
Lemma lem5384562 : True = term245.
Proof. exact (SYM (@lem5384561)). Qed.
Lemma lem5384563 : term245.
Proof. exact (EQ_MP (@lem5384562) (@lem0)). Qed.
Lemma lem5384564 : term393 = term396.
Proof. exact (@lem5384553 (@lem5384563)). Qed.
Lemma lem5384566 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5384567 : term210 = term211.
Proof. exact (@lem5384566 term44 term44). Qed.
Lemma lem5384568 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5384569 : term213 = term44.
Proof. exact (EQ_MP (@lem5384568) (@lem940073)). Qed.
Lemma lem5384570 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5384571 : term211 = term138.
Proof. exact (MK_COMB (@lem5384570) (@lem5384569)). Qed.
Lemma lem5384572 : term210 = term138.
Proof. exact (TRANS (@lem5384567) (@lem5384571)). Qed.
Lemma lem5384574 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5384575 : term398 = term128.
Proof. exact (@lem5384574 term44). Qed.
Lemma lem5384576 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5384577 : term399 = term391.
Proof. exact (MK_COMB (@lem5384576) (@lem5384575)). Qed.
Lemma lem5384578 : term396 = term245.
Proof. exact (MK_COMB (@lem5384577) (@lem5384572)). Qed.
Lemma lem5384580 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5384581 : term245 = term246.
Proof. exact (@lem5384580 (NUMERAL 0) term44). Qed.
Lemma lem5384582 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5384583 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5384584 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5384583 h1) (fun h1 : term246 = True => @lem5384582)). Qed.
Lemma lem5384585 : term246 = True.
Proof. exact (EQ_MP (@lem5384584) (@lem5384582)). Qed.
Lemma lem5384586 : term245 = True.
Proof. exact (TRANS (@lem5384581) (@lem5384585)). Qed.
Lemma lem5384587 : term396 = True.
Proof. exact (TRANS (@lem5384578) (@lem5384586)). Qed.
Lemma lem5384588 : term393 = True.
Proof. exact (TRANS (@lem5384564) (@lem5384587)). Qed.
Lemma lem5384589 : term245 = True.
Proof. exact (TRANS (@lem5384541) (@lem5384588)). Qed.
Lemma lem5384590 : term390 = True.
Proof. exact (TRANS (@lem5384532) (@lem5384589)). Qed.
Lemma lem5384591 : True = term390.
Proof. exact (SYM (@lem5384590)). Qed.
Lemma lem5384592 : term390.
Proof. exact (EQ_MP (@lem5384591) (@lem0)). Qed.
Lemma lem5384593 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term467 _69794 _69795 _69793) : term468 _69793.
Proof. exact (conj (@lem5384592) (@lem5384528 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384595 (x : real) (y : real) : term401 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5384596 (_69793 : int) : term469 _69793.
Proof. exact (@lem5384595 term138 (term324 _69793)). Qed.
Lemma lem5384597 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term467 _69794 _69795 _69793) : term470 _69793.
Proof. exact (@lem5384596 _69793 (@lem5384593 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384598 (_69793 : int) : (term471 _69793) = (term324 _69793).
Proof. exact (@lem1982733 (term324 _69793)). Qed.
Lemma lem5384599 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5384600 (_69793 : int) : (term472 _69793) = (term326 _69793).
Proof. exact (MK_COMB (@lem5384599) (@lem5384598 _69793)). Qed.
Lemma lem5384601 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5384602 (_69793 : int) : (term470 _69793) = (term327 _69793).
Proof. exact (MK_COMB (@lem5384600 _69793) (@lem5384601)). Qed.
Lemma lem5384603 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term467 _69794 _69795 _69793) : term327 _69793.
Proof. exact (EQ_MP (@lem5384602 _69793) (@lem5384597 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384605 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5384606 : term390 = term245.
Proof. exact (@lem5384605 term128 term138). Qed.
Lemma lem5384608 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5384609 : term138 = term237.
Proof. exact (@lem5384608 term44). Qed.
Lemma lem5384611 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5384612 : term128 = term198.
Proof. exact (@lem5384611 (NUMERAL 0)). Qed.
Lemma lem5384613 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5384614 : term391 = term392.
Proof. exact (MK_COMB (@lem5384613) (@lem5384612)). Qed.
Lemma lem5384615 : term245 = term393.
Proof. exact (MK_COMB (@lem5384614) (@lem5384609)). Qed.
Lemma lem5384616 : term394.
Proof. exact (@lem1980255 term128 term138 term138 term138). Qed.
Lemma lem5384618 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5384619 : term245 = term246.
Proof. exact (@lem5384618 (NUMERAL 0) term44). Qed.
Lemma lem5384620 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5384621 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5384622 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5384621 h1) (fun h1 : term246 = True => @lem5384620)). Qed.
Lemma lem5384623 : term246 = True.
Proof. exact (EQ_MP (@lem5384622) (@lem5384620)). Qed.
Lemma lem5384624 : term245 = True.
Proof. exact (TRANS (@lem5384619) (@lem5384623)). Qed.
Lemma lem5384625 : True = term245.
Proof. exact (SYM (@lem5384624)). Qed.
Lemma lem5384626 : term245.
Proof. exact (EQ_MP (@lem5384625) (@lem0)). Qed.
Lemma lem5384627 : term395.
Proof. exact (@lem5384616 (@lem5384626)). Qed.
Lemma lem5384629 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5384630 : term245 = term246.
Proof. exact (@lem5384629 (NUMERAL 0) term44). Qed.
Lemma lem5384631 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5384632 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5384633 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5384632 h1) (fun h1 : term246 = True => @lem5384631)). Qed.
Lemma lem5384634 : term246 = True.
Proof. exact (EQ_MP (@lem5384633) (@lem5384631)). Qed.
Lemma lem5384635 : term245 = True.
Proof. exact (TRANS (@lem5384630) (@lem5384634)). Qed.
Lemma lem5384636 : True = term245.
Proof. exact (SYM (@lem5384635)). Qed.
Lemma lem5384637 : term245.
Proof. exact (EQ_MP (@lem5384636) (@lem0)). Qed.
Lemma lem5384638 : term393 = term396.
Proof. exact (@lem5384627 (@lem5384637)). Qed.
Lemma lem5384640 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5384641 : term210 = term211.
Proof. exact (@lem5384640 term44 term44). Qed.
Lemma lem5384642 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5384643 : term213 = term44.
Proof. exact (EQ_MP (@lem5384642) (@lem940073)). Qed.
Lemma lem5384644 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5384645 : term211 = term138.
Proof. exact (MK_COMB (@lem5384644) (@lem5384643)). Qed.
Lemma lem5384646 : term210 = term138.
Proof. exact (TRANS (@lem5384641) (@lem5384645)). Qed.
Lemma lem5384648 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5384649 : term398 = term128.
Proof. exact (@lem5384648 term44). Qed.
Lemma lem5384650 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5384651 : term399 = term391.
Proof. exact (MK_COMB (@lem5384650) (@lem5384649)). Qed.
Lemma lem5384652 : term396 = term245.
Proof. exact (MK_COMB (@lem5384651) (@lem5384646)). Qed.
Lemma lem5384654 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5384655 : term245 = term246.
Proof. exact (@lem5384654 (NUMERAL 0) term44). Qed.
Lemma lem5384656 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5384657 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5384658 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5384657 h1) (fun h1 : term246 = True => @lem5384656)). Qed.
Lemma lem5384659 : term246 = True.
Proof. exact (EQ_MP (@lem5384658) (@lem5384656)). Qed.
Lemma lem5384660 : term245 = True.
Proof. exact (TRANS (@lem5384655) (@lem5384659)). Qed.
Lemma lem5384661 : term396 = True.
Proof. exact (TRANS (@lem5384652) (@lem5384660)). Qed.
Lemma lem5384662 : term393 = True.
Proof. exact (TRANS (@lem5384638) (@lem5384661)). Qed.
Lemma lem5384663 : term245 = True.
Proof. exact (TRANS (@lem5384615) (@lem5384662)). Qed.
Lemma lem5384664 : term390 = True.
Proof. exact (TRANS (@lem5384606) (@lem5384663)). Qed.
Lemma lem5384665 : True = term390.
Proof. exact (SYM (@lem5384664)). Qed.
Lemma lem5384666 : term390.
Proof. exact (EQ_MP (@lem5384665) (@lem0)). Qed.
Lemma lem5384667 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term467 _69794 _69795 _69793) : term473 _69794 _69795.
Proof. exact (conj (@lem5384666) (@lem5384529 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384669 (x : real) (y : real) : term401 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5384670 (_69794 : int) (_69795 : int) : term474 _69794 _69795.
Proof. exact (@lem5384669 term138 (term309 _69794 _69795)). Qed.
Lemma lem5384671 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term467 _69794 _69795 _69793) : term475 _69794 _69795.
Proof. exact (@lem5384670 _69794 _69795 (@lem5384667 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384672 (_69794 : int) (_69795 : int) : (term476 _69794 _69795) = (term309 _69794 _69795).
Proof. exact (@lem1982733 (term309 _69794 _69795)). Qed.
Lemma lem5384673 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5384674 (_69794 : int) (_69795 : int) : (term477 _69794 _69795) = (term311 _69794 _69795).
Proof. exact (MK_COMB (@lem5384673) (@lem5384672 _69794 _69795)). Qed.
Lemma lem5384675 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5384676 (_69794 : int) (_69795 : int) : (term475 _69794 _69795) = (term312 _69794 _69795).
Proof. exact (MK_COMB (@lem5384674 _69794 _69795) (@lem5384675)). Qed.
Lemma lem5384677 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term467 _69794 _69795 _69793) : term312 _69794 _69795.
Proof. exact (EQ_MP (@lem5384676 _69794 _69795) (@lem5384671 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384679 (y : real) : term453 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5384680 (_69793 : int) (_69794 : int) (_69795 : int) : term478 _69793 _69794 _69795.
Proof. exact (@lem5384679 (term232 _69793 _69794 _69795)). Qed.
Lemma lem5384681 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term467 _69794 _69795 _69793) : term479 _69793 _69794 _69795.
Proof. exact (@lem5384680 _69793 _69794 _69795 (@lem5384527 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384682 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term467 _69794 _69795 _69793) : term480 _69793 _69794 _69795.
Proof. exact (@lem5384681 _69794 _69795 _69793 h1 term138). Qed.
Lemma lem5384683 (_69793 : int) (_69794 : int) (_69795 : int) : (term480 _69793 _69794 _69795) = ((term481 _69793 _69794 _69795) = term128).
Proof. exact (eq_refl (term480 _69793 _69794 _69795)). Qed.
Lemma lem5384684 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term467 _69794 _69795 _69793) : (term481 _69793 _69794 _69795) = term128.
Proof. exact (EQ_MP (@lem5384683 _69793 _69794 _69795) (@lem5384682 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384685 (_69793 : int) (_69794 : int) (_69795 : int) : (term481 _69793 _69794 _69795) = (term232 _69793 _69794 _69795).
Proof. exact (@lem1982733 (term232 _69793 _69794 _69795)). Qed.
Lemma lem5384686 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5384687 (_69793 : int) (_69794 : int) (_69795 : int) : (term482 _69793 _69794 _69795) = (term234 _69793 _69794 _69795).
Proof. exact (MK_COMB (@lem5384686) (@lem5384685 _69793 _69794 _69795)). Qed.
Lemma lem5384688 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5384689 (_69793 : int) (_69794 : int) (_69795 : int) : ((term481 _69793 _69794 _69795) = term128) = ((term232 _69793 _69794 _69795) = term128).
Proof. exact (MK_COMB (@lem5384687 _69793 _69794 _69795) (@lem5384688)). Qed.
Lemma lem5384690 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term467 _69794 _69795 _69793) : (term232 _69793 _69794 _69795) = term128.
Proof. exact (EQ_MP (@lem5384689 _69793 _69794 _69795) (@lem5384684 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384691 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term467 _69794 _69795 _69793) : term483 _69793 _69794 _69795.
Proof. exact (conj (@lem5384690 _69794 _69795 _69793 h1) (@lem5384677 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384693 (x : real) (y : real) : term459 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5384694 (_69793 : int) (_69794 : int) (_69795 : int) : term484 _69793 _69794 _69795.
Proof. exact (@lem5384693 (term232 _69793 _69794 _69795) (term309 _69794 _69795)). Qed.
Lemma lem5384695 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term467 _69794 _69795 _69793) : term485 _69793 _69794 _69795.
Proof. exact (@lem5384694 _69793 _69794 _69795 (@lem5384691 _69794 _69795 _69793 h1)). Qed.
Lemma lem5384696 (_69793 : int) (_69794 : int) (_69795 : int) : (term486 _69793 _69794 _69795) = (term487 _69793 _69794 _69795).
Proof. exact (@lem1982755 (term228 _69793) (term230 _69794 _69795) (term309 _69794 _69795)). Qed.
Lemma lem5384697 (_69794 : int) (_69795 : int) : (term488 _69794 _69795) = (term489 _69794 _69795).
Proof. exact (@lem1982753 (term228 _69794) (real_of_int _69794) (term140 _69795) (term308 _69795)). Qed.
Lemma lem5384698 (_69794 : int) : (term417 _69794) = (term418 _69794).
Proof. exact (@lem1982713 term201 (real_of_int _69794)). Qed.
Lemma lem5384700 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5384701 : term138 = term237.
Proof. exact (@lem5384700 term44). Qed.
Lemma lem5384703 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5384704 : term201 = term202.
Proof. exact (@lem5384703 term44). Qed.
Lemma lem5384705 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5384706 : term419 = term420.
Proof. exact (MK_COMB (@lem5384705) (@lem5384704)). Qed.
Lemma lem5384707 : term421 = term422.
Proof. exact (MK_COMB (@lem5384706) (@lem5384701)). Qed.
Lemma lem5384708 : term423.
Proof. exact (@lem1981473 term201 term138 term138 term138 term128 term138). Qed.
Lemma lem5384710 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5384711 : term245 = term246.
Proof. exact (@lem5384710 (NUMERAL 0) term44). Qed.
Lemma lem5384712 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5384713 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5384714 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5384713 h1) (fun h1 : term246 = True => @lem5384712)). Qed.
Lemma lem5384715 : term246 = True.
Proof. exact (EQ_MP (@lem5384714) (@lem5384712)). Qed.
Lemma lem5384716 : term245 = True.
Proof. exact (TRANS (@lem5384711) (@lem5384715)). Qed.
Lemma lem5384717 : True = term245.
Proof. exact (SYM (@lem5384716)). Qed.
Lemma lem5384718 : term245.
Proof. exact (EQ_MP (@lem5384717) (@lem0)). Qed.
Lemma lem5384719 : term424.
Proof. exact (@lem5384708 (@lem5384718)). Qed.
Lemma lem5384721 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5384722 : term245 = term246.
Proof. exact (@lem5384721 (NUMERAL 0) term44). Qed.
Lemma lem5384723 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5384724 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5384725 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5384724 h1) (fun h1 : term246 = True => @lem5384723)). Qed.
Lemma lem5384726 : term246 = True.
Proof. exact (EQ_MP (@lem5384725) (@lem5384723)). Qed.
Lemma lem5384727 : term245 = True.
Proof. exact (TRANS (@lem5384722) (@lem5384726)). Qed.
Lemma lem5384728 : True = term245.
Proof. exact (SYM (@lem5384727)). Qed.
Lemma lem5384729 : term245.
Proof. exact (EQ_MP (@lem5384728) (@lem0)). Qed.
Lemma lem5384730 : term425.
Proof. exact (@lem5384719 (@lem5384729)). Qed.
Lemma lem5384732 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5384733 : term245 = term246.
Proof. exact (@lem5384732 (NUMERAL 0) term44). Qed.
Lemma lem5384734 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5384735 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5384736 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5384735 h1) (fun h1 : term246 = True => @lem5384734)). Qed.
Lemma lem5384737 : term246 = True.
Proof. exact (EQ_MP (@lem5384736) (@lem5384734)). Qed.
Lemma lem5384738 : term245 = True.
Proof. exact (TRANS (@lem5384733) (@lem5384737)). Qed.
Lemma lem5384739 : True = term245.
Proof. exact (SYM (@lem5384738)). Qed.
Lemma lem5384740 : term245.
Proof. exact (EQ_MP (@lem5384739) (@lem0)). Qed.
Lemma lem5384741 : term426.
Proof. exact (@lem5384730 (@lem5384740)). Qed.
Lemma lem5384743 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5384744 : term210 = term211.
Proof. exact (@lem5384743 term44 term44). Qed.
Lemma lem5384745 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5384746 : term213 = term44.
Proof. exact (EQ_MP (@lem5384745) (@lem940073)). Qed.
Lemma lem5384747 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5384748 : term211 = term138.
Proof. exact (MK_COMB (@lem5384747) (@lem5384746)). Qed.
Lemma lem5384749 : term210 = term138.
Proof. exact (TRANS (@lem5384744) (@lem5384748)). Qed.
Lemma lem5384751 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5384752 : term302 = term305.
Proof. exact (@lem5384751 term44 term44). Qed.
Lemma lem5384753 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5384754 : term213 = term44.
Proof. exact (EQ_MP (@lem5384753) (@lem940073)). Qed.
Lemma lem5384755 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5384756 : term211 = term138.
Proof. exact (MK_COMB (@lem5384755) (@lem5384754)). Qed.
Lemma lem5384757 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5384758 : term305 = term201.
Proof. exact (MK_COMB (@lem5384757) (@lem5384756)). Qed.
Lemma lem5384759 : term302 = term201.
Proof. exact (TRANS (@lem5384752) (@lem5384758)). Qed.
Lemma lem5384760 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5384761 : term427 = term419.
Proof. exact (MK_COMB (@lem5384760) (@lem5384759)). Qed.
Lemma lem5384762 : term428 = term421.
Proof. exact (MK_COMB (@lem5384761) (@lem5384749)). Qed.
Lemma lem5384764 (m : nat) : (term429 m) = term128.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5384765 : term421 = term128.
Proof. exact (@lem5384764 term44). Qed.
Lemma lem5384766 : term428 = term128.
Proof. exact (TRANS (@lem5384762) (@lem5384765)). Qed.
Lemma lem5384767 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5384768 : term430 = term431.
Proof. exact (MK_COMB (@lem5384767) (@lem5384766)). Qed.
Lemma lem5384769 : term138 = term138.
Proof. exact (eq_refl term138). Qed.
Lemma lem5384770 : term432 = term398.
Proof. exact (MK_COMB (@lem5384768) (@lem5384769)). Qed.
Lemma lem5384772 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5384773 : term398 = term128.
Proof. exact (@lem5384772 term44). Qed.
Lemma lem5384774 : term432 = term128.
Proof. exact (TRANS (@lem5384770) (@lem5384773)). Qed.
Lemma lem5384776 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5384777 : term210 = term211.
Proof. exact (@lem5384776 term44 term44). Qed.
Lemma lem5384778 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5384779 : term213 = term44.
Proof. exact (EQ_MP (@lem5384778) (@lem940073)). Qed.
Lemma lem5384780 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5384781 : term211 = term138.
Proof. exact (MK_COMB (@lem5384780) (@lem5384779)). Qed.
Lemma lem5384782 : term210 = term138.
Proof. exact (TRANS (@lem5384777) (@lem5384781)). Qed.
Lemma lem5384783 : term431 = term431.
Proof. exact (eq_refl term431). Qed.
Lemma lem5384784 : term433 = term398.
Proof. exact (MK_COMB (@lem5384783) (@lem5384782)). Qed.
Lemma lem5384786 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5384787 : term398 = term128.
Proof. exact (@lem5384786 term44). Qed.
Lemma lem5384788 : term433 = term128.
Proof. exact (TRANS (@lem5384784) (@lem5384787)). Qed.
Lemma lem5384789 : term128 = term433.
Proof. exact (SYM (@lem5384788)). Qed.
Lemma lem5384790 : term432 = term433.
Proof. exact (TRANS (@lem5384774) (@lem5384789)). Qed.
Lemma lem5384791 : term422 = term198.
Proof. exact (@lem5384741 (@lem5384790)). Qed.
Lemma lem5384792 : term421 = term198.
Proof. exact (TRANS (@lem5384707) (@lem5384791)). Qed.
Lemma lem5384794 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5384795 : term198 = term128.
Proof. exact (@lem5384794 term128). Qed.
Lemma lem5384796 : term421 = term128.
Proof. exact (TRANS (@lem5384792) (@lem5384795)). Qed.
Lemma lem5384797 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5384798 : term434 = term431.
Proof. exact (MK_COMB (@lem5384797) (@lem5384796)). Qed.
Lemma lem5384799 (_69794 : int) : (real_of_int _69794) = (real_of_int _69794).
Proof. exact (eq_refl (real_of_int _69794)). Qed.
Lemma lem5384800 (_69794 : int) : (term418 _69794) = (term435 _69794).
Proof. exact (MK_COMB (@lem5384798) (@lem5384799 _69794)). Qed.
Lemma lem5384801 (_69794 : int) : (term417 _69794) = (term435 _69794).
Proof. exact (TRANS (@lem5384698 _69794) (@lem5384800 _69794)). Qed.
Lemma lem5384802 (_69794 : int) : (term435 _69794) = term128.
Proof. exact (@lem1982719 (real_of_int _69794)). Qed.
Lemma lem5384803 (_69794 : int) : (term417 _69794) = term128.
Proof. exact (TRANS (@lem5384801 _69794) (@lem5384802 _69794)). Qed.
Lemma lem5384804 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5384805 (_69794 : int) : (term436 _69794) = term178.
Proof. exact (MK_COMB (@lem5384804) (@lem5384803 _69794)). Qed.
Lemma lem5384806 (_69795 : int) : (term490 _69795) = (term491 _69795).
Proof. exact (@lem1982753 (real_of_int _69795) (term228 _69795) term138 term201). Qed.
Lemma lem5384807 (_69795 : int) : (term464 _69795) = (term418 _69795).
Proof. exact (@lem1982715 term201 (real_of_int _69795)). Qed.
Lemma lem5384809 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5384810 : term138 = term237.
Proof. exact (@lem5384809 term44). Qed.
Lemma lem5384812 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5384813 : term201 = term202.
Proof. exact (@lem5384812 term44). Qed.
Lemma lem5384814 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5384815 : term419 = term420.
Proof. exact (MK_COMB (@lem5384814) (@lem5384813)). Qed.
Lemma lem5384816 : term421 = term422.
Proof. exact (MK_COMB (@lem5384815) (@lem5384810)). Qed.
Lemma lem5384817 : term423.
Proof. exact (@lem1981473 term201 term138 term138 term138 term128 term138). Qed.
Lemma lem5384819 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5384820 : term245 = term246.
Proof. exact (@lem5384819 (NUMERAL 0) term44). Qed.
Lemma lem5384821 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5384822 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5384823 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5384822 h1) (fun h1 : term246 = True => @lem5384821)). Qed.
Lemma lem5384824 : term246 = True.
Proof. exact (EQ_MP (@lem5384823) (@lem5384821)). Qed.
Lemma lem5384825 : term245 = True.
Proof. exact (TRANS (@lem5384820) (@lem5384824)). Qed.
Lemma lem5384826 : True = term245.
Proof. exact (SYM (@lem5384825)). Qed.
Lemma lem5384827 : term245.
Proof. exact (EQ_MP (@lem5384826) (@lem0)). Qed.
Lemma lem5384828 : term424.
Proof. exact (@lem5384817 (@lem5384827)). Qed.
Lemma lem5384830 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5384831 : term245 = term246.
Proof. exact (@lem5384830 (NUMERAL 0) term44). Qed.
Lemma lem5384832 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5384833 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5384834 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5384833 h1) (fun h1 : term246 = True => @lem5384832)). Qed.
Lemma lem5384835 : term246 = True.
Proof. exact (EQ_MP (@lem5384834) (@lem5384832)). Qed.
Lemma lem5384836 : term245 = True.
Proof. exact (TRANS (@lem5384831) (@lem5384835)). Qed.
Lemma lem5384837 : True = term245.
Proof. exact (SYM (@lem5384836)). Qed.
Lemma lem5384838 : term245.
Proof. exact (EQ_MP (@lem5384837) (@lem0)). Qed.
Lemma lem5384839 : term425.
Proof. exact (@lem5384828 (@lem5384838)). Qed.
Lemma lem5384841 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5384842 : term245 = term246.
Proof. exact (@lem5384841 (NUMERAL 0) term44). Qed.
Lemma lem5384843 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5384844 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5384845 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5384844 h1) (fun h1 : term246 = True => @lem5384843)). Qed.
Lemma lem5384846 : term246 = True.
Proof. exact (EQ_MP (@lem5384845) (@lem5384843)). Qed.
Lemma lem5384847 : term245 = True.
Proof. exact (TRANS (@lem5384842) (@lem5384846)). Qed.
Lemma lem5384848 : True = term245.
Proof. exact (SYM (@lem5384847)). Qed.
Lemma lem5384849 : term245.
Proof. exact (EQ_MP (@lem5384848) (@lem0)). Qed.
Lemma lem5384850 : term426.
Proof. exact (@lem5384839 (@lem5384849)). Qed.
Lemma lem5384852 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5384853 : term210 = term211.
Proof. exact (@lem5384852 term44 term44). Qed.
Lemma lem5384854 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5384855 : term213 = term44.
Proof. exact (EQ_MP (@lem5384854) (@lem940073)). Qed.
Lemma lem5384856 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5384857 : term211 = term138.
Proof. exact (MK_COMB (@lem5384856) (@lem5384855)). Qed.
Lemma lem5384858 : term210 = term138.
Proof. exact (TRANS (@lem5384853) (@lem5384857)). Qed.
Lemma lem5384860 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5384861 : term302 = term305.
Proof. exact (@lem5384860 term44 term44). Qed.
Lemma lem5384862 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5384863 : term213 = term44.
Proof. exact (EQ_MP (@lem5384862) (@lem940073)). Qed.
Lemma lem5384864 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5384865 : term211 = term138.
Proof. exact (MK_COMB (@lem5384864) (@lem5384863)). Qed.
Lemma lem5384866 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5384867 : term305 = term201.
Proof. exact (MK_COMB (@lem5384866) (@lem5384865)). Qed.
Lemma lem5384868 : term302 = term201.
Proof. exact (TRANS (@lem5384861) (@lem5384867)). Qed.
Lemma lem5384869 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5384870 : term427 = term419.
Proof. exact (MK_COMB (@lem5384869) (@lem5384868)). Qed.
Lemma lem5384871 : term428 = term421.
Proof. exact (MK_COMB (@lem5384870) (@lem5384858)). Qed.
Lemma lem5384873 (m : nat) : (term429 m) = term128.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5384874 : term421 = term128.
Proof. exact (@lem5384873 term44). Qed.
Lemma lem5384875 : term428 = term128.
Proof. exact (TRANS (@lem5384871) (@lem5384874)). Qed.
Lemma lem5384876 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5384877 : term430 = term431.
Proof. exact (MK_COMB (@lem5384876) (@lem5384875)). Qed.
Lemma lem5384878 : term138 = term138.
Proof. exact (eq_refl term138). Qed.
Lemma lem5384879 : term432 = term398.
Proof. exact (MK_COMB (@lem5384877) (@lem5384878)). Qed.
Lemma lem5384881 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5384882 : term398 = term128.
Proof. exact (@lem5384881 term44). Qed.
Lemma lem5384883 : term432 = term128.
Proof. exact (TRANS (@lem5384879) (@lem5384882)). Qed.
Lemma lem5384885 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5384886 : term210 = term211.
Proof. exact (@lem5384885 term44 term44). Qed.
Lemma lem5384887 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5384888 : term213 = term44.
Proof. exact (EQ_MP (@lem5384887) (@lem940073)). Qed.
Lemma lem5384889 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5384890 : term211 = term138.
Proof. exact (MK_COMB (@lem5384889) (@lem5384888)). Qed.
Lemma lem5384891 : term210 = term138.
Proof. exact (TRANS (@lem5384886) (@lem5384890)). Qed.
Lemma lem5384892 : term431 = term431.
Proof. exact (eq_refl term431). Qed.
Lemma lem5384893 : term433 = term398.
Proof. exact (MK_COMB (@lem5384892) (@lem5384891)). Qed.
Lemma lem5384895 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5384896 : term398 = term128.
Proof. exact (@lem5384895 term44). Qed.
Lemma lem5384897 : term433 = term128.
Proof. exact (TRANS (@lem5384893) (@lem5384896)). Qed.
Lemma lem5384898 : term128 = term433.
Proof. exact (SYM (@lem5384897)). Qed.
Lemma lem5384899 : term432 = term433.
Proof. exact (TRANS (@lem5384883) (@lem5384898)). Qed.
Lemma lem5384900 : term422 = term198.
Proof. exact (@lem5384850 (@lem5384899)). Qed.
Lemma lem5384901 : term421 = term198.
Proof. exact (TRANS (@lem5384816) (@lem5384900)). Qed.
Lemma lem5384903 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5384904 : term198 = term128.
Proof. exact (@lem5384903 term128). Qed.
Lemma lem5384905 : term421 = term128.
Proof. exact (TRANS (@lem5384901) (@lem5384904)). Qed.
Lemma lem5384906 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5384907 : term434 = term431.
Proof. exact (MK_COMB (@lem5384906) (@lem5384905)). Qed.
Lemma lem5384908 (_69795 : int) : (real_of_int _69795) = (real_of_int _69795).
Proof. exact (eq_refl (real_of_int _69795)). Qed.
Lemma lem5384909 (_69795 : int) : (term418 _69795) = (term435 _69795).
Proof. exact (MK_COMB (@lem5384907) (@lem5384908 _69795)). Qed.
Lemma lem5384910 (_69795 : int) : (term464 _69795) = (term435 _69795).
Proof. exact (TRANS (@lem5384807 _69795) (@lem5384909 _69795)). Qed.
Lemma lem5384911 (_69795 : int) : (term435 _69795) = term128.
Proof. exact (@lem1982719 (real_of_int _69795)). Qed.
Lemma lem5384912 (_69795 : int) : (term464 _69795) = term128.
Proof. exact (TRANS (@lem5384910 _69795) (@lem5384911 _69795)). Qed.
Lemma lem5384913 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5384914 (_69795 : int) : (term465 _69795) = term178.
Proof. exact (MK_COMB (@lem5384913) (@lem5384912 _69795)). Qed.
Lemma lem5384916 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5384917 : term201 = term202.
Proof. exact (@lem5384916 term44). Qed.
Lemma lem5384919 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5384920 : term138 = term237.
Proof. exact (@lem5384919 term44). Qed.
Lemma lem5384921 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5384922 : term238 = term239.
Proof. exact (MK_COMB (@lem5384921) (@lem5384920)). Qed.
Lemma lem5384923 : term492 = term493.
Proof. exact (MK_COMB (@lem5384922) (@lem5384917)). Qed.
Lemma lem5384924 : term494.
Proof. exact (@lem1981473 term138 term138 term201 term138 term128 term138). Qed.
Lemma lem5384926 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5384927 : term245 = term246.
Proof. exact (@lem5384926 (NUMERAL 0) term44). Qed.
Lemma lem5384928 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5384929 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5384930 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5384929 h1) (fun h1 : term246 = True => @lem5384928)). Qed.
Lemma lem5384931 : term246 = True.
Proof. exact (EQ_MP (@lem5384930) (@lem5384928)). Qed.
Lemma lem5384932 : term245 = True.
Proof. exact (TRANS (@lem5384927) (@lem5384931)). Qed.
Lemma lem5384933 : True = term245.
Proof. exact (SYM (@lem5384932)). Qed.
Lemma lem5384934 : term245.
Proof. exact (EQ_MP (@lem5384933) (@lem0)). Qed.
Lemma lem5384935 : term495.
Proof. exact (@lem5384924 (@lem5384934)). Qed.
Lemma lem5384937 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5384938 : term245 = term246.
Proof. exact (@lem5384937 (NUMERAL 0) term44). Qed.
Lemma lem5384939 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5384940 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5384941 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5384940 h1) (fun h1 : term246 = True => @lem5384939)). Qed.
Lemma lem5384942 : term246 = True.
Proof. exact (EQ_MP (@lem5384941) (@lem5384939)). Qed.
Lemma lem5384943 : term245 = True.
Proof. exact (TRANS (@lem5384938) (@lem5384942)). Qed.
Lemma lem5384944 : True = term245.
Proof. exact (SYM (@lem5384943)). Qed.
Lemma lem5384945 : term245.
Proof. exact (EQ_MP (@lem5384944) (@lem0)). Qed.
Lemma lem5384946 : term496.
Proof. exact (@lem5384935 (@lem5384945)). Qed.
Lemma lem5384948 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5384949 : term245 = term246.
Proof. exact (@lem5384948 (NUMERAL 0) term44). Qed.
Lemma lem5384950 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5384951 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5384952 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5384951 h1) (fun h1 : term246 = True => @lem5384950)). Qed.
Lemma lem5384953 : term246 = True.
Proof. exact (EQ_MP (@lem5384952) (@lem5384950)). Qed.
Lemma lem5384954 : term245 = True.
Proof. exact (TRANS (@lem5384949) (@lem5384953)). Qed.
Lemma lem5384955 : True = term245.
Proof. exact (SYM (@lem5384954)). Qed.
Lemma lem5384956 : term245.
Proof. exact (EQ_MP (@lem5384955) (@lem0)). Qed.
Lemma lem5384957 : term497.
Proof. exact (@lem5384946 (@lem5384956)). Qed.
Lemma lem5384959 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5384960 : term302 = term305.
Proof. exact (@lem5384959 term44 term44). Qed.
Lemma lem5384961 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5384962 : term213 = term44.
Proof. exact (EQ_MP (@lem5384961) (@lem940073)). Qed.
Lemma lem5384963 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5384964 : term211 = term138.
Proof. exact (MK_COMB (@lem5384963) (@lem5384962)). Qed.
Lemma lem5384965 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5384966 : term305 = term201.
Proof. exact (MK_COMB (@lem5384965) (@lem5384964)). Qed.
Lemma lem5384967 : term302 = term201.
Proof. exact (TRANS (@lem5384960) (@lem5384966)). Qed.
Lemma lem5384969 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5384970 : term210 = term211.
Proof. exact (@lem5384969 term44 term44). Qed.
Lemma lem5384971 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5384972 : term213 = term44.
Proof. exact (EQ_MP (@lem5384971) (@lem940073)). Qed.
Lemma lem5384973 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5384974 : term211 = term138.
Proof. exact (MK_COMB (@lem5384973) (@lem5384972)). Qed.
Lemma lem5384975 : term210 = term138.
Proof. exact (TRANS (@lem5384970) (@lem5384974)). Qed.
Lemma lem5384976 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5384977 : term251 = term238.
Proof. exact (MK_COMB (@lem5384976) (@lem5384975)). Qed.
Lemma lem5384978 : term498 = term492.
Proof. exact (MK_COMB (@lem5384977) (@lem5384967)). Qed.
Lemma lem5384980 (m : nat) : (term499 m) = term128.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem5384981 : term492 = term128.
Proof. exact (@lem5384980 term44). Qed.
Lemma lem5384982 : term498 = term128.
Proof. exact (TRANS (@lem5384978) (@lem5384981)). Qed.
Lemma lem5384983 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5384984 : term500 = term431.
Proof. exact (MK_COMB (@lem5384983) (@lem5384982)). Qed.
Lemma lem5384985 : term138 = term138.
Proof. exact (eq_refl term138). Qed.
Lemma lem5384986 : term501 = term398.
Proof. exact (MK_COMB (@lem5384984) (@lem5384985)). Qed.
Lemma lem5384988 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5384989 : term398 = term128.
Proof. exact (@lem5384988 term44). Qed.
Lemma lem5384990 : term501 = term128.
Proof. exact (TRANS (@lem5384986) (@lem5384989)). Qed.
Lemma lem5384992 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5384993 : term210 = term211.
Proof. exact (@lem5384992 term44 term44). Qed.
Lemma lem5384994 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5384995 : term213 = term44.
Proof. exact (EQ_MP (@lem5384994) (@lem940073)). Qed.
Lemma lem5384996 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5384997 : term211 = term138.
Proof. exact (MK_COMB (@lem5384996) (@lem5384995)). Qed.
Lemma lem5384998 : term210 = term138.
Proof. exact (TRANS (@lem5384993) (@lem5384997)). Qed.
Lemma lem5384999 : term431 = term431.
Proof. exact (eq_refl term431). Qed.
Lemma lem5385000 : term433 = term398.
Proof. exact (MK_COMB (@lem5384999) (@lem5384998)). Qed.
Lemma lem5385002 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5385003 : term398 = term128.
Proof. exact (@lem5385002 term44). Qed.
Lemma lem5385004 : term433 = term128.
Proof. exact (TRANS (@lem5385000) (@lem5385003)). Qed.
Lemma lem5385005 : term128 = term433.
Proof. exact (SYM (@lem5385004)). Qed.
Lemma lem5385006 : term501 = term433.
Proof. exact (TRANS (@lem5384990) (@lem5385005)). Qed.
Lemma lem5385007 : term493 = term198.
Proof. exact (@lem5384957 (@lem5385006)). Qed.
Lemma lem5385008 : term492 = term198.
Proof. exact (TRANS (@lem5384923) (@lem5385007)). Qed.
Lemma lem5385010 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5385011 : term198 = term128.
Proof. exact (@lem5385010 term128). Qed.
Lemma lem5385012 : term492 = term128.
Proof. exact (TRANS (@lem5385008) (@lem5385011)). Qed.
Lemma lem5385013 (_69795 : int) : (term491 _69795) = term502.
Proof. exact (MK_COMB (@lem5384914 _69795) (@lem5385012)). Qed.
Lemma lem5385014 (_69795 : int) : (term490 _69795) = term502.
Proof. exact (TRANS (@lem5384806 _69795) (@lem5385013 _69795)). Qed.
Lemma lem5385015 : term502 = term128.
Proof. exact (@lem1982721 term128). Qed.
Lemma lem5385016 (_69795 : int) : (term490 _69795) = term128.
Proof. exact (TRANS (@lem5385014 _69795) (@lem5385015)). Qed.
Lemma lem5385017 (_69794 : int) (_69795 : int) : (term489 _69794 _69795) = term502.
Proof. exact (MK_COMB (@lem5384805 _69794) (@lem5385016 _69795)). Qed.
Lemma lem5385018 (_69794 : int) (_69795 : int) : (term488 _69794 _69795) = term502.
Proof. exact (TRANS (@lem5384697 _69794 _69795) (@lem5385017 _69794 _69795)). Qed.
Lemma lem5385019 : term502 = term128.
Proof. exact (@lem1982721 term128). Qed.
Lemma lem5385020 (_69794 : int) (_69795 : int) : (term488 _69794 _69795) = term128.
Proof. exact (TRANS (@lem5385018 _69794 _69795) (@lem5385019)). Qed.
Lemma lem5385021 (_69793 : int) : (term231 _69793) = (term231 _69793).
Proof. exact (eq_refl (term231 _69793)). Qed.
Lemma lem5385022 (_69794 : int) (_69795 : int) (_69793 : int) : (term487 _69793 _69794 _69795) = (term503 _69793).
Proof. exact (MK_COMB (@lem5385021 _69793) (@lem5385020 _69794 _69795)). Qed.
Lemma lem5385023 (_69794 : int) (_69795 : int) (_69793 : int) : (term486 _69793 _69794 _69795) = (term503 _69793).
Proof. exact (TRANS (@lem5384696 _69793 _69794 _69795) (@lem5385022 _69794 _69795 _69793)). Qed.
Lemma lem5385024 (_69793 : int) : (term503 _69793) = (term228 _69793).
Proof. exact (@lem1982723 (term228 _69793)). Qed.
Lemma lem5385025 (_69794 : int) (_69795 : int) (_69793 : int) : (term486 _69793 _69794 _69795) = (term228 _69793).
Proof. exact (TRANS (@lem5385023 _69794 _69795 _69793) (@lem5385024 _69793)). Qed.
Lemma lem5385026 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5385027 (_69794 : int) (_69795 : int) (_69793 : int) : (term504 _69793 _69794 _69795) = (term505 _69793).
Proof. exact (MK_COMB (@lem5385026) (@lem5385025 _69794 _69795 _69793)). Qed.
Lemma lem5385028 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5385029 (_69794 : int) (_69795 : int) (_69793 : int) : (term485 _69793 _69794 _69795) = (term506 _69793).
Proof. exact (MK_COMB (@lem5385027 _69794 _69795 _69793) (@lem5385028)). Qed.
Lemma lem5385030 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term467 _69794 _69795 _69793) : term506 _69793.
Proof. exact (EQ_MP (@lem5385029 _69794 _69795 _69793) (@lem5384695 _69794 _69795 _69793 h1)). Qed.
Lemma lem5385032 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5385033 : term390 = term245.
Proof. exact (@lem5385032 term128 term138). Qed.
Lemma lem5385035 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5385036 : term138 = term237.
Proof. exact (@lem5385035 term44). Qed.
Lemma lem5385038 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5385039 : term128 = term198.
Proof. exact (@lem5385038 (NUMERAL 0)). Qed.
Lemma lem5385040 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5385041 : term391 = term392.
Proof. exact (MK_COMB (@lem5385040) (@lem5385039)). Qed.
Lemma lem5385042 : term245 = term393.
Proof. exact (MK_COMB (@lem5385041) (@lem5385036)). Qed.
Lemma lem5385043 : term394.
Proof. exact (@lem1980255 term128 term138 term138 term138). Qed.
Lemma lem5385045 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5385046 : term245 = term246.
Proof. exact (@lem5385045 (NUMERAL 0) term44). Qed.
Lemma lem5385047 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5385048 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5385049 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5385048 h1) (fun h1 : term246 = True => @lem5385047)). Qed.
Lemma lem5385050 : term246 = True.
Proof. exact (EQ_MP (@lem5385049) (@lem5385047)). Qed.
Lemma lem5385051 : term245 = True.
Proof. exact (TRANS (@lem5385046) (@lem5385050)). Qed.
Lemma lem5385052 : True = term245.
Proof. exact (SYM (@lem5385051)). Qed.
Lemma lem5385053 : term245.
Proof. exact (EQ_MP (@lem5385052) (@lem0)). Qed.
Lemma lem5385054 : term395.
Proof. exact (@lem5385043 (@lem5385053)). Qed.
Lemma lem5385056 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5385057 : term245 = term246.
Proof. exact (@lem5385056 (NUMERAL 0) term44). Qed.
Lemma lem5385058 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5385059 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5385060 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5385059 h1) (fun h1 : term246 = True => @lem5385058)). Qed.
Lemma lem5385061 : term246 = True.
Proof. exact (EQ_MP (@lem5385060) (@lem5385058)). Qed.
Lemma lem5385062 : term245 = True.
Proof. exact (TRANS (@lem5385057) (@lem5385061)). Qed.
Lemma lem5385063 : True = term245.
Proof. exact (SYM (@lem5385062)). Qed.
Lemma lem5385064 : term245.
Proof. exact (EQ_MP (@lem5385063) (@lem0)). Qed.
Lemma lem5385065 : term393 = term396.
Proof. exact (@lem5385054 (@lem5385064)). Qed.
Lemma lem5385067 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5385068 : term210 = term211.
Proof. exact (@lem5385067 term44 term44). Qed.
Lemma lem5385069 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5385070 : term213 = term44.
Proof. exact (EQ_MP (@lem5385069) (@lem940073)). Qed.
Lemma lem5385071 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5385072 : term211 = term138.
Proof. exact (MK_COMB (@lem5385071) (@lem5385070)). Qed.
Lemma lem5385073 : term210 = term138.
Proof. exact (TRANS (@lem5385068) (@lem5385072)). Qed.
Lemma lem5385075 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5385076 : term398 = term128.
Proof. exact (@lem5385075 term44). Qed.
Lemma lem5385077 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5385078 : term399 = term391.
Proof. exact (MK_COMB (@lem5385077) (@lem5385076)). Qed.
Lemma lem5385079 : term396 = term245.
Proof. exact (MK_COMB (@lem5385078) (@lem5385073)). Qed.
Lemma lem5385081 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5385082 : term245 = term246.
Proof. exact (@lem5385081 (NUMERAL 0) term44). Qed.
Lemma lem5385083 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5385084 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5385085 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5385084 h1) (fun h1 : term246 = True => @lem5385083)). Qed.
Lemma lem5385086 : term246 = True.
Proof. exact (EQ_MP (@lem5385085) (@lem5385083)). Qed.
Lemma lem5385087 : term245 = True.
Proof. exact (TRANS (@lem5385082) (@lem5385086)). Qed.
Lemma lem5385088 : term396 = True.
Proof. exact (TRANS (@lem5385079) (@lem5385087)). Qed.
Lemma lem5385089 : term393 = True.
Proof. exact (TRANS (@lem5385065) (@lem5385088)). Qed.
Lemma lem5385090 : term245 = True.
Proof. exact (TRANS (@lem5385042) (@lem5385089)). Qed.
Lemma lem5385091 : term390 = True.
Proof. exact (TRANS (@lem5385033) (@lem5385090)). Qed.
Lemma lem5385092 : True = term390.
Proof. exact (SYM (@lem5385091)). Qed.
Lemma lem5385093 : term390.
Proof. exact (EQ_MP (@lem5385092) (@lem0)). Qed.
Lemma lem5385094 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term467 _69794 _69795 _69793) : term507 _69793.
Proof. exact (conj (@lem5385093) (@lem5385030 _69794 _69795 _69793 h1)). Qed.
Lemma lem5385096 (x : real) (y : real) : term401 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5385097 (_69793 : int) : term508 _69793.
Proof. exact (@lem5385096 term138 (term228 _69793)). Qed.
Lemma lem5385098 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term467 _69794 _69795 _69793) : term509 _69793.
Proof. exact (@lem5385097 _69793 (@lem5385094 _69794 _69795 _69793 h1)). Qed.
Lemma lem5385099 (_69793 : int) : (term510 _69793) = (term228 _69793).
Proof. exact (@lem1982733 (term228 _69793)). Qed.
Lemma lem5385100 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5385101 (_69793 : int) : (term511 _69793) = (term505 _69793).
Proof. exact (MK_COMB (@lem5385100) (@lem5385099 _69793)). Qed.
Lemma lem5385102 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5385103 (_69793 : int) : (term509 _69793) = (term506 _69793).
Proof. exact (MK_COMB (@lem5385101 _69793) (@lem5385102)). Qed.
Lemma lem5385104 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term467 _69794 _69795 _69793) : term506 _69793.
Proof. exact (EQ_MP (@lem5385103 _69793) (@lem5385098 _69794 _69795 _69793 h1)). Qed.
Lemma lem5385105 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term467 _69794 _69795 _69793) : term512 _69793.
Proof. exact (conj (@lem5385104 _69794 _69795 _69793 h1) (@lem5384603 _69794 _69795 _69793 h1)). Qed.
Lemma lem5385107 (x : real) (y : real) : term412 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5385108 (_69793 : int) : term513 _69793.
Proof. exact (@lem5385107 (term228 _69793) (term324 _69793)). Qed.
Lemma lem5385109 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term467 _69794 _69795 _69793) : term514 _69793.
Proof. exact (@lem5385108 _69793 (@lem5385105 _69794 _69795 _69793 h1)). Qed.
Lemma lem5385110 (_69793 : int) : (term515 _69793) = (term416 _69793).
Proof. exact (@lem1982763 (term228 _69793) (real_of_int _69793) term201). Qed.
Lemma lem5385111 (_69793 : int) : (term417 _69793) = (term418 _69793).
Proof. exact (@lem1982713 term201 (real_of_int _69793)). Qed.
Lemma lem5385113 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5385114 : term138 = term237.
Proof. exact (@lem5385113 term44). Qed.
Lemma lem5385116 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5385117 : term201 = term202.
Proof. exact (@lem5385116 term44). Qed.
Lemma lem5385118 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5385119 : term419 = term420.
Proof. exact (MK_COMB (@lem5385118) (@lem5385117)). Qed.
Lemma lem5385120 : term421 = term422.
Proof. exact (MK_COMB (@lem5385119) (@lem5385114)). Qed.
Lemma lem5385121 : term423.
Proof. exact (@lem1981473 term201 term138 term138 term138 term128 term138). Qed.
Lemma lem5385123 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5385124 : term245 = term246.
Proof. exact (@lem5385123 (NUMERAL 0) term44). Qed.
Lemma lem5385125 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5385126 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5385127 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5385126 h1) (fun h1 : term246 = True => @lem5385125)). Qed.
Lemma lem5385128 : term246 = True.
Proof. exact (EQ_MP (@lem5385127) (@lem5385125)). Qed.
Lemma lem5385129 : term245 = True.
Proof. exact (TRANS (@lem5385124) (@lem5385128)). Qed.
Lemma lem5385130 : True = term245.
Proof. exact (SYM (@lem5385129)). Qed.
Lemma lem5385131 : term245.
Proof. exact (EQ_MP (@lem5385130) (@lem0)). Qed.
Lemma lem5385132 : term424.
Proof. exact (@lem5385121 (@lem5385131)). Qed.
Lemma lem5385134 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5385135 : term245 = term246.
Proof. exact (@lem5385134 (NUMERAL 0) term44). Qed.
Lemma lem5385136 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5385137 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5385138 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5385137 h1) (fun h1 : term246 = True => @lem5385136)). Qed.
Lemma lem5385139 : term246 = True.
Proof. exact (EQ_MP (@lem5385138) (@lem5385136)). Qed.
Lemma lem5385140 : term245 = True.
Proof. exact (TRANS (@lem5385135) (@lem5385139)). Qed.
Lemma lem5385141 : True = term245.
Proof. exact (SYM (@lem5385140)). Qed.
Lemma lem5385142 : term245.
Proof. exact (EQ_MP (@lem5385141) (@lem0)). Qed.
Lemma lem5385143 : term425.
Proof. exact (@lem5385132 (@lem5385142)). Qed.
Lemma lem5385145 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5385146 : term245 = term246.
Proof. exact (@lem5385145 (NUMERAL 0) term44). Qed.
Lemma lem5385147 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5385148 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5385149 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5385148 h1) (fun h1 : term246 = True => @lem5385147)). Qed.
Lemma lem5385150 : term246 = True.
Proof. exact (EQ_MP (@lem5385149) (@lem5385147)). Qed.
Lemma lem5385151 : term245 = True.
Proof. exact (TRANS (@lem5385146) (@lem5385150)). Qed.
Lemma lem5385152 : True = term245.
Proof. exact (SYM (@lem5385151)). Qed.
Lemma lem5385153 : term245.
Proof. exact (EQ_MP (@lem5385152) (@lem0)). Qed.
Lemma lem5385154 : term426.
Proof. exact (@lem5385143 (@lem5385153)). Qed.
Lemma lem5385156 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5385157 : term210 = term211.
Proof. exact (@lem5385156 term44 term44). Qed.
Lemma lem5385158 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5385159 : term213 = term44.
Proof. exact (EQ_MP (@lem5385158) (@lem940073)). Qed.
Lemma lem5385160 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5385161 : term211 = term138.
Proof. exact (MK_COMB (@lem5385160) (@lem5385159)). Qed.
Lemma lem5385162 : term210 = term138.
Proof. exact (TRANS (@lem5385157) (@lem5385161)). Qed.
Lemma lem5385164 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5385165 : term302 = term305.
Proof. exact (@lem5385164 term44 term44). Qed.
Lemma lem5385166 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5385167 : term213 = term44.
Proof. exact (EQ_MP (@lem5385166) (@lem940073)). Qed.
Lemma lem5385168 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5385169 : term211 = term138.
Proof. exact (MK_COMB (@lem5385168) (@lem5385167)). Qed.
Lemma lem5385170 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5385171 : term305 = term201.
Proof. exact (MK_COMB (@lem5385170) (@lem5385169)). Qed.
Lemma lem5385172 : term302 = term201.
Proof. exact (TRANS (@lem5385165) (@lem5385171)). Qed.
Lemma lem5385173 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5385174 : term427 = term419.
Proof. exact (MK_COMB (@lem5385173) (@lem5385172)). Qed.
Lemma lem5385175 : term428 = term421.
Proof. exact (MK_COMB (@lem5385174) (@lem5385162)). Qed.
Lemma lem5385177 (m : nat) : (term429 m) = term128.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5385178 : term421 = term128.
Proof. exact (@lem5385177 term44). Qed.
Lemma lem5385179 : term428 = term128.
Proof. exact (TRANS (@lem5385175) (@lem5385178)). Qed.
Lemma lem5385180 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5385181 : term430 = term431.
Proof. exact (MK_COMB (@lem5385180) (@lem5385179)). Qed.
Lemma lem5385182 : term138 = term138.
Proof. exact (eq_refl term138). Qed.
Lemma lem5385183 : term432 = term398.
Proof. exact (MK_COMB (@lem5385181) (@lem5385182)). Qed.
Lemma lem5385185 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5385186 : term398 = term128.
Proof. exact (@lem5385185 term44). Qed.
Lemma lem5385187 : term432 = term128.
Proof. exact (TRANS (@lem5385183) (@lem5385186)). Qed.
Lemma lem5385189 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5385190 : term210 = term211.
Proof. exact (@lem5385189 term44 term44). Qed.
Lemma lem5385191 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5385192 : term213 = term44.
Proof. exact (EQ_MP (@lem5385191) (@lem940073)). Qed.
Lemma lem5385193 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5385194 : term211 = term138.
Proof. exact (MK_COMB (@lem5385193) (@lem5385192)). Qed.
Lemma lem5385195 : term210 = term138.
Proof. exact (TRANS (@lem5385190) (@lem5385194)). Qed.
Lemma lem5385196 : term431 = term431.
Proof. exact (eq_refl term431). Qed.
Lemma lem5385197 : term433 = term398.
Proof. exact (MK_COMB (@lem5385196) (@lem5385195)). Qed.
Lemma lem5385199 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5385200 : term398 = term128.
Proof. exact (@lem5385199 term44). Qed.
Lemma lem5385201 : term433 = term128.
Proof. exact (TRANS (@lem5385197) (@lem5385200)). Qed.
Lemma lem5385202 : term128 = term433.
Proof. exact (SYM (@lem5385201)). Qed.
Lemma lem5385203 : term432 = term433.
Proof. exact (TRANS (@lem5385187) (@lem5385202)). Qed.
Lemma lem5385204 : term422 = term198.
Proof. exact (@lem5385154 (@lem5385203)). Qed.
Lemma lem5385205 : term421 = term198.
Proof. exact (TRANS (@lem5385120) (@lem5385204)). Qed.
Lemma lem5385207 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5385208 : term198 = term128.
Proof. exact (@lem5385207 term128). Qed.
Lemma lem5385209 : term421 = term128.
Proof. exact (TRANS (@lem5385205) (@lem5385208)). Qed.
Lemma lem5385210 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5385211 : term434 = term431.
Proof. exact (MK_COMB (@lem5385210) (@lem5385209)). Qed.
Lemma lem5385212 (_69793 : int) : (real_of_int _69793) = (real_of_int _69793).
Proof. exact (eq_refl (real_of_int _69793)). Qed.
Lemma lem5385213 (_69793 : int) : (term418 _69793) = (term435 _69793).
Proof. exact (MK_COMB (@lem5385211) (@lem5385212 _69793)). Qed.
Lemma lem5385214 (_69793 : int) : (term417 _69793) = (term435 _69793).
Proof. exact (TRANS (@lem5385111 _69793) (@lem5385213 _69793)). Qed.
Lemma lem5385215 (_69793 : int) : (term435 _69793) = term128.
Proof. exact (@lem1982719 (real_of_int _69793)). Qed.
Lemma lem5385216 (_69793 : int) : (term417 _69793) = term128.
Proof. exact (TRANS (@lem5385214 _69793) (@lem5385215 _69793)). Qed.
Lemma lem5385217 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5385218 (_69793 : int) : (term436 _69793) = term178.
Proof. exact (MK_COMB (@lem5385217) (@lem5385216 _69793)). Qed.
Lemma lem5385219 : term201 = term201.
Proof. exact (eq_refl term201). Qed.
Lemma lem5385220 (_69793 : int) : (term416 _69793) = term437.
Proof. exact (MK_COMB (@lem5385218 _69793) (@lem5385219)). Qed.
Lemma lem5385221 (_69793 : int) : (term515 _69793) = term437.
Proof. exact (TRANS (@lem5385110 _69793) (@lem5385220 _69793)). Qed.
Lemma lem5385222 : term437 = term201.
Proof. exact (@lem1982721 term201). Qed.
Lemma lem5385223 (_69793 : int) : (term515 _69793) = term201.
Proof. exact (TRANS (@lem5385221 _69793) (@lem5385222)). Qed.
Lemma lem5385224 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5385225 (_69793 : int) : (term516 _69793) = term439.
Proof. exact (MK_COMB (@lem5385224) (@lem5385223 _69793)). Qed.
Lemma lem5385226 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5385227 (_69793 : int) : (term514 _69793) = term440.
Proof. exact (MK_COMB (@lem5385225 _69793) (@lem5385226)). Qed.
Lemma lem5385228 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term467 _69794 _69795 _69793) : term440.
Proof. exact (EQ_MP (@lem5385227 _69793) (@lem5385109 _69794 _69795 _69793 h1)). Qed.
Lemma lem5385230 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5385231 : term440 = term441.
Proof. exact (@lem5385230 term128 term201). Qed.
Lemma lem5385233 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5385234 : term201 = term202.
Proof. exact (@lem5385233 term44). Qed.
Lemma lem5385236 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5385237 : term128 = term198.
Proof. exact (@lem5385236 (NUMERAL 0)). Qed.
Lemma lem5385238 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5385239 : term130 = term442.
Proof. exact (MK_COMB (@lem5385238) (@lem5385237)). Qed.
Lemma lem5385240 : term441 = term443.
Proof. exact (MK_COMB (@lem5385239) (@lem5385234)). Qed.
Lemma lem5385241 : term444.
Proof. exact (@lem1980026 term128 term138 term201 term138). Qed.
Lemma lem5385243 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5385244 : term245 = term246.
Proof. exact (@lem5385243 (NUMERAL 0) term44). Qed.
Lemma lem5385245 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5385246 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5385247 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5385246 h1) (fun h1 : term246 = True => @lem5385245)). Qed.
Lemma lem5385248 : term246 = True.
Proof. exact (EQ_MP (@lem5385247) (@lem5385245)). Qed.
Lemma lem5385249 : term245 = True.
Proof. exact (TRANS (@lem5385244) (@lem5385248)). Qed.
Lemma lem5385250 : True = term245.
Proof. exact (SYM (@lem5385249)). Qed.
Lemma lem5385251 : term245.
Proof. exact (EQ_MP (@lem5385250) (@lem0)). Qed.
Lemma lem5385252 : term445.
Proof. exact (@lem5385241 (@lem5385251)). Qed.
Lemma lem5385254 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5385255 : term245 = term246.
Proof. exact (@lem5385254 (NUMERAL 0) term44). Qed.
Lemma lem5385256 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5385257 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5385258 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5385257 h1) (fun h1 : term246 = True => @lem5385256)). Qed.
Lemma lem5385259 : term246 = True.
Proof. exact (EQ_MP (@lem5385258) (@lem5385256)). Qed.
Lemma lem5385260 : term245 = True.
Proof. exact (TRANS (@lem5385255) (@lem5385259)). Qed.
Lemma lem5385261 : True = term245.
Proof. exact (SYM (@lem5385260)). Qed.
Lemma lem5385262 : term245.
Proof. exact (EQ_MP (@lem5385261) (@lem0)). Qed.
Lemma lem5385263 : term443 = term446.
Proof. exact (@lem5385252 (@lem5385262)). Qed.
Lemma lem5385265 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5385266 : term302 = term305.
Proof. exact (@lem5385265 term44 term44). Qed.
Lemma lem5385267 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5385268 : term213 = term44.
Proof. exact (EQ_MP (@lem5385267) (@lem940073)). Qed.
Lemma lem5385269 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5385270 : term211 = term138.
Proof. exact (MK_COMB (@lem5385269) (@lem5385268)). Qed.
Lemma lem5385271 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5385272 : term305 = term201.
Proof. exact (MK_COMB (@lem5385271) (@lem5385270)). Qed.
Lemma lem5385273 : term302 = term201.
Proof. exact (TRANS (@lem5385266) (@lem5385272)). Qed.
Lemma lem5385275 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5385276 : term398 = term128.
Proof. exact (@lem5385275 term44). Qed.
Lemma lem5385277 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5385278 : term447 = term130.
Proof. exact (MK_COMB (@lem5385277) (@lem5385276)). Qed.
Lemma lem5385279 : term446 = term441.
Proof. exact (MK_COMB (@lem5385278) (@lem5385273)). Qed.
Lemma lem5385281 (m : nat) (n : nat) : (term448 m n) = (term449 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5385282 : term441 = term450.
Proof. exact (@lem5385281 (NUMERAL 0) term44). Qed.
Lemma lem5385283 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5385284 (h1 : term247 = (BIT1 0)) : (term44 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5385285 : (term247 = (BIT1 0)) = ((term44 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5385284 h1) (fun h1 : (term44 = (NUMERAL 0)) = False => @lem5385283)). Qed.
Lemma lem5385286 : (term44 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5385285) (@lem5385283)). Qed.
Lemma lem5385287 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5385288 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5385289 : term451 = (and True).
Proof. exact (MK_COMB (@lem5385288) (@lem5385287)). Qed.
Lemma lem5385290 : term450 = (True /\ False).
Proof. exact (MK_COMB (@lem5385289) (@lem5385286)). Qed.
Lemma lem5385292 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5385293 : term450 = False.
Proof. exact (TRANS (@lem5385290) (@lem5385292)). Qed.
Lemma lem5385294 : term441 = False.
Proof. exact (TRANS (@lem5385282) (@lem5385293)). Qed.
Lemma lem5385295 : term446 = False.
Proof. exact (TRANS (@lem5385279) (@lem5385294)). Qed.
Lemma lem5385296 : term443 = False.
Proof. exact (TRANS (@lem5385263) (@lem5385295)). Qed.
Lemma lem5385297 : term441 = False.
Proof. exact (TRANS (@lem5385240) (@lem5385296)). Qed.
Lemma lem5385298 : term440 = False.
Proof. exact (TRANS (@lem5385231) (@lem5385297)). Qed.
Lemma lem5385299 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term467 _69794 _69795 _69793) : False.
Proof. exact (EQ_MP (@lem5385298) (@lem5385228 _69794 _69795 _69793 h1)). Qed.
Lemma lem5385300 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term517 _69794 _69795 _69793) : term517 _69794 _69795 _69793.
Proof. exact (h1). Qed.
Lemma lem5385301 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term517 _69794 _69795 _69793) : term381 _69794 _69795 _69793.
Proof. exact (proj2 (@lem5385300 _69794 _69795 _69793 h1)). Qed.
Lemma lem5385303 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term517 _69794 _69795 _69793) : term368 _69794 _69795 _69793.
Proof. exact (proj2 (@lem5385301 _69794 _69795 _69793 h1)). Qed.
Lemma lem5385305 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term517 _69794 _69795 _69793) : term355 _69794 _69795 _69793.
Proof. exact (proj2 (@lem5385303 _69794 _69795 _69793 h1)). Qed.
Lemma lem5385307 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term517 _69794 _69795 _69793) : term342 _69794 _69795 _69793.
Proof. exact (proj2 (@lem5385305 _69794 _69795 _69793 h1)). Qed.
Lemma lem5385308 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term517 _69794 _69795 _69793) : term294 _69794 _69795 _69793.
Proof. exact (proj1 (@lem5385305 _69794 _69795 _69793 h1)). Qed.
Lemma lem5385309 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term517 _69794 _69795 _69793) : (real_of_int _69793) = term128.
Proof. exact (proj2 (@lem5385308 _69794 _69795 _69793 h1)). Qed.
Lemma lem5385311 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term517 _69794 _69795 _69793) : term327 _69793.
Proof. exact (proj2 (@lem5385307 _69794 _69795 _69793 h1)). Qed.
Lemma lem5385314 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5385315 : term390 = term245.
Proof. exact (@lem5385314 term128 term138). Qed.
Lemma lem5385317 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5385318 : term138 = term237.
Proof. exact (@lem5385317 term44). Qed.
Lemma lem5385320 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5385321 : term128 = term198.
Proof. exact (@lem5385320 (NUMERAL 0)). Qed.
Lemma lem5385322 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5385323 : term391 = term392.
Proof. exact (MK_COMB (@lem5385322) (@lem5385321)). Qed.
Lemma lem5385324 : term245 = term393.
Proof. exact (MK_COMB (@lem5385323) (@lem5385318)). Qed.
Lemma lem5385325 : term394.
Proof. exact (@lem1980255 term128 term138 term138 term138). Qed.
Lemma lem5385327 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5385328 : term245 = term246.
Proof. exact (@lem5385327 (NUMERAL 0) term44). Qed.
Lemma lem5385329 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5385330 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5385331 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5385330 h1) (fun h1 : term246 = True => @lem5385329)). Qed.
Lemma lem5385332 : term246 = True.
Proof. exact (EQ_MP (@lem5385331) (@lem5385329)). Qed.
Lemma lem5385333 : term245 = True.
Proof. exact (TRANS (@lem5385328) (@lem5385332)). Qed.
Lemma lem5385334 : True = term245.
Proof. exact (SYM (@lem5385333)). Qed.
Lemma lem5385335 : term245.
Proof. exact (EQ_MP (@lem5385334) (@lem0)). Qed.
Lemma lem5385336 : term395.
Proof. exact (@lem5385325 (@lem5385335)). Qed.
Lemma lem5385338 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5385339 : term245 = term246.
Proof. exact (@lem5385338 (NUMERAL 0) term44). Qed.
Lemma lem5385340 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5385341 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5385342 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5385341 h1) (fun h1 : term246 = True => @lem5385340)). Qed.
Lemma lem5385343 : term246 = True.
Proof. exact (EQ_MP (@lem5385342) (@lem5385340)). Qed.
Lemma lem5385344 : term245 = True.
Proof. exact (TRANS (@lem5385339) (@lem5385343)). Qed.
Lemma lem5385345 : True = term245.
Proof. exact (SYM (@lem5385344)). Qed.
Lemma lem5385346 : term245.
Proof. exact (EQ_MP (@lem5385345) (@lem0)). Qed.
Lemma lem5385347 : term393 = term396.
Proof. exact (@lem5385336 (@lem5385346)). Qed.
Lemma lem5385349 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5385350 : term210 = term211.
Proof. exact (@lem5385349 term44 term44). Qed.
Lemma lem5385351 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5385352 : term213 = term44.
Proof. exact (EQ_MP (@lem5385351) (@lem940073)). Qed.
Lemma lem5385353 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5385354 : term211 = term138.
Proof. exact (MK_COMB (@lem5385353) (@lem5385352)). Qed.
Lemma lem5385355 : term210 = term138.
Proof. exact (TRANS (@lem5385350) (@lem5385354)). Qed.
Lemma lem5385357 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5385358 : term398 = term128.
Proof. exact (@lem5385357 term44). Qed.
Lemma lem5385359 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5385360 : term399 = term391.
Proof. exact (MK_COMB (@lem5385359) (@lem5385358)). Qed.
Lemma lem5385361 : term396 = term245.
Proof. exact (MK_COMB (@lem5385360) (@lem5385355)). Qed.
Lemma lem5385363 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5385364 : term245 = term246.
Proof. exact (@lem5385363 (NUMERAL 0) term44). Qed.
Lemma lem5385365 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5385366 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5385367 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5385366 h1) (fun h1 : term246 = True => @lem5385365)). Qed.
Lemma lem5385368 : term246 = True.
Proof. exact (EQ_MP (@lem5385367) (@lem5385365)). Qed.
Lemma lem5385369 : term245 = True.
Proof. exact (TRANS (@lem5385364) (@lem5385368)). Qed.
Lemma lem5385370 : term396 = True.
Proof. exact (TRANS (@lem5385361) (@lem5385369)). Qed.
Lemma lem5385371 : term393 = True.
Proof. exact (TRANS (@lem5385347) (@lem5385370)). Qed.
Lemma lem5385372 : term245 = True.
Proof. exact (TRANS (@lem5385324) (@lem5385371)). Qed.
Lemma lem5385373 : term390 = True.
Proof. exact (TRANS (@lem5385315) (@lem5385372)). Qed.
Lemma lem5385374 : True = term390.
Proof. exact (SYM (@lem5385373)). Qed.
Lemma lem5385375 : term390.
Proof. exact (EQ_MP (@lem5385374) (@lem0)). Qed.
Lemma lem5385376 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term517 _69794 _69795 _69793) : term468 _69793.
Proof. exact (conj (@lem5385375) (@lem5385311 _69794 _69795 _69793 h1)). Qed.
Lemma lem5385378 (x : real) (y : real) : term401 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5385379 (_69793 : int) : term469 _69793.
Proof. exact (@lem5385378 term138 (term324 _69793)). Qed.
Lemma lem5385380 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term517 _69794 _69795 _69793) : term470 _69793.
Proof. exact (@lem5385379 _69793 (@lem5385376 _69794 _69795 _69793 h1)). Qed.
Lemma lem5385381 (_69793 : int) : (term471 _69793) = (term324 _69793).
Proof. exact (@lem1982733 (term324 _69793)). Qed.
Lemma lem5385382 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5385383 (_69793 : int) : (term472 _69793) = (term326 _69793).
Proof. exact (MK_COMB (@lem5385382) (@lem5385381 _69793)). Qed.
Lemma lem5385384 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5385385 (_69793 : int) : (term470 _69793) = (term327 _69793).
Proof. exact (MK_COMB (@lem5385383 _69793) (@lem5385384)). Qed.
Lemma lem5385386 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term517 _69794 _69795 _69793) : term327 _69793.
Proof. exact (EQ_MP (@lem5385385 _69793) (@lem5385380 _69794 _69795 _69793 h1)). Qed.
Lemma lem5385388 (y : real) : term453 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5385389 (_69793 : int) : term454 _69793.
Proof. exact (@lem5385388 (real_of_int _69793)). Qed.
Lemma lem5385390 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term517 _69794 _69795 _69793) : term455 _69793.
Proof. exact (@lem5385389 _69793 (@lem5385309 _69794 _69795 _69793 h1)). Qed.
Lemma lem5385391 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term517 _69794 _69795 _69793) : term518 _69793.
Proof. exact (@lem5385390 _69794 _69795 _69793 h1 term201). Qed.
Lemma lem5385392 (_69793 : int) : (term518 _69793) = ((term228 _69793) = term128).
Proof. exact (eq_refl (term518 _69793)). Qed.
Lemma lem5385399 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term517 _69794 _69795 _69793) : (term228 _69793) = term128.
Proof. exact (EQ_MP (@lem5385392 _69793) (@lem5385391 _69794 _69795 _69793 h1)). Qed.
Lemma lem5385400 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term517 _69794 _69795 _69793) : term519 _69793.
Proof. exact (conj (@lem5385399 _69794 _69795 _69793 h1) (@lem5385386 _69794 _69795 _69793 h1)). Qed.
Lemma lem5385402 (x : real) (y : real) : term459 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5385403 (_69793 : int) : term520 _69793.
Proof. exact (@lem5385402 (term228 _69793) (term324 _69793)). Qed.
Lemma lem5385404 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term517 _69794 _69795 _69793) : term514 _69793.
Proof. exact (@lem5385403 _69793 (@lem5385400 _69794 _69795 _69793 h1)). Qed.
Lemma lem5385405 (_69793 : int) : (term515 _69793) = (term416 _69793).
Proof. exact (@lem1982763 (term228 _69793) (real_of_int _69793) term201). Qed.
Lemma lem5385406 (_69793 : int) : (term417 _69793) = (term418 _69793).
Proof. exact (@lem1982713 term201 (real_of_int _69793)). Qed.
Lemma lem5385408 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5385409 : term138 = term237.
Proof. exact (@lem5385408 term44). Qed.
Lemma lem5385411 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5385412 : term201 = term202.
Proof. exact (@lem5385411 term44). Qed.
Lemma lem5385413 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5385414 : term419 = term420.
Proof. exact (MK_COMB (@lem5385413) (@lem5385412)). Qed.
Lemma lem5385415 : term421 = term422.
Proof. exact (MK_COMB (@lem5385414) (@lem5385409)). Qed.
Lemma lem5385416 : term423.
Proof. exact (@lem1981473 term201 term138 term138 term138 term128 term138). Qed.
Lemma lem5385418 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5385419 : term245 = term246.
Proof. exact (@lem5385418 (NUMERAL 0) term44). Qed.
Lemma lem5385420 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5385421 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5385422 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5385421 h1) (fun h1 : term246 = True => @lem5385420)). Qed.
Lemma lem5385423 : term246 = True.
Proof. exact (EQ_MP (@lem5385422) (@lem5385420)). Qed.
Lemma lem5385424 : term245 = True.
Proof. exact (TRANS (@lem5385419) (@lem5385423)). Qed.
Lemma lem5385425 : True = term245.
Proof. exact (SYM (@lem5385424)). Qed.
Lemma lem5385426 : term245.
Proof. exact (EQ_MP (@lem5385425) (@lem0)). Qed.
Lemma lem5385427 : term424.
Proof. exact (@lem5385416 (@lem5385426)). Qed.
Lemma lem5385429 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5385430 : term245 = term246.
Proof. exact (@lem5385429 (NUMERAL 0) term44). Qed.
Lemma lem5385431 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5385432 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5385433 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5385432 h1) (fun h1 : term246 = True => @lem5385431)). Qed.
Lemma lem5385434 : term246 = True.
Proof. exact (EQ_MP (@lem5385433) (@lem5385431)). Qed.
Lemma lem5385435 : term245 = True.
Proof. exact (TRANS (@lem5385430) (@lem5385434)). Qed.
Lemma lem5385436 : True = term245.
Proof. exact (SYM (@lem5385435)). Qed.
Lemma lem5385437 : term245.
Proof. exact (EQ_MP (@lem5385436) (@lem0)). Qed.
Lemma lem5385438 : term425.
Proof. exact (@lem5385427 (@lem5385437)). Qed.
Lemma lem5385440 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5385441 : term245 = term246.
Proof. exact (@lem5385440 (NUMERAL 0) term44). Qed.
Lemma lem5385442 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5385443 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5385444 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5385443 h1) (fun h1 : term246 = True => @lem5385442)). Qed.
Lemma lem5385445 : term246 = True.
Proof. exact (EQ_MP (@lem5385444) (@lem5385442)). Qed.
Lemma lem5385446 : term245 = True.
Proof. exact (TRANS (@lem5385441) (@lem5385445)). Qed.
Lemma lem5385447 : True = term245.
Proof. exact (SYM (@lem5385446)). Qed.
Lemma lem5385448 : term245.
Proof. exact (EQ_MP (@lem5385447) (@lem0)). Qed.
Lemma lem5385449 : term426.
Proof. exact (@lem5385438 (@lem5385448)). Qed.
Lemma lem5385451 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5385452 : term210 = term211.
Proof. exact (@lem5385451 term44 term44). Qed.
Lemma lem5385453 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5385454 : term213 = term44.
Proof. exact (EQ_MP (@lem5385453) (@lem940073)). Qed.
Lemma lem5385455 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5385456 : term211 = term138.
Proof. exact (MK_COMB (@lem5385455) (@lem5385454)). Qed.
Lemma lem5385457 : term210 = term138.
Proof. exact (TRANS (@lem5385452) (@lem5385456)). Qed.
Lemma lem5385459 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5385460 : term302 = term305.
Proof. exact (@lem5385459 term44 term44). Qed.
Lemma lem5385461 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5385462 : term213 = term44.
Proof. exact (EQ_MP (@lem5385461) (@lem940073)). Qed.
Lemma lem5385463 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5385464 : term211 = term138.
Proof. exact (MK_COMB (@lem5385463) (@lem5385462)). Qed.
Lemma lem5385465 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5385466 : term305 = term201.
Proof. exact (MK_COMB (@lem5385465) (@lem5385464)). Qed.
Lemma lem5385467 : term302 = term201.
Proof. exact (TRANS (@lem5385460) (@lem5385466)). Qed.
Lemma lem5385468 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5385469 : term427 = term419.
Proof. exact (MK_COMB (@lem5385468) (@lem5385467)). Qed.
Lemma lem5385470 : term428 = term421.
Proof. exact (MK_COMB (@lem5385469) (@lem5385457)). Qed.
Lemma lem5385472 (m : nat) : (term429 m) = term128.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5385473 : term421 = term128.
Proof. exact (@lem5385472 term44). Qed.
Lemma lem5385474 : term428 = term128.
Proof. exact (TRANS (@lem5385470) (@lem5385473)). Qed.
Lemma lem5385475 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5385476 : term430 = term431.
Proof. exact (MK_COMB (@lem5385475) (@lem5385474)). Qed.
Lemma lem5385477 : term138 = term138.
Proof. exact (eq_refl term138). Qed.
Lemma lem5385478 : term432 = term398.
Proof. exact (MK_COMB (@lem5385476) (@lem5385477)). Qed.
Lemma lem5385480 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5385481 : term398 = term128.
Proof. exact (@lem5385480 term44). Qed.
Lemma lem5385482 : term432 = term128.
Proof. exact (TRANS (@lem5385478) (@lem5385481)). Qed.
Lemma lem5385484 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5385485 : term210 = term211.
Proof. exact (@lem5385484 term44 term44). Qed.
Lemma lem5385486 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5385487 : term213 = term44.
Proof. exact (EQ_MP (@lem5385486) (@lem940073)). Qed.
Lemma lem5385488 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5385489 : term211 = term138.
Proof. exact (MK_COMB (@lem5385488) (@lem5385487)). Qed.
Lemma lem5385490 : term210 = term138.
Proof. exact (TRANS (@lem5385485) (@lem5385489)). Qed.
Lemma lem5385491 : term431 = term431.
Proof. exact (eq_refl term431). Qed.
Lemma lem5385492 : term433 = term398.
Proof. exact (MK_COMB (@lem5385491) (@lem5385490)). Qed.
Lemma lem5385494 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5385495 : term398 = term128.
Proof. exact (@lem5385494 term44). Qed.
Lemma lem5385496 : term433 = term128.
Proof. exact (TRANS (@lem5385492) (@lem5385495)). Qed.
Lemma lem5385497 : term128 = term433.
Proof. exact (SYM (@lem5385496)). Qed.
Lemma lem5385498 : term432 = term433.
Proof. exact (TRANS (@lem5385482) (@lem5385497)). Qed.
Lemma lem5385499 : term422 = term198.
Proof. exact (@lem5385449 (@lem5385498)). Qed.
Lemma lem5385500 : term421 = term198.
Proof. exact (TRANS (@lem5385415) (@lem5385499)). Qed.
Lemma lem5385502 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5385503 : term198 = term128.
Proof. exact (@lem5385502 term128). Qed.
Lemma lem5385504 : term421 = term128.
Proof. exact (TRANS (@lem5385500) (@lem5385503)). Qed.
Lemma lem5385505 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5385506 : term434 = term431.
Proof. exact (MK_COMB (@lem5385505) (@lem5385504)). Qed.
Lemma lem5385507 (_69793 : int) : (real_of_int _69793) = (real_of_int _69793).
Proof. exact (eq_refl (real_of_int _69793)). Qed.
Lemma lem5385508 (_69793 : int) : (term418 _69793) = (term435 _69793).
Proof. exact (MK_COMB (@lem5385506) (@lem5385507 _69793)). Qed.
Lemma lem5385509 (_69793 : int) : (term417 _69793) = (term435 _69793).
Proof. exact (TRANS (@lem5385406 _69793) (@lem5385508 _69793)). Qed.
Lemma lem5385510 (_69793 : int) : (term435 _69793) = term128.
Proof. exact (@lem1982719 (real_of_int _69793)). Qed.
Lemma lem5385511 (_69793 : int) : (term417 _69793) = term128.
Proof. exact (TRANS (@lem5385509 _69793) (@lem5385510 _69793)). Qed.
Lemma lem5385512 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5385513 (_69793 : int) : (term436 _69793) = term178.
Proof. exact (MK_COMB (@lem5385512) (@lem5385511 _69793)). Qed.
Lemma lem5385514 : term201 = term201.
Proof. exact (eq_refl term201). Qed.
Lemma lem5385515 (_69793 : int) : (term416 _69793) = term437.
Proof. exact (MK_COMB (@lem5385513 _69793) (@lem5385514)). Qed.
Lemma lem5385516 (_69793 : int) : (term515 _69793) = term437.
Proof. exact (TRANS (@lem5385405 _69793) (@lem5385515 _69793)). Qed.
Lemma lem5385517 : term437 = term201.
Proof. exact (@lem1982721 term201). Qed.
Lemma lem5385518 (_69793 : int) : (term515 _69793) = term201.
Proof. exact (TRANS (@lem5385516 _69793) (@lem5385517)). Qed.
Lemma lem5385519 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5385520 (_69793 : int) : (term516 _69793) = term439.
Proof. exact (MK_COMB (@lem5385519) (@lem5385518 _69793)). Qed.
Lemma lem5385521 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5385522 (_69793 : int) : (term514 _69793) = term440.
Proof. exact (MK_COMB (@lem5385520 _69793) (@lem5385521)). Qed.
Lemma lem5385523 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term517 _69794 _69795 _69793) : term440.
Proof. exact (EQ_MP (@lem5385522 _69793) (@lem5385404 _69794 _69795 _69793 h1)). Qed.
Lemma lem5385525 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5385526 : term440 = term441.
Proof. exact (@lem5385525 term128 term201). Qed.
Lemma lem5385528 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5385529 : term201 = term202.
Proof. exact (@lem5385528 term44). Qed.
Lemma lem5385531 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5385532 : term128 = term198.
Proof. exact (@lem5385531 (NUMERAL 0)). Qed.
Lemma lem5385533 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5385534 : term130 = term442.
Proof. exact (MK_COMB (@lem5385533) (@lem5385532)). Qed.
Lemma lem5385535 : term441 = term443.
Proof. exact (MK_COMB (@lem5385534) (@lem5385529)). Qed.
Lemma lem5385536 : term444.
Proof. exact (@lem1980026 term128 term138 term201 term138). Qed.
Lemma lem5385538 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5385539 : term245 = term246.
Proof. exact (@lem5385538 (NUMERAL 0) term44). Qed.
Lemma lem5385540 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5385541 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5385542 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5385541 h1) (fun h1 : term246 = True => @lem5385540)). Qed.
Lemma lem5385543 : term246 = True.
Proof. exact (EQ_MP (@lem5385542) (@lem5385540)). Qed.
Lemma lem5385544 : term245 = True.
Proof. exact (TRANS (@lem5385539) (@lem5385543)). Qed.
Lemma lem5385545 : True = term245.
Proof. exact (SYM (@lem5385544)). Qed.
Lemma lem5385546 : term245.
Proof. exact (EQ_MP (@lem5385545) (@lem0)). Qed.
Lemma lem5385547 : term445.
Proof. exact (@lem5385536 (@lem5385546)). Qed.
Lemma lem5385549 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5385550 : term245 = term246.
Proof. exact (@lem5385549 (NUMERAL 0) term44). Qed.
Lemma lem5385551 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5385552 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5385553 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5385552 h1) (fun h1 : term246 = True => @lem5385551)). Qed.
Lemma lem5385554 : term246 = True.
Proof. exact (EQ_MP (@lem5385553) (@lem5385551)). Qed.
Lemma lem5385555 : term245 = True.
Proof. exact (TRANS (@lem5385550) (@lem5385554)). Qed.
Lemma lem5385556 : True = term245.
Proof. exact (SYM (@lem5385555)). Qed.
Lemma lem5385557 : term245.
Proof. exact (EQ_MP (@lem5385556) (@lem0)). Qed.
Lemma lem5385558 : term443 = term446.
Proof. exact (@lem5385547 (@lem5385557)). Qed.
Lemma lem5385560 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5385561 : term302 = term305.
Proof. exact (@lem5385560 term44 term44). Qed.
Lemma lem5385562 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5385563 : term213 = term44.
Proof. exact (EQ_MP (@lem5385562) (@lem940073)). Qed.
Lemma lem5385564 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5385565 : term211 = term138.
Proof. exact (MK_COMB (@lem5385564) (@lem5385563)). Qed.
Lemma lem5385566 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5385567 : term305 = term201.
Proof. exact (MK_COMB (@lem5385566) (@lem5385565)). Qed.
Lemma lem5385568 : term302 = term201.
Proof. exact (TRANS (@lem5385561) (@lem5385567)). Qed.
Lemma lem5385570 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5385571 : term398 = term128.
Proof. exact (@lem5385570 term44). Qed.
Lemma lem5385572 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5385573 : term447 = term130.
Proof. exact (MK_COMB (@lem5385572) (@lem5385571)). Qed.
Lemma lem5385574 : term446 = term441.
Proof. exact (MK_COMB (@lem5385573) (@lem5385568)). Qed.
Lemma lem5385576 (m : nat) (n : nat) : (term448 m n) = (term449 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5385577 : term441 = term450.
Proof. exact (@lem5385576 (NUMERAL 0) term44). Qed.
Lemma lem5385578 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5385579 (h1 : term247 = (BIT1 0)) : (term44 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5385580 : (term247 = (BIT1 0)) = ((term44 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5385579 h1) (fun h1 : (term44 = (NUMERAL 0)) = False => @lem5385578)). Qed.
Lemma lem5385581 : (term44 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5385580) (@lem5385578)). Qed.
Lemma lem5385582 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5385583 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5385584 : term451 = (and True).
Proof. exact (MK_COMB (@lem5385583) (@lem5385582)). Qed.
Lemma lem5385585 : term450 = (True /\ False).
Proof. exact (MK_COMB (@lem5385584) (@lem5385581)). Qed.
Lemma lem5385587 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5385588 : term450 = False.
Proof. exact (TRANS (@lem5385585) (@lem5385587)). Qed.
Lemma lem5385589 : term441 = False.
Proof. exact (TRANS (@lem5385577) (@lem5385588)). Qed.
Lemma lem5385590 : term446 = False.
Proof. exact (TRANS (@lem5385574) (@lem5385589)). Qed.
Lemma lem5385591 : term443 = False.
Proof. exact (TRANS (@lem5385558) (@lem5385590)). Qed.
Lemma lem5385592 : term441 = False.
Proof. exact (TRANS (@lem5385535) (@lem5385591)). Qed.
Lemma lem5385593 : term440 = False.
Proof. exact (TRANS (@lem5385526) (@lem5385592)). Qed.
Lemma lem5385594 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term517 _69794 _69795 _69793) : False.
Proof. exact (EQ_MP (@lem5385593) (@lem5385523 _69794 _69795 _69793 h1)). Qed.
Lemma lem5385595 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term379 _69794 _69795 _69793) : False.
Proof. exact (or_elim (@lem5384518 _69794 _69795 _69793 h1) (fun h0 : term467 _69794 _69795 _69793 => @lem5385299 _69794 _69795 _69793 h0) (fun h0 : term517 _69794 _69795 _69793 => @lem5385594 _69794 _69795 _69793 h0)). Qed.
Lemma lem5385596 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term388 _69794 _69795 _69793) : False.
Proof. exact (or_elim (@lem5383866 _69794 _69795 _69793 h1) (fun h0 : term383 _69794 _69795 _69793 => @lem5384517 _69794 _69795 _69793 h0) (fun h0 : term379 _69794 _69795 _69793 => @lem5385595 _69794 _69795 _69793 h0)). Qed.
Lemma lem5385598 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term388 _69794 _69795 _69793) : term388 _69794 _69795 _69793.
Proof. exact (h1). Qed.
Lemma lem5385599 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term388 _69794 _69795 _69793) : (term388 _69794 _69795 _69793) = False.
Proof. exact (prop_ext (fun h2 : term388 _69794 _69795 _69793 => @lem5385596 _69794 _69795 _69793 h1) (fun h2 : False => @lem5385598 _69794 _69795 _69793 h1)). Qed.
Lemma lem5385600 (_69794 : int) (_69795 : int) (_69793 : int) (h1 : term388 _69794 _69795 _69793) : False.
Proof. exact (EQ_MP (@lem5385599 _69794 _69795 _69793 h1) (@lem5385598 _69794 _69795 _69793 h1)). Qed.
Lemma lem5385601 (_69795 : int) (_69794 : int) (_69793 : int) (h1 : term193 _69795 _69794 _69793) : term193 _69795 _69794 _69793.
Proof. exact (h1). Qed.
Lemma lem5385602 (_69795 : int) (_69794 : int) (_69793 : int) (h1 : term193 _69795 _69794 _69793) : term388 _69794 _69795 _69793.
Proof. exact (EQ_MP (@lem5383844 _69794 _69795 _69793) (@lem5385601 _69795 _69794 _69793 h1)). Qed.
Lemma lem5385603 (_69795 : int) (_69794 : int) (_69793 : int) (h1 : term193 _69795 _69794 _69793) : (term388 _69794 _69795 _69793) = False.
Proof. exact (prop_ext (fun h2 : term388 _69794 _69795 _69793 => @lem5385600 _69794 _69795 _69793 h2) (fun h2 : False => @lem5385602 _69795 _69794 _69793 h1)). Qed.
Lemma lem5385604 (_69795 : int) (_69794 : int) (_69793 : int) (h1 : term193 _69795 _69794 _69793) : False.
Proof. exact (EQ_MP (@lem5385603 _69795 _69794 _69793 h1) (@lem5385602 _69795 _69794 _69793 h1)). Qed.
Lemma lem5385605 (_69795 : int) (_69794 : int) (_69793 : int) : term521 _69795 _69794 _69793.
Proof. exact (fun h0 : term193 _69795 _69794 _69793 => @lem5385604 _69795 _69794 _69793 h0). Qed.
Lemma lem5385606 (_69795 : int) (_69794 : int) (_69793 : int) : term522 _69795 _69794 _69793.
Proof. exact (@lem1386578 (term523 _69795 _69794 _69793)). Qed.
Lemma lem5385609 (_69795 : int) (_69794 : int) (_69793 : int) : term523 _69795 _69794 _69793.
Proof. exact (@lem5385606 _69795 _69794 _69793 (@lem5385605 _69795 _69794 _69793)). Qed.
Lemma lem5385610 (_69795 : int) (_69794 : int) (_69793 : int) : (term191 _69795 _69794 _69793) = (term122 _69795 _69794 _69793).
Proof. exact (SYM (@lem5382982 _69795 _69794 _69793)). Qed.
Lemma lem5385611 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5385612 (_69795 : int) (_69794 : int) (_69793 : int) : (term523 _69795 _69794 _69793) = (term75 _69795 _69794 _69793).
Proof. exact (MK_COMB (@lem5385611) (@lem5385610 _69795 _69794 _69793)). Qed.
Lemma lem5385613 (_69795 : int) (_69794 : int) (_69793 : int) : term75 _69795 _69794 _69793.
Proof. exact (EQ_MP (@lem5385612 _69795 _69794 _69793) (@lem5385609 _69795 _69794 _69793)). Qed.
Lemma lem5385614 (_69795 : int) (_69794 : int) (_69793 : int) : term76 _69795 _69794 _69793.
Proof. exact (EQ_MP (@lem5382683 _69795 _69794 _69793) (@lem5385613 _69795 _69794 _69793)). Qed.
Lemma lem5385615 (n : nat) (m : nat) (d : nat) : term524 n m d.
Proof. exact (@lem5385614 (int_of_num n) (int_of_num m) (int_of_num d)). Qed.
Lemma lem5385616 (n : nat) (m : nat) (d : nat) : term525 n m d.
Proof. exact (@lem5385615 n m d (@lem5382676 d)). Qed.
Lemma lem5385617 (n : nat) (m : nat) (d : nat) : term526 n m d.
Proof. exact (@lem5385616 n m d (@lem5382679 m)). Qed.
Lemma lem5385618 (n : nat) (m : nat) (d : nat) : term70 n m d.
Proof. exact (@lem5385617 n m d (@lem5382682 n)). Qed.
Lemma lem5385619 (n : nat) (m : nat) : term72 n m.
Proof. exact (fun d : nat => @lem5385618 n m d). Qed.
Lemma lem5385620 (n : nat) (m : nat) : (term72 n m) = (term14 n m).
Proof. exact (SYM (@lem5382673 n m)). Qed.
Lemma lem5385621 (n : nat) (m : nat) : term14 n m.
Proof. exact (EQ_MP (@lem5385620 n m) (@lem5385619 n m)). Qed.
Lemma lem5385632 (n : nat) : term527 n.
Proof. exact (fun m : nat => @lem5385621 n m). Qed.
Lemma lem5385633 : term528.
Proof. exact (fun n : nat => @lem5385632 n). Qed.
Lemma lem5385676 (m : nat) (n : nat) : (Peano.lt m n) = (term49 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem5385677 (n : nat) (m : nat) : (Peano.lt n m) = (term49 n m).
Proof. exact (@lem5385676 n m). Qed.
Lemma lem5385678 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5385679 (n : nat) (m : nat) : (term529 n m) = (term530 n m).
Proof. exact (MK_COMB (@lem5385678) (@lem5385677 n m)). Qed.
Lemma lem5385681 (m : nat) (n : nat) : (Peano.le m n) = (term531 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5385683 (m : nat) (n : nat) : (term532 m n) = (term533 m n).
Proof. exact (MK_COMB (@lem5385679 n m) (@lem5385681 m n)). Qed.
Lemma lem5385684 (m : nat) : term73 m.
Proof. exact (@lem2307535 m). Qed.
Lemma lem5385685 (m : nat) : (term73 m) = (term74 m).
Proof. exact (eq_refl (term73 m)). Qed.
Lemma lem5385686 (m : nat) : term74 m.
Proof. exact (EQ_MP (@lem5385685 m) (@lem5385684 m)). Qed.
Lemma lem5385687 (n : nat) : term73 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem5385688 (n : nat) : (term73 n) = (term74 n).
Proof. exact (eq_refl (term73 n)). Qed.
Lemma lem5385689 (n : nat) : term74 n.
Proof. exact (EQ_MP (@lem5385688 n) (@lem5385687 n)). Qed.
Lemma lem5385690 (_69799 : int) (_69800 : int) : (term534 _69799 _69800) = (term535 _69799 _69800).
Proof. exact (@lem2318604 (term535 _69799 _69800)). Qed.
Lemma lem5385710 (_69799 : int) (_69800 : int) : (term536 _69799 _69800) = (term537 _69799 _69800).
Proof. exact (@lem17160 (int_lt _69800 _69799) (int_le _69799 _69800)). Qed.
Lemma lem5385712 (_69800 : int) : (term110 _69800) = (term110 _69800).
Proof. exact (eq_refl (term110 _69800)). Qed.
Lemma lem5385713 (_69799 : int) (_69800 : int) : (term538 _69799 _69800) = (term539 _69799 _69800).
Proof. exact (MK_COMB (@lem5385712 _69800) (@lem5385710 _69799 _69800)). Qed.
Lemma lem5385714 (_69799 : int) (_69800 : int) : (term540 _69799 _69800) = (term538 _69799 _69800).
Proof. exact (@lem17362 (term114 _69800) (term541 _69799 _69800)). Qed.
Lemma lem5385715 (_69799 : int) (_69800 : int) : (term540 _69799 _69800) = (term539 _69799 _69800).
Proof. exact (TRANS (@lem5385714 _69799 _69800) (@lem5385713 _69799 _69800)). Qed.
Lemma lem5385717 (_69799 : int) : (term110 _69799) = (term110 _69799).
Proof. exact (eq_refl (term110 _69799)). Qed.
Lemma lem5385718 (_69799 : int) (_69800 : int) : (term542 _69799 _69800) = (term543 _69799 _69800).
Proof. exact (MK_COMB (@lem5385717 _69799) (@lem5385715 _69799 _69800)). Qed.
Lemma lem5385719 (_69799 : int) (_69800 : int) : (term544 _69799 _69800) = (term542 _69799 _69800).
Proof. exact (@lem17362 (term114 _69799) (term545 _69799 _69800)). Qed.
Lemma lem5385739 (_69799 : int) (_69800 : int) : (term544 _69799 _69800) = (term543 _69799 _69800).
Proof. exact (TRANS (@lem5385719 _69799 _69800) (@lem5385718 _69799 _69800)). Qed.
Lemma lem5385742 (x : int) (y : int) : (int_le x y) = (term124 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5385743 (_69799 : int) : (term114 _69799) = (term125 _69799).
Proof. exact (@lem5385742 term59 _69799). Qed.
Lemma lem5385745 (n : nat) : (term126 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5385746 : term127 = term128.
Proof. exact (@lem5385745 (NUMERAL 0)). Qed.
Lemma lem5385747 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5385748 : term129 = term130.
Proof. exact (MK_COMB (@lem5385747) (@lem5385746)). Qed.
Lemma lem5385749 (_69799 : int) : (real_of_int _69799) = (real_of_int _69799).
Proof. exact (eq_refl (real_of_int _69799)). Qed.
Lemma lem5385750 (_69799 : int) : (term125 _69799) = (term131 _69799).
Proof. exact (MK_COMB (@lem5385748) (@lem5385749 _69799)). Qed.
Lemma lem5385752 (_69799 : int) : (term114 _69799) = (term131 _69799).
Proof. exact (TRANS (@lem5385743 _69799) (@lem5385750 _69799)). Qed.
Lemma lem5385755 (x : int) (y : int) : (int_le x y) = (term124 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5385756 (_69800 : int) : (term114 _69800) = (term125 _69800).
Proof. exact (@lem5385755 term59 _69800). Qed.
Lemma lem5385758 (n : nat) : (term126 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5385759 : term127 = term128.
Proof. exact (@lem5385758 (NUMERAL 0)). Qed.
Lemma lem5385760 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5385761 : term129 = term130.
Proof. exact (MK_COMB (@lem5385760) (@lem5385759)). Qed.
Lemma lem5385762 (_69800 : int) : (real_of_int _69800) = (real_of_int _69800).
Proof. exact (eq_refl (real_of_int _69800)). Qed.
Lemma lem5385763 (_69800 : int) : (term125 _69800) = (term131 _69800).
Proof. exact (MK_COMB (@lem5385761) (@lem5385762 _69800)). Qed.
Lemma lem5385765 (_69800 : int) : (term114 _69800) = (term131 _69800).
Proof. exact (TRANS (@lem5385756 _69800) (@lem5385763 _69800)). Qed.
Lemma lem5385767 (y : int) (x : int) : (term102 x y) = (int_le y x).
Proof. exact (proj1 (@lem2318496 x y)). Qed.
Lemma lem5385768 (_69799 : int) (_69800 : int) : (term102 _69800 _69799) = (int_le _69799 _69800).
Proof. exact (@lem5385767 _69799 _69800). Qed.
Lemma lem5385770 (x : int) (y : int) : (int_le x y) = (term124 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5385771 (_69799 : int) (_69800 : int) : (int_le _69799 _69800) = (term124 _69799 _69800).
Proof. exact (@lem5385770 _69799 _69800). Qed.
Lemma lem5385772 (_69799 : int) (_69800 : int) : (term102 _69800 _69799) = (term124 _69799 _69800).
Proof. exact (TRANS (@lem5385768 _69799 _69800) (@lem5385771 _69799 _69800)). Qed.
Lemma lem5385774 (y : int) (x : int) : (term546 x y) = (term143 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5385775 (_69800 : int) (_69799 : int) : (term546 _69799 _69800) = (term143 _69800 _69799).
Proof. exact (@lem5385774 _69800 _69799). Qed.
Lemma lem5385777 (x : int) (y : int) : (int_le x y) = (term124 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5385778 (_69800 : int) (_69799 : int) : (term143 _69800 _69799) = (term160 _69800 _69799).
Proof. exact (@lem5385777 (term78 _69800) _69799). Qed.
Lemma lem5385780 (x : int) (y : int) : (term133 x y) = (term134 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5385781 (_69800 : int) : (term132 _69800) = (term135 _69800).
Proof. exact (@lem5385780 _69800 term136). Qed.
Lemma lem5385783 (n : nat) : (term126 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5385784 : term137 = term138.
Proof. exact (@lem5385783 term44). Qed.
Lemma lem5385785 (_69800 : int) : (term139 _69800) = (term139 _69800).
Proof. exact (eq_refl (term139 _69800)). Qed.
Lemma lem5385786 (_69800 : int) : (term135 _69800) = (term140 _69800).
Proof. exact (MK_COMB (@lem5385785 _69800) (@lem5385784)). Qed.
Lemma lem5385787 (_69800 : int) : (term132 _69800) = (term140 _69800).
Proof. exact (TRANS (@lem5385781 _69800) (@lem5385786 _69800)). Qed.
Lemma lem5385788 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5385789 (_69800 : int) : (term161 _69800) = (term162 _69800).
Proof. exact (MK_COMB (@lem5385788) (@lem5385787 _69800)). Qed.
Lemma lem5385790 (_69799 : int) : (real_of_int _69799) = (real_of_int _69799).
Proof. exact (eq_refl (real_of_int _69799)). Qed.
Lemma lem5385791 (_69800 : int) (_69799 : int) : (term160 _69800 _69799) = (term163 _69800 _69799).
Proof. exact (MK_COMB (@lem5385789 _69800) (@lem5385790 _69799)). Qed.
Lemma lem5385792 (_69800 : int) (_69799 : int) : (term143 _69800 _69799) = (term163 _69800 _69799).
Proof. exact (TRANS (@lem5385778 _69800 _69799) (@lem5385791 _69800 _69799)). Qed.
Lemma lem5385793 (_69800 : int) (_69799 : int) : (term546 _69799 _69800) = (term163 _69800 _69799).
Proof. exact (TRANS (@lem5385775 _69800 _69799) (@lem5385792 _69800 _69799)). Qed.
Lemma lem5385794 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5385795 (_69799 : int) (_69800 : int) : (term547 _69800 _69799) = (term548 _69799 _69800).
Proof. exact (MK_COMB (@lem5385794) (@lem5385772 _69799 _69800)). Qed.
Lemma lem5385796 (_69800 : int) (_69799 : int) : (term537 _69799 _69800) = (term549 _69800 _69799).
Proof. exact (MK_COMB (@lem5385795 _69799 _69800) (@lem5385793 _69800 _69799)). Qed.
Lemma lem5385797 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5385798 (_69800 : int) : (term110 _69800) = (term188 _69800).
Proof. exact (MK_COMB (@lem5385797) (@lem5385765 _69800)). Qed.
Lemma lem5385799 (_69800 : int) (_69799 : int) : (term539 _69799 _69800) = (term550 _69800 _69799).
Proof. exact (MK_COMB (@lem5385798 _69800) (@lem5385796 _69800 _69799)). Qed.
Lemma lem5385800 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5385801 (_69799 : int) : (term110 _69799) = (term188 _69799).
Proof. exact (MK_COMB (@lem5385800) (@lem5385752 _69799)). Qed.
Lemma lem5385802 (_69800 : int) (_69799 : int) : (term543 _69799 _69800) = (term551 _69800 _69799).
Proof. exact (MK_COMB (@lem5385801 _69799) (@lem5385799 _69800 _69799)). Qed.
Lemma lem5385803 (_69800 : int) (_69799 : int) : (term544 _69799 _69800) = (term551 _69800 _69799).
Proof. exact (TRANS (@lem5385739 _69799 _69800) (@lem5385802 _69800 _69799)). Qed.
Lemma lem5385807 (t : Prop) : (term192 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5385843 (_69800 : int) (_69799 : int) : (term552 _69800 _69799) = (term551 _69800 _69799).
Proof. exact (@lem5385807 (term551 _69800 _69799)). Qed.
Lemma lem5385844 (_69799 : int) : (term131 _69799) = (term194 _69799).
Proof. exact (@lem1988287 (real_of_int _69799) term128). Qed.
Lemma lem5385850 (_69799 : int) : (term195 _69799) = (term196 _69799).
Proof. exact (@lem1982792 (real_of_int _69799) term128). Qed.
Lemma lem5385852 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5385853 : term128 = term198.
Proof. exact (@lem5385852 (NUMERAL 0)). Qed.
Lemma lem5385855 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5385856 : term201 = term202.
Proof. exact (@lem5385855 term44). Qed.
Lemma lem5385857 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5385858 : term203 = term204.
Proof. exact (MK_COMB (@lem5385857) (@lem5385856)). Qed.
Lemma lem5385859 : term205 = term206.
Proof. exact (MK_COMB (@lem5385858) (@lem5385853)). Qed.
Lemma lem5385860 : term206 = term207.
Proof. exact (@lem1981613 term201 term128 term138 term138). Qed.
Lemma lem5385862 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5385863 : term210 = term211.
Proof. exact (@lem5385862 term44 term44). Qed.
Lemma lem5385864 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5385865 : term213 = term44.
Proof. exact (EQ_MP (@lem5385864) (@lem940073)). Qed.
Lemma lem5385866 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5385867 : term211 = term138.
Proof. exact (MK_COMB (@lem5385866) (@lem5385865)). Qed.
Lemma lem5385868 : term210 = term138.
Proof. exact (TRANS (@lem5385863) (@lem5385867)). Qed.
Lemma lem5385870 (x : nat) : (term214 x) = term128.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5385871 : term205 = term128.
Proof. exact (@lem5385870 term44). Qed.
Lemma lem5385872 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5385873 : term215 = term216.
Proof. exact (MK_COMB (@lem5385872) (@lem5385871)). Qed.
Lemma lem5385874 : term207 = term198.
Proof. exact (MK_COMB (@lem5385873) (@lem5385868)). Qed.
Lemma lem5385875 : term206 = term198.
Proof. exact (TRANS (@lem5385860) (@lem5385874)). Qed.
Lemma lem5385876 : term205 = term198.
Proof. exact (TRANS (@lem5385859) (@lem5385875)). Qed.
Lemma lem5385878 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5385879 : term198 = term128.
Proof. exact (@lem5385878 term128). Qed.
Lemma lem5385880 : term205 = term128.
Proof. exact (TRANS (@lem5385876) (@lem5385879)). Qed.
Lemma lem5385881 (_69799 : int) : (term139 _69799) = (term139 _69799).
Proof. exact (eq_refl (term139 _69799)). Qed.
Lemma lem5385882 (_69799 : int) : (term196 _69799) = (term218 _69799).
Proof. exact (MK_COMB (@lem5385881 _69799) (@lem5385880)). Qed.
Lemma lem5385883 (_69799 : int) : (term218 _69799) = (real_of_int _69799).
Proof. exact (@lem1982723 (real_of_int _69799)). Qed.
Lemma lem5385884 (_69799 : int) : (term196 _69799) = (real_of_int _69799).
Proof. exact (TRANS (@lem5385882 _69799) (@lem5385883 _69799)). Qed.
Lemma lem5385886 (_69799 : int) : (term195 _69799) = (real_of_int _69799).
Proof. exact (TRANS (@lem5385850 _69799) (@lem5385884 _69799)). Qed.
Lemma lem5385887 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5385888 (_69799 : int) : (term219 _69799) = (term220 _69799).
Proof. exact (MK_COMB (@lem5385887) (@lem5385886 _69799)). Qed.
Lemma lem5385889 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5385890 (_69799 : int) : (term194 _69799) = (term221 _69799).
Proof. exact (MK_COMB (@lem5385888 _69799) (@lem5385889)). Qed.
Lemma lem5385891 (_69799 : int) : (term131 _69799) = (term221 _69799).
Proof. exact (TRANS (@lem5385844 _69799) (@lem5385890 _69799)). Qed.
Lemma lem5385892 (_69800 : int) : (term131 _69800) = (term194 _69800).
Proof. exact (@lem1988287 (real_of_int _69800) term128). Qed.
Lemma lem5385898 (_69800 : int) : (term195 _69800) = (term196 _69800).
Proof. exact (@lem1982792 (real_of_int _69800) term128). Qed.
Lemma lem5385900 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5385901 : term128 = term198.
Proof. exact (@lem5385900 (NUMERAL 0)). Qed.
Lemma lem5385903 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5385904 : term201 = term202.
Proof. exact (@lem5385903 term44). Qed.
Lemma lem5385905 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5385906 : term203 = term204.
Proof. exact (MK_COMB (@lem5385905) (@lem5385904)). Qed.
Lemma lem5385907 : term205 = term206.
Proof. exact (MK_COMB (@lem5385906) (@lem5385901)). Qed.
Lemma lem5385908 : term206 = term207.
Proof. exact (@lem1981613 term201 term128 term138 term138). Qed.
Lemma lem5385910 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5385911 : term210 = term211.
Proof. exact (@lem5385910 term44 term44). Qed.
Lemma lem5385912 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5385913 : term213 = term44.
Proof. exact (EQ_MP (@lem5385912) (@lem940073)). Qed.
Lemma lem5385914 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5385915 : term211 = term138.
Proof. exact (MK_COMB (@lem5385914) (@lem5385913)). Qed.
Lemma lem5385916 : term210 = term138.
Proof. exact (TRANS (@lem5385911) (@lem5385915)). Qed.
Lemma lem5385918 (x : nat) : (term214 x) = term128.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5385919 : term205 = term128.
Proof. exact (@lem5385918 term44). Qed.
Lemma lem5385920 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5385921 : term215 = term216.
Proof. exact (MK_COMB (@lem5385920) (@lem5385919)). Qed.
Lemma lem5385922 : term207 = term198.
Proof. exact (MK_COMB (@lem5385921) (@lem5385916)). Qed.
Lemma lem5385923 : term206 = term198.
Proof. exact (TRANS (@lem5385908) (@lem5385922)). Qed.
Lemma lem5385924 : term205 = term198.
Proof. exact (TRANS (@lem5385907) (@lem5385923)). Qed.
Lemma lem5385926 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5385927 : term198 = term128.
Proof. exact (@lem5385926 term128). Qed.
Lemma lem5385928 : term205 = term128.
Proof. exact (TRANS (@lem5385924) (@lem5385927)). Qed.
Lemma lem5385929 (_69800 : int) : (term139 _69800) = (term139 _69800).
Proof. exact (eq_refl (term139 _69800)). Qed.
Lemma lem5385930 (_69800 : int) : (term196 _69800) = (term218 _69800).
Proof. exact (MK_COMB (@lem5385929 _69800) (@lem5385928)). Qed.
Lemma lem5385931 (_69800 : int) : (term218 _69800) = (real_of_int _69800).
Proof. exact (@lem1982723 (real_of_int _69800)). Qed.
Lemma lem5385932 (_69800 : int) : (term196 _69800) = (real_of_int _69800).
Proof. exact (TRANS (@lem5385930 _69800) (@lem5385931 _69800)). Qed.
Lemma lem5385934 (_69800 : int) : (term195 _69800) = (real_of_int _69800).
Proof. exact (TRANS (@lem5385898 _69800) (@lem5385932 _69800)). Qed.
Lemma lem5385935 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5385936 (_69800 : int) : (term219 _69800) = (term220 _69800).
Proof. exact (MK_COMB (@lem5385935) (@lem5385934 _69800)). Qed.
Lemma lem5385937 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5385938 (_69800 : int) : (term194 _69800) = (term221 _69800).
Proof. exact (MK_COMB (@lem5385936 _69800) (@lem5385937)). Qed.
Lemma lem5385939 (_69800 : int) : (term131 _69800) = (term221 _69800).
Proof. exact (TRANS (@lem5385892 _69800) (@lem5385938 _69800)). Qed.
Lemma lem5385940 (_69800 : int) (_69799 : int) : (term124 _69799 _69800) = (term553 _69800 _69799).
Proof. exact (@lem1988287 (real_of_int _69800) (real_of_int _69799)). Qed.
Lemma lem5385946 (_69800 : int) (_69799 : int) : (term554 _69800 _69799) = (term555 _69800 _69799).
Proof. exact (@lem1982792 (real_of_int _69800) (real_of_int _69799)). Qed.
Lemma lem5385951 (_69799 : int) (_69800 : int) : (term555 _69800 _69799) = (term556 _69799 _69800).
Proof. exact (@lem1982761 (term228 _69799) (real_of_int _69800)). Qed.
Lemma lem5385953 (_69799 : int) (_69800 : int) : (term554 _69800 _69799) = (term556 _69799 _69800).
Proof. exact (TRANS (@lem5385946 _69800 _69799) (@lem5385951 _69799 _69800)). Qed.
Lemma lem5385954 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5385955 (_69799 : int) (_69800 : int) : (term557 _69800 _69799) = (term558 _69799 _69800).
Proof. exact (MK_COMB (@lem5385954) (@lem5385953 _69799 _69800)). Qed.
Lemma lem5385956 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5385957 (_69799 : int) (_69800 : int) : (term553 _69800 _69799) = (term559 _69799 _69800).
Proof. exact (MK_COMB (@lem5385955 _69799 _69800) (@lem5385956)). Qed.
Lemma lem5385958 (_69799 : int) (_69800 : int) : (term124 _69799 _69800) = (term559 _69799 _69800).
Proof. exact (TRANS (@lem5385940 _69800 _69799) (@lem5385957 _69799 _69800)). Qed.
Lemma lem5385959 (_69799 : int) (_69800 : int) : (term163 _69800 _69799) = (term297 _69799 _69800).
Proof. exact (@lem1988287 (real_of_int _69799) (term140 _69800)). Qed.
Lemma lem5385971 (_69799 : int) (_69800 : int) : (term298 _69799 _69800) = (term299 _69799 _69800).
Proof. exact (@lem1982792 (real_of_int _69799) (term140 _69800)). Qed.
Lemma lem5385972 (_69800 : int) : (term300 _69800) = (term301 _69800).
Proof. exact (@lem1982781 (real_of_int _69800) term201 term138). Qed.
Lemma lem5385974 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5385975 : term138 = term237.
Proof. exact (@lem5385974 term44). Qed.
Lemma lem5385977 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5385978 : term201 = term202.
Proof. exact (@lem5385977 term44). Qed.
Lemma lem5385979 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5385980 : term203 = term204.
Proof. exact (MK_COMB (@lem5385979) (@lem5385978)). Qed.
Lemma lem5385981 : term302 = term303.
Proof. exact (MK_COMB (@lem5385980) (@lem5385975)). Qed.
Lemma lem5385982 : term303 = term304.
Proof. exact (@lem1981613 term201 term138 term138 term138). Qed.
Lemma lem5385984 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5385985 : term210 = term211.
Proof. exact (@lem5385984 term44 term44). Qed.
Lemma lem5385986 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5385987 : term213 = term44.
Proof. exact (EQ_MP (@lem5385986) (@lem940073)). Qed.
Lemma lem5385988 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5385989 : term211 = term138.
Proof. exact (MK_COMB (@lem5385988) (@lem5385987)). Qed.
Lemma lem5385990 : term210 = term138.
Proof. exact (TRANS (@lem5385985) (@lem5385989)). Qed.
Lemma lem5385992 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5385993 : term302 = term305.
Proof. exact (@lem5385992 term44 term44). Qed.
Lemma lem5385994 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5385995 : term213 = term44.
Proof. exact (EQ_MP (@lem5385994) (@lem940073)). Qed.
Lemma lem5385996 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5385997 : term211 = term138.
Proof. exact (MK_COMB (@lem5385996) (@lem5385995)). Qed.
Lemma lem5385998 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5385999 : term305 = term201.
Proof. exact (MK_COMB (@lem5385998) (@lem5385997)). Qed.
Lemma lem5386000 : term302 = term201.
Proof. exact (TRANS (@lem5385993) (@lem5385999)). Qed.
Lemma lem5386001 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5386002 : term306 = term307.
Proof. exact (MK_COMB (@lem5386001) (@lem5386000)). Qed.
Lemma lem5386003 : term304 = term202.
Proof. exact (MK_COMB (@lem5386002) (@lem5385990)). Qed.
Lemma lem5386004 : term303 = term202.
Proof. exact (TRANS (@lem5385982) (@lem5386003)). Qed.
Lemma lem5386005 : term302 = term202.
Proof. exact (TRANS (@lem5385981) (@lem5386004)). Qed.
Lemma lem5386007 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5386008 : term202 = term201.
Proof. exact (@lem5386007 term201). Qed.
Lemma lem5386009 : term302 = term201.
Proof. exact (TRANS (@lem5386005) (@lem5386008)). Qed.
Lemma lem5386012 (_69800 : int) : (term231 _69800) = (term231 _69800).
Proof. exact (eq_refl (term231 _69800)). Qed.
Lemma lem5386013 (_69800 : int) : (term301 _69800) = (term308 _69800).
Proof. exact (MK_COMB (@lem5386012 _69800) (@lem5386009)). Qed.
Lemma lem5386014 (_69800 : int) : (term300 _69800) = (term308 _69800).
Proof. exact (TRANS (@lem5385972 _69800) (@lem5386013 _69800)). Qed.
Lemma lem5386015 (_69799 : int) : (term139 _69799) = (term139 _69799).
Proof. exact (eq_refl (term139 _69799)). Qed.
Lemma lem5386018 (_69799 : int) (_69800 : int) : (term299 _69799 _69800) = (term309 _69799 _69800).
Proof. exact (MK_COMB (@lem5386015 _69799) (@lem5386014 _69800)). Qed.
Lemma lem5386020 (_69799 : int) (_69800 : int) : (term298 _69799 _69800) = (term309 _69799 _69800).
Proof. exact (TRANS (@lem5385971 _69799 _69800) (@lem5386018 _69799 _69800)). Qed.
Lemma lem5386021 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5386022 (_69799 : int) (_69800 : int) : (term310 _69799 _69800) = (term311 _69799 _69800).
Proof. exact (MK_COMB (@lem5386021) (@lem5386020 _69799 _69800)). Qed.
Lemma lem5386023 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5386024 (_69799 : int) (_69800 : int) : (term297 _69799 _69800) = (term312 _69799 _69800).
Proof. exact (MK_COMB (@lem5386022 _69799 _69800) (@lem5386023)). Qed.
Lemma lem5386025 (_69799 : int) (_69800 : int) : (term163 _69800 _69799) = (term312 _69799 _69800).
Proof. exact (TRANS (@lem5385959 _69799 _69800) (@lem5386024 _69799 _69800)). Qed.
Lemma lem5386026 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5386027 (_69799 : int) (_69800 : int) : (term548 _69799 _69800) = (term560 _69799 _69800).
Proof. exact (MK_COMB (@lem5386026) (@lem5385958 _69799 _69800)). Qed.
Lemma lem5386028 (_69799 : int) (_69800 : int) : (term549 _69800 _69799) = (term561 _69799 _69800).
Proof. exact (MK_COMB (@lem5386027 _69799 _69800) (@lem5386025 _69799 _69800)). Qed.
Lemma lem5386029 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5386030 (_69800 : int) : (term188 _69800) = (term334 _69800).
Proof. exact (MK_COMB (@lem5386029) (@lem5385939 _69800)). Qed.
Lemma lem5386031 (_69799 : int) (_69800 : int) : (term550 _69800 _69799) = (term562 _69799 _69800).
Proof. exact (MK_COMB (@lem5386030 _69800) (@lem5386028 _69799 _69800)). Qed.
Lemma lem5386032 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5386033 (_69799 : int) : (term188 _69799) = (term334 _69799).
Proof. exact (MK_COMB (@lem5386032) (@lem5385891 _69799)). Qed.
Lemma lem5386034 (_69799 : int) (_69800 : int) : (term551 _69800 _69799) = (term563 _69799 _69800).
Proof. exact (MK_COMB (@lem5386033 _69799) (@lem5386031 _69799 _69800)). Qed.
Lemma lem5386061 (_69799 : int) (_69800 : int) : (term552 _69800 _69799) = (term563 _69799 _69800).
Proof. exact (TRANS (@lem5385843 _69800 _69799) (@lem5386034 _69799 _69800)). Qed.
Lemma lem5386065 (_69799 : int) (_69800 : int) (h1 : term563 _69799 _69800) : term563 _69799 _69800.
Proof. exact (h1). Qed.
Lemma lem5386066 (_69799 : int) (_69800 : int) (h1 : term563 _69799 _69800) : term562 _69799 _69800.
Proof. exact (proj2 (@lem5386065 _69799 _69800 h1)). Qed.
Lemma lem5386068 (_69799 : int) (_69800 : int) (h1 : term563 _69799 _69800) : term561 _69799 _69800.
Proof. exact (proj2 (@lem5386066 _69799 _69800 h1)). Qed.
Lemma lem5386070 (_69799 : int) (_69800 : int) (h1 : term563 _69799 _69800) : term312 _69799 _69800.
Proof. exact (proj2 (@lem5386068 _69799 _69800 h1)). Qed.
Lemma lem5386071 (_69799 : int) (_69800 : int) (h1 : term563 _69799 _69800) : term559 _69799 _69800.
Proof. exact (proj1 (@lem5386068 _69799 _69800 h1)). Qed.
Lemma lem5386073 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5386074 : term390 = term245.
Proof. exact (@lem5386073 term128 term138). Qed.
Lemma lem5386076 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5386077 : term138 = term237.
Proof. exact (@lem5386076 term44). Qed.
Lemma lem5386079 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5386080 : term128 = term198.
Proof. exact (@lem5386079 (NUMERAL 0)). Qed.
Lemma lem5386081 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5386082 : term391 = term392.
Proof. exact (MK_COMB (@lem5386081) (@lem5386080)). Qed.
Lemma lem5386083 : term245 = term393.
Proof. exact (MK_COMB (@lem5386082) (@lem5386077)). Qed.
Lemma lem5386084 : term394.
Proof. exact (@lem1980255 term128 term138 term138 term138). Qed.
Lemma lem5386086 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5386087 : term245 = term246.
Proof. exact (@lem5386086 (NUMERAL 0) term44). Qed.
Lemma lem5386088 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5386089 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5386090 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5386089 h1) (fun h1 : term246 = True => @lem5386088)). Qed.
Lemma lem5386091 : term246 = True.
Proof. exact (EQ_MP (@lem5386090) (@lem5386088)). Qed.
Lemma lem5386092 : term245 = True.
Proof. exact (TRANS (@lem5386087) (@lem5386091)). Qed.
Lemma lem5386093 : True = term245.
Proof. exact (SYM (@lem5386092)). Qed.
Lemma lem5386094 : term245.
Proof. exact (EQ_MP (@lem5386093) (@lem0)). Qed.
Lemma lem5386095 : term395.
Proof. exact (@lem5386084 (@lem5386094)). Qed.
Lemma lem5386097 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5386098 : term245 = term246.
Proof. exact (@lem5386097 (NUMERAL 0) term44). Qed.
Lemma lem5386099 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5386100 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5386101 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5386100 h1) (fun h1 : term246 = True => @lem5386099)). Qed.
Lemma lem5386102 : term246 = True.
Proof. exact (EQ_MP (@lem5386101) (@lem5386099)). Qed.
Lemma lem5386103 : term245 = True.
Proof. exact (TRANS (@lem5386098) (@lem5386102)). Qed.
Lemma lem5386104 : True = term245.
Proof. exact (SYM (@lem5386103)). Qed.
Lemma lem5386105 : term245.
Proof. exact (EQ_MP (@lem5386104) (@lem0)). Qed.
Lemma lem5386106 : term393 = term396.
Proof. exact (@lem5386095 (@lem5386105)). Qed.
Lemma lem5386108 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5386109 : term210 = term211.
Proof. exact (@lem5386108 term44 term44). Qed.
Lemma lem5386110 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5386111 : term213 = term44.
Proof. exact (EQ_MP (@lem5386110) (@lem940073)). Qed.
Lemma lem5386112 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5386113 : term211 = term138.
Proof. exact (MK_COMB (@lem5386112) (@lem5386111)). Qed.
Lemma lem5386114 : term210 = term138.
Proof. exact (TRANS (@lem5386109) (@lem5386113)). Qed.
Lemma lem5386116 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5386117 : term398 = term128.
Proof. exact (@lem5386116 term44). Qed.
Lemma lem5386118 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5386119 : term399 = term391.
Proof. exact (MK_COMB (@lem5386118) (@lem5386117)). Qed.
Lemma lem5386120 : term396 = term245.
Proof. exact (MK_COMB (@lem5386119) (@lem5386114)). Qed.
Lemma lem5386122 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5386123 : term245 = term246.
Proof. exact (@lem5386122 (NUMERAL 0) term44). Qed.
Lemma lem5386124 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5386125 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5386126 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5386125 h1) (fun h1 : term246 = True => @lem5386124)). Qed.
Lemma lem5386127 : term246 = True.
Proof. exact (EQ_MP (@lem5386126) (@lem5386124)). Qed.
Lemma lem5386128 : term245 = True.
Proof. exact (TRANS (@lem5386123) (@lem5386127)). Qed.
Lemma lem5386129 : term396 = True.
Proof. exact (TRANS (@lem5386120) (@lem5386128)). Qed.
Lemma lem5386130 : term393 = True.
Proof. exact (TRANS (@lem5386106) (@lem5386129)). Qed.
Lemma lem5386131 : term245 = True.
Proof. exact (TRANS (@lem5386083) (@lem5386130)). Qed.
Lemma lem5386132 : term390 = True.
Proof. exact (TRANS (@lem5386074) (@lem5386131)). Qed.
Lemma lem5386133 : True = term390.
Proof. exact (SYM (@lem5386132)). Qed.
Lemma lem5386134 : term390.
Proof. exact (EQ_MP (@lem5386133) (@lem0)). Qed.
Lemma lem5386135 (_69799 : int) (_69800 : int) (h1 : term563 _69799 _69800) : term473 _69799 _69800.
Proof. exact (conj (@lem5386134) (@lem5386070 _69799 _69800 h1)). Qed.
Lemma lem5386137 (x : real) (y : real) : term401 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5386138 (_69799 : int) (_69800 : int) : term474 _69799 _69800.
Proof. exact (@lem5386137 term138 (term309 _69799 _69800)). Qed.
Lemma lem5386139 (_69799 : int) (_69800 : int) (h1 : term563 _69799 _69800) : term475 _69799 _69800.
Proof. exact (@lem5386138 _69799 _69800 (@lem5386135 _69799 _69800 h1)). Qed.
Lemma lem5386140 (_69799 : int) (_69800 : int) : (term476 _69799 _69800) = (term309 _69799 _69800).
Proof. exact (@lem1982733 (term309 _69799 _69800)). Qed.
Lemma lem5386141 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5386142 (_69799 : int) (_69800 : int) : (term477 _69799 _69800) = (term311 _69799 _69800).
Proof. exact (MK_COMB (@lem5386141) (@lem5386140 _69799 _69800)). Qed.
Lemma lem5386143 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5386144 (_69799 : int) (_69800 : int) : (term475 _69799 _69800) = (term312 _69799 _69800).
Proof. exact (MK_COMB (@lem5386142 _69799 _69800) (@lem5386143)). Qed.
Lemma lem5386145 (_69799 : int) (_69800 : int) (h1 : term563 _69799 _69800) : term312 _69799 _69800.
Proof. exact (EQ_MP (@lem5386144 _69799 _69800) (@lem5386139 _69799 _69800 h1)). Qed.
Lemma lem5386147 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5386148 : term390 = term245.
Proof. exact (@lem5386147 term128 term138). Qed.
Lemma lem5386150 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5386151 : term138 = term237.
Proof. exact (@lem5386150 term44). Qed.
Lemma lem5386153 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5386154 : term128 = term198.
Proof. exact (@lem5386153 (NUMERAL 0)). Qed.
Lemma lem5386155 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5386156 : term391 = term392.
Proof. exact (MK_COMB (@lem5386155) (@lem5386154)). Qed.
Lemma lem5386157 : term245 = term393.
Proof. exact (MK_COMB (@lem5386156) (@lem5386151)). Qed.
Lemma lem5386158 : term394.
Proof. exact (@lem1980255 term128 term138 term138 term138). Qed.
Lemma lem5386160 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5386161 : term245 = term246.
Proof. exact (@lem5386160 (NUMERAL 0) term44). Qed.
Lemma lem5386162 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5386163 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5386164 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5386163 h1) (fun h1 : term246 = True => @lem5386162)). Qed.
Lemma lem5386165 : term246 = True.
Proof. exact (EQ_MP (@lem5386164) (@lem5386162)). Qed.
Lemma lem5386166 : term245 = True.
Proof. exact (TRANS (@lem5386161) (@lem5386165)). Qed.
Lemma lem5386167 : True = term245.
Proof. exact (SYM (@lem5386166)). Qed.
Lemma lem5386168 : term245.
Proof. exact (EQ_MP (@lem5386167) (@lem0)). Qed.
Lemma lem5386169 : term395.
Proof. exact (@lem5386158 (@lem5386168)). Qed.
Lemma lem5386171 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5386172 : term245 = term246.
Proof. exact (@lem5386171 (NUMERAL 0) term44). Qed.
Lemma lem5386173 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5386174 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5386175 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5386174 h1) (fun h1 : term246 = True => @lem5386173)). Qed.
Lemma lem5386176 : term246 = True.
Proof. exact (EQ_MP (@lem5386175) (@lem5386173)). Qed.
Lemma lem5386177 : term245 = True.
Proof. exact (TRANS (@lem5386172) (@lem5386176)). Qed.
Lemma lem5386178 : True = term245.
Proof. exact (SYM (@lem5386177)). Qed.
Lemma lem5386179 : term245.
Proof. exact (EQ_MP (@lem5386178) (@lem0)). Qed.
Lemma lem5386180 : term393 = term396.
Proof. exact (@lem5386169 (@lem5386179)). Qed.
Lemma lem5386182 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5386183 : term210 = term211.
Proof. exact (@lem5386182 term44 term44). Qed.
Lemma lem5386184 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5386185 : term213 = term44.
Proof. exact (EQ_MP (@lem5386184) (@lem940073)). Qed.
Lemma lem5386186 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5386187 : term211 = term138.
Proof. exact (MK_COMB (@lem5386186) (@lem5386185)). Qed.
Lemma lem5386188 : term210 = term138.
Proof. exact (TRANS (@lem5386183) (@lem5386187)). Qed.
Lemma lem5386190 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5386191 : term398 = term128.
Proof. exact (@lem5386190 term44). Qed.
Lemma lem5386192 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5386193 : term399 = term391.
Proof. exact (MK_COMB (@lem5386192) (@lem5386191)). Qed.
Lemma lem5386194 : term396 = term245.
Proof. exact (MK_COMB (@lem5386193) (@lem5386188)). Qed.
Lemma lem5386196 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5386197 : term245 = term246.
Proof. exact (@lem5386196 (NUMERAL 0) term44). Qed.
Lemma lem5386198 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5386199 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5386200 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5386199 h1) (fun h1 : term246 = True => @lem5386198)). Qed.
Lemma lem5386201 : term246 = True.
Proof. exact (EQ_MP (@lem5386200) (@lem5386198)). Qed.
Lemma lem5386202 : term245 = True.
Proof. exact (TRANS (@lem5386197) (@lem5386201)). Qed.
Lemma lem5386203 : term396 = True.
Proof. exact (TRANS (@lem5386194) (@lem5386202)). Qed.
Lemma lem5386204 : term393 = True.
Proof. exact (TRANS (@lem5386180) (@lem5386203)). Qed.
Lemma lem5386205 : term245 = True.
Proof. exact (TRANS (@lem5386157) (@lem5386204)). Qed.
Lemma lem5386206 : term390 = True.
Proof. exact (TRANS (@lem5386148) (@lem5386205)). Qed.
Lemma lem5386207 : True = term390.
Proof. exact (SYM (@lem5386206)). Qed.
Lemma lem5386208 : term390.
Proof. exact (EQ_MP (@lem5386207) (@lem0)). Qed.
Lemma lem5386209 (_69799 : int) (_69800 : int) (h1 : term563 _69799 _69800) : term564 _69799 _69800.
Proof. exact (conj (@lem5386208) (@lem5386071 _69799 _69800 h1)). Qed.
Lemma lem5386211 (x : real) (y : real) : term401 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5386212 (_69799 : int) (_69800 : int) : term565 _69799 _69800.
Proof. exact (@lem5386211 term138 (term556 _69799 _69800)). Qed.
Lemma lem5386213 (_69799 : int) (_69800 : int) (h1 : term563 _69799 _69800) : term566 _69799 _69800.
Proof. exact (@lem5386212 _69799 _69800 (@lem5386209 _69799 _69800 h1)). Qed.
Lemma lem5386214 (_69799 : int) (_69800 : int) : (term567 _69799 _69800) = (term556 _69799 _69800).
Proof. exact (@lem1982733 (term556 _69799 _69800)). Qed.
Lemma lem5386215 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5386216 (_69799 : int) (_69800 : int) : (term568 _69799 _69800) = (term558 _69799 _69800).
Proof. exact (MK_COMB (@lem5386215) (@lem5386214 _69799 _69800)). Qed.
Lemma lem5386217 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5386218 (_69799 : int) (_69800 : int) : (term566 _69799 _69800) = (term559 _69799 _69800).
Proof. exact (MK_COMB (@lem5386216 _69799 _69800) (@lem5386217)). Qed.
Lemma lem5386219 (_69799 : int) (_69800 : int) (h1 : term563 _69799 _69800) : term559 _69799 _69800.
Proof. exact (EQ_MP (@lem5386218 _69799 _69800) (@lem5386213 _69799 _69800 h1)). Qed.
Lemma lem5386220 (_69799 : int) (_69800 : int) (h1 : term563 _69799 _69800) : term561 _69799 _69800.
Proof. exact (conj (@lem5386219 _69799 _69800 h1) (@lem5386145 _69799 _69800 h1)). Qed.
Lemma lem5386222 (x : real) (y : real) : term412 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5386223 (_69799 : int) (_69800 : int) : term569 _69799 _69800.
Proof. exact (@lem5386222 (term556 _69799 _69800) (term309 _69799 _69800)). Qed.
Lemma lem5386224 (_69799 : int) (_69800 : int) (h1 : term563 _69799 _69800) : term570 _69799 _69800.
Proof. exact (@lem5386223 _69799 _69800 (@lem5386220 _69799 _69800 h1)). Qed.
Lemma lem5386225 (_69799 : int) (_69800 : int) : (term571 _69799 _69800) = (term572 _69799 _69800).
Proof. exact (@lem1982753 (term228 _69799) (real_of_int _69799) (real_of_int _69800) (term308 _69800)). Qed.
Lemma lem5386226 (_69799 : int) : (term417 _69799) = (term418 _69799).
Proof. exact (@lem1982713 term201 (real_of_int _69799)). Qed.
Lemma lem5386228 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5386229 : term138 = term237.
Proof. exact (@lem5386228 term44). Qed.
Lemma lem5386231 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5386232 : term201 = term202.
Proof. exact (@lem5386231 term44). Qed.
Lemma lem5386233 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5386234 : term419 = term420.
Proof. exact (MK_COMB (@lem5386233) (@lem5386232)). Qed.
Lemma lem5386235 : term421 = term422.
Proof. exact (MK_COMB (@lem5386234) (@lem5386229)). Qed.
Lemma lem5386236 : term423.
Proof. exact (@lem1981473 term201 term138 term138 term138 term128 term138). Qed.
Lemma lem5386238 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5386239 : term245 = term246.
Proof. exact (@lem5386238 (NUMERAL 0) term44). Qed.
Lemma lem5386240 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5386241 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5386242 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5386241 h1) (fun h1 : term246 = True => @lem5386240)). Qed.
Lemma lem5386243 : term246 = True.
Proof. exact (EQ_MP (@lem5386242) (@lem5386240)). Qed.
Lemma lem5386244 : term245 = True.
Proof. exact (TRANS (@lem5386239) (@lem5386243)). Qed.
Lemma lem5386245 : True = term245.
Proof. exact (SYM (@lem5386244)). Qed.
Lemma lem5386246 : term245.
Proof. exact (EQ_MP (@lem5386245) (@lem0)). Qed.
Lemma lem5386247 : term424.
Proof. exact (@lem5386236 (@lem5386246)). Qed.
Lemma lem5386249 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5386250 : term245 = term246.
Proof. exact (@lem5386249 (NUMERAL 0) term44). Qed.
Lemma lem5386251 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5386252 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5386253 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5386252 h1) (fun h1 : term246 = True => @lem5386251)). Qed.
Lemma lem5386254 : term246 = True.
Proof. exact (EQ_MP (@lem5386253) (@lem5386251)). Qed.
Lemma lem5386255 : term245 = True.
Proof. exact (TRANS (@lem5386250) (@lem5386254)). Qed.
Lemma lem5386256 : True = term245.
Proof. exact (SYM (@lem5386255)). Qed.
Lemma lem5386257 : term245.
Proof. exact (EQ_MP (@lem5386256) (@lem0)). Qed.
Lemma lem5386258 : term425.
Proof. exact (@lem5386247 (@lem5386257)). Qed.
Lemma lem5386260 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5386261 : term245 = term246.
Proof. exact (@lem5386260 (NUMERAL 0) term44). Qed.
Lemma lem5386262 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5386263 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5386264 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5386263 h1) (fun h1 : term246 = True => @lem5386262)). Qed.
Lemma lem5386265 : term246 = True.
Proof. exact (EQ_MP (@lem5386264) (@lem5386262)). Qed.
Lemma lem5386266 : term245 = True.
Proof. exact (TRANS (@lem5386261) (@lem5386265)). Qed.
Lemma lem5386267 : True = term245.
Proof. exact (SYM (@lem5386266)). Qed.
Lemma lem5386268 : term245.
Proof. exact (EQ_MP (@lem5386267) (@lem0)). Qed.
Lemma lem5386269 : term426.
Proof. exact (@lem5386258 (@lem5386268)). Qed.
Lemma lem5386271 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5386272 : term210 = term211.
Proof. exact (@lem5386271 term44 term44). Qed.
Lemma lem5386273 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5386274 : term213 = term44.
Proof. exact (EQ_MP (@lem5386273) (@lem940073)). Qed.
Lemma lem5386275 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5386276 : term211 = term138.
Proof. exact (MK_COMB (@lem5386275) (@lem5386274)). Qed.
Lemma lem5386277 : term210 = term138.
Proof. exact (TRANS (@lem5386272) (@lem5386276)). Qed.
Lemma lem5386279 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5386280 : term302 = term305.
Proof. exact (@lem5386279 term44 term44). Qed.
Lemma lem5386281 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5386282 : term213 = term44.
Proof. exact (EQ_MP (@lem5386281) (@lem940073)). Qed.
Lemma lem5386283 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5386284 : term211 = term138.
Proof. exact (MK_COMB (@lem5386283) (@lem5386282)). Qed.
Lemma lem5386285 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5386286 : term305 = term201.
Proof. exact (MK_COMB (@lem5386285) (@lem5386284)). Qed.
Lemma lem5386287 : term302 = term201.
Proof. exact (TRANS (@lem5386280) (@lem5386286)). Qed.
Lemma lem5386288 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5386289 : term427 = term419.
Proof. exact (MK_COMB (@lem5386288) (@lem5386287)). Qed.
Lemma lem5386290 : term428 = term421.
Proof. exact (MK_COMB (@lem5386289) (@lem5386277)). Qed.
Lemma lem5386292 (m : nat) : (term429 m) = term128.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5386293 : term421 = term128.
Proof. exact (@lem5386292 term44). Qed.
Lemma lem5386294 : term428 = term128.
Proof. exact (TRANS (@lem5386290) (@lem5386293)). Qed.
Lemma lem5386295 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5386296 : term430 = term431.
Proof. exact (MK_COMB (@lem5386295) (@lem5386294)). Qed.
Lemma lem5386297 : term138 = term138.
Proof. exact (eq_refl term138). Qed.
Lemma lem5386298 : term432 = term398.
Proof. exact (MK_COMB (@lem5386296) (@lem5386297)). Qed.
Lemma lem5386300 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5386301 : term398 = term128.
Proof. exact (@lem5386300 term44). Qed.
Lemma lem5386302 : term432 = term128.
Proof. exact (TRANS (@lem5386298) (@lem5386301)). Qed.
Lemma lem5386304 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5386305 : term210 = term211.
Proof. exact (@lem5386304 term44 term44). Qed.
Lemma lem5386306 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5386307 : term213 = term44.
Proof. exact (EQ_MP (@lem5386306) (@lem940073)). Qed.
Lemma lem5386308 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5386309 : term211 = term138.
Proof. exact (MK_COMB (@lem5386308) (@lem5386307)). Qed.
Lemma lem5386310 : term210 = term138.
Proof. exact (TRANS (@lem5386305) (@lem5386309)). Qed.
Lemma lem5386311 : term431 = term431.
Proof. exact (eq_refl term431). Qed.
Lemma lem5386312 : term433 = term398.
Proof. exact (MK_COMB (@lem5386311) (@lem5386310)). Qed.
Lemma lem5386314 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5386315 : term398 = term128.
Proof. exact (@lem5386314 term44). Qed.
Lemma lem5386316 : term433 = term128.
Proof. exact (TRANS (@lem5386312) (@lem5386315)). Qed.
Lemma lem5386317 : term128 = term433.
Proof. exact (SYM (@lem5386316)). Qed.
Lemma lem5386318 : term432 = term433.
Proof. exact (TRANS (@lem5386302) (@lem5386317)). Qed.
Lemma lem5386319 : term422 = term198.
Proof. exact (@lem5386269 (@lem5386318)). Qed.
Lemma lem5386320 : term421 = term198.
Proof. exact (TRANS (@lem5386235) (@lem5386319)). Qed.
Lemma lem5386322 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5386323 : term198 = term128.
Proof. exact (@lem5386322 term128). Qed.
Lemma lem5386324 : term421 = term128.
Proof. exact (TRANS (@lem5386320) (@lem5386323)). Qed.
Lemma lem5386325 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5386326 : term434 = term431.
Proof. exact (MK_COMB (@lem5386325) (@lem5386324)). Qed.
Lemma lem5386327 (_69799 : int) : (real_of_int _69799) = (real_of_int _69799).
Proof. exact (eq_refl (real_of_int _69799)). Qed.
Lemma lem5386328 (_69799 : int) : (term418 _69799) = (term435 _69799).
Proof. exact (MK_COMB (@lem5386326) (@lem5386327 _69799)). Qed.
Lemma lem5386329 (_69799 : int) : (term417 _69799) = (term435 _69799).
Proof. exact (TRANS (@lem5386226 _69799) (@lem5386328 _69799)). Qed.
Lemma lem5386330 (_69799 : int) : (term435 _69799) = term128.
Proof. exact (@lem1982719 (real_of_int _69799)). Qed.
Lemma lem5386331 (_69799 : int) : (term417 _69799) = term128.
Proof. exact (TRANS (@lem5386329 _69799) (@lem5386330 _69799)). Qed.
Lemma lem5386332 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5386333 (_69799 : int) : (term436 _69799) = term178.
Proof. exact (MK_COMB (@lem5386332) (@lem5386331 _69799)). Qed.
Lemma lem5386334 (_69800 : int) : (term462 _69800) = (term463 _69800).
Proof. exact (@lem1982763 (real_of_int _69800) (term228 _69800) term201). Qed.
Lemma lem5386335 (_69800 : int) : (term464 _69800) = (term418 _69800).
Proof. exact (@lem1982715 term201 (real_of_int _69800)). Qed.
Lemma lem5386337 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5386338 : term138 = term237.
Proof. exact (@lem5386337 term44). Qed.
Lemma lem5386340 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5386341 : term201 = term202.
Proof. exact (@lem5386340 term44). Qed.
Lemma lem5386342 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5386343 : term419 = term420.
Proof. exact (MK_COMB (@lem5386342) (@lem5386341)). Qed.
Lemma lem5386344 : term421 = term422.
Proof. exact (MK_COMB (@lem5386343) (@lem5386338)). Qed.
Lemma lem5386345 : term423.
Proof. exact (@lem1981473 term201 term138 term138 term138 term128 term138). Qed.
Lemma lem5386347 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5386348 : term245 = term246.
Proof. exact (@lem5386347 (NUMERAL 0) term44). Qed.
Lemma lem5386349 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5386350 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5386351 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5386350 h1) (fun h1 : term246 = True => @lem5386349)). Qed.
Lemma lem5386352 : term246 = True.
Proof. exact (EQ_MP (@lem5386351) (@lem5386349)). Qed.
Lemma lem5386353 : term245 = True.
Proof. exact (TRANS (@lem5386348) (@lem5386352)). Qed.
Lemma lem5386354 : True = term245.
Proof. exact (SYM (@lem5386353)). Qed.
Lemma lem5386355 : term245.
Proof. exact (EQ_MP (@lem5386354) (@lem0)). Qed.
Lemma lem5386356 : term424.
Proof. exact (@lem5386345 (@lem5386355)). Qed.
Lemma lem5386358 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5386359 : term245 = term246.
Proof. exact (@lem5386358 (NUMERAL 0) term44). Qed.
Lemma lem5386360 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5386361 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5386362 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5386361 h1) (fun h1 : term246 = True => @lem5386360)). Qed.
Lemma lem5386363 : term246 = True.
Proof. exact (EQ_MP (@lem5386362) (@lem5386360)). Qed.
Lemma lem5386364 : term245 = True.
Proof. exact (TRANS (@lem5386359) (@lem5386363)). Qed.
Lemma lem5386365 : True = term245.
Proof. exact (SYM (@lem5386364)). Qed.
Lemma lem5386366 : term245.
Proof. exact (EQ_MP (@lem5386365) (@lem0)). Qed.
Lemma lem5386367 : term425.
Proof. exact (@lem5386356 (@lem5386366)). Qed.
Lemma lem5386369 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5386370 : term245 = term246.
Proof. exact (@lem5386369 (NUMERAL 0) term44). Qed.
Lemma lem5386371 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5386372 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5386373 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5386372 h1) (fun h1 : term246 = True => @lem5386371)). Qed.
Lemma lem5386374 : term246 = True.
Proof. exact (EQ_MP (@lem5386373) (@lem5386371)). Qed.
Lemma lem5386375 : term245 = True.
Proof. exact (TRANS (@lem5386370) (@lem5386374)). Qed.
Lemma lem5386376 : True = term245.
Proof. exact (SYM (@lem5386375)). Qed.
Lemma lem5386377 : term245.
Proof. exact (EQ_MP (@lem5386376) (@lem0)). Qed.
Lemma lem5386378 : term426.
Proof. exact (@lem5386367 (@lem5386377)). Qed.
Lemma lem5386380 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5386381 : term210 = term211.
Proof. exact (@lem5386380 term44 term44). Qed.
Lemma lem5386382 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5386383 : term213 = term44.
Proof. exact (EQ_MP (@lem5386382) (@lem940073)). Qed.
Lemma lem5386384 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5386385 : term211 = term138.
Proof. exact (MK_COMB (@lem5386384) (@lem5386383)). Qed.
Lemma lem5386386 : term210 = term138.
Proof. exact (TRANS (@lem5386381) (@lem5386385)). Qed.
Lemma lem5386388 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5386389 : term302 = term305.
Proof. exact (@lem5386388 term44 term44). Qed.
Lemma lem5386390 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5386391 : term213 = term44.
Proof. exact (EQ_MP (@lem5386390) (@lem940073)). Qed.
Lemma lem5386392 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5386393 : term211 = term138.
Proof. exact (MK_COMB (@lem5386392) (@lem5386391)). Qed.
Lemma lem5386394 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5386395 : term305 = term201.
Proof. exact (MK_COMB (@lem5386394) (@lem5386393)). Qed.
Lemma lem5386396 : term302 = term201.
Proof. exact (TRANS (@lem5386389) (@lem5386395)). Qed.
Lemma lem5386397 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5386398 : term427 = term419.
Proof. exact (MK_COMB (@lem5386397) (@lem5386396)). Qed.
Lemma lem5386399 : term428 = term421.
Proof. exact (MK_COMB (@lem5386398) (@lem5386386)). Qed.
Lemma lem5386401 (m : nat) : (term429 m) = term128.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5386402 : term421 = term128.
Proof. exact (@lem5386401 term44). Qed.
Lemma lem5386403 : term428 = term128.
Proof. exact (TRANS (@lem5386399) (@lem5386402)). Qed.
Lemma lem5386404 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5386405 : term430 = term431.
Proof. exact (MK_COMB (@lem5386404) (@lem5386403)). Qed.
Lemma lem5386406 : term138 = term138.
Proof. exact (eq_refl term138). Qed.
Lemma lem5386407 : term432 = term398.
Proof. exact (MK_COMB (@lem5386405) (@lem5386406)). Qed.
Lemma lem5386409 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5386410 : term398 = term128.
Proof. exact (@lem5386409 term44). Qed.
Lemma lem5386411 : term432 = term128.
Proof. exact (TRANS (@lem5386407) (@lem5386410)). Qed.
Lemma lem5386413 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5386414 : term210 = term211.
Proof. exact (@lem5386413 term44 term44). Qed.
Lemma lem5386415 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5386416 : term213 = term44.
Proof. exact (EQ_MP (@lem5386415) (@lem940073)). Qed.
Lemma lem5386417 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5386418 : term211 = term138.
Proof. exact (MK_COMB (@lem5386417) (@lem5386416)). Qed.
Lemma lem5386419 : term210 = term138.
Proof. exact (TRANS (@lem5386414) (@lem5386418)). Qed.
Lemma lem5386420 : term431 = term431.
Proof. exact (eq_refl term431). Qed.
Lemma lem5386421 : term433 = term398.
Proof. exact (MK_COMB (@lem5386420) (@lem5386419)). Qed.
Lemma lem5386423 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5386424 : term398 = term128.
Proof. exact (@lem5386423 term44). Qed.
Lemma lem5386425 : term433 = term128.
Proof. exact (TRANS (@lem5386421) (@lem5386424)). Qed.
Lemma lem5386426 : term128 = term433.
Proof. exact (SYM (@lem5386425)). Qed.
Lemma lem5386427 : term432 = term433.
Proof. exact (TRANS (@lem5386411) (@lem5386426)). Qed.
Lemma lem5386428 : term422 = term198.
Proof. exact (@lem5386378 (@lem5386427)). Qed.
Lemma lem5386429 : term421 = term198.
Proof. exact (TRANS (@lem5386344) (@lem5386428)). Qed.
Lemma lem5386431 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5386432 : term198 = term128.
Proof. exact (@lem5386431 term128). Qed.
Lemma lem5386433 : term421 = term128.
Proof. exact (TRANS (@lem5386429) (@lem5386432)). Qed.
Lemma lem5386434 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5386435 : term434 = term431.
Proof. exact (MK_COMB (@lem5386434) (@lem5386433)). Qed.
Lemma lem5386436 (_69800 : int) : (real_of_int _69800) = (real_of_int _69800).
Proof. exact (eq_refl (real_of_int _69800)). Qed.
Lemma lem5386437 (_69800 : int) : (term418 _69800) = (term435 _69800).
Proof. exact (MK_COMB (@lem5386435) (@lem5386436 _69800)). Qed.
Lemma lem5386438 (_69800 : int) : (term464 _69800) = (term435 _69800).
Proof. exact (TRANS (@lem5386335 _69800) (@lem5386437 _69800)). Qed.
Lemma lem5386439 (_69800 : int) : (term435 _69800) = term128.
Proof. exact (@lem1982719 (real_of_int _69800)). Qed.
Lemma lem5386440 (_69800 : int) : (term464 _69800) = term128.
Proof. exact (TRANS (@lem5386438 _69800) (@lem5386439 _69800)). Qed.
Lemma lem5386441 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5386442 (_69800 : int) : (term465 _69800) = term178.
Proof. exact (MK_COMB (@lem5386441) (@lem5386440 _69800)). Qed.
Lemma lem5386443 : term201 = term201.
Proof. exact (eq_refl term201). Qed.
Lemma lem5386444 (_69800 : int) : (term463 _69800) = term437.
Proof. exact (MK_COMB (@lem5386442 _69800) (@lem5386443)). Qed.
Lemma lem5386445 (_69800 : int) : (term462 _69800) = term437.
Proof. exact (TRANS (@lem5386334 _69800) (@lem5386444 _69800)). Qed.
Lemma lem5386446 : term437 = term201.
Proof. exact (@lem1982721 term201). Qed.
Lemma lem5386447 (_69800 : int) : (term462 _69800) = term201.
Proof. exact (TRANS (@lem5386445 _69800) (@lem5386446)). Qed.
Lemma lem5386448 (_69799 : int) (_69800 : int) : (term572 _69799 _69800) = term437.
Proof. exact (MK_COMB (@lem5386333 _69799) (@lem5386447 _69800)). Qed.
Lemma lem5386449 (_69799 : int) (_69800 : int) : (term571 _69799 _69800) = term437.
Proof. exact (TRANS (@lem5386225 _69799 _69800) (@lem5386448 _69799 _69800)). Qed.
Lemma lem5386450 : term437 = term201.
Proof. exact (@lem1982721 term201). Qed.
Lemma lem5386451 (_69799 : int) (_69800 : int) : (term571 _69799 _69800) = term201.
Proof. exact (TRANS (@lem5386449 _69799 _69800) (@lem5386450)). Qed.
Lemma lem5386452 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5386453 (_69799 : int) (_69800 : int) : (term573 _69799 _69800) = term439.
Proof. exact (MK_COMB (@lem5386452) (@lem5386451 _69799 _69800)). Qed.
Lemma lem5386454 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5386455 (_69799 : int) (_69800 : int) : (term570 _69799 _69800) = term440.
Proof. exact (MK_COMB (@lem5386453 _69799 _69800) (@lem5386454)). Qed.
Lemma lem5386456 (_69799 : int) (_69800 : int) (h1 : term563 _69799 _69800) : term440.
Proof. exact (EQ_MP (@lem5386455 _69799 _69800) (@lem5386224 _69799 _69800 h1)). Qed.
Lemma lem5386458 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5386459 : term440 = term441.
Proof. exact (@lem5386458 term128 term201). Qed.
Lemma lem5386461 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5386462 : term201 = term202.
Proof. exact (@lem5386461 term44). Qed.
Lemma lem5386464 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5386465 : term128 = term198.
Proof. exact (@lem5386464 (NUMERAL 0)). Qed.
Lemma lem5386466 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5386467 : term130 = term442.
Proof. exact (MK_COMB (@lem5386466) (@lem5386465)). Qed.
Lemma lem5386468 : term441 = term443.
Proof. exact (MK_COMB (@lem5386467) (@lem5386462)). Qed.
Lemma lem5386469 : term444.
Proof. exact (@lem1980026 term128 term138 term201 term138). Qed.
Lemma lem5386471 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5386472 : term245 = term246.
Proof. exact (@lem5386471 (NUMERAL 0) term44). Qed.
Lemma lem5386473 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5386474 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5386475 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5386474 h1) (fun h1 : term246 = True => @lem5386473)). Qed.
Lemma lem5386476 : term246 = True.
Proof. exact (EQ_MP (@lem5386475) (@lem5386473)). Qed.
Lemma lem5386477 : term245 = True.
Proof. exact (TRANS (@lem5386472) (@lem5386476)). Qed.
Lemma lem5386478 : True = term245.
Proof. exact (SYM (@lem5386477)). Qed.
Lemma lem5386479 : term245.
Proof. exact (EQ_MP (@lem5386478) (@lem0)). Qed.
Lemma lem5386480 : term445.
Proof. exact (@lem5386469 (@lem5386479)). Qed.
Lemma lem5386482 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5386483 : term245 = term246.
Proof. exact (@lem5386482 (NUMERAL 0) term44). Qed.
Lemma lem5386484 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5386485 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5386486 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5386485 h1) (fun h1 : term246 = True => @lem5386484)). Qed.
Lemma lem5386487 : term246 = True.
Proof. exact (EQ_MP (@lem5386486) (@lem5386484)). Qed.
Lemma lem5386488 : term245 = True.
Proof. exact (TRANS (@lem5386483) (@lem5386487)). Qed.
Lemma lem5386489 : True = term245.
Proof. exact (SYM (@lem5386488)). Qed.
Lemma lem5386490 : term245.
Proof. exact (EQ_MP (@lem5386489) (@lem0)). Qed.
Lemma lem5386491 : term443 = term446.
Proof. exact (@lem5386480 (@lem5386490)). Qed.
Lemma lem5386493 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5386494 : term302 = term305.
Proof. exact (@lem5386493 term44 term44). Qed.
Lemma lem5386495 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5386496 : term213 = term44.
Proof. exact (EQ_MP (@lem5386495) (@lem940073)). Qed.
Lemma lem5386497 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5386498 : term211 = term138.
Proof. exact (MK_COMB (@lem5386497) (@lem5386496)). Qed.
Lemma lem5386499 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5386500 : term305 = term201.
Proof. exact (MK_COMB (@lem5386499) (@lem5386498)). Qed.
Lemma lem5386501 : term302 = term201.
Proof. exact (TRANS (@lem5386494) (@lem5386500)). Qed.
Lemma lem5386503 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5386504 : term398 = term128.
Proof. exact (@lem5386503 term44). Qed.
Lemma lem5386505 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5386506 : term447 = term130.
Proof. exact (MK_COMB (@lem5386505) (@lem5386504)). Qed.
Lemma lem5386507 : term446 = term441.
Proof. exact (MK_COMB (@lem5386506) (@lem5386501)). Qed.
Lemma lem5386509 (m : nat) (n : nat) : (term448 m n) = (term449 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5386510 : term441 = term450.
Proof. exact (@lem5386509 (NUMERAL 0) term44). Qed.
Lemma lem5386511 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5386512 (h1 : term247 = (BIT1 0)) : (term44 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5386513 : (term247 = (BIT1 0)) = ((term44 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5386512 h1) (fun h1 : (term44 = (NUMERAL 0)) = False => @lem5386511)). Qed.
Lemma lem5386514 : (term44 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5386513) (@lem5386511)). Qed.
Lemma lem5386515 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5386516 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5386517 : term451 = (and True).
Proof. exact (MK_COMB (@lem5386516) (@lem5386515)). Qed.
Lemma lem5386518 : term450 = (True /\ False).
Proof. exact (MK_COMB (@lem5386517) (@lem5386514)). Qed.
Lemma lem5386520 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5386521 : term450 = False.
Proof. exact (TRANS (@lem5386518) (@lem5386520)). Qed.
Lemma lem5386522 : term441 = False.
Proof. exact (TRANS (@lem5386510) (@lem5386521)). Qed.
Lemma lem5386523 : term446 = False.
Proof. exact (TRANS (@lem5386507) (@lem5386522)). Qed.
Lemma lem5386524 : term443 = False.
Proof. exact (TRANS (@lem5386491) (@lem5386523)). Qed.
Lemma lem5386525 : term441 = False.
Proof. exact (TRANS (@lem5386468) (@lem5386524)). Qed.
Lemma lem5386526 : term440 = False.
Proof. exact (TRANS (@lem5386459) (@lem5386525)). Qed.
Lemma lem5386527 (_69799 : int) (_69800 : int) (h1 : term563 _69799 _69800) : False.
Proof. exact (EQ_MP (@lem5386526) (@lem5386456 _69799 _69800 h1)). Qed.
Lemma lem5386529 (_69799 : int) (_69800 : int) (h1 : term563 _69799 _69800) : term563 _69799 _69800.
Proof. exact (h1). Qed.
Lemma lem5386530 (_69799 : int) (_69800 : int) (h1 : term563 _69799 _69800) : (term563 _69799 _69800) = False.
Proof. exact (prop_ext (fun h2 : term563 _69799 _69800 => @lem5386527 _69799 _69800 h1) (fun h2 : False => @lem5386529 _69799 _69800 h1)). Qed.
Lemma lem5386531 (_69799 : int) (_69800 : int) (h1 : term563 _69799 _69800) : False.
Proof. exact (EQ_MP (@lem5386530 _69799 _69800 h1) (@lem5386529 _69799 _69800 h1)). Qed.
Lemma lem5386532 (_69800 : int) (_69799 : int) (h1 : term552 _69800 _69799) : term552 _69800 _69799.
Proof. exact (h1). Qed.
Lemma lem5386533 (_69800 : int) (_69799 : int) (h1 : term552 _69800 _69799) : term563 _69799 _69800.
Proof. exact (EQ_MP (@lem5386061 _69799 _69800) (@lem5386532 _69800 _69799 h1)). Qed.
Lemma lem5386534 (_69800 : int) (_69799 : int) (h1 : term552 _69800 _69799) : (term563 _69799 _69800) = False.
Proof. exact (prop_ext (fun h2 : term563 _69799 _69800 => @lem5386531 _69799 _69800 h2) (fun h2 : False => @lem5386533 _69800 _69799 h1)). Qed.
Lemma lem5386535 (_69800 : int) (_69799 : int) (h1 : term552 _69800 _69799) : False.
Proof. exact (EQ_MP (@lem5386534 _69800 _69799 h1) (@lem5386533 _69800 _69799 h1)). Qed.
Lemma lem5386536 (_69800 : int) (_69799 : int) : term574 _69800 _69799.
Proof. exact (fun h0 : term552 _69800 _69799 => @lem5386535 _69800 _69799 h0). Qed.
Lemma lem5386537 (_69800 : int) (_69799 : int) : term575 _69800 _69799.
Proof. exact (@lem1386578 (term576 _69800 _69799)). Qed.
Lemma lem5386540 (_69800 : int) (_69799 : int) : term576 _69800 _69799.
Proof. exact (@lem5386537 _69800 _69799 (@lem5386536 _69800 _69799)). Qed.
Lemma lem5386541 (_69799 : int) (_69800 : int) : (term551 _69800 _69799) = (term544 _69799 _69800).
Proof. exact (SYM (@lem5385803 _69800 _69799)). Qed.
Lemma lem5386542 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5386543 (_69799 : int) (_69800 : int) : (term576 _69800 _69799) = (term534 _69799 _69800).
Proof. exact (MK_COMB (@lem5386542) (@lem5386541 _69799 _69800)). Qed.
Lemma lem5386544 (_69799 : int) (_69800 : int) : term534 _69799 _69800.
Proof. exact (EQ_MP (@lem5386543 _69799 _69800) (@lem5386540 _69800 _69799)). Qed.
Lemma lem5386545 (_69799 : int) (_69800 : int) : term535 _69799 _69800.
Proof. exact (EQ_MP (@lem5385690 _69799 _69800) (@lem5386544 _69799 _69800)). Qed.
Lemma lem5386546 (m : nat) (n : nat) : term577 m n.
Proof. exact (@lem5386545 (int_of_num m) (int_of_num n)). Qed.
Lemma lem5386547 (m : nat) (n : nat) : term578 m n.
Proof. exact (@lem5386546 m n (@lem5385686 m)). Qed.
Lemma lem5386548 (m : nat) (n : nat) : term533 m n.
Proof. exact (@lem5386547 m n (@lem5385689 n)). Qed.
Lemma lem5386549 (m : nat) (n : nat) : (term533 m n) = (term532 m n).
Proof. exact (SYM (@lem5385683 m n)). Qed.
Lemma lem5386550 (m : nat) (n : nat) : term532 m n.
Proof. exact (EQ_MP (@lem5386549 m n) (@lem5386548 m n)). Qed.
Lemma lem5386551 (n : nat) (m : nat) (h1 : Peano.lt n m) : Peano.lt n m.
Proof. exact (h1). Qed.
Lemma lem5386552 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem5386554 (p : Prop) : p = (term579 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5386555 (n : nat) (m : nat) : (term580 n m) = (term581 n m).
Proof. exact (@lem5386554 (term580 n m)). Qed.
Lemma lem5386556 (n : nat) (m : nat) : (term581 n m) = (term580 n m).
Proof. exact (SYM (@lem5386555 n m)). Qed.
Lemma lem5386557 (n : nat) (m : nat) (h1 : term582 n m) : term582 n m.
Proof. exact (h1). Qed.
Lemma lem5386558 : term583.
Proof. exact (@lem3840691 nat). Qed.
Lemma lem5386562 {A : Type'} (n : nat) (m : nat) (h1 : term584 A n m) : term584 A n m.
Proof. exact (h1). Qed.
Lemma lem5386563 {A : Type'} (n : nat) (m : nat) : term585 A n m.
Proof. exact (fun h0 : term584 A n m => @lem5386562 A n m h0). Qed.
Lemma lem5386564 {A : Type'} (n : nat) (m : nat) (h1 : term585 A n m) : term585 A n m.
Proof. exact (h1). Qed.
Lemma lem5386565 {A : Type'} (n : nat) (m : nat) (h1 : term584 A n m) : term584 A n m.
Proof. exact (h1). Qed.
Lemma lem5386566 {A : Type'} (n : nat) (m : nat) (h1 : term584 A n m) (h2 : term585 A n m) : term584 A n m.
Proof. exact (@lem5386564 A n m h2 (@lem5386565 A n m h1)). Qed.
Lemma lem5386567 {A : Type'} (n : nat) (m : nat) (h1 : term584 A n m) : term586 A n m.
Proof. exact (fun h0 : term585 A n m => @lem5386566 A n m h1 h0). Qed.
Lemma lem5386568 {A : Type'} (n : nat) (m : nat) (h1 : term585 A n m) : term585 A n m.
Proof. exact (h1). Qed.
Lemma lem5386569 {A : Type'} (n : nat) (m : nat) (h1 : term584 A n m) (h2 : term585 A n m) : term584 A n m.
Proof. exact (@lem5386567 A n m h1 (@lem5386568 A n m h2)). Qed.
Lemma lem5386570 {A : Type'} (n : nat) (m : nat) (h1 : term585 A n m) : term585 A n m.
Proof. exact (fun h0 : term584 A n m => @lem5386569 A n m h0 h1). Qed.
Lemma lem5386571 {A : Type'} (n : nat) (m : nat) : term587 A n m.
Proof. exact (fun h0 : term585 A n m => @lem5386570 A n m h0). Qed.
Lemma lem5386574 {A : Type'} (n : nat) (m : nat) : term585 A n m.
Proof. exact (@lem5386571 A n m (@lem5386563 A n m)). Qed.
Lemma lem5386575 {A : Type'} (n : nat) (m : nat) : term585 A n m.
Proof. exact (@lem5386574 A n m). Qed.
Lemma lem5386629 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5386630 : term588 = term589.
Proof. exact (@lem5386629 term590). Qed.
Lemma lem5386639 : term591 = term591.
Proof. exact (eq_refl term591). Qed.
Lemma lem5386640 : term592 = term593.
Proof. exact (MK_COMB (@lem5386639) (@lem5386630)). Qed.
Lemma lem5386643 {A : Type'} : (term594 A) = (term594 A).
Proof. exact (eq_refl (term594 A)). Qed.
Lemma lem5386644 {A : Type'} : (term595 A) = (term596 A).
Proof. exact (MK_COMB (@lem5386643 A) (@lem5386640)). Qed.
Lemma lem5386647 : term597 = term597.
Proof. exact (eq_refl term597). Qed.
Lemma lem5386648 {A : Type'} : (term598 A) = (term599 A).
Proof. exact (MK_COMB (@lem5386647) (@lem5386644 A)). Qed.
Lemma lem5386651 (n : nat) (m : nat) : (term600 n m) = (term600 n m).
Proof. exact (eq_refl (term600 n m)). Qed.
Lemma lem5386652 {A : Type'} (n : nat) (m : nat) : (term584 A n m) = (term601 A n m).
Proof. exact (MK_COMB (@lem5386651 n m) (@lem5386648 A)). Qed.
Lemma lem5386655 {A : Type'} (m : nat) : (term602 A m) = (term603 A m).
Proof. exact (fun_ext (fun n : nat => @lem5386652 A n m)). Qed.
Lemma lem5386656 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5386657 {A : Type'} (m : nat) : (term604 A m) = (term605 A m).
Proof. exact (MK_COMB (@lem5386656) (@lem5386655 A m)). Qed.
Lemma lem5386662 {A : Type'} : (term606 A) = (term607 A).
Proof. exact (fun_ext (fun m : nat => @lem5386657 A m)). Qed.
Lemma lem5386663 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5386672 {A : Type'} : (term608 A) = (term609 A).
Proof. exact (MK_COMB (@lem5386663) (@lem5386662 A)). Qed.
Lemma lem5386677 (n : nat) (m : nat) : (((dotdot m n) = (@EMPTY nat)) = (Peano.lt n m)) = (((dotdot m n) = (@EMPTY nat)) = (Peano.lt n m)).
Proof. exact (eq_refl (((dotdot m n) = (@EMPTY nat)) = (Peano.lt n m))). Qed.
Lemma lem5386678 (m : nat) : (term610 m) = (term610 m).
Proof. exact (fun_ext (fun n : nat => @lem5386677 n m)). Qed.
Lemma lem5386679 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5386680 (m : nat) : (term611 m) = (term611 m).
Proof. exact (MK_COMB (@lem5386679) (@lem5386678 m)). Qed.
Lemma lem5386681 : term612 = term612.
Proof. exact (fun_ext (fun m : nat => @lem5386680 m)). Qed.
Lemma lem5386682 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5386683 : term590 = term590.
Proof. exact (MK_COMB (@lem5386682) (@lem5386681)). Qed.
Lemma lem5386684 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5386685 : term589 = term589.
Proof. exact (MK_COMB (@lem5386684) (@lem5386683)). Qed.
Lemma lem5386689 (x : nat) (s : nat -> Prop) (h1 : (@IN nat x s) = False) : (@IN nat x s) = False.
Proof. exact (h1). Qed.
Lemma lem5386690 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem5386691 (x : nat) (s : nat -> Prop) (h1 : (@IN nat x s) = False) : (term613 x s) = (@COND nat False).
Proof. exact (MK_COMB (@lem5386690) (@lem5386689 x s h1)). Qed.
Lemma lem5386692 (s : nat -> Prop) : (@CARD nat s) = (@CARD nat s).
Proof. exact (eq_refl (@CARD nat s)). Qed.
Lemma lem5386693 (x : nat) (s : nat -> Prop) (h1 : (@IN nat x s) = False) : (term614 x s) = (term615 s).
Proof. exact (MK_COMB (@lem5386691 x s h1) (@lem5386692 s)). Qed.
Lemma lem5386694 (s : nat -> Prop) : (term616 s) = (term616 s).
Proof. exact (eq_refl (term616 s)). Qed.
Lemma lem5386695 (x : nat) (s : nat -> Prop) (h1 : (@IN nat x s) = False) : (term617 x s) = (term618 s).
Proof. exact (MK_COMB (@lem5386693 x s h1) (@lem5386694 s)). Qed.
Lemma lem5386697 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5386698 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem5386697 nat t1 t2). Qed.
Lemma lem5386699 (s : nat -> Prop) : (term618 s) = (term616 s).
Proof. exact (@lem5386698 (@CARD nat s) (term616 s)). Qed.
Lemma lem5386700 (x : nat) (s : nat -> Prop) (h1 : (@IN nat x s) = False) : (term617 x s) = (term616 s).
Proof. exact (TRANS (@lem5386695 x s h1) (@lem5386699 s)). Qed.
Lemma lem5386701 (x : nat) (s : nat -> Prop) : (term619 x s) = (term619 x s).
Proof. exact (eq_refl (term619 x s)). Qed.
Lemma lem5386702 (x : nat) (s : nat -> Prop) (h1 : (@IN nat x s) = False) : ((term620 x s) = (term617 x s)) = ((term620 x s) = (term616 s)).
Proof. exact (MK_COMB (@lem5386701 x s) (@lem5386700 x s h1)). Qed.
Lemma lem5386705 (s : nat -> Prop) : (term621 s) = (term621 s).
Proof. exact (eq_refl (term621 s)). Qed.
Lemma lem5386706 (x : nat) (s : nat -> Prop) (h1 : (@IN nat x s) = False) : (term622 x s) = (term623 x s).
Proof. exact (MK_COMB (@lem5386705 s) (@lem5386702 x s h1)). Qed.
Lemma lem5386709 (x : nat) (s : nat -> Prop) : term624 x s.
Proof. exact (fun h0 : (@IN nat x s) = False => @lem5386706 x s h0). Qed.
Lemma lem5386711 (x : nat) (s : nat -> Prop) (h1 : (@IN nat x s) = True) : (@IN nat x s) = True.
Proof. exact (h1). Qed.
Lemma lem5386712 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem5386713 (x : nat) (s : nat -> Prop) (h1 : (@IN nat x s) = True) : (term613 x s) = (@COND nat True).
Proof. exact (MK_COMB (@lem5386712) (@lem5386711 x s h1)). Qed.
Lemma lem5386714 (s : nat -> Prop) : (@CARD nat s) = (@CARD nat s).
Proof. exact (eq_refl (@CARD nat s)). Qed.
Lemma lem5386715 (x : nat) (s : nat -> Prop) (h1 : (@IN nat x s) = True) : (term614 x s) = (term625 s).
Proof. exact (MK_COMB (@lem5386713 x s h1) (@lem5386714 s)). Qed.
Lemma lem5386716 (s : nat -> Prop) : (term616 s) = (term616 s).
Proof. exact (eq_refl (term616 s)). Qed.
Lemma lem5386717 (x : nat) (s : nat -> Prop) (h1 : (@IN nat x s) = True) : (term617 x s) = (term626 s).
Proof. exact (MK_COMB (@lem5386715 x s h1) (@lem5386716 s)). Qed.
Lemma lem5386719 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5386720 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem5386719 nat t2 t1). Qed.
Lemma lem5386721 (s : nat -> Prop) : (term626 s) = (@CARD nat s).
Proof. exact (@lem5386720 (term616 s) (@CARD nat s)). Qed.
Lemma lem5386722 (x : nat) (s : nat -> Prop) (h1 : (@IN nat x s) = True) : (term617 x s) = (@CARD nat s).
Proof. exact (TRANS (@lem5386717 x s h1) (@lem5386721 s)). Qed.
Lemma lem5386723 (x : nat) (s : nat -> Prop) : (term619 x s) = (term619 x s).
Proof. exact (eq_refl (term619 x s)). Qed.
Lemma lem5386724 (x : nat) (s : nat -> Prop) (h1 : (@IN nat x s) = True) : ((term620 x s) = (term617 x s)) = ((term620 x s) = (@CARD nat s)).
Proof. exact (MK_COMB (@lem5386723 x s) (@lem5386722 x s h1)). Qed.
Lemma lem5386727 (s : nat -> Prop) : (term621 s) = (term621 s).
Proof. exact (eq_refl (term621 s)). Qed.
Lemma lem5386728 (x : nat) (s : nat -> Prop) (h1 : (@IN nat x s) = True) : (term622 x s) = (term627 x s).
Proof. exact (MK_COMB (@lem5386727 s) (@lem5386724 x s h1)). Qed.
Lemma lem5386731 (x : nat) (s : nat -> Prop) : term628 x s.
Proof. exact (fun h0 : (@IN nat x s) = True => @lem5386728 x s h0). Qed.
Lemma lem5386732 (x : nat) (s : nat -> Prop) : term629 x s.
Proof. exact (conj (@lem5386709 x s) (@lem5386731 x s)). Qed.
Lemma lem5386734 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term630 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem5386735 (x : nat) (s : nat -> Prop) : term631 x s.
Proof. exact (@lem5386734 (term622 x s) (term627 x s) (@IN nat x s) (term623 x s)). Qed.
Lemma lem5386776 (x : nat) (s : nat -> Prop) : (term622 x s) = (term632 x s).
Proof. exact (@lem5386735 x s (@lem5386732 x s)). Qed.
Lemma lem5386777 (x : nat) : (term633 x) = (term634 x).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5386776 x s)). Qed.
Lemma lem5386778 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5386779 (x : nat) : (term635 x) = (term636 x).
Proof. exact (MK_COMB (@lem5386778) (@lem5386777 x)). Qed.
Lemma lem5386780 : term637 = term638.
Proof. exact (fun_ext (fun x : nat => @lem5386779 x)). Qed.
Lemma lem5386781 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5386782 : term639 = term640.
Proof. exact (MK_COMB (@lem5386781) (@lem5386780)). Qed.
Lemma lem5386785 : term641 = term641.
Proof. exact (eq_refl term641). Qed.
Lemma lem5386786 : term583 = term642.
Proof. exact (MK_COMB (@lem5386785) (@lem5386782)). Qed.
Lemma lem5386787 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5386788 : term591 = term643.
Proof. exact (MK_COMB (@lem5386787) (@lem5386786)). Qed.
Lemma lem5386789 : term593 = term644.
Proof. exact (MK_COMB (@lem5386788) (@lem5386685)). Qed.
Lemma lem5386793 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (@IN A x s) = False.
Proof. exact (h1). Qed.
Lemma lem5386794 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem5386795 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term645 A x s) = (@COND nat False).
Proof. exact (MK_COMB (@lem5386794) (@lem5386793 A x s h1)). Qed.
Lemma lem5386796 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@CARD A s).
Proof. exact (eq_refl (@CARD A s)). Qed.
Lemma lem5386797 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term646 A x s) = (term647 A s).
Proof. exact (MK_COMB (@lem5386795 A x s h1) (@lem5386796 A s)). Qed.
Lemma lem5386798 {A : Type'} (s : A -> Prop) : (term648 A s) = (term648 A s).
Proof. exact (eq_refl (term648 A s)). Qed.
Lemma lem5386799 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term649 A x s) = (term650 A s).
Proof. exact (MK_COMB (@lem5386797 A x s h1) (@lem5386798 A s)). Qed.
Lemma lem5386801 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5386802 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem5386801 nat t1 t2). Qed.
Lemma lem5386803 {A : Type'} (s : A -> Prop) : (term650 A s) = (term648 A s).
Proof. exact (@lem5386802 (@CARD A s) (term648 A s)). Qed.
Lemma lem5386804 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term649 A x s) = (term648 A s).
Proof. exact (TRANS (@lem5386799 A x s h1) (@lem5386803 A s)). Qed.
Lemma lem5386805 {A : Type'} (x : A) (s : A -> Prop) : (term651 A x s) = (term651 A x s).
Proof. exact (eq_refl (term651 A x s)). Qed.
Lemma lem5386806 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : ((term652 A x s) = (term649 A x s)) = ((term652 A x s) = (term648 A s)).
Proof. exact (MK_COMB (@lem5386805 A x s) (@lem5386804 A x s h1)). Qed.
Lemma lem5386809 {A : Type'} (s : A -> Prop) : (term653 A s) = (term653 A s).
Proof. exact (eq_refl (term653 A s)). Qed.
Lemma lem5386810 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term654 A x s) = (term655 A x s).
Proof. exact (MK_COMB (@lem5386809 A s) (@lem5386806 A x s h1)). Qed.
Lemma lem5386813 {A : Type'} (x : A) (s : A -> Prop) : term656 A x s.
Proof. exact (fun h0 : (@IN A x s) = False => @lem5386810 A x s h0). Qed.
Lemma lem5386815 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (@IN A x s) = True.
Proof. exact (h1). Qed.
Lemma lem5386816 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem5386817 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term645 A x s) = (@COND nat True).
Proof. exact (MK_COMB (@lem5386816) (@lem5386815 A x s h1)). Qed.
Lemma lem5386818 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@CARD A s).
Proof. exact (eq_refl (@CARD A s)). Qed.
Lemma lem5386819 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term646 A x s) = (term657 A s).
Proof. exact (MK_COMB (@lem5386817 A x s h1) (@lem5386818 A s)). Qed.
Lemma lem5386820 {A : Type'} (s : A -> Prop) : (term648 A s) = (term648 A s).
Proof. exact (eq_refl (term648 A s)). Qed.
Lemma lem5386821 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term649 A x s) = (term658 A s).
Proof. exact (MK_COMB (@lem5386819 A x s h1) (@lem5386820 A s)). Qed.
Lemma lem5386823 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5386824 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem5386823 nat t2 t1). Qed.
Lemma lem5386825 {A : Type'} (s : A -> Prop) : (term658 A s) = (@CARD A s).
Proof. exact (@lem5386824 (term648 A s) (@CARD A s)). Qed.
Lemma lem5386826 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term649 A x s) = (@CARD A s).
Proof. exact (TRANS (@lem5386821 A x s h1) (@lem5386825 A s)). Qed.
Lemma lem5386827 {A : Type'} (x : A) (s : A -> Prop) : (term651 A x s) = (term651 A x s).
Proof. exact (eq_refl (term651 A x s)). Qed.
Lemma lem5386828 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : ((term652 A x s) = (term649 A x s)) = ((term652 A x s) = (@CARD A s)).
Proof. exact (MK_COMB (@lem5386827 A x s) (@lem5386826 A x s h1)). Qed.
Lemma lem5386831 {A : Type'} (s : A -> Prop) : (term653 A s) = (term653 A s).
Proof. exact (eq_refl (term653 A s)). Qed.
Lemma lem5386832 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term654 A x s) = (term659 A x s).
Proof. exact (MK_COMB (@lem5386831 A s) (@lem5386828 A x s h1)). Qed.
Lemma lem5386835 {A : Type'} (x : A) (s : A -> Prop) : term660 A x s.
Proof. exact (fun h0 : (@IN A x s) = True => @lem5386832 A x s h0). Qed.
Lemma lem5386836 {A : Type'} (x : A) (s : A -> Prop) : term661 A x s.
Proof. exact (conj (@lem5386813 A x s) (@lem5386835 A x s)). Qed.
Lemma lem5386838 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term630 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem5386839 {A : Type'} (x : A) (s : A -> Prop) : term662 A x s.
Proof. exact (@lem5386838 (term654 A x s) (term659 A x s) (@IN A x s) (term655 A x s)). Qed.
Lemma lem5386880 {A : Type'} (x : A) (s : A -> Prop) : (term654 A x s) = (term663 A x s).
Proof. exact (@lem5386839 A x s (@lem5386836 A x s)). Qed.
Lemma lem5386881 {A : Type'} (x : A) : (term664 A x) = (term665 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5386880 A x s)). Qed.
Lemma lem5386882 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5386883 {A : Type'} (x : A) : (term666 A x) = (term667 A x).
Proof. exact (MK_COMB (@lem5386882 A) (@lem5386881 A x)). Qed.
Lemma lem5386884 {A : Type'} : (term668 A) = (term669 A).
Proof. exact (fun_ext (fun x : A => @lem5386883 A x)). Qed.
Lemma lem5386885 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5386886 {A : Type'} : (term670 A) = (term671 A).
Proof. exact (MK_COMB (@lem5386885 A) (@lem5386884 A)). Qed.
Lemma lem5386889 {A : Type'} : (term672 A) = (term672 A).
Proof. exact (eq_refl (term672 A)). Qed.
Lemma lem5386890 {A : Type'} : (term673 A) = (term674 A).
Proof. exact (MK_COMB (@lem5386889 A) (@lem5386886 A)). Qed.
Lemma lem5386891 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5386892 {A : Type'} : (term594 A) = (term675 A).
Proof. exact (MK_COMB (@lem5386891) (@lem5386890 A)). Qed.
Lemma lem5386893 {A : Type'} : (term596 A) = (term676 A).
Proof. exact (MK_COMB (@lem5386892 A) (@lem5386789)). Qed.
Lemma lem5386898 (n : nat) (m : nat) : (term14 n m) = (term14 n m).
Proof. exact (eq_refl (term14 n m)). Qed.
Lemma lem5386899 (n : nat) : (term677 n) = (term677 n).
Proof. exact (fun_ext (fun m : nat => @lem5386898 n m)). Qed.
Lemma lem5386900 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5386901 (n : nat) : (term527 n) = (term527 n).
Proof. exact (MK_COMB (@lem5386900) (@lem5386899 n)). Qed.
Lemma lem5386902 : term678 = term678.
Proof. exact (fun_ext (fun n : nat => @lem5386901 n)). Qed.
Lemma lem5386903 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5386904 : term528 = term528.
Proof. exact (MK_COMB (@lem5386903) (@lem5386902)). Qed.
Lemma lem5386905 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5386906 : term597 = term597.
Proof. exact (MK_COMB (@lem5386905) (@lem5386904)). Qed.
Lemma lem5386907 {A : Type'} : (term599 A) = (term679 A).
Proof. exact (MK_COMB (@lem5386906) (@lem5386893 A)). Qed.
Lemma lem5386916 (n : nat) (m : nat) : (term600 n m) = (term600 n m).
Proof. exact (eq_refl (term600 n m)). Qed.
Lemma lem5386917 {A : Type'} (n : nat) (m : nat) : (term601 A n m) = (term680 A n m).
Proof. exact (MK_COMB (@lem5386916 n m) (@lem5386907 A)). Qed.
Lemma lem5386918 {A : Type'} (m : nat) : (term603 A m) = (term681 A m).
Proof. exact (fun_ext (fun n : nat => @lem5386917 A n m)). Qed.
Lemma lem5386919 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5386920 {A : Type'} (m : nat) : (term605 A m) = (term682 A m).
Proof. exact (MK_COMB (@lem5386919) (@lem5386918 A m)). Qed.
Lemma lem5386921 {A : Type'} : (term607 A) = (term683 A).
Proof. exact (fun_ext (fun m : nat => @lem5386920 A m)). Qed.
Lemma lem5386922 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5386923 {A : Type'} : (term609 A) = (term684 A).
Proof. exact (MK_COMB (@lem5386922) (@lem5386921 A)). Qed.
Lemma lem5387022 {A : Type'} : (term608 A) = (term684 A).
Proof. exact (TRANS (@lem5386672 A) (@lem5386923 A)). Qed.
Lemma lem5387023 {A : Type'} : (term684 A) = (term608 A).
Proof. exact (SYM (@lem5387022 A)). Qed.
Lemma lem5387024 (n : nat) (m : nat) (h1 : term582 n m) : term582 n m.
Proof. exact (h1). Qed.
Lemma lem5387025 (h1 : term528) : term528.
Proof. exact (h1). Qed.
Lemma lem5387027 (h1 : term642) : term642.
Proof. exact (h1). Qed.
Lemma lem5387028 (h1 : term590) : term590.
Proof. exact (h1). Qed.
Lemma lem5387039 (n : nat) (m : nat) : (term582 n m) = (term685 n m).
Proof. exact (@lem17362 (Peano.lt n m) ((term686 m n) = (term16 n m))). Qed.
Lemma lem5387047 (n : nat) (m : nat) : (term14 n m) = (term15 n m).
Proof. exact (@lem17265 (Peano.lt n m) ((term16 n m) = (NUMERAL 0))). Qed.
Lemma lem5387048 (n : nat) : (term677 n) = (term687 n).
Proof. exact (fun_ext (fun m : nat => @lem5387047 n m)). Qed.
Lemma lem5387049 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5387050 (n : nat) : (term527 n) = (term688 n).
Proof. exact (MK_COMB (@lem5387049) (@lem5387048 n)). Qed.
Lemma lem5387051 : term678 = term689.
Proof. exact (fun_ext (fun n : nat => @lem5387050 n)). Qed.
Lemma lem5387052 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5387109 : term528 = term690.
Proof. exact (MK_COMB (@lem5387052) (@lem5387051)). Qed.
Lemma lem5387110 (h1 : term528) : term690.
Proof. exact (EQ_MP (@lem5387109) (@lem5387025 h1)). Qed.
Lemma lem5387422 (x : nat) (s : nat -> Prop) : (term627 x s) = (term691 x s).
Proof. exact (@lem17265 (@FINITE nat s) ((term620 x s) = (@CARD nat s))). Qed.
Lemma lem5387424 (x : nat) (s : nat -> Prop) : (term692 x s) = (term692 x s).
Proof. exact (eq_refl (term692 x s)). Qed.
Lemma lem5387425 (x : nat) (s : nat -> Prop) : (term693 x s) = (term694 x s).
Proof. exact (MK_COMB (@lem5387424 x s) (@lem5387422 x s)). Qed.
Lemma lem5387433 (x : nat) (s : nat -> Prop) : (term623 x s) = (term695 x s).
Proof. exact (@lem17265 (@FINITE nat s) ((term620 x s) = (term616 s))). Qed.
Lemma lem5387435 (x : nat) (s : nat -> Prop) : (term696 x s) = (term696 x s).
Proof. exact (eq_refl (term696 x s)). Qed.
Lemma lem5387436 (x : nat) (s : nat -> Prop) : (term697 x s) = (term698 x s).
Proof. exact (MK_COMB (@lem5387435 x s) (@lem5387433 x s)). Qed.
Lemma lem5387437 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5387438 (x : nat) (s : nat -> Prop) : (term699 x s) = (term700 x s).
Proof. exact (MK_COMB (@lem5387437) (@lem5387425 x s)). Qed.
Lemma lem5387439 (x : nat) (s : nat -> Prop) : (term632 x s) = (term701 x s).
Proof. exact (MK_COMB (@lem5387438 x s) (@lem5387436 x s)). Qed.
Lemma lem5387440 (x : nat) : (term634 x) = (term702 x).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5387439 x s)). Qed.
Lemma lem5387441 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5387442 (x : nat) : (term636 x) = (term703 x).
Proof. exact (MK_COMB (@lem5387441) (@lem5387440 x)). Qed.
Lemma lem5387443 : term638 = term704.
Proof. exact (fun_ext (fun x : nat => @lem5387442 x)). Qed.
Lemma lem5387444 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5387445 : term640 = term705.
Proof. exact (MK_COMB (@lem5387444) (@lem5387443)). Qed.
Lemma lem5387447 : term641 = term641.
Proof. exact (eq_refl term641). Qed.
Lemma lem5387448 : term642 = term706.
Proof. exact (MK_COMB (@lem5387447) (@lem5387445)). Qed.
Lemma lem5387454 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term707 A P Q) = (term708 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5387455 (P : type993) (Q : type993) : (term709 P Q) = (term710 P Q).
Proof. exact (@lem5387454 (nat -> Prop) P Q). Qed.
Lemma lem5387456 (x : nat) : (term711 x) = (term712 x).
Proof. exact (@lem5387455 (term713 x) (term714 x)). Qed.
Lemma lem5387457 (x : nat) (s : nat -> Prop) : (term715 x s) = (term694 x s).
Proof. exact (eq_refl (term715 x s)). Qed.
Lemma lem5387458 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5387459 (x : nat) (s : nat -> Prop) : (term716 x s) = (term700 x s).
Proof. exact (MK_COMB (@lem5387458) (@lem5387457 x s)). Qed.
Lemma lem5387460 (x : nat) (s : nat -> Prop) : (term717 x s) = (term698 x s).
Proof. exact (eq_refl (term717 x s)). Qed.
Lemma lem5387461 (x : nat) (s : nat -> Prop) : (term718 x s) = (term701 x s).
Proof. exact (MK_COMB (@lem5387459 x s) (@lem5387460 x s)). Qed.
Lemma lem5387462 (x : nat) : (term719 x) = (term702 x).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5387461 x s)). Qed.
Lemma lem5387463 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5387464 (x : nat) : (term711 x) = (term703 x).
Proof. exact (MK_COMB (@lem5387463) (@lem5387462 x)). Qed.
Lemma lem5387465 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5387466 (x : nat) : (term720 x) = (term721 x).
Proof. exact (MK_COMB (@lem5387465) (@lem5387464 x)). Qed.
Lemma lem5387467 (x : nat) (s : nat -> Prop) : (term715 x s) = (term694 x s).
Proof. exact (eq_refl (term715 x s)). Qed.
Lemma lem5387468 (x : nat) : (term722 x) = (term713 x).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5387467 x s)). Qed.
Lemma lem5387469 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5387470 (x : nat) : (term723 x) = (term724 x).
Proof. exact (MK_COMB (@lem5387469) (@lem5387468 x)). Qed.
Lemma lem5387471 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5387472 (x : nat) : (term725 x) = (term726 x).
Proof. exact (MK_COMB (@lem5387471) (@lem5387470 x)). Qed.
Lemma lem5387473 (x : nat) (s : nat -> Prop) : (term717 x s) = (term698 x s).
Proof. exact (eq_refl (term717 x s)). Qed.
Lemma lem5387474 (x : nat) : (term727 x) = (term714 x).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5387473 x s)). Qed.
Lemma lem5387475 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5387476 (x : nat) : (term728 x) = (term729 x).
Proof. exact (MK_COMB (@lem5387475) (@lem5387474 x)). Qed.
Lemma lem5387477 (x : nat) : (term712 x) = (term730 x).
Proof. exact (MK_COMB (@lem5387472 x) (@lem5387476 x)). Qed.
Lemma lem5387478 (x : nat) : ((term711 x) = (term712 x)) = ((term703 x) = (term730 x)).
Proof. exact (MK_COMB (@lem5387466 x) (@lem5387477 x)). Qed.
Lemma lem5387479 (x : nat) : (term703 x) = (term730 x).
Proof. exact (EQ_MP (@lem5387478 x) (@lem5387456 x)). Qed.
Lemma lem5387576 : term704 = term731.
Proof. exact (fun_ext (fun x : nat => @lem5387479 x)). Qed.
Lemma lem5387577 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5387578 : term705 = term732.
Proof. exact (MK_COMB (@lem5387577) (@lem5387576)). Qed.
Lemma lem5387580 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term707 A P Q) = (term708 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5387581 (P : nat -> Prop) (Q : nat -> Prop) : (term733 P Q) = (term734 P Q).
Proof. exact (@lem5387580 nat P Q). Qed.
Lemma lem5387582 : term735 = term736.
Proof. exact (@lem5387581 term737 term738). Qed.
Lemma lem5387583 (x : nat) : (term739 x) = (term724 x).
Proof. exact (eq_refl (term739 x)). Qed.
Lemma lem5387584 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5387585 (x : nat) : (term740 x) = (term726 x).
Proof. exact (MK_COMB (@lem5387584) (@lem5387583 x)). Qed.
Lemma lem5387586 (x : nat) : (term741 x) = (term729 x).
Proof. exact (eq_refl (term741 x)). Qed.
Lemma lem5387587 (x : nat) : (term742 x) = (term730 x).
Proof. exact (MK_COMB (@lem5387585 x) (@lem5387586 x)). Qed.
Lemma lem5387588 : term743 = term731.
Proof. exact (fun_ext (fun x : nat => @lem5387587 x)). Qed.
Lemma lem5387589 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5387590 : term735 = term732.
Proof. exact (MK_COMB (@lem5387589) (@lem5387588)). Qed.
Lemma lem5387591 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5387592 : term744 = term745.
Proof. exact (MK_COMB (@lem5387591) (@lem5387590)). Qed.
Lemma lem5387593 (x : nat) : (term739 x) = (term724 x).
Proof. exact (eq_refl (term739 x)). Qed.
Lemma lem5387594 : term746 = term737.
Proof. exact (fun_ext (fun x : nat => @lem5387593 x)). Qed.
Lemma lem5387595 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5387596 : term747 = term748.
Proof. exact (MK_COMB (@lem5387595) (@lem5387594)). Qed.
Lemma lem5387597 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5387598 : term749 = term750.
Proof. exact (MK_COMB (@lem5387597) (@lem5387596)). Qed.
Lemma lem5387599 (x : nat) : (term741 x) = (term729 x).
Proof. exact (eq_refl (term741 x)). Qed.
Lemma lem5387600 : term751 = term738.
Proof. exact (fun_ext (fun x : nat => @lem5387599 x)). Qed.
Lemma lem5387601 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5387602 : term752 = term753.
Proof. exact (MK_COMB (@lem5387601) (@lem5387600)). Qed.
Lemma lem5387603 : term736 = term754.
Proof. exact (MK_COMB (@lem5387598) (@lem5387602)). Qed.
Lemma lem5387604 : (term735 = term736) = (term732 = term754).
Proof. exact (MK_COMB (@lem5387592) (@lem5387603)). Qed.
Lemma lem5387605 : term732 = term754.
Proof. exact (EQ_MP (@lem5387604) (@lem5387582)). Qed.
Lemma lem5387710 : term705 = term754.
Proof. exact (TRANS (@lem5387578) (@lem5387605)). Qed.
Lemma lem5387711 : term641 = term641.
Proof. exact (eq_refl term641). Qed.
Lemma lem5387714 : term706 = term755.
Proof. exact (MK_COMB (@lem5387711) (@lem5387710)). Qed.
Lemma lem5387715 : term642 = term755.
Proof. exact (TRANS (@lem5387448) (@lem5387714)). Qed.
Lemma lem5387716 (h1 : term642) : term755.
Proof. exact (EQ_MP (@lem5387715) (@lem5387027 h1)). Qed.
Lemma lem5387731 (n : nat) (m : nat) : (((dotdot m n) = (@EMPTY nat)) = (Peano.lt n m)) = (term756 n m).
Proof. exact (@lem17784 ((dotdot m n) = (@EMPTY nat)) (Peano.lt n m)). Qed.
Lemma lem5387732 (m : nat) : (term610 m) = (term757 m).
Proof. exact (fun_ext (fun n : nat => @lem5387731 n m)). Qed.
Lemma lem5387733 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5387734 (m : nat) : (term611 m) = (term758 m).
Proof. exact (MK_COMB (@lem5387733) (@lem5387732 m)). Qed.
Lemma lem5387735 : term612 = term759.
Proof. exact (fun_ext (fun m : nat => @lem5387734 m)). Qed.
Lemma lem5387736 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5387737 : term590 = term760.
Proof. exact (MK_COMB (@lem5387736) (@lem5387735)). Qed.
Lemma lem5387743 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term707 A P Q) = (term708 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5387744 (P : nat -> Prop) (Q : nat -> Prop) : (term733 P Q) = (term734 P Q).
Proof. exact (@lem5387743 nat P Q). Qed.
Lemma lem5387745 (m : nat) : (term761 m) = (term762 m).
Proof. exact (@lem5387744 (term763 m) (term764 m)). Qed.
Lemma lem5387746 (n : nat) (m : nat) : (term765 m n) = (term766 n m).
Proof. exact (eq_refl (term765 m n)). Qed.
Lemma lem5387747 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5387748 (n : nat) (m : nat) : (term767 m n) = (term768 n m).
Proof. exact (MK_COMB (@lem5387747) (@lem5387746 n m)). Qed.
Lemma lem5387749 (n : nat) (m : nat) : (term769 m n) = (term770 n m).
Proof. exact (eq_refl (term769 m n)). Qed.
Lemma lem5387750 (n : nat) (m : nat) : (term771 m n) = (term756 n m).
Proof. exact (MK_COMB (@lem5387748 n m) (@lem5387749 n m)). Qed.
Lemma lem5387751 (m : nat) : (term772 m) = (term757 m).
Proof. exact (fun_ext (fun n : nat => @lem5387750 n m)). Qed.
Lemma lem5387752 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5387753 (m : nat) : (term761 m) = (term758 m).
Proof. exact (MK_COMB (@lem5387752) (@lem5387751 m)). Qed.
Lemma lem5387754 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5387755 (m : nat) : (term773 m) = (term774 m).
Proof. exact (MK_COMB (@lem5387754) (@lem5387753 m)). Qed.
Lemma lem5387756 (n : nat) (m : nat) : (term765 m n) = (term766 n m).
Proof. exact (eq_refl (term765 m n)). Qed.
Lemma lem5387757 (m : nat) : (term775 m) = (term763 m).
Proof. exact (fun_ext (fun n : nat => @lem5387756 n m)). Qed.
Lemma lem5387758 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5387759 (m : nat) : (term776 m) = (term777 m).
Proof. exact (MK_COMB (@lem5387758) (@lem5387757 m)). Qed.
Lemma lem5387760 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5387761 (m : nat) : (term778 m) = (term779 m).
Proof. exact (MK_COMB (@lem5387760) (@lem5387759 m)). Qed.
Lemma lem5387762 (n : nat) (m : nat) : (term769 m n) = (term770 n m).
Proof. exact (eq_refl (term769 m n)). Qed.
Lemma lem5387763 (m : nat) : (term780 m) = (term764 m).
Proof. exact (fun_ext (fun n : nat => @lem5387762 n m)). Qed.
Lemma lem5387764 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5387765 (m : nat) : (term781 m) = (term782 m).
Proof. exact (MK_COMB (@lem5387764) (@lem5387763 m)). Qed.
Lemma lem5387766 (m : nat) : (term762 m) = (term783 m).
Proof. exact (MK_COMB (@lem5387761 m) (@lem5387765 m)). Qed.
Lemma lem5387767 (m : nat) : ((term761 m) = (term762 m)) = ((term758 m) = (term783 m)).
Proof. exact (MK_COMB (@lem5387755 m) (@lem5387766 m)). Qed.
Lemma lem5387768 (m : nat) : (term758 m) = (term783 m).
Proof. exact (EQ_MP (@lem5387767 m) (@lem5387745 m)). Qed.
Lemma lem5387865 : term759 = term784.
Proof. exact (fun_ext (fun m : nat => @lem5387768 m)). Qed.
Lemma lem5387866 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5387867 : term760 = term785.
Proof. exact (MK_COMB (@lem5387866) (@lem5387865)). Qed.
Lemma lem5387869 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term707 A P Q) = (term708 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5387870 (P : nat -> Prop) (Q : nat -> Prop) : (term733 P Q) = (term734 P Q).
Proof. exact (@lem5387869 nat P Q). Qed.
Lemma lem5387871 : term786 = term787.
Proof. exact (@lem5387870 term788 term789). Qed.
Lemma lem5387872 (m : nat) : (term790 m) = (term777 m).
Proof. exact (eq_refl (term790 m)). Qed.
Lemma lem5387873 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5387874 (m : nat) : (term791 m) = (term779 m).
Proof. exact (MK_COMB (@lem5387873) (@lem5387872 m)). Qed.
Lemma lem5387875 (m : nat) : (term792 m) = (term782 m).
Proof. exact (eq_refl (term792 m)). Qed.
Lemma lem5387876 (m : nat) : (term793 m) = (term783 m).
Proof. exact (MK_COMB (@lem5387874 m) (@lem5387875 m)). Qed.
Lemma lem5387877 : term794 = term784.
Proof. exact (fun_ext (fun m : nat => @lem5387876 m)). Qed.
Lemma lem5387878 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5387879 : term786 = term785.
Proof. exact (MK_COMB (@lem5387878) (@lem5387877)). Qed.
Lemma lem5387880 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5387881 : term795 = term796.
Proof. exact (MK_COMB (@lem5387880) (@lem5387879)). Qed.
Lemma lem5387882 (m : nat) : (term790 m) = (term777 m).
Proof. exact (eq_refl (term790 m)). Qed.
Lemma lem5387883 : term797 = term788.
Proof. exact (fun_ext (fun m : nat => @lem5387882 m)). Qed.
Lemma lem5387884 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5387885 : term798 = term799.
Proof. exact (MK_COMB (@lem5387884) (@lem5387883)). Qed.
Lemma lem5387886 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5387887 : term800 = term801.
Proof. exact (MK_COMB (@lem5387886) (@lem5387885)). Qed.
Lemma lem5387888 (m : nat) : (term792 m) = (term782 m).
Proof. exact (eq_refl (term792 m)). Qed.
Lemma lem5387889 : term802 = term789.
Proof. exact (fun_ext (fun m : nat => @lem5387888 m)). Qed.
Lemma lem5387890 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5387891 : term803 = term804.
Proof. exact (MK_COMB (@lem5387890) (@lem5387889)). Qed.
Lemma lem5387892 : term787 = term805.
Proof. exact (MK_COMB (@lem5387887) (@lem5387891)). Qed.
Lemma lem5387893 : (term786 = term787) = (term785 = term805).
Proof. exact (MK_COMB (@lem5387881) (@lem5387892)). Qed.
Lemma lem5387894 : term785 = term805.
Proof. exact (EQ_MP (@lem5387893) (@lem5387871)). Qed.
Lemma lem5388001 : term760 = term805.
Proof. exact (TRANS (@lem5387867) (@lem5387894)). Qed.
Lemma lem5388002 : term590 = term805.
Proof. exact (TRANS (@lem5387737) (@lem5388001)). Qed.
Lemma lem5388003 (h1 : term590) : term805.
Proof. exact (EQ_MP (@lem5388002) (@lem5387028 h1)). Qed.
Lemma lem5388037 (n : nat) (m : nat) (h1 : term582 n m) : term685 n m.
Proof. exact (EQ_MP (@lem5387039 n m) (@lem5387024 n m h1)). Qed.
Lemma lem5388066 (n : nat) (m : nat) : (term15 n m) = (term15 n m).
Proof. exact (eq_refl (term15 n m)). Qed.
Lemma lem5388067 (n : nat) : (term687 n) = (term687 n).
Proof. exact (fun_ext (fun m : nat => @lem5388066 n m)). Qed.
Lemma lem5388068 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5388069 (n : nat) : (term688 n) = (term688 n).
Proof. exact (MK_COMB (@lem5388068) (@lem5388067 n)). Qed.
Lemma lem5388070 : term689 = term689.
Proof. exact (fun_ext (fun n : nat => @lem5388069 n)). Qed.
Lemma lem5388071 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5388072 : term690 = term690.
Proof. exact (MK_COMB (@lem5388071) (@lem5388070)). Qed.
Lemma lem5388073 (h1 : term528) : term690.
Proof. exact (EQ_MP (@lem5388072) (@lem5387110 h1)). Qed.
Lemma lem5388194 (x : nat) (s : nat -> Prop) : (term698 x s) = (term698 x s).
Proof. exact (eq_refl (term698 x s)). Qed.
Lemma lem5388195 (x : nat) : (term714 x) = (term714 x).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5388194 x s)). Qed.
Lemma lem5388196 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5388197 (x : nat) : (term729 x) = (term729 x).
Proof. exact (MK_COMB (@lem5388196) (@lem5388195 x)). Qed.
Lemma lem5388198 : term738 = term738.
Proof. exact (fun_ext (fun x : nat => @lem5388197 x)). Qed.
Lemma lem5388199 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5388200 : term753 = term753.
Proof. exact (MK_COMB (@lem5388199) (@lem5388198)). Qed.
Lemma lem5388231 (x : nat) (s : nat -> Prop) : (term694 x s) = (term694 x s).
Proof. exact (eq_refl (term694 x s)). Qed.
Lemma lem5388232 (x : nat) : (term713 x) = (term713 x).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5388231 x s)). Qed.
Lemma lem5388233 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5388234 (x : nat) : (term724 x) = (term724 x).
Proof. exact (MK_COMB (@lem5388233) (@lem5388232 x)). Qed.
Lemma lem5388235 : term737 = term737.
Proof. exact (fun_ext (fun x : nat => @lem5388234 x)). Qed.
Lemma lem5388236 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5388237 : term748 = term748.
Proof. exact (MK_COMB (@lem5388236) (@lem5388235)). Qed.
Lemma lem5388238 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5388239 : term750 = term750.
Proof. exact (MK_COMB (@lem5388238) (@lem5388237)). Qed.
Lemma lem5388240 : term754 = term754.
Proof. exact (MK_COMB (@lem5388239) (@lem5388200)). Qed.
Lemma lem5388251 : term641 = term641.
Proof. exact (eq_refl term641). Qed.
Lemma lem5388252 : term755 = term755.
Proof. exact (MK_COMB (@lem5388251) (@lem5388240)). Qed.
Lemma lem5388253 (h1 : term642) : term755.
Proof. exact (EQ_MP (@lem5388252) (@lem5387716 h1)). Qed.
Lemma lem5388272 (n : nat) (m : nat) : (term770 n m) = (term770 n m).
Proof. exact (eq_refl (term770 n m)). Qed.
Lemma lem5388273 (m : nat) : (term764 m) = (term764 m).
Proof. exact (fun_ext (fun n : nat => @lem5388272 n m)). Qed.
Lemma lem5388274 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5388275 (m : nat) : (term782 m) = (term782 m).
Proof. exact (MK_COMB (@lem5388274) (@lem5388273 m)). Qed.
Lemma lem5388276 : term789 = term789.
Proof. exact (fun_ext (fun m : nat => @lem5388275 m)). Qed.
Lemma lem5388277 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5388278 : term804 = term804.
Proof. exact (MK_COMB (@lem5388277) (@lem5388276)). Qed.
Lemma lem5388297 (n : nat) (m : nat) : (term766 n m) = (term766 n m).
Proof. exact (eq_refl (term766 n m)). Qed.
Lemma lem5388298 (m : nat) : (term763 m) = (term763 m).
Proof. exact (fun_ext (fun n : nat => @lem5388297 n m)). Qed.
Lemma lem5388299 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5388300 (m : nat) : (term777 m) = (term777 m).
Proof. exact (MK_COMB (@lem5388299) (@lem5388298 m)). Qed.
Lemma lem5388301 : term788 = term788.
Proof. exact (fun_ext (fun m : nat => @lem5388300 m)). Qed.
Lemma lem5388302 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5388303 : term799 = term799.
Proof. exact (MK_COMB (@lem5388302) (@lem5388301)). Qed.
Lemma lem5388304 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5388305 : term801 = term801.
Proof. exact (MK_COMB (@lem5388304) (@lem5388303)). Qed.
Lemma lem5388306 : term805 = term805.
Proof. exact (MK_COMB (@lem5388305) (@lem5388278)). Qed.
Lemma lem5388307 (h1 : term590) : term805.
Proof. exact (EQ_MP (@lem5388306) (@lem5388003 h1)). Qed.
Lemma lem5388309 (h1 : term590) : term799.
Proof. exact (proj1 (@lem5388307 h1)). Qed.
Lemma lem5388327 (n : nat) (m : nat) : (term15 n m) = (term15 n m).
Proof. exact (eq_refl (term15 n m)). Qed.
Lemma lem5388328 (n : nat) : (term687 n) = (term687 n).
Proof. exact (fun_ext (fun m : nat => @lem5388327 n m)). Qed.
Lemma lem5388329 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5388330 (n : nat) : (term688 n) = (term688 n).
Proof. exact (MK_COMB (@lem5388329) (@lem5388328 n)). Qed.
Lemma lem5388331 : term689 = term689.
Proof. exact (fun_ext (fun n : nat => @lem5388330 n)). Qed.
Lemma lem5388332 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5388334 : term690 = term690.
Proof. exact (MK_COMB (@lem5388332) (@lem5388331)). Qed.
Lemma lem5388335 (h1 : term528) : term690.
Proof. exact (EQ_MP (@lem5388334) (@lem5388073 h1)). Qed.
Lemma lem5388343 (n : nat) (m : nat) : (term766 n m) = (term766 n m).
Proof. exact (eq_refl (term766 n m)). Qed.
Lemma lem5388344 (m : nat) : (term763 m) = (term763 m).
Proof. exact (fun_ext (fun n : nat => @lem5388343 n m)). Qed.
Lemma lem5388345 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5388346 (m : nat) : (term777 m) = (term777 m).
Proof. exact (MK_COMB (@lem5388345) (@lem5388344 m)). Qed.
Lemma lem5388347 : term788 = term788.
Proof. exact (fun_ext (fun m : nat => @lem5388346 m)). Qed.
Lemma lem5388348 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5388350 : term799 = term799.
Proof. exact (MK_COMB (@lem5388348) (@lem5388347)). Qed.
Lemma lem5388351 (h1 : term590) : term799.
Proof. exact (EQ_MP (@lem5388350) (@lem5388309 h1)). Qed.
Lemma lem5388472 (_69803 : nat) (h1 : term528) : term806 _69803.
Proof. exact (@lem5388335 h1 _69803). Qed.
Lemma lem5388473 (_69803 : nat) : (term806 _69803) = (term688 _69803).
Proof. exact (eq_refl (term806 _69803)). Qed.
Lemma lem5388474 (_69803 : nat) (h1 : term528) : term688 _69803.
Proof. exact (EQ_MP (@lem5388473 _69803) (@lem5388472 _69803 h1)). Qed.
Lemma lem5388475 (_69803 : nat) (_69804 : nat) (h1 : term528) : term807 _69803 _69804.
Proof. exact (@lem5388474 _69803 h1 _69804). Qed.
Lemma lem5388476 (_69803 : nat) (_69804 : nat) : (term807 _69803 _69804) = (term15 _69803 _69804).
Proof. exact (eq_refl (term807 _69803 _69804)). Qed.
Lemma lem5388478 (_69805 : nat) (h1 : term590) : term790 _69805.
Proof. exact (@lem5388351 h1 _69805). Qed.
Lemma lem5388479 (_69805 : nat) : (term790 _69805) = (term777 _69805).
Proof. exact (eq_refl (term790 _69805)). Qed.
Lemma lem5388480 (_69805 : nat) (h1 : term590) : term777 _69805.
Proof. exact (EQ_MP (@lem5388479 _69805) (@lem5388478 _69805 h1)). Qed.
Lemma lem5388481 (_69805 : nat) (_69806 : nat) (h1 : term590) : term765 _69805 _69806.
Proof. exact (@lem5388480 _69805 h1 _69806). Qed.
Lemma lem5388482 (_69806 : nat) (_69805 : nat) : (term765 _69805 _69806) = (term766 _69806 _69805).
Proof. exact (eq_refl (term765 _69805 _69806)). Qed.
Lemma lem5388519 (_69803 : nat) (_69804 : nat) (h1 : term528) : term15 _69803 _69804.
Proof. exact (EQ_MP (@lem5388476 _69803 _69804) (@lem5388475 _69803 _69804 h1)). Qed.
Lemma lem5388525 (_69806 : nat) (_69805 : nat) (h1 : term590) : term766 _69806 _69805.
Proof. exact (EQ_MP (@lem5388482 _69806 _69805) (@lem5388481 _69805 _69806 h1)). Qed.
Lemma lem5388579 (n : nat) (m : nat) (h1 : term582 n m) : term808 n m.
Proof. exact (proj2 (@lem5388037 n m h1)). Qed.
Lemma lem5388707 : (@CARD nat) = (@CARD nat).
Proof. exact (eq_refl (@CARD nat)). Qed.
Lemma lem5388708 (_69845 : nat -> Prop) (_69846 : nat -> Prop) (h1 : _69845 = _69846) : _69845 = _69846.
Proof. exact (h1). Qed.
Lemma lem5388709 (_69845 : nat -> Prop) (_69846 : nat -> Prop) (h1 : _69845 = _69846) : (@CARD nat _69845) = (@CARD nat _69846).
Proof. exact (MK_COMB (@lem5388707) (@lem5388708 _69845 _69846 h1)). Qed.
Lemma lem5388710 (_69845 : nat -> Prop) (_69846 : nat -> Prop) : term809 _69845 _69846.
Proof. exact (fun h0 : _69845 = _69846 => @lem5388709 _69845 _69846 h0). Qed.
Lemma lem5388712 (a : Prop) (b : Prop) : (a -> b) = (term810 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5388713 (_69845 : nat -> Prop) (_69846 : nat -> Prop) : (term809 _69845 _69846) = (term811 _69845 _69846).
Proof. exact (@lem5388712 (_69845 = _69846) ((@CARD nat _69845) = (@CARD nat _69846))). Qed.
Lemma lem5388714 (_69845 : nat -> Prop) (_69846 : nat -> Prop) : term811 _69845 _69846.
Proof. exact (EQ_MP (@lem5388713 _69845 _69846) (@lem5388710 _69845 _69846)). Qed.
Lemma lem5388777 (x : nat) (y : nat) (z : nat) : term812 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem5388779 (x : nat -> Prop) (y : nat -> Prop) (z : nat -> Prop) : term813 x y z.
Proof. exact (@lem21385 (nat -> Prop) x y z). Qed.
Lemma lem5388785 (h1 : term642) : (@CARD nat (@EMPTY nat)) = (NUMERAL 0).
Proof. exact (proj1 (@lem5388253 h1)). Qed.
Lemma lem5388786 (h1 : term642) : term814.
Proof. exact (fun h0 : term815 => @lem5388785 h1). Qed.
Lemma lem5388788 (p : Prop) : (term816 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5388789 : term814 = ((@CARD nat (@EMPTY nat)) = (NUMERAL 0)).
Proof. exact (@lem5388788 ((@CARD nat (@EMPTY nat)) = (NUMERAL 0))). Qed.
Lemma lem5388790 (h1 : term642) : (@CARD nat (@EMPTY nat)) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem5388789) (@lem5388786 h1)). Qed.
Lemma lem5388792 (n : nat) (m : nat) (h1 : term582 n m) : Peano.lt n m.
Proof. exact (proj1 (@lem5388037 n m h1)). Qed.
Lemma lem5388793 (n : nat) (m : nat) (h1 : term582 n m) : term817 n m.
Proof. exact (fun h0 : term65 n m => @lem5388792 n m h1). Qed.
Lemma lem5388795 (p : Prop) : (term816 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5388796 (n : nat) (m : nat) : (term817 n m) = (Peano.lt n m).
Proof. exact (@lem5388795 (Peano.lt n m)). Qed.
Lemma lem5388797 (n : nat) (m : nat) (h1 : term582 n m) : Peano.lt n m.
Proof. exact (EQ_MP (@lem5388796 n m) (@lem5388793 n m h1)). Qed.
Lemma lem5388799 (b : Prop) (a : Prop) : (a \/ b) = (term818 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5388800 (_69805 : nat) (_69806 : nat) : (term766 _69806 _69805) = (term819 _69805 _69806).
Proof. exact (@lem5388799 (term65 _69806 _69805) ((dotdot _69805 _69806) = (@EMPTY nat))). Qed.
Lemma lem5388802 (a : Prop) : (term192 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5388803 (_69806 : nat) (_69805 : nat) : (term820 _69806 _69805) = (Peano.lt _69806 _69805).
Proof. exact (@lem5388802 (Peano.lt _69806 _69805)). Qed.
Lemma lem5388804 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5388805 (_69806 : nat) (_69805 : nat) : (term821 _69806 _69805) = (term822 _69806 _69805).
Proof. exact (MK_COMB (@lem5388804) (@lem5388803 _69806 _69805)). Qed.
Lemma lem5388806 (_69805 : nat) (_69806 : nat) : ((dotdot _69805 _69806) = (@EMPTY nat)) = ((dotdot _69805 _69806) = (@EMPTY nat)).
Proof. exact (eq_refl ((dotdot _69805 _69806) = (@EMPTY nat))). Qed.
Lemma lem5388807 (_69805 : nat) (_69806 : nat) : (term819 _69805 _69806) = (term823 _69805 _69806).
Proof. exact (MK_COMB (@lem5388805 _69806 _69805) (@lem5388806 _69805 _69806)). Qed.
Lemma lem5388808 (_69805 : nat) (_69806 : nat) : (term766 _69806 _69805) = (term823 _69805 _69806).
Proof. exact (TRANS (@lem5388800 _69805 _69806) (@lem5388807 _69805 _69806)). Qed.
Lemma lem5388811 (_69805 : nat) (_69806 : nat) (h1 : term590) : term823 _69805 _69806.
Proof. exact (EQ_MP (@lem5388808 _69805 _69806) (@lem5388525 _69806 _69805 h1)). Qed.
Lemma lem5388812 (m : nat) (n : nat) (h1 : term590) : term823 m n.
Proof. exact (@lem5388811 m n h1). Qed.
Lemma lem5388815 (n : nat) (m : nat) (h1 : term590) (h2 : term582 n m) : (dotdot m n) = (@EMPTY nat).
Proof. exact (@lem5388812 m n h1 (@lem5388797 n m h2)). Qed.
Lemma lem5388816 (n : nat) (m : nat) (h1 : term590) (h2 : term582 n m) : term824 m n.
Proof. exact (fun h0 : term825 m n => @lem5388815 n m h1 h2). Qed.
Lemma lem5388818 (p : Prop) : (term816 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5388819 (m : nat) (n : nat) : (term824 m n) = ((dotdot m n) = (@EMPTY nat)).
Proof. exact (@lem5388818 ((dotdot m n) = (@EMPTY nat))). Qed.
Lemma lem5388820 (n : nat) (m : nat) (h1 : term590) (h2 : term582 n m) : (dotdot m n) = (@EMPTY nat).
Proof. exact (EQ_MP (@lem5388819 m n) (@lem5388816 n m h1 h2)). Qed.
Lemma lem5388822 (x : nat -> Prop) : x = x.
Proof. exact (@lem21386 (nat -> Prop) x). Qed.
Lemma lem5388823 (m : nat) (n : nat) : (dotdot m n) = (dotdot m n).
Proof. exact (@lem5388822 (dotdot m n)). Qed.
Lemma lem5388824 (m : nat) (n : nat) : term826 m n.
Proof. exact (fun h0 : term827 m n => @lem5388823 m n). Qed.
Lemma lem5388826 (p : Prop) : (term816 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5388827 (m : nat) (n : nat) : (term826 m n) = ((dotdot m n) = (dotdot m n)).
Proof. exact (@lem5388826 ((dotdot m n) = (dotdot m n))). Qed.
Lemma lem5388828 (m : nat) (n : nat) : (dotdot m n) = (dotdot m n).
Proof. exact (EQ_MP (@lem5388827 m n) (@lem5388824 m n)). Qed.
Lemma lem5388846 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5388847 (y : nat -> Prop) (x : nat -> Prop) (z : nat -> Prop) : (term828 x y z) = (term829 y x z).
Proof. exact (@lem5388846 (y = z) (term830 x z)). Qed.
Lemma lem5388857 (x : nat -> Prop) (y : nat -> Prop) : (term831 x y) = (term831 x y).
Proof. exact (eq_refl (term831 x y)). Qed.
Lemma lem5388858 (y : nat -> Prop) (x : nat -> Prop) (z : nat -> Prop) : (term813 x y z) = (term832 y x z).
Proof. exact (MK_COMB (@lem5388857 x y) (@lem5388847 y x z)). Qed.
Lemma lem5388862 (q : Prop) (p : Prop) (r : Prop) : (term833 p q r) = (term833 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5388863 (y : nat -> Prop) (x : nat -> Prop) (z : nat -> Prop) : (term832 y x z) = (term834 y x z).
Proof. exact (@lem5388862 (y = z) (term830 x y) (term830 x z)). Qed.
Lemma lem5388885 (y : nat -> Prop) (x : nat -> Prop) (z : nat -> Prop) : (term813 x y z) = (term834 y x z).
Proof. exact (TRANS (@lem5388858 y x z) (@lem5388863 y x z)). Qed.
Lemma lem5388886 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5388887 (y : nat -> Prop) (x : nat -> Prop) (z : nat -> Prop) : (term835 x y z) = (term836 y x z).
Proof. exact (MK_COMB (@lem5388886) (@lem5388885 y x z)). Qed.
Lemma lem5388909 (y : nat -> Prop) (x : nat -> Prop) (z : nat -> Prop) : (term834 y x z) = (term834 y x z).
Proof. exact (eq_refl (term834 y x z)). Qed.
Lemma lem5388910 (y : nat -> Prop) (x : nat -> Prop) (z : nat -> Prop) : ((term813 x y z) = (term834 y x z)) = ((term834 y x z) = (term834 y x z)).
Proof. exact (MK_COMB (@lem5388887 y x z) (@lem5388909 y x z)). Qed.
Lemma lem5388912 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5388913 (x : Prop) : (x = x) = True.
Proof. exact (@lem5388912 Prop x). Qed.
Lemma lem5388914 (y : nat -> Prop) (x : nat -> Prop) (z : nat -> Prop) : ((term834 y x z) = (term834 y x z)) = True.
Proof. exact (@lem5388913 (term834 y x z)). Qed.
Lemma lem5388915 (y : nat -> Prop) (x : nat -> Prop) (z : nat -> Prop) : ((term813 x y z) = (term834 y x z)) = True.
Proof. exact (TRANS (@lem5388910 y x z) (@lem5388914 y x z)). Qed.
Lemma lem5388916 (y : nat -> Prop) (x : nat -> Prop) (z : nat -> Prop) : True = ((term813 x y z) = (term834 y x z)).
Proof. exact (SYM (@lem5388915 y x z)). Qed.
Lemma lem5388917 (y : nat -> Prop) (x : nat -> Prop) (z : nat -> Prop) : (term813 x y z) = (term834 y x z).
Proof. exact (EQ_MP (@lem5388916 y x z) (@lem0)). Qed.
Lemma lem5388918 (y : nat -> Prop) (x : nat -> Prop) (z : nat -> Prop) : term834 y x z.
Proof. exact (EQ_MP (@lem5388917 y x z) (@lem5388779 x y z)). Qed.
Lemma lem5388920 (b : Prop) (a : Prop) : (a \/ b) = (term818 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5388921 (x : nat -> Prop) (y : nat -> Prop) (z : nat -> Prop) : (term834 y x z) = (term837 x y z).
Proof. exact (@lem5388920 (term838 y x z) (y = z)). Qed.
Lemma lem5388923 (a : Prop) (b : Prop) : (term839 a b) = (term840 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5388924 (y : nat -> Prop) (x : nat -> Prop) (z : nat -> Prop) : (term841 y x z) = (term842 y x z).
Proof. exact (@lem5388923 (term830 x y) (term830 x z)). Qed.
Lemma lem5388926 (a : Prop) : (term192 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5388927 (x : nat -> Prop) (y : nat -> Prop) : (term843 x y) = (x = y).
Proof. exact (@lem5388926 (x = y)). Qed.
Lemma lem5388928 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5388929 (x : nat -> Prop) (y : nat -> Prop) : (term844 x y) = (term845 x y).
Proof. exact (MK_COMB (@lem5388928) (@lem5388927 x y)). Qed.
Lemma lem5388931 (a : Prop) : (term192 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5388932 (x : nat -> Prop) (z : nat -> Prop) : (term843 x z) = (x = z).
Proof. exact (@lem5388931 (x = z)). Qed.
Lemma lem5388933 (y : nat -> Prop) (x : nat -> Prop) (z : nat -> Prop) : (term842 y x z) = (term846 y x z).
Proof. exact (MK_COMB (@lem5388929 x y) (@lem5388932 x z)). Qed.
Lemma lem5388934 (y : nat -> Prop) (x : nat -> Prop) (z : nat -> Prop) : (term841 y x z) = (term846 y x z).
Proof. exact (TRANS (@lem5388924 y x z) (@lem5388933 y x z)). Qed.
Lemma lem5388935 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5388936 (y : nat -> Prop) (x : nat -> Prop) (z : nat -> Prop) : (term847 y x z) = (term848 y x z).
Proof. exact (MK_COMB (@lem5388935) (@lem5388934 y x z)). Qed.
Lemma lem5388937 (y : nat -> Prop) (z : nat -> Prop) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5388938 (x : nat -> Prop) (y : nat -> Prop) (z : nat -> Prop) : (term837 x y z) = (term849 x y z).
Proof. exact (MK_COMB (@lem5388936 y x z) (@lem5388937 y z)). Qed.
Lemma lem5388939 (x : nat -> Prop) (y : nat -> Prop) (z : nat -> Prop) : (term834 y x z) = (term849 x y z).
Proof. exact (TRANS (@lem5388921 x y z) (@lem5388938 x y z)). Qed.
Lemma lem5388941 (n : nat) (m : nat) (h1 : term590) (h2 : term582 n m) : term850 m n.
Proof. exact (conj (@lem5388820 n m h1 h2) (@lem5388828 m n)). Qed.
Lemma lem5388943 (x : nat -> Prop) (y : nat -> Prop) (z : nat -> Prop) : term849 x y z.
Proof. exact (EQ_MP (@lem5388939 x y z) (@lem5388918 y x z)). Qed.
Lemma lem5388944 (m : nat) (n : nat) : term851 m n.
Proof. exact (@lem5388943 (dotdot m n) (@EMPTY nat) (dotdot m n)). Qed.
Lemma lem5388947 (n : nat) (m : nat) (h1 : term590) (h2 : term582 n m) : (@EMPTY nat) = (dotdot m n).
Proof. exact (@lem5388944 m n (@lem5388941 n m h1 h2)). Qed.
Lemma lem5388948 (n : nat) (m : nat) (h1 : term590) (h2 : term582 n m) : term852 m n.
Proof. exact (fun h0 : term853 m n => @lem5388947 n m h1 h2). Qed.
Lemma lem5388950 (p : Prop) : (term816 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5388951 (m : nat) (n : nat) : (term852 m n) = ((@EMPTY nat) = (dotdot m n)).
Proof. exact (@lem5388950 ((@EMPTY nat) = (dotdot m n))). Qed.
Lemma lem5388952 (n : nat) (m : nat) (h1 : term590) (h2 : term582 n m) : (@EMPTY nat) = (dotdot m n).
Proof. exact (EQ_MP (@lem5388951 m n) (@lem5388948 n m h1 h2)). Qed.
Lemma lem5388958 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5388959 (_69845 : nat -> Prop) (_69846 : nat -> Prop) : (term811 _69845 _69846) = (term854 _69845 _69846).
Proof. exact (@lem5388958 ((@CARD nat _69845) = (@CARD nat _69846)) (term830 _69845 _69846)). Qed.
Lemma lem5388969 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5388970 (_69845 : nat -> Prop) (_69846 : nat -> Prop) : (term855 _69845 _69846) = (term856 _69845 _69846).
Proof. exact (MK_COMB (@lem5388969) (@lem5388959 _69845 _69846)). Qed.
Lemma lem5388980 (_69845 : nat -> Prop) (_69846 : nat -> Prop) : (term854 _69845 _69846) = (term854 _69845 _69846).
Proof. exact (eq_refl (term854 _69845 _69846)). Qed.
Lemma lem5388981 (_69845 : nat -> Prop) (_69846 : nat -> Prop) : ((term811 _69845 _69846) = (term854 _69845 _69846)) = ((term854 _69845 _69846) = (term854 _69845 _69846)).
Proof. exact (MK_COMB (@lem5388970 _69845 _69846) (@lem5388980 _69845 _69846)). Qed.
Lemma lem5388983 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5388984 (x : Prop) : (x = x) = True.
Proof. exact (@lem5388983 Prop x). Qed.
Lemma lem5388985 (_69845 : nat -> Prop) (_69846 : nat -> Prop) : ((term854 _69845 _69846) = (term854 _69845 _69846)) = True.
Proof. exact (@lem5388984 (term854 _69845 _69846)). Qed.
Lemma lem5388986 (_69845 : nat -> Prop) (_69846 : nat -> Prop) : ((term811 _69845 _69846) = (term854 _69845 _69846)) = True.
Proof. exact (TRANS (@lem5388981 _69845 _69846) (@lem5388985 _69845 _69846)). Qed.
Lemma lem5388987 (_69845 : nat -> Prop) (_69846 : nat -> Prop) : True = ((term811 _69845 _69846) = (term854 _69845 _69846)).
Proof. exact (SYM (@lem5388986 _69845 _69846)). Qed.
Lemma lem5388988 (_69845 : nat -> Prop) (_69846 : nat -> Prop) : (term811 _69845 _69846) = (term854 _69845 _69846).
Proof. exact (EQ_MP (@lem5388987 _69845 _69846) (@lem0)). Qed.
Lemma lem5388989 (_69845 : nat -> Prop) (_69846 : nat -> Prop) : term854 _69845 _69846.
Proof. exact (EQ_MP (@lem5388988 _69845 _69846) (@lem5388714 _69845 _69846)). Qed.
Lemma lem5388991 (b : Prop) (a : Prop) : (a \/ b) = (term818 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5388992 (_69845 : nat -> Prop) (_69846 : nat -> Prop) : (term854 _69845 _69846) = (term857 _69845 _69846).
Proof. exact (@lem5388991 (term830 _69845 _69846) ((@CARD nat _69845) = (@CARD nat _69846))). Qed.
Lemma lem5388994 (a : Prop) : (term192 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5388995 (_69845 : nat -> Prop) (_69846 : nat -> Prop) : (term843 _69845 _69846) = (_69845 = _69846).
Proof. exact (@lem5388994 (_69845 = _69846)). Qed.
Lemma lem5388996 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5388997 (_69845 : nat -> Prop) (_69846 : nat -> Prop) : (term858 _69845 _69846) = (term859 _69845 _69846).
Proof. exact (MK_COMB (@lem5388996) (@lem5388995 _69845 _69846)). Qed.
Lemma lem5388998 (_69845 : nat -> Prop) (_69846 : nat -> Prop) : ((@CARD nat _69845) = (@CARD nat _69846)) = ((@CARD nat _69845) = (@CARD nat _69846)).
Proof. exact (eq_refl ((@CARD nat _69845) = (@CARD nat _69846))). Qed.
Lemma lem5388999 (_69845 : nat -> Prop) (_69846 : nat -> Prop) : (term857 _69845 _69846) = (term809 _69845 _69846).
Proof. exact (MK_COMB (@lem5388997 _69845 _69846) (@lem5388998 _69845 _69846)). Qed.
Lemma lem5389000 (_69845 : nat -> Prop) (_69846 : nat -> Prop) : (term854 _69845 _69846) = (term809 _69845 _69846).
Proof. exact (TRANS (@lem5388992 _69845 _69846) (@lem5388999 _69845 _69846)). Qed.
Lemma lem5389003 (_69845 : nat -> Prop) (_69846 : nat -> Prop) : term809 _69845 _69846.
Proof. exact (EQ_MP (@lem5389000 _69845 _69846) (@lem5388989 _69845 _69846)). Qed.
Lemma lem5389004 (m : nat) (n : nat) : term860 m n.
Proof. exact (@lem5389003 (@EMPTY nat) (dotdot m n)). Qed.
Lemma lem5389007 (n : nat) (m : nat) (h1 : term590) (h2 : term582 n m) : (@CARD nat (@EMPTY nat)) = (term686 m n).
Proof. exact (@lem5389004 m n (@lem5388952 n m h1 h2)). Qed.
Lemma lem5389008 (n : nat) (m : nat) (h1 : term590) (h2 : term582 n m) : term861 m n.
Proof. exact (fun h0 : term862 m n => @lem5389007 n m h1 h2). Qed.
Lemma lem5389010 (p : Prop) : (term816 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5389011 (m : nat) (n : nat) : (term861 m n) = ((@CARD nat (@EMPTY nat)) = (term686 m n)).
Proof. exact (@lem5389010 ((@CARD nat (@EMPTY nat)) = (term686 m n))). Qed.
Lemma lem5389012 (n : nat) (m : nat) (h1 : term590) (h2 : term582 n m) : (@CARD nat (@EMPTY nat)) = (term686 m n).
Proof. exact (EQ_MP (@lem5389011 m n) (@lem5389008 n m h1 h2)). Qed.
Lemma lem5389030 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5389031 (y : nat) (x : nat) (z : nat) : (term863 x y z) = (term864 y x z).
Proof. exact (@lem5389030 (y = z) (term865 x z)). Qed.
Lemma lem5389041 (x : nat) (y : nat) : (term866 x y) = (term866 x y).
Proof. exact (eq_refl (term866 x y)). Qed.
Lemma lem5389042 (y : nat) (x : nat) (z : nat) : (term812 x y z) = (term867 y x z).
Proof. exact (MK_COMB (@lem5389041 x y) (@lem5389031 y x z)). Qed.
Lemma lem5389046 (q : Prop) (p : Prop) (r : Prop) : (term833 p q r) = (term833 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5389047 (y : nat) (x : nat) (z : nat) : (term867 y x z) = (term868 y x z).
Proof. exact (@lem5389046 (y = z) (term865 x y) (term865 x z)). Qed.
Lemma lem5389069 (y : nat) (x : nat) (z : nat) : (term812 x y z) = (term868 y x z).
Proof. exact (TRANS (@lem5389042 y x z) (@lem5389047 y x z)). Qed.
Lemma lem5389070 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5389071 (y : nat) (x : nat) (z : nat) : (term869 x y z) = (term870 y x z).
Proof. exact (MK_COMB (@lem5389070) (@lem5389069 y x z)). Qed.
Lemma lem5389093 (y : nat) (x : nat) (z : nat) : (term868 y x z) = (term868 y x z).
Proof. exact (eq_refl (term868 y x z)). Qed.
Lemma lem5389094 (y : nat) (x : nat) (z : nat) : ((term812 x y z) = (term868 y x z)) = ((term868 y x z) = (term868 y x z)).
Proof. exact (MK_COMB (@lem5389071 y x z) (@lem5389093 y x z)). Qed.
Lemma lem5389096 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5389097 (x : Prop) : (x = x) = True.
Proof. exact (@lem5389096 Prop x). Qed.
Lemma lem5389098 (y : nat) (x : nat) (z : nat) : ((term868 y x z) = (term868 y x z)) = True.
Proof. exact (@lem5389097 (term868 y x z)). Qed.
Lemma lem5389099 (y : nat) (x : nat) (z : nat) : ((term812 x y z) = (term868 y x z)) = True.
Proof. exact (TRANS (@lem5389094 y x z) (@lem5389098 y x z)). Qed.
Lemma lem5389100 (y : nat) (x : nat) (z : nat) : True = ((term812 x y z) = (term868 y x z)).
Proof. exact (SYM (@lem5389099 y x z)). Qed.
Lemma lem5389101 (y : nat) (x : nat) (z : nat) : (term812 x y z) = (term868 y x z).
Proof. exact (EQ_MP (@lem5389100 y x z) (@lem0)). Qed.
Lemma lem5389102 (y : nat) (x : nat) (z : nat) : term868 y x z.
Proof. exact (EQ_MP (@lem5389101 y x z) (@lem5388777 x y z)). Qed.
Lemma lem5389104 (b : Prop) (a : Prop) : (a \/ b) = (term818 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5389105 (x : nat) (y : nat) (z : nat) : (term868 y x z) = (term871 x y z).
Proof. exact (@lem5389104 (term872 y x z) (y = z)). Qed.
Lemma lem5389107 (a : Prop) (b : Prop) : (term839 a b) = (term840 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5389108 (y : nat) (x : nat) (z : nat) : (term873 y x z) = (term874 y x z).
Proof. exact (@lem5389107 (term865 x y) (term865 x z)). Qed.
Lemma lem5389110 (a : Prop) : (term192 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5389111 (x : nat) (y : nat) : (term875 x y) = (x = y).
Proof. exact (@lem5389110 (x = y)). Qed.
Lemma lem5389112 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5389113 (x : nat) (y : nat) : (term876 x y) = (term877 x y).
Proof. exact (MK_COMB (@lem5389112) (@lem5389111 x y)). Qed.
Lemma lem5389115 (a : Prop) : (term192 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5389116 (x : nat) (z : nat) : (term875 x z) = (x = z).
Proof. exact (@lem5389115 (x = z)). Qed.
Lemma lem5389117 (y : nat) (x : nat) (z : nat) : (term874 y x z) = (term878 y x z).
Proof. exact (MK_COMB (@lem5389113 x y) (@lem5389116 x z)). Qed.
Lemma lem5389118 (y : nat) (x : nat) (z : nat) : (term873 y x z) = (term878 y x z).
Proof. exact (TRANS (@lem5389108 y x z) (@lem5389117 y x z)). Qed.
Lemma lem5389119 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5389120 (y : nat) (x : nat) (z : nat) : (term879 y x z) = (term880 y x z).
Proof. exact (MK_COMB (@lem5389119) (@lem5389118 y x z)). Qed.
Lemma lem5389121 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5389122 (x : nat) (y : nat) (z : nat) : (term871 x y z) = (term881 x y z).
Proof. exact (MK_COMB (@lem5389120 y x z) (@lem5389121 y z)). Qed.
Lemma lem5389123 (x : nat) (y : nat) (z : nat) : (term868 y x z) = (term881 x y z).
Proof. exact (TRANS (@lem5389105 x y z) (@lem5389122 x y z)). Qed.
Lemma lem5389125 (n : nat) (m : nat) (h1 : term590) (h2 : term582 n m) (h3 : term642) : term882 m n.
Proof. exact (conj (@lem5388790 h3) (@lem5389012 n m h1 h2)). Qed.
Lemma lem5389127 (x : nat) (y : nat) (z : nat) : term881 x y z.
Proof. exact (EQ_MP (@lem5389123 x y z) (@lem5389102 y x z)). Qed.
Lemma lem5389128 (m : nat) (n : nat) : term883 m n.
Proof. exact (@lem5389127 (@CARD nat (@EMPTY nat)) (NUMERAL 0) (term686 m n)). Qed.
Lemma lem5389131 (n : nat) (m : nat) (h1 : term590) (h2 : term582 n m) (h3 : term642) : (NUMERAL 0) = (term686 m n).
Proof. exact (@lem5389128 m n (@lem5389125 n m h1 h2 h3)). Qed.
Lemma lem5389132 (n : nat) (m : nat) (h1 : term590) (h2 : term582 n m) (h3 : term642) : term884 m n.
Proof. exact (fun h0 : term885 m n => @lem5389131 n m h1 h2 h3). Qed.
Lemma lem5389134 (p : Prop) : (term816 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5389135 (m : nat) (n : nat) : (term884 m n) = ((NUMERAL 0) = (term686 m n)).
Proof. exact (@lem5389134 ((NUMERAL 0) = (term686 m n))). Qed.
Lemma lem5389136 (n : nat) (m : nat) (h1 : term590) (h2 : term582 n m) (h3 : term642) : (NUMERAL 0) = (term686 m n).
Proof. exact (EQ_MP (@lem5389135 m n) (@lem5389132 n m h1 h2 h3)). Qed.
Lemma lem5389138 (n : nat) (m : nat) (h1 : term582 n m) : Peano.lt n m.
Proof. exact (proj1 (@lem5388037 n m h1)). Qed.
Lemma lem5389139 (n : nat) (m : nat) (h1 : term582 n m) : term817 n m.
Proof. exact (fun h0 : term65 n m => @lem5389138 n m h1). Qed.
Lemma lem5389141 (p : Prop) : (term816 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5389142 (n : nat) (m : nat) : (term817 n m) = (Peano.lt n m).
Proof. exact (@lem5389141 (Peano.lt n m)). Qed.
Lemma lem5389143 (n : nat) (m : nat) (h1 : term582 n m) : Peano.lt n m.
Proof. exact (EQ_MP (@lem5389142 n m) (@lem5389139 n m h1)). Qed.
Lemma lem5389149 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5389150 (_69803 : nat) (_69804 : nat) : (term15 _69803 _69804) = (term886 _69803 _69804).
Proof. exact (@lem5389149 ((term16 _69803 _69804) = (NUMERAL 0)) (term65 _69803 _69804)). Qed.
Lemma lem5389158 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5389159 (_69803 : nat) (_69804 : nat) : (term29 _69803 _69804) = (term887 _69803 _69804).
Proof. exact (MK_COMB (@lem5389158) (@lem5389150 _69803 _69804)). Qed.
Lemma lem5389167 (_69803 : nat) (_69804 : nat) : (term886 _69803 _69804) = (term886 _69803 _69804).
Proof. exact (eq_refl (term886 _69803 _69804)). Qed.
Lemma lem5389168 (_69803 : nat) (_69804 : nat) : ((term15 _69803 _69804) = (term886 _69803 _69804)) = ((term886 _69803 _69804) = (term886 _69803 _69804)).
Proof. exact (MK_COMB (@lem5389159 _69803 _69804) (@lem5389167 _69803 _69804)). Qed.
Lemma lem5389170 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5389171 (x : Prop) : (x = x) = True.
Proof. exact (@lem5389170 Prop x). Qed.
Lemma lem5389172 (_69803 : nat) (_69804 : nat) : ((term886 _69803 _69804) = (term886 _69803 _69804)) = True.
Proof. exact (@lem5389171 (term886 _69803 _69804)). Qed.
Lemma lem5389173 (_69803 : nat) (_69804 : nat) : ((term15 _69803 _69804) = (term886 _69803 _69804)) = True.
Proof. exact (TRANS (@lem5389168 _69803 _69804) (@lem5389172 _69803 _69804)). Qed.
Lemma lem5389174 (_69803 : nat) (_69804 : nat) : True = ((term15 _69803 _69804) = (term886 _69803 _69804)).
Proof. exact (SYM (@lem5389173 _69803 _69804)). Qed.
Lemma lem5389175 (_69803 : nat) (_69804 : nat) : (term15 _69803 _69804) = (term886 _69803 _69804).
Proof. exact (EQ_MP (@lem5389174 _69803 _69804) (@lem0)). Qed.
Lemma lem5389176 (_69803 : nat) (_69804 : nat) (h1 : term528) : term886 _69803 _69804.
Proof. exact (EQ_MP (@lem5389175 _69803 _69804) (@lem5388519 _69803 _69804 h1)). Qed.
Lemma lem5389178 (b : Prop) (a : Prop) : (a \/ b) = (term818 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5389179 (_69803 : nat) (_69804 : nat) : (term886 _69803 _69804) = (term888 _69803 _69804).
Proof. exact (@lem5389178 (term65 _69803 _69804) ((term16 _69803 _69804) = (NUMERAL 0))). Qed.
Lemma lem5389181 (a : Prop) : (term192 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5389182 (_69803 : nat) (_69804 : nat) : (term820 _69803 _69804) = (Peano.lt _69803 _69804).
Proof. exact (@lem5389181 (Peano.lt _69803 _69804)). Qed.
Lemma lem5389183 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5389184 (_69803 : nat) (_69804 : nat) : (term821 _69803 _69804) = (term822 _69803 _69804).
Proof. exact (MK_COMB (@lem5389183) (@lem5389182 _69803 _69804)). Qed.
Lemma lem5389185 (_69803 : nat) (_69804 : nat) : ((term16 _69803 _69804) = (NUMERAL 0)) = ((term16 _69803 _69804) = (NUMERAL 0)).
Proof. exact (eq_refl ((term16 _69803 _69804) = (NUMERAL 0))). Qed.
Lemma lem5389186 (_69803 : nat) (_69804 : nat) : (term888 _69803 _69804) = (term14 _69803 _69804).
Proof. exact (MK_COMB (@lem5389184 _69803 _69804) (@lem5389185 _69803 _69804)). Qed.
Lemma lem5389187 (_69803 : nat) (_69804 : nat) : (term886 _69803 _69804) = (term14 _69803 _69804).
Proof. exact (TRANS (@lem5389179 _69803 _69804) (@lem5389186 _69803 _69804)). Qed.
Lemma lem5389190 (_69803 : nat) (_69804 : nat) (h1 : term528) : term14 _69803 _69804.
Proof. exact (EQ_MP (@lem5389187 _69803 _69804) (@lem5389176 _69803 _69804 h1)). Qed.
Lemma lem5389191 (n : nat) (m : nat) (h1 : term528) : term14 n m.
Proof. exact (@lem5389190 n m h1). Qed.
Lemma lem5389194 (n : nat) (m : nat) (h1 : term528) (h2 : term582 n m) : (term16 n m) = (NUMERAL 0).
Proof. exact (@lem5389191 n m h1 (@lem5389143 n m h2)). Qed.
Lemma lem5389195 (n : nat) (m : nat) (h1 : term528) (h2 : term582 n m) : term889 n m.
Proof. exact (fun h0 : term890 n m => @lem5389194 n m h1 h2). Qed.
Lemma lem5389197 (p : Prop) : (term816 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5389198 (n : nat) (m : nat) : (term889 n m) = ((term16 n m) = (NUMERAL 0)).
Proof. exact (@lem5389197 ((term16 n m) = (NUMERAL 0))). Qed.
Lemma lem5389199 (n : nat) (m : nat) (h1 : term528) (h2 : term582 n m) : (term16 n m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem5389198 n m) (@lem5389195 n m h1 h2)). Qed.
Lemma lem5389201 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem5389202 (n : nat) (m : nat) : (term16 n m) = (term16 n m).
Proof. exact (@lem5389201 (term16 n m)). Qed.
Lemma lem5389203 (n : nat) (m : nat) : term891 n m.
Proof. exact (fun h0 : term892 n m => @lem5389202 n m). Qed.
Lemma lem5389205 (p : Prop) : (term816 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5389206 (n : nat) (m : nat) : (term891 n m) = ((term16 n m) = (term16 n m)).
Proof. exact (@lem5389205 ((term16 n m) = (term16 n m))). Qed.
Lemma lem5389207 (n : nat) (m : nat) : (term16 n m) = (term16 n m).
Proof. exact (EQ_MP (@lem5389206 n m) (@lem5389203 n m)). Qed.
Lemma lem5389208 (n : nat) (m : nat) (h1 : term528) (h2 : term582 n m) : term893 n m.
Proof. exact (conj (@lem5389199 n m h1 h2) (@lem5389207 n m)). Qed.
Lemma lem5389210 (x : nat) (y : nat) (z : nat) : term881 x y z.
Proof. exact (EQ_MP (@lem5389123 x y z) (@lem5389102 y x z)). Qed.
Lemma lem5389211 (n : nat) (m : nat) : term894 n m.
Proof. exact (@lem5389210 (term16 n m) (NUMERAL 0) (term16 n m)). Qed.
Lemma lem5389214 (n : nat) (m : nat) (h1 : term528) (h2 : term582 n m) : (NUMERAL 0) = (term16 n m).
Proof. exact (@lem5389211 n m (@lem5389208 n m h1 h2)). Qed.
Lemma lem5389215 (n : nat) (m : nat) (h1 : term528) (h2 : term582 n m) : term895 n m.
Proof. exact (fun h0 : term896 n m => @lem5389214 n m h1 h2). Qed.
Lemma lem5389217 (p : Prop) : (term816 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5389218 (n : nat) (m : nat) : (term895 n m) = ((NUMERAL 0) = (term16 n m)).
Proof. exact (@lem5389217 ((NUMERAL 0) = (term16 n m))). Qed.
Lemma lem5389219 (n : nat) (m : nat) (h1 : term528) (h2 : term582 n m) : (NUMERAL 0) = (term16 n m).
Proof. exact (EQ_MP (@lem5389218 n m) (@lem5389215 n m h1 h2)). Qed.
Lemma lem5389220 (n : nat) (m : nat) (h1 : term590) (h2 : term528) (h3 : term582 n m) (h4 : term642) : term897 n m.
Proof. exact (conj (@lem5389136 n m h1 h3 h4) (@lem5389219 n m h2 h3)). Qed.
Lemma lem5389222 (x : nat) (y : nat) (z : nat) : term881 x y z.
Proof. exact (EQ_MP (@lem5389123 x y z) (@lem5389102 y x z)). Qed.
Lemma lem5389223 (n : nat) (m : nat) : term898 n m.
Proof. exact (@lem5389222 (NUMERAL 0) (term686 m n) (term16 n m)). Qed.
Lemma lem5389226 (n : nat) (m : nat) (h1 : term590) (h2 : term528) (h3 : term582 n m) (h4 : term642) : (term686 m n) = (term16 n m).
Proof. exact (@lem5389223 n m (@lem5389220 n m h1 h2 h3 h4)). Qed.
Lemma lem5389227 (n : nat) (m : nat) (h1 : term590) (h2 : term528) (h3 : term582 n m) (h4 : term642) : term899 n m.
Proof. exact (fun h0 : term808 n m => @lem5389226 n m h1 h2 h3 h4). Qed.
Lemma lem5389229 (p : Prop) : (term816 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5389230 (n : nat) (m : nat) : (term899 n m) = ((term686 m n) = (term16 n m)).
Proof. exact (@lem5389229 ((term686 m n) = (term16 n m))). Qed.
Lemma lem5389231 (n : nat) (m : nat) (h1 : term590) (h2 : term528) (h3 : term582 n m) (h4 : term642) : (term686 m n) = (term16 n m).
Proof. exact (EQ_MP (@lem5389230 n m) (@lem5389227 n m h1 h2 h3 h4)). Qed.
Lemma lem5389234 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5389236 (n : nat) (m : nat) : (term808 n m) = (term900 n m).
Proof. exact (@lem5389234 ((term686 m n) = (term16 n m))). Qed.
Lemma lem5389239 (n : nat) (m : nat) (h1 : term582 n m) : term900 n m.
Proof. exact (EQ_MP (@lem5389236 n m) (@lem5388579 n m h1)). Qed.
Lemma lem5389242 (n : nat) (m : nat) (h1 : term590) (h2 : term528) (h3 : term582 n m) (h4 : term642) : False.
Proof. exact (@lem5389239 n m h3 (@lem5389231 n m h1 h2 h3 h4)). Qed.
Lemma lem5389243 (n : nat) (m : nat) (h1 : term590) (h2 : term528) (h3 : term582 n m) (h4 : term642) : term901.
Proof. exact (fun h0 : ~ False => @lem5389242 n m h1 h2 h3 h4). Qed.
Lemma lem5389245 (p : Prop) : (term816 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5389246 : term901 = False.
Proof. exact (@lem5389245 False). Qed.
Lemma lem5389247 (n : nat) (m : nat) (h1 : term590) (h2 : term528) (h3 : term582 n m) (h4 : term642) : False.
Proof. exact (EQ_MP (@lem5389246) (@lem5389243 n m h1 h2 h3 h4)). Qed.
Lemma lem5389248 (n : nat) (m : nat) (h1 : term528) (h2 : term582 n m) (h3 : term642) : term588.
Proof. exact (fun h0 : term590 => @lem5389247 n m h0 h1 h2 h3). Qed.
Lemma lem5389249 : term588 = term589.
Proof. exact (@lem69 term590). Qed.
Lemma lem5389250 (n : nat) (m : nat) (h1 : term528) (h2 : term582 n m) (h3 : term642) : term589.
Proof. exact (EQ_MP (@lem5389249) (@lem5389248 n m h1 h2 h3)). Qed.
Lemma lem5389251 (n : nat) (m : nat) (h1 : term528) (h2 : term582 n m) : term644.
Proof. exact (fun h0 : term642 => @lem5389250 n m h1 h2 h0). Qed.
Lemma lem5389252 {A : Type'} (n : nat) (m : nat) (h1 : term528) (h2 : term582 n m) : term676 A.
Proof. exact (fun h0 : term674 A => @lem5389251 n m h1 h2). Qed.
Lemma lem5389253 {A : Type'} (n : nat) (m : nat) (h1 : term582 n m) : term679 A.
Proof. exact (fun h0 : term528 => @lem5389252 A n m h0 h1). Qed.
Lemma lem5389254 {A : Type'} (n : nat) (m : nat) : term680 A n m.
Proof. exact (fun h0 : term582 n m => @lem5389253 A n m h0). Qed.
Lemma lem5389259 {A : Type'} (m : nat) : term682 A m.
Proof. exact (fun n : nat => @lem5389254 A n m). Qed.
Lemma lem5389264 {A : Type'} : term684 A.
Proof. exact (fun m : nat => @lem5389259 A m). Qed.
Lemma lem5389265 {A : Type'} : term608 A.
Proof. exact (EQ_MP (@lem5387023 A) (@lem5389264 A)). Qed.
Lemma lem5389266 {A : Type'} (m : nat) : term902 A m.
Proof. exact (@lem5389265 A m). Qed.
Lemma lem5389267 {A : Type'} (m : nat) : (term902 A m) = (term604 A m).
Proof. exact (eq_refl (term902 A m)). Qed.
Lemma lem5389268 {A : Type'} (m : nat) : term604 A m.
Proof. exact (EQ_MP (@lem5389267 A m) (@lem5389266 A m)). Qed.
Lemma lem5389269 {A : Type'} (m : nat) (n : nat) : term903 A m n.
Proof. exact (@lem5389268 A m n). Qed.
Lemma lem5389270 {A : Type'} (n : nat) (m : nat) : (term903 A m n) = (term584 A n m).
Proof. exact (eq_refl (term903 A m n)). Qed.
Lemma lem5389271 {A : Type'} (n : nat) (m : nat) : term584 A n m.
Proof. exact (EQ_MP (@lem5389270 A n m) (@lem5389269 A m n)). Qed.
Lemma lem5389273 {A : Type'} (n : nat) (m : nat) : term584 A n m.
Proof. exact (@lem5386575 A n m (@lem5389271 A n m)). Qed.
Lemma lem5389274 {A : Type'} (n : nat) (m : nat) (h1 : term582 n m) : term598 A.
Proof. exact (@lem5389273 A n m (@lem5386557 n m h1)). Qed.
Lemma lem5389275 {A : Type'} (n : nat) (m : nat) (h1 : term582 n m) : term595 A.
Proof. exact (@lem5389274 A n m h1 (@lem5385633)). Qed.
Lemma lem5389276 (n : nat) (m : nat) (h1 : term582 n m) : term592.
Proof. exact (@lem5389275 Prop n m h1 (@lem3840691 Prop)). Qed.
Lemma lem5389277 (n : nat) (m : nat) (h1 : term582 n m) : term588.
Proof. exact (@lem5389276 n m h1 (@lem5386558)). Qed.
Lemma lem5389278 (n : nat) (m : nat) (h1 : term582 n m) : False.
Proof. exact (@lem5389277 n m h1 (@lem5376447)). Qed.
Lemma lem5389279 (n : nat) (m : nat) (h1 : term582 n m) : (term582 n m) = False.
Proof. exact (prop_ext (fun h2 : term582 n m => @lem5389278 n m h1) (fun h2 : False => @lem5386557 n m h1)). Qed.
Lemma lem5389280 (n : nat) (m : nat) (h1 : term582 n m) : False.
Proof. exact (EQ_MP (@lem5389279 n m h1) (@lem5386557 n m h1)). Qed.
Lemma lem5389281 (n : nat) (m : nat) : term581 n m.
Proof. exact (fun h0 : term582 n m => @lem5389280 n m h0). Qed.
Lemma lem5389282 (n : nat) (m : nat) : term580 n m.
Proof. exact (EQ_MP (@lem5386556 n m) (@lem5389281 n m)). Qed.
Lemma lem5389286 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term904 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5389287 (p : Prop) (q : Prop) (p' : Prop) : term905 p q p'.
Proof. exact (fun q' : Prop => @lem5389286 p q p' q'). Qed.
Lemma lem5389288 (p : Prop) (q : Prop) : term906 p q.
Proof. exact (fun p' : Prop => @lem5389287 p q p'). Qed.
Lemma lem5389289 (n : nat) (m : nat) : term907 n m.
Proof. exact (@lem5389288 (Peano.le m n) ((term686 m n) = (term16 n m))). Qed.
Lemma lem5389290 (n : nat) (m : nat) (p' : Prop) : term908 n m p'.
Proof. exact (@lem5389289 n m p'). Qed.
Lemma lem5389291 (n : nat) (m : nat) (p' : Prop) : (term908 n m p') = (term909 n m p').
Proof. exact (eq_refl (term908 n m p')). Qed.
Lemma lem5389292 (n : nat) (m : nat) (p' : Prop) : term909 n m p'.
Proof. exact (EQ_MP (@lem5389291 n m p') (@lem5389290 n m p')). Qed.
Lemma lem5389293 (n : nat) (m : nat) (p' : Prop) (q' : Prop) : term910 n m p' q'.
Proof. exact (@lem5389292 n m p' q'). Qed.
Lemma lem5389294 (n : nat) (m : nat) (p' : Prop) (q' : Prop) : (term910 n m p' q') = (term911 n m p' q').
Proof. exact (eq_refl (term910 n m p' q')). Qed.
Lemma lem5389295 (n : nat) (m : nat) (p' : Prop) (q' : Prop) : term911 n m p' q'.
Proof. exact (EQ_MP (@lem5389294 n m p' q') (@lem5389293 n m p' q')). Qed.
Lemma lem5389297 (n : nat) (m : nat) : (Peano.le m n) = (term13 n m).
Proof. exact (EQ_MP (@lem5382477 n m) (@lem5382476 m n)). Qed.
Lemma lem5389304 (n : nat) (m : nat) (q' : Prop) : term912 n m q'.
Proof. exact (@lem5389295 n m (term13 n m) q'). Qed.
Lemma lem5389305 (n : nat) (m : nat) (q' : Prop) : term913 n m q'.
Proof. exact (@lem5389304 n m q' (@lem5389297 n m)). Qed.
Lemma lem5389311 (n : nat) (m : nat) : ((term686 m n) = (term16 n m)) = ((term686 m n) = (term16 n m)).
Proof. exact (eq_refl ((term686 m n) = (term16 n m))). Qed.
Lemma lem5389312 (n : nat) (m : nat) : term914 n m.
Proof. exact (fun h0 : term13 n m => @lem5389311 n m). Qed.
Lemma lem5389313 (n : nat) (m : nat) : term915 n m.
Proof. exact (@lem5389305 n m ((term686 m n) = (term16 n m))). Qed.
Lemma lem5389314 (n : nat) (m : nat) : (term916 n m) = (term917 n m).
Proof. exact (@lem5389313 n m (@lem5389312 n m)). Qed.
Lemma lem5389316 {A : Type'} (P : A -> Prop) (Q : Prop) : (term8 A P Q) = (term9 A P Q).
Proof. exact (EQ_MP (@lem5382471 A P Q) (@lem5382470 A P Q)). Qed.
Lemma lem5389317 (P : nat -> Prop) (Q : Prop) : (term918 P Q) = (term919 P Q).
Proof. exact (@lem5389316 nat P Q). Qed.
Lemma lem5389318 (n : nat) (m : nat) : (term920 n m) = (term921 n m).
Proof. exact (@lem5389317 (term922 n m) ((term686 m n) = (term16 n m))). Qed.
Lemma lem5389319 (n : nat) (m : nat) (d : nat) : (term923 n m d) = (n = (Nat.add m d)).
Proof. exact (eq_refl (term923 n m d)). Qed.
Lemma lem5389320 (n : nat) (m : nat) : (term924 n m) = (term922 n m).
Proof. exact (fun_ext (fun d : nat => @lem5389319 n m d)). Qed.
Lemma lem5389321 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5389322 (n : nat) (m : nat) : (term925 n m) = (term13 n m).
Proof. exact (MK_COMB (@lem5389321) (@lem5389320 n m)). Qed.
Lemma lem5389323 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5389324 (n : nat) (m : nat) : (term926 n m) = (term927 n m).
Proof. exact (MK_COMB (@lem5389323) (@lem5389322 n m)). Qed.
Lemma lem5389325 (n : nat) (m : nat) : ((term686 m n) = (term16 n m)) = ((term686 m n) = (term16 n m)).
Proof. exact (eq_refl ((term686 m n) = (term16 n m))). Qed.
Lemma lem5389326 (n : nat) (m : nat) : (term920 n m) = (term917 n m).
Proof. exact (MK_COMB (@lem5389324 n m) (@lem5389325 n m)). Qed.
Lemma lem5389327 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5389328 (n : nat) (m : nat) : (term928 n m) = (term929 n m).
Proof. exact (MK_COMB (@lem5389327) (@lem5389326 n m)). Qed.
Lemma lem5389329 (n : nat) (m : nat) (d : nat) : (term923 n m d) = (n = (Nat.add m d)).
Proof. exact (eq_refl (term923 n m d)). Qed.
Lemma lem5389330 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5389331 (n : nat) (m : nat) (d : nat) : (term930 n m d) = (term931 n m d).
Proof. exact (MK_COMB (@lem5389330) (@lem5389329 n m d)). Qed.
Lemma lem5389332 (n : nat) (m : nat) : ((term686 m n) = (term16 n m)) = ((term686 m n) = (term16 n m)).
Proof. exact (eq_refl ((term686 m n) = (term16 n m))). Qed.
Lemma lem5389333 (d : nat) (n : nat) (m : nat) : (term932 d n m) = (term933 d n m).
Proof. exact (MK_COMB (@lem5389331 n m d) (@lem5389332 n m)). Qed.
Lemma lem5389334 (n : nat) (m : nat) : (term934 n m) = (term935 n m).
Proof. exact (fun_ext (fun d : nat => @lem5389333 d n m)). Qed.
Lemma lem5389335 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5389336 (n : nat) (m : nat) : (term921 n m) = (term936 n m).
Proof. exact (MK_COMB (@lem5389335) (@lem5389334 n m)). Qed.
Lemma lem5389337 (n : nat) (m : nat) : ((term920 n m) = (term921 n m)) = ((term917 n m) = (term936 n m)).
Proof. exact (MK_COMB (@lem5389328 n m) (@lem5389336 n m)). Qed.
Lemma lem5389338 (n : nat) (m : nat) : (term917 n m) = (term936 n m).
Proof. exact (EQ_MP (@lem5389337 n m) (@lem5389318 n m)). Qed.
Lemma lem5389348 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term904 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5389349 (p : Prop) (q : Prop) (p' : Prop) : term905 p q p'.
Proof. exact (fun q' : Prop => @lem5389348 p q p' q'). Qed.
Lemma lem5389350 (p : Prop) (q : Prop) : term906 p q.
Proof. exact (fun p' : Prop => @lem5389349 p q p'). Qed.
Lemma lem5389351 (d : nat) (n : nat) (m : nat) : term937 d n m.
Proof. exact (@lem5389350 (n = (Nat.add m d)) ((term686 m n) = (term16 n m))). Qed.
Lemma lem5389352 (d : nat) (n : nat) (m : nat) (p' : Prop) : term938 d n m p'.
Proof. exact (@lem5389351 d n m p'). Qed.
Lemma lem5389353 (d : nat) (n : nat) (m : nat) (p' : Prop) : (term938 d n m p') = (term939 d n m p').
Proof. exact (eq_refl (term938 d n m p')). Qed.
Lemma lem5389354 (d : nat) (n : nat) (m : nat) (p' : Prop) : term939 d n m p'.
Proof. exact (EQ_MP (@lem5389353 d n m p') (@lem5389352 d n m p')). Qed.
Lemma lem5389355 (d : nat) (n : nat) (m : nat) (p' : Prop) (q' : Prop) : term940 d n m p' q'.
Proof. exact (@lem5389354 d n m p' q'). Qed.
Lemma lem5389356 (d : nat) (n : nat) (m : nat) (p' : Prop) (q' : Prop) : (term940 d n m p' q') = (term941 d n m p' q').
Proof. exact (eq_refl (term940 d n m p' q')). Qed.
Lemma lem5389357 (d : nat) (n : nat) (m : nat) (p' : Prop) (q' : Prop) : term941 d n m p' q'.
Proof. exact (EQ_MP (@lem5389356 d n m p' q') (@lem5389355 d n m p' q')). Qed.
Lemma lem5389360 (n : nat) (m : nat) (d : nat) : (n = (Nat.add m d)) = (n = (Nat.add m d)).
Proof. exact (eq_refl (n = (Nat.add m d))). Qed.
Lemma lem5389361 (n : nat) (m : nat) (d : nat) (q' : Prop) : term942 n m d q'.
Proof. exact (@lem5389357 d n m (n = (Nat.add m d)) q'). Qed.
Lemma lem5389362 (n : nat) (m : nat) (d : nat) (q' : Prop) : term943 n m d q'.
Proof. exact (@lem5389361 n m d q' (@lem5389360 n m d)). Qed.
Lemma lem5389367 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : n = (Nat.add m d).
Proof. exact (h1). Qed.
Lemma lem5389368 (m : nat) : (dotdot m) = (dotdot m).
Proof. exact (eq_refl (dotdot m)). Qed.
Lemma lem5389369 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (dotdot m n) = (term944 m d).
Proof. exact (MK_COMB (@lem5389368 m) (@lem5389367 n m d h1)). Qed.
Lemma lem5389370 : (@CARD nat) = (@CARD nat).
Proof. exact (eq_refl (@CARD nat)). Qed.
Lemma lem5389371 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term686 m n) = (term3 m d).
Proof. exact (MK_COMB (@lem5389370) (@lem5389369 n m d h1)). Qed.
Lemma lem5389373 (m : nat) (d : nat) : (term3 m d) = (term4 d).
Proof. exact (EQ_MP (@lem5382465 m d) (@lem5382464 m d)). Qed.
Lemma lem5389374 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term686 m n) = (term4 d).
Proof. exact (TRANS (@lem5389371 n m d h1) (@lem5389373 m d)). Qed.
Lemma lem5389375 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem5389376 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term945 m n) = (term31 d).
Proof. exact (MK_COMB (@lem5389375) (@lem5389374 n m d h1)). Qed.
Lemma lem5389378 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : n = (Nat.add m d).
Proof. exact (h1). Qed.
Lemma lem5389379 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem5389380 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (Nat.add n) = (term946 m d).
Proof. exact (MK_COMB (@lem5389379) (@lem5389378 n m d h1)). Qed.
Lemma lem5389381 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem5389382 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term4 n) = (term947 m d).
Proof. exact (MK_COMB (@lem5389380 n m d h1) (@lem5389381)). Qed.
Lemma lem5389383 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem5389384 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term948 n) = (term949 m d).
Proof. exact (MK_COMB (@lem5389383) (@lem5389382 n m d h1)). Qed.
Lemma lem5389385 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem5389386 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term16 n m) = (term950 d m).
Proof. exact (MK_COMB (@lem5389384 n m d h1) (@lem5389385 m)). Qed.
Lemma lem5389387 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : ((term686 m n) = (term16 n m)) = ((term4 d) = (term950 d m)).
Proof. exact (MK_COMB (@lem5389376 n m d h1) (@lem5389386 n m d h1)). Qed.
Lemma lem5389390 (n : nat) (d : nat) (m : nat) : term951 n d m.
Proof. exact (fun h0 : n = (Nat.add m d) => @lem5389387 n m d h0). Qed.
Lemma lem5389391 (n : nat) (d : nat) (m : nat) : term952 n d m.
Proof. exact (@lem5389362 n m d ((term4 d) = (term950 d m))). Qed.
Lemma lem5389392 (n : nat) (d : nat) (m : nat) : (term933 d n m) = (term953 n d m).
Proof. exact (@lem5389391 n d m (@lem5389390 n d m)). Qed.
Lemma lem5389424 (n : nat) (m : nat) : (term935 n m) = (term954 n m).
Proof. exact (fun_ext (fun d : nat => @lem5389392 n d m)). Qed.
Lemma lem5389456 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5389457 (n : nat) (m : nat) : (term936 n m) = (term955 n m).
Proof. exact (MK_COMB (@lem5389456) (@lem5389424 n m)). Qed.
Lemma lem5389493 (n : nat) (m : nat) : (term917 n m) = (term955 n m).
Proof. exact (TRANS (@lem5389338 n m) (@lem5389457 n m)). Qed.
Lemma lem5389494 (n : nat) (m : nat) : (term916 n m) = (term955 n m).
Proof. exact (TRANS (@lem5389314 n m) (@lem5389493 n m)). Qed.
Lemma lem5389495 (n : nat) (m : nat) : (term955 n m) = (term916 n m).
Proof. exact (SYM (@lem5389494 n m)). Qed.
Lemma lem5389504 (m : nat) (d : nat) : (term956 d m) = (term957 m d).
Proof. exact (@lem1032781 (term947 m d) m (term958 d)). Qed.
Lemma lem5389505 (d : nat) (d' : nat) : (term959 d d') = ((term4 d) = d').
Proof. exact (eq_refl (term959 d d')). Qed.
Lemma lem5389506 (d : nat) (m : nat) (d' : nat) : (term960 d m d') = (term960 d m d').
Proof. exact (eq_refl (term960 d m d')). Qed.
Lemma lem5389507 (m : nat) (d : nat) (d' : nat) : (term961 m d d') = (term962 m d d').
Proof. exact (MK_COMB (@lem5389506 d m d') (@lem5389505 d d')). Qed.
Lemma lem5389508 (m : nat) (d : nat) : (term963 m d) = (term964 m d).
Proof. exact (fun_ext (fun d' : nat => @lem5389507 m d d')). Qed.
Lemma lem5389509 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5389510 (m : nat) (d : nat) : (term957 m d) = (term965 m d).
Proof. exact (MK_COMB (@lem5389509) (@lem5389508 m d)). Qed.
Lemma lem5389511 (d : nat) (m : nat) : (term956 d m) = ((term4 d) = (term950 d m)).
Proof. exact (eq_refl (term956 d m)). Qed.
Lemma lem5389512 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5389513 (d : nat) (m : nat) : (term966 d m) = (term967 d m).
Proof. exact (MK_COMB (@lem5389512) (@lem5389511 d m)). Qed.
Lemma lem5389514 (m : nat) (d : nat) : ((term956 d m) = (term957 m d)) = (((term4 d) = (term950 d m)) = (term965 m d)).
Proof. exact (MK_COMB (@lem5389513 d m) (@lem5389510 m d)). Qed.
Lemma lem5389515 (m : nat) (d : nat) : ((term4 d) = (term950 d m)) = (term965 m d).
Proof. exact (EQ_MP (@lem5389514 m d) (@lem5389504 m d)). Qed.
Lemma lem5389516 (m : nat) (d : nat) (d' : nat) : (term962 m d d') = (term962 m d d').
Proof. exact (eq_refl (term962 m d d')). Qed.
Lemma lem5389517 (m : nat) (d : nat) : (term964 m d) = (term964 m d).
Proof. exact (fun_ext (fun d' : nat => @lem5389516 m d d')). Qed.
Lemma lem5389518 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5389519 (m : nat) (d : nat) : (term965 m d) = (term965 m d).
Proof. exact (MK_COMB (@lem5389518) (@lem5389517 m d)). Qed.
Lemma lem5389520 (d : nat) (m : nat) : (term967 d m) = (term967 d m).
Proof. exact (eq_refl (term967 d m)). Qed.
Lemma lem5389521 (m : nat) (d : nat) : (((term4 d) = (term950 d m)) = (term965 m d)) = (((term4 d) = (term950 d m)) = (term965 m d)).
Proof. exact (MK_COMB (@lem5389520 d m) (@lem5389519 m d)). Qed.
Lemma lem5389545 (m : nat) (d : nat) : ((term4 d) = (term950 d m)) = (term965 m d).
Proof. exact (EQ_MP (@lem5389521 m d) (@lem5389515 m d)). Qed.
Lemma lem5389556 (d : nat) (d' : nat) : ((term4 d) = d') = ((term4 d) = d').
Proof. exact (eq_refl ((term4 d) = d')). Qed.
Lemma lem5389563 (d' : nat) : (term60 d') = (term60 d').
Proof. exact (eq_refl (term60 d')). Qed.
Lemma lem5389564 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem5389565 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem5389572 (d : nat) (m : nat) : (Nat.add m d) = (Nat.add d m).
Proof. exact (@lem1032098 d m). Qed.
Lemma lem5389573 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem5389574 (d : nat) (m : nat) : (term946 m d) = (term946 d m).
Proof. exact (MK_COMB (@lem5389573) (@lem5389572 d m)). Qed.
Lemma lem5389575 (d : nat) (m : nat) : (term947 m d) = (term947 d m).
Proof. exact (MK_COMB (@lem5389574 d m) (@lem5389565)). Qed.
Lemma lem5389580 (d : nat) (m : nat) : (term947 d m) = (term968 d m).
Proof. exact (@lem1032092 d m term44). Qed.
Lemma lem5389581 (d : nat) (m : nat) : (term947 m d) = (term968 d m).
Proof. exact (TRANS (@lem5389575 d m) (@lem5389580 d m)). Qed.
Lemma lem5389582 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem5389583 (d : nat) (m : nat) : (term969 m d) = (term970 d m).
Proof. exact (MK_COMB (@lem5389582) (@lem5389581 d m)). Qed.
Lemma lem5389584 (d : nat) (m : nat) : (term971 d m) = (term972 d m).
Proof. exact (MK_COMB (@lem5389583 d m) (@lem5389564 m)). Qed.
Lemma lem5389585 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5389586 (d : nat) (m : nat) : (term973 d m) = (term974 d m).
Proof. exact (MK_COMB (@lem5389585) (@lem5389584 d m)). Qed.
Lemma lem5389587 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5389588 (d : nat) (m : nat) : (term975 d m) = (term976 d m).
Proof. exact (MK_COMB (@lem5389587) (@lem5389586 d m)). Qed.
Lemma lem5389589 (d : nat) (m : nat) (d' : nat) : (term977 d m d') = (term978 d m d').
Proof. exact (MK_COMB (@lem5389588 d m) (@lem5389563 d')). Qed.
Lemma lem5389596 (d' : nat) (m : nat) : (Nat.add m d') = (Nat.add d' m).
Proof. exact (@lem1032098 d' m). Qed.
Lemma lem5389597 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem5389604 (d : nat) (m : nat) : (Nat.add m d) = (Nat.add d m).
Proof. exact (@lem1032098 d m). Qed.
Lemma lem5389605 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem5389606 (d : nat) (m : nat) : (term946 m d) = (term946 d m).
Proof. exact (MK_COMB (@lem5389605) (@lem5389604 d m)). Qed.
Lemma lem5389607 (d : nat) (m : nat) : (term947 m d) = (term947 d m).
Proof. exact (MK_COMB (@lem5389606 d m) (@lem5389597)). Qed.
Lemma lem5389612 (d : nat) (m : nat) : (term947 d m) = (term968 d m).
Proof. exact (@lem1032092 d m term44). Qed.
Lemma lem5389613 (d : nat) (m : nat) : (term947 m d) = (term968 d m).
Proof. exact (TRANS (@lem5389607 d m) (@lem5389612 d m)). Qed.
Lemma lem5389614 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem5389615 (d : nat) (m : nat) : (term979 m d) = (term980 d m).
Proof. exact (MK_COMB (@lem5389614) (@lem5389613 d m)). Qed.
Lemma lem5389616 (d : nat) (d' : nat) (m : nat) : ((term947 m d) = (Nat.add m d')) = ((term968 d m) = (Nat.add d' m)).
Proof. exact (MK_COMB (@lem5389615 d m) (@lem5389596 d' m)). Qed.
Lemma lem5389617 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5389618 (d : nat) (d' : nat) (m : nat) : (term981 d m d') = (term982 d d' m).
Proof. exact (MK_COMB (@lem5389617) (@lem5389616 d d' m)). Qed.
Lemma lem5389619 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5389620 (d : nat) (d' : nat) (m : nat) : (term983 d m d') = (term984 d d' m).
Proof. exact (MK_COMB (@lem5389619) (@lem5389618 d d' m)). Qed.
Lemma lem5389621 (d : nat) (m : nat) (d' : nat) : (term985 d m d') = (term986 d m d').
Proof. exact (MK_COMB (@lem5389620 d d' m) (@lem5389589 d m d')). Qed.
Lemma lem5389622 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5389623 (d : nat) (m : nat) (d' : nat) : (term960 d m d') = (term987 d m d').
Proof. exact (MK_COMB (@lem5389622) (@lem5389621 d m d')). Qed.
Lemma lem5389624 (m : nat) (d : nat) (d' : nat) : (term962 m d d') = (term988 m d d').
Proof. exact (MK_COMB (@lem5389623 d m d') (@lem5389556 d d')). Qed.
Lemma lem5389625 (m : nat) (d : nat) : (term964 m d) = (term989 m d).
Proof. exact (fun_ext (fun d' : nat => @lem5389624 m d d')). Qed.
Lemma lem5389626 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5389627 (m : nat) (d : nat) : (term965 m d) = (term990 m d).
Proof. exact (MK_COMB (@lem5389626) (@lem5389625 m d)). Qed.
Lemma lem5389630 (m : nat) (d : nat) : ((term4 d) = (term950 d m)) = (term990 m d).
Proof. exact (TRANS (@lem5389545 m d) (@lem5389627 m d)). Qed.
Lemma lem5389632 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem5389633 (d : nat) (d' : nat) (m : nat) : ((term968 d m) = (Nat.add d' m)) = ((term991 d m) = (term41 d' m)).
Proof. exact (@lem5389632 (term968 d m) (Nat.add d' m)). Qed.
Lemma lem5389637 (m : nat) (n : nat) : (term41 m n) = (term42 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5389638 (d : nat) (m : nat) : (term991 d m) = (term992 d m).
Proof. exact (@lem5389637 d (term4 m)). Qed.
Lemma lem5389640 (m : nat) (n : nat) : (term41 m n) = (term42 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5389641 (m : nat) : (term40 m) = (term43 m).
Proof. exact (@lem5389640 m term44). Qed.
Lemma lem5389642 (d : nat) : (term993 d) = (term993 d).
Proof. exact (eq_refl (term993 d)). Qed.
Lemma lem5389643 (d : nat) (m : nat) : (term992 d m) = (term994 d m).
Proof. exact (MK_COMB (@lem5389642 d) (@lem5389641 m)). Qed.
Lemma lem5389644 (d : nat) (m : nat) : (term991 d m) = (term994 d m).
Proof. exact (TRANS (@lem5389638 d m) (@lem5389643 d m)). Qed.
Lemma lem5389645 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem5389646 (d : nat) (m : nat) : (term995 d m) = (term996 d m).
Proof. exact (MK_COMB (@lem5389645) (@lem5389644 d m)). Qed.
Lemma lem5389648 (m : nat) (n : nat) : (term41 m n) = (term42 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5389649 (d' : nat) (m : nat) : (term41 d' m) = (term42 d' m).
Proof. exact (@lem5389648 d' m). Qed.
Lemma lem5389650 (d : nat) (d' : nat) (m : nat) : ((term991 d m) = (term41 d' m)) = ((term994 d m) = (term42 d' m)).
Proof. exact (MK_COMB (@lem5389646 d m) (@lem5389649 d' m)). Qed.
Lemma lem5389651 (d : nat) (d' : nat) (m : nat) : ((term968 d m) = (Nat.add d' m)) = ((term994 d m) = (term42 d' m)).
Proof. exact (TRANS (@lem5389633 d d' m) (@lem5389650 d d' m)). Qed.
Lemma lem5389652 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5389653 (d : nat) (d' : nat) (m : nat) : (term982 d d' m) = (term997 d d' m).
Proof. exact (MK_COMB (@lem5389652) (@lem5389651 d d' m)). Qed.
Lemma lem5389654 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5389655 (d : nat) (d' : nat) (m : nat) : (term984 d d' m) = (term998 d d' m).
Proof. exact (MK_COMB (@lem5389654) (@lem5389653 d d' m)). Qed.
Lemma lem5389657 (m : nat) (n : nat) : (Peano.lt m n) = (term49 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem5389658 (d : nat) (m : nat) : (term972 d m) = (term999 d m).
Proof. exact (@lem5389657 (term968 d m) m). Qed.
Lemma lem5389660 (m : nat) (n : nat) : (term41 m n) = (term42 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5389661 (d : nat) (m : nat) : (term991 d m) = (term992 d m).
Proof. exact (@lem5389660 d (term4 m)). Qed.
Lemma lem5389663 (m : nat) (n : nat) : (term41 m n) = (term42 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5389664 (m : nat) : (term40 m) = (term43 m).
Proof. exact (@lem5389663 m term44). Qed.
Lemma lem5389665 (d : nat) : (term993 d) = (term993 d).
Proof. exact (eq_refl (term993 d)). Qed.
Lemma lem5389666 (d : nat) (m : nat) : (term992 d m) = (term994 d m).
Proof. exact (MK_COMB (@lem5389665 d) (@lem5389664 m)). Qed.
Lemma lem5389667 (d : nat) (m : nat) : (term991 d m) = (term994 d m).
Proof. exact (TRANS (@lem5389661 d m) (@lem5389666 d m)). Qed.
Lemma lem5389668 : int_lt = int_lt.
Proof. exact (eq_refl int_lt). Qed.
Lemma lem5389669 (d : nat) (m : nat) : (term1000 d m) = (term1001 d m).
Proof. exact (MK_COMB (@lem5389668) (@lem5389667 d m)). Qed.
Lemma lem5389670 (m : nat) : (int_of_num m) = (int_of_num m).
Proof. exact (eq_refl (int_of_num m)). Qed.
Lemma lem5389671 (d : nat) (m : nat) : (term999 d m) = (term1002 d m).
Proof. exact (MK_COMB (@lem5389669 d m) (@lem5389670 m)). Qed.
Lemma lem5389672 (d : nat) (m : nat) : (term972 d m) = (term1002 d m).
Proof. exact (TRANS (@lem5389658 d m) (@lem5389671 d m)). Qed.
Lemma lem5389673 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5389674 (d : nat) (m : nat) : (term974 d m) = (term1003 d m).
Proof. exact (MK_COMB (@lem5389673) (@lem5389672 d m)). Qed.
Lemma lem5389675 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5389676 (d : nat) (m : nat) : (term976 d m) = (term1004 d m).
Proof. exact (MK_COMB (@lem5389675) (@lem5389674 d m)). Qed.
Lemma lem5389678 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem5389679 (d' : nat) : (d' = (NUMERAL 0)) = ((int_of_num d') = term59).
Proof. exact (@lem5389678 d' (NUMERAL 0)). Qed.
Lemma lem5389682 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5389683 (d' : nat) : (term60 d') = (term61 d').
Proof. exact (MK_COMB (@lem5389682) (@lem5389679 d')). Qed.
Lemma lem5389684 (d : nat) (m : nat) (d' : nat) : (term978 d m d') = (term1005 d m d').
Proof. exact (MK_COMB (@lem5389676 d m) (@lem5389683 d')). Qed.
Lemma lem5389685 (d : nat) (m : nat) (d' : nat) : (term986 d m d') = (term1006 d m d').
Proof. exact (MK_COMB (@lem5389655 d d' m) (@lem5389684 d m d')). Qed.
Lemma lem5389686 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5389687 (d : nat) (m : nat) (d' : nat) : (term987 d m d') = (term1007 d m d').
Proof. exact (MK_COMB (@lem5389686) (@lem5389685 d m d')). Qed.
Lemma lem5389689 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem5389690 (d : nat) (d' : nat) : ((term4 d) = d') = ((term40 d) = (int_of_num d')).
Proof. exact (@lem5389689 (term4 d) d'). Qed.
Lemma lem5389694 (m : nat) (n : nat) : (term41 m n) = (term42 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5389695 (d : nat) : (term40 d) = (term43 d).
Proof. exact (@lem5389694 d term44). Qed.
Lemma lem5389696 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem5389697 (d : nat) : (term45 d) = (term46 d).
Proof. exact (MK_COMB (@lem5389696) (@lem5389695 d)). Qed.
Lemma lem5389698 (d' : nat) : (int_of_num d') = (int_of_num d').
Proof. exact (eq_refl (int_of_num d')). Qed.
Lemma lem5389699 (d : nat) (d' : nat) : ((term40 d) = (int_of_num d')) = ((term43 d) = (int_of_num d')).
Proof. exact (MK_COMB (@lem5389697 d) (@lem5389698 d')). Qed.
Lemma lem5389700 (d : nat) (d' : nat) : ((term4 d) = d') = ((term43 d) = (int_of_num d')).
Proof. exact (TRANS (@lem5389690 d d') (@lem5389699 d d')). Qed.
Lemma lem5389701 (m : nat) (d : nat) (d' : nat) : (term988 m d d') = (term1008 m d d').
Proof. exact (MK_COMB (@lem5389687 d m d') (@lem5389700 d d')). Qed.
Lemma lem5389702 (m : nat) (d : nat) : (term989 m d) = (term1009 m d).
Proof. exact (fun_ext (fun d' : nat => @lem5389701 m d d')). Qed.
Lemma lem5389703 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5389704 (m : nat) (d : nat) : (term990 m d) = (term1010 m d).
Proof. exact (MK_COMB (@lem5389703) (@lem5389702 m d)). Qed.
Lemma lem5389705 (m : nat) (d : nat) : ((term4 d) = (term950 d m)) = (term1010 m d).
Proof. exact (TRANS (@lem5389630 m d) (@lem5389704 m d)). Qed.
Lemma lem5389706 (d : nat) : term73 d.
Proof. exact (@lem2307535 d). Qed.
Lemma lem5389707 (d : nat) : (term73 d) = (term74 d).
Proof. exact (eq_refl (term73 d)). Qed.
Lemma lem5389708 (d : nat) : term74 d.
Proof. exact (EQ_MP (@lem5389707 d) (@lem5389706 d)). Qed.
Lemma lem5389709 (d' : nat) : term73 d'.
Proof. exact (@lem2307535 d'). Qed.
Lemma lem5389710 (d' : nat) : (term73 d') = (term74 d').
Proof. exact (eq_refl (term73 d')). Qed.
Lemma lem5389711 (d' : nat) : term74 d'.
Proof. exact (EQ_MP (@lem5389710 d') (@lem5389709 d')). Qed.
Lemma lem5389712 (m : nat) : term73 m.
Proof. exact (@lem2307535 m). Qed.
Lemma lem5389713 (m : nat) : (term73 m) = (term74 m).
Proof. exact (eq_refl (term73 m)). Qed.
Lemma lem5389714 (m : nat) : term74 m.
Proof. exact (EQ_MP (@lem5389713 m) (@lem5389712 m)). Qed.
Lemma lem5389715 (_69867 : int) (_69865 : int) (_69866 : int) : (term1011 _69867 _69865 _69866) = (term1012 _69867 _69865 _69866).
Proof. exact (@lem2318604 (term1012 _69867 _69865 _69866)). Qed.
Lemma lem5389738 (_69865 : int) (_69866 : int) (_69867 : int) : (term1013 _69865 _69866 _69867) = ((term1014 _69865 _69867) = (int_add _69866 _69867)).
Proof. exact (@lem16933 ((term1014 _69865 _69867) = (int_add _69866 _69867))). Qed.
Lemma lem5389741 (_69865 : int) (_69867 : int) : (term1015 _69865 _69867) = (term1016 _69865 _69867).
Proof. exact (@lem16933 (term1016 _69865 _69867)). Qed.
Lemma lem5389744 (_69866 : int) : (term81 _69866) = (_69866 = term59).
Proof. exact (@lem16933 (_69866 = term59)). Qed.
Lemma lem5389745 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5389746 (_69865 : int) (_69867 : int) : (term1017 _69865 _69867) = (term1018 _69865 _69867).
Proof. exact (MK_COMB (@lem5389745) (@lem5389741 _69865 _69867)). Qed.
Lemma lem5389747 (_69865 : int) (_69867 : int) (_69866 : int) : (term1019 _69865 _69867 _69866) = (term1020 _69865 _69867 _69866).
Proof. exact (MK_COMB (@lem5389746 _69865 _69867) (@lem5389744 _69866)). Qed.
Lemma lem5389748 (_69865 : int) (_69867 : int) (_69866 : int) : (term1021 _69865 _69867 _69866) = (term1019 _69865 _69867 _69866).
Proof. exact (@lem17160 (term1022 _69865 _69867) (term88 _69866)). Qed.
Lemma lem5389749 (_69865 : int) (_69867 : int) (_69866 : int) : (term1021 _69865 _69867 _69866) = (term1020 _69865 _69867 _69866).
Proof. exact (TRANS (@lem5389748 _69865 _69867 _69866) (@lem5389747 _69865 _69867 _69866)). Qed.
Lemma lem5389750 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5389751 (_69865 : int) (_69866 : int) (_69867 : int) : (term1023 _69865 _69866 _69867) = (term1024 _69865 _69866 _69867).
Proof. exact (MK_COMB (@lem5389750) (@lem5389738 _69865 _69866 _69867)). Qed.
Lemma lem5389752 (_69865 : int) (_69867 : int) (_69866 : int) : (term1025 _69865 _69867 _69866) = (term1026 _69865 _69867 _69866).
Proof. exact (MK_COMB (@lem5389751 _69865 _69866 _69867) (@lem5389749 _69865 _69867 _69866)). Qed.
Lemma lem5389753 (_69865 : int) (_69867 : int) (_69866 : int) : (term1027 _69865 _69867 _69866) = (term1025 _69865 _69867 _69866).
Proof. exact (@lem17045 (term1028 _69865 _69866 _69867) (term1029 _69865 _69867 _69866)). Qed.
Lemma lem5389754 (_69865 : int) (_69867 : int) (_69866 : int) : (term1027 _69865 _69867 _69866) = (term1026 _69865 _69867 _69866).
Proof. exact (TRANS (@lem5389753 _69865 _69867 _69866) (@lem5389752 _69865 _69867 _69866)). Qed.
Lemma lem5389755 (_69865 : int) (_69866 : int) : (term1030 _69865 _69866) = (term1030 _69865 _69866).
Proof. exact (eq_refl (term1030 _69865 _69866)). Qed.
Lemma lem5389756 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5389757 (_69865 : int) (_69867 : int) (_69866 : int) : (term1031 _69865 _69867 _69866) = (term1032 _69865 _69867 _69866).
Proof. exact (MK_COMB (@lem5389756) (@lem5389754 _69865 _69867 _69866)). Qed.
Lemma lem5389758 (_69867 : int) (_69865 : int) (_69866 : int) : (term1033 _69867 _69865 _69866) = (term1034 _69867 _69865 _69866).
Proof. exact (MK_COMB (@lem5389757 _69865 _69867 _69866) (@lem5389755 _69865 _69866)). Qed.
Lemma lem5389759 (_69867 : int) (_69865 : int) (_69866 : int) : (term1035 _69867 _69865 _69866) = (term1033 _69867 _69865 _69866).
Proof. exact (@lem17160 (term1036 _69865 _69867 _69866) ((term78 _69865) = _69866)). Qed.
Lemma lem5389760 (_69867 : int) (_69865 : int) (_69866 : int) : (term1035 _69867 _69865 _69866) = (term1034 _69867 _69865 _69866).
Proof. exact (TRANS (@lem5389759 _69867 _69865 _69866) (@lem5389758 _69867 _69865 _69866)). Qed.
Lemma lem5389762 (_69867 : int) : (term110 _69867) = (term110 _69867).
Proof. exact (eq_refl (term110 _69867)). Qed.
Lemma lem5389763 (_69867 : int) (_69865 : int) (_69866 : int) : (term1037 _69867 _69865 _69866) = (term1038 _69867 _69865 _69866).
Proof. exact (MK_COMB (@lem5389762 _69867) (@lem5389760 _69867 _69865 _69866)). Qed.
Lemma lem5389764 (_69867 : int) (_69865 : int) (_69866 : int) : (term1039 _69867 _69865 _69866) = (term1037 _69867 _69865 _69866).
Proof. exact (@lem17362 (term114 _69867) (term1040 _69867 _69865 _69866)). Qed.
Lemma lem5389765 (_69867 : int) (_69865 : int) (_69866 : int) : (term1039 _69867 _69865 _69866) = (term1038 _69867 _69865 _69866).
Proof. exact (TRANS (@lem5389764 _69867 _69865 _69866) (@lem5389763 _69867 _69865 _69866)). Qed.
Lemma lem5389767 (_69866 : int) : (term110 _69866) = (term110 _69866).
Proof. exact (eq_refl (term110 _69866)). Qed.
Lemma lem5389768 (_69867 : int) (_69865 : int) (_69866 : int) : (term1041 _69867 _69865 _69866) = (term1042 _69867 _69865 _69866).
Proof. exact (MK_COMB (@lem5389767 _69866) (@lem5389765 _69867 _69865 _69866)). Qed.
Lemma lem5389769 (_69867 : int) (_69865 : int) (_69866 : int) : (term1043 _69867 _69865 _69866) = (term1041 _69867 _69865 _69866).
Proof. exact (@lem17362 (term114 _69866) (term1044 _69867 _69865 _69866)). Qed.
Lemma lem5389770 (_69867 : int) (_69865 : int) (_69866 : int) : (term1043 _69867 _69865 _69866) = (term1042 _69867 _69865 _69866).
Proof. exact (TRANS (@lem5389769 _69867 _69865 _69866) (@lem5389768 _69867 _69865 _69866)). Qed.
Lemma lem5389772 (_69865 : int) : (term110 _69865) = (term110 _69865).
Proof. exact (eq_refl (term110 _69865)). Qed.
Lemma lem5389773 (_69867 : int) (_69865 : int) (_69866 : int) : (term1045 _69867 _69865 _69866) = (term1046 _69867 _69865 _69866).
Proof. exact (MK_COMB (@lem5389772 _69865) (@lem5389770 _69867 _69865 _69866)). Qed.
Lemma lem5389774 (_69867 : int) (_69865 : int) (_69866 : int) : (term1047 _69867 _69865 _69866) = (term1045 _69867 _69865 _69866).
Proof. exact (@lem17362 (term114 _69865) (term1048 _69867 _69865 _69866)). Qed.
Lemma lem5389804 (_69867 : int) (_69865 : int) (_69866 : int) : (term1047 _69867 _69865 _69866) = (term1046 _69867 _69865 _69866).
Proof. exact (TRANS (@lem5389774 _69867 _69865 _69866) (@lem5389773 _69867 _69865 _69866)). Qed.
Lemma lem5389807 (x : int) (y : int) : (int_le x y) = (term124 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5389808 (_69865 : int) : (term114 _69865) = (term125 _69865).
Proof. exact (@lem5389807 term59 _69865). Qed.
Lemma lem5389810 (n : nat) : (term126 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5389811 : term127 = term128.
Proof. exact (@lem5389810 (NUMERAL 0)). Qed.
Lemma lem5389812 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5389813 : term129 = term130.
Proof. exact (MK_COMB (@lem5389812) (@lem5389811)). Qed.
Lemma lem5389814 (_69865 : int) : (real_of_int _69865) = (real_of_int _69865).
Proof. exact (eq_refl (real_of_int _69865)). Qed.
Lemma lem5389815 (_69865 : int) : (term125 _69865) = (term131 _69865).
Proof. exact (MK_COMB (@lem5389813) (@lem5389814 _69865)). Qed.
Lemma lem5389817 (_69865 : int) : (term114 _69865) = (term131 _69865).
Proof. exact (TRANS (@lem5389808 _69865) (@lem5389815 _69865)). Qed.
Lemma lem5389820 (x : int) (y : int) : (int_le x y) = (term124 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5389821 (_69866 : int) : (term114 _69866) = (term125 _69866).
Proof. exact (@lem5389820 term59 _69866). Qed.
Lemma lem5389823 (n : nat) : (term126 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5389824 : term127 = term128.
Proof. exact (@lem5389823 (NUMERAL 0)). Qed.
Lemma lem5389825 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5389826 : term129 = term130.
Proof. exact (MK_COMB (@lem5389825) (@lem5389824)). Qed.
Lemma lem5389827 (_69866 : int) : (real_of_int _69866) = (real_of_int _69866).
Proof. exact (eq_refl (real_of_int _69866)). Qed.
Lemma lem5389828 (_69866 : int) : (term125 _69866) = (term131 _69866).
Proof. exact (MK_COMB (@lem5389826) (@lem5389827 _69866)). Qed.
Lemma lem5389830 (_69866 : int) : (term114 _69866) = (term131 _69866).
Proof. exact (TRANS (@lem5389821 _69866) (@lem5389828 _69866)). Qed.
Lemma lem5389833 (x : int) (y : int) : (int_le x y) = (term124 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5389834 (_69867 : int) : (term114 _69867) = (term125 _69867).
Proof. exact (@lem5389833 term59 _69867). Qed.
Lemma lem5389836 (n : nat) : (term126 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5389837 : term127 = term128.
Proof. exact (@lem5389836 (NUMERAL 0)). Qed.
Lemma lem5389838 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5389839 : term129 = term130.
Proof. exact (MK_COMB (@lem5389838) (@lem5389837)). Qed.
Lemma lem5389840 (_69867 : int) : (real_of_int _69867) = (real_of_int _69867).
Proof. exact (eq_refl (real_of_int _69867)). Qed.
Lemma lem5389841 (_69867 : int) : (term125 _69867) = (term131 _69867).
Proof. exact (MK_COMB (@lem5389839) (@lem5389840 _69867)). Qed.
Lemma lem5389843 (_69867 : int) : (term114 _69867) = (term131 _69867).
Proof. exact (TRANS (@lem5389834 _69867) (@lem5389841 _69867)). Qed.
Lemma lem5389846 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem5389847 (_69865 : int) (_69866 : int) (_69867 : int) : ((term1014 _69865 _69867) = (int_add _69866 _69867)) = ((term1049 _69865 _69867) = (term133 _69866 _69867)).
Proof. exact (@lem5389846 (term1014 _69865 _69867) (int_add _69866 _69867)). Qed.
Lemma lem5389851 (x : int) (y : int) : (term133 x y) = (term134 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5389852 (_69865 : int) (_69867 : int) : (term1049 _69865 _69867) = (term1050 _69865 _69867).
Proof. exact (@lem5389851 _69865 (term78 _69867)). Qed.
Lemma lem5389854 (x : int) (y : int) : (term133 x y) = (term134 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5389855 (_69867 : int) : (term132 _69867) = (term135 _69867).
Proof. exact (@lem5389854 _69867 term136). Qed.
Lemma lem5389857 (n : nat) : (term126 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5389858 : term137 = term138.
Proof. exact (@lem5389857 term44). Qed.
Lemma lem5389859 (_69867 : int) : (term139 _69867) = (term139 _69867).
Proof. exact (eq_refl (term139 _69867)). Qed.
Lemma lem5389860 (_69867 : int) : (term135 _69867) = (term140 _69867).
Proof. exact (MK_COMB (@lem5389859 _69867) (@lem5389858)). Qed.
Lemma lem5389861 (_69867 : int) : (term132 _69867) = (term140 _69867).
Proof. exact (TRANS (@lem5389855 _69867) (@lem5389860 _69867)). Qed.
Lemma lem5389862 (_69865 : int) : (term139 _69865) = (term139 _69865).
Proof. exact (eq_refl (term139 _69865)). Qed.
Lemma lem5389863 (_69865 : int) (_69867 : int) : (term1050 _69865 _69867) = (term1051 _69865 _69867).
Proof. exact (MK_COMB (@lem5389862 _69865) (@lem5389861 _69867)). Qed.
Lemma lem5389864 (_69865 : int) (_69867 : int) : (term1049 _69865 _69867) = (term1051 _69865 _69867).
Proof. exact (TRANS (@lem5389852 _69865 _69867) (@lem5389863 _69865 _69867)). Qed.
Lemma lem5389865 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5389866 (_69865 : int) (_69867 : int) : (term1052 _69865 _69867) = (term1053 _69865 _69867).
Proof. exact (MK_COMB (@lem5389865) (@lem5389864 _69865 _69867)). Qed.
Lemma lem5389868 (x : int) (y : int) : (term133 x y) = (term134 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5389869 (_69866 : int) (_69867 : int) : (term133 _69866 _69867) = (term134 _69866 _69867).
Proof. exact (@lem5389868 _69866 _69867). Qed.
Lemma lem5389870 (_69865 : int) (_69866 : int) (_69867 : int) : ((term1049 _69865 _69867) = (term133 _69866 _69867)) = ((term1051 _69865 _69867) = (term134 _69866 _69867)).
Proof. exact (MK_COMB (@lem5389866 _69865 _69867) (@lem5389869 _69866 _69867)). Qed.
Lemma lem5389872 (_69865 : int) (_69866 : int) (_69867 : int) : ((term1014 _69865 _69867) = (int_add _69866 _69867)) = ((term1051 _69865 _69867) = (term134 _69866 _69867)).
Proof. exact (TRANS (@lem5389847 _69865 _69866 _69867) (@lem5389870 _69865 _69866 _69867)). Qed.
Lemma lem5389874 (x : int) (y : int) : (int_lt x y) = (term143 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem5389875 (_69865 : int) (_69867 : int) : (term1016 _69865 _69867) = (term1054 _69865 _69867).
Proof. exact (@lem5389874 (term1014 _69865 _69867) _69867). Qed.
Lemma lem5389877 (x : int) (y : int) : (int_le x y) = (term124 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5389878 (_69865 : int) (_69867 : int) : (term1054 _69865 _69867) = (term1055 _69865 _69867).
Proof. exact (@lem5389877 (term1056 _69865 _69867) _69867). Qed.
Lemma lem5389880 (x : int) (y : int) : (term133 x y) = (term134 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5389881 (_69865 : int) (_69867 : int) : (term1057 _69865 _69867) = (term1058 _69865 _69867).
Proof. exact (@lem5389880 (term1014 _69865 _69867) term136). Qed.
Lemma lem5389883 (x : int) (y : int) : (term133 x y) = (term134 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5389884 (_69865 : int) (_69867 : int) : (term1049 _69865 _69867) = (term1050 _69865 _69867).
Proof. exact (@lem5389883 _69865 (term78 _69867)). Qed.
Lemma lem5389886 (x : int) (y : int) : (term133 x y) = (term134 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5389887 (_69867 : int) : (term132 _69867) = (term135 _69867).
Proof. exact (@lem5389886 _69867 term136). Qed.
Lemma lem5389889 (n : nat) : (term126 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5389890 : term137 = term138.
Proof. exact (@lem5389889 term44). Qed.
Lemma lem5389891 (_69867 : int) : (term139 _69867) = (term139 _69867).
Proof. exact (eq_refl (term139 _69867)). Qed.
Lemma lem5389892 (_69867 : int) : (term135 _69867) = (term140 _69867).
Proof. exact (MK_COMB (@lem5389891 _69867) (@lem5389890)). Qed.
Lemma lem5389893 (_69867 : int) : (term132 _69867) = (term140 _69867).
Proof. exact (TRANS (@lem5389887 _69867) (@lem5389892 _69867)). Qed.
Lemma lem5389894 (_69865 : int) : (term139 _69865) = (term139 _69865).
Proof. exact (eq_refl (term139 _69865)). Qed.
Lemma lem5389895 (_69865 : int) (_69867 : int) : (term1050 _69865 _69867) = (term1051 _69865 _69867).
Proof. exact (MK_COMB (@lem5389894 _69865) (@lem5389893 _69867)). Qed.
Lemma lem5389896 (_69865 : int) (_69867 : int) : (term1049 _69865 _69867) = (term1051 _69865 _69867).
Proof. exact (TRANS (@lem5389884 _69865 _69867) (@lem5389895 _69865 _69867)). Qed.
Lemma lem5389897 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5389898 (_69865 : int) (_69867 : int) : (term1059 _69865 _69867) = (term1060 _69865 _69867).
Proof. exact (MK_COMB (@lem5389897) (@lem5389896 _69865 _69867)). Qed.
Lemma lem5389900 (n : nat) : (term126 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5389901 : term137 = term138.
Proof. exact (@lem5389900 term44). Qed.
Lemma lem5389902 (_69865 : int) (_69867 : int) : (term1058 _69865 _69867) = (term1061 _69865 _69867).
Proof. exact (MK_COMB (@lem5389898 _69865 _69867) (@lem5389901)). Qed.
Lemma lem5389903 (_69865 : int) (_69867 : int) : (term1057 _69865 _69867) = (term1061 _69865 _69867).
Proof. exact (TRANS (@lem5389881 _69865 _69867) (@lem5389902 _69865 _69867)). Qed.
Lemma lem5389904 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5389905 (_69865 : int) (_69867 : int) : (term1062 _69865 _69867) = (term1063 _69865 _69867).
Proof. exact (MK_COMB (@lem5389904) (@lem5389903 _69865 _69867)). Qed.
Lemma lem5389906 (_69867 : int) : (real_of_int _69867) = (real_of_int _69867).
Proof. exact (eq_refl (real_of_int _69867)). Qed.
Lemma lem5389907 (_69865 : int) (_69867 : int) : (term1055 _69865 _69867) = (term1064 _69865 _69867).
Proof. exact (MK_COMB (@lem5389905 _69865 _69867) (@lem5389906 _69867)). Qed.
Lemma lem5389908 (_69865 : int) (_69867 : int) : (term1054 _69865 _69867) = (term1064 _69865 _69867).
Proof. exact (TRANS (@lem5389878 _69865 _69867) (@lem5389907 _69865 _69867)). Qed.
Lemma lem5389909 (_69865 : int) (_69867 : int) : (term1016 _69865 _69867) = (term1064 _69865 _69867).
Proof. exact (TRANS (@lem5389875 _69865 _69867) (@lem5389908 _69865 _69867)). Qed.
Lemma lem5389912 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem5389913 (_69866 : int) : (_69866 = term59) = ((real_of_int _69866) = term127).
Proof. exact (@lem5389912 _69866 term59). Qed.
Lemma lem5389917 (n : nat) : (term126 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5389918 : term127 = term128.
Proof. exact (@lem5389917 (NUMERAL 0)). Qed.
Lemma lem5389919 (_69866 : int) : (term155 _69866) = (term155 _69866).
Proof. exact (eq_refl (term155 _69866)). Qed.
Lemma lem5389920 (_69866 : int) : ((real_of_int _69866) = term127) = ((real_of_int _69866) = term128).
Proof. exact (MK_COMB (@lem5389919 _69866) (@lem5389918)). Qed.
Lemma lem5389922 (_69866 : int) : (_69866 = term59) = ((real_of_int _69866) = term128).
Proof. exact (TRANS (@lem5389913 _69866) (@lem5389920 _69866)). Qed.
Lemma lem5389923 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5389924 (_69865 : int) (_69867 : int) : (term1018 _69865 _69867) = (term1065 _69865 _69867).
Proof. exact (MK_COMB (@lem5389923) (@lem5389909 _69865 _69867)). Qed.
Lemma lem5389925 (_69865 : int) (_69867 : int) (_69866 : int) : (term1020 _69865 _69867 _69866) = (term1066 _69865 _69867 _69866).
Proof. exact (MK_COMB (@lem5389924 _69865 _69867) (@lem5389922 _69866)). Qed.
Lemma lem5389926 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5389927 (_69865 : int) (_69866 : int) (_69867 : int) : (term1024 _69865 _69866 _69867) = (term1067 _69865 _69866 _69867).
Proof. exact (MK_COMB (@lem5389926) (@lem5389872 _69865 _69866 _69867)). Qed.
Lemma lem5389928 (_69865 : int) (_69867 : int) (_69866 : int) : (term1026 _69865 _69867 _69866) = (term1068 _69865 _69867 _69866).
Proof. exact (MK_COMB (@lem5389927 _69865 _69866 _69867) (@lem5389925 _69865 _69867 _69866)). Qed.
Lemma lem5389930 (y : int) (x : int) : (term164 x y) = (term165 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem5389931 (_69866 : int) (_69865 : int) : (term1030 _69865 _69866) = (term1069 _69866 _69865).
Proof. exact (@lem5389930 _69866 (term78 _69865)). Qed.
Lemma lem5389933 (x : int) (y : int) : (int_le x y) = (term124 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5389934 (_69865 : int) (_69866 : int) : (term144 _69865 _69866) = (term145 _69865 _69866).
Proof. exact (@lem5389933 (term146 _69865) _69866). Qed.
Lemma lem5389936 (x : int) (y : int) : (term133 x y) = (term134 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5389937 (_69865 : int) : (term147 _69865) = (term148 _69865).
Proof. exact (@lem5389936 (term78 _69865) term136). Qed.
Lemma lem5389939 (x : int) (y : int) : (term133 x y) = (term134 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5389940 (_69865 : int) : (term132 _69865) = (term135 _69865).
Proof. exact (@lem5389939 _69865 term136). Qed.
Lemma lem5389942 (n : nat) : (term126 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5389943 : term137 = term138.
Proof. exact (@lem5389942 term44). Qed.
Lemma lem5389944 (_69865 : int) : (term139 _69865) = (term139 _69865).
Proof. exact (eq_refl (term139 _69865)). Qed.
Lemma lem5389945 (_69865 : int) : (term135 _69865) = (term140 _69865).
Proof. exact (MK_COMB (@lem5389944 _69865) (@lem5389943)). Qed.
Lemma lem5389946 (_69865 : int) : (term132 _69865) = (term140 _69865).
Proof. exact (TRANS (@lem5389940 _69865) (@lem5389945 _69865)). Qed.
Lemma lem5389947 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5389948 (_69865 : int) : (term149 _69865) = (term150 _69865).
Proof. exact (MK_COMB (@lem5389947) (@lem5389946 _69865)). Qed.
Lemma lem5389950 (n : nat) : (term126 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5389951 : term137 = term138.
Proof. exact (@lem5389950 term44). Qed.
Lemma lem5389952 (_69865 : int) : (term148 _69865) = (term151 _69865).
Proof. exact (MK_COMB (@lem5389948 _69865) (@lem5389951)). Qed.
Lemma lem5389953 (_69865 : int) : (term147 _69865) = (term151 _69865).
Proof. exact (TRANS (@lem5389937 _69865) (@lem5389952 _69865)). Qed.
Lemma lem5389954 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5389955 (_69865 : int) : (term152 _69865) = (term153 _69865).
Proof. exact (MK_COMB (@lem5389954) (@lem5389953 _69865)). Qed.
Lemma lem5389956 (_69866 : int) : (real_of_int _69866) = (real_of_int _69866).
Proof. exact (eq_refl (real_of_int _69866)). Qed.
Lemma lem5389957 (_69865 : int) (_69866 : int) : (term145 _69865 _69866) = (term154 _69865 _69866).
Proof. exact (MK_COMB (@lem5389955 _69865) (@lem5389956 _69866)). Qed.
Lemma lem5389958 (_69865 : int) (_69866 : int) : (term144 _69865 _69866) = (term154 _69865 _69866).
Proof. exact (TRANS (@lem5389934 _69865 _69866) (@lem5389957 _69865 _69866)). Qed.
Lemma lem5389959 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5389960 (_69865 : int) (_69866 : int) : (term1070 _69865 _69866) = (term1071 _69865 _69866).
Proof. exact (MK_COMB (@lem5389959) (@lem5389958 _69865 _69866)). Qed.
Lemma lem5389962 (x : int) (y : int) : (int_le x y) = (term124 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5389963 (_69866 : int) (_69865 : int) : (term1072 _69866 _69865) = (term1073 _69866 _69865).
Proof. exact (@lem5389962 (term78 _69866) (term78 _69865)). Qed.
Lemma lem5389965 (x : int) (y : int) : (term133 x y) = (term134 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5389966 (_69866 : int) : (term132 _69866) = (term135 _69866).
Proof. exact (@lem5389965 _69866 term136). Qed.
Lemma lem5389968 (n : nat) : (term126 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5389969 : term137 = term138.
Proof. exact (@lem5389968 term44). Qed.
Lemma lem5389970 (_69866 : int) : (term139 _69866) = (term139 _69866).
Proof. exact (eq_refl (term139 _69866)). Qed.
Lemma lem5389971 (_69866 : int) : (term135 _69866) = (term140 _69866).
Proof. exact (MK_COMB (@lem5389970 _69866) (@lem5389969)). Qed.
Lemma lem5389972 (_69866 : int) : (term132 _69866) = (term140 _69866).
Proof. exact (TRANS (@lem5389966 _69866) (@lem5389971 _69866)). Qed.
Lemma lem5389973 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5389974 (_69866 : int) : (term161 _69866) = (term162 _69866).
Proof. exact (MK_COMB (@lem5389973) (@lem5389972 _69866)). Qed.
Lemma lem5389976 (x : int) (y : int) : (term133 x y) = (term134 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5389977 (_69865 : int) : (term132 _69865) = (term135 _69865).
Proof. exact (@lem5389976 _69865 term136). Qed.
Lemma lem5389979 (n : nat) : (term126 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5389980 : term137 = term138.
Proof. exact (@lem5389979 term44). Qed.
Lemma lem5389981 (_69865 : int) : (term139 _69865) = (term139 _69865).
Proof. exact (eq_refl (term139 _69865)). Qed.
Lemma lem5389982 (_69865 : int) : (term135 _69865) = (term140 _69865).
Proof. exact (MK_COMB (@lem5389981 _69865) (@lem5389980)). Qed.
Lemma lem5389983 (_69865 : int) : (term132 _69865) = (term140 _69865).
Proof. exact (TRANS (@lem5389977 _69865) (@lem5389982 _69865)). Qed.
Lemma lem5389984 (_69866 : int) (_69865 : int) : (term1073 _69866 _69865) = (term1074 _69866 _69865).
Proof. exact (MK_COMB (@lem5389974 _69866) (@lem5389983 _69865)). Qed.
Lemma lem5389985 (_69866 : int) (_69865 : int) : (term1072 _69866 _69865) = (term1074 _69866 _69865).
Proof. exact (TRANS (@lem5389963 _69866 _69865) (@lem5389984 _69866 _69865)). Qed.
Lemma lem5389986 (_69866 : int) (_69865 : int) : (term1069 _69866 _69865) = (term1075 _69866 _69865).
Proof. exact (MK_COMB (@lem5389960 _69865 _69866) (@lem5389985 _69866 _69865)). Qed.
Lemma lem5389987 (_69866 : int) (_69865 : int) : (term1030 _69865 _69866) = (term1075 _69866 _69865).
Proof. exact (TRANS (@lem5389931 _69866 _69865) (@lem5389986 _69866 _69865)). Qed.
Lemma lem5389988 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5389989 (_69865 : int) (_69867 : int) (_69866 : int) : (term1032 _69865 _69867 _69866) = (term1076 _69865 _69867 _69866).
Proof. exact (MK_COMB (@lem5389988) (@lem5389928 _69865 _69867 _69866)). Qed.
Lemma lem5389990 (_69867 : int) (_69866 : int) (_69865 : int) : (term1034 _69867 _69865 _69866) = (term1077 _69867 _69866 _69865).
Proof. exact (MK_COMB (@lem5389989 _69865 _69867 _69866) (@lem5389987 _69866 _69865)). Qed.
Lemma lem5389991 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5389992 (_69867 : int) : (term110 _69867) = (term188 _69867).
Proof. exact (MK_COMB (@lem5389991) (@lem5389843 _69867)). Qed.
Lemma lem5389993 (_69867 : int) (_69866 : int) (_69865 : int) : (term1038 _69867 _69865 _69866) = (term1078 _69867 _69866 _69865).
Proof. exact (MK_COMB (@lem5389992 _69867) (@lem5389990 _69867 _69866 _69865)). Qed.
Lemma lem5389994 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5389995 (_69866 : int) : (term110 _69866) = (term188 _69866).
Proof. exact (MK_COMB (@lem5389994) (@lem5389830 _69866)). Qed.
Lemma lem5389996 (_69867 : int) (_69866 : int) (_69865 : int) : (term1042 _69867 _69865 _69866) = (term1079 _69867 _69866 _69865).
Proof. exact (MK_COMB (@lem5389995 _69866) (@lem5389993 _69867 _69866 _69865)). Qed.
Lemma lem5389997 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5389998 (_69865 : int) : (term110 _69865) = (term188 _69865).
Proof. exact (MK_COMB (@lem5389997) (@lem5389817 _69865)). Qed.
Lemma lem5389999 (_69867 : int) (_69866 : int) (_69865 : int) : (term1046 _69867 _69865 _69866) = (term1080 _69867 _69866 _69865).
Proof. exact (MK_COMB (@lem5389998 _69865) (@lem5389996 _69867 _69866 _69865)). Qed.
Lemma lem5390000 (_69867 : int) (_69866 : int) (_69865 : int) : (term1047 _69867 _69865 _69866) = (term1080 _69867 _69866 _69865).
Proof. exact (TRANS (@lem5389804 _69867 _69865 _69866) (@lem5389999 _69867 _69866 _69865)). Qed.
Lemma lem5390004 (t : Prop) : (term192 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5390080 (_69867 : int) (_69866 : int) (_69865 : int) : (term1081 _69867 _69866 _69865) = (term1080 _69867 _69866 _69865).
Proof. exact (@lem5390004 (term1080 _69867 _69866 _69865)). Qed.
Lemma lem5390081 (_69865 : int) : (term131 _69865) = (term194 _69865).
Proof. exact (@lem1988287 (real_of_int _69865) term128). Qed.
Lemma lem5390087 (_69865 : int) : (term195 _69865) = (term196 _69865).
Proof. exact (@lem1982792 (real_of_int _69865) term128). Qed.
Lemma lem5390089 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5390090 : term128 = term198.
Proof. exact (@lem5390089 (NUMERAL 0)). Qed.
Lemma lem5390092 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5390093 : term201 = term202.
Proof. exact (@lem5390092 term44). Qed.
Lemma lem5390094 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5390095 : term203 = term204.
Proof. exact (MK_COMB (@lem5390094) (@lem5390093)). Qed.
Lemma lem5390096 : term205 = term206.
Proof. exact (MK_COMB (@lem5390095) (@lem5390090)). Qed.
Lemma lem5390097 : term206 = term207.
Proof. exact (@lem1981613 term201 term128 term138 term138). Qed.
Lemma lem5390099 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5390100 : term210 = term211.
Proof. exact (@lem5390099 term44 term44). Qed.
Lemma lem5390101 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5390102 : term213 = term44.
Proof. exact (EQ_MP (@lem5390101) (@lem940073)). Qed.
Lemma lem5390103 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5390104 : term211 = term138.
Proof. exact (MK_COMB (@lem5390103) (@lem5390102)). Qed.
Lemma lem5390105 : term210 = term138.
Proof. exact (TRANS (@lem5390100) (@lem5390104)). Qed.
Lemma lem5390107 (x : nat) : (term214 x) = term128.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5390108 : term205 = term128.
Proof. exact (@lem5390107 term44). Qed.
Lemma lem5390109 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5390110 : term215 = term216.
Proof. exact (MK_COMB (@lem5390109) (@lem5390108)). Qed.
Lemma lem5390111 : term207 = term198.
Proof. exact (MK_COMB (@lem5390110) (@lem5390105)). Qed.
Lemma lem5390112 : term206 = term198.
Proof. exact (TRANS (@lem5390097) (@lem5390111)). Qed.
Lemma lem5390113 : term205 = term198.
Proof. exact (TRANS (@lem5390096) (@lem5390112)). Qed.
Lemma lem5390115 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5390116 : term198 = term128.
Proof. exact (@lem5390115 term128). Qed.
Lemma lem5390117 : term205 = term128.
Proof. exact (TRANS (@lem5390113) (@lem5390116)). Qed.
Lemma lem5390118 (_69865 : int) : (term139 _69865) = (term139 _69865).
Proof. exact (eq_refl (term139 _69865)). Qed.
Lemma lem5390119 (_69865 : int) : (term196 _69865) = (term218 _69865).
Proof. exact (MK_COMB (@lem5390118 _69865) (@lem5390117)). Qed.
Lemma lem5390120 (_69865 : int) : (term218 _69865) = (real_of_int _69865).
Proof. exact (@lem1982723 (real_of_int _69865)). Qed.
Lemma lem5390121 (_69865 : int) : (term196 _69865) = (real_of_int _69865).
Proof. exact (TRANS (@lem5390119 _69865) (@lem5390120 _69865)). Qed.
Lemma lem5390123 (_69865 : int) : (term195 _69865) = (real_of_int _69865).
Proof. exact (TRANS (@lem5390087 _69865) (@lem5390121 _69865)). Qed.
Lemma lem5390124 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5390125 (_69865 : int) : (term219 _69865) = (term220 _69865).
Proof. exact (MK_COMB (@lem5390124) (@lem5390123 _69865)). Qed.
Lemma lem5390126 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5390127 (_69865 : int) : (term194 _69865) = (term221 _69865).
Proof. exact (MK_COMB (@lem5390125 _69865) (@lem5390126)). Qed.
Lemma lem5390128 (_69865 : int) : (term131 _69865) = (term221 _69865).
Proof. exact (TRANS (@lem5390081 _69865) (@lem5390127 _69865)). Qed.
Lemma lem5390129 (_69866 : int) : (term131 _69866) = (term194 _69866).
Proof. exact (@lem1988287 (real_of_int _69866) term128). Qed.
Lemma lem5390135 (_69866 : int) : (term195 _69866) = (term196 _69866).
Proof. exact (@lem1982792 (real_of_int _69866) term128). Qed.
Lemma lem5390137 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5390138 : term128 = term198.
Proof. exact (@lem5390137 (NUMERAL 0)). Qed.
Lemma lem5390140 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5390141 : term201 = term202.
Proof. exact (@lem5390140 term44). Qed.
Lemma lem5390142 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5390143 : term203 = term204.
Proof. exact (MK_COMB (@lem5390142) (@lem5390141)). Qed.
Lemma lem5390144 : term205 = term206.
Proof. exact (MK_COMB (@lem5390143) (@lem5390138)). Qed.
Lemma lem5390145 : term206 = term207.
Proof. exact (@lem1981613 term201 term128 term138 term138). Qed.
Lemma lem5390147 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5390148 : term210 = term211.
Proof. exact (@lem5390147 term44 term44). Qed.
Lemma lem5390149 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5390150 : term213 = term44.
Proof. exact (EQ_MP (@lem5390149) (@lem940073)). Qed.
Lemma lem5390151 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5390152 : term211 = term138.
Proof. exact (MK_COMB (@lem5390151) (@lem5390150)). Qed.
Lemma lem5390153 : term210 = term138.
Proof. exact (TRANS (@lem5390148) (@lem5390152)). Qed.
Lemma lem5390155 (x : nat) : (term214 x) = term128.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5390156 : term205 = term128.
Proof. exact (@lem5390155 term44). Qed.
Lemma lem5390157 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5390158 : term215 = term216.
Proof. exact (MK_COMB (@lem5390157) (@lem5390156)). Qed.
Lemma lem5390159 : term207 = term198.
Proof. exact (MK_COMB (@lem5390158) (@lem5390153)). Qed.
Lemma lem5390160 : term206 = term198.
Proof. exact (TRANS (@lem5390145) (@lem5390159)). Qed.
Lemma lem5390161 : term205 = term198.
Proof. exact (TRANS (@lem5390144) (@lem5390160)). Qed.
Lemma lem5390163 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5390164 : term198 = term128.
Proof. exact (@lem5390163 term128). Qed.
Lemma lem5390165 : term205 = term128.
Proof. exact (TRANS (@lem5390161) (@lem5390164)). Qed.
Lemma lem5390166 (_69866 : int) : (term139 _69866) = (term139 _69866).
Proof. exact (eq_refl (term139 _69866)). Qed.
Lemma lem5390167 (_69866 : int) : (term196 _69866) = (term218 _69866).
Proof. exact (MK_COMB (@lem5390166 _69866) (@lem5390165)). Qed.
Lemma lem5390168 (_69866 : int) : (term218 _69866) = (real_of_int _69866).
Proof. exact (@lem1982723 (real_of_int _69866)). Qed.
Lemma lem5390169 (_69866 : int) : (term196 _69866) = (real_of_int _69866).
Proof. exact (TRANS (@lem5390167 _69866) (@lem5390168 _69866)). Qed.
Lemma lem5390171 (_69866 : int) : (term195 _69866) = (real_of_int _69866).
Proof. exact (TRANS (@lem5390135 _69866) (@lem5390169 _69866)). Qed.
Lemma lem5390172 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5390173 (_69866 : int) : (term219 _69866) = (term220 _69866).
Proof. exact (MK_COMB (@lem5390172) (@lem5390171 _69866)). Qed.
Lemma lem5390174 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5390175 (_69866 : int) : (term194 _69866) = (term221 _69866).
Proof. exact (MK_COMB (@lem5390173 _69866) (@lem5390174)). Qed.
Lemma lem5390176 (_69866 : int) : (term131 _69866) = (term221 _69866).
Proof. exact (TRANS (@lem5390129 _69866) (@lem5390175 _69866)). Qed.
Lemma lem5390177 (_69867 : int) : (term131 _69867) = (term194 _69867).
Proof. exact (@lem1988287 (real_of_int _69867) term128). Qed.
Lemma lem5390183 (_69867 : int) : (term195 _69867) = (term196 _69867).
Proof. exact (@lem1982792 (real_of_int _69867) term128). Qed.
Lemma lem5390185 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5390186 : term128 = term198.
Proof. exact (@lem5390185 (NUMERAL 0)). Qed.
Lemma lem5390188 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5390189 : term201 = term202.
Proof. exact (@lem5390188 term44). Qed.
Lemma lem5390190 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5390191 : term203 = term204.
Proof. exact (MK_COMB (@lem5390190) (@lem5390189)). Qed.
Lemma lem5390192 : term205 = term206.
Proof. exact (MK_COMB (@lem5390191) (@lem5390186)). Qed.
Lemma lem5390193 : term206 = term207.
Proof. exact (@lem1981613 term201 term128 term138 term138). Qed.
Lemma lem5390195 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5390196 : term210 = term211.
Proof. exact (@lem5390195 term44 term44). Qed.
Lemma lem5390197 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5390198 : term213 = term44.
Proof. exact (EQ_MP (@lem5390197) (@lem940073)). Qed.
Lemma lem5390199 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5390200 : term211 = term138.
Proof. exact (MK_COMB (@lem5390199) (@lem5390198)). Qed.
Lemma lem5390201 : term210 = term138.
Proof. exact (TRANS (@lem5390196) (@lem5390200)). Qed.
Lemma lem5390203 (x : nat) : (term214 x) = term128.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5390204 : term205 = term128.
Proof. exact (@lem5390203 term44). Qed.
Lemma lem5390205 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5390206 : term215 = term216.
Proof. exact (MK_COMB (@lem5390205) (@lem5390204)). Qed.
Lemma lem5390207 : term207 = term198.
Proof. exact (MK_COMB (@lem5390206) (@lem5390201)). Qed.
Lemma lem5390208 : term206 = term198.
Proof. exact (TRANS (@lem5390193) (@lem5390207)). Qed.
Lemma lem5390209 : term205 = term198.
Proof. exact (TRANS (@lem5390192) (@lem5390208)). Qed.
Lemma lem5390211 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5390212 : term198 = term128.
Proof. exact (@lem5390211 term128). Qed.
Lemma lem5390213 : term205 = term128.
Proof. exact (TRANS (@lem5390209) (@lem5390212)). Qed.
Lemma lem5390214 (_69867 : int) : (term139 _69867) = (term139 _69867).
Proof. exact (eq_refl (term139 _69867)). Qed.
Lemma lem5390215 (_69867 : int) : (term196 _69867) = (term218 _69867).
Proof. exact (MK_COMB (@lem5390214 _69867) (@lem5390213)). Qed.
Lemma lem5390216 (_69867 : int) : (term218 _69867) = (real_of_int _69867).
Proof. exact (@lem1982723 (real_of_int _69867)). Qed.
Lemma lem5390217 (_69867 : int) : (term196 _69867) = (real_of_int _69867).
Proof. exact (TRANS (@lem5390215 _69867) (@lem5390216 _69867)). Qed.
Lemma lem5390219 (_69867 : int) : (term195 _69867) = (real_of_int _69867).
Proof. exact (TRANS (@lem5390183 _69867) (@lem5390217 _69867)). Qed.
Lemma lem5390220 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5390221 (_69867 : int) : (term219 _69867) = (term220 _69867).
Proof. exact (MK_COMB (@lem5390220) (@lem5390219 _69867)). Qed.
Lemma lem5390222 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5390223 (_69867 : int) : (term194 _69867) = (term221 _69867).
Proof. exact (MK_COMB (@lem5390221 _69867) (@lem5390222)). Qed.
Lemma lem5390224 (_69867 : int) : (term131 _69867) = (term221 _69867).
Proof. exact (TRANS (@lem5390177 _69867) (@lem5390223 _69867)). Qed.
Lemma lem5390225 (_69865 : int) (_69866 : int) (_69867 : int) : ((term1051 _69865 _69867) = (term134 _69866 _69867)) = ((term1082 _69865 _69866 _69867) = term128).
Proof. exact (@lem1988293 (term1051 _69865 _69867) (term134 _69866 _69867)). Qed.
Lemma lem5390249 (_69865 : int) (_69866 : int) (_69867 : int) : (term1082 _69865 _69866 _69867) = (term1083 _69865 _69866 _69867).
Proof. exact (@lem1982792 (term1051 _69865 _69867) (term134 _69866 _69867)). Qed.
Lemma lem5390256 (_69866 : int) (_69867 : int) : (term224 _69866 _69867) = (term225 _69866 _69867).
Proof. exact (@lem1982781 (real_of_int _69866) term201 (real_of_int _69867)). Qed.
Lemma lem5390257 (_69865 : int) (_69867 : int) : (term1060 _69865 _69867) = (term1060 _69865 _69867).
Proof. exact (eq_refl (term1060 _69865 _69867)). Qed.
Lemma lem5390258 (_69865 : int) (_69866 : int) (_69867 : int) : (term1083 _69865 _69866 _69867) = (term1084 _69865 _69866 _69867).
Proof. exact (MK_COMB (@lem5390257 _69865 _69867) (@lem5390256 _69866 _69867)). Qed.
Lemma lem5390259 (_69865 : int) (_69866 : int) (_69867 : int) : (term1084 _69865 _69866 _69867) = (term1085 _69865 _69866 _69867).
Proof. exact (@lem1982755 (real_of_int _69865) (term140 _69867) (term225 _69866 _69867)). Qed.
Lemma lem5390260 (_69866 : int) (_69867 : int) : (term1086 _69866 _69867) = (term1087 _69866 _69867).
Proof. exact (@lem1982757 (term228 _69866) (term140 _69867) (term228 _69867)). Qed.
Lemma lem5390261 (_69867 : int) : (term1088 _69867) = (term1089 _69867).
Proof. exact (@lem1982759 (real_of_int _69867) (term228 _69867) term138). Qed.
Lemma lem5390262 (_69867 : int) : (term464 _69867) = (term418 _69867).
Proof. exact (@lem1982715 term201 (real_of_int _69867)). Qed.
Lemma lem5390264 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5390265 : term138 = term237.
Proof. exact (@lem5390264 term44). Qed.
Lemma lem5390267 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5390268 : term201 = term202.
Proof. exact (@lem5390267 term44). Qed.
Lemma lem5390269 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5390270 : term419 = term420.
Proof. exact (MK_COMB (@lem5390269) (@lem5390268)). Qed.
Lemma lem5390271 : term421 = term422.
Proof. exact (MK_COMB (@lem5390270) (@lem5390265)). Qed.
Lemma lem5390272 : term423.
Proof. exact (@lem1981473 term201 term138 term138 term138 term128 term138). Qed.
Lemma lem5390274 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5390275 : term245 = term246.
Proof. exact (@lem5390274 (NUMERAL 0) term44). Qed.
Lemma lem5390276 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5390277 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5390278 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5390277 h1) (fun h1 : term246 = True => @lem5390276)). Qed.
Lemma lem5390279 : term246 = True.
Proof. exact (EQ_MP (@lem5390278) (@lem5390276)). Qed.
Lemma lem5390280 : term245 = True.
Proof. exact (TRANS (@lem5390275) (@lem5390279)). Qed.
Lemma lem5390281 : True = term245.
Proof. exact (SYM (@lem5390280)). Qed.
Lemma lem5390282 : term245.
Proof. exact (EQ_MP (@lem5390281) (@lem0)). Qed.
Lemma lem5390283 : term424.
Proof. exact (@lem5390272 (@lem5390282)). Qed.
Lemma lem5390285 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5390286 : term245 = term246.
Proof. exact (@lem5390285 (NUMERAL 0) term44). Qed.
Lemma lem5390287 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5390288 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5390289 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5390288 h1) (fun h1 : term246 = True => @lem5390287)). Qed.
Lemma lem5390290 : term246 = True.
Proof. exact (EQ_MP (@lem5390289) (@lem5390287)). Qed.
Lemma lem5390291 : term245 = True.
Proof. exact (TRANS (@lem5390286) (@lem5390290)). Qed.
Lemma lem5390292 : True = term245.
Proof. exact (SYM (@lem5390291)). Qed.
Lemma lem5390293 : term245.
Proof. exact (EQ_MP (@lem5390292) (@lem0)). Qed.
Lemma lem5390294 : term425.
Proof. exact (@lem5390283 (@lem5390293)). Qed.
Lemma lem5390296 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5390297 : term245 = term246.
Proof. exact (@lem5390296 (NUMERAL 0) term44). Qed.
Lemma lem5390298 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5390299 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5390300 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5390299 h1) (fun h1 : term246 = True => @lem5390298)). Qed.
Lemma lem5390301 : term246 = True.
Proof. exact (EQ_MP (@lem5390300) (@lem5390298)). Qed.
Lemma lem5390302 : term245 = True.
Proof. exact (TRANS (@lem5390297) (@lem5390301)). Qed.
Lemma lem5390303 : True = term245.
Proof. exact (SYM (@lem5390302)). Qed.
Lemma lem5390304 : term245.
Proof. exact (EQ_MP (@lem5390303) (@lem0)). Qed.
Lemma lem5390305 : term426.
Proof. exact (@lem5390294 (@lem5390304)). Qed.
Lemma lem5390307 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5390308 : term210 = term211.
Proof. exact (@lem5390307 term44 term44). Qed.
Lemma lem5390309 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5390310 : term213 = term44.
Proof. exact (EQ_MP (@lem5390309) (@lem940073)). Qed.
Lemma lem5390311 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5390312 : term211 = term138.
Proof. exact (MK_COMB (@lem5390311) (@lem5390310)). Qed.
Lemma lem5390313 : term210 = term138.
Proof. exact (TRANS (@lem5390308) (@lem5390312)). Qed.
Lemma lem5390315 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5390316 : term302 = term305.
Proof. exact (@lem5390315 term44 term44). Qed.
Lemma lem5390317 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5390318 : term213 = term44.
Proof. exact (EQ_MP (@lem5390317) (@lem940073)). Qed.
Lemma lem5390319 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5390320 : term211 = term138.
Proof. exact (MK_COMB (@lem5390319) (@lem5390318)). Qed.
Lemma lem5390321 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5390322 : term305 = term201.
Proof. exact (MK_COMB (@lem5390321) (@lem5390320)). Qed.
Lemma lem5390323 : term302 = term201.
Proof. exact (TRANS (@lem5390316) (@lem5390322)). Qed.
Lemma lem5390324 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5390325 : term427 = term419.
Proof. exact (MK_COMB (@lem5390324) (@lem5390323)). Qed.
Lemma lem5390326 : term428 = term421.
Proof. exact (MK_COMB (@lem5390325) (@lem5390313)). Qed.
Lemma lem5390328 (m : nat) : (term429 m) = term128.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5390329 : term421 = term128.
Proof. exact (@lem5390328 term44). Qed.
Lemma lem5390330 : term428 = term128.
Proof. exact (TRANS (@lem5390326) (@lem5390329)). Qed.
Lemma lem5390331 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5390332 : term430 = term431.
Proof. exact (MK_COMB (@lem5390331) (@lem5390330)). Qed.
Lemma lem5390333 : term138 = term138.
Proof. exact (eq_refl term138). Qed.
Lemma lem5390334 : term432 = term398.
Proof. exact (MK_COMB (@lem5390332) (@lem5390333)). Qed.
Lemma lem5390336 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5390337 : term398 = term128.
Proof. exact (@lem5390336 term44). Qed.
Lemma lem5390338 : term432 = term128.
Proof. exact (TRANS (@lem5390334) (@lem5390337)). Qed.
Lemma lem5390340 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5390341 : term210 = term211.
Proof. exact (@lem5390340 term44 term44). Qed.
Lemma lem5390342 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5390343 : term213 = term44.
Proof. exact (EQ_MP (@lem5390342) (@lem940073)). Qed.
Lemma lem5390344 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5390345 : term211 = term138.
Proof. exact (MK_COMB (@lem5390344) (@lem5390343)). Qed.
Lemma lem5390346 : term210 = term138.
Proof. exact (TRANS (@lem5390341) (@lem5390345)). Qed.
Lemma lem5390347 : term431 = term431.
Proof. exact (eq_refl term431). Qed.
Lemma lem5390348 : term433 = term398.
Proof. exact (MK_COMB (@lem5390347) (@lem5390346)). Qed.
Lemma lem5390350 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5390351 : term398 = term128.
Proof. exact (@lem5390350 term44). Qed.
Lemma lem5390352 : term433 = term128.
Proof. exact (TRANS (@lem5390348) (@lem5390351)). Qed.
Lemma lem5390353 : term128 = term433.
Proof. exact (SYM (@lem5390352)). Qed.
Lemma lem5390354 : term432 = term433.
Proof. exact (TRANS (@lem5390338) (@lem5390353)). Qed.
Lemma lem5390355 : term422 = term198.
Proof. exact (@lem5390305 (@lem5390354)). Qed.
Lemma lem5390356 : term421 = term198.
Proof. exact (TRANS (@lem5390271) (@lem5390355)). Qed.
Lemma lem5390358 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5390359 : term198 = term128.
Proof. exact (@lem5390358 term128). Qed.
Lemma lem5390360 : term421 = term128.
Proof. exact (TRANS (@lem5390356) (@lem5390359)). Qed.
Lemma lem5390361 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5390362 : term434 = term431.
Proof. exact (MK_COMB (@lem5390361) (@lem5390360)). Qed.
Lemma lem5390363 (_69867 : int) : (real_of_int _69867) = (real_of_int _69867).
Proof. exact (eq_refl (real_of_int _69867)). Qed.
Lemma lem5390364 (_69867 : int) : (term418 _69867) = (term435 _69867).
Proof. exact (MK_COMB (@lem5390362) (@lem5390363 _69867)). Qed.
Lemma lem5390365 (_69867 : int) : (term464 _69867) = (term435 _69867).
Proof. exact (TRANS (@lem5390262 _69867) (@lem5390364 _69867)). Qed.
Lemma lem5390366 (_69867 : int) : (term435 _69867) = term128.
Proof. exact (@lem1982719 (real_of_int _69867)). Qed.
Lemma lem5390367 (_69867 : int) : (term464 _69867) = term128.
Proof. exact (TRANS (@lem5390365 _69867) (@lem5390366 _69867)). Qed.
Lemma lem5390368 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5390369 (_69867 : int) : (term465 _69867) = term178.
Proof. exact (MK_COMB (@lem5390368) (@lem5390367 _69867)). Qed.
Lemma lem5390370 : term138 = term138.
Proof. exact (eq_refl term138). Qed.
Lemma lem5390371 (_69867 : int) : (term1089 _69867) = term179.
Proof. exact (MK_COMB (@lem5390369 _69867) (@lem5390370)). Qed.
Lemma lem5390372 (_69867 : int) : (term1088 _69867) = term179.
Proof. exact (TRANS (@lem5390261 _69867) (@lem5390371 _69867)). Qed.
Lemma lem5390373 : term179 = term138.
Proof. exact (@lem1982721 term138). Qed.
Lemma lem5390374 (_69867 : int) : (term1088 _69867) = term138.
Proof. exact (TRANS (@lem5390372 _69867) (@lem5390373)). Qed.
Lemma lem5390375 (_69866 : int) : (term231 _69866) = (term231 _69866).
Proof. exact (eq_refl (term231 _69866)). Qed.
Lemma lem5390376 (_69867 : int) (_69866 : int) : (term1087 _69866 _69867) = (term1090 _69866).
Proof. exact (MK_COMB (@lem5390375 _69866) (@lem5390374 _69867)). Qed.
Lemma lem5390377 (_69867 : int) (_69866 : int) : (term1086 _69866 _69867) = (term1090 _69866).
Proof. exact (TRANS (@lem5390260 _69866 _69867) (@lem5390376 _69867 _69866)). Qed.
Lemma lem5390378 (_69865 : int) : (term139 _69865) = (term139 _69865).
Proof. exact (eq_refl (term139 _69865)). Qed.
Lemma lem5390379 (_69867 : int) (_69865 : int) (_69866 : int) : (term1085 _69865 _69866 _69867) = (term1091 _69865 _69866).
Proof. exact (MK_COMB (@lem5390378 _69865) (@lem5390377 _69867 _69866)). Qed.
Lemma lem5390380 (_69867 : int) (_69865 : int) (_69866 : int) : (term1084 _69865 _69866 _69867) = (term1091 _69865 _69866).
Proof. exact (TRANS (@lem5390259 _69865 _69866 _69867) (@lem5390379 _69867 _69865 _69866)). Qed.
Lemma lem5390381 (_69867 : int) (_69865 : int) (_69866 : int) : (term1083 _69865 _69866 _69867) = (term1091 _69865 _69866).
Proof. exact (TRANS (@lem5390258 _69865 _69866 _69867) (@lem5390380 _69867 _69865 _69866)). Qed.
Lemma lem5390383 (_69867 : int) (_69865 : int) (_69866 : int) : (term1082 _69865 _69866 _69867) = (term1091 _69865 _69866).
Proof. exact (TRANS (@lem5390249 _69865 _69866 _69867) (@lem5390381 _69867 _69865 _69866)). Qed.
Lemma lem5390384 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5390385 (_69867 : int) (_69865 : int) (_69866 : int) : (term1092 _69865 _69866 _69867) = (term1093 _69865 _69866).
Proof. exact (MK_COMB (@lem5390384) (@lem5390383 _69867 _69865 _69866)). Qed.
Lemma lem5390386 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5390387 (_69867 : int) (_69865 : int) (_69866 : int) : ((term1082 _69865 _69866 _69867) = term128) = ((term1091 _69865 _69866) = term128).
Proof. exact (MK_COMB (@lem5390385 _69867 _69865 _69866) (@lem5390386)). Qed.
Lemma lem5390388 (_69867 : int) (_69865 : int) (_69866 : int) : ((term1051 _69865 _69867) = (term134 _69866 _69867)) = ((term1091 _69865 _69866) = term128).
Proof. exact (TRANS (@lem5390225 _69865 _69866 _69867) (@lem5390387 _69867 _69865 _69866)). Qed.
Lemma lem5390389 (_69865 : int) (_69867 : int) : (term1064 _69865 _69867) = (term1094 _69865 _69867).
Proof. exact (@lem1988287 (real_of_int _69867) (term1061 _69865 _69867)). Qed.
Lemma lem5390407 (_69865 : int) (_69867 : int) : (term1061 _69865 _69867) = (term1095 _69865 _69867).
Proof. exact (@lem1982755 (real_of_int _69865) (term140 _69867) term138). Qed.
Lemma lem5390408 (_69867 : int) : (term151 _69867) = (term236 _69867).
Proof. exact (@lem1982755 (real_of_int _69867) term138 term138). Qed.
Lemma lem5390410 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5390411 : term138 = term237.
Proof. exact (@lem5390410 term44). Qed.
Lemma lem5390413 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5390414 : term138 = term237.
Proof. exact (@lem5390413 term44). Qed.
Lemma lem5390415 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5390416 : term238 = term239.
Proof. exact (MK_COMB (@lem5390415) (@lem5390414)). Qed.
Lemma lem5390417 : term240 = term241.
Proof. exact (MK_COMB (@lem5390416) (@lem5390411)). Qed.
Lemma lem5390418 : term242.
Proof. exact (@lem1981473 term138 term138 term138 term138 term243 term138). Qed.
Lemma lem5390420 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5390421 : term245 = term246.
Proof. exact (@lem5390420 (NUMERAL 0) term44). Qed.
Lemma lem5390422 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5390423 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5390424 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5390423 h1) (fun h1 : term246 = True => @lem5390422)). Qed.
Lemma lem5390425 : term246 = True.
Proof. exact (EQ_MP (@lem5390424) (@lem5390422)). Qed.
Lemma lem5390426 : term245 = True.
Proof. exact (TRANS (@lem5390421) (@lem5390425)). Qed.
Lemma lem5390427 : True = term245.
Proof. exact (SYM (@lem5390426)). Qed.
Lemma lem5390428 : term245.
Proof. exact (EQ_MP (@lem5390427) (@lem0)). Qed.
Lemma lem5390429 : term248.
Proof. exact (@lem5390418 (@lem5390428)). Qed.
Lemma lem5390431 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5390432 : term245 = term246.
Proof. exact (@lem5390431 (NUMERAL 0) term44). Qed.
Lemma lem5390433 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5390434 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5390435 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5390434 h1) (fun h1 : term246 = True => @lem5390433)). Qed.
Lemma lem5390436 : term246 = True.
Proof. exact (EQ_MP (@lem5390435) (@lem5390433)). Qed.
Lemma lem5390437 : term245 = True.
Proof. exact (TRANS (@lem5390432) (@lem5390436)). Qed.
Lemma lem5390438 : True = term245.
Proof. exact (SYM (@lem5390437)). Qed.
Lemma lem5390439 : term245.
Proof. exact (EQ_MP (@lem5390438) (@lem0)). Qed.
Lemma lem5390440 : term249.
Proof. exact (@lem5390429 (@lem5390439)). Qed.
Lemma lem5390442 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5390443 : term245 = term246.
Proof. exact (@lem5390442 (NUMERAL 0) term44). Qed.
Lemma lem5390444 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5390445 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5390446 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5390445 h1) (fun h1 : term246 = True => @lem5390444)). Qed.
Lemma lem5390447 : term246 = True.
Proof. exact (EQ_MP (@lem5390446) (@lem5390444)). Qed.
Lemma lem5390448 : term245 = True.
Proof. exact (TRANS (@lem5390443) (@lem5390447)). Qed.
Lemma lem5390449 : True = term245.
Proof. exact (SYM (@lem5390448)). Qed.
Lemma lem5390450 : term245.
Proof. exact (EQ_MP (@lem5390449) (@lem0)). Qed.
Lemma lem5390451 : term250.
Proof. exact (@lem5390440 (@lem5390450)). Qed.
Lemma lem5390453 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5390454 : term210 = term211.
Proof. exact (@lem5390453 term44 term44). Qed.
Lemma lem5390455 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5390456 : term213 = term44.
Proof. exact (EQ_MP (@lem5390455) (@lem940073)). Qed.
Lemma lem5390457 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5390458 : term211 = term138.
Proof. exact (MK_COMB (@lem5390457) (@lem5390456)). Qed.
Lemma lem5390459 : term210 = term138.
Proof. exact (TRANS (@lem5390454) (@lem5390458)). Qed.
Lemma lem5390461 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5390462 : term210 = term211.
Proof. exact (@lem5390461 term44 term44). Qed.
Lemma lem5390463 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5390464 : term213 = term44.
Proof. exact (EQ_MP (@lem5390463) (@lem940073)). Qed.
Lemma lem5390465 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5390466 : term211 = term138.
Proof. exact (MK_COMB (@lem5390465) (@lem5390464)). Qed.
Lemma lem5390467 : term210 = term138.
Proof. exact (TRANS (@lem5390462) (@lem5390466)). Qed.
Lemma lem5390468 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5390469 : term251 = term238.
Proof. exact (MK_COMB (@lem5390468) (@lem5390467)). Qed.
Lemma lem5390470 : term252 = term240.
Proof. exact (MK_COMB (@lem5390469) (@lem5390459)). Qed.
Lemma lem5390471 : term240 = term253.
Proof. exact (@lem1367770 term44 term44). Qed.
Lemma lem5390472 : term254 = term255.
Proof. exact (@lem706885). Qed.
Lemma lem5390473 : (term254 = term255) = (term256 = term257).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term255). Qed.
Lemma lem5390474 : term256 = term257.
Proof. exact (EQ_MP (@lem5390473) (@lem5390472)). Qed.
Lemma lem5390475 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5390476 : term253 = term243.
Proof. exact (MK_COMB (@lem5390475) (@lem5390474)). Qed.
Lemma lem5390477 : term240 = term243.
Proof. exact (TRANS (@lem5390471) (@lem5390476)). Qed.
Lemma lem5390478 : term252 = term243.
Proof. exact (TRANS (@lem5390470) (@lem5390477)). Qed.
Lemma lem5390479 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5390480 : term258 = term259.
Proof. exact (MK_COMB (@lem5390479) (@lem5390478)). Qed.
Lemma lem5390481 : term138 = term138.
Proof. exact (eq_refl term138). Qed.
Lemma lem5390482 : term260 = term261.
Proof. exact (MK_COMB (@lem5390480) (@lem5390481)). Qed.
Lemma lem5390484 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5390485 : term261 = term262.
Proof. exact (@lem5390484 term257 term44). Qed.
Lemma lem5390486 : term263 = term255.
Proof. exact (@lem996237 term255). Qed.
Lemma lem5390487 : (term263 = term255) = (term264 = term257).
Proof. exact (@lem1007663 term255 (BIT1 0) term255). Qed.
Lemma lem5390488 : term264 = term257.
Proof. exact (EQ_MP (@lem5390487) (@lem5390486)). Qed.
Lemma lem5390489 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5390490 : term262 = term243.
Proof. exact (MK_COMB (@lem5390489) (@lem5390488)). Qed.
Lemma lem5390491 : term261 = term243.
Proof. exact (TRANS (@lem5390485) (@lem5390490)). Qed.
Lemma lem5390492 : term260 = term243.
Proof. exact (TRANS (@lem5390482) (@lem5390491)). Qed.
Lemma lem5390494 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5390495 : term210 = term211.
Proof. exact (@lem5390494 term44 term44). Qed.
Lemma lem5390496 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5390497 : term213 = term44.
Proof. exact (EQ_MP (@lem5390496) (@lem940073)). Qed.
Lemma lem5390498 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5390499 : term211 = term138.
Proof. exact (MK_COMB (@lem5390498) (@lem5390497)). Qed.
Lemma lem5390500 : term210 = term138.
Proof. exact (TRANS (@lem5390495) (@lem5390499)). Qed.
Lemma lem5390501 : term259 = term259.
Proof. exact (eq_refl term259). Qed.
Lemma lem5390502 : term265 = term261.
Proof. exact (MK_COMB (@lem5390501) (@lem5390500)). Qed.
Lemma lem5390504 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5390505 : term261 = term262.
Proof. exact (@lem5390504 term257 term44). Qed.
Lemma lem5390506 : term263 = term255.
Proof. exact (@lem996237 term255). Qed.
Lemma lem5390507 : (term263 = term255) = (term264 = term257).
Proof. exact (@lem1007663 term255 (BIT1 0) term255). Qed.
Lemma lem5390508 : term264 = term257.
Proof. exact (EQ_MP (@lem5390507) (@lem5390506)). Qed.
Lemma lem5390509 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5390510 : term262 = term243.
Proof. exact (MK_COMB (@lem5390509) (@lem5390508)). Qed.
Lemma lem5390511 : term261 = term243.
Proof. exact (TRANS (@lem5390505) (@lem5390510)). Qed.
Lemma lem5390512 : term265 = term243.
Proof. exact (TRANS (@lem5390502) (@lem5390511)). Qed.
Lemma lem5390513 : term243 = term265.
Proof. exact (SYM (@lem5390512)). Qed.
Lemma lem5390514 : term260 = term265.
Proof. exact (TRANS (@lem5390492) (@lem5390513)). Qed.
Lemma lem5390515 : term241 = term266.
Proof. exact (@lem5390451 (@lem5390514)). Qed.
Lemma lem5390516 : term240 = term266.
Proof. exact (TRANS (@lem5390417) (@lem5390515)). Qed.
Lemma lem5390518 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5390519 : term266 = term243.
Proof. exact (@lem5390518 term243). Qed.
Lemma lem5390520 : term240 = term243.
Proof. exact (TRANS (@lem5390516) (@lem5390519)). Qed.
Lemma lem5390521 (_69867 : int) : (term139 _69867) = (term139 _69867).
Proof. exact (eq_refl (term139 _69867)). Qed.
Lemma lem5390522 (_69867 : int) : (term236 _69867) = (term267 _69867).
Proof. exact (MK_COMB (@lem5390521 _69867) (@lem5390520)). Qed.
Lemma lem5390523 (_69867 : int) : (term151 _69867) = (term267 _69867).
Proof. exact (TRANS (@lem5390408 _69867) (@lem5390522 _69867)). Qed.
Lemma lem5390524 (_69865 : int) : (term139 _69865) = (term139 _69865).
Proof. exact (eq_refl (term139 _69865)). Qed.
Lemma lem5390525 (_69865 : int) (_69867 : int) : (term1095 _69865 _69867) = (term1096 _69865 _69867).
Proof. exact (MK_COMB (@lem5390524 _69865) (@lem5390523 _69867)). Qed.
Lemma lem5390527 (_69865 : int) (_69867 : int) : (term1061 _69865 _69867) = (term1096 _69865 _69867).
Proof. exact (TRANS (@lem5390407 _69865 _69867) (@lem5390525 _69865 _69867)). Qed.
Lemma lem5390530 (_69867 : int) : (term268 _69867) = (term268 _69867).
Proof. exact (eq_refl (term268 _69867)). Qed.
Lemma lem5390531 (_69865 : int) (_69867 : int) : (term1097 _69865 _69867) = (term1098 _69865 _69867).
Proof. exact (MK_COMB (@lem5390530 _69867) (@lem5390527 _69865 _69867)). Qed.
Lemma lem5390532 (_69865 : int) (_69867 : int) : (term1098 _69865 _69867) = (term1099 _69865 _69867).
Proof. exact (@lem1982792 (real_of_int _69867) (term1096 _69865 _69867)). Qed.
Lemma lem5390533 (_69865 : int) (_69867 : int) : (term1100 _69865 _69867) = (term1101 _69865 _69867).
Proof. exact (@lem1982781 (real_of_int _69865) term201 (term267 _69867)). Qed.
Lemma lem5390534 (_69867 : int) : (term272 _69867) = (term273 _69867).
Proof. exact (@lem1982781 (real_of_int _69867) term201 term243). Qed.
Lemma lem5390536 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5390537 : term243 = term266.
Proof. exact (@lem5390536 term257). Qed.
Lemma lem5390539 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5390540 : term201 = term202.
Proof. exact (@lem5390539 term44). Qed.
Lemma lem5390541 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5390542 : term203 = term204.
Proof. exact (MK_COMB (@lem5390541) (@lem5390540)). Qed.
Lemma lem5390543 : term274 = term275.
Proof. exact (MK_COMB (@lem5390542) (@lem5390537)). Qed.
Lemma lem5390544 : term275 = term276.
Proof. exact (@lem1981613 term201 term243 term138 term138). Qed.
Lemma lem5390546 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5390547 : term210 = term211.
Proof. exact (@lem5390546 term44 term44). Qed.
Lemma lem5390548 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5390549 : term213 = term44.
Proof. exact (EQ_MP (@lem5390548) (@lem940073)). Qed.
Lemma lem5390550 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5390551 : term211 = term138.
Proof. exact (MK_COMB (@lem5390550) (@lem5390549)). Qed.
Lemma lem5390552 : term210 = term138.
Proof. exact (TRANS (@lem5390547) (@lem5390551)). Qed.
Lemma lem5390554 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5390555 : term274 = term279.
Proof. exact (@lem5390554 term44 term257). Qed.
Lemma lem5390556 : term280 = term255.
Proof. exact (@lem996238 term255). Qed.
Lemma lem5390557 : (term280 = term255) = (term281 = term257).
Proof. exact (@lem1007663 (BIT1 0) term255 term255). Qed.
Lemma lem5390558 : term281 = term257.
Proof. exact (EQ_MP (@lem5390557) (@lem5390556)). Qed.
Lemma lem5390559 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5390560 : term282 = term243.
Proof. exact (MK_COMB (@lem5390559) (@lem5390558)). Qed.
Lemma lem5390561 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5390562 : term279 = term283.
Proof. exact (MK_COMB (@lem5390561) (@lem5390560)). Qed.
Lemma lem5390563 : term274 = term283.
Proof. exact (TRANS (@lem5390555) (@lem5390562)). Qed.
Lemma lem5390564 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5390565 : term284 = term285.
Proof. exact (MK_COMB (@lem5390564) (@lem5390563)). Qed.
Lemma lem5390566 : term276 = term286.
Proof. exact (MK_COMB (@lem5390565) (@lem5390552)). Qed.
Lemma lem5390567 : term275 = term286.
Proof. exact (TRANS (@lem5390544) (@lem5390566)). Qed.
Lemma lem5390568 : term274 = term286.
Proof. exact (TRANS (@lem5390543) (@lem5390567)). Qed.
Lemma lem5390570 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5390571 : term286 = term283.
Proof. exact (@lem5390570 term283). Qed.
Lemma lem5390572 : term274 = term283.
Proof. exact (TRANS (@lem5390568) (@lem5390571)). Qed.
Lemma lem5390575 (_69867 : int) : (term231 _69867) = (term231 _69867).
Proof. exact (eq_refl (term231 _69867)). Qed.
Lemma lem5390576 (_69867 : int) : (term273 _69867) = (term287 _69867).
Proof. exact (MK_COMB (@lem5390575 _69867) (@lem5390572)). Qed.
Lemma lem5390577 (_69867 : int) : (term272 _69867) = (term287 _69867).
Proof. exact (TRANS (@lem5390534 _69867) (@lem5390576 _69867)). Qed.
Lemma lem5390580 (_69865 : int) : (term231 _69865) = (term231 _69865).
Proof. exact (eq_refl (term231 _69865)). Qed.
Lemma lem5390581 (_69865 : int) (_69867 : int) : (term1101 _69865 _69867) = (term1102 _69865 _69867).
Proof. exact (MK_COMB (@lem5390580 _69865) (@lem5390577 _69867)). Qed.
Lemma lem5390582 (_69865 : int) (_69867 : int) : (term1100 _69865 _69867) = (term1102 _69865 _69867).
Proof. exact (TRANS (@lem5390533 _69865 _69867) (@lem5390581 _69865 _69867)). Qed.
Lemma lem5390583 (_69867 : int) : (term139 _69867) = (term139 _69867).
Proof. exact (eq_refl (term139 _69867)). Qed.
Lemma lem5390584 (_69865 : int) (_69867 : int) : (term1099 _69865 _69867) = (term1103 _69865 _69867).
Proof. exact (MK_COMB (@lem5390583 _69867) (@lem5390582 _69865 _69867)). Qed.
Lemma lem5390585 (_69865 : int) (_69867 : int) : (term1103 _69865 _69867) = (term1104 _69865 _69867).
Proof. exact (@lem1982757 (term228 _69865) (real_of_int _69867) (term287 _69867)). Qed.
Lemma lem5390586 (_69867 : int) : (term1105 _69867) = (term1106 _69867).
Proof. exact (@lem1982763 (real_of_int _69867) (term228 _69867) term283). Qed.
Lemma lem5390587 (_69867 : int) : (term464 _69867) = (term418 _69867).
Proof. exact (@lem1982715 term201 (real_of_int _69867)). Qed.
Lemma lem5390589 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5390590 : term138 = term237.
Proof. exact (@lem5390589 term44). Qed.
Lemma lem5390592 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5390593 : term201 = term202.
Proof. exact (@lem5390592 term44). Qed.
Lemma lem5390594 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5390595 : term419 = term420.
Proof. exact (MK_COMB (@lem5390594) (@lem5390593)). Qed.
Lemma lem5390596 : term421 = term422.
Proof. exact (MK_COMB (@lem5390595) (@lem5390590)). Qed.
Lemma lem5390597 : term423.
Proof. exact (@lem1981473 term201 term138 term138 term138 term128 term138). Qed.
Lemma lem5390599 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5390600 : term245 = term246.
Proof. exact (@lem5390599 (NUMERAL 0) term44). Qed.
Lemma lem5390601 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5390602 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5390603 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5390602 h1) (fun h1 : term246 = True => @lem5390601)). Qed.
Lemma lem5390604 : term246 = True.
Proof. exact (EQ_MP (@lem5390603) (@lem5390601)). Qed.
Lemma lem5390605 : term245 = True.
Proof. exact (TRANS (@lem5390600) (@lem5390604)). Qed.
Lemma lem5390606 : True = term245.
Proof. exact (SYM (@lem5390605)). Qed.
Lemma lem5390607 : term245.
Proof. exact (EQ_MP (@lem5390606) (@lem0)). Qed.
Lemma lem5390608 : term424.
Proof. exact (@lem5390597 (@lem5390607)). Qed.
Lemma lem5390610 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5390611 : term245 = term246.
Proof. exact (@lem5390610 (NUMERAL 0) term44). Qed.
Lemma lem5390612 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5390613 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5390614 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5390613 h1) (fun h1 : term246 = True => @lem5390612)). Qed.
Lemma lem5390615 : term246 = True.
Proof. exact (EQ_MP (@lem5390614) (@lem5390612)). Qed.
Lemma lem5390616 : term245 = True.
Proof. exact (TRANS (@lem5390611) (@lem5390615)). Qed.
Lemma lem5390617 : True = term245.
Proof. exact (SYM (@lem5390616)). Qed.
Lemma lem5390618 : term245.
Proof. exact (EQ_MP (@lem5390617) (@lem0)). Qed.
Lemma lem5390619 : term425.
Proof. exact (@lem5390608 (@lem5390618)). Qed.
Lemma lem5390621 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5390622 : term245 = term246.
Proof. exact (@lem5390621 (NUMERAL 0) term44). Qed.
Lemma lem5390623 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5390624 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5390625 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5390624 h1) (fun h1 : term246 = True => @lem5390623)). Qed.
Lemma lem5390626 : term246 = True.
Proof. exact (EQ_MP (@lem5390625) (@lem5390623)). Qed.
Lemma lem5390627 : term245 = True.
Proof. exact (TRANS (@lem5390622) (@lem5390626)). Qed.
Lemma lem5390628 : True = term245.
Proof. exact (SYM (@lem5390627)). Qed.
Lemma lem5390629 : term245.
Proof. exact (EQ_MP (@lem5390628) (@lem0)). Qed.
Lemma lem5390630 : term426.
Proof. exact (@lem5390619 (@lem5390629)). Qed.
Lemma lem5390632 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5390633 : term210 = term211.
Proof. exact (@lem5390632 term44 term44). Qed.
Lemma lem5390634 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5390635 : term213 = term44.
Proof. exact (EQ_MP (@lem5390634) (@lem940073)). Qed.
Lemma lem5390636 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5390637 : term211 = term138.
Proof. exact (MK_COMB (@lem5390636) (@lem5390635)). Qed.
Lemma lem5390638 : term210 = term138.
Proof. exact (TRANS (@lem5390633) (@lem5390637)). Qed.
Lemma lem5390640 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5390641 : term302 = term305.
Proof. exact (@lem5390640 term44 term44). Qed.
Lemma lem5390642 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5390643 : term213 = term44.
Proof. exact (EQ_MP (@lem5390642) (@lem940073)). Qed.
Lemma lem5390644 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5390645 : term211 = term138.
Proof. exact (MK_COMB (@lem5390644) (@lem5390643)). Qed.
Lemma lem5390646 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5390647 : term305 = term201.
Proof. exact (MK_COMB (@lem5390646) (@lem5390645)). Qed.
Lemma lem5390648 : term302 = term201.
Proof. exact (TRANS (@lem5390641) (@lem5390647)). Qed.
Lemma lem5390649 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5390650 : term427 = term419.
Proof. exact (MK_COMB (@lem5390649) (@lem5390648)). Qed.
Lemma lem5390651 : term428 = term421.
Proof. exact (MK_COMB (@lem5390650) (@lem5390638)). Qed.
Lemma lem5390653 (m : nat) : (term429 m) = term128.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5390654 : term421 = term128.
Proof. exact (@lem5390653 term44). Qed.
Lemma lem5390655 : term428 = term128.
Proof. exact (TRANS (@lem5390651) (@lem5390654)). Qed.
Lemma lem5390656 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5390657 : term430 = term431.
Proof. exact (MK_COMB (@lem5390656) (@lem5390655)). Qed.
Lemma lem5390658 : term138 = term138.
Proof. exact (eq_refl term138). Qed.
Lemma lem5390659 : term432 = term398.
Proof. exact (MK_COMB (@lem5390657) (@lem5390658)). Qed.
Lemma lem5390661 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5390662 : term398 = term128.
Proof. exact (@lem5390661 term44). Qed.
Lemma lem5390663 : term432 = term128.
Proof. exact (TRANS (@lem5390659) (@lem5390662)). Qed.
Lemma lem5390665 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5390666 : term210 = term211.
Proof. exact (@lem5390665 term44 term44). Qed.
Lemma lem5390667 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5390668 : term213 = term44.
Proof. exact (EQ_MP (@lem5390667) (@lem940073)). Qed.
Lemma lem5390669 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5390670 : term211 = term138.
Proof. exact (MK_COMB (@lem5390669) (@lem5390668)). Qed.
Lemma lem5390671 : term210 = term138.
Proof. exact (TRANS (@lem5390666) (@lem5390670)). Qed.
Lemma lem5390672 : term431 = term431.
Proof. exact (eq_refl term431). Qed.
Lemma lem5390673 : term433 = term398.
Proof. exact (MK_COMB (@lem5390672) (@lem5390671)). Qed.
Lemma lem5390675 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5390676 : term398 = term128.
Proof. exact (@lem5390675 term44). Qed.
Lemma lem5390677 : term433 = term128.
Proof. exact (TRANS (@lem5390673) (@lem5390676)). Qed.
Lemma lem5390678 : term128 = term433.
Proof. exact (SYM (@lem5390677)). Qed.
Lemma lem5390679 : term432 = term433.
Proof. exact (TRANS (@lem5390663) (@lem5390678)). Qed.
Lemma lem5390680 : term422 = term198.
Proof. exact (@lem5390630 (@lem5390679)). Qed.
Lemma lem5390681 : term421 = term198.
Proof. exact (TRANS (@lem5390596) (@lem5390680)). Qed.
Lemma lem5390683 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5390684 : term198 = term128.
Proof. exact (@lem5390683 term128). Qed.
Lemma lem5390685 : term421 = term128.
Proof. exact (TRANS (@lem5390681) (@lem5390684)). Qed.
Lemma lem5390686 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5390687 : term434 = term431.
Proof. exact (MK_COMB (@lem5390686) (@lem5390685)). Qed.
Lemma lem5390688 (_69867 : int) : (real_of_int _69867) = (real_of_int _69867).
Proof. exact (eq_refl (real_of_int _69867)). Qed.
Lemma lem5390689 (_69867 : int) : (term418 _69867) = (term435 _69867).
Proof. exact (MK_COMB (@lem5390687) (@lem5390688 _69867)). Qed.
Lemma lem5390690 (_69867 : int) : (term464 _69867) = (term435 _69867).
Proof. exact (TRANS (@lem5390587 _69867) (@lem5390689 _69867)). Qed.
Lemma lem5390691 (_69867 : int) : (term435 _69867) = term128.
Proof. exact (@lem1982719 (real_of_int _69867)). Qed.
Lemma lem5390692 (_69867 : int) : (term464 _69867) = term128.
Proof. exact (TRANS (@lem5390690 _69867) (@lem5390691 _69867)). Qed.
Lemma lem5390693 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5390694 (_69867 : int) : (term465 _69867) = term178.
Proof. exact (MK_COMB (@lem5390693) (@lem5390692 _69867)). Qed.
Lemma lem5390695 : term283 = term283.
Proof. exact (eq_refl term283). Qed.
Lemma lem5390696 (_69867 : int) : (term1106 _69867) = term1107.
Proof. exact (MK_COMB (@lem5390694 _69867) (@lem5390695)). Qed.
Lemma lem5390697 (_69867 : int) : (term1105 _69867) = term1107.
Proof. exact (TRANS (@lem5390586 _69867) (@lem5390696 _69867)). Qed.
Lemma lem5390698 : term1107 = term283.
Proof. exact (@lem1982721 term283). Qed.
Lemma lem5390699 (_69867 : int) : (term1105 _69867) = term283.
Proof. exact (TRANS (@lem5390697 _69867) (@lem5390698)). Qed.
Lemma lem5390700 (_69865 : int) : (term231 _69865) = (term231 _69865).
Proof. exact (eq_refl (term231 _69865)). Qed.
Lemma lem5390701 (_69867 : int) (_69865 : int) : (term1104 _69865 _69867) = (term287 _69865).
Proof. exact (MK_COMB (@lem5390700 _69865) (@lem5390699 _69867)). Qed.
Lemma lem5390702 (_69867 : int) (_69865 : int) : (term1103 _69865 _69867) = (term287 _69865).
Proof. exact (TRANS (@lem5390585 _69865 _69867) (@lem5390701 _69867 _69865)). Qed.
Lemma lem5390703 (_69867 : int) (_69865 : int) : (term1099 _69865 _69867) = (term287 _69865).
Proof. exact (TRANS (@lem5390584 _69865 _69867) (@lem5390702 _69867 _69865)). Qed.
Lemma lem5390704 (_69867 : int) (_69865 : int) : (term1098 _69865 _69867) = (term287 _69865).
Proof. exact (TRANS (@lem5390532 _69865 _69867) (@lem5390703 _69867 _69865)). Qed.
Lemma lem5390705 (_69867 : int) (_69865 : int) : (term1097 _69865 _69867) = (term287 _69865).
Proof. exact (TRANS (@lem5390531 _69865 _69867) (@lem5390704 _69867 _69865)). Qed.
Lemma lem5390706 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5390707 (_69867 : int) (_69865 : int) : (term1108 _69865 _69867) = (term1109 _69865).
Proof. exact (MK_COMB (@lem5390706) (@lem5390705 _69867 _69865)). Qed.
Lemma lem5390708 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5390709 (_69867 : int) (_69865 : int) : (term1094 _69865 _69867) = (term1110 _69865).
Proof. exact (MK_COMB (@lem5390707 _69867 _69865) (@lem5390708)). Qed.
Lemma lem5390710 (_69867 : int) (_69865 : int) : (term1064 _69865 _69867) = (term1110 _69865).
Proof. exact (TRANS (@lem5390389 _69865 _69867) (@lem5390709 _69867 _69865)). Qed.
Lemma lem5390711 (_69866 : int) : ((real_of_int _69866) = term128) = ((term195 _69866) = term128).
Proof. exact (@lem1988293 (real_of_int _69866) term128). Qed.
Lemma lem5390717 (_69866 : int) : (term195 _69866) = (term196 _69866).
Proof. exact (@lem1982792 (real_of_int _69866) term128). Qed.
Lemma lem5390719 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5390720 : term128 = term198.
Proof. exact (@lem5390719 (NUMERAL 0)). Qed.
Lemma lem5390722 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5390723 : term201 = term202.
Proof. exact (@lem5390722 term44). Qed.
Lemma lem5390724 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5390725 : term203 = term204.
Proof. exact (MK_COMB (@lem5390724) (@lem5390723)). Qed.
Lemma lem5390726 : term205 = term206.
Proof. exact (MK_COMB (@lem5390725) (@lem5390720)). Qed.
Lemma lem5390727 : term206 = term207.
Proof. exact (@lem1981613 term201 term128 term138 term138). Qed.
Lemma lem5390729 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5390730 : term210 = term211.
Proof. exact (@lem5390729 term44 term44). Qed.
Lemma lem5390731 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5390732 : term213 = term44.
Proof. exact (EQ_MP (@lem5390731) (@lem940073)). Qed.
Lemma lem5390733 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5390734 : term211 = term138.
Proof. exact (MK_COMB (@lem5390733) (@lem5390732)). Qed.
Lemma lem5390735 : term210 = term138.
Proof. exact (TRANS (@lem5390730) (@lem5390734)). Qed.
Lemma lem5390737 (x : nat) : (term214 x) = term128.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5390738 : term205 = term128.
Proof. exact (@lem5390737 term44). Qed.
Lemma lem5390739 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5390740 : term215 = term216.
Proof. exact (MK_COMB (@lem5390739) (@lem5390738)). Qed.
Lemma lem5390741 : term207 = term198.
Proof. exact (MK_COMB (@lem5390740) (@lem5390735)). Qed.
Lemma lem5390742 : term206 = term198.
Proof. exact (TRANS (@lem5390727) (@lem5390741)). Qed.
Lemma lem5390743 : term205 = term198.
Proof. exact (TRANS (@lem5390726) (@lem5390742)). Qed.
Lemma lem5390745 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5390746 : term198 = term128.
Proof. exact (@lem5390745 term128). Qed.
Lemma lem5390747 : term205 = term128.
Proof. exact (TRANS (@lem5390743) (@lem5390746)). Qed.
Lemma lem5390748 (_69866 : int) : (term139 _69866) = (term139 _69866).
Proof. exact (eq_refl (term139 _69866)). Qed.
Lemma lem5390749 (_69866 : int) : (term196 _69866) = (term218 _69866).
Proof. exact (MK_COMB (@lem5390748 _69866) (@lem5390747)). Qed.
Lemma lem5390750 (_69866 : int) : (term218 _69866) = (real_of_int _69866).
Proof. exact (@lem1982723 (real_of_int _69866)). Qed.
Lemma lem5390751 (_69866 : int) : (term196 _69866) = (real_of_int _69866).
Proof. exact (TRANS (@lem5390749 _69866) (@lem5390750 _69866)). Qed.
Lemma lem5390753 (_69866 : int) : (term195 _69866) = (real_of_int _69866).
Proof. exact (TRANS (@lem5390717 _69866) (@lem5390751 _69866)). Qed.
Lemma lem5390754 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5390755 (_69866 : int) : (term292 _69866) = (term155 _69866).
Proof. exact (MK_COMB (@lem5390754) (@lem5390753 _69866)). Qed.
Lemma lem5390756 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5390757 (_69866 : int) : ((term195 _69866) = term128) = ((real_of_int _69866) = term128).
Proof. exact (MK_COMB (@lem5390755 _69866) (@lem5390756)). Qed.
Lemma lem5390758 (_69866 : int) : ((real_of_int _69866) = term128) = ((real_of_int _69866) = term128).
Proof. exact (TRANS (@lem5390711 _69866) (@lem5390757 _69866)). Qed.
Lemma lem5390759 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5390760 (_69867 : int) (_69865 : int) : (term1065 _69865 _69867) = (term1111 _69865).
Proof. exact (MK_COMB (@lem5390759) (@lem5390710 _69867 _69865)). Qed.
Lemma lem5390761 (_69867 : int) (_69865 : int) (_69866 : int) : (term1066 _69865 _69867 _69866) = (term1112 _69865 _69866).
Proof. exact (MK_COMB (@lem5390760 _69867 _69865) (@lem5390758 _69866)). Qed.
Lemma lem5390762 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5390763 (_69867 : int) (_69865 : int) (_69866 : int) : (term1067 _69865 _69866 _69867) = (term1113 _69865 _69866).
Proof. exact (MK_COMB (@lem5390762) (@lem5390388 _69867 _69865 _69866)). Qed.
Lemma lem5390764 (_69867 : int) (_69865 : int) (_69866 : int) : (term1068 _69865 _69867 _69866) = (term1114 _69865 _69866).
Proof. exact (MK_COMB (@lem5390763 _69867 _69865 _69866) (@lem5390761 _69867 _69865 _69866)). Qed.
Lemma lem5390765 (_69866 : int) (_69865 : int) : (term154 _69865 _69866) = (term235 _69866 _69865).
Proof. exact (@lem1988287 (real_of_int _69866) (term151 _69865)). Qed.
Lemma lem5390777 (_69865 : int) : (term151 _69865) = (term236 _69865).
Proof. exact (@lem1982755 (real_of_int _69865) term138 term138). Qed.
Lemma lem5390779 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5390780 : term138 = term237.
Proof. exact (@lem5390779 term44). Qed.
Lemma lem5390782 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5390783 : term138 = term237.
Proof. exact (@lem5390782 term44). Qed.
Lemma lem5390784 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5390785 : term238 = term239.
Proof. exact (MK_COMB (@lem5390784) (@lem5390783)). Qed.
Lemma lem5390786 : term240 = term241.
Proof. exact (MK_COMB (@lem5390785) (@lem5390780)). Qed.
Lemma lem5390787 : term242.
Proof. exact (@lem1981473 term138 term138 term138 term138 term243 term138). Qed.
Lemma lem5390789 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5390790 : term245 = term246.
Proof. exact (@lem5390789 (NUMERAL 0) term44). Qed.
Lemma lem5390791 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5390792 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5390793 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5390792 h1) (fun h1 : term246 = True => @lem5390791)). Qed.
Lemma lem5390794 : term246 = True.
Proof. exact (EQ_MP (@lem5390793) (@lem5390791)). Qed.
Lemma lem5390795 : term245 = True.
Proof. exact (TRANS (@lem5390790) (@lem5390794)). Qed.
Lemma lem5390796 : True = term245.
Proof. exact (SYM (@lem5390795)). Qed.
Lemma lem5390797 : term245.
Proof. exact (EQ_MP (@lem5390796) (@lem0)). Qed.
Lemma lem5390798 : term248.
Proof. exact (@lem5390787 (@lem5390797)). Qed.
Lemma lem5390800 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5390801 : term245 = term246.
Proof. exact (@lem5390800 (NUMERAL 0) term44). Qed.
Lemma lem5390802 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5390803 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5390804 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5390803 h1) (fun h1 : term246 = True => @lem5390802)). Qed.
Lemma lem5390805 : term246 = True.
Proof. exact (EQ_MP (@lem5390804) (@lem5390802)). Qed.
Lemma lem5390806 : term245 = True.
Proof. exact (TRANS (@lem5390801) (@lem5390805)). Qed.
Lemma lem5390807 : True = term245.
Proof. exact (SYM (@lem5390806)). Qed.
Lemma lem5390808 : term245.
Proof. exact (EQ_MP (@lem5390807) (@lem0)). Qed.
Lemma lem5390809 : term249.
Proof. exact (@lem5390798 (@lem5390808)). Qed.
Lemma lem5390811 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5390812 : term245 = term246.
Proof. exact (@lem5390811 (NUMERAL 0) term44). Qed.
Lemma lem5390813 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5390814 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5390815 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5390814 h1) (fun h1 : term246 = True => @lem5390813)). Qed.
Lemma lem5390816 : term246 = True.
Proof. exact (EQ_MP (@lem5390815) (@lem5390813)). Qed.
Lemma lem5390817 : term245 = True.
Proof. exact (TRANS (@lem5390812) (@lem5390816)). Qed.
Lemma lem5390818 : True = term245.
Proof. exact (SYM (@lem5390817)). Qed.
Lemma lem5390819 : term245.
Proof. exact (EQ_MP (@lem5390818) (@lem0)). Qed.
Lemma lem5390820 : term250.
Proof. exact (@lem5390809 (@lem5390819)). Qed.
Lemma lem5390822 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5390823 : term210 = term211.
Proof. exact (@lem5390822 term44 term44). Qed.
Lemma lem5390824 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5390825 : term213 = term44.
Proof. exact (EQ_MP (@lem5390824) (@lem940073)). Qed.
Lemma lem5390826 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5390827 : term211 = term138.
Proof. exact (MK_COMB (@lem5390826) (@lem5390825)). Qed.
Lemma lem5390828 : term210 = term138.
Proof. exact (TRANS (@lem5390823) (@lem5390827)). Qed.
Lemma lem5390830 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5390831 : term210 = term211.
Proof. exact (@lem5390830 term44 term44). Qed.
Lemma lem5390832 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5390833 : term213 = term44.
Proof. exact (EQ_MP (@lem5390832) (@lem940073)). Qed.
Lemma lem5390834 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5390835 : term211 = term138.
Proof. exact (MK_COMB (@lem5390834) (@lem5390833)). Qed.
Lemma lem5390836 : term210 = term138.
Proof. exact (TRANS (@lem5390831) (@lem5390835)). Qed.
Lemma lem5390837 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5390838 : term251 = term238.
Proof. exact (MK_COMB (@lem5390837) (@lem5390836)). Qed.
Lemma lem5390839 : term252 = term240.
Proof. exact (MK_COMB (@lem5390838) (@lem5390828)). Qed.
Lemma lem5390840 : term240 = term253.
Proof. exact (@lem1367770 term44 term44). Qed.
Lemma lem5390841 : term254 = term255.
Proof. exact (@lem706885). Qed.
Lemma lem5390842 : (term254 = term255) = (term256 = term257).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term255). Qed.
Lemma lem5390843 : term256 = term257.
Proof. exact (EQ_MP (@lem5390842) (@lem5390841)). Qed.
Lemma lem5390844 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5390845 : term253 = term243.
Proof. exact (MK_COMB (@lem5390844) (@lem5390843)). Qed.
Lemma lem5390846 : term240 = term243.
Proof. exact (TRANS (@lem5390840) (@lem5390845)). Qed.
Lemma lem5390847 : term252 = term243.
Proof. exact (TRANS (@lem5390839) (@lem5390846)). Qed.
Lemma lem5390848 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5390849 : term258 = term259.
Proof. exact (MK_COMB (@lem5390848) (@lem5390847)). Qed.
Lemma lem5390850 : term138 = term138.
Proof. exact (eq_refl term138). Qed.
Lemma lem5390851 : term260 = term261.
Proof. exact (MK_COMB (@lem5390849) (@lem5390850)). Qed.
Lemma lem5390853 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5390854 : term261 = term262.
Proof. exact (@lem5390853 term257 term44). Qed.
Lemma lem5390855 : term263 = term255.
Proof. exact (@lem996237 term255). Qed.
Lemma lem5390856 : (term263 = term255) = (term264 = term257).
Proof. exact (@lem1007663 term255 (BIT1 0) term255). Qed.
Lemma lem5390857 : term264 = term257.
Proof. exact (EQ_MP (@lem5390856) (@lem5390855)). Qed.
Lemma lem5390858 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5390859 : term262 = term243.
Proof. exact (MK_COMB (@lem5390858) (@lem5390857)). Qed.
Lemma lem5390860 : term261 = term243.
Proof. exact (TRANS (@lem5390854) (@lem5390859)). Qed.
Lemma lem5390861 : term260 = term243.
Proof. exact (TRANS (@lem5390851) (@lem5390860)). Qed.
Lemma lem5390863 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5390864 : term210 = term211.
Proof. exact (@lem5390863 term44 term44). Qed.
Lemma lem5390865 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5390866 : term213 = term44.
Proof. exact (EQ_MP (@lem5390865) (@lem940073)). Qed.
Lemma lem5390867 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5390868 : term211 = term138.
Proof. exact (MK_COMB (@lem5390867) (@lem5390866)). Qed.
Lemma lem5390869 : term210 = term138.
Proof. exact (TRANS (@lem5390864) (@lem5390868)). Qed.
Lemma lem5390870 : term259 = term259.
Proof. exact (eq_refl term259). Qed.
Lemma lem5390871 : term265 = term261.
Proof. exact (MK_COMB (@lem5390870) (@lem5390869)). Qed.
Lemma lem5390873 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5390874 : term261 = term262.
Proof. exact (@lem5390873 term257 term44). Qed.
Lemma lem5390875 : term263 = term255.
Proof. exact (@lem996237 term255). Qed.
Lemma lem5390876 : (term263 = term255) = (term264 = term257).
Proof. exact (@lem1007663 term255 (BIT1 0) term255). Qed.
Lemma lem5390877 : term264 = term257.
Proof. exact (EQ_MP (@lem5390876) (@lem5390875)). Qed.
Lemma lem5390878 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5390879 : term262 = term243.
Proof. exact (MK_COMB (@lem5390878) (@lem5390877)). Qed.
Lemma lem5390880 : term261 = term243.
Proof. exact (TRANS (@lem5390874) (@lem5390879)). Qed.
Lemma lem5390881 : term265 = term243.
Proof. exact (TRANS (@lem5390871) (@lem5390880)). Qed.
Lemma lem5390882 : term243 = term265.
Proof. exact (SYM (@lem5390881)). Qed.
Lemma lem5390883 : term260 = term265.
Proof. exact (TRANS (@lem5390861) (@lem5390882)). Qed.
Lemma lem5390884 : term241 = term266.
Proof. exact (@lem5390820 (@lem5390883)). Qed.
Lemma lem5390885 : term240 = term266.
Proof. exact (TRANS (@lem5390786) (@lem5390884)). Qed.
Lemma lem5390887 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5390888 : term266 = term243.
Proof. exact (@lem5390887 term243). Qed.
Lemma lem5390889 : term240 = term243.
Proof. exact (TRANS (@lem5390885) (@lem5390888)). Qed.
Lemma lem5390890 (_69865 : int) : (term139 _69865) = (term139 _69865).
Proof. exact (eq_refl (term139 _69865)). Qed.
Lemma lem5390891 (_69865 : int) : (term236 _69865) = (term267 _69865).
Proof. exact (MK_COMB (@lem5390890 _69865) (@lem5390889)). Qed.
Lemma lem5390893 (_69865 : int) : (term151 _69865) = (term267 _69865).
Proof. exact (TRANS (@lem5390777 _69865) (@lem5390891 _69865)). Qed.
Lemma lem5390896 (_69866 : int) : (term268 _69866) = (term268 _69866).
Proof. exact (eq_refl (term268 _69866)). Qed.
Lemma lem5390897 (_69866 : int) (_69865 : int) : (term269 _69866 _69865) = (term270 _69866 _69865).
Proof. exact (MK_COMB (@lem5390896 _69866) (@lem5390893 _69865)). Qed.
Lemma lem5390898 (_69866 : int) (_69865 : int) : (term270 _69866 _69865) = (term271 _69866 _69865).
Proof. exact (@lem1982792 (real_of_int _69866) (term267 _69865)). Qed.
Lemma lem5390899 (_69865 : int) : (term272 _69865) = (term273 _69865).
Proof. exact (@lem1982781 (real_of_int _69865) term201 term243). Qed.
Lemma lem5390901 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5390902 : term243 = term266.
Proof. exact (@lem5390901 term257). Qed.
Lemma lem5390904 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5390905 : term201 = term202.
Proof. exact (@lem5390904 term44). Qed.
Lemma lem5390906 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5390907 : term203 = term204.
Proof. exact (MK_COMB (@lem5390906) (@lem5390905)). Qed.
Lemma lem5390908 : term274 = term275.
Proof. exact (MK_COMB (@lem5390907) (@lem5390902)). Qed.
Lemma lem5390909 : term275 = term276.
Proof. exact (@lem1981613 term201 term243 term138 term138). Qed.
Lemma lem5390911 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5390912 : term210 = term211.
Proof. exact (@lem5390911 term44 term44). Qed.
Lemma lem5390913 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5390914 : term213 = term44.
Proof. exact (EQ_MP (@lem5390913) (@lem940073)). Qed.
Lemma lem5390915 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5390916 : term211 = term138.
Proof. exact (MK_COMB (@lem5390915) (@lem5390914)). Qed.
Lemma lem5390917 : term210 = term138.
Proof. exact (TRANS (@lem5390912) (@lem5390916)). Qed.
Lemma lem5390919 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5390920 : term274 = term279.
Proof. exact (@lem5390919 term44 term257). Qed.
Lemma lem5390921 : term280 = term255.
Proof. exact (@lem996238 term255). Qed.
Lemma lem5390922 : (term280 = term255) = (term281 = term257).
Proof. exact (@lem1007663 (BIT1 0) term255 term255). Qed.
Lemma lem5390923 : term281 = term257.
Proof. exact (EQ_MP (@lem5390922) (@lem5390921)). Qed.
Lemma lem5390924 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5390925 : term282 = term243.
Proof. exact (MK_COMB (@lem5390924) (@lem5390923)). Qed.
Lemma lem5390926 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5390927 : term279 = term283.
Proof. exact (MK_COMB (@lem5390926) (@lem5390925)). Qed.
Lemma lem5390928 : term274 = term283.
Proof. exact (TRANS (@lem5390920) (@lem5390927)). Qed.
Lemma lem5390929 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5390930 : term284 = term285.
Proof. exact (MK_COMB (@lem5390929) (@lem5390928)). Qed.
Lemma lem5390931 : term276 = term286.
Proof. exact (MK_COMB (@lem5390930) (@lem5390917)). Qed.
Lemma lem5390932 : term275 = term286.
Proof. exact (TRANS (@lem5390909) (@lem5390931)). Qed.
Lemma lem5390933 : term274 = term286.
Proof. exact (TRANS (@lem5390908) (@lem5390932)). Qed.
Lemma lem5390935 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5390936 : term286 = term283.
Proof. exact (@lem5390935 term283). Qed.
Lemma lem5390937 : term274 = term283.
Proof. exact (TRANS (@lem5390933) (@lem5390936)). Qed.
Lemma lem5390940 (_69865 : int) : (term231 _69865) = (term231 _69865).
Proof. exact (eq_refl (term231 _69865)). Qed.
Lemma lem5390941 (_69865 : int) : (term273 _69865) = (term287 _69865).
Proof. exact (MK_COMB (@lem5390940 _69865) (@lem5390937)). Qed.
Lemma lem5390942 (_69865 : int) : (term272 _69865) = (term287 _69865).
Proof. exact (TRANS (@lem5390899 _69865) (@lem5390941 _69865)). Qed.
Lemma lem5390943 (_69866 : int) : (term139 _69866) = (term139 _69866).
Proof. exact (eq_refl (term139 _69866)). Qed.
Lemma lem5390944 (_69866 : int) (_69865 : int) : (term271 _69866 _69865) = (term288 _69866 _69865).
Proof. exact (MK_COMB (@lem5390943 _69866) (@lem5390942 _69865)). Qed.
Lemma lem5390949 (_69865 : int) (_69866 : int) : (term288 _69866 _69865) = (term1115 _69865 _69866).
Proof. exact (@lem1982757 (term228 _69865) (real_of_int _69866) term283). Qed.
Lemma lem5390950 (_69865 : int) (_69866 : int) : (term271 _69866 _69865) = (term1115 _69865 _69866).
Proof. exact (TRANS (@lem5390944 _69866 _69865) (@lem5390949 _69865 _69866)). Qed.
Lemma lem5390951 (_69865 : int) (_69866 : int) : (term270 _69866 _69865) = (term1115 _69865 _69866).
Proof. exact (TRANS (@lem5390898 _69866 _69865) (@lem5390950 _69865 _69866)). Qed.
Lemma lem5390952 (_69865 : int) (_69866 : int) : (term269 _69866 _69865) = (term1115 _69865 _69866).
Proof. exact (TRANS (@lem5390897 _69866 _69865) (@lem5390951 _69865 _69866)). Qed.
Lemma lem5390953 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5390954 (_69865 : int) (_69866 : int) : (term289 _69866 _69865) = (term1116 _69865 _69866).
Proof. exact (MK_COMB (@lem5390953) (@lem5390952 _69865 _69866)). Qed.
Lemma lem5390955 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5390956 (_69865 : int) (_69866 : int) : (term235 _69866 _69865) = (term1117 _69865 _69866).
Proof. exact (MK_COMB (@lem5390954 _69865 _69866) (@lem5390955)). Qed.
Lemma lem5390957 (_69865 : int) (_69866 : int) : (term154 _69865 _69866) = (term1117 _69865 _69866).
Proof. exact (TRANS (@lem5390765 _69866 _69865) (@lem5390956 _69865 _69866)). Qed.
Lemma lem5390958 (_69865 : int) (_69866 : int) : (term1074 _69866 _69865) = (term1118 _69865 _69866).
Proof. exact (@lem1988287 (term140 _69865) (term140 _69866)). Qed.
Lemma lem5390976 (_69865 : int) (_69866 : int) : (term1119 _69865 _69866) = (term1120 _69865 _69866).
Proof. exact (@lem1982792 (term140 _69865) (term140 _69866)). Qed.
Lemma lem5390977 (_69866 : int) : (term300 _69866) = (term301 _69866).
Proof. exact (@lem1982781 (real_of_int _69866) term201 term138). Qed.
Lemma lem5390979 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5390980 : term138 = term237.
Proof. exact (@lem5390979 term44). Qed.
Lemma lem5390982 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5390983 : term201 = term202.
Proof. exact (@lem5390982 term44). Qed.
Lemma lem5390984 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5390985 : term203 = term204.
Proof. exact (MK_COMB (@lem5390984) (@lem5390983)). Qed.
Lemma lem5390986 : term302 = term303.
Proof. exact (MK_COMB (@lem5390985) (@lem5390980)). Qed.
Lemma lem5390987 : term303 = term304.
Proof. exact (@lem1981613 term201 term138 term138 term138). Qed.
Lemma lem5390989 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5390990 : term210 = term211.
Proof. exact (@lem5390989 term44 term44). Qed.
Lemma lem5390991 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5390992 : term213 = term44.
Proof. exact (EQ_MP (@lem5390991) (@lem940073)). Qed.
Lemma lem5390993 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5390994 : term211 = term138.
Proof. exact (MK_COMB (@lem5390993) (@lem5390992)). Qed.
Lemma lem5390995 : term210 = term138.
Proof. exact (TRANS (@lem5390990) (@lem5390994)). Qed.
Lemma lem5390997 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5390998 : term302 = term305.
Proof. exact (@lem5390997 term44 term44). Qed.
Lemma lem5390999 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5391000 : term213 = term44.
Proof. exact (EQ_MP (@lem5390999) (@lem940073)). Qed.
Lemma lem5391001 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5391002 : term211 = term138.
Proof. exact (MK_COMB (@lem5391001) (@lem5391000)). Qed.
Lemma lem5391003 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5391004 : term305 = term201.
Proof. exact (MK_COMB (@lem5391003) (@lem5391002)). Qed.
Lemma lem5391005 : term302 = term201.
Proof. exact (TRANS (@lem5390998) (@lem5391004)). Qed.
Lemma lem5391006 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5391007 : term306 = term307.
Proof. exact (MK_COMB (@lem5391006) (@lem5391005)). Qed.
Lemma lem5391008 : term304 = term202.
Proof. exact (MK_COMB (@lem5391007) (@lem5390995)). Qed.
Lemma lem5391009 : term303 = term202.
Proof. exact (TRANS (@lem5390987) (@lem5391008)). Qed.
Lemma lem5391010 : term302 = term202.
Proof. exact (TRANS (@lem5390986) (@lem5391009)). Qed.
Lemma lem5391012 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5391013 : term202 = term201.
Proof. exact (@lem5391012 term201). Qed.
Lemma lem5391014 : term302 = term201.
Proof. exact (TRANS (@lem5391010) (@lem5391013)). Qed.
Lemma lem5391017 (_69866 : int) : (term231 _69866) = (term231 _69866).
Proof. exact (eq_refl (term231 _69866)). Qed.
Lemma lem5391018 (_69866 : int) : (term301 _69866) = (term308 _69866).
Proof. exact (MK_COMB (@lem5391017 _69866) (@lem5391014)). Qed.
Lemma lem5391019 (_69866 : int) : (term300 _69866) = (term308 _69866).
Proof. exact (TRANS (@lem5390977 _69866) (@lem5391018 _69866)). Qed.
Lemma lem5391020 (_69865 : int) : (term150 _69865) = (term150 _69865).
Proof. exact (eq_refl (term150 _69865)). Qed.
Lemma lem5391021 (_69865 : int) (_69866 : int) : (term1120 _69865 _69866) = (term1121 _69865 _69866).
Proof. exact (MK_COMB (@lem5391020 _69865) (@lem5391019 _69866)). Qed.
Lemma lem5391022 (_69865 : int) (_69866 : int) : (term1121 _69865 _69866) = (term1122 _69865 _69866).
Proof. exact (@lem1982755 (real_of_int _69865) term138 (term308 _69866)). Qed.
Lemma lem5391023 (_69866 : int) : (term1123 _69866) = (term1124 _69866).
Proof. exact (@lem1982757 (term228 _69866) term138 term201). Qed.
Lemma lem5391025 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5391026 : term201 = term202.
Proof. exact (@lem5391025 term44). Qed.
Lemma lem5391028 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5391029 : term138 = term237.
Proof. exact (@lem5391028 term44). Qed.
Lemma lem5391030 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5391031 : term238 = term239.
Proof. exact (MK_COMB (@lem5391030) (@lem5391029)). Qed.
Lemma lem5391032 : term492 = term493.
Proof. exact (MK_COMB (@lem5391031) (@lem5391026)). Qed.
Lemma lem5391033 : term494.
Proof. exact (@lem1981473 term138 term138 term201 term138 term128 term138). Qed.
Lemma lem5391035 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5391036 : term245 = term246.
Proof. exact (@lem5391035 (NUMERAL 0) term44). Qed.
Lemma lem5391037 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5391038 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5391039 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5391038 h1) (fun h1 : term246 = True => @lem5391037)). Qed.
Lemma lem5391040 : term246 = True.
Proof. exact (EQ_MP (@lem5391039) (@lem5391037)). Qed.
Lemma lem5391041 : term245 = True.
Proof. exact (TRANS (@lem5391036) (@lem5391040)). Qed.
Lemma lem5391042 : True = term245.
Proof. exact (SYM (@lem5391041)). Qed.
Lemma lem5391043 : term245.
Proof. exact (EQ_MP (@lem5391042) (@lem0)). Qed.
Lemma lem5391044 : term495.
Proof. exact (@lem5391033 (@lem5391043)). Qed.
Lemma lem5391046 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5391047 : term245 = term246.
Proof. exact (@lem5391046 (NUMERAL 0) term44). Qed.
Lemma lem5391048 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5391049 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5391050 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5391049 h1) (fun h1 : term246 = True => @lem5391048)). Qed.
Lemma lem5391051 : term246 = True.
Proof. exact (EQ_MP (@lem5391050) (@lem5391048)). Qed.
Lemma lem5391052 : term245 = True.
Proof. exact (TRANS (@lem5391047) (@lem5391051)). Qed.
Lemma lem5391053 : True = term245.
Proof. exact (SYM (@lem5391052)). Qed.
Lemma lem5391054 : term245.
Proof. exact (EQ_MP (@lem5391053) (@lem0)). Qed.
Lemma lem5391055 : term496.
Proof. exact (@lem5391044 (@lem5391054)). Qed.
Lemma lem5391057 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5391058 : term245 = term246.
Proof. exact (@lem5391057 (NUMERAL 0) term44). Qed.
Lemma lem5391059 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5391060 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5391061 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5391060 h1) (fun h1 : term246 = True => @lem5391059)). Qed.
Lemma lem5391062 : term246 = True.
Proof. exact (EQ_MP (@lem5391061) (@lem5391059)). Qed.
Lemma lem5391063 : term245 = True.
Proof. exact (TRANS (@lem5391058) (@lem5391062)). Qed.
Lemma lem5391064 : True = term245.
Proof. exact (SYM (@lem5391063)). Qed.
Lemma lem5391065 : term245.
Proof. exact (EQ_MP (@lem5391064) (@lem0)). Qed.
Lemma lem5391066 : term497.
Proof. exact (@lem5391055 (@lem5391065)). Qed.
Lemma lem5391068 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5391069 : term302 = term305.
Proof. exact (@lem5391068 term44 term44). Qed.
Lemma lem5391070 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5391071 : term213 = term44.
Proof. exact (EQ_MP (@lem5391070) (@lem940073)). Qed.
Lemma lem5391072 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5391073 : term211 = term138.
Proof. exact (MK_COMB (@lem5391072) (@lem5391071)). Qed.
Lemma lem5391074 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5391075 : term305 = term201.
Proof. exact (MK_COMB (@lem5391074) (@lem5391073)). Qed.
Lemma lem5391076 : term302 = term201.
Proof. exact (TRANS (@lem5391069) (@lem5391075)). Qed.
Lemma lem5391078 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5391079 : term210 = term211.
Proof. exact (@lem5391078 term44 term44). Qed.
Lemma lem5391080 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5391081 : term213 = term44.
Proof. exact (EQ_MP (@lem5391080) (@lem940073)). Qed.
Lemma lem5391082 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5391083 : term211 = term138.
Proof. exact (MK_COMB (@lem5391082) (@lem5391081)). Qed.
Lemma lem5391084 : term210 = term138.
Proof. exact (TRANS (@lem5391079) (@lem5391083)). Qed.
Lemma lem5391085 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5391086 : term251 = term238.
Proof. exact (MK_COMB (@lem5391085) (@lem5391084)). Qed.
Lemma lem5391087 : term498 = term492.
Proof. exact (MK_COMB (@lem5391086) (@lem5391076)). Qed.
Lemma lem5391089 (m : nat) : (term499 m) = term128.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem5391090 : term492 = term128.
Proof. exact (@lem5391089 term44). Qed.
Lemma lem5391091 : term498 = term128.
Proof. exact (TRANS (@lem5391087) (@lem5391090)). Qed.
Lemma lem5391092 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5391093 : term500 = term431.
Proof. exact (MK_COMB (@lem5391092) (@lem5391091)). Qed.
Lemma lem5391094 : term138 = term138.
Proof. exact (eq_refl term138). Qed.
Lemma lem5391095 : term501 = term398.
Proof. exact (MK_COMB (@lem5391093) (@lem5391094)). Qed.
Lemma lem5391097 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5391098 : term398 = term128.
Proof. exact (@lem5391097 term44). Qed.
Lemma lem5391099 : term501 = term128.
Proof. exact (TRANS (@lem5391095) (@lem5391098)). Qed.
Lemma lem5391101 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5391102 : term210 = term211.
Proof. exact (@lem5391101 term44 term44). Qed.
Lemma lem5391103 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5391104 : term213 = term44.
Proof. exact (EQ_MP (@lem5391103) (@lem940073)). Qed.
Lemma lem5391105 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5391106 : term211 = term138.
Proof. exact (MK_COMB (@lem5391105) (@lem5391104)). Qed.
Lemma lem5391107 : term210 = term138.
Proof. exact (TRANS (@lem5391102) (@lem5391106)). Qed.
Lemma lem5391108 : term431 = term431.
Proof. exact (eq_refl term431). Qed.
Lemma lem5391109 : term433 = term398.
Proof. exact (MK_COMB (@lem5391108) (@lem5391107)). Qed.
Lemma lem5391111 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5391112 : term398 = term128.
Proof. exact (@lem5391111 term44). Qed.
Lemma lem5391113 : term433 = term128.
Proof. exact (TRANS (@lem5391109) (@lem5391112)). Qed.
Lemma lem5391114 : term128 = term433.
Proof. exact (SYM (@lem5391113)). Qed.
Lemma lem5391115 : term501 = term433.
Proof. exact (TRANS (@lem5391099) (@lem5391114)). Qed.
Lemma lem5391116 : term493 = term198.
Proof. exact (@lem5391066 (@lem5391115)). Qed.
Lemma lem5391117 : term492 = term198.
Proof. exact (TRANS (@lem5391032) (@lem5391116)). Qed.
Lemma lem5391119 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5391120 : term198 = term128.
Proof. exact (@lem5391119 term128). Qed.
Lemma lem5391121 : term492 = term128.
Proof. exact (TRANS (@lem5391117) (@lem5391120)). Qed.
Lemma lem5391122 (_69866 : int) : (term231 _69866) = (term231 _69866).
Proof. exact (eq_refl (term231 _69866)). Qed.
Lemma lem5391123 (_69866 : int) : (term1124 _69866) = (term503 _69866).
Proof. exact (MK_COMB (@lem5391122 _69866) (@lem5391121)). Qed.
Lemma lem5391124 (_69866 : int) : (term1123 _69866) = (term503 _69866).
Proof. exact (TRANS (@lem5391023 _69866) (@lem5391123 _69866)). Qed.
Lemma lem5391125 (_69866 : int) : (term503 _69866) = (term228 _69866).
Proof. exact (@lem1982723 (term228 _69866)). Qed.
Lemma lem5391126 (_69866 : int) : (term1123 _69866) = (term228 _69866).
Proof. exact (TRANS (@lem5391124 _69866) (@lem5391125 _69866)). Qed.
Lemma lem5391127 (_69865 : int) : (term139 _69865) = (term139 _69865).
Proof. exact (eq_refl (term139 _69865)). Qed.
Lemma lem5391128 (_69865 : int) (_69866 : int) : (term1122 _69865 _69866) = (term555 _69865 _69866).
Proof. exact (MK_COMB (@lem5391127 _69865) (@lem5391126 _69866)). Qed.
Lemma lem5391129 (_69865 : int) (_69866 : int) : (term1121 _69865 _69866) = (term555 _69865 _69866).
Proof. exact (TRANS (@lem5391022 _69865 _69866) (@lem5391128 _69865 _69866)). Qed.
Lemma lem5391130 (_69865 : int) (_69866 : int) : (term1120 _69865 _69866) = (term555 _69865 _69866).
Proof. exact (TRANS (@lem5391021 _69865 _69866) (@lem5391129 _69865 _69866)). Qed.
Lemma lem5391132 (_69865 : int) (_69866 : int) : (term1119 _69865 _69866) = (term555 _69865 _69866).
Proof. exact (TRANS (@lem5390976 _69865 _69866) (@lem5391130 _69865 _69866)). Qed.
Lemma lem5391133 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5391134 (_69865 : int) (_69866 : int) : (term1125 _69865 _69866) = (term1126 _69865 _69866).
Proof. exact (MK_COMB (@lem5391133) (@lem5391132 _69865 _69866)). Qed.
Lemma lem5391135 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5391136 (_69865 : int) (_69866 : int) : (term1118 _69865 _69866) = (term1127 _69865 _69866).
Proof. exact (MK_COMB (@lem5391134 _69865 _69866) (@lem5391135)). Qed.
Lemma lem5391137 (_69865 : int) (_69866 : int) : (term1074 _69866 _69865) = (term1127 _69865 _69866).
Proof. exact (TRANS (@lem5390958 _69865 _69866) (@lem5391136 _69865 _69866)). Qed.
Lemma lem5391138 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5391139 (_69865 : int) (_69866 : int) : (term1071 _69865 _69866) = (term1128 _69865 _69866).
Proof. exact (MK_COMB (@lem5391138) (@lem5390957 _69865 _69866)). Qed.
Lemma lem5391140 (_69865 : int) (_69866 : int) : (term1075 _69866 _69865) = (term1129 _69865 _69866).
Proof. exact (MK_COMB (@lem5391139 _69865 _69866) (@lem5391137 _69865 _69866)). Qed.
Lemma lem5391141 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5391142 (_69867 : int) (_69865 : int) (_69866 : int) : (term1076 _69865 _69867 _69866) = (term1130 _69865 _69866).
Proof. exact (MK_COMB (@lem5391141) (@lem5390764 _69867 _69865 _69866)). Qed.
Lemma lem5391143 (_69867 : int) (_69865 : int) (_69866 : int) : (term1077 _69867 _69866 _69865) = (term1131 _69865 _69866).
Proof. exact (MK_COMB (@lem5391142 _69867 _69865 _69866) (@lem5391140 _69865 _69866)). Qed.
Lemma lem5391144 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5391145 (_69867 : int) : (term188 _69867) = (term334 _69867).
Proof. exact (MK_COMB (@lem5391144) (@lem5390224 _69867)). Qed.
Lemma lem5391146 (_69867 : int) (_69865 : int) (_69866 : int) : (term1078 _69867 _69866 _69865) = (term1132 _69867 _69865 _69866).
Proof. exact (MK_COMB (@lem5391145 _69867) (@lem5391143 _69867 _69865 _69866)). Qed.
Lemma lem5391147 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5391148 (_69866 : int) : (term188 _69866) = (term334 _69866).
Proof. exact (MK_COMB (@lem5391147) (@lem5390176 _69866)). Qed.
Lemma lem5391149 (_69867 : int) (_69865 : int) (_69866 : int) : (term1079 _69867 _69866 _69865) = (term1133 _69867 _69865 _69866).
Proof. exact (MK_COMB (@lem5391148 _69866) (@lem5391146 _69867 _69865 _69866)). Qed.
Lemma lem5391150 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5391151 (_69865 : int) : (term188 _69865) = (term334 _69865).
Proof. exact (MK_COMB (@lem5391150) (@lem5390128 _69865)). Qed.
Lemma lem5391152 (_69867 : int) (_69865 : int) (_69866 : int) : (term1080 _69867 _69866 _69865) = (term1134 _69867 _69865 _69866).
Proof. exact (MK_COMB (@lem5391151 _69865) (@lem5391149 _69867 _69865 _69866)). Qed.
Lemma lem5391159 (_69867 : int) (_69865 : int) (_69866 : int) : (term1081 _69867 _69866 _69865) = (term1134 _69867 _69865 _69866).
Proof. exact (TRANS (@lem5390080 _69867 _69866 _69865) (@lem5391152 _69867 _69865 _69866)). Qed.
Lemma lem5391179 (_69865 : int) (_69866 : int) : (term1131 _69865 _69866) = (term1135 _69865 _69866).
Proof. exact (@lem19158 (term1117 _69865 _69866) (term1114 _69865 _69866) (term1127 _69865 _69866)). Qed.
Lemma lem5391186 (_69865 : int) (_69866 : int) : (term1136 _69865 _69866) = (term1137 _69865 _69866).
Proof. exact (@lem19367 ((term1091 _69865 _69866) = term128) (term1112 _69865 _69866) (term1127 _69865 _69866)). Qed.
Lemma lem5391193 (_69865 : int) (_69866 : int) : (term1138 _69865 _69866) = (term1139 _69865 _69866).
Proof. exact (@lem19367 ((term1091 _69865 _69866) = term128) (term1112 _69865 _69866) (term1117 _69865 _69866)). Qed.
Lemma lem5391194 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5391195 (_69865 : int) (_69866 : int) : (term1140 _69865 _69866) = (term1141 _69865 _69866).
Proof. exact (MK_COMB (@lem5391194) (@lem5391193 _69865 _69866)). Qed.
Lemma lem5391196 (_69865 : int) (_69866 : int) : (term1135 _69865 _69866) = (term1142 _69865 _69866).
Proof. exact (MK_COMB (@lem5391195 _69865 _69866) (@lem5391186 _69865 _69866)). Qed.
Lemma lem5391198 (_69865 : int) (_69866 : int) : (term1131 _69865 _69866) = (term1142 _69865 _69866).
Proof. exact (TRANS (@lem5391179 _69865 _69866) (@lem5391196 _69865 _69866)). Qed.
Lemma lem5391201 (_69867 : int) : (term334 _69867) = (term334 _69867).
Proof. exact (eq_refl (term334 _69867)). Qed.
Lemma lem5391202 (_69867 : int) (_69865 : int) (_69866 : int) : (term1132 _69867 _69865 _69866) = (term1143 _69867 _69865 _69866).
Proof. exact (MK_COMB (@lem5391201 _69867) (@lem5391198 _69865 _69866)). Qed.
Lemma lem5391203 (_69867 : int) (_69865 : int) (_69866 : int) : (term1143 _69867 _69865 _69866) = (term1144 _69867 _69865 _69866).
Proof. exact (@lem19158 (term1139 _69865 _69866) (term221 _69867) (term1137 _69865 _69866)). Qed.
Lemma lem5391210 (_69867 : int) (_69865 : int) (_69866 : int) : (term1145 _69867 _69865 _69866) = (term1146 _69867 _69865 _69866).
Proof. exact (@lem19158 (term1147 _69865 _69866) (term221 _69867) (term1148 _69865 _69866)). Qed.
Lemma lem5391217 (_69867 : int) (_69865 : int) (_69866 : int) : (term1149 _69867 _69865 _69866) = (term1150 _69867 _69865 _69866).
Proof. exact (@lem19158 (term1151 _69865 _69866) (term221 _69867) (term1152 _69865 _69866)). Qed.
Lemma lem5391218 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5391219 (_69867 : int) (_69865 : int) (_69866 : int) : (term1153 _69867 _69865 _69866) = (term1154 _69867 _69865 _69866).
Proof. exact (MK_COMB (@lem5391218) (@lem5391217 _69867 _69865 _69866)). Qed.
Lemma lem5391220 (_69867 : int) (_69865 : int) (_69866 : int) : (term1144 _69867 _69865 _69866) = (term1155 _69867 _69865 _69866).
Proof. exact (MK_COMB (@lem5391219 _69867 _69865 _69866) (@lem5391210 _69867 _69865 _69866)). Qed.
Lemma lem5391221 (_69867 : int) (_69865 : int) (_69866 : int) : (term1143 _69867 _69865 _69866) = (term1155 _69867 _69865 _69866).
Proof. exact (TRANS (@lem5391203 _69867 _69865 _69866) (@lem5391220 _69867 _69865 _69866)). Qed.
Lemma lem5391222 (_69867 : int) (_69865 : int) (_69866 : int) : (term1132 _69867 _69865 _69866) = (term1155 _69867 _69865 _69866).
Proof. exact (TRANS (@lem5391202 _69867 _69865 _69866) (@lem5391221 _69867 _69865 _69866)). Qed.
Lemma lem5391225 (_69866 : int) : (term334 _69866) = (term334 _69866).
Proof. exact (eq_refl (term334 _69866)). Qed.
Lemma lem5391226 (_69867 : int) (_69865 : int) (_69866 : int) : (term1133 _69867 _69865 _69866) = (term1156 _69867 _69865 _69866).
Proof. exact (MK_COMB (@lem5391225 _69866) (@lem5391222 _69867 _69865 _69866)). Qed.
Lemma lem5391227 (_69867 : int) (_69865 : int) (_69866 : int) : (term1156 _69867 _69865 _69866) = (term1157 _69867 _69865 _69866).
Proof. exact (@lem19158 (term1150 _69867 _69865 _69866) (term221 _69866) (term1146 _69867 _69865 _69866)). Qed.
Lemma lem5391234 (_69867 : int) (_69865 : int) (_69866 : int) : (term1158 _69867 _69865 _69866) = (term1159 _69867 _69865 _69866).
Proof. exact (@lem19158 (term1160 _69867 _69865 _69866) (term221 _69866) (term1161 _69867 _69865 _69866)). Qed.
Lemma lem5391241 (_69867 : int) (_69865 : int) (_69866 : int) : (term1162 _69867 _69865 _69866) = (term1163 _69867 _69865 _69866).
Proof. exact (@lem19158 (term1164 _69867 _69865 _69866) (term221 _69866) (term1165 _69867 _69865 _69866)). Qed.
Lemma lem5391242 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5391243 (_69867 : int) (_69865 : int) (_69866 : int) : (term1166 _69867 _69865 _69866) = (term1167 _69867 _69865 _69866).
Proof. exact (MK_COMB (@lem5391242) (@lem5391241 _69867 _69865 _69866)). Qed.
Lemma lem5391244 (_69867 : int) (_69865 : int) (_69866 : int) : (term1157 _69867 _69865 _69866) = (term1168 _69867 _69865 _69866).
Proof. exact (MK_COMB (@lem5391243 _69867 _69865 _69866) (@lem5391234 _69867 _69865 _69866)). Qed.
Lemma lem5391245 (_69867 : int) (_69865 : int) (_69866 : int) : (term1156 _69867 _69865 _69866) = (term1168 _69867 _69865 _69866).
Proof. exact (TRANS (@lem5391227 _69867 _69865 _69866) (@lem5391244 _69867 _69865 _69866)). Qed.
Lemma lem5391246 (_69867 : int) (_69865 : int) (_69866 : int) : (term1133 _69867 _69865 _69866) = (term1168 _69867 _69865 _69866).
Proof. exact (TRANS (@lem5391226 _69867 _69865 _69866) (@lem5391245 _69867 _69865 _69866)). Qed.
Lemma lem5391249 (_69865 : int) : (term334 _69865) = (term334 _69865).
Proof. exact (eq_refl (term334 _69865)). Qed.
Lemma lem5391250 (_69867 : int) (_69865 : int) (_69866 : int) : (term1134 _69867 _69865 _69866) = (term1169 _69867 _69865 _69866).
Proof. exact (MK_COMB (@lem5391249 _69865) (@lem5391246 _69867 _69865 _69866)). Qed.
Lemma lem5391251 (_69867 : int) (_69865 : int) (_69866 : int) : (term1169 _69867 _69865 _69866) = (term1170 _69867 _69865 _69866).
Proof. exact (@lem19158 (term1163 _69867 _69865 _69866) (term221 _69865) (term1159 _69867 _69865 _69866)). Qed.
Lemma lem5391258 (_69867 : int) (_69865 : int) (_69866 : int) : (term1171 _69867 _69865 _69866) = (term1172 _69867 _69865 _69866).
Proof. exact (@lem19158 (term1173 _69867 _69865 _69866) (term221 _69865) (term1174 _69867 _69865 _69866)). Qed.
Lemma lem5391265 (_69867 : int) (_69865 : int) (_69866 : int) : (term1175 _69867 _69865 _69866) = (term1176 _69867 _69865 _69866).
Proof. exact (@lem19158 (term1177 _69867 _69865 _69866) (term221 _69865) (term1178 _69867 _69865 _69866)). Qed.
Lemma lem5391266 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5391267 (_69867 : int) (_69865 : int) (_69866 : int) : (term1179 _69867 _69865 _69866) = (term1180 _69867 _69865 _69866).
Proof. exact (MK_COMB (@lem5391266) (@lem5391265 _69867 _69865 _69866)). Qed.
Lemma lem5391268 (_69867 : int) (_69865 : int) (_69866 : int) : (term1170 _69867 _69865 _69866) = (term1181 _69867 _69865 _69866).
Proof. exact (MK_COMB (@lem5391267 _69867 _69865 _69866) (@lem5391258 _69867 _69865 _69866)). Qed.
Lemma lem5391269 (_69867 : int) (_69865 : int) (_69866 : int) : (term1169 _69867 _69865 _69866) = (term1181 _69867 _69865 _69866).
Proof. exact (TRANS (@lem5391251 _69867 _69865 _69866) (@lem5391268 _69867 _69865 _69866)). Qed.
Lemma lem5391270 (_69867 : int) (_69865 : int) (_69866 : int) : (term1134 _69867 _69865 _69866) = (term1181 _69867 _69865 _69866).
Proof. exact (TRANS (@lem5391250 _69867 _69865 _69866) (@lem5391269 _69867 _69865 _69866)). Qed.
Lemma lem5391271 (_69867 : int) (_69865 : int) (_69866 : int) : (term1081 _69867 _69866 _69865) = (term1181 _69867 _69865 _69866).
Proof. exact (TRANS (@lem5391159 _69867 _69865 _69866) (@lem5391270 _69867 _69865 _69866)). Qed.
Lemma lem5391293 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1181 _69867 _69865 _69866) : term1181 _69867 _69865 _69866.
Proof. exact (h1). Qed.
Lemma lem5391294 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1176 _69867 _69865 _69866) : term1176 _69867 _69865 _69866.
Proof. exact (h1). Qed.
Lemma lem5391295 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1182 _69867 _69865 _69866) : term1182 _69867 _69865 _69866.
Proof. exact (h1). Qed.
Lemma lem5391296 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1182 _69867 _69865 _69866) : term1177 _69867 _69865 _69866.
Proof. exact (proj2 (@lem5391295 _69867 _69865 _69866 h1)). Qed.
Lemma lem5391298 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1182 _69867 _69865 _69866) : term1164 _69867 _69865 _69866.
Proof. exact (proj2 (@lem5391296 _69867 _69865 _69866 h1)). Qed.
Lemma lem5391300 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1182 _69867 _69865 _69866) : term1151 _69865 _69866.
Proof. exact (proj2 (@lem5391298 _69867 _69865 _69866 h1)). Qed.
Lemma lem5391302 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1182 _69867 _69865 _69866) : term1117 _69865 _69866.
Proof. exact (proj2 (@lem5391300 _69867 _69865 _69866 h1)). Qed.
Lemma lem5391303 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1182 _69867 _69865 _69866) : (term1091 _69865 _69866) = term128.
Proof. exact (proj1 (@lem5391300 _69867 _69865 _69866 h1)). Qed.
Lemma lem5391305 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5391306 : term390 = term245.
Proof. exact (@lem5391305 term128 term138). Qed.
Lemma lem5391308 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5391309 : term138 = term237.
Proof. exact (@lem5391308 term44). Qed.
Lemma lem5391311 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5391312 : term128 = term198.
Proof. exact (@lem5391311 (NUMERAL 0)). Qed.
Lemma lem5391313 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5391314 : term391 = term392.
Proof. exact (MK_COMB (@lem5391313) (@lem5391312)). Qed.
Lemma lem5391315 : term245 = term393.
Proof. exact (MK_COMB (@lem5391314) (@lem5391309)). Qed.
Lemma lem5391316 : term394.
Proof. exact (@lem1980255 term128 term138 term138 term138). Qed.
Lemma lem5391318 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5391319 : term245 = term246.
Proof. exact (@lem5391318 (NUMERAL 0) term44). Qed.
Lemma lem5391320 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5391321 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5391322 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5391321 h1) (fun h1 : term246 = True => @lem5391320)). Qed.
Lemma lem5391323 : term246 = True.
Proof. exact (EQ_MP (@lem5391322) (@lem5391320)). Qed.
Lemma lem5391324 : term245 = True.
Proof. exact (TRANS (@lem5391319) (@lem5391323)). Qed.
Lemma lem5391325 : True = term245.
Proof. exact (SYM (@lem5391324)). Qed.
Lemma lem5391326 : term245.
Proof. exact (EQ_MP (@lem5391325) (@lem0)). Qed.
Lemma lem5391327 : term395.
Proof. exact (@lem5391316 (@lem5391326)). Qed.
Lemma lem5391329 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5391330 : term245 = term246.
Proof. exact (@lem5391329 (NUMERAL 0) term44). Qed.
Lemma lem5391331 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5391332 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5391333 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5391332 h1) (fun h1 : term246 = True => @lem5391331)). Qed.
Lemma lem5391334 : term246 = True.
Proof. exact (EQ_MP (@lem5391333) (@lem5391331)). Qed.
Lemma lem5391335 : term245 = True.
Proof. exact (TRANS (@lem5391330) (@lem5391334)). Qed.
Lemma lem5391336 : True = term245.
Proof. exact (SYM (@lem5391335)). Qed.
Lemma lem5391337 : term245.
Proof. exact (EQ_MP (@lem5391336) (@lem0)). Qed.
Lemma lem5391338 : term393 = term396.
Proof. exact (@lem5391327 (@lem5391337)). Qed.
Lemma lem5391340 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5391341 : term210 = term211.
Proof. exact (@lem5391340 term44 term44). Qed.
Lemma lem5391342 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5391343 : term213 = term44.
Proof. exact (EQ_MP (@lem5391342) (@lem940073)). Qed.
Lemma lem5391344 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5391345 : term211 = term138.
Proof. exact (MK_COMB (@lem5391344) (@lem5391343)). Qed.
Lemma lem5391346 : term210 = term138.
Proof. exact (TRANS (@lem5391341) (@lem5391345)). Qed.
Lemma lem5391348 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5391349 : term398 = term128.
Proof. exact (@lem5391348 term44). Qed.
Lemma lem5391350 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5391351 : term399 = term391.
Proof. exact (MK_COMB (@lem5391350) (@lem5391349)). Qed.
Lemma lem5391352 : term396 = term245.
Proof. exact (MK_COMB (@lem5391351) (@lem5391346)). Qed.
Lemma lem5391354 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5391355 : term245 = term246.
Proof. exact (@lem5391354 (NUMERAL 0) term44). Qed.
Lemma lem5391356 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5391357 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5391358 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5391357 h1) (fun h1 : term246 = True => @lem5391356)). Qed.
Lemma lem5391359 : term246 = True.
Proof. exact (EQ_MP (@lem5391358) (@lem5391356)). Qed.
Lemma lem5391360 : term245 = True.
Proof. exact (TRANS (@lem5391355) (@lem5391359)). Qed.
Lemma lem5391361 : term396 = True.
Proof. exact (TRANS (@lem5391352) (@lem5391360)). Qed.
Lemma lem5391362 : term393 = True.
Proof. exact (TRANS (@lem5391338) (@lem5391361)). Qed.
Lemma lem5391363 : term245 = True.
Proof. exact (TRANS (@lem5391315) (@lem5391362)). Qed.
Lemma lem5391364 : term390 = True.
Proof. exact (TRANS (@lem5391306) (@lem5391363)). Qed.
Lemma lem5391365 : True = term390.
Proof. exact (SYM (@lem5391364)). Qed.
Lemma lem5391366 : term390.
Proof. exact (EQ_MP (@lem5391365) (@lem0)). Qed.
Lemma lem5391367 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1182 _69867 _69865 _69866) : term1183 _69865 _69866.
Proof. exact (conj (@lem5391366) (@lem5391302 _69867 _69865 _69866 h1)). Qed.
Lemma lem5391369 (x : real) (y : real) : term401 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5391370 (_69865 : int) (_69866 : int) : term1184 _69865 _69866.
Proof. exact (@lem5391369 term138 (term1115 _69865 _69866)). Qed.
Lemma lem5391371 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1182 _69867 _69865 _69866) : term1185 _69865 _69866.
Proof. exact (@lem5391370 _69865 _69866 (@lem5391367 _69867 _69865 _69866 h1)). Qed.
Lemma lem5391372 (_69865 : int) (_69866 : int) : (term1186 _69865 _69866) = (term1115 _69865 _69866).
Proof. exact (@lem1982733 (term1115 _69865 _69866)). Qed.
Lemma lem5391373 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5391374 (_69865 : int) (_69866 : int) : (term1187 _69865 _69866) = (term1116 _69865 _69866).
Proof. exact (MK_COMB (@lem5391373) (@lem5391372 _69865 _69866)). Qed.
Lemma lem5391375 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5391376 (_69865 : int) (_69866 : int) : (term1185 _69865 _69866) = (term1117 _69865 _69866).
Proof. exact (MK_COMB (@lem5391374 _69865 _69866) (@lem5391375)). Qed.
Lemma lem5391377 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1182 _69867 _69865 _69866) : term1117 _69865 _69866.
Proof. exact (EQ_MP (@lem5391376 _69865 _69866) (@lem5391371 _69867 _69865 _69866 h1)). Qed.
Lemma lem5391379 (y : real) : term453 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5391380 (_69865 : int) (_69866 : int) : term1188 _69865 _69866.
Proof. exact (@lem5391379 (term1091 _69865 _69866)). Qed.
Lemma lem5391381 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1182 _69867 _69865 _69866) : term1189 _69865 _69866.
Proof. exact (@lem5391380 _69865 _69866 (@lem5391303 _69867 _69865 _69866 h1)). Qed.
Lemma lem5391382 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1182 _69867 _69865 _69866) : term1190 _69865 _69866.
Proof. exact (@lem5391381 _69867 _69865 _69866 h1 term138). Qed.
Lemma lem5391383 (_69865 : int) (_69866 : int) : (term1190 _69865 _69866) = ((term1191 _69865 _69866) = term128).
Proof. exact (eq_refl (term1190 _69865 _69866)). Qed.
Lemma lem5391384 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1182 _69867 _69865 _69866) : (term1191 _69865 _69866) = term128.
Proof. exact (EQ_MP (@lem5391383 _69865 _69866) (@lem5391382 _69867 _69865 _69866 h1)). Qed.
Lemma lem5391385 (_69865 : int) (_69866 : int) : (term1191 _69865 _69866) = (term1091 _69865 _69866).
Proof. exact (@lem1982733 (term1091 _69865 _69866)). Qed.
Lemma lem5391386 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5391387 (_69865 : int) (_69866 : int) : (term1192 _69865 _69866) = (term1093 _69865 _69866).
Proof. exact (MK_COMB (@lem5391386) (@lem5391385 _69865 _69866)). Qed.
Lemma lem5391388 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5391389 (_69865 : int) (_69866 : int) : ((term1191 _69865 _69866) = term128) = ((term1091 _69865 _69866) = term128).
Proof. exact (MK_COMB (@lem5391387 _69865 _69866) (@lem5391388)). Qed.
Lemma lem5391390 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1182 _69867 _69865 _69866) : (term1091 _69865 _69866) = term128.
Proof. exact (EQ_MP (@lem5391389 _69865 _69866) (@lem5391384 _69867 _69865 _69866 h1)). Qed.
Lemma lem5391391 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1182 _69867 _69865 _69866) : term1151 _69865 _69866.
Proof. exact (conj (@lem5391390 _69867 _69865 _69866 h1) (@lem5391377 _69867 _69865 _69866 h1)). Qed.
Lemma lem5391393 (x : real) (y : real) : term459 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5391394 (_69865 : int) (_69866 : int) : term1193 _69865 _69866.
Proof. exact (@lem5391393 (term1091 _69865 _69866) (term1115 _69865 _69866)). Qed.
Lemma lem5391395 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1182 _69867 _69865 _69866) : term1194 _69865 _69866.
Proof. exact (@lem5391394 _69865 _69866 (@lem5391391 _69867 _69865 _69866 h1)). Qed.
Lemma lem5391396 (_69865 : int) (_69866 : int) : (term1195 _69865 _69866) = (term1196 _69865 _69866).
Proof. exact (@lem1982753 (real_of_int _69865) (term228 _69865) (term1090 _69866) (term1197 _69866)). Qed.
Lemma lem5391397 (_69865 : int) : (term464 _69865) = (term418 _69865).
Proof. exact (@lem1982715 term201 (real_of_int _69865)). Qed.
Lemma lem5391399 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5391400 : term138 = term237.
Proof. exact (@lem5391399 term44). Qed.
Lemma lem5391402 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5391403 : term201 = term202.
Proof. exact (@lem5391402 term44). Qed.
Lemma lem5391404 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5391405 : term419 = term420.
Proof. exact (MK_COMB (@lem5391404) (@lem5391403)). Qed.
Lemma lem5391406 : term421 = term422.
Proof. exact (MK_COMB (@lem5391405) (@lem5391400)). Qed.
Lemma lem5391407 : term423.
Proof. exact (@lem1981473 term201 term138 term138 term138 term128 term138). Qed.
Lemma lem5391409 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5391410 : term245 = term246.
Proof. exact (@lem5391409 (NUMERAL 0) term44). Qed.
Lemma lem5391411 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5391412 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5391413 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5391412 h1) (fun h1 : term246 = True => @lem5391411)). Qed.
Lemma lem5391414 : term246 = True.
Proof. exact (EQ_MP (@lem5391413) (@lem5391411)). Qed.
Lemma lem5391415 : term245 = True.
Proof. exact (TRANS (@lem5391410) (@lem5391414)). Qed.
Lemma lem5391416 : True = term245.
Proof. exact (SYM (@lem5391415)). Qed.
Lemma lem5391417 : term245.
Proof. exact (EQ_MP (@lem5391416) (@lem0)). Qed.
Lemma lem5391418 : term424.
Proof. exact (@lem5391407 (@lem5391417)). Qed.
Lemma lem5391420 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5391421 : term245 = term246.
Proof. exact (@lem5391420 (NUMERAL 0) term44). Qed.
Lemma lem5391422 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5391423 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5391424 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5391423 h1) (fun h1 : term246 = True => @lem5391422)). Qed.
Lemma lem5391425 : term246 = True.
Proof. exact (EQ_MP (@lem5391424) (@lem5391422)). Qed.
Lemma lem5391426 : term245 = True.
Proof. exact (TRANS (@lem5391421) (@lem5391425)). Qed.
Lemma lem5391427 : True = term245.
Proof. exact (SYM (@lem5391426)). Qed.
Lemma lem5391428 : term245.
Proof. exact (EQ_MP (@lem5391427) (@lem0)). Qed.
Lemma lem5391429 : term425.
Proof. exact (@lem5391418 (@lem5391428)). Qed.
Lemma lem5391431 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5391432 : term245 = term246.
Proof. exact (@lem5391431 (NUMERAL 0) term44). Qed.
Lemma lem5391433 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5391434 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5391435 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5391434 h1) (fun h1 : term246 = True => @lem5391433)). Qed.
Lemma lem5391436 : term246 = True.
Proof. exact (EQ_MP (@lem5391435) (@lem5391433)). Qed.
Lemma lem5391437 : term245 = True.
Proof. exact (TRANS (@lem5391432) (@lem5391436)). Qed.
Lemma lem5391438 : True = term245.
Proof. exact (SYM (@lem5391437)). Qed.
Lemma lem5391439 : term245.
Proof. exact (EQ_MP (@lem5391438) (@lem0)). Qed.
Lemma lem5391440 : term426.
Proof. exact (@lem5391429 (@lem5391439)). Qed.
Lemma lem5391442 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5391443 : term210 = term211.
Proof. exact (@lem5391442 term44 term44). Qed.
Lemma lem5391444 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5391445 : term213 = term44.
Proof. exact (EQ_MP (@lem5391444) (@lem940073)). Qed.
Lemma lem5391446 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5391447 : term211 = term138.
Proof. exact (MK_COMB (@lem5391446) (@lem5391445)). Qed.
Lemma lem5391448 : term210 = term138.
Proof. exact (TRANS (@lem5391443) (@lem5391447)). Qed.
Lemma lem5391450 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5391451 : term302 = term305.
Proof. exact (@lem5391450 term44 term44). Qed.
Lemma lem5391452 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5391453 : term213 = term44.
Proof. exact (EQ_MP (@lem5391452) (@lem940073)). Qed.
Lemma lem5391454 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5391455 : term211 = term138.
Proof. exact (MK_COMB (@lem5391454) (@lem5391453)). Qed.
Lemma lem5391456 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5391457 : term305 = term201.
Proof. exact (MK_COMB (@lem5391456) (@lem5391455)). Qed.
Lemma lem5391458 : term302 = term201.
Proof. exact (TRANS (@lem5391451) (@lem5391457)). Qed.
Lemma lem5391459 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5391460 : term427 = term419.
Proof. exact (MK_COMB (@lem5391459) (@lem5391458)). Qed.
Lemma lem5391461 : term428 = term421.
Proof. exact (MK_COMB (@lem5391460) (@lem5391448)). Qed.
Lemma lem5391463 (m : nat) : (term429 m) = term128.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5391464 : term421 = term128.
Proof. exact (@lem5391463 term44). Qed.
Lemma lem5391465 : term428 = term128.
Proof. exact (TRANS (@lem5391461) (@lem5391464)). Qed.
Lemma lem5391466 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5391467 : term430 = term431.
Proof. exact (MK_COMB (@lem5391466) (@lem5391465)). Qed.
Lemma lem5391468 : term138 = term138.
Proof. exact (eq_refl term138). Qed.
Lemma lem5391469 : term432 = term398.
Proof. exact (MK_COMB (@lem5391467) (@lem5391468)). Qed.
Lemma lem5391471 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5391472 : term398 = term128.
Proof. exact (@lem5391471 term44). Qed.
Lemma lem5391473 : term432 = term128.
Proof. exact (TRANS (@lem5391469) (@lem5391472)). Qed.
Lemma lem5391475 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5391476 : term210 = term211.
Proof. exact (@lem5391475 term44 term44). Qed.
Lemma lem5391477 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5391478 : term213 = term44.
Proof. exact (EQ_MP (@lem5391477) (@lem940073)). Qed.
Lemma lem5391479 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5391480 : term211 = term138.
Proof. exact (MK_COMB (@lem5391479) (@lem5391478)). Qed.
Lemma lem5391481 : term210 = term138.
Proof. exact (TRANS (@lem5391476) (@lem5391480)). Qed.
Lemma lem5391482 : term431 = term431.
Proof. exact (eq_refl term431). Qed.
Lemma lem5391483 : term433 = term398.
Proof. exact (MK_COMB (@lem5391482) (@lem5391481)). Qed.
Lemma lem5391485 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5391486 : term398 = term128.
Proof. exact (@lem5391485 term44). Qed.
Lemma lem5391487 : term433 = term128.
Proof. exact (TRANS (@lem5391483) (@lem5391486)). Qed.
Lemma lem5391488 : term128 = term433.
Proof. exact (SYM (@lem5391487)). Qed.
Lemma lem5391489 : term432 = term433.
Proof. exact (TRANS (@lem5391473) (@lem5391488)). Qed.
Lemma lem5391490 : term422 = term198.
Proof. exact (@lem5391440 (@lem5391489)). Qed.
Lemma lem5391491 : term421 = term198.
Proof. exact (TRANS (@lem5391406) (@lem5391490)). Qed.
Lemma lem5391493 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5391494 : term198 = term128.
Proof. exact (@lem5391493 term128). Qed.
Lemma lem5391495 : term421 = term128.
Proof. exact (TRANS (@lem5391491) (@lem5391494)). Qed.
Lemma lem5391496 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5391497 : term434 = term431.
Proof. exact (MK_COMB (@lem5391496) (@lem5391495)). Qed.
Lemma lem5391498 (_69865 : int) : (real_of_int _69865) = (real_of_int _69865).
Proof. exact (eq_refl (real_of_int _69865)). Qed.
Lemma lem5391499 (_69865 : int) : (term418 _69865) = (term435 _69865).
Proof. exact (MK_COMB (@lem5391497) (@lem5391498 _69865)). Qed.
Lemma lem5391500 (_69865 : int) : (term464 _69865) = (term435 _69865).
Proof. exact (TRANS (@lem5391397 _69865) (@lem5391499 _69865)). Qed.
Lemma lem5391501 (_69865 : int) : (term435 _69865) = term128.
Proof. exact (@lem1982719 (real_of_int _69865)). Qed.
Lemma lem5391502 (_69865 : int) : (term464 _69865) = term128.
Proof. exact (TRANS (@lem5391500 _69865) (@lem5391501 _69865)). Qed.
Lemma lem5391503 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5391504 (_69865 : int) : (term465 _69865) = term178.
Proof. exact (MK_COMB (@lem5391503) (@lem5391502 _69865)). Qed.
Lemma lem5391505 (_69866 : int) : (term1198 _69866) = (term1199 _69866).
Proof. exact (@lem1982753 (term228 _69866) (real_of_int _69866) term138 term283). Qed.
Lemma lem5391506 (_69866 : int) : (term417 _69866) = (term418 _69866).
Proof. exact (@lem1982713 term201 (real_of_int _69866)). Qed.
Lemma lem5391508 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5391509 : term138 = term237.
Proof. exact (@lem5391508 term44). Qed.
Lemma lem5391511 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5391512 : term201 = term202.
Proof. exact (@lem5391511 term44). Qed.
Lemma lem5391513 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5391514 : term419 = term420.
Proof. exact (MK_COMB (@lem5391513) (@lem5391512)). Qed.
Lemma lem5391515 : term421 = term422.
Proof. exact (MK_COMB (@lem5391514) (@lem5391509)). Qed.
Lemma lem5391516 : term423.
Proof. exact (@lem1981473 term201 term138 term138 term138 term128 term138). Qed.
Lemma lem5391518 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5391519 : term245 = term246.
Proof. exact (@lem5391518 (NUMERAL 0) term44). Qed.
Lemma lem5391520 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5391521 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5391522 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5391521 h1) (fun h1 : term246 = True => @lem5391520)). Qed.
Lemma lem5391523 : term246 = True.
Proof. exact (EQ_MP (@lem5391522) (@lem5391520)). Qed.
Lemma lem5391524 : term245 = True.
Proof. exact (TRANS (@lem5391519) (@lem5391523)). Qed.
Lemma lem5391525 : True = term245.
Proof. exact (SYM (@lem5391524)). Qed.
Lemma lem5391526 : term245.
Proof. exact (EQ_MP (@lem5391525) (@lem0)). Qed.
Lemma lem5391527 : term424.
Proof. exact (@lem5391516 (@lem5391526)). Qed.
Lemma lem5391529 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5391530 : term245 = term246.
Proof. exact (@lem5391529 (NUMERAL 0) term44). Qed.
Lemma lem5391531 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5391532 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5391533 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5391532 h1) (fun h1 : term246 = True => @lem5391531)). Qed.
Lemma lem5391534 : term246 = True.
Proof. exact (EQ_MP (@lem5391533) (@lem5391531)). Qed.
Lemma lem5391535 : term245 = True.
Proof. exact (TRANS (@lem5391530) (@lem5391534)). Qed.
Lemma lem5391536 : True = term245.
Proof. exact (SYM (@lem5391535)). Qed.
Lemma lem5391537 : term245.
Proof. exact (EQ_MP (@lem5391536) (@lem0)). Qed.
Lemma lem5391538 : term425.
Proof. exact (@lem5391527 (@lem5391537)). Qed.
Lemma lem5391540 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5391541 : term245 = term246.
Proof. exact (@lem5391540 (NUMERAL 0) term44). Qed.
Lemma lem5391542 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5391543 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5391544 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5391543 h1) (fun h1 : term246 = True => @lem5391542)). Qed.
Lemma lem5391545 : term246 = True.
Proof. exact (EQ_MP (@lem5391544) (@lem5391542)). Qed.
Lemma lem5391546 : term245 = True.
Proof. exact (TRANS (@lem5391541) (@lem5391545)). Qed.
Lemma lem5391547 : True = term245.
Proof. exact (SYM (@lem5391546)). Qed.
Lemma lem5391548 : term245.
Proof. exact (EQ_MP (@lem5391547) (@lem0)). Qed.
Lemma lem5391549 : term426.
Proof. exact (@lem5391538 (@lem5391548)). Qed.
Lemma lem5391551 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5391552 : term210 = term211.
Proof. exact (@lem5391551 term44 term44). Qed.
Lemma lem5391553 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5391554 : term213 = term44.
Proof. exact (EQ_MP (@lem5391553) (@lem940073)). Qed.
Lemma lem5391555 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5391556 : term211 = term138.
Proof. exact (MK_COMB (@lem5391555) (@lem5391554)). Qed.
Lemma lem5391557 : term210 = term138.
Proof. exact (TRANS (@lem5391552) (@lem5391556)). Qed.
Lemma lem5391559 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5391560 : term302 = term305.
Proof. exact (@lem5391559 term44 term44). Qed.
Lemma lem5391561 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5391562 : term213 = term44.
Proof. exact (EQ_MP (@lem5391561) (@lem940073)). Qed.
Lemma lem5391563 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5391564 : term211 = term138.
Proof. exact (MK_COMB (@lem5391563) (@lem5391562)). Qed.
Lemma lem5391565 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5391566 : term305 = term201.
Proof. exact (MK_COMB (@lem5391565) (@lem5391564)). Qed.
Lemma lem5391567 : term302 = term201.
Proof. exact (TRANS (@lem5391560) (@lem5391566)). Qed.
Lemma lem5391568 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5391569 : term427 = term419.
Proof. exact (MK_COMB (@lem5391568) (@lem5391567)). Qed.
Lemma lem5391570 : term428 = term421.
Proof. exact (MK_COMB (@lem5391569) (@lem5391557)). Qed.
Lemma lem5391572 (m : nat) : (term429 m) = term128.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5391573 : term421 = term128.
Proof. exact (@lem5391572 term44). Qed.
Lemma lem5391574 : term428 = term128.
Proof. exact (TRANS (@lem5391570) (@lem5391573)). Qed.
Lemma lem5391575 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5391576 : term430 = term431.
Proof. exact (MK_COMB (@lem5391575) (@lem5391574)). Qed.
Lemma lem5391577 : term138 = term138.
Proof. exact (eq_refl term138). Qed.
Lemma lem5391578 : term432 = term398.
Proof. exact (MK_COMB (@lem5391576) (@lem5391577)). Qed.
Lemma lem5391580 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5391581 : term398 = term128.
Proof. exact (@lem5391580 term44). Qed.
Lemma lem5391582 : term432 = term128.
Proof. exact (TRANS (@lem5391578) (@lem5391581)). Qed.
Lemma lem5391584 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5391585 : term210 = term211.
Proof. exact (@lem5391584 term44 term44). Qed.
Lemma lem5391586 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5391587 : term213 = term44.
Proof. exact (EQ_MP (@lem5391586) (@lem940073)). Qed.
Lemma lem5391588 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5391589 : term211 = term138.
Proof. exact (MK_COMB (@lem5391588) (@lem5391587)). Qed.
Lemma lem5391590 : term210 = term138.
Proof. exact (TRANS (@lem5391585) (@lem5391589)). Qed.
Lemma lem5391591 : term431 = term431.
Proof. exact (eq_refl term431). Qed.
Lemma lem5391592 : term433 = term398.
Proof. exact (MK_COMB (@lem5391591) (@lem5391590)). Qed.
Lemma lem5391594 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5391595 : term398 = term128.
Proof. exact (@lem5391594 term44). Qed.
Lemma lem5391596 : term433 = term128.
Proof. exact (TRANS (@lem5391592) (@lem5391595)). Qed.
Lemma lem5391597 : term128 = term433.
Proof. exact (SYM (@lem5391596)). Qed.
Lemma lem5391598 : term432 = term433.
Proof. exact (TRANS (@lem5391582) (@lem5391597)). Qed.
Lemma lem5391599 : term422 = term198.
Proof. exact (@lem5391549 (@lem5391598)). Qed.
Lemma lem5391600 : term421 = term198.
Proof. exact (TRANS (@lem5391515) (@lem5391599)). Qed.
Lemma lem5391602 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5391603 : term198 = term128.
Proof. exact (@lem5391602 term128). Qed.
Lemma lem5391604 : term421 = term128.
Proof. exact (TRANS (@lem5391600) (@lem5391603)). Qed.
Lemma lem5391605 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5391606 : term434 = term431.
Proof. exact (MK_COMB (@lem5391605) (@lem5391604)). Qed.
Lemma lem5391607 (_69866 : int) : (real_of_int _69866) = (real_of_int _69866).
Proof. exact (eq_refl (real_of_int _69866)). Qed.
Lemma lem5391608 (_69866 : int) : (term418 _69866) = (term435 _69866).
Proof. exact (MK_COMB (@lem5391606) (@lem5391607 _69866)). Qed.
Lemma lem5391609 (_69866 : int) : (term417 _69866) = (term435 _69866).
Proof. exact (TRANS (@lem5391506 _69866) (@lem5391608 _69866)). Qed.
Lemma lem5391610 (_69866 : int) : (term435 _69866) = term128.
Proof. exact (@lem1982719 (real_of_int _69866)). Qed.
Lemma lem5391611 (_69866 : int) : (term417 _69866) = term128.
Proof. exact (TRANS (@lem5391609 _69866) (@lem5391610 _69866)). Qed.
Lemma lem5391612 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5391613 (_69866 : int) : (term436 _69866) = term178.
Proof. exact (MK_COMB (@lem5391612) (@lem5391611 _69866)). Qed.
Lemma lem5391615 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5391616 : term283 = term286.
Proof. exact (@lem5391615 term257). Qed.
Lemma lem5391618 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5391619 : term138 = term237.
Proof. exact (@lem5391618 term44). Qed.
Lemma lem5391620 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5391621 : term238 = term239.
Proof. exact (MK_COMB (@lem5391620) (@lem5391619)). Qed.
Lemma lem5391622 : term1200 = term1201.
Proof. exact (MK_COMB (@lem5391621) (@lem5391616)). Qed.
Lemma lem5391623 : term1202.
Proof. exact (@lem1981473 term138 term138 term283 term138 term201 term138). Qed.
Lemma lem5391625 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5391626 : term245 = term246.
Proof. exact (@lem5391625 (NUMERAL 0) term44). Qed.
Lemma lem5391627 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5391628 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5391629 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5391628 h1) (fun h1 : term246 = True => @lem5391627)). Qed.
Lemma lem5391630 : term246 = True.
Proof. exact (EQ_MP (@lem5391629) (@lem5391627)). Qed.
Lemma lem5391631 : term245 = True.
Proof. exact (TRANS (@lem5391626) (@lem5391630)). Qed.
Lemma lem5391632 : True = term245.
Proof. exact (SYM (@lem5391631)). Qed.
Lemma lem5391633 : term245.
Proof. exact (EQ_MP (@lem5391632) (@lem0)). Qed.
Lemma lem5391634 : term1203.
Proof. exact (@lem5391623 (@lem5391633)). Qed.
Lemma lem5391636 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5391637 : term245 = term246.
Proof. exact (@lem5391636 (NUMERAL 0) term44). Qed.
Lemma lem5391638 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5391639 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5391640 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5391639 h1) (fun h1 : term246 = True => @lem5391638)). Qed.
Lemma lem5391641 : term246 = True.
Proof. exact (EQ_MP (@lem5391640) (@lem5391638)). Qed.
Lemma lem5391642 : term245 = True.
Proof. exact (TRANS (@lem5391637) (@lem5391641)). Qed.
Lemma lem5391643 : True = term245.
Proof. exact (SYM (@lem5391642)). Qed.
Lemma lem5391644 : term245.
Proof. exact (EQ_MP (@lem5391643) (@lem0)). Qed.
Lemma lem5391645 : term1204.
Proof. exact (@lem5391634 (@lem5391644)). Qed.
Lemma lem5391647 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5391648 : term245 = term246.
Proof. exact (@lem5391647 (NUMERAL 0) term44). Qed.
Lemma lem5391649 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5391650 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5391651 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5391650 h1) (fun h1 : term246 = True => @lem5391649)). Qed.
Lemma lem5391652 : term246 = True.
Proof. exact (EQ_MP (@lem5391651) (@lem5391649)). Qed.
Lemma lem5391653 : term245 = True.
Proof. exact (TRANS (@lem5391648) (@lem5391652)). Qed.
Lemma lem5391654 : True = term245.
Proof. exact (SYM (@lem5391653)). Qed.
Lemma lem5391655 : term245.
Proof. exact (EQ_MP (@lem5391654) (@lem0)). Qed.
Lemma lem5391656 : term1205.
Proof. exact (@lem5391645 (@lem5391655)). Qed.
Lemma lem5391658 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5391659 : term1206 = term1207.
Proof. exact (@lem5391658 term257 term44). Qed.
Lemma lem5391660 : term263 = term255.
Proof. exact (@lem996237 term255). Qed.
Lemma lem5391661 : (term263 = term255) = (term264 = term257).
Proof. exact (@lem1007663 term255 (BIT1 0) term255). Qed.
Lemma lem5391662 : term264 = term257.
Proof. exact (EQ_MP (@lem5391661) (@lem5391660)). Qed.
Lemma lem5391663 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5391664 : term262 = term243.
Proof. exact (MK_COMB (@lem5391663) (@lem5391662)). Qed.
Lemma lem5391665 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5391666 : term1207 = term283.
Proof. exact (MK_COMB (@lem5391665) (@lem5391664)). Qed.
Lemma lem5391667 : term1206 = term283.
Proof. exact (TRANS (@lem5391659) (@lem5391666)). Qed.
Lemma lem5391669 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5391670 : term210 = term211.
Proof. exact (@lem5391669 term44 term44). Qed.
Lemma lem5391671 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5391672 : term213 = term44.
Proof. exact (EQ_MP (@lem5391671) (@lem940073)). Qed.
Lemma lem5391673 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5391674 : term211 = term138.
Proof. exact (MK_COMB (@lem5391673) (@lem5391672)). Qed.
Lemma lem5391675 : term210 = term138.
Proof. exact (TRANS (@lem5391670) (@lem5391674)). Qed.
Lemma lem5391676 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5391677 : term251 = term238.
Proof. exact (MK_COMB (@lem5391676) (@lem5391675)). Qed.
Lemma lem5391678 : term1208 = term1200.
Proof. exact (MK_COMB (@lem5391677) (@lem5391667)). Qed.
Lemma lem5391681 : term1209 = term201.
Proof. exact (@lem1367771 term44 term44). Qed.
Lemma lem5391682 : term254 = term255.
Proof. exact (@lem706885). Qed.
Lemma lem5391683 : (term254 = term255) = (term256 = term257).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term255). Qed.
Lemma lem5391684 : term256 = term257.
Proof. exact (EQ_MP (@lem5391683) (@lem5391682)). Qed.
Lemma lem5391685 : term257 = term256.
Proof. exact (SYM (@lem5391684)). Qed.
Lemma lem5391686 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5391687 : term243 = term253.
Proof. exact (MK_COMB (@lem5391686) (@lem5391685)). Qed.
Lemma lem5391688 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5391689 : term283 = term1210.
Proof. exact (MK_COMB (@lem5391688) (@lem5391687)). Qed.
Lemma lem5391690 : term238 = term238.
Proof. exact (eq_refl term238). Qed.
Lemma lem5391691 : term1200 = term1209.
Proof. exact (MK_COMB (@lem5391690) (@lem5391689)). Qed.
Lemma lem5391692 : term1200 = term201.
Proof. exact (TRANS (@lem5391691) (@lem5391681)). Qed.
Lemma lem5391693 : term1208 = term201.
Proof. exact (TRANS (@lem5391678) (@lem5391692)). Qed.
Lemma lem5391694 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5391695 : term1211 = term203.
Proof. exact (MK_COMB (@lem5391694) (@lem5391693)). Qed.
Lemma lem5391696 : term138 = term138.
Proof. exact (eq_refl term138). Qed.
Lemma lem5391697 : term1212 = term302.
Proof. exact (MK_COMB (@lem5391695) (@lem5391696)). Qed.
Lemma lem5391699 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5391700 : term302 = term305.
Proof. exact (@lem5391699 term44 term44). Qed.
Lemma lem5391701 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5391702 : term213 = term44.
Proof. exact (EQ_MP (@lem5391701) (@lem940073)). Qed.
Lemma lem5391703 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5391704 : term211 = term138.
Proof. exact (MK_COMB (@lem5391703) (@lem5391702)). Qed.
Lemma lem5391705 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5391706 : term305 = term201.
Proof. exact (MK_COMB (@lem5391705) (@lem5391704)). Qed.
Lemma lem5391707 : term302 = term201.
Proof. exact (TRANS (@lem5391700) (@lem5391706)). Qed.
Lemma lem5391708 : term1212 = term201.
Proof. exact (TRANS (@lem5391697) (@lem5391707)). Qed.
Lemma lem5391710 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5391711 : term210 = term211.
Proof. exact (@lem5391710 term44 term44). Qed.
Lemma lem5391712 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5391713 : term213 = term44.
Proof. exact (EQ_MP (@lem5391712) (@lem940073)). Qed.
Lemma lem5391714 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5391715 : term211 = term138.
Proof. exact (MK_COMB (@lem5391714) (@lem5391713)). Qed.
Lemma lem5391716 : term210 = term138.
Proof. exact (TRANS (@lem5391711) (@lem5391715)). Qed.
Lemma lem5391717 : term203 = term203.
Proof. exact (eq_refl term203). Qed.
Lemma lem5391718 : term1213 = term302.
Proof. exact (MK_COMB (@lem5391717) (@lem5391716)). Qed.
Lemma lem5391720 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5391721 : term302 = term305.
Proof. exact (@lem5391720 term44 term44). Qed.
Lemma lem5391722 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5391723 : term213 = term44.
Proof. exact (EQ_MP (@lem5391722) (@lem940073)). Qed.
Lemma lem5391724 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5391725 : term211 = term138.
Proof. exact (MK_COMB (@lem5391724) (@lem5391723)). Qed.
Lemma lem5391726 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5391727 : term305 = term201.
Proof. exact (MK_COMB (@lem5391726) (@lem5391725)). Qed.
Lemma lem5391728 : term302 = term201.
Proof. exact (TRANS (@lem5391721) (@lem5391727)). Qed.
Lemma lem5391729 : term1213 = term201.
Proof. exact (TRANS (@lem5391718) (@lem5391728)). Qed.
Lemma lem5391730 : term201 = term1213.
Proof. exact (SYM (@lem5391729)). Qed.
Lemma lem5391731 : term1212 = term1213.
Proof. exact (TRANS (@lem5391708) (@lem5391730)). Qed.
Lemma lem5391732 : term1201 = term202.
Proof. exact (@lem5391656 (@lem5391731)). Qed.
Lemma lem5391733 : term1200 = term202.
Proof. exact (TRANS (@lem5391622) (@lem5391732)). Qed.
Lemma lem5391735 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5391736 : term202 = term201.
Proof. exact (@lem5391735 term201). Qed.
Lemma lem5391737 : term1200 = term201.
Proof. exact (TRANS (@lem5391733) (@lem5391736)). Qed.
Lemma lem5391738 (_69866 : int) : (term1199 _69866) = term437.
Proof. exact (MK_COMB (@lem5391613 _69866) (@lem5391737)). Qed.
Lemma lem5391739 (_69866 : int) : (term1198 _69866) = term437.
Proof. exact (TRANS (@lem5391505 _69866) (@lem5391738 _69866)). Qed.
Lemma lem5391740 : term437 = term201.
Proof. exact (@lem1982721 term201). Qed.
Lemma lem5391741 (_69866 : int) : (term1198 _69866) = term201.
Proof. exact (TRANS (@lem5391739 _69866) (@lem5391740)). Qed.
Lemma lem5391742 (_69865 : int) (_69866 : int) : (term1196 _69865 _69866) = term437.
Proof. exact (MK_COMB (@lem5391504 _69865) (@lem5391741 _69866)). Qed.
Lemma lem5391743 (_69865 : int) (_69866 : int) : (term1195 _69865 _69866) = term437.
Proof. exact (TRANS (@lem5391396 _69865 _69866) (@lem5391742 _69865 _69866)). Qed.
Lemma lem5391744 : term437 = term201.
Proof. exact (@lem1982721 term201). Qed.
Lemma lem5391745 (_69865 : int) (_69866 : int) : (term1195 _69865 _69866) = term201.
Proof. exact (TRANS (@lem5391743 _69865 _69866) (@lem5391744)). Qed.
Lemma lem5391746 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5391747 (_69865 : int) (_69866 : int) : (term1214 _69865 _69866) = term439.
Proof. exact (MK_COMB (@lem5391746) (@lem5391745 _69865 _69866)). Qed.
Lemma lem5391748 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5391749 (_69865 : int) (_69866 : int) : (term1194 _69865 _69866) = term440.
Proof. exact (MK_COMB (@lem5391747 _69865 _69866) (@lem5391748)). Qed.
Lemma lem5391750 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1182 _69867 _69865 _69866) : term440.
Proof. exact (EQ_MP (@lem5391749 _69865 _69866) (@lem5391395 _69867 _69865 _69866 h1)). Qed.
Lemma lem5391752 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5391753 : term440 = term441.
Proof. exact (@lem5391752 term128 term201). Qed.
Lemma lem5391755 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5391756 : term201 = term202.
Proof. exact (@lem5391755 term44). Qed.
Lemma lem5391758 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5391759 : term128 = term198.
Proof. exact (@lem5391758 (NUMERAL 0)). Qed.
Lemma lem5391760 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5391761 : term130 = term442.
Proof. exact (MK_COMB (@lem5391760) (@lem5391759)). Qed.
Lemma lem5391762 : term441 = term443.
Proof. exact (MK_COMB (@lem5391761) (@lem5391756)). Qed.
Lemma lem5391763 : term444.
Proof. exact (@lem1980026 term128 term138 term201 term138). Qed.
Lemma lem5391765 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5391766 : term245 = term246.
Proof. exact (@lem5391765 (NUMERAL 0) term44). Qed.
Lemma lem5391767 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5391768 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5391769 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5391768 h1) (fun h1 : term246 = True => @lem5391767)). Qed.
Lemma lem5391770 : term246 = True.
Proof. exact (EQ_MP (@lem5391769) (@lem5391767)). Qed.
Lemma lem5391771 : term245 = True.
Proof. exact (TRANS (@lem5391766) (@lem5391770)). Qed.
Lemma lem5391772 : True = term245.
Proof. exact (SYM (@lem5391771)). Qed.
Lemma lem5391773 : term245.
Proof. exact (EQ_MP (@lem5391772) (@lem0)). Qed.
Lemma lem5391774 : term445.
Proof. exact (@lem5391763 (@lem5391773)). Qed.
Lemma lem5391776 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5391777 : term245 = term246.
Proof. exact (@lem5391776 (NUMERAL 0) term44). Qed.
Lemma lem5391778 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5391779 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5391780 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5391779 h1) (fun h1 : term246 = True => @lem5391778)). Qed.
Lemma lem5391781 : term246 = True.
Proof. exact (EQ_MP (@lem5391780) (@lem5391778)). Qed.
Lemma lem5391782 : term245 = True.
Proof. exact (TRANS (@lem5391777) (@lem5391781)). Qed.
Lemma lem5391783 : True = term245.
Proof. exact (SYM (@lem5391782)). Qed.
Lemma lem5391784 : term245.
Proof. exact (EQ_MP (@lem5391783) (@lem0)). Qed.
Lemma lem5391785 : term443 = term446.
Proof. exact (@lem5391774 (@lem5391784)). Qed.
Lemma lem5391787 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5391788 : term302 = term305.
Proof. exact (@lem5391787 term44 term44). Qed.
Lemma lem5391789 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5391790 : term213 = term44.
Proof. exact (EQ_MP (@lem5391789) (@lem940073)). Qed.
Lemma lem5391791 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5391792 : term211 = term138.
Proof. exact (MK_COMB (@lem5391791) (@lem5391790)). Qed.
Lemma lem5391793 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5391794 : term305 = term201.
Proof. exact (MK_COMB (@lem5391793) (@lem5391792)). Qed.
Lemma lem5391795 : term302 = term201.
Proof. exact (TRANS (@lem5391788) (@lem5391794)). Qed.
Lemma lem5391797 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5391798 : term398 = term128.
Proof. exact (@lem5391797 term44). Qed.
Lemma lem5391799 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5391800 : term447 = term130.
Proof. exact (MK_COMB (@lem5391799) (@lem5391798)). Qed.
Lemma lem5391801 : term446 = term441.
Proof. exact (MK_COMB (@lem5391800) (@lem5391795)). Qed.
Lemma lem5391803 (m : nat) (n : nat) : (term448 m n) = (term449 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5391804 : term441 = term450.
Proof. exact (@lem5391803 (NUMERAL 0) term44). Qed.
Lemma lem5391805 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5391806 (h1 : term247 = (BIT1 0)) : (term44 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5391807 : (term247 = (BIT1 0)) = ((term44 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5391806 h1) (fun h1 : (term44 = (NUMERAL 0)) = False => @lem5391805)). Qed.
Lemma lem5391808 : (term44 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5391807) (@lem5391805)). Qed.
Lemma lem5391809 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5391810 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5391811 : term451 = (and True).
Proof. exact (MK_COMB (@lem5391810) (@lem5391809)). Qed.
Lemma lem5391812 : term450 = (True /\ False).
Proof. exact (MK_COMB (@lem5391811) (@lem5391808)). Qed.
Lemma lem5391814 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5391815 : term450 = False.
Proof. exact (TRANS (@lem5391812) (@lem5391814)). Qed.
Lemma lem5391816 : term441 = False.
Proof. exact (TRANS (@lem5391804) (@lem5391815)). Qed.
Lemma lem5391817 : term446 = False.
Proof. exact (TRANS (@lem5391801) (@lem5391816)). Qed.
Lemma lem5391818 : term443 = False.
Proof. exact (TRANS (@lem5391785) (@lem5391817)). Qed.
Lemma lem5391819 : term441 = False.
Proof. exact (TRANS (@lem5391762) (@lem5391818)). Qed.
Lemma lem5391820 : term440 = False.
Proof. exact (TRANS (@lem5391753) (@lem5391819)). Qed.
Lemma lem5391821 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1182 _69867 _69865 _69866) : False.
Proof. exact (EQ_MP (@lem5391820) (@lem5391750 _69867 _69865 _69866 h1)). Qed.
Lemma lem5391822 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1215 _69867 _69865 _69866) : term1215 _69867 _69865 _69866.
Proof. exact (h1). Qed.
Lemma lem5391823 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1215 _69867 _69865 _69866) : term1178 _69867 _69865 _69866.
Proof. exact (proj2 (@lem5391822 _69867 _69865 _69866 h1)). Qed.
Lemma lem5391824 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1215 _69867 _69865 _69866) : term221 _69865.
Proof. exact (proj1 (@lem5391822 _69867 _69865 _69866 h1)). Qed.
Lemma lem5391825 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1215 _69867 _69865 _69866) : term1165 _69867 _69865 _69866.
Proof. exact (proj2 (@lem5391823 _69867 _69865 _69866 h1)). Qed.
Lemma lem5391827 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1215 _69867 _69865 _69866) : term1152 _69865 _69866.
Proof. exact (proj2 (@lem5391825 _69867 _69865 _69866 h1)). Qed.
Lemma lem5391829 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1215 _69867 _69865 _69866) : term1117 _69865 _69866.
Proof. exact (proj2 (@lem5391827 _69867 _69865 _69866 h1)). Qed.
Lemma lem5391830 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1215 _69867 _69865 _69866) : term1112 _69865 _69866.
Proof. exact (proj1 (@lem5391827 _69867 _69865 _69866 h1)). Qed.
Lemma lem5391831 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1215 _69867 _69865 _69866) : (real_of_int _69866) = term128.
Proof. exact (proj2 (@lem5391830 _69867 _69865 _69866 h1)). Qed.
Lemma lem5391834 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5391835 : term390 = term245.
Proof. exact (@lem5391834 term128 term138). Qed.
Lemma lem5391837 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5391838 : term138 = term237.
Proof. exact (@lem5391837 term44). Qed.
Lemma lem5391840 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5391841 : term128 = term198.
Proof. exact (@lem5391840 (NUMERAL 0)). Qed.
Lemma lem5391842 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5391843 : term391 = term392.
Proof. exact (MK_COMB (@lem5391842) (@lem5391841)). Qed.
Lemma lem5391844 : term245 = term393.
Proof. exact (MK_COMB (@lem5391843) (@lem5391838)). Qed.
Lemma lem5391845 : term394.
Proof. exact (@lem1980255 term128 term138 term138 term138). Qed.
Lemma lem5391847 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5391848 : term245 = term246.
Proof. exact (@lem5391847 (NUMERAL 0) term44). Qed.
Lemma lem5391849 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5391850 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5391851 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5391850 h1) (fun h1 : term246 = True => @lem5391849)). Qed.
Lemma lem5391852 : term246 = True.
Proof. exact (EQ_MP (@lem5391851) (@lem5391849)). Qed.
Lemma lem5391853 : term245 = True.
Proof. exact (TRANS (@lem5391848) (@lem5391852)). Qed.
Lemma lem5391854 : True = term245.
Proof. exact (SYM (@lem5391853)). Qed.
Lemma lem5391855 : term245.
Proof. exact (EQ_MP (@lem5391854) (@lem0)). Qed.
Lemma lem5391856 : term395.
Proof. exact (@lem5391845 (@lem5391855)). Qed.
Lemma lem5391858 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5391859 : term245 = term246.
Proof. exact (@lem5391858 (NUMERAL 0) term44). Qed.
Lemma lem5391860 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5391861 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5391862 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5391861 h1) (fun h1 : term246 = True => @lem5391860)). Qed.
Lemma lem5391863 : term246 = True.
Proof. exact (EQ_MP (@lem5391862) (@lem5391860)). Qed.
Lemma lem5391864 : term245 = True.
Proof. exact (TRANS (@lem5391859) (@lem5391863)). Qed.
Lemma lem5391865 : True = term245.
Proof. exact (SYM (@lem5391864)). Qed.
Lemma lem5391866 : term245.
Proof. exact (EQ_MP (@lem5391865) (@lem0)). Qed.
Lemma lem5391867 : term393 = term396.
Proof. exact (@lem5391856 (@lem5391866)). Qed.
Lemma lem5391869 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5391870 : term210 = term211.
Proof. exact (@lem5391869 term44 term44). Qed.
Lemma lem5391871 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5391872 : term213 = term44.
Proof. exact (EQ_MP (@lem5391871) (@lem940073)). Qed.
Lemma lem5391873 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5391874 : term211 = term138.
Proof. exact (MK_COMB (@lem5391873) (@lem5391872)). Qed.
Lemma lem5391875 : term210 = term138.
Proof. exact (TRANS (@lem5391870) (@lem5391874)). Qed.
Lemma lem5391877 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5391878 : term398 = term128.
Proof. exact (@lem5391877 term44). Qed.
Lemma lem5391879 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5391880 : term399 = term391.
Proof. exact (MK_COMB (@lem5391879) (@lem5391878)). Qed.
Lemma lem5391881 : term396 = term245.
Proof. exact (MK_COMB (@lem5391880) (@lem5391875)). Qed.
Lemma lem5391883 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5391884 : term245 = term246.
Proof. exact (@lem5391883 (NUMERAL 0) term44). Qed.
Lemma lem5391885 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5391886 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5391887 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5391886 h1) (fun h1 : term246 = True => @lem5391885)). Qed.
Lemma lem5391888 : term246 = True.
Proof. exact (EQ_MP (@lem5391887) (@lem5391885)). Qed.
Lemma lem5391889 : term245 = True.
Proof. exact (TRANS (@lem5391884) (@lem5391888)). Qed.
Lemma lem5391890 : term396 = True.
Proof. exact (TRANS (@lem5391881) (@lem5391889)). Qed.
Lemma lem5391891 : term393 = True.
Proof. exact (TRANS (@lem5391867) (@lem5391890)). Qed.
Lemma lem5391892 : term245 = True.
Proof. exact (TRANS (@lem5391844) (@lem5391891)). Qed.
Lemma lem5391893 : term390 = True.
Proof. exact (TRANS (@lem5391835) (@lem5391892)). Qed.
Lemma lem5391894 : True = term390.
Proof. exact (SYM (@lem5391893)). Qed.
Lemma lem5391895 : term390.
Proof. exact (EQ_MP (@lem5391894) (@lem0)). Qed.
Lemma lem5391896 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1215 _69867 _69865 _69866) : term400 _69865.
Proof. exact (conj (@lem5391895) (@lem5391824 _69867 _69865 _69866 h1)). Qed.
Lemma lem5391898 (x : real) (y : real) : term401 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5391899 (_69865 : int) : term402 _69865.
Proof. exact (@lem5391898 term138 (real_of_int _69865)). Qed.
Lemma lem5391900 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1215 _69867 _69865 _69866) : term403 _69865.
Proof. exact (@lem5391899 _69865 (@lem5391896 _69867 _69865 _69866 h1)). Qed.
Lemma lem5391901 (_69865 : int) : (term404 _69865) = (real_of_int _69865).
Proof. exact (@lem1982733 (real_of_int _69865)). Qed.
Lemma lem5391902 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5391903 (_69865 : int) : (term405 _69865) = (term220 _69865).
Proof. exact (MK_COMB (@lem5391902) (@lem5391901 _69865)). Qed.
Lemma lem5391904 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5391905 (_69865 : int) : (term403 _69865) = (term221 _69865).
Proof. exact (MK_COMB (@lem5391903 _69865) (@lem5391904)). Qed.
Lemma lem5391906 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1215 _69867 _69865 _69866) : term221 _69865.
Proof. exact (EQ_MP (@lem5391905 _69865) (@lem5391900 _69867 _69865 _69866 h1)). Qed.
Lemma lem5391908 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5391909 : term390 = term245.
Proof. exact (@lem5391908 term128 term138). Qed.
Lemma lem5391911 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5391912 : term138 = term237.
Proof. exact (@lem5391911 term44). Qed.
Lemma lem5391914 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5391915 : term128 = term198.
Proof. exact (@lem5391914 (NUMERAL 0)). Qed.
Lemma lem5391916 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5391917 : term391 = term392.
Proof. exact (MK_COMB (@lem5391916) (@lem5391915)). Qed.
Lemma lem5391918 : term245 = term393.
Proof. exact (MK_COMB (@lem5391917) (@lem5391912)). Qed.
Lemma lem5391919 : term394.
Proof. exact (@lem1980255 term128 term138 term138 term138). Qed.
Lemma lem5391921 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5391922 : term245 = term246.
Proof. exact (@lem5391921 (NUMERAL 0) term44). Qed.
Lemma lem5391923 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5391924 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5391925 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5391924 h1) (fun h1 : term246 = True => @lem5391923)). Qed.
Lemma lem5391926 : term246 = True.
Proof. exact (EQ_MP (@lem5391925) (@lem5391923)). Qed.
Lemma lem5391927 : term245 = True.
Proof. exact (TRANS (@lem5391922) (@lem5391926)). Qed.
Lemma lem5391928 : True = term245.
Proof. exact (SYM (@lem5391927)). Qed.
Lemma lem5391929 : term245.
Proof. exact (EQ_MP (@lem5391928) (@lem0)). Qed.
Lemma lem5391930 : term395.
Proof. exact (@lem5391919 (@lem5391929)). Qed.
Lemma lem5391932 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5391933 : term245 = term246.
Proof. exact (@lem5391932 (NUMERAL 0) term44). Qed.
Lemma lem5391934 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5391935 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5391936 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5391935 h1) (fun h1 : term246 = True => @lem5391934)). Qed.
Lemma lem5391937 : term246 = True.
Proof. exact (EQ_MP (@lem5391936) (@lem5391934)). Qed.
Lemma lem5391938 : term245 = True.
Proof. exact (TRANS (@lem5391933) (@lem5391937)). Qed.
Lemma lem5391939 : True = term245.
Proof. exact (SYM (@lem5391938)). Qed.
Lemma lem5391940 : term245.
Proof. exact (EQ_MP (@lem5391939) (@lem0)). Qed.
Lemma lem5391941 : term393 = term396.
Proof. exact (@lem5391930 (@lem5391940)). Qed.
Lemma lem5391943 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5391944 : term210 = term211.
Proof. exact (@lem5391943 term44 term44). Qed.
Lemma lem5391945 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5391946 : term213 = term44.
Proof. exact (EQ_MP (@lem5391945) (@lem940073)). Qed.
Lemma lem5391947 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5391948 : term211 = term138.
Proof. exact (MK_COMB (@lem5391947) (@lem5391946)). Qed.
Lemma lem5391949 : term210 = term138.
Proof. exact (TRANS (@lem5391944) (@lem5391948)). Qed.
Lemma lem5391951 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5391952 : term398 = term128.
Proof. exact (@lem5391951 term44). Qed.
Lemma lem5391953 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5391954 : term399 = term391.
Proof. exact (MK_COMB (@lem5391953) (@lem5391952)). Qed.
Lemma lem5391955 : term396 = term245.
Proof. exact (MK_COMB (@lem5391954) (@lem5391949)). Qed.
Lemma lem5391957 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5391958 : term245 = term246.
Proof. exact (@lem5391957 (NUMERAL 0) term44). Qed.
Lemma lem5391959 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5391960 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5391961 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5391960 h1) (fun h1 : term246 = True => @lem5391959)). Qed.
Lemma lem5391962 : term246 = True.
Proof. exact (EQ_MP (@lem5391961) (@lem5391959)). Qed.
Lemma lem5391963 : term245 = True.
Proof. exact (TRANS (@lem5391958) (@lem5391962)). Qed.
Lemma lem5391964 : term396 = True.
Proof. exact (TRANS (@lem5391955) (@lem5391963)). Qed.
Lemma lem5391965 : term393 = True.
Proof. exact (TRANS (@lem5391941) (@lem5391964)). Qed.
Lemma lem5391966 : term245 = True.
Proof. exact (TRANS (@lem5391918) (@lem5391965)). Qed.
Lemma lem5391967 : term390 = True.
Proof. exact (TRANS (@lem5391909) (@lem5391966)). Qed.
Lemma lem5391968 : True = term390.
Proof. exact (SYM (@lem5391967)). Qed.
Lemma lem5391969 : term390.
Proof. exact (EQ_MP (@lem5391968) (@lem0)). Qed.
Lemma lem5391970 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1215 _69867 _69865 _69866) : term1183 _69865 _69866.
Proof. exact (conj (@lem5391969) (@lem5391829 _69867 _69865 _69866 h1)). Qed.
Lemma lem5391972 (x : real) (y : real) : term401 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5391973 (_69865 : int) (_69866 : int) : term1184 _69865 _69866.
Proof. exact (@lem5391972 term138 (term1115 _69865 _69866)). Qed.
Lemma lem5391974 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1215 _69867 _69865 _69866) : term1185 _69865 _69866.
Proof. exact (@lem5391973 _69865 _69866 (@lem5391970 _69867 _69865 _69866 h1)). Qed.
Lemma lem5391975 (_69865 : int) (_69866 : int) : (term1186 _69865 _69866) = (term1115 _69865 _69866).
Proof. exact (@lem1982733 (term1115 _69865 _69866)). Qed.
Lemma lem5391976 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5391977 (_69865 : int) (_69866 : int) : (term1187 _69865 _69866) = (term1116 _69865 _69866).
Proof. exact (MK_COMB (@lem5391976) (@lem5391975 _69865 _69866)). Qed.
Lemma lem5391978 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5391979 (_69865 : int) (_69866 : int) : (term1185 _69865 _69866) = (term1117 _69865 _69866).
Proof. exact (MK_COMB (@lem5391977 _69865 _69866) (@lem5391978)). Qed.
Lemma lem5391980 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1215 _69867 _69865 _69866) : term1117 _69865 _69866.
Proof. exact (EQ_MP (@lem5391979 _69865 _69866) (@lem5391974 _69867 _69865 _69866 h1)). Qed.
Lemma lem5391982 (y : real) : term453 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5391983 (_69866 : int) : term454 _69866.
Proof. exact (@lem5391982 (real_of_int _69866)). Qed.
Lemma lem5391984 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1215 _69867 _69865 _69866) : term455 _69866.
Proof. exact (@lem5391983 _69866 (@lem5391831 _69867 _69865 _69866 h1)). Qed.
Lemma lem5391985 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1215 _69867 _69865 _69866) : term518 _69866.
Proof. exact (@lem5391984 _69867 _69865 _69866 h1 term201). Qed.
Lemma lem5391986 (_69866 : int) : (term518 _69866) = ((term228 _69866) = term128).
Proof. exact (eq_refl (term518 _69866)). Qed.
Lemma lem5391993 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1215 _69867 _69865 _69866) : (term228 _69866) = term128.
Proof. exact (EQ_MP (@lem5391986 _69866) (@lem5391985 _69867 _69865 _69866 h1)). Qed.
Lemma lem5391994 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1215 _69867 _69865 _69866) : term1216 _69865 _69866.
Proof. exact (conj (@lem5391993 _69867 _69865 _69866 h1) (@lem5391980 _69867 _69865 _69866 h1)). Qed.
Lemma lem5391996 (x : real) (y : real) : term459 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5391997 (_69865 : int) (_69866 : int) : term1217 _69865 _69866.
Proof. exact (@lem5391996 (term228 _69866) (term1115 _69865 _69866)). Qed.
Lemma lem5391998 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1215 _69867 _69865 _69866) : term1218 _69865 _69866.
Proof. exact (@lem5391997 _69865 _69866 (@lem5391994 _69867 _69865 _69866 h1)). Qed.
Lemma lem5391999 (_69865 : int) (_69866 : int) : (term1219 _69865 _69866) = (term1220 _69865 _69866).
Proof. exact (@lem1982757 (term228 _69865) (term228 _69866) (term1197 _69866)). Qed.
Lemma lem5392000 (_69866 : int) : (term1221 _69866) = (term1222 _69866).
Proof. exact (@lem1982763 (term228 _69866) (real_of_int _69866) term283). Qed.
Lemma lem5392001 (_69866 : int) : (term417 _69866) = (term418 _69866).
Proof. exact (@lem1982713 term201 (real_of_int _69866)). Qed.
Lemma lem5392003 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5392004 : term138 = term237.
Proof. exact (@lem5392003 term44). Qed.
Lemma lem5392006 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5392007 : term201 = term202.
Proof. exact (@lem5392006 term44). Qed.
Lemma lem5392008 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5392009 : term419 = term420.
Proof. exact (MK_COMB (@lem5392008) (@lem5392007)). Qed.
Lemma lem5392010 : term421 = term422.
Proof. exact (MK_COMB (@lem5392009) (@lem5392004)). Qed.
Lemma lem5392011 : term423.
Proof. exact (@lem1981473 term201 term138 term138 term138 term128 term138). Qed.
Lemma lem5392013 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5392014 : term245 = term246.
Proof. exact (@lem5392013 (NUMERAL 0) term44). Qed.
Lemma lem5392015 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5392016 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5392017 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5392016 h1) (fun h1 : term246 = True => @lem5392015)). Qed.
Lemma lem5392018 : term246 = True.
Proof. exact (EQ_MP (@lem5392017) (@lem5392015)). Qed.
Lemma lem5392019 : term245 = True.
Proof. exact (TRANS (@lem5392014) (@lem5392018)). Qed.
Lemma lem5392020 : True = term245.
Proof. exact (SYM (@lem5392019)). Qed.
Lemma lem5392021 : term245.
Proof. exact (EQ_MP (@lem5392020) (@lem0)). Qed.
Lemma lem5392022 : term424.
Proof. exact (@lem5392011 (@lem5392021)). Qed.
Lemma lem5392024 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5392025 : term245 = term246.
Proof. exact (@lem5392024 (NUMERAL 0) term44). Qed.
Lemma lem5392026 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5392027 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5392028 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5392027 h1) (fun h1 : term246 = True => @lem5392026)). Qed.
Lemma lem5392029 : term246 = True.
Proof. exact (EQ_MP (@lem5392028) (@lem5392026)). Qed.
Lemma lem5392030 : term245 = True.
Proof. exact (TRANS (@lem5392025) (@lem5392029)). Qed.
Lemma lem5392031 : True = term245.
Proof. exact (SYM (@lem5392030)). Qed.
Lemma lem5392032 : term245.
Proof. exact (EQ_MP (@lem5392031) (@lem0)). Qed.
Lemma lem5392033 : term425.
Proof. exact (@lem5392022 (@lem5392032)). Qed.
Lemma lem5392035 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5392036 : term245 = term246.
Proof. exact (@lem5392035 (NUMERAL 0) term44). Qed.
Lemma lem5392037 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5392038 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5392039 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5392038 h1) (fun h1 : term246 = True => @lem5392037)). Qed.
Lemma lem5392040 : term246 = True.
Proof. exact (EQ_MP (@lem5392039) (@lem5392037)). Qed.
Lemma lem5392041 : term245 = True.
Proof. exact (TRANS (@lem5392036) (@lem5392040)). Qed.
Lemma lem5392042 : True = term245.
Proof. exact (SYM (@lem5392041)). Qed.
Lemma lem5392043 : term245.
Proof. exact (EQ_MP (@lem5392042) (@lem0)). Qed.
Lemma lem5392044 : term426.
Proof. exact (@lem5392033 (@lem5392043)). Qed.
Lemma lem5392046 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5392047 : term210 = term211.
Proof. exact (@lem5392046 term44 term44). Qed.
Lemma lem5392048 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5392049 : term213 = term44.
Proof. exact (EQ_MP (@lem5392048) (@lem940073)). Qed.
Lemma lem5392050 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5392051 : term211 = term138.
Proof. exact (MK_COMB (@lem5392050) (@lem5392049)). Qed.
Lemma lem5392052 : term210 = term138.
Proof. exact (TRANS (@lem5392047) (@lem5392051)). Qed.
Lemma lem5392054 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5392055 : term302 = term305.
Proof. exact (@lem5392054 term44 term44). Qed.
Lemma lem5392056 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5392057 : term213 = term44.
Proof. exact (EQ_MP (@lem5392056) (@lem940073)). Qed.
Lemma lem5392058 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5392059 : term211 = term138.
Proof. exact (MK_COMB (@lem5392058) (@lem5392057)). Qed.
Lemma lem5392060 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5392061 : term305 = term201.
Proof. exact (MK_COMB (@lem5392060) (@lem5392059)). Qed.
Lemma lem5392062 : term302 = term201.
Proof. exact (TRANS (@lem5392055) (@lem5392061)). Qed.
Lemma lem5392063 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5392064 : term427 = term419.
Proof. exact (MK_COMB (@lem5392063) (@lem5392062)). Qed.
Lemma lem5392065 : term428 = term421.
Proof. exact (MK_COMB (@lem5392064) (@lem5392052)). Qed.
Lemma lem5392067 (m : nat) : (term429 m) = term128.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5392068 : term421 = term128.
Proof. exact (@lem5392067 term44). Qed.
Lemma lem5392069 : term428 = term128.
Proof. exact (TRANS (@lem5392065) (@lem5392068)). Qed.
Lemma lem5392070 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5392071 : term430 = term431.
Proof. exact (MK_COMB (@lem5392070) (@lem5392069)). Qed.
Lemma lem5392072 : term138 = term138.
Proof. exact (eq_refl term138). Qed.
Lemma lem5392073 : term432 = term398.
Proof. exact (MK_COMB (@lem5392071) (@lem5392072)). Qed.
Lemma lem5392075 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5392076 : term398 = term128.
Proof. exact (@lem5392075 term44). Qed.
Lemma lem5392077 : term432 = term128.
Proof. exact (TRANS (@lem5392073) (@lem5392076)). Qed.
Lemma lem5392079 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5392080 : term210 = term211.
Proof. exact (@lem5392079 term44 term44). Qed.
Lemma lem5392081 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5392082 : term213 = term44.
Proof. exact (EQ_MP (@lem5392081) (@lem940073)). Qed.
Lemma lem5392083 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5392084 : term211 = term138.
Proof. exact (MK_COMB (@lem5392083) (@lem5392082)). Qed.
Lemma lem5392085 : term210 = term138.
Proof. exact (TRANS (@lem5392080) (@lem5392084)). Qed.
Lemma lem5392086 : term431 = term431.
Proof. exact (eq_refl term431). Qed.
Lemma lem5392087 : term433 = term398.
Proof. exact (MK_COMB (@lem5392086) (@lem5392085)). Qed.
Lemma lem5392089 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5392090 : term398 = term128.
Proof. exact (@lem5392089 term44). Qed.
Lemma lem5392091 : term433 = term128.
Proof. exact (TRANS (@lem5392087) (@lem5392090)). Qed.
Lemma lem5392092 : term128 = term433.
Proof. exact (SYM (@lem5392091)). Qed.
Lemma lem5392093 : term432 = term433.
Proof. exact (TRANS (@lem5392077) (@lem5392092)). Qed.
Lemma lem5392094 : term422 = term198.
Proof. exact (@lem5392044 (@lem5392093)). Qed.
Lemma lem5392095 : term421 = term198.
Proof. exact (TRANS (@lem5392010) (@lem5392094)). Qed.
Lemma lem5392097 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5392098 : term198 = term128.
Proof. exact (@lem5392097 term128). Qed.
Lemma lem5392099 : term421 = term128.
Proof. exact (TRANS (@lem5392095) (@lem5392098)). Qed.
Lemma lem5392100 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5392101 : term434 = term431.
Proof. exact (MK_COMB (@lem5392100) (@lem5392099)). Qed.
Lemma lem5392102 (_69866 : int) : (real_of_int _69866) = (real_of_int _69866).
Proof. exact (eq_refl (real_of_int _69866)). Qed.
Lemma lem5392103 (_69866 : int) : (term418 _69866) = (term435 _69866).
Proof. exact (MK_COMB (@lem5392101) (@lem5392102 _69866)). Qed.
Lemma lem5392104 (_69866 : int) : (term417 _69866) = (term435 _69866).
Proof. exact (TRANS (@lem5392001 _69866) (@lem5392103 _69866)). Qed.
Lemma lem5392105 (_69866 : int) : (term435 _69866) = term128.
Proof. exact (@lem1982719 (real_of_int _69866)). Qed.
Lemma lem5392106 (_69866 : int) : (term417 _69866) = term128.
Proof. exact (TRANS (@lem5392104 _69866) (@lem5392105 _69866)). Qed.
Lemma lem5392107 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5392108 (_69866 : int) : (term436 _69866) = term178.
Proof. exact (MK_COMB (@lem5392107) (@lem5392106 _69866)). Qed.
Lemma lem5392109 : term283 = term283.
Proof. exact (eq_refl term283). Qed.
Lemma lem5392110 (_69866 : int) : (term1222 _69866) = term1107.
Proof. exact (MK_COMB (@lem5392108 _69866) (@lem5392109)). Qed.
Lemma lem5392111 (_69866 : int) : (term1221 _69866) = term1107.
Proof. exact (TRANS (@lem5392000 _69866) (@lem5392110 _69866)). Qed.
Lemma lem5392112 : term1107 = term283.
Proof. exact (@lem1982721 term283). Qed.
Lemma lem5392113 (_69866 : int) : (term1221 _69866) = term283.
Proof. exact (TRANS (@lem5392111 _69866) (@lem5392112)). Qed.
Lemma lem5392114 (_69865 : int) : (term231 _69865) = (term231 _69865).
Proof. exact (eq_refl (term231 _69865)). Qed.
Lemma lem5392115 (_69866 : int) (_69865 : int) : (term1220 _69865 _69866) = (term287 _69865).
Proof. exact (MK_COMB (@lem5392114 _69865) (@lem5392113 _69866)). Qed.
Lemma lem5392116 (_69866 : int) (_69865 : int) : (term1219 _69865 _69866) = (term287 _69865).
Proof. exact (TRANS (@lem5391999 _69865 _69866) (@lem5392115 _69866 _69865)). Qed.
Lemma lem5392117 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5392118 (_69866 : int) (_69865 : int) : (term1223 _69865 _69866) = (term1109 _69865).
Proof. exact (MK_COMB (@lem5392117) (@lem5392116 _69866 _69865)). Qed.
Lemma lem5392119 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5392120 (_69866 : int) (_69865 : int) : (term1218 _69865 _69866) = (term1110 _69865).
Proof. exact (MK_COMB (@lem5392118 _69866 _69865) (@lem5392119)). Qed.
Lemma lem5392121 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1215 _69867 _69865 _69866) : term1110 _69865.
Proof. exact (EQ_MP (@lem5392120 _69866 _69865) (@lem5391998 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392123 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5392124 : term390 = term245.
Proof. exact (@lem5392123 term128 term138). Qed.
Lemma lem5392126 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5392127 : term138 = term237.
Proof. exact (@lem5392126 term44). Qed.
Lemma lem5392129 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5392130 : term128 = term198.
Proof. exact (@lem5392129 (NUMERAL 0)). Qed.
Lemma lem5392131 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5392132 : term391 = term392.
Proof. exact (MK_COMB (@lem5392131) (@lem5392130)). Qed.
Lemma lem5392133 : term245 = term393.
Proof. exact (MK_COMB (@lem5392132) (@lem5392127)). Qed.
Lemma lem5392134 : term394.
Proof. exact (@lem1980255 term128 term138 term138 term138). Qed.
Lemma lem5392136 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5392137 : term245 = term246.
Proof. exact (@lem5392136 (NUMERAL 0) term44). Qed.
Lemma lem5392138 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5392139 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5392140 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5392139 h1) (fun h1 : term246 = True => @lem5392138)). Qed.
Lemma lem5392141 : term246 = True.
Proof. exact (EQ_MP (@lem5392140) (@lem5392138)). Qed.
Lemma lem5392142 : term245 = True.
Proof. exact (TRANS (@lem5392137) (@lem5392141)). Qed.
Lemma lem5392143 : True = term245.
Proof. exact (SYM (@lem5392142)). Qed.
Lemma lem5392144 : term245.
Proof. exact (EQ_MP (@lem5392143) (@lem0)). Qed.
Lemma lem5392145 : term395.
Proof. exact (@lem5392134 (@lem5392144)). Qed.
Lemma lem5392147 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5392148 : term245 = term246.
Proof. exact (@lem5392147 (NUMERAL 0) term44). Qed.
Lemma lem5392149 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5392150 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5392151 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5392150 h1) (fun h1 : term246 = True => @lem5392149)). Qed.
Lemma lem5392152 : term246 = True.
Proof. exact (EQ_MP (@lem5392151) (@lem5392149)). Qed.
Lemma lem5392153 : term245 = True.
Proof. exact (TRANS (@lem5392148) (@lem5392152)). Qed.
Lemma lem5392154 : True = term245.
Proof. exact (SYM (@lem5392153)). Qed.
Lemma lem5392155 : term245.
Proof. exact (EQ_MP (@lem5392154) (@lem0)). Qed.
Lemma lem5392156 : term393 = term396.
Proof. exact (@lem5392145 (@lem5392155)). Qed.
Lemma lem5392158 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5392159 : term210 = term211.
Proof. exact (@lem5392158 term44 term44). Qed.
Lemma lem5392160 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5392161 : term213 = term44.
Proof. exact (EQ_MP (@lem5392160) (@lem940073)). Qed.
Lemma lem5392162 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5392163 : term211 = term138.
Proof. exact (MK_COMB (@lem5392162) (@lem5392161)). Qed.
Lemma lem5392164 : term210 = term138.
Proof. exact (TRANS (@lem5392159) (@lem5392163)). Qed.
Lemma lem5392166 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5392167 : term398 = term128.
Proof. exact (@lem5392166 term44). Qed.
Lemma lem5392168 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5392169 : term399 = term391.
Proof. exact (MK_COMB (@lem5392168) (@lem5392167)). Qed.
Lemma lem5392170 : term396 = term245.
Proof. exact (MK_COMB (@lem5392169) (@lem5392164)). Qed.
Lemma lem5392172 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5392173 : term245 = term246.
Proof. exact (@lem5392172 (NUMERAL 0) term44). Qed.
Lemma lem5392174 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5392175 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5392176 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5392175 h1) (fun h1 : term246 = True => @lem5392174)). Qed.
Lemma lem5392177 : term246 = True.
Proof. exact (EQ_MP (@lem5392176) (@lem5392174)). Qed.
Lemma lem5392178 : term245 = True.
Proof. exact (TRANS (@lem5392173) (@lem5392177)). Qed.
Lemma lem5392179 : term396 = True.
Proof. exact (TRANS (@lem5392170) (@lem5392178)). Qed.
Lemma lem5392180 : term393 = True.
Proof. exact (TRANS (@lem5392156) (@lem5392179)). Qed.
Lemma lem5392181 : term245 = True.
Proof. exact (TRANS (@lem5392133) (@lem5392180)). Qed.
Lemma lem5392182 : term390 = True.
Proof. exact (TRANS (@lem5392124) (@lem5392181)). Qed.
Lemma lem5392183 : True = term390.
Proof. exact (SYM (@lem5392182)). Qed.
Lemma lem5392184 : term390.
Proof. exact (EQ_MP (@lem5392183) (@lem0)). Qed.
Lemma lem5392185 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1215 _69867 _69865 _69866) : term1224 _69865.
Proof. exact (conj (@lem5392184) (@lem5392121 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392187 (x : real) (y : real) : term401 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5392188 (_69865 : int) : term1225 _69865.
Proof. exact (@lem5392187 term138 (term287 _69865)). Qed.
Lemma lem5392189 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1215 _69867 _69865 _69866) : term1226 _69865.
Proof. exact (@lem5392188 _69865 (@lem5392185 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392190 (_69865 : int) : (term1227 _69865) = (term287 _69865).
Proof. exact (@lem1982733 (term287 _69865)). Qed.
Lemma lem5392191 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5392192 (_69865 : int) : (term1228 _69865) = (term1109 _69865).
Proof. exact (MK_COMB (@lem5392191) (@lem5392190 _69865)). Qed.
Lemma lem5392193 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5392194 (_69865 : int) : (term1226 _69865) = (term1110 _69865).
Proof. exact (MK_COMB (@lem5392192 _69865) (@lem5392193)). Qed.
Lemma lem5392195 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1215 _69867 _69865 _69866) : term1110 _69865.
Proof. exact (EQ_MP (@lem5392194 _69865) (@lem5392189 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392196 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1215 _69867 _69865 _69866) : term1229 _69865.
Proof. exact (conj (@lem5392195 _69867 _69865 _69866 h1) (@lem5391906 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392198 (x : real) (y : real) : term412 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5392199 (_69865 : int) : term1230 _69865.
Proof. exact (@lem5392198 (term287 _69865) (real_of_int _69865)). Qed.
Lemma lem5392200 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1215 _69867 _69865 _69866) : term1231 _69865.
Proof. exact (@lem5392199 _69865 (@lem5392196 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392201 (_69865 : int) : (term1232 _69865) = (term1222 _69865).
Proof. exact (@lem1982759 (term228 _69865) (real_of_int _69865) term283). Qed.
Lemma lem5392202 (_69865 : int) : (term417 _69865) = (term418 _69865).
Proof. exact (@lem1982713 term201 (real_of_int _69865)). Qed.
Lemma lem5392204 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5392205 : term138 = term237.
Proof. exact (@lem5392204 term44). Qed.
Lemma lem5392207 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5392208 : term201 = term202.
Proof. exact (@lem5392207 term44). Qed.
Lemma lem5392209 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5392210 : term419 = term420.
Proof. exact (MK_COMB (@lem5392209) (@lem5392208)). Qed.
Lemma lem5392211 : term421 = term422.
Proof. exact (MK_COMB (@lem5392210) (@lem5392205)). Qed.
Lemma lem5392212 : term423.
Proof. exact (@lem1981473 term201 term138 term138 term138 term128 term138). Qed.
Lemma lem5392214 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5392215 : term245 = term246.
Proof. exact (@lem5392214 (NUMERAL 0) term44). Qed.
Lemma lem5392216 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5392217 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5392218 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5392217 h1) (fun h1 : term246 = True => @lem5392216)). Qed.
Lemma lem5392219 : term246 = True.
Proof. exact (EQ_MP (@lem5392218) (@lem5392216)). Qed.
Lemma lem5392220 : term245 = True.
Proof. exact (TRANS (@lem5392215) (@lem5392219)). Qed.
Lemma lem5392221 : True = term245.
Proof. exact (SYM (@lem5392220)). Qed.
Lemma lem5392222 : term245.
Proof. exact (EQ_MP (@lem5392221) (@lem0)). Qed.
Lemma lem5392223 : term424.
Proof. exact (@lem5392212 (@lem5392222)). Qed.
Lemma lem5392225 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5392226 : term245 = term246.
Proof. exact (@lem5392225 (NUMERAL 0) term44). Qed.
Lemma lem5392227 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5392228 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5392229 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5392228 h1) (fun h1 : term246 = True => @lem5392227)). Qed.
Lemma lem5392230 : term246 = True.
Proof. exact (EQ_MP (@lem5392229) (@lem5392227)). Qed.
Lemma lem5392231 : term245 = True.
Proof. exact (TRANS (@lem5392226) (@lem5392230)). Qed.
Lemma lem5392232 : True = term245.
Proof. exact (SYM (@lem5392231)). Qed.
Lemma lem5392233 : term245.
Proof. exact (EQ_MP (@lem5392232) (@lem0)). Qed.
Lemma lem5392234 : term425.
Proof. exact (@lem5392223 (@lem5392233)). Qed.
Lemma lem5392236 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5392237 : term245 = term246.
Proof. exact (@lem5392236 (NUMERAL 0) term44). Qed.
Lemma lem5392238 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5392239 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5392240 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5392239 h1) (fun h1 : term246 = True => @lem5392238)). Qed.
Lemma lem5392241 : term246 = True.
Proof. exact (EQ_MP (@lem5392240) (@lem5392238)). Qed.
Lemma lem5392242 : term245 = True.
Proof. exact (TRANS (@lem5392237) (@lem5392241)). Qed.
Lemma lem5392243 : True = term245.
Proof. exact (SYM (@lem5392242)). Qed.
Lemma lem5392244 : term245.
Proof. exact (EQ_MP (@lem5392243) (@lem0)). Qed.
Lemma lem5392245 : term426.
Proof. exact (@lem5392234 (@lem5392244)). Qed.
Lemma lem5392247 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5392248 : term210 = term211.
Proof. exact (@lem5392247 term44 term44). Qed.
Lemma lem5392249 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5392250 : term213 = term44.
Proof. exact (EQ_MP (@lem5392249) (@lem940073)). Qed.
Lemma lem5392251 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5392252 : term211 = term138.
Proof. exact (MK_COMB (@lem5392251) (@lem5392250)). Qed.
Lemma lem5392253 : term210 = term138.
Proof. exact (TRANS (@lem5392248) (@lem5392252)). Qed.
Lemma lem5392255 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5392256 : term302 = term305.
Proof. exact (@lem5392255 term44 term44). Qed.
Lemma lem5392257 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5392258 : term213 = term44.
Proof. exact (EQ_MP (@lem5392257) (@lem940073)). Qed.
Lemma lem5392259 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5392260 : term211 = term138.
Proof. exact (MK_COMB (@lem5392259) (@lem5392258)). Qed.
Lemma lem5392261 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5392262 : term305 = term201.
Proof. exact (MK_COMB (@lem5392261) (@lem5392260)). Qed.
Lemma lem5392263 : term302 = term201.
Proof. exact (TRANS (@lem5392256) (@lem5392262)). Qed.
Lemma lem5392264 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5392265 : term427 = term419.
Proof. exact (MK_COMB (@lem5392264) (@lem5392263)). Qed.
Lemma lem5392266 : term428 = term421.
Proof. exact (MK_COMB (@lem5392265) (@lem5392253)). Qed.
Lemma lem5392268 (m : nat) : (term429 m) = term128.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5392269 : term421 = term128.
Proof. exact (@lem5392268 term44). Qed.
Lemma lem5392270 : term428 = term128.
Proof. exact (TRANS (@lem5392266) (@lem5392269)). Qed.
Lemma lem5392271 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5392272 : term430 = term431.
Proof. exact (MK_COMB (@lem5392271) (@lem5392270)). Qed.
Lemma lem5392273 : term138 = term138.
Proof. exact (eq_refl term138). Qed.
Lemma lem5392274 : term432 = term398.
Proof. exact (MK_COMB (@lem5392272) (@lem5392273)). Qed.
Lemma lem5392276 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5392277 : term398 = term128.
Proof. exact (@lem5392276 term44). Qed.
Lemma lem5392278 : term432 = term128.
Proof. exact (TRANS (@lem5392274) (@lem5392277)). Qed.
Lemma lem5392280 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5392281 : term210 = term211.
Proof. exact (@lem5392280 term44 term44). Qed.
Lemma lem5392282 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5392283 : term213 = term44.
Proof. exact (EQ_MP (@lem5392282) (@lem940073)). Qed.
Lemma lem5392284 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5392285 : term211 = term138.
Proof. exact (MK_COMB (@lem5392284) (@lem5392283)). Qed.
Lemma lem5392286 : term210 = term138.
Proof. exact (TRANS (@lem5392281) (@lem5392285)). Qed.
Lemma lem5392287 : term431 = term431.
Proof. exact (eq_refl term431). Qed.
Lemma lem5392288 : term433 = term398.
Proof. exact (MK_COMB (@lem5392287) (@lem5392286)). Qed.
Lemma lem5392290 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5392291 : term398 = term128.
Proof. exact (@lem5392290 term44). Qed.
Lemma lem5392292 : term433 = term128.
Proof. exact (TRANS (@lem5392288) (@lem5392291)). Qed.
Lemma lem5392293 : term128 = term433.
Proof. exact (SYM (@lem5392292)). Qed.
Lemma lem5392294 : term432 = term433.
Proof. exact (TRANS (@lem5392278) (@lem5392293)). Qed.
Lemma lem5392295 : term422 = term198.
Proof. exact (@lem5392245 (@lem5392294)). Qed.
Lemma lem5392296 : term421 = term198.
Proof. exact (TRANS (@lem5392211) (@lem5392295)). Qed.
Lemma lem5392298 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5392299 : term198 = term128.
Proof. exact (@lem5392298 term128). Qed.
Lemma lem5392300 : term421 = term128.
Proof. exact (TRANS (@lem5392296) (@lem5392299)). Qed.
Lemma lem5392301 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5392302 : term434 = term431.
Proof. exact (MK_COMB (@lem5392301) (@lem5392300)). Qed.
Lemma lem5392303 (_69865 : int) : (real_of_int _69865) = (real_of_int _69865).
Proof. exact (eq_refl (real_of_int _69865)). Qed.
Lemma lem5392304 (_69865 : int) : (term418 _69865) = (term435 _69865).
Proof. exact (MK_COMB (@lem5392302) (@lem5392303 _69865)). Qed.
Lemma lem5392305 (_69865 : int) : (term417 _69865) = (term435 _69865).
Proof. exact (TRANS (@lem5392202 _69865) (@lem5392304 _69865)). Qed.
Lemma lem5392306 (_69865 : int) : (term435 _69865) = term128.
Proof. exact (@lem1982719 (real_of_int _69865)). Qed.
Lemma lem5392307 (_69865 : int) : (term417 _69865) = term128.
Proof. exact (TRANS (@lem5392305 _69865) (@lem5392306 _69865)). Qed.
Lemma lem5392308 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5392309 (_69865 : int) : (term436 _69865) = term178.
Proof. exact (MK_COMB (@lem5392308) (@lem5392307 _69865)). Qed.
Lemma lem5392310 : term283 = term283.
Proof. exact (eq_refl term283). Qed.
Lemma lem5392311 (_69865 : int) : (term1222 _69865) = term1107.
Proof. exact (MK_COMB (@lem5392309 _69865) (@lem5392310)). Qed.
Lemma lem5392312 (_69865 : int) : (term1232 _69865) = term1107.
Proof. exact (TRANS (@lem5392201 _69865) (@lem5392311 _69865)). Qed.
Lemma lem5392313 : term1107 = term283.
Proof. exact (@lem1982721 term283). Qed.
Lemma lem5392314 (_69865 : int) : (term1232 _69865) = term283.
Proof. exact (TRANS (@lem5392312 _69865) (@lem5392313)). Qed.
Lemma lem5392315 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5392316 (_69865 : int) : (term1233 _69865) = term1234.
Proof. exact (MK_COMB (@lem5392315) (@lem5392314 _69865)). Qed.
Lemma lem5392317 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5392318 (_69865 : int) : (term1231 _69865) = term1235.
Proof. exact (MK_COMB (@lem5392316 _69865) (@lem5392317)). Qed.
Lemma lem5392319 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1215 _69867 _69865 _69866) : term1235.
Proof. exact (EQ_MP (@lem5392318 _69865) (@lem5392200 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392321 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5392322 : term1235 = term1236.
Proof. exact (@lem5392321 term128 term283). Qed.
Lemma lem5392324 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5392325 : term283 = term286.
Proof. exact (@lem5392324 term257). Qed.
Lemma lem5392327 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5392328 : term128 = term198.
Proof. exact (@lem5392327 (NUMERAL 0)). Qed.
Lemma lem5392329 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5392330 : term130 = term442.
Proof. exact (MK_COMB (@lem5392329) (@lem5392328)). Qed.
Lemma lem5392331 : term1236 = term1237.
Proof. exact (MK_COMB (@lem5392330) (@lem5392325)). Qed.
Lemma lem5392332 : term1238.
Proof. exact (@lem1980026 term128 term138 term283 term138). Qed.
Lemma lem5392334 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5392335 : term245 = term246.
Proof. exact (@lem5392334 (NUMERAL 0) term44). Qed.
Lemma lem5392336 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5392337 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5392338 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5392337 h1) (fun h1 : term246 = True => @lem5392336)). Qed.
Lemma lem5392339 : term246 = True.
Proof. exact (EQ_MP (@lem5392338) (@lem5392336)). Qed.
Lemma lem5392340 : term245 = True.
Proof. exact (TRANS (@lem5392335) (@lem5392339)). Qed.
Lemma lem5392341 : True = term245.
Proof. exact (SYM (@lem5392340)). Qed.
Lemma lem5392342 : term245.
Proof. exact (EQ_MP (@lem5392341) (@lem0)). Qed.
Lemma lem5392343 : term1239.
Proof. exact (@lem5392332 (@lem5392342)). Qed.
Lemma lem5392345 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5392346 : term245 = term246.
Proof. exact (@lem5392345 (NUMERAL 0) term44). Qed.
Lemma lem5392347 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5392348 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5392349 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5392348 h1) (fun h1 : term246 = True => @lem5392347)). Qed.
Lemma lem5392350 : term246 = True.
Proof. exact (EQ_MP (@lem5392349) (@lem5392347)). Qed.
Lemma lem5392351 : term245 = True.
Proof. exact (TRANS (@lem5392346) (@lem5392350)). Qed.
Lemma lem5392352 : True = term245.
Proof. exact (SYM (@lem5392351)). Qed.
Lemma lem5392353 : term245.
Proof. exact (EQ_MP (@lem5392352) (@lem0)). Qed.
Lemma lem5392354 : term1237 = term1240.
Proof. exact (@lem5392343 (@lem5392353)). Qed.
Lemma lem5392356 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5392357 : term1206 = term1207.
Proof. exact (@lem5392356 term257 term44). Qed.
Lemma lem5392358 : term263 = term255.
Proof. exact (@lem996237 term255). Qed.
Lemma lem5392359 : (term263 = term255) = (term264 = term257).
Proof. exact (@lem1007663 term255 (BIT1 0) term255). Qed.
Lemma lem5392360 : term264 = term257.
Proof. exact (EQ_MP (@lem5392359) (@lem5392358)). Qed.
Lemma lem5392361 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5392362 : term262 = term243.
Proof. exact (MK_COMB (@lem5392361) (@lem5392360)). Qed.
Lemma lem5392363 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5392364 : term1207 = term283.
Proof. exact (MK_COMB (@lem5392363) (@lem5392362)). Qed.
Lemma lem5392365 : term1206 = term283.
Proof. exact (TRANS (@lem5392357) (@lem5392364)). Qed.
Lemma lem5392367 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5392368 : term398 = term128.
Proof. exact (@lem5392367 term44). Qed.
Lemma lem5392369 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5392370 : term447 = term130.
Proof. exact (MK_COMB (@lem5392369) (@lem5392368)). Qed.
Lemma lem5392371 : term1240 = term1236.
Proof. exact (MK_COMB (@lem5392370) (@lem5392365)). Qed.
Lemma lem5392373 (m : nat) (n : nat) : (term448 m n) = (term449 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5392374 : term1236 = term1241.
Proof. exact (@lem5392373 (NUMERAL 0) term257). Qed.
Lemma lem5392375 : term1242 = term255.
Proof. exact (@lem912803). Qed.
Lemma lem5392376 (h1 : term1242 = term255) : (term257 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term255 h1). Qed.
Lemma lem5392377 : (term1242 = term255) = ((term257 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term1242 = term255 => @lem5392376 h1) (fun h1 : (term257 = (NUMERAL 0)) = False => @lem5392375)). Qed.
Lemma lem5392378 : (term257 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5392377) (@lem5392375)). Qed.
Lemma lem5392379 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5392380 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5392381 : term451 = (and True).
Proof. exact (MK_COMB (@lem5392380) (@lem5392379)). Qed.
Lemma lem5392382 : term1241 = (True /\ False).
Proof. exact (MK_COMB (@lem5392381) (@lem5392378)). Qed.
Lemma lem5392384 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5392385 : term1241 = False.
Proof. exact (TRANS (@lem5392382) (@lem5392384)). Qed.
Lemma lem5392386 : term1236 = False.
Proof. exact (TRANS (@lem5392374) (@lem5392385)). Qed.
Lemma lem5392387 : term1240 = False.
Proof. exact (TRANS (@lem5392371) (@lem5392386)). Qed.
Lemma lem5392388 : term1237 = False.
Proof. exact (TRANS (@lem5392354) (@lem5392387)). Qed.
Lemma lem5392389 : term1236 = False.
Proof. exact (TRANS (@lem5392331) (@lem5392388)). Qed.
Lemma lem5392390 : term1235 = False.
Proof. exact (TRANS (@lem5392322) (@lem5392389)). Qed.
Lemma lem5392391 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1215 _69867 _69865 _69866) : False.
Proof. exact (EQ_MP (@lem5392390) (@lem5392319 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392392 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1176 _69867 _69865 _69866) : False.
Proof. exact (or_elim (@lem5391294 _69867 _69865 _69866 h1) (fun h0 : term1182 _69867 _69865 _69866 => @lem5391821 _69867 _69865 _69866 h0) (fun h0 : term1215 _69867 _69865 _69866 => @lem5392391 _69867 _69865 _69866 h0)). Qed.
Lemma lem5392393 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1172 _69867 _69865 _69866) : term1172 _69867 _69865 _69866.
Proof. exact (h1). Qed.
Lemma lem5392394 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1243 _69867 _69865 _69866) : term1243 _69867 _69865 _69866.
Proof. exact (h1). Qed.
Lemma lem5392395 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1243 _69867 _69865 _69866) : term1173 _69867 _69865 _69866.
Proof. exact (proj2 (@lem5392394 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392397 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1243 _69867 _69865 _69866) : term1160 _69867 _69865 _69866.
Proof. exact (proj2 (@lem5392395 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392399 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1243 _69867 _69865 _69866) : term1147 _69865 _69866.
Proof. exact (proj2 (@lem5392397 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392401 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1243 _69867 _69865 _69866) : term1127 _69865 _69866.
Proof. exact (proj2 (@lem5392399 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392402 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1243 _69867 _69865 _69866) : (term1091 _69865 _69866) = term128.
Proof. exact (proj1 (@lem5392399 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392404 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5392405 : term390 = term245.
Proof. exact (@lem5392404 term128 term138). Qed.
Lemma lem5392407 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5392408 : term138 = term237.
Proof. exact (@lem5392407 term44). Qed.
Lemma lem5392410 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5392411 : term128 = term198.
Proof. exact (@lem5392410 (NUMERAL 0)). Qed.
Lemma lem5392412 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5392413 : term391 = term392.
Proof. exact (MK_COMB (@lem5392412) (@lem5392411)). Qed.
Lemma lem5392414 : term245 = term393.
Proof. exact (MK_COMB (@lem5392413) (@lem5392408)). Qed.
Lemma lem5392415 : term394.
Proof. exact (@lem1980255 term128 term138 term138 term138). Qed.
Lemma lem5392417 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5392418 : term245 = term246.
Proof. exact (@lem5392417 (NUMERAL 0) term44). Qed.
Lemma lem5392419 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5392420 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5392421 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5392420 h1) (fun h1 : term246 = True => @lem5392419)). Qed.
Lemma lem5392422 : term246 = True.
Proof. exact (EQ_MP (@lem5392421) (@lem5392419)). Qed.
Lemma lem5392423 : term245 = True.
Proof. exact (TRANS (@lem5392418) (@lem5392422)). Qed.
Lemma lem5392424 : True = term245.
Proof. exact (SYM (@lem5392423)). Qed.
Lemma lem5392425 : term245.
Proof. exact (EQ_MP (@lem5392424) (@lem0)). Qed.
Lemma lem5392426 : term395.
Proof. exact (@lem5392415 (@lem5392425)). Qed.
Lemma lem5392428 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5392429 : term245 = term246.
Proof. exact (@lem5392428 (NUMERAL 0) term44). Qed.
Lemma lem5392430 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5392431 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5392432 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5392431 h1) (fun h1 : term246 = True => @lem5392430)). Qed.
Lemma lem5392433 : term246 = True.
Proof. exact (EQ_MP (@lem5392432) (@lem5392430)). Qed.
Lemma lem5392434 : term245 = True.
Proof. exact (TRANS (@lem5392429) (@lem5392433)). Qed.
Lemma lem5392435 : True = term245.
Proof. exact (SYM (@lem5392434)). Qed.
Lemma lem5392436 : term245.
Proof. exact (EQ_MP (@lem5392435) (@lem0)). Qed.
Lemma lem5392437 : term393 = term396.
Proof. exact (@lem5392426 (@lem5392436)). Qed.
Lemma lem5392439 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5392440 : term210 = term211.
Proof. exact (@lem5392439 term44 term44). Qed.
Lemma lem5392441 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5392442 : term213 = term44.
Proof. exact (EQ_MP (@lem5392441) (@lem940073)). Qed.
Lemma lem5392443 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5392444 : term211 = term138.
Proof. exact (MK_COMB (@lem5392443) (@lem5392442)). Qed.
Lemma lem5392445 : term210 = term138.
Proof. exact (TRANS (@lem5392440) (@lem5392444)). Qed.
Lemma lem5392447 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5392448 : term398 = term128.
Proof. exact (@lem5392447 term44). Qed.
Lemma lem5392449 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5392450 : term399 = term391.
Proof. exact (MK_COMB (@lem5392449) (@lem5392448)). Qed.
Lemma lem5392451 : term396 = term245.
Proof. exact (MK_COMB (@lem5392450) (@lem5392445)). Qed.
Lemma lem5392453 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5392454 : term245 = term246.
Proof. exact (@lem5392453 (NUMERAL 0) term44). Qed.
Lemma lem5392455 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5392456 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5392457 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5392456 h1) (fun h1 : term246 = True => @lem5392455)). Qed.
Lemma lem5392458 : term246 = True.
Proof. exact (EQ_MP (@lem5392457) (@lem5392455)). Qed.
Lemma lem5392459 : term245 = True.
Proof. exact (TRANS (@lem5392454) (@lem5392458)). Qed.
Lemma lem5392460 : term396 = True.
Proof. exact (TRANS (@lem5392451) (@lem5392459)). Qed.
Lemma lem5392461 : term393 = True.
Proof. exact (TRANS (@lem5392437) (@lem5392460)). Qed.
Lemma lem5392462 : term245 = True.
Proof. exact (TRANS (@lem5392414) (@lem5392461)). Qed.
Lemma lem5392463 : term390 = True.
Proof. exact (TRANS (@lem5392405) (@lem5392462)). Qed.
Lemma lem5392464 : True = term390.
Proof. exact (SYM (@lem5392463)). Qed.
Lemma lem5392465 : term390.
Proof. exact (EQ_MP (@lem5392464) (@lem0)). Qed.
Lemma lem5392466 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1243 _69867 _69865 _69866) : term1244 _69865 _69866.
Proof. exact (conj (@lem5392465) (@lem5392401 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392468 (x : real) (y : real) : term401 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5392469 (_69865 : int) (_69866 : int) : term1245 _69865 _69866.
Proof. exact (@lem5392468 term138 (term555 _69865 _69866)). Qed.
Lemma lem5392470 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1243 _69867 _69865 _69866) : term1246 _69865 _69866.
Proof. exact (@lem5392469 _69865 _69866 (@lem5392466 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392471 (_69865 : int) (_69866 : int) : (term1247 _69865 _69866) = (term555 _69865 _69866).
Proof. exact (@lem1982733 (term555 _69865 _69866)). Qed.
Lemma lem5392472 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5392473 (_69865 : int) (_69866 : int) : (term1248 _69865 _69866) = (term1126 _69865 _69866).
Proof. exact (MK_COMB (@lem5392472) (@lem5392471 _69865 _69866)). Qed.
Lemma lem5392474 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5392475 (_69865 : int) (_69866 : int) : (term1246 _69865 _69866) = (term1127 _69865 _69866).
Proof. exact (MK_COMB (@lem5392473 _69865 _69866) (@lem5392474)). Qed.
Lemma lem5392476 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1243 _69867 _69865 _69866) : term1127 _69865 _69866.
Proof. exact (EQ_MP (@lem5392475 _69865 _69866) (@lem5392470 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392478 (y : real) : term453 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5392479 (_69865 : int) (_69866 : int) : term1188 _69865 _69866.
Proof. exact (@lem5392478 (term1091 _69865 _69866)). Qed.
Lemma lem5392480 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1243 _69867 _69865 _69866) : term1189 _69865 _69866.
Proof. exact (@lem5392479 _69865 _69866 (@lem5392402 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392481 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1243 _69867 _69865 _69866) : term1249 _69865 _69866.
Proof. exact (@lem5392480 _69867 _69865 _69866 h1 term201). Qed.
Lemma lem5392482 (_69865 : int) (_69866 : int) : (term1249 _69865 _69866) = ((term1250 _69865 _69866) = term128).
Proof. exact (eq_refl (term1249 _69865 _69866)). Qed.
Lemma lem5392483 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1243 _69867 _69865 _69866) : (term1250 _69865 _69866) = term128.
Proof. exact (EQ_MP (@lem5392482 _69865 _69866) (@lem5392481 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392484 (_69865 : int) (_69866 : int) : (term1250 _69865 _69866) = (term1251 _69865 _69866).
Proof. exact (@lem1982781 (real_of_int _69865) term201 (term1090 _69866)). Qed.
Lemma lem5392485 (_69866 : int) : (term1252 _69866) = (term1253 _69866).
Proof. exact (@lem1982781 (term228 _69866) term201 term138). Qed.
Lemma lem5392487 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5392488 : term138 = term237.
Proof. exact (@lem5392487 term44). Qed.
Lemma lem5392490 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5392491 : term201 = term202.
Proof. exact (@lem5392490 term44). Qed.
Lemma lem5392492 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5392493 : term203 = term204.
Proof. exact (MK_COMB (@lem5392492) (@lem5392491)). Qed.
Lemma lem5392494 : term302 = term303.
Proof. exact (MK_COMB (@lem5392493) (@lem5392488)). Qed.
Lemma lem5392495 : term303 = term304.
Proof. exact (@lem1981613 term201 term138 term138 term138). Qed.
Lemma lem5392497 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5392498 : term210 = term211.
Proof. exact (@lem5392497 term44 term44). Qed.
Lemma lem5392499 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5392500 : term213 = term44.
Proof. exact (EQ_MP (@lem5392499) (@lem940073)). Qed.
Lemma lem5392501 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5392502 : term211 = term138.
Proof. exact (MK_COMB (@lem5392501) (@lem5392500)). Qed.
Lemma lem5392503 : term210 = term138.
Proof. exact (TRANS (@lem5392498) (@lem5392502)). Qed.
Lemma lem5392505 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5392506 : term302 = term305.
Proof. exact (@lem5392505 term44 term44). Qed.
Lemma lem5392507 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5392508 : term213 = term44.
Proof. exact (EQ_MP (@lem5392507) (@lem940073)). Qed.
Lemma lem5392509 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5392510 : term211 = term138.
Proof. exact (MK_COMB (@lem5392509) (@lem5392508)). Qed.
Lemma lem5392511 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5392512 : term305 = term201.
Proof. exact (MK_COMB (@lem5392511) (@lem5392510)). Qed.
Lemma lem5392513 : term302 = term201.
Proof. exact (TRANS (@lem5392506) (@lem5392512)). Qed.
Lemma lem5392514 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5392515 : term306 = term307.
Proof. exact (MK_COMB (@lem5392514) (@lem5392513)). Qed.
Lemma lem5392516 : term304 = term202.
Proof. exact (MK_COMB (@lem5392515) (@lem5392503)). Qed.
Lemma lem5392517 : term303 = term202.
Proof. exact (TRANS (@lem5392495) (@lem5392516)). Qed.
Lemma lem5392518 : term302 = term202.
Proof. exact (TRANS (@lem5392494) (@lem5392517)). Qed.
Lemma lem5392520 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5392521 : term202 = term201.
Proof. exact (@lem5392520 term201). Qed.
Lemma lem5392522 : term302 = term201.
Proof. exact (TRANS (@lem5392518) (@lem5392521)). Qed.
Lemma lem5392523 (_69866 : int) : (term1254 _69866) = (term1255 _69866).
Proof. exact (@lem1982749 term201 term201 (real_of_int _69866)). Qed.
Lemma lem5392525 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5392526 : term201 = term202.
Proof. exact (@lem5392525 term44). Qed.
Lemma lem5392528 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5392529 : term201 = term202.
Proof. exact (@lem5392528 term44). Qed.
Lemma lem5392530 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5392531 : term203 = term204.
Proof. exact (MK_COMB (@lem5392530) (@lem5392529)). Qed.
Lemma lem5392532 : term1256 = term1257.
Proof. exact (MK_COMB (@lem5392531) (@lem5392526)). Qed.
Lemma lem5392533 : term1257 = term1258.
Proof. exact (@lem1981613 term201 term201 term138 term138). Qed.
Lemma lem5392535 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5392536 : term210 = term211.
Proof. exact (@lem5392535 term44 term44). Qed.
Lemma lem5392537 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5392538 : term213 = term44.
Proof. exact (EQ_MP (@lem5392537) (@lem940073)). Qed.
Lemma lem5392539 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5392540 : term211 = term138.
Proof. exact (MK_COMB (@lem5392539) (@lem5392538)). Qed.
Lemma lem5392541 : term210 = term138.
Proof. exact (TRANS (@lem5392536) (@lem5392540)). Qed.
Lemma lem5392543 (m : nat) (n : nat) : (term1259 m n) = (term209 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem5392544 : term1256 = term211.
Proof. exact (@lem5392543 term44 term44). Qed.
Lemma lem5392545 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5392546 : term213 = term44.
Proof. exact (EQ_MP (@lem5392545) (@lem940073)). Qed.
Lemma lem5392547 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5392548 : term211 = term138.
Proof. exact (MK_COMB (@lem5392547) (@lem5392546)). Qed.
Lemma lem5392549 : term1256 = term138.
Proof. exact (TRANS (@lem5392544) (@lem5392548)). Qed.
Lemma lem5392550 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5392551 : term1260 = term1261.
Proof. exact (MK_COMB (@lem5392550) (@lem5392549)). Qed.
Lemma lem5392552 : term1258 = term237.
Proof. exact (MK_COMB (@lem5392551) (@lem5392541)). Qed.
Lemma lem5392553 : term1257 = term237.
Proof. exact (TRANS (@lem5392533) (@lem5392552)). Qed.
Lemma lem5392554 : term1256 = term237.
Proof. exact (TRANS (@lem5392532) (@lem5392553)). Qed.
Lemma lem5392556 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5392557 : term237 = term138.
Proof. exact (@lem5392556 term138). Qed.
Lemma lem5392558 : term1256 = term138.
Proof. exact (TRANS (@lem5392554) (@lem5392557)). Qed.
Lemma lem5392559 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5392560 : term1262 = term1263.
Proof. exact (MK_COMB (@lem5392559) (@lem5392558)). Qed.
Lemma lem5392561 (_69866 : int) : (real_of_int _69866) = (real_of_int _69866).
Proof. exact (eq_refl (real_of_int _69866)). Qed.
Lemma lem5392562 (_69866 : int) : (term1255 _69866) = (term404 _69866).
Proof. exact (MK_COMB (@lem5392560) (@lem5392561 _69866)). Qed.
Lemma lem5392563 (_69866 : int) : (term1254 _69866) = (term404 _69866).
Proof. exact (TRANS (@lem5392523 _69866) (@lem5392562 _69866)). Qed.
Lemma lem5392564 (_69866 : int) : (term404 _69866) = (real_of_int _69866).
Proof. exact (@lem1982709 (real_of_int _69866)). Qed.
Lemma lem5392565 (_69866 : int) : (term1254 _69866) = (real_of_int _69866).
Proof. exact (TRANS (@lem5392563 _69866) (@lem5392564 _69866)). Qed.
Lemma lem5392566 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5392567 (_69866 : int) : (term1264 _69866) = (term139 _69866).
Proof. exact (MK_COMB (@lem5392566) (@lem5392565 _69866)). Qed.
Lemma lem5392568 (_69866 : int) : (term1253 _69866) = (term324 _69866).
Proof. exact (MK_COMB (@lem5392567 _69866) (@lem5392522)). Qed.
Lemma lem5392569 (_69866 : int) : (term1252 _69866) = (term324 _69866).
Proof. exact (TRANS (@lem5392485 _69866) (@lem5392568 _69866)). Qed.
Lemma lem5392572 (_69865 : int) : (term231 _69865) = (term231 _69865).
Proof. exact (eq_refl (term231 _69865)). Qed.
Lemma lem5392573 (_69865 : int) (_69866 : int) : (term1251 _69865 _69866) = (term1265 _69865 _69866).
Proof. exact (MK_COMB (@lem5392572 _69865) (@lem5392569 _69866)). Qed.
Lemma lem5392574 (_69865 : int) (_69866 : int) : (term1250 _69865 _69866) = (term1265 _69865 _69866).
Proof. exact (TRANS (@lem5392484 _69865 _69866) (@lem5392573 _69865 _69866)). Qed.
Lemma lem5392575 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5392576 (_69865 : int) (_69866 : int) : (term1266 _69865 _69866) = (term1267 _69865 _69866).
Proof. exact (MK_COMB (@lem5392575) (@lem5392574 _69865 _69866)). Qed.
Lemma lem5392577 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5392578 (_69865 : int) (_69866 : int) : ((term1250 _69865 _69866) = term128) = ((term1265 _69865 _69866) = term128).
Proof. exact (MK_COMB (@lem5392576 _69865 _69866) (@lem5392577)). Qed.
Lemma lem5392579 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1243 _69867 _69865 _69866) : (term1265 _69865 _69866) = term128.
Proof. exact (EQ_MP (@lem5392578 _69865 _69866) (@lem5392483 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392580 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1243 _69867 _69865 _69866) : term1268 _69865 _69866.
Proof. exact (conj (@lem5392579 _69867 _69865 _69866 h1) (@lem5392476 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392582 (x : real) (y : real) : term459 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5392583 (_69865 : int) (_69866 : int) : term1269 _69865 _69866.
Proof. exact (@lem5392582 (term1265 _69865 _69866) (term555 _69865 _69866)). Qed.
Lemma lem5392584 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1243 _69867 _69865 _69866) : term1270 _69865 _69866.
Proof. exact (@lem5392583 _69865 _69866 (@lem5392580 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392585 (_69865 : int) (_69866 : int) : (term1271 _69865 _69866) = (term1272 _69865 _69866).
Proof. exact (@lem1982753 (term228 _69865) (real_of_int _69865) (term324 _69866) (term228 _69866)). Qed.
Lemma lem5392586 (_69865 : int) : (term417 _69865) = (term418 _69865).
Proof. exact (@lem1982713 term201 (real_of_int _69865)). Qed.
Lemma lem5392588 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5392589 : term138 = term237.
Proof. exact (@lem5392588 term44). Qed.
Lemma lem5392591 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5392592 : term201 = term202.
Proof. exact (@lem5392591 term44). Qed.
Lemma lem5392593 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5392594 : term419 = term420.
Proof. exact (MK_COMB (@lem5392593) (@lem5392592)). Qed.
Lemma lem5392595 : term421 = term422.
Proof. exact (MK_COMB (@lem5392594) (@lem5392589)). Qed.
Lemma lem5392596 : term423.
Proof. exact (@lem1981473 term201 term138 term138 term138 term128 term138). Qed.
Lemma lem5392598 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5392599 : term245 = term246.
Proof. exact (@lem5392598 (NUMERAL 0) term44). Qed.
Lemma lem5392600 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5392601 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5392602 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5392601 h1) (fun h1 : term246 = True => @lem5392600)). Qed.
Lemma lem5392603 : term246 = True.
Proof. exact (EQ_MP (@lem5392602) (@lem5392600)). Qed.
Lemma lem5392604 : term245 = True.
Proof. exact (TRANS (@lem5392599) (@lem5392603)). Qed.
Lemma lem5392605 : True = term245.
Proof. exact (SYM (@lem5392604)). Qed.
Lemma lem5392606 : term245.
Proof. exact (EQ_MP (@lem5392605) (@lem0)). Qed.
Lemma lem5392607 : term424.
Proof. exact (@lem5392596 (@lem5392606)). Qed.
Lemma lem5392609 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5392610 : term245 = term246.
Proof. exact (@lem5392609 (NUMERAL 0) term44). Qed.
Lemma lem5392611 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5392612 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5392613 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5392612 h1) (fun h1 : term246 = True => @lem5392611)). Qed.
Lemma lem5392614 : term246 = True.
Proof. exact (EQ_MP (@lem5392613) (@lem5392611)). Qed.
Lemma lem5392615 : term245 = True.
Proof. exact (TRANS (@lem5392610) (@lem5392614)). Qed.
Lemma lem5392616 : True = term245.
Proof. exact (SYM (@lem5392615)). Qed.
Lemma lem5392617 : term245.
Proof. exact (EQ_MP (@lem5392616) (@lem0)). Qed.
Lemma lem5392618 : term425.
Proof. exact (@lem5392607 (@lem5392617)). Qed.
Lemma lem5392620 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5392621 : term245 = term246.
Proof. exact (@lem5392620 (NUMERAL 0) term44). Qed.
Lemma lem5392622 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5392623 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5392624 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5392623 h1) (fun h1 : term246 = True => @lem5392622)). Qed.
Lemma lem5392625 : term246 = True.
Proof. exact (EQ_MP (@lem5392624) (@lem5392622)). Qed.
Lemma lem5392626 : term245 = True.
Proof. exact (TRANS (@lem5392621) (@lem5392625)). Qed.
Lemma lem5392627 : True = term245.
Proof. exact (SYM (@lem5392626)). Qed.
Lemma lem5392628 : term245.
Proof. exact (EQ_MP (@lem5392627) (@lem0)). Qed.
Lemma lem5392629 : term426.
Proof. exact (@lem5392618 (@lem5392628)). Qed.
Lemma lem5392631 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5392632 : term210 = term211.
Proof. exact (@lem5392631 term44 term44). Qed.
Lemma lem5392633 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5392634 : term213 = term44.
Proof. exact (EQ_MP (@lem5392633) (@lem940073)). Qed.
Lemma lem5392635 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5392636 : term211 = term138.
Proof. exact (MK_COMB (@lem5392635) (@lem5392634)). Qed.
Lemma lem5392637 : term210 = term138.
Proof. exact (TRANS (@lem5392632) (@lem5392636)). Qed.
Lemma lem5392639 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5392640 : term302 = term305.
Proof. exact (@lem5392639 term44 term44). Qed.
Lemma lem5392641 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5392642 : term213 = term44.
Proof. exact (EQ_MP (@lem5392641) (@lem940073)). Qed.
Lemma lem5392643 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5392644 : term211 = term138.
Proof. exact (MK_COMB (@lem5392643) (@lem5392642)). Qed.
Lemma lem5392645 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5392646 : term305 = term201.
Proof. exact (MK_COMB (@lem5392645) (@lem5392644)). Qed.
Lemma lem5392647 : term302 = term201.
Proof. exact (TRANS (@lem5392640) (@lem5392646)). Qed.
Lemma lem5392648 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5392649 : term427 = term419.
Proof. exact (MK_COMB (@lem5392648) (@lem5392647)). Qed.
Lemma lem5392650 : term428 = term421.
Proof. exact (MK_COMB (@lem5392649) (@lem5392637)). Qed.
Lemma lem5392652 (m : nat) : (term429 m) = term128.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5392653 : term421 = term128.
Proof. exact (@lem5392652 term44). Qed.
Lemma lem5392654 : term428 = term128.
Proof. exact (TRANS (@lem5392650) (@lem5392653)). Qed.
Lemma lem5392655 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5392656 : term430 = term431.
Proof. exact (MK_COMB (@lem5392655) (@lem5392654)). Qed.
Lemma lem5392657 : term138 = term138.
Proof. exact (eq_refl term138). Qed.
Lemma lem5392658 : term432 = term398.
Proof. exact (MK_COMB (@lem5392656) (@lem5392657)). Qed.
Lemma lem5392660 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5392661 : term398 = term128.
Proof. exact (@lem5392660 term44). Qed.
Lemma lem5392662 : term432 = term128.
Proof. exact (TRANS (@lem5392658) (@lem5392661)). Qed.
Lemma lem5392664 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5392665 : term210 = term211.
Proof. exact (@lem5392664 term44 term44). Qed.
Lemma lem5392666 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5392667 : term213 = term44.
Proof. exact (EQ_MP (@lem5392666) (@lem940073)). Qed.
Lemma lem5392668 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5392669 : term211 = term138.
Proof. exact (MK_COMB (@lem5392668) (@lem5392667)). Qed.
Lemma lem5392670 : term210 = term138.
Proof. exact (TRANS (@lem5392665) (@lem5392669)). Qed.
Lemma lem5392671 : term431 = term431.
Proof. exact (eq_refl term431). Qed.
Lemma lem5392672 : term433 = term398.
Proof. exact (MK_COMB (@lem5392671) (@lem5392670)). Qed.
Lemma lem5392674 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5392675 : term398 = term128.
Proof. exact (@lem5392674 term44). Qed.
Lemma lem5392676 : term433 = term128.
Proof. exact (TRANS (@lem5392672) (@lem5392675)). Qed.
Lemma lem5392677 : term128 = term433.
Proof. exact (SYM (@lem5392676)). Qed.
Lemma lem5392678 : term432 = term433.
Proof. exact (TRANS (@lem5392662) (@lem5392677)). Qed.
Lemma lem5392679 : term422 = term198.
Proof. exact (@lem5392629 (@lem5392678)). Qed.
Lemma lem5392680 : term421 = term198.
Proof. exact (TRANS (@lem5392595) (@lem5392679)). Qed.
Lemma lem5392682 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5392683 : term198 = term128.
Proof. exact (@lem5392682 term128). Qed.
Lemma lem5392684 : term421 = term128.
Proof. exact (TRANS (@lem5392680) (@lem5392683)). Qed.
Lemma lem5392685 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5392686 : term434 = term431.
Proof. exact (MK_COMB (@lem5392685) (@lem5392684)). Qed.
Lemma lem5392687 (_69865 : int) : (real_of_int _69865) = (real_of_int _69865).
Proof. exact (eq_refl (real_of_int _69865)). Qed.
Lemma lem5392688 (_69865 : int) : (term418 _69865) = (term435 _69865).
Proof. exact (MK_COMB (@lem5392686) (@lem5392687 _69865)). Qed.
Lemma lem5392689 (_69865 : int) : (term417 _69865) = (term435 _69865).
Proof. exact (TRANS (@lem5392586 _69865) (@lem5392688 _69865)). Qed.
Lemma lem5392690 (_69865 : int) : (term435 _69865) = term128.
Proof. exact (@lem1982719 (real_of_int _69865)). Qed.
Lemma lem5392691 (_69865 : int) : (term417 _69865) = term128.
Proof. exact (TRANS (@lem5392689 _69865) (@lem5392690 _69865)). Qed.
Lemma lem5392692 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5392693 (_69865 : int) : (term436 _69865) = term178.
Proof. exact (MK_COMB (@lem5392692) (@lem5392691 _69865)). Qed.
Lemma lem5392694 (_69866 : int) : (term1273 _69866) = (term463 _69866).
Proof. exact (@lem1982759 (real_of_int _69866) (term228 _69866) term201). Qed.
Lemma lem5392695 (_69866 : int) : (term464 _69866) = (term418 _69866).
Proof. exact (@lem1982715 term201 (real_of_int _69866)). Qed.
Lemma lem5392697 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5392698 : term138 = term237.
Proof. exact (@lem5392697 term44). Qed.
Lemma lem5392700 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5392701 : term201 = term202.
Proof. exact (@lem5392700 term44). Qed.
Lemma lem5392702 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5392703 : term419 = term420.
Proof. exact (MK_COMB (@lem5392702) (@lem5392701)). Qed.
Lemma lem5392704 : term421 = term422.
Proof. exact (MK_COMB (@lem5392703) (@lem5392698)). Qed.
Lemma lem5392705 : term423.
Proof. exact (@lem1981473 term201 term138 term138 term138 term128 term138). Qed.
Lemma lem5392707 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5392708 : term245 = term246.
Proof. exact (@lem5392707 (NUMERAL 0) term44). Qed.
Lemma lem5392709 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5392710 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5392711 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5392710 h1) (fun h1 : term246 = True => @lem5392709)). Qed.
Lemma lem5392712 : term246 = True.
Proof. exact (EQ_MP (@lem5392711) (@lem5392709)). Qed.
Lemma lem5392713 : term245 = True.
Proof. exact (TRANS (@lem5392708) (@lem5392712)). Qed.
Lemma lem5392714 : True = term245.
Proof. exact (SYM (@lem5392713)). Qed.
Lemma lem5392715 : term245.
Proof. exact (EQ_MP (@lem5392714) (@lem0)). Qed.
Lemma lem5392716 : term424.
Proof. exact (@lem5392705 (@lem5392715)). Qed.
Lemma lem5392718 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5392719 : term245 = term246.
Proof. exact (@lem5392718 (NUMERAL 0) term44). Qed.
Lemma lem5392720 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5392721 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5392722 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5392721 h1) (fun h1 : term246 = True => @lem5392720)). Qed.
Lemma lem5392723 : term246 = True.
Proof. exact (EQ_MP (@lem5392722) (@lem5392720)). Qed.
Lemma lem5392724 : term245 = True.
Proof. exact (TRANS (@lem5392719) (@lem5392723)). Qed.
Lemma lem5392725 : True = term245.
Proof. exact (SYM (@lem5392724)). Qed.
Lemma lem5392726 : term245.
Proof. exact (EQ_MP (@lem5392725) (@lem0)). Qed.
Lemma lem5392727 : term425.
Proof. exact (@lem5392716 (@lem5392726)). Qed.
Lemma lem5392729 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5392730 : term245 = term246.
Proof. exact (@lem5392729 (NUMERAL 0) term44). Qed.
Lemma lem5392731 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5392732 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5392733 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5392732 h1) (fun h1 : term246 = True => @lem5392731)). Qed.
Lemma lem5392734 : term246 = True.
Proof. exact (EQ_MP (@lem5392733) (@lem5392731)). Qed.
Lemma lem5392735 : term245 = True.
Proof. exact (TRANS (@lem5392730) (@lem5392734)). Qed.
Lemma lem5392736 : True = term245.
Proof. exact (SYM (@lem5392735)). Qed.
Lemma lem5392737 : term245.
Proof. exact (EQ_MP (@lem5392736) (@lem0)). Qed.
Lemma lem5392738 : term426.
Proof. exact (@lem5392727 (@lem5392737)). Qed.
Lemma lem5392740 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5392741 : term210 = term211.
Proof. exact (@lem5392740 term44 term44). Qed.
Lemma lem5392742 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5392743 : term213 = term44.
Proof. exact (EQ_MP (@lem5392742) (@lem940073)). Qed.
Lemma lem5392744 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5392745 : term211 = term138.
Proof. exact (MK_COMB (@lem5392744) (@lem5392743)). Qed.
Lemma lem5392746 : term210 = term138.
Proof. exact (TRANS (@lem5392741) (@lem5392745)). Qed.
Lemma lem5392748 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5392749 : term302 = term305.
Proof. exact (@lem5392748 term44 term44). Qed.
Lemma lem5392750 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5392751 : term213 = term44.
Proof. exact (EQ_MP (@lem5392750) (@lem940073)). Qed.
Lemma lem5392752 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5392753 : term211 = term138.
Proof. exact (MK_COMB (@lem5392752) (@lem5392751)). Qed.
Lemma lem5392754 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5392755 : term305 = term201.
Proof. exact (MK_COMB (@lem5392754) (@lem5392753)). Qed.
Lemma lem5392756 : term302 = term201.
Proof. exact (TRANS (@lem5392749) (@lem5392755)). Qed.
Lemma lem5392757 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5392758 : term427 = term419.
Proof. exact (MK_COMB (@lem5392757) (@lem5392756)). Qed.
Lemma lem5392759 : term428 = term421.
Proof. exact (MK_COMB (@lem5392758) (@lem5392746)). Qed.
Lemma lem5392761 (m : nat) : (term429 m) = term128.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5392762 : term421 = term128.
Proof. exact (@lem5392761 term44). Qed.
Lemma lem5392763 : term428 = term128.
Proof. exact (TRANS (@lem5392759) (@lem5392762)). Qed.
Lemma lem5392764 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5392765 : term430 = term431.
Proof. exact (MK_COMB (@lem5392764) (@lem5392763)). Qed.
Lemma lem5392766 : term138 = term138.
Proof. exact (eq_refl term138). Qed.
Lemma lem5392767 : term432 = term398.
Proof. exact (MK_COMB (@lem5392765) (@lem5392766)). Qed.
Lemma lem5392769 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5392770 : term398 = term128.
Proof. exact (@lem5392769 term44). Qed.
Lemma lem5392771 : term432 = term128.
Proof. exact (TRANS (@lem5392767) (@lem5392770)). Qed.
Lemma lem5392773 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5392774 : term210 = term211.
Proof. exact (@lem5392773 term44 term44). Qed.
Lemma lem5392775 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5392776 : term213 = term44.
Proof. exact (EQ_MP (@lem5392775) (@lem940073)). Qed.
Lemma lem5392777 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5392778 : term211 = term138.
Proof. exact (MK_COMB (@lem5392777) (@lem5392776)). Qed.
Lemma lem5392779 : term210 = term138.
Proof. exact (TRANS (@lem5392774) (@lem5392778)). Qed.
Lemma lem5392780 : term431 = term431.
Proof. exact (eq_refl term431). Qed.
Lemma lem5392781 : term433 = term398.
Proof. exact (MK_COMB (@lem5392780) (@lem5392779)). Qed.
Lemma lem5392783 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5392784 : term398 = term128.
Proof. exact (@lem5392783 term44). Qed.
Lemma lem5392785 : term433 = term128.
Proof. exact (TRANS (@lem5392781) (@lem5392784)). Qed.
Lemma lem5392786 : term128 = term433.
Proof. exact (SYM (@lem5392785)). Qed.
Lemma lem5392787 : term432 = term433.
Proof. exact (TRANS (@lem5392771) (@lem5392786)). Qed.
Lemma lem5392788 : term422 = term198.
Proof. exact (@lem5392738 (@lem5392787)). Qed.
Lemma lem5392789 : term421 = term198.
Proof. exact (TRANS (@lem5392704) (@lem5392788)). Qed.
Lemma lem5392791 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5392792 : term198 = term128.
Proof. exact (@lem5392791 term128). Qed.
Lemma lem5392793 : term421 = term128.
Proof. exact (TRANS (@lem5392789) (@lem5392792)). Qed.
Lemma lem5392794 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5392795 : term434 = term431.
Proof. exact (MK_COMB (@lem5392794) (@lem5392793)). Qed.
Lemma lem5392796 (_69866 : int) : (real_of_int _69866) = (real_of_int _69866).
Proof. exact (eq_refl (real_of_int _69866)). Qed.
Lemma lem5392797 (_69866 : int) : (term418 _69866) = (term435 _69866).
Proof. exact (MK_COMB (@lem5392795) (@lem5392796 _69866)). Qed.
Lemma lem5392798 (_69866 : int) : (term464 _69866) = (term435 _69866).
Proof. exact (TRANS (@lem5392695 _69866) (@lem5392797 _69866)). Qed.
Lemma lem5392799 (_69866 : int) : (term435 _69866) = term128.
Proof. exact (@lem1982719 (real_of_int _69866)). Qed.
Lemma lem5392800 (_69866 : int) : (term464 _69866) = term128.
Proof. exact (TRANS (@lem5392798 _69866) (@lem5392799 _69866)). Qed.
Lemma lem5392801 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5392802 (_69866 : int) : (term465 _69866) = term178.
Proof. exact (MK_COMB (@lem5392801) (@lem5392800 _69866)). Qed.
Lemma lem5392803 : term201 = term201.
Proof. exact (eq_refl term201). Qed.
Lemma lem5392804 (_69866 : int) : (term463 _69866) = term437.
Proof. exact (MK_COMB (@lem5392802 _69866) (@lem5392803)). Qed.
Lemma lem5392805 (_69866 : int) : (term1273 _69866) = term437.
Proof. exact (TRANS (@lem5392694 _69866) (@lem5392804 _69866)). Qed.
Lemma lem5392806 : term437 = term201.
Proof. exact (@lem1982721 term201). Qed.
Lemma lem5392807 (_69866 : int) : (term1273 _69866) = term201.
Proof. exact (TRANS (@lem5392805 _69866) (@lem5392806)). Qed.
Lemma lem5392808 (_69865 : int) (_69866 : int) : (term1272 _69865 _69866) = term437.
Proof. exact (MK_COMB (@lem5392693 _69865) (@lem5392807 _69866)). Qed.
Lemma lem5392809 (_69865 : int) (_69866 : int) : (term1271 _69865 _69866) = term437.
Proof. exact (TRANS (@lem5392585 _69865 _69866) (@lem5392808 _69865 _69866)). Qed.
Lemma lem5392810 : term437 = term201.
Proof. exact (@lem1982721 term201). Qed.
Lemma lem5392811 (_69865 : int) (_69866 : int) : (term1271 _69865 _69866) = term201.
Proof. exact (TRANS (@lem5392809 _69865 _69866) (@lem5392810)). Qed.
Lemma lem5392812 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5392813 (_69865 : int) (_69866 : int) : (term1274 _69865 _69866) = term439.
Proof. exact (MK_COMB (@lem5392812) (@lem5392811 _69865 _69866)). Qed.
Lemma lem5392814 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5392815 (_69865 : int) (_69866 : int) : (term1270 _69865 _69866) = term440.
Proof. exact (MK_COMB (@lem5392813 _69865 _69866) (@lem5392814)). Qed.
Lemma lem5392816 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1243 _69867 _69865 _69866) : term440.
Proof. exact (EQ_MP (@lem5392815 _69865 _69866) (@lem5392584 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392818 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5392819 : term440 = term441.
Proof. exact (@lem5392818 term128 term201). Qed.
Lemma lem5392821 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5392822 : term201 = term202.
Proof. exact (@lem5392821 term44). Qed.
Lemma lem5392824 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5392825 : term128 = term198.
Proof. exact (@lem5392824 (NUMERAL 0)). Qed.
Lemma lem5392826 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5392827 : term130 = term442.
Proof. exact (MK_COMB (@lem5392826) (@lem5392825)). Qed.
Lemma lem5392828 : term441 = term443.
Proof. exact (MK_COMB (@lem5392827) (@lem5392822)). Qed.
Lemma lem5392829 : term444.
Proof. exact (@lem1980026 term128 term138 term201 term138). Qed.
Lemma lem5392831 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5392832 : term245 = term246.
Proof. exact (@lem5392831 (NUMERAL 0) term44). Qed.
Lemma lem5392833 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5392834 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5392835 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5392834 h1) (fun h1 : term246 = True => @lem5392833)). Qed.
Lemma lem5392836 : term246 = True.
Proof. exact (EQ_MP (@lem5392835) (@lem5392833)). Qed.
Lemma lem5392837 : term245 = True.
Proof. exact (TRANS (@lem5392832) (@lem5392836)). Qed.
Lemma lem5392838 : True = term245.
Proof. exact (SYM (@lem5392837)). Qed.
Lemma lem5392839 : term245.
Proof. exact (EQ_MP (@lem5392838) (@lem0)). Qed.
Lemma lem5392840 : term445.
Proof. exact (@lem5392829 (@lem5392839)). Qed.
Lemma lem5392842 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5392843 : term245 = term246.
Proof. exact (@lem5392842 (NUMERAL 0) term44). Qed.
Lemma lem5392844 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5392845 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5392846 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5392845 h1) (fun h1 : term246 = True => @lem5392844)). Qed.
Lemma lem5392847 : term246 = True.
Proof. exact (EQ_MP (@lem5392846) (@lem5392844)). Qed.
Lemma lem5392848 : term245 = True.
Proof. exact (TRANS (@lem5392843) (@lem5392847)). Qed.
Lemma lem5392849 : True = term245.
Proof. exact (SYM (@lem5392848)). Qed.
Lemma lem5392850 : term245.
Proof. exact (EQ_MP (@lem5392849) (@lem0)). Qed.
Lemma lem5392851 : term443 = term446.
Proof. exact (@lem5392840 (@lem5392850)). Qed.
Lemma lem5392853 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5392854 : term302 = term305.
Proof. exact (@lem5392853 term44 term44). Qed.
Lemma lem5392855 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5392856 : term213 = term44.
Proof. exact (EQ_MP (@lem5392855) (@lem940073)). Qed.
Lemma lem5392857 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5392858 : term211 = term138.
Proof. exact (MK_COMB (@lem5392857) (@lem5392856)). Qed.
Lemma lem5392859 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5392860 : term305 = term201.
Proof. exact (MK_COMB (@lem5392859) (@lem5392858)). Qed.
Lemma lem5392861 : term302 = term201.
Proof. exact (TRANS (@lem5392854) (@lem5392860)). Qed.
Lemma lem5392863 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5392864 : term398 = term128.
Proof. exact (@lem5392863 term44). Qed.
Lemma lem5392865 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5392866 : term447 = term130.
Proof. exact (MK_COMB (@lem5392865) (@lem5392864)). Qed.
Lemma lem5392867 : term446 = term441.
Proof. exact (MK_COMB (@lem5392866) (@lem5392861)). Qed.
Lemma lem5392869 (m : nat) (n : nat) : (term448 m n) = (term449 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5392870 : term441 = term450.
Proof. exact (@lem5392869 (NUMERAL 0) term44). Qed.
Lemma lem5392871 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5392872 (h1 : term247 = (BIT1 0)) : (term44 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5392873 : (term247 = (BIT1 0)) = ((term44 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5392872 h1) (fun h1 : (term44 = (NUMERAL 0)) = False => @lem5392871)). Qed.
Lemma lem5392874 : (term44 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5392873) (@lem5392871)). Qed.
Lemma lem5392875 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5392876 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5392877 : term451 = (and True).
Proof. exact (MK_COMB (@lem5392876) (@lem5392875)). Qed.
Lemma lem5392878 : term450 = (True /\ False).
Proof. exact (MK_COMB (@lem5392877) (@lem5392874)). Qed.
Lemma lem5392880 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5392881 : term450 = False.
Proof. exact (TRANS (@lem5392878) (@lem5392880)). Qed.
Lemma lem5392882 : term441 = False.
Proof. exact (TRANS (@lem5392870) (@lem5392881)). Qed.
Lemma lem5392883 : term446 = False.
Proof. exact (TRANS (@lem5392867) (@lem5392882)). Qed.
Lemma lem5392884 : term443 = False.
Proof. exact (TRANS (@lem5392851) (@lem5392883)). Qed.
Lemma lem5392885 : term441 = False.
Proof. exact (TRANS (@lem5392828) (@lem5392884)). Qed.
Lemma lem5392886 : term440 = False.
Proof. exact (TRANS (@lem5392819) (@lem5392885)). Qed.
Lemma lem5392887 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1243 _69867 _69865 _69866) : False.
Proof. exact (EQ_MP (@lem5392886) (@lem5392816 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392888 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1275 _69867 _69865 _69866) : term1275 _69867 _69865 _69866.
Proof. exact (h1). Qed.
Lemma lem5392889 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1275 _69867 _69865 _69866) : term1174 _69867 _69865 _69866.
Proof. exact (proj2 (@lem5392888 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392891 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1275 _69867 _69865 _69866) : term1161 _69867 _69865 _69866.
Proof. exact (proj2 (@lem5392889 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392893 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1275 _69867 _69865 _69866) : term1148 _69865 _69866.
Proof. exact (proj2 (@lem5392891 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392895 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1275 _69867 _69865 _69866) : term1127 _69865 _69866.
Proof. exact (proj2 (@lem5392893 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392896 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1275 _69867 _69865 _69866) : term1112 _69865 _69866.
Proof. exact (proj1 (@lem5392893 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392897 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1275 _69867 _69865 _69866) : (real_of_int _69866) = term128.
Proof. exact (proj2 (@lem5392896 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392898 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1275 _69867 _69865 _69866) : term1110 _69865.
Proof. exact (proj1 (@lem5392896 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392900 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5392901 : term390 = term245.
Proof. exact (@lem5392900 term128 term138). Qed.
Lemma lem5392903 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5392904 : term138 = term237.
Proof. exact (@lem5392903 term44). Qed.
Lemma lem5392906 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5392907 : term128 = term198.
Proof. exact (@lem5392906 (NUMERAL 0)). Qed.
Lemma lem5392908 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5392909 : term391 = term392.
Proof. exact (MK_COMB (@lem5392908) (@lem5392907)). Qed.
Lemma lem5392910 : term245 = term393.
Proof. exact (MK_COMB (@lem5392909) (@lem5392904)). Qed.
Lemma lem5392911 : term394.
Proof. exact (@lem1980255 term128 term138 term138 term138). Qed.
Lemma lem5392913 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5392914 : term245 = term246.
Proof. exact (@lem5392913 (NUMERAL 0) term44). Qed.
Lemma lem5392915 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5392916 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5392917 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5392916 h1) (fun h1 : term246 = True => @lem5392915)). Qed.
Lemma lem5392918 : term246 = True.
Proof. exact (EQ_MP (@lem5392917) (@lem5392915)). Qed.
Lemma lem5392919 : term245 = True.
Proof. exact (TRANS (@lem5392914) (@lem5392918)). Qed.
Lemma lem5392920 : True = term245.
Proof. exact (SYM (@lem5392919)). Qed.
Lemma lem5392921 : term245.
Proof. exact (EQ_MP (@lem5392920) (@lem0)). Qed.
Lemma lem5392922 : term395.
Proof. exact (@lem5392911 (@lem5392921)). Qed.
Lemma lem5392924 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5392925 : term245 = term246.
Proof. exact (@lem5392924 (NUMERAL 0) term44). Qed.
Lemma lem5392926 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5392927 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5392928 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5392927 h1) (fun h1 : term246 = True => @lem5392926)). Qed.
Lemma lem5392929 : term246 = True.
Proof. exact (EQ_MP (@lem5392928) (@lem5392926)). Qed.
Lemma lem5392930 : term245 = True.
Proof. exact (TRANS (@lem5392925) (@lem5392929)). Qed.
Lemma lem5392931 : True = term245.
Proof. exact (SYM (@lem5392930)). Qed.
Lemma lem5392932 : term245.
Proof. exact (EQ_MP (@lem5392931) (@lem0)). Qed.
Lemma lem5392933 : term393 = term396.
Proof. exact (@lem5392922 (@lem5392932)). Qed.
Lemma lem5392935 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5392936 : term210 = term211.
Proof. exact (@lem5392935 term44 term44). Qed.
Lemma lem5392937 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5392938 : term213 = term44.
Proof. exact (EQ_MP (@lem5392937) (@lem940073)). Qed.
Lemma lem5392939 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5392940 : term211 = term138.
Proof. exact (MK_COMB (@lem5392939) (@lem5392938)). Qed.
Lemma lem5392941 : term210 = term138.
Proof. exact (TRANS (@lem5392936) (@lem5392940)). Qed.
Lemma lem5392943 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5392944 : term398 = term128.
Proof. exact (@lem5392943 term44). Qed.
Lemma lem5392945 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5392946 : term399 = term391.
Proof. exact (MK_COMB (@lem5392945) (@lem5392944)). Qed.
Lemma lem5392947 : term396 = term245.
Proof. exact (MK_COMB (@lem5392946) (@lem5392941)). Qed.
Lemma lem5392949 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5392950 : term245 = term246.
Proof. exact (@lem5392949 (NUMERAL 0) term44). Qed.
Lemma lem5392951 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5392952 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5392953 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5392952 h1) (fun h1 : term246 = True => @lem5392951)). Qed.
Lemma lem5392954 : term246 = True.
Proof. exact (EQ_MP (@lem5392953) (@lem5392951)). Qed.
Lemma lem5392955 : term245 = True.
Proof. exact (TRANS (@lem5392950) (@lem5392954)). Qed.
Lemma lem5392956 : term396 = True.
Proof. exact (TRANS (@lem5392947) (@lem5392955)). Qed.
Lemma lem5392957 : term393 = True.
Proof. exact (TRANS (@lem5392933) (@lem5392956)). Qed.
Lemma lem5392958 : term245 = True.
Proof. exact (TRANS (@lem5392910) (@lem5392957)). Qed.
Lemma lem5392959 : term390 = True.
Proof. exact (TRANS (@lem5392901) (@lem5392958)). Qed.
Lemma lem5392960 : True = term390.
Proof. exact (SYM (@lem5392959)). Qed.
Lemma lem5392961 : term390.
Proof. exact (EQ_MP (@lem5392960) (@lem0)). Qed.
Lemma lem5392962 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1275 _69867 _69865 _69866) : term1244 _69865 _69866.
Proof. exact (conj (@lem5392961) (@lem5392895 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392964 (x : real) (y : real) : term401 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5392965 (_69865 : int) (_69866 : int) : term1245 _69865 _69866.
Proof. exact (@lem5392964 term138 (term555 _69865 _69866)). Qed.
Lemma lem5392966 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1275 _69867 _69865 _69866) : term1246 _69865 _69866.
Proof. exact (@lem5392965 _69865 _69866 (@lem5392962 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392967 (_69865 : int) (_69866 : int) : (term1247 _69865 _69866) = (term555 _69865 _69866).
Proof. exact (@lem1982733 (term555 _69865 _69866)). Qed.
Lemma lem5392968 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5392969 (_69865 : int) (_69866 : int) : (term1248 _69865 _69866) = (term1126 _69865 _69866).
Proof. exact (MK_COMB (@lem5392968) (@lem5392967 _69865 _69866)). Qed.
Lemma lem5392970 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5392971 (_69865 : int) (_69866 : int) : (term1246 _69865 _69866) = (term1127 _69865 _69866).
Proof. exact (MK_COMB (@lem5392969 _69865 _69866) (@lem5392970)). Qed.
Lemma lem5392972 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1275 _69867 _69865 _69866) : term1127 _69865 _69866.
Proof. exact (EQ_MP (@lem5392971 _69865 _69866) (@lem5392966 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392974 (y : real) : term453 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5392975 (_69866 : int) : term454 _69866.
Proof. exact (@lem5392974 (real_of_int _69866)). Qed.
Lemma lem5392976 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1275 _69867 _69865 _69866) : term455 _69866.
Proof. exact (@lem5392975 _69866 (@lem5392897 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392977 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1275 _69867 _69865 _69866) : term456 _69866.
Proof. exact (@lem5392976 _69867 _69865 _69866 h1 term138). Qed.
Lemma lem5392978 (_69866 : int) : (term456 _69866) = ((term404 _69866) = term128).
Proof. exact (eq_refl (term456 _69866)). Qed.
Lemma lem5392979 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1275 _69867 _69865 _69866) : (term404 _69866) = term128.
Proof. exact (EQ_MP (@lem5392978 _69866) (@lem5392977 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392980 (_69866 : int) : (term404 _69866) = (real_of_int _69866).
Proof. exact (@lem1982733 (real_of_int _69866)). Qed.
Lemma lem5392981 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5392982 (_69866 : int) : (term457 _69866) = (term155 _69866).
Proof. exact (MK_COMB (@lem5392981) (@lem5392980 _69866)). Qed.
Lemma lem5392983 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5392984 (_69866 : int) : ((term404 _69866) = term128) = ((real_of_int _69866) = term128).
Proof. exact (MK_COMB (@lem5392982 _69866) (@lem5392983)). Qed.
Lemma lem5392985 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1275 _69867 _69865 _69866) : (real_of_int _69866) = term128.
Proof. exact (EQ_MP (@lem5392984 _69866) (@lem5392979 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392986 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1275 _69867 _69865 _69866) : term1276 _69865 _69866.
Proof. exact (conj (@lem5392985 _69867 _69865 _69866 h1) (@lem5392972 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392988 (x : real) (y : real) : term459 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5392989 (_69865 : int) (_69866 : int) : term1277 _69865 _69866.
Proof. exact (@lem5392988 (real_of_int _69866) (term555 _69865 _69866)). Qed.
Lemma lem5392990 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1275 _69867 _69865 _69866) : term1278 _69865 _69866.
Proof. exact (@lem5392989 _69865 _69866 (@lem5392986 _69867 _69865 _69866 h1)). Qed.
Lemma lem5392991 (_69865 : int) (_69866 : int) : (term1279 _69865 _69866) = (term1280 _69865 _69866).
Proof. exact (@lem1982757 (real_of_int _69865) (real_of_int _69866) (term228 _69866)). Qed.
Lemma lem5392992 (_69866 : int) : (term464 _69866) = (term418 _69866).
Proof. exact (@lem1982715 term201 (real_of_int _69866)). Qed.
Lemma lem5392994 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5392995 : term138 = term237.
Proof. exact (@lem5392994 term44). Qed.
Lemma lem5392997 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5392998 : term201 = term202.
Proof. exact (@lem5392997 term44). Qed.
Lemma lem5392999 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5393000 : term419 = term420.
Proof. exact (MK_COMB (@lem5392999) (@lem5392998)). Qed.
Lemma lem5393001 : term421 = term422.
Proof. exact (MK_COMB (@lem5393000) (@lem5392995)). Qed.
Lemma lem5393002 : term423.
Proof. exact (@lem1981473 term201 term138 term138 term138 term128 term138). Qed.
Lemma lem5393004 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5393005 : term245 = term246.
Proof. exact (@lem5393004 (NUMERAL 0) term44). Qed.
Lemma lem5393006 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5393007 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5393008 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5393007 h1) (fun h1 : term246 = True => @lem5393006)). Qed.
Lemma lem5393009 : term246 = True.
Proof. exact (EQ_MP (@lem5393008) (@lem5393006)). Qed.
Lemma lem5393010 : term245 = True.
Proof. exact (TRANS (@lem5393005) (@lem5393009)). Qed.
Lemma lem5393011 : True = term245.
Proof. exact (SYM (@lem5393010)). Qed.
Lemma lem5393012 : term245.
Proof. exact (EQ_MP (@lem5393011) (@lem0)). Qed.
Lemma lem5393013 : term424.
Proof. exact (@lem5393002 (@lem5393012)). Qed.
Lemma lem5393015 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5393016 : term245 = term246.
Proof. exact (@lem5393015 (NUMERAL 0) term44). Qed.
Lemma lem5393017 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5393018 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5393019 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5393018 h1) (fun h1 : term246 = True => @lem5393017)). Qed.
Lemma lem5393020 : term246 = True.
Proof. exact (EQ_MP (@lem5393019) (@lem5393017)). Qed.
Lemma lem5393021 : term245 = True.
Proof. exact (TRANS (@lem5393016) (@lem5393020)). Qed.
Lemma lem5393022 : True = term245.
Proof. exact (SYM (@lem5393021)). Qed.
Lemma lem5393023 : term245.
Proof. exact (EQ_MP (@lem5393022) (@lem0)). Qed.
Lemma lem5393024 : term425.
Proof. exact (@lem5393013 (@lem5393023)). Qed.
Lemma lem5393026 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5393027 : term245 = term246.
Proof. exact (@lem5393026 (NUMERAL 0) term44). Qed.
Lemma lem5393028 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5393029 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5393030 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5393029 h1) (fun h1 : term246 = True => @lem5393028)). Qed.
Lemma lem5393031 : term246 = True.
Proof. exact (EQ_MP (@lem5393030) (@lem5393028)). Qed.
Lemma lem5393032 : term245 = True.
Proof. exact (TRANS (@lem5393027) (@lem5393031)). Qed.
Lemma lem5393033 : True = term245.
Proof. exact (SYM (@lem5393032)). Qed.
Lemma lem5393034 : term245.
Proof. exact (EQ_MP (@lem5393033) (@lem0)). Qed.
Lemma lem5393035 : term426.
Proof. exact (@lem5393024 (@lem5393034)). Qed.
Lemma lem5393037 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5393038 : term210 = term211.
Proof. exact (@lem5393037 term44 term44). Qed.
Lemma lem5393039 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5393040 : term213 = term44.
Proof. exact (EQ_MP (@lem5393039) (@lem940073)). Qed.
Lemma lem5393041 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5393042 : term211 = term138.
Proof. exact (MK_COMB (@lem5393041) (@lem5393040)). Qed.
Lemma lem5393043 : term210 = term138.
Proof. exact (TRANS (@lem5393038) (@lem5393042)). Qed.
Lemma lem5393045 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5393046 : term302 = term305.
Proof. exact (@lem5393045 term44 term44). Qed.
Lemma lem5393047 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5393048 : term213 = term44.
Proof. exact (EQ_MP (@lem5393047) (@lem940073)). Qed.
Lemma lem5393049 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5393050 : term211 = term138.
Proof. exact (MK_COMB (@lem5393049) (@lem5393048)). Qed.
Lemma lem5393051 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5393052 : term305 = term201.
Proof. exact (MK_COMB (@lem5393051) (@lem5393050)). Qed.
Lemma lem5393053 : term302 = term201.
Proof. exact (TRANS (@lem5393046) (@lem5393052)). Qed.
Lemma lem5393054 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5393055 : term427 = term419.
Proof. exact (MK_COMB (@lem5393054) (@lem5393053)). Qed.
Lemma lem5393056 : term428 = term421.
Proof. exact (MK_COMB (@lem5393055) (@lem5393043)). Qed.
Lemma lem5393058 (m : nat) : (term429 m) = term128.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5393059 : term421 = term128.
Proof. exact (@lem5393058 term44). Qed.
Lemma lem5393060 : term428 = term128.
Proof. exact (TRANS (@lem5393056) (@lem5393059)). Qed.
Lemma lem5393061 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5393062 : term430 = term431.
Proof. exact (MK_COMB (@lem5393061) (@lem5393060)). Qed.
Lemma lem5393063 : term138 = term138.
Proof. exact (eq_refl term138). Qed.
Lemma lem5393064 : term432 = term398.
Proof. exact (MK_COMB (@lem5393062) (@lem5393063)). Qed.
Lemma lem5393066 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5393067 : term398 = term128.
Proof. exact (@lem5393066 term44). Qed.
Lemma lem5393068 : term432 = term128.
Proof. exact (TRANS (@lem5393064) (@lem5393067)). Qed.
Lemma lem5393070 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5393071 : term210 = term211.
Proof. exact (@lem5393070 term44 term44). Qed.
Lemma lem5393072 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5393073 : term213 = term44.
Proof. exact (EQ_MP (@lem5393072) (@lem940073)). Qed.
Lemma lem5393074 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5393075 : term211 = term138.
Proof. exact (MK_COMB (@lem5393074) (@lem5393073)). Qed.
Lemma lem5393076 : term210 = term138.
Proof. exact (TRANS (@lem5393071) (@lem5393075)). Qed.
Lemma lem5393077 : term431 = term431.
Proof. exact (eq_refl term431). Qed.
Lemma lem5393078 : term433 = term398.
Proof. exact (MK_COMB (@lem5393077) (@lem5393076)). Qed.
Lemma lem5393080 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5393081 : term398 = term128.
Proof. exact (@lem5393080 term44). Qed.
Lemma lem5393082 : term433 = term128.
Proof. exact (TRANS (@lem5393078) (@lem5393081)). Qed.
Lemma lem5393083 : term128 = term433.
Proof. exact (SYM (@lem5393082)). Qed.
Lemma lem5393084 : term432 = term433.
Proof. exact (TRANS (@lem5393068) (@lem5393083)). Qed.
Lemma lem5393085 : term422 = term198.
Proof. exact (@lem5393035 (@lem5393084)). Qed.
Lemma lem5393086 : term421 = term198.
Proof. exact (TRANS (@lem5393001) (@lem5393085)). Qed.
Lemma lem5393088 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5393089 : term198 = term128.
Proof. exact (@lem5393088 term128). Qed.
Lemma lem5393090 : term421 = term128.
Proof. exact (TRANS (@lem5393086) (@lem5393089)). Qed.
Lemma lem5393091 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5393092 : term434 = term431.
Proof. exact (MK_COMB (@lem5393091) (@lem5393090)). Qed.
Lemma lem5393093 (_69866 : int) : (real_of_int _69866) = (real_of_int _69866).
Proof. exact (eq_refl (real_of_int _69866)). Qed.
Lemma lem5393094 (_69866 : int) : (term418 _69866) = (term435 _69866).
Proof. exact (MK_COMB (@lem5393092) (@lem5393093 _69866)). Qed.
Lemma lem5393095 (_69866 : int) : (term464 _69866) = (term435 _69866).
Proof. exact (TRANS (@lem5392992 _69866) (@lem5393094 _69866)). Qed.
Lemma lem5393096 (_69866 : int) : (term435 _69866) = term128.
Proof. exact (@lem1982719 (real_of_int _69866)). Qed.
Lemma lem5393097 (_69866 : int) : (term464 _69866) = term128.
Proof. exact (TRANS (@lem5393095 _69866) (@lem5393096 _69866)). Qed.
Lemma lem5393098 (_69865 : int) : (term139 _69865) = (term139 _69865).
Proof. exact (eq_refl (term139 _69865)). Qed.
Lemma lem5393099 (_69866 : int) (_69865 : int) : (term1280 _69865 _69866) = (term218 _69865).
Proof. exact (MK_COMB (@lem5393098 _69865) (@lem5393097 _69866)). Qed.
Lemma lem5393100 (_69866 : int) (_69865 : int) : (term1279 _69865 _69866) = (term218 _69865).
Proof. exact (TRANS (@lem5392991 _69865 _69866) (@lem5393099 _69866 _69865)). Qed.
Lemma lem5393101 (_69865 : int) : (term218 _69865) = (real_of_int _69865).
Proof. exact (@lem1982723 (real_of_int _69865)). Qed.
Lemma lem5393102 (_69866 : int) (_69865 : int) : (term1279 _69865 _69866) = (real_of_int _69865).
Proof. exact (TRANS (@lem5393100 _69866 _69865) (@lem5393101 _69865)). Qed.
Lemma lem5393103 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5393104 (_69866 : int) (_69865 : int) : (term1281 _69865 _69866) = (term220 _69865).
Proof. exact (MK_COMB (@lem5393103) (@lem5393102 _69866 _69865)). Qed.
Lemma lem5393105 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5393106 (_69866 : int) (_69865 : int) : (term1278 _69865 _69866) = (term221 _69865).
Proof. exact (MK_COMB (@lem5393104 _69866 _69865) (@lem5393105)). Qed.
Lemma lem5393107 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1275 _69867 _69865 _69866) : term221 _69865.
Proof. exact (EQ_MP (@lem5393106 _69866 _69865) (@lem5392990 _69867 _69865 _69866 h1)). Qed.
Lemma lem5393109 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5393110 : term390 = term245.
Proof. exact (@lem5393109 term128 term138). Qed.
Lemma lem5393112 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5393113 : term138 = term237.
Proof. exact (@lem5393112 term44). Qed.
Lemma lem5393115 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5393116 : term128 = term198.
Proof. exact (@lem5393115 (NUMERAL 0)). Qed.
Lemma lem5393117 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5393118 : term391 = term392.
Proof. exact (MK_COMB (@lem5393117) (@lem5393116)). Qed.
Lemma lem5393119 : term245 = term393.
Proof. exact (MK_COMB (@lem5393118) (@lem5393113)). Qed.
Lemma lem5393120 : term394.
Proof. exact (@lem1980255 term128 term138 term138 term138). Qed.
Lemma lem5393122 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5393123 : term245 = term246.
Proof. exact (@lem5393122 (NUMERAL 0) term44). Qed.
Lemma lem5393124 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5393125 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5393126 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5393125 h1) (fun h1 : term246 = True => @lem5393124)). Qed.
Lemma lem5393127 : term246 = True.
Proof. exact (EQ_MP (@lem5393126) (@lem5393124)). Qed.
Lemma lem5393128 : term245 = True.
Proof. exact (TRANS (@lem5393123) (@lem5393127)). Qed.
Lemma lem5393129 : True = term245.
Proof. exact (SYM (@lem5393128)). Qed.
Lemma lem5393130 : term245.
Proof. exact (EQ_MP (@lem5393129) (@lem0)). Qed.
Lemma lem5393131 : term395.
Proof. exact (@lem5393120 (@lem5393130)). Qed.
Lemma lem5393133 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5393134 : term245 = term246.
Proof. exact (@lem5393133 (NUMERAL 0) term44). Qed.
Lemma lem5393135 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5393136 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5393137 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5393136 h1) (fun h1 : term246 = True => @lem5393135)). Qed.
Lemma lem5393138 : term246 = True.
Proof. exact (EQ_MP (@lem5393137) (@lem5393135)). Qed.
Lemma lem5393139 : term245 = True.
Proof. exact (TRANS (@lem5393134) (@lem5393138)). Qed.
Lemma lem5393140 : True = term245.
Proof. exact (SYM (@lem5393139)). Qed.
Lemma lem5393141 : term245.
Proof. exact (EQ_MP (@lem5393140) (@lem0)). Qed.
Lemma lem5393142 : term393 = term396.
Proof. exact (@lem5393131 (@lem5393141)). Qed.
Lemma lem5393144 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5393145 : term210 = term211.
Proof. exact (@lem5393144 term44 term44). Qed.
Lemma lem5393146 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5393147 : term213 = term44.
Proof. exact (EQ_MP (@lem5393146) (@lem940073)). Qed.
Lemma lem5393148 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5393149 : term211 = term138.
Proof. exact (MK_COMB (@lem5393148) (@lem5393147)). Qed.
Lemma lem5393150 : term210 = term138.
Proof. exact (TRANS (@lem5393145) (@lem5393149)). Qed.
Lemma lem5393152 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5393153 : term398 = term128.
Proof. exact (@lem5393152 term44). Qed.
Lemma lem5393154 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5393155 : term399 = term391.
Proof. exact (MK_COMB (@lem5393154) (@lem5393153)). Qed.
Lemma lem5393156 : term396 = term245.
Proof. exact (MK_COMB (@lem5393155) (@lem5393150)). Qed.
Lemma lem5393158 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5393159 : term245 = term246.
Proof. exact (@lem5393158 (NUMERAL 0) term44). Qed.
Lemma lem5393160 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5393161 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5393162 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5393161 h1) (fun h1 : term246 = True => @lem5393160)). Qed.
Lemma lem5393163 : term246 = True.
Proof. exact (EQ_MP (@lem5393162) (@lem5393160)). Qed.
Lemma lem5393164 : term245 = True.
Proof. exact (TRANS (@lem5393159) (@lem5393163)). Qed.
Lemma lem5393165 : term396 = True.
Proof. exact (TRANS (@lem5393156) (@lem5393164)). Qed.
Lemma lem5393166 : term393 = True.
Proof. exact (TRANS (@lem5393142) (@lem5393165)). Qed.
Lemma lem5393167 : term245 = True.
Proof. exact (TRANS (@lem5393119) (@lem5393166)). Qed.
Lemma lem5393168 : term390 = True.
Proof. exact (TRANS (@lem5393110) (@lem5393167)). Qed.
Lemma lem5393169 : True = term390.
Proof. exact (SYM (@lem5393168)). Qed.
Lemma lem5393170 : term390.
Proof. exact (EQ_MP (@lem5393169) (@lem0)). Qed.
Lemma lem5393171 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1275 _69867 _69865 _69866) : term400 _69865.
Proof. exact (conj (@lem5393170) (@lem5393107 _69867 _69865 _69866 h1)). Qed.
Lemma lem5393173 (x : real) (y : real) : term401 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5393174 (_69865 : int) : term402 _69865.
Proof. exact (@lem5393173 term138 (real_of_int _69865)). Qed.
Lemma lem5393175 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1275 _69867 _69865 _69866) : term403 _69865.
Proof. exact (@lem5393174 _69865 (@lem5393171 _69867 _69865 _69866 h1)). Qed.
Lemma lem5393176 (_69865 : int) : (term404 _69865) = (real_of_int _69865).
Proof. exact (@lem1982733 (real_of_int _69865)). Qed.
Lemma lem5393177 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5393178 (_69865 : int) : (term405 _69865) = (term220 _69865).
Proof. exact (MK_COMB (@lem5393177) (@lem5393176 _69865)). Qed.
Lemma lem5393179 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5393180 (_69865 : int) : (term403 _69865) = (term221 _69865).
Proof. exact (MK_COMB (@lem5393178 _69865) (@lem5393179)). Qed.
Lemma lem5393181 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1275 _69867 _69865 _69866) : term221 _69865.
Proof. exact (EQ_MP (@lem5393180 _69865) (@lem5393175 _69867 _69865 _69866 h1)). Qed.
Lemma lem5393183 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5393184 : term390 = term245.
Proof. exact (@lem5393183 term128 term138). Qed.
Lemma lem5393186 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5393187 : term138 = term237.
Proof. exact (@lem5393186 term44). Qed.
Lemma lem5393189 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5393190 : term128 = term198.
Proof. exact (@lem5393189 (NUMERAL 0)). Qed.
Lemma lem5393191 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5393192 : term391 = term392.
Proof. exact (MK_COMB (@lem5393191) (@lem5393190)). Qed.
Lemma lem5393193 : term245 = term393.
Proof. exact (MK_COMB (@lem5393192) (@lem5393187)). Qed.
Lemma lem5393194 : term394.
Proof. exact (@lem1980255 term128 term138 term138 term138). Qed.
Lemma lem5393196 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5393197 : term245 = term246.
Proof. exact (@lem5393196 (NUMERAL 0) term44). Qed.
Lemma lem5393198 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5393199 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5393200 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5393199 h1) (fun h1 : term246 = True => @lem5393198)). Qed.
Lemma lem5393201 : term246 = True.
Proof. exact (EQ_MP (@lem5393200) (@lem5393198)). Qed.
Lemma lem5393202 : term245 = True.
Proof. exact (TRANS (@lem5393197) (@lem5393201)). Qed.
Lemma lem5393203 : True = term245.
Proof. exact (SYM (@lem5393202)). Qed.
Lemma lem5393204 : term245.
Proof. exact (EQ_MP (@lem5393203) (@lem0)). Qed.
Lemma lem5393205 : term395.
Proof. exact (@lem5393194 (@lem5393204)). Qed.
Lemma lem5393207 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5393208 : term245 = term246.
Proof. exact (@lem5393207 (NUMERAL 0) term44). Qed.
Lemma lem5393209 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5393210 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5393211 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5393210 h1) (fun h1 : term246 = True => @lem5393209)). Qed.
Lemma lem5393212 : term246 = True.
Proof. exact (EQ_MP (@lem5393211) (@lem5393209)). Qed.
Lemma lem5393213 : term245 = True.
Proof. exact (TRANS (@lem5393208) (@lem5393212)). Qed.
Lemma lem5393214 : True = term245.
Proof. exact (SYM (@lem5393213)). Qed.
Lemma lem5393215 : term245.
Proof. exact (EQ_MP (@lem5393214) (@lem0)). Qed.
Lemma lem5393216 : term393 = term396.
Proof. exact (@lem5393205 (@lem5393215)). Qed.
Lemma lem5393218 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5393219 : term210 = term211.
Proof. exact (@lem5393218 term44 term44). Qed.
Lemma lem5393220 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5393221 : term213 = term44.
Proof. exact (EQ_MP (@lem5393220) (@lem940073)). Qed.
Lemma lem5393222 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5393223 : term211 = term138.
Proof. exact (MK_COMB (@lem5393222) (@lem5393221)). Qed.
Lemma lem5393224 : term210 = term138.
Proof. exact (TRANS (@lem5393219) (@lem5393223)). Qed.
Lemma lem5393226 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5393227 : term398 = term128.
Proof. exact (@lem5393226 term44). Qed.
Lemma lem5393228 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5393229 : term399 = term391.
Proof. exact (MK_COMB (@lem5393228) (@lem5393227)). Qed.
Lemma lem5393230 : term396 = term245.
Proof. exact (MK_COMB (@lem5393229) (@lem5393224)). Qed.
Lemma lem5393232 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5393233 : term245 = term246.
Proof. exact (@lem5393232 (NUMERAL 0) term44). Qed.
Lemma lem5393234 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5393235 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5393236 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5393235 h1) (fun h1 : term246 = True => @lem5393234)). Qed.
Lemma lem5393237 : term246 = True.
Proof. exact (EQ_MP (@lem5393236) (@lem5393234)). Qed.
Lemma lem5393238 : term245 = True.
Proof. exact (TRANS (@lem5393233) (@lem5393237)). Qed.
Lemma lem5393239 : term396 = True.
Proof. exact (TRANS (@lem5393230) (@lem5393238)). Qed.
Lemma lem5393240 : term393 = True.
Proof. exact (TRANS (@lem5393216) (@lem5393239)). Qed.
Lemma lem5393241 : term245 = True.
Proof. exact (TRANS (@lem5393193) (@lem5393240)). Qed.
Lemma lem5393242 : term390 = True.
Proof. exact (TRANS (@lem5393184) (@lem5393241)). Qed.
Lemma lem5393243 : True = term390.
Proof. exact (SYM (@lem5393242)). Qed.
Lemma lem5393244 : term390.
Proof. exact (EQ_MP (@lem5393243) (@lem0)). Qed.
Lemma lem5393245 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1275 _69867 _69865 _69866) : term1224 _69865.
Proof. exact (conj (@lem5393244) (@lem5392898 _69867 _69865 _69866 h1)). Qed.
Lemma lem5393247 (x : real) (y : real) : term401 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5393248 (_69865 : int) : term1225 _69865.
Proof. exact (@lem5393247 term138 (term287 _69865)). Qed.
Lemma lem5393249 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1275 _69867 _69865 _69866) : term1226 _69865.
Proof. exact (@lem5393248 _69865 (@lem5393245 _69867 _69865 _69866 h1)). Qed.
Lemma lem5393250 (_69865 : int) : (term1227 _69865) = (term287 _69865).
Proof. exact (@lem1982733 (term287 _69865)). Qed.
Lemma lem5393251 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5393252 (_69865 : int) : (term1228 _69865) = (term1109 _69865).
Proof. exact (MK_COMB (@lem5393251) (@lem5393250 _69865)). Qed.
Lemma lem5393253 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5393254 (_69865 : int) : (term1226 _69865) = (term1110 _69865).
Proof. exact (MK_COMB (@lem5393252 _69865) (@lem5393253)). Qed.
Lemma lem5393255 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1275 _69867 _69865 _69866) : term1110 _69865.
Proof. exact (EQ_MP (@lem5393254 _69865) (@lem5393249 _69867 _69865 _69866 h1)). Qed.
Lemma lem5393256 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1275 _69867 _69865 _69866) : term1229 _69865.
Proof. exact (conj (@lem5393255 _69867 _69865 _69866 h1) (@lem5393181 _69867 _69865 _69866 h1)). Qed.
Lemma lem5393258 (x : real) (y : real) : term412 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5393259 (_69865 : int) : term1230 _69865.
Proof. exact (@lem5393258 (term287 _69865) (real_of_int _69865)). Qed.
Lemma lem5393260 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1275 _69867 _69865 _69866) : term1231 _69865.
Proof. exact (@lem5393259 _69865 (@lem5393256 _69867 _69865 _69866 h1)). Qed.
Lemma lem5393261 (_69865 : int) : (term1232 _69865) = (term1222 _69865).
Proof. exact (@lem1982759 (term228 _69865) (real_of_int _69865) term283). Qed.
Lemma lem5393262 (_69865 : int) : (term417 _69865) = (term418 _69865).
Proof. exact (@lem1982713 term201 (real_of_int _69865)). Qed.
Lemma lem5393264 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5393265 : term138 = term237.
Proof. exact (@lem5393264 term44). Qed.
Lemma lem5393267 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5393268 : term201 = term202.
Proof. exact (@lem5393267 term44). Qed.
Lemma lem5393269 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5393270 : term419 = term420.
Proof. exact (MK_COMB (@lem5393269) (@lem5393268)). Qed.
Lemma lem5393271 : term421 = term422.
Proof. exact (MK_COMB (@lem5393270) (@lem5393265)). Qed.
Lemma lem5393272 : term423.
Proof. exact (@lem1981473 term201 term138 term138 term138 term128 term138). Qed.
Lemma lem5393274 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5393275 : term245 = term246.
Proof. exact (@lem5393274 (NUMERAL 0) term44). Qed.
Lemma lem5393276 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5393277 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5393278 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5393277 h1) (fun h1 : term246 = True => @lem5393276)). Qed.
Lemma lem5393279 : term246 = True.
Proof. exact (EQ_MP (@lem5393278) (@lem5393276)). Qed.
Lemma lem5393280 : term245 = True.
Proof. exact (TRANS (@lem5393275) (@lem5393279)). Qed.
Lemma lem5393281 : True = term245.
Proof. exact (SYM (@lem5393280)). Qed.
Lemma lem5393282 : term245.
Proof. exact (EQ_MP (@lem5393281) (@lem0)). Qed.
Lemma lem5393283 : term424.
Proof. exact (@lem5393272 (@lem5393282)). Qed.
Lemma lem5393285 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5393286 : term245 = term246.
Proof. exact (@lem5393285 (NUMERAL 0) term44). Qed.
Lemma lem5393287 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5393288 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5393289 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5393288 h1) (fun h1 : term246 = True => @lem5393287)). Qed.
Lemma lem5393290 : term246 = True.
Proof. exact (EQ_MP (@lem5393289) (@lem5393287)). Qed.
Lemma lem5393291 : term245 = True.
Proof. exact (TRANS (@lem5393286) (@lem5393290)). Qed.
Lemma lem5393292 : True = term245.
Proof. exact (SYM (@lem5393291)). Qed.
Lemma lem5393293 : term245.
Proof. exact (EQ_MP (@lem5393292) (@lem0)). Qed.
Lemma lem5393294 : term425.
Proof. exact (@lem5393283 (@lem5393293)). Qed.
Lemma lem5393296 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5393297 : term245 = term246.
Proof. exact (@lem5393296 (NUMERAL 0) term44). Qed.
Lemma lem5393298 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5393299 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5393300 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5393299 h1) (fun h1 : term246 = True => @lem5393298)). Qed.
Lemma lem5393301 : term246 = True.
Proof. exact (EQ_MP (@lem5393300) (@lem5393298)). Qed.
Lemma lem5393302 : term245 = True.
Proof. exact (TRANS (@lem5393297) (@lem5393301)). Qed.
Lemma lem5393303 : True = term245.
Proof. exact (SYM (@lem5393302)). Qed.
Lemma lem5393304 : term245.
Proof. exact (EQ_MP (@lem5393303) (@lem0)). Qed.
Lemma lem5393305 : term426.
Proof. exact (@lem5393294 (@lem5393304)). Qed.
Lemma lem5393307 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5393308 : term210 = term211.
Proof. exact (@lem5393307 term44 term44). Qed.
Lemma lem5393309 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5393310 : term213 = term44.
Proof. exact (EQ_MP (@lem5393309) (@lem940073)). Qed.
Lemma lem5393311 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5393312 : term211 = term138.
Proof. exact (MK_COMB (@lem5393311) (@lem5393310)). Qed.
Lemma lem5393313 : term210 = term138.
Proof. exact (TRANS (@lem5393308) (@lem5393312)). Qed.
Lemma lem5393315 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5393316 : term302 = term305.
Proof. exact (@lem5393315 term44 term44). Qed.
Lemma lem5393317 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5393318 : term213 = term44.
Proof. exact (EQ_MP (@lem5393317) (@lem940073)). Qed.
Lemma lem5393319 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5393320 : term211 = term138.
Proof. exact (MK_COMB (@lem5393319) (@lem5393318)). Qed.
Lemma lem5393321 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5393322 : term305 = term201.
Proof. exact (MK_COMB (@lem5393321) (@lem5393320)). Qed.
Lemma lem5393323 : term302 = term201.
Proof. exact (TRANS (@lem5393316) (@lem5393322)). Qed.
Lemma lem5393324 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5393325 : term427 = term419.
Proof. exact (MK_COMB (@lem5393324) (@lem5393323)). Qed.
Lemma lem5393326 : term428 = term421.
Proof. exact (MK_COMB (@lem5393325) (@lem5393313)). Qed.
Lemma lem5393328 (m : nat) : (term429 m) = term128.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5393329 : term421 = term128.
Proof. exact (@lem5393328 term44). Qed.
Lemma lem5393330 : term428 = term128.
Proof. exact (TRANS (@lem5393326) (@lem5393329)). Qed.
Lemma lem5393331 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5393332 : term430 = term431.
Proof. exact (MK_COMB (@lem5393331) (@lem5393330)). Qed.
Lemma lem5393333 : term138 = term138.
Proof. exact (eq_refl term138). Qed.
Lemma lem5393334 : term432 = term398.
Proof. exact (MK_COMB (@lem5393332) (@lem5393333)). Qed.
Lemma lem5393336 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5393337 : term398 = term128.
Proof. exact (@lem5393336 term44). Qed.
Lemma lem5393338 : term432 = term128.
Proof. exact (TRANS (@lem5393334) (@lem5393337)). Qed.
Lemma lem5393340 (m : nat) (n : nat) : (term208 m n) = (term209 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5393341 : term210 = term211.
Proof. exact (@lem5393340 term44 term44). Qed.
Lemma lem5393342 : (term212 = (BIT1 0)) = (term213 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5393343 : term213 = term44.
Proof. exact (EQ_MP (@lem5393342) (@lem940073)). Qed.
Lemma lem5393344 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5393345 : term211 = term138.
Proof. exact (MK_COMB (@lem5393344) (@lem5393343)). Qed.
Lemma lem5393346 : term210 = term138.
Proof. exact (TRANS (@lem5393341) (@lem5393345)). Qed.
Lemma lem5393347 : term431 = term431.
Proof. exact (eq_refl term431). Qed.
Lemma lem5393348 : term433 = term398.
Proof. exact (MK_COMB (@lem5393347) (@lem5393346)). Qed.
Lemma lem5393350 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5393351 : term398 = term128.
Proof. exact (@lem5393350 term44). Qed.
Lemma lem5393352 : term433 = term128.
Proof. exact (TRANS (@lem5393348) (@lem5393351)). Qed.
Lemma lem5393353 : term128 = term433.
Proof. exact (SYM (@lem5393352)). Qed.
Lemma lem5393354 : term432 = term433.
Proof. exact (TRANS (@lem5393338) (@lem5393353)). Qed.
Lemma lem5393355 : term422 = term198.
Proof. exact (@lem5393305 (@lem5393354)). Qed.
Lemma lem5393356 : term421 = term198.
Proof. exact (TRANS (@lem5393271) (@lem5393355)). Qed.
Lemma lem5393358 (x : real) : (term217 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5393359 : term198 = term128.
Proof. exact (@lem5393358 term128). Qed.
Lemma lem5393360 : term421 = term128.
Proof. exact (TRANS (@lem5393356) (@lem5393359)). Qed.
Lemma lem5393361 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5393362 : term434 = term431.
Proof. exact (MK_COMB (@lem5393361) (@lem5393360)). Qed.
Lemma lem5393363 (_69865 : int) : (real_of_int _69865) = (real_of_int _69865).
Proof. exact (eq_refl (real_of_int _69865)). Qed.
Lemma lem5393364 (_69865 : int) : (term418 _69865) = (term435 _69865).
Proof. exact (MK_COMB (@lem5393362) (@lem5393363 _69865)). Qed.
Lemma lem5393365 (_69865 : int) : (term417 _69865) = (term435 _69865).
Proof. exact (TRANS (@lem5393262 _69865) (@lem5393364 _69865)). Qed.
Lemma lem5393366 (_69865 : int) : (term435 _69865) = term128.
Proof. exact (@lem1982719 (real_of_int _69865)). Qed.
Lemma lem5393367 (_69865 : int) : (term417 _69865) = term128.
Proof. exact (TRANS (@lem5393365 _69865) (@lem5393366 _69865)). Qed.
Lemma lem5393368 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5393369 (_69865 : int) : (term436 _69865) = term178.
Proof. exact (MK_COMB (@lem5393368) (@lem5393367 _69865)). Qed.
Lemma lem5393370 : term283 = term283.
Proof. exact (eq_refl term283). Qed.
Lemma lem5393371 (_69865 : int) : (term1222 _69865) = term1107.
Proof. exact (MK_COMB (@lem5393369 _69865) (@lem5393370)). Qed.
Lemma lem5393372 (_69865 : int) : (term1232 _69865) = term1107.
Proof. exact (TRANS (@lem5393261 _69865) (@lem5393371 _69865)). Qed.
Lemma lem5393373 : term1107 = term283.
Proof. exact (@lem1982721 term283). Qed.
Lemma lem5393374 (_69865 : int) : (term1232 _69865) = term283.
Proof. exact (TRANS (@lem5393372 _69865) (@lem5393373)). Qed.
Lemma lem5393375 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5393376 (_69865 : int) : (term1233 _69865) = term1234.
Proof. exact (MK_COMB (@lem5393375) (@lem5393374 _69865)). Qed.
Lemma lem5393377 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem5393378 (_69865 : int) : (term1231 _69865) = term1235.
Proof. exact (MK_COMB (@lem5393376 _69865) (@lem5393377)). Qed.
Lemma lem5393379 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1275 _69867 _69865 _69866) : term1235.
Proof. exact (EQ_MP (@lem5393378 _69865) (@lem5393260 _69867 _69865 _69866 h1)). Qed.
Lemma lem5393381 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5393382 : term1235 = term1236.
Proof. exact (@lem5393381 term128 term283). Qed.
Lemma lem5393384 (x : nat) : (term199 x) = (term200 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5393385 : term283 = term286.
Proof. exact (@lem5393384 term257). Qed.
Lemma lem5393387 (x : nat) : (real_of_num x) = (term197 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5393388 : term128 = term198.
Proof. exact (@lem5393387 (NUMERAL 0)). Qed.
Lemma lem5393389 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5393390 : term130 = term442.
Proof. exact (MK_COMB (@lem5393389) (@lem5393388)). Qed.
Lemma lem5393391 : term1236 = term1237.
Proof. exact (MK_COMB (@lem5393390) (@lem5393385)). Qed.
Lemma lem5393392 : term1238.
Proof. exact (@lem1980026 term128 term138 term283 term138). Qed.
Lemma lem5393394 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5393395 : term245 = term246.
Proof. exact (@lem5393394 (NUMERAL 0) term44). Qed.
Lemma lem5393396 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5393397 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5393398 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5393397 h1) (fun h1 : term246 = True => @lem5393396)). Qed.
Lemma lem5393399 : term246 = True.
Proof. exact (EQ_MP (@lem5393398) (@lem5393396)). Qed.
Lemma lem5393400 : term245 = True.
Proof. exact (TRANS (@lem5393395) (@lem5393399)). Qed.
Lemma lem5393401 : True = term245.
Proof. exact (SYM (@lem5393400)). Qed.
Lemma lem5393402 : term245.
Proof. exact (EQ_MP (@lem5393401) (@lem0)). Qed.
Lemma lem5393403 : term1239.
Proof. exact (@lem5393392 (@lem5393402)). Qed.
Lemma lem5393405 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5393406 : term245 = term246.
Proof. exact (@lem5393405 (NUMERAL 0) term44). Qed.
Lemma lem5393407 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5393408 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5393409 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5393408 h1) (fun h1 : term246 = True => @lem5393407)). Qed.
Lemma lem5393410 : term246 = True.
Proof. exact (EQ_MP (@lem5393409) (@lem5393407)). Qed.
Lemma lem5393411 : term245 = True.
Proof. exact (TRANS (@lem5393406) (@lem5393410)). Qed.
Lemma lem5393412 : True = term245.
Proof. exact (SYM (@lem5393411)). Qed.
Lemma lem5393413 : term245.
Proof. exact (EQ_MP (@lem5393412) (@lem0)). Qed.
Lemma lem5393414 : term1237 = term1240.
Proof. exact (@lem5393403 (@lem5393413)). Qed.
Lemma lem5393416 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5393417 : term1206 = term1207.
Proof. exact (@lem5393416 term257 term44). Qed.
Lemma lem5393418 : term263 = term255.
Proof. exact (@lem996237 term255). Qed.
Lemma lem5393419 : (term263 = term255) = (term264 = term257).
Proof. exact (@lem1007663 term255 (BIT1 0) term255). Qed.
Lemma lem5393420 : term264 = term257.
Proof. exact (EQ_MP (@lem5393419) (@lem5393418)). Qed.
Lemma lem5393421 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5393422 : term262 = term243.
Proof. exact (MK_COMB (@lem5393421) (@lem5393420)). Qed.
Lemma lem5393423 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5393424 : term1207 = term283.
Proof. exact (MK_COMB (@lem5393423) (@lem5393422)). Qed.
Lemma lem5393425 : term1206 = term283.
Proof. exact (TRANS (@lem5393417) (@lem5393424)). Qed.
Lemma lem5393427 (x : nat) : (term397 x) = term128.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5393428 : term398 = term128.
Proof. exact (@lem5393427 term44). Qed.
Lemma lem5393429 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5393430 : term447 = term130.
Proof. exact (MK_COMB (@lem5393429) (@lem5393428)). Qed.
Lemma lem5393431 : term1240 = term1236.
Proof. exact (MK_COMB (@lem5393430) (@lem5393425)). Qed.
Lemma lem5393433 (m : nat) (n : nat) : (term448 m n) = (term449 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5393434 : term1236 = term1241.
Proof. exact (@lem5393433 (NUMERAL 0) term257). Qed.
Lemma lem5393435 : term1242 = term255.
Proof. exact (@lem912803). Qed.
Lemma lem5393436 (h1 : term1242 = term255) : (term257 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term255 h1). Qed.
Lemma lem5393437 : (term1242 = term255) = ((term257 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term1242 = term255 => @lem5393436 h1) (fun h1 : (term257 = (NUMERAL 0)) = False => @lem5393435)). Qed.
Lemma lem5393438 : (term257 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5393437) (@lem5393435)). Qed.
Lemma lem5393439 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5393440 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5393441 : term451 = (and True).
Proof. exact (MK_COMB (@lem5393440) (@lem5393439)). Qed.
Lemma lem5393442 : term1241 = (True /\ False).
Proof. exact (MK_COMB (@lem5393441) (@lem5393438)). Qed.
Lemma lem5393444 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5393445 : term1241 = False.
Proof. exact (TRANS (@lem5393442) (@lem5393444)). Qed.
Lemma lem5393446 : term1236 = False.
Proof. exact (TRANS (@lem5393434) (@lem5393445)). Qed.
Lemma lem5393447 : term1240 = False.
Proof. exact (TRANS (@lem5393431) (@lem5393446)). Qed.
Lemma lem5393448 : term1237 = False.
Proof. exact (TRANS (@lem5393414) (@lem5393447)). Qed.
Lemma lem5393449 : term1236 = False.
Proof. exact (TRANS (@lem5393391) (@lem5393448)). Qed.
Lemma lem5393450 : term1235 = False.
Proof. exact (TRANS (@lem5393382) (@lem5393449)). Qed.
Lemma lem5393451 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1275 _69867 _69865 _69866) : False.
Proof. exact (EQ_MP (@lem5393450) (@lem5393379 _69867 _69865 _69866 h1)). Qed.
Lemma lem5393452 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1172 _69867 _69865 _69866) : False.
Proof. exact (or_elim (@lem5392393 _69867 _69865 _69866 h1) (fun h0 : term1243 _69867 _69865 _69866 => @lem5392887 _69867 _69865 _69866 h0) (fun h0 : term1275 _69867 _69865 _69866 => @lem5393451 _69867 _69865 _69866 h0)). Qed.
Lemma lem5393453 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1181 _69867 _69865 _69866) : False.
Proof. exact (or_elim (@lem5391293 _69867 _69865 _69866 h1) (fun h0 : term1176 _69867 _69865 _69866 => @lem5392392 _69867 _69865 _69866 h0) (fun h0 : term1172 _69867 _69865 _69866 => @lem5393452 _69867 _69865 _69866 h0)). Qed.
Lemma lem5393455 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1181 _69867 _69865 _69866) : term1181 _69867 _69865 _69866.
Proof. exact (h1). Qed.
Lemma lem5393456 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1181 _69867 _69865 _69866) : (term1181 _69867 _69865 _69866) = False.
Proof. exact (prop_ext (fun h2 : term1181 _69867 _69865 _69866 => @lem5393453 _69867 _69865 _69866 h1) (fun h2 : False => @lem5393455 _69867 _69865 _69866 h1)). Qed.
Lemma lem5393457 (_69867 : int) (_69865 : int) (_69866 : int) (h1 : term1181 _69867 _69865 _69866) : False.
Proof. exact (EQ_MP (@lem5393456 _69867 _69865 _69866 h1) (@lem5393455 _69867 _69865 _69866 h1)). Qed.
Lemma lem5393458 (_69867 : int) (_69866 : int) (_69865 : int) (h1 : term1081 _69867 _69866 _69865) : term1081 _69867 _69866 _69865.
Proof. exact (h1). Qed.
Lemma lem5393459 (_69867 : int) (_69866 : int) (_69865 : int) (h1 : term1081 _69867 _69866 _69865) : term1181 _69867 _69865 _69866.
Proof. exact (EQ_MP (@lem5391271 _69867 _69865 _69866) (@lem5393458 _69867 _69866 _69865 h1)). Qed.
Lemma lem5393460 (_69867 : int) (_69866 : int) (_69865 : int) (h1 : term1081 _69867 _69866 _69865) : (term1181 _69867 _69865 _69866) = False.
Proof. exact (prop_ext (fun h2 : term1181 _69867 _69865 _69866 => @lem5393457 _69867 _69865 _69866 h2) (fun h2 : False => @lem5393459 _69867 _69866 _69865 h1)). Qed.
Lemma lem5393461 (_69867 : int) (_69866 : int) (_69865 : int) (h1 : term1081 _69867 _69866 _69865) : False.
Proof. exact (EQ_MP (@lem5393460 _69867 _69866 _69865 h1) (@lem5393459 _69867 _69866 _69865 h1)). Qed.
Lemma lem5393462 (_69867 : int) (_69866 : int) (_69865 : int) : term1282 _69867 _69866 _69865.
Proof. exact (fun h0 : term1081 _69867 _69866 _69865 => @lem5393461 _69867 _69866 _69865 h0). Qed.
Lemma lem5393463 (_69867 : int) (_69866 : int) (_69865 : int) : term1283 _69867 _69866 _69865.
Proof. exact (@lem1386578 (term1284 _69867 _69866 _69865)). Qed.
Lemma lem5393466 (_69867 : int) (_69866 : int) (_69865 : int) : term1284 _69867 _69866 _69865.
Proof. exact (@lem5393463 _69867 _69866 _69865 (@lem5393462 _69867 _69866 _69865)). Qed.
Lemma lem5393467 (_69867 : int) (_69865 : int) (_69866 : int) : (term1080 _69867 _69866 _69865) = (term1047 _69867 _69865 _69866).
Proof. exact (SYM (@lem5390000 _69867 _69866 _69865)). Qed.
Lemma lem5393468 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5393469 (_69867 : int) (_69865 : int) (_69866 : int) : (term1284 _69867 _69866 _69865) = (term1011 _69867 _69865 _69866).
Proof. exact (MK_COMB (@lem5393468) (@lem5393467 _69867 _69865 _69866)). Qed.
Lemma lem5393470 (_69867 : int) (_69865 : int) (_69866 : int) : term1011 _69867 _69865 _69866.
Proof. exact (EQ_MP (@lem5393469 _69867 _69865 _69866) (@lem5393466 _69867 _69866 _69865)). Qed.
Lemma lem5393471 (_69867 : int) (_69865 : int) (_69866 : int) : term1012 _69867 _69865 _69866.
Proof. exact (EQ_MP (@lem5389715 _69867 _69865 _69866) (@lem5393470 _69867 _69865 _69866)). Qed.
Lemma lem5393472 (m : nat) (d : nat) (d' : nat) : term1285 m d d'.
Proof. exact (@lem5393471 (int_of_num m) (int_of_num d) (int_of_num d')). Qed.
Lemma lem5393473 (m : nat) (d : nat) (d' : nat) : term1286 m d d'.
Proof. exact (@lem5393472 m d d' (@lem5389708 d)). Qed.
Lemma lem5393474 (m : nat) (d : nat) (d' : nat) : term1287 m d d'.
Proof. exact (@lem5393473 m d d' (@lem5389711 d')). Qed.
Lemma lem5393475 (m : nat) (d : nat) (d' : nat) : term1008 m d d'.
Proof. exact (@lem5393474 m d d' (@lem5389714 m)). Qed.
Lemma lem5393476 (m : nat) (d : nat) : term1010 m d.
Proof. exact (fun d' : nat => @lem5393475 m d d'). Qed.
Lemma lem5393477 (d : nat) (m : nat) : (term1010 m d) = ((term4 d) = (term950 d m)).
Proof. exact (SYM (@lem5389705 m d)). Qed.
Lemma lem5393478 (d : nat) (m : nat) : (term4 d) = (term950 d m).
Proof. exact (EQ_MP (@lem5393477 d m) (@lem5393476 m d)). Qed.
Lemma lem5393479 (d : nat) (m : nat) : ((term4 d) = (term950 d m)) = (((term4 d) = (term950 d m)) = True).
Proof. exact (@lem7 ((term4 d) = (term950 d m))). Qed.
Lemma lem5393480 (d : nat) (m : nat) : ((term4 d) = (term950 d m)) = True.
Proof. exact (EQ_MP (@lem5393479 d m) (@lem5393478 d m)). Qed.
Lemma lem5393481 (d : nat) (m : nat) : True = ((term4 d) = (term950 d m)).
Proof. exact (SYM (@lem5393480 d m)). Qed.
Lemma lem5393482 (d : nat) (m : nat) : (term4 d) = (term950 d m).
Proof. exact (EQ_MP (@lem5393481 d m) (@lem0)). Qed.
Lemma lem5393483 (n : nat) (d : nat) (m : nat) : term953 n d m.
Proof. exact (fun h0 : n = (Nat.add m d) => @lem5393482 d m). Qed.
Lemma lem5393488 (n : nat) (m : nat) : term955 n m.
Proof. exact (fun d : nat => @lem5393483 n d m). Qed.
Lemma lem5393489 (n : nat) (m : nat) : term916 n m.
Proof. exact (EQ_MP (@lem5389495 n m) (@lem5393488 n m)). Qed.
Lemma lem5393490 (m : nat) (n : nat) (h1 : Peano.le m n) : (term686 m n) = (term16 n m).
Proof. exact (@lem5393489 n m (@lem5386552 m n h1)). Qed.
Lemma lem5393491 (n : nat) (m : nat) (h1 : Peano.lt n m) : (term686 m n) = (term16 n m).
Proof. exact (@lem5389282 n m (@lem5386551 n m h1)). Qed.
Lemma lem5393492 (n : nat) (m : nat) : (term686 m n) = (term16 n m).
Proof. exact (or_elim (@lem5386550 m n) (fun h0 : Peano.lt n m => @lem5393491 n m h0) (fun h0 : Peano.le m n => @lem5393490 m n h0)). Qed.
Lemma lem5393497 (m : nat) : term1288 m.
Proof. exact (fun n : nat => @lem5393492 n m). Qed.
Lemma lem5393502 : term1289.
Proof. exact (fun m : nat => @lem5393497 m). Qed.
