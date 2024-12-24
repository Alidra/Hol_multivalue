Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POLYFUN_EQ_CONST_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EQ_TRANS_spec.
Require Import IN_NUMSEG_spec.
Require Import LE_0_spec.
Require Import LE_1_spec.
Require Import REAL_MUL_RID_spec.
Require Import REAL_POLYFUN_EQ_0_spec.
Require Import REAL_SUB_0_spec.
Require Import SUM_CLAUSES_LEFT_spec.
Require Import SUM_EQ_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Require Import thm13473_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm15249_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
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
Require Import thm1982761_spec.
Require Import thm1982781_spec.
Require Import thm1982785_spec.
Require Import thm1982792_spec.
Require Import thm1988293_spec.
Require Import thm1988318_spec.
Require Import thm1988332_spec.
Require Import thm1988338_spec.
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
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm4211_spec.
Require Import thm513870_spec.
Require Import thm514290_spec.
Require Import thm517422_spec.
Require Import thm519779_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem7539533 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7539534 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem7539535 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem7539534 t1) (@lem7539533 t1)). Qed.
Lemma lem7539536 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem7539535 t1 t2). Qed.
Lemma lem7539537 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem7539538 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem7539537 t1 t2) (@lem7539536 t1 t2)). Qed.
Lemma lem7539539 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem7539538 t1 t2 t3). Qed.
Lemma lem7539540 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem7539541 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem7539540 t1 t2 t3) (@lem7539539 t1 t2 t3)). Qed.
Lemma lem7539542 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem7539541 t1 t2 t3)). Qed.
Lemma lem7539543 (x : real) : term7 x.
Proof. exact (@lem1376695 x). Qed.
Lemma lem7539544 (x : real) : (term7 x) = (term8 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem7539545 (x : real) : term8 x.
Proof. exact (EQ_MP (@lem7539544 x) (@lem7539543 x)). Qed.
Lemma lem7539546 (x : real) (y : real) : term9 x y.
Proof. exact (@lem7539545 x y). Qed.
Lemma lem7539547 (x : real) (y : real) : (term9 x y) = (((real_sub x y) = term10) = (x = y)).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem7539549 (n : nat) : term11 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem7539550 (n : nat) : (term11 n) = (term12 n).
Proof. exact (eq_refl (term11 n)). Qed.
Lemma lem7539551 (n : nat) : term12 n.
Proof. exact (EQ_MP (@lem7539550 n) (@lem7539549 n)). Qed.
Lemma lem7539552 (n : nat) : (term12 n) = ((term12 n) = True).
Proof. exact (@lem7 (term12 n)). Qed.
Lemma lem7539565 (p : Prop) : p = (term13 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7539566 (P : nat -> Prop) : ((term14 P) = (term15 P)) = (term16 P).
Proof. exact (@lem7539565 ((term14 P) = (term15 P))). Qed.
Lemma lem7539567 (P : nat -> Prop) : (term16 P) = ((term14 P) = (term15 P)).
Proof. exact (SYM (@lem7539566 P)). Qed.
Lemma lem7539568 (P : nat -> Prop) (h1 : term17 P) : term17 P.
Proof. exact (h1). Qed.
Lemma lem7539571 (P : nat -> Prop) (h1 : term16 P) : term16 P.
Proof. exact (h1). Qed.
Lemma lem7539572 (P : nat -> Prop) : term18 P.
Proof. exact (fun h0 : term16 P => @lem7539571 P h0). Qed.
Lemma lem7539573 (P : nat -> Prop) (h1 : term18 P) : term18 P.
Proof. exact (h1). Qed.
Lemma lem7539574 (P : nat -> Prop) (h1 : term16 P) : term16 P.
Proof. exact (h1). Qed.
Lemma lem7539575 (P : nat -> Prop) (h1 : term16 P) (h2 : term18 P) : term16 P.
Proof. exact (@lem7539573 P h2 (@lem7539574 P h1)). Qed.
Lemma lem7539576 (P : nat -> Prop) (h1 : term16 P) : term19 P.
Proof. exact (fun h0 : term18 P => @lem7539575 P h1 h0). Qed.
Lemma lem7539577 (P : nat -> Prop) (h1 : term18 P) : term18 P.
Proof. exact (h1). Qed.
Lemma lem7539578 (P : nat -> Prop) (h1 : term16 P) (h2 : term18 P) : term16 P.
Proof. exact (@lem7539576 P h1 (@lem7539577 P h2)). Qed.
Lemma lem7539579 (P : nat -> Prop) (h1 : term18 P) : term18 P.
Proof. exact (fun h0 : term16 P => @lem7539578 P h0 h1). Qed.
Lemma lem7539580 (P : nat -> Prop) : term20 P.
Proof. exact (fun h0 : term18 P => @lem7539579 P h0). Qed.
Lemma lem7539583 (P : nat -> Prop) : term18 P.
Proof. exact (@lem7539580 P (@lem7539572 P)). Qed.
Lemma lem7539589 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7539590 (P : nat -> Prop) : (term16 P) = (term21 P).
Proof. exact (@lem7539589 (term17 P)). Qed.
Lemma lem7539592 (t : Prop) : (term22 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7539593 (P : nat -> Prop) : (term21 P) = ((term14 P) = (term15 P)).
Proof. exact (@lem7539592 ((term14 P) = (term15 P))). Qed.
Lemma lem7539594 (P : nat -> Prop) : (term16 P) = ((term14 P) = (term15 P)).
Proof. exact (TRANS (@lem7539590 P) (@lem7539593 P)). Qed.
Lemma lem7539607 : term23 = term24.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem7539594 P)). Qed.
Lemma lem7539608 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem7539617 : term25 = term26.
Proof. exact (MK_COMB (@lem7539608) (@lem7539607)). Qed.
Lemma lem7539624 (P : nat -> Prop) (n : nat) : (term27 P n) = (term27 P n).
Proof. exact (eq_refl (term27 P n)). Qed.
Lemma lem7539625 (P : nat -> Prop) : (term28 P) = (term28 P).
Proof. exact (fun_ext (fun n : nat => @lem7539624 P n)). Qed.
Lemma lem7539626 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7539627 (P : nat -> Prop) : (term29 P) = (term29 P).
Proof. exact (MK_COMB (@lem7539626) (@lem7539625 P)). Qed.
Lemma lem7539630 (P : nat -> Prop) : (term30 P) = (term30 P).
Proof. exact (eq_refl (term30 P)). Qed.
Lemma lem7539631 (P : nat -> Prop) : (term15 P) = (term15 P).
Proof. exact (MK_COMB (@lem7539630 P) (@lem7539627 P)). Qed.
Lemma lem7539632 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem7539633 (P : nat -> Prop) : (term31 P) = (term31 P).
Proof. exact (fun_ext (fun n : nat => @lem7539632 P n)). Qed.
Lemma lem7539634 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7539635 (P : nat -> Prop) : (term14 P) = (term14 P).
Proof. exact (MK_COMB (@lem7539634) (@lem7539633 P)). Qed.
Lemma lem7539636 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7539637 (P : nat -> Prop) : (term32 P) = (term32 P).
Proof. exact (MK_COMB (@lem7539636) (@lem7539635 P)). Qed.
Lemma lem7539638 (P : nat -> Prop) : ((term14 P) = (term15 P)) = ((term14 P) = (term15 P)).
Proof. exact (MK_COMB (@lem7539637 P) (@lem7539631 P)). Qed.
Lemma lem7539639 : term24 = term24.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem7539638 P)). Qed.
Lemma lem7539640 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem7539641 : term26 = term26.
Proof. exact (MK_COMB (@lem7539640) (@lem7539639)). Qed.
Lemma lem7539666 : term25 = term26.
Proof. exact (TRANS (@lem7539617) (@lem7539641)). Qed.
Lemma lem7539667 : term26 = term25.
Proof. exact (SYM (@lem7539666)). Qed.
Lemma lem7539669 (p : Prop) : p = (term13 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7539670 (P : nat -> Prop) : ((term14 P) = (term15 P)) = (term16 P).
Proof. exact (@lem7539669 ((term14 P) = (term15 P))). Qed.
Lemma lem7539671 (P : nat -> Prop) : (term16 P) = ((term14 P) = (term15 P)).
Proof. exact (SYM (@lem7539670 P)). Qed.
Lemma lem7539672 (P : nat -> Prop) (h1 : term17 P) : term17 P.
Proof. exact (h1). Qed.
Lemma lem7539674 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem7539675 (P : nat -> Prop) : (term33 P) = (term34 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7539676 (P : nat -> Prop) : (term35 P) = (term36 P).
Proof. exact (@lem7539675 (term31 P)). Qed.
Lemma lem7539677 (P : nat -> Prop) (n : nat) : (term37 P n) = (P n).
Proof. exact (eq_refl (term37 P n)). Qed.
Lemma lem7539678 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7539680 (P : nat -> Prop) (n : nat) : (term38 P n) = (term39 P n).
Proof. exact (MK_COMB (@lem7539678) (@lem7539677 P n)). Qed.
Lemma lem7539681 (P : nat -> Prop) : (term40 P) = (term41 P).
Proof. exact (fun_ext (fun n : nat => @lem7539680 P n)). Qed.
Lemma lem7539682 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7539683 (P : nat -> Prop) : (term36 P) = (term34 P).
Proof. exact (MK_COMB (@lem7539682) (@lem7539681 P)). Qed.
Lemma lem7539684 (P : nat -> Prop) : (term35 P) = (term34 P).
Proof. exact (TRANS (@lem7539676 P) (@lem7539683 P)). Qed.
Lemma lem7539685 (P : nat -> Prop) : (term31 P) = (term31 P).
Proof. exact (fun_ext (fun n : nat => @lem7539674 P n)). Qed.
Lemma lem7539686 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7539687 (P : nat -> Prop) : (term14 P) = (term14 P).
Proof. exact (MK_COMB (@lem7539686) (@lem7539685 P)). Qed.
Lemma lem7539693 (n : nat) : (term42 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem7539695 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem7539700 (P : nat -> Prop) (n : nat) : (term43 P n) = (term44 P n).
Proof. exact (@lem17362 (term45 n) (P n)). Qed.
Lemma lem7539701 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7539702 (n : nat) : (term46 n) = (term47 n).
Proof. exact (MK_COMB (@lem7539701) (@lem7539693 n)). Qed.
Lemma lem7539703 (P : nat -> Prop) (n : nat) : (term48 P n) = (term49 P n).
Proof. exact (MK_COMB (@lem7539702 n) (@lem7539695 P n)). Qed.
Lemma lem7539704 (P : nat -> Prop) (n : nat) : (term27 P n) = (term48 P n).
Proof. exact (@lem17265 (term45 n) (P n)). Qed.
Lemma lem7539705 (P : nat -> Prop) (n : nat) : (term27 P n) = (term49 P n).
Proof. exact (TRANS (@lem7539704 P n) (@lem7539703 P n)). Qed.
Lemma lem7539706 (P : nat -> Prop) : (term33 P) = (term34 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7539707 (P : nat -> Prop) : (term50 P) = (term51 P).
Proof. exact (@lem7539706 (term28 P)). Qed.
Lemma lem7539708 (P : nat -> Prop) (n : nat) : (term52 P n) = (term27 P n).
Proof. exact (eq_refl (term52 P n)). Qed.
Lemma lem7539709 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7539710 (P : nat -> Prop) (n : nat) : (term53 P n) = (term43 P n).
Proof. exact (MK_COMB (@lem7539709) (@lem7539708 P n)). Qed.
Lemma lem7539711 (P : nat -> Prop) (n : nat) : (term53 P n) = (term44 P n).
Proof. exact (TRANS (@lem7539710 P n) (@lem7539700 P n)). Qed.
Lemma lem7539712 (P : nat -> Prop) : (term54 P) = (term55 P).
Proof. exact (fun_ext (fun n : nat => @lem7539711 P n)). Qed.
Lemma lem7539713 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7539714 (P : nat -> Prop) : (term51 P) = (term56 P).
Proof. exact (MK_COMB (@lem7539713) (@lem7539712 P)). Qed.
Lemma lem7539715 (P : nat -> Prop) : (term50 P) = (term56 P).
Proof. exact (TRANS (@lem7539707 P) (@lem7539714 P)). Qed.
Lemma lem7539716 (P : nat -> Prop) : (term28 P) = (term57 P).
Proof. exact (fun_ext (fun n : nat => @lem7539705 P n)). Qed.
Lemma lem7539717 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7539718 (P : nat -> Prop) : (term29 P) = (term58 P).
Proof. exact (MK_COMB (@lem7539717) (@lem7539716 P)). Qed.
Lemma lem7539720 (P : nat -> Prop) : (term59 P) = (term59 P).
Proof. exact (eq_refl (term59 P)). Qed.
Lemma lem7539721 (P : nat -> Prop) : (term60 P) = (term61 P).
Proof. exact (MK_COMB (@lem7539720 P) (@lem7539715 P)). Qed.
Lemma lem7539722 (P : nat -> Prop) : (term62 P) = (term60 P).
Proof. exact (@lem17045 (term63 P) (term29 P)). Qed.
Lemma lem7539723 (P : nat -> Prop) : (term62 P) = (term61 P).
Proof. exact (TRANS (@lem7539722 P) (@lem7539721 P)). Qed.
Lemma lem7539725 (P : nat -> Prop) : (term30 P) = (term30 P).
Proof. exact (eq_refl (term30 P)). Qed.
Lemma lem7539726 (P : nat -> Prop) : (term15 P) = (term64 P).
Proof. exact (MK_COMB (@lem7539725 P) (@lem7539718 P)). Qed.
Lemma lem7539727 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7539728 (P : nat -> Prop) : (term65 P) = (term66 P).
Proof. exact (MK_COMB (@lem7539727) (@lem7539684 P)). Qed.
Lemma lem7539729 (P : nat -> Prop) : (term67 P) = (term68 P).
Proof. exact (MK_COMB (@lem7539728 P) (@lem7539726 P)). Qed.
Lemma lem7539730 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7539731 (P : nat -> Prop) : (term69 P) = (term69 P).
Proof. exact (MK_COMB (@lem7539730) (@lem7539687 P)). Qed.
Lemma lem7539732 (P : nat -> Prop) : (term70 P) = (term71 P).
Proof. exact (MK_COMB (@lem7539731 P) (@lem7539723 P)). Qed.
Lemma lem7539733 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7539734 (P : nat -> Prop) : (term72 P) = (term73 P).
Proof. exact (MK_COMB (@lem7539733) (@lem7539732 P)). Qed.
Lemma lem7539735 (P : nat -> Prop) : (term74 P) = (term75 P).
Proof. exact (MK_COMB (@lem7539734 P) (@lem7539729 P)). Qed.
Lemma lem7539736 (P : nat -> Prop) : (term17 P) = (term74 P).
Proof. exact (@lem17646 (term14 P) (term15 P)). Qed.
Lemma lem7539737 (P : nat -> Prop) : (term17 P) = (term75 P).
Proof. exact (TRANS (@lem7539736 P) (@lem7539735 P)). Qed.
Lemma lem7539828 {A : Type'} (P : Prop) (Q : A -> Prop) : (term76 A P Q) = (term77 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7539829 (P : Prop) (Q : nat -> Prop) : (term78 P Q) = (term79 P Q).
Proof. exact (@lem7539828 nat P Q). Qed.
Lemma lem7539830 (P : nat -> Prop) : (term80 P) = (term81 P).
Proof. exact (@lem7539829 (term82 P) (term55 P)). Qed.
Lemma lem7539831 (P : nat -> Prop) (n : nat) : (term83 P n) = (term44 P n).
Proof. exact (eq_refl (term83 P n)). Qed.
Lemma lem7539832 (P : nat -> Prop) : (term84 P) = (term55 P).
Proof. exact (fun_ext (fun n : nat => @lem7539831 P n)). Qed.
Lemma lem7539833 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7539834 (P : nat -> Prop) : (term85 P) = (term56 P).
Proof. exact (MK_COMB (@lem7539833) (@lem7539832 P)). Qed.
Lemma lem7539835 (P : nat -> Prop) : (term59 P) = (term59 P).
Proof. exact (eq_refl (term59 P)). Qed.
Lemma lem7539836 (P : nat -> Prop) : (term80 P) = (term61 P).
Proof. exact (MK_COMB (@lem7539835 P) (@lem7539834 P)). Qed.
Lemma lem7539837 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7539838 (P : nat -> Prop) : (term86 P) = (term87 P).
Proof. exact (MK_COMB (@lem7539837) (@lem7539836 P)). Qed.
Lemma lem7539839 (P : nat -> Prop) (n : nat) : (term83 P n) = (term44 P n).
Proof. exact (eq_refl (term83 P n)). Qed.
Lemma lem7539840 (P : nat -> Prop) : (term59 P) = (term59 P).
Proof. exact (eq_refl (term59 P)). Qed.
Lemma lem7539841 (P : nat -> Prop) (n : nat) : (term88 P n) = (term89 P n).
Proof. exact (MK_COMB (@lem7539840 P) (@lem7539839 P n)). Qed.
Lemma lem7539842 (P : nat -> Prop) : (term90 P) = (term91 P).
Proof. exact (fun_ext (fun n : nat => @lem7539841 P n)). Qed.
Lemma lem7539843 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7539844 (P : nat -> Prop) : (term81 P) = (term92 P).
Proof. exact (MK_COMB (@lem7539843) (@lem7539842 P)). Qed.
Lemma lem7539845 (P : nat -> Prop) : ((term80 P) = (term81 P)) = ((term61 P) = (term92 P)).
Proof. exact (MK_COMB (@lem7539838 P) (@lem7539844 P)). Qed.
Lemma lem7539846 (P : nat -> Prop) : (term61 P) = (term92 P).
Proof. exact (EQ_MP (@lem7539845 P) (@lem7539830 P)). Qed.
Lemma lem7539847 (P : nat -> Prop) : (term69 P) = (term69 P).
Proof. exact (eq_refl (term69 P)). Qed.
Lemma lem7539848 (P : nat -> Prop) : (term71 P) = (term93 P).
Proof. exact (MK_COMB (@lem7539847 P) (@lem7539846 P)). Qed.
Lemma lem7539850 {A : Type'} (P : Prop) (Q : A -> Prop) : (term94 A P Q) = (term95 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7539851 (P : Prop) (Q : nat -> Prop) : (term96 P Q) = (term97 P Q).
Proof. exact (@lem7539850 nat P Q). Qed.
Lemma lem7539852 (P : nat -> Prop) : (term98 P) = (term99 P).
Proof. exact (@lem7539851 (term14 P) (term91 P)). Qed.
Lemma lem7539853 (P : nat -> Prop) (n : nat) : (term100 P n) = (term89 P n).
Proof. exact (eq_refl (term100 P n)). Qed.
Lemma lem7539854 (P : nat -> Prop) : (term101 P) = (term91 P).
Proof. exact (fun_ext (fun n : nat => @lem7539853 P n)). Qed.
Lemma lem7539855 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7539856 (P : nat -> Prop) : (term102 P) = (term92 P).
Proof. exact (MK_COMB (@lem7539855) (@lem7539854 P)). Qed.
Lemma lem7539857 (P : nat -> Prop) : (term69 P) = (term69 P).
Proof. exact (eq_refl (term69 P)). Qed.
Lemma lem7539858 (P : nat -> Prop) : (term98 P) = (term93 P).
Proof. exact (MK_COMB (@lem7539857 P) (@lem7539856 P)). Qed.
Lemma lem7539859 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7539860 (P : nat -> Prop) : (term103 P) = (term104 P).
Proof. exact (MK_COMB (@lem7539859) (@lem7539858 P)). Qed.
Lemma lem7539861 (P : nat -> Prop) (n : nat) : (term100 P n) = (term89 P n).
Proof. exact (eq_refl (term100 P n)). Qed.
Lemma lem7539862 (P : nat -> Prop) : (term69 P) = (term69 P).
Proof. exact (eq_refl (term69 P)). Qed.
Lemma lem7539863 (P : nat -> Prop) (n : nat) : (term105 P n) = (term106 P n).
Proof. exact (MK_COMB (@lem7539862 P) (@lem7539861 P n)). Qed.
Lemma lem7539864 (P : nat -> Prop) : (term107 P) = (term108 P).
Proof. exact (fun_ext (fun n : nat => @lem7539863 P n)). Qed.
Lemma lem7539865 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7539866 (P : nat -> Prop) : (term99 P) = (term109 P).
Proof. exact (MK_COMB (@lem7539865) (@lem7539864 P)). Qed.
Lemma lem7539867 (P : nat -> Prop) : ((term98 P) = (term99 P)) = ((term93 P) = (term109 P)).
Proof. exact (MK_COMB (@lem7539860 P) (@lem7539866 P)). Qed.
Lemma lem7539868 (P : nat -> Prop) : (term93 P) = (term109 P).
Proof. exact (EQ_MP (@lem7539867 P) (@lem7539852 P)). Qed.
Lemma lem7539869 (P : nat -> Prop) : (term71 P) = (term109 P).
Proof. exact (TRANS (@lem7539848 P) (@lem7539868 P)). Qed.
Lemma lem7539870 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7539871 (P : nat -> Prop) : (term73 P) = (term110 P).
Proof. exact (MK_COMB (@lem7539870) (@lem7539869 P)). Qed.
Lemma lem7539873 {A : Type'} (P : A -> Prop) (Q : Prop) : (term111 A P Q) = (term112 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7539874 (P : nat -> Prop) (Q : Prop) : (term113 P Q) = (term114 P Q).
Proof. exact (@lem7539873 nat P Q). Qed.
Lemma lem7539875 (P : nat -> Prop) : (term115 P) = (term116 P).
Proof. exact (@lem7539874 (term41 P) (term64 P)). Qed.
Lemma lem7539876 (P : nat -> Prop) (n : nat) : (term117 P n) = (term39 P n).
Proof. exact (eq_refl (term117 P n)). Qed.
Lemma lem7539877 (P : nat -> Prop) : (term118 P) = (term41 P).
Proof. exact (fun_ext (fun n : nat => @lem7539876 P n)). Qed.
Lemma lem7539878 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7539879 (P : nat -> Prop) : (term119 P) = (term34 P).
Proof. exact (MK_COMB (@lem7539878) (@lem7539877 P)). Qed.
Lemma lem7539880 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7539881 (P : nat -> Prop) : (term120 P) = (term66 P).
Proof. exact (MK_COMB (@lem7539880) (@lem7539879 P)). Qed.
Lemma lem7539882 (P : nat -> Prop) : (term64 P) = (term64 P).
Proof. exact (eq_refl (term64 P)). Qed.
Lemma lem7539883 (P : nat -> Prop) : (term115 P) = (term68 P).
Proof. exact (MK_COMB (@lem7539881 P) (@lem7539882 P)). Qed.
Lemma lem7539884 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7539885 (P : nat -> Prop) : (term121 P) = (term122 P).
Proof. exact (MK_COMB (@lem7539884) (@lem7539883 P)). Qed.
Lemma lem7539886 (P : nat -> Prop) (n : nat) : (term117 P n) = (term39 P n).
Proof. exact (eq_refl (term117 P n)). Qed.
Lemma lem7539887 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7539888 (P : nat -> Prop) (n : nat) : (term123 P n) = (term124 P n).
Proof. exact (MK_COMB (@lem7539887) (@lem7539886 P n)). Qed.
Lemma lem7539889 (P : nat -> Prop) : (term64 P) = (term64 P).
Proof. exact (eq_refl (term64 P)). Qed.
Lemma lem7539890 (n : nat) (P : nat -> Prop) : (term125 n P) = (term126 n P).
Proof. exact (MK_COMB (@lem7539888 P n) (@lem7539889 P)). Qed.
Lemma lem7539891 (P : nat -> Prop) : (term127 P) = (term128 P).
Proof. exact (fun_ext (fun n : nat => @lem7539890 n P)). Qed.
Lemma lem7539892 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7539893 (P : nat -> Prop) : (term116 P) = (term129 P).
Proof. exact (MK_COMB (@lem7539892) (@lem7539891 P)). Qed.
Lemma lem7539894 (P : nat -> Prop) : ((term115 P) = (term116 P)) = ((term68 P) = (term129 P)).
Proof. exact (MK_COMB (@lem7539885 P) (@lem7539893 P)). Qed.
Lemma lem7539895 (P : nat -> Prop) : (term68 P) = (term129 P).
Proof. exact (EQ_MP (@lem7539894 P) (@lem7539875 P)). Qed.
Lemma lem7539896 (P : nat -> Prop) : (term75 P) = (term130 P).
Proof. exact (MK_COMB (@lem7539871 P) (@lem7539895 P)). Qed.
Lemma lem7539898 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term131 A P Q) = (term132 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem7539899 (P : nat -> Prop) (Q : nat -> Prop) : (term133 P Q) = (term134 P Q).
Proof. exact (@lem7539898 nat P Q). Qed.
Lemma lem7539900 (P : nat -> Prop) : (term135 P) = (term136 P).
Proof. exact (@lem7539899 (term108 P) (term128 P)). Qed.
Lemma lem7539901 (P : nat -> Prop) (n : nat) : (term137 P n) = (term106 P n).
Proof. exact (eq_refl (term137 P n)). Qed.
Lemma lem7539902 (P : nat -> Prop) : (term138 P) = (term108 P).
Proof. exact (fun_ext (fun n : nat => @lem7539901 P n)). Qed.
Lemma lem7539903 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7539904 (P : nat -> Prop) : (term139 P) = (term109 P).
Proof. exact (MK_COMB (@lem7539903) (@lem7539902 P)). Qed.
Lemma lem7539905 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7539906 (P : nat -> Prop) : (term140 P) = (term110 P).
Proof. exact (MK_COMB (@lem7539905) (@lem7539904 P)). Qed.
Lemma lem7539907 (n : nat) (P : nat -> Prop) : (term141 P n) = (term126 n P).
Proof. exact (eq_refl (term141 P n)). Qed.
Lemma lem7539908 (P : nat -> Prop) : (term142 P) = (term128 P).
Proof. exact (fun_ext (fun n : nat => @lem7539907 n P)). Qed.
Lemma lem7539909 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7539910 (P : nat -> Prop) : (term143 P) = (term129 P).
Proof. exact (MK_COMB (@lem7539909) (@lem7539908 P)). Qed.
Lemma lem7539911 (P : nat -> Prop) : (term135 P) = (term130 P).
Proof. exact (MK_COMB (@lem7539906 P) (@lem7539910 P)). Qed.
Lemma lem7539912 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7539913 (P : nat -> Prop) : (term144 P) = (term145 P).
Proof. exact (MK_COMB (@lem7539912) (@lem7539911 P)). Qed.
Lemma lem7539914 (P : nat -> Prop) (n : nat) : (term137 P n) = (term106 P n).
Proof. exact (eq_refl (term137 P n)). Qed.
Lemma lem7539915 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7539916 (P : nat -> Prop) (n : nat) : (term146 P n) = (term147 P n).
Proof. exact (MK_COMB (@lem7539915) (@lem7539914 P n)). Qed.
Lemma lem7539917 (n : nat) (P : nat -> Prop) : (term141 P n) = (term126 n P).
Proof. exact (eq_refl (term141 P n)). Qed.
Lemma lem7539918 (n : nat) (P : nat -> Prop) : (term148 P n) = (term149 n P).
Proof. exact (MK_COMB (@lem7539916 P n) (@lem7539917 n P)). Qed.
Lemma lem7539919 (P : nat -> Prop) : (term150 P) = (term151 P).
Proof. exact (fun_ext (fun n : nat => @lem7539918 n P)). Qed.
Lemma lem7539920 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7539921 (P : nat -> Prop) : (term136 P) = (term152 P).
Proof. exact (MK_COMB (@lem7539920) (@lem7539919 P)). Qed.
Lemma lem7539922 (P : nat -> Prop) : ((term135 P) = (term136 P)) = ((term130 P) = (term152 P)).
Proof. exact (MK_COMB (@lem7539913 P) (@lem7539921 P)). Qed.
Lemma lem7539923 (P : nat -> Prop) : (term130 P) = (term152 P).
Proof. exact (EQ_MP (@lem7539922 P) (@lem7539900 P)). Qed.
Lemma lem7539925 (P : nat -> Prop) : (term75 P) = (term152 P).
Proof. exact (TRANS (@lem7539896 P) (@lem7539923 P)). Qed.
Lemma lem7539926 (P : nat -> Prop) : (term17 P) = (term152 P).
Proof. exact (TRANS (@lem7539737 P) (@lem7539925 P)). Qed.
Lemma lem7539927 (P : nat -> Prop) (h1 : term17 P) : term152 P.
Proof. exact (EQ_MP (@lem7539926 P) (@lem7539672 P h1)). Qed.
Lemma lem7539928 (n : nat) (P : nat -> Prop) (h1 : term149 n P) : term149 n P.
Proof. exact (h1). Qed.
Lemma lem7539941 (P : nat -> Prop) (n : nat) : (term49 P n) = (term49 P n).
Proof. exact (eq_refl (term49 P n)). Qed.
Lemma lem7539942 (P : nat -> Prop) : (term57 P) = (term57 P).
Proof. exact (fun_ext (fun n : nat => @lem7539941 P n)). Qed.
Lemma lem7539943 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7539944 (P : nat -> Prop) : (term58 P) = (term58 P).
Proof. exact (MK_COMB (@lem7539943) (@lem7539942 P)). Qed.
Lemma lem7539951 (P : nat -> Prop) : (term30 P) = (term30 P).
Proof. exact (eq_refl (term30 P)). Qed.
Lemma lem7539952 (P : nat -> Prop) : (term64 P) = (term64 P).
Proof. exact (MK_COMB (@lem7539951 P) (@lem7539944 P)). Qed.
Lemma lem7539959 (P : nat -> Prop) (n : nat) : (term124 P n) = (term124 P n).
Proof. exact (eq_refl (term124 P n)). Qed.
Lemma lem7539960 (n : nat) (P : nat -> Prop) : (term126 n P) = (term126 n P).
Proof. exact (MK_COMB (@lem7539959 P n) (@lem7539952 P)). Qed.
Lemma lem7539987 (P : nat -> Prop) (n : nat) : (term89 P n) = (term89 P n).
Proof. exact (eq_refl (term89 P n)). Qed.
Lemma lem7539990 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem7539991 (P : nat -> Prop) : (term31 P) = (term31 P).
Proof. exact (fun_ext (fun n : nat => @lem7539990 P n)). Qed.
Lemma lem7539992 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7539993 (P : nat -> Prop) : (term14 P) = (term14 P).
Proof. exact (MK_COMB (@lem7539992) (@lem7539991 P)). Qed.
Lemma lem7539994 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7539995 (P : nat -> Prop) : (term69 P) = (term69 P).
Proof. exact (MK_COMB (@lem7539994) (@lem7539993 P)). Qed.
Lemma lem7539996 (P : nat -> Prop) (n : nat) : (term106 P n) = (term106 P n).
Proof. exact (MK_COMB (@lem7539995 P) (@lem7539987 P n)). Qed.
Lemma lem7539997 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7539998 (P : nat -> Prop) (n : nat) : (term147 P n) = (term147 P n).
Proof. exact (MK_COMB (@lem7539997) (@lem7539996 P n)). Qed.
Lemma lem7539999 (n : nat) (P : nat -> Prop) : (term149 n P) = (term149 n P).
Proof. exact (MK_COMB (@lem7539998 P n) (@lem7539960 n P)). Qed.
Lemma lem7540000 (n : nat) (P : nat -> Prop) (h1 : term149 n P) : term149 n P.
Proof. exact (EQ_MP (@lem7539999 n P) (@lem7539928 n P h1)). Qed.
Lemma lem7540001 (P : nat -> Prop) (n : nat) (h1 : term106 P n) : term106 P n.
Proof. exact (h1). Qed.
Lemma lem7540002 (n : nat) (P : nat -> Prop) (h1 : term126 n P) : term126 n P.
Proof. exact (h1). Qed.
Lemma lem7540003 (P : nat -> Prop) (n : nat) (h1 : term106 P n) : term89 P n.
Proof. exact (proj2 (@lem7540001 P n h1)). Qed.
Lemma lem7540004 (P : nat -> Prop) (n : nat) (h1 : term106 P n) : term14 P.
Proof. exact (proj1 (@lem7540001 P n h1)). Qed.
Lemma lem7540006 (P : nat -> Prop) (n : nat) (h1 : term44 P n) : term44 P n.
Proof. exact (h1). Qed.
Lemma lem7540009 (n : nat) (P : nat -> Prop) (h1 : term126 n P) : term64 P.
Proof. exact (proj2 (@lem7540002 n P h1)). Qed.
Lemma lem7540011 (n : nat) (P : nat -> Prop) (h1 : term126 n P) : term58 P.
Proof. exact (proj2 (@lem7540009 n P h1)). Qed.
Lemma lem7540014 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem7540015 (P : nat -> Prop) : (term31 P) = (term31 P).
Proof. exact (fun_ext (fun n : nat => @lem7540014 P n)). Qed.
Lemma lem7540016 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7540018 (P : nat -> Prop) : (term14 P) = (term14 P).
Proof. exact (MK_COMB (@lem7540016) (@lem7540015 P)). Qed.
Lemma lem7540019 (P : nat -> Prop) (n : nat) (h1 : term106 P n) : term14 P.
Proof. exact (EQ_MP (@lem7540018 P) (@lem7540004 P n h1)). Qed.
Lemma lem7540023 (P : nat -> Prop) (h1 : term82 P) : term82 P.
Proof. exact (h1). Qed.
Lemma lem7540025 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem7540026 (P : nat -> Prop) : (term31 P) = (term31 P).
Proof. exact (fun_ext (fun n : nat => @lem7540025 P n)). Qed.
Lemma lem7540027 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7540029 (P : nat -> Prop) : (term14 P) = (term14 P).
Proof. exact (MK_COMB (@lem7540027) (@lem7540026 P)). Qed.
Lemma lem7540030 (P : nat -> Prop) (n : nat) (h1 : term106 P n) : term14 P.
Proof. exact (EQ_MP (@lem7540029 P) (@lem7540004 P n h1)). Qed.
Lemma lem7540054 (P : nat -> Prop) (n : nat) : (term49 P n) = (term49 P n).
Proof. exact (eq_refl (term49 P n)). Qed.
Lemma lem7540055 (P : nat -> Prop) : (term57 P) = (term57 P).
Proof. exact (fun_ext (fun n : nat => @lem7540054 P n)). Qed.
Lemma lem7540056 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7540058 (P : nat -> Prop) : (term58 P) = (term58 P).
Proof. exact (MK_COMB (@lem7540056) (@lem7540055 P)). Qed.
Lemma lem7540059 (n : nat) (P : nat -> Prop) (h1 : term126 n P) : term58 P.
Proof. exact (EQ_MP (@lem7540058 P) (@lem7540011 n P h1)). Qed.
Lemma lem7540060 (_97364 : nat) (P : nat -> Prop) (n : nat) (h1 : term106 P n) : term37 P _97364.
Proof. exact (@lem7540019 P n h1 _97364). Qed.
Lemma lem7540061 (P : nat -> Prop) (_97364 : nat) : (term37 P _97364) = (P _97364).
Proof. exact (eq_refl (term37 P _97364)). Qed.
Lemma lem7540063 (_97365 : nat) (P : nat -> Prop) (n : nat) (h1 : term106 P n) : term37 P _97365.
Proof. exact (@lem7540030 P n h1 _97365). Qed.
Lemma lem7540064 (P : nat -> Prop) (_97365 : nat) : (term37 P _97365) = (P _97365).
Proof. exact (eq_refl (term37 P _97365)). Qed.
Lemma lem7540066 (_97366 : nat) (n : nat) (P : nat -> Prop) (h1 : term126 n P) : term153 P _97366.
Proof. exact (@lem7540059 n P h1 _97366). Qed.
Lemma lem7540067 (P : nat -> Prop) (_97366 : nat) : (term153 P _97366) = (term49 P _97366).
Proof. exact (eq_refl (term153 P _97366)). Qed.
Lemma lem7540072 (P : nat -> Prop) (h1 : term82 P) : term82 P.
Proof. exact (h1). Qed.
Lemma lem7540078 (P : nat -> Prop) (n : nat) (h1 : term44 P n) : term39 P n.
Proof. exact (proj2 (@lem7540006 P n h1)). Qed.
Lemma lem7540080 (n : nat) (P : nat -> Prop) (h1 : term126 n P) : term39 P n.
Proof. exact (proj1 (@lem7540002 n P h1)). Qed.
Lemma lem7540088 (_97366 : nat) (n : nat) (P : nat -> Prop) (h1 : term126 n P) : term49 P _97366.
Proof. exact (EQ_MP (@lem7540067 P _97366) (@lem7540066 _97366 n P h1)). Qed.
Lemma lem7540090 (_97364 : nat) (P : nat -> Prop) (n : nat) (h1 : term106 P n) : P _97364.
Proof. exact (EQ_MP (@lem7540061 P _97364) (@lem7540060 _97364 P n h1)). Qed.
Lemma lem7540091 (P : nat -> Prop) (n : nat) (h1 : term106 P n) : term63 P.
Proof. exact (@lem7540090 (NUMERAL 0) P n h1). Qed.
Lemma lem7540092 (P : nat -> Prop) (n : nat) (h1 : term106 P n) : term154 P.
Proof. exact (fun h0 : term82 P => @lem7540091 P n h1). Qed.
Lemma lem7540094 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7540095 (P : nat -> Prop) : (term154 P) = (term63 P).
Proof. exact (@lem7540094 (term63 P)). Qed.
Lemma lem7540096 (P : nat -> Prop) (n : nat) (h1 : term106 P n) : term63 P.
Proof. exact (EQ_MP (@lem7540095 P) (@lem7540092 P n h1)). Qed.
Lemma lem7540099 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7540101 (P : nat -> Prop) : (term82 P) = (term156 P).
Proof. exact (@lem7540099 (term63 P)). Qed.
Lemma lem7540104 (P : nat -> Prop) (h1 : term82 P) : term156 P.
Proof. exact (EQ_MP (@lem7540101 P) (@lem7540072 P h1)). Qed.
Lemma lem7540107 (P : nat -> Prop) (n : nat) (h1 : term82 P) (h2 : term106 P n) : False.
Proof. exact (@lem7540104 P h1 (@lem7540096 P n h2)). Qed.
Lemma lem7540108 (P : nat -> Prop) (n : nat) (h1 : term82 P) (h2 : term106 P n) : term157.
Proof. exact (fun h0 : ~ False => @lem7540107 P n h1 h2). Qed.
Lemma lem7540110 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7540111 : term157 = False.
Proof. exact (@lem7540110 False). Qed.
Lemma lem7540112 (P : nat -> Prop) (n : nat) (h1 : term82 P) (h2 : term106 P n) : False.
Proof. exact (EQ_MP (@lem7540111) (@lem7540108 P n h1 h2)). Qed.
Lemma lem7540136 (_97365 : nat) (P : nat -> Prop) (n : nat) (h1 : term106 P n) : P _97365.
Proof. exact (EQ_MP (@lem7540064 P _97365) (@lem7540063 _97365 P n h1)). Qed.
Lemma lem7540137 (P : nat -> Prop) (n : nat) (h1 : term106 P n) : P n.
Proof. exact (@lem7540136 n P n h1). Qed.
Lemma lem7540138 (P : nat -> Prop) (n : nat) (h1 : term106 P n) : term158 P n.
Proof. exact (fun h0 : term39 P n => @lem7540137 P n h1). Qed.
Lemma lem7540140 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7540141 (P : nat -> Prop) (n : nat) : (term158 P n) = (P n).
Proof. exact (@lem7540140 (P n)). Qed.
Lemma lem7540142 (P : nat -> Prop) (n : nat) (h1 : term106 P n) : P n.
Proof. exact (EQ_MP (@lem7540141 P n) (@lem7540138 P n h1)). Qed.
Lemma lem7540145 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7540147 (P : nat -> Prop) (n : nat) : (term39 P n) = (term159 P n).
Proof. exact (@lem7540145 (P n)). Qed.
Lemma lem7540150 (P : nat -> Prop) (n : nat) (h1 : term44 P n) : term159 P n.
Proof. exact (EQ_MP (@lem7540147 P n) (@lem7540078 P n h1)). Qed.
Lemma lem7540153 (P : nat -> Prop) (n : nat) (h1 : term106 P n) (h2 : term44 P n) : False.
Proof. exact (@lem7540150 P n h2 (@lem7540142 P n h1)). Qed.
Lemma lem7540154 (P : nat -> Prop) (n : nat) (h1 : term106 P n) (h2 : term44 P n) : term157.
Proof. exact (fun h0 : ~ False => @lem7540153 P n h1 h2). Qed.
Lemma lem7540156 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7540157 : term157 = False.
Proof. exact (@lem7540156 False). Qed.
Lemma lem7540158 (P : nat -> Prop) (n : nat) (h1 : term106 P n) (h2 : term44 P n) : False.
Proof. exact (EQ_MP (@lem7540157) (@lem7540154 P n h1 h2)). Qed.
Lemma lem7540159 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem7540160 (_97371 : nat) (_97372 : nat) (h1 : _97371 = _97372) : _97371 = _97372.
Proof. exact (h1). Qed.
Lemma lem7540161 (P : nat -> Prop) (_97371 : nat) (_97372 : nat) (h1 : _97371 = _97372) : (P _97371) = (P _97372).
Proof. exact (MK_COMB (@lem7540159 P) (@lem7540160 _97371 _97372 h1)). Qed.
Lemma lem7540163 (b : Prop) (a : Prop) : term160 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem7540164 (_97372 : nat) (P : nat -> Prop) (_97371 : nat) : term161 _97372 P _97371.
Proof. exact (@lem7540163 (P _97372) (P _97371)). Qed.
Lemma lem7540165 (P : nat -> Prop) (_97371 : nat) (_97372 : nat) (h1 : _97371 = _97372) : term162 _97372 P _97371.
Proof. exact (@lem7540164 _97372 P _97371 (@lem7540161 P _97371 _97372 h1)). Qed.
Lemma lem7540166 (_97372 : nat) (P : nat -> Prop) (_97371 : nat) : term163 _97372 P _97371.
Proof. exact (fun h0 : _97371 = _97372 => @lem7540165 P _97371 _97372 h0). Qed.
Lemma lem7540168 (a : Prop) (b : Prop) : (a -> b) = (term164 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7540169 (_97372 : nat) (P : nat -> Prop) (_97371 : nat) : (term163 _97372 P _97371) = (term165 _97372 P _97371).
Proof. exact (@lem7540168 (_97371 = _97372) (term162 _97372 P _97371)). Qed.
Lemma lem7540170 (_97372 : nat) (P : nat -> Prop) (_97371 : nat) : term165 _97372 P _97371.
Proof. exact (EQ_MP (@lem7540169 _97372 P _97371) (@lem7540166 _97372 P _97371)). Qed.
Lemma lem7540180 (x : nat) (y : nat) (z : nat) : term166 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem7540182 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem7540183 (n : nat) : n = n.
Proof. exact (@lem7540182 n). Qed.
Lemma lem7540184 (n : nat) : term167 n.
Proof. exact (fun h0 : term168 n => @lem7540183 n). Qed.
Lemma lem7540186 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7540187 (n : nat) : (term167 n) = (n = n).
Proof. exact (@lem7540186 (n = n)). Qed.
Lemma lem7540188 (n : nat) : n = n.
Proof. exact (EQ_MP (@lem7540187 n) (@lem7540184 n)). Qed.
Lemma lem7540191 (P : nat -> Prop) (n : nat) (h1 : term39 P n) : term39 P n.
Proof. exact (h1). Qed.
Lemma lem7540192 (P : nat -> Prop) (n : nat) (h1 : term39 P n) : term169 P n.
Proof. exact (fun h0 : P n => @lem7540191 P n h1). Qed.
Lemma lem7540194 (p : Prop) : (term170 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7540195 (P : nat -> Prop) (n : nat) : (term169 P n) = (term39 P n).
Proof. exact (@lem7540194 (P n)). Qed.
Lemma lem7540196 (P : nat -> Prop) (n : nat) (h1 : term39 P n) : term39 P n.
Proof. exact (EQ_MP (@lem7540195 P n) (@lem7540192 P n h1)). Qed.
Lemma lem7540198 (n : nat) (P : nat -> Prop) (h1 : term126 n P) : term63 P.
Proof. exact (proj1 (@lem7540009 n P h1)). Qed.
Lemma lem7540199 (n : nat) (P : nat -> Prop) (h1 : term126 n P) : term154 P.
Proof. exact (fun h0 : term82 P => @lem7540198 n P h1). Qed.
Lemma lem7540201 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7540202 (P : nat -> Prop) : (term154 P) = (term63 P).
Proof. exact (@lem7540201 (term63 P)). Qed.
Lemma lem7540203 (n : nat) (P : nat -> Prop) (h1 : term126 n P) : term63 P.
Proof. exact (EQ_MP (@lem7540202 P) (@lem7540199 n P h1)). Qed.
Lemma lem7540205 (b : Prop) (a : Prop) : (a \/ b) = (term171 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7540206 (P : nat -> Prop) (_97371 : nat) (_97372 : nat) : (term165 _97372 P _97371) = (term172 P _97371 _97372).
Proof. exact (@lem7540205 (term162 _97372 P _97371) (term173 _97371 _97372)). Qed.
Lemma lem7540208 (a : Prop) (b : Prop) : (term174 a b) = (term175 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7540209 (_97372 : nat) (P : nat -> Prop) (_97371 : nat) : (term176 _97372 P _97371) = (term177 _97372 P _97371).
Proof. exact (@lem7540208 (P _97372) (term39 P _97371)). Qed.
Lemma lem7540211 (a : Prop) : (term22 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7540212 (P : nat -> Prop) (_97371 : nat) : (term178 P _97371) = (P _97371).
Proof. exact (@lem7540211 (P _97371)). Qed.
Lemma lem7540213 (P : nat -> Prop) (_97372 : nat) : (term124 P _97372) = (term124 P _97372).
Proof. exact (eq_refl (term124 P _97372)). Qed.
Lemma lem7540214 (_97372 : nat) (P : nat -> Prop) (_97371 : nat) : (term177 _97372 P _97371) = (term179 _97372 P _97371).
Proof. exact (MK_COMB (@lem7540213 P _97372) (@lem7540212 P _97371)). Qed.
Lemma lem7540215 (_97372 : nat) (P : nat -> Prop) (_97371 : nat) : (term176 _97372 P _97371) = (term179 _97372 P _97371).
Proof. exact (TRANS (@lem7540209 _97372 P _97371) (@lem7540214 _97372 P _97371)). Qed.
Lemma lem7540216 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7540217 (_97372 : nat) (P : nat -> Prop) (_97371 : nat) : (term180 _97372 P _97371) = (term181 _97372 P _97371).
Proof. exact (MK_COMB (@lem7540216) (@lem7540215 _97372 P _97371)). Qed.
Lemma lem7540218 (_97371 : nat) (_97372 : nat) : (term173 _97371 _97372) = (term173 _97371 _97372).
Proof. exact (eq_refl (term173 _97371 _97372)). Qed.
Lemma lem7540219 (P : nat -> Prop) (_97371 : nat) (_97372 : nat) : (term172 P _97371 _97372) = (term182 P _97371 _97372).
Proof. exact (MK_COMB (@lem7540217 _97372 P _97371) (@lem7540218 _97371 _97372)). Qed.
Lemma lem7540220 (P : nat -> Prop) (_97371 : nat) (_97372 : nat) : (term165 _97372 P _97371) = (term182 P _97371 _97372).
Proof. exact (TRANS (@lem7540206 P _97371 _97372) (@lem7540219 P _97371 _97372)). Qed.
Lemma lem7540222 (n : nat) (P : nat -> Prop) (h1 : term39 P n) (h2 : term126 n P) : term183 n P.
Proof. exact (conj (@lem7540196 P n h1) (@lem7540203 n P h2)). Qed.
Lemma lem7540224 (P : nat -> Prop) (_97371 : nat) (_97372 : nat) : term182 P _97371 _97372.
Proof. exact (EQ_MP (@lem7540220 P _97371 _97372) (@lem7540170 _97372 P _97371)). Qed.
Lemma lem7540225 (P : nat -> Prop) (n : nat) : term184 P n.
Proof. exact (@lem7540224 P (NUMERAL 0) n). Qed.
Lemma lem7540228 (n : nat) (P : nat -> Prop) (h1 : term39 P n) (h2 : term126 n P) : term185 n.
Proof. exact (@lem7540225 P n (@lem7540222 n P h1 h2)). Qed.
Lemma lem7540229 (n : nat) (P : nat -> Prop) (h1 : term39 P n) (h2 : term126 n P) : term186 n.
Proof. exact (fun h0 : (NUMERAL 0) = n => @lem7540228 n P h1 h2). Qed.
Lemma lem7540231 (p : Prop) : (term170 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7540232 (n : nat) : (term186 n) = (term185 n).
Proof. exact (@lem7540231 ((NUMERAL 0) = n)). Qed.
Lemma lem7540233 (n : nat) (P : nat -> Prop) (h1 : term39 P n) (h2 : term126 n P) : term185 n.
Proof. exact (EQ_MP (@lem7540232 n) (@lem7540229 n P h1 h2)). Qed.
Lemma lem7540235 (b : Prop) (a : Prop) : (a \/ b) = (term171 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7540236 (z : nat) (x : nat) (y : nat) : (term166 x y z) = (term187 z x y).
Proof. exact (@lem7540235 (term188 x y z) (term173 x y)). Qed.
Lemma lem7540238 (a : Prop) (b : Prop) : (term174 a b) = (term175 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7540239 (x : nat) (y : nat) (z : nat) : (term189 x y z) = (term190 x y z).
Proof. exact (@lem7540238 (term173 x z) (y = z)). Qed.
Lemma lem7540241 (a : Prop) : (term22 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7540242 (x : nat) (z : nat) : (term191 x z) = (x = z).
Proof. exact (@lem7540241 (x = z)). Qed.
Lemma lem7540243 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7540244 (x : nat) (z : nat) : (term192 x z) = (term193 x z).
Proof. exact (MK_COMB (@lem7540243) (@lem7540242 x z)). Qed.
Lemma lem7540245 (y : nat) (z : nat) : (term173 y z) = (term173 y z).
Proof. exact (eq_refl (term173 y z)). Qed.
Lemma lem7540246 (x : nat) (y : nat) (z : nat) : (term190 x y z) = (term194 x y z).
Proof. exact (MK_COMB (@lem7540244 x z) (@lem7540245 y z)). Qed.
Lemma lem7540247 (x : nat) (y : nat) (z : nat) : (term189 x y z) = (term194 x y z).
Proof. exact (TRANS (@lem7540239 x y z) (@lem7540246 x y z)). Qed.
Lemma lem7540248 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7540249 (x : nat) (y : nat) (z : nat) : (term195 x y z) = (term196 x y z).
Proof. exact (MK_COMB (@lem7540248) (@lem7540247 x y z)). Qed.
Lemma lem7540250 (x : nat) (y : nat) : (term173 x y) = (term173 x y).
Proof. exact (eq_refl (term173 x y)). Qed.
Lemma lem7540251 (z : nat) (x : nat) (y : nat) : (term187 z x y) = (term197 z x y).
Proof. exact (MK_COMB (@lem7540249 x y z) (@lem7540250 x y)). Qed.
Lemma lem7540252 (z : nat) (x : nat) (y : nat) : (term166 x y z) = (term197 z x y).
Proof. exact (TRANS (@lem7540236 z x y) (@lem7540251 z x y)). Qed.
Lemma lem7540254 (n : nat) (P : nat -> Prop) (h1 : term39 P n) (h2 : term126 n P) : term198 n.
Proof. exact (conj (@lem7540188 n) (@lem7540233 n P h1 h2)). Qed.
Lemma lem7540256 (z : nat) (x : nat) (y : nat) : term197 z x y.
Proof. exact (EQ_MP (@lem7540252 z x y) (@lem7540180 x y z)). Qed.
Lemma lem7540257 (n : nat) : term199 n.
Proof. exact (@lem7540256 n n (NUMERAL 0)). Qed.
Lemma lem7540260 (n : nat) (P : nat -> Prop) (h1 : term39 P n) (h2 : term126 n P) : term45 n.
Proof. exact (@lem7540257 n (@lem7540254 n P h1 h2)). Qed.
Lemma lem7540261 (n : nat) (P : nat -> Prop) (h1 : term39 P n) (h2 : term126 n P) : term200 n.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem7540260 n P h1 h2). Qed.
Lemma lem7540263 (p : Prop) : (term170 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7540264 (n : nat) : (term200 n) = (term45 n).
Proof. exact (@lem7540263 (n = (NUMERAL 0))). Qed.
Lemma lem7540265 (n : nat) (P : nat -> Prop) (h1 : term39 P n) (h2 : term126 n P) : term45 n.
Proof. exact (EQ_MP (@lem7540264 n) (@lem7540261 n P h1 h2)). Qed.
Lemma lem7540271 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7540272 (P : nat -> Prop) (_97366 : nat) : (term49 P _97366) = (term201 P _97366).
Proof. exact (@lem7540271 (P _97366) (_97366 = (NUMERAL 0))). Qed.
Lemma lem7540280 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7540281 (P : nat -> Prop) (_97366 : nat) : (term202 P _97366) = (term203 P _97366).
Proof. exact (MK_COMB (@lem7540280) (@lem7540272 P _97366)). Qed.
Lemma lem7540289 (P : nat -> Prop) (_97366 : nat) : (term201 P _97366) = (term201 P _97366).
Proof. exact (eq_refl (term201 P _97366)). Qed.
Lemma lem7540290 (P : nat -> Prop) (_97366 : nat) : ((term49 P _97366) = (term201 P _97366)) = ((term201 P _97366) = (term201 P _97366)).
Proof. exact (MK_COMB (@lem7540281 P _97366) (@lem7540289 P _97366)). Qed.
Lemma lem7540292 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7540293 (x : Prop) : (x = x) = True.
Proof. exact (@lem7540292 Prop x). Qed.
Lemma lem7540294 (P : nat -> Prop) (_97366 : nat) : ((term201 P _97366) = (term201 P _97366)) = True.
Proof. exact (@lem7540293 (term201 P _97366)). Qed.
Lemma lem7540295 (P : nat -> Prop) (_97366 : nat) : ((term49 P _97366) = (term201 P _97366)) = True.
Proof. exact (TRANS (@lem7540290 P _97366) (@lem7540294 P _97366)). Qed.
Lemma lem7540296 (P : nat -> Prop) (_97366 : nat) : True = ((term49 P _97366) = (term201 P _97366)).
Proof. exact (SYM (@lem7540295 P _97366)). Qed.
Lemma lem7540297 (P : nat -> Prop) (_97366 : nat) : (term49 P _97366) = (term201 P _97366).
Proof. exact (EQ_MP (@lem7540296 P _97366) (@lem0)). Qed.
Lemma lem7540298 (_97366 : nat) (n : nat) (P : nat -> Prop) (h1 : term126 n P) : term201 P _97366.
Proof. exact (EQ_MP (@lem7540297 P _97366) (@lem7540088 _97366 n P h1)). Qed.
Lemma lem7540300 (b : Prop) (a : Prop) : (a \/ b) = (term171 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7540303 (P : nat -> Prop) (_97366 : nat) : (term201 P _97366) = (term27 P _97366).
Proof. exact (@lem7540300 (_97366 = (NUMERAL 0)) (P _97366)). Qed.
Lemma lem7540306 (_97366 : nat) (n : nat) (P : nat -> Prop) (h1 : term126 n P) : term27 P _97366.
Proof. exact (EQ_MP (@lem7540303 P _97366) (@lem7540298 _97366 n P h1)). Qed.
Lemma lem7540307 (n : nat) (P : nat -> Prop) (h1 : term126 n P) : term27 P n.
Proof. exact (@lem7540306 n n P h1). Qed.
Lemma lem7540310 (n : nat) (P : nat -> Prop) (h1 : term39 P n) (h2 : term126 n P) : P n.
Proof. exact (@lem7540307 n P h2 (@lem7540265 n P h1 h2)). Qed.
Lemma lem7540311 (n : nat) (P : nat -> Prop) (h1 : term126 n P) : term158 P n.
Proof. exact (fun h0 : term39 P n => @lem7540310 n P h0 h1). Qed.
Lemma lem7540313 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7540314 (P : nat -> Prop) (n : nat) : (term158 P n) = (P n).
Proof. exact (@lem7540313 (P n)). Qed.
Lemma lem7540315 (n : nat) (P : nat -> Prop) (h1 : term126 n P) : P n.
Proof. exact (EQ_MP (@lem7540314 P n) (@lem7540311 n P h1)). Qed.
Lemma lem7540318 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7540320 (P : nat -> Prop) (n : nat) : (term39 P n) = (term159 P n).
Proof. exact (@lem7540318 (P n)). Qed.
Lemma lem7540323 (n : nat) (P : nat -> Prop) (h1 : term126 n P) : term159 P n.
Proof. exact (EQ_MP (@lem7540320 P n) (@lem7540080 n P h1)). Qed.
Lemma lem7540326 (n : nat) (P : nat -> Prop) (h1 : term126 n P) : False.
Proof. exact (@lem7540323 n P h1 (@lem7540315 n P h1)). Qed.
Lemma lem7540327 (n : nat) (P : nat -> Prop) (h1 : term126 n P) : term157.
Proof. exact (fun h0 : ~ False => @lem7540326 n P h1). Qed.
Lemma lem7540329 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7540330 : term157 = False.
Proof. exact (@lem7540329 False). Qed.
Lemma lem7540331 (n : nat) (P : nat -> Prop) (h1 : term126 n P) : False.
Proof. exact (EQ_MP (@lem7540330) (@lem7540327 n P h1)). Qed.
Lemma lem7540332 (P : nat -> Prop) (n : nat) (h1 : term82 P) (h2 : term106 P n) : (term82 P) = False.
Proof. exact (prop_ext (fun h3 : term82 P => @lem7540112 P n h1 h2) (fun h3 : False => @lem7540072 P h1)). Qed.
Lemma lem7540333 (P : nat -> Prop) (n : nat) (h1 : term82 P) (h2 : term106 P n) : False.
Proof. exact (EQ_MP (@lem7540332 P n h1 h2) (@lem7540072 P h1)). Qed.
Lemma lem7540334 (P : nat -> Prop) (n : nat) (h1 : term82 P) (h2 : term106 P n) : (term82 P) = False.
Proof. exact (prop_ext (fun h3 : term82 P => @lem7540333 P n h1 h2) (fun h3 : False => @lem7540023 P h1)). Qed.
Lemma lem7540335 (P : nat -> Prop) (n : nat) (h1 : term82 P) (h2 : term106 P n) : False.
Proof. exact (EQ_MP (@lem7540334 P n h1 h2) (@lem7540023 P h1)). Qed.
Lemma lem7540336 (P : nat -> Prop) (n : nat) (h1 : term82 P) (h2 : term106 P n) : (term82 P) = False.
Proof. exact (prop_ext (fun h3 : term82 P => @lem7540335 P n h1 h2) (fun h3 : False => @lem7540023 P h1)). Qed.
Lemma lem7540337 (P : nat -> Prop) (n : nat) (h1 : term82 P) (h2 : term106 P n) : False.
Proof. exact (EQ_MP (@lem7540336 P n h1 h2) (@lem7540023 P h1)). Qed.
Lemma lem7540338 (P : nat -> Prop) (n : nat) (h1 : term106 P n) : False.
Proof. exact (or_elim (@lem7540003 P n h1) (fun h0 : term82 P => @lem7540337 P n h0 h1) (fun h0 : term44 P n => @lem7540158 P n h1 h0)). Qed.
Lemma lem7540339 (n : nat) (P : nat -> Prop) (h1 : term149 n P) : False.
Proof. exact (or_elim (@lem7540000 n P h1) (fun h0 : term106 P n => @lem7540338 P n h0) (fun h0 : term126 n P => @lem7540331 n P h0)). Qed.
Lemma lem7540340 (n : nat) (P : nat -> Prop) (h1 : term149 n P) : (term149 n P) = False.
Proof. exact (prop_ext (fun h2 : term149 n P => @lem7540339 n P h1) (fun h2 : False => @lem7540000 n P h1)). Qed.
Lemma lem7540341 (n : nat) (P : nat -> Prop) (h1 : term149 n P) : False.
Proof. exact (EQ_MP (@lem7540340 n P h1) (@lem7540000 n P h1)). Qed.
Lemma lem7540342 (P : nat -> Prop) (h1 : term17 P) : False.
Proof. exact (ex_elim (@lem7539927 P h1) (fun n : nat => fun h0 : term151 P n => @lem7540341 n P h0)). Qed.
Lemma lem7540343 (P : nat -> Prop) (h1 : term17 P) : (term17 P) = False.
Proof. exact (prop_ext (fun h2 : term17 P => @lem7540342 P h1) (fun h2 : False => @lem7539672 P h1)). Qed.
Lemma lem7540344 (P : nat -> Prop) (h1 : term17 P) : False.
Proof. exact (EQ_MP (@lem7540343 P h1) (@lem7539672 P h1)). Qed.
Lemma lem7540345 (P : nat -> Prop) : term16 P.
Proof. exact (fun h0 : term17 P => @lem7540344 P h0). Qed.
Lemma lem7540346 (P : nat -> Prop) : (term14 P) = (term15 P).
Proof. exact (EQ_MP (@lem7539671 P) (@lem7540345 P)). Qed.
Lemma lem7540351 : term26.
Proof. exact (fun P : nat -> Prop => @lem7540346 P). Qed.
Lemma lem7540352 : term25.
Proof. exact (EQ_MP (@lem7539667) (@lem7540351)). Qed.
Lemma lem7540353 (P : nat -> Prop) : term204 P.
Proof. exact (@lem7540352 P). Qed.
Lemma lem7540354 (P : nat -> Prop) : (term204 P) = (term16 P).
Proof. exact (eq_refl (term204 P)). Qed.
Lemma lem7540355 (P : nat -> Prop) : term16 P.
Proof. exact (EQ_MP (@lem7540354 P) (@lem7540353 P)). Qed.
Lemma lem7540357 (P : nat -> Prop) : term16 P.
Proof. exact (@lem7539583 P (@lem7540355 P)). Qed.
Lemma lem7540358 (P : nat -> Prop) (h1 : term17 P) : False.
Proof. exact (@lem7540357 P (@lem7539568 P h1)). Qed.
Lemma lem7540359 (P : nat -> Prop) (h1 : term17 P) : (term17 P) = False.
Proof. exact (prop_ext (fun h2 : term17 P => @lem7540358 P h1) (fun h2 : False => @lem7539568 P h1)). Qed.
Lemma lem7540360 (P : nat -> Prop) (h1 : term17 P) : False.
Proof. exact (EQ_MP (@lem7540359 P h1) (@lem7539568 P h1)). Qed.
Lemma lem7540361 (P : nat -> Prop) : term16 P.
Proof. exact (fun h0 : term17 P => @lem7540360 P h0). Qed.
Lemma lem7540363 (n : nat) : term11 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem7540364 (n : nat) : (term11 n) = (term12 n).
Proof. exact (eq_refl (term11 n)). Qed.
Lemma lem7540365 (n : nat) : term12 n.
Proof. exact (EQ_MP (@lem7540364 n) (@lem7540363 n)). Qed.
Lemma lem7540366 (n : nat) : (term12 n) = ((term12 n) = True).
Proof. exact (@lem7 (term12 n)). Qed.
Lemma lem7540368 (m : nat) : term205 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem7540369 (m : nat) : (term205 m) = (term206 m).
Proof. exact (eq_refl (term205 m)). Qed.
Lemma lem7540370 (m : nat) : term206 m.
Proof. exact (EQ_MP (@lem7540369 m) (@lem7540368 m)). Qed.
Lemma lem7540371 (m : nat) (n : nat) : term207 m n.
Proof. exact (@lem7540370 m n). Qed.
Lemma lem7540372 (m : nat) (n : nat) : (term207 m n) = (term208 m n).
Proof. exact (eq_refl (term207 m n)). Qed.
Lemma lem7540373 (m : nat) (n : nat) : term208 m n.
Proof. exact (EQ_MP (@lem7540372 m n) (@lem7540371 m n)). Qed.
Lemma lem7540374 (m : nat) (n : nat) (p : nat) : term209 m n p.
Proof. exact (@lem7540373 m n p). Qed.
Lemma lem7540375 (m : nat) (p : nat) (n : nat) : (term209 m n p) = ((term210 p m n) = (term211 m p n)).
Proof. exact (eq_refl (term209 m n p)). Qed.
Lemma lem7540377 (n : nat) : term212 n.
Proof. exact (@lem7539532 n). Qed.
Lemma lem7540378 (n : nat) : (term212 n) = (term213 n).
Proof. exact (eq_refl (term212 n)). Qed.
Lemma lem7540379 (n : nat) : term213 n.
Proof. exact (EQ_MP (@lem7540378 n) (@lem7540377 n)). Qed.
Lemma lem7540380 (n : nat) (c : nat -> real) : term214 n c.
Proof. exact (@lem7540379 n c). Qed.
Lemma lem7540381 (n : nat) (c : nat -> real) : (term214 n c) = ((term215 n c) = (term216 n c)).
Proof. exact (eq_refl (term214 n c)). Qed.
Lemma lem7540383 (m : nat) : term205 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem7540384 (m : nat) : (term205 m) = (term206 m).
Proof. exact (eq_refl (term205 m)). Qed.
Lemma lem7540385 (m : nat) : term206 m.
Proof. exact (EQ_MP (@lem7540384 m) (@lem7540383 m)). Qed.
Lemma lem7540386 (m : nat) (n : nat) : term207 m n.
Proof. exact (@lem7540385 m n). Qed.
Lemma lem7540387 (m : nat) (n : nat) : (term207 m n) = (term208 m n).
Proof. exact (eq_refl (term207 m n)). Qed.
Lemma lem7540388 (m : nat) (n : nat) : term208 m n.
Proof. exact (EQ_MP (@lem7540387 m n) (@lem7540386 m n)). Qed.
Lemma lem7540389 (m : nat) (n : nat) (p : nat) : term209 m n p.
Proof. exact (@lem7540388 m n p). Qed.
Lemma lem7540390 (m : nat) (p : nat) (n : nat) : (term209 m n p) = ((term210 p m n) = (term211 m p n)).
Proof. exact (eq_refl (term209 m n p)). Qed.
Lemma lem7540392 {_132349 : Type'} (h1 : term217 _132349) : term217 _132349.
Proof. exact (h1). Qed.
Lemma lem7540393 {_132349 : Type'} (f : _132349 -> real) (h1 : term217 _132349) : term218 _132349 f.
Proof. exact (@lem7540392 _132349 h1 f). Qed.
Lemma lem7540394 {_132349 : Type'} (f : _132349 -> real) : (term218 _132349 f) = (term219 _132349 f).
Proof. exact (eq_refl (term218 _132349 f)). Qed.
Lemma lem7540395 {_132349 : Type'} (f : _132349 -> real) (h1 : term217 _132349) : term219 _132349 f.
Proof. exact (EQ_MP (@lem7540394 _132349 f) (@lem7540393 _132349 f h1)). Qed.
Lemma lem7540396 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) (h1 : term217 _132349) : term220 _132349 f g.
Proof. exact (@lem7540395 _132349 f h1 g). Qed.
Lemma lem7540397 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term220 _132349 f g) = (term221 _132349 f g).
Proof. exact (eq_refl (term220 _132349 f g)). Qed.
Lemma lem7540398 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) (h1 : term217 _132349) : term221 _132349 f g.
Proof. exact (EQ_MP (@lem7540397 _132349 f g) (@lem7540396 _132349 f g h1)). Qed.
Lemma lem7540399 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) (s : _132349 -> Prop) (h1 : term217 _132349) : term222 _132349 f g s.
Proof. exact (@lem7540398 _132349 f g h1 s). Qed.
Lemma lem7540400 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term222 _132349 f g s) = (term223 _132349 f s g).
Proof. exact (eq_refl (term222 _132349 f g s)). Qed.
Lemma lem7540401 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) (h1 : term217 _132349) : term223 _132349 f s g.
Proof. exact (EQ_MP (@lem7540400 _132349 f s g) (@lem7540399 _132349 f g s h1)). Qed.
Lemma lem7540402 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (h1 : term224 _132349 s f g) : term224 _132349 s f g.
Proof. exact (h1). Qed.
Lemma lem7540403 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (h1 : term224 _132349 s f g) (h2 : term217 _132349) : (@sum _132349 s f) = (@sum _132349 s g).
Proof. exact (@lem7540401 _132349 f s g h2 (@lem7540402 _132349 s f g h1)). Qed.
Lemma lem7540404 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (h1 : term224 _132349 s f g) : term225 _132349 f s g.
Proof. exact (fun h0 : term217 _132349 => @lem7540403 _132349 s f g h1 h0). Qed.
Lemma lem7540405 {_132349 : Type'} (h1 : term217 _132349) : term217 _132349.
Proof. exact (h1). Qed.
Lemma lem7540406 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (h1 : term224 _132349 s f g) (h2 : term217 _132349) : (@sum _132349 s f) = (@sum _132349 s g).
Proof. exact (@lem7540404 _132349 s f g h1 (@lem7540405 _132349 h2)). Qed.
Lemma lem7540407 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) (h1 : term217 _132349) : term223 _132349 f s g.
Proof. exact (fun h0 : term224 _132349 s f g => @lem7540406 _132349 s f g h0 h1). Qed.
Lemma lem7540408 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (h1 : term217 _132349) : term226 _132349 f s.
Proof. exact (fun g : _132349 -> real => @lem7540407 _132349 f s g h1). Qed.
Lemma lem7540409 {_132349 : Type'} (f : _132349 -> real) (h1 : term217 _132349) : term227 _132349 f.
Proof. exact (fun s : _132349 -> Prop => @lem7540408 _132349 f s h1). Qed.
Lemma lem7540410 {_132349 : Type'} (h1 : term217 _132349) : term228 _132349.
Proof. exact (fun f : _132349 -> real => @lem7540409 _132349 f h1). Qed.
Lemma lem7540411 {_132349 : Type'} : term229 _132349.
Proof. exact (fun h0 : term217 _132349 => @lem7540410 _132349 h0). Qed.
Lemma lem7540412 {_132349 : Type'} : term228 _132349.
Proof. exact (@lem7540411 _132349 (@lem7081239 _132349)). Qed.
Lemma lem7540413 {_132349 : Type'} (f : _132349 -> real) : term230 _132349 f.
Proof. exact (@lem7540412 _132349 f). Qed.
Lemma lem7540414 {_132349 : Type'} (f : _132349 -> real) : (term230 _132349 f) = (term227 _132349 f).
Proof. exact (eq_refl (term230 _132349 f)). Qed.
Lemma lem7540415 {_132349 : Type'} (f : _132349 -> real) : term227 _132349 f.
Proof. exact (EQ_MP (@lem7540414 _132349 f) (@lem7540413 _132349 f)). Qed.
Lemma lem7540416 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) : term231 _132349 f s.
Proof. exact (@lem7540415 _132349 f s). Qed.
Lemma lem7540417 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) : (term231 _132349 f s) = (term226 _132349 f s).
Proof. exact (eq_refl (term231 _132349 f s)). Qed.
Lemma lem7540418 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) : term226 _132349 f s.
Proof. exact (EQ_MP (@lem7540417 _132349 f s) (@lem7540416 _132349 f s)). Qed.
Lemma lem7540419 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : term232 _132349 f s g.
Proof. exact (@lem7540418 _132349 f s g). Qed.
Lemma lem7540420 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term232 _132349 f s g) = (term223 _132349 f s g).
Proof. exact (eq_refl (term232 _132349 f s g)). Qed.
Lemma lem7540459 (c : real) (s : real) (k : real) : (term233 c s k) = (term234 c s k).
Proof. exact (@lem17646 ((term235 c k s) = term10) ((real_add c s) = k)). Qed.
Lemma lem7540460 (c : real) (k : real) (s : real) : ((term235 c k s) = term10) = ((term236 c k s) = term10).
Proof. exact (@lem1988293 (term235 c k s) term10). Qed.
Lemma lem7540461 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7540462 (s : real) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7540475 (c : real) (k : real) : (real_sub c k) = (term237 c k).
Proof. exact (@lem1982792 c k). Qed.
Lemma lem7540476 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7540477 (c : real) (k : real) : (term238 c k) = (term239 c k).
Proof. exact (MK_COMB (@lem7540476) (@lem7540475 c k)). Qed.
Lemma lem7540478 (c : real) (k : real) (s : real) : (term235 c k s) = (term240 c k s).
Proof. exact (MK_COMB (@lem7540477 c k) (@lem7540462 s)). Qed.
Lemma lem7540483 (c : real) (k : real) (s : real) : (term240 c k s) = (term241 c k s).
Proof. exact (@lem1982755 c (term242 k) s). Qed.
Lemma lem7540484 (c : real) (k : real) (s : real) : (term235 c k s) = (term241 c k s).
Proof. exact (TRANS (@lem7540478 c k s) (@lem7540483 c k s)). Qed.
Lemma lem7540485 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7540486 (c : real) (k : real) (s : real) : (term243 c k s) = (term244 c k s).
Proof. exact (MK_COMB (@lem7540485) (@lem7540484 c k s)). Qed.
Lemma lem7540487 (c : real) (k : real) (s : real) : (term236 c k s) = (term245 c k s).
Proof. exact (MK_COMB (@lem7540486 c k s) (@lem7540461)). Qed.
Lemma lem7540488 (c : real) (k : real) (s : real) : (term245 c k s) = (term246 c k s).
Proof. exact (@lem1982792 (term241 c k s) term10). Qed.
Lemma lem7540490 (x : nat) : (real_of_num x) = (term247 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7540491 : term10 = term248.
Proof. exact (@lem7540490 (NUMERAL 0)). Qed.
Lemma lem7540493 (x : nat) : (term249 x) = (term250 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7540494 : term251 = term252.
Proof. exact (@lem7540493 term253). Qed.
Lemma lem7540495 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7540496 : term254 = term255.
Proof. exact (MK_COMB (@lem7540495) (@lem7540494)). Qed.
Lemma lem7540497 : term256 = term257.
Proof. exact (MK_COMB (@lem7540496) (@lem7540491)). Qed.
Lemma lem7540498 : term257 = term258.
Proof. exact (@lem1981613 term251 term10 term259 term259). Qed.
Lemma lem7540500 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7540501 : term262 = term263.
Proof. exact (@lem7540500 term253 term253). Qed.
Lemma lem7540502 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7540503 : term265 = term253.
Proof. exact (EQ_MP (@lem7540502) (@lem940073)). Qed.
Lemma lem7540504 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7540505 : term263 = term259.
Proof. exact (MK_COMB (@lem7540504) (@lem7540503)). Qed.
Lemma lem7540506 : term262 = term259.
Proof. exact (TRANS (@lem7540501) (@lem7540505)). Qed.
Lemma lem7540508 (x : nat) : (term266 x) = term10.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7540509 : term256 = term10.
Proof. exact (@lem7540508 term253). Qed.
Lemma lem7540510 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7540511 : term267 = term268.
Proof. exact (MK_COMB (@lem7540510) (@lem7540509)). Qed.
Lemma lem7540512 : term258 = term248.
Proof. exact (MK_COMB (@lem7540511) (@lem7540506)). Qed.
Lemma lem7540513 : term257 = term248.
Proof. exact (TRANS (@lem7540498) (@lem7540512)). Qed.
Lemma lem7540514 : term256 = term248.
Proof. exact (TRANS (@lem7540497) (@lem7540513)). Qed.
Lemma lem7540516 (x : real) : (term269 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7540517 : term248 = term10.
Proof. exact (@lem7540516 term10). Qed.
Lemma lem7540518 : term256 = term10.
Proof. exact (TRANS (@lem7540514) (@lem7540517)). Qed.
Lemma lem7540519 (c : real) (k : real) (s : real) : (term270 c k s) = (term270 c k s).
Proof. exact (eq_refl (term270 c k s)). Qed.
Lemma lem7540520 (c : real) (k : real) (s : real) : (term246 c k s) = (term271 c k s).
Proof. exact (MK_COMB (@lem7540519 c k s) (@lem7540518)). Qed.
Lemma lem7540521 (c : real) (k : real) (s : real) : (term271 c k s) = (term241 c k s).
Proof. exact (@lem1982723 (term241 c k s)). Qed.
Lemma lem7540522 (c : real) (k : real) (s : real) : (term246 c k s) = (term241 c k s).
Proof. exact (TRANS (@lem7540520 c k s) (@lem7540521 c k s)). Qed.
Lemma lem7540523 (c : real) (k : real) (s : real) : (term245 c k s) = (term241 c k s).
Proof. exact (TRANS (@lem7540488 c k s) (@lem7540522 c k s)). Qed.
Lemma lem7540524 (c : real) (k : real) (s : real) : (term236 c k s) = (term241 c k s).
Proof. exact (TRANS (@lem7540487 c k s) (@lem7540523 c k s)). Qed.
Lemma lem7540525 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7540526 (c : real) (k : real) (s : real) : (term272 c k s) = (term273 c k s).
Proof. exact (MK_COMB (@lem7540525) (@lem7540524 c k s)). Qed.
Lemma lem7540527 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7540528 (c : real) (k : real) (s : real) : ((term236 c k s) = term10) = ((term241 c k s) = term10).
Proof. exact (MK_COMB (@lem7540526 c k s) (@lem7540527)). Qed.
Lemma lem7540529 (c : real) (k : real) (s : real) : ((term235 c k s) = term10) = ((term241 c k s) = term10).
Proof. exact (TRANS (@lem7540460 c k s) (@lem7540528 c k s)). Qed.
Lemma lem7540530 (c : real) (s : real) (k : real) : (term274 c s k) = (term275 c s k).
Proof. exact (@lem1988318 (real_add c s) k). Qed.
Lemma lem7540542 (c : real) (s : real) (k : real) : (term276 c s k) = (term277 c s k).
Proof. exact (@lem1982792 (real_add c s) k). Qed.
Lemma lem7540546 (c : real) (s : real) (k : real) : (term277 c s k) = (term278 c s k).
Proof. exact (@lem1982755 c s (term242 k)). Qed.
Lemma lem7540547 (k : real) (s : real) : (term237 s k) = (term279 k s).
Proof. exact (@lem1982761 (term242 k) s). Qed.
Lemma lem7540548 (c : real) : (real_add c) = (real_add c).
Proof. exact (eq_refl (real_add c)). Qed.
Lemma lem7540549 (c : real) (k : real) (s : real) : (term278 c s k) = (term241 c k s).
Proof. exact (MK_COMB (@lem7540548 c) (@lem7540547 k s)). Qed.
Lemma lem7540551 (c : real) (k : real) (s : real) : (term277 c s k) = (term241 c k s).
Proof. exact (TRANS (@lem7540546 c s k) (@lem7540549 c k s)). Qed.
Lemma lem7540553 (c : real) (k : real) (s : real) : (term276 c s k) = (term241 c k s).
Proof. exact (TRANS (@lem7540542 c s k) (@lem7540551 c k s)). Qed.
Lemma lem7540554 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7540555 (c : real) (k : real) (s : real) : (term280 c s k) = (term281 c k s).
Proof. exact (MK_COMB (@lem7540554) (@lem7540553 c k s)). Qed.
Lemma lem7540556 (c : real) (k : real) (s : real) : (term281 c k s) = (term282 c k s).
Proof. exact (@lem1982785 (term241 c k s)). Qed.
Lemma lem7540557 (c : real) (k : real) (s : real) : (term282 c k s) = (term283 c k s).
Proof. exact (@lem1982781 c term251 (term279 k s)). Qed.
Lemma lem7540558 (k : real) (s : real) : (term284 k s) = (term285 k s).
Proof. exact (@lem1982781 (term242 k) term251 s). Qed.
Lemma lem7540559 (s : real) : (term242 s) = (term242 s).
Proof. exact (eq_refl (term242 s)). Qed.
Lemma lem7540560 (k : real) : (term286 k) = (term287 k).
Proof. exact (@lem1982749 term251 term251 k). Qed.
Lemma lem7540562 (x : nat) : (term249 x) = (term250 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7540563 : term251 = term252.
Proof. exact (@lem7540562 term253). Qed.
Lemma lem7540565 (x : nat) : (term249 x) = (term250 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7540566 : term251 = term252.
Proof. exact (@lem7540565 term253). Qed.
Lemma lem7540567 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7540568 : term254 = term255.
Proof. exact (MK_COMB (@lem7540567) (@lem7540566)). Qed.
Lemma lem7540569 : term288 = term289.
Proof. exact (MK_COMB (@lem7540568) (@lem7540563)). Qed.
Lemma lem7540570 : term289 = term290.
Proof. exact (@lem1981613 term251 term251 term259 term259). Qed.
Lemma lem7540572 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7540573 : term262 = term263.
Proof. exact (@lem7540572 term253 term253). Qed.
Lemma lem7540574 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7540575 : term265 = term253.
Proof. exact (EQ_MP (@lem7540574) (@lem940073)). Qed.
Lemma lem7540576 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7540577 : term263 = term259.
Proof. exact (MK_COMB (@lem7540576) (@lem7540575)). Qed.
Lemma lem7540578 : term262 = term259.
Proof. exact (TRANS (@lem7540573) (@lem7540577)). Qed.
Lemma lem7540580 (m : nat) (n : nat) : (term291 m n) = (term261 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7540581 : term288 = term263.
Proof. exact (@lem7540580 term253 term253). Qed.
Lemma lem7540582 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7540583 : term265 = term253.
Proof. exact (EQ_MP (@lem7540582) (@lem940073)). Qed.
Lemma lem7540584 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7540585 : term263 = term259.
Proof. exact (MK_COMB (@lem7540584) (@lem7540583)). Qed.
Lemma lem7540586 : term288 = term259.
Proof. exact (TRANS (@lem7540581) (@lem7540585)). Qed.
Lemma lem7540587 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7540588 : term292 = term293.
Proof. exact (MK_COMB (@lem7540587) (@lem7540586)). Qed.
Lemma lem7540589 : term290 = term294.
Proof. exact (MK_COMB (@lem7540588) (@lem7540578)). Qed.
Lemma lem7540590 : term289 = term294.
Proof. exact (TRANS (@lem7540570) (@lem7540589)). Qed.
Lemma lem7540591 : term288 = term294.
Proof. exact (TRANS (@lem7540569) (@lem7540590)). Qed.
Lemma lem7540593 (x : real) : (term269 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7540594 : term294 = term259.
Proof. exact (@lem7540593 term259). Qed.
Lemma lem7540595 : term288 = term259.
Proof. exact (TRANS (@lem7540591) (@lem7540594)). Qed.
Lemma lem7540596 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7540597 : term295 = term296.
Proof. exact (MK_COMB (@lem7540596) (@lem7540595)). Qed.
Lemma lem7540598 (k : real) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem7540599 (k : real) : (term287 k) = (term297 k).
Proof. exact (MK_COMB (@lem7540597) (@lem7540598 k)). Qed.
Lemma lem7540600 (k : real) : (term286 k) = (term297 k).
Proof. exact (TRANS (@lem7540560 k) (@lem7540599 k)). Qed.
Lemma lem7540601 (k : real) : (term297 k) = k.
Proof. exact (@lem1982709 k). Qed.
Lemma lem7540602 (k : real) : (term286 k) = k.
Proof. exact (TRANS (@lem7540600 k) (@lem7540601 k)). Qed.
Lemma lem7540603 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7540604 (k : real) : (term298 k) = (real_add k).
Proof. exact (MK_COMB (@lem7540603) (@lem7540602 k)). Qed.
Lemma lem7540605 (k : real) (s : real) : (term285 k s) = (term237 k s).
Proof. exact (MK_COMB (@lem7540604 k) (@lem7540559 s)). Qed.
Lemma lem7540606 (k : real) (s : real) : (term284 k s) = (term237 k s).
Proof. exact (TRANS (@lem7540558 k s) (@lem7540605 k s)). Qed.
Lemma lem7540609 (c : real) : (term299 c) = (term299 c).
Proof. exact (eq_refl (term299 c)). Qed.
Lemma lem7540610 (c : real) (k : real) (s : real) : (term283 c k s) = (term300 c k s).
Proof. exact (MK_COMB (@lem7540609 c) (@lem7540606 k s)). Qed.
Lemma lem7540611 (c : real) (k : real) (s : real) : (term282 c k s) = (term300 c k s).
Proof. exact (TRANS (@lem7540557 c k s) (@lem7540610 c k s)). Qed.
Lemma lem7540612 (c : real) (k : real) (s : real) : (term281 c k s) = (term300 c k s).
Proof. exact (TRANS (@lem7540556 c k s) (@lem7540611 c k s)). Qed.
Lemma lem7540613 (c : real) (s : real) (k : real) : (term301 c s k) = (term301 c s k).
Proof. exact (eq_refl (term301 c s k)). Qed.
Lemma lem7540614 (c : real) (k : real) (s : real) : ((term280 c s k) = (term281 c k s)) = ((term280 c s k) = (term300 c k s)).
Proof. exact (MK_COMB (@lem7540613 c s k) (@lem7540612 c k s)). Qed.
Lemma lem7540615 (c : real) (k : real) (s : real) : (term280 c s k) = (term300 c k s).
Proof. exact (EQ_MP (@lem7540614 c k s) (@lem7540555 c k s)). Qed.
Lemma lem7540616 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7540617 (c : real) (k : real) (s : real) : (term302 c s k) = (term303 c k s).
Proof. exact (MK_COMB (@lem7540616) (@lem7540615 c k s)). Qed.
Lemma lem7540618 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7540619 (c : real) (k : real) (s : real) : (term304 c s k) = (term305 c k s).
Proof. exact (MK_COMB (@lem7540617 c k s) (@lem7540618)). Qed.
Lemma lem7540620 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7540621 (c : real) (k : real) (s : real) : (term306 c s k) = (term307 c k s).
Proof. exact (MK_COMB (@lem7540620) (@lem7540553 c k s)). Qed.
Lemma lem7540622 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7540623 (c : real) (k : real) (s : real) : (term308 c s k) = (term309 c k s).
Proof. exact (MK_COMB (@lem7540621 c k s) (@lem7540622)). Qed.
Lemma lem7540624 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7540625 (c : real) (k : real) (s : real) : (term310 c s k) = (term311 c k s).
Proof. exact (MK_COMB (@lem7540624) (@lem7540623 c k s)). Qed.
Lemma lem7540626 (c : real) (k : real) (s : real) : (term275 c s k) = (term312 c k s).
Proof. exact (MK_COMB (@lem7540625 c k s) (@lem7540619 c k s)). Qed.
Lemma lem7540627 (c : real) (k : real) (s : real) : (term274 c s k) = (term312 c k s).
Proof. exact (TRANS (@lem7540530 c s k) (@lem7540626 c k s)). Qed.
Lemma lem7540628 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7540629 (c : real) (k : real) (s : real) : (term313 c k s) = (term314 c k s).
Proof. exact (MK_COMB (@lem7540628) (@lem7540529 c k s)). Qed.
Lemma lem7540630 (c : real) (k : real) (s : real) : (term315 c s k) = (term316 c k s).
Proof. exact (MK_COMB (@lem7540629 c k s) (@lem7540627 c k s)). Qed.
Lemma lem7540631 (c : real) (k : real) (s : real) : (term317 c k s) = (term318 c k s).
Proof. exact (@lem1988318 (term235 c k s) term10). Qed.
Lemma lem7540632 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7540633 (s : real) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7540646 (c : real) (k : real) : (real_sub c k) = (term237 c k).
Proof. exact (@lem1982792 c k). Qed.
Lemma lem7540647 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7540648 (c : real) (k : real) : (term238 c k) = (term239 c k).
Proof. exact (MK_COMB (@lem7540647) (@lem7540646 c k)). Qed.
Lemma lem7540649 (c : real) (k : real) (s : real) : (term235 c k s) = (term240 c k s).
Proof. exact (MK_COMB (@lem7540648 c k) (@lem7540633 s)). Qed.
Lemma lem7540654 (c : real) (k : real) (s : real) : (term240 c k s) = (term241 c k s).
Proof. exact (@lem1982755 c (term242 k) s). Qed.
Lemma lem7540655 (c : real) (k : real) (s : real) : (term235 c k s) = (term241 c k s).
Proof. exact (TRANS (@lem7540649 c k s) (@lem7540654 c k s)). Qed.
Lemma lem7540656 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7540657 (c : real) (k : real) (s : real) : (term243 c k s) = (term244 c k s).
Proof. exact (MK_COMB (@lem7540656) (@lem7540655 c k s)). Qed.
Lemma lem7540658 (c : real) (k : real) (s : real) : (term236 c k s) = (term245 c k s).
Proof. exact (MK_COMB (@lem7540657 c k s) (@lem7540632)). Qed.
Lemma lem7540659 (c : real) (k : real) (s : real) : (term245 c k s) = (term246 c k s).
Proof. exact (@lem1982792 (term241 c k s) term10). Qed.
Lemma lem7540661 (x : nat) : (real_of_num x) = (term247 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7540662 : term10 = term248.
Proof. exact (@lem7540661 (NUMERAL 0)). Qed.
Lemma lem7540664 (x : nat) : (term249 x) = (term250 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7540665 : term251 = term252.
Proof. exact (@lem7540664 term253). Qed.
Lemma lem7540666 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7540667 : term254 = term255.
Proof. exact (MK_COMB (@lem7540666) (@lem7540665)). Qed.
Lemma lem7540668 : term256 = term257.
Proof. exact (MK_COMB (@lem7540667) (@lem7540662)). Qed.
Lemma lem7540669 : term257 = term258.
Proof. exact (@lem1981613 term251 term10 term259 term259). Qed.
Lemma lem7540671 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7540672 : term262 = term263.
Proof. exact (@lem7540671 term253 term253). Qed.
Lemma lem7540673 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7540674 : term265 = term253.
Proof. exact (EQ_MP (@lem7540673) (@lem940073)). Qed.
Lemma lem7540675 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7540676 : term263 = term259.
Proof. exact (MK_COMB (@lem7540675) (@lem7540674)). Qed.
Lemma lem7540677 : term262 = term259.
Proof. exact (TRANS (@lem7540672) (@lem7540676)). Qed.
Lemma lem7540679 (x : nat) : (term266 x) = term10.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7540680 : term256 = term10.
Proof. exact (@lem7540679 term253). Qed.
Lemma lem7540681 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7540682 : term267 = term268.
Proof. exact (MK_COMB (@lem7540681) (@lem7540680)). Qed.
Lemma lem7540683 : term258 = term248.
Proof. exact (MK_COMB (@lem7540682) (@lem7540677)). Qed.
Lemma lem7540684 : term257 = term248.
Proof. exact (TRANS (@lem7540669) (@lem7540683)). Qed.
Lemma lem7540685 : term256 = term248.
Proof. exact (TRANS (@lem7540668) (@lem7540684)). Qed.
Lemma lem7540687 (x : real) : (term269 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7540688 : term248 = term10.
Proof. exact (@lem7540687 term10). Qed.
Lemma lem7540689 : term256 = term10.
Proof. exact (TRANS (@lem7540685) (@lem7540688)). Qed.
Lemma lem7540690 (c : real) (k : real) (s : real) : (term270 c k s) = (term270 c k s).
Proof. exact (eq_refl (term270 c k s)). Qed.
Lemma lem7540691 (c : real) (k : real) (s : real) : (term246 c k s) = (term271 c k s).
Proof. exact (MK_COMB (@lem7540690 c k s) (@lem7540689)). Qed.
Lemma lem7540692 (c : real) (k : real) (s : real) : (term271 c k s) = (term241 c k s).
Proof. exact (@lem1982723 (term241 c k s)). Qed.
Lemma lem7540693 (c : real) (k : real) (s : real) : (term246 c k s) = (term241 c k s).
Proof. exact (TRANS (@lem7540691 c k s) (@lem7540692 c k s)). Qed.
Lemma lem7540694 (c : real) (k : real) (s : real) : (term245 c k s) = (term241 c k s).
Proof. exact (TRANS (@lem7540659 c k s) (@lem7540693 c k s)). Qed.
Lemma lem7540695 (c : real) (k : real) (s : real) : (term236 c k s) = (term241 c k s).
Proof. exact (TRANS (@lem7540658 c k s) (@lem7540694 c k s)). Qed.
Lemma lem7540696 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7540697 (c : real) (k : real) (s : real) : (term319 c k s) = (term281 c k s).
Proof. exact (MK_COMB (@lem7540696) (@lem7540695 c k s)). Qed.
Lemma lem7540698 (c : real) (k : real) (s : real) : (term281 c k s) = (term282 c k s).
Proof. exact (@lem1982785 (term241 c k s)). Qed.
Lemma lem7540699 (c : real) (k : real) (s : real) : (term282 c k s) = (term283 c k s).
Proof. exact (@lem1982781 c term251 (term279 k s)). Qed.
Lemma lem7540700 (k : real) (s : real) : (term284 k s) = (term285 k s).
Proof. exact (@lem1982781 (term242 k) term251 s). Qed.
Lemma lem7540701 (s : real) : (term242 s) = (term242 s).
Proof. exact (eq_refl (term242 s)). Qed.
Lemma lem7540702 (k : real) : (term286 k) = (term287 k).
Proof. exact (@lem1982749 term251 term251 k). Qed.
Lemma lem7540704 (x : nat) : (term249 x) = (term250 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7540705 : term251 = term252.
Proof. exact (@lem7540704 term253). Qed.
Lemma lem7540707 (x : nat) : (term249 x) = (term250 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7540708 : term251 = term252.
Proof. exact (@lem7540707 term253). Qed.
Lemma lem7540709 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7540710 : term254 = term255.
Proof. exact (MK_COMB (@lem7540709) (@lem7540708)). Qed.
Lemma lem7540711 : term288 = term289.
Proof. exact (MK_COMB (@lem7540710) (@lem7540705)). Qed.
Lemma lem7540712 : term289 = term290.
Proof. exact (@lem1981613 term251 term251 term259 term259). Qed.
Lemma lem7540714 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7540715 : term262 = term263.
Proof. exact (@lem7540714 term253 term253). Qed.
Lemma lem7540716 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7540717 : term265 = term253.
Proof. exact (EQ_MP (@lem7540716) (@lem940073)). Qed.
Lemma lem7540718 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7540719 : term263 = term259.
Proof. exact (MK_COMB (@lem7540718) (@lem7540717)). Qed.
Lemma lem7540720 : term262 = term259.
Proof. exact (TRANS (@lem7540715) (@lem7540719)). Qed.
Lemma lem7540722 (m : nat) (n : nat) : (term291 m n) = (term261 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7540723 : term288 = term263.
Proof. exact (@lem7540722 term253 term253). Qed.
Lemma lem7540724 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7540725 : term265 = term253.
Proof. exact (EQ_MP (@lem7540724) (@lem940073)). Qed.
Lemma lem7540726 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7540727 : term263 = term259.
Proof. exact (MK_COMB (@lem7540726) (@lem7540725)). Qed.
Lemma lem7540728 : term288 = term259.
Proof. exact (TRANS (@lem7540723) (@lem7540727)). Qed.
Lemma lem7540729 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7540730 : term292 = term293.
Proof. exact (MK_COMB (@lem7540729) (@lem7540728)). Qed.
Lemma lem7540731 : term290 = term294.
Proof. exact (MK_COMB (@lem7540730) (@lem7540720)). Qed.
Lemma lem7540732 : term289 = term294.
Proof. exact (TRANS (@lem7540712) (@lem7540731)). Qed.
Lemma lem7540733 : term288 = term294.
Proof. exact (TRANS (@lem7540711) (@lem7540732)). Qed.
Lemma lem7540735 (x : real) : (term269 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7540736 : term294 = term259.
Proof. exact (@lem7540735 term259). Qed.
Lemma lem7540737 : term288 = term259.
Proof. exact (TRANS (@lem7540733) (@lem7540736)). Qed.
Lemma lem7540738 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7540739 : term295 = term296.
Proof. exact (MK_COMB (@lem7540738) (@lem7540737)). Qed.
Lemma lem7540740 (k : real) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem7540741 (k : real) : (term287 k) = (term297 k).
Proof. exact (MK_COMB (@lem7540739) (@lem7540740 k)). Qed.
Lemma lem7540742 (k : real) : (term286 k) = (term297 k).
Proof. exact (TRANS (@lem7540702 k) (@lem7540741 k)). Qed.
Lemma lem7540743 (k : real) : (term297 k) = k.
Proof. exact (@lem1982709 k). Qed.
Lemma lem7540744 (k : real) : (term286 k) = k.
Proof. exact (TRANS (@lem7540742 k) (@lem7540743 k)). Qed.
Lemma lem7540745 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7540746 (k : real) : (term298 k) = (real_add k).
Proof. exact (MK_COMB (@lem7540745) (@lem7540744 k)). Qed.
Lemma lem7540747 (k : real) (s : real) : (term285 k s) = (term237 k s).
Proof. exact (MK_COMB (@lem7540746 k) (@lem7540701 s)). Qed.
Lemma lem7540748 (k : real) (s : real) : (term284 k s) = (term237 k s).
Proof. exact (TRANS (@lem7540700 k s) (@lem7540747 k s)). Qed.
Lemma lem7540751 (c : real) : (term299 c) = (term299 c).
Proof. exact (eq_refl (term299 c)). Qed.
Lemma lem7540752 (c : real) (k : real) (s : real) : (term283 c k s) = (term300 c k s).
Proof. exact (MK_COMB (@lem7540751 c) (@lem7540748 k s)). Qed.
Lemma lem7540753 (c : real) (k : real) (s : real) : (term282 c k s) = (term300 c k s).
Proof. exact (TRANS (@lem7540699 c k s) (@lem7540752 c k s)). Qed.
Lemma lem7540754 (c : real) (k : real) (s : real) : (term281 c k s) = (term300 c k s).
Proof. exact (TRANS (@lem7540698 c k s) (@lem7540753 c k s)). Qed.
Lemma lem7540755 (c : real) (k : real) (s : real) : (term320 c k s) = (term320 c k s).
Proof. exact (eq_refl (term320 c k s)). Qed.
Lemma lem7540756 (c : real) (k : real) (s : real) : ((term319 c k s) = (term281 c k s)) = ((term319 c k s) = (term300 c k s)).
Proof. exact (MK_COMB (@lem7540755 c k s) (@lem7540754 c k s)). Qed.
Lemma lem7540757 (c : real) (k : real) (s : real) : (term319 c k s) = (term300 c k s).
Proof. exact (EQ_MP (@lem7540756 c k s) (@lem7540697 c k s)). Qed.
Lemma lem7540758 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7540759 (c : real) (k : real) (s : real) : (term321 c k s) = (term303 c k s).
Proof. exact (MK_COMB (@lem7540758) (@lem7540757 c k s)). Qed.
Lemma lem7540760 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7540761 (c : real) (k : real) (s : real) : (term322 c k s) = (term305 c k s).
Proof. exact (MK_COMB (@lem7540759 c k s) (@lem7540760)). Qed.
Lemma lem7540762 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7540763 (c : real) (k : real) (s : real) : (term323 c k s) = (term307 c k s).
Proof. exact (MK_COMB (@lem7540762) (@lem7540695 c k s)). Qed.
Lemma lem7540764 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7540765 (c : real) (k : real) (s : real) : (term324 c k s) = (term309 c k s).
Proof. exact (MK_COMB (@lem7540763 c k s) (@lem7540764)). Qed.
Lemma lem7540766 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7540767 (c : real) (k : real) (s : real) : (term325 c k s) = (term311 c k s).
Proof. exact (MK_COMB (@lem7540766) (@lem7540765 c k s)). Qed.
Lemma lem7540768 (c : real) (k : real) (s : real) : (term318 c k s) = (term312 c k s).
Proof. exact (MK_COMB (@lem7540767 c k s) (@lem7540761 c k s)). Qed.
Lemma lem7540769 (c : real) (k : real) (s : real) : (term317 c k s) = (term312 c k s).
Proof. exact (TRANS (@lem7540631 c k s) (@lem7540768 c k s)). Qed.
Lemma lem7540770 (c : real) (s : real) (k : real) : ((real_add c s) = k) = ((term276 c s k) = term10).
Proof. exact (@lem1988293 (real_add c s) k). Qed.
Lemma lem7540782 (c : real) (s : real) (k : real) : (term276 c s k) = (term277 c s k).
Proof. exact (@lem1982792 (real_add c s) k). Qed.
Lemma lem7540786 (c : real) (s : real) (k : real) : (term277 c s k) = (term278 c s k).
Proof. exact (@lem1982755 c s (term242 k)). Qed.
Lemma lem7540787 (k : real) (s : real) : (term237 s k) = (term279 k s).
Proof. exact (@lem1982761 (term242 k) s). Qed.
Lemma lem7540788 (c : real) : (real_add c) = (real_add c).
Proof. exact (eq_refl (real_add c)). Qed.
Lemma lem7540789 (c : real) (k : real) (s : real) : (term278 c s k) = (term241 c k s).
Proof. exact (MK_COMB (@lem7540788 c) (@lem7540787 k s)). Qed.
Lemma lem7540791 (c : real) (k : real) (s : real) : (term277 c s k) = (term241 c k s).
Proof. exact (TRANS (@lem7540786 c s k) (@lem7540789 c k s)). Qed.
Lemma lem7540793 (c : real) (k : real) (s : real) : (term276 c s k) = (term241 c k s).
Proof. exact (TRANS (@lem7540782 c s k) (@lem7540791 c k s)). Qed.
Lemma lem7540794 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7540795 (c : real) (k : real) (s : real) : (term326 c s k) = (term273 c k s).
Proof. exact (MK_COMB (@lem7540794) (@lem7540793 c k s)). Qed.
Lemma lem7540796 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7540797 (c : real) (k : real) (s : real) : ((term276 c s k) = term10) = ((term241 c k s) = term10).
Proof. exact (MK_COMB (@lem7540795 c k s) (@lem7540796)). Qed.
Lemma lem7540798 (c : real) (k : real) (s : real) : ((real_add c s) = k) = ((term241 c k s) = term10).
Proof. exact (TRANS (@lem7540770 c s k) (@lem7540797 c k s)). Qed.
Lemma lem7540799 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7540800 (c : real) (k : real) (s : real) : (term327 c k s) = (term328 c k s).
Proof. exact (MK_COMB (@lem7540799) (@lem7540769 c k s)). Qed.
Lemma lem7540801 (c : real) (k : real) (s : real) : (term329 c s k) = (term330 c k s).
Proof. exact (MK_COMB (@lem7540800 c k s) (@lem7540798 c k s)). Qed.
Lemma lem7540802 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7540803 (c : real) (k : real) (s : real) : (term331 c s k) = (term332 c k s).
Proof. exact (MK_COMB (@lem7540802) (@lem7540630 c k s)). Qed.
Lemma lem7540804 (c : real) (k : real) (s : real) : (term234 c s k) = (term333 c k s).
Proof. exact (MK_COMB (@lem7540803 c k s) (@lem7540801 c k s)). Qed.
Lemma lem7540811 (c : real) (k : real) (s : real) : (term233 c s k) = (term333 c k s).
Proof. exact (TRANS (@lem7540459 c s k) (@lem7540804 c k s)). Qed.
Lemma lem7540828 (c : real) (k : real) (s : real) : (term330 c k s) = (term334 c k s).
Proof. exact (@lem19367 (term309 c k s) (term305 c k s) ((term241 c k s) = term10)). Qed.
Lemma lem7540845 (c : real) (k : real) (s : real) : (term316 c k s) = (term335 c k s).
Proof. exact (@lem19158 (term309 c k s) ((term241 c k s) = term10) (term305 c k s)). Qed.
Lemma lem7540846 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7540847 (c : real) (k : real) (s : real) : (term332 c k s) = (term336 c k s).
Proof. exact (MK_COMB (@lem7540846) (@lem7540845 c k s)). Qed.
Lemma lem7540848 (c : real) (k : real) (s : real) : (term333 c k s) = (term337 c k s).
Proof. exact (MK_COMB (@lem7540847 c k s) (@lem7540828 c k s)). Qed.
Lemma lem7540849 (c : real) (k : real) (s : real) : (term233 c s k) = (term337 c k s).
Proof. exact (TRANS (@lem7540811 c k s) (@lem7540848 c k s)). Qed.
Lemma lem7540871 (c : real) (k : real) (s : real) (h1 : term337 c k s) : term337 c k s.
Proof. exact (h1). Qed.
Lemma lem7540872 (c : real) (k : real) (s : real) (h1 : term335 c k s) : term335 c k s.
Proof. exact (h1). Qed.
Lemma lem7540873 (c : real) (k : real) (s : real) (h1 : term338 c k s) : term338 c k s.
Proof. exact (h1). Qed.
Lemma lem7540874 (c : real) (k : real) (s : real) (h1 : term338 c k s) : term309 c k s.
Proof. exact (proj2 (@lem7540873 c k s h1)). Qed.
Lemma lem7540875 (c : real) (k : real) (s : real) (h1 : term338 c k s) : (term241 c k s) = term10.
Proof. exact (proj1 (@lem7540873 c k s h1)). Qed.
Lemma lem7540877 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7540878 : term339 = term340.
Proof. exact (@lem7540877 term10 term259). Qed.
Lemma lem7540880 (x : nat) : (real_of_num x) = (term247 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7540881 : term259 = term294.
Proof. exact (@lem7540880 term253). Qed.
Lemma lem7540883 (x : nat) : (real_of_num x) = (term247 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7540884 : term10 = term248.
Proof. exact (@lem7540883 (NUMERAL 0)). Qed.
Lemma lem7540885 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7540886 : term341 = term342.
Proof. exact (MK_COMB (@lem7540885) (@lem7540884)). Qed.
Lemma lem7540887 : term340 = term343.
Proof. exact (MK_COMB (@lem7540886) (@lem7540881)). Qed.
Lemma lem7540888 : term344.
Proof. exact (@lem1980255 term10 term259 term259 term259). Qed.
Lemma lem7540890 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7540891 : term340 = term346.
Proof. exact (@lem7540890 (NUMERAL 0) term253). Qed.
Lemma lem7540892 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7540893 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7540894 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7540893 h1) (fun h1 : term346 = True => @lem7540892)). Qed.
Lemma lem7540895 : term346 = True.
Proof. exact (EQ_MP (@lem7540894) (@lem7540892)). Qed.
Lemma lem7540896 : term340 = True.
Proof. exact (TRANS (@lem7540891) (@lem7540895)). Qed.
Lemma lem7540897 : True = term340.
Proof. exact (SYM (@lem7540896)). Qed.
Lemma lem7540898 : term340.
Proof. exact (EQ_MP (@lem7540897) (@lem0)). Qed.
Lemma lem7540899 : term348.
Proof. exact (@lem7540888 (@lem7540898)). Qed.
Lemma lem7540901 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7540902 : term340 = term346.
Proof. exact (@lem7540901 (NUMERAL 0) term253). Qed.
Lemma lem7540903 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7540904 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7540905 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7540904 h1) (fun h1 : term346 = True => @lem7540903)). Qed.
Lemma lem7540906 : term346 = True.
Proof. exact (EQ_MP (@lem7540905) (@lem7540903)). Qed.
Lemma lem7540907 : term340 = True.
Proof. exact (TRANS (@lem7540902) (@lem7540906)). Qed.
Lemma lem7540908 : True = term340.
Proof. exact (SYM (@lem7540907)). Qed.
Lemma lem7540909 : term340.
Proof. exact (EQ_MP (@lem7540908) (@lem0)). Qed.
Lemma lem7540910 : term343 = term349.
Proof. exact (@lem7540899 (@lem7540909)). Qed.
Lemma lem7540912 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7540913 : term262 = term263.
Proof. exact (@lem7540912 term253 term253). Qed.
Lemma lem7540914 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7540915 : term265 = term253.
Proof. exact (EQ_MP (@lem7540914) (@lem940073)). Qed.
Lemma lem7540916 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7540917 : term263 = term259.
Proof. exact (MK_COMB (@lem7540916) (@lem7540915)). Qed.
Lemma lem7540918 : term262 = term259.
Proof. exact (TRANS (@lem7540913) (@lem7540917)). Qed.
Lemma lem7540920 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7540921 : term351 = term10.
Proof. exact (@lem7540920 term253). Qed.
Lemma lem7540922 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7540923 : term352 = term341.
Proof. exact (MK_COMB (@lem7540922) (@lem7540921)). Qed.
Lemma lem7540924 : term349 = term340.
Proof. exact (MK_COMB (@lem7540923) (@lem7540918)). Qed.
Lemma lem7540926 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7540927 : term340 = term346.
Proof. exact (@lem7540926 (NUMERAL 0) term253). Qed.
Lemma lem7540928 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7540929 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7540930 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7540929 h1) (fun h1 : term346 = True => @lem7540928)). Qed.
Lemma lem7540931 : term346 = True.
Proof. exact (EQ_MP (@lem7540930) (@lem7540928)). Qed.
Lemma lem7540932 : term340 = True.
Proof. exact (TRANS (@lem7540927) (@lem7540931)). Qed.
Lemma lem7540933 : term349 = True.
Proof. exact (TRANS (@lem7540924) (@lem7540932)). Qed.
Lemma lem7540934 : term343 = True.
Proof. exact (TRANS (@lem7540910) (@lem7540933)). Qed.
Lemma lem7540935 : term340 = True.
Proof. exact (TRANS (@lem7540887) (@lem7540934)). Qed.
Lemma lem7540936 : term339 = True.
Proof. exact (TRANS (@lem7540878) (@lem7540935)). Qed.
Lemma lem7540937 : True = term339.
Proof. exact (SYM (@lem7540936)). Qed.
Lemma lem7540938 : term339.
Proof. exact (EQ_MP (@lem7540937) (@lem0)). Qed.
Lemma lem7540939 (c : real) (k : real) (s : real) (h1 : term338 c k s) : term353 c k s.
Proof. exact (conj (@lem7540938) (@lem7540874 c k s h1)). Qed.
Lemma lem7540941 (x : real) (y : real) : term354 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem7540942 (c : real) (k : real) (s : real) : term355 c k s.
Proof. exact (@lem7540941 term259 (term241 c k s)). Qed.
Lemma lem7540943 (c : real) (k : real) (s : real) (h1 : term338 c k s) : term356 c k s.
Proof. exact (@lem7540942 c k s (@lem7540939 c k s h1)). Qed.
Lemma lem7540944 (c : real) (k : real) (s : real) : (term357 c k s) = (term241 c k s).
Proof. exact (@lem1982733 (term241 c k s)). Qed.
Lemma lem7540945 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7540946 (c : real) (k : real) (s : real) : (term358 c k s) = (term307 c k s).
Proof. exact (MK_COMB (@lem7540945) (@lem7540944 c k s)). Qed.
Lemma lem7540947 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7540948 (c : real) (k : real) (s : real) : (term356 c k s) = (term309 c k s).
Proof. exact (MK_COMB (@lem7540946 c k s) (@lem7540947)). Qed.
Lemma lem7540949 (c : real) (k : real) (s : real) (h1 : term338 c k s) : term309 c k s.
Proof. exact (EQ_MP (@lem7540948 c k s) (@lem7540943 c k s h1)). Qed.
Lemma lem7540951 (y : real) : term359 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem7540952 (c : real) (k : real) (s : real) : term360 c k s.
Proof. exact (@lem7540951 (term241 c k s)). Qed.
Lemma lem7540953 (c : real) (k : real) (s : real) (h1 : term338 c k s) : term361 c k s.
Proof. exact (@lem7540952 c k s (@lem7540875 c k s h1)). Qed.
Lemma lem7540954 (c : real) (k : real) (s : real) (h1 : term338 c k s) : term362 c k s.
Proof. exact (@lem7540953 c k s h1 term251). Qed.
Lemma lem7540955 (c : real) (k : real) (s : real) : (term362 c k s) = ((term282 c k s) = term10).
Proof. exact (eq_refl (term362 c k s)). Qed.
Lemma lem7540956 (c : real) (k : real) (s : real) (h1 : term338 c k s) : (term282 c k s) = term10.
Proof. exact (EQ_MP (@lem7540955 c k s) (@lem7540954 c k s h1)). Qed.
Lemma lem7540957 (c : real) (k : real) (s : real) : (term282 c k s) = (term283 c k s).
Proof. exact (@lem1982781 c term251 (term279 k s)). Qed.
Lemma lem7540958 (k : real) (s : real) : (term284 k s) = (term285 k s).
Proof. exact (@lem1982781 (term242 k) term251 s). Qed.
Lemma lem7540959 (s : real) : (term242 s) = (term242 s).
Proof. exact (eq_refl (term242 s)). Qed.
Lemma lem7540960 (k : real) : (term286 k) = (term287 k).
Proof. exact (@lem1982749 term251 term251 k). Qed.
Lemma lem7540962 (x : nat) : (term249 x) = (term250 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7540963 : term251 = term252.
Proof. exact (@lem7540962 term253). Qed.
Lemma lem7540965 (x : nat) : (term249 x) = (term250 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7540966 : term251 = term252.
Proof. exact (@lem7540965 term253). Qed.
Lemma lem7540967 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7540968 : term254 = term255.
Proof. exact (MK_COMB (@lem7540967) (@lem7540966)). Qed.
Lemma lem7540969 : term288 = term289.
Proof. exact (MK_COMB (@lem7540968) (@lem7540963)). Qed.
Lemma lem7540970 : term289 = term290.
Proof. exact (@lem1981613 term251 term251 term259 term259). Qed.
Lemma lem7540972 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7540973 : term262 = term263.
Proof. exact (@lem7540972 term253 term253). Qed.
Lemma lem7540974 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7540975 : term265 = term253.
Proof. exact (EQ_MP (@lem7540974) (@lem940073)). Qed.
Lemma lem7540976 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7540977 : term263 = term259.
Proof. exact (MK_COMB (@lem7540976) (@lem7540975)). Qed.
Lemma lem7540978 : term262 = term259.
Proof. exact (TRANS (@lem7540973) (@lem7540977)). Qed.
Lemma lem7540980 (m : nat) (n : nat) : (term291 m n) = (term261 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7540981 : term288 = term263.
Proof. exact (@lem7540980 term253 term253). Qed.
Lemma lem7540982 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7540983 : term265 = term253.
Proof. exact (EQ_MP (@lem7540982) (@lem940073)). Qed.
Lemma lem7540984 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7540985 : term263 = term259.
Proof. exact (MK_COMB (@lem7540984) (@lem7540983)). Qed.
Lemma lem7540986 : term288 = term259.
Proof. exact (TRANS (@lem7540981) (@lem7540985)). Qed.
Lemma lem7540987 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7540988 : term292 = term293.
Proof. exact (MK_COMB (@lem7540987) (@lem7540986)). Qed.
Lemma lem7540989 : term290 = term294.
Proof. exact (MK_COMB (@lem7540988) (@lem7540978)). Qed.
Lemma lem7540990 : term289 = term294.
Proof. exact (TRANS (@lem7540970) (@lem7540989)). Qed.
Lemma lem7540991 : term288 = term294.
Proof. exact (TRANS (@lem7540969) (@lem7540990)). Qed.
Lemma lem7540993 (x : real) : (term269 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7540994 : term294 = term259.
Proof. exact (@lem7540993 term259). Qed.
Lemma lem7540995 : term288 = term259.
Proof. exact (TRANS (@lem7540991) (@lem7540994)). Qed.
Lemma lem7540996 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7540997 : term295 = term296.
Proof. exact (MK_COMB (@lem7540996) (@lem7540995)). Qed.
Lemma lem7540998 (k : real) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem7540999 (k : real) : (term287 k) = (term297 k).
Proof. exact (MK_COMB (@lem7540997) (@lem7540998 k)). Qed.
Lemma lem7541000 (k : real) : (term286 k) = (term297 k).
Proof. exact (TRANS (@lem7540960 k) (@lem7540999 k)). Qed.
Lemma lem7541001 (k : real) : (term297 k) = k.
Proof. exact (@lem1982709 k). Qed.
Lemma lem7541002 (k : real) : (term286 k) = k.
Proof. exact (TRANS (@lem7541000 k) (@lem7541001 k)). Qed.
Lemma lem7541003 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7541004 (k : real) : (term298 k) = (real_add k).
Proof. exact (MK_COMB (@lem7541003) (@lem7541002 k)). Qed.
Lemma lem7541005 (k : real) (s : real) : (term285 k s) = (term237 k s).
Proof. exact (MK_COMB (@lem7541004 k) (@lem7540959 s)). Qed.
Lemma lem7541006 (k : real) (s : real) : (term284 k s) = (term237 k s).
Proof. exact (TRANS (@lem7540958 k s) (@lem7541005 k s)). Qed.
Lemma lem7541009 (c : real) : (term299 c) = (term299 c).
Proof. exact (eq_refl (term299 c)). Qed.
Lemma lem7541010 (c : real) (k : real) (s : real) : (term283 c k s) = (term300 c k s).
Proof. exact (MK_COMB (@lem7541009 c) (@lem7541006 k s)). Qed.
Lemma lem7541011 (c : real) (k : real) (s : real) : (term282 c k s) = (term300 c k s).
Proof. exact (TRANS (@lem7540957 c k s) (@lem7541010 c k s)). Qed.
Lemma lem7541012 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7541013 (c : real) (k : real) (s : real) : (term363 c k s) = (term364 c k s).
Proof. exact (MK_COMB (@lem7541012) (@lem7541011 c k s)). Qed.
Lemma lem7541014 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7541015 (c : real) (k : real) (s : real) : ((term282 c k s) = term10) = ((term300 c k s) = term10).
Proof. exact (MK_COMB (@lem7541013 c k s) (@lem7541014)). Qed.
Lemma lem7541016 (c : real) (k : real) (s : real) (h1 : term338 c k s) : (term300 c k s) = term10.
Proof. exact (EQ_MP (@lem7541015 c k s) (@lem7540956 c k s h1)). Qed.
Lemma lem7541017 (c : real) (k : real) (s : real) (h1 : term338 c k s) : term365 c k s.
Proof. exact (conj (@lem7541016 c k s h1) (@lem7540949 c k s h1)). Qed.
Lemma lem7541019 (x : real) (y : real) : term366 x y.
Proof. exact (proj1 (@lem1988338 x y)). Qed.
Lemma lem7541020 (c : real) (k : real) (s : real) : term367 c k s.
Proof. exact (@lem7541019 (term300 c k s) (term241 c k s)). Qed.
Lemma lem7541021 (c : real) (k : real) (s : real) (h1 : term338 c k s) : term368 c k s.
Proof. exact (@lem7541020 c k s (@lem7541017 c k s h1)). Qed.
Lemma lem7541022 (c : real) (k : real) (s : real) : (term369 c k s) = (term370 c k s).
Proof. exact (@lem1982753 (term242 c) c (term237 k s) (term279 k s)). Qed.
Lemma lem7541023 (c : real) : (term371 c) = (term372 c).
Proof. exact (@lem1982713 term251 c). Qed.
Lemma lem7541025 (x : nat) : (real_of_num x) = (term247 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7541026 : term259 = term294.
Proof. exact (@lem7541025 term253). Qed.
Lemma lem7541028 (x : nat) : (term249 x) = (term250 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7541029 : term251 = term252.
Proof. exact (@lem7541028 term253). Qed.
Lemma lem7541030 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7541031 : term373 = term374.
Proof. exact (MK_COMB (@lem7541030) (@lem7541029)). Qed.
Lemma lem7541032 : term375 = term376.
Proof. exact (MK_COMB (@lem7541031) (@lem7541026)). Qed.
Lemma lem7541033 : term377.
Proof. exact (@lem1981473 term251 term259 term259 term259 term10 term259). Qed.
Lemma lem7541035 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7541036 : term340 = term346.
Proof. exact (@lem7541035 (NUMERAL 0) term253). Qed.
Lemma lem7541037 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7541038 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7541039 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7541038 h1) (fun h1 : term346 = True => @lem7541037)). Qed.
Lemma lem7541040 : term346 = True.
Proof. exact (EQ_MP (@lem7541039) (@lem7541037)). Qed.
Lemma lem7541041 : term340 = True.
Proof. exact (TRANS (@lem7541036) (@lem7541040)). Qed.
Lemma lem7541042 : True = term340.
Proof. exact (SYM (@lem7541041)). Qed.
Lemma lem7541043 : term340.
Proof. exact (EQ_MP (@lem7541042) (@lem0)). Qed.
Lemma lem7541044 : term378.
Proof. exact (@lem7541033 (@lem7541043)). Qed.
Lemma lem7541046 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7541047 : term340 = term346.
Proof. exact (@lem7541046 (NUMERAL 0) term253). Qed.
Lemma lem7541048 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7541049 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7541050 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7541049 h1) (fun h1 : term346 = True => @lem7541048)). Qed.
Lemma lem7541051 : term346 = True.
Proof. exact (EQ_MP (@lem7541050) (@lem7541048)). Qed.
Lemma lem7541052 : term340 = True.
Proof. exact (TRANS (@lem7541047) (@lem7541051)). Qed.
Lemma lem7541053 : True = term340.
Proof. exact (SYM (@lem7541052)). Qed.
Lemma lem7541054 : term340.
Proof. exact (EQ_MP (@lem7541053) (@lem0)). Qed.
Lemma lem7541055 : term379.
Proof. exact (@lem7541044 (@lem7541054)). Qed.
Lemma lem7541057 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7541058 : term340 = term346.
Proof. exact (@lem7541057 (NUMERAL 0) term253). Qed.
Lemma lem7541059 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7541060 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7541061 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7541060 h1) (fun h1 : term346 = True => @lem7541059)). Qed.
Lemma lem7541062 : term346 = True.
Proof. exact (EQ_MP (@lem7541061) (@lem7541059)). Qed.
Lemma lem7541063 : term340 = True.
Proof. exact (TRANS (@lem7541058) (@lem7541062)). Qed.
Lemma lem7541064 : True = term340.
Proof. exact (SYM (@lem7541063)). Qed.
Lemma lem7541065 : term340.
Proof. exact (EQ_MP (@lem7541064) (@lem0)). Qed.
Lemma lem7541066 : term380.
Proof. exact (@lem7541055 (@lem7541065)). Qed.
Lemma lem7541068 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7541069 : term262 = term263.
Proof. exact (@lem7541068 term253 term253). Qed.
Lemma lem7541070 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7541071 : term265 = term253.
Proof. exact (EQ_MP (@lem7541070) (@lem940073)). Qed.
Lemma lem7541072 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7541073 : term263 = term259.
Proof. exact (MK_COMB (@lem7541072) (@lem7541071)). Qed.
Lemma lem7541074 : term262 = term259.
Proof. exact (TRANS (@lem7541069) (@lem7541073)). Qed.
Lemma lem7541076 (m : nat) (n : nat) : (term381 m n) = (term382 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7541077 : term383 = term384.
Proof. exact (@lem7541076 term253 term253). Qed.
Lemma lem7541078 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7541079 : term265 = term253.
Proof. exact (EQ_MP (@lem7541078) (@lem940073)). Qed.
Lemma lem7541080 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7541081 : term263 = term259.
Proof. exact (MK_COMB (@lem7541080) (@lem7541079)). Qed.
Lemma lem7541082 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7541083 : term384 = term251.
Proof. exact (MK_COMB (@lem7541082) (@lem7541081)). Qed.
Lemma lem7541084 : term383 = term251.
Proof. exact (TRANS (@lem7541077) (@lem7541083)). Qed.
Lemma lem7541085 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7541086 : term385 = term373.
Proof. exact (MK_COMB (@lem7541085) (@lem7541084)). Qed.
Lemma lem7541087 : term386 = term375.
Proof. exact (MK_COMB (@lem7541086) (@lem7541074)). Qed.
Lemma lem7541089 (m : nat) : (term387 m) = term10.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7541090 : term375 = term10.
Proof. exact (@lem7541089 term253). Qed.
Lemma lem7541091 : term386 = term10.
Proof. exact (TRANS (@lem7541087) (@lem7541090)). Qed.
Lemma lem7541092 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7541093 : term388 = term389.
Proof. exact (MK_COMB (@lem7541092) (@lem7541091)). Qed.
Lemma lem7541094 : term259 = term259.
Proof. exact (eq_refl term259). Qed.
Lemma lem7541095 : term390 = term351.
Proof. exact (MK_COMB (@lem7541093) (@lem7541094)). Qed.
Lemma lem7541097 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7541098 : term351 = term10.
Proof. exact (@lem7541097 term253). Qed.
Lemma lem7541099 : term390 = term10.
Proof. exact (TRANS (@lem7541095) (@lem7541098)). Qed.
Lemma lem7541101 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7541102 : term262 = term263.
Proof. exact (@lem7541101 term253 term253). Qed.
Lemma lem7541103 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7541104 : term265 = term253.
Proof. exact (EQ_MP (@lem7541103) (@lem940073)). Qed.
Lemma lem7541105 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7541106 : term263 = term259.
Proof. exact (MK_COMB (@lem7541105) (@lem7541104)). Qed.
Lemma lem7541107 : term262 = term259.
Proof. exact (TRANS (@lem7541102) (@lem7541106)). Qed.
Lemma lem7541108 : term389 = term389.
Proof. exact (eq_refl term389). Qed.
Lemma lem7541109 : term391 = term351.
Proof. exact (MK_COMB (@lem7541108) (@lem7541107)). Qed.
Lemma lem7541111 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7541112 : term351 = term10.
Proof. exact (@lem7541111 term253). Qed.
Lemma lem7541113 : term391 = term10.
Proof. exact (TRANS (@lem7541109) (@lem7541112)). Qed.
Lemma lem7541114 : term10 = term391.
Proof. exact (SYM (@lem7541113)). Qed.
Lemma lem7541115 : term390 = term391.
Proof. exact (TRANS (@lem7541099) (@lem7541114)). Qed.
Lemma lem7541116 : term376 = term248.
Proof. exact (@lem7541066 (@lem7541115)). Qed.
Lemma lem7541117 : term375 = term248.
Proof. exact (TRANS (@lem7541032) (@lem7541116)). Qed.
Lemma lem7541119 (x : real) : (term269 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7541120 : term248 = term10.
Proof. exact (@lem7541119 term10). Qed.
Lemma lem7541121 : term375 = term10.
Proof. exact (TRANS (@lem7541117) (@lem7541120)). Qed.
Lemma lem7541122 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7541123 : term392 = term389.
Proof. exact (MK_COMB (@lem7541122) (@lem7541121)). Qed.
Lemma lem7541124 (c : real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem7541125 (c : real) : (term372 c) = (term393 c).
Proof. exact (MK_COMB (@lem7541123) (@lem7541124 c)). Qed.
Lemma lem7541126 (c : real) : (term371 c) = (term393 c).
Proof. exact (TRANS (@lem7541023 c) (@lem7541125 c)). Qed.
Lemma lem7541127 (c : real) : (term393 c) = term10.
Proof. exact (@lem1982719 c). Qed.
Lemma lem7541128 (c : real) : (term371 c) = term10.
Proof. exact (TRANS (@lem7541126 c) (@lem7541127 c)). Qed.
Lemma lem7541129 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7541130 (c : real) : (term394 c) = term395.
Proof. exact (MK_COMB (@lem7541129) (@lem7541128 c)). Qed.
Lemma lem7541131 (k : real) (s : real) : (term396 k s) = (term397 k s).
Proof. exact (@lem1982753 k (term242 k) (term242 s) s). Qed.
Lemma lem7541132 (k : real) : (term398 k) = (term372 k).
Proof. exact (@lem1982715 term251 k). Qed.
Lemma lem7541134 (x : nat) : (real_of_num x) = (term247 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7541135 : term259 = term294.
Proof. exact (@lem7541134 term253). Qed.
Lemma lem7541137 (x : nat) : (term249 x) = (term250 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7541138 : term251 = term252.
Proof. exact (@lem7541137 term253). Qed.
Lemma lem7541139 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7541140 : term373 = term374.
Proof. exact (MK_COMB (@lem7541139) (@lem7541138)). Qed.
Lemma lem7541141 : term375 = term376.
Proof. exact (MK_COMB (@lem7541140) (@lem7541135)). Qed.
Lemma lem7541142 : term377.
Proof. exact (@lem1981473 term251 term259 term259 term259 term10 term259). Qed.
Lemma lem7541144 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7541145 : term340 = term346.
Proof. exact (@lem7541144 (NUMERAL 0) term253). Qed.
Lemma lem7541146 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7541147 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7541148 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7541147 h1) (fun h1 : term346 = True => @lem7541146)). Qed.
Lemma lem7541149 : term346 = True.
Proof. exact (EQ_MP (@lem7541148) (@lem7541146)). Qed.
Lemma lem7541150 : term340 = True.
Proof. exact (TRANS (@lem7541145) (@lem7541149)). Qed.
Lemma lem7541151 : True = term340.
Proof. exact (SYM (@lem7541150)). Qed.
Lemma lem7541152 : term340.
Proof. exact (EQ_MP (@lem7541151) (@lem0)). Qed.
Lemma lem7541153 : term378.
Proof. exact (@lem7541142 (@lem7541152)). Qed.
Lemma lem7541155 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7541156 : term340 = term346.
Proof. exact (@lem7541155 (NUMERAL 0) term253). Qed.
Lemma lem7541157 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7541158 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7541159 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7541158 h1) (fun h1 : term346 = True => @lem7541157)). Qed.
Lemma lem7541160 : term346 = True.
Proof. exact (EQ_MP (@lem7541159) (@lem7541157)). Qed.
Lemma lem7541161 : term340 = True.
Proof. exact (TRANS (@lem7541156) (@lem7541160)). Qed.
Lemma lem7541162 : True = term340.
Proof. exact (SYM (@lem7541161)). Qed.
Lemma lem7541163 : term340.
Proof. exact (EQ_MP (@lem7541162) (@lem0)). Qed.
Lemma lem7541164 : term379.
Proof. exact (@lem7541153 (@lem7541163)). Qed.
Lemma lem7541166 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7541167 : term340 = term346.
Proof. exact (@lem7541166 (NUMERAL 0) term253). Qed.
Lemma lem7541168 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7541169 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7541170 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7541169 h1) (fun h1 : term346 = True => @lem7541168)). Qed.
Lemma lem7541171 : term346 = True.
Proof. exact (EQ_MP (@lem7541170) (@lem7541168)). Qed.
Lemma lem7541172 : term340 = True.
Proof. exact (TRANS (@lem7541167) (@lem7541171)). Qed.
Lemma lem7541173 : True = term340.
Proof. exact (SYM (@lem7541172)). Qed.
Lemma lem7541174 : term340.
Proof. exact (EQ_MP (@lem7541173) (@lem0)). Qed.
Lemma lem7541175 : term380.
Proof. exact (@lem7541164 (@lem7541174)). Qed.
Lemma lem7541177 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7541178 : term262 = term263.
Proof. exact (@lem7541177 term253 term253). Qed.
Lemma lem7541179 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7541180 : term265 = term253.
Proof. exact (EQ_MP (@lem7541179) (@lem940073)). Qed.
Lemma lem7541181 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7541182 : term263 = term259.
Proof. exact (MK_COMB (@lem7541181) (@lem7541180)). Qed.
Lemma lem7541183 : term262 = term259.
Proof. exact (TRANS (@lem7541178) (@lem7541182)). Qed.
Lemma lem7541185 (m : nat) (n : nat) : (term381 m n) = (term382 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7541186 : term383 = term384.
Proof. exact (@lem7541185 term253 term253). Qed.
Lemma lem7541187 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7541188 : term265 = term253.
Proof. exact (EQ_MP (@lem7541187) (@lem940073)). Qed.
Lemma lem7541189 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7541190 : term263 = term259.
Proof. exact (MK_COMB (@lem7541189) (@lem7541188)). Qed.
Lemma lem7541191 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7541192 : term384 = term251.
Proof. exact (MK_COMB (@lem7541191) (@lem7541190)). Qed.
Lemma lem7541193 : term383 = term251.
Proof. exact (TRANS (@lem7541186) (@lem7541192)). Qed.
Lemma lem7541194 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7541195 : term385 = term373.
Proof. exact (MK_COMB (@lem7541194) (@lem7541193)). Qed.
Lemma lem7541196 : term386 = term375.
Proof. exact (MK_COMB (@lem7541195) (@lem7541183)). Qed.
Lemma lem7541198 (m : nat) : (term387 m) = term10.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7541199 : term375 = term10.
Proof. exact (@lem7541198 term253). Qed.
Lemma lem7541200 : term386 = term10.
Proof. exact (TRANS (@lem7541196) (@lem7541199)). Qed.
Lemma lem7541201 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7541202 : term388 = term389.
Proof. exact (MK_COMB (@lem7541201) (@lem7541200)). Qed.
Lemma lem7541203 : term259 = term259.
Proof. exact (eq_refl term259). Qed.
Lemma lem7541204 : term390 = term351.
Proof. exact (MK_COMB (@lem7541202) (@lem7541203)). Qed.
Lemma lem7541206 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7541207 : term351 = term10.
Proof. exact (@lem7541206 term253). Qed.
Lemma lem7541208 : term390 = term10.
Proof. exact (TRANS (@lem7541204) (@lem7541207)). Qed.
Lemma lem7541210 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7541211 : term262 = term263.
Proof. exact (@lem7541210 term253 term253). Qed.
Lemma lem7541212 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7541213 : term265 = term253.
Proof. exact (EQ_MP (@lem7541212) (@lem940073)). Qed.
Lemma lem7541214 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7541215 : term263 = term259.
Proof. exact (MK_COMB (@lem7541214) (@lem7541213)). Qed.
Lemma lem7541216 : term262 = term259.
Proof. exact (TRANS (@lem7541211) (@lem7541215)). Qed.
Lemma lem7541217 : term389 = term389.
Proof. exact (eq_refl term389). Qed.
Lemma lem7541218 : term391 = term351.
Proof. exact (MK_COMB (@lem7541217) (@lem7541216)). Qed.
Lemma lem7541220 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7541221 : term351 = term10.
Proof. exact (@lem7541220 term253). Qed.
Lemma lem7541222 : term391 = term10.
Proof. exact (TRANS (@lem7541218) (@lem7541221)). Qed.
Lemma lem7541223 : term10 = term391.
Proof. exact (SYM (@lem7541222)). Qed.
Lemma lem7541224 : term390 = term391.
Proof. exact (TRANS (@lem7541208) (@lem7541223)). Qed.
Lemma lem7541225 : term376 = term248.
Proof. exact (@lem7541175 (@lem7541224)). Qed.
Lemma lem7541226 : term375 = term248.
Proof. exact (TRANS (@lem7541141) (@lem7541225)). Qed.
Lemma lem7541228 (x : real) : (term269 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7541229 : term248 = term10.
Proof. exact (@lem7541228 term10). Qed.
Lemma lem7541230 : term375 = term10.
Proof. exact (TRANS (@lem7541226) (@lem7541229)). Qed.
Lemma lem7541231 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7541232 : term392 = term389.
Proof. exact (MK_COMB (@lem7541231) (@lem7541230)). Qed.
Lemma lem7541233 (k : real) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem7541234 (k : real) : (term372 k) = (term393 k).
Proof. exact (MK_COMB (@lem7541232) (@lem7541233 k)). Qed.
Lemma lem7541235 (k : real) : (term398 k) = (term393 k).
Proof. exact (TRANS (@lem7541132 k) (@lem7541234 k)). Qed.
Lemma lem7541236 (k : real) : (term393 k) = term10.
Proof. exact (@lem1982719 k). Qed.
Lemma lem7541237 (k : real) : (term398 k) = term10.
Proof. exact (TRANS (@lem7541235 k) (@lem7541236 k)). Qed.
Lemma lem7541238 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7541239 (k : real) : (term399 k) = term395.
Proof. exact (MK_COMB (@lem7541238) (@lem7541237 k)). Qed.
Lemma lem7541240 (s : real) : (term371 s) = (term372 s).
Proof. exact (@lem1982713 term251 s). Qed.
Lemma lem7541242 (x : nat) : (real_of_num x) = (term247 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7541243 : term259 = term294.
Proof. exact (@lem7541242 term253). Qed.
Lemma lem7541245 (x : nat) : (term249 x) = (term250 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7541246 : term251 = term252.
Proof. exact (@lem7541245 term253). Qed.
Lemma lem7541247 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7541248 : term373 = term374.
Proof. exact (MK_COMB (@lem7541247) (@lem7541246)). Qed.
Lemma lem7541249 : term375 = term376.
Proof. exact (MK_COMB (@lem7541248) (@lem7541243)). Qed.
Lemma lem7541250 : term377.
Proof. exact (@lem1981473 term251 term259 term259 term259 term10 term259). Qed.
Lemma lem7541252 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7541253 : term340 = term346.
Proof. exact (@lem7541252 (NUMERAL 0) term253). Qed.
Lemma lem7541254 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7541255 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7541256 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7541255 h1) (fun h1 : term346 = True => @lem7541254)). Qed.
Lemma lem7541257 : term346 = True.
Proof. exact (EQ_MP (@lem7541256) (@lem7541254)). Qed.
Lemma lem7541258 : term340 = True.
Proof. exact (TRANS (@lem7541253) (@lem7541257)). Qed.
Lemma lem7541259 : True = term340.
Proof. exact (SYM (@lem7541258)). Qed.
Lemma lem7541260 : term340.
Proof. exact (EQ_MP (@lem7541259) (@lem0)). Qed.
Lemma lem7541261 : term378.
Proof. exact (@lem7541250 (@lem7541260)). Qed.
Lemma lem7541263 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7541264 : term340 = term346.
Proof. exact (@lem7541263 (NUMERAL 0) term253). Qed.
Lemma lem7541265 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7541266 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7541267 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7541266 h1) (fun h1 : term346 = True => @lem7541265)). Qed.
Lemma lem7541268 : term346 = True.
Proof. exact (EQ_MP (@lem7541267) (@lem7541265)). Qed.
Lemma lem7541269 : term340 = True.
Proof. exact (TRANS (@lem7541264) (@lem7541268)). Qed.
Lemma lem7541270 : True = term340.
Proof. exact (SYM (@lem7541269)). Qed.
Lemma lem7541271 : term340.
Proof. exact (EQ_MP (@lem7541270) (@lem0)). Qed.
Lemma lem7541272 : term379.
Proof. exact (@lem7541261 (@lem7541271)). Qed.
Lemma lem7541274 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7541275 : term340 = term346.
Proof. exact (@lem7541274 (NUMERAL 0) term253). Qed.
Lemma lem7541276 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7541277 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7541278 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7541277 h1) (fun h1 : term346 = True => @lem7541276)). Qed.
Lemma lem7541279 : term346 = True.
Proof. exact (EQ_MP (@lem7541278) (@lem7541276)). Qed.
Lemma lem7541280 : term340 = True.
Proof. exact (TRANS (@lem7541275) (@lem7541279)). Qed.
Lemma lem7541281 : True = term340.
Proof. exact (SYM (@lem7541280)). Qed.
Lemma lem7541282 : term340.
Proof. exact (EQ_MP (@lem7541281) (@lem0)). Qed.
Lemma lem7541283 : term380.
Proof. exact (@lem7541272 (@lem7541282)). Qed.
Lemma lem7541285 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7541286 : term262 = term263.
Proof. exact (@lem7541285 term253 term253). Qed.
Lemma lem7541287 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7541288 : term265 = term253.
Proof. exact (EQ_MP (@lem7541287) (@lem940073)). Qed.
Lemma lem7541289 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7541290 : term263 = term259.
Proof. exact (MK_COMB (@lem7541289) (@lem7541288)). Qed.
Lemma lem7541291 : term262 = term259.
Proof. exact (TRANS (@lem7541286) (@lem7541290)). Qed.
Lemma lem7541293 (m : nat) (n : nat) : (term381 m n) = (term382 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7541294 : term383 = term384.
Proof. exact (@lem7541293 term253 term253). Qed.
Lemma lem7541295 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7541296 : term265 = term253.
Proof. exact (EQ_MP (@lem7541295) (@lem940073)). Qed.
Lemma lem7541297 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7541298 : term263 = term259.
Proof. exact (MK_COMB (@lem7541297) (@lem7541296)). Qed.
Lemma lem7541299 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7541300 : term384 = term251.
Proof. exact (MK_COMB (@lem7541299) (@lem7541298)). Qed.
Lemma lem7541301 : term383 = term251.
Proof. exact (TRANS (@lem7541294) (@lem7541300)). Qed.
Lemma lem7541302 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7541303 : term385 = term373.
Proof. exact (MK_COMB (@lem7541302) (@lem7541301)). Qed.
Lemma lem7541304 : term386 = term375.
Proof. exact (MK_COMB (@lem7541303) (@lem7541291)). Qed.
Lemma lem7541306 (m : nat) : (term387 m) = term10.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7541307 : term375 = term10.
Proof. exact (@lem7541306 term253). Qed.
Lemma lem7541308 : term386 = term10.
Proof. exact (TRANS (@lem7541304) (@lem7541307)). Qed.
Lemma lem7541309 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7541310 : term388 = term389.
Proof. exact (MK_COMB (@lem7541309) (@lem7541308)). Qed.
Lemma lem7541311 : term259 = term259.
Proof. exact (eq_refl term259). Qed.
Lemma lem7541312 : term390 = term351.
Proof. exact (MK_COMB (@lem7541310) (@lem7541311)). Qed.
Lemma lem7541314 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7541315 : term351 = term10.
Proof. exact (@lem7541314 term253). Qed.
Lemma lem7541316 : term390 = term10.
Proof. exact (TRANS (@lem7541312) (@lem7541315)). Qed.
Lemma lem7541318 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7541319 : term262 = term263.
Proof. exact (@lem7541318 term253 term253). Qed.
Lemma lem7541320 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7541321 : term265 = term253.
Proof. exact (EQ_MP (@lem7541320) (@lem940073)). Qed.
Lemma lem7541322 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7541323 : term263 = term259.
Proof. exact (MK_COMB (@lem7541322) (@lem7541321)). Qed.
Lemma lem7541324 : term262 = term259.
Proof. exact (TRANS (@lem7541319) (@lem7541323)). Qed.
Lemma lem7541325 : term389 = term389.
Proof. exact (eq_refl term389). Qed.
Lemma lem7541326 : term391 = term351.
Proof. exact (MK_COMB (@lem7541325) (@lem7541324)). Qed.
Lemma lem7541328 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7541329 : term351 = term10.
Proof. exact (@lem7541328 term253). Qed.
Lemma lem7541330 : term391 = term10.
Proof. exact (TRANS (@lem7541326) (@lem7541329)). Qed.
Lemma lem7541331 : term10 = term391.
Proof. exact (SYM (@lem7541330)). Qed.
Lemma lem7541332 : term390 = term391.
Proof. exact (TRANS (@lem7541316) (@lem7541331)). Qed.
Lemma lem7541333 : term376 = term248.
Proof. exact (@lem7541283 (@lem7541332)). Qed.
Lemma lem7541334 : term375 = term248.
Proof. exact (TRANS (@lem7541249) (@lem7541333)). Qed.
Lemma lem7541336 (x : real) : (term269 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7541337 : term248 = term10.
Proof. exact (@lem7541336 term10). Qed.
Lemma lem7541338 : term375 = term10.
Proof. exact (TRANS (@lem7541334) (@lem7541337)). Qed.
Lemma lem7541339 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7541340 : term392 = term389.
Proof. exact (MK_COMB (@lem7541339) (@lem7541338)). Qed.
Lemma lem7541341 (s : real) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7541342 (s : real) : (term372 s) = (term393 s).
Proof. exact (MK_COMB (@lem7541340) (@lem7541341 s)). Qed.
Lemma lem7541343 (s : real) : (term371 s) = (term393 s).
Proof. exact (TRANS (@lem7541240 s) (@lem7541342 s)). Qed.
Lemma lem7541344 (s : real) : (term393 s) = term10.
Proof. exact (@lem1982719 s). Qed.
Lemma lem7541345 (s : real) : (term371 s) = term10.
Proof. exact (TRANS (@lem7541343 s) (@lem7541344 s)). Qed.
Lemma lem7541346 (k : real) (s : real) : (term397 k s) = term400.
Proof. exact (MK_COMB (@lem7541239 k) (@lem7541345 s)). Qed.
Lemma lem7541347 (k : real) (s : real) : (term396 k s) = term400.
Proof. exact (TRANS (@lem7541131 k s) (@lem7541346 k s)). Qed.
Lemma lem7541348 : term400 = term10.
Proof. exact (@lem1982721 term10). Qed.
Lemma lem7541349 (k : real) (s : real) : (term396 k s) = term10.
Proof. exact (TRANS (@lem7541347 k s) (@lem7541348)). Qed.
Lemma lem7541350 (c : real) (k : real) (s : real) : (term370 c k s) = term400.
Proof. exact (MK_COMB (@lem7541130 c) (@lem7541349 k s)). Qed.
Lemma lem7541351 (c : real) (k : real) (s : real) : (term369 c k s) = term400.
Proof. exact (TRANS (@lem7541022 c k s) (@lem7541350 c k s)). Qed.
Lemma lem7541352 : term400 = term10.
Proof. exact (@lem1982721 term10). Qed.
Lemma lem7541353 (c : real) (k : real) (s : real) : (term369 c k s) = term10.
Proof. exact (TRANS (@lem7541351 c k s) (@lem7541352)). Qed.
Lemma lem7541354 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7541355 (c : real) (k : real) (s : real) : (term401 c k s) = term402.
Proof. exact (MK_COMB (@lem7541354) (@lem7541353 c k s)). Qed.
Lemma lem7541356 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7541357 (c : real) (k : real) (s : real) : (term368 c k s) = term403.
Proof. exact (MK_COMB (@lem7541355 c k s) (@lem7541356)). Qed.
Lemma lem7541358 (c : real) (k : real) (s : real) (h1 : term338 c k s) : term403.
Proof. exact (EQ_MP (@lem7541357 c k s) (@lem7541021 c k s h1)). Qed.
Lemma lem7541360 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7541361 : term403 = term404.
Proof. exact (@lem7541360 term10 term10). Qed.
Lemma lem7541363 (x : nat) : (real_of_num x) = (term247 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7541364 : term10 = term248.
Proof. exact (@lem7541363 (NUMERAL 0)). Qed.
Lemma lem7541366 (x : nat) : (real_of_num x) = (term247 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7541367 : term10 = term248.
Proof. exact (@lem7541366 (NUMERAL 0)). Qed.
Lemma lem7541368 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7541369 : term341 = term342.
Proof. exact (MK_COMB (@lem7541368) (@lem7541367)). Qed.
Lemma lem7541370 : term404 = term405.
Proof. exact (MK_COMB (@lem7541369) (@lem7541364)). Qed.
Lemma lem7541371 : term406.
Proof. exact (@lem1980255 term10 term259 term10 term259). Qed.
Lemma lem7541373 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7541374 : term340 = term346.
Proof. exact (@lem7541373 (NUMERAL 0) term253). Qed.
Lemma lem7541375 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7541376 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7541377 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7541376 h1) (fun h1 : term346 = True => @lem7541375)). Qed.
Lemma lem7541378 : term346 = True.
Proof. exact (EQ_MP (@lem7541377) (@lem7541375)). Qed.
Lemma lem7541379 : term340 = True.
Proof. exact (TRANS (@lem7541374) (@lem7541378)). Qed.
Lemma lem7541380 : True = term340.
Proof. exact (SYM (@lem7541379)). Qed.
Lemma lem7541381 : term340.
Proof. exact (EQ_MP (@lem7541380) (@lem0)). Qed.
Lemma lem7541382 : term407.
Proof. exact (@lem7541371 (@lem7541381)). Qed.
Lemma lem7541384 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7541385 : term340 = term346.
Proof. exact (@lem7541384 (NUMERAL 0) term253). Qed.
Lemma lem7541386 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7541387 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7541388 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7541387 h1) (fun h1 : term346 = True => @lem7541386)). Qed.
Lemma lem7541389 : term346 = True.
Proof. exact (EQ_MP (@lem7541388) (@lem7541386)). Qed.
Lemma lem7541390 : term340 = True.
Proof. exact (TRANS (@lem7541385) (@lem7541389)). Qed.
Lemma lem7541391 : True = term340.
Proof. exact (SYM (@lem7541390)). Qed.
Lemma lem7541392 : term340.
Proof. exact (EQ_MP (@lem7541391) (@lem0)). Qed.
Lemma lem7541393 : term405 = term408.
Proof. exact (@lem7541382 (@lem7541392)). Qed.
Lemma lem7541395 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7541396 : term351 = term10.
Proof. exact (@lem7541395 term253). Qed.
Lemma lem7541398 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7541399 : term351 = term10.
Proof. exact (@lem7541398 term253). Qed.
Lemma lem7541400 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7541401 : term352 = term341.
Proof. exact (MK_COMB (@lem7541400) (@lem7541399)). Qed.
Lemma lem7541402 : term408 = term404.
Proof. exact (MK_COMB (@lem7541401) (@lem7541396)). Qed.
Lemma lem7541404 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7541405 : term404 = term409.
Proof. exact (@lem7541404 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7541406 : term409 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7541407 : term404 = False.
Proof. exact (TRANS (@lem7541405) (@lem7541406)). Qed.
Lemma lem7541408 : term408 = False.
Proof. exact (TRANS (@lem7541402) (@lem7541407)). Qed.
Lemma lem7541409 : term405 = False.
Proof. exact (TRANS (@lem7541393) (@lem7541408)). Qed.
Lemma lem7541410 : term404 = False.
Proof. exact (TRANS (@lem7541370) (@lem7541409)). Qed.
Lemma lem7541411 : term403 = False.
Proof. exact (TRANS (@lem7541361) (@lem7541410)). Qed.
Lemma lem7541412 (c : real) (k : real) (s : real) (h1 : term338 c k s) : False.
Proof. exact (EQ_MP (@lem7541411) (@lem7541358 c k s h1)). Qed.
Lemma lem7541413 (c : real) (k : real) (s : real) (h1 : term410 c k s) : term410 c k s.
Proof. exact (h1). Qed.
Lemma lem7541414 (c : real) (k : real) (s : real) (h1 : term410 c k s) : term305 c k s.
Proof. exact (proj2 (@lem7541413 c k s h1)). Qed.
Lemma lem7541415 (c : real) (k : real) (s : real) (h1 : term410 c k s) : (term241 c k s) = term10.
Proof. exact (proj1 (@lem7541413 c k s h1)). Qed.
Lemma lem7541417 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7541418 : term339 = term340.
Proof. exact (@lem7541417 term10 term259). Qed.
Lemma lem7541420 (x : nat) : (real_of_num x) = (term247 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7541421 : term259 = term294.
Proof. exact (@lem7541420 term253). Qed.
Lemma lem7541423 (x : nat) : (real_of_num x) = (term247 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7541424 : term10 = term248.
Proof. exact (@lem7541423 (NUMERAL 0)). Qed.
Lemma lem7541425 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7541426 : term341 = term342.
Proof. exact (MK_COMB (@lem7541425) (@lem7541424)). Qed.
Lemma lem7541427 : term340 = term343.
Proof. exact (MK_COMB (@lem7541426) (@lem7541421)). Qed.
Lemma lem7541428 : term344.
Proof. exact (@lem1980255 term10 term259 term259 term259). Qed.
Lemma lem7541430 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7541431 : term340 = term346.
Proof. exact (@lem7541430 (NUMERAL 0) term253). Qed.
Lemma lem7541432 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7541433 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7541434 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7541433 h1) (fun h1 : term346 = True => @lem7541432)). Qed.
Lemma lem7541435 : term346 = True.
Proof. exact (EQ_MP (@lem7541434) (@lem7541432)). Qed.
Lemma lem7541436 : term340 = True.
Proof. exact (TRANS (@lem7541431) (@lem7541435)). Qed.
Lemma lem7541437 : True = term340.
Proof. exact (SYM (@lem7541436)). Qed.
Lemma lem7541438 : term340.
Proof. exact (EQ_MP (@lem7541437) (@lem0)). Qed.
Lemma lem7541439 : term348.
Proof. exact (@lem7541428 (@lem7541438)). Qed.
Lemma lem7541441 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7541442 : term340 = term346.
Proof. exact (@lem7541441 (NUMERAL 0) term253). Qed.
Lemma lem7541443 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7541444 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7541445 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7541444 h1) (fun h1 : term346 = True => @lem7541443)). Qed.
Lemma lem7541446 : term346 = True.
Proof. exact (EQ_MP (@lem7541445) (@lem7541443)). Qed.
Lemma lem7541447 : term340 = True.
Proof. exact (TRANS (@lem7541442) (@lem7541446)). Qed.
Lemma lem7541448 : True = term340.
Proof. exact (SYM (@lem7541447)). Qed.
Lemma lem7541449 : term340.
Proof. exact (EQ_MP (@lem7541448) (@lem0)). Qed.
Lemma lem7541450 : term343 = term349.
Proof. exact (@lem7541439 (@lem7541449)). Qed.
Lemma lem7541452 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7541453 : term262 = term263.
Proof. exact (@lem7541452 term253 term253). Qed.
Lemma lem7541454 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7541455 : term265 = term253.
Proof. exact (EQ_MP (@lem7541454) (@lem940073)). Qed.
Lemma lem7541456 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7541457 : term263 = term259.
Proof. exact (MK_COMB (@lem7541456) (@lem7541455)). Qed.
Lemma lem7541458 : term262 = term259.
Proof. exact (TRANS (@lem7541453) (@lem7541457)). Qed.
Lemma lem7541460 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7541461 : term351 = term10.
Proof. exact (@lem7541460 term253). Qed.
Lemma lem7541462 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7541463 : term352 = term341.
Proof. exact (MK_COMB (@lem7541462) (@lem7541461)). Qed.
Lemma lem7541464 : term349 = term340.
Proof. exact (MK_COMB (@lem7541463) (@lem7541458)). Qed.
Lemma lem7541466 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7541467 : term340 = term346.
Proof. exact (@lem7541466 (NUMERAL 0) term253). Qed.
Lemma lem7541468 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7541469 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7541470 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7541469 h1) (fun h1 : term346 = True => @lem7541468)). Qed.
Lemma lem7541471 : term346 = True.
Proof. exact (EQ_MP (@lem7541470) (@lem7541468)). Qed.
Lemma lem7541472 : term340 = True.
Proof. exact (TRANS (@lem7541467) (@lem7541471)). Qed.
Lemma lem7541473 : term349 = True.
Proof. exact (TRANS (@lem7541464) (@lem7541472)). Qed.
Lemma lem7541474 : term343 = True.
Proof. exact (TRANS (@lem7541450) (@lem7541473)). Qed.
Lemma lem7541475 : term340 = True.
Proof. exact (TRANS (@lem7541427) (@lem7541474)). Qed.
Lemma lem7541476 : term339 = True.
Proof. exact (TRANS (@lem7541418) (@lem7541475)). Qed.
Lemma lem7541477 : True = term339.
Proof. exact (SYM (@lem7541476)). Qed.
Lemma lem7541478 : term339.
Proof. exact (EQ_MP (@lem7541477) (@lem0)). Qed.
Lemma lem7541479 (c : real) (k : real) (s : real) (h1 : term410 c k s) : term411 c k s.
Proof. exact (conj (@lem7541478) (@lem7541414 c k s h1)). Qed.
Lemma lem7541481 (x : real) (y : real) : term354 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem7541482 (c : real) (k : real) (s : real) : term412 c k s.
Proof. exact (@lem7541481 term259 (term300 c k s)). Qed.
Lemma lem7541483 (c : real) (k : real) (s : real) (h1 : term410 c k s) : term413 c k s.
Proof. exact (@lem7541482 c k s (@lem7541479 c k s h1)). Qed.
Lemma lem7541484 (c : real) (k : real) (s : real) : (term414 c k s) = (term300 c k s).
Proof. exact (@lem1982733 (term300 c k s)). Qed.
Lemma lem7541485 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7541486 (c : real) (k : real) (s : real) : (term415 c k s) = (term303 c k s).
Proof. exact (MK_COMB (@lem7541485) (@lem7541484 c k s)). Qed.
Lemma lem7541487 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7541488 (c : real) (k : real) (s : real) : (term413 c k s) = (term305 c k s).
Proof. exact (MK_COMB (@lem7541486 c k s) (@lem7541487)). Qed.
Lemma lem7541489 (c : real) (k : real) (s : real) (h1 : term410 c k s) : term305 c k s.
Proof. exact (EQ_MP (@lem7541488 c k s) (@lem7541483 c k s h1)). Qed.
Lemma lem7541491 (y : real) : term359 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem7541492 (c : real) (k : real) (s : real) : term360 c k s.
Proof. exact (@lem7541491 (term241 c k s)). Qed.
Lemma lem7541493 (c : real) (k : real) (s : real) (h1 : term410 c k s) : term361 c k s.
Proof. exact (@lem7541492 c k s (@lem7541415 c k s h1)). Qed.
Lemma lem7541494 (c : real) (k : real) (s : real) (h1 : term410 c k s) : term416 c k s.
Proof. exact (@lem7541493 c k s h1 term259). Qed.
Lemma lem7541495 (c : real) (k : real) (s : real) : (term416 c k s) = ((term357 c k s) = term10).
Proof. exact (eq_refl (term416 c k s)). Qed.
Lemma lem7541496 (c : real) (k : real) (s : real) (h1 : term410 c k s) : (term357 c k s) = term10.
Proof. exact (EQ_MP (@lem7541495 c k s) (@lem7541494 c k s h1)). Qed.
Lemma lem7541497 (c : real) (k : real) (s : real) : (term357 c k s) = (term241 c k s).
Proof. exact (@lem1982733 (term241 c k s)). Qed.
Lemma lem7541498 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7541499 (c : real) (k : real) (s : real) : (term417 c k s) = (term273 c k s).
Proof. exact (MK_COMB (@lem7541498) (@lem7541497 c k s)). Qed.
Lemma lem7541500 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7541501 (c : real) (k : real) (s : real) : ((term357 c k s) = term10) = ((term241 c k s) = term10).
Proof. exact (MK_COMB (@lem7541499 c k s) (@lem7541500)). Qed.
Lemma lem7541502 (c : real) (k : real) (s : real) (h1 : term410 c k s) : (term241 c k s) = term10.
Proof. exact (EQ_MP (@lem7541501 c k s) (@lem7541496 c k s h1)). Qed.
Lemma lem7541503 (c : real) (k : real) (s : real) (h1 : term410 c k s) : term410 c k s.
Proof. exact (conj (@lem7541502 c k s h1) (@lem7541489 c k s h1)). Qed.
Lemma lem7541505 (x : real) (y : real) : term366 x y.
Proof. exact (proj1 (@lem1988338 x y)). Qed.
Lemma lem7541506 (c : real) (k : real) (s : real) : term418 c k s.
Proof. exact (@lem7541505 (term241 c k s) (term300 c k s)). Qed.
Lemma lem7541507 (c : real) (k : real) (s : real) (h1 : term410 c k s) : term419 c k s.
Proof. exact (@lem7541506 c k s (@lem7541503 c k s h1)). Qed.
Lemma lem7541508 (c : real) (k : real) (s : real) : (term420 c k s) = (term421 c k s).
Proof. exact (@lem1982753 c (term242 c) (term279 k s) (term237 k s)). Qed.
Lemma lem7541509 (c : real) : (term398 c) = (term372 c).
Proof. exact (@lem1982715 term251 c). Qed.
Lemma lem7541511 (x : nat) : (real_of_num x) = (term247 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7541512 : term259 = term294.
Proof. exact (@lem7541511 term253). Qed.
Lemma lem7541514 (x : nat) : (term249 x) = (term250 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7541515 : term251 = term252.
Proof. exact (@lem7541514 term253). Qed.
Lemma lem7541516 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7541517 : term373 = term374.
Proof. exact (MK_COMB (@lem7541516) (@lem7541515)). Qed.
Lemma lem7541518 : term375 = term376.
Proof. exact (MK_COMB (@lem7541517) (@lem7541512)). Qed.
Lemma lem7541519 : term377.
Proof. exact (@lem1981473 term251 term259 term259 term259 term10 term259). Qed.
Lemma lem7541521 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7541522 : term340 = term346.
Proof. exact (@lem7541521 (NUMERAL 0) term253). Qed.
Lemma lem7541523 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7541524 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7541525 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7541524 h1) (fun h1 : term346 = True => @lem7541523)). Qed.
Lemma lem7541526 : term346 = True.
Proof. exact (EQ_MP (@lem7541525) (@lem7541523)). Qed.
Lemma lem7541527 : term340 = True.
Proof. exact (TRANS (@lem7541522) (@lem7541526)). Qed.
Lemma lem7541528 : True = term340.
Proof. exact (SYM (@lem7541527)). Qed.
Lemma lem7541529 : term340.
Proof. exact (EQ_MP (@lem7541528) (@lem0)). Qed.
Lemma lem7541530 : term378.
Proof. exact (@lem7541519 (@lem7541529)). Qed.
Lemma lem7541532 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7541533 : term340 = term346.
Proof. exact (@lem7541532 (NUMERAL 0) term253). Qed.
Lemma lem7541534 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7541535 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7541536 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7541535 h1) (fun h1 : term346 = True => @lem7541534)). Qed.
Lemma lem7541537 : term346 = True.
Proof. exact (EQ_MP (@lem7541536) (@lem7541534)). Qed.
Lemma lem7541538 : term340 = True.
Proof. exact (TRANS (@lem7541533) (@lem7541537)). Qed.
Lemma lem7541539 : True = term340.
Proof. exact (SYM (@lem7541538)). Qed.
Lemma lem7541540 : term340.
Proof. exact (EQ_MP (@lem7541539) (@lem0)). Qed.
Lemma lem7541541 : term379.
Proof. exact (@lem7541530 (@lem7541540)). Qed.
Lemma lem7541543 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7541544 : term340 = term346.
Proof. exact (@lem7541543 (NUMERAL 0) term253). Qed.
Lemma lem7541545 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7541546 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7541547 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7541546 h1) (fun h1 : term346 = True => @lem7541545)). Qed.
Lemma lem7541548 : term346 = True.
Proof. exact (EQ_MP (@lem7541547) (@lem7541545)). Qed.
Lemma lem7541549 : term340 = True.
Proof. exact (TRANS (@lem7541544) (@lem7541548)). Qed.
Lemma lem7541550 : True = term340.
Proof. exact (SYM (@lem7541549)). Qed.
Lemma lem7541551 : term340.
Proof. exact (EQ_MP (@lem7541550) (@lem0)). Qed.
Lemma lem7541552 : term380.
Proof. exact (@lem7541541 (@lem7541551)). Qed.
Lemma lem7541554 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7541555 : term262 = term263.
Proof. exact (@lem7541554 term253 term253). Qed.
Lemma lem7541556 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7541557 : term265 = term253.
Proof. exact (EQ_MP (@lem7541556) (@lem940073)). Qed.
Lemma lem7541558 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7541559 : term263 = term259.
Proof. exact (MK_COMB (@lem7541558) (@lem7541557)). Qed.
Lemma lem7541560 : term262 = term259.
Proof. exact (TRANS (@lem7541555) (@lem7541559)). Qed.
Lemma lem7541562 (m : nat) (n : nat) : (term381 m n) = (term382 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7541563 : term383 = term384.
Proof. exact (@lem7541562 term253 term253). Qed.
Lemma lem7541564 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7541565 : term265 = term253.
Proof. exact (EQ_MP (@lem7541564) (@lem940073)). Qed.
Lemma lem7541566 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7541567 : term263 = term259.
Proof. exact (MK_COMB (@lem7541566) (@lem7541565)). Qed.
Lemma lem7541568 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7541569 : term384 = term251.
Proof. exact (MK_COMB (@lem7541568) (@lem7541567)). Qed.
Lemma lem7541570 : term383 = term251.
Proof. exact (TRANS (@lem7541563) (@lem7541569)). Qed.
Lemma lem7541571 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7541572 : term385 = term373.
Proof. exact (MK_COMB (@lem7541571) (@lem7541570)). Qed.
Lemma lem7541573 : term386 = term375.
Proof. exact (MK_COMB (@lem7541572) (@lem7541560)). Qed.
Lemma lem7541575 (m : nat) : (term387 m) = term10.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7541576 : term375 = term10.
Proof. exact (@lem7541575 term253). Qed.
Lemma lem7541577 : term386 = term10.
Proof. exact (TRANS (@lem7541573) (@lem7541576)). Qed.
Lemma lem7541578 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7541579 : term388 = term389.
Proof. exact (MK_COMB (@lem7541578) (@lem7541577)). Qed.
Lemma lem7541580 : term259 = term259.
Proof. exact (eq_refl term259). Qed.
Lemma lem7541581 : term390 = term351.
Proof. exact (MK_COMB (@lem7541579) (@lem7541580)). Qed.
Lemma lem7541583 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7541584 : term351 = term10.
Proof. exact (@lem7541583 term253). Qed.
Lemma lem7541585 : term390 = term10.
Proof. exact (TRANS (@lem7541581) (@lem7541584)). Qed.
Lemma lem7541587 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7541588 : term262 = term263.
Proof. exact (@lem7541587 term253 term253). Qed.
Lemma lem7541589 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7541590 : term265 = term253.
Proof. exact (EQ_MP (@lem7541589) (@lem940073)). Qed.
Lemma lem7541591 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7541592 : term263 = term259.
Proof. exact (MK_COMB (@lem7541591) (@lem7541590)). Qed.
Lemma lem7541593 : term262 = term259.
Proof. exact (TRANS (@lem7541588) (@lem7541592)). Qed.
Lemma lem7541594 : term389 = term389.
Proof. exact (eq_refl term389). Qed.
Lemma lem7541595 : term391 = term351.
Proof. exact (MK_COMB (@lem7541594) (@lem7541593)). Qed.
Lemma lem7541597 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7541598 : term351 = term10.
Proof. exact (@lem7541597 term253). Qed.
Lemma lem7541599 : term391 = term10.
Proof. exact (TRANS (@lem7541595) (@lem7541598)). Qed.
Lemma lem7541600 : term10 = term391.
Proof. exact (SYM (@lem7541599)). Qed.
Lemma lem7541601 : term390 = term391.
Proof. exact (TRANS (@lem7541585) (@lem7541600)). Qed.
Lemma lem7541602 : term376 = term248.
Proof. exact (@lem7541552 (@lem7541601)). Qed.
Lemma lem7541603 : term375 = term248.
Proof. exact (TRANS (@lem7541518) (@lem7541602)). Qed.
Lemma lem7541605 (x : real) : (term269 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7541606 : term248 = term10.
Proof. exact (@lem7541605 term10). Qed.
Lemma lem7541607 : term375 = term10.
Proof. exact (TRANS (@lem7541603) (@lem7541606)). Qed.
Lemma lem7541608 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7541609 : term392 = term389.
Proof. exact (MK_COMB (@lem7541608) (@lem7541607)). Qed.
Lemma lem7541610 (c : real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem7541611 (c : real) : (term372 c) = (term393 c).
Proof. exact (MK_COMB (@lem7541609) (@lem7541610 c)). Qed.
Lemma lem7541612 (c : real) : (term398 c) = (term393 c).
Proof. exact (TRANS (@lem7541509 c) (@lem7541611 c)). Qed.
Lemma lem7541613 (c : real) : (term393 c) = term10.
Proof. exact (@lem1982719 c). Qed.
Lemma lem7541614 (c : real) : (term398 c) = term10.
Proof. exact (TRANS (@lem7541612 c) (@lem7541613 c)). Qed.
Lemma lem7541615 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7541616 (c : real) : (term399 c) = term395.
Proof. exact (MK_COMB (@lem7541615) (@lem7541614 c)). Qed.
Lemma lem7541617 (k : real) (s : real) : (term422 k s) = (term423 k s).
Proof. exact (@lem1982753 (term242 k) k s (term242 s)). Qed.
Lemma lem7541618 (k : real) : (term371 k) = (term372 k).
Proof. exact (@lem1982713 term251 k). Qed.
Lemma lem7541620 (x : nat) : (real_of_num x) = (term247 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7541621 : term259 = term294.
Proof. exact (@lem7541620 term253). Qed.
Lemma lem7541623 (x : nat) : (term249 x) = (term250 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7541624 : term251 = term252.
Proof. exact (@lem7541623 term253). Qed.
Lemma lem7541625 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7541626 : term373 = term374.
Proof. exact (MK_COMB (@lem7541625) (@lem7541624)). Qed.
Lemma lem7541627 : term375 = term376.
Proof. exact (MK_COMB (@lem7541626) (@lem7541621)). Qed.
Lemma lem7541628 : term377.
Proof. exact (@lem1981473 term251 term259 term259 term259 term10 term259). Qed.
Lemma lem7541630 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7541631 : term340 = term346.
Proof. exact (@lem7541630 (NUMERAL 0) term253). Qed.
Lemma lem7541632 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7541633 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7541634 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7541633 h1) (fun h1 : term346 = True => @lem7541632)). Qed.
Lemma lem7541635 : term346 = True.
Proof. exact (EQ_MP (@lem7541634) (@lem7541632)). Qed.
Lemma lem7541636 : term340 = True.
Proof. exact (TRANS (@lem7541631) (@lem7541635)). Qed.
Lemma lem7541637 : True = term340.
Proof. exact (SYM (@lem7541636)). Qed.
Lemma lem7541638 : term340.
Proof. exact (EQ_MP (@lem7541637) (@lem0)). Qed.
Lemma lem7541639 : term378.
Proof. exact (@lem7541628 (@lem7541638)). Qed.
Lemma lem7541641 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7541642 : term340 = term346.
Proof. exact (@lem7541641 (NUMERAL 0) term253). Qed.
Lemma lem7541643 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7541644 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7541645 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7541644 h1) (fun h1 : term346 = True => @lem7541643)). Qed.
Lemma lem7541646 : term346 = True.
Proof. exact (EQ_MP (@lem7541645) (@lem7541643)). Qed.
Lemma lem7541647 : term340 = True.
Proof. exact (TRANS (@lem7541642) (@lem7541646)). Qed.
Lemma lem7541648 : True = term340.
Proof. exact (SYM (@lem7541647)). Qed.
Lemma lem7541649 : term340.
Proof. exact (EQ_MP (@lem7541648) (@lem0)). Qed.
Lemma lem7541650 : term379.
Proof. exact (@lem7541639 (@lem7541649)). Qed.
Lemma lem7541652 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7541653 : term340 = term346.
Proof. exact (@lem7541652 (NUMERAL 0) term253). Qed.
Lemma lem7541654 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7541655 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7541656 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7541655 h1) (fun h1 : term346 = True => @lem7541654)). Qed.
Lemma lem7541657 : term346 = True.
Proof. exact (EQ_MP (@lem7541656) (@lem7541654)). Qed.
Lemma lem7541658 : term340 = True.
Proof. exact (TRANS (@lem7541653) (@lem7541657)). Qed.
Lemma lem7541659 : True = term340.
Proof. exact (SYM (@lem7541658)). Qed.
Lemma lem7541660 : term340.
Proof. exact (EQ_MP (@lem7541659) (@lem0)). Qed.
Lemma lem7541661 : term380.
Proof. exact (@lem7541650 (@lem7541660)). Qed.
Lemma lem7541663 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7541664 : term262 = term263.
Proof. exact (@lem7541663 term253 term253). Qed.
Lemma lem7541665 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7541666 : term265 = term253.
Proof. exact (EQ_MP (@lem7541665) (@lem940073)). Qed.
Lemma lem7541667 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7541668 : term263 = term259.
Proof. exact (MK_COMB (@lem7541667) (@lem7541666)). Qed.
Lemma lem7541669 : term262 = term259.
Proof. exact (TRANS (@lem7541664) (@lem7541668)). Qed.
Lemma lem7541671 (m : nat) (n : nat) : (term381 m n) = (term382 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7541672 : term383 = term384.
Proof. exact (@lem7541671 term253 term253). Qed.
Lemma lem7541673 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7541674 : term265 = term253.
Proof. exact (EQ_MP (@lem7541673) (@lem940073)). Qed.
Lemma lem7541675 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7541676 : term263 = term259.
Proof. exact (MK_COMB (@lem7541675) (@lem7541674)). Qed.
Lemma lem7541677 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7541678 : term384 = term251.
Proof. exact (MK_COMB (@lem7541677) (@lem7541676)). Qed.
Lemma lem7541679 : term383 = term251.
Proof. exact (TRANS (@lem7541672) (@lem7541678)). Qed.
Lemma lem7541680 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7541681 : term385 = term373.
Proof. exact (MK_COMB (@lem7541680) (@lem7541679)). Qed.
Lemma lem7541682 : term386 = term375.
Proof. exact (MK_COMB (@lem7541681) (@lem7541669)). Qed.
Lemma lem7541684 (m : nat) : (term387 m) = term10.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7541685 : term375 = term10.
Proof. exact (@lem7541684 term253). Qed.
Lemma lem7541686 : term386 = term10.
Proof. exact (TRANS (@lem7541682) (@lem7541685)). Qed.
Lemma lem7541687 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7541688 : term388 = term389.
Proof. exact (MK_COMB (@lem7541687) (@lem7541686)). Qed.
Lemma lem7541689 : term259 = term259.
Proof. exact (eq_refl term259). Qed.
Lemma lem7541690 : term390 = term351.
Proof. exact (MK_COMB (@lem7541688) (@lem7541689)). Qed.
Lemma lem7541692 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7541693 : term351 = term10.
Proof. exact (@lem7541692 term253). Qed.
Lemma lem7541694 : term390 = term10.
Proof. exact (TRANS (@lem7541690) (@lem7541693)). Qed.
Lemma lem7541696 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7541697 : term262 = term263.
Proof. exact (@lem7541696 term253 term253). Qed.
Lemma lem7541698 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7541699 : term265 = term253.
Proof. exact (EQ_MP (@lem7541698) (@lem940073)). Qed.
Lemma lem7541700 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7541701 : term263 = term259.
Proof. exact (MK_COMB (@lem7541700) (@lem7541699)). Qed.
Lemma lem7541702 : term262 = term259.
Proof. exact (TRANS (@lem7541697) (@lem7541701)). Qed.
Lemma lem7541703 : term389 = term389.
Proof. exact (eq_refl term389). Qed.
Lemma lem7541704 : term391 = term351.
Proof. exact (MK_COMB (@lem7541703) (@lem7541702)). Qed.
Lemma lem7541706 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7541707 : term351 = term10.
Proof. exact (@lem7541706 term253). Qed.
Lemma lem7541708 : term391 = term10.
Proof. exact (TRANS (@lem7541704) (@lem7541707)). Qed.
Lemma lem7541709 : term10 = term391.
Proof. exact (SYM (@lem7541708)). Qed.
Lemma lem7541710 : term390 = term391.
Proof. exact (TRANS (@lem7541694) (@lem7541709)). Qed.
Lemma lem7541711 : term376 = term248.
Proof. exact (@lem7541661 (@lem7541710)). Qed.
Lemma lem7541712 : term375 = term248.
Proof. exact (TRANS (@lem7541627) (@lem7541711)). Qed.
Lemma lem7541714 (x : real) : (term269 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7541715 : term248 = term10.
Proof. exact (@lem7541714 term10). Qed.
Lemma lem7541716 : term375 = term10.
Proof. exact (TRANS (@lem7541712) (@lem7541715)). Qed.
Lemma lem7541717 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7541718 : term392 = term389.
Proof. exact (MK_COMB (@lem7541717) (@lem7541716)). Qed.
Lemma lem7541719 (k : real) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem7541720 (k : real) : (term372 k) = (term393 k).
Proof. exact (MK_COMB (@lem7541718) (@lem7541719 k)). Qed.
Lemma lem7541721 (k : real) : (term371 k) = (term393 k).
Proof. exact (TRANS (@lem7541618 k) (@lem7541720 k)). Qed.
Lemma lem7541722 (k : real) : (term393 k) = term10.
Proof. exact (@lem1982719 k). Qed.
Lemma lem7541723 (k : real) : (term371 k) = term10.
Proof. exact (TRANS (@lem7541721 k) (@lem7541722 k)). Qed.
Lemma lem7541724 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7541725 (k : real) : (term394 k) = term395.
Proof. exact (MK_COMB (@lem7541724) (@lem7541723 k)). Qed.
Lemma lem7541726 (s : real) : (term398 s) = (term372 s).
Proof. exact (@lem1982715 term251 s). Qed.
Lemma lem7541728 (x : nat) : (real_of_num x) = (term247 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7541729 : term259 = term294.
Proof. exact (@lem7541728 term253). Qed.
Lemma lem7541731 (x : nat) : (term249 x) = (term250 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7541732 : term251 = term252.
Proof. exact (@lem7541731 term253). Qed.
Lemma lem7541733 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7541734 : term373 = term374.
Proof. exact (MK_COMB (@lem7541733) (@lem7541732)). Qed.
Lemma lem7541735 : term375 = term376.
Proof. exact (MK_COMB (@lem7541734) (@lem7541729)). Qed.
Lemma lem7541736 : term377.
Proof. exact (@lem1981473 term251 term259 term259 term259 term10 term259). Qed.
Lemma lem7541738 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7541739 : term340 = term346.
Proof. exact (@lem7541738 (NUMERAL 0) term253). Qed.
Lemma lem7541740 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7541741 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7541742 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7541741 h1) (fun h1 : term346 = True => @lem7541740)). Qed.
Lemma lem7541743 : term346 = True.
Proof. exact (EQ_MP (@lem7541742) (@lem7541740)). Qed.
Lemma lem7541744 : term340 = True.
Proof. exact (TRANS (@lem7541739) (@lem7541743)). Qed.
Lemma lem7541745 : True = term340.
Proof. exact (SYM (@lem7541744)). Qed.
Lemma lem7541746 : term340.
Proof. exact (EQ_MP (@lem7541745) (@lem0)). Qed.
Lemma lem7541747 : term378.
Proof. exact (@lem7541736 (@lem7541746)). Qed.
Lemma lem7541749 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7541750 : term340 = term346.
Proof. exact (@lem7541749 (NUMERAL 0) term253). Qed.
Lemma lem7541751 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7541752 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7541753 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7541752 h1) (fun h1 : term346 = True => @lem7541751)). Qed.
Lemma lem7541754 : term346 = True.
Proof. exact (EQ_MP (@lem7541753) (@lem7541751)). Qed.
Lemma lem7541755 : term340 = True.
Proof. exact (TRANS (@lem7541750) (@lem7541754)). Qed.
Lemma lem7541756 : True = term340.
Proof. exact (SYM (@lem7541755)). Qed.
Lemma lem7541757 : term340.
Proof. exact (EQ_MP (@lem7541756) (@lem0)). Qed.
Lemma lem7541758 : term379.
Proof. exact (@lem7541747 (@lem7541757)). Qed.
Lemma lem7541760 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7541761 : term340 = term346.
Proof. exact (@lem7541760 (NUMERAL 0) term253). Qed.
Lemma lem7541762 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7541763 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7541764 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7541763 h1) (fun h1 : term346 = True => @lem7541762)). Qed.
Lemma lem7541765 : term346 = True.
Proof. exact (EQ_MP (@lem7541764) (@lem7541762)). Qed.
Lemma lem7541766 : term340 = True.
Proof. exact (TRANS (@lem7541761) (@lem7541765)). Qed.
Lemma lem7541767 : True = term340.
Proof. exact (SYM (@lem7541766)). Qed.
Lemma lem7541768 : term340.
Proof. exact (EQ_MP (@lem7541767) (@lem0)). Qed.
Lemma lem7541769 : term380.
Proof. exact (@lem7541758 (@lem7541768)). Qed.
Lemma lem7541771 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7541772 : term262 = term263.
Proof. exact (@lem7541771 term253 term253). Qed.
Lemma lem7541773 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7541774 : term265 = term253.
Proof. exact (EQ_MP (@lem7541773) (@lem940073)). Qed.
Lemma lem7541775 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7541776 : term263 = term259.
Proof. exact (MK_COMB (@lem7541775) (@lem7541774)). Qed.
Lemma lem7541777 : term262 = term259.
Proof. exact (TRANS (@lem7541772) (@lem7541776)). Qed.
Lemma lem7541779 (m : nat) (n : nat) : (term381 m n) = (term382 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7541780 : term383 = term384.
Proof. exact (@lem7541779 term253 term253). Qed.
Lemma lem7541781 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7541782 : term265 = term253.
Proof. exact (EQ_MP (@lem7541781) (@lem940073)). Qed.
Lemma lem7541783 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7541784 : term263 = term259.
Proof. exact (MK_COMB (@lem7541783) (@lem7541782)). Qed.
Lemma lem7541785 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7541786 : term384 = term251.
Proof. exact (MK_COMB (@lem7541785) (@lem7541784)). Qed.
Lemma lem7541787 : term383 = term251.
Proof. exact (TRANS (@lem7541780) (@lem7541786)). Qed.
Lemma lem7541788 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7541789 : term385 = term373.
Proof. exact (MK_COMB (@lem7541788) (@lem7541787)). Qed.
Lemma lem7541790 : term386 = term375.
Proof. exact (MK_COMB (@lem7541789) (@lem7541777)). Qed.
Lemma lem7541792 (m : nat) : (term387 m) = term10.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7541793 : term375 = term10.
Proof. exact (@lem7541792 term253). Qed.
Lemma lem7541794 : term386 = term10.
Proof. exact (TRANS (@lem7541790) (@lem7541793)). Qed.
Lemma lem7541795 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7541796 : term388 = term389.
Proof. exact (MK_COMB (@lem7541795) (@lem7541794)). Qed.
Lemma lem7541797 : term259 = term259.
Proof. exact (eq_refl term259). Qed.
Lemma lem7541798 : term390 = term351.
Proof. exact (MK_COMB (@lem7541796) (@lem7541797)). Qed.
Lemma lem7541800 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7541801 : term351 = term10.
Proof. exact (@lem7541800 term253). Qed.
Lemma lem7541802 : term390 = term10.
Proof. exact (TRANS (@lem7541798) (@lem7541801)). Qed.
Lemma lem7541804 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7541805 : term262 = term263.
Proof. exact (@lem7541804 term253 term253). Qed.
Lemma lem7541806 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7541807 : term265 = term253.
Proof. exact (EQ_MP (@lem7541806) (@lem940073)). Qed.
Lemma lem7541808 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7541809 : term263 = term259.
Proof. exact (MK_COMB (@lem7541808) (@lem7541807)). Qed.
Lemma lem7541810 : term262 = term259.
Proof. exact (TRANS (@lem7541805) (@lem7541809)). Qed.
Lemma lem7541811 : term389 = term389.
Proof. exact (eq_refl term389). Qed.
Lemma lem7541812 : term391 = term351.
Proof. exact (MK_COMB (@lem7541811) (@lem7541810)). Qed.
Lemma lem7541814 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7541815 : term351 = term10.
Proof. exact (@lem7541814 term253). Qed.
Lemma lem7541816 : term391 = term10.
Proof. exact (TRANS (@lem7541812) (@lem7541815)). Qed.
Lemma lem7541817 : term10 = term391.
Proof. exact (SYM (@lem7541816)). Qed.
Lemma lem7541818 : term390 = term391.
Proof. exact (TRANS (@lem7541802) (@lem7541817)). Qed.
Lemma lem7541819 : term376 = term248.
Proof. exact (@lem7541769 (@lem7541818)). Qed.
Lemma lem7541820 : term375 = term248.
Proof. exact (TRANS (@lem7541735) (@lem7541819)). Qed.
Lemma lem7541822 (x : real) : (term269 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7541823 : term248 = term10.
Proof. exact (@lem7541822 term10). Qed.
Lemma lem7541824 : term375 = term10.
Proof. exact (TRANS (@lem7541820) (@lem7541823)). Qed.
Lemma lem7541825 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7541826 : term392 = term389.
Proof. exact (MK_COMB (@lem7541825) (@lem7541824)). Qed.
Lemma lem7541827 (s : real) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7541828 (s : real) : (term372 s) = (term393 s).
Proof. exact (MK_COMB (@lem7541826) (@lem7541827 s)). Qed.
Lemma lem7541829 (s : real) : (term398 s) = (term393 s).
Proof. exact (TRANS (@lem7541726 s) (@lem7541828 s)). Qed.
Lemma lem7541830 (s : real) : (term393 s) = term10.
Proof. exact (@lem1982719 s). Qed.
Lemma lem7541831 (s : real) : (term398 s) = term10.
Proof. exact (TRANS (@lem7541829 s) (@lem7541830 s)). Qed.
Lemma lem7541832 (k : real) (s : real) : (term423 k s) = term400.
Proof. exact (MK_COMB (@lem7541725 k) (@lem7541831 s)). Qed.
Lemma lem7541833 (k : real) (s : real) : (term422 k s) = term400.
Proof. exact (TRANS (@lem7541617 k s) (@lem7541832 k s)). Qed.
Lemma lem7541834 : term400 = term10.
Proof. exact (@lem1982721 term10). Qed.
Lemma lem7541835 (k : real) (s : real) : (term422 k s) = term10.
Proof. exact (TRANS (@lem7541833 k s) (@lem7541834)). Qed.
Lemma lem7541836 (c : real) (k : real) (s : real) : (term421 c k s) = term400.
Proof. exact (MK_COMB (@lem7541616 c) (@lem7541835 k s)). Qed.
Lemma lem7541837 (c : real) (k : real) (s : real) : (term420 c k s) = term400.
Proof. exact (TRANS (@lem7541508 c k s) (@lem7541836 c k s)). Qed.
Lemma lem7541838 : term400 = term10.
Proof. exact (@lem1982721 term10). Qed.
Lemma lem7541839 (c : real) (k : real) (s : real) : (term420 c k s) = term10.
Proof. exact (TRANS (@lem7541837 c k s) (@lem7541838)). Qed.
Lemma lem7541840 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7541841 (c : real) (k : real) (s : real) : (term424 c k s) = term402.
Proof. exact (MK_COMB (@lem7541840) (@lem7541839 c k s)). Qed.
Lemma lem7541842 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7541843 (c : real) (k : real) (s : real) : (term419 c k s) = term403.
Proof. exact (MK_COMB (@lem7541841 c k s) (@lem7541842)). Qed.
Lemma lem7541844 (c : real) (k : real) (s : real) (h1 : term410 c k s) : term403.
Proof. exact (EQ_MP (@lem7541843 c k s) (@lem7541507 c k s h1)). Qed.
Lemma lem7541846 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7541847 : term403 = term404.
Proof. exact (@lem7541846 term10 term10). Qed.
Lemma lem7541849 (x : nat) : (real_of_num x) = (term247 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7541850 : term10 = term248.
Proof. exact (@lem7541849 (NUMERAL 0)). Qed.
Lemma lem7541852 (x : nat) : (real_of_num x) = (term247 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7541853 : term10 = term248.
Proof. exact (@lem7541852 (NUMERAL 0)). Qed.
Lemma lem7541854 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7541855 : term341 = term342.
Proof. exact (MK_COMB (@lem7541854) (@lem7541853)). Qed.
Lemma lem7541856 : term404 = term405.
Proof. exact (MK_COMB (@lem7541855) (@lem7541850)). Qed.
Lemma lem7541857 : term406.
Proof. exact (@lem1980255 term10 term259 term10 term259). Qed.
Lemma lem7541859 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7541860 : term340 = term346.
Proof. exact (@lem7541859 (NUMERAL 0) term253). Qed.
Lemma lem7541861 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7541862 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7541863 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7541862 h1) (fun h1 : term346 = True => @lem7541861)). Qed.
Lemma lem7541864 : term346 = True.
Proof. exact (EQ_MP (@lem7541863) (@lem7541861)). Qed.
Lemma lem7541865 : term340 = True.
Proof. exact (TRANS (@lem7541860) (@lem7541864)). Qed.
Lemma lem7541866 : True = term340.
Proof. exact (SYM (@lem7541865)). Qed.
Lemma lem7541867 : term340.
Proof. exact (EQ_MP (@lem7541866) (@lem0)). Qed.
Lemma lem7541868 : term407.
Proof. exact (@lem7541857 (@lem7541867)). Qed.
Lemma lem7541870 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7541871 : term340 = term346.
Proof. exact (@lem7541870 (NUMERAL 0) term253). Qed.
Lemma lem7541872 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7541873 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7541874 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7541873 h1) (fun h1 : term346 = True => @lem7541872)). Qed.
Lemma lem7541875 : term346 = True.
Proof. exact (EQ_MP (@lem7541874) (@lem7541872)). Qed.
Lemma lem7541876 : term340 = True.
Proof. exact (TRANS (@lem7541871) (@lem7541875)). Qed.
Lemma lem7541877 : True = term340.
Proof. exact (SYM (@lem7541876)). Qed.
Lemma lem7541878 : term340.
Proof. exact (EQ_MP (@lem7541877) (@lem0)). Qed.
Lemma lem7541879 : term405 = term408.
Proof. exact (@lem7541868 (@lem7541878)). Qed.
Lemma lem7541881 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7541882 : term351 = term10.
Proof. exact (@lem7541881 term253). Qed.
Lemma lem7541884 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7541885 : term351 = term10.
Proof. exact (@lem7541884 term253). Qed.
Lemma lem7541886 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7541887 : term352 = term341.
Proof. exact (MK_COMB (@lem7541886) (@lem7541885)). Qed.
Lemma lem7541888 : term408 = term404.
Proof. exact (MK_COMB (@lem7541887) (@lem7541882)). Qed.
Lemma lem7541890 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7541891 : term404 = term409.
Proof. exact (@lem7541890 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7541892 : term409 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7541893 : term404 = False.
Proof. exact (TRANS (@lem7541891) (@lem7541892)). Qed.
Lemma lem7541894 : term408 = False.
Proof. exact (TRANS (@lem7541888) (@lem7541893)). Qed.
Lemma lem7541895 : term405 = False.
Proof. exact (TRANS (@lem7541879) (@lem7541894)). Qed.
Lemma lem7541896 : term404 = False.
Proof. exact (TRANS (@lem7541856) (@lem7541895)). Qed.
Lemma lem7541897 : term403 = False.
Proof. exact (TRANS (@lem7541847) (@lem7541896)). Qed.
Lemma lem7541898 (c : real) (k : real) (s : real) (h1 : term410 c k s) : False.
Proof. exact (EQ_MP (@lem7541897) (@lem7541844 c k s h1)). Qed.
Lemma lem7541899 (c : real) (k : real) (s : real) (h1 : term335 c k s) : False.
Proof. exact (or_elim (@lem7540872 c k s h1) (fun h0 : term338 c k s => @lem7541412 c k s h0) (fun h0 : term410 c k s => @lem7541898 c k s h0)). Qed.
Lemma lem7541900 (c : real) (k : real) (s : real) (h1 : term334 c k s) : term334 c k s.
Proof. exact (h1). Qed.
Lemma lem7541901 (c : real) (k : real) (s : real) (h1 : term425 c k s) : term425 c k s.
Proof. exact (h1). Qed.
Lemma lem7541902 (c : real) (k : real) (s : real) (h1 : term425 c k s) : (term241 c k s) = term10.
Proof. exact (proj2 (@lem7541901 c k s h1)). Qed.
Lemma lem7541903 (c : real) (k : real) (s : real) (h1 : term425 c k s) : term309 c k s.
Proof. exact (proj1 (@lem7541901 c k s h1)). Qed.
Lemma lem7541905 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7541906 : term339 = term340.
Proof. exact (@lem7541905 term10 term259). Qed.
Lemma lem7541908 (x : nat) : (real_of_num x) = (term247 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7541909 : term259 = term294.
Proof. exact (@lem7541908 term253). Qed.
Lemma lem7541911 (x : nat) : (real_of_num x) = (term247 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7541912 : term10 = term248.
Proof. exact (@lem7541911 (NUMERAL 0)). Qed.
Lemma lem7541913 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7541914 : term341 = term342.
Proof. exact (MK_COMB (@lem7541913) (@lem7541912)). Qed.
Lemma lem7541915 : term340 = term343.
Proof. exact (MK_COMB (@lem7541914) (@lem7541909)). Qed.
Lemma lem7541916 : term344.
Proof. exact (@lem1980255 term10 term259 term259 term259). Qed.
Lemma lem7541918 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7541919 : term340 = term346.
Proof. exact (@lem7541918 (NUMERAL 0) term253). Qed.
Lemma lem7541920 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7541921 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7541922 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7541921 h1) (fun h1 : term346 = True => @lem7541920)). Qed.
Lemma lem7541923 : term346 = True.
Proof. exact (EQ_MP (@lem7541922) (@lem7541920)). Qed.
Lemma lem7541924 : term340 = True.
Proof. exact (TRANS (@lem7541919) (@lem7541923)). Qed.
Lemma lem7541925 : True = term340.
Proof. exact (SYM (@lem7541924)). Qed.
Lemma lem7541926 : term340.
Proof. exact (EQ_MP (@lem7541925) (@lem0)). Qed.
Lemma lem7541927 : term348.
Proof. exact (@lem7541916 (@lem7541926)). Qed.
Lemma lem7541929 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7541930 : term340 = term346.
Proof. exact (@lem7541929 (NUMERAL 0) term253). Qed.
Lemma lem7541931 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7541932 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7541933 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7541932 h1) (fun h1 : term346 = True => @lem7541931)). Qed.
Lemma lem7541934 : term346 = True.
Proof. exact (EQ_MP (@lem7541933) (@lem7541931)). Qed.
Lemma lem7541935 : term340 = True.
Proof. exact (TRANS (@lem7541930) (@lem7541934)). Qed.
Lemma lem7541936 : True = term340.
Proof. exact (SYM (@lem7541935)). Qed.
Lemma lem7541937 : term340.
Proof. exact (EQ_MP (@lem7541936) (@lem0)). Qed.
Lemma lem7541938 : term343 = term349.
Proof. exact (@lem7541927 (@lem7541937)). Qed.
Lemma lem7541940 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7541941 : term262 = term263.
Proof. exact (@lem7541940 term253 term253). Qed.
Lemma lem7541942 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7541943 : term265 = term253.
Proof. exact (EQ_MP (@lem7541942) (@lem940073)). Qed.
Lemma lem7541944 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7541945 : term263 = term259.
Proof. exact (MK_COMB (@lem7541944) (@lem7541943)). Qed.
Lemma lem7541946 : term262 = term259.
Proof. exact (TRANS (@lem7541941) (@lem7541945)). Qed.
Lemma lem7541948 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7541949 : term351 = term10.
Proof. exact (@lem7541948 term253). Qed.
Lemma lem7541950 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7541951 : term352 = term341.
Proof. exact (MK_COMB (@lem7541950) (@lem7541949)). Qed.
Lemma lem7541952 : term349 = term340.
Proof. exact (MK_COMB (@lem7541951) (@lem7541946)). Qed.
Lemma lem7541954 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7541955 : term340 = term346.
Proof. exact (@lem7541954 (NUMERAL 0) term253). Qed.
Lemma lem7541956 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7541957 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7541958 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7541957 h1) (fun h1 : term346 = True => @lem7541956)). Qed.
Lemma lem7541959 : term346 = True.
Proof. exact (EQ_MP (@lem7541958) (@lem7541956)). Qed.
Lemma lem7541960 : term340 = True.
Proof. exact (TRANS (@lem7541955) (@lem7541959)). Qed.
Lemma lem7541961 : term349 = True.
Proof. exact (TRANS (@lem7541952) (@lem7541960)). Qed.
Lemma lem7541962 : term343 = True.
Proof. exact (TRANS (@lem7541938) (@lem7541961)). Qed.
Lemma lem7541963 : term340 = True.
Proof. exact (TRANS (@lem7541915) (@lem7541962)). Qed.
Lemma lem7541964 : term339 = True.
Proof. exact (TRANS (@lem7541906) (@lem7541963)). Qed.
Lemma lem7541965 : True = term339.
Proof. exact (SYM (@lem7541964)). Qed.
Lemma lem7541966 : term339.
Proof. exact (EQ_MP (@lem7541965) (@lem0)). Qed.
Lemma lem7541967 (c : real) (k : real) (s : real) (h1 : term425 c k s) : term353 c k s.
Proof. exact (conj (@lem7541966) (@lem7541903 c k s h1)). Qed.
Lemma lem7541969 (x : real) (y : real) : term354 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem7541970 (c : real) (k : real) (s : real) : term355 c k s.
Proof. exact (@lem7541969 term259 (term241 c k s)). Qed.
Lemma lem7541971 (c : real) (k : real) (s : real) (h1 : term425 c k s) : term356 c k s.
Proof. exact (@lem7541970 c k s (@lem7541967 c k s h1)). Qed.
Lemma lem7541972 (c : real) (k : real) (s : real) : (term357 c k s) = (term241 c k s).
Proof. exact (@lem1982733 (term241 c k s)). Qed.
Lemma lem7541973 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7541974 (c : real) (k : real) (s : real) : (term358 c k s) = (term307 c k s).
Proof. exact (MK_COMB (@lem7541973) (@lem7541972 c k s)). Qed.
Lemma lem7541975 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7541976 (c : real) (k : real) (s : real) : (term356 c k s) = (term309 c k s).
Proof. exact (MK_COMB (@lem7541974 c k s) (@lem7541975)). Qed.
Lemma lem7541977 (c : real) (k : real) (s : real) (h1 : term425 c k s) : term309 c k s.
Proof. exact (EQ_MP (@lem7541976 c k s) (@lem7541971 c k s h1)). Qed.
Lemma lem7541979 (y : real) : term359 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem7541980 (c : real) (k : real) (s : real) : term360 c k s.
Proof. exact (@lem7541979 (term241 c k s)). Qed.
Lemma lem7541981 (c : real) (k : real) (s : real) (h1 : term425 c k s) : term361 c k s.
Proof. exact (@lem7541980 c k s (@lem7541902 c k s h1)). Qed.
Lemma lem7541982 (c : real) (k : real) (s : real) (h1 : term425 c k s) : term362 c k s.
Proof. exact (@lem7541981 c k s h1 term251). Qed.
Lemma lem7541983 (c : real) (k : real) (s : real) : (term362 c k s) = ((term282 c k s) = term10).
Proof. exact (eq_refl (term362 c k s)). Qed.
Lemma lem7541984 (c : real) (k : real) (s : real) (h1 : term425 c k s) : (term282 c k s) = term10.
Proof. exact (EQ_MP (@lem7541983 c k s) (@lem7541982 c k s h1)). Qed.
Lemma lem7541985 (c : real) (k : real) (s : real) : (term282 c k s) = (term283 c k s).
Proof. exact (@lem1982781 c term251 (term279 k s)). Qed.
Lemma lem7541986 (k : real) (s : real) : (term284 k s) = (term285 k s).
Proof. exact (@lem1982781 (term242 k) term251 s). Qed.
Lemma lem7541987 (s : real) : (term242 s) = (term242 s).
Proof. exact (eq_refl (term242 s)). Qed.
Lemma lem7541988 (k : real) : (term286 k) = (term287 k).
Proof. exact (@lem1982749 term251 term251 k). Qed.
Lemma lem7541990 (x : nat) : (term249 x) = (term250 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7541991 : term251 = term252.
Proof. exact (@lem7541990 term253). Qed.
Lemma lem7541993 (x : nat) : (term249 x) = (term250 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7541994 : term251 = term252.
Proof. exact (@lem7541993 term253). Qed.
Lemma lem7541995 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7541996 : term254 = term255.
Proof. exact (MK_COMB (@lem7541995) (@lem7541994)). Qed.
Lemma lem7541997 : term288 = term289.
Proof. exact (MK_COMB (@lem7541996) (@lem7541991)). Qed.
Lemma lem7541998 : term289 = term290.
Proof. exact (@lem1981613 term251 term251 term259 term259). Qed.
Lemma lem7542000 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7542001 : term262 = term263.
Proof. exact (@lem7542000 term253 term253). Qed.
Lemma lem7542002 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7542003 : term265 = term253.
Proof. exact (EQ_MP (@lem7542002) (@lem940073)). Qed.
Lemma lem7542004 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7542005 : term263 = term259.
Proof. exact (MK_COMB (@lem7542004) (@lem7542003)). Qed.
Lemma lem7542006 : term262 = term259.
Proof. exact (TRANS (@lem7542001) (@lem7542005)). Qed.
Lemma lem7542008 (m : nat) (n : nat) : (term291 m n) = (term261 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7542009 : term288 = term263.
Proof. exact (@lem7542008 term253 term253). Qed.
Lemma lem7542010 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7542011 : term265 = term253.
Proof. exact (EQ_MP (@lem7542010) (@lem940073)). Qed.
Lemma lem7542012 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7542013 : term263 = term259.
Proof. exact (MK_COMB (@lem7542012) (@lem7542011)). Qed.
Lemma lem7542014 : term288 = term259.
Proof. exact (TRANS (@lem7542009) (@lem7542013)). Qed.
Lemma lem7542015 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7542016 : term292 = term293.
Proof. exact (MK_COMB (@lem7542015) (@lem7542014)). Qed.
Lemma lem7542017 : term290 = term294.
Proof. exact (MK_COMB (@lem7542016) (@lem7542006)). Qed.
Lemma lem7542018 : term289 = term294.
Proof. exact (TRANS (@lem7541998) (@lem7542017)). Qed.
Lemma lem7542019 : term288 = term294.
Proof. exact (TRANS (@lem7541997) (@lem7542018)). Qed.
Lemma lem7542021 (x : real) : (term269 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7542022 : term294 = term259.
Proof. exact (@lem7542021 term259). Qed.
Lemma lem7542023 : term288 = term259.
Proof. exact (TRANS (@lem7542019) (@lem7542022)). Qed.
Lemma lem7542024 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7542025 : term295 = term296.
Proof. exact (MK_COMB (@lem7542024) (@lem7542023)). Qed.
Lemma lem7542026 (k : real) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem7542027 (k : real) : (term287 k) = (term297 k).
Proof. exact (MK_COMB (@lem7542025) (@lem7542026 k)). Qed.
Lemma lem7542028 (k : real) : (term286 k) = (term297 k).
Proof. exact (TRANS (@lem7541988 k) (@lem7542027 k)). Qed.
Lemma lem7542029 (k : real) : (term297 k) = k.
Proof. exact (@lem1982709 k). Qed.
Lemma lem7542030 (k : real) : (term286 k) = k.
Proof. exact (TRANS (@lem7542028 k) (@lem7542029 k)). Qed.
Lemma lem7542031 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7542032 (k : real) : (term298 k) = (real_add k).
Proof. exact (MK_COMB (@lem7542031) (@lem7542030 k)). Qed.
Lemma lem7542033 (k : real) (s : real) : (term285 k s) = (term237 k s).
Proof. exact (MK_COMB (@lem7542032 k) (@lem7541987 s)). Qed.
Lemma lem7542034 (k : real) (s : real) : (term284 k s) = (term237 k s).
Proof. exact (TRANS (@lem7541986 k s) (@lem7542033 k s)). Qed.
Lemma lem7542037 (c : real) : (term299 c) = (term299 c).
Proof. exact (eq_refl (term299 c)). Qed.
Lemma lem7542038 (c : real) (k : real) (s : real) : (term283 c k s) = (term300 c k s).
Proof. exact (MK_COMB (@lem7542037 c) (@lem7542034 k s)). Qed.
Lemma lem7542039 (c : real) (k : real) (s : real) : (term282 c k s) = (term300 c k s).
Proof. exact (TRANS (@lem7541985 c k s) (@lem7542038 c k s)). Qed.
Lemma lem7542040 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7542041 (c : real) (k : real) (s : real) : (term363 c k s) = (term364 c k s).
Proof. exact (MK_COMB (@lem7542040) (@lem7542039 c k s)). Qed.
Lemma lem7542042 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7542043 (c : real) (k : real) (s : real) : ((term282 c k s) = term10) = ((term300 c k s) = term10).
Proof. exact (MK_COMB (@lem7542041 c k s) (@lem7542042)). Qed.
Lemma lem7542044 (c : real) (k : real) (s : real) (h1 : term425 c k s) : (term300 c k s) = term10.
Proof. exact (EQ_MP (@lem7542043 c k s) (@lem7541984 c k s h1)). Qed.
Lemma lem7542045 (c : real) (k : real) (s : real) (h1 : term425 c k s) : term365 c k s.
Proof. exact (conj (@lem7542044 c k s h1) (@lem7541977 c k s h1)). Qed.
Lemma lem7542047 (x : real) (y : real) : term366 x y.
Proof. exact (proj1 (@lem1988338 x y)). Qed.
Lemma lem7542048 (c : real) (k : real) (s : real) : term367 c k s.
Proof. exact (@lem7542047 (term300 c k s) (term241 c k s)). Qed.
Lemma lem7542049 (c : real) (k : real) (s : real) (h1 : term425 c k s) : term368 c k s.
Proof. exact (@lem7542048 c k s (@lem7542045 c k s h1)). Qed.
Lemma lem7542050 (c : real) (k : real) (s : real) : (term369 c k s) = (term370 c k s).
Proof. exact (@lem1982753 (term242 c) c (term237 k s) (term279 k s)). Qed.
Lemma lem7542051 (c : real) : (term371 c) = (term372 c).
Proof. exact (@lem1982713 term251 c). Qed.
Lemma lem7542053 (x : nat) : (real_of_num x) = (term247 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7542054 : term259 = term294.
Proof. exact (@lem7542053 term253). Qed.
Lemma lem7542056 (x : nat) : (term249 x) = (term250 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7542057 : term251 = term252.
Proof. exact (@lem7542056 term253). Qed.
Lemma lem7542058 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7542059 : term373 = term374.
Proof. exact (MK_COMB (@lem7542058) (@lem7542057)). Qed.
Lemma lem7542060 : term375 = term376.
Proof. exact (MK_COMB (@lem7542059) (@lem7542054)). Qed.
Lemma lem7542061 : term377.
Proof. exact (@lem1981473 term251 term259 term259 term259 term10 term259). Qed.
Lemma lem7542063 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7542064 : term340 = term346.
Proof. exact (@lem7542063 (NUMERAL 0) term253). Qed.
Lemma lem7542065 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7542066 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7542067 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7542066 h1) (fun h1 : term346 = True => @lem7542065)). Qed.
Lemma lem7542068 : term346 = True.
Proof. exact (EQ_MP (@lem7542067) (@lem7542065)). Qed.
Lemma lem7542069 : term340 = True.
Proof. exact (TRANS (@lem7542064) (@lem7542068)). Qed.
Lemma lem7542070 : True = term340.
Proof. exact (SYM (@lem7542069)). Qed.
Lemma lem7542071 : term340.
Proof. exact (EQ_MP (@lem7542070) (@lem0)). Qed.
Lemma lem7542072 : term378.
Proof. exact (@lem7542061 (@lem7542071)). Qed.
Lemma lem7542074 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7542075 : term340 = term346.
Proof. exact (@lem7542074 (NUMERAL 0) term253). Qed.
Lemma lem7542076 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7542077 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7542078 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7542077 h1) (fun h1 : term346 = True => @lem7542076)). Qed.
Lemma lem7542079 : term346 = True.
Proof. exact (EQ_MP (@lem7542078) (@lem7542076)). Qed.
Lemma lem7542080 : term340 = True.
Proof. exact (TRANS (@lem7542075) (@lem7542079)). Qed.
Lemma lem7542081 : True = term340.
Proof. exact (SYM (@lem7542080)). Qed.
Lemma lem7542082 : term340.
Proof. exact (EQ_MP (@lem7542081) (@lem0)). Qed.
Lemma lem7542083 : term379.
Proof. exact (@lem7542072 (@lem7542082)). Qed.
Lemma lem7542085 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7542086 : term340 = term346.
Proof. exact (@lem7542085 (NUMERAL 0) term253). Qed.
Lemma lem7542087 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7542088 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7542089 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7542088 h1) (fun h1 : term346 = True => @lem7542087)). Qed.
Lemma lem7542090 : term346 = True.
Proof. exact (EQ_MP (@lem7542089) (@lem7542087)). Qed.
Lemma lem7542091 : term340 = True.
Proof. exact (TRANS (@lem7542086) (@lem7542090)). Qed.
Lemma lem7542092 : True = term340.
Proof. exact (SYM (@lem7542091)). Qed.
Lemma lem7542093 : term340.
Proof. exact (EQ_MP (@lem7542092) (@lem0)). Qed.
Lemma lem7542094 : term380.
Proof. exact (@lem7542083 (@lem7542093)). Qed.
Lemma lem7542096 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7542097 : term262 = term263.
Proof. exact (@lem7542096 term253 term253). Qed.
Lemma lem7542098 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7542099 : term265 = term253.
Proof. exact (EQ_MP (@lem7542098) (@lem940073)). Qed.
Lemma lem7542100 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7542101 : term263 = term259.
Proof. exact (MK_COMB (@lem7542100) (@lem7542099)). Qed.
Lemma lem7542102 : term262 = term259.
Proof. exact (TRANS (@lem7542097) (@lem7542101)). Qed.
Lemma lem7542104 (m : nat) (n : nat) : (term381 m n) = (term382 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7542105 : term383 = term384.
Proof. exact (@lem7542104 term253 term253). Qed.
Lemma lem7542106 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7542107 : term265 = term253.
Proof. exact (EQ_MP (@lem7542106) (@lem940073)). Qed.
Lemma lem7542108 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7542109 : term263 = term259.
Proof. exact (MK_COMB (@lem7542108) (@lem7542107)). Qed.
Lemma lem7542110 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7542111 : term384 = term251.
Proof. exact (MK_COMB (@lem7542110) (@lem7542109)). Qed.
Lemma lem7542112 : term383 = term251.
Proof. exact (TRANS (@lem7542105) (@lem7542111)). Qed.
Lemma lem7542113 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7542114 : term385 = term373.
Proof. exact (MK_COMB (@lem7542113) (@lem7542112)). Qed.
Lemma lem7542115 : term386 = term375.
Proof. exact (MK_COMB (@lem7542114) (@lem7542102)). Qed.
Lemma lem7542117 (m : nat) : (term387 m) = term10.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7542118 : term375 = term10.
Proof. exact (@lem7542117 term253). Qed.
Lemma lem7542119 : term386 = term10.
Proof. exact (TRANS (@lem7542115) (@lem7542118)). Qed.
Lemma lem7542120 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7542121 : term388 = term389.
Proof. exact (MK_COMB (@lem7542120) (@lem7542119)). Qed.
Lemma lem7542122 : term259 = term259.
Proof. exact (eq_refl term259). Qed.
Lemma lem7542123 : term390 = term351.
Proof. exact (MK_COMB (@lem7542121) (@lem7542122)). Qed.
Lemma lem7542125 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7542126 : term351 = term10.
Proof. exact (@lem7542125 term253). Qed.
Lemma lem7542127 : term390 = term10.
Proof. exact (TRANS (@lem7542123) (@lem7542126)). Qed.
Lemma lem7542129 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7542130 : term262 = term263.
Proof. exact (@lem7542129 term253 term253). Qed.
Lemma lem7542131 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7542132 : term265 = term253.
Proof. exact (EQ_MP (@lem7542131) (@lem940073)). Qed.
Lemma lem7542133 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7542134 : term263 = term259.
Proof. exact (MK_COMB (@lem7542133) (@lem7542132)). Qed.
Lemma lem7542135 : term262 = term259.
Proof. exact (TRANS (@lem7542130) (@lem7542134)). Qed.
Lemma lem7542136 : term389 = term389.
Proof. exact (eq_refl term389). Qed.
Lemma lem7542137 : term391 = term351.
Proof. exact (MK_COMB (@lem7542136) (@lem7542135)). Qed.
Lemma lem7542139 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7542140 : term351 = term10.
Proof. exact (@lem7542139 term253). Qed.
Lemma lem7542141 : term391 = term10.
Proof. exact (TRANS (@lem7542137) (@lem7542140)). Qed.
Lemma lem7542142 : term10 = term391.
Proof. exact (SYM (@lem7542141)). Qed.
Lemma lem7542143 : term390 = term391.
Proof. exact (TRANS (@lem7542127) (@lem7542142)). Qed.
Lemma lem7542144 : term376 = term248.
Proof. exact (@lem7542094 (@lem7542143)). Qed.
Lemma lem7542145 : term375 = term248.
Proof. exact (TRANS (@lem7542060) (@lem7542144)). Qed.
Lemma lem7542147 (x : real) : (term269 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7542148 : term248 = term10.
Proof. exact (@lem7542147 term10). Qed.
Lemma lem7542149 : term375 = term10.
Proof. exact (TRANS (@lem7542145) (@lem7542148)). Qed.
Lemma lem7542150 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7542151 : term392 = term389.
Proof. exact (MK_COMB (@lem7542150) (@lem7542149)). Qed.
Lemma lem7542152 (c : real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem7542153 (c : real) : (term372 c) = (term393 c).
Proof. exact (MK_COMB (@lem7542151) (@lem7542152 c)). Qed.
Lemma lem7542154 (c : real) : (term371 c) = (term393 c).
Proof. exact (TRANS (@lem7542051 c) (@lem7542153 c)). Qed.
Lemma lem7542155 (c : real) : (term393 c) = term10.
Proof. exact (@lem1982719 c). Qed.
Lemma lem7542156 (c : real) : (term371 c) = term10.
Proof. exact (TRANS (@lem7542154 c) (@lem7542155 c)). Qed.
Lemma lem7542157 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7542158 (c : real) : (term394 c) = term395.
Proof. exact (MK_COMB (@lem7542157) (@lem7542156 c)). Qed.
Lemma lem7542159 (k : real) (s : real) : (term396 k s) = (term397 k s).
Proof. exact (@lem1982753 k (term242 k) (term242 s) s). Qed.
Lemma lem7542160 (k : real) : (term398 k) = (term372 k).
Proof. exact (@lem1982715 term251 k). Qed.
Lemma lem7542162 (x : nat) : (real_of_num x) = (term247 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7542163 : term259 = term294.
Proof. exact (@lem7542162 term253). Qed.
Lemma lem7542165 (x : nat) : (term249 x) = (term250 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7542166 : term251 = term252.
Proof. exact (@lem7542165 term253). Qed.
Lemma lem7542167 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7542168 : term373 = term374.
Proof. exact (MK_COMB (@lem7542167) (@lem7542166)). Qed.
Lemma lem7542169 : term375 = term376.
Proof. exact (MK_COMB (@lem7542168) (@lem7542163)). Qed.
Lemma lem7542170 : term377.
Proof. exact (@lem1981473 term251 term259 term259 term259 term10 term259). Qed.
Lemma lem7542172 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7542173 : term340 = term346.
Proof. exact (@lem7542172 (NUMERAL 0) term253). Qed.
Lemma lem7542174 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7542175 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7542176 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7542175 h1) (fun h1 : term346 = True => @lem7542174)). Qed.
Lemma lem7542177 : term346 = True.
Proof. exact (EQ_MP (@lem7542176) (@lem7542174)). Qed.
Lemma lem7542178 : term340 = True.
Proof. exact (TRANS (@lem7542173) (@lem7542177)). Qed.
Lemma lem7542179 : True = term340.
Proof. exact (SYM (@lem7542178)). Qed.
Lemma lem7542180 : term340.
Proof. exact (EQ_MP (@lem7542179) (@lem0)). Qed.
Lemma lem7542181 : term378.
Proof. exact (@lem7542170 (@lem7542180)). Qed.
Lemma lem7542183 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7542184 : term340 = term346.
Proof. exact (@lem7542183 (NUMERAL 0) term253). Qed.
Lemma lem7542185 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7542186 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7542187 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7542186 h1) (fun h1 : term346 = True => @lem7542185)). Qed.
Lemma lem7542188 : term346 = True.
Proof. exact (EQ_MP (@lem7542187) (@lem7542185)). Qed.
Lemma lem7542189 : term340 = True.
Proof. exact (TRANS (@lem7542184) (@lem7542188)). Qed.
Lemma lem7542190 : True = term340.
Proof. exact (SYM (@lem7542189)). Qed.
Lemma lem7542191 : term340.
Proof. exact (EQ_MP (@lem7542190) (@lem0)). Qed.
Lemma lem7542192 : term379.
Proof. exact (@lem7542181 (@lem7542191)). Qed.
Lemma lem7542194 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7542195 : term340 = term346.
Proof. exact (@lem7542194 (NUMERAL 0) term253). Qed.
Lemma lem7542196 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7542197 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7542198 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7542197 h1) (fun h1 : term346 = True => @lem7542196)). Qed.
Lemma lem7542199 : term346 = True.
Proof. exact (EQ_MP (@lem7542198) (@lem7542196)). Qed.
Lemma lem7542200 : term340 = True.
Proof. exact (TRANS (@lem7542195) (@lem7542199)). Qed.
Lemma lem7542201 : True = term340.
Proof. exact (SYM (@lem7542200)). Qed.
Lemma lem7542202 : term340.
Proof. exact (EQ_MP (@lem7542201) (@lem0)). Qed.
Lemma lem7542203 : term380.
Proof. exact (@lem7542192 (@lem7542202)). Qed.
Lemma lem7542205 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7542206 : term262 = term263.
Proof. exact (@lem7542205 term253 term253). Qed.
Lemma lem7542207 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7542208 : term265 = term253.
Proof. exact (EQ_MP (@lem7542207) (@lem940073)). Qed.
Lemma lem7542209 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7542210 : term263 = term259.
Proof. exact (MK_COMB (@lem7542209) (@lem7542208)). Qed.
Lemma lem7542211 : term262 = term259.
Proof. exact (TRANS (@lem7542206) (@lem7542210)). Qed.
Lemma lem7542213 (m : nat) (n : nat) : (term381 m n) = (term382 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7542214 : term383 = term384.
Proof. exact (@lem7542213 term253 term253). Qed.
Lemma lem7542215 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7542216 : term265 = term253.
Proof. exact (EQ_MP (@lem7542215) (@lem940073)). Qed.
Lemma lem7542217 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7542218 : term263 = term259.
Proof. exact (MK_COMB (@lem7542217) (@lem7542216)). Qed.
Lemma lem7542219 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7542220 : term384 = term251.
Proof. exact (MK_COMB (@lem7542219) (@lem7542218)). Qed.
Lemma lem7542221 : term383 = term251.
Proof. exact (TRANS (@lem7542214) (@lem7542220)). Qed.
Lemma lem7542222 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7542223 : term385 = term373.
Proof. exact (MK_COMB (@lem7542222) (@lem7542221)). Qed.
Lemma lem7542224 : term386 = term375.
Proof. exact (MK_COMB (@lem7542223) (@lem7542211)). Qed.
Lemma lem7542226 (m : nat) : (term387 m) = term10.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7542227 : term375 = term10.
Proof. exact (@lem7542226 term253). Qed.
Lemma lem7542228 : term386 = term10.
Proof. exact (TRANS (@lem7542224) (@lem7542227)). Qed.
Lemma lem7542229 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7542230 : term388 = term389.
Proof. exact (MK_COMB (@lem7542229) (@lem7542228)). Qed.
Lemma lem7542231 : term259 = term259.
Proof. exact (eq_refl term259). Qed.
Lemma lem7542232 : term390 = term351.
Proof. exact (MK_COMB (@lem7542230) (@lem7542231)). Qed.
Lemma lem7542234 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7542235 : term351 = term10.
Proof. exact (@lem7542234 term253). Qed.
Lemma lem7542236 : term390 = term10.
Proof. exact (TRANS (@lem7542232) (@lem7542235)). Qed.
Lemma lem7542238 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7542239 : term262 = term263.
Proof. exact (@lem7542238 term253 term253). Qed.
Lemma lem7542240 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7542241 : term265 = term253.
Proof. exact (EQ_MP (@lem7542240) (@lem940073)). Qed.
Lemma lem7542242 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7542243 : term263 = term259.
Proof. exact (MK_COMB (@lem7542242) (@lem7542241)). Qed.
Lemma lem7542244 : term262 = term259.
Proof. exact (TRANS (@lem7542239) (@lem7542243)). Qed.
Lemma lem7542245 : term389 = term389.
Proof. exact (eq_refl term389). Qed.
Lemma lem7542246 : term391 = term351.
Proof. exact (MK_COMB (@lem7542245) (@lem7542244)). Qed.
Lemma lem7542248 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7542249 : term351 = term10.
Proof. exact (@lem7542248 term253). Qed.
Lemma lem7542250 : term391 = term10.
Proof. exact (TRANS (@lem7542246) (@lem7542249)). Qed.
Lemma lem7542251 : term10 = term391.
Proof. exact (SYM (@lem7542250)). Qed.
Lemma lem7542252 : term390 = term391.
Proof. exact (TRANS (@lem7542236) (@lem7542251)). Qed.
Lemma lem7542253 : term376 = term248.
Proof. exact (@lem7542203 (@lem7542252)). Qed.
Lemma lem7542254 : term375 = term248.
Proof. exact (TRANS (@lem7542169) (@lem7542253)). Qed.
Lemma lem7542256 (x : real) : (term269 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7542257 : term248 = term10.
Proof. exact (@lem7542256 term10). Qed.
Lemma lem7542258 : term375 = term10.
Proof. exact (TRANS (@lem7542254) (@lem7542257)). Qed.
Lemma lem7542259 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7542260 : term392 = term389.
Proof. exact (MK_COMB (@lem7542259) (@lem7542258)). Qed.
Lemma lem7542261 (k : real) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem7542262 (k : real) : (term372 k) = (term393 k).
Proof. exact (MK_COMB (@lem7542260) (@lem7542261 k)). Qed.
Lemma lem7542263 (k : real) : (term398 k) = (term393 k).
Proof. exact (TRANS (@lem7542160 k) (@lem7542262 k)). Qed.
Lemma lem7542264 (k : real) : (term393 k) = term10.
Proof. exact (@lem1982719 k). Qed.
Lemma lem7542265 (k : real) : (term398 k) = term10.
Proof. exact (TRANS (@lem7542263 k) (@lem7542264 k)). Qed.
Lemma lem7542266 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7542267 (k : real) : (term399 k) = term395.
Proof. exact (MK_COMB (@lem7542266) (@lem7542265 k)). Qed.
Lemma lem7542268 (s : real) : (term371 s) = (term372 s).
Proof. exact (@lem1982713 term251 s). Qed.
Lemma lem7542270 (x : nat) : (real_of_num x) = (term247 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7542271 : term259 = term294.
Proof. exact (@lem7542270 term253). Qed.
Lemma lem7542273 (x : nat) : (term249 x) = (term250 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7542274 : term251 = term252.
Proof. exact (@lem7542273 term253). Qed.
Lemma lem7542275 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7542276 : term373 = term374.
Proof. exact (MK_COMB (@lem7542275) (@lem7542274)). Qed.
Lemma lem7542277 : term375 = term376.
Proof. exact (MK_COMB (@lem7542276) (@lem7542271)). Qed.
Lemma lem7542278 : term377.
Proof. exact (@lem1981473 term251 term259 term259 term259 term10 term259). Qed.
Lemma lem7542280 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7542281 : term340 = term346.
Proof. exact (@lem7542280 (NUMERAL 0) term253). Qed.
Lemma lem7542282 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7542283 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7542284 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7542283 h1) (fun h1 : term346 = True => @lem7542282)). Qed.
Lemma lem7542285 : term346 = True.
Proof. exact (EQ_MP (@lem7542284) (@lem7542282)). Qed.
Lemma lem7542286 : term340 = True.
Proof. exact (TRANS (@lem7542281) (@lem7542285)). Qed.
Lemma lem7542287 : True = term340.
Proof. exact (SYM (@lem7542286)). Qed.
Lemma lem7542288 : term340.
Proof. exact (EQ_MP (@lem7542287) (@lem0)). Qed.
Lemma lem7542289 : term378.
Proof. exact (@lem7542278 (@lem7542288)). Qed.
Lemma lem7542291 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7542292 : term340 = term346.
Proof. exact (@lem7542291 (NUMERAL 0) term253). Qed.
Lemma lem7542293 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7542294 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7542295 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7542294 h1) (fun h1 : term346 = True => @lem7542293)). Qed.
Lemma lem7542296 : term346 = True.
Proof. exact (EQ_MP (@lem7542295) (@lem7542293)). Qed.
Lemma lem7542297 : term340 = True.
Proof. exact (TRANS (@lem7542292) (@lem7542296)). Qed.
Lemma lem7542298 : True = term340.
Proof. exact (SYM (@lem7542297)). Qed.
Lemma lem7542299 : term340.
Proof. exact (EQ_MP (@lem7542298) (@lem0)). Qed.
Lemma lem7542300 : term379.
Proof. exact (@lem7542289 (@lem7542299)). Qed.
Lemma lem7542302 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7542303 : term340 = term346.
Proof. exact (@lem7542302 (NUMERAL 0) term253). Qed.
Lemma lem7542304 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7542305 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7542306 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7542305 h1) (fun h1 : term346 = True => @lem7542304)). Qed.
Lemma lem7542307 : term346 = True.
Proof. exact (EQ_MP (@lem7542306) (@lem7542304)). Qed.
Lemma lem7542308 : term340 = True.
Proof. exact (TRANS (@lem7542303) (@lem7542307)). Qed.
Lemma lem7542309 : True = term340.
Proof. exact (SYM (@lem7542308)). Qed.
Lemma lem7542310 : term340.
Proof. exact (EQ_MP (@lem7542309) (@lem0)). Qed.
Lemma lem7542311 : term380.
Proof. exact (@lem7542300 (@lem7542310)). Qed.
Lemma lem7542313 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7542314 : term262 = term263.
Proof. exact (@lem7542313 term253 term253). Qed.
Lemma lem7542315 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7542316 : term265 = term253.
Proof. exact (EQ_MP (@lem7542315) (@lem940073)). Qed.
Lemma lem7542317 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7542318 : term263 = term259.
Proof. exact (MK_COMB (@lem7542317) (@lem7542316)). Qed.
Lemma lem7542319 : term262 = term259.
Proof. exact (TRANS (@lem7542314) (@lem7542318)). Qed.
Lemma lem7542321 (m : nat) (n : nat) : (term381 m n) = (term382 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7542322 : term383 = term384.
Proof. exact (@lem7542321 term253 term253). Qed.
Lemma lem7542323 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7542324 : term265 = term253.
Proof. exact (EQ_MP (@lem7542323) (@lem940073)). Qed.
Lemma lem7542325 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7542326 : term263 = term259.
Proof. exact (MK_COMB (@lem7542325) (@lem7542324)). Qed.
Lemma lem7542327 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7542328 : term384 = term251.
Proof. exact (MK_COMB (@lem7542327) (@lem7542326)). Qed.
Lemma lem7542329 : term383 = term251.
Proof. exact (TRANS (@lem7542322) (@lem7542328)). Qed.
Lemma lem7542330 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7542331 : term385 = term373.
Proof. exact (MK_COMB (@lem7542330) (@lem7542329)). Qed.
Lemma lem7542332 : term386 = term375.
Proof. exact (MK_COMB (@lem7542331) (@lem7542319)). Qed.
Lemma lem7542334 (m : nat) : (term387 m) = term10.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7542335 : term375 = term10.
Proof. exact (@lem7542334 term253). Qed.
Lemma lem7542336 : term386 = term10.
Proof. exact (TRANS (@lem7542332) (@lem7542335)). Qed.
Lemma lem7542337 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7542338 : term388 = term389.
Proof. exact (MK_COMB (@lem7542337) (@lem7542336)). Qed.
Lemma lem7542339 : term259 = term259.
Proof. exact (eq_refl term259). Qed.
Lemma lem7542340 : term390 = term351.
Proof. exact (MK_COMB (@lem7542338) (@lem7542339)). Qed.
Lemma lem7542342 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7542343 : term351 = term10.
Proof. exact (@lem7542342 term253). Qed.
Lemma lem7542344 : term390 = term10.
Proof. exact (TRANS (@lem7542340) (@lem7542343)). Qed.
Lemma lem7542346 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7542347 : term262 = term263.
Proof. exact (@lem7542346 term253 term253). Qed.
Lemma lem7542348 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7542349 : term265 = term253.
Proof. exact (EQ_MP (@lem7542348) (@lem940073)). Qed.
Lemma lem7542350 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7542351 : term263 = term259.
Proof. exact (MK_COMB (@lem7542350) (@lem7542349)). Qed.
Lemma lem7542352 : term262 = term259.
Proof. exact (TRANS (@lem7542347) (@lem7542351)). Qed.
Lemma lem7542353 : term389 = term389.
Proof. exact (eq_refl term389). Qed.
Lemma lem7542354 : term391 = term351.
Proof. exact (MK_COMB (@lem7542353) (@lem7542352)). Qed.
Lemma lem7542356 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7542357 : term351 = term10.
Proof. exact (@lem7542356 term253). Qed.
Lemma lem7542358 : term391 = term10.
Proof. exact (TRANS (@lem7542354) (@lem7542357)). Qed.
Lemma lem7542359 : term10 = term391.
Proof. exact (SYM (@lem7542358)). Qed.
Lemma lem7542360 : term390 = term391.
Proof. exact (TRANS (@lem7542344) (@lem7542359)). Qed.
Lemma lem7542361 : term376 = term248.
Proof. exact (@lem7542311 (@lem7542360)). Qed.
Lemma lem7542362 : term375 = term248.
Proof. exact (TRANS (@lem7542277) (@lem7542361)). Qed.
Lemma lem7542364 (x : real) : (term269 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7542365 : term248 = term10.
Proof. exact (@lem7542364 term10). Qed.
Lemma lem7542366 : term375 = term10.
Proof. exact (TRANS (@lem7542362) (@lem7542365)). Qed.
Lemma lem7542367 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7542368 : term392 = term389.
Proof. exact (MK_COMB (@lem7542367) (@lem7542366)). Qed.
Lemma lem7542369 (s : real) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7542370 (s : real) : (term372 s) = (term393 s).
Proof. exact (MK_COMB (@lem7542368) (@lem7542369 s)). Qed.
Lemma lem7542371 (s : real) : (term371 s) = (term393 s).
Proof. exact (TRANS (@lem7542268 s) (@lem7542370 s)). Qed.
Lemma lem7542372 (s : real) : (term393 s) = term10.
Proof. exact (@lem1982719 s). Qed.
Lemma lem7542373 (s : real) : (term371 s) = term10.
Proof. exact (TRANS (@lem7542371 s) (@lem7542372 s)). Qed.
Lemma lem7542374 (k : real) (s : real) : (term397 k s) = term400.
Proof. exact (MK_COMB (@lem7542267 k) (@lem7542373 s)). Qed.
Lemma lem7542375 (k : real) (s : real) : (term396 k s) = term400.
Proof. exact (TRANS (@lem7542159 k s) (@lem7542374 k s)). Qed.
Lemma lem7542376 : term400 = term10.
Proof. exact (@lem1982721 term10). Qed.
Lemma lem7542377 (k : real) (s : real) : (term396 k s) = term10.
Proof. exact (TRANS (@lem7542375 k s) (@lem7542376)). Qed.
Lemma lem7542378 (c : real) (k : real) (s : real) : (term370 c k s) = term400.
Proof. exact (MK_COMB (@lem7542158 c) (@lem7542377 k s)). Qed.
Lemma lem7542379 (c : real) (k : real) (s : real) : (term369 c k s) = term400.
Proof. exact (TRANS (@lem7542050 c k s) (@lem7542378 c k s)). Qed.
Lemma lem7542380 : term400 = term10.
Proof. exact (@lem1982721 term10). Qed.
Lemma lem7542381 (c : real) (k : real) (s : real) : (term369 c k s) = term10.
Proof. exact (TRANS (@lem7542379 c k s) (@lem7542380)). Qed.
Lemma lem7542382 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7542383 (c : real) (k : real) (s : real) : (term401 c k s) = term402.
Proof. exact (MK_COMB (@lem7542382) (@lem7542381 c k s)). Qed.
Lemma lem7542384 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7542385 (c : real) (k : real) (s : real) : (term368 c k s) = term403.
Proof. exact (MK_COMB (@lem7542383 c k s) (@lem7542384)). Qed.
Lemma lem7542386 (c : real) (k : real) (s : real) (h1 : term425 c k s) : term403.
Proof. exact (EQ_MP (@lem7542385 c k s) (@lem7542049 c k s h1)). Qed.
Lemma lem7542388 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7542389 : term403 = term404.
Proof. exact (@lem7542388 term10 term10). Qed.
Lemma lem7542391 (x : nat) : (real_of_num x) = (term247 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7542392 : term10 = term248.
Proof. exact (@lem7542391 (NUMERAL 0)). Qed.
Lemma lem7542394 (x : nat) : (real_of_num x) = (term247 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7542395 : term10 = term248.
Proof. exact (@lem7542394 (NUMERAL 0)). Qed.
Lemma lem7542396 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7542397 : term341 = term342.
Proof. exact (MK_COMB (@lem7542396) (@lem7542395)). Qed.
Lemma lem7542398 : term404 = term405.
Proof. exact (MK_COMB (@lem7542397) (@lem7542392)). Qed.
Lemma lem7542399 : term406.
Proof. exact (@lem1980255 term10 term259 term10 term259). Qed.
Lemma lem7542401 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7542402 : term340 = term346.
Proof. exact (@lem7542401 (NUMERAL 0) term253). Qed.
Lemma lem7542403 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7542404 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7542405 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7542404 h1) (fun h1 : term346 = True => @lem7542403)). Qed.
Lemma lem7542406 : term346 = True.
Proof. exact (EQ_MP (@lem7542405) (@lem7542403)). Qed.
Lemma lem7542407 : term340 = True.
Proof. exact (TRANS (@lem7542402) (@lem7542406)). Qed.
Lemma lem7542408 : True = term340.
Proof. exact (SYM (@lem7542407)). Qed.
Lemma lem7542409 : term340.
Proof. exact (EQ_MP (@lem7542408) (@lem0)). Qed.
Lemma lem7542410 : term407.
Proof. exact (@lem7542399 (@lem7542409)). Qed.
Lemma lem7542412 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7542413 : term340 = term346.
Proof. exact (@lem7542412 (NUMERAL 0) term253). Qed.
Lemma lem7542414 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7542415 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7542416 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7542415 h1) (fun h1 : term346 = True => @lem7542414)). Qed.
Lemma lem7542417 : term346 = True.
Proof. exact (EQ_MP (@lem7542416) (@lem7542414)). Qed.
Lemma lem7542418 : term340 = True.
Proof. exact (TRANS (@lem7542413) (@lem7542417)). Qed.
Lemma lem7542419 : True = term340.
Proof. exact (SYM (@lem7542418)). Qed.
Lemma lem7542420 : term340.
Proof. exact (EQ_MP (@lem7542419) (@lem0)). Qed.
Lemma lem7542421 : term405 = term408.
Proof. exact (@lem7542410 (@lem7542420)). Qed.
Lemma lem7542423 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7542424 : term351 = term10.
Proof. exact (@lem7542423 term253). Qed.
Lemma lem7542426 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7542427 : term351 = term10.
Proof. exact (@lem7542426 term253). Qed.
Lemma lem7542428 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7542429 : term352 = term341.
Proof. exact (MK_COMB (@lem7542428) (@lem7542427)). Qed.
Lemma lem7542430 : term408 = term404.
Proof. exact (MK_COMB (@lem7542429) (@lem7542424)). Qed.
Lemma lem7542432 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7542433 : term404 = term409.
Proof. exact (@lem7542432 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7542434 : term409 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7542435 : term404 = False.
Proof. exact (TRANS (@lem7542433) (@lem7542434)). Qed.
Lemma lem7542436 : term408 = False.
Proof. exact (TRANS (@lem7542430) (@lem7542435)). Qed.
Lemma lem7542437 : term405 = False.
Proof. exact (TRANS (@lem7542421) (@lem7542436)). Qed.
Lemma lem7542438 : term404 = False.
Proof. exact (TRANS (@lem7542398) (@lem7542437)). Qed.
Lemma lem7542439 : term403 = False.
Proof. exact (TRANS (@lem7542389) (@lem7542438)). Qed.
Lemma lem7542440 (c : real) (k : real) (s : real) (h1 : term425 c k s) : False.
Proof. exact (EQ_MP (@lem7542439) (@lem7542386 c k s h1)). Qed.
Lemma lem7542441 (c : real) (k : real) (s : real) (h1 : term426 c k s) : term426 c k s.
Proof. exact (h1). Qed.
Lemma lem7542442 (c : real) (k : real) (s : real) (h1 : term426 c k s) : (term241 c k s) = term10.
Proof. exact (proj2 (@lem7542441 c k s h1)). Qed.
Lemma lem7542443 (c : real) (k : real) (s : real) (h1 : term426 c k s) : term305 c k s.
Proof. exact (proj1 (@lem7542441 c k s h1)). Qed.
Lemma lem7542445 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7542446 : term339 = term340.
Proof. exact (@lem7542445 term10 term259). Qed.
Lemma lem7542448 (x : nat) : (real_of_num x) = (term247 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7542449 : term259 = term294.
Proof. exact (@lem7542448 term253). Qed.
Lemma lem7542451 (x : nat) : (real_of_num x) = (term247 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7542452 : term10 = term248.
Proof. exact (@lem7542451 (NUMERAL 0)). Qed.
Lemma lem7542453 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7542454 : term341 = term342.
Proof. exact (MK_COMB (@lem7542453) (@lem7542452)). Qed.
Lemma lem7542455 : term340 = term343.
Proof. exact (MK_COMB (@lem7542454) (@lem7542449)). Qed.
Lemma lem7542456 : term344.
Proof. exact (@lem1980255 term10 term259 term259 term259). Qed.
Lemma lem7542458 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7542459 : term340 = term346.
Proof. exact (@lem7542458 (NUMERAL 0) term253). Qed.
Lemma lem7542460 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7542461 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7542462 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7542461 h1) (fun h1 : term346 = True => @lem7542460)). Qed.
Lemma lem7542463 : term346 = True.
Proof. exact (EQ_MP (@lem7542462) (@lem7542460)). Qed.
Lemma lem7542464 : term340 = True.
Proof. exact (TRANS (@lem7542459) (@lem7542463)). Qed.
Lemma lem7542465 : True = term340.
Proof. exact (SYM (@lem7542464)). Qed.
Lemma lem7542466 : term340.
Proof. exact (EQ_MP (@lem7542465) (@lem0)). Qed.
Lemma lem7542467 : term348.
Proof. exact (@lem7542456 (@lem7542466)). Qed.
Lemma lem7542469 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7542470 : term340 = term346.
Proof. exact (@lem7542469 (NUMERAL 0) term253). Qed.
Lemma lem7542471 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7542472 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7542473 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7542472 h1) (fun h1 : term346 = True => @lem7542471)). Qed.
Lemma lem7542474 : term346 = True.
Proof. exact (EQ_MP (@lem7542473) (@lem7542471)). Qed.
Lemma lem7542475 : term340 = True.
Proof. exact (TRANS (@lem7542470) (@lem7542474)). Qed.
Lemma lem7542476 : True = term340.
Proof. exact (SYM (@lem7542475)). Qed.
Lemma lem7542477 : term340.
Proof. exact (EQ_MP (@lem7542476) (@lem0)). Qed.
Lemma lem7542478 : term343 = term349.
Proof. exact (@lem7542467 (@lem7542477)). Qed.
Lemma lem7542480 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7542481 : term262 = term263.
Proof. exact (@lem7542480 term253 term253). Qed.
Lemma lem7542482 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7542483 : term265 = term253.
Proof. exact (EQ_MP (@lem7542482) (@lem940073)). Qed.
Lemma lem7542484 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7542485 : term263 = term259.
Proof. exact (MK_COMB (@lem7542484) (@lem7542483)). Qed.
Lemma lem7542486 : term262 = term259.
Proof. exact (TRANS (@lem7542481) (@lem7542485)). Qed.
Lemma lem7542488 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7542489 : term351 = term10.
Proof. exact (@lem7542488 term253). Qed.
Lemma lem7542490 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7542491 : term352 = term341.
Proof. exact (MK_COMB (@lem7542490) (@lem7542489)). Qed.
Lemma lem7542492 : term349 = term340.
Proof. exact (MK_COMB (@lem7542491) (@lem7542486)). Qed.
Lemma lem7542494 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7542495 : term340 = term346.
Proof. exact (@lem7542494 (NUMERAL 0) term253). Qed.
Lemma lem7542496 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7542497 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7542498 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7542497 h1) (fun h1 : term346 = True => @lem7542496)). Qed.
Lemma lem7542499 : term346 = True.
Proof. exact (EQ_MP (@lem7542498) (@lem7542496)). Qed.
Lemma lem7542500 : term340 = True.
Proof. exact (TRANS (@lem7542495) (@lem7542499)). Qed.
Lemma lem7542501 : term349 = True.
Proof. exact (TRANS (@lem7542492) (@lem7542500)). Qed.
Lemma lem7542502 : term343 = True.
Proof. exact (TRANS (@lem7542478) (@lem7542501)). Qed.
Lemma lem7542503 : term340 = True.
Proof. exact (TRANS (@lem7542455) (@lem7542502)). Qed.
Lemma lem7542504 : term339 = True.
Proof. exact (TRANS (@lem7542446) (@lem7542503)). Qed.
Lemma lem7542505 : True = term339.
Proof. exact (SYM (@lem7542504)). Qed.
Lemma lem7542506 : term339.
Proof. exact (EQ_MP (@lem7542505) (@lem0)). Qed.
Lemma lem7542507 (c : real) (k : real) (s : real) (h1 : term426 c k s) : term411 c k s.
Proof. exact (conj (@lem7542506) (@lem7542443 c k s h1)). Qed.
Lemma lem7542509 (x : real) (y : real) : term354 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem7542510 (c : real) (k : real) (s : real) : term412 c k s.
Proof. exact (@lem7542509 term259 (term300 c k s)). Qed.
Lemma lem7542511 (c : real) (k : real) (s : real) (h1 : term426 c k s) : term413 c k s.
Proof. exact (@lem7542510 c k s (@lem7542507 c k s h1)). Qed.
Lemma lem7542512 (c : real) (k : real) (s : real) : (term414 c k s) = (term300 c k s).
Proof. exact (@lem1982733 (term300 c k s)). Qed.
Lemma lem7542513 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7542514 (c : real) (k : real) (s : real) : (term415 c k s) = (term303 c k s).
Proof. exact (MK_COMB (@lem7542513) (@lem7542512 c k s)). Qed.
Lemma lem7542515 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7542516 (c : real) (k : real) (s : real) : (term413 c k s) = (term305 c k s).
Proof. exact (MK_COMB (@lem7542514 c k s) (@lem7542515)). Qed.
Lemma lem7542517 (c : real) (k : real) (s : real) (h1 : term426 c k s) : term305 c k s.
Proof. exact (EQ_MP (@lem7542516 c k s) (@lem7542511 c k s h1)). Qed.
Lemma lem7542519 (y : real) : term359 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem7542520 (c : real) (k : real) (s : real) : term360 c k s.
Proof. exact (@lem7542519 (term241 c k s)). Qed.
Lemma lem7542521 (c : real) (k : real) (s : real) (h1 : term426 c k s) : term361 c k s.
Proof. exact (@lem7542520 c k s (@lem7542442 c k s h1)). Qed.
Lemma lem7542522 (c : real) (k : real) (s : real) (h1 : term426 c k s) : term416 c k s.
Proof. exact (@lem7542521 c k s h1 term259). Qed.
Lemma lem7542523 (c : real) (k : real) (s : real) : (term416 c k s) = ((term357 c k s) = term10).
Proof. exact (eq_refl (term416 c k s)). Qed.
Lemma lem7542524 (c : real) (k : real) (s : real) (h1 : term426 c k s) : (term357 c k s) = term10.
Proof. exact (EQ_MP (@lem7542523 c k s) (@lem7542522 c k s h1)). Qed.
Lemma lem7542525 (c : real) (k : real) (s : real) : (term357 c k s) = (term241 c k s).
Proof. exact (@lem1982733 (term241 c k s)). Qed.
Lemma lem7542526 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7542527 (c : real) (k : real) (s : real) : (term417 c k s) = (term273 c k s).
Proof. exact (MK_COMB (@lem7542526) (@lem7542525 c k s)). Qed.
Lemma lem7542528 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7542529 (c : real) (k : real) (s : real) : ((term357 c k s) = term10) = ((term241 c k s) = term10).
Proof. exact (MK_COMB (@lem7542527 c k s) (@lem7542528)). Qed.
Lemma lem7542530 (c : real) (k : real) (s : real) (h1 : term426 c k s) : (term241 c k s) = term10.
Proof. exact (EQ_MP (@lem7542529 c k s) (@lem7542524 c k s h1)). Qed.
Lemma lem7542531 (c : real) (k : real) (s : real) (h1 : term426 c k s) : term410 c k s.
Proof. exact (conj (@lem7542530 c k s h1) (@lem7542517 c k s h1)). Qed.
Lemma lem7542533 (x : real) (y : real) : term366 x y.
Proof. exact (proj1 (@lem1988338 x y)). Qed.
Lemma lem7542534 (c : real) (k : real) (s : real) : term418 c k s.
Proof. exact (@lem7542533 (term241 c k s) (term300 c k s)). Qed.
Lemma lem7542535 (c : real) (k : real) (s : real) (h1 : term426 c k s) : term419 c k s.
Proof. exact (@lem7542534 c k s (@lem7542531 c k s h1)). Qed.
Lemma lem7542536 (c : real) (k : real) (s : real) : (term420 c k s) = (term421 c k s).
Proof. exact (@lem1982753 c (term242 c) (term279 k s) (term237 k s)). Qed.
Lemma lem7542537 (c : real) : (term398 c) = (term372 c).
Proof. exact (@lem1982715 term251 c). Qed.
Lemma lem7542539 (x : nat) : (real_of_num x) = (term247 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7542540 : term259 = term294.
Proof. exact (@lem7542539 term253). Qed.
Lemma lem7542542 (x : nat) : (term249 x) = (term250 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7542543 : term251 = term252.
Proof. exact (@lem7542542 term253). Qed.
Lemma lem7542544 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7542545 : term373 = term374.
Proof. exact (MK_COMB (@lem7542544) (@lem7542543)). Qed.
Lemma lem7542546 : term375 = term376.
Proof. exact (MK_COMB (@lem7542545) (@lem7542540)). Qed.
Lemma lem7542547 : term377.
Proof. exact (@lem1981473 term251 term259 term259 term259 term10 term259). Qed.
Lemma lem7542549 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7542550 : term340 = term346.
Proof. exact (@lem7542549 (NUMERAL 0) term253). Qed.
Lemma lem7542551 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7542552 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7542553 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7542552 h1) (fun h1 : term346 = True => @lem7542551)). Qed.
Lemma lem7542554 : term346 = True.
Proof. exact (EQ_MP (@lem7542553) (@lem7542551)). Qed.
Lemma lem7542555 : term340 = True.
Proof. exact (TRANS (@lem7542550) (@lem7542554)). Qed.
Lemma lem7542556 : True = term340.
Proof. exact (SYM (@lem7542555)). Qed.
Lemma lem7542557 : term340.
Proof. exact (EQ_MP (@lem7542556) (@lem0)). Qed.
Lemma lem7542558 : term378.
Proof. exact (@lem7542547 (@lem7542557)). Qed.
Lemma lem7542560 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7542561 : term340 = term346.
Proof. exact (@lem7542560 (NUMERAL 0) term253). Qed.
Lemma lem7542562 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7542563 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7542564 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7542563 h1) (fun h1 : term346 = True => @lem7542562)). Qed.
Lemma lem7542565 : term346 = True.
Proof. exact (EQ_MP (@lem7542564) (@lem7542562)). Qed.
Lemma lem7542566 : term340 = True.
Proof. exact (TRANS (@lem7542561) (@lem7542565)). Qed.
Lemma lem7542567 : True = term340.
Proof. exact (SYM (@lem7542566)). Qed.
Lemma lem7542568 : term340.
Proof. exact (EQ_MP (@lem7542567) (@lem0)). Qed.
Lemma lem7542569 : term379.
Proof. exact (@lem7542558 (@lem7542568)). Qed.
Lemma lem7542571 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7542572 : term340 = term346.
Proof. exact (@lem7542571 (NUMERAL 0) term253). Qed.
Lemma lem7542573 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7542574 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7542575 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7542574 h1) (fun h1 : term346 = True => @lem7542573)). Qed.
Lemma lem7542576 : term346 = True.
Proof. exact (EQ_MP (@lem7542575) (@lem7542573)). Qed.
Lemma lem7542577 : term340 = True.
Proof. exact (TRANS (@lem7542572) (@lem7542576)). Qed.
Lemma lem7542578 : True = term340.
Proof. exact (SYM (@lem7542577)). Qed.
Lemma lem7542579 : term340.
Proof. exact (EQ_MP (@lem7542578) (@lem0)). Qed.
Lemma lem7542580 : term380.
Proof. exact (@lem7542569 (@lem7542579)). Qed.
Lemma lem7542582 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7542583 : term262 = term263.
Proof. exact (@lem7542582 term253 term253). Qed.
Lemma lem7542584 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7542585 : term265 = term253.
Proof. exact (EQ_MP (@lem7542584) (@lem940073)). Qed.
Lemma lem7542586 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7542587 : term263 = term259.
Proof. exact (MK_COMB (@lem7542586) (@lem7542585)). Qed.
Lemma lem7542588 : term262 = term259.
Proof. exact (TRANS (@lem7542583) (@lem7542587)). Qed.
Lemma lem7542590 (m : nat) (n : nat) : (term381 m n) = (term382 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7542591 : term383 = term384.
Proof. exact (@lem7542590 term253 term253). Qed.
Lemma lem7542592 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7542593 : term265 = term253.
Proof. exact (EQ_MP (@lem7542592) (@lem940073)). Qed.
Lemma lem7542594 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7542595 : term263 = term259.
Proof. exact (MK_COMB (@lem7542594) (@lem7542593)). Qed.
Lemma lem7542596 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7542597 : term384 = term251.
Proof. exact (MK_COMB (@lem7542596) (@lem7542595)). Qed.
Lemma lem7542598 : term383 = term251.
Proof. exact (TRANS (@lem7542591) (@lem7542597)). Qed.
Lemma lem7542599 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7542600 : term385 = term373.
Proof. exact (MK_COMB (@lem7542599) (@lem7542598)). Qed.
Lemma lem7542601 : term386 = term375.
Proof. exact (MK_COMB (@lem7542600) (@lem7542588)). Qed.
Lemma lem7542603 (m : nat) : (term387 m) = term10.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7542604 : term375 = term10.
Proof. exact (@lem7542603 term253). Qed.
Lemma lem7542605 : term386 = term10.
Proof. exact (TRANS (@lem7542601) (@lem7542604)). Qed.
Lemma lem7542606 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7542607 : term388 = term389.
Proof. exact (MK_COMB (@lem7542606) (@lem7542605)). Qed.
Lemma lem7542608 : term259 = term259.
Proof. exact (eq_refl term259). Qed.
Lemma lem7542609 : term390 = term351.
Proof. exact (MK_COMB (@lem7542607) (@lem7542608)). Qed.
Lemma lem7542611 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7542612 : term351 = term10.
Proof. exact (@lem7542611 term253). Qed.
Lemma lem7542613 : term390 = term10.
Proof. exact (TRANS (@lem7542609) (@lem7542612)). Qed.
Lemma lem7542615 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7542616 : term262 = term263.
Proof. exact (@lem7542615 term253 term253). Qed.
Lemma lem7542617 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7542618 : term265 = term253.
Proof. exact (EQ_MP (@lem7542617) (@lem940073)). Qed.
Lemma lem7542619 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7542620 : term263 = term259.
Proof. exact (MK_COMB (@lem7542619) (@lem7542618)). Qed.
Lemma lem7542621 : term262 = term259.
Proof. exact (TRANS (@lem7542616) (@lem7542620)). Qed.
Lemma lem7542622 : term389 = term389.
Proof. exact (eq_refl term389). Qed.
Lemma lem7542623 : term391 = term351.
Proof. exact (MK_COMB (@lem7542622) (@lem7542621)). Qed.
Lemma lem7542625 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7542626 : term351 = term10.
Proof. exact (@lem7542625 term253). Qed.
Lemma lem7542627 : term391 = term10.
Proof. exact (TRANS (@lem7542623) (@lem7542626)). Qed.
Lemma lem7542628 : term10 = term391.
Proof. exact (SYM (@lem7542627)). Qed.
Lemma lem7542629 : term390 = term391.
Proof. exact (TRANS (@lem7542613) (@lem7542628)). Qed.
Lemma lem7542630 : term376 = term248.
Proof. exact (@lem7542580 (@lem7542629)). Qed.
Lemma lem7542631 : term375 = term248.
Proof. exact (TRANS (@lem7542546) (@lem7542630)). Qed.
Lemma lem7542633 (x : real) : (term269 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7542634 : term248 = term10.
Proof. exact (@lem7542633 term10). Qed.
Lemma lem7542635 : term375 = term10.
Proof. exact (TRANS (@lem7542631) (@lem7542634)). Qed.
Lemma lem7542636 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7542637 : term392 = term389.
Proof. exact (MK_COMB (@lem7542636) (@lem7542635)). Qed.
Lemma lem7542638 (c : real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem7542639 (c : real) : (term372 c) = (term393 c).
Proof. exact (MK_COMB (@lem7542637) (@lem7542638 c)). Qed.
Lemma lem7542640 (c : real) : (term398 c) = (term393 c).
Proof. exact (TRANS (@lem7542537 c) (@lem7542639 c)). Qed.
Lemma lem7542641 (c : real) : (term393 c) = term10.
Proof. exact (@lem1982719 c). Qed.
Lemma lem7542642 (c : real) : (term398 c) = term10.
Proof. exact (TRANS (@lem7542640 c) (@lem7542641 c)). Qed.
Lemma lem7542643 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7542644 (c : real) : (term399 c) = term395.
Proof. exact (MK_COMB (@lem7542643) (@lem7542642 c)). Qed.
Lemma lem7542645 (k : real) (s : real) : (term422 k s) = (term423 k s).
Proof. exact (@lem1982753 (term242 k) k s (term242 s)). Qed.
Lemma lem7542646 (k : real) : (term371 k) = (term372 k).
Proof. exact (@lem1982713 term251 k). Qed.
Lemma lem7542648 (x : nat) : (real_of_num x) = (term247 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7542649 : term259 = term294.
Proof. exact (@lem7542648 term253). Qed.
Lemma lem7542651 (x : nat) : (term249 x) = (term250 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7542652 : term251 = term252.
Proof. exact (@lem7542651 term253). Qed.
Lemma lem7542653 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7542654 : term373 = term374.
Proof. exact (MK_COMB (@lem7542653) (@lem7542652)). Qed.
Lemma lem7542655 : term375 = term376.
Proof. exact (MK_COMB (@lem7542654) (@lem7542649)). Qed.
Lemma lem7542656 : term377.
Proof. exact (@lem1981473 term251 term259 term259 term259 term10 term259). Qed.
Lemma lem7542658 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7542659 : term340 = term346.
Proof. exact (@lem7542658 (NUMERAL 0) term253). Qed.
Lemma lem7542660 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7542661 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7542662 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7542661 h1) (fun h1 : term346 = True => @lem7542660)). Qed.
Lemma lem7542663 : term346 = True.
Proof. exact (EQ_MP (@lem7542662) (@lem7542660)). Qed.
Lemma lem7542664 : term340 = True.
Proof. exact (TRANS (@lem7542659) (@lem7542663)). Qed.
Lemma lem7542665 : True = term340.
Proof. exact (SYM (@lem7542664)). Qed.
Lemma lem7542666 : term340.
Proof. exact (EQ_MP (@lem7542665) (@lem0)). Qed.
Lemma lem7542667 : term378.
Proof. exact (@lem7542656 (@lem7542666)). Qed.
Lemma lem7542669 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7542670 : term340 = term346.
Proof. exact (@lem7542669 (NUMERAL 0) term253). Qed.
Lemma lem7542671 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7542672 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7542673 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7542672 h1) (fun h1 : term346 = True => @lem7542671)). Qed.
Lemma lem7542674 : term346 = True.
Proof. exact (EQ_MP (@lem7542673) (@lem7542671)). Qed.
Lemma lem7542675 : term340 = True.
Proof. exact (TRANS (@lem7542670) (@lem7542674)). Qed.
Lemma lem7542676 : True = term340.
Proof. exact (SYM (@lem7542675)). Qed.
Lemma lem7542677 : term340.
Proof. exact (EQ_MP (@lem7542676) (@lem0)). Qed.
Lemma lem7542678 : term379.
Proof. exact (@lem7542667 (@lem7542677)). Qed.
Lemma lem7542680 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7542681 : term340 = term346.
Proof. exact (@lem7542680 (NUMERAL 0) term253). Qed.
Lemma lem7542682 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7542683 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7542684 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7542683 h1) (fun h1 : term346 = True => @lem7542682)). Qed.
Lemma lem7542685 : term346 = True.
Proof. exact (EQ_MP (@lem7542684) (@lem7542682)). Qed.
Lemma lem7542686 : term340 = True.
Proof. exact (TRANS (@lem7542681) (@lem7542685)). Qed.
Lemma lem7542687 : True = term340.
Proof. exact (SYM (@lem7542686)). Qed.
Lemma lem7542688 : term340.
Proof. exact (EQ_MP (@lem7542687) (@lem0)). Qed.
Lemma lem7542689 : term380.
Proof. exact (@lem7542678 (@lem7542688)). Qed.
Lemma lem7542691 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7542692 : term262 = term263.
Proof. exact (@lem7542691 term253 term253). Qed.
Lemma lem7542693 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7542694 : term265 = term253.
Proof. exact (EQ_MP (@lem7542693) (@lem940073)). Qed.
Lemma lem7542695 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7542696 : term263 = term259.
Proof. exact (MK_COMB (@lem7542695) (@lem7542694)). Qed.
Lemma lem7542697 : term262 = term259.
Proof. exact (TRANS (@lem7542692) (@lem7542696)). Qed.
Lemma lem7542699 (m : nat) (n : nat) : (term381 m n) = (term382 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7542700 : term383 = term384.
Proof. exact (@lem7542699 term253 term253). Qed.
Lemma lem7542701 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7542702 : term265 = term253.
Proof. exact (EQ_MP (@lem7542701) (@lem940073)). Qed.
Lemma lem7542703 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7542704 : term263 = term259.
Proof. exact (MK_COMB (@lem7542703) (@lem7542702)). Qed.
Lemma lem7542705 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7542706 : term384 = term251.
Proof. exact (MK_COMB (@lem7542705) (@lem7542704)). Qed.
Lemma lem7542707 : term383 = term251.
Proof. exact (TRANS (@lem7542700) (@lem7542706)). Qed.
Lemma lem7542708 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7542709 : term385 = term373.
Proof. exact (MK_COMB (@lem7542708) (@lem7542707)). Qed.
Lemma lem7542710 : term386 = term375.
Proof. exact (MK_COMB (@lem7542709) (@lem7542697)). Qed.
Lemma lem7542712 (m : nat) : (term387 m) = term10.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7542713 : term375 = term10.
Proof. exact (@lem7542712 term253). Qed.
Lemma lem7542714 : term386 = term10.
Proof. exact (TRANS (@lem7542710) (@lem7542713)). Qed.
Lemma lem7542715 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7542716 : term388 = term389.
Proof. exact (MK_COMB (@lem7542715) (@lem7542714)). Qed.
Lemma lem7542717 : term259 = term259.
Proof. exact (eq_refl term259). Qed.
Lemma lem7542718 : term390 = term351.
Proof. exact (MK_COMB (@lem7542716) (@lem7542717)). Qed.
Lemma lem7542720 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7542721 : term351 = term10.
Proof. exact (@lem7542720 term253). Qed.
Lemma lem7542722 : term390 = term10.
Proof. exact (TRANS (@lem7542718) (@lem7542721)). Qed.
Lemma lem7542724 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7542725 : term262 = term263.
Proof. exact (@lem7542724 term253 term253). Qed.
Lemma lem7542726 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7542727 : term265 = term253.
Proof. exact (EQ_MP (@lem7542726) (@lem940073)). Qed.
Lemma lem7542728 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7542729 : term263 = term259.
Proof. exact (MK_COMB (@lem7542728) (@lem7542727)). Qed.
Lemma lem7542730 : term262 = term259.
Proof. exact (TRANS (@lem7542725) (@lem7542729)). Qed.
Lemma lem7542731 : term389 = term389.
Proof. exact (eq_refl term389). Qed.
Lemma lem7542732 : term391 = term351.
Proof. exact (MK_COMB (@lem7542731) (@lem7542730)). Qed.
Lemma lem7542734 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7542735 : term351 = term10.
Proof. exact (@lem7542734 term253). Qed.
Lemma lem7542736 : term391 = term10.
Proof. exact (TRANS (@lem7542732) (@lem7542735)). Qed.
Lemma lem7542737 : term10 = term391.
Proof. exact (SYM (@lem7542736)). Qed.
Lemma lem7542738 : term390 = term391.
Proof. exact (TRANS (@lem7542722) (@lem7542737)). Qed.
Lemma lem7542739 : term376 = term248.
Proof. exact (@lem7542689 (@lem7542738)). Qed.
Lemma lem7542740 : term375 = term248.
Proof. exact (TRANS (@lem7542655) (@lem7542739)). Qed.
Lemma lem7542742 (x : real) : (term269 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7542743 : term248 = term10.
Proof. exact (@lem7542742 term10). Qed.
Lemma lem7542744 : term375 = term10.
Proof. exact (TRANS (@lem7542740) (@lem7542743)). Qed.
Lemma lem7542745 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7542746 : term392 = term389.
Proof. exact (MK_COMB (@lem7542745) (@lem7542744)). Qed.
Lemma lem7542747 (k : real) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem7542748 (k : real) : (term372 k) = (term393 k).
Proof. exact (MK_COMB (@lem7542746) (@lem7542747 k)). Qed.
Lemma lem7542749 (k : real) : (term371 k) = (term393 k).
Proof. exact (TRANS (@lem7542646 k) (@lem7542748 k)). Qed.
Lemma lem7542750 (k : real) : (term393 k) = term10.
Proof. exact (@lem1982719 k). Qed.
Lemma lem7542751 (k : real) : (term371 k) = term10.
Proof. exact (TRANS (@lem7542749 k) (@lem7542750 k)). Qed.
Lemma lem7542752 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7542753 (k : real) : (term394 k) = term395.
Proof. exact (MK_COMB (@lem7542752) (@lem7542751 k)). Qed.
Lemma lem7542754 (s : real) : (term398 s) = (term372 s).
Proof. exact (@lem1982715 term251 s). Qed.
Lemma lem7542756 (x : nat) : (real_of_num x) = (term247 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7542757 : term259 = term294.
Proof. exact (@lem7542756 term253). Qed.
Lemma lem7542759 (x : nat) : (term249 x) = (term250 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7542760 : term251 = term252.
Proof. exact (@lem7542759 term253). Qed.
Lemma lem7542761 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7542762 : term373 = term374.
Proof. exact (MK_COMB (@lem7542761) (@lem7542760)). Qed.
Lemma lem7542763 : term375 = term376.
Proof. exact (MK_COMB (@lem7542762) (@lem7542757)). Qed.
Lemma lem7542764 : term377.
Proof. exact (@lem1981473 term251 term259 term259 term259 term10 term259). Qed.
Lemma lem7542766 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7542767 : term340 = term346.
Proof. exact (@lem7542766 (NUMERAL 0) term253). Qed.
Lemma lem7542768 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7542769 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7542770 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7542769 h1) (fun h1 : term346 = True => @lem7542768)). Qed.
Lemma lem7542771 : term346 = True.
Proof. exact (EQ_MP (@lem7542770) (@lem7542768)). Qed.
Lemma lem7542772 : term340 = True.
Proof. exact (TRANS (@lem7542767) (@lem7542771)). Qed.
Lemma lem7542773 : True = term340.
Proof. exact (SYM (@lem7542772)). Qed.
Lemma lem7542774 : term340.
Proof. exact (EQ_MP (@lem7542773) (@lem0)). Qed.
Lemma lem7542775 : term378.
Proof. exact (@lem7542764 (@lem7542774)). Qed.
Lemma lem7542777 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7542778 : term340 = term346.
Proof. exact (@lem7542777 (NUMERAL 0) term253). Qed.
Lemma lem7542779 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7542780 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7542781 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7542780 h1) (fun h1 : term346 = True => @lem7542779)). Qed.
Lemma lem7542782 : term346 = True.
Proof. exact (EQ_MP (@lem7542781) (@lem7542779)). Qed.
Lemma lem7542783 : term340 = True.
Proof. exact (TRANS (@lem7542778) (@lem7542782)). Qed.
Lemma lem7542784 : True = term340.
Proof. exact (SYM (@lem7542783)). Qed.
Lemma lem7542785 : term340.
Proof. exact (EQ_MP (@lem7542784) (@lem0)). Qed.
Lemma lem7542786 : term379.
Proof. exact (@lem7542775 (@lem7542785)). Qed.
Lemma lem7542788 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7542789 : term340 = term346.
Proof. exact (@lem7542788 (NUMERAL 0) term253). Qed.
Lemma lem7542790 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7542791 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7542792 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7542791 h1) (fun h1 : term346 = True => @lem7542790)). Qed.
Lemma lem7542793 : term346 = True.
Proof. exact (EQ_MP (@lem7542792) (@lem7542790)). Qed.
Lemma lem7542794 : term340 = True.
Proof. exact (TRANS (@lem7542789) (@lem7542793)). Qed.
Lemma lem7542795 : True = term340.
Proof. exact (SYM (@lem7542794)). Qed.
Lemma lem7542796 : term340.
Proof. exact (EQ_MP (@lem7542795) (@lem0)). Qed.
Lemma lem7542797 : term380.
Proof. exact (@lem7542786 (@lem7542796)). Qed.
Lemma lem7542799 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7542800 : term262 = term263.
Proof. exact (@lem7542799 term253 term253). Qed.
Lemma lem7542801 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7542802 : term265 = term253.
Proof. exact (EQ_MP (@lem7542801) (@lem940073)). Qed.
Lemma lem7542803 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7542804 : term263 = term259.
Proof. exact (MK_COMB (@lem7542803) (@lem7542802)). Qed.
Lemma lem7542805 : term262 = term259.
Proof. exact (TRANS (@lem7542800) (@lem7542804)). Qed.
Lemma lem7542807 (m : nat) (n : nat) : (term381 m n) = (term382 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7542808 : term383 = term384.
Proof. exact (@lem7542807 term253 term253). Qed.
Lemma lem7542809 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7542810 : term265 = term253.
Proof. exact (EQ_MP (@lem7542809) (@lem940073)). Qed.
Lemma lem7542811 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7542812 : term263 = term259.
Proof. exact (MK_COMB (@lem7542811) (@lem7542810)). Qed.
Lemma lem7542813 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7542814 : term384 = term251.
Proof. exact (MK_COMB (@lem7542813) (@lem7542812)). Qed.
Lemma lem7542815 : term383 = term251.
Proof. exact (TRANS (@lem7542808) (@lem7542814)). Qed.
Lemma lem7542816 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7542817 : term385 = term373.
Proof. exact (MK_COMB (@lem7542816) (@lem7542815)). Qed.
Lemma lem7542818 : term386 = term375.
Proof. exact (MK_COMB (@lem7542817) (@lem7542805)). Qed.
Lemma lem7542820 (m : nat) : (term387 m) = term10.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7542821 : term375 = term10.
Proof. exact (@lem7542820 term253). Qed.
Lemma lem7542822 : term386 = term10.
Proof. exact (TRANS (@lem7542818) (@lem7542821)). Qed.
Lemma lem7542823 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7542824 : term388 = term389.
Proof. exact (MK_COMB (@lem7542823) (@lem7542822)). Qed.
Lemma lem7542825 : term259 = term259.
Proof. exact (eq_refl term259). Qed.
Lemma lem7542826 : term390 = term351.
Proof. exact (MK_COMB (@lem7542824) (@lem7542825)). Qed.
Lemma lem7542828 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7542829 : term351 = term10.
Proof. exact (@lem7542828 term253). Qed.
Lemma lem7542830 : term390 = term10.
Proof. exact (TRANS (@lem7542826) (@lem7542829)). Qed.
Lemma lem7542832 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7542833 : term262 = term263.
Proof. exact (@lem7542832 term253 term253). Qed.
Lemma lem7542834 : (term264 = (BIT1 0)) = (term265 = term253).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7542835 : term265 = term253.
Proof. exact (EQ_MP (@lem7542834) (@lem940073)). Qed.
Lemma lem7542836 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7542837 : term263 = term259.
Proof. exact (MK_COMB (@lem7542836) (@lem7542835)). Qed.
Lemma lem7542838 : term262 = term259.
Proof. exact (TRANS (@lem7542833) (@lem7542837)). Qed.
Lemma lem7542839 : term389 = term389.
Proof. exact (eq_refl term389). Qed.
Lemma lem7542840 : term391 = term351.
Proof. exact (MK_COMB (@lem7542839) (@lem7542838)). Qed.
Lemma lem7542842 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7542843 : term351 = term10.
Proof. exact (@lem7542842 term253). Qed.
Lemma lem7542844 : term391 = term10.
Proof. exact (TRANS (@lem7542840) (@lem7542843)). Qed.
Lemma lem7542845 : term10 = term391.
Proof. exact (SYM (@lem7542844)). Qed.
Lemma lem7542846 : term390 = term391.
Proof. exact (TRANS (@lem7542830) (@lem7542845)). Qed.
Lemma lem7542847 : term376 = term248.
Proof. exact (@lem7542797 (@lem7542846)). Qed.
Lemma lem7542848 : term375 = term248.
Proof. exact (TRANS (@lem7542763) (@lem7542847)). Qed.
Lemma lem7542850 (x : real) : (term269 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7542851 : term248 = term10.
Proof. exact (@lem7542850 term10). Qed.
Lemma lem7542852 : term375 = term10.
Proof. exact (TRANS (@lem7542848) (@lem7542851)). Qed.
Lemma lem7542853 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7542854 : term392 = term389.
Proof. exact (MK_COMB (@lem7542853) (@lem7542852)). Qed.
Lemma lem7542855 (s : real) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7542856 (s : real) : (term372 s) = (term393 s).
Proof. exact (MK_COMB (@lem7542854) (@lem7542855 s)). Qed.
Lemma lem7542857 (s : real) : (term398 s) = (term393 s).
Proof. exact (TRANS (@lem7542754 s) (@lem7542856 s)). Qed.
Lemma lem7542858 (s : real) : (term393 s) = term10.
Proof. exact (@lem1982719 s). Qed.
Lemma lem7542859 (s : real) : (term398 s) = term10.
Proof. exact (TRANS (@lem7542857 s) (@lem7542858 s)). Qed.
Lemma lem7542860 (k : real) (s : real) : (term423 k s) = term400.
Proof. exact (MK_COMB (@lem7542753 k) (@lem7542859 s)). Qed.
Lemma lem7542861 (k : real) (s : real) : (term422 k s) = term400.
Proof. exact (TRANS (@lem7542645 k s) (@lem7542860 k s)). Qed.
Lemma lem7542862 : term400 = term10.
Proof. exact (@lem1982721 term10). Qed.
Lemma lem7542863 (k : real) (s : real) : (term422 k s) = term10.
Proof. exact (TRANS (@lem7542861 k s) (@lem7542862)). Qed.
Lemma lem7542864 (c : real) (k : real) (s : real) : (term421 c k s) = term400.
Proof. exact (MK_COMB (@lem7542644 c) (@lem7542863 k s)). Qed.
Lemma lem7542865 (c : real) (k : real) (s : real) : (term420 c k s) = term400.
Proof. exact (TRANS (@lem7542536 c k s) (@lem7542864 c k s)). Qed.
Lemma lem7542866 : term400 = term10.
Proof. exact (@lem1982721 term10). Qed.
Lemma lem7542867 (c : real) (k : real) (s : real) : (term420 c k s) = term10.
Proof. exact (TRANS (@lem7542865 c k s) (@lem7542866)). Qed.
Lemma lem7542868 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7542869 (c : real) (k : real) (s : real) : (term424 c k s) = term402.
Proof. exact (MK_COMB (@lem7542868) (@lem7542867 c k s)). Qed.
Lemma lem7542870 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7542871 (c : real) (k : real) (s : real) : (term419 c k s) = term403.
Proof. exact (MK_COMB (@lem7542869 c k s) (@lem7542870)). Qed.
Lemma lem7542872 (c : real) (k : real) (s : real) (h1 : term426 c k s) : term403.
Proof. exact (EQ_MP (@lem7542871 c k s) (@lem7542535 c k s h1)). Qed.
Lemma lem7542874 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7542875 : term403 = term404.
Proof. exact (@lem7542874 term10 term10). Qed.
Lemma lem7542877 (x : nat) : (real_of_num x) = (term247 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7542878 : term10 = term248.
Proof. exact (@lem7542877 (NUMERAL 0)). Qed.
Lemma lem7542880 (x : nat) : (real_of_num x) = (term247 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7542881 : term10 = term248.
Proof. exact (@lem7542880 (NUMERAL 0)). Qed.
Lemma lem7542882 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7542883 : term341 = term342.
Proof. exact (MK_COMB (@lem7542882) (@lem7542881)). Qed.
Lemma lem7542884 : term404 = term405.
Proof. exact (MK_COMB (@lem7542883) (@lem7542878)). Qed.
Lemma lem7542885 : term406.
Proof. exact (@lem1980255 term10 term259 term10 term259). Qed.
Lemma lem7542887 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7542888 : term340 = term346.
Proof. exact (@lem7542887 (NUMERAL 0) term253). Qed.
Lemma lem7542889 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7542890 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7542891 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7542890 h1) (fun h1 : term346 = True => @lem7542889)). Qed.
Lemma lem7542892 : term346 = True.
Proof. exact (EQ_MP (@lem7542891) (@lem7542889)). Qed.
Lemma lem7542893 : term340 = True.
Proof. exact (TRANS (@lem7542888) (@lem7542892)). Qed.
Lemma lem7542894 : True = term340.
Proof. exact (SYM (@lem7542893)). Qed.
Lemma lem7542895 : term340.
Proof. exact (EQ_MP (@lem7542894) (@lem0)). Qed.
Lemma lem7542896 : term407.
Proof. exact (@lem7542885 (@lem7542895)). Qed.
Lemma lem7542898 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7542899 : term340 = term346.
Proof. exact (@lem7542898 (NUMERAL 0) term253). Qed.
Lemma lem7542900 : term347 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7542901 (h1 : term347 = (BIT1 0)) : term346 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7542902 : (term347 = (BIT1 0)) = (term346 = True).
Proof. exact (prop_ext (fun h1 : term347 = (BIT1 0) => @lem7542901 h1) (fun h1 : term346 = True => @lem7542900)). Qed.
Lemma lem7542903 : term346 = True.
Proof. exact (EQ_MP (@lem7542902) (@lem7542900)). Qed.
Lemma lem7542904 : term340 = True.
Proof. exact (TRANS (@lem7542899) (@lem7542903)). Qed.
Lemma lem7542905 : True = term340.
Proof. exact (SYM (@lem7542904)). Qed.
Lemma lem7542906 : term340.
Proof. exact (EQ_MP (@lem7542905) (@lem0)). Qed.
Lemma lem7542907 : term405 = term408.
Proof. exact (@lem7542896 (@lem7542906)). Qed.
Lemma lem7542909 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7542910 : term351 = term10.
Proof. exact (@lem7542909 term253). Qed.
Lemma lem7542912 (x : nat) : (term350 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7542913 : term351 = term10.
Proof. exact (@lem7542912 term253). Qed.
Lemma lem7542914 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7542915 : term352 = term341.
Proof. exact (MK_COMB (@lem7542914) (@lem7542913)). Qed.
Lemma lem7542916 : term408 = term404.
Proof. exact (MK_COMB (@lem7542915) (@lem7542910)). Qed.
Lemma lem7542918 (m : nat) (n : nat) : (term345 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7542919 : term404 = term409.
Proof. exact (@lem7542918 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7542920 : term409 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7542921 : term404 = False.
Proof. exact (TRANS (@lem7542919) (@lem7542920)). Qed.
Lemma lem7542922 : term408 = False.
Proof. exact (TRANS (@lem7542916) (@lem7542921)). Qed.
Lemma lem7542923 : term405 = False.
Proof. exact (TRANS (@lem7542907) (@lem7542922)). Qed.
Lemma lem7542924 : term404 = False.
Proof. exact (TRANS (@lem7542884) (@lem7542923)). Qed.
Lemma lem7542925 : term403 = False.
Proof. exact (TRANS (@lem7542875) (@lem7542924)). Qed.
Lemma lem7542926 (c : real) (k : real) (s : real) (h1 : term426 c k s) : False.
Proof. exact (EQ_MP (@lem7542925) (@lem7542872 c k s h1)). Qed.
Lemma lem7542927 (c : real) (k : real) (s : real) (h1 : term334 c k s) : False.
Proof. exact (or_elim (@lem7541900 c k s h1) (fun h0 : term425 c k s => @lem7542440 c k s h0) (fun h0 : term426 c k s => @lem7542926 c k s h0)). Qed.
Lemma lem7542928 (c : real) (k : real) (s : real) (h1 : term337 c k s) : False.
Proof. exact (or_elim (@lem7540871 c k s h1) (fun h0 : term335 c k s => @lem7541899 c k s h0) (fun h0 : term334 c k s => @lem7542927 c k s h0)). Qed.
Lemma lem7542930 (c : real) (k : real) (s : real) (h1 : term337 c k s) : term337 c k s.
Proof. exact (h1). Qed.
Lemma lem7542931 (c : real) (k : real) (s : real) (h1 : term337 c k s) : (term337 c k s) = False.
Proof. exact (prop_ext (fun h2 : term337 c k s => @lem7542928 c k s h1) (fun h2 : False => @lem7542930 c k s h1)). Qed.
Lemma lem7542932 (c : real) (k : real) (s : real) (h1 : term337 c k s) : False.
Proof. exact (EQ_MP (@lem7542931 c k s h1) (@lem7542930 c k s h1)). Qed.
Lemma lem7542933 (c : real) (s : real) (k : real) (h1 : term233 c s k) : term233 c s k.
Proof. exact (h1). Qed.
Lemma lem7542934 (c : real) (s : real) (k : real) (h1 : term233 c s k) : term337 c k s.
Proof. exact (EQ_MP (@lem7540849 c k s) (@lem7542933 c s k h1)). Qed.
Lemma lem7542935 (c : real) (s : real) (k : real) (h1 : term233 c s k) : (term337 c k s) = False.
Proof. exact (prop_ext (fun h2 : term337 c k s => @lem7542932 c k s h2) (fun h2 : False => @lem7542934 c s k h1)). Qed.
Lemma lem7542936 (c : real) (s : real) (k : real) (h1 : term233 c s k) : False.
Proof. exact (EQ_MP (@lem7542935 c s k h1) (@lem7542934 c s k h1)). Qed.
Lemma lem7542937 (c : real) (s : real) (k : real) : term427 c s k.
Proof. exact (fun h0 : term233 c s k => @lem7542936 c s k h0). Qed.
Lemma lem7542938 (c : real) (s : real) (k : real) : term428 c s k.
Proof. exact (@lem1386578 (((term235 c k s) = term10) = ((real_add c s) = k))). Qed.
Lemma lem7542942 (x : real) : term429 x.
Proof. exact (@lem1383409 x). Qed.
Lemma lem7542943 (x : real) : (term429 x) = ((term430 x) = x).
Proof. exact (eq_refl (term429 x)). Qed.
Lemma lem7542950 (n : nat) : term11 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem7542951 (n : nat) : (term11 n) = (term12 n).
Proof. exact (eq_refl (term11 n)). Qed.
Lemma lem7542952 (n : nat) : term12 n.
Proof. exact (EQ_MP (@lem7542951 n) (@lem7542950 n)). Qed.
Lemma lem7542953 (n : nat) : (term12 n) = ((term12 n) = True).
Proof. exact (@lem7 (term12 n)). Qed.
Lemma lem7542955 (f : nat -> real) : term431 f.
Proof. exact (@lem7226008 f). Qed.
Lemma lem7542956 (f : nat -> real) : (term431 f) = (term432 f).
Proof. exact (eq_refl (term431 f)). Qed.
Lemma lem7542957 (f : nat -> real) : term432 f.
Proof. exact (EQ_MP (@lem7542956 f) (@lem7542955 f)). Qed.
Lemma lem7542958 (f : nat -> real) (m : nat) : term433 f m.
Proof. exact (@lem7542957 f m). Qed.
Lemma lem7542959 (m : nat) (f : nat -> real) : (term433 f m) = (term434 m f).
Proof. exact (eq_refl (term433 f m)). Qed.
Lemma lem7542960 (m : nat) (f : nat -> real) : term434 m f.
Proof. exact (EQ_MP (@lem7542959 m f) (@lem7542958 f m)). Qed.
Lemma lem7542961 (m : nat) (f : nat -> real) (n : nat) : term435 m f n.
Proof. exact (@lem7542960 m f n). Qed.
Lemma lem7542962 (m : nat) (n : nat) (f : nat -> real) : (term435 m f n) = (term436 m n f).
Proof. exact (eq_refl (term435 m f n)). Qed.
Lemma lem7542963 (m : nat) (n : nat) (f : nat -> real) : term436 m n f.
Proof. exact (EQ_MP (@lem7542962 m n f) (@lem7542961 m f n)). Qed.
Lemma lem7542964 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem7542965 (f : nat -> real) (m : nat) (n : nat) (h1 : Peano.le m n) : (term437 m n f) = (term438 m n f).
Proof. exact (@lem7542963 m n f (@lem7542964 m n h1)). Qed.
Lemma lem7542971 {A : Type'} (h1 : term439 A) : term439 A.
Proof. exact (h1). Qed.
Lemma lem7542972 {A : Type'} (x : A) (h1 : term439 A) : term440 A x.
Proof. exact (@lem7542971 A h1 x). Qed.
Lemma lem7542973 {A : Type'} (x : A) : (term440 A x) = (term441 A x).
Proof. exact (eq_refl (term440 A x)). Qed.
Lemma lem7542974 {A : Type'} (x : A) (h1 : term439 A) : term441 A x.
Proof. exact (EQ_MP (@lem7542973 A x) (@lem7542972 A x h1)). Qed.
Lemma lem7542975 {A : Type'} (x : A) (y : A) (h1 : term439 A) : term442 A x y.
Proof. exact (@lem7542974 A x h1 y). Qed.
Lemma lem7542976 {A : Type'} (y : A) (x : A) : (term442 A x y) = (term443 A y x).
Proof. exact (eq_refl (term442 A x y)). Qed.
Lemma lem7542977 {A : Type'} (y : A) (x : A) (h1 : term439 A) : term443 A y x.
Proof. exact (EQ_MP (@lem7542976 A y x) (@lem7542975 A x y h1)). Qed.
Lemma lem7542978 {A : Type'} (y : A) (x : A) (z : A) (h1 : term439 A) : term444 A y x z.
Proof. exact (@lem7542977 A y x h1 z). Qed.
Lemma lem7542979 {A : Type'} (y : A) (x : A) (z : A) : (term444 A y x z) = (term445 A y x z).
Proof. exact (eq_refl (term444 A y x z)). Qed.
Lemma lem7542980 {A : Type'} (y : A) (x : A) (z : A) (h1 : term439 A) : term445 A y x z.
Proof. exact (EQ_MP (@lem7542979 A y x z) (@lem7542978 A y x z h1)). Qed.
Lemma lem7542981 {A : Type'} (x : A) (y : A) (z : A) (h1 : term446 A x y z) : term446 A x y z.
Proof. exact (h1). Qed.
Lemma lem7542982 {A : Type'} (x : A) (y : A) (z : A) (h1 : term439 A) (h2 : term446 A x y z) : x = z.
Proof. exact (@lem7542980 A y x z h1 (@lem7542981 A x y z h2)). Qed.
Lemma lem7542983 {A : Type'} (x : A) (y : A) (z : A) (h1 : term446 A x y z) : term447 A x z.
Proof. exact (fun h0 : term439 A => @lem7542982 A x y z h0 h1). Qed.
Lemma lem7542984 {A : Type'} (x : A) (z : A) (h1 : term448 A x z) : term448 A x z.
Proof. exact (h1). Qed.
Lemma lem7542985 {A : Type'} (x : A) (z : A) (h1 : term448 A x z) : term447 A x z.
Proof. exact (ex_elim (@lem7542984 A x z h1) (fun y : A => fun h0 : term449 A x z y => @lem7542983 A x y z h0)). Qed.
Lemma lem7542986 {A : Type'} (h1 : term439 A) : term439 A.
Proof. exact (h1). Qed.
Lemma lem7542987 {A : Type'} (x : A) (z : A) (h1 : term439 A) (h2 : term448 A x z) : x = z.
Proof. exact (@lem7542985 A x z h2 (@lem7542986 A h1)). Qed.
Lemma lem7542988 {A : Type'} (x : A) (z : A) (h1 : term439 A) : term450 A x z.
Proof. exact (fun h0 : term448 A x z => @lem7542987 A x z h1 h0). Qed.
Lemma lem7542989 {A : Type'} (x : A) (h1 : term439 A) : term451 A x.
Proof. exact (fun z : A => @lem7542988 A x z h1). Qed.
Lemma lem7542990 {A : Type'} (h1 : term439 A) : term452 A.
Proof. exact (fun x : A => @lem7542989 A x h1). Qed.
Lemma lem7542991 {A : Type'} : term453 A.
Proof. exact (fun h0 : term439 A => @lem7542990 A h0). Qed.
Lemma lem7542992 {A : Type'} : term452 A.
Proof. exact (@lem7542991 A (@lem403 A)). Qed.
Lemma lem7542993 {A : Type'} (x : A) : term454 A x.
Proof. exact (@lem7542992 A x). Qed.
Lemma lem7542994 {A : Type'} (x : A) : (term454 A x) = (term451 A x).
Proof. exact (eq_refl (term454 A x)). Qed.
Lemma lem7542995 {A : Type'} (x : A) : term451 A x.
Proof. exact (EQ_MP (@lem7542994 A x) (@lem7542993 A x)). Qed.
Lemma lem7542996 {A : Type'} (x : A) (z : A) : term455 A x z.
Proof. exact (@lem7542995 A x z). Qed.
Lemma lem7542997 {A : Type'} (x : A) (z : A) : (term455 A x z) = (term450 A x z).
Proof. exact (eq_refl (term455 A x z)). Qed.
Lemma lem7543000 {A : Type'} (x : A) (z : A) : term450 A x z.
Proof. exact (EQ_MP (@lem7542997 A x z) (@lem7542996 A x z)). Qed.
Lemma lem7543001 (x : Prop) (z : Prop) : term456 x z.
Proof. exact (@lem7543000 Prop x z). Qed.
Lemma lem7543002 (k : real) (n : nat) (c : nat -> real) : term457 k n c.
Proof. exact (@lem7543001 (term458 n c k) (term459 k n c)). Qed.
Lemma lem7543012 (m : nat) (n : nat) (f : nat -> real) : term436 m n f.
Proof. exact (fun h0 : Peano.le m n => @lem7542965 f m n h0). Qed.
Lemma lem7543013 (n : nat) (c : nat -> real) (x : real) : term460 n c x.
Proof. exact (@lem7543012 (NUMERAL 0) n (term461 c x)). Qed.
Lemma lem7543015 (n : nat) : (term12 n) = True.
Proof. exact (EQ_MP (@lem7542953 n) (@lem7542952 n)). Qed.
Lemma lem7543016 (n : nat) : True = (term12 n).
Proof. exact (SYM (@lem7543015 n)). Qed.
Lemma lem7543017 (n : nat) : term12 n.
Proof. exact (EQ_MP (@lem7543016 n) (@lem0)). Qed.
Lemma lem7543018 (n : nat) (c : nat -> real) (x : real) : (term462 n c x) = (term463 n c x).
Proof. exact (@lem7543013 n c x (@lem7543017 n)). Qed.
Lemma lem7543020 {A B : Type'} (f : A -> B) (y : A) : (term464 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7543021 (f : nat -> real) (y : nat) : (term465 f y) = (f y).
Proof. exact (@lem7543020 nat real f y). Qed.
Lemma lem7543022 (c : nat -> real) (x : real) : (term466 c x) = (term467 c x).
Proof. exact (@lem7543021 (term461 c x) (NUMERAL 0)). Qed.
Lemma lem7543023 (c : nat -> real) (x : real) (i : nat) : (term468 c x i) = (term469 c x i).
Proof. exact (eq_refl (term468 c x i)). Qed.
Lemma lem7543024 (c : nat -> real) (x : real) : (term470 c x) = (term461 c x).
Proof. exact (fun_ext (fun i : nat => @lem7543023 c x i)). Qed.
Lemma lem7543025 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem7543026 (c : nat -> real) (x : real) : (term466 c x) = (term467 c x).
Proof. exact (MK_COMB (@lem7543024 c x) (@lem7543025)). Qed.
Lemma lem7543027 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7543028 (c : nat -> real) (x : real) : (term471 c x) = (term472 c x).
Proof. exact (MK_COMB (@lem7543027) (@lem7543026 c x)). Qed.
Lemma lem7543029 (c : nat -> real) (x : real) : (term467 c x) = (term473 c x).
Proof. exact (eq_refl (term467 c x)). Qed.
Lemma lem7543030 (c : nat -> real) (x : real) : ((term466 c x) = (term467 c x)) = ((term467 c x) = (term473 c x)).
Proof. exact (MK_COMB (@lem7543028 c x) (@lem7543029 c x)). Qed.
Lemma lem7543031 (c : nat -> real) (x : real) : (term467 c x) = (term473 c x).
Proof. exact (EQ_MP (@lem7543030 c x) (@lem7543022 c x)). Qed.
Lemma lem7543033 (x : real) : (term474 x) = term259.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem7543034 (c : nat -> real) : (term475 c) = (term475 c).
Proof. exact (eq_refl (term475 c)). Qed.
Lemma lem7543035 (x : real) (c : nat -> real) : (term473 c x) = (term476 c).
Proof. exact (MK_COMB (@lem7543034 c) (@lem7543033 x)). Qed.
Lemma lem7543037 (x : real) : (term430 x) = x.
Proof. exact (EQ_MP (@lem7542943 x) (@lem7542942 x)). Qed.
Lemma lem7543038 (c : nat -> real) : (term476 c) = (term477 c).
Proof. exact (@lem7543037 (term477 c)). Qed.
Lemma lem7543039 (x : real) (c : nat -> real) : (term473 c x) = (term477 c).
Proof. exact (TRANS (@lem7543035 x c) (@lem7543038 c)). Qed.
Lemma lem7543040 (x : real) (c : nat -> real) : (term467 c x) = (term477 c).
Proof. exact (TRANS (@lem7543031 c x) (@lem7543039 x c)). Qed.
Lemma lem7543041 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7543042 (x : real) (c : nat -> real) : (term478 c x) = (term479 c).
Proof. exact (MK_COMB (@lem7543041) (@lem7543040 x c)). Qed.
Lemma lem7543163 (n : nat) (c : nat -> real) (x : real) : (term480 n c x) = (term480 n c x).
Proof. exact (eq_refl (term480 n c x)). Qed.
Lemma lem7543164 (n : nat) (c : nat -> real) (x : real) : (term463 n c x) = (term481 n c x).
Proof. exact (MK_COMB (@lem7543042 x c) (@lem7543163 n c x)). Qed.
Lemma lem7543285 (n : nat) (c : nat -> real) (x : real) : (term462 n c x) = (term481 n c x).
Proof. exact (TRANS (@lem7543018 n c x) (@lem7543164 n c x)). Qed.
Lemma lem7543286 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7543287 (n : nat) (c : nat -> real) (x : real) : (term482 n c x) = (term483 n c x).
Proof. exact (MK_COMB (@lem7543286) (@lem7543285 n c x)). Qed.
Lemma lem7543408 (k : real) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem7543409 (n : nat) (c : nat -> real) (x : real) (k : real) : ((term462 n c x) = k) = ((term481 n c x) = k).
Proof. exact (MK_COMB (@lem7543287 n c x) (@lem7543408 k)). Qed.
Lemma lem7543532 (n : nat) (c : nat -> real) (k : real) : (term484 n c k) = (term485 n c k).
Proof. exact (fun_ext (fun x : real => @lem7543409 n c x k)). Qed.
Lemma lem7543655 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7543656 (n : nat) (c : nat -> real) (k : real) : (term458 n c k) = (term486 n c k).
Proof. exact (MK_COMB (@lem7543655) (@lem7543532 n c k)). Qed.
Lemma lem7543783 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7543784 (n : nat) (c : nat -> real) (k : real) : (term487 n c k) = (term488 n c k).
Proof. exact (MK_COMB (@lem7543783) (@lem7543656 n c k)). Qed.
Lemma lem7543918 (m : nat) (n : nat) (f : nat -> real) : term436 m n f.
Proof. exact (fun h0 : Peano.le m n => @lem7542965 f m n h0). Qed.
Lemma lem7543919 (n : nat) (k : real) (c : nat -> real) (x : real) : term489 n k c x.
Proof. exact (@lem7543918 (NUMERAL 0) n (term490 k c x)). Qed.
Lemma lem7543921 (n : nat) : (term12 n) = True.
Proof. exact (EQ_MP (@lem7542953 n) (@lem7542952 n)). Qed.
Lemma lem7543922 (n : nat) : True = (term12 n).
Proof. exact (SYM (@lem7543921 n)). Qed.
Lemma lem7543923 (n : nat) : term12 n.
Proof. exact (EQ_MP (@lem7543922 n) (@lem0)). Qed.
Lemma lem7543924 (n : nat) (k : real) (c : nat -> real) (x : real) : (term491 n k c x) = (term492 n k c x).
Proof. exact (@lem7543919 n k c x (@lem7543923 n)). Qed.
Lemma lem7543926 {A B : Type'} (f : A -> B) (y : A) : (term464 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7543927 (f : nat -> real) (y : nat) : (term465 f y) = (f y).
Proof. exact (@lem7543926 nat real f y). Qed.
Lemma lem7543928 (k : real) (c : nat -> real) (x : real) : (term493 k c x) = (term494 k c x).
Proof. exact (@lem7543927 (term490 k c x) (NUMERAL 0)). Qed.
Lemma lem7543929 (k : real) (c : nat -> real) (x : real) (i : nat) : (term495 k c x i) = (term496 k c x i).
Proof. exact (eq_refl (term495 k c x i)). Qed.
Lemma lem7543930 (k : real) (c : nat -> real) (x : real) : (term497 k c x) = (term490 k c x).
Proof. exact (fun_ext (fun i : nat => @lem7543929 k c x i)). Qed.
Lemma lem7543931 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem7543932 (k : real) (c : nat -> real) (x : real) : (term493 k c x) = (term494 k c x).
Proof. exact (MK_COMB (@lem7543930 k c x) (@lem7543931)). Qed.
Lemma lem7543933 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7543934 (k : real) (c : nat -> real) (x : real) : (term498 k c x) = (term499 k c x).
Proof. exact (MK_COMB (@lem7543933) (@lem7543932 k c x)). Qed.
Lemma lem7543935 (k : real) (c : nat -> real) (x : real) : (term494 k c x) = (term500 k c x).
Proof. exact (eq_refl (term494 k c x)). Qed.
Lemma lem7543936 (k : real) (c : nat -> real) (x : real) : ((term493 k c x) = (term494 k c x)) = ((term494 k c x) = (term500 k c x)).
Proof. exact (MK_COMB (@lem7543934 k c x) (@lem7543935 k c x)). Qed.
Lemma lem7543937 (k : real) (c : nat -> real) (x : real) : (term494 k c x) = (term500 k c x).
Proof. exact (EQ_MP (@lem7543936 k c x) (@lem7543928 k c x)). Qed.
Lemma lem7543939 {_2975 _2982 : Type'} (x : _2982) (z : _2975) (y : _2975) : (term501 _2975 _2982 x y z) = y.
Proof. exact (EQ_MP (@lem15249 _2975 _2982 x z y) (@lem0)). Qed.
Lemma lem7543940 (x : nat) (z : real) (y : real) : (term502 x y z) = y.
Proof. exact (@lem7543939 real nat x z y). Qed.
Lemma lem7543941 (c : nat -> real) (k : real) : (term503 k c) = (term504 c k).
Proof. exact (@lem7543940 (NUMERAL 0) (term477 c) (term504 c k)). Qed.
Lemma lem7543942 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7543943 (c : nat -> real) (k : real) : (term505 k c) = (term506 c k).
Proof. exact (MK_COMB (@lem7543942) (@lem7543941 c k)). Qed.
Lemma lem7543945 (x : real) : (term474 x) = term259.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem7543946 (x : real) (c : nat -> real) (k : real) : (term500 k c x) = (term507 c k).
Proof. exact (MK_COMB (@lem7543943 c k) (@lem7543945 x)). Qed.
Lemma lem7543948 (x : real) : (term430 x) = x.
Proof. exact (EQ_MP (@lem7542943 x) (@lem7542942 x)). Qed.
Lemma lem7543949 (c : nat -> real) (k : real) : (term507 c k) = (term504 c k).
Proof. exact (@lem7543948 (term504 c k)). Qed.
Lemma lem7543950 (x : real) (c : nat -> real) (k : real) : (term500 k c x) = (term504 c k).
Proof. exact (TRANS (@lem7543946 x c k) (@lem7543949 c k)). Qed.
Lemma lem7543951 (x : real) (c : nat -> real) (k : real) : (term494 k c x) = (term504 c k).
Proof. exact (TRANS (@lem7543937 k c x) (@lem7543950 x c k)). Qed.
Lemma lem7543952 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7543953 (x : real) (c : nat -> real) (k : real) : (term508 k c x) = (term509 c k).
Proof. exact (MK_COMB (@lem7543952) (@lem7543951 x c k)). Qed.
Lemma lem7544218 (n : nat) (k : real) (c : nat -> real) (x : real) : (term510 n k c x) = (term510 n k c x).
Proof. exact (eq_refl (term510 n k c x)). Qed.
Lemma lem7544219 (n : nat) (k : real) (c : nat -> real) (x : real) : (term492 n k c x) = (term511 n k c x).
Proof. exact (MK_COMB (@lem7543953 x c k) (@lem7544218 n k c x)). Qed.
Lemma lem7544484 (n : nat) (k : real) (c : nat -> real) (x : real) : (term491 n k c x) = (term511 n k c x).
Proof. exact (TRANS (@lem7543924 n k c x) (@lem7544219 n k c x)). Qed.
Lemma lem7544485 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7544486 (n : nat) (k : real) (c : nat -> real) (x : real) : (term512 n k c x) = (term513 n k c x).
Proof. exact (MK_COMB (@lem7544485) (@lem7544484 n k c x)). Qed.
Lemma lem7544751 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7544752 (n : nat) (k : real) (c : nat -> real) (x : real) : ((term491 n k c x) = term10) = ((term511 n k c x) = term10).
Proof. exact (MK_COMB (@lem7544486 n k c x) (@lem7544751)). Qed.
Lemma lem7545019 (n : nat) (k : real) (c : nat -> real) : (term514 n k c) = (term515 n k c).
Proof. exact (fun_ext (fun x : real => @lem7544752 n k c x)). Qed.
Lemma lem7545286 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7545287 (n : nat) (k : real) (c : nat -> real) : (term516 n k c) = (term517 n k c).
Proof. exact (MK_COMB (@lem7545286) (@lem7545019 n k c)). Qed.
Lemma lem7545558 (n : nat) (k : real) (c : nat -> real) : ((term458 n c k) = (term516 n k c)) = ((term486 n c k) = (term517 n k c)).
Proof. exact (MK_COMB (@lem7543784 n c k) (@lem7545287 n k c)). Qed.
Lemma lem7545957 (n : nat) (k : real) (c : nat -> real) : ((term486 n c k) = (term517 n k c)) = ((term458 n c k) = (term516 n k c)).
Proof. exact (SYM (@lem7545558 n k c)). Qed.
Lemma lem7545971 (c : real) (s : real) (k : real) : ((term235 c k s) = term10) = ((real_add c s) = k).
Proof. exact (@lem7542938 c s k (@lem7542937 c s k)). Qed.
Lemma lem7545972 (n : nat) (c : nat -> real) (x : real) (k : real) : ((term511 n k c x) = term10) = ((term518 n k c x) = k).
Proof. exact (@lem7545971 (term477 c) (term510 n k c x) k). Qed.
Lemma lem7545979 (n : nat) (c : nat -> real) (k : real) : (term515 n k c) = (term519 n c k).
Proof. exact (fun_ext (fun x : real => @lem7545972 n c x k)). Qed.
Lemma lem7545980 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7545981 (n : nat) (c : nat -> real) (k : real) : (term517 n k c) = (term520 n c k).
Proof. exact (MK_COMB (@lem7545980) (@lem7545979 n c k)). Qed.
Lemma lem7545986 (n : nat) (c : nat -> real) (k : real) : (term488 n c k) = (term488 n c k).
Proof. exact (eq_refl (term488 n c k)). Qed.
Lemma lem7545987 (n : nat) (c : nat -> real) (k : real) : ((term486 n c k) = (term517 n k c)) = ((term486 n c k) = (term520 n c k)).
Proof. exact (MK_COMB (@lem7545986 n c k) (@lem7545981 n c k)). Qed.
Lemma lem7545990 (n : nat) (k : real) (c : nat -> real) : ((term486 n c k) = (term520 n c k)) = ((term486 n c k) = (term517 n k c)).
Proof. exact (SYM (@lem7545987 n c k)). Qed.
Lemma lem7545991 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7545992 (k : real) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem7545993 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7545994 (c : nat -> real) : (term479 c) = (term479 c).
Proof. exact (eq_refl (term479 c)). Qed.
Lemma lem7545996 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : term223 _132349 f s g.
Proof. exact (EQ_MP (@lem7540420 _132349 f s g) (@lem7540419 _132349 f s g)). Qed.
Lemma lem7545997 (f : nat -> real) (s : nat -> Prop) (g : nat -> real) : term521 f s g.
Proof. exact (@lem7545996 nat f s g). Qed.
Lemma lem7545998 (n : nat) (k : real) (c : nat -> real) (x : real) : term522 n k c x.
Proof. exact (@lem7545997 (term461 c x) (term523 n) (term490 k c x)). Qed.
Lemma lem7546002 (m : nat) (p : nat) (n : nat) : (term210 p m n) = (term211 m p n).
Proof. exact (EQ_MP (@lem7540390 m p n) (@lem7540389 m n p)). Qed.
Lemma lem7546003 (x' : nat) (n : nat) : (term524 x' n) = (term525 x' n).
Proof. exact (@lem7546002 term526 x' n). Qed.
Lemma lem7546006 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7546007 (x' : nat) (n : nat) : (term527 x' n) = (term528 x' n).
Proof. exact (MK_COMB (@lem7546006) (@lem7546003 x' n)). Qed.
Lemma lem7546011 {A B : Type'} (f : A -> B) (y : A) : (term464 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7546012 (f : nat -> real) (y : nat) : (term465 f y) = (f y).
Proof. exact (@lem7546011 nat real f y). Qed.
Lemma lem7546013 (c : nat -> real) (x : real) (x' : nat) : (term529 c x x') = (term468 c x x').
Proof. exact (@lem7546012 (term461 c x) x'). Qed.
Lemma lem7546014 (c : nat -> real) (x : real) (i : nat) : (term468 c x i) = (term469 c x i).
Proof. exact (eq_refl (term468 c x i)). Qed.
Lemma lem7546015 (c : nat -> real) (x : real) : (term470 c x) = (term461 c x).
Proof. exact (fun_ext (fun i : nat => @lem7546014 c x i)). Qed.
Lemma lem7546016 (x' : nat) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem7546017 (c : nat -> real) (x : real) (x' : nat) : (term529 c x x') = (term468 c x x').
Proof. exact (MK_COMB (@lem7546015 c x) (@lem7546016 x')). Qed.
Lemma lem7546018 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7546019 (c : nat -> real) (x : real) (x' : nat) : (term530 c x x') = (term531 c x x').
Proof. exact (MK_COMB (@lem7546018) (@lem7546017 c x x')). Qed.
Lemma lem7546020 (c : nat -> real) (x : real) (x' : nat) : (term468 c x x') = (term469 c x x').
Proof. exact (eq_refl (term468 c x x')). Qed.
Lemma lem7546021 (c : nat -> real) (x : real) (x' : nat) : ((term529 c x x') = (term468 c x x')) = ((term468 c x x') = (term469 c x x')).
Proof. exact (MK_COMB (@lem7546019 c x x') (@lem7546020 c x x')). Qed.
Lemma lem7546022 (c : nat -> real) (x : real) (x' : nat) : (term468 c x x') = (term469 c x x').
Proof. exact (EQ_MP (@lem7546021 c x x') (@lem7546013 c x x')). Qed.
Lemma lem7546023 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7546024 (c : nat -> real) (x : real) (x' : nat) : (term531 c x x') = (term532 c x x').
Proof. exact (MK_COMB (@lem7546023) (@lem7546022 c x x')). Qed.
Lemma lem7546026 {A B : Type'} (f : A -> B) (y : A) : (term464 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7546027 (f : nat -> real) (y : nat) : (term465 f y) = (f y).
Proof. exact (@lem7546026 nat real f y). Qed.
Lemma lem7546028 (k : real) (c : nat -> real) (x : real) (x' : nat) : (term533 k c x x') = (term495 k c x x').
Proof. exact (@lem7546027 (term490 k c x) x'). Qed.
Lemma lem7546029 (k : real) (c : nat -> real) (x : real) (i : nat) : (term495 k c x i) = (term496 k c x i).
Proof. exact (eq_refl (term495 k c x i)). Qed.
Lemma lem7546030 (k : real) (c : nat -> real) (x : real) : (term497 k c x) = (term490 k c x).
Proof. exact (fun_ext (fun i : nat => @lem7546029 k c x i)). Qed.
Lemma lem7546031 (x' : nat) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem7546032 (k : real) (c : nat -> real) (x : real) (x' : nat) : (term533 k c x x') = (term495 k c x x').
Proof. exact (MK_COMB (@lem7546030 k c x) (@lem7546031 x')). Qed.
Lemma lem7546033 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7546034 (k : real) (c : nat -> real) (x : real) (x' : nat) : (term534 k c x x') = (term535 k c x x').
Proof. exact (MK_COMB (@lem7546033) (@lem7546032 k c x x')). Qed.
Lemma lem7546035 (k : real) (c : nat -> real) (x : real) (x' : nat) : (term495 k c x x') = (term496 k c x x').
Proof. exact (eq_refl (term495 k c x x')). Qed.
Lemma lem7546036 (k : real) (c : nat -> real) (x : real) (x' : nat) : ((term533 k c x x') = (term495 k c x x')) = ((term495 k c x x') = (term496 k c x x')).
Proof. exact (MK_COMB (@lem7546034 k c x x') (@lem7546035 k c x x')). Qed.
Lemma lem7546037 (k : real) (c : nat -> real) (x : real) (x' : nat) : (term495 k c x x') = (term496 k c x x').
Proof. exact (EQ_MP (@lem7546036 k c x x') (@lem7546028 k c x x')). Qed.
Lemma lem7546042 (k : real) (c : nat -> real) (x : real) (x' : nat) : ((term468 c x x') = (term495 k c x x')) = ((term469 c x x') = (term496 k c x x')).
Proof. exact (MK_COMB (@lem7546024 c x x') (@lem7546037 k c x x')). Qed.
Lemma lem7546045 (n : nat) (k : real) (c : nat -> real) (x : real) (x' : nat) : (term536 n k c x x') = (term537 n k c x x').
Proof. exact (MK_COMB (@lem7546007 x' n) (@lem7546042 k c x x')). Qed.
Lemma lem7546048 (n : nat) (k : real) (c : nat -> real) (x : real) (x' : nat) : (term537 n k c x x') = (term536 n k c x x').
Proof. exact (SYM (@lem7546045 n k c x x')). Qed.
Lemma lem7546049 (_474 : real) (_475 : Prop) (_476 : real -> Prop) (_477 : real) : (term538 _476 _475 _474 _477) = (term539 _474 _475 _476 _477).
Proof. exact (@lem13473 real _474 _475 _476 _477). Qed.
Lemma lem7546050 (_474 : real) (_475 : Prop) (n : nat) (c : nat -> real) (x : real) (x' : nat) (_477 : real) : (term540 n c x x' _475 _474 _477) = (term541 _474 _475 n c x x' _477).
Proof. exact (@lem7546049 _474 _475 (term542 n c x x') _477). Qed.
Lemma lem7546051 (k : real) (n : nat) (x : real) (c : nat -> real) (x' : nat) : (term543 n x k c x') = (term544 k n x c x').
Proof. exact (@lem7546050 (term504 c k) (x' = (NUMERAL 0)) n c x x' (c x')). Qed.
Lemma lem7546052 (n : nat) (c : nat -> real) (x : real) (x' : nat) : (term545 n x c x') = (term546 n c x x').
Proof. exact (eq_refl (term545 n x c x')). Qed.
Lemma lem7546053 (x' : nat) : (term547 x') = (term547 x').
Proof. exact (eq_refl (term547 x')). Qed.
Lemma lem7546054 (n : nat) (c : nat -> real) (x : real) (x' : nat) : (term548 n x c x') = (term549 n c x x').
Proof. exact (MK_COMB (@lem7546053 x') (@lem7546052 n c x x')). Qed.
Lemma lem7546055 (n : nat) (c : nat -> real) (k : real) (x : real) (x' : nat) : (term550 n x x' c k) = (term551 n c k x x').
Proof. exact (eq_refl (term550 n x x' c k)). Qed.
Lemma lem7546056 (x' : nat) : (term552 x') = (term552 x').
Proof. exact (eq_refl (term552 x')). Qed.
Lemma lem7546057 (n : nat) (c : nat -> real) (k : real) (x : real) (x' : nat) : (term553 n x x' c k) = (term554 n c k x x').
Proof. exact (MK_COMB (@lem7546056 x') (@lem7546055 n c k x x')). Qed.
Lemma lem7546058 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7546059 (n : nat) (c : nat -> real) (k : real) (x : real) (x' : nat) : (term555 n x x' c k) = (term556 n c k x x').
Proof. exact (MK_COMB (@lem7546058) (@lem7546057 n c k x x')). Qed.
Lemma lem7546060 (k : real) (n : nat) (c : nat -> real) (x : real) (x' : nat) : (term544 k n x c x') = (term557 k n c x x').
Proof. exact (MK_COMB (@lem7546059 n c k x x') (@lem7546054 n c x x')). Qed.
Lemma lem7546061 (n : nat) (k : real) (c : nat -> real) (x : real) (x' : nat) : (term543 n x k c x') = (term537 n k c x x').
Proof. exact (eq_refl (term543 n x k c x')). Qed.
Lemma lem7546062 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7546063 (n : nat) (k : real) (c : nat -> real) (x : real) (x' : nat) : (term558 n x k c x') = (term559 n k c x x').
Proof. exact (MK_COMB (@lem7546062) (@lem7546061 n k c x x')). Qed.
Lemma lem7546064 (k : real) (n : nat) (c : nat -> real) (x : real) (x' : nat) : ((term543 n x k c x') = (term544 k n x c x')) = ((term537 n k c x x') = (term557 k n c x x')).
Proof. exact (MK_COMB (@lem7546063 n k c x x') (@lem7546060 k n c x x')). Qed.
Lemma lem7546065 (k : real) (n : nat) (c : nat -> real) (x : real) (x' : nat) : (term537 n k c x x') = (term557 k n c x x').
Proof. exact (EQ_MP (@lem7546064 k n c x x') (@lem7546051 k n x c x')). Qed.
Lemma lem7546066 (n : nat) (k : real) (c : nat -> real) (x : real) (x' : nat) : (term557 k n c x x') = (term537 n k c x x').
Proof. exact (SYM (@lem7546065 k n c x x')). Qed.
Lemma lem7546067 (x' : nat) (h1 : x' = (NUMERAL 0)) : x' = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem7546373 : term560.
Proof. exact (EQ_MP (@lem517422) (@lem519779)). Qed.
Lemma lem7546374 : term561.
Proof. exact (proj2 (@lem7546373)). Qed.
Lemma lem7546375 : term562.
Proof. exact (proj2 (@lem7546374)). Qed.
Lemma lem7546376 : term563.
Proof. exact (proj2 (@lem7546375)). Qed.
Lemma lem7546418 : term564.
Proof. exact (proj1 (@lem7546376)). Qed.
Lemma lem7546419 (n : nat) : term565 n.
Proof. exact (@lem7546418 n). Qed.
Lemma lem7546420 (n : nat) : (term565 n) = ((term566 n) = False).
Proof. exact (eq_refl (term565 n)). Qed.
Lemma lem7546427 : term567.
Proof. exact (proj1 (@lem7546373)). Qed.
Lemma lem7546428 (m : nat) : term568 m.
Proof. exact (@lem7546427 m). Qed.
Lemma lem7546429 (m : nat) : (term568 m) = (term569 m).
Proof. exact (eq_refl (term568 m)). Qed.
Lemma lem7546430 (m : nat) : term569 m.
Proof. exact (EQ_MP (@lem7546429 m) (@lem7546428 m)). Qed.
Lemma lem7546431 (m : nat) (n : nat) : term570 m n.
Proof. exact (@lem7546430 m n). Qed.
Lemma lem7546432 (m : nat) (n : nat) : (term570 m n) = ((term571 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term570 m n)). Qed.
Lemma lem7546649 : term572.
Proof. exact (EQ_MP (@lem513870) (@lem514290)). Qed.
Lemma lem7546650 : term573.
Proof. exact (proj2 (@lem7546649)). Qed.
Lemma lem7546651 : term574.
Proof. exact (proj2 (@lem7546650)). Qed.
Lemma lem7546652 : term575.
Proof. exact (proj2 (@lem7546651)). Qed.
Lemma lem7546694 : term576.
Proof. exact (proj1 (@lem7546652)). Qed.
Lemma lem7546695 (n : nat) : term577 n.
Proof. exact (@lem7546694 n). Qed.
Lemma lem7546696 (n : nat) : (term577 n) = ((term578 n) = (BIT1 n)).
Proof. exact (eq_refl (term577 n)). Qed.
Lemma lem7546703 : term579.
Proof. exact (proj1 (@lem7546649)). Qed.
Lemma lem7546704 (m : nat) : term580 m.
Proof. exact (@lem7546703 m). Qed.
Lemma lem7546705 (m : nat) : (term580 m) = (term581 m).
Proof. exact (eq_refl (term580 m)). Qed.
Lemma lem7546706 (m : nat) : term581 m.
Proof. exact (EQ_MP (@lem7546705 m) (@lem7546704 m)). Qed.
Lemma lem7546707 (m : nat) (n : nat) : term582 m n.
Proof. exact (@lem7546706 m n). Qed.
Lemma lem7546708 (m : nat) (n : nat) : (term582 m n) = ((term583 m n) = (term584 m n)).
Proof. exact (eq_refl (term582 m n)). Qed.
Lemma lem7546750 (m : nat) (n : nat) : (term583 m n) = (term584 m n).
Proof. exact (EQ_MP (@lem7546708 m n) (@lem7546707 m n)). Qed.
Lemma lem7546751 : term526 = term585.
Proof. exact (@lem7546750 0 (BIT1 0)). Qed.
Lemma lem7546753 (n : nat) : (term578 n) = (BIT1 n).
Proof. exact (EQ_MP (@lem7546696 n) (@lem7546695 n)). Qed.
Lemma lem7546754 : term586 = (BIT1 0).
Proof. exact (@lem7546753 0). Qed.
Lemma lem7546755 : NUMERAL = NUMERAL.
Proof. exact (eq_refl NUMERAL). Qed.
Lemma lem7546756 : term585 = term253.
Proof. exact (MK_COMB (@lem7546755) (@lem7546754)). Qed.
Lemma lem7546757 : term526 = term253.
Proof. exact (TRANS (@lem7546751) (@lem7546756)). Qed.
Lemma lem7546758 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem7546759 : term587 = term588.
Proof. exact (MK_COMB (@lem7546758) (@lem7546757)). Qed.
Lemma lem7546761 (x' : nat) (h1 : x' = (NUMERAL 0)) : x' = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem7546762 (x' : nat) (h1 : x' = (NUMERAL 0)) : (term589 x') = term590.
Proof. exact (MK_COMB (@lem7546759) (@lem7546761 x' h1)). Qed.
Lemma lem7546764 (m : nat) (n : nat) : (term571 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem7546432 m n) (@lem7546431 m n)). Qed.
Lemma lem7546765 : term590 = term591.
Proof. exact (@lem7546764 (BIT1 0) 0). Qed.
Lemma lem7546767 (n : nat) : (term566 n) = False.
Proof. exact (EQ_MP (@lem7546420 n) (@lem7546419 n)). Qed.
Lemma lem7546768 : term591 = False.
Proof. exact (@lem7546767 0). Qed.
Lemma lem7546769 : term590 = False.
Proof. exact (TRANS (@lem7546765) (@lem7546768)). Qed.
Lemma lem7546770 (x' : nat) (h1 : x' = (NUMERAL 0)) : (term589 x') = False.
Proof. exact (TRANS (@lem7546762 x' h1) (@lem7546769)). Qed.
Lemma lem7546771 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7546772 (x' : nat) (h1 : x' = (NUMERAL 0)) : (term592 x') = (and False).
Proof. exact (MK_COMB (@lem7546771) (@lem7546770 x' h1)). Qed.
Lemma lem7546774 (x' : nat) (h1 : x' = (NUMERAL 0)) : x' = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem7546775 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem7546776 (x' : nat) (h1 : x' = (NUMERAL 0)) : (Peano.le x') = term593.
Proof. exact (MK_COMB (@lem7546775) (@lem7546774 x' h1)). Qed.
Lemma lem7546777 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7546778 (n : nat) (x' : nat) (h1 : x' = (NUMERAL 0)) : (Peano.le x' n) = (term12 n).
Proof. exact (MK_COMB (@lem7546776 x' h1) (@lem7546777 n)). Qed.
Lemma lem7546779 (n : nat) (x' : nat) (h1 : x' = (NUMERAL 0)) : (term525 x' n) = (term594 n).
Proof. exact (MK_COMB (@lem7546772 x' h1) (@lem7546778 n x' h1)). Qed.
Lemma lem7546781 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem7546782 (n : nat) : (term594 n) = False.
Proof. exact (@lem7546781 (term12 n)). Qed.
Lemma lem7546783 (n : nat) (x' : nat) (h1 : x' = (NUMERAL 0)) : (term525 x' n) = False.
Proof. exact (TRANS (@lem7546779 n x' h1) (@lem7546782 n)). Qed.
Lemma lem7546784 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7546785 (n : nat) (x' : nat) (h1 : x' = (NUMERAL 0)) : (term528 x' n) = (imp False).
Proof. exact (MK_COMB (@lem7546784) (@lem7546783 n x' h1)). Qed.
Lemma lem7546789 (x' : nat) (h1 : x' = (NUMERAL 0)) : x' = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem7546790 (c : nat -> real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem7546791 (c : nat -> real) (x' : nat) (h1 : x' = (NUMERAL 0)) : (c x') = (term477 c).
Proof. exact (MK_COMB (@lem7546790 c) (@lem7546789 x' h1)). Qed.
Lemma lem7546792 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7546793 (c : nat -> real) (x' : nat) (h1 : x' = (NUMERAL 0)) : (term595 c x') = (term475 c).
Proof. exact (MK_COMB (@lem7546792) (@lem7546791 c x' h1)). Qed.
Lemma lem7546795 (x' : nat) (h1 : x' = (NUMERAL 0)) : x' = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem7546796 (x : real) : (real_pow x) = (real_pow x).
Proof. exact (eq_refl (real_pow x)). Qed.
Lemma lem7546797 (x : real) (x' : nat) (h1 : x' = (NUMERAL 0)) : (real_pow x x') = (term474 x).
Proof. exact (MK_COMB (@lem7546796 x) (@lem7546795 x' h1)). Qed.
Lemma lem7546798 (c : nat -> real) (x : real) (x' : nat) (h1 : x' = (NUMERAL 0)) : (term469 c x x') = (term473 c x).
Proof. exact (MK_COMB (@lem7546793 c x' h1) (@lem7546797 x x' h1)). Qed.
Lemma lem7546799 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7546800 (c : nat -> real) (x : real) (x' : nat) (h1 : x' = (NUMERAL 0)) : (term532 c x x') = (term596 c x).
Proof. exact (MK_COMB (@lem7546799) (@lem7546798 c x x' h1)). Qed.
Lemma lem7546802 (x' : nat) (h1 : x' = (NUMERAL 0)) : x' = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem7546803 (x : real) : (real_pow x) = (real_pow x).
Proof. exact (eq_refl (real_pow x)). Qed.
Lemma lem7546804 (x : real) (x' : nat) (h1 : x' = (NUMERAL 0)) : (real_pow x x') = (term474 x).
Proof. exact (MK_COMB (@lem7546803 x) (@lem7546802 x' h1)). Qed.
Lemma lem7546805 (c : nat -> real) (k : real) : (term506 c k) = (term506 c k).
Proof. exact (eq_refl (term506 c k)). Qed.
Lemma lem7546806 (c : nat -> real) (k : real) (x : real) (x' : nat) (h1 : x' = (NUMERAL 0)) : (term597 c k x x') = (term598 c k x).
Proof. exact (MK_COMB (@lem7546805 c k) (@lem7546804 x x' h1)). Qed.
Lemma lem7546807 (c : nat -> real) (k : real) (x : real) (x' : nat) (h1 : x' = (NUMERAL 0)) : ((term469 c x x') = (term597 c k x x')) = ((term473 c x) = (term598 c k x)).
Proof. exact (MK_COMB (@lem7546800 c x x' h1) (@lem7546806 c k x x' h1)). Qed.
Lemma lem7546810 (n : nat) (c : nat -> real) (k : real) (x : real) (x' : nat) (h1 : x' = (NUMERAL 0)) : (term551 n c k x x') = (term599 c k x).
Proof. exact (MK_COMB (@lem7546785 n x' h1) (@lem7546807 c k x x' h1)). Qed.
Lemma lem7546812 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem7546813 (c : nat -> real) (k : real) (x : real) : (term599 c k x) = True.
Proof. exact (@lem7546812 ((term473 c x) = (term598 c k x))). Qed.
Lemma lem7546814 (n : nat) (c : nat -> real) (k : real) (x : real) (x' : nat) (h1 : x' = (NUMERAL 0)) : (term551 n c k x x') = True.
Proof. exact (TRANS (@lem7546810 n c k x x' h1) (@lem7546813 c k x)). Qed.
Lemma lem7546815 (n : nat) (c : nat -> real) (k : real) (x : real) (x' : nat) (h1 : x' = (NUMERAL 0)) : True = (term551 n c k x x').
Proof. exact (SYM (@lem7546814 n c k x x' h1)). Qed.
Lemma lem7547365 : term572.
Proof. exact (EQ_MP (@lem513870) (@lem514290)). Qed.
Lemma lem7547366 : term573.
Proof. exact (proj2 (@lem7547365)). Qed.
Lemma lem7547367 : term574.
Proof. exact (proj2 (@lem7547366)). Qed.
Lemma lem7547368 : term575.
Proof. exact (proj2 (@lem7547367)). Qed.
Lemma lem7547410 : term576.
Proof. exact (proj1 (@lem7547368)). Qed.
Lemma lem7547411 (n : nat) : term577 n.
Proof. exact (@lem7547410 n). Qed.
Lemma lem7547412 (n : nat) : (term577 n) = ((term578 n) = (BIT1 n)).
Proof. exact (eq_refl (term577 n)). Qed.
Lemma lem7547419 : term579.
Proof. exact (proj1 (@lem7547365)). Qed.
Lemma lem7547420 (m : nat) : term580 m.
Proof. exact (@lem7547419 m). Qed.
Lemma lem7547421 (m : nat) : (term580 m) = (term581 m).
Proof. exact (eq_refl (term580 m)). Qed.
Lemma lem7547422 (m : nat) : term581 m.
Proof. exact (EQ_MP (@lem7547421 m) (@lem7547420 m)). Qed.
Lemma lem7547423 (m : nat) (n : nat) : term582 m n.
Proof. exact (@lem7547422 m n). Qed.
Lemma lem7547424 (m : nat) (n : nat) : (term582 m n) = ((term583 m n) = (term584 m n)).
Proof. exact (eq_refl (term582 m n)). Qed.
Lemma lem7547479 (m : nat) (n : nat) : (term583 m n) = (term584 m n).
Proof. exact (EQ_MP (@lem7547424 m n) (@lem7547423 m n)). Qed.
Lemma lem7547480 : term526 = term585.
Proof. exact (@lem7547479 0 (BIT1 0)). Qed.
Lemma lem7547482 (n : nat) : (term578 n) = (BIT1 n).
Proof. exact (EQ_MP (@lem7547412 n) (@lem7547411 n)). Qed.
Lemma lem7547483 : term586 = (BIT1 0).
Proof. exact (@lem7547482 0). Qed.
Lemma lem7547484 : NUMERAL = NUMERAL.
Proof. exact (eq_refl NUMERAL). Qed.
Lemma lem7547485 : term585 = term253.
Proof. exact (MK_COMB (@lem7547484) (@lem7547483)). Qed.
Lemma lem7547486 : term526 = term253.
Proof. exact (TRANS (@lem7547480) (@lem7547485)). Qed.
Lemma lem7547487 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem7547488 : term587 = term588.
Proof. exact (MK_COMB (@lem7547487) (@lem7547486)). Qed.
Lemma lem7547489 (x' : nat) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem7547490 (x' : nat) : (term589 x') = (term600 x').
Proof. exact (MK_COMB (@lem7547488) (@lem7547489 x')). Qed.
Lemma lem7547491 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7547492 (x' : nat) : (term592 x') = (term601 x').
Proof. exact (MK_COMB (@lem7547491) (@lem7547490 x')). Qed.
Lemma lem7547493 (x' : nat) (n : nat) : (Peano.le x' n) = (Peano.le x' n).
Proof. exact (eq_refl (Peano.le x' n)). Qed.
Lemma lem7547494 (x' : nat) (n : nat) : (term525 x' n) = (term602 x' n).
Proof. exact (MK_COMB (@lem7547492 x') (@lem7547493 x' n)). Qed.
Lemma lem7547497 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7547498 (x' : nat) (n : nat) : (term528 x' n) = (term603 x' n).
Proof. exact (MK_COMB (@lem7547497) (@lem7547494 x' n)). Qed.
Lemma lem7547500 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7547501 (x : real) : (x = x) = True.
Proof. exact (@lem7547500 real x). Qed.
Lemma lem7547502 (c : nat -> real) (x : real) (x' : nat) : ((term469 c x x') = (term469 c x x')) = True.
Proof. exact (@lem7547501 (term469 c x x')). Qed.
Lemma lem7547503 (c : nat -> real) (x : real) (x' : nat) (n : nat) : (term546 n c x x') = (term604 x' n).
Proof. exact (MK_COMB (@lem7547498 x' n) (@lem7547502 c x x')). Qed.
Lemma lem7547505 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7547506 (x' : nat) (n : nat) : (term604 x' n) = True.
Proof. exact (@lem7547505 (term602 x' n)). Qed.
Lemma lem7547507 (n : nat) (c : nat -> real) (x : real) (x' : nat) : (term546 n c x x') = True.
Proof. exact (TRANS (@lem7547503 c x x' n) (@lem7547506 x' n)). Qed.
Lemma lem7547508 (n : nat) (c : nat -> real) (x : real) (x' : nat) : True = (term546 n c x x').
Proof. exact (SYM (@lem7547507 n c x x')). Qed.
Lemma lem7547510 (n : nat) (c : nat -> real) (x : real) (x' : nat) : term546 n c x x'.
Proof. exact (EQ_MP (@lem7547508 n c x x') (@lem0)). Qed.
Lemma lem7547511 (n : nat) (c : nat -> real) (x : real) (x' : nat) : term549 n c x x'.
Proof. exact (fun h0 : term45 x' => @lem7547510 n c x x'). Qed.
Lemma lem7547512 (n : nat) (c : nat -> real) (k : real) (x : real) (x' : nat) (h1 : x' = (NUMERAL 0)) : term551 n c k x x'.
Proof. exact (EQ_MP (@lem7546815 n c k x x' h1) (@lem0)). Qed.
Lemma lem7547513 (n : nat) (c : nat -> real) (k : real) (x : real) (x' : nat) (h1 : x' = (NUMERAL 0)) : (x' = (NUMERAL 0)) = (term551 n c k x x').
Proof. exact (prop_ext (fun h2 : x' = (NUMERAL 0) => @lem7547512 n c k x x' h1) (fun h2 : term551 n c k x x' => @lem7546067 x' h1)). Qed.
Lemma lem7547514 (n : nat) (c : nat -> real) (k : real) (x : real) (x' : nat) (h1 : x' = (NUMERAL 0)) : term551 n c k x x'.
Proof. exact (EQ_MP (@lem7547513 n c k x x' h1) (@lem7546067 x' h1)). Qed.
Lemma lem7547515 (n : nat) (c : nat -> real) (k : real) (x : real) (x' : nat) : term554 n c k x x'.
Proof. exact (fun h0 : x' = (NUMERAL 0) => @lem7547514 n c k x x' h0). Qed.
Lemma lem7547516 (k : real) (n : nat) (c : nat -> real) (x : real) (x' : nat) : term557 k n c x x'.
Proof. exact (conj (@lem7547515 n c k x x') (@lem7547511 n c x x')). Qed.
Lemma lem7547517 (n : nat) (k : real) (c : nat -> real) (x : real) (x' : nat) : term537 n k c x x'.
Proof. exact (EQ_MP (@lem7546066 n k c x x') (@lem7547516 k n c x x')). Qed.
Lemma lem7547518 (n : nat) (k : real) (c : nat -> real) (x : real) (x' : nat) : term536 n k c x x'.
Proof. exact (EQ_MP (@lem7546048 n k c x x') (@lem7547517 n k c x x')). Qed.
Lemma lem7547523 (n : nat) (k : real) (c : nat -> real) (x : real) : term605 n k c x.
Proof. exact (fun x' : nat => @lem7547518 n k c x x'). Qed.
Lemma lem7547524 (n : nat) (k : real) (c : nat -> real) (x : real) : (term480 n c x) = (term510 n k c x).
Proof. exact (@lem7545998 n k c x (@lem7547523 n k c x)). Qed.
Lemma lem7547525 (n : nat) (k : real) (c : nat -> real) (x : real) : (term481 n c x) = (term518 n k c x).
Proof. exact (MK_COMB (@lem7545994 c) (@lem7547524 n k c x)). Qed.
Lemma lem7547526 (n : nat) (k : real) (c : nat -> real) (x : real) : (term483 n c x) = (term606 n k c x).
Proof. exact (MK_COMB (@lem7545993) (@lem7547525 n k c x)). Qed.
Lemma lem7547527 (n : nat) (c : nat -> real) (x : real) (k : real) : ((term481 n c x) = k) = ((term518 n k c x) = k).
Proof. exact (MK_COMB (@lem7547526 n k c x) (@lem7545992 k)). Qed.
Lemma lem7547530 (n : nat) (c : nat -> real) (k : real) : (term485 n c k) = (term519 n c k).
Proof. exact (fun_ext (fun x : real => @lem7547527 n c x k)). Qed.
Lemma lem7547531 (n : nat) (c : nat -> real) (k : real) : (term486 n c k) = (term520 n c k).
Proof. exact (MK_COMB (@lem7545991) (@lem7547530 n c k)). Qed.
Lemma lem7547532 (n : nat) (k : real) (c : nat -> real) : (term486 n c k) = (term517 n k c).
Proof. exact (EQ_MP (@lem7545990 n k c) (@lem7547531 n c k)). Qed.
Lemma lem7547533 (n : nat) (k : real) (c : nat -> real) : (term458 n c k) = (term516 n k c).
Proof. exact (EQ_MP (@lem7545957 n k c) (@lem7547532 n k c)). Qed.
Lemma lem7547537 (n : nat) (c : nat -> real) : (term215 n c) = (term216 n c).
Proof. exact (EQ_MP (@lem7540381 n c) (@lem7540380 n c)). Qed.
Lemma lem7547538 (n : nat) (k : real) (c : nat -> real) : (term607 n k c) = (term608 n k c).
Proof. exact (@lem7547537 n (term609 k c)). Qed.
Lemma lem7547539 (k : real) (c : nat -> real) (i : nat) : (term610 k c i) = (term611 k c i).
Proof. exact (eq_refl (term610 k c i)). Qed.
Lemma lem7547540 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7547541 (k : real) (c : nat -> real) (i : nat) : (term612 k c i) = (term613 k c i).
Proof. exact (MK_COMB (@lem7547540) (@lem7547539 k c i)). Qed.
Lemma lem7547542 (x : real) (i : nat) : (real_pow x i) = (real_pow x i).
Proof. exact (eq_refl (real_pow x i)). Qed.
Lemma lem7547543 (k : real) (c : nat -> real) (x : real) (i : nat) : (term614 k c x i) = (term496 k c x i).
Proof. exact (MK_COMB (@lem7547541 k c i) (@lem7547542 x i)). Qed.
Lemma lem7547544 (k : real) (c : nat -> real) (x : real) : (term615 k c x) = (term490 k c x).
Proof. exact (fun_ext (fun i : nat => @lem7547543 k c x i)). Qed.
Lemma lem7547545 (n : nat) : (term616 n) = (term616 n).
Proof. exact (eq_refl (term616 n)). Qed.
Lemma lem7547546 (n : nat) (k : real) (c : nat -> real) (x : real) : (term617 n k c x) = (term491 n k c x).
Proof. exact (MK_COMB (@lem7547545 n) (@lem7547544 k c x)). Qed.
Lemma lem7547547 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7547548 (n : nat) (k : real) (c : nat -> real) (x : real) : (term618 n k c x) = (term512 n k c x).
Proof. exact (MK_COMB (@lem7547547) (@lem7547546 n k c x)). Qed.
Lemma lem7547549 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7547550 (n : nat) (k : real) (c : nat -> real) (x : real) : ((term617 n k c x) = term10) = ((term491 n k c x) = term10).
Proof. exact (MK_COMB (@lem7547548 n k c x) (@lem7547549)). Qed.
Lemma lem7547551 (n : nat) (k : real) (c : nat -> real) : (term619 n k c) = (term514 n k c).
Proof. exact (fun_ext (fun x : real => @lem7547550 n k c x)). Qed.
Lemma lem7547552 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7547553 (n : nat) (k : real) (c : nat -> real) : (term607 n k c) = (term516 n k c).
Proof. exact (MK_COMB (@lem7547552) (@lem7547551 n k c)). Qed.
Lemma lem7547554 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7547555 (n : nat) (k : real) (c : nat -> real) : (term620 n k c) = (term621 n k c).
Proof. exact (MK_COMB (@lem7547554) (@lem7547553 n k c)). Qed.
Lemma lem7547556 (k : real) (c : nat -> real) (i : nat) : (term610 k c i) = (term611 k c i).
Proof. exact (eq_refl (term610 k c i)). Qed.
Lemma lem7547557 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7547558 (k : real) (c : nat -> real) (i : nat) : (term622 k c i) = (term623 k c i).
Proof. exact (MK_COMB (@lem7547557) (@lem7547556 k c i)). Qed.
Lemma lem7547559 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7547560 (k : real) (c : nat -> real) (i : nat) : ((term610 k c i) = term10) = ((term611 k c i) = term10).
Proof. exact (MK_COMB (@lem7547558 k c i) (@lem7547559)). Qed.
Lemma lem7547561 (i : nat) (n : nat) : (term624 i n) = (term624 i n).
Proof. exact (eq_refl (term624 i n)). Qed.
Lemma lem7547562 (n : nat) (k : real) (c : nat -> real) (i : nat) : (term625 n k c i) = (term626 n k c i).
Proof. exact (MK_COMB (@lem7547561 i n) (@lem7547560 k c i)). Qed.
Lemma lem7547563 (n : nat) (k : real) (c : nat -> real) : (term627 n k c) = (term628 n k c).
Proof. exact (fun_ext (fun i : nat => @lem7547562 n k c i)). Qed.
Lemma lem7547564 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7547565 (n : nat) (k : real) (c : nat -> real) : (term608 n k c) = (term629 n k c).
Proof. exact (MK_COMB (@lem7547564) (@lem7547563 n k c)). Qed.
Lemma lem7547566 (n : nat) (k : real) (c : nat -> real) : ((term607 n k c) = (term608 n k c)) = ((term516 n k c) = (term629 n k c)).
Proof. exact (MK_COMB (@lem7547555 n k c) (@lem7547565 n k c)). Qed.
Lemma lem7547567 (n : nat) (k : real) (c : nat -> real) : (term516 n k c) = (term629 n k c).
Proof. exact (EQ_MP (@lem7547566 n k c) (@lem7547538 n k c)). Qed.
Lemma lem7547575 (m : nat) (p : nat) (n : nat) : (term210 p m n) = (term211 m p n).
Proof. exact (EQ_MP (@lem7540375 m p n) (@lem7540374 m n p)). Qed.
Lemma lem7547576 (i : nat) (n : nat) : (term630 i n) = (term631 i n).
Proof. exact (@lem7547575 (NUMERAL 0) i n). Qed.
Lemma lem7547580 (n : nat) : (term12 n) = True.
Proof. exact (EQ_MP (@lem7540366 n) (@lem7540365 n)). Qed.
Lemma lem7547581 (i : nat) : (term12 i) = True.
Proof. exact (@lem7547580 i). Qed.
Lemma lem7547582 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7547583 (i : nat) : (term632 i) = (and True).
Proof. exact (MK_COMB (@lem7547582) (@lem7547581 i)). Qed.
Lemma lem7547584 (i : nat) (n : nat) : (Peano.le i n) = (Peano.le i n).
Proof. exact (eq_refl (Peano.le i n)). Qed.
Lemma lem7547585 (i : nat) (n : nat) : (term631 i n) = (term633 i n).
Proof. exact (MK_COMB (@lem7547583 i) (@lem7547584 i n)). Qed.
Lemma lem7547587 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7547588 (i : nat) (n : nat) : (term633 i n) = (Peano.le i n).
Proof. exact (@lem7547587 (Peano.le i n)). Qed.
Lemma lem7547589 (i : nat) (n : nat) : (term631 i n) = (Peano.le i n).
Proof. exact (TRANS (@lem7547585 i n) (@lem7547588 i n)). Qed.
Lemma lem7547590 (i : nat) (n : nat) : (term630 i n) = (Peano.le i n).
Proof. exact (TRANS (@lem7547576 i n) (@lem7547589 i n)). Qed.
Lemma lem7547591 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7547592 (i : nat) (n : nat) : (term624 i n) = (term634 i n).
Proof. exact (MK_COMB (@lem7547591) (@lem7547590 i n)). Qed.
Lemma lem7547599 (k : real) (c : nat -> real) (i : nat) : ((term611 k c i) = term10) = ((term611 k c i) = term10).
Proof. exact (eq_refl ((term611 k c i) = term10)). Qed.
Lemma lem7547600 (n : nat) (k : real) (c : nat -> real) (i : nat) : (term626 n k c i) = (term635 n k c i).
Proof. exact (MK_COMB (@lem7547592 i n) (@lem7547599 k c i)). Qed.
Lemma lem7547603 (n : nat) (k : real) (c : nat -> real) : (term628 n k c) = (term636 n k c).
Proof. exact (fun_ext (fun i : nat => @lem7547600 n k c i)). Qed.
Lemma lem7547604 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7547605 (n : nat) (k : real) (c : nat -> real) : (term629 n k c) = (term637 n k c).
Proof. exact (MK_COMB (@lem7547604) (@lem7547603 n k c)). Qed.
Lemma lem7547610 (n : nat) (k : real) (c : nat -> real) : (term516 n k c) = (term637 n k c).
Proof. exact (TRANS (@lem7547567 n k c) (@lem7547605 n k c)). Qed.
Lemma lem7547611 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7547612 (n : nat) (k : real) (c : nat -> real) : (term621 n k c) = (term638 n k c).
Proof. exact (MK_COMB (@lem7547611) (@lem7547610 n k c)). Qed.
Lemma lem7547624 (m : nat) (p : nat) (n : nat) : (term210 p m n) = (term211 m p n).
Proof. exact (EQ_MP (@lem7540375 m p n) (@lem7540374 m n p)). Qed.
Lemma lem7547625 (i : nat) (n : nat) : (term639 i n) = (term602 i n).
Proof. exact (@lem7547624 term253 i n). Qed.
Lemma lem7547628 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7547629 (i : nat) (n : nat) : (term640 i n) = (term603 i n).
Proof. exact (MK_COMB (@lem7547628) (@lem7547625 i n)). Qed.
Lemma lem7547632 (c : nat -> real) (i : nat) : ((c i) = term10) = ((c i) = term10).
Proof. exact (eq_refl ((c i) = term10)). Qed.
Lemma lem7547633 (n : nat) (c : nat -> real) (i : nat) : (term641 n c i) = (term642 n c i).
Proof. exact (MK_COMB (@lem7547629 i n) (@lem7547632 c i)). Qed.
Lemma lem7547636 (n : nat) (c : nat -> real) : (term643 n c) = (term644 n c).
Proof. exact (fun_ext (fun i : nat => @lem7547633 n c i)). Qed.
Lemma lem7547637 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7547638 (n : nat) (c : nat -> real) : (term645 n c) = (term646 n c).
Proof. exact (MK_COMB (@lem7547637) (@lem7547636 n c)). Qed.
Lemma lem7547643 (c : nat -> real) (k : real) : (term647 c k) = (term647 c k).
Proof. exact (eq_refl (term647 c k)). Qed.
Lemma lem7547644 (k : real) (n : nat) (c : nat -> real) : (term459 k n c) = (term648 k n c).
Proof. exact (MK_COMB (@lem7547643 c k) (@lem7547638 n c)). Qed.
Lemma lem7547647 (k : real) (n : nat) (c : nat -> real) : ((term516 n k c) = (term459 k n c)) = ((term637 n k c) = (term648 k n c)).
Proof. exact (MK_COMB (@lem7547612 n k c) (@lem7547644 k n c)). Qed.
Lemma lem7547650 (k : real) (n : nat) (c : nat -> real) : ((term637 n k c) = (term648 k n c)) = ((term516 n k c) = (term459 k n c)).
Proof. exact (SYM (@lem7547647 k n c)). Qed.
Lemma lem7547652 (P : nat -> Prop) : (term14 P) = (term15 P).
Proof. exact (EQ_MP (@lem7539567 P) (@lem7540361 P)). Qed.
Lemma lem7547653 (n : nat) (k : real) (c : nat -> real) : (term649 n k c) = (term650 n k c).
Proof. exact (@lem7547652 (term636 n k c)). Qed.
Lemma lem7547654 (n : nat) (k : real) (c : nat -> real) (i : nat) : (term651 n k c i) = (term635 n k c i).
Proof. exact (eq_refl (term651 n k c i)). Qed.
Lemma lem7547655 (n : nat) (k : real) (c : nat -> real) : (term652 n k c) = (term636 n k c).
Proof. exact (fun_ext (fun i : nat => @lem7547654 n k c i)). Qed.
Lemma lem7547656 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7547657 (n : nat) (k : real) (c : nat -> real) : (term649 n k c) = (term637 n k c).
Proof. exact (MK_COMB (@lem7547656) (@lem7547655 n k c)). Qed.
Lemma lem7547658 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7547659 (n : nat) (k : real) (c : nat -> real) : (term653 n k c) = (term638 n k c).
Proof. exact (MK_COMB (@lem7547658) (@lem7547657 n k c)). Qed.
Lemma lem7547660 (n : nat) (k : real) (c : nat -> real) : (term654 n k c) = (term655 n k c).
Proof. exact (eq_refl (term654 n k c)). Qed.
Lemma lem7547661 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7547662 (n : nat) (k : real) (c : nat -> real) : (term656 n k c) = (term657 n k c).
Proof. exact (MK_COMB (@lem7547661) (@lem7547660 n k c)). Qed.
Lemma lem7547663 (n : nat) (k : real) (c : nat -> real) (i : nat) : (term651 n k c i) = (term635 n k c i).
Proof. exact (eq_refl (term651 n k c i)). Qed.
Lemma lem7547664 (i : nat) : (term547 i) = (term547 i).
Proof. exact (eq_refl (term547 i)). Qed.
Lemma lem7547665 (n : nat) (k : real) (c : nat -> real) (i : nat) : (term658 n k c i) = (term659 n k c i).
Proof. exact (MK_COMB (@lem7547664 i) (@lem7547663 n k c i)). Qed.
Lemma lem7547666 (n : nat) (k : real) (c : nat -> real) : (term660 n k c) = (term661 n k c).
Proof. exact (fun_ext (fun i : nat => @lem7547665 n k c i)). Qed.
Lemma lem7547667 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7547668 (n : nat) (k : real) (c : nat -> real) : (term662 n k c) = (term663 n k c).
Proof. exact (MK_COMB (@lem7547667) (@lem7547666 n k c)). Qed.
Lemma lem7547669 (n : nat) (k : real) (c : nat -> real) : (term650 n k c) = (term664 n k c).
Proof. exact (MK_COMB (@lem7547662 n k c) (@lem7547668 n k c)). Qed.
Lemma lem7547670 (n : nat) (k : real) (c : nat -> real) : ((term649 n k c) = (term650 n k c)) = ((term637 n k c) = (term664 n k c)).
Proof. exact (MK_COMB (@lem7547659 n k c) (@lem7547669 n k c)). Qed.
Lemma lem7547671 (n : nat) (k : real) (c : nat -> real) : (term637 n k c) = (term664 n k c).
Proof. exact (EQ_MP (@lem7547670 n k c) (@lem7547653 n k c)). Qed.
Lemma lem7547672 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7547673 (n : nat) (k : real) (c : nat -> real) : (term638 n k c) = (term665 n k c).
Proof. exact (MK_COMB (@lem7547672) (@lem7547671 n k c)). Qed.
Lemma lem7547674 (k : real) (n : nat) (c : nat -> real) : (term648 k n c) = (term648 k n c).
Proof. exact (eq_refl (term648 k n c)). Qed.
Lemma lem7547675 (k : real) (n : nat) (c : nat -> real) : ((term637 n k c) = (term648 k n c)) = ((term664 n k c) = (term648 k n c)).
Proof. exact (MK_COMB (@lem7547673 n k c) (@lem7547674 k n c)). Qed.
Lemma lem7547676 (k : real) (n : nat) (c : nat -> real) : ((term664 n k c) = (term648 k n c)) = ((term637 n k c) = (term648 k n c)).
Proof. exact (SYM (@lem7547675 k n c)). Qed.
Lemma lem7547684 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term666 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7547685 (p : Prop) (q : Prop) (p' : Prop) : term667 p q p'.
Proof. exact (fun q' : Prop => @lem7547684 p q p' q'). Qed.
Lemma lem7547686 (p : Prop) (q : Prop) : term668 p q.
Proof. exact (fun p' : Prop => @lem7547685 p q p'). Qed.
Lemma lem7547687 (n : nat) (k : real) (c : nat -> real) : term669 n k c.
Proof. exact (@lem7547686 (term12 n) ((term503 k c) = term10)). Qed.
Lemma lem7547688 (n : nat) (k : real) (c : nat -> real) (p' : Prop) : term670 n k c p'.
Proof. exact (@lem7547687 n k c p'). Qed.
Lemma lem7547689 (n : nat) (k : real) (c : nat -> real) (p' : Prop) : (term670 n k c p') = (term671 n k c p').
Proof. exact (eq_refl (term670 n k c p')). Qed.
Lemma lem7547690 (n : nat) (k : real) (c : nat -> real) (p' : Prop) : term671 n k c p'.
Proof. exact (EQ_MP (@lem7547689 n k c p') (@lem7547688 n k c p')). Qed.
Lemma lem7547691 (n : nat) (k : real) (c : nat -> real) (p' : Prop) (q' : Prop) : term672 n k c p' q'.
Proof. exact (@lem7547690 n k c p' q'). Qed.
Lemma lem7547692 (n : nat) (k : real) (c : nat -> real) (p' : Prop) (q' : Prop) : (term672 n k c p' q') = (term673 n k c p' q').
Proof. exact (eq_refl (term672 n k c p' q')). Qed.
Lemma lem7547693 (n : nat) (k : real) (c : nat -> real) (p' : Prop) (q' : Prop) : term673 n k c p' q'.
Proof. exact (EQ_MP (@lem7547692 n k c p' q') (@lem7547691 n k c p' q')). Qed.
Lemma lem7547695 (n : nat) : (term12 n) = True.
Proof. exact (EQ_MP (@lem7539552 n) (@lem7539551 n)). Qed.
Lemma lem7547696 (n : nat) (k : real) (c : nat -> real) (q' : Prop) : term674 n k c q'.
Proof. exact (@lem7547693 n k c True q'). Qed.
Lemma lem7547697 (n : nat) (k : real) (c : nat -> real) (q' : Prop) : term675 n k c q'.
Proof. exact (@lem7547696 n k c q' (@lem7547695 n)). Qed.
Lemma lem7547706 {_2975 _2982 : Type'} (x : _2982) (z : _2975) (y : _2975) : (term501 _2975 _2982 x y z) = y.
Proof. exact (EQ_MP (@lem15249 _2975 _2982 x z y) (@lem0)). Qed.
Lemma lem7547707 (x : nat) (z : real) (y : real) : (term502 x y z) = y.
Proof. exact (@lem7547706 real nat x z y). Qed.
Lemma lem7547708 (c : nat -> real) (k : real) : (term503 k c) = (term504 c k).
Proof. exact (@lem7547707 (NUMERAL 0) (term477 c) (term504 c k)). Qed.
Lemma lem7547709 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7547710 (c : nat -> real) (k : real) : (term676 k c) = (term677 c k).
Proof. exact (MK_COMB (@lem7547709) (@lem7547708 c k)). Qed.
Lemma lem7547711 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7547712 (c : nat -> real) (k : real) : ((term503 k c) = term10) = ((term504 c k) = term10).
Proof. exact (MK_COMB (@lem7547710 c k) (@lem7547711)). Qed.
Lemma lem7547714 (x : real) (y : real) : ((real_sub x y) = term10) = (x = y).
Proof. exact (EQ_MP (@lem7539547 x y) (@lem7539546 x y)). Qed.
Lemma lem7547715 (c : nat -> real) (k : real) : ((term504 c k) = term10) = ((term477 c) = k).
Proof. exact (@lem7547714 (term477 c) k). Qed.
Lemma lem7547718 (c : nat -> real) (k : real) : ((term503 k c) = term10) = ((term477 c) = k).
Proof. exact (TRANS (@lem7547712 c k) (@lem7547715 c k)). Qed.
Lemma lem7547719 (c : nat -> real) (k : real) : term678 c k.
Proof. exact (fun h0 : True => @lem7547718 c k). Qed.
Lemma lem7547720 (n : nat) (c : nat -> real) (k : real) : term679 n c k.
Proof. exact (@lem7547697 n k c ((term477 c) = k)). Qed.
Lemma lem7547721 (n : nat) (c : nat -> real) (k : real) : (term655 n k c) = (term680 c k).
Proof. exact (@lem7547720 n c k (@lem7547719 c k)). Qed.
Lemma lem7547723 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem7547724 (c : nat -> real) (k : real) : (term680 c k) = ((term477 c) = k).
Proof. exact (@lem7547723 ((term477 c) = k)). Qed.
Lemma lem7547727 (n : nat) (c : nat -> real) (k : real) : (term655 n k c) = ((term477 c) = k).
Proof. exact (TRANS (@lem7547721 n c k) (@lem7547724 c k)). Qed.
Lemma lem7547728 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7547729 (n : nat) (c : nat -> real) (k : real) : (term657 n k c) = (term647 c k).
Proof. exact (MK_COMB (@lem7547728) (@lem7547727 n c k)). Qed.
Lemma lem7547739 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term666 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7547740 (p : Prop) (q : Prop) (p' : Prop) : term667 p q p'.
Proof. exact (fun q' : Prop => @lem7547739 p q p' q'). Qed.
Lemma lem7547741 (p : Prop) (q : Prop) : term668 p q.
Proof. exact (fun p' : Prop => @lem7547740 p q p'). Qed.
Lemma lem7547742 (n : nat) (k : real) (c : nat -> real) (i : nat) : term681 n k c i.
Proof. exact (@lem7547741 (term45 i) (term635 n k c i)). Qed.
Lemma lem7547743 (n : nat) (k : real) (c : nat -> real) (i : nat) (p' : Prop) : term682 n k c i p'.
Proof. exact (@lem7547742 n k c i p'). Qed.
Lemma lem7547744 (n : nat) (k : real) (c : nat -> real) (i : nat) (p' : Prop) : (term682 n k c i p') = (term683 n k c i p').
Proof. exact (eq_refl (term682 n k c i p')). Qed.
Lemma lem7547745 (n : nat) (k : real) (c : nat -> real) (i : nat) (p' : Prop) : term683 n k c i p'.
Proof. exact (EQ_MP (@lem7547744 n k c i p') (@lem7547743 n k c i p')). Qed.
Lemma lem7547746 (n : nat) (k : real) (c : nat -> real) (i : nat) (p' : Prop) (q' : Prop) : term684 n k c i p' q'.
Proof. exact (@lem7547745 n k c i p' q'). Qed.
Lemma lem7547747 (n : nat) (k : real) (c : nat -> real) (i : nat) (p' : Prop) (q' : Prop) : (term684 n k c i p' q') = (term685 n k c i p' q').
Proof. exact (eq_refl (term684 n k c i p' q')). Qed.
Lemma lem7547748 (n : nat) (k : real) (c : nat -> real) (i : nat) (p' : Prop) (q' : Prop) : term685 n k c i p' q'.
Proof. exact (EQ_MP (@lem7547747 n k c i p' q') (@lem7547746 n k c i p' q')). Qed.
Lemma lem7547751 (i : nat) : (term45 i) = (term45 i).
Proof. exact (eq_refl (term45 i)). Qed.
Lemma lem7547752 (n : nat) (k : real) (c : nat -> real) (i : nat) (q' : Prop) : term686 n k c i q'.
Proof. exact (@lem7547748 n k c i (term45 i) q'). Qed.
Lemma lem7547753 (n : nat) (k : real) (c : nat -> real) (i : nat) (q' : Prop) : term687 n k c i q'.
Proof. exact (@lem7547752 n k c i q' (@lem7547751 i)). Qed.
Lemma lem7547754 (i : nat) (h1 : term45 i) : term45 i.
Proof. exact (h1). Qed.
Lemma lem7547755 (i : nat) : term688 i.
Proof. exact (@lem82 (i = (NUMERAL 0))). Qed.
Lemma lem7547771 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term666 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7547772 (p : Prop) (q : Prop) (p' : Prop) : term667 p q p'.
Proof. exact (fun q' : Prop => @lem7547771 p q p' q'). Qed.
Lemma lem7547773 (p : Prop) (q : Prop) : term668 p q.
Proof. exact (fun p' : Prop => @lem7547772 p q p'). Qed.
Lemma lem7547774 (n : nat) (k : real) (c : nat -> real) (i : nat) : term689 n k c i.
Proof. exact (@lem7547773 (Peano.le i n) ((term611 k c i) = term10)). Qed.
Lemma lem7547775 (n : nat) (k : real) (c : nat -> real) (i : nat) (p' : Prop) : term690 n k c i p'.
Proof. exact (@lem7547774 n k c i p'). Qed.
Lemma lem7547776 (n : nat) (k : real) (c : nat -> real) (i : nat) (p' : Prop) : (term690 n k c i p') = (term691 n k c i p').
Proof. exact (eq_refl (term690 n k c i p')). Qed.
Lemma lem7547777 (n : nat) (k : real) (c : nat -> real) (i : nat) (p' : Prop) : term691 n k c i p'.
Proof. exact (EQ_MP (@lem7547776 n k c i p') (@lem7547775 n k c i p')). Qed.
Lemma lem7547778 (n : nat) (k : real) (c : nat -> real) (i : nat) (p' : Prop) (q' : Prop) : term692 n k c i p' q'.
Proof. exact (@lem7547777 n k c i p' q'). Qed.
Lemma lem7547779 (n : nat) (k : real) (c : nat -> real) (i : nat) (p' : Prop) (q' : Prop) : (term692 n k c i p' q') = (term693 n k c i p' q').
Proof. exact (eq_refl (term692 n k c i p' q')). Qed.
Lemma lem7547780 (n : nat) (k : real) (c : nat -> real) (i : nat) (p' : Prop) (q' : Prop) : term693 n k c i p' q'.
Proof. exact (EQ_MP (@lem7547779 n k c i p' q') (@lem7547778 n k c i p' q')). Qed.
Lemma lem7547781 (i : nat) (n : nat) : (Peano.le i n) = (Peano.le i n).
Proof. exact (eq_refl (Peano.le i n)). Qed.
Lemma lem7547782 (k : real) (c : nat -> real) (i : nat) (n : nat) (q' : Prop) : term694 k c i n q'.
Proof. exact (@lem7547780 n k c i (Peano.le i n) q'). Qed.
Lemma lem7547783 (k : real) (c : nat -> real) (i : nat) (n : nat) (q' : Prop) : term695 k c i n q'.
Proof. exact (@lem7547782 k c i n q' (@lem7547781 i n)). Qed.
Lemma lem7547792 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term696 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7547793 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term697 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7547792 _2963 g t e g' t' e'). Qed.
Lemma lem7547794 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term698 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7547793 _2963 g t e g' t'). Qed.
Lemma lem7547795 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term699 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7547794 _2963 g t e g'). Qed.
Lemma lem7547796 (g : Prop) (t : real) (e : real) : term700 g t e.
Proof. exact (@lem7547795 real g t e). Qed.
Lemma lem7547797 (k : real) (c : nat -> real) (i : nat) : term701 k c i.
Proof. exact (@lem7547796 (i = (NUMERAL 0)) (term504 c k) (c i)). Qed.
Lemma lem7547798 (k : real) (c : nat -> real) (i : nat) (g' : Prop) : term702 k c i g'.
Proof. exact (@lem7547797 k c i g'). Qed.
Lemma lem7547799 (k : real) (c : nat -> real) (i : nat) (g' : Prop) : (term702 k c i g') = (term703 k c i g').
Proof. exact (eq_refl (term702 k c i g')). Qed.
Lemma lem7547800 (k : real) (c : nat -> real) (i : nat) (g' : Prop) : term703 k c i g'.
Proof. exact (EQ_MP (@lem7547799 k c i g') (@lem7547798 k c i g')). Qed.
Lemma lem7547801 (k : real) (c : nat -> real) (i : nat) (g' : Prop) (t' : real) : term704 k c i g' t'.
Proof. exact (@lem7547800 k c i g' t'). Qed.
Lemma lem7547802 (k : real) (c : nat -> real) (i : nat) (g' : Prop) (t' : real) : (term704 k c i g' t') = (term705 k c i g' t').
Proof. exact (eq_refl (term704 k c i g' t')). Qed.
Lemma lem7547803 (k : real) (c : nat -> real) (i : nat) (g' : Prop) (t' : real) : term705 k c i g' t'.
Proof. exact (EQ_MP (@lem7547802 k c i g' t') (@lem7547801 k c i g' t')). Qed.
Lemma lem7547804 (k : real) (c : nat -> real) (i : nat) (g' : Prop) (t' : real) (e' : real) : term706 k c i g' t' e'.
Proof. exact (@lem7547803 k c i g' t' e'). Qed.
Lemma lem7547805 (k : real) (c : nat -> real) (i : nat) (g' : Prop) (t' : real) (e' : real) : (term706 k c i g' t' e') = (term707 k c i g' t' e').
Proof. exact (eq_refl (term706 k c i g' t' e')). Qed.
Lemma lem7547806 (k : real) (c : nat -> real) (i : nat) (g' : Prop) (t' : real) (e' : real) : term707 k c i g' t' e'.
Proof. exact (EQ_MP (@lem7547805 k c i g' t' e') (@lem7547804 k c i g' t' e')). Qed.
Lemma lem7547808 (i : nat) (h1 : term45 i) : (i = (NUMERAL 0)) = False.
Proof. exact (@lem7547755 i (@lem7547754 i h1)). Qed.
Lemma lem7547809 (k : real) (c : nat -> real) (i : nat) (t' : real) (e' : real) : term708 k c i t' e'.
Proof. exact (@lem7547806 k c i False t' e'). Qed.
Lemma lem7547810 (k : real) (c : nat -> real) (t' : real) (e' : real) (i : nat) (h1 : term45 i) : term709 k c i t' e'.
Proof. exact (@lem7547809 k c i t' e' (@lem7547808 i h1)). Qed.
Lemma lem7547814 (c : nat -> real) (k : real) : (term504 c k) = (term504 c k).
Proof. exact (eq_refl (term504 c k)). Qed.
Lemma lem7547815 (c : nat -> real) (k : real) : term710 c k.
Proof. exact (fun h0 : False => @lem7547814 c k). Qed.
Lemma lem7547816 (c : nat -> real) (k : real) (e' : real) (i : nat) (h1 : term45 i) : term711 i c k e'.
Proof. exact (@lem7547810 k c (term504 c k) e' i h1). Qed.
Lemma lem7547817 (c : nat -> real) (k : real) (e' : real) (i : nat) (h1 : term45 i) : term712 i c k e'.
Proof. exact (@lem7547816 c k e' i h1 (@lem7547815 c k)). Qed.
Lemma lem7547823 (c : nat -> real) (i : nat) : (c i) = (c i).
Proof. exact (eq_refl (c i)). Qed.
Lemma lem7547824 (c : nat -> real) (i : nat) : term713 c i.
Proof. exact (fun h0 : ~ False => @lem7547823 c i). Qed.
Lemma lem7547825 (k : real) (c : nat -> real) (i : nat) (h1 : term45 i) : term714 k c i.
Proof. exact (@lem7547817 c k (c i) i h1). Qed.
Lemma lem7547826 (k : real) (c : nat -> real) (i : nat) (h1 : term45 i) : (term611 k c i) = (term715 k c i).
Proof. exact (@lem7547825 k c i h1 (@lem7547824 c i)). Qed.
Lemma lem7547828 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7547829 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem7547828 real t1 t2). Qed.
Lemma lem7547830 (k : real) (c : nat -> real) (i : nat) : (term715 k c i) = (c i).
Proof. exact (@lem7547829 (term504 c k) (c i)). Qed.
Lemma lem7547831 (k : real) (c : nat -> real) (i : nat) (h1 : term45 i) : (term611 k c i) = (c i).
Proof. exact (TRANS (@lem7547826 k c i h1) (@lem7547830 k c i)). Qed.
Lemma lem7547832 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7547833 (k : real) (c : nat -> real) (i : nat) (h1 : term45 i) : (term623 k c i) = (term716 c i).
Proof. exact (MK_COMB (@lem7547832) (@lem7547831 k c i h1)). Qed.
Lemma lem7547834 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7547835 (k : real) (c : nat -> real) (i : nat) (h1 : term45 i) : ((term611 k c i) = term10) = ((c i) = term10).
Proof. exact (MK_COMB (@lem7547833 k c i h1) (@lem7547834)). Qed.
Lemma lem7547838 (n : nat) (k : real) (c : nat -> real) (i : nat) (h1 : term45 i) : term717 n k c i.
Proof. exact (fun h0 : Peano.le i n => @lem7547835 k c i h1). Qed.
Lemma lem7547839 (k : real) (n : nat) (c : nat -> real) (i : nat) : term718 k n c i.
Proof. exact (@lem7547783 k c i n ((c i) = term10)). Qed.
Lemma lem7547840 (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term45 i) : (term635 n k c i) = (term719 n c i).
Proof. exact (@lem7547839 k n c i (@lem7547838 n k c i h1)). Qed.
Lemma lem7547868 (k : real) (n : nat) (c : nat -> real) (i : nat) : term720 k n c i.
Proof. exact (fun h0 : term45 i => @lem7547840 k n c i h0). Qed.
Lemma lem7547869 (k : real) (n : nat) (c : nat -> real) (i : nat) : term721 k n c i.
Proof. exact (@lem7547753 n k c i (term719 n c i)). Qed.
Lemma lem7547870 (k : real) (n : nat) (c : nat -> real) (i : nat) : (term659 n k c i) = (term722 n c i).
Proof. exact (@lem7547869 k n c i (@lem7547868 k n c i)). Qed.
Lemma lem7547963 (k : real) (n : nat) (c : nat -> real) : (term661 n k c) = (term723 n c).
Proof. exact (fun_ext (fun i : nat => @lem7547870 k n c i)). Qed.
Lemma lem7548056 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7548057 (k : real) (n : nat) (c : nat -> real) : (term663 n k c) = (term724 n c).
Proof. exact (MK_COMB (@lem7548056) (@lem7547963 k n c)). Qed.
Lemma lem7548154 (k : real) (n : nat) (c : nat -> real) : (term664 n k c) = (term725 k n c).
Proof. exact (MK_COMB (@lem7547729 n c k) (@lem7548057 k n c)). Qed.
Lemma lem7548255 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7548256 (k : real) (n : nat) (c : nat -> real) : (term665 n k c) = (term726 k n c).
Proof. exact (MK_COMB (@lem7548255) (@lem7548154 k n c)). Qed.
Lemma lem7548400 (k : real) (n : nat) (c : nat -> real) : (term648 k n c) = (term648 k n c).
Proof. exact (eq_refl (term648 k n c)). Qed.
Lemma lem7548401 (k : real) (n : nat) (c : nat -> real) : ((term664 n k c) = (term648 k n c)) = ((term725 k n c) = (term648 k n c)).
Proof. exact (MK_COMB (@lem7548256 k n c) (@lem7548400 k n c)). Qed.
Lemma lem7548547 (k : real) (n : nat) (c : nat -> real) : ((term725 k n c) = (term648 k n c)) = ((term664 n k c) = (term648 k n c)).
Proof. exact (SYM (@lem7548401 k n c)). Qed.
Lemma lem7548549 (p : Prop) : p = (term13 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7548550 (k : real) (n : nat) (c : nat -> real) : ((term725 k n c) = (term648 k n c)) = (term727 k n c).
Proof. exact (@lem7548549 ((term725 k n c) = (term648 k n c))). Qed.
Lemma lem7548551 (k : real) (n : nat) (c : nat -> real) : (term727 k n c) = ((term725 k n c) = (term648 k n c)).
Proof. exact (SYM (@lem7548550 k n c)). Qed.
Lemma lem7548552 (k : real) (n : nat) (c : nat -> real) (h1 : term728 k n c) : term728 k n c.
Proof. exact (h1). Qed.
Lemma lem7548555 (k : real) (n : nat) (c : nat -> real) (h1 : term729 k n c) : term729 k n c.
Proof. exact (h1). Qed.
Lemma lem7548556 (k : real) (n : nat) (c : nat -> real) : term730 k n c.
Proof. exact (fun h0 : term729 k n c => @lem7548555 k n c h0). Qed.
Lemma lem7548557 (k : real) (n : nat) (c : nat -> real) (h1 : term730 k n c) : term730 k n c.
Proof. exact (h1). Qed.
Lemma lem7548558 (k : real) (n : nat) (c : nat -> real) (h1 : term729 k n c) : term729 k n c.
Proof. exact (h1). Qed.
Lemma lem7548559 (k : real) (n : nat) (c : nat -> real) (h1 : term729 k n c) (h2 : term730 k n c) : term729 k n c.
Proof. exact (@lem7548557 k n c h2 (@lem7548558 k n c h1)). Qed.
Lemma lem7548560 (k : real) (n : nat) (c : nat -> real) (h1 : term729 k n c) : term731 k n c.
Proof. exact (fun h0 : term730 k n c => @lem7548559 k n c h1 h0). Qed.
Lemma lem7548561 (k : real) (n : nat) (c : nat -> real) (h1 : term730 k n c) : term730 k n c.
Proof. exact (h1). Qed.
Lemma lem7548562 (k : real) (n : nat) (c : nat -> real) (h1 : term729 k n c) (h2 : term730 k n c) : term729 k n c.
Proof. exact (@lem7548560 k n c h1 (@lem7548561 k n c h2)). Qed.
Lemma lem7548563 (k : real) (n : nat) (c : nat -> real) (h1 : term730 k n c) : term730 k n c.
Proof. exact (fun h0 : term729 k n c => @lem7548562 k n c h0 h1). Qed.
Lemma lem7548564 (k : real) (n : nat) (c : nat -> real) : term732 k n c.
Proof. exact (fun h0 : term730 k n c => @lem7548563 k n c h0). Qed.
Lemma lem7548567 (k : real) (n : nat) (c : nat -> real) : term730 k n c.
Proof. exact (@lem7548564 k n c (@lem7548556 k n c)). Qed.
Lemma lem7548603 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7548604 : term733 = term734.
Proof. exact (@lem7548603 term735). Qed.
Lemma lem7548651 (k : real) (n : nat) (c : nat -> real) : (term736 k n c) = (term736 k n c).
Proof. exact (eq_refl (term736 k n c)). Qed.
Lemma lem7548652 (k : real) (n : nat) (c : nat -> real) : (term729 k n c) = (term737 k n c).
Proof. exact (MK_COMB (@lem7548651 k n c) (@lem7548604)). Qed.
Lemma lem7548655 (n : nat) (c : nat -> real) : (term738 n c) = (term739 n c).
Proof. exact (fun_ext (fun k : real => @lem7548652 k n c)). Qed.
Lemma lem7548656 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7548657 (n : nat) (c : nat -> real) : (term740 n c) = (term741 n c).
Proof. exact (MK_COMB (@lem7548656) (@lem7548655 n c)). Qed.
Lemma lem7548662 (c : nat -> real) : (term742 c) = (term743 c).
Proof. exact (fun_ext (fun n : nat => @lem7548657 n c)). Qed.
Lemma lem7548663 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7548664 (c : nat -> real) : (term744 c) = (term745 c).
Proof. exact (MK_COMB (@lem7548663) (@lem7548662 c)). Qed.
Lemma lem7548669 : term746 = term747.
Proof. exact (fun_ext (fun c : nat -> real => @lem7548664 c)). Qed.
Lemma lem7548670 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7548679 : term748 = term749.
Proof. exact (MK_COMB (@lem7548670) (@lem7548669)). Qed.
Lemma lem7548686 (n : nat) : (term750 n) = (term750 n).
Proof. exact (eq_refl (term750 n)). Qed.
Lemma lem7548687 : term751 = term751.
Proof. exact (fun_ext (fun n : nat => @lem7548686 n)). Qed.
Lemma lem7548688 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7548689 : term752 = term752.
Proof. exact (MK_COMB (@lem7548688) (@lem7548687)). Qed.
Lemma lem7548694 (n : nat) : (term753 n) = (term753 n).
Proof. exact (eq_refl (term753 n)). Qed.
Lemma lem7548695 : term754 = term754.
Proof. exact (fun_ext (fun n : nat => @lem7548694 n)). Qed.
Lemma lem7548696 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7548697 : term755 = term755.
Proof. exact (MK_COMB (@lem7548696) (@lem7548695)). Qed.
Lemma lem7548698 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7548699 : term756 = term756.
Proof. exact (MK_COMB (@lem7548698) (@lem7548697)). Qed.
Lemma lem7548700 : term757 = term757.
Proof. exact (MK_COMB (@lem7548699) (@lem7548689)). Qed.
Lemma lem7548705 (n : nat) : (term758 n) = (term758 n).
Proof. exact (eq_refl (term758 n)). Qed.
Lemma lem7548706 : term759 = term759.
Proof. exact (fun_ext (fun n : nat => @lem7548705 n)). Qed.
Lemma lem7548707 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7548708 : term760 = term760.
Proof. exact (MK_COMB (@lem7548707) (@lem7548706)). Qed.
Lemma lem7548709 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7548710 : term761 = term761.
Proof. exact (MK_COMB (@lem7548709) (@lem7548708)). Qed.
Lemma lem7548711 : term762 = term762.
Proof. exact (MK_COMB (@lem7548710) (@lem7548700)). Qed.
Lemma lem7548718 (n : nat) : (term763 n) = (term763 n).
Proof. exact (eq_refl (term763 n)). Qed.
Lemma lem7548719 : term764 = term764.
Proof. exact (fun_ext (fun n : nat => @lem7548718 n)). Qed.
Lemma lem7548720 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7548721 : term765 = term765.
Proof. exact (MK_COMB (@lem7548720) (@lem7548719)). Qed.
Lemma lem7548722 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7548723 : term766 = term766.
Proof. exact (MK_COMB (@lem7548722) (@lem7548721)). Qed.
Lemma lem7548724 : term767 = term767.
Proof. exact (MK_COMB (@lem7548723) (@lem7548711)). Qed.
Lemma lem7548731 (n : nat) : (term768 n) = (term768 n).
Proof. exact (eq_refl (term768 n)). Qed.
Lemma lem7548732 : term769 = term769.
Proof. exact (fun_ext (fun n : nat => @lem7548731 n)). Qed.
Lemma lem7548733 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7548734 : term770 = term770.
Proof. exact (MK_COMB (@lem7548733) (@lem7548732)). Qed.
Lemma lem7548735 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7548736 : term771 = term771.
Proof. exact (MK_COMB (@lem7548735) (@lem7548734)). Qed.
Lemma lem7548737 : term772 = term772.
Proof. exact (MK_COMB (@lem7548736) (@lem7548724)). Qed.
Lemma lem7548744 (n : nat) : (term773 n) = (term773 n).
Proof. exact (eq_refl (term773 n)). Qed.
Lemma lem7548745 : term774 = term774.
Proof. exact (fun_ext (fun n : nat => @lem7548744 n)). Qed.
Lemma lem7548746 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7548747 : term775 = term775.
Proof. exact (MK_COMB (@lem7548746) (@lem7548745)). Qed.
Lemma lem7548748 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7548749 : term776 = term776.
Proof. exact (MK_COMB (@lem7548748) (@lem7548747)). Qed.
Lemma lem7548750 : term735 = term735.
Proof. exact (MK_COMB (@lem7548749) (@lem7548737)). Qed.
Lemma lem7548751 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7548752 : term734 = term734.
Proof. exact (MK_COMB (@lem7548751) (@lem7548750)). Qed.
Lemma lem7548761 (n : nat) (c : nat -> real) (i : nat) : (term642 n c i) = (term642 n c i).
Proof. exact (eq_refl (term642 n c i)). Qed.
Lemma lem7548762 (n : nat) (c : nat -> real) : (term644 n c) = (term644 n c).
Proof. exact (fun_ext (fun i : nat => @lem7548761 n c i)). Qed.
Lemma lem7548763 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7548764 (n : nat) (c : nat -> real) : (term646 n c) = (term646 n c).
Proof. exact (MK_COMB (@lem7548763) (@lem7548762 n c)). Qed.
Lemma lem7548767 (c : nat -> real) (k : real) : (term647 c k) = (term647 c k).
Proof. exact (eq_refl (term647 c k)). Qed.
Lemma lem7548768 (k : real) (n : nat) (c : nat -> real) : (term648 k n c) = (term648 k n c).
Proof. exact (MK_COMB (@lem7548767 c k) (@lem7548764 n c)). Qed.
Lemma lem7548779 (n : nat) (c : nat -> real) (i : nat) : (term722 n c i) = (term722 n c i).
Proof. exact (eq_refl (term722 n c i)). Qed.
Lemma lem7548780 (n : nat) (c : nat -> real) : (term723 n c) = (term723 n c).
Proof. exact (fun_ext (fun i : nat => @lem7548779 n c i)). Qed.
Lemma lem7548781 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7548782 (n : nat) (c : nat -> real) : (term724 n c) = (term724 n c).
Proof. exact (MK_COMB (@lem7548781) (@lem7548780 n c)). Qed.
Lemma lem7548785 (c : nat -> real) (k : real) : (term647 c k) = (term647 c k).
Proof. exact (eq_refl (term647 c k)). Qed.
Lemma lem7548786 (k : real) (n : nat) (c : nat -> real) : (term725 k n c) = (term725 k n c).
Proof. exact (MK_COMB (@lem7548785 c k) (@lem7548782 n c)). Qed.
Lemma lem7548787 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7548788 (k : real) (n : nat) (c : nat -> real) : (term726 k n c) = (term726 k n c).
Proof. exact (MK_COMB (@lem7548787) (@lem7548786 k n c)). Qed.
Lemma lem7548789 (k : real) (n : nat) (c : nat -> real) : ((term725 k n c) = (term648 k n c)) = ((term725 k n c) = (term648 k n c)).
Proof. exact (MK_COMB (@lem7548788 k n c) (@lem7548768 k n c)). Qed.
Lemma lem7548790 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7548791 (k : real) (n : nat) (c : nat -> real) : (term728 k n c) = (term728 k n c).
Proof. exact (MK_COMB (@lem7548790) (@lem7548789 k n c)). Qed.
Lemma lem7548792 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7548793 (k : real) (n : nat) (c : nat -> real) : (term736 k n c) = (term736 k n c).
Proof. exact (MK_COMB (@lem7548792) (@lem7548791 k n c)). Qed.
Lemma lem7548794 (k : real) (n : nat) (c : nat -> real) : (term737 k n c) = (term737 k n c).
Proof. exact (MK_COMB (@lem7548793 k n c) (@lem7548752)). Qed.
Lemma lem7548795 (n : nat) (c : nat -> real) : (term739 n c) = (term739 n c).
Proof. exact (fun_ext (fun k : real => @lem7548794 k n c)). Qed.
Lemma lem7548796 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7548797 (n : nat) (c : nat -> real) : (term741 n c) = (term741 n c).
Proof. exact (MK_COMB (@lem7548796) (@lem7548795 n c)). Qed.
Lemma lem7548798 (c : nat -> real) : (term743 c) = (term743 c).
Proof. exact (fun_ext (fun n : nat => @lem7548797 n c)). Qed.
Lemma lem7548799 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7548800 (c : nat -> real) : (term745 c) = (term745 c).
Proof. exact (MK_COMB (@lem7548799) (@lem7548798 c)). Qed.
Lemma lem7548801 : term747 = term747.
Proof. exact (fun_ext (fun c : nat -> real => @lem7548800 c)). Qed.
Lemma lem7548802 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7548803 : term749 = term749.
Proof. exact (MK_COMB (@lem7548802) (@lem7548801)). Qed.
Lemma lem7548908 : term748 = term749.
Proof. exact (TRANS (@lem7548679) (@lem7548803)). Qed.
Lemma lem7548909 : term749 = term748.
Proof. exact (SYM (@lem7548908)). Qed.
Lemma lem7548910 (k : real) (n : nat) (c : nat -> real) (h1 : term728 k n c) : term728 k n c.
Proof. exact (h1). Qed.
Lemma lem7548911 (h1 : term735) : term735.
Proof. exact (h1). Qed.
Lemma lem7548917 (i : nat) : (term42 i) = (i = (NUMERAL 0)).
Proof. exact (@lem16933 (i = (NUMERAL 0))). Qed.
Lemma lem7548926 (n : nat) (c : nat -> real) (i : nat) : (term777 n c i) = (term778 n c i).
Proof. exact (@lem17362 (Peano.le i n) ((c i) = term10)). Qed.
Lemma lem7548931 (n : nat) (c : nat -> real) (i : nat) : (term719 n c i) = (term779 n c i).
Proof. exact (@lem17265 (Peano.le i n) ((c i) = term10)). Qed.
Lemma lem7548933 (i : nat) : (term780 i) = (term780 i).
Proof. exact (eq_refl (term780 i)). Qed.
Lemma lem7548934 (n : nat) (c : nat -> real) (i : nat) : (term781 n c i) = (term782 n c i).
Proof. exact (MK_COMB (@lem7548933 i) (@lem7548926 n c i)). Qed.
Lemma lem7548935 (n : nat) (c : nat -> real) (i : nat) : (term783 n c i) = (term781 n c i).
Proof. exact (@lem17362 (term45 i) (term719 n c i)). Qed.
Lemma lem7548936 (n : nat) (c : nat -> real) (i : nat) : (term783 n c i) = (term782 n c i).
Proof. exact (TRANS (@lem7548935 n c i) (@lem7548934 n c i)). Qed.
Lemma lem7548937 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7548938 (i : nat) : (term46 i) = (term47 i).
Proof. exact (MK_COMB (@lem7548937) (@lem7548917 i)). Qed.
Lemma lem7548939 (n : nat) (c : nat -> real) (i : nat) : (term784 n c i) = (term785 n c i).
Proof. exact (MK_COMB (@lem7548938 i) (@lem7548931 n c i)). Qed.
Lemma lem7548940 (n : nat) (c : nat -> real) (i : nat) : (term722 n c i) = (term784 n c i).
Proof. exact (@lem17265 (term45 i) (term719 n c i)). Qed.
Lemma lem7548941 (n : nat) (c : nat -> real) (i : nat) : (term722 n c i) = (term785 n c i).
Proof. exact (TRANS (@lem7548940 n c i) (@lem7548939 n c i)). Qed.
Lemma lem7548942 (P : nat -> Prop) : (term33 P) = (term34 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7548943 (n : nat) (c : nat -> real) : (term786 n c) = (term787 n c).
Proof. exact (@lem7548942 (term723 n c)). Qed.
Lemma lem7548944 (n : nat) (c : nat -> real) (i : nat) : (term788 n c i) = (term722 n c i).
Proof. exact (eq_refl (term788 n c i)). Qed.
Lemma lem7548945 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7548946 (n : nat) (c : nat -> real) (i : nat) : (term789 n c i) = (term783 n c i).
Proof. exact (MK_COMB (@lem7548945) (@lem7548944 n c i)). Qed.
Lemma lem7548947 (n : nat) (c : nat -> real) (i : nat) : (term789 n c i) = (term782 n c i).
Proof. exact (TRANS (@lem7548946 n c i) (@lem7548936 n c i)). Qed.
Lemma lem7548948 (n : nat) (c : nat -> real) : (term790 n c) = (term791 n c).
Proof. exact (fun_ext (fun i : nat => @lem7548947 n c i)). Qed.
Lemma lem7548949 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7548950 (n : nat) (c : nat -> real) : (term787 n c) = (term792 n c).
Proof. exact (MK_COMB (@lem7548949) (@lem7548948 n c)). Qed.
Lemma lem7548951 (n : nat) (c : nat -> real) : (term786 n c) = (term792 n c).
Proof. exact (TRANS (@lem7548943 n c) (@lem7548950 n c)). Qed.
Lemma lem7548952 (n : nat) (c : nat -> real) : (term723 n c) = (term793 n c).
Proof. exact (fun_ext (fun i : nat => @lem7548941 n c i)). Qed.
Lemma lem7548953 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7548954 (n : nat) (c : nat -> real) : (term724 n c) = (term794 n c).
Proof. exact (MK_COMB (@lem7548953) (@lem7548952 n c)). Qed.
Lemma lem7548956 (c : nat -> real) (k : real) : (term795 c k) = (term795 c k).
Proof. exact (eq_refl (term795 c k)). Qed.
Lemma lem7548957 (k : real) (n : nat) (c : nat -> real) : (term796 k n c) = (term797 k n c).
Proof. exact (MK_COMB (@lem7548956 c k) (@lem7548951 n c)). Qed.
Lemma lem7548958 (k : real) (n : nat) (c : nat -> real) : (term798 k n c) = (term796 k n c).
Proof. exact (@lem17045 ((term477 c) = k) (term724 n c)). Qed.
Lemma lem7548959 (k : real) (n : nat) (c : nat -> real) : (term798 k n c) = (term797 k n c).
Proof. exact (TRANS (@lem7548958 k n c) (@lem7548957 k n c)). Qed.
Lemma lem7548961 (c : nat -> real) (k : real) : (term647 c k) = (term647 c k).
Proof. exact (eq_refl (term647 c k)). Qed.
Lemma lem7548962 (k : real) (n : nat) (c : nat -> real) : (term725 k n c) = (term799 k n c).
Proof. exact (MK_COMB (@lem7548961 c k) (@lem7548954 n c)). Qed.
Lemma lem7548973 (i : nat) (n : nat) : (term800 i n) = (term801 i n).
Proof. exact (@lem17045 (term600 i) (Peano.le i n)). Qed.
Lemma lem7548978 (c : nat -> real) (i : nat) : ((c i) = term10) = ((c i) = term10).
Proof. exact (eq_refl ((c i) = term10)). Qed.
Lemma lem7548983 (n : nat) (c : nat -> real) (i : nat) : (term802 n c i) = (term803 n c i).
Proof. exact (@lem17362 (term602 i n) ((c i) = term10)). Qed.
Lemma lem7548984 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7548985 (i : nat) (n : nat) : (term804 i n) = (term805 i n).
Proof. exact (MK_COMB (@lem7548984) (@lem7548973 i n)). Qed.
Lemma lem7548986 (n : nat) (c : nat -> real) (i : nat) : (term806 n c i) = (term807 n c i).
Proof. exact (MK_COMB (@lem7548985 i n) (@lem7548978 c i)). Qed.
Lemma lem7548987 (n : nat) (c : nat -> real) (i : nat) : (term642 n c i) = (term806 n c i).
Proof. exact (@lem17265 (term602 i n) ((c i) = term10)). Qed.
Lemma lem7548988 (n : nat) (c : nat -> real) (i : nat) : (term642 n c i) = (term807 n c i).
Proof. exact (TRANS (@lem7548987 n c i) (@lem7548986 n c i)). Qed.
Lemma lem7548989 (P : nat -> Prop) : (term33 P) = (term34 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7548990 (n : nat) (c : nat -> real) : (term808 n c) = (term809 n c).
Proof. exact (@lem7548989 (term644 n c)). Qed.
Lemma lem7548991 (n : nat) (c : nat -> real) (i : nat) : (term810 n c i) = (term642 n c i).
Proof. exact (eq_refl (term810 n c i)). Qed.
Lemma lem7548992 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7548993 (n : nat) (c : nat -> real) (i : nat) : (term811 n c i) = (term802 n c i).
Proof. exact (MK_COMB (@lem7548992) (@lem7548991 n c i)). Qed.
Lemma lem7548994 (n : nat) (c : nat -> real) (i : nat) : (term811 n c i) = (term803 n c i).
Proof. exact (TRANS (@lem7548993 n c i) (@lem7548983 n c i)). Qed.
Lemma lem7548995 (n : nat) (c : nat -> real) : (term812 n c) = (term813 n c).
Proof. exact (fun_ext (fun i : nat => @lem7548994 n c i)). Qed.
Lemma lem7548996 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7548997 (n : nat) (c : nat -> real) : (term809 n c) = (term814 n c).
Proof. exact (MK_COMB (@lem7548996) (@lem7548995 n c)). Qed.
Lemma lem7548998 (n : nat) (c : nat -> real) : (term808 n c) = (term814 n c).
Proof. exact (TRANS (@lem7548990 n c) (@lem7548997 n c)). Qed.
Lemma lem7548999 (n : nat) (c : nat -> real) : (term644 n c) = (term815 n c).
Proof. exact (fun_ext (fun i : nat => @lem7548988 n c i)). Qed.
Lemma lem7549000 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7549001 (n : nat) (c : nat -> real) : (term646 n c) = (term816 n c).
Proof. exact (MK_COMB (@lem7549000) (@lem7548999 n c)). Qed.
Lemma lem7549003 (c : nat -> real) (k : real) : (term795 c k) = (term795 c k).
Proof. exact (eq_refl (term795 c k)). Qed.
Lemma lem7549004 (k : real) (n : nat) (c : nat -> real) : (term817 k n c) = (term818 k n c).
Proof. exact (MK_COMB (@lem7549003 c k) (@lem7548998 n c)). Qed.
Lemma lem7549005 (k : real) (n : nat) (c : nat -> real) : (term819 k n c) = (term817 k n c).
Proof. exact (@lem17045 ((term477 c) = k) (term646 n c)). Qed.
Lemma lem7549006 (k : real) (n : nat) (c : nat -> real) : (term819 k n c) = (term818 k n c).
Proof. exact (TRANS (@lem7549005 k n c) (@lem7549004 k n c)). Qed.
Lemma lem7549008 (c : nat -> real) (k : real) : (term647 c k) = (term647 c k).
Proof. exact (eq_refl (term647 c k)). Qed.
Lemma lem7549009 (k : real) (n : nat) (c : nat -> real) : (term648 k n c) = (term820 k n c).
Proof. exact (MK_COMB (@lem7549008 c k) (@lem7549001 n c)). Qed.
Lemma lem7549010 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7549011 (k : real) (n : nat) (c : nat -> real) : (term821 k n c) = (term822 k n c).
Proof. exact (MK_COMB (@lem7549010) (@lem7548959 k n c)). Qed.
Lemma lem7549012 (k : real) (n : nat) (c : nat -> real) : (term823 k n c) = (term824 k n c).
Proof. exact (MK_COMB (@lem7549011 k n c) (@lem7549009 k n c)). Qed.
Lemma lem7549013 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7549014 (k : real) (n : nat) (c : nat -> real) : (term825 k n c) = (term826 k n c).
Proof. exact (MK_COMB (@lem7549013) (@lem7548962 k n c)). Qed.
Lemma lem7549015 (k : real) (n : nat) (c : nat -> real) : (term827 k n c) = (term828 k n c).
Proof. exact (MK_COMB (@lem7549014 k n c) (@lem7549006 k n c)). Qed.
Lemma lem7549016 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7549017 (k : real) (n : nat) (c : nat -> real) : (term829 k n c) = (term830 k n c).
Proof. exact (MK_COMB (@lem7549016) (@lem7549015 k n c)). Qed.
Lemma lem7549018 (k : real) (n : nat) (c : nat -> real) : (term831 k n c) = (term832 k n c).
Proof. exact (MK_COMB (@lem7549017 k n c) (@lem7549012 k n c)). Qed.
Lemma lem7549019 (k : real) (n : nat) (c : nat -> real) : (term728 k n c) = (term831 k n c).
Proof. exact (@lem17646 (term725 k n c) (term648 k n c)). Qed.
Lemma lem7549020 (k : real) (n : nat) (c : nat -> real) : (term728 k n c) = (term832 k n c).
Proof. exact (TRANS (@lem7549019 k n c) (@lem7549018 k n c)). Qed.
Lemma lem7549215 {A : Type'} (P : Prop) (Q : A -> Prop) : (term76 A P Q) = (term77 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7549216 (P : Prop) (Q : nat -> Prop) : (term78 P Q) = (term79 P Q).
Proof. exact (@lem7549215 nat P Q). Qed.
Lemma lem7549217 (k : real) (n : nat) (c : nat -> real) : (term833 k n c) = (term834 k n c).
Proof. exact (@lem7549216 (term835 c k) (term813 n c)). Qed.
Lemma lem7549218 (n : nat) (c : nat -> real) (i : nat) : (term836 n c i) = (term803 n c i).
Proof. exact (eq_refl (term836 n c i)). Qed.
Lemma lem7549219 (n : nat) (c : nat -> real) : (term837 n c) = (term813 n c).
Proof. exact (fun_ext (fun i : nat => @lem7549218 n c i)). Qed.
Lemma lem7549220 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7549221 (n : nat) (c : nat -> real) : (term838 n c) = (term814 n c).
Proof. exact (MK_COMB (@lem7549220) (@lem7549219 n c)). Qed.
Lemma lem7549222 (c : nat -> real) (k : real) : (term795 c k) = (term795 c k).
Proof. exact (eq_refl (term795 c k)). Qed.
Lemma lem7549223 (k : real) (n : nat) (c : nat -> real) : (term833 k n c) = (term818 k n c).
Proof. exact (MK_COMB (@lem7549222 c k) (@lem7549221 n c)). Qed.
Lemma lem7549224 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7549225 (k : real) (n : nat) (c : nat -> real) : (term839 k n c) = (term840 k n c).
Proof. exact (MK_COMB (@lem7549224) (@lem7549223 k n c)). Qed.
Lemma lem7549226 (n : nat) (c : nat -> real) (i : nat) : (term836 n c i) = (term803 n c i).
Proof. exact (eq_refl (term836 n c i)). Qed.
Lemma lem7549227 (c : nat -> real) (k : real) : (term795 c k) = (term795 c k).
Proof. exact (eq_refl (term795 c k)). Qed.
Lemma lem7549228 (k : real) (n : nat) (c : nat -> real) (i : nat) : (term841 k n c i) = (term842 k n c i).
Proof. exact (MK_COMB (@lem7549227 c k) (@lem7549226 n c i)). Qed.
Lemma lem7549229 (k : real) (n : nat) (c : nat -> real) : (term843 k n c) = (term844 k n c).
Proof. exact (fun_ext (fun i : nat => @lem7549228 k n c i)). Qed.
Lemma lem7549230 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7549231 (k : real) (n : nat) (c : nat -> real) : (term834 k n c) = (term845 k n c).
Proof. exact (MK_COMB (@lem7549230) (@lem7549229 k n c)). Qed.
Lemma lem7549232 (k : real) (n : nat) (c : nat -> real) : ((term833 k n c) = (term834 k n c)) = ((term818 k n c) = (term845 k n c)).
Proof. exact (MK_COMB (@lem7549225 k n c) (@lem7549231 k n c)). Qed.
Lemma lem7549233 (k : real) (n : nat) (c : nat -> real) : (term818 k n c) = (term845 k n c).
Proof. exact (EQ_MP (@lem7549232 k n c) (@lem7549217 k n c)). Qed.
Lemma lem7549234 (k : real) (n : nat) (c : nat -> real) : (term826 k n c) = (term826 k n c).
Proof. exact (eq_refl (term826 k n c)). Qed.
Lemma lem7549235 (k : real) (n : nat) (c : nat -> real) : (term828 k n c) = (term846 k n c).
Proof. exact (MK_COMB (@lem7549234 k n c) (@lem7549233 k n c)). Qed.
Lemma lem7549237 {A : Type'} (P : Prop) (Q : A -> Prop) : (term94 A P Q) = (term95 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7549238 (P : Prop) (Q : nat -> Prop) : (term96 P Q) = (term97 P Q).
Proof. exact (@lem7549237 nat P Q). Qed.
Lemma lem7549239 (k : real) (n : nat) (c : nat -> real) : (term847 k n c) = (term848 k n c).
Proof. exact (@lem7549238 (term799 k n c) (term844 k n c)). Qed.
Lemma lem7549240 (k : real) (n : nat) (c : nat -> real) (i : nat) : (term849 k n c i) = (term842 k n c i).
Proof. exact (eq_refl (term849 k n c i)). Qed.
Lemma lem7549241 (k : real) (n : nat) (c : nat -> real) : (term850 k n c) = (term844 k n c).
Proof. exact (fun_ext (fun i : nat => @lem7549240 k n c i)). Qed.
Lemma lem7549242 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7549243 (k : real) (n : nat) (c : nat -> real) : (term851 k n c) = (term845 k n c).
Proof. exact (MK_COMB (@lem7549242) (@lem7549241 k n c)). Qed.
Lemma lem7549244 (k : real) (n : nat) (c : nat -> real) : (term826 k n c) = (term826 k n c).
Proof. exact (eq_refl (term826 k n c)). Qed.
Lemma lem7549245 (k : real) (n : nat) (c : nat -> real) : (term847 k n c) = (term846 k n c).
Proof. exact (MK_COMB (@lem7549244 k n c) (@lem7549243 k n c)). Qed.
Lemma lem7549246 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7549247 (k : real) (n : nat) (c : nat -> real) : (term852 k n c) = (term853 k n c).
Proof. exact (MK_COMB (@lem7549246) (@lem7549245 k n c)). Qed.
Lemma lem7549248 (k : real) (n : nat) (c : nat -> real) (i : nat) : (term849 k n c i) = (term842 k n c i).
Proof. exact (eq_refl (term849 k n c i)). Qed.
Lemma lem7549249 (k : real) (n : nat) (c : nat -> real) : (term826 k n c) = (term826 k n c).
Proof. exact (eq_refl (term826 k n c)). Qed.
Lemma lem7549250 (k : real) (n : nat) (c : nat -> real) (i : nat) : (term854 k n c i) = (term855 k n c i).
Proof. exact (MK_COMB (@lem7549249 k n c) (@lem7549248 k n c i)). Qed.
Lemma lem7549251 (k : real) (n : nat) (c : nat -> real) : (term856 k n c) = (term857 k n c).
Proof. exact (fun_ext (fun i : nat => @lem7549250 k n c i)). Qed.
Lemma lem7549252 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7549253 (k : real) (n : nat) (c : nat -> real) : (term848 k n c) = (term858 k n c).
Proof. exact (MK_COMB (@lem7549252) (@lem7549251 k n c)). Qed.
Lemma lem7549254 (k : real) (n : nat) (c : nat -> real) : ((term847 k n c) = (term848 k n c)) = ((term846 k n c) = (term858 k n c)).
Proof. exact (MK_COMB (@lem7549247 k n c) (@lem7549253 k n c)). Qed.
Lemma lem7549255 (k : real) (n : nat) (c : nat -> real) : (term846 k n c) = (term858 k n c).
Proof. exact (EQ_MP (@lem7549254 k n c) (@lem7549239 k n c)). Qed.
Lemma lem7549256 (k : real) (n : nat) (c : nat -> real) : (term828 k n c) = (term858 k n c).
Proof. exact (TRANS (@lem7549235 k n c) (@lem7549255 k n c)). Qed.
Lemma lem7549257 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7549258 (k : real) (n : nat) (c : nat -> real) : (term830 k n c) = (term859 k n c).
Proof. exact (MK_COMB (@lem7549257) (@lem7549256 k n c)). Qed.
Lemma lem7549260 {A : Type'} (P : Prop) (Q : A -> Prop) : (term76 A P Q) = (term77 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7549261 (P : Prop) (Q : nat -> Prop) : (term78 P Q) = (term79 P Q).
Proof. exact (@lem7549260 nat P Q). Qed.
Lemma lem7549262 (k : real) (n : nat) (c : nat -> real) : (term860 k n c) = (term861 k n c).
Proof. exact (@lem7549261 (term835 c k) (term791 n c)). Qed.
Lemma lem7549263 (n : nat) (c : nat -> real) (i : nat) : (term862 n c i) = (term782 n c i).
Proof. exact (eq_refl (term862 n c i)). Qed.
Lemma lem7549264 (n : nat) (c : nat -> real) : (term863 n c) = (term791 n c).
Proof. exact (fun_ext (fun i : nat => @lem7549263 n c i)). Qed.
Lemma lem7549265 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7549266 (n : nat) (c : nat -> real) : (term864 n c) = (term792 n c).
Proof. exact (MK_COMB (@lem7549265) (@lem7549264 n c)). Qed.
Lemma lem7549267 (c : nat -> real) (k : real) : (term795 c k) = (term795 c k).
Proof. exact (eq_refl (term795 c k)). Qed.
Lemma lem7549268 (k : real) (n : nat) (c : nat -> real) : (term860 k n c) = (term797 k n c).
Proof. exact (MK_COMB (@lem7549267 c k) (@lem7549266 n c)). Qed.
Lemma lem7549269 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7549270 (k : real) (n : nat) (c : nat -> real) : (term865 k n c) = (term866 k n c).
Proof. exact (MK_COMB (@lem7549269) (@lem7549268 k n c)). Qed.
Lemma lem7549271 (n : nat) (c : nat -> real) (i : nat) : (term862 n c i) = (term782 n c i).
Proof. exact (eq_refl (term862 n c i)). Qed.
Lemma lem7549272 (c : nat -> real) (k : real) : (term795 c k) = (term795 c k).
Proof. exact (eq_refl (term795 c k)). Qed.
Lemma lem7549273 (k : real) (n : nat) (c : nat -> real) (i : nat) : (term867 k n c i) = (term868 k n c i).
Proof. exact (MK_COMB (@lem7549272 c k) (@lem7549271 n c i)). Qed.
Lemma lem7549274 (k : real) (n : nat) (c : nat -> real) : (term869 k n c) = (term870 k n c).
Proof. exact (fun_ext (fun i : nat => @lem7549273 k n c i)). Qed.
Lemma lem7549275 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7549276 (k : real) (n : nat) (c : nat -> real) : (term861 k n c) = (term871 k n c).
Proof. exact (MK_COMB (@lem7549275) (@lem7549274 k n c)). Qed.
Lemma lem7549277 (k : real) (n : nat) (c : nat -> real) : ((term860 k n c) = (term861 k n c)) = ((term797 k n c) = (term871 k n c)).
Proof. exact (MK_COMB (@lem7549270 k n c) (@lem7549276 k n c)). Qed.
Lemma lem7549278 (k : real) (n : nat) (c : nat -> real) : (term797 k n c) = (term871 k n c).
Proof. exact (EQ_MP (@lem7549277 k n c) (@lem7549262 k n c)). Qed.
Lemma lem7549279 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7549280 (k : real) (n : nat) (c : nat -> real) : (term822 k n c) = (term872 k n c).
Proof. exact (MK_COMB (@lem7549279) (@lem7549278 k n c)). Qed.
Lemma lem7549281 (k : real) (n : nat) (c : nat -> real) : (term820 k n c) = (term820 k n c).
Proof. exact (eq_refl (term820 k n c)). Qed.
Lemma lem7549282 (k : real) (n : nat) (c : nat -> real) : (term824 k n c) = (term873 k n c).
Proof. exact (MK_COMB (@lem7549280 k n c) (@lem7549281 k n c)). Qed.
Lemma lem7549284 {A : Type'} (P : A -> Prop) (Q : Prop) : (term111 A P Q) = (term112 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7549285 (P : nat -> Prop) (Q : Prop) : (term113 P Q) = (term114 P Q).
Proof. exact (@lem7549284 nat P Q). Qed.
Lemma lem7549286 (k : real) (n : nat) (c : nat -> real) : (term874 k n c) = (term875 k n c).
Proof. exact (@lem7549285 (term870 k n c) (term820 k n c)). Qed.
Lemma lem7549287 (k : real) (n : nat) (c : nat -> real) (i : nat) : (term876 k n c i) = (term868 k n c i).
Proof. exact (eq_refl (term876 k n c i)). Qed.
Lemma lem7549288 (k : real) (n : nat) (c : nat -> real) : (term877 k n c) = (term870 k n c).
Proof. exact (fun_ext (fun i : nat => @lem7549287 k n c i)). Qed.
Lemma lem7549289 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7549290 (k : real) (n : nat) (c : nat -> real) : (term878 k n c) = (term871 k n c).
Proof. exact (MK_COMB (@lem7549289) (@lem7549288 k n c)). Qed.
Lemma lem7549291 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7549292 (k : real) (n : nat) (c : nat -> real) : (term879 k n c) = (term872 k n c).
Proof. exact (MK_COMB (@lem7549291) (@lem7549290 k n c)). Qed.
Lemma lem7549293 (k : real) (n : nat) (c : nat -> real) : (term820 k n c) = (term820 k n c).
Proof. exact (eq_refl (term820 k n c)). Qed.
Lemma lem7549294 (k : real) (n : nat) (c : nat -> real) : (term874 k n c) = (term873 k n c).
Proof. exact (MK_COMB (@lem7549292 k n c) (@lem7549293 k n c)). Qed.
Lemma lem7549295 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7549296 (k : real) (n : nat) (c : nat -> real) : (term880 k n c) = (term881 k n c).
Proof. exact (MK_COMB (@lem7549295) (@lem7549294 k n c)). Qed.
Lemma lem7549297 (k : real) (n : nat) (c : nat -> real) (i : nat) : (term876 k n c i) = (term868 k n c i).
Proof. exact (eq_refl (term876 k n c i)). Qed.
Lemma lem7549298 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7549299 (k : real) (n : nat) (c : nat -> real) (i : nat) : (term882 k n c i) = (term883 k n c i).
Proof. exact (MK_COMB (@lem7549298) (@lem7549297 k n c i)). Qed.
Lemma lem7549300 (k : real) (n : nat) (c : nat -> real) : (term820 k n c) = (term820 k n c).
Proof. exact (eq_refl (term820 k n c)). Qed.
Lemma lem7549301 (i : nat) (k : real) (n : nat) (c : nat -> real) : (term884 i k n c) = (term885 i k n c).
Proof. exact (MK_COMB (@lem7549299 k n c i) (@lem7549300 k n c)). Qed.
Lemma lem7549302 (k : real) (n : nat) (c : nat -> real) : (term886 k n c) = (term887 k n c).
Proof. exact (fun_ext (fun i : nat => @lem7549301 i k n c)). Qed.
Lemma lem7549303 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7549304 (k : real) (n : nat) (c : nat -> real) : (term875 k n c) = (term888 k n c).
Proof. exact (MK_COMB (@lem7549303) (@lem7549302 k n c)). Qed.
Lemma lem7549305 (k : real) (n : nat) (c : nat -> real) : ((term874 k n c) = (term875 k n c)) = ((term873 k n c) = (term888 k n c)).
Proof. exact (MK_COMB (@lem7549296 k n c) (@lem7549304 k n c)). Qed.
Lemma lem7549306 (k : real) (n : nat) (c : nat -> real) : (term873 k n c) = (term888 k n c).
Proof. exact (EQ_MP (@lem7549305 k n c) (@lem7549286 k n c)). Qed.
Lemma lem7549307 (k : real) (n : nat) (c : nat -> real) : (term824 k n c) = (term888 k n c).
Proof. exact (TRANS (@lem7549282 k n c) (@lem7549306 k n c)). Qed.
Lemma lem7549308 (k : real) (n : nat) (c : nat -> real) : (term832 k n c) = (term889 k n c).
Proof. exact (MK_COMB (@lem7549258 k n c) (@lem7549307 k n c)). Qed.
Lemma lem7549310 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term131 A P Q) = (term132 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem7549311 (P : nat -> Prop) (Q : nat -> Prop) : (term133 P Q) = (term134 P Q).
Proof. exact (@lem7549310 nat P Q). Qed.
Lemma lem7549312 (k : real) (n : nat) (c : nat -> real) : (term890 k n c) = (term891 k n c).
Proof. exact (@lem7549311 (term857 k n c) (term887 k n c)). Qed.
Lemma lem7549313 (k : real) (n : nat) (c : nat -> real) (i : nat) : (term892 k n c i) = (term855 k n c i).
Proof. exact (eq_refl (term892 k n c i)). Qed.
Lemma lem7549314 (k : real) (n : nat) (c : nat -> real) : (term893 k n c) = (term857 k n c).
Proof. exact (fun_ext (fun i : nat => @lem7549313 k n c i)). Qed.
Lemma lem7549315 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7549316 (k : real) (n : nat) (c : nat -> real) : (term894 k n c) = (term858 k n c).
Proof. exact (MK_COMB (@lem7549315) (@lem7549314 k n c)). Qed.
Lemma lem7549317 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7549318 (k : real) (n : nat) (c : nat -> real) : (term895 k n c) = (term859 k n c).
Proof. exact (MK_COMB (@lem7549317) (@lem7549316 k n c)). Qed.
Lemma lem7549319 (i : nat) (k : real) (n : nat) (c : nat -> real) : (term896 k n c i) = (term885 i k n c).
Proof. exact (eq_refl (term896 k n c i)). Qed.
Lemma lem7549320 (k : real) (n : nat) (c : nat -> real) : (term897 k n c) = (term887 k n c).
Proof. exact (fun_ext (fun i : nat => @lem7549319 i k n c)). Qed.
Lemma lem7549321 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7549322 (k : real) (n : nat) (c : nat -> real) : (term898 k n c) = (term888 k n c).
Proof. exact (MK_COMB (@lem7549321) (@lem7549320 k n c)). Qed.
Lemma lem7549323 (k : real) (n : nat) (c : nat -> real) : (term890 k n c) = (term889 k n c).
Proof. exact (MK_COMB (@lem7549318 k n c) (@lem7549322 k n c)). Qed.
Lemma lem7549324 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7549325 (k : real) (n : nat) (c : nat -> real) : (term899 k n c) = (term900 k n c).
Proof. exact (MK_COMB (@lem7549324) (@lem7549323 k n c)). Qed.
Lemma lem7549326 (k : real) (n : nat) (c : nat -> real) (i : nat) : (term892 k n c i) = (term855 k n c i).
Proof. exact (eq_refl (term892 k n c i)). Qed.
Lemma lem7549327 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7549328 (k : real) (n : nat) (c : nat -> real) (i : nat) : (term901 k n c i) = (term902 k n c i).
Proof. exact (MK_COMB (@lem7549327) (@lem7549326 k n c i)). Qed.
Lemma lem7549329 (i : nat) (k : real) (n : nat) (c : nat -> real) : (term896 k n c i) = (term885 i k n c).
Proof. exact (eq_refl (term896 k n c i)). Qed.
Lemma lem7549330 (i : nat) (k : real) (n : nat) (c : nat -> real) : (term903 k n c i) = (term904 i k n c).
Proof. exact (MK_COMB (@lem7549328 k n c i) (@lem7549329 i k n c)). Qed.
Lemma lem7549331 (k : real) (n : nat) (c : nat -> real) : (term905 k n c) = (term906 k n c).
Proof. exact (fun_ext (fun i : nat => @lem7549330 i k n c)). Qed.
Lemma lem7549332 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7549333 (k : real) (n : nat) (c : nat -> real) : (term891 k n c) = (term907 k n c).
Proof. exact (MK_COMB (@lem7549332) (@lem7549331 k n c)). Qed.
Lemma lem7549334 (k : real) (n : nat) (c : nat -> real) : ((term890 k n c) = (term891 k n c)) = ((term889 k n c) = (term907 k n c)).
Proof. exact (MK_COMB (@lem7549325 k n c) (@lem7549333 k n c)). Qed.
Lemma lem7549335 (k : real) (n : nat) (c : nat -> real) : (term889 k n c) = (term907 k n c).
Proof. exact (EQ_MP (@lem7549334 k n c) (@lem7549312 k n c)). Qed.
Lemma lem7549337 (k : real) (n : nat) (c : nat -> real) : (term832 k n c) = (term907 k n c).
Proof. exact (TRANS (@lem7549308 k n c) (@lem7549335 k n c)). Qed.
Lemma lem7549338 (k : real) (n : nat) (c : nat -> real) : (term728 k n c) = (term907 k n c).
Proof. exact (TRANS (@lem7549020 k n c) (@lem7549337 k n c)). Qed.
Lemma lem7549339 (k : real) (n : nat) (c : nat -> real) (h1 : term728 k n c) : term907 k n c.
Proof. exact (EQ_MP (@lem7549338 k n c) (@lem7548910 k n c h1)). Qed.
Lemma lem7549342 (n : nat) : (term42 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem7549343 (n : nat) : (term908 n) = (term908 n).
Proof. exact (eq_refl (term908 n)). Qed.
Lemma lem7549344 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7549345 (n : nat) : (term46 n) = (term47 n).
Proof. exact (MK_COMB (@lem7549344) (@lem7549342 n)). Qed.
Lemma lem7549346 (n : nat) : (term909 n) = (term910 n).
Proof. exact (MK_COMB (@lem7549345 n) (@lem7549343 n)). Qed.
Lemma lem7549347 (n : nat) : (term773 n) = (term909 n).
Proof. exact (@lem17265 (term45 n) (term908 n)). Qed.
Lemma lem7549348 (n : nat) : (term773 n) = (term910 n).
Proof. exact (TRANS (@lem7549347 n) (@lem7549346 n)). Qed.
Lemma lem7549349 : term774 = term911.
Proof. exact (fun_ext (fun n : nat => @lem7549348 n)). Qed.
Lemma lem7549350 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7549351 : term775 = term912.
Proof. exact (MK_COMB (@lem7549350) (@lem7549349)). Qed.
Lemma lem7549354 (n : nat) : (term42 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem7549355 (n : nat) : (term600 n) = (term600 n).
Proof. exact (eq_refl (term600 n)). Qed.
Lemma lem7549356 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7549357 (n : nat) : (term46 n) = (term47 n).
Proof. exact (MK_COMB (@lem7549356) (@lem7549354 n)). Qed.
Lemma lem7549358 (n : nat) : (term913 n) = (term914 n).
Proof. exact (MK_COMB (@lem7549357 n) (@lem7549355 n)). Qed.
Lemma lem7549359 (n : nat) : (term768 n) = (term913 n).
Proof. exact (@lem17265 (term45 n) (term600 n)). Qed.
Lemma lem7549360 (n : nat) : (term768 n) = (term914 n).
Proof. exact (TRANS (@lem7549359 n) (@lem7549358 n)). Qed.
Lemma lem7549361 : term769 = term915.
Proof. exact (fun_ext (fun n : nat => @lem7549360 n)). Qed.
Lemma lem7549362 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7549363 : term770 = term916.
Proof. exact (MK_COMB (@lem7549362) (@lem7549361)). Qed.
Lemma lem7549370 (n : nat) : (term763 n) = (term917 n).
Proof. exact (@lem17265 (term908 n) (term45 n)). Qed.
Lemma lem7549371 : term764 = term918.
Proof. exact (fun_ext (fun n : nat => @lem7549370 n)). Qed.
Lemma lem7549372 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7549373 : term765 = term919.
Proof. exact (MK_COMB (@lem7549372) (@lem7549371)). Qed.
Lemma lem7549380 (n : nat) : (term758 n) = (term920 n).
Proof. exact (@lem17265 (term908 n) (term600 n)). Qed.
Lemma lem7549381 : term759 = term921.
Proof. exact (fun_ext (fun n : nat => @lem7549380 n)). Qed.
Lemma lem7549382 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7549383 : term760 = term922.
Proof. exact (MK_COMB (@lem7549382) (@lem7549381)). Qed.
Lemma lem7549390 (n : nat) : (term753 n) = (term923 n).
Proof. exact (@lem17265 (term600 n) (term908 n)). Qed.
Lemma lem7549391 : term754 = term924.
Proof. exact (fun_ext (fun n : nat => @lem7549390 n)). Qed.
Lemma lem7549392 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7549393 : term755 = term925.
Proof. exact (MK_COMB (@lem7549392) (@lem7549391)). Qed.
Lemma lem7549400 (n : nat) : (term750 n) = (term926 n).
Proof. exact (@lem17265 (term600 n) (term45 n)). Qed.
Lemma lem7549401 : term751 = term927.
Proof. exact (fun_ext (fun n : nat => @lem7549400 n)). Qed.
Lemma lem7549402 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7549403 : term752 = term928.
Proof. exact (MK_COMB (@lem7549402) (@lem7549401)). Qed.
Lemma lem7549404 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7549405 : term756 = term929.
Proof. exact (MK_COMB (@lem7549404) (@lem7549393)). Qed.
Lemma lem7549406 : term757 = term930.
Proof. exact (MK_COMB (@lem7549405) (@lem7549403)). Qed.
Lemma lem7549407 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7549408 : term761 = term931.
Proof. exact (MK_COMB (@lem7549407) (@lem7549383)). Qed.
Lemma lem7549409 : term762 = term932.
Proof. exact (MK_COMB (@lem7549408) (@lem7549406)). Qed.
Lemma lem7549410 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7549411 : term766 = term933.
Proof. exact (MK_COMB (@lem7549410) (@lem7549373)). Qed.
Lemma lem7549412 : term767 = term934.
Proof. exact (MK_COMB (@lem7549411) (@lem7549409)). Qed.
Lemma lem7549413 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7549414 : term771 = term935.
Proof. exact (MK_COMB (@lem7549413) (@lem7549363)). Qed.
Lemma lem7549415 : term772 = term936.
Proof. exact (MK_COMB (@lem7549414) (@lem7549412)). Qed.
Lemma lem7549416 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7549417 : term776 = term937.
Proof. exact (MK_COMB (@lem7549416) (@lem7549351)). Qed.
Lemma lem7549710 : term735 = term938.
Proof. exact (MK_COMB (@lem7549417) (@lem7549415)). Qed.
Lemma lem7549711 (h1 : term735) : term938.
Proof. exact (EQ_MP (@lem7549710) (@lem7548911 h1)). Qed.
Lemma lem7549712 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term904 i k n c) : term904 i k n c.
Proof. exact (h1). Qed.
Lemma lem7549735 (n : nat) : (term926 n) = (term926 n).
Proof. exact (eq_refl (term926 n)). Qed.
Lemma lem7549736 : term927 = term927.
Proof. exact (fun_ext (fun n : nat => @lem7549735 n)). Qed.
Lemma lem7549737 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7549738 : term928 = term928.
Proof. exact (MK_COMB (@lem7549737) (@lem7549736)). Qed.
Lemma lem7549759 (n : nat) : (term923 n) = (term923 n).
Proof. exact (eq_refl (term923 n)). Qed.
Lemma lem7549760 : term924 = term924.
Proof. exact (fun_ext (fun n : nat => @lem7549759 n)). Qed.
Lemma lem7549761 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7549762 : term925 = term925.
Proof. exact (MK_COMB (@lem7549761) (@lem7549760)). Qed.
Lemma lem7549763 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7549764 : term929 = term929.
Proof. exact (MK_COMB (@lem7549763) (@lem7549762)). Qed.
Lemma lem7549765 : term930 = term930.
Proof. exact (MK_COMB (@lem7549764) (@lem7549738)). Qed.
Lemma lem7549786 (n : nat) : (term920 n) = (term920 n).
Proof. exact (eq_refl (term920 n)). Qed.
Lemma lem7549787 : term921 = term921.
Proof. exact (fun_ext (fun n : nat => @lem7549786 n)). Qed.
Lemma lem7549788 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7549789 : term922 = term922.
Proof. exact (MK_COMB (@lem7549788) (@lem7549787)). Qed.
Lemma lem7549790 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7549791 : term931 = term931.
Proof. exact (MK_COMB (@lem7549790) (@lem7549789)). Qed.
Lemma lem7549792 : term932 = term932.
Proof. exact (MK_COMB (@lem7549791) (@lem7549765)). Qed.
Lemma lem7549813 (n : nat) : (term917 n) = (term917 n).
Proof. exact (eq_refl (term917 n)). Qed.
Lemma lem7549814 : term918 = term918.
Proof. exact (fun_ext (fun n : nat => @lem7549813 n)). Qed.
Lemma lem7549815 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7549816 : term919 = term919.
Proof. exact (MK_COMB (@lem7549815) (@lem7549814)). Qed.
Lemma lem7549817 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7549818 : term933 = term933.
Proof. exact (MK_COMB (@lem7549817) (@lem7549816)). Qed.
Lemma lem7549819 : term934 = term934.
Proof. exact (MK_COMB (@lem7549818) (@lem7549792)). Qed.
Lemma lem7549838 (n : nat) : (term914 n) = (term914 n).
Proof. exact (eq_refl (term914 n)). Qed.
Lemma lem7549839 : term915 = term915.
Proof. exact (fun_ext (fun n : nat => @lem7549838 n)). Qed.
Lemma lem7549840 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7549841 : term916 = term916.
Proof. exact (MK_COMB (@lem7549840) (@lem7549839)). Qed.
Lemma lem7549842 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7549843 : term935 = term935.
Proof. exact (MK_COMB (@lem7549842) (@lem7549841)). Qed.
Lemma lem7549844 : term936 = term936.
Proof. exact (MK_COMB (@lem7549843) (@lem7549819)). Qed.
Lemma lem7549861 (n : nat) : (term910 n) = (term910 n).
Proof. exact (eq_refl (term910 n)). Qed.
Lemma lem7549862 : term911 = term911.
Proof. exact (fun_ext (fun n : nat => @lem7549861 n)). Qed.
Lemma lem7549863 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7549864 : term912 = term912.
Proof. exact (MK_COMB (@lem7549863) (@lem7549862)). Qed.
Lemma lem7549865 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7549866 : term937 = term937.
Proof. exact (MK_COMB (@lem7549865) (@lem7549864)). Qed.
Lemma lem7549867 : term938 = term938.
Proof. exact (MK_COMB (@lem7549866) (@lem7549844)). Qed.
Lemma lem7549868 (h1 : term735) : term938.
Proof. exact (EQ_MP (@lem7549867) (@lem7549711 h1)). Qed.
Lemma lem7549903 (n : nat) (c : nat -> real) (i : nat) : (term807 n c i) = (term807 n c i).
Proof. exact (eq_refl (term807 n c i)). Qed.
Lemma lem7549904 (n : nat) (c : nat -> real) : (term815 n c) = (term815 n c).
Proof. exact (fun_ext (fun i : nat => @lem7549903 n c i)). Qed.
Lemma lem7549905 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7549906 (n : nat) (c : nat -> real) : (term816 n c) = (term816 n c).
Proof. exact (MK_COMB (@lem7549905) (@lem7549904 n c)). Qed.
Lemma lem7549917 (c : nat -> real) (k : real) : (term647 c k) = (term647 c k).
Proof. exact (eq_refl (term647 c k)). Qed.
Lemma lem7549918 (k : real) (n : nat) (c : nat -> real) : (term820 k n c) = (term820 k n c).
Proof. exact (MK_COMB (@lem7549917 c k) (@lem7549906 n c)). Qed.
Lemma lem7549967 (k : real) (n : nat) (c : nat -> real) (i : nat) : (term883 k n c i) = (term883 k n c i).
Proof. exact (eq_refl (term883 k n c i)). Qed.
Lemma lem7549968 (i : nat) (k : real) (n : nat) (c : nat -> real) : (term885 i k n c) = (term885 i k n c).
Proof. exact (MK_COMB (@lem7549967 k n c i) (@lem7549918 k n c)). Qed.
Lemma lem7550015 (k : real) (n : nat) (c : nat -> real) (i : nat) : (term842 k n c i) = (term842 k n c i).
Proof. exact (eq_refl (term842 k n c i)). Qed.
Lemma lem7550046 (n : nat) (c : nat -> real) (i : nat) : (term785 n c i) = (term785 n c i).
Proof. exact (eq_refl (term785 n c i)). Qed.
Lemma lem7550047 (n : nat) (c : nat -> real) : (term793 n c) = (term793 n c).
Proof. exact (fun_ext (fun i : nat => @lem7550046 n c i)). Qed.
Lemma lem7550048 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7550049 (n : nat) (c : nat -> real) : (term794 n c) = (term794 n c).
Proof. exact (MK_COMB (@lem7550048) (@lem7550047 n c)). Qed.
Lemma lem7550060 (c : nat -> real) (k : real) : (term647 c k) = (term647 c k).
Proof. exact (eq_refl (term647 c k)). Qed.
Lemma lem7550061 (k : real) (n : nat) (c : nat -> real) : (term799 k n c) = (term799 k n c).
Proof. exact (MK_COMB (@lem7550060 c k) (@lem7550049 n c)). Qed.
Lemma lem7550062 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7550063 (k : real) (n : nat) (c : nat -> real) : (term826 k n c) = (term826 k n c).
Proof. exact (MK_COMB (@lem7550062) (@lem7550061 k n c)). Qed.
Lemma lem7550064 (k : real) (n : nat) (c : nat -> real) (i : nat) : (term855 k n c i) = (term855 k n c i).
Proof. exact (MK_COMB (@lem7550063 k n c) (@lem7550015 k n c i)). Qed.
Lemma lem7550065 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7550066 (k : real) (n : nat) (c : nat -> real) (i : nat) : (term902 k n c i) = (term902 k n c i).
Proof. exact (MK_COMB (@lem7550065) (@lem7550064 k n c i)). Qed.
Lemma lem7550067 (i : nat) (k : real) (n : nat) (c : nat -> real) : (term904 i k n c) = (term904 i k n c).
Proof. exact (MK_COMB (@lem7550066 k n c i) (@lem7549968 i k n c)). Qed.
Lemma lem7550068 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term904 i k n c) : term904 i k n c.
Proof. exact (EQ_MP (@lem7550067 i k n c) (@lem7549712 i k n c h1)). Qed.
Lemma lem7550069 (h1 : term735) : term936.
Proof. exact (proj2 (@lem7549868 h1)). Qed.
Lemma lem7550071 (h1 : term735) : term934.
Proof. exact (proj2 (@lem7550069 h1)). Qed.
Lemma lem7550072 (h1 : term735) : term916.
Proof. exact (proj1 (@lem7550069 h1)). Qed.
Lemma lem7550073 (h1 : term735) : term932.
Proof. exact (proj2 (@lem7550071 h1)). Qed.
Lemma lem7550075 (h1 : term735) : term930.
Proof. exact (proj2 (@lem7550073 h1)). Qed.
Lemma lem7550077 (h1 : term735) : term928.
Proof. exact (proj2 (@lem7550075 h1)). Qed.
Lemma lem7550079 (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term855 k n c i) : term855 k n c i.
Proof. exact (h1). Qed.
Lemma lem7550080 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term885 i k n c) : term885 i k n c.
Proof. exact (h1). Qed.
Lemma lem7550081 (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term855 k n c i) : term842 k n c i.
Proof. exact (proj2 (@lem7550079 k n c i h1)). Qed.
Lemma lem7550082 (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term855 k n c i) : term799 k n c.
Proof. exact (proj1 (@lem7550079 k n c i h1)). Qed.
Lemma lem7550083 (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term855 k n c i) : term794 n c.
Proof. exact (proj2 (@lem7550082 k n c i h1)). Qed.
Lemma lem7550086 (n : nat) (c : nat -> real) (i : nat) (h1 : term803 n c i) : term803 n c i.
Proof. exact (h1). Qed.
Lemma lem7550088 (n : nat) (c : nat -> real) (i : nat) (h1 : term803 n c i) : term602 i n.
Proof. exact (proj1 (@lem7550086 n c i h1)). Qed.
Lemma lem7550091 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term885 i k n c) : term820 k n c.
Proof. exact (proj2 (@lem7550080 i k n c h1)). Qed.
Lemma lem7550092 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term885 i k n c) : term868 k n c i.
Proof. exact (proj1 (@lem7550080 i k n c h1)). Qed.
Lemma lem7550093 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term885 i k n c) : term816 n c.
Proof. exact (proj2 (@lem7550091 i k n c h1)). Qed.
Lemma lem7550096 (n : nat) (c : nat -> real) (i : nat) (h1 : term782 n c i) : term782 n c i.
Proof. exact (h1). Qed.
Lemma lem7550097 (n : nat) (c : nat -> real) (i : nat) (h1 : term782 n c i) : term778 n c i.
Proof. exact (proj2 (@lem7550096 n c i h1)). Qed.
Lemma lem7550205 (c : nat -> real) (k : real) (h1 : term835 c k) : term835 c k.
Proof. exact (h1). Qed.
Lemma lem7550278 (n : nat) : (term926 n) = (term926 n).
Proof. exact (eq_refl (term926 n)). Qed.
Lemma lem7550279 : term927 = term927.
Proof. exact (fun_ext (fun n : nat => @lem7550278 n)). Qed.
Lemma lem7550280 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7550282 : term928 = term928.
Proof. exact (MK_COMB (@lem7550280) (@lem7550279)). Qed.
Lemma lem7550283 (h1 : term735) : term928.
Proof. exact (EQ_MP (@lem7550282) (@lem7550077 h1)). Qed.
Lemma lem7550301 (n : nat) (c : nat -> real) (i : nat) : (term785 n c i) = (term785 n c i).
Proof. exact (eq_refl (term785 n c i)). Qed.
Lemma lem7550302 (n : nat) (c : nat -> real) : (term793 n c) = (term793 n c).
Proof. exact (fun_ext (fun i : nat => @lem7550301 n c i)). Qed.
Lemma lem7550303 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7550305 (n : nat) (c : nat -> real) : (term794 n c) = (term794 n c).
Proof. exact (MK_COMB (@lem7550303) (@lem7550302 n c)). Qed.
Lemma lem7550306 (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term855 k n c i) : term794 n c.
Proof. exact (EQ_MP (@lem7550305 n c) (@lem7550083 k n c i h1)). Qed.
Lemma lem7550423 (c : nat -> real) (k : real) (h1 : term835 c k) : term835 c k.
Proof. exact (h1). Qed.
Lemma lem7550444 (n : nat) : (term914 n) = (term914 n).
Proof. exact (eq_refl (term914 n)). Qed.
Lemma lem7550445 : term915 = term915.
Proof. exact (fun_ext (fun n : nat => @lem7550444 n)). Qed.
Lemma lem7550446 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7550448 : term916 = term916.
Proof. exact (MK_COMB (@lem7550446) (@lem7550445)). Qed.
Lemma lem7550449 (h1 : term735) : term916.
Proof. exact (EQ_MP (@lem7550448) (@lem7550072 h1)). Qed.
Lemma lem7550519 (n : nat) (c : nat -> real) (i : nat) : (term807 n c i) = (term807 n c i).
Proof. exact (eq_refl (term807 n c i)). Qed.
Lemma lem7550520 (n : nat) (c : nat -> real) : (term815 n c) = (term815 n c).
Proof. exact (fun_ext (fun i : nat => @lem7550519 n c i)). Qed.
Lemma lem7550521 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7550523 (n : nat) (c : nat -> real) : (term816 n c) = (term816 n c).
Proof. exact (MK_COMB (@lem7550521) (@lem7550520 n c)). Qed.
Lemma lem7550524 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term885 i k n c) : term816 n c.
Proof. exact (EQ_MP (@lem7550523 n c) (@lem7550093 i k n c h1)). Qed.
Lemma lem7550573 (_97393 : nat) (h1 : term735) : term939 _97393.
Proof. exact (@lem7550283 h1 _97393). Qed.
Lemma lem7550574 (_97393 : nat) : (term939 _97393) = (term926 _97393).
Proof. exact (eq_refl (term939 _97393)). Qed.
Lemma lem7550576 (_97394 : nat) (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term855 k n c i) : term940 n c _97394.
Proof. exact (@lem7550306 k n c i h1 _97394). Qed.
Lemma lem7550577 (n : nat) (c : nat -> real) (_97394 : nat) : (term940 n c _97394) = (term785 n c _97394).
Proof. exact (eq_refl (term940 n c _97394)). Qed.
Lemma lem7550603 (_97403 : nat) (h1 : term735) : term941 _97403.
Proof. exact (@lem7550449 h1 _97403). Qed.
Lemma lem7550604 (_97403 : nat) : (term941 _97403) = (term914 _97403).
Proof. exact (eq_refl (term941 _97403)). Qed.
Lemma lem7550618 (_97408 : nat) (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term885 i k n c) : term942 n c _97408.
Proof. exact (@lem7550524 i k n c h1 _97408). Qed.
Lemma lem7550619 (n : nat) (c : nat -> real) (_97408 : nat) : (term942 n c _97408) = (term807 n c _97408).
Proof. exact (eq_refl (term942 n c _97408)). Qed.
Lemma lem7550620 (_97408 : nat) (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term885 i k n c) : term807 n c _97408.
Proof. exact (EQ_MP (@lem7550619 n c _97408) (@lem7550618 _97408 i k n c h1)). Qed.
Lemma lem7550658 (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term855 k n c i) : (term477 c) = k.
Proof. exact (proj1 (@lem7550082 k n c i h1)). Qed.
Lemma lem7550670 (c : nat -> real) (k : real) (h1 : term835 c k) : term835 c k.
Proof. exact (h1). Qed.
Lemma lem7550762 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term885 i k n c) : (term477 c) = k.
Proof. exact (proj1 (@lem7550091 i k n c h1)). Qed.
Lemma lem7550776 (c : nat -> real) (k : real) (h1 : term835 c k) : term835 c k.
Proof. exact (h1). Qed.
Lemma lem7550825 (n : nat) (c : nat -> real) (_97408 : nat) : (term807 n c _97408) = (term943 n c _97408).
Proof. exact (@lem7539542 (term944 _97408) (term945 _97408 n) ((c _97408) = term10)). Qed.
Lemma lem7550833 (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term855 k n c i) : k = (term477 c).
Proof. exact (SYM (@lem7550658 k n c i h1)). Qed.
Lemma lem7550946 (c : nat -> real) : (term946 c) = (term946 c).
Proof. exact (eq_refl (term946 c)). Qed.
Lemma lem7550947 (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term855 k n c i) : (term947 c k) = (term948 c).
Proof. exact (MK_COMB (@lem7550946 c) (@lem7550833 k n c i h1)). Qed.
Lemma lem7550948 (c : nat -> real) : (term948 c) = (term949 c).
Proof. exact (eq_refl (term948 c)). Qed.
Lemma lem7550949 (c : nat -> real) (k : real) : (term950 c k) = (term950 c k).
Proof. exact (eq_refl (term950 c k)). Qed.
Lemma lem7550950 (k : real) (c : nat -> real) : ((term947 c k) = (term948 c)) = ((term947 c k) = (term949 c)).
Proof. exact (MK_COMB (@lem7550949 c k) (@lem7550948 c)). Qed.
Lemma lem7550951 (c : nat -> real) (k : real) : (term947 c k) = (term835 c k).
Proof. exact (eq_refl (term947 c k)). Qed.
Lemma lem7550952 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7550953 (c : nat -> real) (k : real) : (term950 c k) = (term951 c k).
Proof. exact (MK_COMB (@lem7550952) (@lem7550951 c k)). Qed.
Lemma lem7550954 (c : nat -> real) : (term949 c) = (term949 c).
Proof. exact (eq_refl (term949 c)). Qed.
Lemma lem7550955 (k : real) (c : nat -> real) : ((term947 c k) = (term949 c)) = ((term835 c k) = (term949 c)).
Proof. exact (MK_COMB (@lem7550953 c k) (@lem7550954 c)). Qed.
Lemma lem7550956 (k : real) (c : nat -> real) : ((term947 c k) = (term948 c)) = ((term835 c k) = (term949 c)).
Proof. exact (TRANS (@lem7550950 k c) (@lem7550955 k c)). Qed.
Lemma lem7550957 (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term855 k n c i) : (term835 c k) = (term949 c).
Proof. exact (EQ_MP (@lem7550956 k c) (@lem7550947 k n c i h1)). Qed.
Lemma lem7550958 (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term835 c k) (h2 : term855 k n c i) : term949 c.
Proof. exact (EQ_MP (@lem7550957 k n c i h2) (@lem7550670 c k h1)). Qed.
Lemma lem7551057 (_97393 : nat) (h1 : term735) : term926 _97393.
Proof. exact (EQ_MP (@lem7550574 _97393) (@lem7550573 _97393 h1)). Qed.
Lemma lem7551071 (_97394 : nat) (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term855 k n c i) : term785 n c _97394.
Proof. exact (EQ_MP (@lem7550577 n c _97394) (@lem7550576 _97394 k n c i h1)). Qed.
Lemma lem7551085 (n : nat) (c : nat -> real) (i : nat) (h1 : term803 n c i) : term952 c i.
Proof. exact (proj2 (@lem7550086 n c i h1)). Qed.
Lemma lem7551114 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term885 i k n c) : k = (term477 c).
Proof. exact (SYM (@lem7550762 i k n c h1)). Qed.
Lemma lem7551227 (c : nat -> real) : (term946 c) = (term946 c).
Proof. exact (eq_refl (term946 c)). Qed.
Lemma lem7551228 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term885 i k n c) : (term947 c k) = (term948 c).
Proof. exact (MK_COMB (@lem7551227 c) (@lem7551114 i k n c h1)). Qed.
Lemma lem7551229 (c : nat -> real) : (term948 c) = (term949 c).
Proof. exact (eq_refl (term948 c)). Qed.
Lemma lem7551230 (c : nat -> real) (k : real) : (term950 c k) = (term950 c k).
Proof. exact (eq_refl (term950 c k)). Qed.
Lemma lem7551231 (k : real) (c : nat -> real) : ((term947 c k) = (term948 c)) = ((term947 c k) = (term949 c)).
Proof. exact (MK_COMB (@lem7551230 c k) (@lem7551229 c)). Qed.
Lemma lem7551232 (c : nat -> real) (k : real) : (term947 c k) = (term835 c k).
Proof. exact (eq_refl (term947 c k)). Qed.
Lemma lem7551233 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7551234 (c : nat -> real) (k : real) : (term950 c k) = (term951 c k).
Proof. exact (MK_COMB (@lem7551233) (@lem7551232 c k)). Qed.
Lemma lem7551235 (c : nat -> real) : (term949 c) = (term949 c).
Proof. exact (eq_refl (term949 c)). Qed.
Lemma lem7551236 (k : real) (c : nat -> real) : ((term947 c k) = (term949 c)) = ((term835 c k) = (term949 c)).
Proof. exact (MK_COMB (@lem7551234 c k) (@lem7551235 c)). Qed.
Lemma lem7551237 (k : real) (c : nat -> real) : ((term947 c k) = (term948 c)) = ((term835 c k) = (term949 c)).
Proof. exact (TRANS (@lem7551231 k c) (@lem7551236 k c)). Qed.
Lemma lem7551238 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term885 i k n c) : (term835 c k) = (term949 c).
Proof. exact (EQ_MP (@lem7551237 k c) (@lem7551228 i k n c h1)). Qed.
Lemma lem7551239 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term835 c k) (h2 : term885 i k n c) : term949 c.
Proof. exact (EQ_MP (@lem7551238 i k n c h2) (@lem7550776 c k h1)). Qed.
Lemma lem7551282 (_97403 : nat) (h1 : term735) : term914 _97403.
Proof. exact (EQ_MP (@lem7550604 _97403) (@lem7550603 _97403 h1)). Qed.
Lemma lem7551352 (_97408 : nat) (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term885 i k n c) : term943 n c _97408.
Proof. exact (EQ_MP (@lem7550825 n c _97408) (@lem7550620 _97408 i k n c h1)). Qed.
Lemma lem7551394 (n : nat) (c : nat -> real) (i : nat) (h1 : term782 n c i) : term952 c i.
Proof. exact (proj2 (@lem7550097 n c i h1)). Qed.
Lemma lem7551470 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem7551471 (c : nat -> real) : (term477 c) = (term477 c).
Proof. exact (@lem7551470 (term477 c)). Qed.
Lemma lem7551472 (c : nat -> real) : term953 c.
Proof. exact (fun h0 : term949 c => @lem7551471 c). Qed.
Lemma lem7551474 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7551475 (c : nat -> real) : (term953 c) = ((term477 c) = (term477 c)).
Proof. exact (@lem7551474 ((term477 c) = (term477 c))). Qed.
Lemma lem7551476 (c : nat -> real) : (term477 c) = (term477 c).
Proof. exact (EQ_MP (@lem7551475 c) (@lem7551472 c)). Qed.
Lemma lem7551479 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7551481 (c : nat -> real) : (term949 c) = (term954 c).
Proof. exact (@lem7551479 ((term477 c) = (term477 c))). Qed.
Lemma lem7551484 (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term835 c k) (h2 : term855 k n c i) : term954 c.
Proof. exact (EQ_MP (@lem7551481 c) (@lem7550958 k n c i h1 h2)). Qed.
Lemma lem7551487 (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term835 c k) (h2 : term855 k n c i) : False.
Proof. exact (@lem7551484 k n c i h1 h2 (@lem7551476 c)). Qed.
Lemma lem7551488 (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term835 c k) (h2 : term855 k n c i) : term157.
Proof. exact (fun h0 : ~ False => @lem7551487 k n c i h1 h2). Qed.
Lemma lem7551490 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7551491 : term157 = False.
Proof. exact (@lem7551490 False). Qed.
Lemma lem7551568 (n : nat) (c : nat -> real) (i : nat) (h1 : term803 n c i) : term600 i.
Proof. exact (proj1 (@lem7550088 n c i h1)). Qed.
Lemma lem7551569 (n : nat) (c : nat -> real) (i : nat) (h1 : term803 n c i) : term955 i.
Proof. exact (fun h0 : term944 i => @lem7551568 n c i h1). Qed.
Lemma lem7551571 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7551572 (i : nat) : (term955 i) = (term600 i).
Proof. exact (@lem7551571 (term600 i)). Qed.
Lemma lem7551573 (n : nat) (c : nat -> real) (i : nat) (h1 : term803 n c i) : term600 i.
Proof. exact (EQ_MP (@lem7551572 i) (@lem7551569 n c i h1)). Qed.
Lemma lem7551586 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7551587 (_97393 : nat) : (term956 _97393) = (term926 _97393).
Proof. exact (@lem7551586 (term944 _97393) (term45 _97393)). Qed.
Lemma lem7551595 (_97393 : nat) : (term957 _97393) = (term957 _97393).
Proof. exact (eq_refl (term957 _97393)). Qed.
Lemma lem7551596 (_97393 : nat) : ((term926 _97393) = (term956 _97393)) = ((term926 _97393) = (term926 _97393)).
Proof. exact (MK_COMB (@lem7551595 _97393) (@lem7551587 _97393)). Qed.
Lemma lem7551598 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7551599 (x : Prop) : (x = x) = True.
Proof. exact (@lem7551598 Prop x). Qed.
Lemma lem7551600 (_97393 : nat) : ((term926 _97393) = (term926 _97393)) = True.
Proof. exact (@lem7551599 (term926 _97393)). Qed.
Lemma lem7551601 (_97393 : nat) : ((term926 _97393) = (term956 _97393)) = True.
Proof. exact (TRANS (@lem7551596 _97393) (@lem7551600 _97393)). Qed.
Lemma lem7551602 (_97393 : nat) : True = ((term926 _97393) = (term956 _97393)).
Proof. exact (SYM (@lem7551601 _97393)). Qed.
Lemma lem7551603 (_97393 : nat) : (term926 _97393) = (term956 _97393).
Proof. exact (EQ_MP (@lem7551602 _97393) (@lem0)). Qed.
Lemma lem7551604 (_97393 : nat) (h1 : term735) : term956 _97393.
Proof. exact (EQ_MP (@lem7551603 _97393) (@lem7551057 _97393 h1)). Qed.
Lemma lem7551606 (b : Prop) (a : Prop) : (a \/ b) = (term171 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7551607 (_97393 : nat) : (term956 _97393) = (term958 _97393).
Proof. exact (@lem7551606 (term944 _97393) (term45 _97393)). Qed.
Lemma lem7551609 (a : Prop) : (term22 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7551610 (_97393 : nat) : (term959 _97393) = (term600 _97393).
Proof. exact (@lem7551609 (term600 _97393)). Qed.
Lemma lem7551611 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7551612 (_97393 : nat) : (term960 _97393) = (term961 _97393).
Proof. exact (MK_COMB (@lem7551611) (@lem7551610 _97393)). Qed.
Lemma lem7551613 (_97393 : nat) : (term45 _97393) = (term45 _97393).
Proof. exact (eq_refl (term45 _97393)). Qed.
Lemma lem7551614 (_97393 : nat) : (term958 _97393) = (term750 _97393).
Proof. exact (MK_COMB (@lem7551612 _97393) (@lem7551613 _97393)). Qed.
Lemma lem7551615 (_97393 : nat) : (term956 _97393) = (term750 _97393).
Proof. exact (TRANS (@lem7551607 _97393) (@lem7551614 _97393)). Qed.
Lemma lem7551618 (_97393 : nat) (h1 : term735) : term750 _97393.
Proof. exact (EQ_MP (@lem7551615 _97393) (@lem7551604 _97393 h1)). Qed.
Lemma lem7551619 (i : nat) (h1 : term735) : term750 i.
Proof. exact (@lem7551618 i h1). Qed.
Lemma lem7551622 (n : nat) (c : nat -> real) (i : nat) (h1 : term735) (h2 : term803 n c i) : term45 i.
Proof. exact (@lem7551619 i h1 (@lem7551573 n c i h2)). Qed.
Lemma lem7551623 (n : nat) (c : nat -> real) (i : nat) (h1 : term735) (h2 : term803 n c i) : term200 i.
Proof. exact (fun h0 : i = (NUMERAL 0) => @lem7551622 n c i h1 h2). Qed.
Lemma lem7551625 (p : Prop) : (term170 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7551626 (i : nat) : (term200 i) = (term45 i).
Proof. exact (@lem7551625 (i = (NUMERAL 0))). Qed.
Lemma lem7551627 (n : nat) (c : nat -> real) (i : nat) (h1 : term735) (h2 : term803 n c i) : term45 i.
Proof. exact (EQ_MP (@lem7551626 i) (@lem7551623 n c i h1 h2)). Qed.
Lemma lem7551629 (n : nat) (c : nat -> real) (i : nat) (h1 : term803 n c i) : Peano.le i n.
Proof. exact (proj2 (@lem7550088 n c i h1)). Qed.
Lemma lem7551630 (n : nat) (c : nat -> real) (i : nat) (h1 : term803 n c i) : term962 i n.
Proof. exact (fun h0 : term945 i n => @lem7551629 n c i h1). Qed.
Lemma lem7551632 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7551633 (i : nat) (n : nat) : (term962 i n) = (Peano.le i n).
Proof. exact (@lem7551632 (Peano.le i n)). Qed.
Lemma lem7551634 (n : nat) (c : nat -> real) (i : nat) (h1 : term803 n c i) : Peano.le i n.
Proof. exact (EQ_MP (@lem7551633 i n) (@lem7551630 n c i h1)). Qed.
Lemma lem7551652 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7551653 (c : nat -> real) (_97394 : nat) (n : nat) : (term779 n c _97394) = (term963 c _97394 n).
Proof. exact (@lem7551652 ((c _97394) = term10) (term945 _97394 n)). Qed.
Lemma lem7551661 (_97394 : nat) : (term47 _97394) = (term47 _97394).
Proof. exact (eq_refl (term47 _97394)). Qed.
Lemma lem7551662 (c : nat -> real) (_97394 : nat) (n : nat) : (term785 n c _97394) = (term964 c _97394 n).
Proof. exact (MK_COMB (@lem7551661 _97394) (@lem7551653 c _97394 n)). Qed.
Lemma lem7551673 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7551674 (c : nat -> real) (_97394 : nat) (n : nat) : (term965 n c _97394) = (term966 c _97394 n).
Proof. exact (MK_COMB (@lem7551673) (@lem7551662 c _97394 n)). Qed.
Lemma lem7551678 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7551679 (c : nat -> real) (_97394 : nat) (n : nat) : (term967 c _97394 n) = (term964 c _97394 n).
Proof. exact (@lem7551678 (_97394 = (NUMERAL 0)) ((c _97394) = term10) (term945 _97394 n)). Qed.
Lemma lem7551699 (c : nat -> real) (_97394 : nat) (n : nat) : ((term785 n c _97394) = (term967 c _97394 n)) = ((term964 c _97394 n) = (term964 c _97394 n)).
Proof. exact (MK_COMB (@lem7551674 c _97394 n) (@lem7551679 c _97394 n)). Qed.
Lemma lem7551701 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7551702 (x : Prop) : (x = x) = True.
Proof. exact (@lem7551701 Prop x). Qed.
Lemma lem7551703 (c : nat -> real) (_97394 : nat) (n : nat) : ((term964 c _97394 n) = (term964 c _97394 n)) = True.
Proof. exact (@lem7551702 (term964 c _97394 n)). Qed.
Lemma lem7551704 (c : nat -> real) (_97394 : nat) (n : nat) : ((term785 n c _97394) = (term967 c _97394 n)) = True.
Proof. exact (TRANS (@lem7551699 c _97394 n) (@lem7551703 c _97394 n)). Qed.
Lemma lem7551705 (c : nat -> real) (_97394 : nat) (n : nat) : True = ((term785 n c _97394) = (term967 c _97394 n)).
Proof. exact (SYM (@lem7551704 c _97394 n)). Qed.
Lemma lem7551706 (c : nat -> real) (_97394 : nat) (n : nat) : (term785 n c _97394) = (term967 c _97394 n).
Proof. exact (EQ_MP (@lem7551705 c _97394 n) (@lem0)). Qed.
Lemma lem7551707 (_97394 : nat) (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term855 k n c i) : term967 c _97394 n.
Proof. exact (EQ_MP (@lem7551706 c _97394 n) (@lem7551071 _97394 k n c i h1)). Qed.
Lemma lem7551709 (b : Prop) (a : Prop) : (a \/ b) = (term171 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7551710 (n : nat) (c : nat -> real) (_97394 : nat) : (term967 c _97394 n) = (term968 n c _97394).
Proof. exact (@lem7551709 (term969 _97394 n) ((c _97394) = term10)). Qed.
Lemma lem7551712 (a : Prop) (b : Prop) : (term174 a b) = (term175 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7551713 (_97394 : nat) (n : nat) : (term970 _97394 n) = (term971 _97394 n).
Proof. exact (@lem7551712 (_97394 = (NUMERAL 0)) (term945 _97394 n)). Qed.
Lemma lem7551715 (a : Prop) : (term22 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7551716 (_97394 : nat) (n : nat) : (term972 _97394 n) = (Peano.le _97394 n).
Proof. exact (@lem7551715 (Peano.le _97394 n)). Qed.
Lemma lem7551717 (_97394 : nat) : (term780 _97394) = (term780 _97394).
Proof. exact (eq_refl (term780 _97394)). Qed.
Lemma lem7551718 (_97394 : nat) (n : nat) : (term971 _97394 n) = (term973 _97394 n).
Proof. exact (MK_COMB (@lem7551717 _97394) (@lem7551716 _97394 n)). Qed.
Lemma lem7551719 (_97394 : nat) (n : nat) : (term970 _97394 n) = (term973 _97394 n).
Proof. exact (TRANS (@lem7551713 _97394 n) (@lem7551718 _97394 n)). Qed.
Lemma lem7551720 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7551721 (_97394 : nat) (n : nat) : (term974 _97394 n) = (term975 _97394 n).
Proof. exact (MK_COMB (@lem7551720) (@lem7551719 _97394 n)). Qed.
Lemma lem7551722 (c : nat -> real) (_97394 : nat) : ((c _97394) = term10) = ((c _97394) = term10).
Proof. exact (eq_refl ((c _97394) = term10)). Qed.
Lemma lem7551723 (n : nat) (c : nat -> real) (_97394 : nat) : (term968 n c _97394) = (term976 n c _97394).
Proof. exact (MK_COMB (@lem7551721 _97394 n) (@lem7551722 c _97394)). Qed.
Lemma lem7551724 (n : nat) (c : nat -> real) (_97394 : nat) : (term967 c _97394 n) = (term976 n c _97394).
Proof. exact (TRANS (@lem7551710 n c _97394) (@lem7551723 n c _97394)). Qed.
Lemma lem7551726 (n : nat) (c : nat -> real) (i : nat) (h1 : term735) (h2 : term803 n c i) : term973 i n.
Proof. exact (conj (@lem7551627 n c i h1 h2) (@lem7551634 n c i h2)). Qed.
Lemma lem7551728 (_97394 : nat) (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term855 k n c i) : term976 n c _97394.
Proof. exact (EQ_MP (@lem7551724 n c _97394) (@lem7551707 _97394 k n c i h1)). Qed.
Lemma lem7551729 (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term855 k n c i) : term976 n c i.
Proof. exact (@lem7551728 i k n c i h1). Qed.
Lemma lem7551732 (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term735) (h2 : term803 n c i) (h3 : term855 k n c i) : (c i) = term10.
Proof. exact (@lem7551729 k n c i h3 (@lem7551726 n c i h1 h2)). Qed.
Lemma lem7551733 (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term735) (h2 : term803 n c i) (h3 : term855 k n c i) : term977 c i.
Proof. exact (fun h0 : term952 c i => @lem7551732 k n c i h1 h2 h3). Qed.
Lemma lem7551735 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7551736 (c : nat -> real) (i : nat) : (term977 c i) = ((c i) = term10).
Proof. exact (@lem7551735 ((c i) = term10)). Qed.
Lemma lem7551737 (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term735) (h2 : term803 n c i) (h3 : term855 k n c i) : (c i) = term10.
Proof. exact (EQ_MP (@lem7551736 c i) (@lem7551733 k n c i h1 h2 h3)). Qed.
Lemma lem7551740 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7551742 (c : nat -> real) (i : nat) : (term952 c i) = (term978 c i).
Proof. exact (@lem7551740 ((c i) = term10)). Qed.
Lemma lem7551745 (n : nat) (c : nat -> real) (i : nat) (h1 : term803 n c i) : term978 c i.
Proof. exact (EQ_MP (@lem7551742 c i) (@lem7551085 n c i h1)). Qed.
Lemma lem7551748 (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term735) (h2 : term803 n c i) (h3 : term855 k n c i) : False.
Proof. exact (@lem7551745 n c i h2 (@lem7551737 k n c i h1 h2 h3)). Qed.
Lemma lem7551749 (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term735) (h2 : term803 n c i) (h3 : term855 k n c i) : term157.
Proof. exact (fun h0 : ~ False => @lem7551748 k n c i h1 h2 h3). Qed.
Lemma lem7551751 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7551752 : term157 = False.
Proof. exact (@lem7551751 False). Qed.
Lemma lem7551829 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem7551830 (c : nat -> real) : (term477 c) = (term477 c).
Proof. exact (@lem7551829 (term477 c)). Qed.
Lemma lem7551831 (c : nat -> real) : term953 c.
Proof. exact (fun h0 : term949 c => @lem7551830 c). Qed.
Lemma lem7551833 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7551834 (c : nat -> real) : (term953 c) = ((term477 c) = (term477 c)).
Proof. exact (@lem7551833 ((term477 c) = (term477 c))). Qed.
Lemma lem7551835 (c : nat -> real) : (term477 c) = (term477 c).
Proof. exact (EQ_MP (@lem7551834 c) (@lem7551831 c)). Qed.
Lemma lem7551838 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7551840 (c : nat -> real) : (term949 c) = (term954 c).
Proof. exact (@lem7551838 ((term477 c) = (term477 c))). Qed.
Lemma lem7551843 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term835 c k) (h2 : term885 i k n c) : term954 c.
Proof. exact (EQ_MP (@lem7551840 c) (@lem7551239 i k n c h1 h2)). Qed.
Lemma lem7551846 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term835 c k) (h2 : term885 i k n c) : False.
Proof. exact (@lem7551843 i k n c h1 h2 (@lem7551835 c)). Qed.
Lemma lem7551847 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term835 c k) (h2 : term885 i k n c) : term157.
Proof. exact (fun h0 : ~ False => @lem7551846 i k n c h1 h2). Qed.
Lemma lem7551849 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7551850 : term157 = False.
Proof. exact (@lem7551849 False). Qed.
Lemma lem7551927 (n : nat) (c : nat -> real) (i : nat) (h1 : term782 n c i) : term45 i.
Proof. exact (proj1 (@lem7550096 n c i h1)). Qed.
Lemma lem7551928 (n : nat) (c : nat -> real) (i : nat) (h1 : term782 n c i) : term200 i.
Proof. exact (fun h0 : i = (NUMERAL 0) => @lem7551927 n c i h1). Qed.
Lemma lem7551930 (p : Prop) : (term170 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7551931 (i : nat) : (term200 i) = (term45 i).
Proof. exact (@lem7551930 (i = (NUMERAL 0))). Qed.
Lemma lem7551932 (n : nat) (c : nat -> real) (i : nat) (h1 : term782 n c i) : term45 i.
Proof. exact (EQ_MP (@lem7551931 i) (@lem7551928 n c i h1)). Qed.
Lemma lem7551938 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7551939 (_97403 : nat) : (term914 _97403) = (term979 _97403).
Proof. exact (@lem7551938 (term600 _97403) (_97403 = (NUMERAL 0))). Qed.
Lemma lem7551947 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7551948 (_97403 : nat) : (term980 _97403) = (term981 _97403).
Proof. exact (MK_COMB (@lem7551947) (@lem7551939 _97403)). Qed.
Lemma lem7551956 (_97403 : nat) : (term979 _97403) = (term979 _97403).
Proof. exact (eq_refl (term979 _97403)). Qed.
Lemma lem7551957 (_97403 : nat) : ((term914 _97403) = (term979 _97403)) = ((term979 _97403) = (term979 _97403)).
Proof. exact (MK_COMB (@lem7551948 _97403) (@lem7551956 _97403)). Qed.
Lemma lem7551959 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7551960 (x : Prop) : (x = x) = True.
Proof. exact (@lem7551959 Prop x). Qed.
Lemma lem7551961 (_97403 : nat) : ((term979 _97403) = (term979 _97403)) = True.
Proof. exact (@lem7551960 (term979 _97403)). Qed.
Lemma lem7551962 (_97403 : nat) : ((term914 _97403) = (term979 _97403)) = True.
Proof. exact (TRANS (@lem7551957 _97403) (@lem7551961 _97403)). Qed.
Lemma lem7551963 (_97403 : nat) : True = ((term914 _97403) = (term979 _97403)).
Proof. exact (SYM (@lem7551962 _97403)). Qed.
Lemma lem7551964 (_97403 : nat) : (term914 _97403) = (term979 _97403).
Proof. exact (EQ_MP (@lem7551963 _97403) (@lem0)). Qed.
Lemma lem7551965 (_97403 : nat) (h1 : term735) : term979 _97403.
Proof. exact (EQ_MP (@lem7551964 _97403) (@lem7551282 _97403 h1)). Qed.
Lemma lem7551967 (b : Prop) (a : Prop) : (a \/ b) = (term171 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7551970 (_97403 : nat) : (term979 _97403) = (term768 _97403).
Proof. exact (@lem7551967 (_97403 = (NUMERAL 0)) (term600 _97403)). Qed.
Lemma lem7551973 (_97403 : nat) (h1 : term735) : term768 _97403.
Proof. exact (EQ_MP (@lem7551970 _97403) (@lem7551965 _97403 h1)). Qed.
Lemma lem7551974 (i : nat) (h1 : term735) : term768 i.
Proof. exact (@lem7551973 i h1). Qed.
Lemma lem7551977 (n : nat) (c : nat -> real) (i : nat) (h1 : term735) (h2 : term782 n c i) : term600 i.
Proof. exact (@lem7551974 i h1 (@lem7551932 n c i h2)). Qed.
Lemma lem7551978 (n : nat) (c : nat -> real) (i : nat) (h1 : term735) (h2 : term782 n c i) : term955 i.
Proof. exact (fun h0 : term944 i => @lem7551977 n c i h1 h2). Qed.
Lemma lem7551980 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7551981 (i : nat) : (term955 i) = (term600 i).
Proof. exact (@lem7551980 (term600 i)). Qed.
Lemma lem7551982 (n : nat) (c : nat -> real) (i : nat) (h1 : term735) (h2 : term782 n c i) : term600 i.
Proof. exact (EQ_MP (@lem7551981 i) (@lem7551978 n c i h1 h2)). Qed.
Lemma lem7551984 (n : nat) (c : nat -> real) (i : nat) (h1 : term782 n c i) : Peano.le i n.
Proof. exact (proj1 (@lem7550097 n c i h1)). Qed.
Lemma lem7551985 (n : nat) (c : nat -> real) (i : nat) (h1 : term782 n c i) : term962 i n.
Proof. exact (fun h0 : term945 i n => @lem7551984 n c i h1). Qed.
Lemma lem7551987 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7551988 (i : nat) (n : nat) : (term962 i n) = (Peano.le i n).
Proof. exact (@lem7551987 (Peano.le i n)). Qed.
Lemma lem7551989 (n : nat) (c : nat -> real) (i : nat) (h1 : term782 n c i) : Peano.le i n.
Proof. exact (EQ_MP (@lem7551988 i n) (@lem7551985 n c i h1)). Qed.
Lemma lem7551995 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7551996 (n : nat) (c : nat -> real) (_97408 : nat) : (term943 n c _97408) = (term982 n c _97408).
Proof. exact (@lem7551995 (term945 _97408 n) (term944 _97408) ((c _97408) = term10)). Qed.
Lemma lem7552010 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7552011 (c : nat -> real) (_97408 : nat) : (term983 c _97408) = (term984 c _97408).
Proof. exact (@lem7552010 ((c _97408) = term10) (term944 _97408)). Qed.
Lemma lem7552019 (_97408 : nat) (n : nat) : (term985 _97408 n) = (term985 _97408 n).
Proof. exact (eq_refl (term985 _97408 n)). Qed.
Lemma lem7552020 (n : nat) (c : nat -> real) (_97408 : nat) : (term982 n c _97408) = (term986 n c _97408).
Proof. exact (MK_COMB (@lem7552019 _97408 n) (@lem7552011 c _97408)). Qed.
Lemma lem7552024 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7552025 (c : nat -> real) (n : nat) (_97408 : nat) : (term986 n c _97408) = (term987 c n _97408).
Proof. exact (@lem7552024 ((c _97408) = term10) (term945 _97408 n) (term944 _97408)). Qed.
Lemma lem7552043 (c : nat -> real) (n : nat) (_97408 : nat) : (term982 n c _97408) = (term987 c n _97408).
Proof. exact (TRANS (@lem7552020 n c _97408) (@lem7552025 c n _97408)). Qed.
Lemma lem7552044 (c : nat -> real) (n : nat) (_97408 : nat) : (term943 n c _97408) = (term987 c n _97408).
Proof. exact (TRANS (@lem7551996 n c _97408) (@lem7552043 c n _97408)). Qed.
Lemma lem7552045 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7552046 (c : nat -> real) (n : nat) (_97408 : nat) : (term988 n c _97408) = (term989 c n _97408).
Proof. exact (MK_COMB (@lem7552045) (@lem7552044 c n _97408)). Qed.
Lemma lem7552062 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7552063 (n : nat) (_97408 : nat) : (term801 _97408 n) = (term990 n _97408).
Proof. exact (@lem7552062 (term945 _97408 n) (term944 _97408)). Qed.
Lemma lem7552069 (c : nat -> real) (_97408 : nat) : (term991 c _97408) = (term991 c _97408).
Proof. exact (eq_refl (term991 c _97408)). Qed.
Lemma lem7552070 (c : nat -> real) (n : nat) (_97408 : nat) : (term992 c _97408 n) = (term987 c n _97408).
Proof. exact (MK_COMB (@lem7552069 c _97408) (@lem7552063 n _97408)). Qed.
Lemma lem7552081 (c : nat -> real) (n : nat) (_97408 : nat) : ((term943 n c _97408) = (term992 c _97408 n)) = ((term987 c n _97408) = (term987 c n _97408)).
Proof. exact (MK_COMB (@lem7552046 c n _97408) (@lem7552070 c n _97408)). Qed.
Lemma lem7552083 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7552084 (x : Prop) : (x = x) = True.
Proof. exact (@lem7552083 Prop x). Qed.
Lemma lem7552085 (c : nat -> real) (n : nat) (_97408 : nat) : ((term987 c n _97408) = (term987 c n _97408)) = True.
Proof. exact (@lem7552084 (term987 c n _97408)). Qed.
Lemma lem7552086 (c : nat -> real) (_97408 : nat) (n : nat) : ((term943 n c _97408) = (term992 c _97408 n)) = True.
Proof. exact (TRANS (@lem7552081 c n _97408) (@lem7552085 c n _97408)). Qed.
Lemma lem7552087 (c : nat -> real) (_97408 : nat) (n : nat) : True = ((term943 n c _97408) = (term992 c _97408 n)).
Proof. exact (SYM (@lem7552086 c _97408 n)). Qed.
Lemma lem7552088 (c : nat -> real) (_97408 : nat) (n : nat) : (term943 n c _97408) = (term992 c _97408 n).
Proof. exact (EQ_MP (@lem7552087 c _97408 n) (@lem0)). Qed.
Lemma lem7552089 (_97408 : nat) (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term885 i k n c) : term992 c _97408 n.
Proof. exact (EQ_MP (@lem7552088 c _97408 n) (@lem7551352 _97408 i k n c h1)). Qed.
Lemma lem7552091 (b : Prop) (a : Prop) : (a \/ b) = (term171 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7552092 (n : nat) (c : nat -> real) (_97408 : nat) : (term992 c _97408 n) = (term993 n c _97408).
Proof. exact (@lem7552091 (term801 _97408 n) ((c _97408) = term10)). Qed.
Lemma lem7552094 (a : Prop) (b : Prop) : (term174 a b) = (term175 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7552095 (_97408 : nat) (n : nat) : (term994 _97408 n) = (term995 _97408 n).
Proof. exact (@lem7552094 (term944 _97408) (term945 _97408 n)). Qed.
Lemma lem7552097 (a : Prop) : (term22 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7552098 (_97408 : nat) : (term959 _97408) = (term600 _97408).
Proof. exact (@lem7552097 (term600 _97408)). Qed.
Lemma lem7552099 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7552100 (_97408 : nat) : (term996 _97408) = (term601 _97408).
Proof. exact (MK_COMB (@lem7552099) (@lem7552098 _97408)). Qed.
Lemma lem7552102 (a : Prop) : (term22 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7552103 (_97408 : nat) (n : nat) : (term972 _97408 n) = (Peano.le _97408 n).
Proof. exact (@lem7552102 (Peano.le _97408 n)). Qed.
Lemma lem7552104 (_97408 : nat) (n : nat) : (term995 _97408 n) = (term602 _97408 n).
Proof. exact (MK_COMB (@lem7552100 _97408) (@lem7552103 _97408 n)). Qed.
Lemma lem7552105 (_97408 : nat) (n : nat) : (term994 _97408 n) = (term602 _97408 n).
Proof. exact (TRANS (@lem7552095 _97408 n) (@lem7552104 _97408 n)). Qed.
Lemma lem7552106 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7552107 (_97408 : nat) (n : nat) : (term997 _97408 n) = (term603 _97408 n).
Proof. exact (MK_COMB (@lem7552106) (@lem7552105 _97408 n)). Qed.
Lemma lem7552108 (c : nat -> real) (_97408 : nat) : ((c _97408) = term10) = ((c _97408) = term10).
Proof. exact (eq_refl ((c _97408) = term10)). Qed.
Lemma lem7552109 (n : nat) (c : nat -> real) (_97408 : nat) : (term993 n c _97408) = (term642 n c _97408).
Proof. exact (MK_COMB (@lem7552107 _97408 n) (@lem7552108 c _97408)). Qed.
Lemma lem7552110 (n : nat) (c : nat -> real) (_97408 : nat) : (term992 c _97408 n) = (term642 n c _97408).
Proof. exact (TRANS (@lem7552092 n c _97408) (@lem7552109 n c _97408)). Qed.
Lemma lem7552112 (n : nat) (c : nat -> real) (i : nat) (h1 : term735) (h2 : term782 n c i) : term602 i n.
Proof. exact (conj (@lem7551982 n c i h1 h2) (@lem7551989 n c i h2)). Qed.
Lemma lem7552114 (_97408 : nat) (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term885 i k n c) : term642 n c _97408.
Proof. exact (EQ_MP (@lem7552110 n c _97408) (@lem7552089 _97408 i k n c h1)). Qed.
Lemma lem7552115 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term885 i k n c) : term642 n c i.
Proof. exact (@lem7552114 i i k n c h1). Qed.
Lemma lem7552118 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term735) (h2 : term782 n c i) (h3 : term885 i k n c) : (c i) = term10.
Proof. exact (@lem7552115 i k n c h3 (@lem7552112 n c i h1 h2)). Qed.
Lemma lem7552119 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term735) (h2 : term782 n c i) (h3 : term885 i k n c) : term977 c i.
Proof. exact (fun h0 : term952 c i => @lem7552118 i k n c h1 h2 h3). Qed.
Lemma lem7552121 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7552122 (c : nat -> real) (i : nat) : (term977 c i) = ((c i) = term10).
Proof. exact (@lem7552121 ((c i) = term10)). Qed.
Lemma lem7552123 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term735) (h2 : term782 n c i) (h3 : term885 i k n c) : (c i) = term10.
Proof. exact (EQ_MP (@lem7552122 c i) (@lem7552119 i k n c h1 h2 h3)). Qed.
Lemma lem7552126 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7552128 (c : nat -> real) (i : nat) : (term952 c i) = (term978 c i).
Proof. exact (@lem7552126 ((c i) = term10)). Qed.
Lemma lem7552131 (n : nat) (c : nat -> real) (i : nat) (h1 : term782 n c i) : term978 c i.
Proof. exact (EQ_MP (@lem7552128 c i) (@lem7551394 n c i h1)). Qed.
Lemma lem7552134 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term735) (h2 : term782 n c i) (h3 : term885 i k n c) : False.
Proof. exact (@lem7552131 n c i h2 (@lem7552123 i k n c h1 h2 h3)). Qed.
Lemma lem7552135 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term735) (h2 : term782 n c i) (h3 : term885 i k n c) : term157.
Proof. exact (fun h0 : ~ False => @lem7552134 i k n c h1 h2 h3). Qed.
Lemma lem7552137 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7552138 : term157 = False.
Proof. exact (@lem7552137 False). Qed.
Lemma lem7552140 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term735) (h2 : term782 n c i) (h3 : term885 i k n c) : False.
Proof. exact (EQ_MP (@lem7552138) (@lem7552135 i k n c h1 h2 h3)). Qed.
Lemma lem7552141 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term835 c k) (h2 : term885 i k n c) : False.
Proof. exact (EQ_MP (@lem7551850) (@lem7551847 i k n c h1 h2)). Qed.
Lemma lem7552142 (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term735) (h2 : term803 n c i) (h3 : term855 k n c i) : False.
Proof. exact (EQ_MP (@lem7551752) (@lem7551749 k n c i h1 h2 h3)). Qed.
Lemma lem7552143 (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term835 c k) (h2 : term855 k n c i) : False.
Proof. exact (EQ_MP (@lem7551491) (@lem7551488 k n c i h1 h2)). Qed.
Lemma lem7552144 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term835 c k) (h2 : term885 i k n c) : (term835 c k) = False.
Proof. exact (prop_ext (fun h3 : term835 c k => @lem7552141 i k n c h1 h2) (fun h3 : False => @lem7550776 c k h1)). Qed.
Lemma lem7552145 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term835 c k) (h2 : term885 i k n c) : False.
Proof. exact (EQ_MP (@lem7552144 i k n c h1 h2) (@lem7550776 c k h1)). Qed.
Lemma lem7552146 (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term835 c k) (h2 : term855 k n c i) : (term835 c k) = False.
Proof. exact (prop_ext (fun h3 : term835 c k => @lem7552143 k n c i h1 h2) (fun h3 : False => @lem7550670 c k h1)). Qed.
Lemma lem7552147 (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term835 c k) (h2 : term855 k n c i) : False.
Proof. exact (EQ_MP (@lem7552146 k n c i h1 h2) (@lem7550670 c k h1)). Qed.
Lemma lem7552148 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term835 c k) (h2 : term885 i k n c) : (term835 c k) = False.
Proof. exact (prop_ext (fun h3 : term835 c k => @lem7552145 i k n c h1 h2) (fun h3 : False => @lem7550423 c k h1)). Qed.
Lemma lem7552149 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term835 c k) (h2 : term885 i k n c) : False.
Proof. exact (EQ_MP (@lem7552148 i k n c h1 h2) (@lem7550423 c k h1)). Qed.
Lemma lem7552150 (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term835 c k) (h2 : term855 k n c i) : (term835 c k) = False.
Proof. exact (prop_ext (fun h3 : term835 c k => @lem7552147 k n c i h1 h2) (fun h3 : False => @lem7550205 c k h1)). Qed.
Lemma lem7552151 (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term835 c k) (h2 : term855 k n c i) : False.
Proof. exact (EQ_MP (@lem7552150 k n c i h1 h2) (@lem7550205 c k h1)). Qed.
Lemma lem7552152 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term835 c k) (h2 : term885 i k n c) : (term835 c k) = False.
Proof. exact (prop_ext (fun h3 : term835 c k => @lem7552149 i k n c h1 h2) (fun h3 : False => @lem7550423 c k h1)). Qed.
Lemma lem7552153 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term835 c k) (h2 : term885 i k n c) : False.
Proof. exact (EQ_MP (@lem7552152 i k n c h1 h2) (@lem7550423 c k h1)). Qed.
Lemma lem7552154 (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term835 c k) (h2 : term855 k n c i) : (term835 c k) = False.
Proof. exact (prop_ext (fun h3 : term835 c k => @lem7552151 k n c i h1 h2) (fun h3 : False => @lem7550205 c k h1)). Qed.
Lemma lem7552155 (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term835 c k) (h2 : term855 k n c i) : False.
Proof. exact (EQ_MP (@lem7552154 k n c i h1 h2) (@lem7550205 c k h1)). Qed.
Lemma lem7552156 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term735) (h2 : term885 i k n c) : False.
Proof. exact (or_elim (@lem7550092 i k n c h2) (fun h0 : term835 c k => @lem7552153 i k n c h0 h2) (fun h0 : term782 n c i => @lem7552140 i k n c h1 h0 h2)). Qed.
Lemma lem7552157 (k : real) (n : nat) (c : nat -> real) (i : nat) (h1 : term735) (h2 : term855 k n c i) : False.
Proof. exact (or_elim (@lem7550081 k n c i h2) (fun h0 : term835 c k => @lem7552155 k n c i h0 h2) (fun h0 : term803 n c i => @lem7552142 k n c i h1 h0 h2)). Qed.
Lemma lem7552158 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term735) (h2 : term904 i k n c) : False.
Proof. exact (or_elim (@lem7550068 i k n c h2) (fun h0 : term855 k n c i => @lem7552157 k n c i h1 h0) (fun h0 : term885 i k n c => @lem7552156 i k n c h1 h0)). Qed.
Lemma lem7552159 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term735) (h2 : term904 i k n c) : (term904 i k n c) = False.
Proof. exact (prop_ext (fun h3 : term904 i k n c => @lem7552158 i k n c h1 h2) (fun h3 : False => @lem7550068 i k n c h2)). Qed.
Lemma lem7552160 (i : nat) (k : real) (n : nat) (c : nat -> real) (h1 : term735) (h2 : term904 i k n c) : False.
Proof. exact (EQ_MP (@lem7552159 i k n c h1 h2) (@lem7550068 i k n c h2)). Qed.
Lemma lem7552161 (k : real) (n : nat) (c : nat -> real) (h1 : term728 k n c) (h2 : term735) : False.
Proof. exact (ex_elim (@lem7549339 k n c h1) (fun i : nat => fun h0 : term906 k n c i => @lem7552160 i k n c h2 h0)). Qed.
Lemma lem7552162 (k : real) (n : nat) (c : nat -> real) (h1 : term728 k n c) : term733.
Proof. exact (fun h0 : term735 => @lem7552161 k n c h1 h0). Qed.
Lemma lem7552163 : term733 = term734.
Proof. exact (@lem69 term735). Qed.
Lemma lem7552164 (k : real) (n : nat) (c : nat -> real) (h1 : term728 k n c) : term734.
Proof. exact (EQ_MP (@lem7552163) (@lem7552162 k n c h1)). Qed.
Lemma lem7552165 (k : real) (n : nat) (c : nat -> real) : term737 k n c.
Proof. exact (fun h0 : term728 k n c => @lem7552164 k n c h0). Qed.
Lemma lem7552170 (n : nat) (c : nat -> real) : term741 n c.
Proof. exact (fun k : real => @lem7552165 k n c). Qed.
Lemma lem7552175 (c : nat -> real) : term745 c.
Proof. exact (fun n : nat => @lem7552170 n c). Qed.
Lemma lem7552180 : term749.
Proof. exact (fun c : nat -> real => @lem7552175 c). Qed.
Lemma lem7552181 : term748.
Proof. exact (EQ_MP (@lem7548909) (@lem7552180)). Qed.
Lemma lem7552182 (c : nat -> real) : term998 c.
Proof. exact (@lem7552181 c). Qed.
Lemma lem7552183 (c : nat -> real) : (term998 c) = (term744 c).
Proof. exact (eq_refl (term998 c)). Qed.
Lemma lem7552184 (c : nat -> real) : term744 c.
Proof. exact (EQ_MP (@lem7552183 c) (@lem7552182 c)). Qed.
Lemma lem7552185 (c : nat -> real) (n : nat) : term999 c n.
Proof. exact (@lem7552184 c n). Qed.
Lemma lem7552186 (n : nat) (c : nat -> real) : (term999 c n) = (term740 n c).
Proof. exact (eq_refl (term999 c n)). Qed.
Lemma lem7552187 (n : nat) (c : nat -> real) : term740 n c.
Proof. exact (EQ_MP (@lem7552186 n c) (@lem7552185 c n)). Qed.
Lemma lem7552188 (n : nat) (c : nat -> real) (k : real) : term1000 n c k.
Proof. exact (@lem7552187 n c k). Qed.
Lemma lem7552189 (k : real) (n : nat) (c : nat -> real) : (term1000 n c k) = (term729 k n c).
Proof. exact (eq_refl (term1000 n c k)). Qed.
Lemma lem7552190 (k : real) (n : nat) (c : nat -> real) : term729 k n c.
Proof. exact (EQ_MP (@lem7552189 k n c) (@lem7552188 n c k)). Qed.
Lemma lem7552192 (k : real) (n : nat) (c : nat -> real) : term729 k n c.
Proof. exact (@lem7548567 k n c (@lem7552190 k n c)). Qed.
Lemma lem7552193 (k : real) (n : nat) (c : nat -> real) (h1 : term728 k n c) : term733.
Proof. exact (@lem7552192 k n c (@lem7548552 k n c h1)). Qed.
Lemma lem7552194 (k : real) (n : nat) (c : nat -> real) (h1 : term728 k n c) : False.
Proof. exact (@lem7552193 k n c h1 (@lem99082)). Qed.
Lemma lem7552195 (k : real) (n : nat) (c : nat -> real) (h1 : term728 k n c) : (term728 k n c) = False.
Proof. exact (prop_ext (fun h2 : term728 k n c => @lem7552194 k n c h1) (fun h2 : False => @lem7548552 k n c h1)). Qed.
Lemma lem7552196 (k : real) (n : nat) (c : nat -> real) (h1 : term728 k n c) : False.
Proof. exact (EQ_MP (@lem7552195 k n c h1) (@lem7548552 k n c h1)). Qed.
Lemma lem7552197 (k : real) (n : nat) (c : nat -> real) : term727 k n c.
Proof. exact (fun h0 : term728 k n c => @lem7552196 k n c h0). Qed.
Lemma lem7552198 (k : real) (n : nat) (c : nat -> real) : (term725 k n c) = (term648 k n c).
Proof. exact (EQ_MP (@lem7548551 k n c) (@lem7552197 k n c)). Qed.
Lemma lem7552199 (k : real) (n : nat) (c : nat -> real) : (term664 n k c) = (term648 k n c).
Proof. exact (EQ_MP (@lem7548547 k n c) (@lem7552198 k n c)). Qed.
Lemma lem7552200 (k : real) (n : nat) (c : nat -> real) : (term637 n k c) = (term648 k n c).
Proof. exact (EQ_MP (@lem7547676 k n c) (@lem7552199 k n c)). Qed.
Lemma lem7552201 (k : real) (n : nat) (c : nat -> real) : (term516 n k c) = (term459 k n c).
Proof. exact (EQ_MP (@lem7547650 k n c) (@lem7552200 k n c)). Qed.
Lemma lem7552202 (k : real) (n : nat) (c : nat -> real) : term1001 k n c.
Proof. exact (conj (@lem7547533 n k c) (@lem7552201 k n c)). Qed.
Lemma lem7552203 (k : real) (n : nat) (c : nat -> real) : term1002 k n c.
Proof. exact (ex_intro (term1003 k n c) (term516 n k c) (@lem7552202 k n c)). Qed.
Lemma lem7552204 (k : real) (n : nat) (c : nat -> real) : (term458 n c k) = (term459 k n c).
Proof. exact (@lem7543002 k n c (@lem7552203 k n c)). Qed.
Lemma lem7552209 (n : nat) (c : nat -> real) : term1004 n c.
Proof. exact (fun k : real => @lem7552204 k n c). Qed.
Lemma lem7552214 (n : nat) : term1005 n.
Proof. exact (fun c : nat -> real => @lem7552209 n c). Qed.
Lemma lem7552219 : term1006.
Proof. exact (fun n : nat => @lem7552214 n). Qed.
