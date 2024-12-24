Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DEPENDENT_CHOICE_FIXED_term_abbrevs.
Require Import AND_FORALL_THM_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import MONO_EXISTS_spec.
Require Import num_CASES_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18946_spec.
Require Import thm18947_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19490_spec.
Require Import thm19728_spec.
Require Import thm19732_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
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
Require Import thm51_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm75635_spec.
Lemma lem290485 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem290486 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem290487 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem290486 t1) (@lem290485 t1)). Qed.
Lemma lem290488 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem290487 t1 t2). Qed.
Lemma lem290489 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem290490 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem290489 t1 t2) (@lem290488 t1 t2)). Qed.
Lemma lem290491 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem290490 t1 t2 t3). Qed.
Lemma lem290492 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem290493 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem290492 t1 t2 t3) (@lem290491 t1 t2 t3)). Qed.
Lemma lem290494 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem290493 t1 t2 t3)). Qed.
Lemma lem290506 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem290507 (P : nat -> Prop) : ((term8 P) = (term9 P)) = (term10 P).
Proof. exact (@lem290506 ((term8 P) = (term9 P))). Qed.
Lemma lem290508 (P : nat -> Prop) : (term10 P) = ((term8 P) = (term9 P)).
Proof. exact (SYM (@lem290507 P)). Qed.
Lemma lem290509 (P : nat -> Prop) (h1 : term11 P) : term11 P.
Proof. exact (h1). Qed.
Lemma lem290512 (P : nat -> Prop) (h1 : term12 P) : term12 P.
Proof. exact (h1). Qed.
Lemma lem290513 (P : nat -> Prop) : term13 P.
Proof. exact (fun h0 : term12 P => @lem290512 P h0). Qed.
Lemma lem290514 (P : nat -> Prop) (h1 : term13 P) : term13 P.
Proof. exact (h1). Qed.
Lemma lem290515 (P : nat -> Prop) (h1 : term12 P) : term12 P.
Proof. exact (h1). Qed.
Lemma lem290516 (P : nat -> Prop) (h1 : term12 P) (h2 : term13 P) : term12 P.
Proof. exact (@lem290514 P h2 (@lem290515 P h1)). Qed.
Lemma lem290517 (P : nat -> Prop) (h1 : term12 P) : term14 P.
Proof. exact (fun h0 : term13 P => @lem290516 P h1 h0). Qed.
Lemma lem290518 (P : nat -> Prop) (h1 : term13 P) : term13 P.
Proof. exact (h1). Qed.
Lemma lem290519 (P : nat -> Prop) (h1 : term12 P) (h2 : term13 P) : term12 P.
Proof. exact (@lem290517 P h1 (@lem290518 P h2)). Qed.
Lemma lem290520 (P : nat -> Prop) (h1 : term13 P) : term13 P.
Proof. exact (fun h0 : term12 P => @lem290519 P h0 h1). Qed.
Lemma lem290521 (P : nat -> Prop) : term15 P.
Proof. exact (fun h0 : term13 P => @lem290520 P h0). Qed.
Lemma lem290524 (P : nat -> Prop) : term13 P.
Proof. exact (@lem290521 P (@lem290513 P)). Qed.
Lemma lem290542 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem290543 : term16 = term17.
Proof. exact (@lem290542 term18). Qed.
Lemma lem290598 (P : nat -> Prop) : (term19 P) = (term19 P).
Proof. exact (eq_refl (term19 P)). Qed.
Lemma lem290599 (P : nat -> Prop) : (term12 P) = (term20 P).
Proof. exact (MK_COMB (@lem290598 P) (@lem290543)). Qed.
Lemma lem290602 : term21 = term22.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem290599 P)). Qed.
Lemma lem290603 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem290612 : term23 = term24.
Proof. exact (MK_COMB (@lem290603) (@lem290602)). Qed.
Lemma lem290613 (m : nat) (n : nat) : (m = (S n)) = (m = (S n)).
Proof. exact (eq_refl (m = (S n))). Qed.
Lemma lem290614 (m : nat) : (term25 m) = (term25 m).
Proof. exact (fun_ext (fun n : nat => @lem290613 m n)). Qed.
Lemma lem290615 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem290616 (m : nat) : (term26 m) = (term26 m).
Proof. exact (MK_COMB (@lem290615) (@lem290614 m)). Qed.
Lemma lem290619 (m : nat) : (term27 m) = (term27 m).
Proof. exact (eq_refl (term27 m)). Qed.
Lemma lem290620 (m : nat) : (term28 m) = (term28 m).
Proof. exact (MK_COMB (@lem290619 m) (@lem290616 m)). Qed.
Lemma lem290621 : term29 = term29.
Proof. exact (fun_ext (fun m : nat => @lem290620 m)). Qed.
Lemma lem290622 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem290623 : term18 = term18.
Proof. exact (MK_COMB (@lem290622) (@lem290621)). Qed.
Lemma lem290624 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem290625 : term17 = term17.
Proof. exact (MK_COMB (@lem290624) (@lem290623)). Qed.
Lemma lem290626 (P : nat -> Prop) (n : nat) : (term30 P n) = (term30 P n).
Proof. exact (eq_refl (term30 P n)). Qed.
Lemma lem290627 (P : nat -> Prop) : (term31 P) = (term31 P).
Proof. exact (fun_ext (fun n : nat => @lem290626 P n)). Qed.
Lemma lem290628 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem290629 (P : nat -> Prop) : (term32 P) = (term32 P).
Proof. exact (MK_COMB (@lem290628) (@lem290627 P)). Qed.
Lemma lem290632 (P : nat -> Prop) : (term33 P) = (term33 P).
Proof. exact (eq_refl (term33 P)). Qed.
Lemma lem290633 (P : nat -> Prop) : (term9 P) = (term9 P).
Proof. exact (MK_COMB (@lem290632 P) (@lem290629 P)). Qed.
Lemma lem290634 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem290635 (P : nat -> Prop) : (term34 P) = (term34 P).
Proof. exact (fun_ext (fun n : nat => @lem290634 P n)). Qed.
Lemma lem290636 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem290637 (P : nat -> Prop) : (term8 P) = (term8 P).
Proof. exact (MK_COMB (@lem290636) (@lem290635 P)). Qed.
Lemma lem290638 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem290639 (P : nat -> Prop) : (term35 P) = (term35 P).
Proof. exact (MK_COMB (@lem290638) (@lem290637 P)). Qed.
Lemma lem290640 (P : nat -> Prop) : ((term8 P) = (term9 P)) = ((term8 P) = (term9 P)).
Proof. exact (MK_COMB (@lem290639 P) (@lem290633 P)). Qed.
Lemma lem290641 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem290642 (P : nat -> Prop) : (term11 P) = (term11 P).
Proof. exact (MK_COMB (@lem290641) (@lem290640 P)). Qed.
Lemma lem290643 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem290644 (P : nat -> Prop) : (term19 P) = (term19 P).
Proof. exact (MK_COMB (@lem290643) (@lem290642 P)). Qed.
Lemma lem290645 (P : nat -> Prop) : (term20 P) = (term20 P).
Proof. exact (MK_COMB (@lem290644 P) (@lem290625)). Qed.
Lemma lem290646 : term22 = term22.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem290645 P)). Qed.
Lemma lem290647 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem290648 : term24 = term24.
Proof. exact (MK_COMB (@lem290647) (@lem290646)). Qed.
Lemma lem290687 : term23 = term24.
Proof. exact (TRANS (@lem290612) (@lem290648)). Qed.
Lemma lem290688 : term24 = term23.
Proof. exact (SYM (@lem290687)). Qed.
Lemma lem290689 (P : nat -> Prop) (h1 : term11 P) : term11 P.
Proof. exact (h1). Qed.
Lemma lem290690 (h1 : term18) : term18.
Proof. exact (h1). Qed.
Lemma lem290692 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem290693 (P : nat -> Prop) : (term36 P) = (term37 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem290694 (P : nat -> Prop) : (term38 P) = (term39 P).
Proof. exact (@lem290693 (term34 P)). Qed.
Lemma lem290695 (P : nat -> Prop) (n : nat) : (term40 P n) = (P n).
Proof. exact (eq_refl (term40 P n)). Qed.
Lemma lem290696 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem290698 (P : nat -> Prop) (n : nat) : (term41 P n) = (term42 P n).
Proof. exact (MK_COMB (@lem290696) (@lem290695 P n)). Qed.
Lemma lem290699 (P : nat -> Prop) : (term43 P) = (term44 P).
Proof. exact (fun_ext (fun n : nat => @lem290698 P n)). Qed.
Lemma lem290700 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem290701 (P : nat -> Prop) : (term39 P) = (term37 P).
Proof. exact (MK_COMB (@lem290700) (@lem290699 P)). Qed.
Lemma lem290702 (P : nat -> Prop) : (term38 P) = (term37 P).
Proof. exact (TRANS (@lem290694 P) (@lem290701 P)). Qed.
Lemma lem290703 (P : nat -> Prop) : (term34 P) = (term34 P).
Proof. exact (fun_ext (fun n : nat => @lem290692 P n)). Qed.
Lemma lem290704 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem290705 (P : nat -> Prop) : (term8 P) = (term8 P).
Proof. exact (MK_COMB (@lem290704) (@lem290703 P)). Qed.
Lemma lem290709 (P : nat -> Prop) (n : nat) : (term30 P n) = (term30 P n).
Proof. exact (eq_refl (term30 P n)). Qed.
Lemma lem290710 (P : nat -> Prop) : (term36 P) = (term37 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem290711 (P : nat -> Prop) : (term45 P) = (term46 P).
Proof. exact (@lem290710 (term31 P)). Qed.
Lemma lem290712 (P : nat -> Prop) (n : nat) : (term47 P n) = (term30 P n).
Proof. exact (eq_refl (term47 P n)). Qed.
Lemma lem290713 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem290715 (P : nat -> Prop) (n : nat) : (term48 P n) = (term49 P n).
Proof. exact (MK_COMB (@lem290713) (@lem290712 P n)). Qed.
Lemma lem290716 (P : nat -> Prop) : (term50 P) = (term51 P).
Proof. exact (fun_ext (fun n : nat => @lem290715 P n)). Qed.
Lemma lem290717 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem290718 (P : nat -> Prop) : (term46 P) = (term52 P).
Proof. exact (MK_COMB (@lem290717) (@lem290716 P)). Qed.
Lemma lem290719 (P : nat -> Prop) : (term45 P) = (term52 P).
Proof. exact (TRANS (@lem290711 P) (@lem290718 P)). Qed.
Lemma lem290720 (P : nat -> Prop) : (term31 P) = (term31 P).
Proof. exact (fun_ext (fun n : nat => @lem290709 P n)). Qed.
Lemma lem290721 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem290722 (P : nat -> Prop) : (term32 P) = (term32 P).
Proof. exact (MK_COMB (@lem290721) (@lem290720 P)). Qed.
Lemma lem290724 (P : nat -> Prop) : (term53 P) = (term53 P).
Proof. exact (eq_refl (term53 P)). Qed.
Lemma lem290725 (P : nat -> Prop) : (term54 P) = (term55 P).
Proof. exact (MK_COMB (@lem290724 P) (@lem290719 P)). Qed.
Lemma lem290726 (P : nat -> Prop) : (term56 P) = (term54 P).
Proof. exact (@lem17045 (term57 P) (term32 P)). Qed.
Lemma lem290727 (P : nat -> Prop) : (term56 P) = (term55 P).
Proof. exact (TRANS (@lem290726 P) (@lem290725 P)). Qed.
Lemma lem290729 (P : nat -> Prop) : (term33 P) = (term33 P).
Proof. exact (eq_refl (term33 P)). Qed.
Lemma lem290730 (P : nat -> Prop) : (term9 P) = (term9 P).
Proof. exact (MK_COMB (@lem290729 P) (@lem290722 P)). Qed.
Lemma lem290731 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem290732 (P : nat -> Prop) : (term58 P) = (term59 P).
Proof. exact (MK_COMB (@lem290731) (@lem290702 P)). Qed.
Lemma lem290733 (P : nat -> Prop) : (term60 P) = (term61 P).
Proof. exact (MK_COMB (@lem290732 P) (@lem290730 P)). Qed.
Lemma lem290734 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem290735 (P : nat -> Prop) : (term62 P) = (term62 P).
Proof. exact (MK_COMB (@lem290734) (@lem290705 P)). Qed.
Lemma lem290736 (P : nat -> Prop) : (term63 P) = (term64 P).
Proof. exact (MK_COMB (@lem290735 P) (@lem290727 P)). Qed.
Lemma lem290737 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem290738 (P : nat -> Prop) : (term65 P) = (term66 P).
Proof. exact (MK_COMB (@lem290737) (@lem290736 P)). Qed.
Lemma lem290739 (P : nat -> Prop) : (term67 P) = (term68 P).
Proof. exact (MK_COMB (@lem290738 P) (@lem290733 P)). Qed.
Lemma lem290740 (P : nat -> Prop) : (term11 P) = (term67 P).
Proof. exact (@lem17646 (term8 P) (term9 P)). Qed.
Lemma lem290741 (P : nat -> Prop) : (term11 P) = (term68 P).
Proof. exact (TRANS (@lem290740 P) (@lem290739 P)). Qed.
Lemma lem290760 {A : Type'} (P : Prop) (Q : A -> Prop) : (term69 A P Q) = (term70 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem290761 (P : Prop) (Q : nat -> Prop) : (term71 P Q) = (term72 P Q).
Proof. exact (@lem290760 nat P Q). Qed.
Lemma lem290762 (P : nat -> Prop) : (term73 P) = (term74 P).
Proof. exact (@lem290761 (term75 P) (term51 P)). Qed.
Lemma lem290763 (P : nat -> Prop) (n : nat) : (term76 P n) = (term49 P n).
Proof. exact (eq_refl (term76 P n)). Qed.
Lemma lem290764 (P : nat -> Prop) : (term77 P) = (term51 P).
Proof. exact (fun_ext (fun n : nat => @lem290763 P n)). Qed.
Lemma lem290765 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem290766 (P : nat -> Prop) : (term78 P) = (term52 P).
Proof. exact (MK_COMB (@lem290765) (@lem290764 P)). Qed.
Lemma lem290767 (P : nat -> Prop) : (term53 P) = (term53 P).
Proof. exact (eq_refl (term53 P)). Qed.
Lemma lem290768 (P : nat -> Prop) : (term73 P) = (term55 P).
Proof. exact (MK_COMB (@lem290767 P) (@lem290766 P)). Qed.
Lemma lem290769 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem290770 (P : nat -> Prop) : (term79 P) = (term80 P).
Proof. exact (MK_COMB (@lem290769) (@lem290768 P)). Qed.
Lemma lem290771 (P : nat -> Prop) (n : nat) : (term76 P n) = (term49 P n).
Proof. exact (eq_refl (term76 P n)). Qed.
Lemma lem290772 (P : nat -> Prop) : (term53 P) = (term53 P).
Proof. exact (eq_refl (term53 P)). Qed.
Lemma lem290773 (P : nat -> Prop) (n : nat) : (term81 P n) = (term82 P n).
Proof. exact (MK_COMB (@lem290772 P) (@lem290771 P n)). Qed.
Lemma lem290774 (P : nat -> Prop) : (term83 P) = (term84 P).
Proof. exact (fun_ext (fun n : nat => @lem290773 P n)). Qed.
Lemma lem290775 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem290776 (P : nat -> Prop) : (term74 P) = (term85 P).
Proof. exact (MK_COMB (@lem290775) (@lem290774 P)). Qed.
Lemma lem290777 (P : nat -> Prop) : ((term73 P) = (term74 P)) = ((term55 P) = (term85 P)).
Proof. exact (MK_COMB (@lem290770 P) (@lem290776 P)). Qed.
Lemma lem290778 (P : nat -> Prop) : (term55 P) = (term85 P).
Proof. exact (EQ_MP (@lem290777 P) (@lem290762 P)). Qed.
Lemma lem290779 (P : nat -> Prop) : (term62 P) = (term62 P).
Proof. exact (eq_refl (term62 P)). Qed.
Lemma lem290780 (P : nat -> Prop) : (term64 P) = (term86 P).
Proof. exact (MK_COMB (@lem290779 P) (@lem290778 P)). Qed.
Lemma lem290782 {A : Type'} (P : Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem290783 (P : Prop) (Q : nat -> Prop) : (term89 P Q) = (term90 P Q).
Proof. exact (@lem290782 nat P Q). Qed.
Lemma lem290784 (P : nat -> Prop) : (term91 P) = (term92 P).
Proof. exact (@lem290783 (term8 P) (term84 P)). Qed.
Lemma lem290785 (P : nat -> Prop) (n : nat) : (term93 P n) = (term82 P n).
Proof. exact (eq_refl (term93 P n)). Qed.
Lemma lem290786 (P : nat -> Prop) : (term94 P) = (term84 P).
Proof. exact (fun_ext (fun n : nat => @lem290785 P n)). Qed.
Lemma lem290787 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem290788 (P : nat -> Prop) : (term95 P) = (term85 P).
Proof. exact (MK_COMB (@lem290787) (@lem290786 P)). Qed.
Lemma lem290789 (P : nat -> Prop) : (term62 P) = (term62 P).
Proof. exact (eq_refl (term62 P)). Qed.
Lemma lem290790 (P : nat -> Prop) : (term91 P) = (term86 P).
Proof. exact (MK_COMB (@lem290789 P) (@lem290788 P)). Qed.
Lemma lem290791 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem290792 (P : nat -> Prop) : (term96 P) = (term97 P).
Proof. exact (MK_COMB (@lem290791) (@lem290790 P)). Qed.
Lemma lem290793 (P : nat -> Prop) (n : nat) : (term93 P n) = (term82 P n).
Proof. exact (eq_refl (term93 P n)). Qed.
Lemma lem290794 (P : nat -> Prop) : (term62 P) = (term62 P).
Proof. exact (eq_refl (term62 P)). Qed.
Lemma lem290795 (P : nat -> Prop) (n : nat) : (term98 P n) = (term99 P n).
Proof. exact (MK_COMB (@lem290794 P) (@lem290793 P n)). Qed.
Lemma lem290796 (P : nat -> Prop) : (term100 P) = (term101 P).
Proof. exact (fun_ext (fun n : nat => @lem290795 P n)). Qed.
Lemma lem290797 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem290798 (P : nat -> Prop) : (term92 P) = (term102 P).
Proof. exact (MK_COMB (@lem290797) (@lem290796 P)). Qed.
Lemma lem290799 (P : nat -> Prop) : ((term91 P) = (term92 P)) = ((term86 P) = (term102 P)).
Proof. exact (MK_COMB (@lem290792 P) (@lem290798 P)). Qed.
Lemma lem290800 (P : nat -> Prop) : (term86 P) = (term102 P).
Proof. exact (EQ_MP (@lem290799 P) (@lem290784 P)). Qed.
Lemma lem290801 (P : nat -> Prop) : (term64 P) = (term102 P).
Proof. exact (TRANS (@lem290780 P) (@lem290800 P)). Qed.
Lemma lem290802 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem290803 (P : nat -> Prop) : (term66 P) = (term103 P).
Proof. exact (MK_COMB (@lem290802) (@lem290801 P)). Qed.
Lemma lem290805 {A : Type'} (P : A -> Prop) (Q : Prop) : (term104 A P Q) = (term105 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem290806 (P : nat -> Prop) (Q : Prop) : (term106 P Q) = (term107 P Q).
Proof. exact (@lem290805 nat P Q). Qed.
Lemma lem290807 (P : nat -> Prop) : (term108 P) = (term109 P).
Proof. exact (@lem290806 (term44 P) (term9 P)). Qed.
Lemma lem290808 (P : nat -> Prop) (n : nat) : (term110 P n) = (term42 P n).
Proof. exact (eq_refl (term110 P n)). Qed.
Lemma lem290809 (P : nat -> Prop) : (term111 P) = (term44 P).
Proof. exact (fun_ext (fun n : nat => @lem290808 P n)). Qed.
Lemma lem290810 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem290811 (P : nat -> Prop) : (term112 P) = (term37 P).
Proof. exact (MK_COMB (@lem290810) (@lem290809 P)). Qed.
Lemma lem290812 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem290813 (P : nat -> Prop) : (term113 P) = (term59 P).
Proof. exact (MK_COMB (@lem290812) (@lem290811 P)). Qed.
Lemma lem290814 (P : nat -> Prop) : (term9 P) = (term9 P).
Proof. exact (eq_refl (term9 P)). Qed.
Lemma lem290815 (P : nat -> Prop) : (term108 P) = (term61 P).
Proof. exact (MK_COMB (@lem290813 P) (@lem290814 P)). Qed.
Lemma lem290816 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem290817 (P : nat -> Prop) : (term114 P) = (term115 P).
Proof. exact (MK_COMB (@lem290816) (@lem290815 P)). Qed.
Lemma lem290818 (P : nat -> Prop) (n : nat) : (term110 P n) = (term42 P n).
Proof. exact (eq_refl (term110 P n)). Qed.
Lemma lem290819 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem290820 (P : nat -> Prop) (n : nat) : (term116 P n) = (term117 P n).
Proof. exact (MK_COMB (@lem290819) (@lem290818 P n)). Qed.
Lemma lem290821 (P : nat -> Prop) : (term9 P) = (term9 P).
Proof. exact (eq_refl (term9 P)). Qed.
Lemma lem290822 (n : nat) (P : nat -> Prop) : (term118 n P) = (term119 n P).
Proof. exact (MK_COMB (@lem290820 P n) (@lem290821 P)). Qed.
Lemma lem290823 (P : nat -> Prop) : (term120 P) = (term121 P).
Proof. exact (fun_ext (fun n : nat => @lem290822 n P)). Qed.
Lemma lem290824 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem290825 (P : nat -> Prop) : (term109 P) = (term122 P).
Proof. exact (MK_COMB (@lem290824) (@lem290823 P)). Qed.
Lemma lem290826 (P : nat -> Prop) : ((term108 P) = (term109 P)) = ((term61 P) = (term122 P)).
Proof. exact (MK_COMB (@lem290817 P) (@lem290825 P)). Qed.
Lemma lem290827 (P : nat -> Prop) : (term61 P) = (term122 P).
Proof. exact (EQ_MP (@lem290826 P) (@lem290807 P)). Qed.
Lemma lem290828 (P : nat -> Prop) : (term68 P) = (term123 P).
Proof. exact (MK_COMB (@lem290803 P) (@lem290827 P)). Qed.
Lemma lem290830 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term124 A P Q) = (term125 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem290831 (P : nat -> Prop) (Q : nat -> Prop) : (term126 P Q) = (term127 P Q).
Proof. exact (@lem290830 nat P Q). Qed.
Lemma lem290832 (P : nat -> Prop) : (term128 P) = (term129 P).
Proof. exact (@lem290831 (term101 P) (term121 P)). Qed.
Lemma lem290833 (P : nat -> Prop) (n : nat) : (term130 P n) = (term99 P n).
Proof. exact (eq_refl (term130 P n)). Qed.
Lemma lem290834 (P : nat -> Prop) : (term131 P) = (term101 P).
Proof. exact (fun_ext (fun n : nat => @lem290833 P n)). Qed.
Lemma lem290835 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem290836 (P : nat -> Prop) : (term132 P) = (term102 P).
Proof. exact (MK_COMB (@lem290835) (@lem290834 P)). Qed.
Lemma lem290837 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem290838 (P : nat -> Prop) : (term133 P) = (term103 P).
Proof. exact (MK_COMB (@lem290837) (@lem290836 P)). Qed.
Lemma lem290839 (n : nat) (P : nat -> Prop) : (term134 P n) = (term119 n P).
Proof. exact (eq_refl (term134 P n)). Qed.
Lemma lem290840 (P : nat -> Prop) : (term135 P) = (term121 P).
Proof. exact (fun_ext (fun n : nat => @lem290839 n P)). Qed.
Lemma lem290841 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem290842 (P : nat -> Prop) : (term136 P) = (term122 P).
Proof. exact (MK_COMB (@lem290841) (@lem290840 P)). Qed.
Lemma lem290843 (P : nat -> Prop) : (term128 P) = (term123 P).
Proof. exact (MK_COMB (@lem290838 P) (@lem290842 P)). Qed.
Lemma lem290844 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem290845 (P : nat -> Prop) : (term137 P) = (term138 P).
Proof. exact (MK_COMB (@lem290844) (@lem290843 P)). Qed.
Lemma lem290846 (P : nat -> Prop) (n : nat) : (term130 P n) = (term99 P n).
Proof. exact (eq_refl (term130 P n)). Qed.
Lemma lem290847 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem290848 (P : nat -> Prop) (n : nat) : (term139 P n) = (term140 P n).
Proof. exact (MK_COMB (@lem290847) (@lem290846 P n)). Qed.
Lemma lem290849 (n : nat) (P : nat -> Prop) : (term134 P n) = (term119 n P).
Proof. exact (eq_refl (term134 P n)). Qed.
Lemma lem290850 (n : nat) (P : nat -> Prop) : (term141 P n) = (term142 n P).
Proof. exact (MK_COMB (@lem290848 P n) (@lem290849 n P)). Qed.
Lemma lem290851 (P : nat -> Prop) : (term143 P) = (term144 P).
Proof. exact (fun_ext (fun n : nat => @lem290850 n P)). Qed.
Lemma lem290852 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem290853 (P : nat -> Prop) : (term129 P) = (term145 P).
Proof. exact (MK_COMB (@lem290852) (@lem290851 P)). Qed.
Lemma lem290854 (P : nat -> Prop) : ((term128 P) = (term129 P)) = ((term123 P) = (term145 P)).
Proof. exact (MK_COMB (@lem290845 P) (@lem290853 P)). Qed.
Lemma lem290855 (P : nat -> Prop) : (term123 P) = (term145 P).
Proof. exact (EQ_MP (@lem290854 P) (@lem290832 P)). Qed.
Lemma lem290857 (P : nat -> Prop) : (term68 P) = (term145 P).
Proof. exact (TRANS (@lem290828 P) (@lem290855 P)). Qed.
Lemma lem290858 (P : nat -> Prop) : (term11 P) = (term145 P).
Proof. exact (TRANS (@lem290741 P) (@lem290857 P)). Qed.
Lemma lem290859 (P : nat -> Prop) (h1 : term11 P) : term145 P.
Proof. exact (EQ_MP (@lem290858 P) (@lem290689 P h1)). Qed.
Lemma lem290861 (m : nat) (n : nat) : (m = (S n)) = (m = (S n)).
Proof. exact (eq_refl (m = (S n))). Qed.
Lemma lem290862 (m : nat) : (term25 m) = (term25 m).
Proof. exact (fun_ext (fun n : nat => @lem290861 m n)). Qed.
Lemma lem290863 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem290864 (m : nat) : (term26 m) = (term26 m).
Proof. exact (MK_COMB (@lem290863) (@lem290862 m)). Qed.
Lemma lem290866 (m : nat) : (term27 m) = (term27 m).
Proof. exact (eq_refl (term27 m)). Qed.
Lemma lem290867 (m : nat) : (term28 m) = (term28 m).
Proof. exact (MK_COMB (@lem290866 m) (@lem290864 m)). Qed.
Lemma lem290868 : term29 = term29.
Proof. exact (fun_ext (fun m : nat => @lem290867 m)). Qed.
Lemma lem290869 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem290870 : term18 = term18.
Proof. exact (MK_COMB (@lem290869) (@lem290868)). Qed.
Lemma lem290925 {A : Type'} (P : Prop) (Q : A -> Prop) : (term69 A P Q) = (term70 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem290926 (P : Prop) (Q : nat -> Prop) : (term71 P Q) = (term72 P Q).
Proof. exact (@lem290925 nat P Q). Qed.
Lemma lem290927 (m : nat) : (term146 m) = (term147 m).
Proof. exact (@lem290926 (m = (NUMERAL 0)) (term25 m)). Qed.
Lemma lem290928 (m : nat) (n : nat) : (term148 m n) = (m = (S n)).
Proof. exact (eq_refl (term148 m n)). Qed.
Lemma lem290929 (m : nat) : (term149 m) = (term25 m).
Proof. exact (fun_ext (fun n : nat => @lem290928 m n)). Qed.
Lemma lem290930 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem290931 (m : nat) : (term150 m) = (term26 m).
Proof. exact (MK_COMB (@lem290930) (@lem290929 m)). Qed.
Lemma lem290932 (m : nat) : (term27 m) = (term27 m).
Proof. exact (eq_refl (term27 m)). Qed.
Lemma lem290933 (m : nat) : (term146 m) = (term28 m).
Proof. exact (MK_COMB (@lem290932 m) (@lem290931 m)). Qed.
Lemma lem290934 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem290935 (m : nat) : (term151 m) = (term152 m).
Proof. exact (MK_COMB (@lem290934) (@lem290933 m)). Qed.
Lemma lem290936 (m : nat) (n : nat) : (term148 m n) = (m = (S n)).
Proof. exact (eq_refl (term148 m n)). Qed.
Lemma lem290937 (m : nat) : (term27 m) = (term27 m).
Proof. exact (eq_refl (term27 m)). Qed.
Lemma lem290938 (m : nat) (n : nat) : (term153 m n) = (term154 m n).
Proof. exact (MK_COMB (@lem290937 m) (@lem290936 m n)). Qed.
Lemma lem290939 (m : nat) : (term155 m) = (term156 m).
Proof. exact (fun_ext (fun n : nat => @lem290938 m n)). Qed.
Lemma lem290940 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem290941 (m : nat) : (term147 m) = (term157 m).
Proof. exact (MK_COMB (@lem290940) (@lem290939 m)). Qed.
Lemma lem290942 (m : nat) : ((term146 m) = (term147 m)) = ((term28 m) = (term157 m)).
Proof. exact (MK_COMB (@lem290935 m) (@lem290941 m)). Qed.
Lemma lem290943 (m : nat) : (term28 m) = (term157 m).
Proof. exact (EQ_MP (@lem290942 m) (@lem290927 m)). Qed.
Lemma lem290944 : term29 = term158.
Proof. exact (fun_ext (fun m : nat => @lem290943 m)). Qed.
Lemma lem290945 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem290946 : term18 = term159.
Proof. exact (MK_COMB (@lem290945) (@lem290944)). Qed.
Lemma lem290948 {A B : Type'} (P : type1413 A B) : (term160 A B P) = (term161 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem290949 (P : type1605) : (term162 P) = (term163 P).
Proof. exact (@lem290948 nat nat P). Qed.
Lemma lem290950 : term164 = term165.
Proof. exact (@lem290949 term166). Qed.
Lemma lem290951 (m : nat) : (term167 m) = (term156 m).
Proof. exact (eq_refl (term167 m)). Qed.
Lemma lem290952 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem290953 (m : nat) (n : nat) : (term168 m n) = (term169 m n).
Proof. exact (MK_COMB (@lem290951 m) (@lem290952 n)). Qed.
Lemma lem290954 (m : nat) (n : nat) : (term169 m n) = (term154 m n).
Proof. exact (eq_refl (term169 m n)). Qed.
Lemma lem290955 (m : nat) (n : nat) : (term168 m n) = (term154 m n).
Proof. exact (TRANS (@lem290953 m n) (@lem290954 m n)). Qed.
Lemma lem290956 (m : nat) : (term170 m) = (term156 m).
Proof. exact (fun_ext (fun n : nat => @lem290955 m n)). Qed.
Lemma lem290957 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem290958 (m : nat) : (term171 m) = (term157 m).
Proof. exact (MK_COMB (@lem290957) (@lem290956 m)). Qed.
Lemma lem290959 : term172 = term158.
Proof. exact (fun_ext (fun m : nat => @lem290958 m)). Qed.
Lemma lem290960 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem290961 : term164 = term159.
Proof. exact (MK_COMB (@lem290960) (@lem290959)). Qed.
Lemma lem290962 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem290963 : term173 = term174.
Proof. exact (MK_COMB (@lem290962) (@lem290961)). Qed.
Lemma lem290964 (m : nat) : (term167 m) = (term156 m).
Proof. exact (eq_refl (term167 m)). Qed.
Lemma lem290965 (n : nat -> nat) (m : nat) : (n m) = (n m).
Proof. exact (eq_refl (n m)). Qed.
Lemma lem290966 (n : nat -> nat) (m : nat) : (term175 n m) = (term176 n m).
Proof. exact (MK_COMB (@lem290964 m) (@lem290965 n m)). Qed.
Lemma lem290967 (n : nat -> nat) (m : nat) : (term176 n m) = (term177 n m).
Proof. exact (eq_refl (term176 n m)). Qed.
Lemma lem290968 (n : nat -> nat) (m : nat) : (term175 n m) = (term177 n m).
Proof. exact (TRANS (@lem290966 n m) (@lem290967 n m)). Qed.
Lemma lem290969 (n : nat -> nat) : (term178 n) = (term179 n).
Proof. exact (fun_ext (fun m : nat => @lem290968 n m)). Qed.
Lemma lem290970 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem290971 (n : nat -> nat) : (term180 n) = (term181 n).
Proof. exact (MK_COMB (@lem290970) (@lem290969 n)). Qed.
Lemma lem290972 : term182 = term183.
Proof. exact (fun_ext (fun n : nat -> nat => @lem290971 n)). Qed.
Lemma lem290973 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem290974 : term165 = term184.
Proof. exact (MK_COMB (@lem290973) (@lem290972)). Qed.
Lemma lem290975 : (term164 = term165) = (term159 = term184).
Proof. exact (MK_COMB (@lem290963) (@lem290974)). Qed.
Lemma lem290976 : term159 = term184.
Proof. exact (EQ_MP (@lem290975) (@lem290950)). Qed.
Lemma lem290978 : term18 = term184.
Proof. exact (TRANS (@lem290946) (@lem290976)). Qed.
Lemma lem290979 : term18 = term184.
Proof. exact (TRANS (@lem290870) (@lem290978)). Qed.
Lemma lem290980 (h1 : term18) : term184.
Proof. exact (EQ_MP (@lem290979) (@lem290690 h1)). Qed.
Lemma lem290981 (n : nat -> nat) (h1 : term181 n) : term181 n.
Proof. exact (h1). Qed.
Lemma lem290982 (n' : nat) (P : nat -> Prop) (h1 : term142 n' P) : term142 n' P.
Proof. exact (h1). Qed.
Lemma lem291001 (n : nat -> nat) (m : nat) : (term177 n m) = (term177 n m).
Proof. exact (eq_refl (term177 n m)). Qed.
Lemma lem291002 (n : nat -> nat) : (term179 n) = (term179 n).
Proof. exact (fun_ext (fun m : nat => @lem291001 n m)). Qed.
Lemma lem291003 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem291004 (n : nat -> nat) : (term181 n) = (term181 n).
Proof. exact (MK_COMB (@lem291003) (@lem291002 n)). Qed.
Lemma lem291005 (n : nat -> nat) (h1 : term181 n) : term181 n.
Proof. exact (EQ_MP (@lem291004 n) (@lem290981 n h1)). Qed.
Lemma lem291010 (P : nat -> Prop) (n : nat) : (term30 P n) = (term30 P n).
Proof. exact (eq_refl (term30 P n)). Qed.
Lemma lem291011 (P : nat -> Prop) : (term31 P) = (term31 P).
Proof. exact (fun_ext (fun n : nat => @lem291010 P n)). Qed.
Lemma lem291012 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem291013 (P : nat -> Prop) : (term32 P) = (term32 P).
Proof. exact (MK_COMB (@lem291012) (@lem291011 P)). Qed.
Lemma lem291020 (P : nat -> Prop) : (term33 P) = (term33 P).
Proof. exact (eq_refl (term33 P)). Qed.
Lemma lem291021 (P : nat -> Prop) : (term9 P) = (term9 P).
Proof. exact (MK_COMB (@lem291020 P) (@lem291013 P)). Qed.
Lemma lem291028 (P : nat -> Prop) (n' : nat) : (term117 P n') = (term117 P n').
Proof. exact (eq_refl (term117 P n')). Qed.
Lemma lem291029 (n' : nat) (P : nat -> Prop) : (term119 n' P) = (term119 n' P).
Proof. exact (MK_COMB (@lem291028 P n') (@lem291021 P)). Qed.
Lemma lem291046 (P : nat -> Prop) (n' : nat) : (term82 P n') = (term82 P n').
Proof. exact (eq_refl (term82 P n')). Qed.
Lemma lem291049 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem291050 (P : nat -> Prop) : (term34 P) = (term34 P).
Proof. exact (fun_ext (fun n : nat => @lem291049 P n)). Qed.
Lemma lem291051 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem291052 (P : nat -> Prop) : (term8 P) = (term8 P).
Proof. exact (MK_COMB (@lem291051) (@lem291050 P)). Qed.
Lemma lem291053 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem291054 (P : nat -> Prop) : (term62 P) = (term62 P).
Proof. exact (MK_COMB (@lem291053) (@lem291052 P)). Qed.
Lemma lem291055 (P : nat -> Prop) (n' : nat) : (term99 P n') = (term99 P n').
Proof. exact (MK_COMB (@lem291054 P) (@lem291046 P n')). Qed.
Lemma lem291056 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem291057 (P : nat -> Prop) (n' : nat) : (term140 P n') = (term140 P n').
Proof. exact (MK_COMB (@lem291056) (@lem291055 P n')). Qed.
Lemma lem291058 (n' : nat) (P : nat -> Prop) : (term142 n' P) = (term142 n' P).
Proof. exact (MK_COMB (@lem291057 P n') (@lem291029 n' P)). Qed.
Lemma lem291059 (n' : nat) (P : nat -> Prop) (h1 : term142 n' P) : term142 n' P.
Proof. exact (EQ_MP (@lem291058 n' P) (@lem290982 n' P h1)). Qed.
Lemma lem291060 (P : nat -> Prop) (n' : nat) (h1 : term99 P n') : term99 P n'.
Proof. exact (h1). Qed.
Lemma lem291061 (n' : nat) (P : nat -> Prop) (h1 : term119 n' P) : term119 n' P.
Proof. exact (h1). Qed.
Lemma lem291062 (P : nat -> Prop) (n' : nat) (h1 : term99 P n') : term82 P n'.
Proof. exact (proj2 (@lem291060 P n' h1)). Qed.
Lemma lem291063 (P : nat -> Prop) (n' : nat) (h1 : term99 P n') : term8 P.
Proof. exact (proj1 (@lem291060 P n' h1)). Qed.
Lemma lem291066 (n' : nat) (P : nat -> Prop) (h1 : term119 n' P) : term9 P.
Proof. exact (proj2 (@lem291061 n' P h1)). Qed.
Lemma lem291068 (n' : nat) (P : nat -> Prop) (h1 : term119 n' P) : term32 P.
Proof. exact (proj2 (@lem291066 n' P h1)). Qed.
Lemma lem291084 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem291085 (P : nat -> Prop) : (term34 P) = (term34 P).
Proof. exact (fun_ext (fun n : nat => @lem291084 P n)). Qed.
Lemma lem291086 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem291088 (P : nat -> Prop) : (term8 P) = (term8 P).
Proof. exact (MK_COMB (@lem291086) (@lem291085 P)). Qed.
Lemma lem291089 (P : nat -> Prop) (n' : nat) (h1 : term99 P n') : term8 P.
Proof. exact (EQ_MP (@lem291088 P) (@lem291063 P n' h1)). Qed.
Lemma lem291093 (P : nat -> Prop) (h1 : term75 P) : term75 P.
Proof. exact (h1). Qed.
Lemma lem291108 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem291109 (P : nat -> Prop) : (term34 P) = (term34 P).
Proof. exact (fun_ext (fun n : nat => @lem291108 P n)). Qed.
Lemma lem291110 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem291112 (P : nat -> Prop) : (term8 P) = (term8 P).
Proof. exact (MK_COMB (@lem291110) (@lem291109 P)). Qed.
Lemma lem291113 (P : nat -> Prop) (n' : nat) (h1 : term99 P n') : term8 P.
Proof. exact (EQ_MP (@lem291112 P) (@lem291063 P n' h1)). Qed.
Lemma lem291117 (P : nat -> Prop) (n' : nat) (h1 : term49 P n') : term49 P n'.
Proof. exact (h1). Qed.
Lemma lem291125 (n : nat -> nat) (m : nat) : (term177 n m) = (term177 n m).
Proof. exact (eq_refl (term177 n m)). Qed.
Lemma lem291126 (n : nat -> nat) : (term179 n) = (term179 n).
Proof. exact (fun_ext (fun m : nat => @lem291125 n m)). Qed.
Lemma lem291127 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem291129 (n : nat -> nat) : (term181 n) = (term181 n).
Proof. exact (MK_COMB (@lem291127) (@lem291126 n)). Qed.
Lemma lem291130 (n : nat -> nat) (h1 : term181 n) : term181 n.
Proof. exact (EQ_MP (@lem291129 n) (@lem291005 n h1)). Qed.
Lemma lem291140 (P : nat -> Prop) (n : nat) : (term30 P n) = (term30 P n).
Proof. exact (eq_refl (term30 P n)). Qed.
Lemma lem291141 (P : nat -> Prop) : (term31 P) = (term31 P).
Proof. exact (fun_ext (fun n : nat => @lem291140 P n)). Qed.
Lemma lem291142 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem291144 (P : nat -> Prop) : (term32 P) = (term32 P).
Proof. exact (MK_COMB (@lem291142) (@lem291141 P)). Qed.
Lemma lem291145 (n' : nat) (P : nat -> Prop) (h1 : term119 n' P) : term32 P.
Proof. exact (EQ_MP (@lem291144 P) (@lem291068 n' P h1)). Qed.
Lemma lem291149 (_6508 : nat) (P : nat -> Prop) (n' : nat) (h1 : term99 P n') : term40 P _6508.
Proof. exact (@lem291089 P n' h1 _6508). Qed.
Lemma lem291150 (P : nat -> Prop) (_6508 : nat) : (term40 P _6508) = (P _6508).
Proof. exact (eq_refl (term40 P _6508)). Qed.
Lemma lem291155 (_6510 : nat) (P : nat -> Prop) (n' : nat) (h1 : term99 P n') : term40 P _6510.
Proof. exact (@lem291113 P n' h1 _6510). Qed.
Lemma lem291156 (P : nat -> Prop) (_6510 : nat) : (term40 P _6510) = (P _6510).
Proof. exact (eq_refl (term40 P _6510)). Qed.
Lemma lem291158 (_6511 : nat) (n : nat -> nat) (h1 : term181 n) : term185 n _6511.
Proof. exact (@lem291130 n h1 _6511). Qed.
Lemma lem291159 (n : nat -> nat) (_6511 : nat) : (term185 n _6511) = (term177 n _6511).
Proof. exact (eq_refl (term185 n _6511)). Qed.
Lemma lem291161 (_6512 : nat) (n' : nat) (P : nat -> Prop) (h1 : term119 n' P) : term47 P _6512.
Proof. exact (@lem291145 n' P h1 _6512). Qed.
Lemma lem291162 (P : nat -> Prop) (_6512 : nat) : (term47 P _6512) = (term30 P _6512).
Proof. exact (eq_refl (term47 P _6512)). Qed.
Lemma lem291173 (P : nat -> Prop) (h1 : term75 P) : term75 P.
Proof. exact (h1). Qed.
Lemma lem291183 (P : nat -> Prop) (n' : nat) (h1 : term49 P n') : term49 P n'.
Proof. exact (h1). Qed.
Lemma lem291189 (_6511 : nat) (n : nat -> nat) (h1 : term181 n) : term177 n _6511.
Proof. exact (EQ_MP (@lem291159 n _6511) (@lem291158 _6511 n h1)). Qed.
Lemma lem291191 (n' : nat) (P : nat -> Prop) (h1 : term119 n' P) : term42 P n'.
Proof. exact (proj1 (@lem291061 n' P h1)). Qed.
Lemma lem291235 (_6508 : nat) (P : nat -> Prop) (n' : nat) (h1 : term99 P n') : P _6508.
Proof. exact (EQ_MP (@lem291150 P _6508) (@lem291149 _6508 P n' h1)). Qed.
Lemma lem291236 (P : nat -> Prop) (n' : nat) (h1 : term99 P n') : term57 P.
Proof. exact (@lem291235 (NUMERAL 0) P n' h1). Qed.
Lemma lem291237 (P : nat -> Prop) (n' : nat) (h1 : term99 P n') : term186 P.
Proof. exact (fun h0 : term75 P => @lem291236 P n' h1). Qed.
Lemma lem291239 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem291240 (P : nat -> Prop) : (term186 P) = (term57 P).
Proof. exact (@lem291239 (term57 P)). Qed.
Lemma lem291241 (P : nat -> Prop) (n' : nat) (h1 : term99 P n') : term57 P.
Proof. exact (EQ_MP (@lem291240 P) (@lem291237 P n' h1)). Qed.
Lemma lem291244 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem291246 (P : nat -> Prop) : (term75 P) = (term188 P).
Proof. exact (@lem291244 (term57 P)). Qed.
Lemma lem291249 (P : nat -> Prop) (h1 : term75 P) : term188 P.
Proof. exact (EQ_MP (@lem291246 P) (@lem291173 P h1)). Qed.
Lemma lem291252 (P : nat -> Prop) (n' : nat) (h1 : term75 P) (h2 : term99 P n') : False.
Proof. exact (@lem291249 P h1 (@lem291241 P n' h2)). Qed.
Lemma lem291253 (P : nat -> Prop) (n' : nat) (h1 : term75 P) (h2 : term99 P n') : term189.
Proof. exact (fun h0 : ~ False => @lem291252 P n' h1 h2). Qed.
Lemma lem291255 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem291256 : term189 = False.
Proof. exact (@lem291255 False). Qed.
Lemma lem291257 (P : nat -> Prop) (n' : nat) (h1 : term75 P) (h2 : term99 P n') : False.
Proof. exact (EQ_MP (@lem291256) (@lem291253 P n' h1 h2)). Qed.
Lemma lem291297 (_6510 : nat) (P : nat -> Prop) (n' : nat) (h1 : term99 P n') : P _6510.
Proof. exact (EQ_MP (@lem291156 P _6510) (@lem291155 _6510 P n' h1)). Qed.
Lemma lem291298 (P : nat -> Prop) (n' : nat) (h1 : term99 P n') : term30 P n'.
Proof. exact (@lem291297 (S n') P n' h1). Qed.
Lemma lem291299 (P : nat -> Prop) (n' : nat) (h1 : term99 P n') : term190 P n'.
Proof. exact (fun h0 : term49 P n' => @lem291298 P n' h1). Qed.
Lemma lem291301 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem291302 (P : nat -> Prop) (n' : nat) : (term190 P n') = (term30 P n').
Proof. exact (@lem291301 (term30 P n')). Qed.
Lemma lem291303 (P : nat -> Prop) (n' : nat) (h1 : term99 P n') : term30 P n'.
Proof. exact (EQ_MP (@lem291302 P n') (@lem291299 P n' h1)). Qed.
Lemma lem291306 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem291308 (P : nat -> Prop) (n' : nat) : (term49 P n') = (term191 P n').
Proof. exact (@lem291306 (term30 P n')). Qed.
Lemma lem291311 (P : nat -> Prop) (n' : nat) (h1 : term49 P n') : term191 P n'.
Proof. exact (EQ_MP (@lem291308 P n') (@lem291183 P n' h1)). Qed.
Lemma lem291314 (P : nat -> Prop) (n' : nat) (h1 : term49 P n') (h2 : term99 P n') : False.
Proof. exact (@lem291311 P n' h1 (@lem291303 P n' h2)). Qed.
Lemma lem291315 (P : nat -> Prop) (n' : nat) (h1 : term49 P n') (h2 : term99 P n') : term189.
Proof. exact (fun h0 : ~ False => @lem291314 P n' h1 h2). Qed.
Lemma lem291317 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem291318 : term189 = False.
Proof. exact (@lem291317 False). Qed.
Lemma lem291319 (P : nat -> Prop) (n' : nat) (h1 : term49 P n') (h2 : term99 P n') : False.
Proof. exact (EQ_MP (@lem291318) (@lem291315 P n' h1 h2)). Qed.
Lemma lem291320 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem291321 (_6529 : nat) (_6530 : nat) (h1 : _6529 = _6530) : _6529 = _6530.
Proof. exact (h1). Qed.
Lemma lem291322 (P : nat -> Prop) (_6529 : nat) (_6530 : nat) (h1 : _6529 = _6530) : (P _6529) = (P _6530).
Proof. exact (MK_COMB (@lem291320 P) (@lem291321 _6529 _6530 h1)). Qed.
Lemma lem291324 (b : Prop) (a : Prop) : term192 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem291325 (_6530 : nat) (P : nat -> Prop) (_6529 : nat) : term193 _6530 P _6529.
Proof. exact (@lem291324 (P _6530) (P _6529)). Qed.
Lemma lem291326 (P : nat -> Prop) (_6529 : nat) (_6530 : nat) (h1 : _6529 = _6530) : term194 _6530 P _6529.
Proof. exact (@lem291325 _6530 P _6529 (@lem291322 P _6529 _6530 h1)). Qed.
Lemma lem291327 (_6530 : nat) (P : nat -> Prop) (_6529 : nat) : term195 _6530 P _6529.
Proof. exact (fun h0 : _6529 = _6530 => @lem291326 P _6529 _6530 h0). Qed.
Lemma lem291329 (a : Prop) (b : Prop) : (a -> b) = (term196 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem291330 (_6530 : nat) (P : nat -> Prop) (_6529 : nat) : (term195 _6530 P _6529) = (term197 _6530 P _6529).
Proof. exact (@lem291329 (_6529 = _6530) (term194 _6530 P _6529)). Qed.
Lemma lem291331 (_6530 : nat) (P : nat -> Prop) (_6529 : nat) : term197 _6530 P _6529.
Proof. exact (EQ_MP (@lem291330 _6530 P _6529) (@lem291327 _6530 P _6529)). Qed.
Lemma lem291357 (x : nat) (y : nat) (z : nat) : term198 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem291359 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem291360 (n' : nat) : n' = n'.
Proof. exact (@lem291359 n'). Qed.
Lemma lem291361 (n' : nat) : term199 n'.
Proof. exact (fun h0 : term200 n' => @lem291360 n'). Qed.
Lemma lem291363 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem291364 (n' : nat) : (term199 n') = (n' = n').
Proof. exact (@lem291363 (n' = n')). Qed.
Lemma lem291365 (n' : nat) : n' = n'.
Proof. exact (EQ_MP (@lem291364 n') (@lem291361 n')). Qed.
Lemma lem291368 (P : nat -> Prop) (n' : nat) (h1 : term42 P n') : term42 P n'.
Proof. exact (h1). Qed.
Lemma lem291369 (P : nat -> Prop) (n' : nat) (h1 : term42 P n') : term201 P n'.
Proof. exact (fun h0 : P n' => @lem291368 P n' h1). Qed.
Lemma lem291371 (p : Prop) : (term202 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem291372 (P : nat -> Prop) (n' : nat) : (term201 P n') = (term42 P n').
Proof. exact (@lem291371 (P n')). Qed.
Lemma lem291373 (P : nat -> Prop) (n' : nat) (h1 : term42 P n') : term42 P n'.
Proof. exact (EQ_MP (@lem291372 P n') (@lem291369 P n' h1)). Qed.
Lemma lem291375 (n' : nat) (P : nat -> Prop) (h1 : term119 n' P) : term57 P.
Proof. exact (proj1 (@lem291066 n' P h1)). Qed.
Lemma lem291376 (n' : nat) (P : nat -> Prop) (h1 : term119 n' P) : term186 P.
Proof. exact (fun h0 : term75 P => @lem291375 n' P h1). Qed.
Lemma lem291378 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem291379 (P : nat -> Prop) : (term186 P) = (term57 P).
Proof. exact (@lem291378 (term57 P)). Qed.
Lemma lem291380 (n' : nat) (P : nat -> Prop) (h1 : term119 n' P) : term57 P.
Proof. exact (EQ_MP (@lem291379 P) (@lem291376 n' P h1)). Qed.
Lemma lem291382 (b : Prop) (a : Prop) : (a \/ b) = (term203 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem291383 (P : nat -> Prop) (_6529 : nat) (_6530 : nat) : (term197 _6530 P _6529) = (term204 P _6529 _6530).
Proof. exact (@lem291382 (term194 _6530 P _6529) (term205 _6529 _6530)). Qed.
Lemma lem291385 (a : Prop) (b : Prop) : (term206 a b) = (term207 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem291386 (_6530 : nat) (P : nat -> Prop) (_6529 : nat) : (term208 _6530 P _6529) = (term209 _6530 P _6529).
Proof. exact (@lem291385 (P _6530) (term42 P _6529)). Qed.
Lemma lem291388 (a : Prop) : (term210 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem291389 (P : nat -> Prop) (_6529 : nat) : (term211 P _6529) = (P _6529).
Proof. exact (@lem291388 (P _6529)). Qed.
Lemma lem291390 (P : nat -> Prop) (_6530 : nat) : (term117 P _6530) = (term117 P _6530).
Proof. exact (eq_refl (term117 P _6530)). Qed.
Lemma lem291391 (_6530 : nat) (P : nat -> Prop) (_6529 : nat) : (term209 _6530 P _6529) = (term212 _6530 P _6529).
Proof. exact (MK_COMB (@lem291390 P _6530) (@lem291389 P _6529)). Qed.
Lemma lem291392 (_6530 : nat) (P : nat -> Prop) (_6529 : nat) : (term208 _6530 P _6529) = (term212 _6530 P _6529).
Proof. exact (TRANS (@lem291386 _6530 P _6529) (@lem291391 _6530 P _6529)). Qed.
Lemma lem291393 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem291394 (_6530 : nat) (P : nat -> Prop) (_6529 : nat) : (term213 _6530 P _6529) = (term214 _6530 P _6529).
Proof. exact (MK_COMB (@lem291393) (@lem291392 _6530 P _6529)). Qed.
Lemma lem291395 (_6529 : nat) (_6530 : nat) : (term205 _6529 _6530) = (term205 _6529 _6530).
Proof. exact (eq_refl (term205 _6529 _6530)). Qed.
Lemma lem291396 (P : nat -> Prop) (_6529 : nat) (_6530 : nat) : (term204 P _6529 _6530) = (term215 P _6529 _6530).
Proof. exact (MK_COMB (@lem291394 _6530 P _6529) (@lem291395 _6529 _6530)). Qed.
Lemma lem291397 (P : nat -> Prop) (_6529 : nat) (_6530 : nat) : (term197 _6530 P _6529) = (term215 P _6529 _6530).
Proof. exact (TRANS (@lem291383 P _6529 _6530) (@lem291396 P _6529 _6530)). Qed.
Lemma lem291399 (n' : nat) (P : nat -> Prop) (h1 : term42 P n') (h2 : term119 n' P) : term216 n' P.
Proof. exact (conj (@lem291373 P n' h1) (@lem291380 n' P h2)). Qed.
Lemma lem291401 (P : nat -> Prop) (_6529 : nat) (_6530 : nat) : term215 P _6529 _6530.
Proof. exact (EQ_MP (@lem291397 P _6529 _6530) (@lem291331 _6530 P _6529)). Qed.
Lemma lem291402 (P : nat -> Prop) (n' : nat) : term217 P n'.
Proof. exact (@lem291401 P (NUMERAL 0) n'). Qed.
Lemma lem291405 (n' : nat) (P : nat -> Prop) (h1 : term42 P n') (h2 : term119 n' P) : term218 n'.
Proof. exact (@lem291402 P n' (@lem291399 n' P h1 h2)). Qed.
Lemma lem291406 (n' : nat) (P : nat -> Prop) (h1 : term42 P n') (h2 : term119 n' P) : term219 n'.
Proof. exact (fun h0 : (NUMERAL 0) = n' => @lem291405 n' P h1 h2). Qed.
Lemma lem291408 (p : Prop) : (term202 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem291409 (n' : nat) : (term219 n') = (term218 n').
Proof. exact (@lem291408 ((NUMERAL 0) = n')). Qed.
Lemma lem291410 (n' : nat) (P : nat -> Prop) (h1 : term42 P n') (h2 : term119 n' P) : term218 n'.
Proof. exact (EQ_MP (@lem291409 n') (@lem291406 n' P h1 h2)). Qed.
Lemma lem291412 (b : Prop) (a : Prop) : (a \/ b) = (term203 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem291413 (z : nat) (x : nat) (y : nat) : (term198 x y z) = (term220 z x y).
Proof. exact (@lem291412 (term221 x y z) (term205 x y)). Qed.
Lemma lem291415 (a : Prop) (b : Prop) : (term206 a b) = (term207 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem291416 (x : nat) (y : nat) (z : nat) : (term222 x y z) = (term223 x y z).
Proof. exact (@lem291415 (term205 x z) (y = z)). Qed.
Lemma lem291418 (a : Prop) : (term210 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem291419 (x : nat) (z : nat) : (term224 x z) = (x = z).
Proof. exact (@lem291418 (x = z)). Qed.
Lemma lem291420 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem291421 (x : nat) (z : nat) : (term225 x z) = (term226 x z).
Proof. exact (MK_COMB (@lem291420) (@lem291419 x z)). Qed.
Lemma lem291422 (y : nat) (z : nat) : (term205 y z) = (term205 y z).
Proof. exact (eq_refl (term205 y z)). Qed.
Lemma lem291423 (x : nat) (y : nat) (z : nat) : (term223 x y z) = (term227 x y z).
Proof. exact (MK_COMB (@lem291421 x z) (@lem291422 y z)). Qed.
Lemma lem291424 (x : nat) (y : nat) (z : nat) : (term222 x y z) = (term227 x y z).
Proof. exact (TRANS (@lem291416 x y z) (@lem291423 x y z)). Qed.
Lemma lem291425 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem291426 (x : nat) (y : nat) (z : nat) : (term228 x y z) = (term229 x y z).
Proof. exact (MK_COMB (@lem291425) (@lem291424 x y z)). Qed.
Lemma lem291427 (x : nat) (y : nat) : (term205 x y) = (term205 x y).
Proof. exact (eq_refl (term205 x y)). Qed.
Lemma lem291428 (z : nat) (x : nat) (y : nat) : (term220 z x y) = (term230 z x y).
Proof. exact (MK_COMB (@lem291426 x y z) (@lem291427 x y)). Qed.
Lemma lem291429 (z : nat) (x : nat) (y : nat) : (term198 x y z) = (term230 z x y).
Proof. exact (TRANS (@lem291413 z x y) (@lem291428 z x y)). Qed.
Lemma lem291431 (n' : nat) (P : nat -> Prop) (h1 : term42 P n') (h2 : term119 n' P) : term231 n'.
Proof. exact (conj (@lem291365 n') (@lem291410 n' P h1 h2)). Qed.
Lemma lem291433 (z : nat) (x : nat) (y : nat) : term230 z x y.
Proof. exact (EQ_MP (@lem291429 z x y) (@lem291357 x y z)). Qed.
Lemma lem291434 (n' : nat) : term232 n'.
Proof. exact (@lem291433 n' n' (NUMERAL 0)). Qed.
Lemma lem291437 (n' : nat) (P : nat -> Prop) (h1 : term42 P n') (h2 : term119 n' P) : term233 n'.
Proof. exact (@lem291434 n' (@lem291431 n' P h1 h2)). Qed.
Lemma lem291438 (n' : nat) (P : nat -> Prop) (h1 : term42 P n') (h2 : term119 n' P) : term234 n'.
Proof. exact (fun h0 : n' = (NUMERAL 0) => @lem291437 n' P h1 h2). Qed.
Lemma lem291440 (p : Prop) : (term202 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem291441 (n' : nat) : (term234 n') = (term233 n').
Proof. exact (@lem291440 (n' = (NUMERAL 0))). Qed.
Lemma lem291442 (n' : nat) (P : nat -> Prop) (h1 : term42 P n') (h2 : term119 n' P) : term233 n'.
Proof. exact (EQ_MP (@lem291441 n') (@lem291438 n' P h1 h2)). Qed.
Lemma lem291457 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem291458 (n : nat -> nat) (_6511 : nat) : (term235 n _6511) = (term177 n _6511).
Proof. exact (@lem291457 (_6511 = (NUMERAL 0)) (_6511 = (term236 n _6511))). Qed.
Lemma lem291468 (n : nat -> nat) (_6511 : nat) : (term237 n _6511) = (term237 n _6511).
Proof. exact (eq_refl (term237 n _6511)). Qed.
Lemma lem291469 (n : nat -> nat) (_6511 : nat) : ((term177 n _6511) = (term235 n _6511)) = ((term177 n _6511) = (term177 n _6511)).
Proof. exact (MK_COMB (@lem291468 n _6511) (@lem291458 n _6511)). Qed.
Lemma lem291471 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem291472 (x : Prop) : (x = x) = True.
Proof. exact (@lem291471 Prop x). Qed.
Lemma lem291473 (n : nat -> nat) (_6511 : nat) : ((term177 n _6511) = (term177 n _6511)) = True.
Proof. exact (@lem291472 (term177 n _6511)). Qed.
Lemma lem291474 (n : nat -> nat) (_6511 : nat) : ((term177 n _6511) = (term235 n _6511)) = True.
Proof. exact (TRANS (@lem291469 n _6511) (@lem291473 n _6511)). Qed.
Lemma lem291475 (n : nat -> nat) (_6511 : nat) : True = ((term177 n _6511) = (term235 n _6511)).
Proof. exact (SYM (@lem291474 n _6511)). Qed.
Lemma lem291476 (n : nat -> nat) (_6511 : nat) : (term177 n _6511) = (term235 n _6511).
Proof. exact (EQ_MP (@lem291475 n _6511) (@lem0)). Qed.
Lemma lem291477 (_6511 : nat) (n : nat -> nat) (h1 : term181 n) : term235 n _6511.
Proof. exact (EQ_MP (@lem291476 n _6511) (@lem291189 _6511 n h1)). Qed.
Lemma lem291479 (b : Prop) (a : Prop) : (a \/ b) = (term203 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem291482 (n : nat -> nat) (_6511 : nat) : (term235 n _6511) = (term238 n _6511).
Proof. exact (@lem291479 (_6511 = (NUMERAL 0)) (_6511 = (term236 n _6511))). Qed.
Lemma lem291485 (_6511 : nat) (n : nat -> nat) (h1 : term181 n) : term238 n _6511.
Proof. exact (EQ_MP (@lem291482 n _6511) (@lem291477 _6511 n h1)). Qed.
Lemma lem291486 (n' : nat) (n : nat -> nat) (h1 : term181 n) : term238 n n'.
Proof. exact (@lem291485 n' n h1). Qed.
Lemma lem291489 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term181 n) (h2 : term42 P n') (h3 : term119 n' P) : n' = (term236 n n').
Proof. exact (@lem291486 n' n h1 (@lem291442 n' P h2 h3)). Qed.
Lemma lem291490 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term181 n) (h2 : term42 P n') (h3 : term119 n' P) : term239 n n'.
Proof. exact (fun h0 : term240 n n' => @lem291489 n n' P h1 h2 h3). Qed.
Lemma lem291492 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem291493 (n : nat -> nat) (n' : nat) : (term239 n n') = (n' = (term236 n n')).
Proof. exact (@lem291492 (n' = (term236 n n'))). Qed.
Lemma lem291494 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term181 n) (h2 : term42 P n') (h3 : term119 n' P) : n' = (term236 n n').
Proof. exact (EQ_MP (@lem291493 n n') (@lem291490 n n' P h1 h2 h3)). Qed.
Lemma lem291496 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem291497 (n' : nat) : n' = n'.
Proof. exact (@lem291496 n'). Qed.
Lemma lem291498 (n' : nat) : term199 n'.
Proof. exact (fun h0 : term200 n' => @lem291497 n'). Qed.
Lemma lem291500 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem291501 (n' : nat) : (term199 n') = (n' = n').
Proof. exact (@lem291500 (n' = n')). Qed.
Lemma lem291502 (n' : nat) : n' = n'.
Proof. exact (EQ_MP (@lem291501 n') (@lem291498 n')). Qed.
Lemma lem291520 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem291521 (y : nat) (x : nat) (z : nat) : (term221 x y z) = (term241 y x z).
Proof. exact (@lem291520 (y = z) (term205 x z)). Qed.
Lemma lem291531 (x : nat) (y : nat) : (term242 x y) = (term242 x y).
Proof. exact (eq_refl (term242 x y)). Qed.
Lemma lem291532 (y : nat) (x : nat) (z : nat) : (term198 x y z) = (term243 y x z).
Proof. exact (MK_COMB (@lem291531 x y) (@lem291521 y x z)). Qed.
Lemma lem291536 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem291537 (y : nat) (x : nat) (z : nat) : (term243 y x z) = (term244 y x z).
Proof. exact (@lem291536 (y = z) (term205 x y) (term205 x z)). Qed.
Lemma lem291559 (y : nat) (x : nat) (z : nat) : (term198 x y z) = (term244 y x z).
Proof. exact (TRANS (@lem291532 y x z) (@lem291537 y x z)). Qed.
Lemma lem291560 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem291561 (y : nat) (x : nat) (z : nat) : (term245 x y z) = (term246 y x z).
Proof. exact (MK_COMB (@lem291560) (@lem291559 y x z)). Qed.
Lemma lem291583 (y : nat) (x : nat) (z : nat) : (term244 y x z) = (term244 y x z).
Proof. exact (eq_refl (term244 y x z)). Qed.
Lemma lem291584 (y : nat) (x : nat) (z : nat) : ((term198 x y z) = (term244 y x z)) = ((term244 y x z) = (term244 y x z)).
Proof. exact (MK_COMB (@lem291561 y x z) (@lem291583 y x z)). Qed.
Lemma lem291586 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem291587 (x : Prop) : (x = x) = True.
Proof. exact (@lem291586 Prop x). Qed.
Lemma lem291588 (y : nat) (x : nat) (z : nat) : ((term244 y x z) = (term244 y x z)) = True.
Proof. exact (@lem291587 (term244 y x z)). Qed.
Lemma lem291589 (y : nat) (x : nat) (z : nat) : ((term198 x y z) = (term244 y x z)) = True.
Proof. exact (TRANS (@lem291584 y x z) (@lem291588 y x z)). Qed.
Lemma lem291590 (y : nat) (x : nat) (z : nat) : True = ((term198 x y z) = (term244 y x z)).
Proof. exact (SYM (@lem291589 y x z)). Qed.
Lemma lem291591 (y : nat) (x : nat) (z : nat) : (term198 x y z) = (term244 y x z).
Proof. exact (EQ_MP (@lem291590 y x z) (@lem0)). Qed.
Lemma lem291592 (y : nat) (x : nat) (z : nat) : term244 y x z.
Proof. exact (EQ_MP (@lem291591 y x z) (@lem291357 x y z)). Qed.
Lemma lem291594 (b : Prop) (a : Prop) : (a \/ b) = (term203 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem291595 (x : nat) (y : nat) (z : nat) : (term244 y x z) = (term247 x y z).
Proof. exact (@lem291594 (term248 y x z) (y = z)). Qed.
Lemma lem291597 (a : Prop) (b : Prop) : (term206 a b) = (term207 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem291598 (y : nat) (x : nat) (z : nat) : (term249 y x z) = (term250 y x z).
Proof. exact (@lem291597 (term205 x y) (term205 x z)). Qed.
Lemma lem291600 (a : Prop) : (term210 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem291601 (x : nat) (y : nat) : (term224 x y) = (x = y).
Proof. exact (@lem291600 (x = y)). Qed.
Lemma lem291602 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem291603 (x : nat) (y : nat) : (term225 x y) = (term226 x y).
Proof. exact (MK_COMB (@lem291602) (@lem291601 x y)). Qed.
Lemma lem291605 (a : Prop) : (term210 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem291606 (x : nat) (z : nat) : (term224 x z) = (x = z).
Proof. exact (@lem291605 (x = z)). Qed.
Lemma lem291607 (y : nat) (x : nat) (z : nat) : (term250 y x z) = (term251 y x z).
Proof. exact (MK_COMB (@lem291603 x y) (@lem291606 x z)). Qed.
Lemma lem291608 (y : nat) (x : nat) (z : nat) : (term249 y x z) = (term251 y x z).
Proof. exact (TRANS (@lem291598 y x z) (@lem291607 y x z)). Qed.
Lemma lem291609 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem291610 (y : nat) (x : nat) (z : nat) : (term252 y x z) = (term253 y x z).
Proof. exact (MK_COMB (@lem291609) (@lem291608 y x z)). Qed.
Lemma lem291611 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem291612 (x : nat) (y : nat) (z : nat) : (term247 x y z) = (term254 x y z).
Proof. exact (MK_COMB (@lem291610 y x z) (@lem291611 y z)). Qed.
Lemma lem291613 (x : nat) (y : nat) (z : nat) : (term244 y x z) = (term254 x y z).
Proof. exact (TRANS (@lem291595 x y z) (@lem291612 x y z)). Qed.
Lemma lem291615 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term181 n) (h2 : term42 P n') (h3 : term119 n' P) : term255 n n'.
Proof. exact (conj (@lem291494 n n' P h1 h2 h3) (@lem291502 n')). Qed.
Lemma lem291617 (x : nat) (y : nat) (z : nat) : term254 x y z.
Proof. exact (EQ_MP (@lem291613 x y z) (@lem291592 y x z)). Qed.
Lemma lem291618 (n : nat -> nat) (n' : nat) : term256 n n'.
Proof. exact (@lem291617 n' (term236 n n') n'). Qed.
Lemma lem291621 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term181 n) (h2 : term42 P n') (h3 : term119 n' P) : (term236 n n') = n'.
Proof. exact (@lem291618 n n' (@lem291615 n n' P h1 h2 h3)). Qed.
Lemma lem291622 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term181 n) (h2 : term42 P n') (h3 : term119 n' P) : term257 n n'.
Proof. exact (fun h0 : term258 n n' => @lem291621 n n' P h1 h2 h3). Qed.
Lemma lem291624 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem291625 (n : nat -> nat) (n' : nat) : (term257 n n') = ((term236 n n') = n').
Proof. exact (@lem291624 ((term236 n n') = n')). Qed.
Lemma lem291626 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term181 n) (h2 : term42 P n') (h3 : term119 n' P) : (term236 n n') = n'.
Proof. exact (EQ_MP (@lem291625 n n') (@lem291622 n n' P h1 h2 h3)). Qed.
Lemma lem291628 (_6512 : nat) (n' : nat) (P : nat -> Prop) (h1 : term119 n' P) : term30 P _6512.
Proof. exact (EQ_MP (@lem291162 P _6512) (@lem291161 _6512 n' P h1)). Qed.
Lemma lem291629 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term119 n' P) : term259 P n n'.
Proof. exact (@lem291628 (n n') n' P h1). Qed.
Lemma lem291630 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term119 n' P) : term260 P n n'.
Proof. exact (fun h0 : term261 P n n' => @lem291629 n n' P h1). Qed.
Lemma lem291632 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem291633 (P : nat -> Prop) (n : nat -> nat) (n' : nat) : (term260 P n n') = (term259 P n n').
Proof. exact (@lem291632 (term259 P n n')). Qed.
Lemma lem291634 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term119 n' P) : term259 P n n'.
Proof. exact (EQ_MP (@lem291633 P n n') (@lem291630 n n' P h1)). Qed.
Lemma lem291640 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem291641 (_6530 : nat) (P : nat -> Prop) (_6529 : nat) : (term197 _6530 P _6529) = (term262 _6530 P _6529).
Proof. exact (@lem291640 (P _6530) (term205 _6529 _6530) (term42 P _6529)). Qed.
Lemma lem291655 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem291656 (P : nat -> Prop) (_6529 : nat) (_6530 : nat) : (term263 _6530 P _6529) = (term264 P _6529 _6530).
Proof. exact (@lem291655 (term42 P _6529) (term205 _6529 _6530)). Qed.
Lemma lem291664 (P : nat -> Prop) (_6530 : nat) : (term265 P _6530) = (term265 P _6530).
Proof. exact (eq_refl (term265 P _6530)). Qed.
Lemma lem291665 (P : nat -> Prop) (_6529 : nat) (_6530 : nat) : (term262 _6530 P _6529) = (term266 P _6529 _6530).
Proof. exact (MK_COMB (@lem291664 P _6530) (@lem291656 P _6529 _6530)). Qed.
Lemma lem291676 (P : nat -> Prop) (_6529 : nat) (_6530 : nat) : (term197 _6530 P _6529) = (term266 P _6529 _6530).
Proof. exact (TRANS (@lem291641 _6530 P _6529) (@lem291665 P _6529 _6530)). Qed.
Lemma lem291677 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem291678 (P : nat -> Prop) (_6529 : nat) (_6530 : nat) : (term267 _6530 P _6529) = (term268 P _6529 _6530).
Proof. exact (MK_COMB (@lem291677) (@lem291676 P _6529 _6530)). Qed.
Lemma lem291692 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem291693 (P : nat -> Prop) (_6529 : nat) (_6530 : nat) : (term263 _6530 P _6529) = (term264 P _6529 _6530).
Proof. exact (@lem291692 (term42 P _6529) (term205 _6529 _6530)). Qed.
Lemma lem291701 (P : nat -> Prop) (_6530 : nat) : (term265 P _6530) = (term265 P _6530).
Proof. exact (eq_refl (term265 P _6530)). Qed.
Lemma lem291702 (P : nat -> Prop) (_6529 : nat) (_6530 : nat) : (term262 _6530 P _6529) = (term266 P _6529 _6530).
Proof. exact (MK_COMB (@lem291701 P _6530) (@lem291693 P _6529 _6530)). Qed.
Lemma lem291713 (P : nat -> Prop) (_6529 : nat) (_6530 : nat) : ((term197 _6530 P _6529) = (term262 _6530 P _6529)) = ((term266 P _6529 _6530) = (term266 P _6529 _6530)).
Proof. exact (MK_COMB (@lem291678 P _6529 _6530) (@lem291702 P _6529 _6530)). Qed.
Lemma lem291715 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem291716 (x : Prop) : (x = x) = True.
Proof. exact (@lem291715 Prop x). Qed.
Lemma lem291717 (P : nat -> Prop) (_6529 : nat) (_6530 : nat) : ((term266 P _6529 _6530) = (term266 P _6529 _6530)) = True.
Proof. exact (@lem291716 (term266 P _6529 _6530)). Qed.
Lemma lem291718 (_6530 : nat) (P : nat -> Prop) (_6529 : nat) : ((term197 _6530 P _6529) = (term262 _6530 P _6529)) = True.
Proof. exact (TRANS (@lem291713 P _6529 _6530) (@lem291717 P _6529 _6530)). Qed.
Lemma lem291719 (_6530 : nat) (P : nat -> Prop) (_6529 : nat) : True = ((term197 _6530 P _6529) = (term262 _6530 P _6529)).
Proof. exact (SYM (@lem291718 _6530 P _6529)). Qed.
Lemma lem291720 (_6530 : nat) (P : nat -> Prop) (_6529 : nat) : (term197 _6530 P _6529) = (term262 _6530 P _6529).
Proof. exact (EQ_MP (@lem291719 _6530 P _6529) (@lem0)). Qed.
Lemma lem291721 (_6530 : nat) (P : nat -> Prop) (_6529 : nat) : term262 _6530 P _6529.
Proof. exact (EQ_MP (@lem291720 _6530 P _6529) (@lem291331 _6530 P _6529)). Qed.
Lemma lem291723 (b : Prop) (a : Prop) : (a \/ b) = (term203 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem291724 (_6529 : nat) (P : nat -> Prop) (_6530 : nat) : (term262 _6530 P _6529) = (term269 _6529 P _6530).
Proof. exact (@lem291723 (term263 _6530 P _6529) (P _6530)). Qed.
Lemma lem291726 (a : Prop) (b : Prop) : (term206 a b) = (term207 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem291727 (_6530 : nat) (P : nat -> Prop) (_6529 : nat) : (term270 _6530 P _6529) = (term271 _6530 P _6529).
Proof. exact (@lem291726 (term205 _6529 _6530) (term42 P _6529)). Qed.
Lemma lem291729 (a : Prop) : (term210 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem291730 (_6529 : nat) (_6530 : nat) : (term224 _6529 _6530) = (_6529 = _6530).
Proof. exact (@lem291729 (_6529 = _6530)). Qed.
Lemma lem291731 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem291732 (_6529 : nat) (_6530 : nat) : (term225 _6529 _6530) = (term226 _6529 _6530).
Proof. exact (MK_COMB (@lem291731) (@lem291730 _6529 _6530)). Qed.
Lemma lem291734 (a : Prop) : (term210 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem291735 (P : nat -> Prop) (_6529 : nat) : (term211 P _6529) = (P _6529).
Proof. exact (@lem291734 (P _6529)). Qed.
Lemma lem291736 (_6530 : nat) (P : nat -> Prop) (_6529 : nat) : (term271 _6530 P _6529) = (term272 _6530 P _6529).
Proof. exact (MK_COMB (@lem291732 _6529 _6530) (@lem291735 P _6529)). Qed.
Lemma lem291737 (_6530 : nat) (P : nat -> Prop) (_6529 : nat) : (term270 _6530 P _6529) = (term272 _6530 P _6529).
Proof. exact (TRANS (@lem291727 _6530 P _6529) (@lem291736 _6530 P _6529)). Qed.
Lemma lem291738 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem291739 (_6530 : nat) (P : nat -> Prop) (_6529 : nat) : (term273 _6530 P _6529) = (term274 _6530 P _6529).
Proof. exact (MK_COMB (@lem291738) (@lem291737 _6530 P _6529)). Qed.
Lemma lem291740 (P : nat -> Prop) (_6530 : nat) : (P _6530) = (P _6530).
Proof. exact (eq_refl (P _6530)). Qed.
Lemma lem291741 (_6529 : nat) (P : nat -> Prop) (_6530 : nat) : (term269 _6529 P _6530) = (term275 _6529 P _6530).
Proof. exact (MK_COMB (@lem291739 _6530 P _6529) (@lem291740 P _6530)). Qed.
Lemma lem291742 (_6529 : nat) (P : nat -> Prop) (_6530 : nat) : (term262 _6530 P _6529) = (term275 _6529 P _6530).
Proof. exact (TRANS (@lem291724 _6529 P _6530) (@lem291741 _6529 P _6530)). Qed.
Lemma lem291744 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term181 n) (h2 : term42 P n') (h3 : term119 n' P) : term276 P n n'.
Proof. exact (conj (@lem291626 n n' P h1 h2 h3) (@lem291634 n n' P h3)). Qed.
Lemma lem291746 (_6529 : nat) (P : nat -> Prop) (_6530 : nat) : term275 _6529 P _6530.
Proof. exact (EQ_MP (@lem291742 _6529 P _6530) (@lem291721 _6530 P _6529)). Qed.
Lemma lem291747 (n : nat -> nat) (P : nat -> Prop) (n' : nat) : term277 n P n'.
Proof. exact (@lem291746 (term236 n n') P n'). Qed.
Lemma lem291750 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term181 n) (h2 : term42 P n') (h3 : term119 n' P) : P n'.
Proof. exact (@lem291747 n P n' (@lem291744 n n' P h1 h2 h3)). Qed.
Lemma lem291751 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term181 n) (h2 : term119 n' P) : term278 P n'.
Proof. exact (fun h0 : term42 P n' => @lem291750 n n' P h1 h0 h2). Qed.
Lemma lem291753 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem291754 (P : nat -> Prop) (n' : nat) : (term278 P n') = (P n').
Proof. exact (@lem291753 (P n')). Qed.
Lemma lem291755 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term181 n) (h2 : term119 n' P) : P n'.
Proof. exact (EQ_MP (@lem291754 P n') (@lem291751 n n' P h1 h2)). Qed.
Lemma lem291758 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem291760 (P : nat -> Prop) (n' : nat) : (term42 P n') = (term279 P n').
Proof. exact (@lem291758 (P n')). Qed.
Lemma lem291763 (n' : nat) (P : nat -> Prop) (h1 : term119 n' P) : term279 P n'.
Proof. exact (EQ_MP (@lem291760 P n') (@lem291191 n' P h1)). Qed.
Lemma lem291766 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term181 n) (h2 : term119 n' P) : False.
Proof. exact (@lem291763 n' P h2 (@lem291755 n n' P h1 h2)). Qed.
Lemma lem291767 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term181 n) (h2 : term119 n' P) : term189.
Proof. exact (fun h0 : ~ False => @lem291766 n n' P h1 h2). Qed.
Lemma lem291769 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem291770 : term189 = False.
Proof. exact (@lem291769 False). Qed.
Lemma lem291771 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term181 n) (h2 : term119 n' P) : False.
Proof. exact (EQ_MP (@lem291770) (@lem291767 n n' P h1 h2)). Qed.
Lemma lem291772 (P : nat -> Prop) (n' : nat) (h1 : term49 P n') (h2 : term99 P n') : (term49 P n') = False.
Proof. exact (prop_ext (fun h3 : term49 P n' => @lem291319 P n' h1 h2) (fun h3 : False => @lem291183 P n' h1)). Qed.
Lemma lem291773 (P : nat -> Prop) (n' : nat) (h1 : term49 P n') (h2 : term99 P n') : False.
Proof. exact (EQ_MP (@lem291772 P n' h1 h2) (@lem291183 P n' h1)). Qed.
Lemma lem291774 (P : nat -> Prop) (n' : nat) (h1 : term75 P) (h2 : term99 P n') : (term75 P) = False.
Proof. exact (prop_ext (fun h3 : term75 P => @lem291257 P n' h1 h2) (fun h3 : False => @lem291173 P h1)). Qed.
Lemma lem291775 (P : nat -> Prop) (n' : nat) (h1 : term75 P) (h2 : term99 P n') : False.
Proof. exact (EQ_MP (@lem291774 P n' h1 h2) (@lem291173 P h1)). Qed.
Lemma lem291776 (P : nat -> Prop) (n' : nat) (h1 : term49 P n') (h2 : term99 P n') : (term49 P n') = False.
Proof. exact (prop_ext (fun h3 : term49 P n' => @lem291773 P n' h1 h2) (fun h3 : False => @lem291117 P n' h1)). Qed.
Lemma lem291777 (P : nat -> Prop) (n' : nat) (h1 : term49 P n') (h2 : term99 P n') : False.
Proof. exact (EQ_MP (@lem291776 P n' h1 h2) (@lem291117 P n' h1)). Qed.
Lemma lem291778 (P : nat -> Prop) (n' : nat) (h1 : term75 P) (h2 : term99 P n') : (term75 P) = False.
Proof. exact (prop_ext (fun h3 : term75 P => @lem291775 P n' h1 h2) (fun h3 : False => @lem291093 P h1)). Qed.
Lemma lem291779 (P : nat -> Prop) (n' : nat) (h1 : term75 P) (h2 : term99 P n') : False.
Proof. exact (EQ_MP (@lem291778 P n' h1 h2) (@lem291093 P h1)). Qed.
Lemma lem291780 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term181 n) (h2 : term119 n' P) : (term181 n) = False.
Proof. exact (prop_ext (fun h3 : term181 n => @lem291771 n n' P h1 h2) (fun h3 : False => @lem291130 n h1)). Qed.
Lemma lem291781 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term181 n) (h2 : term119 n' P) : False.
Proof. exact (EQ_MP (@lem291780 n n' P h1 h2) (@lem291130 n h1)). Qed.
Lemma lem291782 (P : nat -> Prop) (n' : nat) (h1 : term49 P n') (h2 : term99 P n') : (term49 P n') = False.
Proof. exact (prop_ext (fun h3 : term49 P n' => @lem291777 P n' h1 h2) (fun h3 : False => @lem291117 P n' h1)). Qed.
Lemma lem291783 (P : nat -> Prop) (n' : nat) (h1 : term49 P n') (h2 : term99 P n') : False.
Proof. exact (EQ_MP (@lem291782 P n' h1 h2) (@lem291117 P n' h1)). Qed.
Lemma lem291784 (P : nat -> Prop) (n' : nat) (h1 : term75 P) (h2 : term99 P n') : (term75 P) = False.
Proof. exact (prop_ext (fun h3 : term75 P => @lem291779 P n' h1 h2) (fun h3 : False => @lem291093 P h1)). Qed.
Lemma lem291785 (P : nat -> Prop) (n' : nat) (h1 : term75 P) (h2 : term99 P n') : False.
Proof. exact (EQ_MP (@lem291784 P n' h1 h2) (@lem291093 P h1)). Qed.
Lemma lem291786 (P : nat -> Prop) (n' : nat) (h1 : term99 P n') : False.
Proof. exact (or_elim (@lem291062 P n' h1) (fun h0 : term75 P => @lem291785 P n' h0 h1) (fun h0 : term49 P n' => @lem291783 P n' h0 h1)). Qed.
Lemma lem291787 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term181 n) (h2 : term142 n' P) : False.
Proof. exact (or_elim (@lem291059 n' P h2) (fun h0 : term99 P n' => @lem291786 P n' h0) (fun h0 : term119 n' P => @lem291781 n n' P h1 h0)). Qed.
Lemma lem291788 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term181 n) (h2 : term142 n' P) : (term142 n' P) = False.
Proof. exact (prop_ext (fun h3 : term142 n' P => @lem291787 n n' P h1 h2) (fun h3 : False => @lem291059 n' P h2)). Qed.
Lemma lem291789 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term181 n) (h2 : term142 n' P) : False.
Proof. exact (EQ_MP (@lem291788 n n' P h1 h2) (@lem291059 n' P h2)). Qed.
Lemma lem291790 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term181 n) (h2 : term142 n' P) : (term181 n) = False.
Proof. exact (prop_ext (fun h3 : term181 n => @lem291789 n n' P h1 h2) (fun h3 : False => @lem291005 n h1)). Qed.
Lemma lem291791 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term181 n) (h2 : term142 n' P) : False.
Proof. exact (EQ_MP (@lem291790 n n' P h1 h2) (@lem291005 n h1)). Qed.
Lemma lem291792 (n : nat -> nat) (P : nat -> Prop) (h1 : term181 n) (h2 : term11 P) : False.
Proof. exact (ex_elim (@lem290859 P h2) (fun n' : nat => fun h0 : term144 P n' => @lem291791 n n' P h1 h0)). Qed.
Lemma lem291793 (P : nat -> Prop) (h1 : term18) (h2 : term11 P) : False.
Proof. exact (ex_elim (@lem290980 h1) (fun n : nat -> nat => fun h0 : term183 n => @lem291792 n P h0 h2)). Qed.
Lemma lem291794 (P : nat -> Prop) (h1 : term11 P) : term16.
Proof. exact (fun h0 : term18 => @lem291793 P h0 h1). Qed.
Lemma lem291795 : term16 = term17.
Proof. exact (@lem69 term18). Qed.
Lemma lem291796 (P : nat -> Prop) (h1 : term11 P) : term17.
Proof. exact (EQ_MP (@lem291795) (@lem291794 P h1)). Qed.
Lemma lem291797 (P : nat -> Prop) : term20 P.
Proof. exact (fun h0 : term11 P => @lem291796 P h0). Qed.
Lemma lem291802 : term24.
Proof. exact (fun P : nat -> Prop => @lem291797 P). Qed.
Lemma lem291803 : term23.
Proof. exact (EQ_MP (@lem290688) (@lem291802)). Qed.
Lemma lem291804 (P : nat -> Prop) : term280 P.
Proof. exact (@lem291803 P). Qed.
Lemma lem291805 (P : nat -> Prop) : (term280 P) = (term12 P).
Proof. exact (eq_refl (term280 P)). Qed.
Lemma lem291806 (P : nat -> Prop) : term12 P.
Proof. exact (EQ_MP (@lem291805 P) (@lem291804 P)). Qed.
Lemma lem291808 (P : nat -> Prop) : term12 P.
Proof. exact (@lem290524 P (@lem291806 P)). Qed.
Lemma lem291809 (P : nat -> Prop) (h1 : term11 P) : term16.
Proof. exact (@lem291808 P (@lem290509 P h1)). Qed.
Lemma lem291810 (P : nat -> Prop) (h1 : term11 P) : False.
Proof. exact (@lem291809 P h1 (@lem76132)). Qed.
Lemma lem291811 (P : nat -> Prop) (h1 : term11 P) : (term11 P) = False.
Proof. exact (prop_ext (fun h2 : term11 P => @lem291810 P h1) (fun h2 : False => @lem290509 P h1)). Qed.
Lemma lem291812 (P : nat -> Prop) (h1 : term11 P) : False.
Proof. exact (EQ_MP (@lem291811 P h1) (@lem290509 P h1)). Qed.
Lemma lem291813 (P : nat -> Prop) : term10 P.
Proof. exact (fun h0 : term11 P => @lem291812 P h0). Qed.
Lemma lem291815 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term281 A P Q) : term281 A P Q.
Proof. exact (h1). Qed.
Lemma lem291816 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term282 A P Q) : term282 A P Q.
Proof. exact (h1). Qed.
Lemma lem291817 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term282 A P Q) (h2 : term281 A P Q) : term283 A P Q.
Proof. exact (@lem291815 A P Q h2 (@lem291816 A P Q h1)). Qed.
Lemma lem291818 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term282 A P Q) : term284 A P Q.
Proof. exact (fun h0 : term281 A P Q => @lem291817 A P Q h1 h0). Qed.
Lemma lem291819 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term281 A P Q) : term281 A P Q.
Proof. exact (h1). Qed.
Lemma lem291820 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term282 A P Q) (h2 : term281 A P Q) : term283 A P Q.
Proof. exact (@lem291818 A P Q h1 (@lem291819 A P Q h2)). Qed.
Lemma lem291821 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term281 A P Q) : term281 A P Q.
Proof. exact (fun h0 : term282 A P Q => @lem291820 A P Q h0 h1). Qed.
Lemma lem291822 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term285 A P Q.
Proof. exact (fun h0 : term281 A P Q => @lem291821 A P Q h0). Qed.
Lemma lem291831 {A : Type'} (f : nat -> A) (a : A) (h1 : (term286 A f) = a) : (term286 A f) = a.
Proof. exact (h1). Qed.
Lemma lem291832 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term287 A P R f) : term287 A P R f.
Proof. exact (h1). Qed.
Lemma lem291833 {A : Type'} (n : nat) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term287 A P R f) : term288 A P R f n.
Proof. exact (@lem291832 A P R f h1 n). Qed.
Lemma lem291834 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term288 A P R f n) = ((term289 A f n) = (term290 A P R f n)).
Proof. exact (eq_refl (term288 A P R f n)). Qed.
Lemma lem291835 {A : Type'} (n : nat) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term287 A P R f) : (term289 A f n) = (term290 A P R f n).
Proof. exact (EQ_MP (@lem291834 A P R f n) (@lem291833 A n P R f h1)). Qed.
Lemma lem291836 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term287 A P R f) : term287 A P R f.
Proof. exact (fun n : nat => @lem291835 A n P R f h1). Qed.
Lemma lem291837 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term291 A a P R f) : term291 A a P R f.
Proof. exact (h1). Qed.
Lemma lem291838 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term291 A a P R f) : term287 A P R f.
Proof. exact (proj2 (@lem291837 A a P R f h1)). Qed.
Lemma lem291839 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term291 A a P R f) : (term286 A f) = a.
Proof. exact (proj1 (@lem291837 A a P R f h1)). Qed.
Lemma lem291840 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term291 A a P R f) : ((term286 A f) = a) = ((term286 A f) = a).
Proof. exact (prop_ext (fun h2 : (term286 A f) = a => @lem291831 A f a h2) (fun h2 : (term286 A f) = a => @lem291839 A a P R f h1)). Qed.
Lemma lem291841 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term291 A a P R f) : (term286 A f) = a.
Proof. exact (EQ_MP (@lem291840 A a P R f h1) (@lem291839 A a P R f h1)). Qed.
Lemma lem291842 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term291 A a P R f) : (term287 A P R f) = (term287 A P R f).
Proof. exact (prop_ext (fun h2 : term287 A P R f => @lem291836 A P R f h2) (fun h2 : term287 A P R f => @lem291838 A a P R f h1)). Qed.
Lemma lem291843 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term291 A a P R f) : term287 A P R f.
Proof. exact (EQ_MP (@lem291842 A a P R f h1) (@lem291838 A a P R f h1)). Qed.
Lemma lem291844 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term291 A a P R f) : term291 A a P R f.
Proof. exact (conj (@lem291841 A a P R f h1) (@lem291843 A a P R f h1)). Qed.
Lemma lem291845 {A : Type'} (e : A) : term292 A e.
Proof. exact (@lem75635 A e). Qed.
Lemma lem291846 {A : Type'} (e : A) : (term292 A e) = (term293 A e).
Proof. exact (eq_refl (term292 A e)). Qed.
Lemma lem291847 {A : Type'} (e : A) : term293 A e.
Proof. exact (EQ_MP (@lem291846 A e) (@lem291845 A e)). Qed.
Lemma lem291848 {A : Type'} (e : A) (f : type1423 A) : term294 A e f.
Proof. exact (@lem291847 A e f). Qed.
Lemma lem291849 {A : Type'} (e : A) (f : type1423 A) : (term294 A e f) = (term295 A e f).
Proof. exact (eq_refl (term294 A e f)). Qed.
Lemma lem291850 {A : Type'} (e : A) (f : type1423 A) : term295 A e f.
Proof. exact (EQ_MP (@lem291849 A e f) (@lem291848 A e f)). Qed.
Lemma lem291851 {A : Type'} (e : A) (f : type1423 A) : term295 A e f.
Proof. exact (@lem291850 A e f). Qed.
Lemma lem291852 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : term296 A a P R.
Proof. exact (@lem291851 A a (term297 A P R)). Qed.
Lemma lem291853 {A : Type'} (P : type1597 A) (R : type1594 A) (fn : nat -> A) (n : nat) : (term298 A P R fn n) = (term299 A P R fn n).
Proof. exact (eq_refl (term298 A P R fn n)). Qed.
Lemma lem291854 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem291855 {A : Type'} (P : type1597 A) (R : type1594 A) (fn : nat -> A) (n : nat) : (term300 A P R fn n) = (term301 A P R fn n).
Proof. exact (MK_COMB (@lem291853 A P R fn n) (@lem291854 n)). Qed.
Lemma lem291856 {A : Type'} (P : type1597 A) (R : type1594 A) (fn : nat -> A) (n : nat) : (term301 A P R fn n) = (term290 A P R fn n).
Proof. exact (eq_refl (term301 A P R fn n)). Qed.
Lemma lem291857 {A : Type'} (P : type1597 A) (R : type1594 A) (fn : nat -> A) (n : nat) : (term300 A P R fn n) = (term290 A P R fn n).
Proof. exact (TRANS (@lem291855 A P R fn n) (@lem291856 A P R fn n)). Qed.
Lemma lem291858 {A : Type'} (fn : nat -> A) (n : nat) : (term302 A fn n) = (term302 A fn n).
Proof. exact (eq_refl (term302 A fn n)). Qed.
Lemma lem291859 {A : Type'} (P : type1597 A) (R : type1594 A) (fn : nat -> A) (n : nat) : ((term289 A fn n) = (term300 A P R fn n)) = ((term289 A fn n) = (term290 A P R fn n)).
Proof. exact (MK_COMB (@lem291858 A fn n) (@lem291857 A P R fn n)). Qed.
Lemma lem291860 {A : Type'} (P : type1597 A) (R : type1594 A) (fn : nat -> A) : (term303 A P R fn) = (term304 A P R fn).
Proof. exact (fun_ext (fun n : nat => @lem291859 A P R fn n)). Qed.
Lemma lem291861 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem291862 {A : Type'} (P : type1597 A) (R : type1594 A) (fn : nat -> A) : (term305 A P R fn) = (term287 A P R fn).
Proof. exact (MK_COMB (@lem291861) (@lem291860 A P R fn)). Qed.
Lemma lem291863 {A : Type'} (fn : nat -> A) (a : A) : (term306 A fn a) = (term306 A fn a).
Proof. exact (eq_refl (term306 A fn a)). Qed.
Lemma lem291864 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (fn : nat -> A) : (term307 A a P R fn) = (term291 A a P R fn).
Proof. exact (MK_COMB (@lem291863 A fn a) (@lem291862 A P R fn)). Qed.
Lemma lem291865 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term308 A a P R) = (term309 A a P R).
Proof. exact (fun_ext (fun fn : nat -> A => @lem291864 A a P R fn)). Qed.
Lemma lem291866 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem291867 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term296 A a P R) = (term310 A a P R).
Proof. exact (MK_COMB (@lem291866 A) (@lem291865 A a P R)). Qed.
Lemma lem291868 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : term310 A a P R.
Proof. exact (EQ_MP (@lem291867 A a P R) (@lem291852 A a P R)). Qed.
Lemma lem291869 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term291 A a P R f) : term291 A a P R f.
Proof. exact (h1). Qed.
Lemma lem291870 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term291 A a P R f) : term287 A P R f.
Proof. exact (proj2 (@lem291869 A a P R f h1)). Qed.
Lemma lem291871 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term291 A a P R f) : (term286 A f) = a.
Proof. exact (proj1 (@lem291869 A a P R f h1)). Qed.
Lemma lem291872 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term291 A a P R f) : term291 A a P R f.
Proof. exact (conj (@lem291871 A a P R f h1) (@lem291870 A a P R f h1)). Qed.
Lemma lem291873 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term291 A a P R f) : term310 A a P R.
Proof. exact (ex_intro (term309 A a P R) f (@lem291872 A a P R f h1)). Qed.
Lemma lem291874 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (h1 : term310 A a P R) : term310 A a P R.
Proof. exact (h1). Qed.
Lemma lem291875 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (h1 : term310 A a P R) : term310 A a P R.
Proof. exact (ex_elim (@lem291874 A a P R h1) (fun f : nat -> A => fun h0 : term309 A a P R f => @lem291873 A a P R f h0)). Qed.
Lemma lem291876 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term310 A a P R) = (term310 A a P R).
Proof. exact (prop_ext (fun h1 : term310 A a P R => @lem291875 A a P R h1) (fun h1 : term310 A a P R => @lem291868 A a P R)). Qed.
Lemma lem291877 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : term310 A a P R.
Proof. exact (EQ_MP (@lem291876 A a P R) (@lem291868 A a P R)). Qed.
Lemma lem291878 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term291 A a P R f) : term310 A a P R.
Proof. exact (ex_intro (term309 A a P R) f (@lem291844 A a P R f h1)). Qed.
Lemma lem291879 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (h1 : term310 A a P R) : term310 A a P R.
Proof. exact (h1). Qed.
Lemma lem291880 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (h1 : term310 A a P R) : term310 A a P R.
Proof. exact (ex_elim (@lem291879 A a P R h1) (fun f : nat -> A => fun h0 : term309 A a P R f => @lem291878 A a P R f h0)). Qed.
Lemma lem291881 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term310 A a P R) = (term310 A a P R).
Proof. exact (prop_ext (fun h1 : term310 A a P R => @lem291880 A a P R h1) (fun h1 : term310 A a P R => @lem291877 A a P R)). Qed.
Lemma lem291882 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : term310 A a P R.
Proof. exact (EQ_MP (@lem291881 A a P R) (@lem291877 A a P R)). Qed.
Lemma lem291885 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term291 A a P R f) : term291 A a P R f.
Proof. exact (h1). Qed.
Lemma lem291886 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term291 A a P R f) : term310 A a P R.
Proof. exact (ex_intro (term309 A a P R) f (@lem291885 A a P R f h1)). Qed.
Lemma lem291887 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (h1 : term310 A a P R) : term310 A a P R.
Proof. exact (h1). Qed.
Lemma lem291888 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (h1 : term310 A a P R) : term310 A a P R.
Proof. exact (ex_elim (@lem291887 A a P R h1) (fun f : nat -> A => fun h0 : term309 A a P R f => @lem291886 A a P R f h0)). Qed.
Lemma lem291889 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term310 A a P R) = (term310 A a P R).
Proof. exact (prop_ext (fun h1 : term310 A a P R => @lem291888 A a P R h1) (fun h1 : term310 A a P R => @lem291882 A a P R)). Qed.
Lemma lem291890 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : term310 A a P R.
Proof. exact (EQ_MP (@lem291889 A a P R) (@lem291882 A a P R)). Qed.
Lemma lem291891 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (h1 : term311 A a P R) : term311 A a P R.
Proof. exact (h1). Qed.
Lemma lem291892 {A : Type'} (P : type1597 A) (R : type1594 A) (h1 : term312 A P R) : term312 A P R.
Proof. exact (h1). Qed.
Lemma lem291893 {A : Type'} (P : type1597 A) (a : A) (h1 : term313 A P a) : term313 A P a.
Proof. exact (h1). Qed.
Lemma lem291895 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term281 A P Q.
Proof. exact (@lem291822 A P Q (@lem7401 A P Q)). Qed.
Lemma lem291896 {A : Type'} (P : type976 A) (Q : type976 A) : term314 A P Q.
Proof. exact (@lem291895 (nat -> A) P Q). Qed.
Lemma lem291897 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : term315 A a P R.
Proof. exact (@lem291896 A (term309 A a P R) (term316 A a P R)). Qed.
Lemma lem291898 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term317 A a P R f) = (term291 A a P R f).
Proof. exact (eq_refl (term317 A a P R f)). Qed.
Lemma lem291899 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem291900 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term318 A a P R f) = (term319 A a P R f).
Proof. exact (MK_COMB (@lem291899) (@lem291898 A a P R f)). Qed.
Lemma lem291901 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term320 A a P R f) = (term321 A a P R f).
Proof. exact (eq_refl (term320 A a P R f)). Qed.
Lemma lem291902 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term322 A a P R f) = (term323 A a P R f).
Proof. exact (MK_COMB (@lem291900 A a P R f) (@lem291901 A a P R f)). Qed.
Lemma lem291903 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term324 A a P R) = (term325 A a P R).
Proof. exact (fun_ext (fun f : nat -> A => @lem291902 A a P R f)). Qed.
Lemma lem291904 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem291905 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term326 A a P R) = (term327 A a P R).
Proof. exact (MK_COMB (@lem291904 A) (@lem291903 A a P R)). Qed.
Lemma lem291906 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem291907 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term328 A a P R) = (term329 A a P R).
Proof. exact (MK_COMB (@lem291906) (@lem291905 A a P R)). Qed.
Lemma lem291908 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term317 A a P R f) = (term291 A a P R f).
Proof. exact (eq_refl (term317 A a P R f)). Qed.
Lemma lem291909 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term330 A a P R) = (term309 A a P R).
Proof. exact (fun_ext (fun f : nat -> A => @lem291908 A a P R f)). Qed.
Lemma lem291910 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem291911 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term331 A a P R) = (term310 A a P R).
Proof. exact (MK_COMB (@lem291910 A) (@lem291909 A a P R)). Qed.
Lemma lem291912 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem291913 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term332 A a P R) = (term333 A a P R).
Proof. exact (MK_COMB (@lem291912) (@lem291911 A a P R)). Qed.
Lemma lem291914 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term320 A a P R f) = (term321 A a P R f).
Proof. exact (eq_refl (term320 A a P R f)). Qed.
Lemma lem291915 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term334 A a P R) = (term316 A a P R).
Proof. exact (fun_ext (fun f : nat -> A => @lem291914 A a P R f)). Qed.
Lemma lem291916 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem291917 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term335 A a P R) = (term336 A a P R).
Proof. exact (MK_COMB (@lem291916 A) (@lem291915 A a P R)). Qed.
Lemma lem291918 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term337 A a P R) = (term338 A a P R).
Proof. exact (MK_COMB (@lem291913 A a P R) (@lem291917 A a P R)). Qed.
Lemma lem291919 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term315 A a P R) = (term339 A a P R).
Proof. exact (MK_COMB (@lem291907 A a P R) (@lem291918 A a P R)). Qed.
Lemma lem291920 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : term339 A a P R.
Proof. exact (EQ_MP (@lem291919 A a P R) (@lem291897 A a P R)). Qed.
Lemma lem291921 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term291 A a P R f) : term291 A a P R f.
Proof. exact (h1). Qed.
Lemma lem291922 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term287 A P R f) : term287 A P R f.
Proof. exact (h1). Qed.
Lemma lem291923 {A : Type'} (f : nat -> A) (a : A) (h1 : (term286 A f) = a) : (term286 A f) = a.
Proof. exact (h1). Qed.
Lemma lem291934 {A : Type'} (n : nat) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term287 A P R f) : term288 A P R f n.
Proof. exact (@lem291922 A P R f h1 n). Qed.
Lemma lem291935 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term288 A P R f n) = ((term289 A f n) = (term290 A P R f n)).
Proof. exact (eq_refl (term288 A P R f n)). Qed.
Lemma lem291942 {A : Type'} (f : nat -> A) (a : A) (h1 : (term286 A f) = a) : (term286 A f) = a.
Proof. exact (h1). Qed.
Lemma lem291943 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem291944 {A : Type'} (f : nat -> A) (a : A) (h1 : (term286 A f) = a) : (term340 A f) = (@eq A a).
Proof. exact (MK_COMB (@lem291943 A) (@lem291942 A f a h1)). Qed.
Lemma lem291945 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem291946 {A : Type'} (f : nat -> A) (a : A) (h1 : (term286 A f) = a) : ((term286 A f) = a) = (a = a).
Proof. exact (MK_COMB (@lem291944 A f a h1) (@lem291945 A a)). Qed.
Lemma lem291948 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem291949 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem291948 A x). Qed.
Lemma lem291950 {A : Type'} (a : A) : (a = a) = True.
Proof. exact (@lem291949 A a). Qed.
Lemma lem291951 {A : Type'} (f : nat -> A) (a : A) (h1 : (term286 A f) = a) : ((term286 A f) = a) = True.
Proof. exact (TRANS (@lem291946 A f a h1) (@lem291950 A a)). Qed.
Lemma lem291952 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem291953 {A : Type'} (f : nat -> A) (a : A) (h1 : (term286 A f) = a) : (term306 A f a) = (and True).
Proof. exact (MK_COMB (@lem291952) (@lem291951 A f a h1)). Qed.
Lemma lem291965 {A : Type'} (n : nat) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term287 A P R f) : (term289 A f n) = (term290 A P R f n).
Proof. exact (EQ_MP (@lem291935 A P R f n) (@lem291934 A n P R f h1)). Qed.
Lemma lem291968 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term341 A R f n) = (term341 A R f n).
Proof. exact (eq_refl (term341 A R f n)). Qed.
Lemma lem291969 {A : Type'} (n : nat) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term287 A P R f) : (term342 A R f n) = (term343 A P R f n).
Proof. exact (MK_COMB (@lem291968 A R f n) (@lem291965 A n P R f h1)). Qed.
Lemma lem291970 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term287 A P R f) : (term344 A R f) = (term345 A P R f).
Proof. exact (fun_ext (fun n : nat => @lem291969 A n P R f h1)). Qed.
Lemma lem291971 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem291972 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term287 A P R f) : (term346 A R f) = (term347 A P R f).
Proof. exact (MK_COMB (@lem291971) (@lem291970 A P R f h1)). Qed.
Lemma lem291977 {A : Type'} (P : type1597 A) (f : nat -> A) : (term348 A P f) = (term348 A P f).
Proof. exact (eq_refl (term348 A P f)). Qed.
Lemma lem291978 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term287 A P R f) : (term349 A P R f) = (term350 A P R f).
Proof. exact (MK_COMB (@lem291977 A P f) (@lem291972 A P R f h1)). Qed.
Lemma lem291981 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (a : A) (h1 : term287 A P R f) (h2 : (term286 A f) = a) : (term321 A a P R f) = (term351 A P R f).
Proof. exact (MK_COMB (@lem291953 A f a h2) (@lem291978 A P R f h1)). Qed.
Lemma lem291983 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem291984 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term351 A P R f) = (term350 A P R f).
Proof. exact (@lem291983 (term350 A P R f)). Qed.
Lemma lem291997 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (a : A) (h1 : term287 A P R f) (h2 : (term286 A f) = a) : (term321 A a P R f) = (term350 A P R f).
Proof. exact (TRANS (@lem291981 A P R f a h1 h2) (@lem291984 A P R f)). Qed.
Lemma lem291998 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (a : A) (h1 : term287 A P R f) (h2 : (term286 A f) = a) : (term350 A P R f) = (term321 A a P R f).
Proof. exact (SYM (@lem291997 A P R f a h1 h2)). Qed.
Lemma lem292000 (P : nat -> Prop) : (term8 P) = (term9 P).
Proof. exact (EQ_MP (@lem290508 P) (@lem291813 P)). Qed.
Lemma lem292001 {A : Type'} (P : type1597 A) (f : nat -> A) : (term352 A P f) = (term353 A P f).
Proof. exact (@lem292000 (term354 A P f)). Qed.
Lemma lem292002 {A : Type'} (P : type1597 A) (f : nat -> A) (n : nat) : (term355 A P f n) = (term356 A P f n).
Proof. exact (eq_refl (term355 A P f n)). Qed.
Lemma lem292003 {A : Type'} (P : type1597 A) (f : nat -> A) : (term357 A P f) = (term354 A P f).
Proof. exact (fun_ext (fun n : nat => @lem292002 A P f n)). Qed.
Lemma lem292004 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem292005 {A : Type'} (P : type1597 A) (f : nat -> A) : (term352 A P f) = (term358 A P f).
Proof. exact (MK_COMB (@lem292004) (@lem292003 A P f)). Qed.
Lemma lem292006 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem292007 {A : Type'} (P : type1597 A) (f : nat -> A) : (term359 A P f) = (term360 A P f).
Proof. exact (MK_COMB (@lem292006) (@lem292005 A P f)). Qed.
Lemma lem292008 {A : Type'} (P : type1597 A) (f : nat -> A) : (term361 A P f) = (term362 A P f).
Proof. exact (eq_refl (term361 A P f)). Qed.
Lemma lem292009 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem292010 {A : Type'} (P : type1597 A) (f : nat -> A) : (term363 A P f) = (term364 A P f).
Proof. exact (MK_COMB (@lem292009) (@lem292008 A P f)). Qed.
Lemma lem292011 {A : Type'} (P : type1597 A) (f : nat -> A) (n : nat) : (term365 A P f n) = (term366 A P f n).
Proof. exact (eq_refl (term365 A P f n)). Qed.
Lemma lem292012 {A : Type'} (P : type1597 A) (f : nat -> A) : (term367 A P f) = (term368 A P f).
Proof. exact (fun_ext (fun n : nat => @lem292011 A P f n)). Qed.
Lemma lem292013 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem292014 {A : Type'} (P : type1597 A) (f : nat -> A) : (term369 A P f) = (term370 A P f).
Proof. exact (MK_COMB (@lem292013) (@lem292012 A P f)). Qed.
Lemma lem292015 {A : Type'} (P : type1597 A) (f : nat -> A) : (term353 A P f) = (term371 A P f).
Proof. exact (MK_COMB (@lem292010 A P f) (@lem292014 A P f)). Qed.
Lemma lem292016 {A : Type'} (P : type1597 A) (f : nat -> A) : ((term352 A P f) = (term353 A P f)) = ((term358 A P f) = (term371 A P f)).
Proof. exact (MK_COMB (@lem292007 A P f) (@lem292015 A P f)). Qed.
Lemma lem292017 {A : Type'} (P : type1597 A) (f : nat -> A) : (term358 A P f) = (term371 A P f).
Proof. exact (EQ_MP (@lem292016 A P f) (@lem292001 A P f)). Qed.
Lemma lem292018 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem292019 {A : Type'} (P : type1597 A) (f : nat -> A) : (term348 A P f) = (term372 A P f).
Proof. exact (MK_COMB (@lem292018) (@lem292017 A P f)). Qed.
Lemma lem292020 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term347 A P R f) = (term347 A P R f).
Proof. exact (eq_refl (term347 A P R f)). Qed.
Lemma lem292021 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term350 A P R f) = (term373 A P R f).
Proof. exact (MK_COMB (@lem292019 A P f) (@lem292020 A P R f)). Qed.
Lemma lem292022 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term373 A P R f) = (term350 A P R f).
Proof. exact (SYM (@lem292021 A P R f)). Qed.
Lemma lem292023 {A : Type'} (P : A -> Prop) : term374 A P.
Proof. exact (@lem5146 A P). Qed.
Lemma lem292024 {A : Type'} (P : A -> Prop) : (term374 A P) = (term375 A P).
Proof. exact (eq_refl (term374 A P)). Qed.
Lemma lem292025 {A : Type'} (P : A -> Prop) : term375 A P.
Proof. exact (EQ_MP (@lem292024 A P) (@lem292023 A P)). Qed.
Lemma lem292026 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term376 A P Q.
Proof. exact (@lem292025 A P Q). Qed.
Lemma lem292027 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term376 A P Q) = ((term377 A P Q) = (term378 A P Q)).
Proof. exact (eq_refl (term376 A P Q)). Qed.
Lemma lem292029 {A : Type'} (P : type1597 A) (a : A) : (term313 A P a) = ((term313 A P a) = True).
Proof. exact (@lem7 (term313 A P a)). Qed.
Lemma lem292039 {A : Type'} (n : nat) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term287 A P R f) : term288 A P R f n.
Proof. exact (@lem291922 A P R f h1 n). Qed.
Lemma lem292040 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term288 A P R f n) = ((term289 A f n) = (term290 A P R f n)).
Proof. exact (eq_refl (term288 A P R f n)). Qed.
Lemma lem292047 {A : Type'} (f : nat -> A) (a : A) (h1 : (term286 A f) = a) : (term286 A f) = a.
Proof. exact (h1). Qed.
Lemma lem292048 {A : Type'} (P : type1597 A) : (term379 A P) = (term379 A P).
Proof. exact (eq_refl (term379 A P)). Qed.
Lemma lem292049 {A : Type'} (P : type1597 A) (f : nat -> A) (a : A) (h1 : (term286 A f) = a) : (term362 A P f) = (term313 A P a).
Proof. exact (MK_COMB (@lem292048 A P) (@lem292047 A f a h1)). Qed.
Lemma lem292051 {A : Type'} (P : type1597 A) (a : A) (h1 : term313 A P a) : (term313 A P a) = True.
Proof. exact (EQ_MP (@lem292029 A P a) (@lem291893 A P a h1)). Qed.
Lemma lem292052 {A : Type'} (f : nat -> A) (P : type1597 A) (a : A) (h1 : (term286 A f) = a) (h2 : term313 A P a) : (term362 A P f) = True.
Proof. exact (TRANS (@lem292049 A P f a h1) (@lem292051 A P a h2)). Qed.
Lemma lem292053 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem292054 {A : Type'} (f : nat -> A) (P : type1597 A) (a : A) (h1 : (term286 A f) = a) (h2 : term313 A P a) : (term364 A P f) = (and True).
Proof. exact (MK_COMB (@lem292053) (@lem292052 A f P a h1 h2)). Qed.
Lemma lem292060 {A : Type'} (n : nat) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term287 A P R f) : (term289 A f n) = (term290 A P R f n).
Proof. exact (EQ_MP (@lem292040 A P R f n) (@lem292039 A n P R f h1)). Qed.
Lemma lem292063 {A : Type'} (P : type1597 A) (n : nat) : (term380 A P n) = (term380 A P n).
Proof. exact (eq_refl (term380 A P n)). Qed.
Lemma lem292064 {A : Type'} (n : nat) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term287 A P R f) : (term366 A P f n) = (term381 A P R f n).
Proof. exact (MK_COMB (@lem292063 A P n) (@lem292060 A n P R f h1)). Qed.
Lemma lem292065 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term287 A P R f) : (term368 A P f) = (term382 A P R f).
Proof. exact (fun_ext (fun n : nat => @lem292064 A n P R f h1)). Qed.
Lemma lem292066 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem292067 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term287 A P R f) : (term370 A P f) = (term383 A P R f).
Proof. exact (MK_COMB (@lem292066) (@lem292065 A P R f h1)). Qed.
Lemma lem292072 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term287 A P R f) (h2 : (term286 A f) = a) (h3 : term313 A P a) : (term371 A P f) = (term384 A P R f).
Proof. exact (MK_COMB (@lem292054 A f P a h2 h3) (@lem292067 A P R f h1)). Qed.
Lemma lem292074 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem292075 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term384 A P R f) = (term383 A P R f).
Proof. exact (@lem292074 (term383 A P R f)). Qed.
Lemma lem292082 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term287 A P R f) (h2 : (term286 A f) = a) (h3 : term313 A P a) : (term371 A P f) = (term383 A P R f).
Proof. exact (TRANS (@lem292072 A R f P a h1 h2 h3) (@lem292075 A P R f)). Qed.
Lemma lem292083 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem292084 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term287 A P R f) (h2 : (term286 A f) = a) (h3 : term313 A P a) : (term372 A P f) = (term385 A P R f).
Proof. exact (MK_COMB (@lem292083) (@lem292082 A R f P a h1 h2 h3)). Qed.
Lemma lem292091 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term347 A P R f) = (term347 A P R f).
Proof. exact (eq_refl (term347 A P R f)). Qed.
Lemma lem292092 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term287 A P R f) (h2 : (term286 A f) = a) (h3 : term313 A P a) : (term373 A P R f) = (term386 A P R f).
Proof. exact (MK_COMB (@lem292084 A R f P a h1 h2 h3) (@lem292091 A P R f)). Qed.
Lemma lem292094 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term377 A P Q) = (term378 A P Q).
Proof. exact (EQ_MP (@lem292027 A P Q) (@lem292026 A P Q)). Qed.
Lemma lem292095 (P : nat -> Prop) (Q : nat -> Prop) : (term387 P Q) = (term388 P Q).
Proof. exact (@lem292094 nat P Q). Qed.
Lemma lem292096 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term389 A P R f) = (term390 A P R f).
Proof. exact (@lem292095 (term382 A P R f) (term345 A P R f)). Qed.
Lemma lem292097 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term391 A P R f n) = (term381 A P R f n).
Proof. exact (eq_refl (term391 A P R f n)). Qed.
Lemma lem292098 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term392 A P R f) = (term382 A P R f).
Proof. exact (fun_ext (fun n : nat => @lem292097 A P R f n)). Qed.
Lemma lem292099 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem292100 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term393 A P R f) = (term383 A P R f).
Proof. exact (MK_COMB (@lem292099) (@lem292098 A P R f)). Qed.
Lemma lem292101 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem292102 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term394 A P R f) = (term385 A P R f).
Proof. exact (MK_COMB (@lem292101) (@lem292100 A P R f)). Qed.
Lemma lem292103 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term395 A P R f n) = (term343 A P R f n).
Proof. exact (eq_refl (term395 A P R f n)). Qed.
Lemma lem292104 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term396 A P R f) = (term345 A P R f).
Proof. exact (fun_ext (fun n : nat => @lem292103 A P R f n)). Qed.
Lemma lem292105 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem292106 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term397 A P R f) = (term347 A P R f).
Proof. exact (MK_COMB (@lem292105) (@lem292104 A P R f)). Qed.
Lemma lem292107 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term389 A P R f) = (term386 A P R f).
Proof. exact (MK_COMB (@lem292102 A P R f) (@lem292106 A P R f)). Qed.
Lemma lem292108 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem292109 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term398 A P R f) = (term399 A P R f).
Proof. exact (MK_COMB (@lem292108) (@lem292107 A P R f)). Qed.
Lemma lem292110 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term391 A P R f n) = (term381 A P R f n).
Proof. exact (eq_refl (term391 A P R f n)). Qed.
Lemma lem292111 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem292112 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term400 A P R f n) = (term401 A P R f n).
Proof. exact (MK_COMB (@lem292111) (@lem292110 A P R f n)). Qed.
Lemma lem292113 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term395 A P R f n) = (term343 A P R f n).
Proof. exact (eq_refl (term395 A P R f n)). Qed.
Lemma lem292114 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term402 A P R f n) = (term403 A P R f n).
Proof. exact (MK_COMB (@lem292112 A P R f n) (@lem292113 A P R f n)). Qed.
Lemma lem292115 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term404 A P R f) = (term405 A P R f).
Proof. exact (fun_ext (fun n : nat => @lem292114 A P R f n)). Qed.
Lemma lem292116 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem292117 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term390 A P R f) = (term406 A P R f).
Proof. exact (MK_COMB (@lem292116) (@lem292115 A P R f)). Qed.
Lemma lem292118 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : ((term389 A P R f) = (term390 A P R f)) = ((term386 A P R f) = (term406 A P R f)).
Proof. exact (MK_COMB (@lem292109 A P R f) (@lem292117 A P R f)). Qed.
Lemma lem292119 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term386 A P R f) = (term406 A P R f).
Proof. exact (EQ_MP (@lem292118 A P R f) (@lem292096 A P R f)). Qed.
Lemma lem292130 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term287 A P R f) (h2 : (term286 A f) = a) (h3 : term313 A P a) : (term373 A P R f) = (term406 A P R f).
Proof. exact (TRANS (@lem292092 A R f P a h1 h2 h3) (@lem292119 A P R f)). Qed.
Lemma lem292131 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term287 A P R f) (h2 : (term286 A f) = a) (h3 : term313 A P a) : (term406 A P R f) = (term373 A P R f).
Proof. exact (SYM (@lem292130 A R f P a h1 h2 h3)). Qed.
Lemma lem292133 (P : nat -> Prop) : term407 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem292134 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : term408 A P R f.
Proof. exact (@lem292133 (term405 A P R f)). Qed.
Lemma lem292135 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term409 A P R f) = (term410 A P R f).
Proof. exact (eq_refl (term409 A P R f)). Qed.
Lemma lem292136 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem292137 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term411 A P R f) = (term412 A P R f).
Proof. exact (MK_COMB (@lem292136) (@lem292135 A P R f)). Qed.
Lemma lem292138 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term413 A P R f n) = (term403 A P R f n).
Proof. exact (eq_refl (term413 A P R f n)). Qed.
Lemma lem292139 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem292140 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term414 A P R f n) = (term415 A P R f n).
Proof. exact (MK_COMB (@lem292139) (@lem292138 A P R f n)). Qed.
Lemma lem292141 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term416 A P R f n) = (term417 A P R f n).
Proof. exact (eq_refl (term416 A P R f n)). Qed.
Lemma lem292142 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term418 A P R f n) = (term419 A P R f n).
Proof. exact (MK_COMB (@lem292140 A P R f n) (@lem292141 A P R f n)). Qed.
Lemma lem292143 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term420 A P R f) = (term421 A P R f).
Proof. exact (fun_ext (fun n : nat => @lem292142 A P R f n)). Qed.
Lemma lem292144 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem292145 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term422 A P R f) = (term423 A P R f).
Proof. exact (MK_COMB (@lem292144) (@lem292143 A P R f)). Qed.
Lemma lem292146 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term424 A P R f) = (term425 A P R f).
Proof. exact (MK_COMB (@lem292137 A P R f) (@lem292145 A P R f)). Qed.
Lemma lem292147 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem292148 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term426 A P R f) = (term427 A P R f).
Proof. exact (MK_COMB (@lem292147) (@lem292146 A P R f)). Qed.
Lemma lem292149 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term413 A P R f n) = (term403 A P R f n).
Proof. exact (eq_refl (term413 A P R f n)). Qed.
Lemma lem292150 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term428 A P R f) = (term405 A P R f).
Proof. exact (fun_ext (fun n : nat => @lem292149 A P R f n)). Qed.
Lemma lem292151 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem292152 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term429 A P R f) = (term406 A P R f).
Proof. exact (MK_COMB (@lem292151) (@lem292150 A P R f)). Qed.
Lemma lem292153 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term408 A P R f) = (term430 A P R f).
Proof. exact (MK_COMB (@lem292148 A P R f) (@lem292152 A P R f)). Qed.
Lemma lem292154 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : term430 A P R f.
Proof. exact (EQ_MP (@lem292153 A P R f) (@lem292134 A P R f)). Qed.
Lemma lem292155 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term403 A P R f n) : term403 A P R f n.
Proof. exact (h1). Qed.
Lemma lem292157 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem292158 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term410 A P R f) = (term431 A P R f).
Proof. exact (@lem292157 (term410 A P R f)). Qed.
Lemma lem292159 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term431 A P R f) = (term410 A P R f).
Proof. exact (SYM (@lem292158 A P R f)). Qed.
Lemma lem292160 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term432 A P R f) : term432 A P R f.
Proof. exact (h1). Qed.
Lemma lem292169 {A : Type'} (P : A -> Prop) : (term433 A P) = (ex P).
Proof. exact (@lem19728 A P). Qed.
Lemma lem292170 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term434 A P R f n) = (term435 A P R f n).
Proof. exact (@lem292169 A (term436 A P R f n)). Qed.
Lemma lem292171 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term434 A P R f n) = (term403 A P R f n).
Proof. exact (eq_refl (term434 A P R f n)). Qed.
Lemma lem292172 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem292173 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term437 A P R f n) = (term438 A P R f n).
Proof. exact (MK_COMB (@lem292172) (@lem292171 A P R f n)). Qed.
Lemma lem292174 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term435 A P R f n) = (term435 A P R f n).
Proof. exact (eq_refl (term435 A P R f n)). Qed.
Lemma lem292175 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : ((term434 A P R f n) = (term435 A P R f n)) = ((term403 A P R f n) = (term435 A P R f n)).
Proof. exact (MK_COMB (@lem292173 A P R f n) (@lem292174 A P R f n)). Qed.
Lemma lem292186 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term403 A P R f n) = (term435 A P R f n).
Proof. exact (EQ_MP (@lem292175 A P R f n) (@lem292170 A P R f n)). Qed.
Lemma lem292187 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term403 A P R f n) = (term435 A P R f n).
Proof. exact (@lem292186 A P R f n). Qed.
Lemma lem292188 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term410 A P R f) = (term439 A P R f).
Proof. exact (@lem292187 A P R f (NUMERAL 0)). Qed.
Lemma lem292193 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem292194 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term432 A P R f) = (term440 A P R f).
Proof. exact (MK_COMB (@lem292193) (@lem292188 A P R f)). Qed.
Lemma lem292195 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem292196 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term441 A P R f) = (term442 A P R f).
Proof. exact (MK_COMB (@lem292195) (@lem292194 A P R f)). Qed.
Lemma lem292197 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem292198 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term431 A P R f) = (term443 A P R f).
Proof. exact (MK_COMB (@lem292196 A P R f) (@lem292197)). Qed.
Lemma lem292199 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term444 A P R f) = (term444 A P R f).
Proof. exact (eq_refl (term444 A P R f)). Qed.
Lemma lem292200 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term445 A P R f) = (term446 A P R f).
Proof. exact (MK_COMB (@lem292199 A P R f) (@lem292198 A P R f)). Qed.
Lemma lem292201 {A : Type'} (f : nat -> A) (a : A) : (term447 A f a) = (term447 A f a).
Proof. exact (eq_refl (term447 A f a)). Qed.
Lemma lem292202 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term448 A a P R f) = (term449 A a P R f).
Proof. exact (MK_COMB (@lem292201 A f a) (@lem292200 A P R f)). Qed.
Lemma lem292203 {A : Type'} (P : type1597 A) (R : type1594 A) : (term450 A P R) = (term450 A P R).
Proof. exact (eq_refl (term450 A P R)). Qed.
Lemma lem292204 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term451 A a P R f) = (term452 A a P R f).
Proof. exact (MK_COMB (@lem292203 A P R) (@lem292202 A a P R f)). Qed.
Lemma lem292205 {A : Type'} (P : type1597 A) (a : A) : (term453 A P a) = (term453 A P a).
Proof. exact (eq_refl (term453 A P a)). Qed.
Lemma lem292206 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term454 A a P R f) = (term455 A a P R f).
Proof. exact (MK_COMB (@lem292205 A P a) (@lem292204 A a P R f)). Qed.
Lemma lem292207 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term455 A a P R f) = (term454 A a P R f).
Proof. exact (SYM (@lem292206 A a P R f)). Qed.
Lemma lem292208 {A : Type'} (P : A -> Prop) : term456 A P.
Proof. exact (@lem19732 A P). Qed.
Lemma lem292209 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : term457 A P R f n.
Proof. exact (@lem292208 A (term436 A P R f n)). Qed.
Lemma lem292210 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term434 A P R f n) = (term403 A P R f n).
Proof. exact (eq_refl (term434 A P R f n)). Qed.
Lemma lem292211 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (x : A) : (term458 A P R f n x) = (term459 A P R f n x).
Proof. exact (eq_refl (term458 A P R f n x)). Qed.
Lemma lem292212 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem292213 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (x : A) : (term460 A P R f n x) = (term461 A P R f n x).
Proof. exact (MK_COMB (@lem292212) (@lem292211 A P R f n x)). Qed.
Lemma lem292214 {A : Type'} (x : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term462 A x P R f n) = (term463 A x P R f n).
Proof. exact (MK_COMB (@lem292213 A P R f n x) (@lem292210 A P R f n)). Qed.
Lemma lem292215 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term464 A P R f n) = (term465 A P R f n).
Proof. exact (fun_ext (fun x : A => @lem292214 A x P R f n)). Qed.
Lemma lem292216 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem292217 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term457 A P R f n) = (term466 A P R f n).
Proof. exact (MK_COMB (@lem292216 A) (@lem292215 A P R f n)). Qed.
Lemma lem292218 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : term466 A P R f n.
Proof. exact (EQ_MP (@lem292217 A P R f n) (@lem292209 A P R f n)). Qed.
Lemma lem292219 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : term467 A P R f.
Proof. exact (fun n : nat => @lem292218 A P R f n). Qed.
Lemma lem292220 {A : Type'} (P : type1597 A) (R : type1594 A) : term468 A P R.
Proof. exact (fun f : nat -> A => @lem292219 A P R f). Qed.
Lemma lem292221 {A : Type'} (P : type1597 A) : term469 A P.
Proof. exact (fun R : type1594 A => @lem292220 A P R). Qed.
Lemma lem292222 {A : Type'} : term470 A.
Proof. exact (fun P : type1597 A => @lem292221 A P). Qed.
Lemma lem292223 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term471 A a P R f) : term471 A a P R f.
Proof. exact (h1). Qed.
Lemma lem292224 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term471 A a P R f) : term455 A a P R f.
Proof. exact (@lem292223 A a P R f h1 (@lem292222 A)). Qed.
Lemma lem292225 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : term472 A a P R f.
Proof. exact (fun h0 : term471 A a P R f => @lem292224 A a P R f h0). Qed.
Lemma lem292226 {A : Type'} (_6540 : type943 A) (h1 : _6540 = (term473 A)) : _6540 = (term473 A).
Proof. exact (h1). Qed.
Lemma lem292227 {A : Type'} (P : type1597 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem292228 {A : Type'} (P : type1597 A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (_6540 P) = (term474 A P).
Proof. exact (MK_COMB (@lem292226 A _6540 h1) (@lem292227 A P)). Qed.
Lemma lem292229 {A : Type'} (P : type1597 A) : (term474 A P) = (term475 A P).
Proof. exact (eq_refl (term474 A P)). Qed.
Lemma lem292230 {A : Type'} (_6540 : type943 A) (P : type1597 A) : (term476 A _6540 P) = (term476 A _6540 P).
Proof. exact (eq_refl (term476 A _6540 P)). Qed.
Lemma lem292231 {A : Type'} (_6540 : type943 A) (P : type1597 A) : ((_6540 P) = (term474 A P)) = ((_6540 P) = (term475 A P)).
Proof. exact (MK_COMB (@lem292230 A _6540 P) (@lem292229 A P)). Qed.
Lemma lem292232 {A : Type'} (P : type1597 A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (_6540 P) = (term475 A P).
Proof. exact (EQ_MP (@lem292231 A _6540 P) (@lem292228 A P _6540 h1)). Qed.
Lemma lem292233 {A : Type'} (R : type1594 A) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem292234 {A : Type'} (P : type1597 A) (R : type1594 A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (_6540 P R) = (term477 A P R).
Proof. exact (MK_COMB (@lem292232 A P _6540 h1) (@lem292233 A R)). Qed.
Lemma lem292235 {A : Type'} (P : type1597 A) (R : type1594 A) : (term477 A P R) = (term478 A P R).
Proof. exact (eq_refl (term477 A P R)). Qed.
Lemma lem292236 {A : Type'} (_6540 : type943 A) (P : type1597 A) (R : type1594 A) : (term479 A _6540 P R) = (term479 A _6540 P R).
Proof. exact (eq_refl (term479 A _6540 P R)). Qed.
Lemma lem292237 {A : Type'} (_6540 : type943 A) (P : type1597 A) (R : type1594 A) : ((_6540 P R) = (term477 A P R)) = ((_6540 P R) = (term478 A P R)).
Proof. exact (MK_COMB (@lem292236 A _6540 P R) (@lem292235 A P R)). Qed.
Lemma lem292238 {A : Type'} (P : type1597 A) (R : type1594 A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (_6540 P R) = (term478 A P R).
Proof. exact (EQ_MP (@lem292237 A _6540 P R) (@lem292234 A P R _6540 h1)). Qed.
Lemma lem292239 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem292240 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (_6540 P R f) = (term480 A P R f).
Proof. exact (MK_COMB (@lem292238 A P R _6540 h1) (@lem292239 A f)). Qed.
Lemma lem292241 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term480 A P R f) = (term481 A P R f).
Proof. exact (eq_refl (term480 A P R f)). Qed.
Lemma lem292242 {A : Type'} (_6540 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term482 A _6540 P R f) = (term482 A _6540 P R f).
Proof. exact (eq_refl (term482 A _6540 P R f)). Qed.
Lemma lem292243 {A : Type'} (_6540 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : ((_6540 P R f) = (term480 A P R f)) = ((_6540 P R f) = (term481 A P R f)).
Proof. exact (MK_COMB (@lem292242 A _6540 P R f) (@lem292241 A P R f)). Qed.
Lemma lem292244 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (_6540 P R f) = (term481 A P R f).
Proof. exact (EQ_MP (@lem292243 A _6540 P R f) (@lem292240 A P R f _6540 h1)). Qed.
Lemma lem292245 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem292246 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (_6540 P R f n) = (term483 A P R f n).
Proof. exact (MK_COMB (@lem292244 A P R f _6540 h1) (@lem292245 n)). Qed.
Lemma lem292247 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term483 A P R f n) = (term290 A P R f n).
Proof. exact (eq_refl (term483 A P R f n)). Qed.
Lemma lem292248 {A : Type'} (_6540 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term484 A _6540 P R f n) = (term484 A _6540 P R f n).
Proof. exact (eq_refl (term484 A _6540 P R f n)). Qed.
Lemma lem292249 {A : Type'} (_6540 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : ((_6540 P R f n) = (term483 A P R f n)) = ((_6540 P R f n) = (term290 A P R f n)).
Proof. exact (MK_COMB (@lem292248 A _6540 P R f n) (@lem292247 A P R f n)). Qed.
Lemma lem292250 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (_6540 P R f n) = (term290 A P R f n).
Proof. exact (EQ_MP (@lem292249 A _6540 P R f n) (@lem292246 A P R f n _6540 h1)). Qed.
Lemma lem292251 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (term290 A P R f n) = (_6540 P R f n).
Proof. exact (SYM (@lem292250 A P R f n _6540 h1)). Qed.
Lemma lem292252 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : term485 A _6540 P R f.
Proof. exact (fun n : nat => @lem292251 A P R f n _6540 h1). Qed.
Lemma lem292253 {A : Type'} (P : type1597 A) (R : type1594 A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : term486 A _6540 P R.
Proof. exact (fun f : nat -> A => @lem292252 A P R f _6540 h1). Qed.
Lemma lem292254 {A : Type'} (P : type1597 A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : term487 A _6540 P.
Proof. exact (fun R : type1594 A => @lem292253 A P R _6540 h1). Qed.
Lemma lem292255 {A : Type'} (_6540 : type943 A) (h1 : _6540 = (term473 A)) : term488 A _6540.
Proof. exact (fun P : type1597 A => @lem292254 A P _6540 h1). Qed.
Lemma lem292256 {A : Type'} (P : type1597 A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : term489 A _6540 P.
Proof. exact (@lem292255 A _6540 h1 P). Qed.
Lemma lem292257 {A : Type'} (_6540 : type943 A) (P : type1597 A) : (term489 A _6540 P) = (term487 A _6540 P).
Proof. exact (eq_refl (term489 A _6540 P)). Qed.
Lemma lem292258 {A : Type'} (P : type1597 A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : term487 A _6540 P.
Proof. exact (EQ_MP (@lem292257 A _6540 P) (@lem292256 A P _6540 h1)). Qed.
Lemma lem292259 {A : Type'} (P : type1597 A) (R : type1594 A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : term490 A _6540 P R.
Proof. exact (@lem292258 A P _6540 h1 R). Qed.
Lemma lem292260 {A : Type'} (_6540 : type943 A) (P : type1597 A) (R : type1594 A) : (term490 A _6540 P R) = (term486 A _6540 P R).
Proof. exact (eq_refl (term490 A _6540 P R)). Qed.
Lemma lem292261 {A : Type'} (P : type1597 A) (R : type1594 A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : term486 A _6540 P R.
Proof. exact (EQ_MP (@lem292260 A _6540 P R) (@lem292259 A P R _6540 h1)). Qed.
Lemma lem292262 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : term491 A _6540 P R f.
Proof. exact (@lem292261 A P R _6540 h1 f). Qed.
Lemma lem292263 {A : Type'} (_6540 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term491 A _6540 P R f) = (term485 A _6540 P R f).
Proof. exact (eq_refl (term491 A _6540 P R f)). Qed.
Lemma lem292264 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : term485 A _6540 P R f.
Proof. exact (EQ_MP (@lem292263 A _6540 P R f) (@lem292262 A P R f _6540 h1)). Qed.
Lemma lem292265 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : term492 A _6540 P R f n.
Proof. exact (@lem292264 A P R f _6540 h1 n). Qed.
Lemma lem292266 {A : Type'} (_6540 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term492 A _6540 P R f n) = ((term290 A P R f n) = (_6540 P R f n)).
Proof. exact (eq_refl (term492 A _6540 P R f n)). Qed.
Lemma lem292269 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (term290 A P R f n) = (_6540 P R f n).
Proof. exact (EQ_MP (@lem292266 A _6540 P R f n) (@lem292265 A P R f n _6540 h1)). Qed.
Lemma lem292270 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (term290 A P R f n) = (_6540 P R f n).
Proof. exact (@lem292269 A P R f n _6540 h1). Qed.
Lemma lem292271 {A : Type'} (P : type1597 A) (n : nat) : (term380 A P n) = (term380 A P n).
Proof. exact (eq_refl (term380 A P n)). Qed.
Lemma lem292272 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (term381 A P R f n) = (term493 A _6540 P R f n).
Proof. exact (MK_COMB (@lem292271 A P n) (@lem292270 A P R f n _6540 h1)). Qed.
Lemma lem292273 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem292274 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (term401 A P R f n) = (term494 A _6540 P R f n).
Proof. exact (MK_COMB (@lem292273) (@lem292272 A P R f n _6540 h1)). Qed.
Lemma lem292276 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (term290 A P R f n) = (_6540 P R f n).
Proof. exact (EQ_MP (@lem292266 A _6540 P R f n) (@lem292265 A P R f n _6540 h1)). Qed.
Lemma lem292277 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (term290 A P R f n) = (_6540 P R f n).
Proof. exact (@lem292276 A P R f n _6540 h1). Qed.
Lemma lem292278 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term341 A R f n) = (term341 A R f n).
Proof. exact (eq_refl (term341 A R f n)). Qed.
Lemma lem292279 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (term343 A P R f n) = (term495 A _6540 P R f n).
Proof. exact (MK_COMB (@lem292278 A R f n) (@lem292277 A P R f n _6540 h1)). Qed.
Lemma lem292280 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (term403 A P R f n) = (term496 A _6540 P R f n).
Proof. exact (MK_COMB (@lem292274 A P R f n _6540 h1) (@lem292279 A P R f n _6540 h1)). Qed.
Lemma lem292281 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (x : A) : (term461 A P R f n x) = (term461 A P R f n x).
Proof. exact (eq_refl (term461 A P R f n x)). Qed.
Lemma lem292282 {A : Type'} (x : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (term463 A x P R f n) = (term497 A x _6540 P R f n).
Proof. exact (MK_COMB (@lem292281 A P R f n x) (@lem292280 A P R f n _6540 h1)). Qed.
Lemma lem292283 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (term465 A P R f n) = (term498 A _6540 P R f n).
Proof. exact (fun_ext (fun x : A => @lem292282 A x P R f n _6540 h1)). Qed.
Lemma lem292284 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem292285 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (term466 A P R f n) = (term499 A _6540 P R f n).
Proof. exact (MK_COMB (@lem292284 A) (@lem292283 A P R f n _6540 h1)). Qed.
Lemma lem292286 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (term500 A P R f) = (term501 A _6540 P R f).
Proof. exact (fun_ext (fun n : nat => @lem292285 A P R f n _6540 h1)). Qed.
Lemma lem292287 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem292288 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (term467 A P R f) = (term502 A _6540 P R f).
Proof. exact (MK_COMB (@lem292287) (@lem292286 A P R f _6540 h1)). Qed.
Lemma lem292289 {A : Type'} (P : type1597 A) (R : type1594 A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (term503 A P R) = (term504 A _6540 P R).
Proof. exact (fun_ext (fun f : nat -> A => @lem292288 A P R f _6540 h1)). Qed.
Lemma lem292290 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem292291 {A : Type'} (P : type1597 A) (R : type1594 A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (term468 A P R) = (term505 A _6540 P R).
Proof. exact (MK_COMB (@lem292290 A) (@lem292289 A P R _6540 h1)). Qed.
Lemma lem292292 {A : Type'} (P : type1597 A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (term506 A P) = (term507 A _6540 P).
Proof. exact (fun_ext (fun R : type1594 A => @lem292291 A P R _6540 h1)). Qed.
Lemma lem292293 {A : Type'} : (@all (nat -> A -> A -> Prop)) = (@all (nat -> A -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> A -> Prop))). Qed.
Lemma lem292294 {A : Type'} (P : type1597 A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (term469 A P) = (term508 A _6540 P).
Proof. exact (MK_COMB (@lem292293 A) (@lem292292 A P _6540 h1)). Qed.
Lemma lem292295 {A : Type'} (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (term509 A) = (term510 A _6540).
Proof. exact (fun_ext (fun P : type1597 A => @lem292294 A P _6540 h1)). Qed.
Lemma lem292296 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem292297 {A : Type'} (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (term470 A) = (term511 A _6540).
Proof. exact (MK_COMB (@lem292296 A) (@lem292295 A _6540 h1)). Qed.
Lemma lem292298 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem292299 {A : Type'} (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (term512 A) = (term513 A _6540).
Proof. exact (MK_COMB (@lem292298) (@lem292297 A _6540 h1)). Qed.
Lemma lem292301 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (term290 A P R f n) = (_6540 P R f n).
Proof. exact (EQ_MP (@lem292266 A _6540 P R f n) (@lem292265 A P R f n _6540 h1)). Qed.
Lemma lem292302 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (term290 A P R f n) = (_6540 P R f n).
Proof. exact (@lem292301 A P R f n _6540 h1). Qed.
Lemma lem292303 {A : Type'} (f : nat -> A) (n : nat) : (term302 A f n) = (term302 A f n).
Proof. exact (eq_refl (term302 A f n)). Qed.
Lemma lem292304 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : ((term289 A f n) = (term290 A P R f n)) = ((term289 A f n) = (_6540 P R f n)).
Proof. exact (MK_COMB (@lem292303 A f n) (@lem292302 A P R f n _6540 h1)). Qed.
Lemma lem292305 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (term304 A P R f) = (term514 A _6540 P R f).
Proof. exact (fun_ext (fun n : nat => @lem292304 A P R f n _6540 h1)). Qed.
Lemma lem292306 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem292307 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (term287 A P R f) = (term515 A _6540 P R f).
Proof. exact (MK_COMB (@lem292306) (@lem292305 A P R f _6540 h1)). Qed.
Lemma lem292308 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem292309 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (term444 A P R f) = (term516 A _6540 P R f).
Proof. exact (MK_COMB (@lem292308) (@lem292307 A P R f _6540 h1)). Qed.
Lemma lem292310 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term443 A P R f) = (term443 A P R f).
Proof. exact (eq_refl (term443 A P R f)). Qed.
Lemma lem292311 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (term446 A P R f) = (term517 A _6540 P R f).
Proof. exact (MK_COMB (@lem292309 A P R f _6540 h1) (@lem292310 A P R f)). Qed.
Lemma lem292312 {A : Type'} (f : nat -> A) (a : A) : (term447 A f a) = (term447 A f a).
Proof. exact (eq_refl (term447 A f a)). Qed.
Lemma lem292313 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (term449 A a P R f) = (term518 A a _6540 P R f).
Proof. exact (MK_COMB (@lem292312 A f a) (@lem292311 A P R f _6540 h1)). Qed.
Lemma lem292314 {A : Type'} (P : type1597 A) (R : type1594 A) : (term450 A P R) = (term450 A P R).
Proof. exact (eq_refl (term450 A P R)). Qed.
Lemma lem292315 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (term452 A a P R f) = (term519 A a _6540 P R f).
Proof. exact (MK_COMB (@lem292314 A P R) (@lem292313 A a P R f _6540 h1)). Qed.
Lemma lem292316 {A : Type'} (P : type1597 A) (a : A) : (term453 A P a) = (term453 A P a).
Proof. exact (eq_refl (term453 A P a)). Qed.
Lemma lem292317 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (term455 A a P R f) = (term520 A a _6540 P R f).
Proof. exact (MK_COMB (@lem292316 A P a) (@lem292315 A a P R f _6540 h1)). Qed.
Lemma lem292318 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (term471 A a P R f) = (term521 A a _6540 P R f).
Proof. exact (MK_COMB (@lem292299 A _6540 h1) (@lem292317 A a P R f _6540 h1)). Qed.
Lemma lem292319 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term522 A a P R f) : term522 A a P R f.
Proof. exact (h1). Qed.
Lemma lem292320 {A : Type'} (_6540 : type943 A) (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term522 A a P R f) : term523 A a P R f _6540.
Proof. exact (@lem292319 A a P R f h1 _6540). Qed.
Lemma lem292321 {A : Type'} (a : A) (_6540 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term523 A a P R f _6540) = (term521 A a _6540 P R f).
Proof. exact (eq_refl (term523 A a P R f _6540)). Qed.
Lemma lem292322 {A : Type'} (_6540 : type943 A) (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term522 A a P R f) : term521 A a _6540 P R f.
Proof. exact (EQ_MP (@lem292321 A a _6540 P R f) (@lem292320 A _6540 a P R f h1)). Qed.
Lemma lem292323 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : (term521 A a _6540 P R f) = (term471 A a P R f).
Proof. exact (SYM (@lem292318 A a P R f _6540 h1)). Qed.
Lemma lem292324 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6540 : type943 A) (h1 : term522 A a P R f) (h2 : _6540 = (term473 A)) : term471 A a P R f.
Proof. exact (EQ_MP (@lem292323 A a P R f _6540 h2) (@lem292322 A _6540 a P R f h1)). Qed.
Lemma lem292325 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : term524 A a P R f.
Proof. exact (fun h0 : term522 A a P R f => @lem292324 A a P R f _6540 h0 h1). Qed.
Lemma lem292326 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : term525 A a P R f.
Proof. exact (@lem51 (term471 A a P R f) (term522 A a P R f) (term455 A a P R f)). Qed.
Lemma lem292327 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : term526 A a P R f.
Proof. exact (@lem292326 A a P R f (@lem292325 A a P R f _6540 h1)). Qed.
Lemma lem292328 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6540 : type943 A) (h1 : _6540 = (term473 A)) : term527 A a P R f.
Proof. exact (@lem292327 A a P R f _6540 h1 (@lem292225 A a P R f)). Qed.
Lemma lem292329 {A : Type'} : (term473 A) = (term473 A).
Proof. exact (eq_refl (term473 A)). Qed.
Lemma lem292330 {A : Type'} (_6540 : type943 A) (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : term528 A _6540 a P R f.
Proof. exact (fun h0 : _6540 = (term473 A) => @lem292328 A a P R f _6540 h0). Qed.
Lemma lem292331 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : term529 A a P R f.
Proof. exact (@lem292330 A (term473 A) a P R f). Qed.
Lemma lem292332 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : term527 A a P R f.
Proof. exact (@lem292331 A a P R f (@lem292329 A)). Qed.
Lemma lem292333 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term522 A a P R f) : term522 A a P R f.
Proof. exact (h1). Qed.
Lemma lem292334 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : term530 A a P R f.
Proof. exact (fun h0 : term522 A a P R f => @lem292333 A a P R f h0). Qed.
Lemma lem292335 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : term531 A a P R f.
Proof. exact (@lem51 (term522 A a P R f) (term522 A a P R f) (term455 A a P R f)). Qed.
Lemma lem292336 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : term532 A a P R f.
Proof. exact (@lem292335 A a P R f (@lem292334 A a P R f)). Qed.
Lemma lem292337 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : term527 A a P R f.
Proof. exact (@lem292336 A a P R f (@lem292332 A a P R f)). Qed.
Lemma lem292338 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term527 A a P R f) : term527 A a P R f.
Proof. exact (h1). Qed.
Lemma lem292339 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term522 A a P R f) : term522 A a P R f.
Proof. exact (h1). Qed.
Lemma lem292340 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term522 A a P R f) (h2 : term527 A a P R f) : term455 A a P R f.
Proof. exact (@lem292338 A a P R f h2 (@lem292339 A a P R f h1)). Qed.
Lemma lem292341 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term522 A a P R f) : term533 A a P R f.
Proof. exact (fun h0 : term527 A a P R f => @lem292340 A a P R f h1 h0). Qed.
Lemma lem292342 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term527 A a P R f) : term527 A a P R f.
Proof. exact (h1). Qed.
Lemma lem292343 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term522 A a P R f) (h2 : term527 A a P R f) : term455 A a P R f.
Proof. exact (@lem292341 A a P R f h1 (@lem292342 A a P R f h2)). Qed.
Lemma lem292344 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term527 A a P R f) : term527 A a P R f.
Proof. exact (fun h0 : term522 A a P R f => @lem292343 A a P R f h0 h1). Qed.
Lemma lem292345 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : term532 A a P R f.
Proof. exact (fun h0 : term527 A a P R f => @lem292344 A a P R f h0). Qed.
Lemma lem292348 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : term527 A a P R f.
Proof. exact (@lem292345 A a P R f (@lem292337 A a P R f)). Qed.
Lemma lem292349 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : term527 A a P R f.
Proof. exact (@lem292348 A a P R f). Qed.
Lemma lem292471 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem292472 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term443 A P R f) = (term534 A P R f).
Proof. exact (@lem292471 (term440 A P R f)). Qed.
Lemma lem292474 (t : Prop) : (term210 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem292475 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term534 A P R f) = (term439 A P R f).
Proof. exact (@lem292474 (term439 A P R f)). Qed.
Lemma lem292524 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term443 A P R f) = (term439 A P R f).
Proof. exact (TRANS (@lem292472 A P R f) (@lem292475 A P R f)). Qed.
Lemma lem292527 {A : Type'} (_6540 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term516 A _6540 P R f) = (term516 A _6540 P R f).
Proof. exact (eq_refl (term516 A _6540 P R f)). Qed.
Lemma lem292528 {A : Type'} (_6540 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term517 A _6540 P R f) = (term535 A _6540 P R f).
Proof. exact (MK_COMB (@lem292527 A _6540 P R f) (@lem292524 A P R f)). Qed.
Lemma lem292531 {A : Type'} (f : nat -> A) (a : A) : (term447 A f a) = (term447 A f a).
Proof. exact (eq_refl (term447 A f a)). Qed.
Lemma lem292532 {A : Type'} (a : A) (_6540 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term518 A a _6540 P R f) = (term536 A a _6540 P R f).
Proof. exact (MK_COMB (@lem292531 A f a) (@lem292528 A _6540 P R f)). Qed.
Lemma lem292535 {A : Type'} (P : type1597 A) (R : type1594 A) : (term450 A P R) = (term450 A P R).
Proof. exact (eq_refl (term450 A P R)). Qed.
Lemma lem292536 {A : Type'} (a : A) (_6540 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term519 A a _6540 P R f) = (term537 A a _6540 P R f).
Proof. exact (MK_COMB (@lem292535 A P R) (@lem292532 A a _6540 P R f)). Qed.
Lemma lem292539 {A : Type'} (P : type1597 A) (a : A) : (term453 A P a) = (term453 A P a).
Proof. exact (eq_refl (term453 A P a)). Qed.
Lemma lem292540 {A : Type'} (a : A) (_6540 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term520 A a _6540 P R f) = (term538 A a _6540 P R f).
Proof. exact (MK_COMB (@lem292539 A P a) (@lem292536 A a _6540 P R f)). Qed.
Lemma lem292543 {A : Type'} (_6540 : type943 A) : (term513 A _6540) = (term513 A _6540).
Proof. exact (eq_refl (term513 A _6540)). Qed.
Lemma lem292544 {A : Type'} (a : A) (_6540 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term521 A a _6540 P R f) = (term539 A a _6540 P R f).
Proof. exact (MK_COMB (@lem292543 A _6540) (@lem292540 A a _6540 P R f)). Qed.
Lemma lem292547 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term540 A a P R f) = (term541 A a P R f).
Proof. exact (fun_ext (fun _6540 : type943 A => @lem292544 A a _6540 P R f)). Qed.
Lemma lem292548 {A : Type'} : (@all ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> (nat -> A) -> nat -> A)) = (@all ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> (nat -> A) -> nat -> A)).
Proof. exact (eq_refl (@all ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> (nat -> A) -> nat -> A))). Qed.
Lemma lem292549 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term522 A a P R f) = (term542 A a P R f).
Proof. exact (MK_COMB (@lem292548 A) (@lem292547 A a P R f)). Qed.
Lemma lem292554 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term543 A P R f) = (term544 A P R f).
Proof. exact (fun_ext (fun a : A => @lem292549 A a P R f)). Qed.
Lemma lem292555 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem292556 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term545 A P R f) = (term546 A P R f).
Proof. exact (MK_COMB (@lem292555 A) (@lem292554 A P R f)). Qed.
Lemma lem292561 {A : Type'} (R : type1594 A) (f : nat -> A) : (term547 A R f) = (term548 A R f).
Proof. exact (fun_ext (fun P : type1597 A => @lem292556 A P R f)). Qed.
Lemma lem292562 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem292563 {A : Type'} (R : type1594 A) (f : nat -> A) : (term549 A R f) = (term550 A R f).
Proof. exact (MK_COMB (@lem292562 A) (@lem292561 A R f)). Qed.
Lemma lem292568 {A : Type'} (f : nat -> A) : (term551 A f) = (term552 A f).
Proof. exact (fun_ext (fun R : type1594 A => @lem292563 A R f)). Qed.
Lemma lem292569 {A : Type'} : (@all (nat -> A -> A -> Prop)) = (@all (nat -> A -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> A -> Prop))). Qed.
Lemma lem292570 {A : Type'} (f : nat -> A) : (term553 A f) = (term554 A f).
Proof. exact (MK_COMB (@lem292569 A) (@lem292568 A f)). Qed.
Lemma lem292575 {A : Type'} : (term555 A) = (term556 A).
Proof. exact (fun_ext (fun f : nat -> A => @lem292570 A f)). Qed.
Lemma lem292576 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem292585 {A : Type'} : (term557 A) = (term558 A).
Proof. exact (MK_COMB (@lem292576 A) (@lem292575 A)). Qed.
Lemma lem292590 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (y : A) : (term559 A P R f y) = (term559 A P R f y).
Proof. exact (eq_refl (term559 A P R f y)). Qed.
Lemma lem292591 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term560 A P R f) = (term560 A P R f).
Proof. exact (fun_ext (fun y : A => @lem292590 A P R f y)). Qed.
Lemma lem292592 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem292593 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term439 A P R f) = (term439 A P R f).
Proof. exact (MK_COMB (@lem292592 A) (@lem292591 A P R f)). Qed.
Lemma lem292594 {A : Type'} (_6540 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : ((term289 A f n) = (_6540 P R f n)) = ((term289 A f n) = (_6540 P R f n)).
Proof. exact (eq_refl ((term289 A f n) = (_6540 P R f n))). Qed.
Lemma lem292595 {A : Type'} (_6540 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term514 A _6540 P R f) = (term514 A _6540 P R f).
Proof. exact (fun_ext (fun n : nat => @lem292594 A _6540 P R f n)). Qed.
Lemma lem292596 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem292597 {A : Type'} (_6540 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term515 A _6540 P R f) = (term515 A _6540 P R f).
Proof. exact (MK_COMB (@lem292596) (@lem292595 A _6540 P R f)). Qed.
Lemma lem292598 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem292599 {A : Type'} (_6540 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term516 A _6540 P R f) = (term516 A _6540 P R f).
Proof. exact (MK_COMB (@lem292598) (@lem292597 A _6540 P R f)). Qed.
Lemma lem292600 {A : Type'} (_6540 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term535 A _6540 P R f) = (term535 A _6540 P R f).
Proof. exact (MK_COMB (@lem292599 A _6540 P R f) (@lem292593 A P R f)). Qed.
Lemma lem292603 {A : Type'} (f : nat -> A) (a : A) : (term447 A f a) = (term447 A f a).
Proof. exact (eq_refl (term447 A f a)). Qed.
Lemma lem292604 {A : Type'} (a : A) (_6540 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term536 A a _6540 P R f) = (term536 A a _6540 P R f).
Proof. exact (MK_COMB (@lem292603 A f a) (@lem292600 A _6540 P R f)). Qed.
Lemma lem292609 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) (y : A) : (term561 A P R n x y) = (term561 A P R n x y).
Proof. exact (eq_refl (term561 A P R n x y)). Qed.
Lemma lem292610 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term562 A P R n x) = (term562 A P R n x).
Proof. exact (fun_ext (fun y : A => @lem292609 A P R n x y)). Qed.
Lemma lem292611 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem292612 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term563 A P R n x) = (term563 A P R n x).
Proof. exact (MK_COMB (@lem292611 A) (@lem292610 A P R n x)). Qed.
Lemma lem292615 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (term564 A P n x) = (term564 A P n x).
Proof. exact (eq_refl (term564 A P n x)). Qed.
Lemma lem292616 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term565 A P R n x) = (term565 A P R n x).
Proof. exact (MK_COMB (@lem292615 A P n x) (@lem292612 A P R n x)). Qed.
Lemma lem292617 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term566 A P R n) = (term566 A P R n).
Proof. exact (fun_ext (fun x : A => @lem292616 A P R n x)). Qed.
Lemma lem292618 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem292619 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term567 A P R n) = (term567 A P R n).
Proof. exact (MK_COMB (@lem292618 A) (@lem292617 A P R n)). Qed.
Lemma lem292620 {A : Type'} (P : type1597 A) (R : type1594 A) : (term568 A P R) = (term568 A P R).
Proof. exact (fun_ext (fun n : nat => @lem292619 A P R n)). Qed.
Lemma lem292621 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem292622 {A : Type'} (P : type1597 A) (R : type1594 A) : (term312 A P R) = (term312 A P R).
Proof. exact (MK_COMB (@lem292621) (@lem292620 A P R)). Qed.
Lemma lem292623 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem292624 {A : Type'} (P : type1597 A) (R : type1594 A) : (term450 A P R) = (term450 A P R).
Proof. exact (MK_COMB (@lem292623) (@lem292622 A P R)). Qed.
Lemma lem292625 {A : Type'} (a : A) (_6540 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term537 A a _6540 P R f) = (term537 A a _6540 P R f).
Proof. exact (MK_COMB (@lem292624 A P R) (@lem292604 A a _6540 P R f)). Qed.
Lemma lem292628 {A : Type'} (P : type1597 A) (a : A) : (term453 A P a) = (term453 A P a).
Proof. exact (eq_refl (term453 A P a)). Qed.
Lemma lem292629 {A : Type'} (a : A) (_6540 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term538 A a _6540 P R f) = (term538 A a _6540 P R f).
Proof. exact (MK_COMB (@lem292628 A P a) (@lem292625 A a _6540 P R f)). Qed.
Lemma lem292642 {A : Type'} (x : A) (_6540 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term497 A x _6540 P R f n) = (term497 A x _6540 P R f n).
Proof. exact (eq_refl (term497 A x _6540 P R f n)). Qed.
Lemma lem292643 {A : Type'} (_6540 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term498 A _6540 P R f n) = (term498 A _6540 P R f n).
Proof. exact (fun_ext (fun x : A => @lem292642 A x _6540 P R f n)). Qed.
Lemma lem292644 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem292645 {A : Type'} (_6540 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term499 A _6540 P R f n) = (term499 A _6540 P R f n).
Proof. exact (MK_COMB (@lem292644 A) (@lem292643 A _6540 P R f n)). Qed.
Lemma lem292646 {A : Type'} (_6540 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term501 A _6540 P R f) = (term501 A _6540 P R f).
Proof. exact (fun_ext (fun n : nat => @lem292645 A _6540 P R f n)). Qed.
Lemma lem292647 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem292648 {A : Type'} (_6540 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term502 A _6540 P R f) = (term502 A _6540 P R f).
Proof. exact (MK_COMB (@lem292647) (@lem292646 A _6540 P R f)). Qed.
Lemma lem292649 {A : Type'} (_6540 : type943 A) (P : type1597 A) (R : type1594 A) : (term504 A _6540 P R) = (term504 A _6540 P R).
Proof. exact (fun_ext (fun f : nat -> A => @lem292648 A _6540 P R f)). Qed.
Lemma lem292650 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem292651 {A : Type'} (_6540 : type943 A) (P : type1597 A) (R : type1594 A) : (term505 A _6540 P R) = (term505 A _6540 P R).
Proof. exact (MK_COMB (@lem292650 A) (@lem292649 A _6540 P R)). Qed.
Lemma lem292652 {A : Type'} (_6540 : type943 A) (P : type1597 A) : (term507 A _6540 P) = (term507 A _6540 P).
Proof. exact (fun_ext (fun R : type1594 A => @lem292651 A _6540 P R)). Qed.
Lemma lem292653 {A : Type'} : (@all (nat -> A -> A -> Prop)) = (@all (nat -> A -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> A -> Prop))). Qed.
Lemma lem292654 {A : Type'} (_6540 : type943 A) (P : type1597 A) : (term508 A _6540 P) = (term508 A _6540 P).
Proof. exact (MK_COMB (@lem292653 A) (@lem292652 A _6540 P)). Qed.
Lemma lem292655 {A : Type'} (_6540 : type943 A) : (term510 A _6540) = (term510 A _6540).
Proof. exact (fun_ext (fun P : type1597 A => @lem292654 A _6540 P)). Qed.
Lemma lem292656 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem292657 {A : Type'} (_6540 : type943 A) : (term511 A _6540) = (term511 A _6540).
Proof. exact (MK_COMB (@lem292656 A) (@lem292655 A _6540)). Qed.
Lemma lem292658 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem292659 {A : Type'} (_6540 : type943 A) : (term513 A _6540) = (term513 A _6540).
Proof. exact (MK_COMB (@lem292658) (@lem292657 A _6540)). Qed.
Lemma lem292660 {A : Type'} (a : A) (_6540 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term539 A a _6540 P R f) = (term539 A a _6540 P R f).
Proof. exact (MK_COMB (@lem292659 A _6540) (@lem292629 A a _6540 P R f)). Qed.
Lemma lem292661 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term541 A a P R f) = (term541 A a P R f).
Proof. exact (fun_ext (fun _6540 : type943 A => @lem292660 A a _6540 P R f)). Qed.
Lemma lem292662 {A : Type'} : (@all ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> (nat -> A) -> nat -> A)) = (@all ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> (nat -> A) -> nat -> A)).
Proof. exact (eq_refl (@all ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> (nat -> A) -> nat -> A))). Qed.
Lemma lem292663 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term542 A a P R f) = (term542 A a P R f).
Proof. exact (MK_COMB (@lem292662 A) (@lem292661 A a P R f)). Qed.
Lemma lem292664 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term544 A P R f) = (term544 A P R f).
Proof. exact (fun_ext (fun a : A => @lem292663 A a P R f)). Qed.
Lemma lem292665 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem292666 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term546 A P R f) = (term546 A P R f).
Proof. exact (MK_COMB (@lem292665 A) (@lem292664 A P R f)). Qed.
Lemma lem292667 {A : Type'} (R : type1594 A) (f : nat -> A) : (term548 A R f) = (term548 A R f).
Proof. exact (fun_ext (fun P : type1597 A => @lem292666 A P R f)). Qed.
Lemma lem292668 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem292669 {A : Type'} (R : type1594 A) (f : nat -> A) : (term550 A R f) = (term550 A R f).
Proof. exact (MK_COMB (@lem292668 A) (@lem292667 A R f)). Qed.
Lemma lem292670 {A : Type'} (f : nat -> A) : (term552 A f) = (term552 A f).
Proof. exact (fun_ext (fun R : type1594 A => @lem292669 A R f)). Qed.
Lemma lem292671 {A : Type'} : (@all (nat -> A -> A -> Prop)) = (@all (nat -> A -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> A -> Prop))). Qed.
Lemma lem292672 {A : Type'} (f : nat -> A) : (term554 A f) = (term554 A f).
Proof. exact (MK_COMB (@lem292671 A) (@lem292670 A f)). Qed.
Lemma lem292673 {A : Type'} : (term556 A) = (term556 A).
Proof. exact (fun_ext (fun f : nat -> A => @lem292672 A f)). Qed.
Lemma lem292674 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem292675 {A : Type'} : (term558 A) = (term558 A).
Proof. exact (MK_COMB (@lem292674 A) (@lem292673 A)). Qed.
Lemma lem292790 {A : Type'} : (term557 A) = (term558 A).
Proof. exact (TRANS (@lem292585 A) (@lem292675 A)). Qed.
Lemma lem292791 {A : Type'} : (term558 A) = (term557 A).
Proof. exact (SYM (@lem292790 A)). Qed.
Lemma lem292794 {A : Type'} (P : type1597 A) (R : type1594 A) (h1 : term312 A P R) : term312 A P R.
Proof. exact (h1). Qed.
Lemma lem292798 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem292799 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term439 A P R f) = (term443 A P R f).
Proof. exact (@lem292798 (term439 A P R f)). Qed.
Lemma lem292800 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term443 A P R f) = (term439 A P R f).
Proof. exact (SYM (@lem292799 A P R f)). Qed.
Lemma lem292801 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term440 A P R f) : term440 A P R f.
Proof. exact (h1). Qed.
Lemma lem293023 {A : Type'} (P : type1597 A) (a : A) (h1 : term313 A P a) : term313 A P a.
Proof. exact (h1). Qed.
Lemma lem293029 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) (y : A) : (term561 A P R n x y) = (term561 A P R n x y).
Proof. exact (eq_refl (term561 A P R n x y)). Qed.
Lemma lem293030 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term562 A P R n x) = (term562 A P R n x).
Proof. exact (fun_ext (fun y : A => @lem293029 A P R n x y)). Qed.
Lemma lem293031 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem293032 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term563 A P R n x) = (term563 A P R n x).
Proof. exact (MK_COMB (@lem293031 A) (@lem293030 A P R n x)). Qed.
Lemma lem293034 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (term569 A P n x) = (term569 A P n x).
Proof. exact (eq_refl (term569 A P n x)). Qed.
Lemma lem293035 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term570 A P R n x) = (term570 A P R n x).
Proof. exact (MK_COMB (@lem293034 A P n x) (@lem293032 A P R n x)). Qed.
Lemma lem293036 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term565 A P R n x) = (term570 A P R n x).
Proof. exact (@lem17265 (P n x) (term563 A P R n x)). Qed.
Lemma lem293037 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term565 A P R n x) = (term570 A P R n x).
Proof. exact (TRANS (@lem293036 A P R n x) (@lem293035 A P R n x)). Qed.
Lemma lem293038 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term566 A P R n) = (term571 A P R n).
Proof. exact (fun_ext (fun x : A => @lem293037 A P R n x)). Qed.
Lemma lem293039 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem293040 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term567 A P R n) = (term572 A P R n).
Proof. exact (MK_COMB (@lem293039 A) (@lem293038 A P R n)). Qed.
Lemma lem293041 {A : Type'} (P : type1597 A) (R : type1594 A) : (term568 A P R) = (term573 A P R).
Proof. exact (fun_ext (fun n : nat => @lem293040 A P R n)). Qed.
Lemma lem293042 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem293043 {A : Type'} (P : type1597 A) (R : type1594 A) : (term312 A P R) = (term574 A P R).
Proof. exact (MK_COMB (@lem293042) (@lem293041 A P R)). Qed.
Lemma lem293146 {A : Type'} (P : Prop) (Q : A -> Prop) : (term69 A P Q) = (term70 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem293147 {A : Type'} (P : Prop) (Q : A -> Prop) : (term69 A P Q) = (term70 A P Q).
Proof. exact (@lem293146 A P Q). Qed.
Lemma lem293148 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term575 A P R n x) = (term576 A P R n x).
Proof. exact (@lem293147 A (term577 A P n x) (term562 A P R n x)). Qed.
Lemma lem293149 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) (y : A) : (term578 A P R n x y) = (term561 A P R n x y).
Proof. exact (eq_refl (term578 A P R n x y)). Qed.
Lemma lem293150 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term579 A P R n x) = (term562 A P R n x).
Proof. exact (fun_ext (fun y : A => @lem293149 A P R n x y)). Qed.
Lemma lem293151 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem293152 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term580 A P R n x) = (term563 A P R n x).
Proof. exact (MK_COMB (@lem293151 A) (@lem293150 A P R n x)). Qed.
Lemma lem293153 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (term569 A P n x) = (term569 A P n x).
Proof. exact (eq_refl (term569 A P n x)). Qed.
Lemma lem293154 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term575 A P R n x) = (term570 A P R n x).
Proof. exact (MK_COMB (@lem293153 A P n x) (@lem293152 A P R n x)). Qed.
Lemma lem293155 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem293156 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term581 A P R n x) = (term582 A P R n x).
Proof. exact (MK_COMB (@lem293155) (@lem293154 A P R n x)). Qed.
Lemma lem293157 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) (y : A) : (term578 A P R n x y) = (term561 A P R n x y).
Proof. exact (eq_refl (term578 A P R n x y)). Qed.
Lemma lem293158 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (term569 A P n x) = (term569 A P n x).
Proof. exact (eq_refl (term569 A P n x)). Qed.
Lemma lem293159 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) (y : A) : (term583 A P R n x y) = (term584 A P R n x y).
Proof. exact (MK_COMB (@lem293158 A P n x) (@lem293157 A P R n x y)). Qed.
Lemma lem293160 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term585 A P R n x) = (term586 A P R n x).
Proof. exact (fun_ext (fun y : A => @lem293159 A P R n x y)). Qed.
Lemma lem293161 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem293162 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term576 A P R n x) = (term587 A P R n x).
Proof. exact (MK_COMB (@lem293161 A) (@lem293160 A P R n x)). Qed.
Lemma lem293163 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : ((term575 A P R n x) = (term576 A P R n x)) = ((term570 A P R n x) = (term587 A P R n x)).
Proof. exact (MK_COMB (@lem293156 A P R n x) (@lem293162 A P R n x)). Qed.
Lemma lem293164 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term570 A P R n x) = (term587 A P R n x).
Proof. exact (EQ_MP (@lem293163 A P R n x) (@lem293148 A P R n x)). Qed.
Lemma lem293165 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term571 A P R n) = (term588 A P R n).
Proof. exact (fun_ext (fun x : A => @lem293164 A P R n x)). Qed.
Lemma lem293166 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem293167 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term572 A P R n) = (term589 A P R n).
Proof. exact (MK_COMB (@lem293166 A) (@lem293165 A P R n)). Qed.
Lemma lem293169 {A B : Type'} (P : type1413 A B) : (term160 A B P) = (term161 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem293170 {A : Type'} (P : type1402 A) : (term590 A P) = (term591 A P).
Proof. exact (@lem293169 A A P). Qed.
Lemma lem293171 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term592 A P R n) = (term593 A P R n).
Proof. exact (@lem293170 A (term594 A P R n)). Qed.
Lemma lem293172 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term595 A P R n x) = (term586 A P R n x).
Proof. exact (eq_refl (term595 A P R n x)). Qed.
Lemma lem293173 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem293174 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) (y : A) : (term596 A P R n x y) = (term597 A P R n x y).
Proof. exact (MK_COMB (@lem293172 A P R n x) (@lem293173 A y)). Qed.
Lemma lem293175 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) (y : A) : (term597 A P R n x y) = (term584 A P R n x y).
Proof. exact (eq_refl (term597 A P R n x y)). Qed.
Lemma lem293176 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) (y : A) : (term596 A P R n x y) = (term584 A P R n x y).
Proof. exact (TRANS (@lem293174 A P R n x y) (@lem293175 A P R n x y)). Qed.
Lemma lem293177 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term598 A P R n x) = (term586 A P R n x).
Proof. exact (fun_ext (fun y : A => @lem293176 A P R n x y)). Qed.
Lemma lem293178 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem293179 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term599 A P R n x) = (term587 A P R n x).
Proof. exact (MK_COMB (@lem293178 A) (@lem293177 A P R n x)). Qed.
Lemma lem293180 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term600 A P R n) = (term588 A P R n).
Proof. exact (fun_ext (fun x : A => @lem293179 A P R n x)). Qed.
Lemma lem293181 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem293182 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term592 A P R n) = (term589 A P R n).
Proof. exact (MK_COMB (@lem293181 A) (@lem293180 A P R n)). Qed.
Lemma lem293183 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem293184 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term601 A P R n) = (term602 A P R n).
Proof. exact (MK_COMB (@lem293183) (@lem293182 A P R n)). Qed.
Lemma lem293185 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term595 A P R n x) = (term586 A P R n x).
Proof. exact (eq_refl (term595 A P R n x)). Qed.
Lemma lem293186 {A : Type'} (y : A -> A) (x : A) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem293187 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (y : A -> A) (x : A) : (term603 A P R n y x) = (term604 A P R n y x).
Proof. exact (MK_COMB (@lem293185 A P R n x) (@lem293186 A y x)). Qed.
Lemma lem293188 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (y : A -> A) (x : A) : (term604 A P R n y x) = (term605 A P R n y x).
Proof. exact (eq_refl (term604 A P R n y x)). Qed.
Lemma lem293189 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (y : A -> A) (x : A) : (term603 A P R n y x) = (term605 A P R n y x).
Proof. exact (TRANS (@lem293187 A P R n y x) (@lem293188 A P R n y x)). Qed.
Lemma lem293190 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (y : A -> A) : (term606 A P R n y) = (term607 A P R n y).
Proof. exact (fun_ext (fun x : A => @lem293189 A P R n y x)). Qed.
Lemma lem293191 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem293192 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (y : A -> A) : (term608 A P R n y) = (term609 A P R n y).
Proof. exact (MK_COMB (@lem293191 A) (@lem293190 A P R n y)). Qed.
Lemma lem293193 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term610 A P R n) = (term611 A P R n).
Proof. exact (fun_ext (fun y : A -> A => @lem293192 A P R n y)). Qed.
Lemma lem293194 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem293195 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term593 A P R n) = (term612 A P R n).
Proof. exact (MK_COMB (@lem293194 A) (@lem293193 A P R n)). Qed.
Lemma lem293196 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : ((term592 A P R n) = (term593 A P R n)) = ((term589 A P R n) = (term612 A P R n)).
Proof. exact (MK_COMB (@lem293184 A P R n) (@lem293195 A P R n)). Qed.
Lemma lem293197 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term589 A P R n) = (term612 A P R n).
Proof. exact (EQ_MP (@lem293196 A P R n) (@lem293171 A P R n)). Qed.
Lemma lem293198 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term572 A P R n) = (term612 A P R n).
Proof. exact (TRANS (@lem293167 A P R n) (@lem293197 A P R n)). Qed.
Lemma lem293199 {A : Type'} (P : type1597 A) (R : type1594 A) : (term573 A P R) = (term613 A P R).
Proof. exact (fun_ext (fun n : nat => @lem293198 A P R n)). Qed.
Lemma lem293200 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem293201 {A : Type'} (P : type1597 A) (R : type1594 A) : (term574 A P R) = (term614 A P R).
Proof. exact (MK_COMB (@lem293200) (@lem293199 A P R)). Qed.
Lemma lem293203 {A B : Type'} (P : type1413 A B) : (term160 A B P) = (term161 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem293204 {A : Type'} (P : type1571 A) : (term615 A P) = (term616 A P).
Proof. exact (@lem293203 nat (A -> A) P). Qed.
Lemma lem293205 {A : Type'} (P : type1597 A) (R : type1594 A) : (term617 A P R) = (term618 A P R).
Proof. exact (@lem293204 A (term619 A P R)). Qed.
Lemma lem293206 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term620 A P R n) = (term611 A P R n).
Proof. exact (eq_refl (term620 A P R n)). Qed.
Lemma lem293207 {A : Type'} (y : A -> A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem293208 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (y : A -> A) : (term621 A P R n y) = (term622 A P R n y).
Proof. exact (MK_COMB (@lem293206 A P R n) (@lem293207 A y)). Qed.
Lemma lem293209 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (y : A -> A) : (term622 A P R n y) = (term609 A P R n y).
Proof. exact (eq_refl (term622 A P R n y)). Qed.
Lemma lem293210 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (y : A -> A) : (term621 A P R n y) = (term609 A P R n y).
Proof. exact (TRANS (@lem293208 A P R n y) (@lem293209 A P R n y)). Qed.
Lemma lem293211 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term623 A P R n) = (term611 A P R n).
Proof. exact (fun_ext (fun y : A -> A => @lem293210 A P R n y)). Qed.
Lemma lem293212 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem293213 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term624 A P R n) = (term612 A P R n).
Proof. exact (MK_COMB (@lem293212 A) (@lem293211 A P R n)). Qed.
Lemma lem293214 {A : Type'} (P : type1597 A) (R : type1594 A) : (term625 A P R) = (term613 A P R).
Proof. exact (fun_ext (fun n : nat => @lem293213 A P R n)). Qed.
Lemma lem293215 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem293216 {A : Type'} (P : type1597 A) (R : type1594 A) : (term617 A P R) = (term614 A P R).
Proof. exact (MK_COMB (@lem293215) (@lem293214 A P R)). Qed.
Lemma lem293217 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem293218 {A : Type'} (P : type1597 A) (R : type1594 A) : (term626 A P R) = (term627 A P R).
Proof. exact (MK_COMB (@lem293217) (@lem293216 A P R)). Qed.
Lemma lem293219 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term620 A P R n) = (term611 A P R n).
Proof. exact (eq_refl (term620 A P R n)). Qed.
Lemma lem293220 {A : Type'} (y : type1596 A) (n : nat) : (y n) = (y n).
Proof. exact (eq_refl (y n)). Qed.
Lemma lem293221 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (n : nat) : (term628 A P R y n) = (term629 A P R y n).
Proof. exact (MK_COMB (@lem293219 A P R n) (@lem293220 A y n)). Qed.
Lemma lem293222 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (n : nat) : (term629 A P R y n) = (term630 A P R y n).
Proof. exact (eq_refl (term629 A P R y n)). Qed.
Lemma lem293223 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (n : nat) : (term628 A P R y n) = (term630 A P R y n).
Proof. exact (TRANS (@lem293221 A P R y n) (@lem293222 A P R y n)). Qed.
Lemma lem293224 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) : (term631 A P R y) = (term632 A P R y).
Proof. exact (fun_ext (fun n : nat => @lem293223 A P R y n)). Qed.
Lemma lem293225 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem293226 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) : (term633 A P R y) = (term634 A P R y).
Proof. exact (MK_COMB (@lem293225) (@lem293224 A P R y)). Qed.
Lemma lem293227 {A : Type'} (P : type1597 A) (R : type1594 A) : (term635 A P R) = (term636 A P R).
Proof. exact (fun_ext (fun y : type1596 A => @lem293226 A P R y)). Qed.
Lemma lem293228 {A : Type'} : (@ex (nat -> A -> A)) = (@ex (nat -> A -> A)).
Proof. exact (eq_refl (@ex (nat -> A -> A))). Qed.
Lemma lem293229 {A : Type'} (P : type1597 A) (R : type1594 A) : (term618 A P R) = (term637 A P R).
Proof. exact (MK_COMB (@lem293228 A) (@lem293227 A P R)). Qed.
Lemma lem293230 {A : Type'} (P : type1597 A) (R : type1594 A) : ((term617 A P R) = (term618 A P R)) = ((term614 A P R) = (term637 A P R)).
Proof. exact (MK_COMB (@lem293218 A P R) (@lem293229 A P R)). Qed.
Lemma lem293231 {A : Type'} (P : type1597 A) (R : type1594 A) : (term614 A P R) = (term637 A P R).
Proof. exact (EQ_MP (@lem293230 A P R) (@lem293205 A P R)). Qed.
Lemma lem293233 {A : Type'} (P : type1597 A) (R : type1594 A) : (term574 A P R) = (term637 A P R).
Proof. exact (TRANS (@lem293201 A P R) (@lem293231 A P R)). Qed.
Lemma lem293234 {A : Type'} (P : type1597 A) (R : type1594 A) : (term312 A P R) = (term637 A P R).
Proof. exact (TRANS (@lem293043 A P R) (@lem293233 A P R)). Qed.
Lemma lem293235 {A : Type'} (P : type1597 A) (R : type1594 A) (h1 : term312 A P R) : term637 A P R.
Proof. exact (EQ_MP (@lem293234 A P R) (@lem292794 A P R h1)). Qed.
Lemma lem293241 {A : Type'} (f : nat -> A) (a : A) (h1 : (term286 A f) = a) : (term286 A f) = a.
Proof. exact (h1). Qed.
Lemma lem293261 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (y : A) : (term638 A P R f y) = (term639 A P R f y).
Proof. exact (@lem17045 (term640 A P y) (term641 A R f y)). Qed.
Lemma lem293262 {A : Type'} (P : A -> Prop) : (term642 A P) = (term643 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem293263 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term440 A P R f) = (term644 A P R f).
Proof. exact (@lem293262 A (term560 A P R f)). Qed.
Lemma lem293264 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (y : A) : (term645 A P R f y) = (term559 A P R f y).
Proof. exact (eq_refl (term645 A P R f y)). Qed.
Lemma lem293265 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem293266 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (y : A) : (term646 A P R f y) = (term638 A P R f y).
Proof. exact (MK_COMB (@lem293265) (@lem293264 A P R f y)). Qed.
Lemma lem293267 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (y : A) : (term646 A P R f y) = (term639 A P R f y).
Proof. exact (TRANS (@lem293266 A P R f y) (@lem293261 A P R f y)). Qed.
Lemma lem293268 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term647 A P R f) = (term648 A P R f).
Proof. exact (fun_ext (fun y : A => @lem293267 A P R f y)). Qed.
Lemma lem293269 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem293270 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term644 A P R f) = (term649 A P R f).
Proof. exact (MK_COMB (@lem293269 A) (@lem293268 A P R f)). Qed.
Lemma lem293323 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term440 A P R f) = (term649 A P R f).
Proof. exact (TRANS (@lem293263 A P R f) (@lem293270 A P R f)). Qed.
Lemma lem293324 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term440 A P R f) : term649 A P R f.
Proof. exact (EQ_MP (@lem293323 A P R f) (@lem292801 A P R f h1)). Qed.
Lemma lem293325 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (h1 : term634 A P R y) : term634 A P R y.
Proof. exact (h1). Qed.
Lemma lem293537 {A : Type'} (P : type1597 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem293542 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem293543 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem293542 nat nat f x). Qed.
Lemma lem293545 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem293543 NUMERAL 0). Qed.
Lemma lem293546 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem293547 {A : Type'} (P : type1597 A) : (term379 A P) = (term650 A P).
Proof. exact (MK_COMB (@lem293537 A P) (@lem293545)). Qed.
Lemma lem293548 {A : Type'} (P : type1597 A) (a : A) : (term313 A P a) = (term651 A P a).
Proof. exact (MK_COMB (@lem293547 A P) (@lem293546 A a)). Qed.
Lemma lem293550 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem293551 {A : Type'} (f : type1597 A) (x : nat) : (f x) = (@I (nat -> A -> Prop) f x).
Proof. exact (@lem293550 nat (A -> Prop) f x). Qed.
Lemma lem293552 {A : Type'} (P : type1597 A) : (term650 A P) = (term652 A P).
Proof. exact (@lem293551 A P (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem293553 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem293554 {A : Type'} (P : type1597 A) (a : A) : (term651 A P a) = (term653 A P a).
Proof. exact (MK_COMB (@lem293552 A P) (@lem293553 A a)). Qed.
Lemma lem293556 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem293557 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem293556 A Prop f x). Qed.
Lemma lem293558 {A : Type'} (P : type1597 A) (a : A) : (term653 A P a) = (term654 A P a).
Proof. exact (@lem293557 A (term652 A P) a). Qed.
Lemma lem293559 {A : Type'} (P : type1597 A) (a : A) : (term651 A P a) = (term654 A P a).
Proof. exact (TRANS (@lem293554 A P a) (@lem293558 A P a)). Qed.
Lemma lem293560 {A : Type'} (P : type1597 A) (a : A) : (term313 A P a) = (term654 A P a).
Proof. exact (TRANS (@lem293548 A P a) (@lem293559 A P a)). Qed.
Lemma lem293562 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem293563 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem293568 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem293569 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem293568 nat nat f x). Qed.
Lemma lem293571 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem293569 NUMERAL 0). Qed.
Lemma lem293572 {A : Type'} (f : nat -> A) : (term286 A f) = (term655 A f).
Proof. exact (MK_COMB (@lem293563 A f) (@lem293571)). Qed.
Lemma lem293574 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem293575 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem293574 nat A f x). Qed.
Lemma lem293576 {A : Type'} (f : nat -> A) : (term655 A f) = (term656 A f).
Proof. exact (@lem293575 A f (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem293577 {A : Type'} (f : nat -> A) : (term286 A f) = (term656 A f).
Proof. exact (TRANS (@lem293572 A f) (@lem293576 A f)). Qed.
Lemma lem293578 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem293579 {A : Type'} (f : nat -> A) : (term340 A f) = (term657 A f).
Proof. exact (MK_COMB (@lem293562 A) (@lem293577 A f)). Qed.
Lemma lem293580 {A : Type'} (f : nat -> A) (a : A) : ((term286 A f) = a) = ((term656 A f) = a).
Proof. exact (MK_COMB (@lem293579 A f) (@lem293578 A a)). Qed.
Lemma lem293639 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem293640 {A : Type'} (R : type1594 A) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem293645 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem293646 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem293645 nat nat f x). Qed.
Lemma lem293648 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem293646 NUMERAL 0). Qed.
Lemma lem293649 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem293654 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem293655 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem293654 nat nat f x). Qed.
Lemma lem293657 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem293655 NUMERAL 0). Qed.
Lemma lem293658 {A : Type'} (f : nat -> A) : (term286 A f) = (term655 A f).
Proof. exact (MK_COMB (@lem293649 A f) (@lem293657)). Qed.
Lemma lem293660 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem293661 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem293660 nat A f x). Qed.
Lemma lem293662 {A : Type'} (f : nat -> A) : (term655 A f) = (term656 A f).
Proof. exact (@lem293661 A f (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem293663 {A : Type'} (f : nat -> A) : (term286 A f) = (term656 A f).
Proof. exact (TRANS (@lem293658 A f) (@lem293662 A f)). Qed.
Lemma lem293664 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem293665 {A : Type'} (R : type1594 A) : (term658 A R) = (term659 A R).
Proof. exact (MK_COMB (@lem293640 A R) (@lem293648)). Qed.
Lemma lem293666 {A : Type'} (R : type1594 A) (f : nat -> A) : (term660 A R f) = (term661 A R f).
Proof. exact (MK_COMB (@lem293665 A R) (@lem293663 A f)). Qed.
Lemma lem293667 {A : Type'} (R : type1594 A) (f : nat -> A) (y : A) : (term641 A R f y) = (term662 A R f y).
Proof. exact (MK_COMB (@lem293666 A R f) (@lem293664 A y)). Qed.
Lemma lem293669 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem293670 {A : Type'} (f : type1594 A) (x : nat) : (f x) = (@I (nat -> A -> A -> Prop) f x).
Proof. exact (@lem293669 nat (type1402 A) f x). Qed.
Lemma lem293671 {A : Type'} (R : type1594 A) : (term659 A R) = (term663 A R).
Proof. exact (@lem293670 A R (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem293672 {A : Type'} (f : nat -> A) : (term656 A f) = (term656 A f).
Proof. exact (eq_refl (term656 A f)). Qed.
Lemma lem293673 {A : Type'} (R : type1594 A) (f : nat -> A) : (term661 A R f) = (term664 A R f).
Proof. exact (MK_COMB (@lem293671 A R) (@lem293672 A f)). Qed.
Lemma lem293675 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem293676 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem293675 A (A -> Prop) f x). Qed.
Lemma lem293677 {A : Type'} (R : type1594 A) (f : nat -> A) : (term664 A R f) = (term665 A R f).
Proof. exact (@lem293676 A (term663 A R) (term656 A f)). Qed.
Lemma lem293678 {A : Type'} (R : type1594 A) (f : nat -> A) : (term661 A R f) = (term665 A R f).
Proof. exact (TRANS (@lem293673 A R f) (@lem293677 A R f)). Qed.
Lemma lem293679 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem293680 {A : Type'} (R : type1594 A) (f : nat -> A) (y : A) : (term662 A R f y) = (term666 A R f y).
Proof. exact (MK_COMB (@lem293678 A R f) (@lem293679 A y)). Qed.
Lemma lem293682 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem293683 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem293682 A Prop f x). Qed.
Lemma lem293684 {A : Type'} (R : type1594 A) (f : nat -> A) (y : A) : (term666 A R f y) = (term667 A R f y).
Proof. exact (@lem293683 A (term665 A R f) y). Qed.
Lemma lem293685 {A : Type'} (R : type1594 A) (f : nat -> A) (y : A) : (term662 A R f y) = (term667 A R f y).
Proof. exact (TRANS (@lem293680 A R f y) (@lem293684 A R f y)). Qed.
Lemma lem293686 {A : Type'} (R : type1594 A) (f : nat -> A) (y : A) : (term641 A R f y) = (term667 A R f y).
Proof. exact (TRANS (@lem293667 A R f y) (@lem293685 A R f y)). Qed.
Lemma lem293687 {A : Type'} (R : type1594 A) (f : nat -> A) (y : A) : (term668 A R f y) = (term669 A R f y).
Proof. exact (MK_COMB (@lem293639) (@lem293686 A R f y)). Qed.
Lemma lem293688 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem293689 {A : Type'} (P : type1597 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem293690 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem293695 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem293696 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem293695 nat nat f x). Qed.
Lemma lem293698 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem293696 NUMERAL 0). Qed.
Lemma lem293699 : term670 = term671.
Proof. exact (MK_COMB (@lem293690) (@lem293698)). Qed.
Lemma lem293701 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem293702 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem293701 nat nat f x). Qed.
Lemma lem293703 : term671 = term672.
Proof. exact (@lem293702 S (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem293704 : term670 = term672.
Proof. exact (TRANS (@lem293699) (@lem293703)). Qed.
Lemma lem293705 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem293706 {A : Type'} (P : type1597 A) : (term673 A P) = (term674 A P).
Proof. exact (MK_COMB (@lem293689 A P) (@lem293704)). Qed.
Lemma lem293707 {A : Type'} (P : type1597 A) (y : A) : (term640 A P y) = (term675 A P y).
Proof. exact (MK_COMB (@lem293706 A P) (@lem293705 A y)). Qed.
Lemma lem293709 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem293710 {A : Type'} (f : type1597 A) (x : nat) : (f x) = (@I (nat -> A -> Prop) f x).
Proof. exact (@lem293709 nat (A -> Prop) f x). Qed.
Lemma lem293711 {A : Type'} (P : type1597 A) : (term674 A P) = (term676 A P).
Proof. exact (@lem293710 A P term672). Qed.
Lemma lem293712 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem293713 {A : Type'} (P : type1597 A) (y : A) : (term675 A P y) = (term677 A P y).
Proof. exact (MK_COMB (@lem293711 A P) (@lem293712 A y)). Qed.
Lemma lem293715 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem293716 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem293715 A Prop f x). Qed.
Lemma lem293717 {A : Type'} (P : type1597 A) (y : A) : (term677 A P y) = (term678 A P y).
Proof. exact (@lem293716 A (term676 A P) y). Qed.
Lemma lem293718 {A : Type'} (P : type1597 A) (y : A) : (term675 A P y) = (term678 A P y).
Proof. exact (TRANS (@lem293713 A P y) (@lem293717 A P y)). Qed.
Lemma lem293719 {A : Type'} (P : type1597 A) (y : A) : (term640 A P y) = (term678 A P y).
Proof. exact (TRANS (@lem293707 A P y) (@lem293718 A P y)). Qed.
Lemma lem293720 {A : Type'} (P : type1597 A) (y : A) : (term679 A P y) = (term680 A P y).
Proof. exact (MK_COMB (@lem293688) (@lem293719 A P y)). Qed.
Lemma lem293721 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem293722 {A : Type'} (P : type1597 A) (y : A) : (term681 A P y) = (term682 A P y).
Proof. exact (MK_COMB (@lem293721) (@lem293720 A P y)). Qed.
Lemma lem293723 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (y : A) : (term639 A P R f y) = (term683 A P R f y).
Proof. exact (MK_COMB (@lem293722 A P y) (@lem293687 A R f y)). Qed.
Lemma lem293724 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term648 A P R f) = (term684 A P R f).
Proof. exact (fun_ext (fun y : A => @lem293723 A P R f y)). Qed.
Lemma lem293725 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem293726 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term649 A P R f) = (term685 A P R f).
Proof. exact (MK_COMB (@lem293725 A) (@lem293724 A P R f)). Qed.
Lemma lem293727 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term440 A P R f) : term685 A P R f.
Proof. exact (EQ_MP (@lem293726 A P R f) (@lem293324 A P R f h1)). Qed.
Lemma lem293737 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem293738 {A : Type'} (f : type1596 A) (x : nat) : (f x) = (@I (nat -> A -> A) f x).
Proof. exact (@lem293737 nat (A -> A) f x). Qed.
Lemma lem293739 {A : Type'} (y : type1596 A) (n : nat) : (y n) = (@I (nat -> A -> A) y n).
Proof. exact (@lem293738 A y n). Qed.
Lemma lem293740 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem293741 {A : Type'} (y : type1596 A) (n : nat) (x : A) : (y n x) = (@I (nat -> A -> A) y n x).
Proof. exact (MK_COMB (@lem293739 A y n) (@lem293740 A x)). Qed.
Lemma lem293743 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem293744 {A : Type'} (f : A -> A) (x : A) : (f x) = (@I (A -> A) f x).
Proof. exact (@lem293743 A A f x). Qed.
Lemma lem293745 {A : Type'} (y : type1596 A) (n : nat) (x : A) : (@I (nat -> A -> A) y n x) = (term686 A y n x).
Proof. exact (@lem293744 A (@I (nat -> A -> A) y n) x). Qed.
Lemma lem293747 {A : Type'} (y : type1596 A) (n : nat) (x : A) : (y n x) = (term686 A y n x).
Proof. exact (TRANS (@lem293741 A y n x) (@lem293745 A y n x)). Qed.
Lemma lem293749 {A : Type'} (R : type1594 A) (n : nat) (x : A) : (R n x) = (R n x).
Proof. exact (eq_refl (R n x)). Qed.
Lemma lem293750 {A : Type'} (R : type1594 A) (y : type1596 A) (n : nat) (x : A) : (term687 A R y n x) = (term688 A R y n x).
Proof. exact (MK_COMB (@lem293749 A R n x) (@lem293747 A y n x)). Qed.
Lemma lem293752 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem293753 {A : Type'} (f : type1594 A) (x : nat) : (f x) = (@I (nat -> A -> A -> Prop) f x).
Proof. exact (@lem293752 nat (type1402 A) f x). Qed.
Lemma lem293754 {A : Type'} (R : type1594 A) (n : nat) : (R n) = (@I (nat -> A -> A -> Prop) R n).
Proof. exact (@lem293753 A R n). Qed.
Lemma lem293755 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem293756 {A : Type'} (R : type1594 A) (n : nat) (x : A) : (R n x) = (@I (nat -> A -> A -> Prop) R n x).
Proof. exact (MK_COMB (@lem293754 A R n) (@lem293755 A x)). Qed.
Lemma lem293758 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem293759 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem293758 A (A -> Prop) f x). Qed.
Lemma lem293760 {A : Type'} (R : type1594 A) (n : nat) (x : A) : (@I (nat -> A -> A -> Prop) R n x) = (term689 A R n x).
Proof. exact (@lem293759 A (@I (nat -> A -> A -> Prop) R n) x). Qed.
Lemma lem293761 {A : Type'} (R : type1594 A) (n : nat) (x : A) : (R n x) = (term689 A R n x).
Proof. exact (TRANS (@lem293756 A R n x) (@lem293760 A R n x)). Qed.
Lemma lem293762 {A : Type'} (y : type1596 A) (n : nat) (x : A) : (term686 A y n x) = (term686 A y n x).
Proof. exact (eq_refl (term686 A y n x)). Qed.
Lemma lem293763 {A : Type'} (R : type1594 A) (y : type1596 A) (n : nat) (x : A) : (term688 A R y n x) = (term690 A R y n x).
Proof. exact (MK_COMB (@lem293761 A R n x) (@lem293762 A y n x)). Qed.
Lemma lem293765 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem293766 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem293765 A Prop f x). Qed.
Lemma lem293767 {A : Type'} (R : type1594 A) (y : type1596 A) (n : nat) (x : A) : (term690 A R y n x) = (term691 A R y n x).
Proof. exact (@lem293766 A (term689 A R n x) (term686 A y n x)). Qed.
Lemma lem293768 {A : Type'} (R : type1594 A) (y : type1596 A) (n : nat) (x : A) : (term688 A R y n x) = (term691 A R y n x).
Proof. exact (TRANS (@lem293763 A R y n x) (@lem293767 A R y n x)). Qed.
Lemma lem293769 {A : Type'} (R : type1594 A) (y : type1596 A) (n : nat) (x : A) : (term687 A R y n x) = (term691 A R y n x).
Proof. exact (TRANS (@lem293750 A R y n x) (@lem293768 A R y n x)). Qed.
Lemma lem293770 {A : Type'} (P : type1597 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem293775 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem293776 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem293775 nat nat f x). Qed.
Lemma lem293778 (n : nat) : (S n) = (@I (nat -> nat) S n).
Proof. exact (@lem293776 S n). Qed.
Lemma lem293785 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem293786 {A : Type'} (f : type1596 A) (x : nat) : (f x) = (@I (nat -> A -> A) f x).
Proof. exact (@lem293785 nat (A -> A) f x). Qed.
Lemma lem293787 {A : Type'} (y : type1596 A) (n : nat) : (y n) = (@I (nat -> A -> A) y n).
Proof. exact (@lem293786 A y n). Qed.
Lemma lem293788 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem293789 {A : Type'} (y : type1596 A) (n : nat) (x : A) : (y n x) = (@I (nat -> A -> A) y n x).
Proof. exact (MK_COMB (@lem293787 A y n) (@lem293788 A x)). Qed.
Lemma lem293791 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem293792 {A : Type'} (f : A -> A) (x : A) : (f x) = (@I (A -> A) f x).
Proof. exact (@lem293791 A A f x). Qed.
Lemma lem293793 {A : Type'} (y : type1596 A) (n : nat) (x : A) : (@I (nat -> A -> A) y n x) = (term686 A y n x).
Proof. exact (@lem293792 A (@I (nat -> A -> A) y n) x). Qed.
Lemma lem293795 {A : Type'} (y : type1596 A) (n : nat) (x : A) : (y n x) = (term686 A y n x).
Proof. exact (TRANS (@lem293789 A y n x) (@lem293793 A y n x)). Qed.
Lemma lem293796 {A : Type'} (P : type1597 A) (n : nat) : (term380 A P n) = (term692 A P n).
Proof. exact (MK_COMB (@lem293770 A P) (@lem293778 n)). Qed.
Lemma lem293797 {A : Type'} (P : type1597 A) (y : type1596 A) (n : nat) (x : A) : (term693 A P y n x) = (term694 A P y n x).
Proof. exact (MK_COMB (@lem293796 A P n) (@lem293795 A y n x)). Qed.
Lemma lem293799 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem293800 {A : Type'} (f : type1597 A) (x : nat) : (f x) = (@I (nat -> A -> Prop) f x).
Proof. exact (@lem293799 nat (A -> Prop) f x). Qed.
Lemma lem293801 {A : Type'} (P : type1597 A) (n : nat) : (term692 A P n) = (term695 A P n).
Proof. exact (@lem293800 A P (@I (nat -> nat) S n)). Qed.
Lemma lem293802 {A : Type'} (y : type1596 A) (n : nat) (x : A) : (term686 A y n x) = (term686 A y n x).
Proof. exact (eq_refl (term686 A y n x)). Qed.
Lemma lem293803 {A : Type'} (P : type1597 A) (y : type1596 A) (n : nat) (x : A) : (term694 A P y n x) = (term696 A P y n x).
Proof. exact (MK_COMB (@lem293801 A P n) (@lem293802 A y n x)). Qed.
Lemma lem293805 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem293806 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem293805 A Prop f x). Qed.
Lemma lem293807 {A : Type'} (P : type1597 A) (y : type1596 A) (n : nat) (x : A) : (term696 A P y n x) = (term697 A P y n x).
Proof. exact (@lem293806 A (term695 A P n) (term686 A y n x)). Qed.
Lemma lem293808 {A : Type'} (P : type1597 A) (y : type1596 A) (n : nat) (x : A) : (term694 A P y n x) = (term697 A P y n x).
Proof. exact (TRANS (@lem293803 A P y n x) (@lem293807 A P y n x)). Qed.
Lemma lem293809 {A : Type'} (P : type1597 A) (y : type1596 A) (n : nat) (x : A) : (term693 A P y n x) = (term697 A P y n x).
Proof. exact (TRANS (@lem293797 A P y n x) (@lem293808 A P y n x)). Qed.
Lemma lem293810 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem293811 {A : Type'} (P : type1597 A) (y : type1596 A) (n : nat) (x : A) : (term698 A P y n x) = (term699 A P y n x).
Proof. exact (MK_COMB (@lem293810) (@lem293809 A P y n x)). Qed.
Lemma lem293812 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (n : nat) (x : A) : (term700 A P R y n x) = (term701 A P R y n x).
Proof. exact (MK_COMB (@lem293811 A P y n x) (@lem293769 A R y n x)). Qed.
Lemma lem293813 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem293820 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem293821 {A : Type'} (f : type1597 A) (x : nat) : (f x) = (@I (nat -> A -> Prop) f x).
Proof. exact (@lem293820 nat (A -> Prop) f x). Qed.
Lemma lem293822 {A : Type'} (P : type1597 A) (n : nat) : (P n) = (@I (nat -> A -> Prop) P n).
Proof. exact (@lem293821 A P n). Qed.
Lemma lem293823 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem293824 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (P n x) = (@I (nat -> A -> Prop) P n x).
Proof. exact (MK_COMB (@lem293822 A P n) (@lem293823 A x)). Qed.
Lemma lem293826 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem293827 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem293826 A Prop f x). Qed.
Lemma lem293828 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (@I (nat -> A -> Prop) P n x) = (term702 A P n x).
Proof. exact (@lem293827 A (@I (nat -> A -> Prop) P n) x). Qed.
Lemma lem293830 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (P n x) = (term702 A P n x).
Proof. exact (TRANS (@lem293824 A P n x) (@lem293828 A P n x)). Qed.
Lemma lem293831 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (term577 A P n x) = (term703 A P n x).
Proof. exact (MK_COMB (@lem293813) (@lem293830 A P n x)). Qed.
Lemma lem293832 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem293833 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (term569 A P n x) = (term704 A P n x).
Proof. exact (MK_COMB (@lem293832) (@lem293831 A P n x)). Qed.
Lemma lem293834 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (n : nat) (x : A) : (term705 A P R y n x) = (term706 A P R y n x).
Proof. exact (MK_COMB (@lem293833 A P n x) (@lem293812 A P R y n x)). Qed.
Lemma lem293835 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (n : nat) : (term707 A P R y n) = (term708 A P R y n).
Proof. exact (fun_ext (fun x : A => @lem293834 A P R y n x)). Qed.
Lemma lem293836 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem293837 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (n : nat) : (term630 A P R y n) = (term709 A P R y n).
Proof. exact (MK_COMB (@lem293836 A) (@lem293835 A P R y n)). Qed.
Lemma lem293838 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) : (term632 A P R y) = (term710 A P R y).
Proof. exact (fun_ext (fun n : nat => @lem293837 A P R y n)). Qed.
Lemma lem293839 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem293840 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) : (term634 A P R y) = (term711 A P R y).
Proof. exact (MK_COMB (@lem293839) (@lem293838 A P R y)). Qed.
Lemma lem293841 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (h1 : term634 A P R y) : term711 A P R y.
Proof. exact (EQ_MP (@lem293840 A P R y) (@lem293325 A P R y h1)). Qed.
Lemma lem293940 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (y : A) : (term683 A P R f y) = (term683 A P R f y).
Proof. exact (eq_refl (term683 A P R f y)). Qed.
Lemma lem293941 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term684 A P R f) = (term684 A P R f).
Proof. exact (fun_ext (fun y : A => @lem293940 A P R f y)). Qed.
Lemma lem293942 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem293944 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term685 A P R f) = (term685 A P R f).
Proof. exact (MK_COMB (@lem293942 A) (@lem293941 A P R f)). Qed.
Lemma lem293945 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term440 A P R f) : term685 A P R f.
Proof. exact (EQ_MP (@lem293944 A P R f) (@lem293727 A P R f h1)). Qed.
Lemma lem293963 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (n : nat) (x : A) : (term706 A P R y n x) = (term712 A P R y n x).
Proof. exact (@lem19490 (term697 A P y n x) (term703 A P n x) (term691 A R y n x)). Qed.
Lemma lem293964 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (n : nat) : (term708 A P R y n) = (term713 A P R y n).
Proof. exact (fun_ext (fun x : A => @lem293963 A P R y n x)). Qed.
Lemma lem293965 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem293966 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (n : nat) : (term709 A P R y n) = (term714 A P R y n).
Proof. exact (MK_COMB (@lem293965 A) (@lem293964 A P R y n)). Qed.
Lemma lem293967 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) : (term710 A P R y) = (term715 A P R y).
Proof. exact (fun_ext (fun n : nat => @lem293966 A P R y n)). Qed.
Lemma lem293968 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem293970 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) : (term711 A P R y) = (term716 A P R y).
Proof. exact (MK_COMB (@lem293968) (@lem293967 A P R y)). Qed.
Lemma lem293971 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (h1 : term634 A P R y) : term716 A P R y.
Proof. exact (EQ_MP (@lem293970 A P R y) (@lem293841 A P R y h1)). Qed.
Lemma lem293990 {A : Type'} (_6547 : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term440 A P R f) : term717 A P R f _6547.
Proof. exact (@lem293945 A P R f h1 _6547). Qed.
Lemma lem293991 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6547 : A) : (term717 A P R f _6547) = (term683 A P R f _6547).
Proof. exact (eq_refl (term717 A P R f _6547)). Qed.
Lemma lem293993 {A : Type'} (_6548 : nat) (P : type1597 A) (R : type1594 A) (y : type1596 A) (h1 : term634 A P R y) : term718 A P R y _6548.
Proof. exact (@lem293971 A P R y h1 _6548). Qed.
Lemma lem293994 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (_6548 : nat) : (term718 A P R y _6548) = (term714 A P R y _6548).
Proof. exact (eq_refl (term718 A P R y _6548)). Qed.
Lemma lem293995 {A : Type'} (_6548 : nat) (P : type1597 A) (R : type1594 A) (y : type1596 A) (h1 : term634 A P R y) : term714 A P R y _6548.
Proof. exact (EQ_MP (@lem293994 A P R y _6548) (@lem293993 A _6548 P R y h1)). Qed.
Lemma lem293996 {A : Type'} (_6548 : nat) (_6549 : A) (P : type1597 A) (R : type1594 A) (y : type1596 A) (h1 : term634 A P R y) : term719 A P R y _6548 _6549.
Proof. exact (@lem293995 A _6548 P R y h1 _6549). Qed.
Lemma lem293997 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (_6548 : nat) (_6549 : A) : (term719 A P R y _6548 _6549) = (term712 A P R y _6548 _6549).
Proof. exact (eq_refl (term719 A P R y _6548 _6549)). Qed.
Lemma lem293998 {A : Type'} (_6548 : nat) (_6549 : A) (P : type1597 A) (R : type1594 A) (y : type1596 A) (h1 : term634 A P R y) : term712 A P R y _6548 _6549.
Proof. exact (EQ_MP (@lem293997 A P R y _6548 _6549) (@lem293996 A _6548 _6549 P R y h1)). Qed.
Lemma lem294004 {A : Type'} (P : type1597 A) (a : A) (h1 : term313 A P a) : term654 A P a.
Proof. exact (EQ_MP (@lem293560 A P a) (@lem293023 A P a h1)). Qed.
Lemma lem294006 {A : Type'} (f : nat -> A) (a : A) (h1 : (term286 A f) = a) : (term656 A f) = a.
Proof. exact (EQ_MP (@lem293580 A f a) (@lem293241 A f a h1)). Qed.
Lemma lem294051 {A : Type'} (f : nat -> A) (a : A) (h1 : (term286 A f) = a) : a = (term656 A f).
Proof. exact (SYM (@lem294006 A f a h1)). Qed.
Lemma lem294066 {A : Type'} (P : type1597 A) : (term720 A P) = (term720 A P).
Proof. exact (eq_refl (term720 A P)). Qed.
Lemma lem294067 {A : Type'} (P : type1597 A) (f : nat -> A) (a : A) (h1 : (term286 A f) = a) : (term721 A P a) = (term722 A P f).
Proof. exact (MK_COMB (@lem294066 A P) (@lem294051 A f a h1)). Qed.
Lemma lem294068 {A : Type'} (P : type1597 A) (f : nat -> A) : (term722 A P f) = (term723 A P f).
Proof. exact (eq_refl (term722 A P f)). Qed.
Lemma lem294069 {A : Type'} (P : type1597 A) (a : A) : (term724 A P a) = (term724 A P a).
Proof. exact (eq_refl (term724 A P a)). Qed.
Lemma lem294070 {A : Type'} (a : A) (P : type1597 A) (f : nat -> A) : ((term721 A P a) = (term722 A P f)) = ((term721 A P a) = (term723 A P f)).
Proof. exact (MK_COMB (@lem294069 A P a) (@lem294068 A P f)). Qed.
Lemma lem294071 {A : Type'} (P : type1597 A) (a : A) : (term721 A P a) = (term654 A P a).
Proof. exact (eq_refl (term721 A P a)). Qed.
Lemma lem294072 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem294073 {A : Type'} (P : type1597 A) (a : A) : (term724 A P a) = (term725 A P a).
Proof. exact (MK_COMB (@lem294072) (@lem294071 A P a)). Qed.
Lemma lem294074 {A : Type'} (P : type1597 A) (f : nat -> A) : (term723 A P f) = (term723 A P f).
Proof. exact (eq_refl (term723 A P f)). Qed.
Lemma lem294075 {A : Type'} (a : A) (P : type1597 A) (f : nat -> A) : ((term721 A P a) = (term723 A P f)) = ((term654 A P a) = (term723 A P f)).
Proof. exact (MK_COMB (@lem294073 A P a) (@lem294074 A P f)). Qed.
Lemma lem294076 {A : Type'} (a : A) (P : type1597 A) (f : nat -> A) : ((term721 A P a) = (term722 A P f)) = ((term654 A P a) = (term723 A P f)).
Proof. exact (TRANS (@lem294070 A a P f) (@lem294075 A a P f)). Qed.
Lemma lem294077 {A : Type'} (P : type1597 A) (f : nat -> A) (a : A) (h1 : (term286 A f) = a) : (term654 A P a) = (term723 A P f).
Proof. exact (EQ_MP (@lem294076 A a P f) (@lem294067 A P f a h1)). Qed.
Lemma lem294106 {A : Type'} (_6547 : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term440 A P R f) : term683 A P R f _6547.
Proof. exact (EQ_MP (@lem293991 A P R f _6547) (@lem293990 A _6547 P R f h1)). Qed.
Lemma lem294120 {A : Type'} (_6548 : nat) (_6549 : A) (P : type1597 A) (R : type1594 A) (y : type1596 A) (h1 : term634 A P R y) : term726 A P y _6548 _6549.
Proof. exact (proj1 (@lem293998 A _6548 _6549 P R y h1)). Qed.
Lemma lem294134 {A : Type'} (_6548 : nat) (_6549 : A) (P : type1597 A) (R : type1594 A) (y : type1596 A) (h1 : term634 A P R y) : term727 A P R y _6548 _6549.
Proof. exact (proj2 (@lem293998 A _6548 _6549 P R y h1)). Qed.
Lemma lem294359 {A : Type'} (f : nat -> A) (P : type1597 A) (a : A) (h1 : (term286 A f) = a) (h2 : term313 A P a) : term723 A P f.
Proof. exact (EQ_MP (@lem294077 A P f a h1) (@lem294004 A P a h2)). Qed.
Lemma lem294360 {A : Type'} (f : nat -> A) (P : type1597 A) (a : A) (h1 : (term286 A f) = a) (h2 : term313 A P a) : term728 A P f.
Proof. exact (fun h0 : term729 A P f => @lem294359 A f P a h1 h2). Qed.
Lemma lem294362 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem294363 {A : Type'} (P : type1597 A) (f : nat -> A) : (term728 A P f) = (term723 A P f).
Proof. exact (@lem294362 (term723 A P f)). Qed.
Lemma lem294364 {A : Type'} (f : nat -> A) (P : type1597 A) (a : A) (h1 : (term286 A f) = a) (h2 : term313 A P a) : term723 A P f.
Proof. exact (EQ_MP (@lem294363 A P f) (@lem294360 A f P a h1 h2)). Qed.
Lemma lem294370 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem294371 {A : Type'} (y : type1596 A) (P : type1597 A) (_6548 : nat) (_6549 : A) : (term726 A P y _6548 _6549) = (term730 A y P _6548 _6549).
Proof. exact (@lem294370 (term697 A P y _6548 _6549) (term703 A P _6548 _6549)). Qed.
Lemma lem294377 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem294378 {A : Type'} (y : type1596 A) (P : type1597 A) (_6548 : nat) (_6549 : A) : (term731 A P y _6548 _6549) = (term732 A y P _6548 _6549).
Proof. exact (MK_COMB (@lem294377) (@lem294371 A y P _6548 _6549)). Qed.
Lemma lem294384 {A : Type'} (y : type1596 A) (P : type1597 A) (_6548 : nat) (_6549 : A) : (term730 A y P _6548 _6549) = (term730 A y P _6548 _6549).
Proof. exact (eq_refl (term730 A y P _6548 _6549)). Qed.
Lemma lem294385 {A : Type'} (y : type1596 A) (P : type1597 A) (_6548 : nat) (_6549 : A) : ((term726 A P y _6548 _6549) = (term730 A y P _6548 _6549)) = ((term730 A y P _6548 _6549) = (term730 A y P _6548 _6549)).
Proof. exact (MK_COMB (@lem294378 A y P _6548 _6549) (@lem294384 A y P _6548 _6549)). Qed.
Lemma lem294387 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem294388 (x : Prop) : (x = x) = True.
Proof. exact (@lem294387 Prop x). Qed.
Lemma lem294389 {A : Type'} (y : type1596 A) (P : type1597 A) (_6548 : nat) (_6549 : A) : ((term730 A y P _6548 _6549) = (term730 A y P _6548 _6549)) = True.
Proof. exact (@lem294388 (term730 A y P _6548 _6549)). Qed.
Lemma lem294390 {A : Type'} (y : type1596 A) (P : type1597 A) (_6548 : nat) (_6549 : A) : ((term726 A P y _6548 _6549) = (term730 A y P _6548 _6549)) = True.
Proof. exact (TRANS (@lem294385 A y P _6548 _6549) (@lem294389 A y P _6548 _6549)). Qed.
Lemma lem294391 {A : Type'} (y : type1596 A) (P : type1597 A) (_6548 : nat) (_6549 : A) : True = ((term726 A P y _6548 _6549) = (term730 A y P _6548 _6549)).
Proof. exact (SYM (@lem294390 A y P _6548 _6549)). Qed.
Lemma lem294392 {A : Type'} (y : type1596 A) (P : type1597 A) (_6548 : nat) (_6549 : A) : (term726 A P y _6548 _6549) = (term730 A y P _6548 _6549).
Proof. exact (EQ_MP (@lem294391 A y P _6548 _6549) (@lem0)). Qed.
Lemma lem294393 {A : Type'} (_6548 : nat) (_6549 : A) (P : type1597 A) (R : type1594 A) (y : type1596 A) (h1 : term634 A P R y) : term730 A y P _6548 _6549.
Proof. exact (EQ_MP (@lem294392 A y P _6548 _6549) (@lem294120 A _6548 _6549 P R y h1)). Qed.
Lemma lem294395 (b : Prop) (a : Prop) : (a \/ b) = (term203 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem294396 {A : Type'} (P : type1597 A) (y : type1596 A) (_6548 : nat) (_6549 : A) : (term730 A y P _6548 _6549) = (term733 A P y _6548 _6549).
Proof. exact (@lem294395 (term703 A P _6548 _6549) (term697 A P y _6548 _6549)). Qed.
Lemma lem294398 (a : Prop) : (term210 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem294399 {A : Type'} (P : type1597 A) (_6548 : nat) (_6549 : A) : (term734 A P _6548 _6549) = (term702 A P _6548 _6549).
Proof. exact (@lem294398 (term702 A P _6548 _6549)). Qed.
Lemma lem294400 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem294401 {A : Type'} (P : type1597 A) (_6548 : nat) (_6549 : A) : (term735 A P _6548 _6549) = (term736 A P _6548 _6549).
Proof. exact (MK_COMB (@lem294400) (@lem294399 A P _6548 _6549)). Qed.
Lemma lem294402 {A : Type'} (P : type1597 A) (y : type1596 A) (_6548 : nat) (_6549 : A) : (term697 A P y _6548 _6549) = (term697 A P y _6548 _6549).
Proof. exact (eq_refl (term697 A P y _6548 _6549)). Qed.
Lemma lem294403 {A : Type'} (P : type1597 A) (y : type1596 A) (_6548 : nat) (_6549 : A) : (term733 A P y _6548 _6549) = (term737 A P y _6548 _6549).
Proof. exact (MK_COMB (@lem294401 A P _6548 _6549) (@lem294402 A P y _6548 _6549)). Qed.
Lemma lem294404 {A : Type'} (P : type1597 A) (y : type1596 A) (_6548 : nat) (_6549 : A) : (term730 A y P _6548 _6549) = (term737 A P y _6548 _6549).
Proof. exact (TRANS (@lem294396 A P y _6548 _6549) (@lem294403 A P y _6548 _6549)). Qed.
Lemma lem294407 {A : Type'} (_6548 : nat) (_6549 : A) (P : type1597 A) (R : type1594 A) (y : type1596 A) (h1 : term634 A P R y) : term737 A P y _6548 _6549.
Proof. exact (EQ_MP (@lem294404 A P y _6548 _6549) (@lem294393 A _6548 _6549 P R y h1)). Qed.
Lemma lem294408 {A : Type'} (_6548 : nat) (_6549 : A) (P : type1597 A) (R : type1594 A) (y : type1596 A) (h1 : term634 A P R y) : term737 A P y _6548 _6549.
Proof. exact (@lem294407 A _6548 _6549 P R y h1). Qed.
Lemma lem294409 {A : Type'} (f : nat -> A) (P : type1597 A) (R : type1594 A) (y : type1596 A) (h1 : term634 A P R y) : term738 A P y f.
Proof. exact (@lem294408 A (@I (nat -> nat) NUMERAL 0) (term656 A f) P R y h1). Qed.
Lemma lem294412 {A : Type'} (R : type1594 A) (y : type1596 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term634 A P R y) (h2 : (term286 A f) = a) (h3 : term313 A P a) : term739 A P y f.
Proof. exact (@lem294409 A f P R y h1 (@lem294364 A f P a h2 h3)). Qed.
Lemma lem294413 {A : Type'} (R : type1594 A) (y : type1596 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term634 A P R y) (h2 : (term286 A f) = a) (h3 : term313 A P a) : term740 A P y f.
Proof. exact (fun h0 : term741 A P y f => @lem294412 A R y f P a h1 h2 h3). Qed.
Lemma lem294415 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem294416 {A : Type'} (P : type1597 A) (y : type1596 A) (f : nat -> A) : (term740 A P y f) = (term739 A P y f).
Proof. exact (@lem294415 (term739 A P y f)). Qed.
Lemma lem294417 {A : Type'} (R : type1594 A) (y : type1596 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term634 A P R y) (h2 : (term286 A f) = a) (h3 : term313 A P a) : term739 A P y f.
Proof. exact (EQ_MP (@lem294416 A P y f) (@lem294413 A R y f P a h1 h2 h3)). Qed.
Lemma lem294419 {A : Type'} (f : nat -> A) (P : type1597 A) (a : A) (h1 : (term286 A f) = a) (h2 : term313 A P a) : term723 A P f.
Proof. exact (EQ_MP (@lem294077 A P f a h1) (@lem294004 A P a h2)). Qed.
Lemma lem294420 {A : Type'} (f : nat -> A) (P : type1597 A) (a : A) (h1 : (term286 A f) = a) (h2 : term313 A P a) : term728 A P f.
Proof. exact (fun h0 : term729 A P f => @lem294419 A f P a h1 h2). Qed.
Lemma lem294422 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem294423 {A : Type'} (P : type1597 A) (f : nat -> A) : (term728 A P f) = (term723 A P f).
Proof. exact (@lem294422 (term723 A P f)). Qed.
Lemma lem294424 {A : Type'} (f : nat -> A) (P : type1597 A) (a : A) (h1 : (term286 A f) = a) (h2 : term313 A P a) : term723 A P f.
Proof. exact (EQ_MP (@lem294423 A P f) (@lem294420 A f P a h1 h2)). Qed.
Lemma lem294430 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem294431 {A : Type'} (R : type1594 A) (y : type1596 A) (P : type1597 A) (_6548 : nat) (_6549 : A) : (term727 A P R y _6548 _6549) = (term742 A R y P _6548 _6549).
Proof. exact (@lem294430 (term691 A R y _6548 _6549) (term703 A P _6548 _6549)). Qed.
Lemma lem294437 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem294438 {A : Type'} (R : type1594 A) (y : type1596 A) (P : type1597 A) (_6548 : nat) (_6549 : A) : (term743 A P R y _6548 _6549) = (term744 A R y P _6548 _6549).
Proof. exact (MK_COMB (@lem294437) (@lem294431 A R y P _6548 _6549)). Qed.
Lemma lem294444 {A : Type'} (R : type1594 A) (y : type1596 A) (P : type1597 A) (_6548 : nat) (_6549 : A) : (term742 A R y P _6548 _6549) = (term742 A R y P _6548 _6549).
Proof. exact (eq_refl (term742 A R y P _6548 _6549)). Qed.
Lemma lem294445 {A : Type'} (R : type1594 A) (y : type1596 A) (P : type1597 A) (_6548 : nat) (_6549 : A) : ((term727 A P R y _6548 _6549) = (term742 A R y P _6548 _6549)) = ((term742 A R y P _6548 _6549) = (term742 A R y P _6548 _6549)).
Proof. exact (MK_COMB (@lem294438 A R y P _6548 _6549) (@lem294444 A R y P _6548 _6549)). Qed.
Lemma lem294447 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem294448 (x : Prop) : (x = x) = True.
Proof. exact (@lem294447 Prop x). Qed.
Lemma lem294449 {A : Type'} (R : type1594 A) (y : type1596 A) (P : type1597 A) (_6548 : nat) (_6549 : A) : ((term742 A R y P _6548 _6549) = (term742 A R y P _6548 _6549)) = True.
Proof. exact (@lem294448 (term742 A R y P _6548 _6549)). Qed.
Lemma lem294450 {A : Type'} (R : type1594 A) (y : type1596 A) (P : type1597 A) (_6548 : nat) (_6549 : A) : ((term727 A P R y _6548 _6549) = (term742 A R y P _6548 _6549)) = True.
Proof. exact (TRANS (@lem294445 A R y P _6548 _6549) (@lem294449 A R y P _6548 _6549)). Qed.
Lemma lem294451 {A : Type'} (R : type1594 A) (y : type1596 A) (P : type1597 A) (_6548 : nat) (_6549 : A) : True = ((term727 A P R y _6548 _6549) = (term742 A R y P _6548 _6549)).
Proof. exact (SYM (@lem294450 A R y P _6548 _6549)). Qed.
Lemma lem294452 {A : Type'} (R : type1594 A) (y : type1596 A) (P : type1597 A) (_6548 : nat) (_6549 : A) : (term727 A P R y _6548 _6549) = (term742 A R y P _6548 _6549).
Proof. exact (EQ_MP (@lem294451 A R y P _6548 _6549) (@lem0)). Qed.
Lemma lem294453 {A : Type'} (_6548 : nat) (_6549 : A) (P : type1597 A) (R : type1594 A) (y : type1596 A) (h1 : term634 A P R y) : term742 A R y P _6548 _6549.
Proof. exact (EQ_MP (@lem294452 A R y P _6548 _6549) (@lem294134 A _6548 _6549 P R y h1)). Qed.
Lemma lem294455 (b : Prop) (a : Prop) : (a \/ b) = (term203 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem294456 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (_6548 : nat) (_6549 : A) : (term742 A R y P _6548 _6549) = (term745 A P R y _6548 _6549).
Proof. exact (@lem294455 (term703 A P _6548 _6549) (term691 A R y _6548 _6549)). Qed.
Lemma lem294458 (a : Prop) : (term210 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem294459 {A : Type'} (P : type1597 A) (_6548 : nat) (_6549 : A) : (term734 A P _6548 _6549) = (term702 A P _6548 _6549).
Proof. exact (@lem294458 (term702 A P _6548 _6549)). Qed.
Lemma lem294460 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem294461 {A : Type'} (P : type1597 A) (_6548 : nat) (_6549 : A) : (term735 A P _6548 _6549) = (term736 A P _6548 _6549).
Proof. exact (MK_COMB (@lem294460) (@lem294459 A P _6548 _6549)). Qed.
Lemma lem294462 {A : Type'} (R : type1594 A) (y : type1596 A) (_6548 : nat) (_6549 : A) : (term691 A R y _6548 _6549) = (term691 A R y _6548 _6549).
Proof. exact (eq_refl (term691 A R y _6548 _6549)). Qed.
Lemma lem294463 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (_6548 : nat) (_6549 : A) : (term745 A P R y _6548 _6549) = (term746 A P R y _6548 _6549).
Proof. exact (MK_COMB (@lem294461 A P _6548 _6549) (@lem294462 A R y _6548 _6549)). Qed.
Lemma lem294464 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (_6548 : nat) (_6549 : A) : (term742 A R y P _6548 _6549) = (term746 A P R y _6548 _6549).
Proof. exact (TRANS (@lem294456 A P R y _6548 _6549) (@lem294463 A P R y _6548 _6549)). Qed.
Lemma lem294467 {A : Type'} (_6548 : nat) (_6549 : A) (P : type1597 A) (R : type1594 A) (y : type1596 A) (h1 : term634 A P R y) : term746 A P R y _6548 _6549.
Proof. exact (EQ_MP (@lem294464 A P R y _6548 _6549) (@lem294453 A _6548 _6549 P R y h1)). Qed.
Lemma lem294468 {A : Type'} (_6548 : nat) (_6549 : A) (P : type1597 A) (R : type1594 A) (y : type1596 A) (h1 : term634 A P R y) : term746 A P R y _6548 _6549.
Proof. exact (@lem294467 A _6548 _6549 P R y h1). Qed.
Lemma lem294469 {A : Type'} (f : nat -> A) (P : type1597 A) (R : type1594 A) (y : type1596 A) (h1 : term634 A P R y) : term747 A P R y f.
Proof. exact (@lem294468 A (@I (nat -> nat) NUMERAL 0) (term656 A f) P R y h1). Qed.
Lemma lem294472 {A : Type'} (R : type1594 A) (y : type1596 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term634 A P R y) (h2 : (term286 A f) = a) (h3 : term313 A P a) : term748 A R y f.
Proof. exact (@lem294469 A f P R y h1 (@lem294424 A f P a h2 h3)). Qed.
Lemma lem294473 {A : Type'} (R : type1594 A) (y : type1596 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term634 A P R y) (h2 : (term286 A f) = a) (h3 : term313 A P a) : term749 A R y f.
Proof. exact (fun h0 : term750 A R y f => @lem294472 A R y f P a h1 h2 h3). Qed.
Lemma lem294475 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem294476 {A : Type'} (R : type1594 A) (y : type1596 A) (f : nat -> A) : (term749 A R y f) = (term748 A R y f).
Proof. exact (@lem294475 (term748 A R y f)). Qed.
Lemma lem294477 {A : Type'} (R : type1594 A) (y : type1596 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term634 A P R y) (h2 : (term286 A f) = a) (h3 : term313 A P a) : term748 A R y f.
Proof. exact (EQ_MP (@lem294476 A R y f) (@lem294473 A R y f P a h1 h2 h3)). Qed.
Lemma lem294479 (a : Prop) (b : Prop) : (term751 a b) = (term752 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem294480 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6547 : A) : (term683 A P R f _6547) = (term753 A P R f _6547).
Proof. exact (@lem294479 (term678 A P _6547) (term667 A R f _6547)). Qed.
Lemma lem294482 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem294483 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6547 : A) : (term753 A P R f _6547) = (term754 A P R f _6547).
Proof. exact (@lem294482 (term755 A P R f _6547)). Qed.
Lemma lem294484 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6547 : A) : (term683 A P R f _6547) = (term754 A P R f _6547).
Proof. exact (TRANS (@lem294480 A P R f _6547) (@lem294483 A P R f _6547)). Qed.
Lemma lem294486 {A : Type'} (R : type1594 A) (y : type1596 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term634 A P R y) (h2 : (term286 A f) = a) (h3 : term313 A P a) : term756 A P R y f.
Proof. exact (conj (@lem294417 A R y f P a h1 h2 h3) (@lem294477 A R y f P a h1 h2 h3)). Qed.
Lemma lem294488 {A : Type'} (_6547 : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term440 A P R f) : term754 A P R f _6547.
Proof. exact (EQ_MP (@lem294484 A P R f _6547) (@lem294106 A _6547 P R f h1)). Qed.
Lemma lem294489 {A : Type'} (_6547 : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term440 A P R f) : term754 A P R f _6547.
Proof. exact (@lem294488 A _6547 P R f h1). Qed.
Lemma lem294490 {A : Type'} (y : type1596 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term440 A P R f) : term757 A P R y f.
Proof. exact (@lem294489 A (term758 A y f) P R f h1). Qed.
Lemma lem294493 {A : Type'} (y : type1596 A) (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term634 A P R y) (h2 : term440 A P R f) (h3 : (term286 A f) = a) (h4 : term313 A P a) : False.
Proof. exact (@lem294490 A y P R f h2 (@lem294486 A R y f P a h1 h3 h4)). Qed.
Lemma lem294494 {A : Type'} (y : type1596 A) (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term634 A P R y) (h2 : term440 A P R f) (h3 : (term286 A f) = a) (h4 : term313 A P a) : term189.
Proof. exact (fun h0 : ~ False => @lem294493 A y R f P a h1 h2 h3 h4). Qed.
Lemma lem294496 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem294497 : term189 = False.
Proof. exact (@lem294496 False). Qed.
Lemma lem294499 {A : Type'} (y : type1596 A) (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term634 A P R y) (h2 : term440 A P R f) (h3 : (term286 A f) = a) (h4 : term313 A P a) : False.
Proof. exact (EQ_MP (@lem294497) (@lem294494 A y R f P a h1 h2 h3 h4)). Qed.
Lemma lem294500 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term440 A P R f) (h3 : (term286 A f) = a) (h4 : term313 A P a) : False.
Proof. exact (ex_elim (@lem293235 A P R h1) (fun y : type1596 A => fun h0 : term636 A P R y => @lem294499 A y R f P a h0 h2 h3 h4)). Qed.
Lemma lem294501 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term440 A P R f) (h3 : (term286 A f) = a) (h4 : term313 A P a) : ((term286 A f) = a) = False.
Proof. exact (prop_ext (fun h5 : (term286 A f) = a => @lem294500 A R f P a h1 h2 h3 h4) (fun h5 : False => @lem293241 A f a h3)). Qed.
Lemma lem294502 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term440 A P R f) (h3 : (term286 A f) = a) (h4 : term313 A P a) : False.
Proof. exact (EQ_MP (@lem294501 A R f P a h1 h2 h3 h4) (@lem293241 A f a h3)). Qed.
Lemma lem294503 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term440 A P R f) (h3 : (term286 A f) = a) (h4 : term313 A P a) : (term313 A P a) = False.
Proof. exact (prop_ext (fun h5 : term313 A P a => @lem294502 A R f P a h1 h2 h3 h4) (fun h5 : False => @lem293023 A P a h4)). Qed.
Lemma lem294504 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term440 A P R f) (h3 : (term286 A f) = a) (h4 : term313 A P a) : False.
Proof. exact (EQ_MP (@lem294503 A R f P a h1 h2 h3 h4) (@lem293023 A P a h4)). Qed.
Lemma lem294505 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term440 A P R f) (h3 : (term286 A f) = a) (h4 : term313 A P a) : (term440 A P R f) = False.
Proof. exact (prop_ext (fun h5 : term440 A P R f => @lem294504 A R f P a h1 h2 h3 h4) (fun h5 : False => @lem292801 A P R f h2)). Qed.
Lemma lem294506 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term440 A P R f) (h3 : (term286 A f) = a) (h4 : term313 A P a) : False.
Proof. exact (EQ_MP (@lem294505 A R f P a h1 h2 h3 h4) (@lem292801 A P R f h2)). Qed.
Lemma lem294507 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : (term286 A f) = a) (h3 : term313 A P a) : term443 A P R f.
Proof. exact (fun h0 : term440 A P R f => @lem294506 A R f P a h1 h0 h2 h3). Qed.
Lemma lem294508 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : (term286 A f) = a) (h3 : term313 A P a) : term439 A P R f.
Proof. exact (EQ_MP (@lem292800 A P R f) (@lem294507 A R f P a h1 h2 h3)). Qed.
Lemma lem294509 {A : Type'} (_6540 : type943 A) (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : (term286 A f) = a) (h3 : term313 A P a) : term535 A _6540 P R f.
Proof. exact (fun h0 : term515 A _6540 P R f => @lem294508 A R f P a h1 h2 h3). Qed.
Lemma lem294510 {A : Type'} (_6540 : type943 A) (f : nat -> A) (R : type1594 A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term313 A P a) : term536 A a _6540 P R f.
Proof. exact (fun h0 : (term286 A f) = a => @lem294509 A _6540 R f P a h1 h0 h2). Qed.
Lemma lem294511 {A : Type'} (_6540 : type943 A) (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term313 A P a) : term537 A a _6540 P R f.
Proof. exact (fun h0 : term312 A P R => @lem294510 A _6540 f R P a h0 h1). Qed.
Lemma lem294512 {A : Type'} (a : A) (_6540 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : term538 A a _6540 P R f.
Proof. exact (fun h0 : term313 A P a => @lem294511 A _6540 R f P a h0). Qed.
Lemma lem294513 {A : Type'} (a : A) (_6540 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : term539 A a _6540 P R f.
Proof. exact (fun h0 : term511 A _6540 => @lem294512 A a _6540 P R f). Qed.
Lemma lem294518 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : term542 A a P R f.
Proof. exact (fun _6540 : type943 A => @lem294513 A a _6540 P R f). Qed.
Lemma lem294523 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : term546 A P R f.
Proof. exact (fun a : A => @lem294518 A a P R f). Qed.
Lemma lem294528 {A : Type'} (R : type1594 A) (f : nat -> A) : term550 A R f.
Proof. exact (fun P : type1597 A => @lem294523 A P R f). Qed.
Lemma lem294533 {A : Type'} (f : nat -> A) : term554 A f.
Proof. exact (fun R : type1594 A => @lem294528 A R f). Qed.
Lemma lem294538 {A : Type'} : term558 A.
Proof. exact (fun f : nat -> A => @lem294533 A f). Qed.
Lemma lem294539 {A : Type'} : term557 A.
Proof. exact (EQ_MP (@lem292791 A) (@lem294538 A)). Qed.
Lemma lem294540 {A : Type'} (f : nat -> A) : term759 A f.
Proof. exact (@lem294539 A f). Qed.
Lemma lem294541 {A : Type'} (f : nat -> A) : (term759 A f) = (term553 A f).
Proof. exact (eq_refl (term759 A f)). Qed.
Lemma lem294542 {A : Type'} (f : nat -> A) : term553 A f.
Proof. exact (EQ_MP (@lem294541 A f) (@lem294540 A f)). Qed.
Lemma lem294543 {A : Type'} (f : nat -> A) (R : type1594 A) : term760 A f R.
Proof. exact (@lem294542 A f R). Qed.
Lemma lem294544 {A : Type'} (R : type1594 A) (f : nat -> A) : (term760 A f R) = (term549 A R f).
Proof. exact (eq_refl (term760 A f R)). Qed.
Lemma lem294545 {A : Type'} (R : type1594 A) (f : nat -> A) : term549 A R f.
Proof. exact (EQ_MP (@lem294544 A R f) (@lem294543 A f R)). Qed.
Lemma lem294546 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) : term761 A R f P.
Proof. exact (@lem294545 A R f P). Qed.
Lemma lem294547 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term761 A R f P) = (term545 A P R f).
Proof. exact (eq_refl (term761 A R f P)). Qed.
Lemma lem294548 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : term545 A P R f.
Proof. exact (EQ_MP (@lem294547 A P R f) (@lem294546 A R f P)). Qed.
Lemma lem294549 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (a : A) : term762 A P R f a.
Proof. exact (@lem294548 A P R f a). Qed.
Lemma lem294550 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term762 A P R f a) = (term522 A a P R f).
Proof. exact (eq_refl (term762 A P R f a)). Qed.
Lemma lem294551 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : term522 A a P R f.
Proof. exact (EQ_MP (@lem294550 A a P R f) (@lem294549 A P R f a)). Qed.
Lemma lem294552 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : term455 A a P R f.
Proof. exact (@lem292349 A a P R f (@lem294551 A a P R f)). Qed.
Lemma lem294553 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : term454 A a P R f.
Proof. exact (EQ_MP (@lem292207 A a P R f) (@lem294552 A a P R f)). Qed.
Lemma lem294554 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term313 A P a) : term451 A a P R f.
Proof. exact (@lem294553 A a P R f (@lem291893 A P a h1)). Qed.
Lemma lem294555 {A : Type'} (f : nat -> A) (R : type1594 A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term313 A P a) : term448 A a P R f.
Proof. exact (@lem294554 A R f P a h2 (@lem291892 A P R h1)). Qed.
Lemma lem294556 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : (term286 A f) = a) (h3 : term313 A P a) : term445 A P R f.
Proof. exact (@lem294555 A f R P a h1 h3 (@lem291923 A f a h2)). Qed.
Lemma lem294557 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term287 A P R f) (h3 : (term286 A f) = a) (h4 : term313 A P a) : term431 A P R f.
Proof. exact (@lem294556 A R f P a h1 h3 h4 (@lem291922 A P R f h2)). Qed.
Lemma lem294558 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term287 A P R f) (h3 : term432 A P R f) (h4 : (term286 A f) = a) (h5 : term313 A P a) : False.
Proof. exact (@lem294557 A R f P a h1 h2 h4 h5 (@lem292160 A P R f h3)). Qed.
Lemma lem294559 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term287 A P R f) (h3 : term432 A P R f) (h4 : (term286 A f) = a) (h5 : term313 A P a) : (term432 A P R f) = False.
Proof. exact (prop_ext (fun h6 : term432 A P R f => @lem294558 A R f P a h1 h2 h3 h4 h5) (fun h6 : False => @lem292160 A P R f h3)). Qed.
Lemma lem294560 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term287 A P R f) (h3 : term432 A P R f) (h4 : (term286 A f) = a) (h5 : term313 A P a) : False.
Proof. exact (EQ_MP (@lem294559 A R f P a h1 h2 h3 h4 h5) (@lem292160 A P R f h3)). Qed.
Lemma lem294561 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term287 A P R f) (h3 : (term286 A f) = a) (h4 : term313 A P a) : term431 A P R f.
Proof. exact (fun h0 : term432 A P R f => @lem294560 A R f P a h1 h2 h0 h3 h4). Qed.
Lemma lem294562 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term287 A P R f) (h3 : (term286 A f) = a) (h4 : term313 A P a) : term410 A P R f.
Proof. exact (EQ_MP (@lem292159 A P R f) (@lem294561 A R f P a h1 h2 h3 h4)). Qed.
Lemma lem294564 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem294565 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term417 A P R f n) = (term763 A P R f n).
Proof. exact (@lem294564 (term417 A P R f n)). Qed.
Lemma lem294566 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term763 A P R f n) = (term417 A P R f n).
Proof. exact (SYM (@lem294565 A P R f n)). Qed.
Lemma lem294567 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term764 A P R f n) : term764 A P R f n.
Proof. exact (h1). Qed.
Lemma lem294576 {A : Type'} (P : A -> Prop) : (term433 A P) = (ex P).
Proof. exact (@lem19728 A P). Qed.
Lemma lem294577 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term434 A P R f n) = (term435 A P R f n).
Proof. exact (@lem294576 A (term436 A P R f n)). Qed.
Lemma lem294578 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term434 A P R f n) = (term403 A P R f n).
Proof. exact (eq_refl (term434 A P R f n)). Qed.
Lemma lem294579 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem294580 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term437 A P R f n) = (term438 A P R f n).
Proof. exact (MK_COMB (@lem294579) (@lem294578 A P R f n)). Qed.
Lemma lem294581 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term435 A P R f n) = (term435 A P R f n).
Proof. exact (eq_refl (term435 A P R f n)). Qed.
Lemma lem294582 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : ((term434 A P R f n) = (term435 A P R f n)) = ((term403 A P R f n) = (term435 A P R f n)).
Proof. exact (MK_COMB (@lem294580 A P R f n) (@lem294581 A P R f n)). Qed.
Lemma lem294593 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term403 A P R f n) = (term435 A P R f n).
Proof. exact (EQ_MP (@lem294582 A P R f n) (@lem294577 A P R f n)). Qed.
Lemma lem294594 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term403 A P R f n) = (term435 A P R f n).
Proof. exact (@lem294593 A P R f n). Qed.
Lemma lem294599 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem294600 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term415 A P R f n) = (term765 A P R f n).
Proof. exact (MK_COMB (@lem294599) (@lem294594 A P R f n)). Qed.
Lemma lem294602 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term403 A P R f n) = (term435 A P R f n).
Proof. exact (EQ_MP (@lem294582 A P R f n) (@lem294577 A P R f n)). Qed.
Lemma lem294603 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term403 A P R f n) = (term435 A P R f n).
Proof. exact (@lem294602 A P R f n). Qed.
Lemma lem294604 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term417 A P R f n) = (term766 A P R f n).
Proof. exact (@lem294603 A P R f (S n)). Qed.
Lemma lem294609 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem294610 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term764 A P R f n) = (term767 A P R f n).
Proof. exact (MK_COMB (@lem294609) (@lem294604 A P R f n)). Qed.
Lemma lem294611 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem294612 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term768 A P R f n) = (term769 A P R f n).
Proof. exact (MK_COMB (@lem294611) (@lem294610 A P R f n)). Qed.
Lemma lem294613 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem294614 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term763 A P R f n) = (term770 A P R f n).
Proof. exact (MK_COMB (@lem294612 A P R f n) (@lem294613)). Qed.
Lemma lem294615 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term771 A P R f n) = (term772 A P R f n).
Proof. exact (MK_COMB (@lem294600 A P R f n) (@lem294614 A P R f n)). Qed.
Lemma lem294616 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term444 A P R f) = (term444 A P R f).
Proof. exact (eq_refl (term444 A P R f)). Qed.
Lemma lem294617 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term773 A P R f n) = (term774 A P R f n).
Proof. exact (MK_COMB (@lem294616 A P R f) (@lem294615 A P R f n)). Qed.
Lemma lem294618 {A : Type'} (f : nat -> A) (a : A) : (term447 A f a) = (term447 A f a).
Proof. exact (eq_refl (term447 A f a)). Qed.
Lemma lem294619 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term775 A a P R f n) = (term776 A a P R f n).
Proof. exact (MK_COMB (@lem294618 A f a) (@lem294617 A P R f n)). Qed.
Lemma lem294620 {A : Type'} (P : type1597 A) (R : type1594 A) : (term450 A P R) = (term450 A P R).
Proof. exact (eq_refl (term450 A P R)). Qed.
Lemma lem294621 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term777 A a P R f n) = (term778 A a P R f n).
Proof. exact (MK_COMB (@lem294620 A P R) (@lem294619 A a P R f n)). Qed.
Lemma lem294622 {A : Type'} (P : type1597 A) (a : A) : (term453 A P a) = (term453 A P a).
Proof. exact (eq_refl (term453 A P a)). Qed.
Lemma lem294623 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term779 A a P R f n) = (term780 A a P R f n).
Proof. exact (MK_COMB (@lem294622 A P a) (@lem294621 A a P R f n)). Qed.
Lemma lem294624 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term780 A a P R f n) = (term779 A a P R f n).
Proof. exact (SYM (@lem294623 A a P R f n)). Qed.
Lemma lem294625 {A : Type'} (P : A -> Prop) : term456 A P.
Proof. exact (@lem19732 A P). Qed.
Lemma lem294626 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : term457 A P R f n.
Proof. exact (@lem294625 A (term436 A P R f n)). Qed.
Lemma lem294627 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term434 A P R f n) = (term403 A P R f n).
Proof. exact (eq_refl (term434 A P R f n)). Qed.
Lemma lem294628 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (x : A) : (term458 A P R f n x) = (term459 A P R f n x).
Proof. exact (eq_refl (term458 A P R f n x)). Qed.
Lemma lem294629 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem294630 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (x : A) : (term460 A P R f n x) = (term461 A P R f n x).
Proof. exact (MK_COMB (@lem294629) (@lem294628 A P R f n x)). Qed.
Lemma lem294631 {A : Type'} (x : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term462 A x P R f n) = (term463 A x P R f n).
Proof. exact (MK_COMB (@lem294630 A P R f n x) (@lem294627 A P R f n)). Qed.
Lemma lem294632 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term464 A P R f n) = (term465 A P R f n).
Proof. exact (fun_ext (fun x : A => @lem294631 A x P R f n)). Qed.
Lemma lem294633 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem294634 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term457 A P R f n) = (term466 A P R f n).
Proof. exact (MK_COMB (@lem294633 A) (@lem294632 A P R f n)). Qed.
Lemma lem294635 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : term466 A P R f n.
Proof. exact (EQ_MP (@lem294634 A P R f n) (@lem294626 A P R f n)). Qed.
Lemma lem294636 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : term467 A P R f.
Proof. exact (fun n : nat => @lem294635 A P R f n). Qed.
Lemma lem294637 {A : Type'} (P : type1597 A) (R : type1594 A) : term468 A P R.
Proof. exact (fun f : nat -> A => @lem294636 A P R f). Qed.
Lemma lem294638 {A : Type'} (P : type1597 A) : term469 A P.
Proof. exact (fun R : type1594 A => @lem294637 A P R). Qed.
Lemma lem294639 {A : Type'} : term470 A.
Proof. exact (fun P : type1597 A => @lem294638 A P). Qed.
Lemma lem294640 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term781 A a P R f n) : term781 A a P R f n.
Proof. exact (h1). Qed.
Lemma lem294641 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term781 A a P R f n) : term780 A a P R f n.
Proof. exact (@lem294640 A a P R f n h1 (@lem294639 A)). Qed.
Lemma lem294642 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : term782 A a P R f n.
Proof. exact (fun h0 : term781 A a P R f n => @lem294641 A a P R f n h0). Qed.
Lemma lem294643 {A : Type'} (_6610 : type943 A) (h1 : _6610 = (term473 A)) : _6610 = (term473 A).
Proof. exact (h1). Qed.
Lemma lem294644 {A : Type'} (P : type1597 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem294645 {A : Type'} (P : type1597 A) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (_6610 P) = (term474 A P).
Proof. exact (MK_COMB (@lem294643 A _6610 h1) (@lem294644 A P)). Qed.
Lemma lem294646 {A : Type'} (P : type1597 A) : (term474 A P) = (term475 A P).
Proof. exact (eq_refl (term474 A P)). Qed.
Lemma lem294647 {A : Type'} (_6610 : type943 A) (P : type1597 A) : (term476 A _6610 P) = (term476 A _6610 P).
Proof. exact (eq_refl (term476 A _6610 P)). Qed.
Lemma lem294648 {A : Type'} (_6610 : type943 A) (P : type1597 A) : ((_6610 P) = (term474 A P)) = ((_6610 P) = (term475 A P)).
Proof. exact (MK_COMB (@lem294647 A _6610 P) (@lem294646 A P)). Qed.
Lemma lem294649 {A : Type'} (P : type1597 A) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (_6610 P) = (term475 A P).
Proof. exact (EQ_MP (@lem294648 A _6610 P) (@lem294645 A P _6610 h1)). Qed.
Lemma lem294650 {A : Type'} (R : type1594 A) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem294651 {A : Type'} (P : type1597 A) (R : type1594 A) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (_6610 P R) = (term477 A P R).
Proof. exact (MK_COMB (@lem294649 A P _6610 h1) (@lem294650 A R)). Qed.
Lemma lem294652 {A : Type'} (P : type1597 A) (R : type1594 A) : (term477 A P R) = (term478 A P R).
Proof. exact (eq_refl (term477 A P R)). Qed.
Lemma lem294653 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) : (term479 A _6610 P R) = (term479 A _6610 P R).
Proof. exact (eq_refl (term479 A _6610 P R)). Qed.
Lemma lem294654 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) : ((_6610 P R) = (term477 A P R)) = ((_6610 P R) = (term478 A P R)).
Proof. exact (MK_COMB (@lem294653 A _6610 P R) (@lem294652 A P R)). Qed.
Lemma lem294655 {A : Type'} (P : type1597 A) (R : type1594 A) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (_6610 P R) = (term478 A P R).
Proof. exact (EQ_MP (@lem294654 A _6610 P R) (@lem294651 A P R _6610 h1)). Qed.
Lemma lem294656 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem294657 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (_6610 P R f) = (term480 A P R f).
Proof. exact (MK_COMB (@lem294655 A P R _6610 h1) (@lem294656 A f)). Qed.
Lemma lem294658 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term480 A P R f) = (term481 A P R f).
Proof. exact (eq_refl (term480 A P R f)). Qed.
Lemma lem294659 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term482 A _6610 P R f) = (term482 A _6610 P R f).
Proof. exact (eq_refl (term482 A _6610 P R f)). Qed.
Lemma lem294660 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : ((_6610 P R f) = (term480 A P R f)) = ((_6610 P R f) = (term481 A P R f)).
Proof. exact (MK_COMB (@lem294659 A _6610 P R f) (@lem294658 A P R f)). Qed.
Lemma lem294661 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (_6610 P R f) = (term481 A P R f).
Proof. exact (EQ_MP (@lem294660 A _6610 P R f) (@lem294657 A P R f _6610 h1)). Qed.
Lemma lem294662 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem294663 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (_6610 P R f n) = (term483 A P R f n).
Proof. exact (MK_COMB (@lem294661 A P R f _6610 h1) (@lem294662 n)). Qed.
Lemma lem294664 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term483 A P R f n) = (term290 A P R f n).
Proof. exact (eq_refl (term483 A P R f n)). Qed.
Lemma lem294665 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term484 A _6610 P R f n) = (term484 A _6610 P R f n).
Proof. exact (eq_refl (term484 A _6610 P R f n)). Qed.
Lemma lem294666 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : ((_6610 P R f n) = (term483 A P R f n)) = ((_6610 P R f n) = (term290 A P R f n)).
Proof. exact (MK_COMB (@lem294665 A _6610 P R f n) (@lem294664 A P R f n)). Qed.
Lemma lem294667 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (_6610 P R f n) = (term290 A P R f n).
Proof. exact (EQ_MP (@lem294666 A _6610 P R f n) (@lem294663 A P R f n _6610 h1)). Qed.
Lemma lem294668 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (term290 A P R f n) = (_6610 P R f n).
Proof. exact (SYM (@lem294667 A P R f n _6610 h1)). Qed.
Lemma lem294669 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : term485 A _6610 P R f.
Proof. exact (fun n : nat => @lem294668 A P R f n _6610 h1). Qed.
Lemma lem294670 {A : Type'} (P : type1597 A) (R : type1594 A) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : term486 A _6610 P R.
Proof. exact (fun f : nat -> A => @lem294669 A P R f _6610 h1). Qed.
Lemma lem294671 {A : Type'} (P : type1597 A) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : term487 A _6610 P.
Proof. exact (fun R : type1594 A => @lem294670 A P R _6610 h1). Qed.
Lemma lem294672 {A : Type'} (_6610 : type943 A) (h1 : _6610 = (term473 A)) : term488 A _6610.
Proof. exact (fun P : type1597 A => @lem294671 A P _6610 h1). Qed.
Lemma lem294673 {A : Type'} (P : type1597 A) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : term489 A _6610 P.
Proof. exact (@lem294672 A _6610 h1 P). Qed.
Lemma lem294674 {A : Type'} (_6610 : type943 A) (P : type1597 A) : (term489 A _6610 P) = (term487 A _6610 P).
Proof. exact (eq_refl (term489 A _6610 P)). Qed.
Lemma lem294675 {A : Type'} (P : type1597 A) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : term487 A _6610 P.
Proof. exact (EQ_MP (@lem294674 A _6610 P) (@lem294673 A P _6610 h1)). Qed.
Lemma lem294676 {A : Type'} (P : type1597 A) (R : type1594 A) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : term490 A _6610 P R.
Proof. exact (@lem294675 A P _6610 h1 R). Qed.
Lemma lem294677 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) : (term490 A _6610 P R) = (term486 A _6610 P R).
Proof. exact (eq_refl (term490 A _6610 P R)). Qed.
Lemma lem294678 {A : Type'} (P : type1597 A) (R : type1594 A) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : term486 A _6610 P R.
Proof. exact (EQ_MP (@lem294677 A _6610 P R) (@lem294676 A P R _6610 h1)). Qed.
Lemma lem294679 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : term491 A _6610 P R f.
Proof. exact (@lem294678 A P R _6610 h1 f). Qed.
Lemma lem294680 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term491 A _6610 P R f) = (term485 A _6610 P R f).
Proof. exact (eq_refl (term491 A _6610 P R f)). Qed.
Lemma lem294681 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : term485 A _6610 P R f.
Proof. exact (EQ_MP (@lem294680 A _6610 P R f) (@lem294679 A P R f _6610 h1)). Qed.
Lemma lem294682 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : term492 A _6610 P R f n.
Proof. exact (@lem294681 A P R f _6610 h1 n). Qed.
Lemma lem294683 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term492 A _6610 P R f n) = ((term290 A P R f n) = (_6610 P R f n)).
Proof. exact (eq_refl (term492 A _6610 P R f n)). Qed.
Lemma lem294686 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (term290 A P R f n) = (_6610 P R f n).
Proof. exact (EQ_MP (@lem294683 A _6610 P R f n) (@lem294682 A P R f n _6610 h1)). Qed.
Lemma lem294687 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (term290 A P R f n) = (_6610 P R f n).
Proof. exact (@lem294686 A P R f n _6610 h1). Qed.
Lemma lem294688 {A : Type'} (P : type1597 A) (n : nat) : (term380 A P n) = (term380 A P n).
Proof. exact (eq_refl (term380 A P n)). Qed.
Lemma lem294689 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (term381 A P R f n) = (term493 A _6610 P R f n).
Proof. exact (MK_COMB (@lem294688 A P n) (@lem294687 A P R f n _6610 h1)). Qed.
Lemma lem294690 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem294691 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (term401 A P R f n) = (term494 A _6610 P R f n).
Proof. exact (MK_COMB (@lem294690) (@lem294689 A P R f n _6610 h1)). Qed.
Lemma lem294693 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (term290 A P R f n) = (_6610 P R f n).
Proof. exact (EQ_MP (@lem294683 A _6610 P R f n) (@lem294682 A P R f n _6610 h1)). Qed.
Lemma lem294694 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (term290 A P R f n) = (_6610 P R f n).
Proof. exact (@lem294693 A P R f n _6610 h1). Qed.
Lemma lem294695 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term341 A R f n) = (term341 A R f n).
Proof. exact (eq_refl (term341 A R f n)). Qed.
Lemma lem294696 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (term343 A P R f n) = (term495 A _6610 P R f n).
Proof. exact (MK_COMB (@lem294695 A R f n) (@lem294694 A P R f n _6610 h1)). Qed.
Lemma lem294697 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (term403 A P R f n) = (term496 A _6610 P R f n).
Proof. exact (MK_COMB (@lem294691 A P R f n _6610 h1) (@lem294696 A P R f n _6610 h1)). Qed.
Lemma lem294698 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (x : A) : (term461 A P R f n x) = (term461 A P R f n x).
Proof. exact (eq_refl (term461 A P R f n x)). Qed.
Lemma lem294699 {A : Type'} (x : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (term463 A x P R f n) = (term497 A x _6610 P R f n).
Proof. exact (MK_COMB (@lem294698 A P R f n x) (@lem294697 A P R f n _6610 h1)). Qed.
Lemma lem294700 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (term465 A P R f n) = (term498 A _6610 P R f n).
Proof. exact (fun_ext (fun x : A => @lem294699 A x P R f n _6610 h1)). Qed.
Lemma lem294701 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem294702 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (term466 A P R f n) = (term499 A _6610 P R f n).
Proof. exact (MK_COMB (@lem294701 A) (@lem294700 A P R f n _6610 h1)). Qed.
Lemma lem294703 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (term500 A P R f) = (term501 A _6610 P R f).
Proof. exact (fun_ext (fun n : nat => @lem294702 A P R f n _6610 h1)). Qed.
Lemma lem294704 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem294705 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (term467 A P R f) = (term502 A _6610 P R f).
Proof. exact (MK_COMB (@lem294704) (@lem294703 A P R f _6610 h1)). Qed.
Lemma lem294706 {A : Type'} (P : type1597 A) (R : type1594 A) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (term503 A P R) = (term504 A _6610 P R).
Proof. exact (fun_ext (fun f : nat -> A => @lem294705 A P R f _6610 h1)). Qed.
Lemma lem294707 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem294708 {A : Type'} (P : type1597 A) (R : type1594 A) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (term468 A P R) = (term505 A _6610 P R).
Proof. exact (MK_COMB (@lem294707 A) (@lem294706 A P R _6610 h1)). Qed.
Lemma lem294709 {A : Type'} (P : type1597 A) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (term506 A P) = (term507 A _6610 P).
Proof. exact (fun_ext (fun R : type1594 A => @lem294708 A P R _6610 h1)). Qed.
Lemma lem294710 {A : Type'} : (@all (nat -> A -> A -> Prop)) = (@all (nat -> A -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> A -> Prop))). Qed.
Lemma lem294711 {A : Type'} (P : type1597 A) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (term469 A P) = (term508 A _6610 P).
Proof. exact (MK_COMB (@lem294710 A) (@lem294709 A P _6610 h1)). Qed.
Lemma lem294712 {A : Type'} (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (term509 A) = (term510 A _6610).
Proof. exact (fun_ext (fun P : type1597 A => @lem294711 A P _6610 h1)). Qed.
Lemma lem294713 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem294714 {A : Type'} (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (term470 A) = (term511 A _6610).
Proof. exact (MK_COMB (@lem294713 A) (@lem294712 A _6610 h1)). Qed.
Lemma lem294715 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem294716 {A : Type'} (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (term512 A) = (term513 A _6610).
Proof. exact (MK_COMB (@lem294715) (@lem294714 A _6610 h1)). Qed.
Lemma lem294718 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (term290 A P R f n) = (_6610 P R f n).
Proof. exact (EQ_MP (@lem294683 A _6610 P R f n) (@lem294682 A P R f n _6610 h1)). Qed.
Lemma lem294719 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (term290 A P R f n) = (_6610 P R f n).
Proof. exact (@lem294718 A P R f n _6610 h1). Qed.
Lemma lem294720 {A : Type'} (f : nat -> A) (n : nat) : (term302 A f n) = (term302 A f n).
Proof. exact (eq_refl (term302 A f n)). Qed.
Lemma lem294721 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : ((term289 A f n) = (term290 A P R f n)) = ((term289 A f n) = (_6610 P R f n)).
Proof. exact (MK_COMB (@lem294720 A f n) (@lem294719 A P R f n _6610 h1)). Qed.
Lemma lem294722 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (term304 A P R f) = (term514 A _6610 P R f).
Proof. exact (fun_ext (fun n : nat => @lem294721 A P R f n _6610 h1)). Qed.
Lemma lem294723 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem294724 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (term287 A P R f) = (term515 A _6610 P R f).
Proof. exact (MK_COMB (@lem294723) (@lem294722 A P R f _6610 h1)). Qed.
Lemma lem294725 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem294726 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (term444 A P R f) = (term516 A _6610 P R f).
Proof. exact (MK_COMB (@lem294725) (@lem294724 A P R f _6610 h1)). Qed.
Lemma lem294727 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term772 A P R f n) = (term772 A P R f n).
Proof. exact (eq_refl (term772 A P R f n)). Qed.
Lemma lem294728 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (term774 A P R f n) = (term783 A _6610 P R f n).
Proof. exact (MK_COMB (@lem294726 A P R f _6610 h1) (@lem294727 A P R f n)). Qed.
Lemma lem294729 {A : Type'} (f : nat -> A) (a : A) : (term447 A f a) = (term447 A f a).
Proof. exact (eq_refl (term447 A f a)). Qed.
Lemma lem294730 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (term776 A a P R f n) = (term784 A a _6610 P R f n).
Proof. exact (MK_COMB (@lem294729 A f a) (@lem294728 A P R f n _6610 h1)). Qed.
Lemma lem294731 {A : Type'} (P : type1597 A) (R : type1594 A) : (term450 A P R) = (term450 A P R).
Proof. exact (eq_refl (term450 A P R)). Qed.
Lemma lem294732 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (term778 A a P R f n) = (term785 A a _6610 P R f n).
Proof. exact (MK_COMB (@lem294731 A P R) (@lem294730 A a P R f n _6610 h1)). Qed.
Lemma lem294733 {A : Type'} (P : type1597 A) (a : A) : (term453 A P a) = (term453 A P a).
Proof. exact (eq_refl (term453 A P a)). Qed.
Lemma lem294734 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (term780 A a P R f n) = (term786 A a _6610 P R f n).
Proof. exact (MK_COMB (@lem294733 A P a) (@lem294732 A a P R f n _6610 h1)). Qed.
Lemma lem294735 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (term781 A a P R f n) = (term787 A a _6610 P R f n).
Proof. exact (MK_COMB (@lem294716 A _6610 h1) (@lem294734 A a P R f n _6610 h1)). Qed.
Lemma lem294736 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term788 A a P R f n) : term788 A a P R f n.
Proof. exact (h1). Qed.
Lemma lem294737 {A : Type'} (_6610 : type943 A) (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term788 A a P R f n) : term789 A a P R f n _6610.
Proof. exact (@lem294736 A a P R f n h1 _6610). Qed.
Lemma lem294738 {A : Type'} (a : A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term789 A a P R f n _6610) = (term787 A a _6610 P R f n).
Proof. exact (eq_refl (term789 A a P R f n _6610)). Qed.
Lemma lem294739 {A : Type'} (_6610 : type943 A) (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term788 A a P R f n) : term787 A a _6610 P R f n.
Proof. exact (EQ_MP (@lem294738 A a _6610 P R f n) (@lem294737 A _6610 a P R f n h1)). Qed.
Lemma lem294740 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : (term787 A a _6610 P R f n) = (term781 A a P R f n).
Proof. exact (SYM (@lem294735 A a P R f n _6610 h1)). Qed.
Lemma lem294741 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6610 : type943 A) (h1 : term788 A a P R f n) (h2 : _6610 = (term473 A)) : term781 A a P R f n.
Proof. exact (EQ_MP (@lem294740 A a P R f n _6610 h2) (@lem294739 A _6610 a P R f n h1)). Qed.
Lemma lem294742 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : term790 A a P R f n.
Proof. exact (fun h0 : term788 A a P R f n => @lem294741 A a P R f n _6610 h0 h1). Qed.
Lemma lem294743 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : term791 A a P R f n.
Proof. exact (@lem51 (term781 A a P R f n) (term788 A a P R f n) (term780 A a P R f n)). Qed.
Lemma lem294744 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : term792 A a P R f n.
Proof. exact (@lem294743 A a P R f n (@lem294742 A a P R f n _6610 h1)). Qed.
Lemma lem294745 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6610 : type943 A) (h1 : _6610 = (term473 A)) : term793 A a P R f n.
Proof. exact (@lem294744 A a P R f n _6610 h1 (@lem294642 A a P R f n)). Qed.
Lemma lem294746 {A : Type'} : (term473 A) = (term473 A).
Proof. exact (eq_refl (term473 A)). Qed.
Lemma lem294747 {A : Type'} (_6610 : type943 A) (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : term794 A _6610 a P R f n.
Proof. exact (fun h0 : _6610 = (term473 A) => @lem294745 A a P R f n _6610 h0). Qed.
Lemma lem294748 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : term795 A a P R f n.
Proof. exact (@lem294747 A (term473 A) a P R f n). Qed.
Lemma lem294749 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : term793 A a P R f n.
Proof. exact (@lem294748 A a P R f n (@lem294746 A)). Qed.
Lemma lem294750 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term788 A a P R f n) : term788 A a P R f n.
Proof. exact (h1). Qed.
Lemma lem294751 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : term796 A a P R f n.
Proof. exact (fun h0 : term788 A a P R f n => @lem294750 A a P R f n h0). Qed.
Lemma lem294752 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : term797 A a P R f n.
Proof. exact (@lem51 (term788 A a P R f n) (term788 A a P R f n) (term780 A a P R f n)). Qed.
Lemma lem294753 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : term798 A a P R f n.
Proof. exact (@lem294752 A a P R f n (@lem294751 A a P R f n)). Qed.
Lemma lem294754 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : term793 A a P R f n.
Proof. exact (@lem294753 A a P R f n (@lem294749 A a P R f n)). Qed.
Lemma lem294755 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term793 A a P R f n) : term793 A a P R f n.
Proof. exact (h1). Qed.
Lemma lem294756 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term788 A a P R f n) : term788 A a P R f n.
Proof. exact (h1). Qed.
Lemma lem294757 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term788 A a P R f n) (h2 : term793 A a P R f n) : term780 A a P R f n.
Proof. exact (@lem294755 A a P R f n h2 (@lem294756 A a P R f n h1)). Qed.
Lemma lem294758 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term788 A a P R f n) : term799 A a P R f n.
Proof. exact (fun h0 : term793 A a P R f n => @lem294757 A a P R f n h1 h0). Qed.
Lemma lem294759 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term793 A a P R f n) : term793 A a P R f n.
Proof. exact (h1). Qed.
Lemma lem294760 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term788 A a P R f n) (h2 : term793 A a P R f n) : term780 A a P R f n.
Proof. exact (@lem294758 A a P R f n h1 (@lem294759 A a P R f n h2)). Qed.
Lemma lem294761 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term793 A a P R f n) : term793 A a P R f n.
Proof. exact (fun h0 : term788 A a P R f n => @lem294760 A a P R f n h0 h1). Qed.
Lemma lem294762 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : term798 A a P R f n.
Proof. exact (fun h0 : term793 A a P R f n => @lem294761 A a P R f n h0). Qed.
Lemma lem294765 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : term793 A a P R f n.
Proof. exact (@lem294762 A a P R f n (@lem294754 A a P R f n)). Qed.
Lemma lem294766 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : term793 A a P R f n.
Proof. exact (@lem294765 A a P R f n). Qed.
Lemma lem294944 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem294945 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term770 A P R f n) = (term800 A P R f n).
Proof. exact (@lem294944 (term767 A P R f n)). Qed.
Lemma lem294947 (t : Prop) : (term210 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem294948 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term800 A P R f n) = (term766 A P R f n).
Proof. exact (@lem294947 (term766 A P R f n)). Qed.
Lemma lem294997 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term770 A P R f n) = (term766 A P R f n).
Proof. exact (TRANS (@lem294945 A P R f n) (@lem294948 A P R f n)). Qed.
Lemma lem295000 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term765 A P R f n) = (term765 A P R f n).
Proof. exact (eq_refl (term765 A P R f n)). Qed.
Lemma lem295001 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term772 A P R f n) = (term801 A P R f n).
Proof. exact (MK_COMB (@lem295000 A P R f n) (@lem294997 A P R f n)). Qed.
Lemma lem295004 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term516 A _6610 P R f) = (term516 A _6610 P R f).
Proof. exact (eq_refl (term516 A _6610 P R f)). Qed.
Lemma lem295005 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term783 A _6610 P R f n) = (term802 A _6610 P R f n).
Proof. exact (MK_COMB (@lem295004 A _6610 P R f) (@lem295001 A P R f n)). Qed.
Lemma lem295008 {A : Type'} (f : nat -> A) (a : A) : (term447 A f a) = (term447 A f a).
Proof. exact (eq_refl (term447 A f a)). Qed.
Lemma lem295009 {A : Type'} (a : A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term784 A a _6610 P R f n) = (term803 A a _6610 P R f n).
Proof. exact (MK_COMB (@lem295008 A f a) (@lem295005 A _6610 P R f n)). Qed.
Lemma lem295012 {A : Type'} (P : type1597 A) (R : type1594 A) : (term450 A P R) = (term450 A P R).
Proof. exact (eq_refl (term450 A P R)). Qed.
Lemma lem295013 {A : Type'} (a : A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term785 A a _6610 P R f n) = (term804 A a _6610 P R f n).
Proof. exact (MK_COMB (@lem295012 A P R) (@lem295009 A a _6610 P R f n)). Qed.
Lemma lem295016 {A : Type'} (P : type1597 A) (a : A) : (term453 A P a) = (term453 A P a).
Proof. exact (eq_refl (term453 A P a)). Qed.
Lemma lem295017 {A : Type'} (a : A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term786 A a _6610 P R f n) = (term805 A a _6610 P R f n).
Proof. exact (MK_COMB (@lem295016 A P a) (@lem295013 A a _6610 P R f n)). Qed.
Lemma lem295020 {A : Type'} (_6610 : type943 A) : (term513 A _6610) = (term513 A _6610).
Proof. exact (eq_refl (term513 A _6610)). Qed.
Lemma lem295021 {A : Type'} (a : A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term787 A a _6610 P R f n) = (term806 A a _6610 P R f n).
Proof. exact (MK_COMB (@lem295020 A _6610) (@lem295017 A a _6610 P R f n)). Qed.
Lemma lem295024 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term807 A a P R f n) = (term808 A a P R f n).
Proof. exact (fun_ext (fun _6610 : type943 A => @lem295021 A a _6610 P R f n)). Qed.
Lemma lem295025 {A : Type'} : (@all ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> (nat -> A) -> nat -> A)) = (@all ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> (nat -> A) -> nat -> A)).
Proof. exact (eq_refl (@all ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> (nat -> A) -> nat -> A))). Qed.
Lemma lem295026 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term788 A a P R f n) = (term809 A a P R f n).
Proof. exact (MK_COMB (@lem295025 A) (@lem295024 A a P R f n)). Qed.
Lemma lem295031 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term810 A P R f n) = (term811 A P R f n).
Proof. exact (fun_ext (fun a : A => @lem295026 A a P R f n)). Qed.
Lemma lem295032 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem295033 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term812 A P R f n) = (term813 A P R f n).
Proof. exact (MK_COMB (@lem295032 A) (@lem295031 A P R f n)). Qed.
Lemma lem295038 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term814 A R f n) = (term815 A R f n).
Proof. exact (fun_ext (fun P : type1597 A => @lem295033 A P R f n)). Qed.
Lemma lem295039 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem295040 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term816 A R f n) = (term817 A R f n).
Proof. exact (MK_COMB (@lem295039 A) (@lem295038 A R f n)). Qed.
Lemma lem295045 {A : Type'} (f : nat -> A) (n : nat) : (term818 A f n) = (term819 A f n).
Proof. exact (fun_ext (fun R : type1594 A => @lem295040 A R f n)). Qed.
Lemma lem295046 {A : Type'} : (@all (nat -> A -> A -> Prop)) = (@all (nat -> A -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> A -> Prop))). Qed.
Lemma lem295047 {A : Type'} (f : nat -> A) (n : nat) : (term820 A f n) = (term821 A f n).
Proof. exact (MK_COMB (@lem295046 A) (@lem295045 A f n)). Qed.
Lemma lem295052 {A : Type'} (n : nat) : (term822 A n) = (term823 A n).
Proof. exact (fun_ext (fun f : nat -> A => @lem295047 A f n)). Qed.
Lemma lem295053 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem295054 {A : Type'} (n : nat) : (term824 A n) = (term825 A n).
Proof. exact (MK_COMB (@lem295053 A) (@lem295052 A n)). Qed.
Lemma lem295059 {A : Type'} : (term826 A) = (term827 A).
Proof. exact (fun_ext (fun n : nat => @lem295054 A n)). Qed.
Lemma lem295060 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem295069 {A : Type'} : (term828 A) = (term829 A).
Proof. exact (MK_COMB (@lem295060) (@lem295059 A)). Qed.
Lemma lem295074 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) : (term830 A P R f n y) = (term830 A P R f n y).
Proof. exact (eq_refl (term830 A P R f n y)). Qed.
Lemma lem295075 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term831 A P R f n) = (term831 A P R f n).
Proof. exact (fun_ext (fun y : A => @lem295074 A P R f n y)). Qed.
Lemma lem295076 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem295077 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term766 A P R f n) = (term766 A P R f n).
Proof. exact (MK_COMB (@lem295076 A) (@lem295075 A P R f n)). Qed.
Lemma lem295082 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) : (term459 A P R f n y) = (term459 A P R f n y).
Proof. exact (eq_refl (term459 A P R f n y)). Qed.
Lemma lem295083 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term436 A P R f n) = (term436 A P R f n).
Proof. exact (fun_ext (fun y : A => @lem295082 A P R f n y)). Qed.
Lemma lem295084 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem295085 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term435 A P R f n) = (term435 A P R f n).
Proof. exact (MK_COMB (@lem295084 A) (@lem295083 A P R f n)). Qed.
Lemma lem295086 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem295087 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term765 A P R f n) = (term765 A P R f n).
Proof. exact (MK_COMB (@lem295086) (@lem295085 A P R f n)). Qed.
Lemma lem295088 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term801 A P R f n) = (term801 A P R f n).
Proof. exact (MK_COMB (@lem295087 A P R f n) (@lem295077 A P R f n)). Qed.
Lemma lem295089 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : ((term289 A f n) = (_6610 P R f n)) = ((term289 A f n) = (_6610 P R f n)).
Proof. exact (eq_refl ((term289 A f n) = (_6610 P R f n))). Qed.
Lemma lem295090 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term514 A _6610 P R f) = (term514 A _6610 P R f).
Proof. exact (fun_ext (fun n : nat => @lem295089 A _6610 P R f n)). Qed.
Lemma lem295091 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem295092 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term515 A _6610 P R f) = (term515 A _6610 P R f).
Proof. exact (MK_COMB (@lem295091) (@lem295090 A _6610 P R f)). Qed.
Lemma lem295093 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem295094 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term516 A _6610 P R f) = (term516 A _6610 P R f).
Proof. exact (MK_COMB (@lem295093) (@lem295092 A _6610 P R f)). Qed.
Lemma lem295095 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term802 A _6610 P R f n) = (term802 A _6610 P R f n).
Proof. exact (MK_COMB (@lem295094 A _6610 P R f) (@lem295088 A P R f n)). Qed.
Lemma lem295098 {A : Type'} (f : nat -> A) (a : A) : (term447 A f a) = (term447 A f a).
Proof. exact (eq_refl (term447 A f a)). Qed.
Lemma lem295099 {A : Type'} (a : A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term803 A a _6610 P R f n) = (term803 A a _6610 P R f n).
Proof. exact (MK_COMB (@lem295098 A f a) (@lem295095 A _6610 P R f n)). Qed.
Lemma lem295104 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) (y : A) : (term561 A P R n x y) = (term561 A P R n x y).
Proof. exact (eq_refl (term561 A P R n x y)). Qed.
Lemma lem295105 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term562 A P R n x) = (term562 A P R n x).
Proof. exact (fun_ext (fun y : A => @lem295104 A P R n x y)). Qed.
Lemma lem295106 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem295107 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term563 A P R n x) = (term563 A P R n x).
Proof. exact (MK_COMB (@lem295106 A) (@lem295105 A P R n x)). Qed.
Lemma lem295110 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (term564 A P n x) = (term564 A P n x).
Proof. exact (eq_refl (term564 A P n x)). Qed.
Lemma lem295111 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term565 A P R n x) = (term565 A P R n x).
Proof. exact (MK_COMB (@lem295110 A P n x) (@lem295107 A P R n x)). Qed.
Lemma lem295112 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term566 A P R n) = (term566 A P R n).
Proof. exact (fun_ext (fun x : A => @lem295111 A P R n x)). Qed.
Lemma lem295113 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem295114 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term567 A P R n) = (term567 A P R n).
Proof. exact (MK_COMB (@lem295113 A) (@lem295112 A P R n)). Qed.
Lemma lem295115 {A : Type'} (P : type1597 A) (R : type1594 A) : (term568 A P R) = (term568 A P R).
Proof. exact (fun_ext (fun n : nat => @lem295114 A P R n)). Qed.
Lemma lem295116 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem295117 {A : Type'} (P : type1597 A) (R : type1594 A) : (term312 A P R) = (term312 A P R).
Proof. exact (MK_COMB (@lem295116) (@lem295115 A P R)). Qed.
Lemma lem295118 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem295119 {A : Type'} (P : type1597 A) (R : type1594 A) : (term450 A P R) = (term450 A P R).
Proof. exact (MK_COMB (@lem295118) (@lem295117 A P R)). Qed.
Lemma lem295120 {A : Type'} (a : A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term804 A a _6610 P R f n) = (term804 A a _6610 P R f n).
Proof. exact (MK_COMB (@lem295119 A P R) (@lem295099 A a _6610 P R f n)). Qed.
Lemma lem295123 {A : Type'} (P : type1597 A) (a : A) : (term453 A P a) = (term453 A P a).
Proof. exact (eq_refl (term453 A P a)). Qed.
Lemma lem295124 {A : Type'} (a : A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term805 A a _6610 P R f n) = (term805 A a _6610 P R f n).
Proof. exact (MK_COMB (@lem295123 A P a) (@lem295120 A a _6610 P R f n)). Qed.
Lemma lem295137 {A : Type'} (x : A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term497 A x _6610 P R f n) = (term497 A x _6610 P R f n).
Proof. exact (eq_refl (term497 A x _6610 P R f n)). Qed.
Lemma lem295138 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term498 A _6610 P R f n) = (term498 A _6610 P R f n).
Proof. exact (fun_ext (fun x : A => @lem295137 A x _6610 P R f n)). Qed.
Lemma lem295139 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem295140 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term499 A _6610 P R f n) = (term499 A _6610 P R f n).
Proof. exact (MK_COMB (@lem295139 A) (@lem295138 A _6610 P R f n)). Qed.
Lemma lem295141 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term501 A _6610 P R f) = (term501 A _6610 P R f).
Proof. exact (fun_ext (fun n : nat => @lem295140 A _6610 P R f n)). Qed.
Lemma lem295142 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem295143 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term502 A _6610 P R f) = (term502 A _6610 P R f).
Proof. exact (MK_COMB (@lem295142) (@lem295141 A _6610 P R f)). Qed.
Lemma lem295144 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) : (term504 A _6610 P R) = (term504 A _6610 P R).
Proof. exact (fun_ext (fun f : nat -> A => @lem295143 A _6610 P R f)). Qed.
Lemma lem295145 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem295146 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) : (term505 A _6610 P R) = (term505 A _6610 P R).
Proof. exact (MK_COMB (@lem295145 A) (@lem295144 A _6610 P R)). Qed.
Lemma lem295147 {A : Type'} (_6610 : type943 A) (P : type1597 A) : (term507 A _6610 P) = (term507 A _6610 P).
Proof. exact (fun_ext (fun R : type1594 A => @lem295146 A _6610 P R)). Qed.
Lemma lem295148 {A : Type'} : (@all (nat -> A -> A -> Prop)) = (@all (nat -> A -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> A -> Prop))). Qed.
Lemma lem295149 {A : Type'} (_6610 : type943 A) (P : type1597 A) : (term508 A _6610 P) = (term508 A _6610 P).
Proof. exact (MK_COMB (@lem295148 A) (@lem295147 A _6610 P)). Qed.
Lemma lem295150 {A : Type'} (_6610 : type943 A) : (term510 A _6610) = (term510 A _6610).
Proof. exact (fun_ext (fun P : type1597 A => @lem295149 A _6610 P)). Qed.
Lemma lem295151 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem295152 {A : Type'} (_6610 : type943 A) : (term511 A _6610) = (term511 A _6610).
Proof. exact (MK_COMB (@lem295151 A) (@lem295150 A _6610)). Qed.
Lemma lem295153 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem295154 {A : Type'} (_6610 : type943 A) : (term513 A _6610) = (term513 A _6610).
Proof. exact (MK_COMB (@lem295153) (@lem295152 A _6610)). Qed.
Lemma lem295155 {A : Type'} (a : A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term806 A a _6610 P R f n) = (term806 A a _6610 P R f n).
Proof. exact (MK_COMB (@lem295154 A _6610) (@lem295124 A a _6610 P R f n)). Qed.
Lemma lem295156 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term808 A a P R f n) = (term808 A a P R f n).
Proof. exact (fun_ext (fun _6610 : type943 A => @lem295155 A a _6610 P R f n)). Qed.
Lemma lem295157 {A : Type'} : (@all ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> (nat -> A) -> nat -> A)) = (@all ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> (nat -> A) -> nat -> A)).
Proof. exact (eq_refl (@all ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> (nat -> A) -> nat -> A))). Qed.
Lemma lem295158 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term809 A a P R f n) = (term809 A a P R f n).
Proof. exact (MK_COMB (@lem295157 A) (@lem295156 A a P R f n)). Qed.
Lemma lem295159 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term811 A P R f n) = (term811 A P R f n).
Proof. exact (fun_ext (fun a : A => @lem295158 A a P R f n)). Qed.
Lemma lem295160 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem295161 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term813 A P R f n) = (term813 A P R f n).
Proof. exact (MK_COMB (@lem295160 A) (@lem295159 A P R f n)). Qed.
Lemma lem295162 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term815 A R f n) = (term815 A R f n).
Proof. exact (fun_ext (fun P : type1597 A => @lem295161 A P R f n)). Qed.
Lemma lem295163 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem295164 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term817 A R f n) = (term817 A R f n).
Proof. exact (MK_COMB (@lem295163 A) (@lem295162 A R f n)). Qed.
Lemma lem295165 {A : Type'} (f : nat -> A) (n : nat) : (term819 A f n) = (term819 A f n).
Proof. exact (fun_ext (fun R : type1594 A => @lem295164 A R f n)). Qed.
Lemma lem295166 {A : Type'} : (@all (nat -> A -> A -> Prop)) = (@all (nat -> A -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> A -> Prop))). Qed.
Lemma lem295167 {A : Type'} (f : nat -> A) (n : nat) : (term821 A f n) = (term821 A f n).
Proof. exact (MK_COMB (@lem295166 A) (@lem295165 A f n)). Qed.
Lemma lem295168 {A : Type'} (n : nat) : (term823 A n) = (term823 A n).
Proof. exact (fun_ext (fun f : nat -> A => @lem295167 A f n)). Qed.
Lemma lem295169 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem295170 {A : Type'} (n : nat) : (term825 A n) = (term825 A n).
Proof. exact (MK_COMB (@lem295169 A) (@lem295168 A n)). Qed.
Lemma lem295171 {A : Type'} : (term827 A) = (term827 A).
Proof. exact (fun_ext (fun n : nat => @lem295170 A n)). Qed.
Lemma lem295172 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem295173 {A : Type'} : (term829 A) = (term829 A).
Proof. exact (MK_COMB (@lem295172) (@lem295171 A)). Qed.
Lemma lem295304 {A : Type'} : (term828 A) = (term829 A).
Proof. exact (TRANS (@lem295069 A) (@lem295173 A)). Qed.
Lemma lem295305 {A : Type'} : (term829 A) = (term828 A).
Proof. exact (SYM (@lem295304 A)). Qed.
Lemma lem295306 {A : Type'} (_6610 : type943 A) (h1 : term511 A _6610) : term511 A _6610.
Proof. exact (h1). Qed.
Lemma lem295308 {A : Type'} (P : type1597 A) (R : type1594 A) (h1 : term312 A P R) : term312 A P R.
Proof. exact (h1). Qed.
Lemma lem295310 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term515 A _6610 P R f) : term515 A _6610 P R f.
Proof. exact (h1). Qed.
Lemma lem295311 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term435 A P R f n) : term435 A P R f n.
Proof. exact (h1). Qed.
Lemma lem295313 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem295314 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term766 A P R f n) = (term770 A P R f n).
Proof. exact (@lem295313 (term766 A P R f n)). Qed.
Lemma lem295315 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term770 A P R f n) = (term766 A P R f n).
Proof. exact (SYM (@lem295314 A P R f n)). Qed.
Lemma lem295316 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term767 A P R f n) : term767 A P R f n.
Proof. exact (h1). Qed.
Lemma lem295323 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (x : A) : (term832 A P R f n x) = (term833 A P R f n x).
Proof. exact (@lem17045 (term834 A P n x) (term835 A R f n x)). Qed.
Lemma lem295328 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term496 A _6610 P R f n) = (term496 A _6610 P R f n).
Proof. exact (eq_refl (term496 A _6610 P R f n)). Qed.
Lemma lem295329 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem295330 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (x : A) : (term836 A P R f n x) = (term837 A P R f n x).
Proof. exact (MK_COMB (@lem295329) (@lem295323 A P R f n x)). Qed.
Lemma lem295331 {A : Type'} (x : A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term838 A x _6610 P R f n) = (term839 A x _6610 P R f n).
Proof. exact (MK_COMB (@lem295330 A P R f n x) (@lem295328 A _6610 P R f n)). Qed.
Lemma lem295332 {A : Type'} (x : A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term497 A x _6610 P R f n) = (term838 A x _6610 P R f n).
Proof. exact (@lem17265 (term459 A P R f n x) (term496 A _6610 P R f n)). Qed.
Lemma lem295333 {A : Type'} (x : A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term497 A x _6610 P R f n) = (term839 A x _6610 P R f n).
Proof. exact (TRANS (@lem295332 A x _6610 P R f n) (@lem295331 A x _6610 P R f n)). Qed.
Lemma lem295334 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term498 A _6610 P R f n) = (term840 A _6610 P R f n).
Proof. exact (fun_ext (fun x : A => @lem295333 A x _6610 P R f n)). Qed.
Lemma lem295335 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem295336 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term499 A _6610 P R f n) = (term841 A _6610 P R f n).
Proof. exact (MK_COMB (@lem295335 A) (@lem295334 A _6610 P R f n)). Qed.
Lemma lem295337 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term501 A _6610 P R f) = (term842 A _6610 P R f).
Proof. exact (fun_ext (fun n : nat => @lem295336 A _6610 P R f n)). Qed.
Lemma lem295338 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem295339 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term502 A _6610 P R f) = (term843 A _6610 P R f).
Proof. exact (MK_COMB (@lem295338) (@lem295337 A _6610 P R f)). Qed.
Lemma lem295340 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) : (term504 A _6610 P R) = (term844 A _6610 P R).
Proof. exact (fun_ext (fun f : nat -> A => @lem295339 A _6610 P R f)). Qed.
Lemma lem295341 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem295342 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) : (term505 A _6610 P R) = (term845 A _6610 P R).
Proof. exact (MK_COMB (@lem295341 A) (@lem295340 A _6610 P R)). Qed.
Lemma lem295343 {A : Type'} (_6610 : type943 A) (P : type1597 A) : (term507 A _6610 P) = (term846 A _6610 P).
Proof. exact (fun_ext (fun R : type1594 A => @lem295342 A _6610 P R)). Qed.
Lemma lem295344 {A : Type'} : (@all (nat -> A -> A -> Prop)) = (@all (nat -> A -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> A -> Prop))). Qed.
Lemma lem295345 {A : Type'} (_6610 : type943 A) (P : type1597 A) : (term508 A _6610 P) = (term847 A _6610 P).
Proof. exact (MK_COMB (@lem295344 A) (@lem295343 A _6610 P)). Qed.
Lemma lem295346 {A : Type'} (_6610 : type943 A) : (term510 A _6610) = (term848 A _6610).
Proof. exact (fun_ext (fun P : type1597 A => @lem295345 A _6610 P)). Qed.
Lemma lem295347 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem295348 {A : Type'} (_6610 : type943 A) : (term511 A _6610) = (term849 A _6610).
Proof. exact (MK_COMB (@lem295347 A) (@lem295346 A _6610)). Qed.
Lemma lem295386 {A : Type'} (P : A -> Prop) (Q : Prop) : (term850 A P Q) = (term851 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem295387 {A : Type'} (P : A -> Prop) (Q : Prop) : (term850 A P Q) = (term851 A P Q).
Proof. exact (@lem295386 A P Q). Qed.
Lemma lem295388 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term852 A _6610 P R f n) = (term853 A _6610 P R f n).
Proof. exact (@lem295387 A (term854 A P R f n) (term496 A _6610 P R f n)). Qed.
Lemma lem295389 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (x : A) : (term855 A P R f n x) = (term833 A P R f n x).
Proof. exact (eq_refl (term855 A P R f n x)). Qed.
Lemma lem295390 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem295391 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (x : A) : (term856 A P R f n x) = (term837 A P R f n x).
Proof. exact (MK_COMB (@lem295390) (@lem295389 A P R f n x)). Qed.
Lemma lem295392 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term496 A _6610 P R f n) = (term496 A _6610 P R f n).
Proof. exact (eq_refl (term496 A _6610 P R f n)). Qed.
Lemma lem295393 {A : Type'} (x : A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term857 A x _6610 P R f n) = (term839 A x _6610 P R f n).
Proof. exact (MK_COMB (@lem295391 A P R f n x) (@lem295392 A _6610 P R f n)). Qed.
Lemma lem295394 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term858 A _6610 P R f n) = (term840 A _6610 P R f n).
Proof. exact (fun_ext (fun x : A => @lem295393 A x _6610 P R f n)). Qed.
Lemma lem295395 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem295396 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term852 A _6610 P R f n) = (term841 A _6610 P R f n).
Proof. exact (MK_COMB (@lem295395 A) (@lem295394 A _6610 P R f n)). Qed.
Lemma lem295397 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem295398 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term859 A _6610 P R f n) = (term860 A _6610 P R f n).
Proof. exact (MK_COMB (@lem295397) (@lem295396 A _6610 P R f n)). Qed.
Lemma lem295399 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (x : A) : (term855 A P R f n x) = (term833 A P R f n x).
Proof. exact (eq_refl (term855 A P R f n x)). Qed.
Lemma lem295400 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term861 A P R f n) = (term854 A P R f n).
Proof. exact (fun_ext (fun x : A => @lem295399 A P R f n x)). Qed.
Lemma lem295401 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem295402 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term862 A P R f n) = (term863 A P R f n).
Proof. exact (MK_COMB (@lem295401 A) (@lem295400 A P R f n)). Qed.
Lemma lem295403 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem295404 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term864 A P R f n) = (term865 A P R f n).
Proof. exact (MK_COMB (@lem295403) (@lem295402 A P R f n)). Qed.
Lemma lem295405 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term496 A _6610 P R f n) = (term496 A _6610 P R f n).
Proof. exact (eq_refl (term496 A _6610 P R f n)). Qed.
Lemma lem295406 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term853 A _6610 P R f n) = (term866 A _6610 P R f n).
Proof. exact (MK_COMB (@lem295404 A P R f n) (@lem295405 A _6610 P R f n)). Qed.
Lemma lem295407 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : ((term852 A _6610 P R f n) = (term853 A _6610 P R f n)) = ((term841 A _6610 P R f n) = (term866 A _6610 P R f n)).
Proof. exact (MK_COMB (@lem295398 A _6610 P R f n) (@lem295406 A _6610 P R f n)). Qed.
Lemma lem295408 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term841 A _6610 P R f n) = (term866 A _6610 P R f n).
Proof. exact (EQ_MP (@lem295407 A _6610 P R f n) (@lem295388 A _6610 P R f n)). Qed.
Lemma lem295457 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term842 A _6610 P R f) = (term867 A _6610 P R f).
Proof. exact (fun_ext (fun n : nat => @lem295408 A _6610 P R f n)). Qed.
Lemma lem295458 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem295459 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term843 A _6610 P R f) = (term868 A _6610 P R f).
Proof. exact (MK_COMB (@lem295458) (@lem295457 A _6610 P R f)). Qed.
Lemma lem295508 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) : (term844 A _6610 P R) = (term869 A _6610 P R).
Proof. exact (fun_ext (fun f : nat -> A => @lem295459 A _6610 P R f)). Qed.
Lemma lem295509 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem295510 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) : (term845 A _6610 P R) = (term870 A _6610 P R).
Proof. exact (MK_COMB (@lem295509 A) (@lem295508 A _6610 P R)). Qed.
Lemma lem295515 {A : Type'} (_6610 : type943 A) (P : type1597 A) : (term846 A _6610 P) = (term871 A _6610 P).
Proof. exact (fun_ext (fun R : type1594 A => @lem295510 A _6610 P R)). Qed.
Lemma lem295516 {A : Type'} : (@all (nat -> A -> A -> Prop)) = (@all (nat -> A -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> A -> Prop))). Qed.
Lemma lem295517 {A : Type'} (_6610 : type943 A) (P : type1597 A) : (term847 A _6610 P) = (term872 A _6610 P).
Proof. exact (MK_COMB (@lem295516 A) (@lem295515 A _6610 P)). Qed.
Lemma lem295522 {A : Type'} (_6610 : type943 A) : (term848 A _6610) = (term873 A _6610).
Proof. exact (fun_ext (fun P : type1597 A => @lem295517 A _6610 P)). Qed.
Lemma lem295523 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem295530 {A : Type'} (_6610 : type943 A) : (term849 A _6610) = (term874 A _6610).
Proof. exact (MK_COMB (@lem295523 A) (@lem295522 A _6610)). Qed.
Lemma lem295531 {A : Type'} (_6610 : type943 A) : (term511 A _6610) = (term874 A _6610).
Proof. exact (TRANS (@lem295348 A _6610) (@lem295530 A _6610)). Qed.
Lemma lem295532 {A : Type'} (_6610 : type943 A) (h1 : term511 A _6610) : term874 A _6610.
Proof. exact (EQ_MP (@lem295531 A _6610) (@lem295306 A _6610 h1)). Qed.
Lemma lem295544 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) (y : A) : (term561 A P R n x y) = (term561 A P R n x y).
Proof. exact (eq_refl (term561 A P R n x y)). Qed.
Lemma lem295545 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term562 A P R n x) = (term562 A P R n x).
Proof. exact (fun_ext (fun y : A => @lem295544 A P R n x y)). Qed.
Lemma lem295546 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem295547 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term563 A P R n x) = (term563 A P R n x).
Proof. exact (MK_COMB (@lem295546 A) (@lem295545 A P R n x)). Qed.
Lemma lem295549 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (term569 A P n x) = (term569 A P n x).
Proof. exact (eq_refl (term569 A P n x)). Qed.
Lemma lem295550 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term570 A P R n x) = (term570 A P R n x).
Proof. exact (MK_COMB (@lem295549 A P n x) (@lem295547 A P R n x)). Qed.
Lemma lem295551 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term565 A P R n x) = (term570 A P R n x).
Proof. exact (@lem17265 (P n x) (term563 A P R n x)). Qed.
Lemma lem295552 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term565 A P R n x) = (term570 A P R n x).
Proof. exact (TRANS (@lem295551 A P R n x) (@lem295550 A P R n x)). Qed.
Lemma lem295553 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term566 A P R n) = (term571 A P R n).
Proof. exact (fun_ext (fun x : A => @lem295552 A P R n x)). Qed.
Lemma lem295554 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem295555 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term567 A P R n) = (term572 A P R n).
Proof. exact (MK_COMB (@lem295554 A) (@lem295553 A P R n)). Qed.
Lemma lem295556 {A : Type'} (P : type1597 A) (R : type1594 A) : (term568 A P R) = (term573 A P R).
Proof. exact (fun_ext (fun n : nat => @lem295555 A P R n)). Qed.
Lemma lem295557 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem295558 {A : Type'} (P : type1597 A) (R : type1594 A) : (term312 A P R) = (term574 A P R).
Proof. exact (MK_COMB (@lem295557) (@lem295556 A P R)). Qed.
Lemma lem295661 {A : Type'} (P : Prop) (Q : A -> Prop) : (term69 A P Q) = (term70 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem295662 {A : Type'} (P : Prop) (Q : A -> Prop) : (term69 A P Q) = (term70 A P Q).
Proof. exact (@lem295661 A P Q). Qed.
Lemma lem295663 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term575 A P R n x) = (term576 A P R n x).
Proof. exact (@lem295662 A (term577 A P n x) (term562 A P R n x)). Qed.
Lemma lem295664 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) (y : A) : (term578 A P R n x y) = (term561 A P R n x y).
Proof. exact (eq_refl (term578 A P R n x y)). Qed.
Lemma lem295665 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term579 A P R n x) = (term562 A P R n x).
Proof. exact (fun_ext (fun y : A => @lem295664 A P R n x y)). Qed.
Lemma lem295666 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem295667 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term580 A P R n x) = (term563 A P R n x).
Proof. exact (MK_COMB (@lem295666 A) (@lem295665 A P R n x)). Qed.
Lemma lem295668 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (term569 A P n x) = (term569 A P n x).
Proof. exact (eq_refl (term569 A P n x)). Qed.
Lemma lem295669 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term575 A P R n x) = (term570 A P R n x).
Proof. exact (MK_COMB (@lem295668 A P n x) (@lem295667 A P R n x)). Qed.
Lemma lem295670 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem295671 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term581 A P R n x) = (term582 A P R n x).
Proof. exact (MK_COMB (@lem295670) (@lem295669 A P R n x)). Qed.
Lemma lem295672 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) (y : A) : (term578 A P R n x y) = (term561 A P R n x y).
Proof. exact (eq_refl (term578 A P R n x y)). Qed.
Lemma lem295673 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (term569 A P n x) = (term569 A P n x).
Proof. exact (eq_refl (term569 A P n x)). Qed.
Lemma lem295674 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) (y : A) : (term583 A P R n x y) = (term584 A P R n x y).
Proof. exact (MK_COMB (@lem295673 A P n x) (@lem295672 A P R n x y)). Qed.
Lemma lem295675 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term585 A P R n x) = (term586 A P R n x).
Proof. exact (fun_ext (fun y : A => @lem295674 A P R n x y)). Qed.
Lemma lem295676 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem295677 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term576 A P R n x) = (term587 A P R n x).
Proof. exact (MK_COMB (@lem295676 A) (@lem295675 A P R n x)). Qed.
Lemma lem295678 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : ((term575 A P R n x) = (term576 A P R n x)) = ((term570 A P R n x) = (term587 A P R n x)).
Proof. exact (MK_COMB (@lem295671 A P R n x) (@lem295677 A P R n x)). Qed.
Lemma lem295679 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term570 A P R n x) = (term587 A P R n x).
Proof. exact (EQ_MP (@lem295678 A P R n x) (@lem295663 A P R n x)). Qed.
Lemma lem295680 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term571 A P R n) = (term588 A P R n).
Proof. exact (fun_ext (fun x : A => @lem295679 A P R n x)). Qed.
Lemma lem295681 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem295682 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term572 A P R n) = (term589 A P R n).
Proof. exact (MK_COMB (@lem295681 A) (@lem295680 A P R n)). Qed.
Lemma lem295684 {A B : Type'} (P : type1413 A B) : (term160 A B P) = (term161 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem295685 {A : Type'} (P : type1402 A) : (term590 A P) = (term591 A P).
Proof. exact (@lem295684 A A P). Qed.
Lemma lem295686 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term592 A P R n) = (term593 A P R n).
Proof. exact (@lem295685 A (term594 A P R n)). Qed.
Lemma lem295687 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term595 A P R n x) = (term586 A P R n x).
Proof. exact (eq_refl (term595 A P R n x)). Qed.
Lemma lem295688 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem295689 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) (y : A) : (term596 A P R n x y) = (term597 A P R n x y).
Proof. exact (MK_COMB (@lem295687 A P R n x) (@lem295688 A y)). Qed.
Lemma lem295690 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) (y : A) : (term597 A P R n x y) = (term584 A P R n x y).
Proof. exact (eq_refl (term597 A P R n x y)). Qed.
Lemma lem295691 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) (y : A) : (term596 A P R n x y) = (term584 A P R n x y).
Proof. exact (TRANS (@lem295689 A P R n x y) (@lem295690 A P R n x y)). Qed.
Lemma lem295692 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term598 A P R n x) = (term586 A P R n x).
Proof. exact (fun_ext (fun y : A => @lem295691 A P R n x y)). Qed.
Lemma lem295693 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem295694 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term599 A P R n x) = (term587 A P R n x).
Proof. exact (MK_COMB (@lem295693 A) (@lem295692 A P R n x)). Qed.
Lemma lem295695 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term600 A P R n) = (term588 A P R n).
Proof. exact (fun_ext (fun x : A => @lem295694 A P R n x)). Qed.
Lemma lem295696 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem295697 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term592 A P R n) = (term589 A P R n).
Proof. exact (MK_COMB (@lem295696 A) (@lem295695 A P R n)). Qed.
Lemma lem295698 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem295699 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term601 A P R n) = (term602 A P R n).
Proof. exact (MK_COMB (@lem295698) (@lem295697 A P R n)). Qed.
Lemma lem295700 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term595 A P R n x) = (term586 A P R n x).
Proof. exact (eq_refl (term595 A P R n x)). Qed.
Lemma lem295701 {A : Type'} (y : A -> A) (x : A) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem295702 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (y : A -> A) (x : A) : (term603 A P R n y x) = (term604 A P R n y x).
Proof. exact (MK_COMB (@lem295700 A P R n x) (@lem295701 A y x)). Qed.
Lemma lem295703 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (y : A -> A) (x : A) : (term604 A P R n y x) = (term605 A P R n y x).
Proof. exact (eq_refl (term604 A P R n y x)). Qed.
Lemma lem295704 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (y : A -> A) (x : A) : (term603 A P R n y x) = (term605 A P R n y x).
Proof. exact (TRANS (@lem295702 A P R n y x) (@lem295703 A P R n y x)). Qed.
Lemma lem295705 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (y : A -> A) : (term606 A P R n y) = (term607 A P R n y).
Proof. exact (fun_ext (fun x : A => @lem295704 A P R n y x)). Qed.
Lemma lem295706 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem295707 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (y : A -> A) : (term608 A P R n y) = (term609 A P R n y).
Proof. exact (MK_COMB (@lem295706 A) (@lem295705 A P R n y)). Qed.
Lemma lem295708 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term610 A P R n) = (term611 A P R n).
Proof. exact (fun_ext (fun y : A -> A => @lem295707 A P R n y)). Qed.
Lemma lem295709 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem295710 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term593 A P R n) = (term612 A P R n).
Proof. exact (MK_COMB (@lem295709 A) (@lem295708 A P R n)). Qed.
Lemma lem295711 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : ((term592 A P R n) = (term593 A P R n)) = ((term589 A P R n) = (term612 A P R n)).
Proof. exact (MK_COMB (@lem295699 A P R n) (@lem295710 A P R n)). Qed.
Lemma lem295712 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term589 A P R n) = (term612 A P R n).
Proof. exact (EQ_MP (@lem295711 A P R n) (@lem295686 A P R n)). Qed.
Lemma lem295713 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term572 A P R n) = (term612 A P R n).
Proof. exact (TRANS (@lem295682 A P R n) (@lem295712 A P R n)). Qed.
Lemma lem295714 {A : Type'} (P : type1597 A) (R : type1594 A) : (term573 A P R) = (term613 A P R).
Proof. exact (fun_ext (fun n : nat => @lem295713 A P R n)). Qed.
Lemma lem295715 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem295716 {A : Type'} (P : type1597 A) (R : type1594 A) : (term574 A P R) = (term614 A P R).
Proof. exact (MK_COMB (@lem295715) (@lem295714 A P R)). Qed.
Lemma lem295718 {A B : Type'} (P : type1413 A B) : (term160 A B P) = (term161 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem295719 {A : Type'} (P : type1571 A) : (term615 A P) = (term616 A P).
Proof. exact (@lem295718 nat (A -> A) P). Qed.
Lemma lem295720 {A : Type'} (P : type1597 A) (R : type1594 A) : (term617 A P R) = (term618 A P R).
Proof. exact (@lem295719 A (term619 A P R)). Qed.
Lemma lem295721 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term620 A P R n) = (term611 A P R n).
Proof. exact (eq_refl (term620 A P R n)). Qed.
Lemma lem295722 {A : Type'} (y : A -> A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem295723 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (y : A -> A) : (term621 A P R n y) = (term622 A P R n y).
Proof. exact (MK_COMB (@lem295721 A P R n) (@lem295722 A y)). Qed.
Lemma lem295724 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (y : A -> A) : (term622 A P R n y) = (term609 A P R n y).
Proof. exact (eq_refl (term622 A P R n y)). Qed.
Lemma lem295725 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (y : A -> A) : (term621 A P R n y) = (term609 A P R n y).
Proof. exact (TRANS (@lem295723 A P R n y) (@lem295724 A P R n y)). Qed.
Lemma lem295726 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term623 A P R n) = (term611 A P R n).
Proof. exact (fun_ext (fun y : A -> A => @lem295725 A P R n y)). Qed.
Lemma lem295727 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem295728 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term624 A P R n) = (term612 A P R n).
Proof. exact (MK_COMB (@lem295727 A) (@lem295726 A P R n)). Qed.
Lemma lem295729 {A : Type'} (P : type1597 A) (R : type1594 A) : (term625 A P R) = (term613 A P R).
Proof. exact (fun_ext (fun n : nat => @lem295728 A P R n)). Qed.
Lemma lem295730 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem295731 {A : Type'} (P : type1597 A) (R : type1594 A) : (term617 A P R) = (term614 A P R).
Proof. exact (MK_COMB (@lem295730) (@lem295729 A P R)). Qed.
Lemma lem295732 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem295733 {A : Type'} (P : type1597 A) (R : type1594 A) : (term626 A P R) = (term627 A P R).
Proof. exact (MK_COMB (@lem295732) (@lem295731 A P R)). Qed.
Lemma lem295734 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term620 A P R n) = (term611 A P R n).
Proof. exact (eq_refl (term620 A P R n)). Qed.
Lemma lem295735 {A : Type'} (y : type1596 A) (n : nat) : (y n) = (y n).
Proof. exact (eq_refl (y n)). Qed.
Lemma lem295736 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (n : nat) : (term628 A P R y n) = (term629 A P R y n).
Proof. exact (MK_COMB (@lem295734 A P R n) (@lem295735 A y n)). Qed.
Lemma lem295737 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (n : nat) : (term629 A P R y n) = (term630 A P R y n).
Proof. exact (eq_refl (term629 A P R y n)). Qed.
Lemma lem295738 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (n : nat) : (term628 A P R y n) = (term630 A P R y n).
Proof. exact (TRANS (@lem295736 A P R y n) (@lem295737 A P R y n)). Qed.
Lemma lem295739 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) : (term631 A P R y) = (term632 A P R y).
Proof. exact (fun_ext (fun n : nat => @lem295738 A P R y n)). Qed.
Lemma lem295740 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem295741 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) : (term633 A P R y) = (term634 A P R y).
Proof. exact (MK_COMB (@lem295740) (@lem295739 A P R y)). Qed.
Lemma lem295742 {A : Type'} (P : type1597 A) (R : type1594 A) : (term635 A P R) = (term636 A P R).
Proof. exact (fun_ext (fun y : type1596 A => @lem295741 A P R y)). Qed.
Lemma lem295743 {A : Type'} : (@ex (nat -> A -> A)) = (@ex (nat -> A -> A)).
Proof. exact (eq_refl (@ex (nat -> A -> A))). Qed.
Lemma lem295744 {A : Type'} (P : type1597 A) (R : type1594 A) : (term618 A P R) = (term637 A P R).
Proof. exact (MK_COMB (@lem295743 A) (@lem295742 A P R)). Qed.
Lemma lem295745 {A : Type'} (P : type1597 A) (R : type1594 A) : ((term617 A P R) = (term618 A P R)) = ((term614 A P R) = (term637 A P R)).
Proof. exact (MK_COMB (@lem295733 A P R) (@lem295744 A P R)). Qed.
Lemma lem295746 {A : Type'} (P : type1597 A) (R : type1594 A) : (term614 A P R) = (term637 A P R).
Proof. exact (EQ_MP (@lem295745 A P R) (@lem295720 A P R)). Qed.
Lemma lem295748 {A : Type'} (P : type1597 A) (R : type1594 A) : (term574 A P R) = (term637 A P R).
Proof. exact (TRANS (@lem295716 A P R) (@lem295746 A P R)). Qed.
Lemma lem295749 {A : Type'} (P : type1597 A) (R : type1594 A) : (term312 A P R) = (term637 A P R).
Proof. exact (TRANS (@lem295558 A P R) (@lem295748 A P R)). Qed.
Lemma lem295750 {A : Type'} (P : type1597 A) (R : type1594 A) (h1 : term312 A P R) : term637 A P R.
Proof. exact (EQ_MP (@lem295749 A P R) (@lem295308 A P R h1)). Qed.
Lemma lem295757 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : ((term289 A f n) = (_6610 P R f n)) = ((term289 A f n) = (_6610 P R f n)).
Proof. exact (eq_refl ((term289 A f n) = (_6610 P R f n))). Qed.
Lemma lem295758 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term514 A _6610 P R f) = (term514 A _6610 P R f).
Proof. exact (fun_ext (fun n : nat => @lem295757 A _6610 P R f n)). Qed.
Lemma lem295759 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem295768 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term515 A _6610 P R f) = (term515 A _6610 P R f).
Proof. exact (MK_COMB (@lem295759) (@lem295758 A _6610 P R f)). Qed.
Lemma lem295769 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term515 A _6610 P R f) : term515 A _6610 P R f.
Proof. exact (EQ_MP (@lem295768 A _6610 P R f) (@lem295310 A _6610 P R f h1)). Qed.
Lemma lem295774 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) : (term459 A P R f n y) = (term459 A P R f n y).
Proof. exact (eq_refl (term459 A P R f n y)). Qed.
Lemma lem295775 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term436 A P R f n) = (term436 A P R f n).
Proof. exact (fun_ext (fun y : A => @lem295774 A P R f n y)). Qed.
Lemma lem295776 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem295829 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term435 A P R f n) = (term435 A P R f n).
Proof. exact (MK_COMB (@lem295776 A) (@lem295775 A P R f n)). Qed.
Lemma lem295830 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term435 A P R f n) : term435 A P R f n.
Proof. exact (EQ_MP (@lem295829 A P R f n) (@lem295311 A P R f n h1)). Qed.
Lemma lem295837 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) : (term875 A P R f n y) = (term876 A P R f n y).
Proof. exact (@lem17045 (term877 A P n y) (term878 A R f n y)). Qed.
Lemma lem295838 {A : Type'} (P : A -> Prop) : (term642 A P) = (term643 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem295839 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term767 A P R f n) = (term879 A P R f n).
Proof. exact (@lem295838 A (term831 A P R f n)). Qed.
Lemma lem295840 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) : (term880 A P R f n y) = (term830 A P R f n y).
Proof. exact (eq_refl (term880 A P R f n y)). Qed.
Lemma lem295841 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem295842 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) : (term881 A P R f n y) = (term875 A P R f n y).
Proof. exact (MK_COMB (@lem295841) (@lem295840 A P R f n y)). Qed.
Lemma lem295843 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) : (term881 A P R f n y) = (term876 A P R f n y).
Proof. exact (TRANS (@lem295842 A P R f n y) (@lem295837 A P R f n y)). Qed.
Lemma lem295844 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term882 A P R f n) = (term883 A P R f n).
Proof. exact (fun_ext (fun y : A => @lem295843 A P R f n y)). Qed.
Lemma lem295845 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem295846 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term879 A P R f n) = (term884 A P R f n).
Proof. exact (MK_COMB (@lem295845 A) (@lem295844 A P R f n)). Qed.
Lemma lem295899 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term767 A P R f n) = (term884 A P R f n).
Proof. exact (TRANS (@lem295839 A P R f n) (@lem295846 A P R f n)). Qed.
Lemma lem295900 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term767 A P R f n) : term884 A P R f n.
Proof. exact (EQ_MP (@lem295899 A P R f n) (@lem295316 A P R f n h1)). Qed.
Lemma lem295901 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term459 A P R f n y) : term459 A P R f n y.
Proof. exact (h1). Qed.
Lemma lem295902 {A : Type'} (P : type1597 A) (R : type1594 A) (y' : type1596 A) (h1 : term634 A P R y') : term634 A P R y'.
Proof. exact (h1). Qed.
Lemma lem295909 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem295910 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem295909 nat A f x). Qed.
Lemma lem295912 {A : Type'} (f : nat -> A) (n : nat) : (f n) = (@I (nat -> A) f n).
Proof. exact (@lem295910 A f n). Qed.
Lemma lem295923 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem295924 {A : Type'} (f : type943 A) (x : type1597 A) : (f x) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> (nat -> A) -> nat -> A) f x).
Proof. exact (@lem295923 (type1597 A) (type933 A) f x). Qed.
Lemma lem295925 {A : Type'} (_6610 : type943 A) (P : type1597 A) : (_6610 P) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> (nat -> A) -> nat -> A) _6610 P).
Proof. exact (@lem295924 A _6610 P). Qed.
Lemma lem295926 {A : Type'} (R : type1594 A) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem295927 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) : (_6610 P R) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> (nat -> A) -> nat -> A) _6610 P R).
Proof. exact (MK_COMB (@lem295925 A _6610 P) (@lem295926 A R)). Qed.
Lemma lem295929 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem295930 {A : Type'} (f : type933 A) (x : type1594 A) : (f x) = (@I ((nat -> A -> A -> Prop) -> (nat -> A) -> nat -> A) f x).
Proof. exact (@lem295929 (type1594 A) (type972 A) f x). Qed.
Lemma lem295931 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) : (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> (nat -> A) -> nat -> A) _6610 P R) = (term885 A _6610 P R).
Proof. exact (@lem295930 A (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> (nat -> A) -> nat -> A) _6610 P) R). Qed.
Lemma lem295932 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) : (_6610 P R) = (term885 A _6610 P R).
Proof. exact (TRANS (@lem295927 A _6610 P R) (@lem295931 A _6610 P R)). Qed.
Lemma lem295933 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem295934 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (_6610 P R f) = (term886 A _6610 P R f).
Proof. exact (MK_COMB (@lem295932 A _6610 P R) (@lem295933 A f)). Qed.
Lemma lem295936 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem295937 {A : Type'} (f : type972 A) (x : nat -> A) : (f x) = (@I ((nat -> A) -> nat -> A) f x).
Proof. exact (@lem295936 (nat -> A) (nat -> A) f x). Qed.
Lemma lem295938 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term886 A _6610 P R f) = (term887 A _6610 P R f).
Proof. exact (@lem295937 A (term885 A _6610 P R) f). Qed.
Lemma lem295939 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (_6610 P R f) = (term887 A _6610 P R f).
Proof. exact (TRANS (@lem295934 A _6610 P R f) (@lem295938 A _6610 P R f)). Qed.
Lemma lem295940 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem295941 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (_6610 P R f n) = (term888 A _6610 P R f n).
Proof. exact (MK_COMB (@lem295939 A _6610 P R f) (@lem295940 n)). Qed.
Lemma lem295943 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem295944 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem295943 nat A f x). Qed.
Lemma lem295945 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term888 A _6610 P R f n) = (term889 A _6610 P R f n).
Proof. exact (@lem295944 A (term887 A _6610 P R f) n). Qed.
Lemma lem295947 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (_6610 P R f n) = (term889 A _6610 P R f n).
Proof. exact (TRANS (@lem295941 A _6610 P R f n) (@lem295945 A _6610 P R f n)). Qed.
Lemma lem295948 {A : Type'} (R : type1594 A) (n : nat) : (R n) = (R n).
Proof. exact (eq_refl (R n)). Qed.
Lemma lem295949 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term341 A R f n) = (term890 A R f n).
Proof. exact (MK_COMB (@lem295948 A R n) (@lem295912 A f n)). Qed.
Lemma lem295950 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term495 A _6610 P R f n) = (term891 A _6610 P R f n).
Proof. exact (MK_COMB (@lem295949 A R f n) (@lem295947 A _6610 P R f n)). Qed.
Lemma lem295952 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem295953 {A : Type'} (f : type1594 A) (x : nat) : (f x) = (@I (nat -> A -> A -> Prop) f x).
Proof. exact (@lem295952 nat (type1402 A) f x). Qed.
Lemma lem295954 {A : Type'} (R : type1594 A) (n : nat) : (R n) = (@I (nat -> A -> A -> Prop) R n).
Proof. exact (@lem295953 A R n). Qed.
Lemma lem295955 {A : Type'} (f : nat -> A) (n : nat) : (@I (nat -> A) f n) = (@I (nat -> A) f n).
Proof. exact (eq_refl (@I (nat -> A) f n)). Qed.
Lemma lem295956 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term890 A R f n) = (term892 A R f n).
Proof. exact (MK_COMB (@lem295954 A R n) (@lem295955 A f n)). Qed.
Lemma lem295958 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem295959 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem295958 A (A -> Prop) f x). Qed.
Lemma lem295960 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term892 A R f n) = (term893 A R f n).
Proof. exact (@lem295959 A (@I (nat -> A -> A -> Prop) R n) (@I (nat -> A) f n)). Qed.
Lemma lem295961 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term890 A R f n) = (term893 A R f n).
Proof. exact (TRANS (@lem295956 A R f n) (@lem295960 A R f n)). Qed.
Lemma lem295962 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term889 A _6610 P R f n) = (term889 A _6610 P R f n).
Proof. exact (eq_refl (term889 A _6610 P R f n)). Qed.
Lemma lem295963 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term891 A _6610 P R f n) = (term894 A _6610 P R f n).
Proof. exact (MK_COMB (@lem295961 A R f n) (@lem295962 A _6610 P R f n)). Qed.
Lemma lem295965 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem295966 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem295965 A Prop f x). Qed.
Lemma lem295967 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term894 A _6610 P R f n) = (term895 A _6610 P R f n).
Proof. exact (@lem295966 A (term893 A R f n) (term889 A _6610 P R f n)). Qed.
Lemma lem295968 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term891 A _6610 P R f n) = (term895 A _6610 P R f n).
Proof. exact (TRANS (@lem295963 A _6610 P R f n) (@lem295967 A _6610 P R f n)). Qed.
Lemma lem295969 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term495 A _6610 P R f n) = (term895 A _6610 P R f n).
Proof. exact (TRANS (@lem295950 A _6610 P R f n) (@lem295968 A _6610 P R f n)). Qed.
Lemma lem295970 {A : Type'} (P : type1597 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem295975 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem295976 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem295975 nat nat f x). Qed.
Lemma lem295978 (n : nat) : (S n) = (@I (nat -> nat) S n).
Proof. exact (@lem295976 S n). Qed.
Lemma lem295989 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem295990 {A : Type'} (f : type943 A) (x : type1597 A) : (f x) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> (nat -> A) -> nat -> A) f x).
Proof. exact (@lem295989 (type1597 A) (type933 A) f x). Qed.
Lemma lem295991 {A : Type'} (_6610 : type943 A) (P : type1597 A) : (_6610 P) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> (nat -> A) -> nat -> A) _6610 P).
Proof. exact (@lem295990 A _6610 P). Qed.
Lemma lem295992 {A : Type'} (R : type1594 A) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem295993 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) : (_6610 P R) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> (nat -> A) -> nat -> A) _6610 P R).
Proof. exact (MK_COMB (@lem295991 A _6610 P) (@lem295992 A R)). Qed.
Lemma lem295995 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem295996 {A : Type'} (f : type933 A) (x : type1594 A) : (f x) = (@I ((nat -> A -> A -> Prop) -> (nat -> A) -> nat -> A) f x).
Proof. exact (@lem295995 (type1594 A) (type972 A) f x). Qed.
Lemma lem295997 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) : (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> (nat -> A) -> nat -> A) _6610 P R) = (term885 A _6610 P R).
Proof. exact (@lem295996 A (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> (nat -> A) -> nat -> A) _6610 P) R). Qed.
Lemma lem295998 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) : (_6610 P R) = (term885 A _6610 P R).
Proof. exact (TRANS (@lem295993 A _6610 P R) (@lem295997 A _6610 P R)). Qed.
Lemma lem295999 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem296000 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (_6610 P R f) = (term886 A _6610 P R f).
Proof. exact (MK_COMB (@lem295998 A _6610 P R) (@lem295999 A f)). Qed.
Lemma lem296002 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296003 {A : Type'} (f : type972 A) (x : nat -> A) : (f x) = (@I ((nat -> A) -> nat -> A) f x).
Proof. exact (@lem296002 (nat -> A) (nat -> A) f x). Qed.
Lemma lem296004 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term886 A _6610 P R f) = (term887 A _6610 P R f).
Proof. exact (@lem296003 A (term885 A _6610 P R) f). Qed.
Lemma lem296005 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (_6610 P R f) = (term887 A _6610 P R f).
Proof. exact (TRANS (@lem296000 A _6610 P R f) (@lem296004 A _6610 P R f)). Qed.
Lemma lem296006 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem296007 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (_6610 P R f n) = (term888 A _6610 P R f n).
Proof. exact (MK_COMB (@lem296005 A _6610 P R f) (@lem296006 n)). Qed.
Lemma lem296009 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296010 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem296009 nat A f x). Qed.
Lemma lem296011 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term888 A _6610 P R f n) = (term889 A _6610 P R f n).
Proof. exact (@lem296010 A (term887 A _6610 P R f) n). Qed.
Lemma lem296013 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (_6610 P R f n) = (term889 A _6610 P R f n).
Proof. exact (TRANS (@lem296007 A _6610 P R f n) (@lem296011 A _6610 P R f n)). Qed.
Lemma lem296014 {A : Type'} (P : type1597 A) (n : nat) : (term380 A P n) = (term692 A P n).
Proof. exact (MK_COMB (@lem295970 A P) (@lem295978 n)). Qed.
Lemma lem296015 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term493 A _6610 P R f n) = (term896 A _6610 P R f n).
Proof. exact (MK_COMB (@lem296014 A P n) (@lem296013 A _6610 P R f n)). Qed.
Lemma lem296017 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296018 {A : Type'} (f : type1597 A) (x : nat) : (f x) = (@I (nat -> A -> Prop) f x).
Proof. exact (@lem296017 nat (A -> Prop) f x). Qed.
Lemma lem296019 {A : Type'} (P : type1597 A) (n : nat) : (term692 A P n) = (term695 A P n).
Proof. exact (@lem296018 A P (@I (nat -> nat) S n)). Qed.
Lemma lem296020 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term889 A _6610 P R f n) = (term889 A _6610 P R f n).
Proof. exact (eq_refl (term889 A _6610 P R f n)). Qed.
Lemma lem296021 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term896 A _6610 P R f n) = (term897 A _6610 P R f n).
Proof. exact (MK_COMB (@lem296019 A P n) (@lem296020 A _6610 P R f n)). Qed.
Lemma lem296023 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296024 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem296023 A Prop f x). Qed.
Lemma lem296025 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term897 A _6610 P R f n) = (term898 A _6610 P R f n).
Proof. exact (@lem296024 A (term695 A P n) (term889 A _6610 P R f n)). Qed.
Lemma lem296026 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term896 A _6610 P R f n) = (term898 A _6610 P R f n).
Proof. exact (TRANS (@lem296021 A _6610 P R f n) (@lem296025 A _6610 P R f n)). Qed.
Lemma lem296027 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term493 A _6610 P R f n) = (term898 A _6610 P R f n).
Proof. exact (TRANS (@lem296015 A _6610 P R f n) (@lem296026 A _6610 P R f n)). Qed.
Lemma lem296028 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem296029 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term494 A _6610 P R f n) = (term899 A _6610 P R f n).
Proof. exact (MK_COMB (@lem296028) (@lem296027 A _6610 P R f n)). Qed.
Lemma lem296030 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term496 A _6610 P R f n) = (term900 A _6610 P R f n).
Proof. exact (MK_COMB (@lem296029 A _6610 P R f n) (@lem295969 A _6610 P R f n)). Qed.
Lemma lem296031 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem296038 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296039 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem296038 nat A f x). Qed.
Lemma lem296041 {A : Type'} (f : nat -> A) (n : nat) : (f n) = (@I (nat -> A) f n).
Proof. exact (@lem296039 A f n). Qed.
Lemma lem296042 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem296043 {A : Type'} (R : type1594 A) (n : nat) : (R n) = (R n).
Proof. exact (eq_refl (R n)). Qed.
Lemma lem296044 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term341 A R f n) = (term890 A R f n).
Proof. exact (MK_COMB (@lem296043 A R n) (@lem296041 A f n)). Qed.
Lemma lem296045 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) (x : A) : (term835 A R f n x) = (term901 A R f n x).
Proof. exact (MK_COMB (@lem296044 A R f n) (@lem296042 A x)). Qed.
Lemma lem296047 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296048 {A : Type'} (f : type1594 A) (x : nat) : (f x) = (@I (nat -> A -> A -> Prop) f x).
Proof. exact (@lem296047 nat (type1402 A) f x). Qed.
Lemma lem296049 {A : Type'} (R : type1594 A) (n : nat) : (R n) = (@I (nat -> A -> A -> Prop) R n).
Proof. exact (@lem296048 A R n). Qed.
Lemma lem296050 {A : Type'} (f : nat -> A) (n : nat) : (@I (nat -> A) f n) = (@I (nat -> A) f n).
Proof. exact (eq_refl (@I (nat -> A) f n)). Qed.
Lemma lem296051 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term890 A R f n) = (term892 A R f n).
Proof. exact (MK_COMB (@lem296049 A R n) (@lem296050 A f n)). Qed.
Lemma lem296053 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296054 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem296053 A (A -> Prop) f x). Qed.
Lemma lem296055 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term892 A R f n) = (term893 A R f n).
Proof. exact (@lem296054 A (@I (nat -> A -> A -> Prop) R n) (@I (nat -> A) f n)). Qed.
Lemma lem296056 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term890 A R f n) = (term893 A R f n).
Proof. exact (TRANS (@lem296051 A R f n) (@lem296055 A R f n)). Qed.
Lemma lem296057 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem296058 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) (x : A) : (term901 A R f n x) = (term902 A R f n x).
Proof. exact (MK_COMB (@lem296056 A R f n) (@lem296057 A x)). Qed.
Lemma lem296060 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296061 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem296060 A Prop f x). Qed.
Lemma lem296062 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) (x : A) : (term902 A R f n x) = (term903 A R f n x).
Proof. exact (@lem296061 A (term893 A R f n) x). Qed.
Lemma lem296063 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) (x : A) : (term901 A R f n x) = (term903 A R f n x).
Proof. exact (TRANS (@lem296058 A R f n x) (@lem296062 A R f n x)). Qed.
Lemma lem296064 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) (x : A) : (term835 A R f n x) = (term903 A R f n x).
Proof. exact (TRANS (@lem296045 A R f n x) (@lem296063 A R f n x)). Qed.
Lemma lem296065 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) (x : A) : (term904 A R f n x) = (term905 A R f n x).
Proof. exact (MK_COMB (@lem296031) (@lem296064 A R f n x)). Qed.
Lemma lem296066 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem296067 {A : Type'} (P : type1597 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem296072 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296073 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem296072 nat nat f x). Qed.
Lemma lem296075 (n : nat) : (S n) = (@I (nat -> nat) S n).
Proof. exact (@lem296073 S n). Qed.
Lemma lem296076 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem296077 {A : Type'} (P : type1597 A) (n : nat) : (term380 A P n) = (term692 A P n).
Proof. exact (MK_COMB (@lem296067 A P) (@lem296075 n)). Qed.
Lemma lem296078 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (term834 A P n x) = (term906 A P n x).
Proof. exact (MK_COMB (@lem296077 A P n) (@lem296076 A x)). Qed.
Lemma lem296080 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296081 {A : Type'} (f : type1597 A) (x : nat) : (f x) = (@I (nat -> A -> Prop) f x).
Proof. exact (@lem296080 nat (A -> Prop) f x). Qed.
Lemma lem296082 {A : Type'} (P : type1597 A) (n : nat) : (term692 A P n) = (term695 A P n).
Proof. exact (@lem296081 A P (@I (nat -> nat) S n)). Qed.
Lemma lem296083 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem296084 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (term906 A P n x) = (term907 A P n x).
Proof. exact (MK_COMB (@lem296082 A P n) (@lem296083 A x)). Qed.
Lemma lem296086 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296087 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem296086 A Prop f x). Qed.
Lemma lem296088 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (term907 A P n x) = (term908 A P n x).
Proof. exact (@lem296087 A (term695 A P n) x). Qed.
Lemma lem296089 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (term906 A P n x) = (term908 A P n x).
Proof. exact (TRANS (@lem296084 A P n x) (@lem296088 A P n x)). Qed.
Lemma lem296090 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (term834 A P n x) = (term908 A P n x).
Proof. exact (TRANS (@lem296078 A P n x) (@lem296089 A P n x)). Qed.
Lemma lem296091 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (term909 A P n x) = (term910 A P n x).
Proof. exact (MK_COMB (@lem296066) (@lem296090 A P n x)). Qed.
Lemma lem296092 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem296093 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (term911 A P n x) = (term912 A P n x).
Proof. exact (MK_COMB (@lem296092) (@lem296091 A P n x)). Qed.
Lemma lem296094 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (x : A) : (term833 A P R f n x) = (term913 A P R f n x).
Proof. exact (MK_COMB (@lem296093 A P n x) (@lem296065 A R f n x)). Qed.
Lemma lem296095 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term854 A P R f n) = (term914 A P R f n).
Proof. exact (fun_ext (fun x : A => @lem296094 A P R f n x)). Qed.
Lemma lem296096 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem296097 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term863 A P R f n) = (term915 A P R f n).
Proof. exact (MK_COMB (@lem296096 A) (@lem296095 A P R f n)). Qed.
Lemma lem296098 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem296099 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term865 A P R f n) = (term916 A P R f n).
Proof. exact (MK_COMB (@lem296098) (@lem296097 A P R f n)). Qed.
Lemma lem296100 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term866 A _6610 P R f n) = (term917 A _6610 P R f n).
Proof. exact (MK_COMB (@lem296099 A P R f n) (@lem296030 A _6610 P R f n)). Qed.
Lemma lem296101 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term867 A _6610 P R f) = (term918 A _6610 P R f).
Proof. exact (fun_ext (fun n : nat => @lem296100 A _6610 P R f n)). Qed.
Lemma lem296102 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem296103 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term868 A _6610 P R f) = (term919 A _6610 P R f).
Proof. exact (MK_COMB (@lem296102) (@lem296101 A _6610 P R f)). Qed.
Lemma lem296104 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) : (term869 A _6610 P R) = (term920 A _6610 P R).
Proof. exact (fun_ext (fun f : nat -> A => @lem296103 A _6610 P R f)). Qed.
Lemma lem296105 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem296106 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) : (term870 A _6610 P R) = (term921 A _6610 P R).
Proof. exact (MK_COMB (@lem296105 A) (@lem296104 A _6610 P R)). Qed.
Lemma lem296107 {A : Type'} (_6610 : type943 A) (P : type1597 A) : (term871 A _6610 P) = (term922 A _6610 P).
Proof. exact (fun_ext (fun R : type1594 A => @lem296106 A _6610 P R)). Qed.
Lemma lem296108 {A : Type'} : (@all (nat -> A -> A -> Prop)) = (@all (nat -> A -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> A -> Prop))). Qed.
Lemma lem296109 {A : Type'} (_6610 : type943 A) (P : type1597 A) : (term872 A _6610 P) = (term923 A _6610 P).
Proof. exact (MK_COMB (@lem296108 A) (@lem296107 A _6610 P)). Qed.
Lemma lem296110 {A : Type'} (_6610 : type943 A) : (term873 A _6610) = (term924 A _6610).
Proof. exact (fun_ext (fun P : type1597 A => @lem296109 A _6610 P)). Qed.
Lemma lem296111 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem296112 {A : Type'} (_6610 : type943 A) : (term874 A _6610) = (term925 A _6610).
Proof. exact (MK_COMB (@lem296111 A) (@lem296110 A _6610)). Qed.
Lemma lem296113 {A : Type'} (_6610 : type943 A) (h1 : term511 A _6610) : term925 A _6610.
Proof. exact (EQ_MP (@lem296112 A _6610) (@lem295532 A _6610 h1)). Qed.
Lemma lem296159 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem296160 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem296165 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296166 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem296165 nat nat f x). Qed.
Lemma lem296168 (n : nat) : (S n) = (@I (nat -> nat) S n).
Proof. exact (@lem296166 S n). Qed.
Lemma lem296169 {A : Type'} (f : nat -> A) (n : nat) : (term289 A f n) = (term926 A f n).
Proof. exact (MK_COMB (@lem296160 A f) (@lem296168 n)). Qed.
Lemma lem296171 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296172 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem296171 nat A f x). Qed.
Lemma lem296173 {A : Type'} (f : nat -> A) (n : nat) : (term926 A f n) = (term927 A f n).
Proof. exact (@lem296172 A f (@I (nat -> nat) S n)). Qed.
Lemma lem296174 {A : Type'} (f : nat -> A) (n : nat) : (term289 A f n) = (term927 A f n).
Proof. exact (TRANS (@lem296169 A f n) (@lem296173 A f n)). Qed.
Lemma lem296185 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296186 {A : Type'} (f : type943 A) (x : type1597 A) : (f x) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> (nat -> A) -> nat -> A) f x).
Proof. exact (@lem296185 (type1597 A) (type933 A) f x). Qed.
Lemma lem296187 {A : Type'} (_6610 : type943 A) (P : type1597 A) : (_6610 P) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> (nat -> A) -> nat -> A) _6610 P).
Proof. exact (@lem296186 A _6610 P). Qed.
Lemma lem296188 {A : Type'} (R : type1594 A) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem296189 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) : (_6610 P R) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> (nat -> A) -> nat -> A) _6610 P R).
Proof. exact (MK_COMB (@lem296187 A _6610 P) (@lem296188 A R)). Qed.
Lemma lem296191 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296192 {A : Type'} (f : type933 A) (x : type1594 A) : (f x) = (@I ((nat -> A -> A -> Prop) -> (nat -> A) -> nat -> A) f x).
Proof. exact (@lem296191 (type1594 A) (type972 A) f x). Qed.
Lemma lem296193 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) : (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> (nat -> A) -> nat -> A) _6610 P R) = (term885 A _6610 P R).
Proof. exact (@lem296192 A (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> (nat -> A) -> nat -> A) _6610 P) R). Qed.
Lemma lem296194 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) : (_6610 P R) = (term885 A _6610 P R).
Proof. exact (TRANS (@lem296189 A _6610 P R) (@lem296193 A _6610 P R)). Qed.
Lemma lem296195 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem296196 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (_6610 P R f) = (term886 A _6610 P R f).
Proof. exact (MK_COMB (@lem296194 A _6610 P R) (@lem296195 A f)). Qed.
Lemma lem296198 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296199 {A : Type'} (f : type972 A) (x : nat -> A) : (f x) = (@I ((nat -> A) -> nat -> A) f x).
Proof. exact (@lem296198 (nat -> A) (nat -> A) f x). Qed.
Lemma lem296200 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term886 A _6610 P R f) = (term887 A _6610 P R f).
Proof. exact (@lem296199 A (term885 A _6610 P R) f). Qed.
Lemma lem296201 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (_6610 P R f) = (term887 A _6610 P R f).
Proof. exact (TRANS (@lem296196 A _6610 P R f) (@lem296200 A _6610 P R f)). Qed.
Lemma lem296202 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem296203 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (_6610 P R f n) = (term888 A _6610 P R f n).
Proof. exact (MK_COMB (@lem296201 A _6610 P R f) (@lem296202 n)). Qed.
Lemma lem296205 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296206 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem296205 nat A f x). Qed.
Lemma lem296207 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term888 A _6610 P R f n) = (term889 A _6610 P R f n).
Proof. exact (@lem296206 A (term887 A _6610 P R f) n). Qed.
Lemma lem296209 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (_6610 P R f n) = (term889 A _6610 P R f n).
Proof. exact (TRANS (@lem296203 A _6610 P R f n) (@lem296207 A _6610 P R f n)). Qed.
Lemma lem296210 {A : Type'} (f : nat -> A) (n : nat) : (term302 A f n) = (term928 A f n).
Proof. exact (MK_COMB (@lem296159 A) (@lem296174 A f n)). Qed.
Lemma lem296211 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : ((term289 A f n) = (_6610 P R f n)) = ((term927 A f n) = (term889 A _6610 P R f n)).
Proof. exact (MK_COMB (@lem296210 A f n) (@lem296209 A _6610 P R f n)). Qed.
Lemma lem296212 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term514 A _6610 P R f) = (term929 A _6610 P R f).
Proof. exact (fun_ext (fun n : nat => @lem296211 A _6610 P R f n)). Qed.
Lemma lem296213 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem296214 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term515 A _6610 P R f) = (term930 A _6610 P R f).
Proof. exact (MK_COMB (@lem296213) (@lem296212 A _6610 P R f)). Qed.
Lemma lem296215 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term515 A _6610 P R f) : term930 A _6610 P R f.
Proof. exact (EQ_MP (@lem296214 A _6610 P R f) (@lem295769 A _6610 P R f h1)). Qed.
Lemma lem296216 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem296217 {A : Type'} (R : type1594 A) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem296222 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296223 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem296222 nat nat f x). Qed.
Lemma lem296225 (n : nat) : (S n) = (@I (nat -> nat) S n).
Proof. exact (@lem296223 S n). Qed.
Lemma lem296226 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem296231 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296232 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem296231 nat nat f x). Qed.
Lemma lem296234 (n : nat) : (S n) = (@I (nat -> nat) S n).
Proof. exact (@lem296232 S n). Qed.
Lemma lem296235 {A : Type'} (f : nat -> A) (n : nat) : (term289 A f n) = (term926 A f n).
Proof. exact (MK_COMB (@lem296226 A f) (@lem296234 n)). Qed.
Lemma lem296237 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296238 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem296237 nat A f x). Qed.
Lemma lem296239 {A : Type'} (f : nat -> A) (n : nat) : (term926 A f n) = (term927 A f n).
Proof. exact (@lem296238 A f (@I (nat -> nat) S n)). Qed.
Lemma lem296240 {A : Type'} (f : nat -> A) (n : nat) : (term289 A f n) = (term927 A f n).
Proof. exact (TRANS (@lem296235 A f n) (@lem296239 A f n)). Qed.
Lemma lem296241 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem296242 {A : Type'} (R : type1594 A) (n : nat) : (term931 A R n) = (term932 A R n).
Proof. exact (MK_COMB (@lem296217 A R) (@lem296225 n)). Qed.
Lemma lem296243 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term933 A R f n) = (term934 A R f n).
Proof. exact (MK_COMB (@lem296242 A R n) (@lem296240 A f n)). Qed.
Lemma lem296244 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) (y : A) : (term878 A R f n y) = (term935 A R f n y).
Proof. exact (MK_COMB (@lem296243 A R f n) (@lem296241 A y)). Qed.
Lemma lem296246 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296247 {A : Type'} (f : type1594 A) (x : nat) : (f x) = (@I (nat -> A -> A -> Prop) f x).
Proof. exact (@lem296246 nat (type1402 A) f x). Qed.
Lemma lem296248 {A : Type'} (R : type1594 A) (n : nat) : (term932 A R n) = (term936 A R n).
Proof. exact (@lem296247 A R (@I (nat -> nat) S n)). Qed.
Lemma lem296249 {A : Type'} (f : nat -> A) (n : nat) : (term927 A f n) = (term927 A f n).
Proof. exact (eq_refl (term927 A f n)). Qed.
Lemma lem296250 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term934 A R f n) = (term937 A R f n).
Proof. exact (MK_COMB (@lem296248 A R n) (@lem296249 A f n)). Qed.
Lemma lem296252 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296253 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem296252 A (A -> Prop) f x). Qed.
Lemma lem296254 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term937 A R f n) = (term938 A R f n).
Proof. exact (@lem296253 A (term936 A R n) (term927 A f n)). Qed.
Lemma lem296255 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term934 A R f n) = (term938 A R f n).
Proof. exact (TRANS (@lem296250 A R f n) (@lem296254 A R f n)). Qed.
Lemma lem296256 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem296257 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) (y : A) : (term935 A R f n y) = (term939 A R f n y).
Proof. exact (MK_COMB (@lem296255 A R f n) (@lem296256 A y)). Qed.
Lemma lem296259 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296260 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem296259 A Prop f x). Qed.
Lemma lem296261 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) (y : A) : (term939 A R f n y) = (term940 A R f n y).
Proof. exact (@lem296260 A (term938 A R f n) y). Qed.
Lemma lem296262 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) (y : A) : (term935 A R f n y) = (term940 A R f n y).
Proof. exact (TRANS (@lem296257 A R f n y) (@lem296261 A R f n y)). Qed.
Lemma lem296263 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) (y : A) : (term878 A R f n y) = (term940 A R f n y).
Proof. exact (TRANS (@lem296244 A R f n y) (@lem296262 A R f n y)). Qed.
Lemma lem296264 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) (y : A) : (term941 A R f n y) = (term942 A R f n y).
Proof. exact (MK_COMB (@lem296216) (@lem296263 A R f n y)). Qed.
Lemma lem296265 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem296266 {A : Type'} (P : type1597 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem296267 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem296272 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296273 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem296272 nat nat f x). Qed.
Lemma lem296275 (n : nat) : (S n) = (@I (nat -> nat) S n).
Proof. exact (@lem296273 S n). Qed.
Lemma lem296276 (n : nat) : (term943 n) = (term944 n).
Proof. exact (MK_COMB (@lem296267) (@lem296275 n)). Qed.
Lemma lem296278 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296279 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem296278 nat nat f x). Qed.
Lemma lem296280 (n : nat) : (term944 n) = (term945 n).
Proof. exact (@lem296279 S (@I (nat -> nat) S n)). Qed.
Lemma lem296281 (n : nat) : (term943 n) = (term945 n).
Proof. exact (TRANS (@lem296276 n) (@lem296280 n)). Qed.
Lemma lem296282 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem296283 {A : Type'} (P : type1597 A) (n : nat) : (term946 A P n) = (term947 A P n).
Proof. exact (MK_COMB (@lem296266 A P) (@lem296281 n)). Qed.
Lemma lem296284 {A : Type'} (P : type1597 A) (n : nat) (y : A) : (term877 A P n y) = (term948 A P n y).
Proof. exact (MK_COMB (@lem296283 A P n) (@lem296282 A y)). Qed.
Lemma lem296286 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296287 {A : Type'} (f : type1597 A) (x : nat) : (f x) = (@I (nat -> A -> Prop) f x).
Proof. exact (@lem296286 nat (A -> Prop) f x). Qed.
Lemma lem296288 {A : Type'} (P : type1597 A) (n : nat) : (term947 A P n) = (term949 A P n).
Proof. exact (@lem296287 A P (term945 n)). Qed.
Lemma lem296289 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem296290 {A : Type'} (P : type1597 A) (n : nat) (y : A) : (term948 A P n y) = (term950 A P n y).
Proof. exact (MK_COMB (@lem296288 A P n) (@lem296289 A y)). Qed.
Lemma lem296292 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296293 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem296292 A Prop f x). Qed.
Lemma lem296294 {A : Type'} (P : type1597 A) (n : nat) (y : A) : (term950 A P n y) = (term951 A P n y).
Proof. exact (@lem296293 A (term949 A P n) y). Qed.
Lemma lem296295 {A : Type'} (P : type1597 A) (n : nat) (y : A) : (term948 A P n y) = (term951 A P n y).
Proof. exact (TRANS (@lem296290 A P n y) (@lem296294 A P n y)). Qed.
Lemma lem296296 {A : Type'} (P : type1597 A) (n : nat) (y : A) : (term877 A P n y) = (term951 A P n y).
Proof. exact (TRANS (@lem296284 A P n y) (@lem296295 A P n y)). Qed.
Lemma lem296297 {A : Type'} (P : type1597 A) (n : nat) (y : A) : (term952 A P n y) = (term953 A P n y).
Proof. exact (MK_COMB (@lem296265) (@lem296296 A P n y)). Qed.
Lemma lem296298 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem296299 {A : Type'} (P : type1597 A) (n : nat) (y : A) : (term954 A P n y) = (term955 A P n y).
Proof. exact (MK_COMB (@lem296298) (@lem296297 A P n y)). Qed.
Lemma lem296300 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) : (term876 A P R f n y) = (term956 A P R f n y).
Proof. exact (MK_COMB (@lem296299 A P n y) (@lem296264 A R f n y)). Qed.
Lemma lem296301 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term883 A P R f n) = (term957 A P R f n).
Proof. exact (fun_ext (fun y : A => @lem296300 A P R f n y)). Qed.
Lemma lem296302 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem296303 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term884 A P R f n) = (term958 A P R f n).
Proof. exact (MK_COMB (@lem296302 A) (@lem296301 A P R f n)). Qed.
Lemma lem296304 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term767 A P R f n) : term958 A P R f n.
Proof. exact (EQ_MP (@lem296303 A P R f n) (@lem295900 A P R f n h1)). Qed.
Lemma lem296311 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296312 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem296311 nat A f x). Qed.
Lemma lem296314 {A : Type'} (f : nat -> A) (n : nat) : (f n) = (@I (nat -> A) f n).
Proof. exact (@lem296312 A f n). Qed.
Lemma lem296315 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem296316 {A : Type'} (R : type1594 A) (n : nat) : (R n) = (R n).
Proof. exact (eq_refl (R n)). Qed.
Lemma lem296317 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term341 A R f n) = (term890 A R f n).
Proof. exact (MK_COMB (@lem296316 A R n) (@lem296314 A f n)). Qed.
Lemma lem296318 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) (y : A) : (term835 A R f n y) = (term901 A R f n y).
Proof. exact (MK_COMB (@lem296317 A R f n) (@lem296315 A y)). Qed.
Lemma lem296320 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296321 {A : Type'} (f : type1594 A) (x : nat) : (f x) = (@I (nat -> A -> A -> Prop) f x).
Proof. exact (@lem296320 nat (type1402 A) f x). Qed.
Lemma lem296322 {A : Type'} (R : type1594 A) (n : nat) : (R n) = (@I (nat -> A -> A -> Prop) R n).
Proof. exact (@lem296321 A R n). Qed.
Lemma lem296323 {A : Type'} (f : nat -> A) (n : nat) : (@I (nat -> A) f n) = (@I (nat -> A) f n).
Proof. exact (eq_refl (@I (nat -> A) f n)). Qed.
Lemma lem296324 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term890 A R f n) = (term892 A R f n).
Proof. exact (MK_COMB (@lem296322 A R n) (@lem296323 A f n)). Qed.
Lemma lem296326 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296327 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem296326 A (A -> Prop) f x). Qed.
Lemma lem296328 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term892 A R f n) = (term893 A R f n).
Proof. exact (@lem296327 A (@I (nat -> A -> A -> Prop) R n) (@I (nat -> A) f n)). Qed.
Lemma lem296329 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term890 A R f n) = (term893 A R f n).
Proof. exact (TRANS (@lem296324 A R f n) (@lem296328 A R f n)). Qed.
Lemma lem296330 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem296331 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) (y : A) : (term901 A R f n y) = (term902 A R f n y).
Proof. exact (MK_COMB (@lem296329 A R f n) (@lem296330 A y)). Qed.
Lemma lem296333 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296334 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem296333 A Prop f x). Qed.
Lemma lem296335 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) (y : A) : (term902 A R f n y) = (term903 A R f n y).
Proof. exact (@lem296334 A (term893 A R f n) y). Qed.
Lemma lem296336 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) (y : A) : (term901 A R f n y) = (term903 A R f n y).
Proof. exact (TRANS (@lem296331 A R f n y) (@lem296335 A R f n y)). Qed.
Lemma lem296337 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) (y : A) : (term835 A R f n y) = (term903 A R f n y).
Proof. exact (TRANS (@lem296318 A R f n y) (@lem296336 A R f n y)). Qed.
Lemma lem296338 {A : Type'} (P : type1597 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem296343 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296344 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem296343 nat nat f x). Qed.
Lemma lem296346 (n : nat) : (S n) = (@I (nat -> nat) S n).
Proof. exact (@lem296344 S n). Qed.
Lemma lem296347 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem296348 {A : Type'} (P : type1597 A) (n : nat) : (term380 A P n) = (term692 A P n).
Proof. exact (MK_COMB (@lem296338 A P) (@lem296346 n)). Qed.
Lemma lem296349 {A : Type'} (P : type1597 A) (n : nat) (y : A) : (term834 A P n y) = (term906 A P n y).
Proof. exact (MK_COMB (@lem296348 A P n) (@lem296347 A y)). Qed.
Lemma lem296351 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296352 {A : Type'} (f : type1597 A) (x : nat) : (f x) = (@I (nat -> A -> Prop) f x).
Proof. exact (@lem296351 nat (A -> Prop) f x). Qed.
Lemma lem296353 {A : Type'} (P : type1597 A) (n : nat) : (term692 A P n) = (term695 A P n).
Proof. exact (@lem296352 A P (@I (nat -> nat) S n)). Qed.
Lemma lem296354 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem296355 {A : Type'} (P : type1597 A) (n : nat) (y : A) : (term906 A P n y) = (term907 A P n y).
Proof. exact (MK_COMB (@lem296353 A P n) (@lem296354 A y)). Qed.
Lemma lem296357 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296358 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem296357 A Prop f x). Qed.
Lemma lem296359 {A : Type'} (P : type1597 A) (n : nat) (y : A) : (term907 A P n y) = (term908 A P n y).
Proof. exact (@lem296358 A (term695 A P n) y). Qed.
Lemma lem296360 {A : Type'} (P : type1597 A) (n : nat) (y : A) : (term906 A P n y) = (term908 A P n y).
Proof. exact (TRANS (@lem296355 A P n y) (@lem296359 A P n y)). Qed.
Lemma lem296361 {A : Type'} (P : type1597 A) (n : nat) (y : A) : (term834 A P n y) = (term908 A P n y).
Proof. exact (TRANS (@lem296349 A P n y) (@lem296360 A P n y)). Qed.
Lemma lem296362 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem296363 {A : Type'} (P : type1597 A) (n : nat) (y : A) : (term959 A P n y) = (term960 A P n y).
Proof. exact (MK_COMB (@lem296362) (@lem296361 A P n y)). Qed.
Lemma lem296364 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) : (term459 A P R f n y) = (term961 A P R f n y).
Proof. exact (MK_COMB (@lem296363 A P n y) (@lem296337 A R f n y)). Qed.
Lemma lem296365 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term459 A P R f n y) : term961 A P R f n y.
Proof. exact (EQ_MP (@lem296364 A P R f n y) (@lem295901 A P R f n y h1)). Qed.
Lemma lem296375 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296376 {A : Type'} (f : type1596 A) (x : nat) : (f x) = (@I (nat -> A -> A) f x).
Proof. exact (@lem296375 nat (A -> A) f x). Qed.
Lemma lem296377 {A : Type'} (y' : type1596 A) (n : nat) : (y' n) = (@I (nat -> A -> A) y' n).
Proof. exact (@lem296376 A y' n). Qed.
Lemma lem296378 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem296379 {A : Type'} (y' : type1596 A) (n : nat) (x : A) : (y' n x) = (@I (nat -> A -> A) y' n x).
Proof. exact (MK_COMB (@lem296377 A y' n) (@lem296378 A x)). Qed.
Lemma lem296381 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296382 {A : Type'} (f : A -> A) (x : A) : (f x) = (@I (A -> A) f x).
Proof. exact (@lem296381 A A f x). Qed.
Lemma lem296383 {A : Type'} (y' : type1596 A) (n : nat) (x : A) : (@I (nat -> A -> A) y' n x) = (term686 A y' n x).
Proof. exact (@lem296382 A (@I (nat -> A -> A) y' n) x). Qed.
Lemma lem296385 {A : Type'} (y' : type1596 A) (n : nat) (x : A) : (y' n x) = (term686 A y' n x).
Proof. exact (TRANS (@lem296379 A y' n x) (@lem296383 A y' n x)). Qed.
Lemma lem296387 {A : Type'} (R : type1594 A) (n : nat) (x : A) : (R n x) = (R n x).
Proof. exact (eq_refl (R n x)). Qed.
Lemma lem296388 {A : Type'} (R : type1594 A) (y' : type1596 A) (n : nat) (x : A) : (term687 A R y' n x) = (term688 A R y' n x).
Proof. exact (MK_COMB (@lem296387 A R n x) (@lem296385 A y' n x)). Qed.
Lemma lem296390 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296391 {A : Type'} (f : type1594 A) (x : nat) : (f x) = (@I (nat -> A -> A -> Prop) f x).
Proof. exact (@lem296390 nat (type1402 A) f x). Qed.
Lemma lem296392 {A : Type'} (R : type1594 A) (n : nat) : (R n) = (@I (nat -> A -> A -> Prop) R n).
Proof. exact (@lem296391 A R n). Qed.
Lemma lem296393 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem296394 {A : Type'} (R : type1594 A) (n : nat) (x : A) : (R n x) = (@I (nat -> A -> A -> Prop) R n x).
Proof. exact (MK_COMB (@lem296392 A R n) (@lem296393 A x)). Qed.
Lemma lem296396 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296397 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem296396 A (A -> Prop) f x). Qed.
Lemma lem296398 {A : Type'} (R : type1594 A) (n : nat) (x : A) : (@I (nat -> A -> A -> Prop) R n x) = (term689 A R n x).
Proof. exact (@lem296397 A (@I (nat -> A -> A -> Prop) R n) x). Qed.
Lemma lem296399 {A : Type'} (R : type1594 A) (n : nat) (x : A) : (R n x) = (term689 A R n x).
Proof. exact (TRANS (@lem296394 A R n x) (@lem296398 A R n x)). Qed.
Lemma lem296400 {A : Type'} (y' : type1596 A) (n : nat) (x : A) : (term686 A y' n x) = (term686 A y' n x).
Proof. exact (eq_refl (term686 A y' n x)). Qed.
Lemma lem296401 {A : Type'} (R : type1594 A) (y' : type1596 A) (n : nat) (x : A) : (term688 A R y' n x) = (term690 A R y' n x).
Proof. exact (MK_COMB (@lem296399 A R n x) (@lem296400 A y' n x)). Qed.
Lemma lem296403 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296404 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem296403 A Prop f x). Qed.
Lemma lem296405 {A : Type'} (R : type1594 A) (y' : type1596 A) (n : nat) (x : A) : (term690 A R y' n x) = (term691 A R y' n x).
Proof. exact (@lem296404 A (term689 A R n x) (term686 A y' n x)). Qed.
Lemma lem296406 {A : Type'} (R : type1594 A) (y' : type1596 A) (n : nat) (x : A) : (term688 A R y' n x) = (term691 A R y' n x).
Proof. exact (TRANS (@lem296401 A R y' n x) (@lem296405 A R y' n x)). Qed.
Lemma lem296407 {A : Type'} (R : type1594 A) (y' : type1596 A) (n : nat) (x : A) : (term687 A R y' n x) = (term691 A R y' n x).
Proof. exact (TRANS (@lem296388 A R y' n x) (@lem296406 A R y' n x)). Qed.
Lemma lem296408 {A : Type'} (P : type1597 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem296413 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296414 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem296413 nat nat f x). Qed.
Lemma lem296416 (n : nat) : (S n) = (@I (nat -> nat) S n).
Proof. exact (@lem296414 S n). Qed.
Lemma lem296423 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296424 {A : Type'} (f : type1596 A) (x : nat) : (f x) = (@I (nat -> A -> A) f x).
Proof. exact (@lem296423 nat (A -> A) f x). Qed.
Lemma lem296425 {A : Type'} (y' : type1596 A) (n : nat) : (y' n) = (@I (nat -> A -> A) y' n).
Proof. exact (@lem296424 A y' n). Qed.
Lemma lem296426 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem296427 {A : Type'} (y' : type1596 A) (n : nat) (x : A) : (y' n x) = (@I (nat -> A -> A) y' n x).
Proof. exact (MK_COMB (@lem296425 A y' n) (@lem296426 A x)). Qed.
Lemma lem296429 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296430 {A : Type'} (f : A -> A) (x : A) : (f x) = (@I (A -> A) f x).
Proof. exact (@lem296429 A A f x). Qed.
Lemma lem296431 {A : Type'} (y' : type1596 A) (n : nat) (x : A) : (@I (nat -> A -> A) y' n x) = (term686 A y' n x).
Proof. exact (@lem296430 A (@I (nat -> A -> A) y' n) x). Qed.
Lemma lem296433 {A : Type'} (y' : type1596 A) (n : nat) (x : A) : (y' n x) = (term686 A y' n x).
Proof. exact (TRANS (@lem296427 A y' n x) (@lem296431 A y' n x)). Qed.
Lemma lem296434 {A : Type'} (P : type1597 A) (n : nat) : (term380 A P n) = (term692 A P n).
Proof. exact (MK_COMB (@lem296408 A P) (@lem296416 n)). Qed.
Lemma lem296435 {A : Type'} (P : type1597 A) (y' : type1596 A) (n : nat) (x : A) : (term693 A P y' n x) = (term694 A P y' n x).
Proof. exact (MK_COMB (@lem296434 A P n) (@lem296433 A y' n x)). Qed.
Lemma lem296437 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296438 {A : Type'} (f : type1597 A) (x : nat) : (f x) = (@I (nat -> A -> Prop) f x).
Proof. exact (@lem296437 nat (A -> Prop) f x). Qed.
Lemma lem296439 {A : Type'} (P : type1597 A) (n : nat) : (term692 A P n) = (term695 A P n).
Proof. exact (@lem296438 A P (@I (nat -> nat) S n)). Qed.
Lemma lem296440 {A : Type'} (y' : type1596 A) (n : nat) (x : A) : (term686 A y' n x) = (term686 A y' n x).
Proof. exact (eq_refl (term686 A y' n x)). Qed.
Lemma lem296441 {A : Type'} (P : type1597 A) (y' : type1596 A) (n : nat) (x : A) : (term694 A P y' n x) = (term696 A P y' n x).
Proof. exact (MK_COMB (@lem296439 A P n) (@lem296440 A y' n x)). Qed.
Lemma lem296443 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296444 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem296443 A Prop f x). Qed.
Lemma lem296445 {A : Type'} (P : type1597 A) (y' : type1596 A) (n : nat) (x : A) : (term696 A P y' n x) = (term697 A P y' n x).
Proof. exact (@lem296444 A (term695 A P n) (term686 A y' n x)). Qed.
Lemma lem296446 {A : Type'} (P : type1597 A) (y' : type1596 A) (n : nat) (x : A) : (term694 A P y' n x) = (term697 A P y' n x).
Proof. exact (TRANS (@lem296441 A P y' n x) (@lem296445 A P y' n x)). Qed.
Lemma lem296447 {A : Type'} (P : type1597 A) (y' : type1596 A) (n : nat) (x : A) : (term693 A P y' n x) = (term697 A P y' n x).
Proof. exact (TRANS (@lem296435 A P y' n x) (@lem296446 A P y' n x)). Qed.
Lemma lem296448 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem296449 {A : Type'} (P : type1597 A) (y' : type1596 A) (n : nat) (x : A) : (term698 A P y' n x) = (term699 A P y' n x).
Proof. exact (MK_COMB (@lem296448) (@lem296447 A P y' n x)). Qed.
Lemma lem296450 {A : Type'} (P : type1597 A) (R : type1594 A) (y' : type1596 A) (n : nat) (x : A) : (term700 A P R y' n x) = (term701 A P R y' n x).
Proof. exact (MK_COMB (@lem296449 A P y' n x) (@lem296407 A R y' n x)). Qed.
Lemma lem296451 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem296458 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296459 {A : Type'} (f : type1597 A) (x : nat) : (f x) = (@I (nat -> A -> Prop) f x).
Proof. exact (@lem296458 nat (A -> Prop) f x). Qed.
Lemma lem296460 {A : Type'} (P : type1597 A) (n : nat) : (P n) = (@I (nat -> A -> Prop) P n).
Proof. exact (@lem296459 A P n). Qed.
Lemma lem296461 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem296462 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (P n x) = (@I (nat -> A -> Prop) P n x).
Proof. exact (MK_COMB (@lem296460 A P n) (@lem296461 A x)). Qed.
Lemma lem296464 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem296465 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem296464 A Prop f x). Qed.
Lemma lem296466 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (@I (nat -> A -> Prop) P n x) = (term702 A P n x).
Proof. exact (@lem296465 A (@I (nat -> A -> Prop) P n) x). Qed.
Lemma lem296468 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (P n x) = (term702 A P n x).
Proof. exact (TRANS (@lem296462 A P n x) (@lem296466 A P n x)). Qed.
Lemma lem296469 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (term577 A P n x) = (term703 A P n x).
Proof. exact (MK_COMB (@lem296451) (@lem296468 A P n x)). Qed.
Lemma lem296470 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem296471 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (term569 A P n x) = (term704 A P n x).
Proof. exact (MK_COMB (@lem296470) (@lem296469 A P n x)). Qed.
Lemma lem296472 {A : Type'} (P : type1597 A) (R : type1594 A) (y' : type1596 A) (n : nat) (x : A) : (term705 A P R y' n x) = (term706 A P R y' n x).
Proof. exact (MK_COMB (@lem296471 A P n x) (@lem296450 A P R y' n x)). Qed.
Lemma lem296473 {A : Type'} (P : type1597 A) (R : type1594 A) (y' : type1596 A) (n : nat) : (term707 A P R y' n) = (term708 A P R y' n).
Proof. exact (fun_ext (fun x : A => @lem296472 A P R y' n x)). Qed.
Lemma lem296474 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem296475 {A : Type'} (P : type1597 A) (R : type1594 A) (y' : type1596 A) (n : nat) : (term630 A P R y' n) = (term709 A P R y' n).
Proof. exact (MK_COMB (@lem296474 A) (@lem296473 A P R y' n)). Qed.
Lemma lem296476 {A : Type'} (P : type1597 A) (R : type1594 A) (y' : type1596 A) : (term632 A P R y') = (term710 A P R y').
Proof. exact (fun_ext (fun n : nat => @lem296475 A P R y' n)). Qed.
Lemma lem296477 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem296478 {A : Type'} (P : type1597 A) (R : type1594 A) (y' : type1596 A) : (term634 A P R y') = (term711 A P R y').
Proof. exact (MK_COMB (@lem296477) (@lem296476 A P R y')). Qed.
Lemma lem296479 {A : Type'} (P : type1597 A) (R : type1594 A) (y' : type1596 A) (h1 : term634 A P R y') : term711 A P R y'.
Proof. exact (EQ_MP (@lem296478 A P R y') (@lem295902 A P R y' h1)). Qed.
Lemma lem296483 {A : Type'} (P : A -> Prop) (Q : Prop) : (term851 A P Q) = (term850 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem296484 {A : Type'} (P : A -> Prop) (Q : Prop) : (term851 A P Q) = (term850 A P Q).
Proof. exact (@lem296483 A P Q). Qed.
Lemma lem296485 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term962 A _6610 P R f n) = (term963 A _6610 P R f n).
Proof. exact (@lem296484 A (term914 A P R f n) (term900 A _6610 P R f n)). Qed.
Lemma lem296486 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (x : A) : (term964 A P R f n x) = (term913 A P R f n x).
Proof. exact (eq_refl (term964 A P R f n x)). Qed.
Lemma lem296487 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term965 A P R f n) = (term914 A P R f n).
Proof. exact (fun_ext (fun x : A => @lem296486 A P R f n x)). Qed.
Lemma lem296488 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem296489 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term966 A P R f n) = (term915 A P R f n).
Proof. exact (MK_COMB (@lem296488 A) (@lem296487 A P R f n)). Qed.
Lemma lem296490 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem296491 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term967 A P R f n) = (term916 A P R f n).
Proof. exact (MK_COMB (@lem296490) (@lem296489 A P R f n)). Qed.
Lemma lem296492 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term900 A _6610 P R f n) = (term900 A _6610 P R f n).
Proof. exact (eq_refl (term900 A _6610 P R f n)). Qed.
Lemma lem296493 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term962 A _6610 P R f n) = (term917 A _6610 P R f n).
Proof. exact (MK_COMB (@lem296491 A P R f n) (@lem296492 A _6610 P R f n)). Qed.
Lemma lem296494 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem296495 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term968 A _6610 P R f n) = (term969 A _6610 P R f n).
Proof. exact (MK_COMB (@lem296494) (@lem296493 A _6610 P R f n)). Qed.
Lemma lem296496 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (x : A) : (term964 A P R f n x) = (term913 A P R f n x).
Proof. exact (eq_refl (term964 A P R f n x)). Qed.
Lemma lem296497 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem296498 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (x : A) : (term970 A P R f n x) = (term971 A P R f n x).
Proof. exact (MK_COMB (@lem296497) (@lem296496 A P R f n x)). Qed.
Lemma lem296499 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term900 A _6610 P R f n) = (term900 A _6610 P R f n).
Proof. exact (eq_refl (term900 A _6610 P R f n)). Qed.
Lemma lem296500 {A : Type'} (x : A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term972 A x _6610 P R f n) = (term973 A x _6610 P R f n).
Proof. exact (MK_COMB (@lem296498 A P R f n x) (@lem296499 A _6610 P R f n)). Qed.
Lemma lem296501 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term974 A _6610 P R f n) = (term975 A _6610 P R f n).
Proof. exact (fun_ext (fun x : A => @lem296500 A x _6610 P R f n)). Qed.
Lemma lem296502 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem296503 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term963 A _6610 P R f n) = (term976 A _6610 P R f n).
Proof. exact (MK_COMB (@lem296502 A) (@lem296501 A _6610 P R f n)). Qed.
Lemma lem296504 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : ((term962 A _6610 P R f n) = (term963 A _6610 P R f n)) = ((term917 A _6610 P R f n) = (term976 A _6610 P R f n)).
Proof. exact (MK_COMB (@lem296495 A _6610 P R f n) (@lem296503 A _6610 P R f n)). Qed.
Lemma lem296505 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term917 A _6610 P R f n) = (term976 A _6610 P R f n).
Proof. exact (EQ_MP (@lem296504 A _6610 P R f n) (@lem296485 A _6610 P R f n)). Qed.
Lemma lem296506 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term918 A _6610 P R f) = (term977 A _6610 P R f).
Proof. exact (fun_ext (fun n : nat => @lem296505 A _6610 P R f n)). Qed.
Lemma lem296507 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem296508 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term919 A _6610 P R f) = (term978 A _6610 P R f).
Proof. exact (MK_COMB (@lem296507) (@lem296506 A _6610 P R f)). Qed.
Lemma lem296509 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) : (term920 A _6610 P R) = (term979 A _6610 P R).
Proof. exact (fun_ext (fun f : nat -> A => @lem296508 A _6610 P R f)). Qed.
Lemma lem296510 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem296511 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) : (term921 A _6610 P R) = (term980 A _6610 P R).
Proof. exact (MK_COMB (@lem296510 A) (@lem296509 A _6610 P R)). Qed.
Lemma lem296512 {A : Type'} (_6610 : type943 A) (P : type1597 A) : (term922 A _6610 P) = (term981 A _6610 P).
Proof. exact (fun_ext (fun R : type1594 A => @lem296511 A _6610 P R)). Qed.
Lemma lem296513 {A : Type'} : (@all (nat -> A -> A -> Prop)) = (@all (nat -> A -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> A -> Prop))). Qed.
Lemma lem296514 {A : Type'} (_6610 : type943 A) (P : type1597 A) : (term923 A _6610 P) = (term982 A _6610 P).
Proof. exact (MK_COMB (@lem296513 A) (@lem296512 A _6610 P)). Qed.
Lemma lem296515 {A : Type'} (_6610 : type943 A) : (term924 A _6610) = (term983 A _6610).
Proof. exact (fun_ext (fun P : type1597 A => @lem296514 A _6610 P)). Qed.
Lemma lem296516 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem296517 {A : Type'} (_6610 : type943 A) : (term925 A _6610) = (term984 A _6610).
Proof. exact (MK_COMB (@lem296516 A) (@lem296515 A _6610)). Qed.
Lemma lem296540 {A : Type'} (x : A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term973 A x _6610 P R f n) = (term985 A x _6610 P R f n).
Proof. exact (@lem19490 (term898 A _6610 P R f n) (term913 A P R f n x) (term895 A _6610 P R f n)). Qed.
Lemma lem296541 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term975 A _6610 P R f n) = (term986 A _6610 P R f n).
Proof. exact (fun_ext (fun x : A => @lem296540 A x _6610 P R f n)). Qed.
Lemma lem296542 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem296543 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term976 A _6610 P R f n) = (term987 A _6610 P R f n).
Proof. exact (MK_COMB (@lem296542 A) (@lem296541 A _6610 P R f n)). Qed.
Lemma lem296544 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term977 A _6610 P R f) = (term988 A _6610 P R f).
Proof. exact (fun_ext (fun n : nat => @lem296543 A _6610 P R f n)). Qed.
Lemma lem296545 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem296546 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term978 A _6610 P R f) = (term989 A _6610 P R f).
Proof. exact (MK_COMB (@lem296545) (@lem296544 A _6610 P R f)). Qed.
Lemma lem296547 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) : (term979 A _6610 P R) = (term990 A _6610 P R).
Proof. exact (fun_ext (fun f : nat -> A => @lem296546 A _6610 P R f)). Qed.
Lemma lem296548 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem296549 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) : (term980 A _6610 P R) = (term991 A _6610 P R).
Proof. exact (MK_COMB (@lem296548 A) (@lem296547 A _6610 P R)). Qed.
Lemma lem296550 {A : Type'} (_6610 : type943 A) (P : type1597 A) : (term981 A _6610 P) = (term992 A _6610 P).
Proof. exact (fun_ext (fun R : type1594 A => @lem296549 A _6610 P R)). Qed.
Lemma lem296551 {A : Type'} : (@all (nat -> A -> A -> Prop)) = (@all (nat -> A -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> A -> Prop))). Qed.
Lemma lem296552 {A : Type'} (_6610 : type943 A) (P : type1597 A) : (term982 A _6610 P) = (term993 A _6610 P).
Proof. exact (MK_COMB (@lem296551 A) (@lem296550 A _6610 P)). Qed.
Lemma lem296553 {A : Type'} (_6610 : type943 A) : (term983 A _6610) = (term994 A _6610).
Proof. exact (fun_ext (fun P : type1597 A => @lem296552 A _6610 P)). Qed.
Lemma lem296554 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem296555 {A : Type'} (_6610 : type943 A) : (term984 A _6610) = (term995 A _6610).
Proof. exact (MK_COMB (@lem296554 A) (@lem296553 A _6610)). Qed.
Lemma lem296556 {A : Type'} (_6610 : type943 A) : (term925 A _6610) = (term995 A _6610).
Proof. exact (TRANS (@lem296517 A _6610) (@lem296555 A _6610)). Qed.
Lemma lem296557 {A : Type'} (_6610 : type943 A) (h1 : term511 A _6610) : term995 A _6610.
Proof. exact (EQ_MP (@lem296556 A _6610) (@lem296113 A _6610 h1)). Qed.
Lemma lem296567 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : ((term927 A f n) = (term889 A _6610 P R f n)) = ((term927 A f n) = (term889 A _6610 P R f n)).
Proof. exact (eq_refl ((term927 A f n) = (term889 A _6610 P R f n))). Qed.
Lemma lem296568 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term929 A _6610 P R f) = (term929 A _6610 P R f).
Proof. exact (fun_ext (fun n : nat => @lem296567 A _6610 P R f n)). Qed.
Lemma lem296569 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem296571 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term930 A _6610 P R f) = (term930 A _6610 P R f).
Proof. exact (MK_COMB (@lem296569) (@lem296568 A _6610 P R f)). Qed.
Lemma lem296572 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term515 A _6610 P R f) : term930 A _6610 P R f.
Proof. exact (EQ_MP (@lem296571 A _6610 P R f) (@lem296215 A _6610 P R f h1)). Qed.
Lemma lem296580 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) : (term956 A P R f n y) = (term956 A P R f n y).
Proof. exact (eq_refl (term956 A P R f n y)). Qed.
Lemma lem296581 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term957 A P R f n) = (term957 A P R f n).
Proof. exact (fun_ext (fun y : A => @lem296580 A P R f n y)). Qed.
Lemma lem296582 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem296584 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term958 A P R f n) = (term958 A P R f n).
Proof. exact (MK_COMB (@lem296582 A) (@lem296581 A P R f n)). Qed.
Lemma lem296585 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term767 A P R f n) : term958 A P R f n.
Proof. exact (EQ_MP (@lem296584 A P R f n) (@lem296304 A P R f n h1)). Qed.
Lemma lem296603 {A : Type'} (P : type1597 A) (R : type1594 A) (y' : type1596 A) (n : nat) (x : A) : (term706 A P R y' n x) = (term712 A P R y' n x).
Proof. exact (@lem19490 (term697 A P y' n x) (term703 A P n x) (term691 A R y' n x)). Qed.
Lemma lem296604 {A : Type'} (P : type1597 A) (R : type1594 A) (y' : type1596 A) (n : nat) : (term708 A P R y' n) = (term713 A P R y' n).
Proof. exact (fun_ext (fun x : A => @lem296603 A P R y' n x)). Qed.
Lemma lem296605 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem296606 {A : Type'} (P : type1597 A) (R : type1594 A) (y' : type1596 A) (n : nat) : (term709 A P R y' n) = (term714 A P R y' n).
Proof. exact (MK_COMB (@lem296605 A) (@lem296604 A P R y' n)). Qed.
Lemma lem296607 {A : Type'} (P : type1597 A) (R : type1594 A) (y' : type1596 A) : (term710 A P R y') = (term715 A P R y').
Proof. exact (fun_ext (fun n : nat => @lem296606 A P R y' n)). Qed.
Lemma lem296608 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem296610 {A : Type'} (P : type1597 A) (R : type1594 A) (y' : type1596 A) : (term711 A P R y') = (term716 A P R y').
Proof. exact (MK_COMB (@lem296608) (@lem296607 A P R y')). Qed.
Lemma lem296611 {A : Type'} (P : type1597 A) (R : type1594 A) (y' : type1596 A) (h1 : term634 A P R y') : term716 A P R y'.
Proof. exact (EQ_MP (@lem296610 A P R y') (@lem296479 A P R y' h1)). Qed.
Lemma lem296620 {A : Type'} (_6611 : type1597 A) (_6610 : type943 A) (h1 : term511 A _6610) : term996 A _6610 _6611.
Proof. exact (@lem296557 A _6610 h1 _6611). Qed.
Lemma lem296621 {A : Type'} (_6610 : type943 A) (_6611 : type1597 A) : (term996 A _6610 _6611) = (term993 A _6610 _6611).
Proof. exact (eq_refl (term996 A _6610 _6611)). Qed.
Lemma lem296622 {A : Type'} (_6611 : type1597 A) (_6610 : type943 A) (h1 : term511 A _6610) : term993 A _6610 _6611.
Proof. exact (EQ_MP (@lem296621 A _6610 _6611) (@lem296620 A _6611 _6610 h1)). Qed.
Lemma lem296623 {A : Type'} (_6611 : type1597 A) (_6612 : type1594 A) (_6610 : type943 A) (h1 : term511 A _6610) : term997 A _6610 _6611 _6612.
Proof. exact (@lem296622 A _6611 _6610 h1 _6612). Qed.
Lemma lem296624 {A : Type'} (_6610 : type943 A) (_6611 : type1597 A) (_6612 : type1594 A) : (term997 A _6610 _6611 _6612) = (term991 A _6610 _6611 _6612).
Proof. exact (eq_refl (term997 A _6610 _6611 _6612)). Qed.
Lemma lem296625 {A : Type'} (_6611 : type1597 A) (_6612 : type1594 A) (_6610 : type943 A) (h1 : term511 A _6610) : term991 A _6610 _6611 _6612.
Proof. exact (EQ_MP (@lem296624 A _6610 _6611 _6612) (@lem296623 A _6611 _6612 _6610 h1)). Qed.
Lemma lem296626 {A : Type'} (_6611 : type1597 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6610 : type943 A) (h1 : term511 A _6610) : term998 A _6610 _6611 _6612 _6613.
Proof. exact (@lem296625 A _6611 _6612 _6610 h1 _6613). Qed.
Lemma lem296627 {A : Type'} (_6610 : type943 A) (_6611 : type1597 A) (_6612 : type1594 A) (_6613 : nat -> A) : (term998 A _6610 _6611 _6612 _6613) = (term989 A _6610 _6611 _6612 _6613).
Proof. exact (eq_refl (term998 A _6610 _6611 _6612 _6613)). Qed.
Lemma lem296628 {A : Type'} (_6611 : type1597 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6610 : type943 A) (h1 : term511 A _6610) : term989 A _6610 _6611 _6612 _6613.
Proof. exact (EQ_MP (@lem296627 A _6610 _6611 _6612 _6613) (@lem296626 A _6611 _6612 _6613 _6610 h1)). Qed.
Lemma lem296629 {A : Type'} (_6611 : type1597 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6614 : nat) (_6610 : type943 A) (h1 : term511 A _6610) : term999 A _6610 _6611 _6612 _6613 _6614.
Proof. exact (@lem296628 A _6611 _6612 _6613 _6610 h1 _6614). Qed.
Lemma lem296630 {A : Type'} (_6610 : type943 A) (_6611 : type1597 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6614 : nat) : (term999 A _6610 _6611 _6612 _6613 _6614) = (term987 A _6610 _6611 _6612 _6613 _6614).
Proof. exact (eq_refl (term999 A _6610 _6611 _6612 _6613 _6614)). Qed.
Lemma lem296631 {A : Type'} (_6611 : type1597 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6614 : nat) (_6610 : type943 A) (h1 : term511 A _6610) : term987 A _6610 _6611 _6612 _6613 _6614.
Proof. exact (EQ_MP (@lem296630 A _6610 _6611 _6612 _6613 _6614) (@lem296629 A _6611 _6612 _6613 _6614 _6610 h1)). Qed.
Lemma lem296632 {A : Type'} (_6611 : type1597 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6614 : nat) (_6615 : A) (_6610 : type943 A) (h1 : term511 A _6610) : term1000 A _6610 _6611 _6612 _6613 _6614 _6615.
Proof. exact (@lem296631 A _6611 _6612 _6613 _6614 _6610 h1 _6615). Qed.
Lemma lem296633 {A : Type'} (_6615 : A) (_6610 : type943 A) (_6611 : type1597 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6614 : nat) : (term1000 A _6610 _6611 _6612 _6613 _6614 _6615) = (term985 A _6615 _6610 _6611 _6612 _6613 _6614).
Proof. exact (eq_refl (term1000 A _6610 _6611 _6612 _6613 _6614 _6615)). Qed.
Lemma lem296634 {A : Type'} (_6615 : A) (_6611 : type1597 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6614 : nat) (_6610 : type943 A) (h1 : term511 A _6610) : term985 A _6615 _6610 _6611 _6612 _6613 _6614.
Proof. exact (EQ_MP (@lem296633 A _6615 _6610 _6611 _6612 _6613 _6614) (@lem296632 A _6611 _6612 _6613 _6614 _6615 _6610 h1)). Qed.
Lemma lem296635 {A : Type'} (_6616 : nat) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term515 A _6610 P R f) : term1001 A _6610 P R f _6616.
Proof. exact (@lem296572 A _6610 P R f h1 _6616). Qed.
Lemma lem296636 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (_6616 : nat) : (term1001 A _6610 P R f _6616) = ((term927 A f _6616) = (term889 A _6610 P R f _6616)).
Proof. exact (eq_refl (term1001 A _6610 P R f _6616)). Qed.
Lemma lem296638 {A : Type'} (_6617 : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term767 A P R f n) : term1002 A P R f n _6617.
Proof. exact (@lem296585 A P R f n h1 _6617). Qed.
Lemma lem296639 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6617 : A) : (term1002 A P R f n _6617) = (term956 A P R f n _6617).
Proof. exact (eq_refl (term1002 A P R f n _6617)). Qed.
Lemma lem296641 {A : Type'} (_6618 : nat) (P : type1597 A) (R : type1594 A) (y' : type1596 A) (h1 : term634 A P R y') : term718 A P R y' _6618.
Proof. exact (@lem296611 A P R y' h1 _6618). Qed.
Lemma lem296642 {A : Type'} (P : type1597 A) (R : type1594 A) (y' : type1596 A) (_6618 : nat) : (term718 A P R y' _6618) = (term714 A P R y' _6618).
Proof. exact (eq_refl (term718 A P R y' _6618)). Qed.
Lemma lem296643 {A : Type'} (_6618 : nat) (P : type1597 A) (R : type1594 A) (y' : type1596 A) (h1 : term634 A P R y') : term714 A P R y' _6618.
Proof. exact (EQ_MP (@lem296642 A P R y' _6618) (@lem296641 A _6618 P R y' h1)). Qed.
Lemma lem296644 {A : Type'} (_6618 : nat) (_6619 : A) (P : type1597 A) (R : type1594 A) (y' : type1596 A) (h1 : term634 A P R y') : term719 A P R y' _6618 _6619.
Proof. exact (@lem296643 A _6618 P R y' h1 _6619). Qed.
Lemma lem296645 {A : Type'} (P : type1597 A) (R : type1594 A) (y' : type1596 A) (_6618 : nat) (_6619 : A) : (term719 A P R y' _6618 _6619) = (term712 A P R y' _6618 _6619).
Proof. exact (eq_refl (term719 A P R y' _6618 _6619)). Qed.
Lemma lem296646 {A : Type'} (_6618 : nat) (_6619 : A) (P : type1597 A) (R : type1594 A) (y' : type1596 A) (h1 : term634 A P R y') : term712 A P R y' _6618 _6619.
Proof. exact (EQ_MP (@lem296645 A P R y' _6618 _6619) (@lem296644 A _6618 _6619 P R y' h1)). Qed.
Lemma lem296650 {A : Type'} (_6615 : A) (_6611 : type1597 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6614 : nat) (_6610 : type943 A) (h1 : term511 A _6610) : term1003 A _6615 _6610 _6611 _6612 _6613 _6614.
Proof. exact (proj1 (@lem296634 A _6615 _6611 _6612 _6613 _6614 _6610 h1)). Qed.
Lemma lem296689 {A : Type'} (_6615 : A) (_6610 : type943 A) (_6611 : type1597 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6614 : nat) : (term1003 A _6615 _6610 _6611 _6612 _6613 _6614) = (term1004 A _6615 _6610 _6611 _6612 _6613 _6614).
Proof. exact (@lem290494 (term910 A _6611 _6614 _6615) (term905 A _6612 _6613 _6614 _6615) (term898 A _6610 _6611 _6612 _6613 _6614)). Qed.
Lemma lem296758 {A : Type'} (_6617 : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term767 A P R f n) : term956 A P R f n _6617.
Proof. exact (EQ_MP (@lem296639 A P R f n _6617) (@lem296638 A _6617 P R f n h1)). Qed.
Lemma lem296800 {A : Type'} (_6618 : nat) (_6619 : A) (P : type1597 A) (R : type1594 A) (y' : type1596 A) (h1 : term634 A P R y') : term726 A P y' _6618 _6619.
Proof. exact (proj1 (@lem296646 A _6618 _6619 P R y' h1)). Qed.
Lemma lem296814 {A : Type'} (_6618 : nat) (_6619 : A) (P : type1597 A) (R : type1594 A) (y' : type1596 A) (h1 : term634 A P R y') : term727 A P R y' _6618 _6619.
Proof. exact (proj2 (@lem296646 A _6618 _6619 P R y' h1)). Qed.
Lemma lem296828 {A : Type'} (_6615 : A) (_6611 : type1597 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6614 : nat) (_6610 : type943 A) (h1 : term511 A _6610) : term1004 A _6615 _6610 _6611 _6612 _6613 _6614.
Proof. exact (EQ_MP (@lem296689 A _6615 _6610 _6611 _6612 _6613 _6614) (@lem296650 A _6615 _6611 _6612 _6613 _6614 _6610 h1)). Qed.
Lemma lem296843 {A : Type'} : (@I (A -> Prop)) = (@I (A -> Prop)).
Proof. exact (eq_refl (@I (A -> Prop))). Qed.
Lemma lem296844 {A : Type'} (_6640 : A -> Prop) (_6642 : A -> Prop) (h1 : _6640 = _6642) : _6640 = _6642.
Proof. exact (h1). Qed.
Lemma lem296845 {A : Type'} (_6641 : A) (_6643 : A) (h1 : _6641 = _6643) : _6641 = _6643.
Proof. exact (h1). Qed.
Lemma lem296846 {A : Type'} (_6640 : A -> Prop) (_6642 : A -> Prop) (h1 : _6640 = _6642) : (@I (A -> Prop) _6640) = (@I (A -> Prop) _6642).
Proof. exact (MK_COMB (@lem296843 A) (@lem296844 A _6640 _6642 h1)). Qed.
Lemma lem296847 {A : Type'} (_6641 : A) (_6643 : A) (_6640 : A -> Prop) (_6642 : A -> Prop) (h1 : _6641 = _6643) (h2 : _6640 = _6642) : (@I (A -> Prop) _6640 _6641) = (@I (A -> Prop) _6642 _6643).
Proof. exact (MK_COMB (@lem296846 A _6640 _6642 h2) (@lem296845 A _6641 _6643 h1)). Qed.
Lemma lem296849 (b : Prop) (a : Prop) : term192 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem296850 {A : Type'} (_6642 : A -> Prop) (_6643 : A) (_6640 : A -> Prop) (_6641 : A) : term1005 A _6642 _6643 _6640 _6641.
Proof. exact (@lem296849 (@I (A -> Prop) _6642 _6643) (@I (A -> Prop) _6640 _6641)). Qed.
Lemma lem296851 {A : Type'} (_6641 : A) (_6643 : A) (_6640 : A -> Prop) (_6642 : A -> Prop) (h1 : _6641 = _6643) (h2 : _6640 = _6642) : term1006 A _6642 _6643 _6640 _6641.
Proof. exact (@lem296850 A _6642 _6643 _6640 _6641 (@lem296847 A _6641 _6643 _6640 _6642 h1 h2)). Qed.
Lemma lem296852 {A : Type'} (_6642 : A -> Prop) (_6640 : A -> Prop) (_6641 : A) (_6643 : A) (h1 : _6641 = _6643) : term1007 A _6642 _6643 _6640 _6641.
Proof. exact (fun h0 : _6640 = _6642 => @lem296851 A _6641 _6643 _6640 _6642 h1 h0). Qed.
Lemma lem296854 (a : Prop) (b : Prop) : (a -> b) = (term196 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem296855 {A : Type'} (_6642 : A -> Prop) (_6643 : A) (_6640 : A -> Prop) (_6641 : A) : (term1007 A _6642 _6643 _6640 _6641) = (term1008 A _6642 _6643 _6640 _6641).
Proof. exact (@lem296854 (_6640 = _6642) (term1006 A _6642 _6643 _6640 _6641)). Qed.
Lemma lem296856 {A : Type'} (_6642 : A -> Prop) (_6640 : A -> Prop) (_6641 : A) (_6643 : A) (h1 : _6641 = _6643) : term1008 A _6642 _6643 _6640 _6641.
Proof. exact (EQ_MP (@lem296855 A _6642 _6643 _6640 _6641) (@lem296852 A _6642 _6640 _6641 _6643 h1)). Qed.
Lemma lem296857 {A : Type'} (_6642 : A -> Prop) (_6643 : A) (_6640 : A -> Prop) (_6641 : A) : term1009 A _6642 _6643 _6640 _6641.
Proof. exact (fun h0 : _6641 = _6643 => @lem296856 A _6642 _6640 _6641 _6643 h0). Qed.
Lemma lem296859 (a : Prop) (b : Prop) : (a -> b) = (term196 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem296860 {A : Type'} (_6642 : A -> Prop) (_6643 : A) (_6640 : A -> Prop) (_6641 : A) : (term1009 A _6642 _6643 _6640 _6641) = (term1010 A _6642 _6643 _6640 _6641).
Proof. exact (@lem296859 (_6641 = _6643) (term1008 A _6642 _6643 _6640 _6641)). Qed.
Lemma lem296861 {A : Type'} (_6642 : A -> Prop) (_6643 : A) (_6640 : A -> Prop) (_6641 : A) : term1010 A _6642 _6643 _6640 _6641.
Proof. exact (EQ_MP (@lem296860 A _6642 _6643 _6640 _6641) (@lem296857 A _6642 _6643 _6640 _6641)). Qed.
Lemma lem296907 {A : Type'} : (@I (A -> A -> Prop)) = (@I (A -> A -> Prop)).
Proof. exact (eq_refl (@I (A -> A -> Prop))). Qed.
Lemma lem296908 {A : Type'} (_6656 : type1402 A) (_6658 : type1402 A) (h1 : _6656 = _6658) : _6656 = _6658.
Proof. exact (h1). Qed.
Lemma lem296909 {A : Type'} (_6657 : A) (_6659 : A) (h1 : _6657 = _6659) : _6657 = _6659.
Proof. exact (h1). Qed.
Lemma lem296910 {A : Type'} (_6656 : type1402 A) (_6658 : type1402 A) (h1 : _6656 = _6658) : (@I (A -> A -> Prop) _6656) = (@I (A -> A -> Prop) _6658).
Proof. exact (MK_COMB (@lem296907 A) (@lem296908 A _6656 _6658 h1)). Qed.
Lemma lem296911 {A : Type'} (_6657 : A) (_6659 : A) (_6656 : type1402 A) (_6658 : type1402 A) (h1 : _6657 = _6659) (h2 : _6656 = _6658) : (@I (A -> A -> Prop) _6656 _6657) = (@I (A -> A -> Prop) _6658 _6659).
Proof. exact (MK_COMB (@lem296910 A _6656 _6658 h2) (@lem296909 A _6657 _6659 h1)). Qed.
Lemma lem296912 {A : Type'} (_6656 : type1402 A) (_6658 : type1402 A) (_6657 : A) (_6659 : A) (h1 : _6657 = _6659) : term1011 A _6656 _6657 _6658 _6659.
Proof. exact (fun h0 : _6656 = _6658 => @lem296911 A _6657 _6659 _6656 _6658 h1 h0). Qed.
Lemma lem296914 (a : Prop) (b : Prop) : (a -> b) = (term196 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem296915 {A : Type'} (_6656 : type1402 A) (_6657 : A) (_6658 : type1402 A) (_6659 : A) : (term1011 A _6656 _6657 _6658 _6659) = (term1012 A _6656 _6657 _6658 _6659).
Proof. exact (@lem296914 (_6656 = _6658) ((@I (A -> A -> Prop) _6656 _6657) = (@I (A -> A -> Prop) _6658 _6659))). Qed.
Lemma lem296916 {A : Type'} (_6656 : type1402 A) (_6658 : type1402 A) (_6657 : A) (_6659 : A) (h1 : _6657 = _6659) : term1012 A _6656 _6657 _6658 _6659.
Proof. exact (EQ_MP (@lem296915 A _6656 _6657 _6658 _6659) (@lem296912 A _6656 _6658 _6657 _6659 h1)). Qed.
Lemma lem296917 {A : Type'} (_6656 : type1402 A) (_6657 : A) (_6658 : type1402 A) (_6659 : A) : term1013 A _6656 _6657 _6658 _6659.
Proof. exact (fun h0 : _6657 = _6659 => @lem296916 A _6656 _6658 _6657 _6659 h0). Qed.
Lemma lem296919 (a : Prop) (b : Prop) : (a -> b) = (term196 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem296920 {A : Type'} (_6656 : type1402 A) (_6657 : A) (_6658 : type1402 A) (_6659 : A) : (term1013 A _6656 _6657 _6658 _6659) = (term1014 A _6656 _6657 _6658 _6659).
Proof. exact (@lem296919 (_6657 = _6659) (term1012 A _6656 _6657 _6658 _6659)). Qed.
Lemma lem296921 {A : Type'} (_6656 : type1402 A) (_6657 : A) (_6658 : type1402 A) (_6659 : A) : term1014 A _6656 _6657 _6658 _6659.
Proof. exact (EQ_MP (@lem296920 A _6656 _6657 _6658 _6659) (@lem296917 A _6656 _6657 _6658 _6659)). Qed.
Lemma lem297021 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : term1015 A x y z.
Proof. exact (@lem21385 (A -> Prop) x y z). Qed.
Lemma lem297039 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term459 A P R f n y) : term908 A P n y.
Proof. exact (proj1 (@lem296365 A P R f n y h1)). Qed.
Lemma lem297040 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term459 A P R f n y) : term1016 A P n y.
Proof. exact (fun h0 : term910 A P n y => @lem297039 A P R f n y h1). Qed.
Lemma lem297042 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem297043 {A : Type'} (P : type1597 A) (n : nat) (y : A) : (term1016 A P n y) = (term908 A P n y).
Proof. exact (@lem297042 (term908 A P n y)). Qed.
Lemma lem297044 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term459 A P R f n y) : term908 A P n y.
Proof. exact (EQ_MP (@lem297043 A P n y) (@lem297040 A P R f n y h1)). Qed.
Lemma lem297046 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term459 A P R f n y) : term903 A R f n y.
Proof. exact (proj2 (@lem296365 A P R f n y h1)). Qed.
Lemma lem297047 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term459 A P R f n y) : term1017 A R f n y.
Proof. exact (fun h0 : term905 A R f n y => @lem297046 A P R f n y h1). Qed.
Lemma lem297049 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem297050 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) (y : A) : (term1017 A R f n y) = (term903 A R f n y).
Proof. exact (@lem297049 (term903 A R f n y)). Qed.
Lemma lem297051 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term459 A P R f n y) : term903 A R f n y.
Proof. exact (EQ_MP (@lem297050 A R f n y) (@lem297047 A P R f n y h1)). Qed.
Lemma lem297057 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem297058 {A : Type'} (_6615 : A) (_6610 : type943 A) (_6611 : type1597 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6614 : nat) : (term1004 A _6615 _6610 _6611 _6612 _6613 _6614) = (term1018 A _6615 _6610 _6611 _6612 _6613 _6614).
Proof. exact (@lem297057 (term905 A _6612 _6613 _6614 _6615) (term910 A _6611 _6614 _6615) (term898 A _6610 _6611 _6612 _6613 _6614)). Qed.
Lemma lem297072 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem297073 {A : Type'} (_6610 : type943 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6611 : type1597 A) (_6614 : nat) (_6615 : A) : (term1019 A _6615 _6610 _6611 _6612 _6613 _6614) = (term1020 A _6610 _6612 _6613 _6611 _6614 _6615).
Proof. exact (@lem297072 (term898 A _6610 _6611 _6612 _6613 _6614) (term910 A _6611 _6614 _6615)). Qed.
Lemma lem297079 {A : Type'} (_6612 : type1594 A) (_6613 : nat -> A) (_6614 : nat) (_6615 : A) : (term1021 A _6612 _6613 _6614 _6615) = (term1021 A _6612 _6613 _6614 _6615).
Proof. exact (eq_refl (term1021 A _6612 _6613 _6614 _6615)). Qed.
Lemma lem297080 {A : Type'} (_6610 : type943 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6611 : type1597 A) (_6614 : nat) (_6615 : A) : (term1018 A _6615 _6610 _6611 _6612 _6613 _6614) = (term1022 A _6610 _6612 _6613 _6611 _6614 _6615).
Proof. exact (MK_COMB (@lem297079 A _6612 _6613 _6614 _6615) (@lem297073 A _6610 _6612 _6613 _6611 _6614 _6615)). Qed.
Lemma lem297084 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem297085 {A : Type'} (_6610 : type943 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6611 : type1597 A) (_6614 : nat) (_6615 : A) : (term1022 A _6610 _6612 _6613 _6611 _6614 _6615) = (term1023 A _6610 _6612 _6613 _6611 _6614 _6615).
Proof. exact (@lem297084 (term898 A _6610 _6611 _6612 _6613 _6614) (term905 A _6612 _6613 _6614 _6615) (term910 A _6611 _6614 _6615)). Qed.
Lemma lem297101 {A : Type'} (_6610 : type943 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6611 : type1597 A) (_6614 : nat) (_6615 : A) : (term1018 A _6615 _6610 _6611 _6612 _6613 _6614) = (term1023 A _6610 _6612 _6613 _6611 _6614 _6615).
Proof. exact (TRANS (@lem297080 A _6610 _6612 _6613 _6611 _6614 _6615) (@lem297085 A _6610 _6612 _6613 _6611 _6614 _6615)). Qed.
Lemma lem297102 {A : Type'} (_6610 : type943 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6611 : type1597 A) (_6614 : nat) (_6615 : A) : (term1004 A _6615 _6610 _6611 _6612 _6613 _6614) = (term1023 A _6610 _6612 _6613 _6611 _6614 _6615).
Proof. exact (TRANS (@lem297058 A _6615 _6610 _6611 _6612 _6613 _6614) (@lem297101 A _6610 _6612 _6613 _6611 _6614 _6615)). Qed.
Lemma lem297103 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem297104 {A : Type'} (_6610 : type943 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6611 : type1597 A) (_6614 : nat) (_6615 : A) : (term1024 A _6615 _6610 _6611 _6612 _6613 _6614) = (term1025 A _6610 _6612 _6613 _6611 _6614 _6615).
Proof. exact (MK_COMB (@lem297103) (@lem297102 A _6610 _6612 _6613 _6611 _6614 _6615)). Qed.
Lemma lem297118 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem297119 {A : Type'} (_6612 : type1594 A) (_6613 : nat -> A) (_6611 : type1597 A) (_6614 : nat) (_6615 : A) : (term913 A _6611 _6612 _6613 _6614 _6615) = (term1026 A _6612 _6613 _6611 _6614 _6615).
Proof. exact (@lem297118 (term905 A _6612 _6613 _6614 _6615) (term910 A _6611 _6614 _6615)). Qed.
Lemma lem297125 {A : Type'} (_6610 : type943 A) (_6611 : type1597 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6614 : nat) : (term1027 A _6610 _6611 _6612 _6613 _6614) = (term1027 A _6610 _6611 _6612 _6613 _6614).
Proof. exact (eq_refl (term1027 A _6610 _6611 _6612 _6613 _6614)). Qed.
Lemma lem297126 {A : Type'} (_6610 : type943 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6611 : type1597 A) (_6614 : nat) (_6615 : A) : (term1028 A _6610 _6611 _6612 _6613 _6614 _6615) = (term1023 A _6610 _6612 _6613 _6611 _6614 _6615).
Proof. exact (MK_COMB (@lem297125 A _6610 _6611 _6612 _6613 _6614) (@lem297119 A _6612 _6613 _6611 _6614 _6615)). Qed.
Lemma lem297137 {A : Type'} (_6610 : type943 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6611 : type1597 A) (_6614 : nat) (_6615 : A) : ((term1004 A _6615 _6610 _6611 _6612 _6613 _6614) = (term1028 A _6610 _6611 _6612 _6613 _6614 _6615)) = ((term1023 A _6610 _6612 _6613 _6611 _6614 _6615) = (term1023 A _6610 _6612 _6613 _6611 _6614 _6615)).
Proof. exact (MK_COMB (@lem297104 A _6610 _6612 _6613 _6611 _6614 _6615) (@lem297126 A _6610 _6612 _6613 _6611 _6614 _6615)). Qed.
Lemma lem297139 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem297140 (x : Prop) : (x = x) = True.
Proof. exact (@lem297139 Prop x). Qed.
Lemma lem297141 {A : Type'} (_6610 : type943 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6611 : type1597 A) (_6614 : nat) (_6615 : A) : ((term1023 A _6610 _6612 _6613 _6611 _6614 _6615) = (term1023 A _6610 _6612 _6613 _6611 _6614 _6615)) = True.
Proof. exact (@lem297140 (term1023 A _6610 _6612 _6613 _6611 _6614 _6615)). Qed.
Lemma lem297142 {A : Type'} (_6610 : type943 A) (_6611 : type1597 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6614 : nat) (_6615 : A) : ((term1004 A _6615 _6610 _6611 _6612 _6613 _6614) = (term1028 A _6610 _6611 _6612 _6613 _6614 _6615)) = True.
Proof. exact (TRANS (@lem297137 A _6610 _6612 _6613 _6611 _6614 _6615) (@lem297141 A _6610 _6612 _6613 _6611 _6614 _6615)). Qed.
Lemma lem297143 {A : Type'} (_6610 : type943 A) (_6611 : type1597 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6614 : nat) (_6615 : A) : True = ((term1004 A _6615 _6610 _6611 _6612 _6613 _6614) = (term1028 A _6610 _6611 _6612 _6613 _6614 _6615)).
Proof. exact (SYM (@lem297142 A _6610 _6611 _6612 _6613 _6614 _6615)). Qed.
Lemma lem297144 {A : Type'} (_6610 : type943 A) (_6611 : type1597 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6614 : nat) (_6615 : A) : (term1004 A _6615 _6610 _6611 _6612 _6613 _6614) = (term1028 A _6610 _6611 _6612 _6613 _6614 _6615).
Proof. exact (EQ_MP (@lem297143 A _6610 _6611 _6612 _6613 _6614 _6615) (@lem0)). Qed.
Lemma lem297145 {A : Type'} (_6611 : type1597 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6614 : nat) (_6615 : A) (_6610 : type943 A) (h1 : term511 A _6610) : term1028 A _6610 _6611 _6612 _6613 _6614 _6615.
Proof. exact (EQ_MP (@lem297144 A _6610 _6611 _6612 _6613 _6614 _6615) (@lem296828 A _6615 _6611 _6612 _6613 _6614 _6610 h1)). Qed.
Lemma lem297147 (b : Prop) (a : Prop) : (a \/ b) = (term203 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem297148 {A : Type'} (_6615 : A) (_6610 : type943 A) (_6611 : type1597 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6614 : nat) : (term1028 A _6610 _6611 _6612 _6613 _6614 _6615) = (term1029 A _6615 _6610 _6611 _6612 _6613 _6614).
Proof. exact (@lem297147 (term913 A _6611 _6612 _6613 _6614 _6615) (term898 A _6610 _6611 _6612 _6613 _6614)). Qed.
Lemma lem297150 (a : Prop) (b : Prop) : (term206 a b) = (term207 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem297151 {A : Type'} (_6611 : type1597 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6614 : nat) (_6615 : A) : (term1030 A _6611 _6612 _6613 _6614 _6615) = (term1031 A _6611 _6612 _6613 _6614 _6615).
Proof. exact (@lem297150 (term910 A _6611 _6614 _6615) (term905 A _6612 _6613 _6614 _6615)). Qed.
Lemma lem297153 (a : Prop) : (term210 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem297154 {A : Type'} (_6611 : type1597 A) (_6614 : nat) (_6615 : A) : (term1032 A _6611 _6614 _6615) = (term908 A _6611 _6614 _6615).
Proof. exact (@lem297153 (term908 A _6611 _6614 _6615)). Qed.
Lemma lem297155 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem297156 {A : Type'} (_6611 : type1597 A) (_6614 : nat) (_6615 : A) : (term1033 A _6611 _6614 _6615) = (term960 A _6611 _6614 _6615).
Proof. exact (MK_COMB (@lem297155) (@lem297154 A _6611 _6614 _6615)). Qed.
Lemma lem297158 (a : Prop) : (term210 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem297159 {A : Type'} (_6612 : type1594 A) (_6613 : nat -> A) (_6614 : nat) (_6615 : A) : (term1034 A _6612 _6613 _6614 _6615) = (term903 A _6612 _6613 _6614 _6615).
Proof. exact (@lem297158 (term903 A _6612 _6613 _6614 _6615)). Qed.
Lemma lem297160 {A : Type'} (_6611 : type1597 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6614 : nat) (_6615 : A) : (term1031 A _6611 _6612 _6613 _6614 _6615) = (term961 A _6611 _6612 _6613 _6614 _6615).
Proof. exact (MK_COMB (@lem297156 A _6611 _6614 _6615) (@lem297159 A _6612 _6613 _6614 _6615)). Qed.
Lemma lem297161 {A : Type'} (_6611 : type1597 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6614 : nat) (_6615 : A) : (term1030 A _6611 _6612 _6613 _6614 _6615) = (term961 A _6611 _6612 _6613 _6614 _6615).
Proof. exact (TRANS (@lem297151 A _6611 _6612 _6613 _6614 _6615) (@lem297160 A _6611 _6612 _6613 _6614 _6615)). Qed.
Lemma lem297162 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem297163 {A : Type'} (_6611 : type1597 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6614 : nat) (_6615 : A) : (term1035 A _6611 _6612 _6613 _6614 _6615) = (term1036 A _6611 _6612 _6613 _6614 _6615).
Proof. exact (MK_COMB (@lem297162) (@lem297161 A _6611 _6612 _6613 _6614 _6615)). Qed.
Lemma lem297164 {A : Type'} (_6610 : type943 A) (_6611 : type1597 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6614 : nat) : (term898 A _6610 _6611 _6612 _6613 _6614) = (term898 A _6610 _6611 _6612 _6613 _6614).
Proof. exact (eq_refl (term898 A _6610 _6611 _6612 _6613 _6614)). Qed.
Lemma lem297165 {A : Type'} (_6615 : A) (_6610 : type943 A) (_6611 : type1597 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6614 : nat) : (term1029 A _6615 _6610 _6611 _6612 _6613 _6614) = (term1037 A _6615 _6610 _6611 _6612 _6613 _6614).
Proof. exact (MK_COMB (@lem297163 A _6611 _6612 _6613 _6614 _6615) (@lem297164 A _6610 _6611 _6612 _6613 _6614)). Qed.
Lemma lem297166 {A : Type'} (_6615 : A) (_6610 : type943 A) (_6611 : type1597 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6614 : nat) : (term1028 A _6610 _6611 _6612 _6613 _6614 _6615) = (term1037 A _6615 _6610 _6611 _6612 _6613 _6614).
Proof. exact (TRANS (@lem297148 A _6615 _6610 _6611 _6612 _6613 _6614) (@lem297165 A _6615 _6610 _6611 _6612 _6613 _6614)). Qed.
Lemma lem297168 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term459 A P R f n y) : term961 A P R f n y.
Proof. exact (conj (@lem297044 A P R f n y h1) (@lem297051 A P R f n y h1)). Qed.
Lemma lem297170 {A : Type'} (_6615 : A) (_6611 : type1597 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6614 : nat) (_6610 : type943 A) (h1 : term511 A _6610) : term1037 A _6615 _6610 _6611 _6612 _6613 _6614.
Proof. exact (EQ_MP (@lem297166 A _6615 _6610 _6611 _6612 _6613 _6614) (@lem297145 A _6611 _6612 _6613 _6614 _6615 _6610 h1)). Qed.
Lemma lem297171 {A : Type'} (_6615 : A) (_6611 : type1597 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6614 : nat) (_6610 : type943 A) (h1 : term511 A _6610) : term1037 A _6615 _6610 _6611 _6612 _6613 _6614.
Proof. exact (@lem297170 A _6615 _6611 _6612 _6613 _6614 _6610 h1). Qed.
Lemma lem297172 {A : Type'} (y : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6610 : type943 A) (h1 : term511 A _6610) : term1037 A y _6610 P R f n.
Proof. exact (@lem297171 A y P R f n _6610 h1). Qed.
Lemma lem297175 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term511 A _6610) (h2 : term459 A P R f n y) : term898 A _6610 P R f n.
Proof. exact (@lem297172 A y P R f n _6610 h1 (@lem297168 A P R f n y h2)). Qed.
Lemma lem297176 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term511 A _6610) (h2 : term459 A P R f n y) : term1038 A _6610 P R f n.
Proof. exact (fun h0 : term1039 A _6610 P R f n => @lem297175 A _6610 P R f n y h1 h2). Qed.
Lemma lem297178 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem297179 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term1038 A _6610 P R f n) = (term898 A _6610 P R f n).
Proof. exact (@lem297178 (term898 A _6610 P R f n)). Qed.
Lemma lem297180 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term511 A _6610) (h2 : term459 A P R f n y) : term898 A _6610 P R f n.
Proof. exact (EQ_MP (@lem297179 A _6610 P R f n) (@lem297176 A _6610 P R f n y h1 h2)). Qed.
Lemma lem297186 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem297187 {A : Type'} (y' : type1596 A) (P : type1597 A) (_6618 : nat) (_6619 : A) : (term726 A P y' _6618 _6619) = (term730 A y' P _6618 _6619).
Proof. exact (@lem297186 (term697 A P y' _6618 _6619) (term703 A P _6618 _6619)). Qed.
Lemma lem297193 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem297194 {A : Type'} (y' : type1596 A) (P : type1597 A) (_6618 : nat) (_6619 : A) : (term731 A P y' _6618 _6619) = (term732 A y' P _6618 _6619).
Proof. exact (MK_COMB (@lem297193) (@lem297187 A y' P _6618 _6619)). Qed.
Lemma lem297200 {A : Type'} (y' : type1596 A) (P : type1597 A) (_6618 : nat) (_6619 : A) : (term730 A y' P _6618 _6619) = (term730 A y' P _6618 _6619).
Proof. exact (eq_refl (term730 A y' P _6618 _6619)). Qed.
Lemma lem297201 {A : Type'} (y' : type1596 A) (P : type1597 A) (_6618 : nat) (_6619 : A) : ((term726 A P y' _6618 _6619) = (term730 A y' P _6618 _6619)) = ((term730 A y' P _6618 _6619) = (term730 A y' P _6618 _6619)).
Proof. exact (MK_COMB (@lem297194 A y' P _6618 _6619) (@lem297200 A y' P _6618 _6619)). Qed.
Lemma lem297203 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem297204 (x : Prop) : (x = x) = True.
Proof. exact (@lem297203 Prop x). Qed.
Lemma lem297205 {A : Type'} (y' : type1596 A) (P : type1597 A) (_6618 : nat) (_6619 : A) : ((term730 A y' P _6618 _6619) = (term730 A y' P _6618 _6619)) = True.
Proof. exact (@lem297204 (term730 A y' P _6618 _6619)). Qed.
Lemma lem297206 {A : Type'} (y' : type1596 A) (P : type1597 A) (_6618 : nat) (_6619 : A) : ((term726 A P y' _6618 _6619) = (term730 A y' P _6618 _6619)) = True.
Proof. exact (TRANS (@lem297201 A y' P _6618 _6619) (@lem297205 A y' P _6618 _6619)). Qed.
Lemma lem297207 {A : Type'} (y' : type1596 A) (P : type1597 A) (_6618 : nat) (_6619 : A) : True = ((term726 A P y' _6618 _6619) = (term730 A y' P _6618 _6619)).
Proof. exact (SYM (@lem297206 A y' P _6618 _6619)). Qed.
Lemma lem297208 {A : Type'} (y' : type1596 A) (P : type1597 A) (_6618 : nat) (_6619 : A) : (term726 A P y' _6618 _6619) = (term730 A y' P _6618 _6619).
Proof. exact (EQ_MP (@lem297207 A y' P _6618 _6619) (@lem0)). Qed.
Lemma lem297209 {A : Type'} (_6618 : nat) (_6619 : A) (P : type1597 A) (R : type1594 A) (y' : type1596 A) (h1 : term634 A P R y') : term730 A y' P _6618 _6619.
Proof. exact (EQ_MP (@lem297208 A y' P _6618 _6619) (@lem296800 A _6618 _6619 P R y' h1)). Qed.
Lemma lem297211 (b : Prop) (a : Prop) : (a \/ b) = (term203 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem297212 {A : Type'} (P : type1597 A) (y' : type1596 A) (_6618 : nat) (_6619 : A) : (term730 A y' P _6618 _6619) = (term733 A P y' _6618 _6619).
Proof. exact (@lem297211 (term703 A P _6618 _6619) (term697 A P y' _6618 _6619)). Qed.
Lemma lem297214 (a : Prop) : (term210 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem297215 {A : Type'} (P : type1597 A) (_6618 : nat) (_6619 : A) : (term734 A P _6618 _6619) = (term702 A P _6618 _6619).
Proof. exact (@lem297214 (term702 A P _6618 _6619)). Qed.
Lemma lem297216 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem297217 {A : Type'} (P : type1597 A) (_6618 : nat) (_6619 : A) : (term735 A P _6618 _6619) = (term736 A P _6618 _6619).
Proof. exact (MK_COMB (@lem297216) (@lem297215 A P _6618 _6619)). Qed.
Lemma lem297218 {A : Type'} (P : type1597 A) (y' : type1596 A) (_6618 : nat) (_6619 : A) : (term697 A P y' _6618 _6619) = (term697 A P y' _6618 _6619).
Proof. exact (eq_refl (term697 A P y' _6618 _6619)). Qed.
Lemma lem297219 {A : Type'} (P : type1597 A) (y' : type1596 A) (_6618 : nat) (_6619 : A) : (term733 A P y' _6618 _6619) = (term737 A P y' _6618 _6619).
Proof. exact (MK_COMB (@lem297217 A P _6618 _6619) (@lem297218 A P y' _6618 _6619)). Qed.
Lemma lem297220 {A : Type'} (P : type1597 A) (y' : type1596 A) (_6618 : nat) (_6619 : A) : (term730 A y' P _6618 _6619) = (term737 A P y' _6618 _6619).
Proof. exact (TRANS (@lem297212 A P y' _6618 _6619) (@lem297219 A P y' _6618 _6619)). Qed.
Lemma lem297223 {A : Type'} (_6618 : nat) (_6619 : A) (P : type1597 A) (R : type1594 A) (y' : type1596 A) (h1 : term634 A P R y') : term737 A P y' _6618 _6619.
Proof. exact (EQ_MP (@lem297220 A P y' _6618 _6619) (@lem297209 A _6618 _6619 P R y' h1)). Qed.
Lemma lem297224 {A : Type'} (_6618 : nat) (_6619 : A) (P : type1597 A) (R : type1594 A) (y' : type1596 A) (h1 : term634 A P R y') : term737 A P y' _6618 _6619.
Proof. exact (@lem297223 A _6618 _6619 P R y' h1). Qed.
Lemma lem297225 {A : Type'} (_6610 : type943 A) (f : nat -> A) (n : nat) (P : type1597 A) (R : type1594 A) (y' : type1596 A) (h1 : term634 A P R y') : term1040 A y' _6610 P R f n.
Proof. exact (@lem297224 A (@I (nat -> nat) S n) (term889 A _6610 P R f n) P R y' h1). Qed.
Lemma lem297228 {A : Type'} (_6610 : type943 A) (y' : type1596 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term511 A _6610) (h2 : term634 A P R y') (h3 : term459 A P R f n y) : term1041 A y' _6610 P R f n.
Proof. exact (@lem297225 A _6610 f n P R y' h2 (@lem297180 A _6610 P R f n y h1 h3)). Qed.
Lemma lem297229 {A : Type'} (_6610 : type943 A) (y' : type1596 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term511 A _6610) (h2 : term634 A P R y') (h3 : term459 A P R f n y) : term1042 A y' _6610 P R f n.
Proof. exact (fun h0 : term1043 A y' _6610 P R f n => @lem297228 A _6610 y' P R f n y h1 h2 h3). Qed.
Lemma lem297231 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem297232 {A : Type'} (y' : type1596 A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term1042 A y' _6610 P R f n) = (term1041 A y' _6610 P R f n).
Proof. exact (@lem297231 (term1041 A y' _6610 P R f n)). Qed.
Lemma lem297233 {A : Type'} (_6610 : type943 A) (y' : type1596 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term511 A _6610) (h2 : term634 A P R y') (h3 : term459 A P R f n y) : term1041 A y' _6610 P R f n.
Proof. exact (EQ_MP (@lem297232 A y' _6610 P R f n) (@lem297229 A _6610 y' P R f n y h1 h2 h3)). Qed.
Lemma lem297235 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem297236 {A : Type'} (x : A) : x = x.
Proof. exact (@lem297235 A x). Qed.
Lemma lem297237 {A : Type'} (y' : type1596 A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term1044 A y' _6610 P R f n) = (term1044 A y' _6610 P R f n).
Proof. exact (@lem297236 A (term1044 A y' _6610 P R f n)). Qed.
Lemma lem297238 {A : Type'} (y' : type1596 A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : term1045 A y' _6610 P R f n.
Proof. exact (fun h0 : term1046 A y' _6610 P R f n => @lem297237 A y' _6610 P R f n). Qed.
Lemma lem297240 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem297241 {A : Type'} (y' : type1596 A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term1045 A y' _6610 P R f n) = ((term1044 A y' _6610 P R f n) = (term1044 A y' _6610 P R f n)).
Proof. exact (@lem297240 ((term1044 A y' _6610 P R f n) = (term1044 A y' _6610 P R f n))). Qed.
Lemma lem297242 {A : Type'} (y' : type1596 A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term1044 A y' _6610 P R f n) = (term1044 A y' _6610 P R f n).
Proof. exact (EQ_MP (@lem297241 A y' _6610 P R f n) (@lem297238 A y' _6610 P R f n)). Qed.
Lemma lem297244 {A : Type'} (_6616 : nat) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term515 A _6610 P R f) : (term927 A f _6616) = (term889 A _6610 P R f _6616).
Proof. exact (EQ_MP (@lem296636 A _6610 P R f _6616) (@lem296635 A _6616 _6610 P R f h1)). Qed.
Lemma lem297245 {A : Type'} (n : nat) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term515 A _6610 P R f) : (term927 A f n) = (term889 A _6610 P R f n).
Proof. exact (@lem297244 A n _6610 P R f h1). Qed.
Lemma lem297246 {A : Type'} (n : nat) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term515 A _6610 P R f) : term1047 A _6610 P R f n.
Proof. exact (fun h0 : term1048 A _6610 P R f n => @lem297245 A n _6610 P R f h1). Qed.
Lemma lem297248 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem297249 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term1047 A _6610 P R f n) = ((term927 A f n) = (term889 A _6610 P R f n)).
Proof. exact (@lem297248 ((term927 A f n) = (term889 A _6610 P R f n))). Qed.
Lemma lem297250 {A : Type'} (n : nat) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term515 A _6610 P R f) : (term927 A f n) = (term889 A _6610 P R f n).
Proof. exact (EQ_MP (@lem297249 A _6610 P R f n) (@lem297246 A n _6610 P R f h1)). Qed.
Lemma lem297252 {A : Type'} (x : type1402 A) : x = x.
Proof. exact (@lem21386 (type1402 A) x). Qed.
Lemma lem297253 {A : Type'} (x : type1402 A) : x = x.
Proof. exact (@lem297252 A x). Qed.
Lemma lem297254 {A : Type'} (R : type1594 A) (n : nat) : (term936 A R n) = (term936 A R n).
Proof. exact (@lem297253 A (term936 A R n)). Qed.
Lemma lem297255 {A : Type'} (R : type1594 A) (n : nat) : term1049 A R n.
Proof. exact (fun h0 : term1050 A R n => @lem297254 A R n). Qed.
Lemma lem297257 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem297258 {A : Type'} (R : type1594 A) (n : nat) : (term1049 A R n) = ((term936 A R n) = (term936 A R n)).
Proof. exact (@lem297257 ((term936 A R n) = (term936 A R n))). Qed.
Lemma lem297259 {A : Type'} (R : type1594 A) (n : nat) : (term936 A R n) = (term936 A R n).
Proof. exact (EQ_MP (@lem297258 A R n) (@lem297255 A R n)). Qed.
Lemma lem297277 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem297278 {A : Type'} (_6657 : A) (_6659 : A) (_6656 : type1402 A) (_6658 : type1402 A) : (term1012 A _6656 _6657 _6658 _6659) = (term1051 A _6657 _6659 _6656 _6658).
Proof. exact (@lem297277 ((@I (A -> A -> Prop) _6656 _6657) = (@I (A -> A -> Prop) _6658 _6659)) (term1052 A _6656 _6658)). Qed.
Lemma lem297288 {A : Type'} (_6657 : A) (_6659 : A) : (term1053 A _6657 _6659) = (term1053 A _6657 _6659).
Proof. exact (eq_refl (term1053 A _6657 _6659)). Qed.
Lemma lem297289 {A : Type'} (_6657 : A) (_6659 : A) (_6656 : type1402 A) (_6658 : type1402 A) : (term1014 A _6656 _6657 _6658 _6659) = (term1054 A _6657 _6659 _6656 _6658).
Proof. exact (MK_COMB (@lem297288 A _6657 _6659) (@lem297278 A _6657 _6659 _6656 _6658)). Qed.
Lemma lem297293 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem297294 {A : Type'} (_6657 : A) (_6659 : A) (_6656 : type1402 A) (_6658 : type1402 A) : (term1054 A _6657 _6659 _6656 _6658) = (term1055 A _6657 _6659 _6656 _6658).
Proof. exact (@lem297293 ((@I (A -> A -> Prop) _6656 _6657) = (@I (A -> A -> Prop) _6658 _6659)) (term1056 A _6657 _6659) (term1052 A _6656 _6658)). Qed.
Lemma lem297316 {A : Type'} (_6657 : A) (_6659 : A) (_6656 : type1402 A) (_6658 : type1402 A) : (term1014 A _6656 _6657 _6658 _6659) = (term1055 A _6657 _6659 _6656 _6658).
Proof. exact (TRANS (@lem297289 A _6657 _6659 _6656 _6658) (@lem297294 A _6657 _6659 _6656 _6658)). Qed.
Lemma lem297317 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem297318 {A : Type'} (_6657 : A) (_6659 : A) (_6656 : type1402 A) (_6658 : type1402 A) : (term1057 A _6656 _6657 _6658 _6659) = (term1058 A _6657 _6659 _6656 _6658).
Proof. exact (MK_COMB (@lem297317) (@lem297316 A _6657 _6659 _6656 _6658)). Qed.
Lemma lem297340 {A : Type'} (_6657 : A) (_6659 : A) (_6656 : type1402 A) (_6658 : type1402 A) : (term1055 A _6657 _6659 _6656 _6658) = (term1055 A _6657 _6659 _6656 _6658).
Proof. exact (eq_refl (term1055 A _6657 _6659 _6656 _6658)). Qed.
Lemma lem297341 {A : Type'} (_6657 : A) (_6659 : A) (_6656 : type1402 A) (_6658 : type1402 A) : ((term1014 A _6656 _6657 _6658 _6659) = (term1055 A _6657 _6659 _6656 _6658)) = ((term1055 A _6657 _6659 _6656 _6658) = (term1055 A _6657 _6659 _6656 _6658)).
Proof. exact (MK_COMB (@lem297318 A _6657 _6659 _6656 _6658) (@lem297340 A _6657 _6659 _6656 _6658)). Qed.
Lemma lem297343 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem297344 (x : Prop) : (x = x) = True.
Proof. exact (@lem297343 Prop x). Qed.
Lemma lem297345 {A : Type'} (_6657 : A) (_6659 : A) (_6656 : type1402 A) (_6658 : type1402 A) : ((term1055 A _6657 _6659 _6656 _6658) = (term1055 A _6657 _6659 _6656 _6658)) = True.
Proof. exact (@lem297344 (term1055 A _6657 _6659 _6656 _6658)). Qed.
Lemma lem297346 {A : Type'} (_6657 : A) (_6659 : A) (_6656 : type1402 A) (_6658 : type1402 A) : ((term1014 A _6656 _6657 _6658 _6659) = (term1055 A _6657 _6659 _6656 _6658)) = True.
Proof. exact (TRANS (@lem297341 A _6657 _6659 _6656 _6658) (@lem297345 A _6657 _6659 _6656 _6658)). Qed.
Lemma lem297347 {A : Type'} (_6657 : A) (_6659 : A) (_6656 : type1402 A) (_6658 : type1402 A) : True = ((term1014 A _6656 _6657 _6658 _6659) = (term1055 A _6657 _6659 _6656 _6658)).
Proof. exact (SYM (@lem297346 A _6657 _6659 _6656 _6658)). Qed.
Lemma lem297348 {A : Type'} (_6657 : A) (_6659 : A) (_6656 : type1402 A) (_6658 : type1402 A) : (term1014 A _6656 _6657 _6658 _6659) = (term1055 A _6657 _6659 _6656 _6658).
Proof. exact (EQ_MP (@lem297347 A _6657 _6659 _6656 _6658) (@lem0)). Qed.
Lemma lem297349 {A : Type'} (_6657 : A) (_6659 : A) (_6656 : type1402 A) (_6658 : type1402 A) : term1055 A _6657 _6659 _6656 _6658.
Proof. exact (EQ_MP (@lem297348 A _6657 _6659 _6656 _6658) (@lem296921 A _6656 _6657 _6658 _6659)). Qed.
Lemma lem297351 (b : Prop) (a : Prop) : (a \/ b) = (term203 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem297352 {A : Type'} (_6656 : type1402 A) (_6657 : A) (_6658 : type1402 A) (_6659 : A) : (term1055 A _6657 _6659 _6656 _6658) = (term1059 A _6656 _6657 _6658 _6659).
Proof. exact (@lem297351 (term1060 A _6657 _6659 _6656 _6658) ((@I (A -> A -> Prop) _6656 _6657) = (@I (A -> A -> Prop) _6658 _6659))). Qed.
Lemma lem297354 (a : Prop) (b : Prop) : (term206 a b) = (term207 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem297355 {A : Type'} (_6657 : A) (_6659 : A) (_6656 : type1402 A) (_6658 : type1402 A) : (term1061 A _6657 _6659 _6656 _6658) = (term1062 A _6657 _6659 _6656 _6658).
Proof. exact (@lem297354 (term1056 A _6657 _6659) (term1052 A _6656 _6658)). Qed.
Lemma lem297357 (a : Prop) : (term210 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem297358 {A : Type'} (_6657 : A) (_6659 : A) : (term1063 A _6657 _6659) = (_6657 = _6659).
Proof. exact (@lem297357 (_6657 = _6659)). Qed.
Lemma lem297359 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem297360 {A : Type'} (_6657 : A) (_6659 : A) : (term1064 A _6657 _6659) = (term1065 A _6657 _6659).
Proof. exact (MK_COMB (@lem297359) (@lem297358 A _6657 _6659)). Qed.
Lemma lem297362 (a : Prop) : (term210 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem297363 {A : Type'} (_6656 : type1402 A) (_6658 : type1402 A) : (term1066 A _6656 _6658) = (_6656 = _6658).
Proof. exact (@lem297362 (_6656 = _6658)). Qed.
Lemma lem297364 {A : Type'} (_6657 : A) (_6659 : A) (_6656 : type1402 A) (_6658 : type1402 A) : (term1062 A _6657 _6659 _6656 _6658) = (term1067 A _6657 _6659 _6656 _6658).
Proof. exact (MK_COMB (@lem297360 A _6657 _6659) (@lem297363 A _6656 _6658)). Qed.
Lemma lem297365 {A : Type'} (_6657 : A) (_6659 : A) (_6656 : type1402 A) (_6658 : type1402 A) : (term1061 A _6657 _6659 _6656 _6658) = (term1067 A _6657 _6659 _6656 _6658).
Proof. exact (TRANS (@lem297355 A _6657 _6659 _6656 _6658) (@lem297364 A _6657 _6659 _6656 _6658)). Qed.
Lemma lem297366 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem297367 {A : Type'} (_6657 : A) (_6659 : A) (_6656 : type1402 A) (_6658 : type1402 A) : (term1068 A _6657 _6659 _6656 _6658) = (term1069 A _6657 _6659 _6656 _6658).
Proof. exact (MK_COMB (@lem297366) (@lem297365 A _6657 _6659 _6656 _6658)). Qed.
Lemma lem297368 {A : Type'} (_6656 : type1402 A) (_6657 : A) (_6658 : type1402 A) (_6659 : A) : ((@I (A -> A -> Prop) _6656 _6657) = (@I (A -> A -> Prop) _6658 _6659)) = ((@I (A -> A -> Prop) _6656 _6657) = (@I (A -> A -> Prop) _6658 _6659)).
Proof. exact (eq_refl ((@I (A -> A -> Prop) _6656 _6657) = (@I (A -> A -> Prop) _6658 _6659))). Qed.
Lemma lem297369 {A : Type'} (_6656 : type1402 A) (_6657 : A) (_6658 : type1402 A) (_6659 : A) : (term1059 A _6656 _6657 _6658 _6659) = (term1070 A _6656 _6657 _6658 _6659).
Proof. exact (MK_COMB (@lem297367 A _6657 _6659 _6656 _6658) (@lem297368 A _6656 _6657 _6658 _6659)). Qed.
Lemma lem297370 {A : Type'} (_6656 : type1402 A) (_6657 : A) (_6658 : type1402 A) (_6659 : A) : (term1055 A _6657 _6659 _6656 _6658) = (term1070 A _6656 _6657 _6658 _6659).
Proof. exact (TRANS (@lem297352 A _6656 _6657 _6658 _6659) (@lem297369 A _6656 _6657 _6658 _6659)). Qed.
Lemma lem297372 {A : Type'} (n : nat) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term515 A _6610 P R f) : term1071 A _6610 P f R n.
Proof. exact (conj (@lem297250 A n _6610 P R f h1) (@lem297259 A R n)). Qed.
Lemma lem297374 {A : Type'} (_6656 : type1402 A) (_6657 : A) (_6658 : type1402 A) (_6659 : A) : term1070 A _6656 _6657 _6658 _6659.
Proof. exact (EQ_MP (@lem297370 A _6656 _6657 _6658 _6659) (@lem297349 A _6657 _6659 _6656 _6658)). Qed.
Lemma lem297375 {A : Type'} (_6656 : type1402 A) (_6657 : A) (_6658 : type1402 A) (_6659 : A) : term1070 A _6656 _6657 _6658 _6659.
Proof. exact (@lem297374 A _6656 _6657 _6658 _6659). Qed.
Lemma lem297376 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : term1072 A _6610 P R f n.
Proof. exact (@lem297375 A (term936 A R n) (term927 A f n) (term936 A R n) (term889 A _6610 P R f n)). Qed.
Lemma lem297379 {A : Type'} (n : nat) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term515 A _6610 P R f) : (term938 A R f n) = (term1073 A _6610 P R f n).
Proof. exact (@lem297376 A _6610 P R f n (@lem297372 A n _6610 P R f h1)). Qed.
Lemma lem297380 {A : Type'} (n : nat) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term515 A _6610 P R f) : term1074 A _6610 P R f n.
Proof. exact (fun h0 : term1075 A _6610 P R f n => @lem297379 A n _6610 P R f h1). Qed.
Lemma lem297382 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem297383 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term1074 A _6610 P R f n) = ((term938 A R f n) = (term1073 A _6610 P R f n)).
Proof. exact (@lem297382 ((term938 A R f n) = (term1073 A _6610 P R f n))). Qed.
Lemma lem297384 {A : Type'} (n : nat) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term515 A _6610 P R f) : (term938 A R f n) = (term1073 A _6610 P R f n).
Proof. exact (EQ_MP (@lem297383 A _6610 P R f n) (@lem297380 A n _6610 P R f h1)). Qed.
Lemma lem297386 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem21386 (A -> Prop) x). Qed.
Lemma lem297387 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem297386 A x). Qed.
Lemma lem297388 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term938 A R f n) = (term938 A R f n).
Proof. exact (@lem297387 A (term938 A R f n)). Qed.
Lemma lem297389 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : term1076 A R f n.
Proof. exact (fun h0 : term1077 A R f n => @lem297388 A R f n). Qed.
Lemma lem297391 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem297392 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term1076 A R f n) = ((term938 A R f n) = (term938 A R f n)).
Proof. exact (@lem297391 ((term938 A R f n) = (term938 A R f n))). Qed.
Lemma lem297393 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term938 A R f n) = (term938 A R f n).
Proof. exact (EQ_MP (@lem297392 A R f n) (@lem297389 A R f n)). Qed.
Lemma lem297411 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem297412 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term1078 A x y z) = (term1079 A y x z).
Proof. exact (@lem297411 (y = z) (term1080 A x z)). Qed.
Lemma lem297422 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term1081 A x y) = (term1081 A x y).
Proof. exact (eq_refl (term1081 A x y)). Qed.
Lemma lem297423 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term1015 A x y z) = (term1082 A y x z).
Proof. exact (MK_COMB (@lem297422 A x y) (@lem297412 A y x z)). Qed.
Lemma lem297427 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem297428 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term1082 A y x z) = (term1083 A y x z).
Proof. exact (@lem297427 (y = z) (term1080 A x y) (term1080 A x z)). Qed.
Lemma lem297450 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term1015 A x y z) = (term1083 A y x z).
Proof. exact (TRANS (@lem297423 A y x z) (@lem297428 A y x z)). Qed.
Lemma lem297451 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem297452 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term1084 A x y z) = (term1085 A y x z).
Proof. exact (MK_COMB (@lem297451) (@lem297450 A y x z)). Qed.
Lemma lem297474 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term1083 A y x z) = (term1083 A y x z).
Proof. exact (eq_refl (term1083 A y x z)). Qed.
Lemma lem297475 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : ((term1015 A x y z) = (term1083 A y x z)) = ((term1083 A y x z) = (term1083 A y x z)).
Proof. exact (MK_COMB (@lem297452 A y x z) (@lem297474 A y x z)). Qed.
Lemma lem297477 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem297478 (x : Prop) : (x = x) = True.
Proof. exact (@lem297477 Prop x). Qed.
Lemma lem297479 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : ((term1083 A y x z) = (term1083 A y x z)) = True.
Proof. exact (@lem297478 (term1083 A y x z)). Qed.
Lemma lem297480 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : ((term1015 A x y z) = (term1083 A y x z)) = True.
Proof. exact (TRANS (@lem297475 A y x z) (@lem297479 A y x z)). Qed.
Lemma lem297481 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : True = ((term1015 A x y z) = (term1083 A y x z)).
Proof. exact (SYM (@lem297480 A y x z)). Qed.
Lemma lem297482 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term1015 A x y z) = (term1083 A y x z).
Proof. exact (EQ_MP (@lem297481 A y x z) (@lem0)). Qed.
Lemma lem297483 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : term1083 A y x z.
Proof. exact (EQ_MP (@lem297482 A y x z) (@lem297021 A x y z)). Qed.
Lemma lem297485 (b : Prop) (a : Prop) : (a \/ b) = (term203 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem297486 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term1083 A y x z) = (term1086 A x y z).
Proof. exact (@lem297485 (term1087 A y x z) (y = z)). Qed.
Lemma lem297488 (a : Prop) (b : Prop) : (term206 a b) = (term207 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem297489 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term1088 A y x z) = (term1089 A y x z).
Proof. exact (@lem297488 (term1080 A x y) (term1080 A x z)). Qed.
Lemma lem297491 (a : Prop) : (term210 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem297492 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term1090 A x y) = (x = y).
Proof. exact (@lem297491 (x = y)). Qed.
Lemma lem297493 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem297494 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term1091 A x y) = (term1092 A x y).
Proof. exact (MK_COMB (@lem297493) (@lem297492 A x y)). Qed.
Lemma lem297496 (a : Prop) : (term210 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem297497 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term1090 A x z) = (x = z).
Proof. exact (@lem297496 (x = z)). Qed.
Lemma lem297498 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term1089 A y x z) = (term1093 A y x z).
Proof. exact (MK_COMB (@lem297494 A x y) (@lem297497 A x z)). Qed.
Lemma lem297499 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term1088 A y x z) = (term1093 A y x z).
Proof. exact (TRANS (@lem297489 A y x z) (@lem297498 A y x z)). Qed.
Lemma lem297500 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem297501 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term1094 A y x z) = (term1095 A y x z).
Proof. exact (MK_COMB (@lem297500) (@lem297499 A y x z)). Qed.
Lemma lem297502 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem297503 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term1086 A x y z) = (term1096 A x y z).
Proof. exact (MK_COMB (@lem297501 A y x z) (@lem297502 A y z)). Qed.
Lemma lem297504 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term1083 A y x z) = (term1096 A x y z).
Proof. exact (TRANS (@lem297486 A x y z) (@lem297503 A x y z)). Qed.
Lemma lem297506 {A : Type'} (n : nat) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term515 A _6610 P R f) : term1097 A _6610 P R f n.
Proof. exact (conj (@lem297384 A n _6610 P R f h1) (@lem297393 A R f n)). Qed.
Lemma lem297508 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : term1096 A x y z.
Proof. exact (EQ_MP (@lem297504 A x y z) (@lem297483 A y x z)). Qed.
Lemma lem297509 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : term1096 A x y z.
Proof. exact (@lem297508 A x y z). Qed.
Lemma lem297510 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : term1098 A _6610 P R f n.
Proof. exact (@lem297509 A (term938 A R f n) (term1073 A _6610 P R f n) (term938 A R f n)). Qed.
Lemma lem297513 {A : Type'} (n : nat) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term515 A _6610 P R f) : (term1073 A _6610 P R f n) = (term938 A R f n).
Proof. exact (@lem297510 A _6610 P R f n (@lem297506 A n _6610 P R f h1)). Qed.
Lemma lem297514 {A : Type'} (n : nat) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term515 A _6610 P R f) : term1099 A _6610 P R f n.
Proof. exact (fun h0 : term1100 A _6610 P R f n => @lem297513 A n _6610 P R f h1). Qed.
Lemma lem297516 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem297517 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term1099 A _6610 P R f n) = ((term1073 A _6610 P R f n) = (term938 A R f n)).
Proof. exact (@lem297516 ((term1073 A _6610 P R f n) = (term938 A R f n))). Qed.
Lemma lem297518 {A : Type'} (n : nat) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term515 A _6610 P R f) : (term1073 A _6610 P R f n) = (term938 A R f n).
Proof. exact (EQ_MP (@lem297517 A _6610 P R f n) (@lem297514 A n _6610 P R f h1)). Qed.
Lemma lem297520 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term459 A P R f n y) : term908 A P n y.
Proof. exact (proj1 (@lem296365 A P R f n y h1)). Qed.
Lemma lem297521 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term459 A P R f n y) : term1016 A P n y.
Proof. exact (fun h0 : term910 A P n y => @lem297520 A P R f n y h1). Qed.
Lemma lem297523 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem297524 {A : Type'} (P : type1597 A) (n : nat) (y : A) : (term1016 A P n y) = (term908 A P n y).
Proof. exact (@lem297523 (term908 A P n y)). Qed.
Lemma lem297525 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term459 A P R f n y) : term908 A P n y.
Proof. exact (EQ_MP (@lem297524 A P n y) (@lem297521 A P R f n y h1)). Qed.
Lemma lem297527 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term459 A P R f n y) : term903 A R f n y.
Proof. exact (proj2 (@lem296365 A P R f n y h1)). Qed.
Lemma lem297528 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term459 A P R f n y) : term1017 A R f n y.
Proof. exact (fun h0 : term905 A R f n y => @lem297527 A P R f n y h1). Qed.
Lemma lem297530 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem297531 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) (y : A) : (term1017 A R f n y) = (term903 A R f n y).
Proof. exact (@lem297530 (term903 A R f n y)). Qed.
Lemma lem297532 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term459 A P R f n y) : term903 A R f n y.
Proof. exact (EQ_MP (@lem297531 A R f n y) (@lem297528 A P R f n y h1)). Qed.
Lemma lem297533 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term459 A P R f n y) : term961 A P R f n y.
Proof. exact (conj (@lem297525 A P R f n y h1) (@lem297532 A P R f n y h1)). Qed.
Lemma lem297535 {A : Type'} (_6615 : A) (_6611 : type1597 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6614 : nat) (_6610 : type943 A) (h1 : term511 A _6610) : term1037 A _6615 _6610 _6611 _6612 _6613 _6614.
Proof. exact (EQ_MP (@lem297166 A _6615 _6610 _6611 _6612 _6613 _6614) (@lem297145 A _6611 _6612 _6613 _6614 _6615 _6610 h1)). Qed.
Lemma lem297536 {A : Type'} (_6615 : A) (_6611 : type1597 A) (_6612 : type1594 A) (_6613 : nat -> A) (_6614 : nat) (_6610 : type943 A) (h1 : term511 A _6610) : term1037 A _6615 _6610 _6611 _6612 _6613 _6614.
Proof. exact (@lem297535 A _6615 _6611 _6612 _6613 _6614 _6610 h1). Qed.
Lemma lem297537 {A : Type'} (y : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6610 : type943 A) (h1 : term511 A _6610) : term1037 A y _6610 P R f n.
Proof. exact (@lem297536 A y P R f n _6610 h1). Qed.
Lemma lem297540 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term511 A _6610) (h2 : term459 A P R f n y) : term898 A _6610 P R f n.
Proof. exact (@lem297537 A y P R f n _6610 h1 (@lem297533 A P R f n y h2)). Qed.
Lemma lem297541 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term511 A _6610) (h2 : term459 A P R f n y) : term1038 A _6610 P R f n.
Proof. exact (fun h0 : term1039 A _6610 P R f n => @lem297540 A _6610 P R f n y h1 h2). Qed.
Lemma lem297543 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem297544 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term1038 A _6610 P R f n) = (term898 A _6610 P R f n).
Proof. exact (@lem297543 (term898 A _6610 P R f n)). Qed.
Lemma lem297545 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term511 A _6610) (h2 : term459 A P R f n y) : term898 A _6610 P R f n.
Proof. exact (EQ_MP (@lem297544 A _6610 P R f n) (@lem297541 A _6610 P R f n y h1 h2)). Qed.
Lemma lem297551 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem297552 {A : Type'} (R : type1594 A) (y' : type1596 A) (P : type1597 A) (_6618 : nat) (_6619 : A) : (term727 A P R y' _6618 _6619) = (term742 A R y' P _6618 _6619).
Proof. exact (@lem297551 (term691 A R y' _6618 _6619) (term703 A P _6618 _6619)). Qed.
Lemma lem297558 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem297559 {A : Type'} (R : type1594 A) (y' : type1596 A) (P : type1597 A) (_6618 : nat) (_6619 : A) : (term743 A P R y' _6618 _6619) = (term744 A R y' P _6618 _6619).
Proof. exact (MK_COMB (@lem297558) (@lem297552 A R y' P _6618 _6619)). Qed.
Lemma lem297565 {A : Type'} (R : type1594 A) (y' : type1596 A) (P : type1597 A) (_6618 : nat) (_6619 : A) : (term742 A R y' P _6618 _6619) = (term742 A R y' P _6618 _6619).
Proof. exact (eq_refl (term742 A R y' P _6618 _6619)). Qed.
Lemma lem297566 {A : Type'} (R : type1594 A) (y' : type1596 A) (P : type1597 A) (_6618 : nat) (_6619 : A) : ((term727 A P R y' _6618 _6619) = (term742 A R y' P _6618 _6619)) = ((term742 A R y' P _6618 _6619) = (term742 A R y' P _6618 _6619)).
Proof. exact (MK_COMB (@lem297559 A R y' P _6618 _6619) (@lem297565 A R y' P _6618 _6619)). Qed.
Lemma lem297568 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem297569 (x : Prop) : (x = x) = True.
Proof. exact (@lem297568 Prop x). Qed.
Lemma lem297570 {A : Type'} (R : type1594 A) (y' : type1596 A) (P : type1597 A) (_6618 : nat) (_6619 : A) : ((term742 A R y' P _6618 _6619) = (term742 A R y' P _6618 _6619)) = True.
Proof. exact (@lem297569 (term742 A R y' P _6618 _6619)). Qed.
Lemma lem297571 {A : Type'} (R : type1594 A) (y' : type1596 A) (P : type1597 A) (_6618 : nat) (_6619 : A) : ((term727 A P R y' _6618 _6619) = (term742 A R y' P _6618 _6619)) = True.
Proof. exact (TRANS (@lem297566 A R y' P _6618 _6619) (@lem297570 A R y' P _6618 _6619)). Qed.
Lemma lem297572 {A : Type'} (R : type1594 A) (y' : type1596 A) (P : type1597 A) (_6618 : nat) (_6619 : A) : True = ((term727 A P R y' _6618 _6619) = (term742 A R y' P _6618 _6619)).
Proof. exact (SYM (@lem297571 A R y' P _6618 _6619)). Qed.
Lemma lem297573 {A : Type'} (R : type1594 A) (y' : type1596 A) (P : type1597 A) (_6618 : nat) (_6619 : A) : (term727 A P R y' _6618 _6619) = (term742 A R y' P _6618 _6619).
Proof. exact (EQ_MP (@lem297572 A R y' P _6618 _6619) (@lem0)). Qed.
Lemma lem297574 {A : Type'} (_6618 : nat) (_6619 : A) (P : type1597 A) (R : type1594 A) (y' : type1596 A) (h1 : term634 A P R y') : term742 A R y' P _6618 _6619.
Proof. exact (EQ_MP (@lem297573 A R y' P _6618 _6619) (@lem296814 A _6618 _6619 P R y' h1)). Qed.
Lemma lem297576 (b : Prop) (a : Prop) : (a \/ b) = (term203 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem297577 {A : Type'} (P : type1597 A) (R : type1594 A) (y' : type1596 A) (_6618 : nat) (_6619 : A) : (term742 A R y' P _6618 _6619) = (term745 A P R y' _6618 _6619).
Proof. exact (@lem297576 (term703 A P _6618 _6619) (term691 A R y' _6618 _6619)). Qed.
Lemma lem297579 (a : Prop) : (term210 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem297580 {A : Type'} (P : type1597 A) (_6618 : nat) (_6619 : A) : (term734 A P _6618 _6619) = (term702 A P _6618 _6619).
Proof. exact (@lem297579 (term702 A P _6618 _6619)). Qed.
Lemma lem297581 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem297582 {A : Type'} (P : type1597 A) (_6618 : nat) (_6619 : A) : (term735 A P _6618 _6619) = (term736 A P _6618 _6619).
Proof. exact (MK_COMB (@lem297581) (@lem297580 A P _6618 _6619)). Qed.
Lemma lem297583 {A : Type'} (R : type1594 A) (y' : type1596 A) (_6618 : nat) (_6619 : A) : (term691 A R y' _6618 _6619) = (term691 A R y' _6618 _6619).
Proof. exact (eq_refl (term691 A R y' _6618 _6619)). Qed.
Lemma lem297584 {A : Type'} (P : type1597 A) (R : type1594 A) (y' : type1596 A) (_6618 : nat) (_6619 : A) : (term745 A P R y' _6618 _6619) = (term746 A P R y' _6618 _6619).
Proof. exact (MK_COMB (@lem297582 A P _6618 _6619) (@lem297583 A R y' _6618 _6619)). Qed.
Lemma lem297585 {A : Type'} (P : type1597 A) (R : type1594 A) (y' : type1596 A) (_6618 : nat) (_6619 : A) : (term742 A R y' P _6618 _6619) = (term746 A P R y' _6618 _6619).
Proof. exact (TRANS (@lem297577 A P R y' _6618 _6619) (@lem297584 A P R y' _6618 _6619)). Qed.
Lemma lem297588 {A : Type'} (_6618 : nat) (_6619 : A) (P : type1597 A) (R : type1594 A) (y' : type1596 A) (h1 : term634 A P R y') : term746 A P R y' _6618 _6619.
Proof. exact (EQ_MP (@lem297585 A P R y' _6618 _6619) (@lem297574 A _6618 _6619 P R y' h1)). Qed.
Lemma lem297589 {A : Type'} (_6618 : nat) (_6619 : A) (P : type1597 A) (R : type1594 A) (y' : type1596 A) (h1 : term634 A P R y') : term746 A P R y' _6618 _6619.
Proof. exact (@lem297588 A _6618 _6619 P R y' h1). Qed.
Lemma lem297590 {A : Type'} (_6610 : type943 A) (f : nat -> A) (n : nat) (P : type1597 A) (R : type1594 A) (y' : type1596 A) (h1 : term634 A P R y') : term1101 A y' _6610 P R f n.
Proof. exact (@lem297589 A (@I (nat -> nat) S n) (term889 A _6610 P R f n) P R y' h1). Qed.
Lemma lem297593 {A : Type'} (_6610 : type943 A) (y' : type1596 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term511 A _6610) (h2 : term634 A P R y') (h3 : term459 A P R f n y) : term1102 A y' _6610 P R f n.
Proof. exact (@lem297590 A _6610 f n P R y' h2 (@lem297545 A _6610 P R f n y h1 h3)). Qed.
Lemma lem297594 {A : Type'} (_6610 : type943 A) (y' : type1596 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term511 A _6610) (h2 : term634 A P R y') (h3 : term459 A P R f n y) : term1103 A y' _6610 P R f n.
Proof. exact (fun h0 : term1104 A y' _6610 P R f n => @lem297593 A _6610 y' P R f n y h1 h2 h3). Qed.
Lemma lem297596 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem297597 {A : Type'} (y' : type1596 A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term1103 A y' _6610 P R f n) = (term1102 A y' _6610 P R f n).
Proof. exact (@lem297596 (term1102 A y' _6610 P R f n)). Qed.
Lemma lem297598 {A : Type'} (_6610 : type943 A) (y' : type1596 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term511 A _6610) (h2 : term634 A P R y') (h3 : term459 A P R f n y) : term1102 A y' _6610 P R f n.
Proof. exact (EQ_MP (@lem297597 A y' _6610 P R f n) (@lem297594 A _6610 y' P R f n y h1 h2 h3)). Qed.
Lemma lem297616 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem297617 {A : Type'} (_6643 : A) (_6642 : A -> Prop) (_6640 : A -> Prop) (_6641 : A) : (term1008 A _6642 _6643 _6640 _6641) = (term1105 A _6643 _6642 _6640 _6641).
Proof. exact (@lem297616 (@I (A -> Prop) _6642 _6643) (term1080 A _6640 _6642) (term1106 A _6640 _6641)). Qed.
Lemma lem297635 {A : Type'} (_6641 : A) (_6643 : A) : (term1053 A _6641 _6643) = (term1053 A _6641 _6643).
Proof. exact (eq_refl (term1053 A _6641 _6643)). Qed.
Lemma lem297636 {A : Type'} (_6643 : A) (_6642 : A -> Prop) (_6640 : A -> Prop) (_6641 : A) : (term1010 A _6642 _6643 _6640 _6641) = (term1107 A _6643 _6642 _6640 _6641).
Proof. exact (MK_COMB (@lem297635 A _6641 _6643) (@lem297617 A _6643 _6642 _6640 _6641)). Qed.
Lemma lem297640 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem297641 {A : Type'} (_6643 : A) (_6642 : A -> Prop) (_6640 : A -> Prop) (_6641 : A) : (term1107 A _6643 _6642 _6640 _6641) = (term1108 A _6643 _6642 _6640 _6641).
Proof. exact (@lem297640 (@I (A -> Prop) _6642 _6643) (term1056 A _6641 _6643) (term1109 A _6642 _6640 _6641)). Qed.
Lemma lem297671 {A : Type'} (_6643 : A) (_6642 : A -> Prop) (_6640 : A -> Prop) (_6641 : A) : (term1010 A _6642 _6643 _6640 _6641) = (term1108 A _6643 _6642 _6640 _6641).
Proof. exact (TRANS (@lem297636 A _6643 _6642 _6640 _6641) (@lem297641 A _6643 _6642 _6640 _6641)). Qed.
Lemma lem297672 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem297673 {A : Type'} (_6643 : A) (_6642 : A -> Prop) (_6640 : A -> Prop) (_6641 : A) : (term1110 A _6642 _6643 _6640 _6641) = (term1111 A _6643 _6642 _6640 _6641).
Proof. exact (MK_COMB (@lem297672) (@lem297671 A _6643 _6642 _6640 _6641)). Qed.
Lemma lem297703 {A : Type'} (_6643 : A) (_6642 : A -> Prop) (_6640 : A -> Prop) (_6641 : A) : (term1108 A _6643 _6642 _6640 _6641) = (term1108 A _6643 _6642 _6640 _6641).
Proof. exact (eq_refl (term1108 A _6643 _6642 _6640 _6641)). Qed.
Lemma lem297704 {A : Type'} (_6643 : A) (_6642 : A -> Prop) (_6640 : A -> Prop) (_6641 : A) : ((term1010 A _6642 _6643 _6640 _6641) = (term1108 A _6643 _6642 _6640 _6641)) = ((term1108 A _6643 _6642 _6640 _6641) = (term1108 A _6643 _6642 _6640 _6641)).
Proof. exact (MK_COMB (@lem297673 A _6643 _6642 _6640 _6641) (@lem297703 A _6643 _6642 _6640 _6641)). Qed.
Lemma lem297706 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem297707 (x : Prop) : (x = x) = True.
Proof. exact (@lem297706 Prop x). Qed.
Lemma lem297708 {A : Type'} (_6643 : A) (_6642 : A -> Prop) (_6640 : A -> Prop) (_6641 : A) : ((term1108 A _6643 _6642 _6640 _6641) = (term1108 A _6643 _6642 _6640 _6641)) = True.
Proof. exact (@lem297707 (term1108 A _6643 _6642 _6640 _6641)). Qed.
Lemma lem297709 {A : Type'} (_6643 : A) (_6642 : A -> Prop) (_6640 : A -> Prop) (_6641 : A) : ((term1010 A _6642 _6643 _6640 _6641) = (term1108 A _6643 _6642 _6640 _6641)) = True.
Proof. exact (TRANS (@lem297704 A _6643 _6642 _6640 _6641) (@lem297708 A _6643 _6642 _6640 _6641)). Qed.
Lemma lem297710 {A : Type'} (_6643 : A) (_6642 : A -> Prop) (_6640 : A -> Prop) (_6641 : A) : True = ((term1010 A _6642 _6643 _6640 _6641) = (term1108 A _6643 _6642 _6640 _6641)).
Proof. exact (SYM (@lem297709 A _6643 _6642 _6640 _6641)). Qed.
Lemma lem297711 {A : Type'} (_6643 : A) (_6642 : A -> Prop) (_6640 : A -> Prop) (_6641 : A) : (term1010 A _6642 _6643 _6640 _6641) = (term1108 A _6643 _6642 _6640 _6641).
Proof. exact (EQ_MP (@lem297710 A _6643 _6642 _6640 _6641) (@lem0)). Qed.
Lemma lem297712 {A : Type'} (_6643 : A) (_6642 : A -> Prop) (_6640 : A -> Prop) (_6641 : A) : term1108 A _6643 _6642 _6640 _6641.
Proof. exact (EQ_MP (@lem297711 A _6643 _6642 _6640 _6641) (@lem296861 A _6642 _6643 _6640 _6641)). Qed.
Lemma lem297714 (b : Prop) (a : Prop) : (a \/ b) = (term203 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem297715 {A : Type'} (_6640 : A -> Prop) (_6641 : A) (_6642 : A -> Prop) (_6643 : A) : (term1108 A _6643 _6642 _6640 _6641) = (term1112 A _6640 _6641 _6642 _6643).
Proof. exact (@lem297714 (term1113 A _6643 _6642 _6640 _6641) (@I (A -> Prop) _6642 _6643)). Qed.
Lemma lem297717 (a : Prop) (b : Prop) : (term206 a b) = (term207 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem297718 {A : Type'} (_6643 : A) (_6642 : A -> Prop) (_6640 : A -> Prop) (_6641 : A) : (term1114 A _6643 _6642 _6640 _6641) = (term1115 A _6643 _6642 _6640 _6641).
Proof. exact (@lem297717 (term1056 A _6641 _6643) (term1109 A _6642 _6640 _6641)). Qed.
Lemma lem297720 (a : Prop) : (term210 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem297721 {A : Type'} (_6641 : A) (_6643 : A) : (term1063 A _6641 _6643) = (_6641 = _6643).
Proof. exact (@lem297720 (_6641 = _6643)). Qed.
Lemma lem297722 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem297723 {A : Type'} (_6641 : A) (_6643 : A) : (term1064 A _6641 _6643) = (term1065 A _6641 _6643).
Proof. exact (MK_COMB (@lem297722) (@lem297721 A _6641 _6643)). Qed.
Lemma lem297725 (a : Prop) (b : Prop) : (term206 a b) = (term207 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem297726 {A : Type'} (_6642 : A -> Prop) (_6640 : A -> Prop) (_6641 : A) : (term1116 A _6642 _6640 _6641) = (term1117 A _6642 _6640 _6641).
Proof. exact (@lem297725 (term1080 A _6640 _6642) (term1106 A _6640 _6641)). Qed.
Lemma lem297728 (a : Prop) : (term210 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem297729 {A : Type'} (_6640 : A -> Prop) (_6642 : A -> Prop) : (term1090 A _6640 _6642) = (_6640 = _6642).
Proof. exact (@lem297728 (_6640 = _6642)). Qed.
Lemma lem297730 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem297731 {A : Type'} (_6640 : A -> Prop) (_6642 : A -> Prop) : (term1091 A _6640 _6642) = (term1092 A _6640 _6642).
Proof. exact (MK_COMB (@lem297730) (@lem297729 A _6640 _6642)). Qed.
Lemma lem297733 (a : Prop) : (term210 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem297734 {A : Type'} (_6640 : A -> Prop) (_6641 : A) : (term1118 A _6640 _6641) = (@I (A -> Prop) _6640 _6641).
Proof. exact (@lem297733 (@I (A -> Prop) _6640 _6641)). Qed.
Lemma lem297735 {A : Type'} (_6642 : A -> Prop) (_6640 : A -> Prop) (_6641 : A) : (term1117 A _6642 _6640 _6641) = (term1119 A _6642 _6640 _6641).
Proof. exact (MK_COMB (@lem297731 A _6640 _6642) (@lem297734 A _6640 _6641)). Qed.
Lemma lem297736 {A : Type'} (_6642 : A -> Prop) (_6640 : A -> Prop) (_6641 : A) : (term1116 A _6642 _6640 _6641) = (term1119 A _6642 _6640 _6641).
Proof. exact (TRANS (@lem297726 A _6642 _6640 _6641) (@lem297735 A _6642 _6640 _6641)). Qed.
Lemma lem297737 {A : Type'} (_6643 : A) (_6642 : A -> Prop) (_6640 : A -> Prop) (_6641 : A) : (term1115 A _6643 _6642 _6640 _6641) = (term1120 A _6643 _6642 _6640 _6641).
Proof. exact (MK_COMB (@lem297723 A _6641 _6643) (@lem297736 A _6642 _6640 _6641)). Qed.
Lemma lem297738 {A : Type'} (_6643 : A) (_6642 : A -> Prop) (_6640 : A -> Prop) (_6641 : A) : (term1114 A _6643 _6642 _6640 _6641) = (term1120 A _6643 _6642 _6640 _6641).
Proof. exact (TRANS (@lem297718 A _6643 _6642 _6640 _6641) (@lem297737 A _6643 _6642 _6640 _6641)). Qed.
Lemma lem297739 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem297740 {A : Type'} (_6643 : A) (_6642 : A -> Prop) (_6640 : A -> Prop) (_6641 : A) : (term1121 A _6643 _6642 _6640 _6641) = (term1122 A _6643 _6642 _6640 _6641).
Proof. exact (MK_COMB (@lem297739) (@lem297738 A _6643 _6642 _6640 _6641)). Qed.
Lemma lem297741 {A : Type'} (_6642 : A -> Prop) (_6643 : A) : (@I (A -> Prop) _6642 _6643) = (@I (A -> Prop) _6642 _6643).
Proof. exact (eq_refl (@I (A -> Prop) _6642 _6643)). Qed.
Lemma lem297742 {A : Type'} (_6640 : A -> Prop) (_6641 : A) (_6642 : A -> Prop) (_6643 : A) : (term1112 A _6640 _6641 _6642 _6643) = (term1123 A _6640 _6641 _6642 _6643).
Proof. exact (MK_COMB (@lem297740 A _6643 _6642 _6640 _6641) (@lem297741 A _6642 _6643)). Qed.
Lemma lem297743 {A : Type'} (_6640 : A -> Prop) (_6641 : A) (_6642 : A -> Prop) (_6643 : A) : (term1108 A _6643 _6642 _6640 _6641) = (term1123 A _6640 _6641 _6642 _6643).
Proof. exact (TRANS (@lem297715 A _6640 _6641 _6642 _6643) (@lem297742 A _6640 _6641 _6642 _6643)). Qed.
Lemma lem297745 {A : Type'} (y' : type1596 A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term511 A _6610) (h2 : term634 A P R y') (h3 : term515 A _6610 P R f) (h4 : term459 A P R f n y) : term1124 A y' _6610 P R f n.
Proof. exact (conj (@lem297518 A n _6610 P R f h3) (@lem297598 A _6610 y' P R f n y h1 h2 h4)). Qed.
Lemma lem297746 {A : Type'} (y' : type1596 A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term511 A _6610) (h2 : term634 A P R y') (h3 : term515 A _6610 P R f) (h4 : term459 A P R f n y) : term1125 A y' _6610 P R f n.
Proof. exact (conj (@lem297242 A y' _6610 P R f n) (@lem297745 A y' _6610 P R f n y h1 h2 h3 h4)). Qed.
Lemma lem297748 {A : Type'} (_6640 : A -> Prop) (_6641 : A) (_6642 : A -> Prop) (_6643 : A) : term1123 A _6640 _6641 _6642 _6643.
Proof. exact (EQ_MP (@lem297743 A _6640 _6641 _6642 _6643) (@lem297712 A _6643 _6642 _6640 _6641)). Qed.
Lemma lem297749 {A : Type'} (_6640 : A -> Prop) (_6641 : A) (_6642 : A -> Prop) (_6643 : A) : term1123 A _6640 _6641 _6642 _6643.
Proof. exact (@lem297748 A _6640 _6641 _6642 _6643). Qed.
Lemma lem297750 {A : Type'} (y' : type1596 A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : term1126 A y' _6610 P R f n.
Proof. exact (@lem297749 A (term1073 A _6610 P R f n) (term1044 A y' _6610 P R f n) (term938 A R f n) (term1044 A y' _6610 P R f n)). Qed.
Lemma lem297753 {A : Type'} (y' : type1596 A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term511 A _6610) (h2 : term634 A P R y') (h3 : term515 A _6610 P R f) (h4 : term459 A P R f n y) : term1127 A y' _6610 P R f n.
Proof. exact (@lem297750 A y' _6610 P R f n (@lem297746 A y' _6610 P R f n y h1 h2 h3 h4)). Qed.
Lemma lem297754 {A : Type'} (y' : type1596 A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term511 A _6610) (h2 : term634 A P R y') (h3 : term515 A _6610 P R f) (h4 : term459 A P R f n y) : term1128 A y' _6610 P R f n.
Proof. exact (fun h0 : term1129 A y' _6610 P R f n => @lem297753 A y' _6610 P R f n y h1 h2 h3 h4). Qed.
Lemma lem297756 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem297757 {A : Type'} (y' : type1596 A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term1128 A y' _6610 P R f n) = (term1127 A y' _6610 P R f n).
Proof. exact (@lem297756 (term1127 A y' _6610 P R f n)). Qed.
Lemma lem297758 {A : Type'} (y' : type1596 A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term511 A _6610) (h2 : term634 A P R y') (h3 : term515 A _6610 P R f) (h4 : term459 A P R f n y) : term1127 A y' _6610 P R f n.
Proof. exact (EQ_MP (@lem297757 A y' _6610 P R f n) (@lem297754 A y' _6610 P R f n y h1 h2 h3 h4)). Qed.
Lemma lem297760 (a : Prop) (b : Prop) : (term751 a b) = (term752 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem297761 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6617 : A) : (term956 A P R f n _6617) = (term1130 A P R f n _6617).
Proof. exact (@lem297760 (term951 A P n _6617) (term940 A R f n _6617)). Qed.
Lemma lem297763 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem297764 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6617 : A) : (term1130 A P R f n _6617) = (term1131 A P R f n _6617).
Proof. exact (@lem297763 (term1132 A P R f n _6617)). Qed.
Lemma lem297765 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6617 : A) : (term956 A P R f n _6617) = (term1131 A P R f n _6617).
Proof. exact (TRANS (@lem297761 A P R f n _6617) (@lem297764 A P R f n _6617)). Qed.
Lemma lem297767 {A : Type'} (y' : type1596 A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term511 A _6610) (h2 : term634 A P R y') (h3 : term515 A _6610 P R f) (h4 : term459 A P R f n y) : term1133 A y' _6610 P R f n.
Proof. exact (conj (@lem297233 A _6610 y' P R f n y h1 h2 h4) (@lem297758 A y' _6610 P R f n y h1 h2 h3 h4)). Qed.
Lemma lem297769 {A : Type'} (_6617 : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term767 A P R f n) : term1131 A P R f n _6617.
Proof. exact (EQ_MP (@lem297765 A P R f n _6617) (@lem296758 A _6617 P R f n h1)). Qed.
Lemma lem297770 {A : Type'} (_6617 : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term767 A P R f n) : term1131 A P R f n _6617.
Proof. exact (@lem297769 A _6617 P R f n h1). Qed.
Lemma lem297771 {A : Type'} (y' : type1596 A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term767 A P R f n) : term1134 A y' _6610 P R f n.
Proof. exact (@lem297770 A (term1044 A y' _6610 P R f n) P R f n h1). Qed.
Lemma lem297774 {A : Type'} (y' : type1596 A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term511 A _6610) (h2 : term634 A P R y') (h3 : term515 A _6610 P R f) (h4 : term767 A P R f n) (h5 : term459 A P R f n y) : False.
Proof. exact (@lem297771 A y' _6610 P R f n h4 (@lem297767 A y' _6610 P R f n y h1 h2 h3 h5)). Qed.
Lemma lem297775 {A : Type'} (y' : type1596 A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term511 A _6610) (h2 : term634 A P R y') (h3 : term515 A _6610 P R f) (h4 : term767 A P R f n) (h5 : term459 A P R f n y) : term189.
Proof. exact (fun h0 : ~ False => @lem297774 A y' _6610 P R f n y h1 h2 h3 h4 h5). Qed.
Lemma lem297777 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem297778 : term189 = False.
Proof. exact (@lem297777 False). Qed.
Lemma lem297780 {A : Type'} (y' : type1596 A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term511 A _6610) (h2 : term634 A P R y') (h3 : term515 A _6610 P R f) (h4 : term767 A P R f n) (h5 : term459 A P R f n y) : False.
Proof. exact (EQ_MP (@lem297778) (@lem297775 A y' _6610 P R f n y h1 h2 h3 h4 h5)). Qed.
Lemma lem297781 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (y : A) (h1 : term511 A _6610) (h2 : term312 A P R) (h3 : term515 A _6610 P R f) (h4 : term767 A P R f n) (h5 : term459 A P R f n y) : False.
Proof. exact (ex_elim (@lem295750 A P R h2) (fun y' : type1596 A => fun h0 : term636 A P R y' => @lem297780 A y' _6610 P R f n y h1 h0 h3 h4 h5)). Qed.
Lemma lem297782 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term511 A _6610) (h2 : term312 A P R) (h3 : term515 A _6610 P R f) (h4 : term435 A P R f n) (h5 : term767 A P R f n) : False.
Proof. exact (ex_elim (@lem295830 A P R f n h4) (fun y : A => fun h0 : term436 A P R f n y => @lem297781 A _6610 P R f n y h1 h2 h3 h5 h0)). Qed.
Lemma lem297783 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term511 A _6610) (h2 : term312 A P R) (h3 : term515 A _6610 P R f) (h4 : term435 A P R f n) (h5 : term767 A P R f n) : (term435 A P R f n) = False.
Proof. exact (prop_ext (fun h6 : term435 A P R f n => @lem297782 A _6610 P R f n h1 h2 h3 h4 h5) (fun h6 : False => @lem295830 A P R f n h4)). Qed.
Lemma lem297784 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term511 A _6610) (h2 : term312 A P R) (h3 : term515 A _6610 P R f) (h4 : term435 A P R f n) (h5 : term767 A P R f n) : False.
Proof. exact (EQ_MP (@lem297783 A _6610 P R f n h1 h2 h3 h4 h5) (@lem295830 A P R f n h4)). Qed.
Lemma lem297785 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term511 A _6610) (h2 : term312 A P R) (h3 : term515 A _6610 P R f) (h4 : term435 A P R f n) (h5 : term767 A P R f n) : (term515 A _6610 P R f) = False.
Proof. exact (prop_ext (fun h6 : term515 A _6610 P R f => @lem297784 A _6610 P R f n h1 h2 h3 h4 h5) (fun h6 : False => @lem295769 A _6610 P R f h3)). Qed.
Lemma lem297786 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term511 A _6610) (h2 : term312 A P R) (h3 : term515 A _6610 P R f) (h4 : term435 A P R f n) (h5 : term767 A P R f n) : False.
Proof. exact (EQ_MP (@lem297785 A _6610 P R f n h1 h2 h3 h4 h5) (@lem295769 A _6610 P R f h3)). Qed.
Lemma lem297787 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term511 A _6610) (h2 : term312 A P R) (h3 : term515 A _6610 P R f) (h4 : term435 A P R f n) (h5 : term767 A P R f n) : (term767 A P R f n) = False.
Proof. exact (prop_ext (fun h6 : term767 A P R f n => @lem297786 A _6610 P R f n h1 h2 h3 h4 h5) (fun h6 : False => @lem295316 A P R f n h5)). Qed.
Lemma lem297788 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term511 A _6610) (h2 : term312 A P R) (h3 : term515 A _6610 P R f) (h4 : term435 A P R f n) (h5 : term767 A P R f n) : False.
Proof. exact (EQ_MP (@lem297787 A _6610 P R f n h1 h2 h3 h4 h5) (@lem295316 A P R f n h5)). Qed.
Lemma lem297789 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term511 A _6610) (h2 : term312 A P R) (h3 : term515 A _6610 P R f) (h4 : term435 A P R f n) : term770 A P R f n.
Proof. exact (fun h0 : term767 A P R f n => @lem297788 A _6610 P R f n h1 h2 h3 h4 h0). Qed.
Lemma lem297790 {A : Type'} (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (h1 : term511 A _6610) (h2 : term312 A P R) (h3 : term515 A _6610 P R f) (h4 : term435 A P R f n) : term766 A P R f n.
Proof. exact (EQ_MP (@lem295315 A P R f n) (@lem297789 A _6610 P R f n h1 h2 h3 h4)). Qed.
Lemma lem297791 {A : Type'} (n : nat) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term511 A _6610) (h2 : term312 A P R) (h3 : term515 A _6610 P R f) : term801 A P R f n.
Proof. exact (fun h0 : term435 A P R f n => @lem297790 A _6610 P R f n h1 h2 h3 h0). Qed.
Lemma lem297792 {A : Type'} (f : nat -> A) (n : nat) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (h1 : term511 A _6610) (h2 : term312 A P R) : term802 A _6610 P R f n.
Proof. exact (fun h0 : term515 A _6610 P R f => @lem297791 A n _6610 P R f h1 h2 h0). Qed.
Lemma lem297793 {A : Type'} (a : A) (f : nat -> A) (n : nat) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (h1 : term511 A _6610) (h2 : term312 A P R) : term803 A a _6610 P R f n.
Proof. exact (fun h0 : (term286 A f) = a => @lem297792 A f n _6610 P R h1 h2). Qed.
Lemma lem297794 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6610 : type943 A) (h1 : term511 A _6610) : term804 A a _6610 P R f n.
Proof. exact (fun h0 : term312 A P R => @lem297793 A a f n _6610 P R h1 h0). Qed.
Lemma lem297795 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (_6610 : type943 A) (h1 : term511 A _6610) : term805 A a _6610 P R f n.
Proof. exact (fun h0 : term313 A P a => @lem297794 A a P R f n _6610 h1). Qed.
Lemma lem297796 {A : Type'} (a : A) (_6610 : type943 A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : term806 A a _6610 P R f n.
Proof. exact (fun h0 : term511 A _6610 => @lem297795 A a P R f n _6610 h0). Qed.
Lemma lem297801 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : term809 A a P R f n.
Proof. exact (fun _6610 : type943 A => @lem297796 A a _6610 P R f n). Qed.
Lemma lem297806 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : term813 A P R f n.
Proof. exact (fun a : A => @lem297801 A a P R f n). Qed.
Lemma lem297811 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : term817 A R f n.
Proof. exact (fun P : type1597 A => @lem297806 A P R f n). Qed.
Lemma lem297816 {A : Type'} (f : nat -> A) (n : nat) : term821 A f n.
Proof. exact (fun R : type1594 A => @lem297811 A R f n). Qed.
Lemma lem297821 {A : Type'} (n : nat) : term825 A n.
Proof. exact (fun f : nat -> A => @lem297816 A f n). Qed.
Lemma lem297826 {A : Type'} : term829 A.
Proof. exact (fun n : nat => @lem297821 A n). Qed.
Lemma lem297827 {A : Type'} : term828 A.
Proof. exact (EQ_MP (@lem295305 A) (@lem297826 A)). Qed.
Lemma lem297828 {A : Type'} (n : nat) : term1135 A n.
Proof. exact (@lem297827 A n). Qed.
Lemma lem297829 {A : Type'} (n : nat) : (term1135 A n) = (term824 A n).
Proof. exact (eq_refl (term1135 A n)). Qed.
Lemma lem297830 {A : Type'} (n : nat) : term824 A n.
Proof. exact (EQ_MP (@lem297829 A n) (@lem297828 A n)). Qed.
Lemma lem297831 {A : Type'} (n : nat) (f : nat -> A) : term1136 A n f.
Proof. exact (@lem297830 A n f). Qed.
Lemma lem297832 {A : Type'} (f : nat -> A) (n : nat) : (term1136 A n f) = (term820 A f n).
Proof. exact (eq_refl (term1136 A n f)). Qed.
Lemma lem297833 {A : Type'} (f : nat -> A) (n : nat) : term820 A f n.
Proof. exact (EQ_MP (@lem297832 A f n) (@lem297831 A n f)). Qed.
Lemma lem297834 {A : Type'} (f : nat -> A) (n : nat) (R : type1594 A) : term1137 A f n R.
Proof. exact (@lem297833 A f n R). Qed.
Lemma lem297835 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term1137 A f n R) = (term816 A R f n).
Proof. exact (eq_refl (term1137 A f n R)). Qed.
Lemma lem297836 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : term816 A R f n.
Proof. exact (EQ_MP (@lem297835 A R f n) (@lem297834 A f n R)). Qed.
Lemma lem297837 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) (P : type1597 A) : term1138 A R f n P.
Proof. exact (@lem297836 A R f n P). Qed.
Lemma lem297838 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term1138 A R f n P) = (term812 A P R f n).
Proof. exact (eq_refl (term1138 A R f n P)). Qed.
Lemma lem297839 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : term812 A P R f n.
Proof. exact (EQ_MP (@lem297838 A P R f n) (@lem297837 A R f n P)). Qed.
Lemma lem297840 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) (a : A) : term1139 A P R f n a.
Proof. exact (@lem297839 A P R f n a). Qed.
Lemma lem297841 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term1139 A P R f n a) = (term788 A a P R f n).
Proof. exact (eq_refl (term1139 A P R f n a)). Qed.
Lemma lem297842 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : term788 A a P R f n.
Proof. exact (EQ_MP (@lem297841 A a P R f n) (@lem297840 A P R f n a)). Qed.
Lemma lem297843 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : term780 A a P R f n.
Proof. exact (@lem294766 A a P R f n (@lem297842 A a P R f n)). Qed.
Lemma lem297844 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : term779 A a P R f n.
Proof. exact (EQ_MP (@lem294624 A a P R f n) (@lem297843 A a P R f n)). Qed.
Lemma lem297845 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) (P : type1597 A) (a : A) (h1 : term313 A P a) : term777 A a P R f n.
Proof. exact (@lem297844 A a P R f n (@lem291893 A P a h1)). Qed.
Lemma lem297846 {A : Type'} (f : nat -> A) (n : nat) (R : type1594 A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term313 A P a) : term775 A a P R f n.
Proof. exact (@lem297845 A R f n P a h2 (@lem291892 A P R h1)). Qed.
Lemma lem297847 {A : Type'} (n : nat) (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : (term286 A f) = a) (h3 : term313 A P a) : term773 A P R f n.
Proof. exact (@lem297846 A f n R P a h1 h3 (@lem291923 A f a h2)). Qed.
Lemma lem297848 {A : Type'} (n : nat) (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term287 A P R f) (h3 : (term286 A f) = a) (h4 : term313 A P a) : term771 A P R f n.
Proof. exact (@lem297847 A n R f P a h1 h3 h4 (@lem291922 A P R f h2)). Qed.
Lemma lem297849 {A : Type'} (R : type1594 A) (n : nat) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term287 A P R f) (h3 : term403 A P R f n) (h4 : (term286 A f) = a) (h5 : term313 A P a) : term763 A P R f n.
Proof. exact (@lem297848 A n R f P a h1 h2 h4 h5 (@lem292155 A P R f n h3)). Qed.
Lemma lem297850 {A : Type'} (R : type1594 A) (n : nat) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term287 A P R f) (h3 : term764 A P R f n) (h4 : term403 A P R f n) (h5 : (term286 A f) = a) (h6 : term313 A P a) : False.
Proof. exact (@lem297849 A R n f P a h1 h2 h4 h5 h6 (@lem294567 A P R f n h3)). Qed.
Lemma lem297851 {A : Type'} (R : type1594 A) (n : nat) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term287 A P R f) (h3 : term764 A P R f n) (h4 : term403 A P R f n) (h5 : (term286 A f) = a) (h6 : term313 A P a) : (term764 A P R f n) = False.
Proof. exact (prop_ext (fun h7 : term764 A P R f n => @lem297850 A R n f P a h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem294567 A P R f n h3)). Qed.
Lemma lem297852 {A : Type'} (R : type1594 A) (n : nat) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term287 A P R f) (h3 : term764 A P R f n) (h4 : term403 A P R f n) (h5 : (term286 A f) = a) (h6 : term313 A P a) : False.
Proof. exact (EQ_MP (@lem297851 A R n f P a h1 h2 h3 h4 h5 h6) (@lem294567 A P R f n h3)). Qed.
Lemma lem297853 {A : Type'} (R : type1594 A) (n : nat) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term287 A P R f) (h3 : term403 A P R f n) (h4 : (term286 A f) = a) (h5 : term313 A P a) : term763 A P R f n.
Proof. exact (fun h0 : term764 A P R f n => @lem297852 A R n f P a h1 h2 h0 h3 h4 h5). Qed.
Lemma lem297854 {A : Type'} (R : type1594 A) (n : nat) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term287 A P R f) (h3 : term403 A P R f n) (h4 : (term286 A f) = a) (h5 : term313 A P a) : term417 A P R f n.
Proof. exact (EQ_MP (@lem294566 A P R f n) (@lem297853 A R n f P a h1 h2 h3 h4 h5)). Qed.
Lemma lem297855 {A : Type'} (n : nat) (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term287 A P R f) (h3 : (term286 A f) = a) (h4 : term313 A P a) : term419 A P R f n.
Proof. exact (fun h0 : term403 A P R f n => @lem297854 A R n f P a h1 h2 h0 h3 h4). Qed.
Lemma lem297860 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term287 A P R f) (h3 : (term286 A f) = a) (h4 : term313 A P a) : term423 A P R f.
Proof. exact (fun n : nat => @lem297855 A n R f P a h1 h2 h3 h4). Qed.
Lemma lem297861 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term287 A P R f) (h3 : (term286 A f) = a) (h4 : term313 A P a) : term425 A P R f.
Proof. exact (conj (@lem294562 A R f P a h1 h2 h3 h4) (@lem297860 A R f P a h1 h2 h3 h4)). Qed.
Lemma lem297862 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term287 A P R f) (h3 : (term286 A f) = a) (h4 : term313 A P a) : term406 A P R f.
Proof. exact (@lem292154 A P R f (@lem297861 A R f P a h1 h2 h3 h4)). Qed.
Lemma lem297863 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term287 A P R f) (h3 : (term286 A f) = a) (h4 : term313 A P a) : term373 A P R f.
Proof. exact (EQ_MP (@lem292131 A R f P a h2 h3 h4) (@lem297862 A R f P a h1 h2 h3 h4)). Qed.
Lemma lem297864 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term287 A P R f) (h3 : (term286 A f) = a) (h4 : term313 A P a) : term350 A P R f.
Proof. exact (EQ_MP (@lem292022 A P R f) (@lem297863 A R f P a h1 h2 h3 h4)). Qed.
Lemma lem297865 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term287 A P R f) (h3 : (term286 A f) = a) (h4 : term313 A P a) : term321 A a P R f.
Proof. exact (EQ_MP (@lem291998 A P R f a h2 h3) (@lem297864 A R f P a h1 h2 h3 h4)). Qed.
Lemma lem297866 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term291 A a P R f) : term287 A P R f.
Proof. exact (proj2 (@lem291921 A a P R f h1)). Qed.
Lemma lem297867 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) (h1 : term291 A a P R f) : (term286 A f) = a.
Proof. exact (proj1 (@lem291921 A a P R f h1)). Qed.
Lemma lem297868 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term287 A P R f) (h3 : (term286 A f) = a) (h4 : term313 A P a) : (term287 A P R f) = (term321 A a P R f).
Proof. exact (prop_ext (fun h5 : term287 A P R f => @lem297865 A R f P a h1 h2 h3 h4) (fun h5 : term321 A a P R f => @lem291922 A P R f h2)). Qed.
Lemma lem297869 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term287 A P R f) (h3 : (term286 A f) = a) (h4 : term313 A P a) : term321 A a P R f.
Proof. exact (EQ_MP (@lem297868 A R f P a h1 h2 h3 h4) (@lem291922 A P R f h2)). Qed.
Lemma lem297870 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term287 A P R f) (h3 : (term286 A f) = a) (h4 : term313 A P a) : ((term286 A f) = a) = (term321 A a P R f).
Proof. exact (prop_ext (fun h5 : (term286 A f) = a => @lem297869 A R f P a h1 h2 h3 h4) (fun h5 : term321 A a P R f => @lem291923 A f a h3)). Qed.
Lemma lem297871 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term287 A P R f) (h3 : (term286 A f) = a) (h4 : term313 A P a) : term321 A a P R f.
Proof. exact (EQ_MP (@lem297870 A R f P a h1 h2 h3 h4) (@lem291923 A f a h3)). Qed.
Lemma lem297872 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term291 A a P R f) (h3 : (term286 A f) = a) (h4 : term313 A P a) : (term287 A P R f) = (term321 A a P R f).
Proof. exact (prop_ext (fun h5 : term287 A P R f => @lem297871 A R f P a h1 h5 h3 h4) (fun h5 : term321 A a P R f => @lem297866 A a P R f h2)). Qed.
Lemma lem297873 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term291 A a P R f) (h3 : (term286 A f) = a) (h4 : term313 A P a) : term321 A a P R f.
Proof. exact (EQ_MP (@lem297872 A R f P a h1 h2 h3 h4) (@lem297866 A a P R f h2)). Qed.
Lemma lem297874 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term291 A a P R f) (h3 : term313 A P a) : ((term286 A f) = a) = (term321 A a P R f).
Proof. exact (prop_ext (fun h4 : (term286 A f) = a => @lem297873 A R f P a h1 h2 h4 h3) (fun h4 : term321 A a P R f => @lem297867 A a P R f h2)). Qed.
Lemma lem297875 {A : Type'} (R : type1594 A) (f : nat -> A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term291 A a P R f) (h3 : term313 A P a) : term321 A a P R f.
Proof. exact (EQ_MP (@lem297874 A R f P a h1 h2 h3) (@lem297867 A a P R f h2)). Qed.
Lemma lem297876 {A : Type'} (f : nat -> A) (R : type1594 A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term313 A P a) : term323 A a P R f.
Proof. exact (fun h0 : term291 A a P R f => @lem297875 A R f P a h1 h0 h2). Qed.
Lemma lem297881 {A : Type'} (R : type1594 A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term313 A P a) : term327 A a P R.
Proof. exact (fun f : nat -> A => @lem297876 A f R P a h1 h2). Qed.
Lemma lem297882 {A : Type'} (R : type1594 A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term313 A P a) : term338 A a P R.
Proof. exact (@lem291920 A a P R (@lem297881 A R P a h1 h2)). Qed.
Lemma lem297883 {A : Type'} (R : type1594 A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term313 A P a) : term336 A a P R.
Proof. exact (@lem297882 A R P a h1 h2 (@lem291890 A a P R)). Qed.
Lemma lem297884 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (h1 : term311 A a P R) : term312 A P R.
Proof. exact (proj2 (@lem291891 A a P R h1)). Qed.
Lemma lem297885 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (h1 : term311 A a P R) : term313 A P a.
Proof. exact (proj1 (@lem291891 A a P R h1)). Qed.
Lemma lem297886 {A : Type'} (R : type1594 A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term313 A P a) : (term312 A P R) = (term336 A a P R).
Proof. exact (prop_ext (fun h3 : term312 A P R => @lem297883 A R P a h1 h2) (fun h3 : term336 A a P R => @lem291892 A P R h1)). Qed.
Lemma lem297887 {A : Type'} (R : type1594 A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term313 A P a) : term336 A a P R.
Proof. exact (EQ_MP (@lem297886 A R P a h1 h2) (@lem291892 A P R h1)). Qed.
Lemma lem297888 {A : Type'} (R : type1594 A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term313 A P a) : (term313 A P a) = (term336 A a P R).
Proof. exact (prop_ext (fun h3 : term313 A P a => @lem297887 A R P a h1 h2) (fun h3 : term336 A a P R => @lem291893 A P a h2)). Qed.
Lemma lem297889 {A : Type'} (R : type1594 A) (P : type1597 A) (a : A) (h1 : term312 A P R) (h2 : term313 A P a) : term336 A a P R.
Proof. exact (EQ_MP (@lem297888 A R P a h1 h2) (@lem291893 A P a h2)). Qed.
Lemma lem297890 {A : Type'} (R : type1594 A) (P : type1597 A) (a : A) (h1 : term311 A a P R) (h2 : term313 A P a) : (term312 A P R) = (term336 A a P R).
Proof. exact (prop_ext (fun h3 : term312 A P R => @lem297889 A R P a h3 h2) (fun h3 : term336 A a P R => @lem297884 A a P R h1)). Qed.
Lemma lem297891 {A : Type'} (R : type1594 A) (P : type1597 A) (a : A) (h1 : term311 A a P R) (h2 : term313 A P a) : term336 A a P R.
Proof. exact (EQ_MP (@lem297890 A R P a h1 h2) (@lem297884 A a P R h1)). Qed.
Lemma lem297892 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (h1 : term311 A a P R) : (term313 A P a) = (term336 A a P R).
Proof. exact (prop_ext (fun h2 : term313 A P a => @lem297891 A R P a h1 h2) (fun h2 : term336 A a P R => @lem297885 A a P R h1)). Qed.
Lemma lem297893 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (h1 : term311 A a P R) : term336 A a P R.
Proof. exact (EQ_MP (@lem297892 A a P R h1) (@lem297885 A a P R h1)). Qed.
Lemma lem297894 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : term1140 A a P R.
Proof. exact (fun h0 : term311 A a P R => @lem297893 A a P R h0). Qed.
Lemma lem297899 {A : Type'} (P : type1597 A) (R : type1594 A) : term1141 A P R.
Proof. exact (fun a : A => @lem297894 A a P R). Qed.
Lemma lem297904 {A : Type'} (P : type1597 A) : term1142 A P.
Proof. exact (fun R : type1594 A => @lem297899 A P R). Qed.
Lemma lem297909 {A : Type'} : term1143 A.
Proof. exact (fun P : type1597 A => @lem297904 A P). Qed.
