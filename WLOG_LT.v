Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import WLOG_LT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import LT_CASES_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
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
Lemma lem109478 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem109479 (P : type1605) : (term1 P) = (term2 P).
Proof. exact (@lem109478 (term1 P)). Qed.
Lemma lem109480 (P : type1605) : (term2 P) = (term1 P).
Proof. exact (SYM (@lem109479 P)). Qed.
Lemma lem109481 (P : type1605) (h1 : term3 P) : term3 P.
Proof. exact (h1). Qed.
Lemma lem109484 (P : type1605) (h1 : term4 P) : term4 P.
Proof. exact (h1). Qed.
Lemma lem109485 (P : type1605) : term5 P.
Proof. exact (fun h0 : term4 P => @lem109484 P h0). Qed.
Lemma lem109486 (P : type1605) (h1 : term5 P) : term5 P.
Proof. exact (h1). Qed.
Lemma lem109487 (P : type1605) (h1 : term4 P) : term4 P.
Proof. exact (h1). Qed.
Lemma lem109488 (P : type1605) (h1 : term4 P) (h2 : term5 P) : term4 P.
Proof. exact (@lem109486 P h2 (@lem109487 P h1)). Qed.
Lemma lem109489 (P : type1605) (h1 : term4 P) : term6 P.
Proof. exact (fun h0 : term5 P => @lem109488 P h1 h0). Qed.
Lemma lem109490 (P : type1605) (h1 : term5 P) : term5 P.
Proof. exact (h1). Qed.
Lemma lem109491 (P : type1605) (h1 : term4 P) (h2 : term5 P) : term4 P.
Proof. exact (@lem109489 P h1 (@lem109490 P h2)). Qed.
Lemma lem109492 (P : type1605) (h1 : term5 P) : term5 P.
Proof. exact (fun h0 : term4 P => @lem109491 P h0 h1). Qed.
Lemma lem109493 (P : type1605) : term7 P.
Proof. exact (fun h0 : term5 P => @lem109492 P h0). Qed.
Lemma lem109496 (P : type1605) : term5 P.
Proof. exact (@lem109493 P (@lem109485 P)). Qed.
Lemma lem109540 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem109541 : term8 = term9.
Proof. exact (@lem109540 term10). Qed.
Lemma lem109598 (P : type1605) : (term11 P) = (term11 P).
Proof. exact (eq_refl (term11 P)). Qed.
Lemma lem109599 (P : type1605) : (term4 P) = (term12 P).
Proof. exact (MK_COMB (@lem109598 P) (@lem109541)). Qed.
Lemma lem109602 : term13 = term14.
Proof. exact (fun_ext (fun P : type1605 => @lem109599 P)). Qed.
Lemma lem109603 : (@all (nat -> nat -> Prop)) = (@all (nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> Prop))). Qed.
Lemma lem109612 : term15 = term16.
Proof. exact (MK_COMB (@lem109603) (@lem109602)). Qed.
Lemma lem109621 (m : nat) (n : nat) : (term17 m n) = (term17 m n).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem109622 (m : nat) : (term18 m) = (term18 m).
Proof. exact (fun_ext (fun n : nat => @lem109621 m n)). Qed.
Lemma lem109623 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109624 (m : nat) : (term19 m) = (term19 m).
Proof. exact (MK_COMB (@lem109623) (@lem109622 m)). Qed.
Lemma lem109625 : term20 = term20.
Proof. exact (fun_ext (fun m : nat => @lem109624 m)). Qed.
Lemma lem109626 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109627 : term10 = term10.
Proof. exact (MK_COMB (@lem109626) (@lem109625)). Qed.
Lemma lem109628 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem109629 : term9 = term9.
Proof. exact (MK_COMB (@lem109628) (@lem109627)). Qed.
Lemma lem109630 (P : type1605) (m : nat) (y : nat) : (P m y) = (P m y).
Proof. exact (eq_refl (P m y)). Qed.
Lemma lem109631 (P : type1605) (m : nat) : (term21 P m) = (term21 P m).
Proof. exact (fun_ext (fun y : nat => @lem109630 P m y)). Qed.
Lemma lem109632 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109633 (P : type1605) (m : nat) : (term22 P m) = (term22 P m).
Proof. exact (MK_COMB (@lem109632) (@lem109631 P m)). Qed.
Lemma lem109634 (P : type1605) : (term23 P) = (term23 P).
Proof. exact (fun_ext (fun m : nat => @lem109633 P m)). Qed.
Lemma lem109635 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109636 (P : type1605) : (term24 P) = (term24 P).
Proof. exact (MK_COMB (@lem109635) (@lem109634 P)). Qed.
Lemma lem109641 (P : type1605) (m : nat) (n : nat) : (term25 P m n) = (term25 P m n).
Proof. exact (eq_refl (term25 P m n)). Qed.
Lemma lem109642 (P : type1605) (m : nat) : (term26 P m) = (term26 P m).
Proof. exact (fun_ext (fun n : nat => @lem109641 P m n)). Qed.
Lemma lem109643 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109644 (P : type1605) (m : nat) : (term27 P m) = (term27 P m).
Proof. exact (MK_COMB (@lem109643) (@lem109642 P m)). Qed.
Lemma lem109645 (P : type1605) : (term28 P) = (term28 P).
Proof. exact (fun_ext (fun m : nat => @lem109644 P m)). Qed.
Lemma lem109646 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109647 (P : type1605) : (term29 P) = (term29 P).
Proof. exact (MK_COMB (@lem109646) (@lem109645 P)). Qed.
Lemma lem109652 (P : type1605) (n : nat) (m : nat) : ((P m n) = (P n m)) = ((P m n) = (P n m)).
Proof. exact (eq_refl ((P m n) = (P n m))). Qed.
Lemma lem109653 (P : type1605) (m : nat) : (term30 P m) = (term30 P m).
Proof. exact (fun_ext (fun n : nat => @lem109652 P n m)). Qed.
Lemma lem109654 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109655 (P : type1605) (m : nat) : (term31 P m) = (term31 P m).
Proof. exact (MK_COMB (@lem109654) (@lem109653 P m)). Qed.
Lemma lem109656 (P : type1605) : (term32 P) = (term32 P).
Proof. exact (fun_ext (fun m : nat => @lem109655 P m)). Qed.
Lemma lem109657 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109658 (P : type1605) : (term33 P) = (term33 P).
Proof. exact (MK_COMB (@lem109657) (@lem109656 P)). Qed.
Lemma lem109659 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem109660 (P : type1605) : (term34 P) = (term34 P).
Proof. exact (MK_COMB (@lem109659) (@lem109658 P)). Qed.
Lemma lem109661 (P : type1605) : (term35 P) = (term35 P).
Proof. exact (MK_COMB (@lem109660 P) (@lem109647 P)). Qed.
Lemma lem109662 (P : type1605) (m : nat) : (P m m) = (P m m).
Proof. exact (eq_refl (P m m)). Qed.
Lemma lem109663 (P : type1605) : (term36 P) = (term36 P).
Proof. exact (fun_ext (fun m : nat => @lem109662 P m)). Qed.
Lemma lem109664 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109665 (P : type1605) : (term37 P) = (term37 P).
Proof. exact (MK_COMB (@lem109664) (@lem109663 P)). Qed.
Lemma lem109666 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem109667 (P : type1605) : (term38 P) = (term38 P).
Proof. exact (MK_COMB (@lem109666) (@lem109665 P)). Qed.
Lemma lem109668 (P : type1605) : (term39 P) = (term39 P).
Proof. exact (MK_COMB (@lem109667 P) (@lem109661 P)). Qed.
Lemma lem109669 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem109670 (P : type1605) : (term40 P) = (term40 P).
Proof. exact (MK_COMB (@lem109669) (@lem109668 P)). Qed.
Lemma lem109671 (P : type1605) : (term1 P) = (term1 P).
Proof. exact (MK_COMB (@lem109670 P) (@lem109636 P)). Qed.
Lemma lem109672 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem109673 (P : type1605) : (term3 P) = (term3 P).
Proof. exact (MK_COMB (@lem109672) (@lem109671 P)). Qed.
Lemma lem109674 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem109675 (P : type1605) : (term11 P) = (term11 P).
Proof. exact (MK_COMB (@lem109674) (@lem109673 P)). Qed.
Lemma lem109676 (P : type1605) : (term12 P) = (term12 P).
Proof. exact (MK_COMB (@lem109675 P) (@lem109629)). Qed.
Lemma lem109677 : term14 = term14.
Proof. exact (fun_ext (fun P : type1605 => @lem109676 P)). Qed.
Lemma lem109678 : (@all (nat -> nat -> Prop)) = (@all (nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> Prop))). Qed.
Lemma lem109679 : term16 = term16.
Proof. exact (MK_COMB (@lem109678) (@lem109677)). Qed.
Lemma lem109756 : term15 = term16.
Proof. exact (TRANS (@lem109612) (@lem109679)). Qed.
Lemma lem109757 : term16 = term15.
Proof. exact (SYM (@lem109756)). Qed.
Lemma lem109758 (P : type1605) (h1 : term3 P) : term3 P.
Proof. exact (h1). Qed.
Lemma lem109759 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem109760 (P : type1605) (m : nat) : (P m m) = (P m m).
Proof. exact (eq_refl (P m m)). Qed.
Lemma lem109761 (P : type1605) : (term36 P) = (term36 P).
Proof. exact (fun_ext (fun m : nat => @lem109760 P m)). Qed.
Lemma lem109762 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109763 (P : type1605) : (term37 P) = (term37 P).
Proof. exact (MK_COMB (@lem109762) (@lem109761 P)). Qed.
Lemma lem109778 (P : type1605) (n : nat) (m : nat) : ((P m n) = (P n m)) = (term41 P n m).
Proof. exact (@lem17784 (P m n) (P n m)). Qed.
Lemma lem109779 (P : type1605) (m : nat) : (term30 P m) = (term42 P m).
Proof. exact (fun_ext (fun n : nat => @lem109778 P n m)). Qed.
Lemma lem109780 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109781 (P : type1605) (m : nat) : (term31 P m) = (term43 P m).
Proof. exact (MK_COMB (@lem109780) (@lem109779 P m)). Qed.
Lemma lem109782 (P : type1605) : (term32 P) = (term44 P).
Proof. exact (fun_ext (fun m : nat => @lem109781 P m)). Qed.
Lemma lem109783 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109784 (P : type1605) : (term33 P) = (term45 P).
Proof. exact (MK_COMB (@lem109783) (@lem109782 P)). Qed.
Lemma lem109791 (P : type1605) (m : nat) (n : nat) : (term25 P m n) = (term46 P m n).
Proof. exact (@lem17265 (Peano.lt m n) (P m n)). Qed.
Lemma lem109792 (P : type1605) (m : nat) : (term26 P m) = (term47 P m).
Proof. exact (fun_ext (fun n : nat => @lem109791 P m n)). Qed.
Lemma lem109793 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109794 (P : type1605) (m : nat) : (term27 P m) = (term48 P m).
Proof. exact (MK_COMB (@lem109793) (@lem109792 P m)). Qed.
Lemma lem109795 (P : type1605) : (term28 P) = (term49 P).
Proof. exact (fun_ext (fun m : nat => @lem109794 P m)). Qed.
Lemma lem109796 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109797 (P : type1605) : (term29 P) = (term50 P).
Proof. exact (MK_COMB (@lem109796) (@lem109795 P)). Qed.
Lemma lem109798 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem109799 (P : type1605) : (term34 P) = (term51 P).
Proof. exact (MK_COMB (@lem109798) (@lem109784 P)). Qed.
Lemma lem109800 (P : type1605) : (term35 P) = (term52 P).
Proof. exact (MK_COMB (@lem109799 P) (@lem109797 P)). Qed.
Lemma lem109801 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem109802 (P : type1605) : (term38 P) = (term38 P).
Proof. exact (MK_COMB (@lem109801) (@lem109763 P)). Qed.
Lemma lem109803 (P : type1605) : (term39 P) = (term53 P).
Proof. exact (MK_COMB (@lem109802 P) (@lem109800 P)). Qed.
Lemma lem109805 (P : nat -> Prop) : (term54 P) = (term55 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem109806 (P : type1605) (m : nat) : (term56 P m) = (term57 P m).
Proof. exact (@lem109805 (term21 P m)). Qed.
Lemma lem109807 (P : type1605) (m : nat) (y : nat) : (term58 P m y) = (P m y).
Proof. exact (eq_refl (term58 P m y)). Qed.
Lemma lem109808 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem109810 (P : type1605) (m : nat) (y : nat) : (term59 P m y) = (term60 P m y).
Proof. exact (MK_COMB (@lem109808) (@lem109807 P m y)). Qed.
Lemma lem109811 (P : type1605) (m : nat) : (term61 P m) = (term62 P m).
Proof. exact (fun_ext (fun y : nat => @lem109810 P m y)). Qed.
Lemma lem109812 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem109813 (P : type1605) (m : nat) : (term57 P m) = (term63 P m).
Proof. exact (MK_COMB (@lem109812) (@lem109811 P m)). Qed.
Lemma lem109814 (P : type1605) (m : nat) : (term56 P m) = (term63 P m).
Proof. exact (TRANS (@lem109806 P m) (@lem109813 P m)). Qed.
Lemma lem109815 (P : nat -> Prop) : (term54 P) = (term55 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem109816 (P : type1605) : (term64 P) = (term65 P).
Proof. exact (@lem109815 (term23 P)). Qed.
Lemma lem109817 (P : type1605) (m : nat) : (term66 P m) = (term22 P m).
Proof. exact (eq_refl (term66 P m)). Qed.
Lemma lem109818 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem109819 (P : type1605) (m : nat) : (term67 P m) = (term56 P m).
Proof. exact (MK_COMB (@lem109818) (@lem109817 P m)). Qed.
Lemma lem109820 (P : type1605) (m : nat) : (term67 P m) = (term63 P m).
Proof. exact (TRANS (@lem109819 P m) (@lem109814 P m)). Qed.
Lemma lem109821 (P : type1605) : (term68 P) = (term69 P).
Proof. exact (fun_ext (fun m : nat => @lem109820 P m)). Qed.
Lemma lem109822 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem109823 (P : type1605) : (term65 P) = (term70 P).
Proof. exact (MK_COMB (@lem109822) (@lem109821 P)). Qed.
Lemma lem109824 (P : type1605) : (term64 P) = (term70 P).
Proof. exact (TRANS (@lem109816 P) (@lem109823 P)). Qed.
Lemma lem109825 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem109826 (P : type1605) : (term71 P) = (term72 P).
Proof. exact (MK_COMB (@lem109825) (@lem109803 P)). Qed.
Lemma lem109827 (P : type1605) : (term73 P) = (term74 P).
Proof. exact (MK_COMB (@lem109826 P) (@lem109824 P)). Qed.
Lemma lem109828 (P : type1605) : (term3 P) = (term73 P).
Proof. exact (@lem17362 (term39 P) (term24 P)). Qed.
Lemma lem109829 (P : type1605) : (term3 P) = (term74 P).
Proof. exact (TRANS (@lem109828 P) (@lem109827 P)). Qed.
Lemma lem109839 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term75 A P Q) = (term76 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem109840 (P : nat -> Prop) (Q : nat -> Prop) : (term77 P Q) = (term78 P Q).
Proof. exact (@lem109839 nat P Q). Qed.
Lemma lem109841 (P : type1605) (m : nat) : (term79 P m) = (term80 P m).
Proof. exact (@lem109840 (term81 P m) (term82 P m)). Qed.
Lemma lem109842 (P : type1605) (n : nat) (m : nat) : (term83 P m n) = (term84 P n m).
Proof. exact (eq_refl (term83 P m n)). Qed.
Lemma lem109843 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem109844 (P : type1605) (n : nat) (m : nat) : (term85 P m n) = (term86 P n m).
Proof. exact (MK_COMB (@lem109843) (@lem109842 P n m)). Qed.
Lemma lem109845 (P : type1605) (n : nat) (m : nat) : (term87 P m n) = (term88 P n m).
Proof. exact (eq_refl (term87 P m n)). Qed.
Lemma lem109846 (P : type1605) (n : nat) (m : nat) : (term89 P m n) = (term41 P n m).
Proof. exact (MK_COMB (@lem109844 P n m) (@lem109845 P n m)). Qed.
Lemma lem109847 (P : type1605) (m : nat) : (term90 P m) = (term42 P m).
Proof. exact (fun_ext (fun n : nat => @lem109846 P n m)). Qed.
Lemma lem109848 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109849 (P : type1605) (m : nat) : (term79 P m) = (term43 P m).
Proof. exact (MK_COMB (@lem109848) (@lem109847 P m)). Qed.
Lemma lem109850 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem109851 (P : type1605) (m : nat) : (term91 P m) = (term92 P m).
Proof. exact (MK_COMB (@lem109850) (@lem109849 P m)). Qed.
Lemma lem109852 (P : type1605) (n : nat) (m : nat) : (term83 P m n) = (term84 P n m).
Proof. exact (eq_refl (term83 P m n)). Qed.
Lemma lem109853 (P : type1605) (m : nat) : (term93 P m) = (term81 P m).
Proof. exact (fun_ext (fun n : nat => @lem109852 P n m)). Qed.
Lemma lem109854 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109855 (P : type1605) (m : nat) : (term94 P m) = (term95 P m).
Proof. exact (MK_COMB (@lem109854) (@lem109853 P m)). Qed.
Lemma lem109856 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem109857 (P : type1605) (m : nat) : (term96 P m) = (term97 P m).
Proof. exact (MK_COMB (@lem109856) (@lem109855 P m)). Qed.
Lemma lem109858 (P : type1605) (n : nat) (m : nat) : (term87 P m n) = (term88 P n m).
Proof. exact (eq_refl (term87 P m n)). Qed.
Lemma lem109859 (P : type1605) (m : nat) : (term98 P m) = (term82 P m).
Proof. exact (fun_ext (fun n : nat => @lem109858 P n m)). Qed.
Lemma lem109860 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109861 (P : type1605) (m : nat) : (term99 P m) = (term100 P m).
Proof. exact (MK_COMB (@lem109860) (@lem109859 P m)). Qed.
Lemma lem109862 (P : type1605) (m : nat) : (term80 P m) = (term101 P m).
Proof. exact (MK_COMB (@lem109857 P m) (@lem109861 P m)). Qed.
Lemma lem109863 (P : type1605) (m : nat) : ((term79 P m) = (term80 P m)) = ((term43 P m) = (term101 P m)).
Proof. exact (MK_COMB (@lem109851 P m) (@lem109862 P m)). Qed.
Lemma lem109864 (P : type1605) (m : nat) : (term43 P m) = (term101 P m).
Proof. exact (EQ_MP (@lem109863 P m) (@lem109841 P m)). Qed.
Lemma lem109961 (P : type1605) : (term44 P) = (term102 P).
Proof. exact (fun_ext (fun m : nat => @lem109864 P m)). Qed.
Lemma lem109962 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109963 (P : type1605) : (term45 P) = (term103 P).
Proof. exact (MK_COMB (@lem109962) (@lem109961 P)). Qed.
Lemma lem109965 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term75 A P Q) = (term76 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem109966 (P : nat -> Prop) (Q : nat -> Prop) : (term77 P Q) = (term78 P Q).
Proof. exact (@lem109965 nat P Q). Qed.
Lemma lem109967 (P : type1605) : (term104 P) = (term105 P).
Proof. exact (@lem109966 (term106 P) (term107 P)). Qed.
Lemma lem109968 (P : type1605) (m : nat) : (term108 P m) = (term95 P m).
Proof. exact (eq_refl (term108 P m)). Qed.
Lemma lem109969 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem109970 (P : type1605) (m : nat) : (term109 P m) = (term97 P m).
Proof. exact (MK_COMB (@lem109969) (@lem109968 P m)). Qed.
Lemma lem109971 (P : type1605) (m : nat) : (term110 P m) = (term100 P m).
Proof. exact (eq_refl (term110 P m)). Qed.
Lemma lem109972 (P : type1605) (m : nat) : (term111 P m) = (term101 P m).
Proof. exact (MK_COMB (@lem109970 P m) (@lem109971 P m)). Qed.
Lemma lem109973 (P : type1605) : (term112 P) = (term102 P).
Proof. exact (fun_ext (fun m : nat => @lem109972 P m)). Qed.
Lemma lem109974 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109975 (P : type1605) : (term104 P) = (term103 P).
Proof. exact (MK_COMB (@lem109974) (@lem109973 P)). Qed.
Lemma lem109976 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem109977 (P : type1605) : (term113 P) = (term114 P).
Proof. exact (MK_COMB (@lem109976) (@lem109975 P)). Qed.
Lemma lem109978 (P : type1605) (m : nat) : (term108 P m) = (term95 P m).
Proof. exact (eq_refl (term108 P m)). Qed.
Lemma lem109979 (P : type1605) : (term115 P) = (term106 P).
Proof. exact (fun_ext (fun m : nat => @lem109978 P m)). Qed.
Lemma lem109980 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109981 (P : type1605) : (term116 P) = (term117 P).
Proof. exact (MK_COMB (@lem109980) (@lem109979 P)). Qed.
Lemma lem109982 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem109983 (P : type1605) : (term118 P) = (term119 P).
Proof. exact (MK_COMB (@lem109982) (@lem109981 P)). Qed.
Lemma lem109984 (P : type1605) (m : nat) : (term110 P m) = (term100 P m).
Proof. exact (eq_refl (term110 P m)). Qed.
Lemma lem109985 (P : type1605) : (term120 P) = (term107 P).
Proof. exact (fun_ext (fun m : nat => @lem109984 P m)). Qed.
Lemma lem109986 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem109987 (P : type1605) : (term121 P) = (term122 P).
Proof. exact (MK_COMB (@lem109986) (@lem109985 P)). Qed.
Lemma lem109988 (P : type1605) : (term105 P) = (term123 P).
Proof. exact (MK_COMB (@lem109983 P) (@lem109987 P)). Qed.
Lemma lem109989 (P : type1605) : ((term104 P) = (term105 P)) = ((term103 P) = (term123 P)).
Proof. exact (MK_COMB (@lem109977 P) (@lem109988 P)). Qed.
Lemma lem109990 (P : type1605) : (term103 P) = (term123 P).
Proof. exact (EQ_MP (@lem109989 P) (@lem109967 P)). Qed.
Lemma lem110095 (P : type1605) : (term45 P) = (term123 P).
Proof. exact (TRANS (@lem109963 P) (@lem109990 P)). Qed.
Lemma lem110096 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem110097 (P : type1605) : (term51 P) = (term124 P).
Proof. exact (MK_COMB (@lem110096) (@lem110095 P)). Qed.
Lemma lem110150 (P : type1605) : (term50 P) = (term50 P).
Proof. exact (eq_refl (term50 P)). Qed.
Lemma lem110151 (P : type1605) : (term52 P) = (term125 P).
Proof. exact (MK_COMB (@lem110097 P) (@lem110150 P)). Qed.
Lemma lem110152 (P : type1605) : (term38 P) = (term38 P).
Proof. exact (eq_refl (term38 P)). Qed.
Lemma lem110153 (P : type1605) : (term53 P) = (term126 P).
Proof. exact (MK_COMB (@lem110152 P) (@lem110151 P)). Qed.
Lemma lem110154 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem110155 (P : type1605) : (term72 P) = (term127 P).
Proof. exact (MK_COMB (@lem110154) (@lem110153 P)). Qed.
Lemma lem110164 (P : type1605) : (term70 P) = (term70 P).
Proof. exact (eq_refl (term70 P)). Qed.
Lemma lem110165 (P : type1605) : (term74 P) = (term128 P).
Proof. exact (MK_COMB (@lem110155 P) (@lem110164 P)). Qed.
Lemma lem110167 {A : Type'} (P : Prop) (Q : A -> Prop) : (term129 A P Q) = (term130 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem110168 (P : Prop) (Q : nat -> Prop) : (term131 P Q) = (term132 P Q).
Proof. exact (@lem110167 nat P Q). Qed.
Lemma lem110169 (P : type1605) : (term133 P) = (term134 P).
Proof. exact (@lem110168 (term126 P) (term69 P)). Qed.
Lemma lem110170 (P : type1605) (m : nat) : (term135 P m) = (term63 P m).
Proof. exact (eq_refl (term135 P m)). Qed.
Lemma lem110171 (P : type1605) : (term136 P) = (term69 P).
Proof. exact (fun_ext (fun m : nat => @lem110170 P m)). Qed.
Lemma lem110172 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem110173 (P : type1605) : (term137 P) = (term70 P).
Proof. exact (MK_COMB (@lem110172) (@lem110171 P)). Qed.
Lemma lem110174 (P : type1605) : (term127 P) = (term127 P).
Proof. exact (eq_refl (term127 P)). Qed.
Lemma lem110175 (P : type1605) : (term133 P) = (term128 P).
Proof. exact (MK_COMB (@lem110174 P) (@lem110173 P)). Qed.
Lemma lem110176 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem110177 (P : type1605) : (term138 P) = (term139 P).
Proof. exact (MK_COMB (@lem110176) (@lem110175 P)). Qed.
Lemma lem110178 (P : type1605) (m : nat) : (term135 P m) = (term63 P m).
Proof. exact (eq_refl (term135 P m)). Qed.
Lemma lem110179 (P : type1605) : (term127 P) = (term127 P).
Proof. exact (eq_refl (term127 P)). Qed.
Lemma lem110180 (P : type1605) (m : nat) : (term140 P m) = (term141 P m).
Proof. exact (MK_COMB (@lem110179 P) (@lem110178 P m)). Qed.
Lemma lem110181 (P : type1605) : (term142 P) = (term143 P).
Proof. exact (fun_ext (fun m : nat => @lem110180 P m)). Qed.
Lemma lem110182 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem110183 (P : type1605) : (term134 P) = (term144 P).
Proof. exact (MK_COMB (@lem110182) (@lem110181 P)). Qed.
Lemma lem110184 (P : type1605) : ((term133 P) = (term134 P)) = ((term128 P) = (term144 P)).
Proof. exact (MK_COMB (@lem110177 P) (@lem110183 P)). Qed.
Lemma lem110185 (P : type1605) : (term128 P) = (term144 P).
Proof. exact (EQ_MP (@lem110184 P) (@lem110169 P)). Qed.
Lemma lem110187 {A : Type'} (P : Prop) (Q : A -> Prop) : (term129 A P Q) = (term130 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem110188 (P : Prop) (Q : nat -> Prop) : (term131 P Q) = (term132 P Q).
Proof. exact (@lem110187 nat P Q). Qed.
Lemma lem110189 (P : type1605) (m : nat) : (term145 P m) = (term146 P m).
Proof. exact (@lem110188 (term126 P) (term62 P m)). Qed.
Lemma lem110190 (P : type1605) (m : nat) (y : nat) : (term147 P m y) = (term60 P m y).
Proof. exact (eq_refl (term147 P m y)). Qed.
Lemma lem110191 (P : type1605) (m : nat) : (term148 P m) = (term62 P m).
Proof. exact (fun_ext (fun y : nat => @lem110190 P m y)). Qed.
Lemma lem110192 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem110193 (P : type1605) (m : nat) : (term149 P m) = (term63 P m).
Proof. exact (MK_COMB (@lem110192) (@lem110191 P m)). Qed.
Lemma lem110194 (P : type1605) : (term127 P) = (term127 P).
Proof. exact (eq_refl (term127 P)). Qed.
Lemma lem110195 (P : type1605) (m : nat) : (term145 P m) = (term141 P m).
Proof. exact (MK_COMB (@lem110194 P) (@lem110193 P m)). Qed.
Lemma lem110196 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem110197 (P : type1605) (m : nat) : (term150 P m) = (term151 P m).
Proof. exact (MK_COMB (@lem110196) (@lem110195 P m)). Qed.
Lemma lem110198 (P : type1605) (m : nat) (y : nat) : (term147 P m y) = (term60 P m y).
Proof. exact (eq_refl (term147 P m y)). Qed.
Lemma lem110199 (P : type1605) : (term127 P) = (term127 P).
Proof. exact (eq_refl (term127 P)). Qed.
Lemma lem110200 (P : type1605) (m : nat) (y : nat) : (term152 P m y) = (term153 P m y).
Proof. exact (MK_COMB (@lem110199 P) (@lem110198 P m y)). Qed.
Lemma lem110201 (P : type1605) (m : nat) : (term154 P m) = (term155 P m).
Proof. exact (fun_ext (fun y : nat => @lem110200 P m y)). Qed.
Lemma lem110202 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem110203 (P : type1605) (m : nat) : (term146 P m) = (term156 P m).
Proof. exact (MK_COMB (@lem110202) (@lem110201 P m)). Qed.
Lemma lem110204 (P : type1605) (m : nat) : ((term145 P m) = (term146 P m)) = ((term141 P m) = (term156 P m)).
Proof. exact (MK_COMB (@lem110197 P m) (@lem110203 P m)). Qed.
Lemma lem110205 (P : type1605) (m : nat) : (term141 P m) = (term156 P m).
Proof. exact (EQ_MP (@lem110204 P m) (@lem110189 P m)). Qed.
Lemma lem110206 (P : type1605) : (term143 P) = (term157 P).
Proof. exact (fun_ext (fun m : nat => @lem110205 P m)). Qed.
Lemma lem110207 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem110208 (P : type1605) : (term144 P) = (term158 P).
Proof. exact (MK_COMB (@lem110207) (@lem110206 P)). Qed.
Lemma lem110209 (P : type1605) : (term128 P) = (term158 P).
Proof. exact (TRANS (@lem110185 P) (@lem110208 P)). Qed.
Lemma lem110210 (P : type1605) : (term74 P) = (term158 P).
Proof. exact (TRANS (@lem110165 P) (@lem110209 P)). Qed.
Lemma lem110211 (P : type1605) : (term3 P) = (term158 P).
Proof. exact (TRANS (@lem109829 P) (@lem110210 P)). Qed.
Lemma lem110212 (P : type1605) (h1 : term3 P) : term158 P.
Proof. exact (EQ_MP (@lem110211 P) (@lem109758 P h1)). Qed.
Lemma lem110221 (m : nat) (n : nat) : (term17 m n) = (term17 m n).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem110222 (m : nat) : (term18 m) = (term18 m).
Proof. exact (fun_ext (fun n : nat => @lem110221 m n)). Qed.
Lemma lem110223 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem110224 (m : nat) : (term19 m) = (term19 m).
Proof. exact (MK_COMB (@lem110223) (@lem110222 m)). Qed.
Lemma lem110225 : term20 = term20.
Proof. exact (fun_ext (fun m : nat => @lem110224 m)). Qed.
Lemma lem110226 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem110283 : term10 = term10.
Proof. exact (MK_COMB (@lem110226) (@lem110225)). Qed.
Lemma lem110284 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem110283) (@lem109759 h1)). Qed.
Lemma lem110285 (P : type1605) (m : nat) (h1 : term156 P m) : term156 P m.
Proof. exact (h1). Qed.
Lemma lem110286 (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : term153 P m y.
Proof. exact (h1). Qed.
Lemma lem110307 (m : nat) (n : nat) : (term17 m n) = (term17 m n).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem110308 (m : nat) : (term18 m) = (term18 m).
Proof. exact (fun_ext (fun n : nat => @lem110307 m n)). Qed.
Lemma lem110309 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem110310 (m : nat) : (term19 m) = (term19 m).
Proof. exact (MK_COMB (@lem110309) (@lem110308 m)). Qed.
Lemma lem110311 : term20 = term20.
Proof. exact (fun_ext (fun m : nat => @lem110310 m)). Qed.
Lemma lem110312 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem110313 : term10 = term10.
Proof. exact (MK_COMB (@lem110312) (@lem110311)). Qed.
Lemma lem110314 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem110313) (@lem110284 h1)). Qed.
Lemma lem110321 (P : type1605) (m : nat) (y : nat) : (term60 P m y) = (term60 P m y).
Proof. exact (eq_refl (term60 P m y)). Qed.
Lemma lem110336 (P : type1605) (m : nat) (n : nat) : (term46 P m n) = (term46 P m n).
Proof. exact (eq_refl (term46 P m n)). Qed.
Lemma lem110337 (P : type1605) (m : nat) : (term47 P m) = (term47 P m).
Proof. exact (fun_ext (fun n : nat => @lem110336 P m n)). Qed.
Lemma lem110338 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem110339 (P : type1605) (m : nat) : (term48 P m) = (term48 P m).
Proof. exact (MK_COMB (@lem110338) (@lem110337 P m)). Qed.
Lemma lem110340 (P : type1605) : (term49 P) = (term49 P).
Proof. exact (fun_ext (fun m : nat => @lem110339 P m)). Qed.
Lemma lem110341 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem110342 (P : type1605) : (term50 P) = (term50 P).
Proof. exact (MK_COMB (@lem110341) (@lem110340 P)). Qed.
Lemma lem110357 (P : type1605) (n : nat) (m : nat) : (term88 P n m) = (term88 P n m).
Proof. exact (eq_refl (term88 P n m)). Qed.
Lemma lem110358 (P : type1605) (m : nat) : (term82 P m) = (term82 P m).
Proof. exact (fun_ext (fun n : nat => @lem110357 P n m)). Qed.
Lemma lem110359 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem110360 (P : type1605) (m : nat) : (term100 P m) = (term100 P m).
Proof. exact (MK_COMB (@lem110359) (@lem110358 P m)). Qed.
Lemma lem110361 (P : type1605) : (term107 P) = (term107 P).
Proof. exact (fun_ext (fun m : nat => @lem110360 P m)). Qed.
Lemma lem110362 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem110363 (P : type1605) : (term122 P) = (term122 P).
Proof. exact (MK_COMB (@lem110362) (@lem110361 P)). Qed.
Lemma lem110378 (P : type1605) (n : nat) (m : nat) : (term84 P n m) = (term84 P n m).
Proof. exact (eq_refl (term84 P n m)). Qed.
Lemma lem110379 (P : type1605) (m : nat) : (term81 P m) = (term81 P m).
Proof. exact (fun_ext (fun n : nat => @lem110378 P n m)). Qed.
Lemma lem110380 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem110381 (P : type1605) (m : nat) : (term95 P m) = (term95 P m).
Proof. exact (MK_COMB (@lem110380) (@lem110379 P m)). Qed.
Lemma lem110382 (P : type1605) : (term106 P) = (term106 P).
Proof. exact (fun_ext (fun m : nat => @lem110381 P m)). Qed.
Lemma lem110383 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem110384 (P : type1605) : (term117 P) = (term117 P).
Proof. exact (MK_COMB (@lem110383) (@lem110382 P)). Qed.
Lemma lem110385 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem110386 (P : type1605) : (term119 P) = (term119 P).
Proof. exact (MK_COMB (@lem110385) (@lem110384 P)). Qed.
Lemma lem110387 (P : type1605) : (term123 P) = (term123 P).
Proof. exact (MK_COMB (@lem110386 P) (@lem110363 P)). Qed.
Lemma lem110388 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem110389 (P : type1605) : (term124 P) = (term124 P).
Proof. exact (MK_COMB (@lem110388) (@lem110387 P)). Qed.
Lemma lem110390 (P : type1605) : (term125 P) = (term125 P).
Proof. exact (MK_COMB (@lem110389 P) (@lem110342 P)). Qed.
Lemma lem110395 (P : type1605) (m : nat) : (P m m) = (P m m).
Proof. exact (eq_refl (P m m)). Qed.
Lemma lem110396 (P : type1605) : (term36 P) = (term36 P).
Proof. exact (fun_ext (fun m : nat => @lem110395 P m)). Qed.
Lemma lem110397 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem110398 (P : type1605) : (term37 P) = (term37 P).
Proof. exact (MK_COMB (@lem110397) (@lem110396 P)). Qed.
Lemma lem110399 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem110400 (P : type1605) : (term38 P) = (term38 P).
Proof. exact (MK_COMB (@lem110399) (@lem110398 P)). Qed.
Lemma lem110401 (P : type1605) : (term126 P) = (term126 P).
Proof. exact (MK_COMB (@lem110400 P) (@lem110390 P)). Qed.
Lemma lem110402 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem110403 (P : type1605) : (term127 P) = (term127 P).
Proof. exact (MK_COMB (@lem110402) (@lem110401 P)). Qed.
Lemma lem110404 (P : type1605) (m : nat) (y : nat) : (term153 P m y) = (term153 P m y).
Proof. exact (MK_COMB (@lem110403 P) (@lem110321 P m y)). Qed.
Lemma lem110405 (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : term153 P m y.
Proof. exact (EQ_MP (@lem110404 P m y) (@lem110286 P m y h1)). Qed.
Lemma lem110407 (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : term126 P.
Proof. exact (proj1 (@lem110405 P m y h1)). Qed.
Lemma lem110408 (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : term125 P.
Proof. exact (proj2 (@lem110407 P m y h1)). Qed.
Lemma lem110409 (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : term37 P.
Proof. exact (proj1 (@lem110407 P m y h1)). Qed.
Lemma lem110410 (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : term50 P.
Proof. exact (proj2 (@lem110408 P m y h1)). Qed.
Lemma lem110411 (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : term123 P.
Proof. exact (proj1 (@lem110408 P m y h1)). Qed.
Lemma lem110412 (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : term122 P.
Proof. exact (proj2 (@lem110411 P m y h1)). Qed.
Lemma lem110427 (m : nat) (n : nat) : (term17 m n) = (term17 m n).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem110428 (m : nat) : (term18 m) = (term18 m).
Proof. exact (fun_ext (fun n : nat => @lem110427 m n)). Qed.
Lemma lem110429 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem110430 (m : nat) : (term19 m) = (term19 m).
Proof. exact (MK_COMB (@lem110429) (@lem110428 m)). Qed.
Lemma lem110431 : term20 = term20.
Proof. exact (fun_ext (fun m : nat => @lem110430 m)). Qed.
Lemma lem110432 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem110434 : term10 = term10.
Proof. exact (MK_COMB (@lem110432) (@lem110431)). Qed.
Lemma lem110435 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem110434) (@lem110314 h1)). Qed.
Lemma lem110441 (P : type1605) (m : nat) : (P m m) = (P m m).
Proof. exact (eq_refl (P m m)). Qed.
Lemma lem110442 (P : type1605) : (term36 P) = (term36 P).
Proof. exact (fun_ext (fun m : nat => @lem110441 P m)). Qed.
Lemma lem110443 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem110445 (P : type1605) : (term37 P) = (term37 P).
Proof. exact (MK_COMB (@lem110443) (@lem110442 P)). Qed.
Lemma lem110446 (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : term37 P.
Proof. exact (EQ_MP (@lem110445 P) (@lem110409 P m y h1)). Qed.
Lemma lem110454 (P : type1605) (m : nat) (n : nat) : (term46 P m n) = (term46 P m n).
Proof. exact (eq_refl (term46 P m n)). Qed.
Lemma lem110455 (P : type1605) (m : nat) : (term47 P m) = (term47 P m).
Proof. exact (fun_ext (fun n : nat => @lem110454 P m n)). Qed.
Lemma lem110456 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem110457 (P : type1605) (m : nat) : (term48 P m) = (term48 P m).
Proof. exact (MK_COMB (@lem110456) (@lem110455 P m)). Qed.
Lemma lem110458 (P : type1605) : (term49 P) = (term49 P).
Proof. exact (fun_ext (fun m : nat => @lem110457 P m)). Qed.
Lemma lem110459 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem110461 (P : type1605) : (term50 P) = (term50 P).
Proof. exact (MK_COMB (@lem110459) (@lem110458 P)). Qed.
Lemma lem110462 (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : term50 P.
Proof. exact (EQ_MP (@lem110461 P) (@lem110410 P m y h1)). Qed.
Lemma lem110486 (P : type1605) (n : nat) (m : nat) : (term88 P n m) = (term88 P n m).
Proof. exact (eq_refl (term88 P n m)). Qed.
Lemma lem110487 (P : type1605) (m : nat) : (term82 P m) = (term82 P m).
Proof. exact (fun_ext (fun n : nat => @lem110486 P n m)). Qed.
Lemma lem110488 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem110489 (P : type1605) (m : nat) : (term100 P m) = (term100 P m).
Proof. exact (MK_COMB (@lem110488) (@lem110487 P m)). Qed.
Lemma lem110490 (P : type1605) : (term107 P) = (term107 P).
Proof. exact (fun_ext (fun m : nat => @lem110489 P m)). Qed.
Lemma lem110491 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem110493 (P : type1605) : (term122 P) = (term122 P).
Proof. exact (MK_COMB (@lem110491) (@lem110490 P)). Qed.
Lemma lem110494 (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : term122 P.
Proof. exact (EQ_MP (@lem110493 P) (@lem110412 P m y h1)). Qed.
Lemma lem110495 (_2365 : nat) (h1 : term10) : term159 _2365.
Proof. exact (@lem110435 h1 _2365). Qed.
Lemma lem110496 (_2365 : nat) : (term159 _2365) = (term19 _2365).
Proof. exact (eq_refl (term159 _2365)). Qed.
Lemma lem110497 (_2365 : nat) (h1 : term10) : term19 _2365.
Proof. exact (EQ_MP (@lem110496 _2365) (@lem110495 _2365 h1)). Qed.
Lemma lem110498 (_2365 : nat) (_2366 : nat) (h1 : term10) : term160 _2365 _2366.
Proof. exact (@lem110497 _2365 h1 _2366). Qed.
Lemma lem110499 (_2365 : nat) (_2366 : nat) : (term160 _2365 _2366) = (term17 _2365 _2366).
Proof. exact (eq_refl (term160 _2365 _2366)). Qed.
Lemma lem110501 (_2367 : nat) (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : term161 P _2367.
Proof. exact (@lem110446 P m y h1 _2367). Qed.
Lemma lem110502 (P : type1605) (_2367 : nat) : (term161 P _2367) = (P _2367 _2367).
Proof. exact (eq_refl (term161 P _2367)). Qed.
Lemma lem110504 (_2368 : nat) (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : term162 P _2368.
Proof. exact (@lem110462 P m y h1 _2368). Qed.
Lemma lem110505 (P : type1605) (_2368 : nat) : (term162 P _2368) = (term48 P _2368).
Proof. exact (eq_refl (term162 P _2368)). Qed.
Lemma lem110506 (_2368 : nat) (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : term48 P _2368.
Proof. exact (EQ_MP (@lem110505 P _2368) (@lem110504 _2368 P m y h1)). Qed.
Lemma lem110507 (_2368 : nat) (_2369 : nat) (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : term163 P _2368 _2369.
Proof. exact (@lem110506 _2368 P m y h1 _2369). Qed.
Lemma lem110508 (P : type1605) (_2368 : nat) (_2369 : nat) : (term163 P _2368 _2369) = (term46 P _2368 _2369).
Proof. exact (eq_refl (term163 P _2368 _2369)). Qed.
Lemma lem110516 (_2372 : nat) (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : term110 P _2372.
Proof. exact (@lem110494 P m y h1 _2372). Qed.
Lemma lem110517 (P : type1605) (_2372 : nat) : (term110 P _2372) = (term100 P _2372).
Proof. exact (eq_refl (term110 P _2372)). Qed.
Lemma lem110518 (_2372 : nat) (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : term100 P _2372.
Proof. exact (EQ_MP (@lem110517 P _2372) (@lem110516 _2372 P m y h1)). Qed.
Lemma lem110519 (_2372 : nat) (_2373 : nat) (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : term87 P _2372 _2373.
Proof. exact (@lem110518 _2372 P m y h1 _2373). Qed.
Lemma lem110520 (P : type1605) (_2373 : nat) (_2372 : nat) : (term87 P _2372 _2373) = (term88 P _2373 _2372).
Proof. exact (eq_refl (term87 P _2372 _2373)). Qed.
Lemma lem110531 (_2365 : nat) (_2366 : nat) (h1 : term10) : term17 _2365 _2366.
Proof. exact (EQ_MP (@lem110499 _2365 _2366) (@lem110498 _2365 _2366 h1)). Qed.
Lemma lem110533 (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : term60 P m y.
Proof. exact (proj2 (@lem110405 P m y h1)). Qed.
Lemma lem110541 (_2368 : nat) (_2369 : nat) (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : term46 P _2368 _2369.
Proof. exact (EQ_MP (@lem110508 P _2368 _2369) (@lem110507 _2368 _2369 P m y h1)). Qed.
Lemma lem110553 (_2373 : nat) (_2372 : nat) (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : term88 P _2373 _2372.
Proof. exact (EQ_MP (@lem110520 P _2373 _2372) (@lem110519 _2372 _2373 P m y h1)). Qed.
Lemma lem110554 (P : type1605) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem110555 (_2374 : nat) (_2376 : nat) (h1 : _2374 = _2376) : _2374 = _2376.
Proof. exact (h1). Qed.
Lemma lem110556 (_2375 : nat) (_2377 : nat) (h1 : _2375 = _2377) : _2375 = _2377.
Proof. exact (h1). Qed.
Lemma lem110557 (P : type1605) (_2374 : nat) (_2376 : nat) (h1 : _2374 = _2376) : (P _2374) = (P _2376).
Proof. exact (MK_COMB (@lem110554 P) (@lem110555 _2374 _2376 h1)). Qed.
Lemma lem110558 (P : type1605) (_2374 : nat) (_2376 : nat) (_2375 : nat) (_2377 : nat) (h1 : _2374 = _2376) (h2 : _2375 = _2377) : (P _2374 _2375) = (P _2376 _2377).
Proof. exact (MK_COMB (@lem110557 P _2374 _2376 h1) (@lem110556 _2375 _2377 h2)). Qed.
Lemma lem110560 (b : Prop) (a : Prop) : term164 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem110561 (_2376 : nat) (_2377 : nat) (P : type1605) (_2374 : nat) (_2375 : nat) : term165 _2376 _2377 P _2374 _2375.
Proof. exact (@lem110560 (P _2376 _2377) (P _2374 _2375)). Qed.
Lemma lem110562 (P : type1605) (_2374 : nat) (_2376 : nat) (_2375 : nat) (_2377 : nat) (h1 : _2374 = _2376) (h2 : _2375 = _2377) : term166 _2376 _2377 P _2374 _2375.
Proof. exact (@lem110561 _2376 _2377 P _2374 _2375 (@lem110558 P _2374 _2376 _2375 _2377 h1 h2)). Qed.
Lemma lem110563 (_2377 : nat) (P : type1605) (_2375 : nat) (_2374 : nat) (_2376 : nat) (h1 : _2374 = _2376) : term167 _2376 _2377 P _2374 _2375.
Proof. exact (fun h0 : _2375 = _2377 => @lem110562 P _2374 _2376 _2375 _2377 h1 h0). Qed.
Lemma lem110565 (a : Prop) (b : Prop) : (a -> b) = (term168 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem110566 (_2376 : nat) (_2377 : nat) (P : type1605) (_2374 : nat) (_2375 : nat) : (term167 _2376 _2377 P _2374 _2375) = (term169 _2376 _2377 P _2374 _2375).
Proof. exact (@lem110565 (_2375 = _2377) (term166 _2376 _2377 P _2374 _2375)). Qed.
Lemma lem110567 (_2377 : nat) (P : type1605) (_2375 : nat) (_2374 : nat) (_2376 : nat) (h1 : _2374 = _2376) : term169 _2376 _2377 P _2374 _2375.
Proof. exact (EQ_MP (@lem110566 _2376 _2377 P _2374 _2375) (@lem110563 _2377 P _2375 _2374 _2376 h1)). Qed.
Lemma lem110568 (_2376 : nat) (_2377 : nat) (P : type1605) (_2374 : nat) (_2375 : nat) : term170 _2376 _2377 P _2374 _2375.
Proof. exact (fun h0 : _2374 = _2376 => @lem110567 _2377 P _2375 _2374 _2376 h0). Qed.
Lemma lem110570 (a : Prop) (b : Prop) : (a -> b) = (term168 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem110571 (_2376 : nat) (_2377 : nat) (P : type1605) (_2374 : nat) (_2375 : nat) : (term170 _2376 _2377 P _2374 _2375) = (term171 _2376 _2377 P _2374 _2375).
Proof. exact (@lem110570 (_2374 = _2376) (term169 _2376 _2377 P _2374 _2375)). Qed.
Lemma lem110572 (_2376 : nat) (_2377 : nat) (P : type1605) (_2374 : nat) (_2375 : nat) : term171 _2376 _2377 P _2374 _2375.
Proof. exact (EQ_MP (@lem110571 _2376 _2377 P _2374 _2375) (@lem110568 _2376 _2377 P _2374 _2375)). Qed.
Lemma lem110596 (P : type1605) (m : nat) (y : nat) (h1 : term60 P m y) : term60 P m y.
Proof. exact (h1). Qed.
Lemma lem110597 (P : type1605) (m : nat) (y : nat) (h1 : term60 P m y) : term172 P m y.
Proof. exact (fun h0 : P m y => @lem110596 P m y h1). Qed.
Lemma lem110599 (p : Prop) : (term173 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem110600 (P : type1605) (m : nat) (y : nat) : (term172 P m y) = (term60 P m y).
Proof. exact (@lem110599 (P m y)). Qed.
Lemma lem110601 (P : type1605) (m : nat) (y : nat) (h1 : term60 P m y) : term60 P m y.
Proof. exact (EQ_MP (@lem110600 P m y) (@lem110597 P m y h1)). Qed.
Lemma lem110603 (b : Prop) (a : Prop) : (a \/ b) = (term174 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem110606 (P : type1605) (_2368 : nat) (_2369 : nat) : (term46 P _2368 _2369) = (term175 P _2368 _2369).
Proof. exact (@lem110603 (P _2368 _2369) (term176 _2368 _2369)). Qed.
Lemma lem110609 (_2368 : nat) (_2369 : nat) (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : term175 P _2368 _2369.
Proof. exact (EQ_MP (@lem110606 P _2368 _2369) (@lem110541 _2368 _2369 P m y h1)). Qed.
Lemma lem110610 (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : term175 P m y.
Proof. exact (@lem110609 m y P m y h1). Qed.
Lemma lem110613 (P : type1605) (m : nat) (y : nat) (h1 : term60 P m y) (h2 : term153 P m y) : term176 m y.
Proof. exact (@lem110610 P m y h2 (@lem110601 P m y h1)). Qed.
Lemma lem110614 (P : type1605) (m : nat) (y : nat) (h1 : term60 P m y) (h2 : term153 P m y) : term177 m y.
Proof. exact (fun h0 : Peano.lt m y => @lem110613 P m y h1 h2). Qed.
Lemma lem110616 (p : Prop) : (term173 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem110617 (m : nat) (y : nat) : (term177 m y) = (term176 m y).
Proof. exact (@lem110616 (Peano.lt m y)). Qed.
Lemma lem110618 (P : type1605) (m : nat) (y : nat) (h1 : term60 P m y) (h2 : term153 P m y) : term176 m y.
Proof. exact (EQ_MP (@lem110617 m y) (@lem110614 P m y h1 h2)). Qed.
Lemma lem110620 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem110621 (m : nat) : m = m.
Proof. exact (@lem110620 m). Qed.
Lemma lem110622 (m : nat) : term178 m.
Proof. exact (fun h0 : term179 m => @lem110621 m). Qed.
Lemma lem110624 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem110625 (m : nat) : (term178 m) = (m = m).
Proof. exact (@lem110624 (m = m)). Qed.
Lemma lem110626 (m : nat) : m = m.
Proof. exact (EQ_MP (@lem110625 m) (@lem110622 m)). Qed.
Lemma lem110629 (P : type1605) (m : nat) (y : nat) (h1 : term60 P m y) : term60 P m y.
Proof. exact (h1). Qed.
Lemma lem110630 (P : type1605) (m : nat) (y : nat) (h1 : term60 P m y) : term172 P m y.
Proof. exact (fun h0 : P m y => @lem110629 P m y h1). Qed.
Lemma lem110632 (p : Prop) : (term173 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem110633 (P : type1605) (m : nat) (y : nat) : (term172 P m y) = (term60 P m y).
Proof. exact (@lem110632 (P m y)). Qed.
Lemma lem110634 (P : type1605) (m : nat) (y : nat) (h1 : term60 P m y) : term60 P m y.
Proof. exact (EQ_MP (@lem110633 P m y) (@lem110630 P m y h1)). Qed.
Lemma lem110636 (_2367 : nat) (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : P _2367 _2367.
Proof. exact (EQ_MP (@lem110502 P _2367) (@lem110501 _2367 P m y h1)). Qed.
Lemma lem110637 (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : P m m.
Proof. exact (@lem110636 m P m y h1). Qed.
Lemma lem110638 (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : term181 P m.
Proof. exact (fun h0 : term182 P m => @lem110637 P m y h1). Qed.
Lemma lem110640 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem110641 (P : type1605) (m : nat) : (term181 P m) = (P m m).
Proof. exact (@lem110640 (P m m)). Qed.
Lemma lem110642 (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : P m m.
Proof. exact (EQ_MP (@lem110641 P m) (@lem110638 P m y h1)). Qed.
Lemma lem110660 (q : Prop) (p : Prop) (r : Prop) : (term183 p q r) = (term183 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem110661 (_2376 : nat) (_2377 : nat) (P : type1605) (_2374 : nat) (_2375 : nat) : (term169 _2376 _2377 P _2374 _2375) = (term184 _2376 _2377 P _2374 _2375).
Proof. exact (@lem110660 (P _2376 _2377) (term185 _2375 _2377) (term60 P _2374 _2375)). Qed.
Lemma lem110675 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem110676 (P : type1605) (_2374 : nat) (_2375 : nat) (_2377 : nat) : (term186 _2377 P _2374 _2375) = (term187 P _2374 _2375 _2377).
Proof. exact (@lem110675 (term60 P _2374 _2375) (term185 _2375 _2377)). Qed.
Lemma lem110684 (P : type1605) (_2376 : nat) (_2377 : nat) : (term188 P _2376 _2377) = (term188 P _2376 _2377).
Proof. exact (eq_refl (term188 P _2376 _2377)). Qed.
Lemma lem110685 (_2376 : nat) (P : type1605) (_2374 : nat) (_2375 : nat) (_2377 : nat) : (term184 _2376 _2377 P _2374 _2375) = (term189 _2376 P _2374 _2375 _2377).
Proof. exact (MK_COMB (@lem110684 P _2376 _2377) (@lem110676 P _2374 _2375 _2377)). Qed.
Lemma lem110696 (_2376 : nat) (P : type1605) (_2374 : nat) (_2375 : nat) (_2377 : nat) : (term169 _2376 _2377 P _2374 _2375) = (term189 _2376 P _2374 _2375 _2377).
Proof. exact (TRANS (@lem110661 _2376 _2377 P _2374 _2375) (@lem110685 _2376 P _2374 _2375 _2377)). Qed.
Lemma lem110697 (_2374 : nat) (_2376 : nat) : (term190 _2374 _2376) = (term190 _2374 _2376).
Proof. exact (eq_refl (term190 _2374 _2376)). Qed.
Lemma lem110698 (_2376 : nat) (P : type1605) (_2374 : nat) (_2375 : nat) (_2377 : nat) : (term171 _2376 _2377 P _2374 _2375) = (term191 _2376 P _2374 _2375 _2377).
Proof. exact (MK_COMB (@lem110697 _2374 _2376) (@lem110696 _2376 P _2374 _2375 _2377)). Qed.
Lemma lem110702 (q : Prop) (p : Prop) (r : Prop) : (term183 p q r) = (term183 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem110703 (_2376 : nat) (P : type1605) (_2374 : nat) (_2375 : nat) (_2377 : nat) : (term191 _2376 P _2374 _2375 _2377) = (term192 _2376 P _2374 _2375 _2377).
Proof. exact (@lem110702 (P _2376 _2377) (term185 _2374 _2376) (term187 P _2374 _2375 _2377)). Qed.
Lemma lem110717 (q : Prop) (p : Prop) (r : Prop) : (term183 p q r) = (term183 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem110718 (P : type1605) (_2374 : nat) (_2376 : nat) (_2375 : nat) (_2377 : nat) : (term193 _2376 P _2374 _2375 _2377) = (term194 P _2374 _2376 _2375 _2377).
Proof. exact (@lem110717 (term60 P _2374 _2375) (term185 _2374 _2376) (term185 _2375 _2377)). Qed.
Lemma lem110738 (P : type1605) (_2376 : nat) (_2377 : nat) : (term188 P _2376 _2377) = (term188 P _2376 _2377).
Proof. exact (eq_refl (term188 P _2376 _2377)). Qed.
Lemma lem110739 (P : type1605) (_2374 : nat) (_2376 : nat) (_2375 : nat) (_2377 : nat) : (term192 _2376 P _2374 _2375 _2377) = (term195 P _2374 _2376 _2375 _2377).
Proof. exact (MK_COMB (@lem110738 P _2376 _2377) (@lem110718 P _2374 _2376 _2375 _2377)). Qed.
Lemma lem110750 (P : type1605) (_2374 : nat) (_2376 : nat) (_2375 : nat) (_2377 : nat) : (term191 _2376 P _2374 _2375 _2377) = (term195 P _2374 _2376 _2375 _2377).
Proof. exact (TRANS (@lem110703 _2376 P _2374 _2375 _2377) (@lem110739 P _2374 _2376 _2375 _2377)). Qed.
Lemma lem110751 (P : type1605) (_2374 : nat) (_2376 : nat) (_2375 : nat) (_2377 : nat) : (term171 _2376 _2377 P _2374 _2375) = (term195 P _2374 _2376 _2375 _2377).
Proof. exact (TRANS (@lem110698 _2376 P _2374 _2375 _2377) (@lem110750 P _2374 _2376 _2375 _2377)). Qed.
Lemma lem110752 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem110753 (P : type1605) (_2374 : nat) (_2376 : nat) (_2375 : nat) (_2377 : nat) : (term196 _2376 _2377 P _2374 _2375) = (term197 P _2374 _2376 _2375 _2377).
Proof. exact (MK_COMB (@lem110752) (@lem110751 P _2374 _2376 _2375 _2377)). Qed.
Lemma lem110757 (q : Prop) (p : Prop) (r : Prop) : (term183 p q r) = (term183 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem110758 (_2376 : nat) (_2377 : nat) (P : type1605) (_2374 : nat) (_2375 : nat) : (term198 _2376 _2377 P _2374 _2375) = (term171 _2376 _2377 P _2374 _2375).
Proof. exact (@lem110757 (term185 _2374 _2376) (term185 _2375 _2377) (term166 _2376 _2377 P _2374 _2375)). Qed.
Lemma lem110774 (q : Prop) (p : Prop) (r : Prop) : (term183 p q r) = (term183 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem110775 (_2376 : nat) (_2377 : nat) (P : type1605) (_2374 : nat) (_2375 : nat) : (term169 _2376 _2377 P _2374 _2375) = (term184 _2376 _2377 P _2374 _2375).
Proof. exact (@lem110774 (P _2376 _2377) (term185 _2375 _2377) (term60 P _2374 _2375)). Qed.
Lemma lem110789 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem110790 (P : type1605) (_2374 : nat) (_2375 : nat) (_2377 : nat) : (term186 _2377 P _2374 _2375) = (term187 P _2374 _2375 _2377).
Proof. exact (@lem110789 (term60 P _2374 _2375) (term185 _2375 _2377)). Qed.
Lemma lem110798 (P : type1605) (_2376 : nat) (_2377 : nat) : (term188 P _2376 _2377) = (term188 P _2376 _2377).
Proof. exact (eq_refl (term188 P _2376 _2377)). Qed.
Lemma lem110799 (_2376 : nat) (P : type1605) (_2374 : nat) (_2375 : nat) (_2377 : nat) : (term184 _2376 _2377 P _2374 _2375) = (term189 _2376 P _2374 _2375 _2377).
Proof. exact (MK_COMB (@lem110798 P _2376 _2377) (@lem110790 P _2374 _2375 _2377)). Qed.
Lemma lem110810 (_2376 : nat) (P : type1605) (_2374 : nat) (_2375 : nat) (_2377 : nat) : (term169 _2376 _2377 P _2374 _2375) = (term189 _2376 P _2374 _2375 _2377).
Proof. exact (TRANS (@lem110775 _2376 _2377 P _2374 _2375) (@lem110799 _2376 P _2374 _2375 _2377)). Qed.
Lemma lem110811 (_2374 : nat) (_2376 : nat) : (term190 _2374 _2376) = (term190 _2374 _2376).
Proof. exact (eq_refl (term190 _2374 _2376)). Qed.
Lemma lem110812 (_2376 : nat) (P : type1605) (_2374 : nat) (_2375 : nat) (_2377 : nat) : (term171 _2376 _2377 P _2374 _2375) = (term191 _2376 P _2374 _2375 _2377).
Proof. exact (MK_COMB (@lem110811 _2374 _2376) (@lem110810 _2376 P _2374 _2375 _2377)). Qed.
Lemma lem110816 (q : Prop) (p : Prop) (r : Prop) : (term183 p q r) = (term183 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem110817 (_2376 : nat) (P : type1605) (_2374 : nat) (_2375 : nat) (_2377 : nat) : (term191 _2376 P _2374 _2375 _2377) = (term192 _2376 P _2374 _2375 _2377).
Proof. exact (@lem110816 (P _2376 _2377) (term185 _2374 _2376) (term187 P _2374 _2375 _2377)). Qed.
Lemma lem110831 (q : Prop) (p : Prop) (r : Prop) : (term183 p q r) = (term183 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem110832 (P : type1605) (_2374 : nat) (_2376 : nat) (_2375 : nat) (_2377 : nat) : (term193 _2376 P _2374 _2375 _2377) = (term194 P _2374 _2376 _2375 _2377).
Proof. exact (@lem110831 (term60 P _2374 _2375) (term185 _2374 _2376) (term185 _2375 _2377)). Qed.
Lemma lem110852 (P : type1605) (_2376 : nat) (_2377 : nat) : (term188 P _2376 _2377) = (term188 P _2376 _2377).
Proof. exact (eq_refl (term188 P _2376 _2377)). Qed.
Lemma lem110853 (P : type1605) (_2374 : nat) (_2376 : nat) (_2375 : nat) (_2377 : nat) : (term192 _2376 P _2374 _2375 _2377) = (term195 P _2374 _2376 _2375 _2377).
Proof. exact (MK_COMB (@lem110852 P _2376 _2377) (@lem110832 P _2374 _2376 _2375 _2377)). Qed.
Lemma lem110864 (P : type1605) (_2374 : nat) (_2376 : nat) (_2375 : nat) (_2377 : nat) : (term191 _2376 P _2374 _2375 _2377) = (term195 P _2374 _2376 _2375 _2377).
Proof. exact (TRANS (@lem110817 _2376 P _2374 _2375 _2377) (@lem110853 P _2374 _2376 _2375 _2377)). Qed.
Lemma lem110865 (P : type1605) (_2374 : nat) (_2376 : nat) (_2375 : nat) (_2377 : nat) : (term171 _2376 _2377 P _2374 _2375) = (term195 P _2374 _2376 _2375 _2377).
Proof. exact (TRANS (@lem110812 _2376 P _2374 _2375 _2377) (@lem110864 P _2374 _2376 _2375 _2377)). Qed.
Lemma lem110866 (P : type1605) (_2374 : nat) (_2376 : nat) (_2375 : nat) (_2377 : nat) : (term198 _2376 _2377 P _2374 _2375) = (term195 P _2374 _2376 _2375 _2377).
Proof. exact (TRANS (@lem110758 _2376 _2377 P _2374 _2375) (@lem110865 P _2374 _2376 _2375 _2377)). Qed.
Lemma lem110867 (P : type1605) (_2374 : nat) (_2376 : nat) (_2375 : nat) (_2377 : nat) : ((term171 _2376 _2377 P _2374 _2375) = (term198 _2376 _2377 P _2374 _2375)) = ((term195 P _2374 _2376 _2375 _2377) = (term195 P _2374 _2376 _2375 _2377)).
Proof. exact (MK_COMB (@lem110753 P _2374 _2376 _2375 _2377) (@lem110866 P _2374 _2376 _2375 _2377)). Qed.
Lemma lem110869 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem110870 (x : Prop) : (x = x) = True.
Proof. exact (@lem110869 Prop x). Qed.
Lemma lem110871 (P : type1605) (_2374 : nat) (_2376 : nat) (_2375 : nat) (_2377 : nat) : ((term195 P _2374 _2376 _2375 _2377) = (term195 P _2374 _2376 _2375 _2377)) = True.
Proof. exact (@lem110870 (term195 P _2374 _2376 _2375 _2377)). Qed.
Lemma lem110872 (_2376 : nat) (_2377 : nat) (P : type1605) (_2374 : nat) (_2375 : nat) : ((term171 _2376 _2377 P _2374 _2375) = (term198 _2376 _2377 P _2374 _2375)) = True.
Proof. exact (TRANS (@lem110867 P _2374 _2376 _2375 _2377) (@lem110871 P _2374 _2376 _2375 _2377)). Qed.
Lemma lem110873 (_2376 : nat) (_2377 : nat) (P : type1605) (_2374 : nat) (_2375 : nat) : True = ((term171 _2376 _2377 P _2374 _2375) = (term198 _2376 _2377 P _2374 _2375)).
Proof. exact (SYM (@lem110872 _2376 _2377 P _2374 _2375)). Qed.
Lemma lem110874 (_2376 : nat) (_2377 : nat) (P : type1605) (_2374 : nat) (_2375 : nat) : (term171 _2376 _2377 P _2374 _2375) = (term198 _2376 _2377 P _2374 _2375).
Proof. exact (EQ_MP (@lem110873 _2376 _2377 P _2374 _2375) (@lem0)). Qed.
Lemma lem110875 (_2376 : nat) (_2377 : nat) (P : type1605) (_2374 : nat) (_2375 : nat) : term198 _2376 _2377 P _2374 _2375.
Proof. exact (EQ_MP (@lem110874 _2376 _2377 P _2374 _2375) (@lem110572 _2376 _2377 P _2374 _2375)). Qed.
Lemma lem110877 (b : Prop) (a : Prop) : (a \/ b) = (term174 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem110878 (_2376 : nat) (P : type1605) (_2374 : nat) (_2375 : nat) (_2377 : nat) : (term198 _2376 _2377 P _2374 _2375) = (term199 _2376 P _2374 _2375 _2377).
Proof. exact (@lem110877 (term200 _2376 _2377 P _2374 _2375) (term185 _2375 _2377)). Qed.
Lemma lem110880 (a : Prop) (b : Prop) : (term201 a b) = (term202 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem110881 (_2376 : nat) (_2377 : nat) (P : type1605) (_2374 : nat) (_2375 : nat) : (term203 _2376 _2377 P _2374 _2375) = (term204 _2376 _2377 P _2374 _2375).
Proof. exact (@lem110880 (term185 _2374 _2376) (term166 _2376 _2377 P _2374 _2375)). Qed.
Lemma lem110883 (a : Prop) : (term205 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem110884 (_2374 : nat) (_2376 : nat) : (term206 _2374 _2376) = (_2374 = _2376).
Proof. exact (@lem110883 (_2374 = _2376)). Qed.
Lemma lem110885 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem110886 (_2374 : nat) (_2376 : nat) : (term207 _2374 _2376) = (term208 _2374 _2376).
Proof. exact (MK_COMB (@lem110885) (@lem110884 _2374 _2376)). Qed.
Lemma lem110888 (a : Prop) (b : Prop) : (term201 a b) = (term202 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem110889 (_2376 : nat) (_2377 : nat) (P : type1605) (_2374 : nat) (_2375 : nat) : (term209 _2376 _2377 P _2374 _2375) = (term210 _2376 _2377 P _2374 _2375).
Proof. exact (@lem110888 (P _2376 _2377) (term60 P _2374 _2375)). Qed.
Lemma lem110891 (a : Prop) : (term205 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem110892 (P : type1605) (_2374 : nat) (_2375 : nat) : (term211 P _2374 _2375) = (P _2374 _2375).
Proof. exact (@lem110891 (P _2374 _2375)). Qed.
Lemma lem110893 (P : type1605) (_2376 : nat) (_2377 : nat) : (term212 P _2376 _2377) = (term212 P _2376 _2377).
Proof. exact (eq_refl (term212 P _2376 _2377)). Qed.
Lemma lem110894 (_2376 : nat) (_2377 : nat) (P : type1605) (_2374 : nat) (_2375 : nat) : (term210 _2376 _2377 P _2374 _2375) = (term213 _2376 _2377 P _2374 _2375).
Proof. exact (MK_COMB (@lem110893 P _2376 _2377) (@lem110892 P _2374 _2375)). Qed.
Lemma lem110895 (_2376 : nat) (_2377 : nat) (P : type1605) (_2374 : nat) (_2375 : nat) : (term209 _2376 _2377 P _2374 _2375) = (term213 _2376 _2377 P _2374 _2375).
Proof. exact (TRANS (@lem110889 _2376 _2377 P _2374 _2375) (@lem110894 _2376 _2377 P _2374 _2375)). Qed.
Lemma lem110896 (_2376 : nat) (_2377 : nat) (P : type1605) (_2374 : nat) (_2375 : nat) : (term204 _2376 _2377 P _2374 _2375) = (term214 _2376 _2377 P _2374 _2375).
Proof. exact (MK_COMB (@lem110886 _2374 _2376) (@lem110895 _2376 _2377 P _2374 _2375)). Qed.
Lemma lem110897 (_2376 : nat) (_2377 : nat) (P : type1605) (_2374 : nat) (_2375 : nat) : (term203 _2376 _2377 P _2374 _2375) = (term214 _2376 _2377 P _2374 _2375).
Proof. exact (TRANS (@lem110881 _2376 _2377 P _2374 _2375) (@lem110896 _2376 _2377 P _2374 _2375)). Qed.
Lemma lem110898 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem110899 (_2376 : nat) (_2377 : nat) (P : type1605) (_2374 : nat) (_2375 : nat) : (term215 _2376 _2377 P _2374 _2375) = (term216 _2376 _2377 P _2374 _2375).
Proof. exact (MK_COMB (@lem110898) (@lem110897 _2376 _2377 P _2374 _2375)). Qed.
Lemma lem110900 (_2375 : nat) (_2377 : nat) : (term185 _2375 _2377) = (term185 _2375 _2377).
Proof. exact (eq_refl (term185 _2375 _2377)). Qed.
Lemma lem110901 (_2376 : nat) (P : type1605) (_2374 : nat) (_2375 : nat) (_2377 : nat) : (term199 _2376 P _2374 _2375 _2377) = (term217 _2376 P _2374 _2375 _2377).
Proof. exact (MK_COMB (@lem110899 _2376 _2377 P _2374 _2375) (@lem110900 _2375 _2377)). Qed.
Lemma lem110902 (_2376 : nat) (P : type1605) (_2374 : nat) (_2375 : nat) (_2377 : nat) : (term198 _2376 _2377 P _2374 _2375) = (term217 _2376 P _2374 _2375 _2377).
Proof. exact (TRANS (@lem110878 _2376 P _2374 _2375 _2377) (@lem110901 _2376 P _2374 _2375 _2377)). Qed.
Lemma lem110904 (P : type1605) (m : nat) (y : nat) (h1 : term60 P m y) (h2 : term153 P m y) : term218 y P m.
Proof. exact (conj (@lem110634 P m y h1) (@lem110642 P m y h2)). Qed.
Lemma lem110905 (P : type1605) (m : nat) (y : nat) (h1 : term60 P m y) (h2 : term153 P m y) : term219 y P m.
Proof. exact (conj (@lem110626 m) (@lem110904 P m y h1 h2)). Qed.
Lemma lem110907 (_2376 : nat) (P : type1605) (_2374 : nat) (_2375 : nat) (_2377 : nat) : term217 _2376 P _2374 _2375 _2377.
Proof. exact (EQ_MP (@lem110902 _2376 P _2374 _2375 _2377) (@lem110875 _2376 _2377 P _2374 _2375)). Qed.
Lemma lem110908 (P : type1605) (m : nat) (y : nat) : term220 P m y.
Proof. exact (@lem110907 m P m m y). Qed.
Lemma lem110911 (P : type1605) (m : nat) (y : nat) (h1 : term60 P m y) (h2 : term153 P m y) : term185 m y.
Proof. exact (@lem110908 P m y (@lem110905 P m y h1 h2)). Qed.
Lemma lem110912 (P : type1605) (m : nat) (y : nat) (h1 : term60 P m y) (h2 : term153 P m y) : term221 m y.
Proof. exact (fun h0 : m = y => @lem110911 P m y h1 h2). Qed.
Lemma lem110914 (p : Prop) : (term173 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem110915 (m : nat) (y : nat) : (term221 m y) = (term185 m y).
Proof. exact (@lem110914 (m = y)). Qed.
Lemma lem110916 (P : type1605) (m : nat) (y : nat) (h1 : term60 P m y) (h2 : term153 P m y) : term185 m y.
Proof. exact (EQ_MP (@lem110915 m y) (@lem110912 P m y h1 h2)). Qed.
Lemma lem110939 (q : Prop) (p : Prop) (r : Prop) : (term183 p q r) = (term183 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem110940 (_2365 : nat) (_2366 : nat) : (term222 _2365 _2366) = (term17 _2365 _2366).
Proof. exact (@lem110939 (Peano.lt _2365 _2366) (Peano.lt _2366 _2365) (_2365 = _2366)). Qed.
Lemma lem110958 (_2365 : nat) (_2366 : nat) : (term223 _2365 _2366) = (term223 _2365 _2366).
Proof. exact (eq_refl (term223 _2365 _2366)). Qed.
Lemma lem110959 (_2365 : nat) (_2366 : nat) : ((term17 _2365 _2366) = (term222 _2365 _2366)) = ((term17 _2365 _2366) = (term17 _2365 _2366)).
Proof. exact (MK_COMB (@lem110958 _2365 _2366) (@lem110940 _2365 _2366)). Qed.
Lemma lem110961 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem110962 (x : Prop) : (x = x) = True.
Proof. exact (@lem110961 Prop x). Qed.
Lemma lem110963 (_2365 : nat) (_2366 : nat) : ((term17 _2365 _2366) = (term17 _2365 _2366)) = True.
Proof. exact (@lem110962 (term17 _2365 _2366)). Qed.
Lemma lem110964 (_2365 : nat) (_2366 : nat) : ((term17 _2365 _2366) = (term222 _2365 _2366)) = True.
Proof. exact (TRANS (@lem110959 _2365 _2366) (@lem110963 _2365 _2366)). Qed.
Lemma lem110965 (_2365 : nat) (_2366 : nat) : True = ((term17 _2365 _2366) = (term222 _2365 _2366)).
Proof. exact (SYM (@lem110964 _2365 _2366)). Qed.
Lemma lem110966 (_2365 : nat) (_2366 : nat) : (term17 _2365 _2366) = (term222 _2365 _2366).
Proof. exact (EQ_MP (@lem110965 _2365 _2366) (@lem0)). Qed.
Lemma lem110967 (_2365 : nat) (_2366 : nat) (h1 : term10) : term222 _2365 _2366.
Proof. exact (EQ_MP (@lem110966 _2365 _2366) (@lem110531 _2365 _2366 h1)). Qed.
Lemma lem110969 (b : Prop) (a : Prop) : (a \/ b) = (term174 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem110970 (_2366 : nat) (_2365 : nat) : (term222 _2365 _2366) = (term224 _2366 _2365).
Proof. exact (@lem110969 (term225 _2365 _2366) (Peano.lt _2366 _2365)). Qed.
Lemma lem110972 (a : Prop) (b : Prop) : (term201 a b) = (term202 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem110973 (_2365 : nat) (_2366 : nat) : (term226 _2365 _2366) = (term227 _2365 _2366).
Proof. exact (@lem110972 (Peano.lt _2365 _2366) (_2365 = _2366)). Qed.
Lemma lem110974 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem110975 (_2365 : nat) (_2366 : nat) : (term228 _2365 _2366) = (term229 _2365 _2366).
Proof. exact (MK_COMB (@lem110974) (@lem110973 _2365 _2366)). Qed.
Lemma lem110976 (_2366 : nat) (_2365 : nat) : (Peano.lt _2366 _2365) = (Peano.lt _2366 _2365).
Proof. exact (eq_refl (Peano.lt _2366 _2365)). Qed.
Lemma lem110977 (_2366 : nat) (_2365 : nat) : (term224 _2366 _2365) = (term230 _2366 _2365).
Proof. exact (MK_COMB (@lem110975 _2365 _2366) (@lem110976 _2366 _2365)). Qed.
Lemma lem110978 (_2366 : nat) (_2365 : nat) : (term222 _2365 _2366) = (term230 _2366 _2365).
Proof. exact (TRANS (@lem110970 _2366 _2365) (@lem110977 _2366 _2365)). Qed.
Lemma lem110980 (P : type1605) (m : nat) (y : nat) (h1 : term60 P m y) (h2 : term153 P m y) : term227 m y.
Proof. exact (conj (@lem110618 P m y h1 h2) (@lem110916 P m y h1 h2)). Qed.
Lemma lem110982 (_2366 : nat) (_2365 : nat) (h1 : term10) : term230 _2366 _2365.
Proof. exact (EQ_MP (@lem110978 _2366 _2365) (@lem110967 _2365 _2366 h1)). Qed.
Lemma lem110983 (y : nat) (m : nat) (h1 : term10) : term230 y m.
Proof. exact (@lem110982 y m h1). Qed.
Lemma lem110986 (P : type1605) (m : nat) (y : nat) (h1 : term10) (h2 : term60 P m y) (h3 : term153 P m y) : Peano.lt y m.
Proof. exact (@lem110983 y m h1 (@lem110980 P m y h2 h3)). Qed.
Lemma lem110987 (P : type1605) (m : nat) (y : nat) (h1 : term10) (h2 : term60 P m y) (h3 : term153 P m y) : term231 y m.
Proof. exact (fun h0 : term176 y m => @lem110986 P m y h1 h2 h3). Qed.
Lemma lem110989 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem110990 (y : nat) (m : nat) : (term231 y m) = (Peano.lt y m).
Proof. exact (@lem110989 (Peano.lt y m)). Qed.
Lemma lem110991 (P : type1605) (m : nat) (y : nat) (h1 : term10) (h2 : term60 P m y) (h3 : term153 P m y) : Peano.lt y m.
Proof. exact (EQ_MP (@lem110990 y m) (@lem110987 P m y h1 h2 h3)). Qed.
Lemma lem110997 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem110998 (P : type1605) (_2368 : nat) (_2369 : nat) : (term46 P _2368 _2369) = (term232 P _2368 _2369).
Proof. exact (@lem110997 (P _2368 _2369) (term176 _2368 _2369)). Qed.
Lemma lem111004 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem111005 (P : type1605) (_2368 : nat) (_2369 : nat) : (term233 P _2368 _2369) = (term234 P _2368 _2369).
Proof. exact (MK_COMB (@lem111004) (@lem110998 P _2368 _2369)). Qed.
Lemma lem111011 (P : type1605) (_2368 : nat) (_2369 : nat) : (term232 P _2368 _2369) = (term232 P _2368 _2369).
Proof. exact (eq_refl (term232 P _2368 _2369)). Qed.
Lemma lem111012 (P : type1605) (_2368 : nat) (_2369 : nat) : ((term46 P _2368 _2369) = (term232 P _2368 _2369)) = ((term232 P _2368 _2369) = (term232 P _2368 _2369)).
Proof. exact (MK_COMB (@lem111005 P _2368 _2369) (@lem111011 P _2368 _2369)). Qed.
Lemma lem111014 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem111015 (x : Prop) : (x = x) = True.
Proof. exact (@lem111014 Prop x). Qed.
Lemma lem111016 (P : type1605) (_2368 : nat) (_2369 : nat) : ((term232 P _2368 _2369) = (term232 P _2368 _2369)) = True.
Proof. exact (@lem111015 (term232 P _2368 _2369)). Qed.
Lemma lem111017 (P : type1605) (_2368 : nat) (_2369 : nat) : ((term46 P _2368 _2369) = (term232 P _2368 _2369)) = True.
Proof. exact (TRANS (@lem111012 P _2368 _2369) (@lem111016 P _2368 _2369)). Qed.
Lemma lem111018 (P : type1605) (_2368 : nat) (_2369 : nat) : True = ((term46 P _2368 _2369) = (term232 P _2368 _2369)).
Proof. exact (SYM (@lem111017 P _2368 _2369)). Qed.
Lemma lem111019 (P : type1605) (_2368 : nat) (_2369 : nat) : (term46 P _2368 _2369) = (term232 P _2368 _2369).
Proof. exact (EQ_MP (@lem111018 P _2368 _2369) (@lem0)). Qed.
Lemma lem111020 (_2368 : nat) (_2369 : nat) (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : term232 P _2368 _2369.
Proof. exact (EQ_MP (@lem111019 P _2368 _2369) (@lem110541 _2368 _2369 P m y h1)). Qed.
Lemma lem111022 (b : Prop) (a : Prop) : (a \/ b) = (term174 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem111023 (P : type1605) (_2368 : nat) (_2369 : nat) : (term232 P _2368 _2369) = (term235 P _2368 _2369).
Proof. exact (@lem111022 (term176 _2368 _2369) (P _2368 _2369)). Qed.
Lemma lem111025 (a : Prop) : (term205 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem111026 (_2368 : nat) (_2369 : nat) : (term236 _2368 _2369) = (Peano.lt _2368 _2369).
Proof. exact (@lem111025 (Peano.lt _2368 _2369)). Qed.
Lemma lem111027 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem111028 (_2368 : nat) (_2369 : nat) : (term237 _2368 _2369) = (term238 _2368 _2369).
Proof. exact (MK_COMB (@lem111027) (@lem111026 _2368 _2369)). Qed.
Lemma lem111029 (P : type1605) (_2368 : nat) (_2369 : nat) : (P _2368 _2369) = (P _2368 _2369).
Proof. exact (eq_refl (P _2368 _2369)). Qed.
Lemma lem111030 (P : type1605) (_2368 : nat) (_2369 : nat) : (term235 P _2368 _2369) = (term25 P _2368 _2369).
Proof. exact (MK_COMB (@lem111028 _2368 _2369) (@lem111029 P _2368 _2369)). Qed.
Lemma lem111031 (P : type1605) (_2368 : nat) (_2369 : nat) : (term232 P _2368 _2369) = (term25 P _2368 _2369).
Proof. exact (TRANS (@lem111023 P _2368 _2369) (@lem111030 P _2368 _2369)). Qed.
Lemma lem111034 (_2368 : nat) (_2369 : nat) (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : term25 P _2368 _2369.
Proof. exact (EQ_MP (@lem111031 P _2368 _2369) (@lem111020 _2368 _2369 P m y h1)). Qed.
Lemma lem111035 (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : term25 P y m.
Proof. exact (@lem111034 y m P m y h1). Qed.
Lemma lem111038 (P : type1605) (m : nat) (y : nat) (h1 : term10) (h2 : term60 P m y) (h3 : term153 P m y) : P y m.
Proof. exact (@lem111035 P m y h3 (@lem110991 P m y h1 h2 h3)). Qed.
Lemma lem111039 (P : type1605) (m : nat) (y : nat) (h1 : term10) (h2 : term60 P m y) (h3 : term153 P m y) : term239 P y m.
Proof. exact (fun h0 : term60 P y m => @lem111038 P m y h1 h2 h3). Qed.
Lemma lem111041 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem111042 (P : type1605) (y : nat) (m : nat) : (term239 P y m) = (P y m).
Proof. exact (@lem111041 (P y m)). Qed.
Lemma lem111043 (P : type1605) (m : nat) (y : nat) (h1 : term10) (h2 : term60 P m y) (h3 : term153 P m y) : P y m.
Proof. exact (EQ_MP (@lem111042 P y m) (@lem111039 P m y h1 h2 h3)). Qed.
Lemma lem111049 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem111050 (P : type1605) (_2372 : nat) (_2373 : nat) : (term88 P _2373 _2372) = (term84 P _2372 _2373).
Proof. exact (@lem111049 (P _2373 _2372) (term60 P _2372 _2373)). Qed.
Lemma lem111056 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem111057 (P : type1605) (_2372 : nat) (_2373 : nat) : (term240 P _2373 _2372) = (term241 P _2372 _2373).
Proof. exact (MK_COMB (@lem111056) (@lem111050 P _2372 _2373)). Qed.
Lemma lem111063 (P : type1605) (_2372 : nat) (_2373 : nat) : (term84 P _2372 _2373) = (term84 P _2372 _2373).
Proof. exact (eq_refl (term84 P _2372 _2373)). Qed.
Lemma lem111064 (P : type1605) (_2372 : nat) (_2373 : nat) : ((term88 P _2373 _2372) = (term84 P _2372 _2373)) = ((term84 P _2372 _2373) = (term84 P _2372 _2373)).
Proof. exact (MK_COMB (@lem111057 P _2372 _2373) (@lem111063 P _2372 _2373)). Qed.
Lemma lem111066 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem111067 (x : Prop) : (x = x) = True.
Proof. exact (@lem111066 Prop x). Qed.
Lemma lem111068 (P : type1605) (_2372 : nat) (_2373 : nat) : ((term84 P _2372 _2373) = (term84 P _2372 _2373)) = True.
Proof. exact (@lem111067 (term84 P _2372 _2373)). Qed.
Lemma lem111069 (P : type1605) (_2372 : nat) (_2373 : nat) : ((term88 P _2373 _2372) = (term84 P _2372 _2373)) = True.
Proof. exact (TRANS (@lem111064 P _2372 _2373) (@lem111068 P _2372 _2373)). Qed.
Lemma lem111070 (P : type1605) (_2372 : nat) (_2373 : nat) : True = ((term88 P _2373 _2372) = (term84 P _2372 _2373)).
Proof. exact (SYM (@lem111069 P _2372 _2373)). Qed.
Lemma lem111071 (P : type1605) (_2372 : nat) (_2373 : nat) : (term88 P _2373 _2372) = (term84 P _2372 _2373).
Proof. exact (EQ_MP (@lem111070 P _2372 _2373) (@lem0)). Qed.
Lemma lem111072 (_2372 : nat) (_2373 : nat) (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : term84 P _2372 _2373.
Proof. exact (EQ_MP (@lem111071 P _2372 _2373) (@lem110553 _2373 _2372 P m y h1)). Qed.
Lemma lem111074 (b : Prop) (a : Prop) : (a \/ b) = (term174 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem111075 (P : type1605) (_2373 : nat) (_2372 : nat) : (term84 P _2372 _2373) = (term242 P _2373 _2372).
Proof. exact (@lem111074 (term60 P _2372 _2373) (P _2373 _2372)). Qed.
Lemma lem111077 (a : Prop) : (term205 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem111078 (P : type1605) (_2372 : nat) (_2373 : nat) : (term211 P _2372 _2373) = (P _2372 _2373).
Proof. exact (@lem111077 (P _2372 _2373)). Qed.
Lemma lem111079 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem111080 (P : type1605) (_2372 : nat) (_2373 : nat) : (term243 P _2372 _2373) = (term244 P _2372 _2373).
Proof. exact (MK_COMB (@lem111079) (@lem111078 P _2372 _2373)). Qed.
Lemma lem111081 (P : type1605) (_2373 : nat) (_2372 : nat) : (P _2373 _2372) = (P _2373 _2372).
Proof. exact (eq_refl (P _2373 _2372)). Qed.
Lemma lem111082 (P : type1605) (_2373 : nat) (_2372 : nat) : (term242 P _2373 _2372) = (term245 P _2373 _2372).
Proof. exact (MK_COMB (@lem111080 P _2372 _2373) (@lem111081 P _2373 _2372)). Qed.
Lemma lem111083 (P : type1605) (_2373 : nat) (_2372 : nat) : (term84 P _2372 _2373) = (term245 P _2373 _2372).
Proof. exact (TRANS (@lem111075 P _2373 _2372) (@lem111082 P _2373 _2372)). Qed.
Lemma lem111086 (_2373 : nat) (_2372 : nat) (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : term245 P _2373 _2372.
Proof. exact (EQ_MP (@lem111083 P _2373 _2372) (@lem111072 _2372 _2373 P m y h1)). Qed.
Lemma lem111087 (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : term245 P m y.
Proof. exact (@lem111086 m y P m y h1). Qed.
Lemma lem111090 (P : type1605) (m : nat) (y : nat) (h1 : term10) (h2 : term60 P m y) (h3 : term153 P m y) : P m y.
Proof. exact (@lem111087 P m y h3 (@lem111043 P m y h1 h2 h3)). Qed.
Lemma lem111091 (P : type1605) (m : nat) (y : nat) (h1 : term10) (h2 : term153 P m y) : term239 P m y.
Proof. exact (fun h0 : term60 P m y => @lem111090 P m y h1 h0 h2). Qed.
Lemma lem111093 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem111094 (P : type1605) (m : nat) (y : nat) : (term239 P m y) = (P m y).
Proof. exact (@lem111093 (P m y)). Qed.
Lemma lem111095 (P : type1605) (m : nat) (y : nat) (h1 : term10) (h2 : term153 P m y) : P m y.
Proof. exact (EQ_MP (@lem111094 P m y) (@lem111091 P m y h1 h2)). Qed.
Lemma lem111098 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem111100 (P : type1605) (m : nat) (y : nat) : (term60 P m y) = (term246 P m y).
Proof. exact (@lem111098 (P m y)). Qed.
Lemma lem111103 (P : type1605) (m : nat) (y : nat) (h1 : term153 P m y) : term246 P m y.
Proof. exact (EQ_MP (@lem111100 P m y) (@lem110533 P m y h1)). Qed.
Lemma lem111106 (P : type1605) (m : nat) (y : nat) (h1 : term10) (h2 : term153 P m y) : False.
Proof. exact (@lem111103 P m y h2 (@lem111095 P m y h1 h2)). Qed.
Lemma lem111107 (P : type1605) (m : nat) (y : nat) (h1 : term10) (h2 : term153 P m y) : term247.
Proof. exact (fun h0 : ~ False => @lem111106 P m y h1 h2). Qed.
Lemma lem111109 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem111110 : term247 = False.
Proof. exact (@lem111109 False). Qed.
Lemma lem111111 (P : type1605) (m : nat) (y : nat) (h1 : term10) (h2 : term153 P m y) : False.
Proof. exact (EQ_MP (@lem111110) (@lem111107 P m y h1 h2)). Qed.
Lemma lem111112 (P : type1605) (m : nat) (y : nat) (h1 : term10) (h2 : term153 P m y) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem111111 P m y h1 h2) (fun h3 : False => @lem110435 h1)). Qed.
Lemma lem111113 (P : type1605) (m : nat) (y : nat) (h1 : term10) (h2 : term153 P m y) : False.
Proof. exact (EQ_MP (@lem111112 P m y h1 h2) (@lem110435 h1)). Qed.
Lemma lem111114 (P : type1605) (m : nat) (y : nat) (h1 : term10) (h2 : term153 P m y) : (term153 P m y) = False.
Proof. exact (prop_ext (fun h3 : term153 P m y => @lem111113 P m y h1 h2) (fun h3 : False => @lem110405 P m y h2)). Qed.
Lemma lem111115 (P : type1605) (m : nat) (y : nat) (h1 : term10) (h2 : term153 P m y) : False.
Proof. exact (EQ_MP (@lem111114 P m y h1 h2) (@lem110405 P m y h2)). Qed.
Lemma lem111116 (P : type1605) (m : nat) (y : nat) (h1 : term10) (h2 : term153 P m y) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem111115 P m y h1 h2) (fun h3 : False => @lem110314 h1)). Qed.
Lemma lem111117 (P : type1605) (m : nat) (y : nat) (h1 : term10) (h2 : term153 P m y) : False.
Proof. exact (EQ_MP (@lem111116 P m y h1 h2) (@lem110314 h1)). Qed.
Lemma lem111118 (P : type1605) (m : nat) (h1 : term10) (h2 : term156 P m) : False.
Proof. exact (ex_elim (@lem110285 P m h2) (fun y : nat => fun h0 : term155 P m y => @lem111117 P m y h1 h0)). Qed.
Lemma lem111119 (P : type1605) (h1 : term10) (h2 : term3 P) : False.
Proof. exact (ex_elim (@lem110212 P h2) (fun m : nat => fun h0 : term157 P m => @lem111118 P m h1 h0)). Qed.
Lemma lem111120 (P : type1605) (h1 : term10) (h2 : term3 P) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem111119 P h1 h2) (fun h3 : False => @lem110284 h1)). Qed.
Lemma lem111121 (P : type1605) (h1 : term10) (h2 : term3 P) : False.
Proof. exact (EQ_MP (@lem111120 P h1 h2) (@lem110284 h1)). Qed.
Lemma lem111122 (P : type1605) (h1 : term3 P) : term8.
Proof. exact (fun h0 : term10 => @lem111121 P h0 h1). Qed.
Lemma lem111123 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem111124 (P : type1605) (h1 : term3 P) : term9.
Proof. exact (EQ_MP (@lem111123) (@lem111122 P h1)). Qed.
Lemma lem111125 (P : type1605) : term12 P.
Proof. exact (fun h0 : term3 P => @lem111124 P h0). Qed.
Lemma lem111130 : term16.
Proof. exact (fun P : type1605 => @lem111125 P). Qed.
Lemma lem111131 : term15.
Proof. exact (EQ_MP (@lem109757) (@lem111130)). Qed.
Lemma lem111132 (P : type1605) : term248 P.
Proof. exact (@lem111131 P). Qed.
Lemma lem111133 (P : type1605) : (term248 P) = (term4 P).
Proof. exact (eq_refl (term248 P)). Qed.
Lemma lem111134 (P : type1605) : term4 P.
Proof. exact (EQ_MP (@lem111133 P) (@lem111132 P)). Qed.
Lemma lem111136 (P : type1605) : term4 P.
Proof. exact (@lem109496 P (@lem111134 P)). Qed.
Lemma lem111137 (P : type1605) (h1 : term3 P) : term8.
Proof. exact (@lem111136 P (@lem109481 P h1)). Qed.
Lemma lem111138 (P : type1605) (h1 : term3 P) : False.
Proof. exact (@lem111137 P h1 (@lem96657)). Qed.
Lemma lem111139 (P : type1605) (h1 : term3 P) : (term3 P) = False.
Proof. exact (prop_ext (fun h2 : term3 P => @lem111138 P h1) (fun h2 : False => @lem109481 P h1)). Qed.
Lemma lem111140 (P : type1605) (h1 : term3 P) : False.
Proof. exact (EQ_MP (@lem111139 P h1) (@lem109481 P h1)). Qed.
Lemma lem111141 (P : type1605) : term2 P.
Proof. exact (fun h0 : term3 P => @lem111140 P h0). Qed.
Lemma lem111142 (P : type1605) : term1 P.
Proof. exact (EQ_MP (@lem109480 P) (@lem111141 P)). Qed.
