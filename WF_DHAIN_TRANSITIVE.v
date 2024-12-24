Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import WF_DHAIN_TRANSITIVE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import MONO_EXISTS_spec.
Require Import TRANSITIVE_STEPWISE_LT_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1831_spec.
Require Import thm18392_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
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
Require Import thm310219_spec.
Require Import thm316636_spec.
Require Import thm32_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm89994_spec.
Lemma lem316638 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem316639 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem316640 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem316639 t1) (@lem316638 t1)). Qed.
Lemma lem316641 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem316640 t1 t2). Qed.
Lemma lem316642 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem316643 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem316642 t1 t2) (@lem316641 t1 t2)). Qed.
Lemma lem316644 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem316643 t1 t2 t3). Qed.
Lemma lem316645 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem316646 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem316645 t1 t2 t3) (@lem316644 t1 t2 t3)). Qed.
Lemma lem316647 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem316646 t1 t2 t3)). Qed.
Lemma lem316648 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem316649 (R : type1605) (h1 : term7) : term8 R.
Proof. exact (@lem316648 h1 R). Qed.
Lemma lem316650 (R : type1605) : (term8 R) = (term9 R).
Proof. exact (eq_refl (term8 R)). Qed.
Lemma lem316651 (R : type1605) (h1 : term7) : term9 R.
Proof. exact (EQ_MP (@lem316650 R) (@lem316649 R h1)). Qed.
Lemma lem316652 (R : type1605) (h1 : term10 R) : term10 R.
Proof. exact (h1). Qed.
Lemma lem316653 (R : type1605) (h1 : term7) (h2 : term10 R) : term11 R.
Proof. exact (@lem316651 R h1 (@lem316652 R h2)). Qed.
Lemma lem316654 (R : type1605) (h1 : term10 R) : term12 R.
Proof. exact (fun h0 : term7 => @lem316653 R h0 h1). Qed.
Lemma lem316655 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem316656 (R : type1605) (h1 : term7) (h2 : term10 R) : term11 R.
Proof. exact (@lem316654 R h2 (@lem316655 h1)). Qed.
Lemma lem316657 (R : type1605) (h1 : term7) : term9 R.
Proof. exact (fun h0 : term10 R => @lem316656 R h1 h0). Qed.
Lemma lem316658 (h1 : term7) : term7.
Proof. exact (fun R : type1605 => @lem316657 R h1). Qed.
Lemma lem316659 : term13.
Proof. exact (fun h0 : term7 => @lem316658 h0). Qed.
Lemma lem316660 : term7.
Proof. exact (@lem316659 (@lem286705)). Qed.
Lemma lem316661 (R : type1605) : term8 R.
Proof. exact (@lem316660 R). Qed.
Lemma lem316662 (R : type1605) : (term8 R) = (term9 R).
Proof. exact (eq_refl (term8 R)). Qed.
Lemma lem316664 : term14.
Proof. exact (proj2 (@lem89994)). Qed.
Lemma lem316665 (m : nat) : term15 m.
Proof. exact (@lem316664 m). Qed.
Lemma lem316666 (m : nat) : (term15 m) = (term16 m).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem316667 (m : nat) : term16 m.
Proof. exact (EQ_MP (@lem316666 m) (@lem316665 m)). Qed.
Lemma lem316668 (m : nat) (n : nat) : term17 m n.
Proof. exact (@lem316667 m n). Qed.
Lemma lem316669 (m : nat) (n : nat) : (term17 m n) = ((term18 m n) = (term19 m n)).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem316675 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term20 A P Q) : term20 A P Q.
Proof. exact (h1). Qed.
Lemma lem316676 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term21 A P Q) : term21 A P Q.
Proof. exact (h1). Qed.
Lemma lem316677 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term21 A P Q) (h2 : term20 A P Q) : term22 A P Q.
Proof. exact (@lem316675 A P Q h2 (@lem316676 A P Q h1)). Qed.
Lemma lem316678 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term21 A P Q) : term23 A P Q.
Proof. exact (fun h0 : term20 A P Q => @lem316677 A P Q h1 h0). Qed.
Lemma lem316679 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term20 A P Q) : term20 A P Q.
Proof. exact (h1). Qed.
Lemma lem316680 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term21 A P Q) (h2 : term20 A P Q) : term22 A P Q.
Proof. exact (@lem316678 A P Q h1 (@lem316679 A P Q h2)). Qed.
Lemma lem316681 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term20 A P Q) : term20 A P Q.
Proof. exact (fun h0 : term21 A P Q => @lem316680 A P Q h0 h1). Qed.
Lemma lem316682 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term24 A P Q.
Proof. exact (fun h0 : term20 A P Q => @lem316681 A P Q h0). Qed.
Lemma lem316684 {A : Type'} (lt2 : type1402 A) (h1 : term25 A lt2) : term25 A lt2.
Proof. exact (h1). Qed.
Lemma lem316688 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term26 A lt2).
Proof. exact (EQ_MP (@lem310219 A lt2) (@lem316636 A lt2)). Qed.
Lemma lem316689 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term26 A lt2).
Proof. exact (@lem316688 A lt2). Qed.
Lemma lem316698 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem316699 {A : Type'} (lt2 : type1402 A) : (term27 A lt2) = (term28 A lt2).
Proof. exact (MK_COMB (@lem316698) (@lem316689 A lt2)). Qed.
Lemma lem316714 {A : Type'} (lt2 : type1402 A) : (term29 A lt2) = (term29 A lt2).
Proof. exact (eq_refl (term29 A lt2)). Qed.
Lemma lem316715 {A : Type'} (lt2 : type1402 A) : ((@WF A lt2) = (term29 A lt2)) = ((term26 A lt2) = (term29 A lt2)).
Proof. exact (MK_COMB (@lem316699 A lt2) (@lem316714 A lt2)). Qed.
Lemma lem316718 {A : Type'} (lt2 : type1402 A) : ((term26 A lt2) = (term29 A lt2)) = ((@WF A lt2) = (term29 A lt2)).
Proof. exact (SYM (@lem316715 A lt2)). Qed.
Lemma lem316719 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem316721 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term20 A P Q.
Proof. exact (@lem316682 A P Q (@lem7401 A P Q)). Qed.
Lemma lem316722 {A : Type'} (P : type976 A) (Q : type976 A) : term30 A P Q.
Proof. exact (@lem316721 (nat -> A) P Q). Qed.
Lemma lem316723 {A : Type'} (lt2 : type1402 A) : term31 A lt2.
Proof. exact (@lem316722 A (term32 A lt2) (term33 A lt2)). Qed.
Lemma lem316724 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term34 A lt2 s) = (term35 A lt2 s).
Proof. exact (eq_refl (term34 A lt2 s)). Qed.
Lemma lem316725 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem316726 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term36 A lt2 s) = (term37 A lt2 s).
Proof. exact (MK_COMB (@lem316725) (@lem316724 A lt2 s)). Qed.
Lemma lem316727 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term38 A lt2 s) = (term39 A lt2 s).
Proof. exact (eq_refl (term38 A lt2 s)). Qed.
Lemma lem316728 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term40 A lt2 s) = (term41 A lt2 s).
Proof. exact (MK_COMB (@lem316726 A lt2 s) (@lem316727 A lt2 s)). Qed.
Lemma lem316729 {A : Type'} (lt2 : type1402 A) : (term42 A lt2) = (term43 A lt2).
Proof. exact (fun_ext (fun s : nat -> A => @lem316728 A lt2 s)). Qed.
Lemma lem316730 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem316731 {A : Type'} (lt2 : type1402 A) : (term44 A lt2) = (term45 A lt2).
Proof. exact (MK_COMB (@lem316730 A) (@lem316729 A lt2)). Qed.
Lemma lem316732 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem316733 {A : Type'} (lt2 : type1402 A) : (term46 A lt2) = (term47 A lt2).
Proof. exact (MK_COMB (@lem316732) (@lem316731 A lt2)). Qed.
Lemma lem316734 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term34 A lt2 s) = (term35 A lt2 s).
Proof. exact (eq_refl (term34 A lt2 s)). Qed.
Lemma lem316735 {A : Type'} (lt2 : type1402 A) : (term48 A lt2) = (term32 A lt2).
Proof. exact (fun_ext (fun s : nat -> A => @lem316734 A lt2 s)). Qed.
Lemma lem316736 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem316737 {A : Type'} (lt2 : type1402 A) : (term49 A lt2) = (term50 A lt2).
Proof. exact (MK_COMB (@lem316736 A) (@lem316735 A lt2)). Qed.
Lemma lem316738 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem316739 {A : Type'} (lt2 : type1402 A) : (term51 A lt2) = (term52 A lt2).
Proof. exact (MK_COMB (@lem316738) (@lem316737 A lt2)). Qed.
Lemma lem316740 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term38 A lt2 s) = (term39 A lt2 s).
Proof. exact (eq_refl (term38 A lt2 s)). Qed.
Lemma lem316741 {A : Type'} (lt2 : type1402 A) : (term53 A lt2) = (term33 A lt2).
Proof. exact (fun_ext (fun s : nat -> A => @lem316740 A lt2 s)). Qed.
Lemma lem316742 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem316743 {A : Type'} (lt2 : type1402 A) : (term54 A lt2) = (term55 A lt2).
Proof. exact (MK_COMB (@lem316742 A) (@lem316741 A lt2)). Qed.
Lemma lem316744 {A : Type'} (lt2 : type1402 A) : (term56 A lt2) = (term57 A lt2).
Proof. exact (MK_COMB (@lem316739 A lt2) (@lem316743 A lt2)). Qed.
Lemma lem316745 {A : Type'} (lt2 : type1402 A) : (term31 A lt2) = (term58 A lt2).
Proof. exact (MK_COMB (@lem316733 A lt2) (@lem316744 A lt2)). Qed.
Lemma lem316746 {A : Type'} (lt2 : type1402 A) : term58 A lt2.
Proof. exact (EQ_MP (@lem316745 A lt2) (@lem316723 A lt2)). Qed.
Lemma lem316748 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term20 A P Q.
Proof. exact (@lem316682 A P Q (@lem7401 A P Q)). Qed.
Lemma lem316749 {A : Type'} (P : type976 A) (Q : type976 A) : term30 A P Q.
Proof. exact (@lem316748 (nat -> A) P Q). Qed.
Lemma lem316750 {A : Type'} (lt2 : type1402 A) : term59 A lt2.
Proof. exact (@lem316749 A (term33 A lt2) (term32 A lt2)). Qed.
Lemma lem316751 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term38 A lt2 s) = (term39 A lt2 s).
Proof. exact (eq_refl (term38 A lt2 s)). Qed.
Lemma lem316752 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem316753 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term60 A lt2 s) = (term61 A lt2 s).
Proof. exact (MK_COMB (@lem316752) (@lem316751 A lt2 s)). Qed.
Lemma lem316754 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term34 A lt2 s) = (term35 A lt2 s).
Proof. exact (eq_refl (term34 A lt2 s)). Qed.
Lemma lem316755 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term62 A lt2 s) = (term63 A lt2 s).
Proof. exact (MK_COMB (@lem316753 A lt2 s) (@lem316754 A lt2 s)). Qed.
Lemma lem316756 {A : Type'} (lt2 : type1402 A) : (term64 A lt2) = (term65 A lt2).
Proof. exact (fun_ext (fun s : nat -> A => @lem316755 A lt2 s)). Qed.
Lemma lem316757 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem316758 {A : Type'} (lt2 : type1402 A) : (term66 A lt2) = (term67 A lt2).
Proof. exact (MK_COMB (@lem316757 A) (@lem316756 A lt2)). Qed.
Lemma lem316759 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem316760 {A : Type'} (lt2 : type1402 A) : (term68 A lt2) = (term69 A lt2).
Proof. exact (MK_COMB (@lem316759) (@lem316758 A lt2)). Qed.
Lemma lem316761 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term38 A lt2 s) = (term39 A lt2 s).
Proof. exact (eq_refl (term38 A lt2 s)). Qed.
Lemma lem316762 {A : Type'} (lt2 : type1402 A) : (term53 A lt2) = (term33 A lt2).
Proof. exact (fun_ext (fun s : nat -> A => @lem316761 A lt2 s)). Qed.
Lemma lem316763 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem316764 {A : Type'} (lt2 : type1402 A) : (term54 A lt2) = (term55 A lt2).
Proof. exact (MK_COMB (@lem316763 A) (@lem316762 A lt2)). Qed.
Lemma lem316765 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem316766 {A : Type'} (lt2 : type1402 A) : (term70 A lt2) = (term71 A lt2).
Proof. exact (MK_COMB (@lem316765) (@lem316764 A lt2)). Qed.
Lemma lem316767 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term34 A lt2 s) = (term35 A lt2 s).
Proof. exact (eq_refl (term34 A lt2 s)). Qed.
Lemma lem316768 {A : Type'} (lt2 : type1402 A) : (term48 A lt2) = (term32 A lt2).
Proof. exact (fun_ext (fun s : nat -> A => @lem316767 A lt2 s)). Qed.
Lemma lem316769 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem316770 {A : Type'} (lt2 : type1402 A) : (term49 A lt2) = (term50 A lt2).
Proof. exact (MK_COMB (@lem316769 A) (@lem316768 A lt2)). Qed.
Lemma lem316771 {A : Type'} (lt2 : type1402 A) : (term72 A lt2) = (term73 A lt2).
Proof. exact (MK_COMB (@lem316766 A lt2) (@lem316770 A lt2)). Qed.
Lemma lem316772 {A : Type'} (lt2 : type1402 A) : (term59 A lt2) = (term74 A lt2).
Proof. exact (MK_COMB (@lem316760 A lt2) (@lem316771 A lt2)). Qed.
Lemma lem316773 {A : Type'} (lt2 : type1402 A) : term74 A lt2.
Proof. exact (EQ_MP (@lem316772 A lt2) (@lem316750 A lt2)). Qed.
Lemma lem316875 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term75 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem316876 (p : Prop) (q : Prop) (p' : Prop) : term76 p q p'.
Proof. exact (fun q' : Prop => @lem316875 p q p' q'). Qed.
Lemma lem316877 (p : Prop) (q : Prop) : term77 p q.
Proof. exact (fun p' : Prop => @lem316876 p q p'). Qed.
Lemma lem316878 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term78 A lt2 s.
Proof. exact (@lem316877 (term39 A lt2 s) (term35 A lt2 s)). Qed.
Lemma lem316879 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (p' : Prop) : term79 A lt2 s p'.
Proof. exact (@lem316878 A lt2 s p'). Qed.
Lemma lem316880 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (p' : Prop) : (term79 A lt2 s p') = (term80 A lt2 s p').
Proof. exact (eq_refl (term79 A lt2 s p')). Qed.
Lemma lem316881 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (p' : Prop) : term80 A lt2 s p'.
Proof. exact (EQ_MP (@lem316880 A lt2 s p') (@lem316879 A lt2 s p')). Qed.
Lemma lem316882 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (p' : Prop) (q' : Prop) : term81 A lt2 s p' q'.
Proof. exact (@lem316881 A lt2 s p' q'). Qed.
Lemma lem316883 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (p' : Prop) (q' : Prop) : (term81 A lt2 s p' q') = (term82 A lt2 s p' q').
Proof. exact (eq_refl (term81 A lt2 s p' q')). Qed.
Lemma lem316884 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (p' : Prop) (q' : Prop) : term82 A lt2 s p' q'.
Proof. exact (EQ_MP (@lem316883 A lt2 s p' q') (@lem316882 A lt2 s p' q')). Qed.
Lemma lem316916 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term39 A lt2 s) = (term39 A lt2 s).
Proof. exact (eq_refl (term39 A lt2 s)). Qed.
Lemma lem316917 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (q' : Prop) : term83 A lt2 s q'.
Proof. exact (@lem316884 A lt2 s (term39 A lt2 s) q'). Qed.
Lemma lem316918 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (q' : Prop) : term84 A lt2 s q'.
Proof. exact (@lem316917 A lt2 s q' (@lem316916 A lt2 s)). Qed.
Lemma lem316919 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term39 A lt2 s) : term39 A lt2 s.
Proof. exact (h1). Qed.
Lemma lem316920 {A : Type'} (i : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term39 A lt2 s) : term85 A lt2 s i.
Proof. exact (@lem316919 A lt2 s h1 i). Qed.
Lemma lem316921 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (i : nat) : (term85 A lt2 s i) = (term86 A lt2 s i).
Proof. exact (eq_refl (term85 A lt2 s i)). Qed.
Lemma lem316922 {A : Type'} (i : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term39 A lt2 s) : term86 A lt2 s i.
Proof. exact (EQ_MP (@lem316921 A lt2 s i) (@lem316920 A i lt2 s h1)). Qed.
Lemma lem316923 {A : Type'} (i : nat) (j : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term39 A lt2 s) : term87 A lt2 s i j.
Proof. exact (@lem316922 A i lt2 s h1 j). Qed.
Lemma lem316924 {A : Type'} (lt2 : type1402 A) (j : nat) (s : nat -> A) (i : nat) : (term87 A lt2 s i j) = (term88 A lt2 j s i).
Proof. exact (eq_refl (term87 A lt2 s i j)). Qed.
Lemma lem316925 {A : Type'} (j : nat) (i : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term39 A lt2 s) : term88 A lt2 j s i.
Proof. exact (EQ_MP (@lem316924 A lt2 j s i) (@lem316923 A i j lt2 s h1)). Qed.
Lemma lem316926 (i : nat) (j : nat) (h1 : Peano.lt i j) : Peano.lt i j.
Proof. exact (h1). Qed.
Lemma lem316927 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (i : nat) (j : nat) (h1 : term39 A lt2 s) (h2 : Peano.lt i j) : term89 A lt2 j s i.
Proof. exact (@lem316925 A j i lt2 s h1 (@lem316926 i j h2)). Qed.
Lemma lem316928 {A : Type'} (lt2 : type1402 A) (j : nat) (s : nat -> A) (i : nat) : (term89 A lt2 j s i) = ((term89 A lt2 j s i) = True).
Proof. exact (@lem7 (term89 A lt2 j s i)). Qed.
Lemma lem316929 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (i : nat) (j : nat) (h1 : term39 A lt2 s) (h2 : Peano.lt i j) : (term89 A lt2 j s i) = True.
Proof. exact (EQ_MP (@lem316928 A lt2 j s i) (@lem316927 A lt2 s i j h1 h2)). Qed.
Lemma lem316940 {A : Type'} (j : nat) (i : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term39 A lt2 s) : term90 A lt2 j s i.
Proof. exact (fun h0 : Peano.lt i j => @lem316929 A lt2 s i j h1 h0). Qed.
Lemma lem316941 {A : Type'} (n : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term39 A lt2 s) : term91 A lt2 s n.
Proof. exact (@lem316940 A (S n) n lt2 s h1). Qed.
Lemma lem316943 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (EQ_MP (@lem316669 m n) (@lem316668 m n)). Qed.
Lemma lem316944 (n : nat) : (term92 n) = (term93 n).
Proof. exact (@lem316943 n n). Qed.
Lemma lem316948 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem316949 (x : nat) : (x = x) = True.
Proof. exact (@lem316948 nat x). Qed.
Lemma lem316950 (n : nat) : (n = n) = True.
Proof. exact (@lem316949 n). Qed.
Lemma lem316951 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem316952 (n : nat) : (term94 n) = (or True).
Proof. exact (MK_COMB (@lem316951) (@lem316950 n)). Qed.
Lemma lem316953 (n : nat) : (Peano.lt n n) = (Peano.lt n n).
Proof. exact (eq_refl (Peano.lt n n)). Qed.
Lemma lem316954 (n : nat) : (term93 n) = (term95 n).
Proof. exact (MK_COMB (@lem316952 n) (@lem316953 n)). Qed.
Lemma lem316956 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem316957 (n : nat) : (term95 n) = True.
Proof. exact (@lem316956 (Peano.lt n n)). Qed.
Lemma lem316958 (n : nat) : (term93 n) = True.
Proof. exact (TRANS (@lem316954 n) (@lem316957 n)). Qed.
Lemma lem316959 (n : nat) : (term92 n) = True.
Proof. exact (TRANS (@lem316944 n) (@lem316958 n)). Qed.
Lemma lem316960 (n : nat) : True = (term92 n).
Proof. exact (SYM (@lem316959 n)). Qed.
Lemma lem316961 (n : nat) : term92 n.
Proof. exact (EQ_MP (@lem316960 n) (@lem0)). Qed.
Lemma lem316962 {A : Type'} (n : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term39 A lt2 s) : (term96 A lt2 s n) = True.
Proof. exact (@lem316941 A n lt2 s h1 (@lem316961 n)). Qed.
Lemma lem316963 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term39 A lt2 s) : (term97 A lt2 s) = term98.
Proof. exact (fun_ext (fun n : nat => @lem316962 A n lt2 s h1)). Qed.
Lemma lem316964 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem316965 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term39 A lt2 s) : (term35 A lt2 s) = term99.
Proof. exact (MK_COMB (@lem316964) (@lem316963 A lt2 s h1)). Qed.
Lemma lem316967 {A : Type'} (t : Prop) : (term100 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem316968 (t : Prop) : (term101 t) = t.
Proof. exact (@lem316967 nat t). Qed.
Lemma lem316969 : term99 = True.
Proof. exact (@lem316968 True). Qed.
Lemma lem316970 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term39 A lt2 s) : (term35 A lt2 s) = True.
Proof. exact (TRANS (@lem316965 A lt2 s h1) (@lem316969)). Qed.
Lemma lem316971 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term102 A lt2 s.
Proof. exact (fun h0 : term39 A lt2 s => @lem316970 A lt2 s h0). Qed.
Lemma lem316972 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term103 A lt2 s.
Proof. exact (@lem316918 A lt2 s True). Qed.
Lemma lem316973 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term63 A lt2 s) = (term104 A lt2 s).
Proof. exact (@lem316972 A lt2 s (@lem316971 A lt2 s)). Qed.
Lemma lem316975 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem316976 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term104 A lt2 s) = True.
Proof. exact (@lem316975 (term39 A lt2 s)). Qed.
Lemma lem316977 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term63 A lt2 s) = True.
Proof. exact (TRANS (@lem316973 A lt2 s) (@lem316976 A lt2 s)). Qed.
Lemma lem316978 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : True = (term63 A lt2 s).
Proof. exact (SYM (@lem316977 A lt2 s)). Qed.
Lemma lem316979 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term63 A lt2 s.
Proof. exact (EQ_MP (@lem316978 A lt2 s) (@lem0)). Qed.
Lemma lem316980 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term35 A lt2 s) : term35 A lt2 s.
Proof. exact (h1). Qed.
Lemma lem316982 (R : type1605) : term9 R.
Proof. exact (EQ_MP (@lem316662 R) (@lem316661 R)). Qed.
Lemma lem316983 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term105 A lt2 s.
Proof. exact (@lem316982 (term106 A lt2 s)). Qed.
Lemma lem316984 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term107 A lt2 s x) = (term108 A lt2 s x).
Proof. exact (eq_refl (term107 A lt2 s x)). Qed.
Lemma lem316985 (y : nat) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem316986 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) (y : nat) : (term109 A lt2 s x y) = (term110 A lt2 s x y).
Proof. exact (MK_COMB (@lem316984 A lt2 s x) (@lem316985 y)). Qed.
Lemma lem316987 {A : Type'} (lt2 : type1402 A) (y : nat) (s : nat -> A) (x : nat) : (term110 A lt2 s x y) = (term89 A lt2 y s x).
Proof. exact (eq_refl (term110 A lt2 s x y)). Qed.
Lemma lem316988 {A : Type'} (lt2 : type1402 A) (y : nat) (s : nat -> A) (x : nat) : (term109 A lt2 s x y) = (term89 A lt2 y s x).
Proof. exact (TRANS (@lem316986 A lt2 s x y) (@lem316987 A lt2 y s x)). Qed.
Lemma lem316989 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem316990 {A : Type'} (lt2 : type1402 A) (y : nat) (s : nat -> A) (x : nat) : (term111 A lt2 s x y) = (term112 A lt2 y s x).
Proof. exact (MK_COMB (@lem316989) (@lem316988 A lt2 y s x)). Qed.
Lemma lem316991 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (y : nat) : (term107 A lt2 s y) = (term108 A lt2 s y).
Proof. exact (eq_refl (term107 A lt2 s y)). Qed.
Lemma lem316992 (z : nat) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem316993 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (y : nat) (z : nat) : (term109 A lt2 s y z) = (term110 A lt2 s y z).
Proof. exact (MK_COMB (@lem316991 A lt2 s y) (@lem316992 z)). Qed.
Lemma lem316994 {A : Type'} (lt2 : type1402 A) (z : nat) (s : nat -> A) (y : nat) : (term110 A lt2 s y z) = (term89 A lt2 z s y).
Proof. exact (eq_refl (term110 A lt2 s y z)). Qed.
Lemma lem316995 {A : Type'} (lt2 : type1402 A) (z : nat) (s : nat -> A) (y : nat) : (term109 A lt2 s y z) = (term89 A lt2 z s y).
Proof. exact (TRANS (@lem316993 A lt2 s y z) (@lem316994 A lt2 z s y)). Qed.
Lemma lem316996 {A : Type'} (x : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (y : nat) : (term113 A x lt2 s y z) = (term114 A x lt2 z s y).
Proof. exact (MK_COMB (@lem316990 A lt2 y s x) (@lem316995 A lt2 z s y)). Qed.
Lemma lem316997 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem316998 {A : Type'} (x : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (y : nat) : (term115 A x lt2 s y z) = (term116 A x lt2 z s y).
Proof. exact (MK_COMB (@lem316997) (@lem316996 A x lt2 z s y)). Qed.
Lemma lem316999 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term107 A lt2 s x) = (term108 A lt2 s x).
Proof. exact (eq_refl (term107 A lt2 s x)). Qed.
Lemma lem317000 (z : nat) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem317001 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) (z : nat) : (term109 A lt2 s x z) = (term110 A lt2 s x z).
Proof. exact (MK_COMB (@lem316999 A lt2 s x) (@lem317000 z)). Qed.
Lemma lem317002 {A : Type'} (lt2 : type1402 A) (z : nat) (s : nat -> A) (x : nat) : (term110 A lt2 s x z) = (term89 A lt2 z s x).
Proof. exact (eq_refl (term110 A lt2 s x z)). Qed.
Lemma lem317003 {A : Type'} (lt2 : type1402 A) (z : nat) (s : nat -> A) (x : nat) : (term109 A lt2 s x z) = (term89 A lt2 z s x).
Proof. exact (TRANS (@lem317001 A lt2 s x z) (@lem317002 A lt2 z s x)). Qed.
Lemma lem317004 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (x : nat) : (term117 A y lt2 s x z) = (term118 A y lt2 z s x).
Proof. exact (MK_COMB (@lem316998 A x lt2 z s y) (@lem317003 A lt2 z s x)). Qed.
Lemma lem317005 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term119 A y lt2 s x) = (term120 A y lt2 s x).
Proof. exact (fun_ext (fun z : nat => @lem317004 A y lt2 z s x)). Qed.
Lemma lem317006 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem317007 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term121 A y lt2 s x) = (term122 A y lt2 s x).
Proof. exact (MK_COMB (@lem317006) (@lem317005 A y lt2 s x)). Qed.
Lemma lem317008 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term123 A lt2 s x) = (term124 A lt2 s x).
Proof. exact (fun_ext (fun y : nat => @lem317007 A y lt2 s x)). Qed.
Lemma lem317009 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem317010 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term125 A lt2 s x) = (term126 A lt2 s x).
Proof. exact (MK_COMB (@lem317009) (@lem317008 A lt2 s x)). Qed.
Lemma lem317011 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term127 A lt2 s) = (term128 A lt2 s).
Proof. exact (fun_ext (fun x : nat => @lem317010 A lt2 s x)). Qed.
Lemma lem317012 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem317013 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term129 A lt2 s) = (term130 A lt2 s).
Proof. exact (MK_COMB (@lem317012) (@lem317011 A lt2 s)). Qed.
Lemma lem317014 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem317015 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term131 A lt2 s) = (term132 A lt2 s).
Proof. exact (MK_COMB (@lem317014) (@lem317013 A lt2 s)). Qed.
Lemma lem317016 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term107 A lt2 s j) = (term108 A lt2 s j).
Proof. exact (eq_refl (term107 A lt2 s j)). Qed.
Lemma lem317017 (j : nat) : (S j) = (S j).
Proof. exact (eq_refl (S j)). Qed.
Lemma lem317018 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term133 A lt2 s j) = (term134 A lt2 s j).
Proof. exact (MK_COMB (@lem317016 A lt2 s j) (@lem317017 j)). Qed.
Lemma lem317019 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term134 A lt2 s j) = (term96 A lt2 s j).
Proof. exact (eq_refl (term134 A lt2 s j)). Qed.
Lemma lem317020 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term133 A lt2 s j) = (term96 A lt2 s j).
Proof. exact (TRANS (@lem317018 A lt2 s j) (@lem317019 A lt2 s j)). Qed.
Lemma lem317021 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term135 A lt2 s) = (term97 A lt2 s).
Proof. exact (fun_ext (fun j : nat => @lem317020 A lt2 s j)). Qed.
Lemma lem317022 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem317023 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term136 A lt2 s) = (term35 A lt2 s).
Proof. exact (MK_COMB (@lem317022) (@lem317021 A lt2 s)). Qed.
Lemma lem317024 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term137 A lt2 s) = (term138 A lt2 s).
Proof. exact (MK_COMB (@lem317015 A lt2 s) (@lem317023 A lt2 s)). Qed.
Lemma lem317025 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem317026 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term139 A lt2 s) = (term140 A lt2 s).
Proof. exact (MK_COMB (@lem317025) (@lem317024 A lt2 s)). Qed.
Lemma lem317027 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (i : nat) : (term107 A lt2 s i) = (term108 A lt2 s i).
Proof. exact (eq_refl (term107 A lt2 s i)). Qed.
Lemma lem317028 (j : nat) : j = j.
Proof. exact (eq_refl j). Qed.
Lemma lem317029 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (i : nat) (j : nat) : (term109 A lt2 s i j) = (term110 A lt2 s i j).
Proof. exact (MK_COMB (@lem317027 A lt2 s i) (@lem317028 j)). Qed.
Lemma lem317030 {A : Type'} (lt2 : type1402 A) (j : nat) (s : nat -> A) (i : nat) : (term110 A lt2 s i j) = (term89 A lt2 j s i).
Proof. exact (eq_refl (term110 A lt2 s i j)). Qed.
Lemma lem317031 {A : Type'} (lt2 : type1402 A) (j : nat) (s : nat -> A) (i : nat) : (term109 A lt2 s i j) = (term89 A lt2 j s i).
Proof. exact (TRANS (@lem317029 A lt2 s i j) (@lem317030 A lt2 j s i)). Qed.
Lemma lem317032 (i : nat) (j : nat) : (term141 i j) = (term141 i j).
Proof. exact (eq_refl (term141 i j)). Qed.
Lemma lem317033 {A : Type'} (lt2 : type1402 A) (j : nat) (s : nat -> A) (i : nat) : (term142 A lt2 s i j) = (term88 A lt2 j s i).
Proof. exact (MK_COMB (@lem317032 i j) (@lem317031 A lt2 j s i)). Qed.
Lemma lem317034 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (i : nat) : (term143 A lt2 s i) = (term144 A lt2 s i).
Proof. exact (fun_ext (fun j : nat => @lem317033 A lt2 j s i)). Qed.
Lemma lem317035 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem317036 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (i : nat) : (term145 A lt2 s i) = (term86 A lt2 s i).
Proof. exact (MK_COMB (@lem317035) (@lem317034 A lt2 s i)). Qed.
Lemma lem317037 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term146 A lt2 s) = (term147 A lt2 s).
Proof. exact (fun_ext (fun i : nat => @lem317036 A lt2 s i)). Qed.
Lemma lem317038 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem317039 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term148 A lt2 s) = (term39 A lt2 s).
Proof. exact (MK_COMB (@lem317038) (@lem317037 A lt2 s)). Qed.
Lemma lem317040 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term105 A lt2 s) = (term149 A lt2 s).
Proof. exact (MK_COMB (@lem317026 A lt2 s) (@lem317039 A lt2 s)). Qed.
Lemma lem317041 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term149 A lt2 s.
Proof. exact (EQ_MP (@lem317040 A lt2 s) (@lem316983 A lt2 s)). Qed.
Lemma lem317043 (p : Prop) : p = (term150 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem317044 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term138 A lt2 s) = (term151 A lt2 s).
Proof. exact (@lem317043 (term138 A lt2 s)). Qed.
Lemma lem317045 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term151 A lt2 s) = (term138 A lt2 s).
Proof. exact (SYM (@lem317044 A lt2 s)). Qed.
Lemma lem317046 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term152 A lt2 s) : term152 A lt2 s.
Proof. exact (h1). Qed.
Lemma lem317049 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term153 A lt2 s) : term153 A lt2 s.
Proof. exact (h1). Qed.
Lemma lem317050 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term154 A lt2 s.
Proof. exact (fun h0 : term153 A lt2 s => @lem317049 A lt2 s h0). Qed.
Lemma lem317051 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term154 A lt2 s) : term154 A lt2 s.
Proof. exact (h1). Qed.
Lemma lem317052 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term153 A lt2 s) : term153 A lt2 s.
Proof. exact (h1). Qed.
Lemma lem317053 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term153 A lt2 s) (h2 : term154 A lt2 s) : term153 A lt2 s.
Proof. exact (@lem317051 A lt2 s h2 (@lem317052 A lt2 s h1)). Qed.
Lemma lem317054 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term153 A lt2 s) : term155 A lt2 s.
Proof. exact (fun h0 : term154 A lt2 s => @lem317053 A lt2 s h1 h0). Qed.
Lemma lem317055 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term154 A lt2 s) : term154 A lt2 s.
Proof. exact (h1). Qed.
Lemma lem317056 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term153 A lt2 s) (h2 : term154 A lt2 s) : term153 A lt2 s.
Proof. exact (@lem317054 A lt2 s h1 (@lem317055 A lt2 s h2)). Qed.
Lemma lem317057 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term154 A lt2 s) : term154 A lt2 s.
Proof. exact (fun h0 : term153 A lt2 s => @lem317056 A lt2 s h0 h1). Qed.
Lemma lem317058 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term156 A lt2 s.
Proof. exact (fun h0 : term154 A lt2 s => @lem317057 A lt2 s h0). Qed.
Lemma lem317061 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term154 A lt2 s.
Proof. exact (@lem317058 A lt2 s (@lem317050 A lt2 s)). Qed.
Lemma lem317062 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term154 A lt2 s.
Proof. exact (@lem317061 A lt2 s). Qed.
Lemma lem317096 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem317097 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term151 A lt2 s) = (term157 A lt2 s).
Proof. exact (@lem317096 (term152 A lt2 s)). Qed.
Lemma lem317099 (t : Prop) : (term158 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem317100 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term157 A lt2 s) = (term138 A lt2 s).
Proof. exact (@lem317099 (term138 A lt2 s)). Qed.
Lemma lem317103 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term151 A lt2 s) = (term138 A lt2 s).
Proof. exact (TRANS (@lem317097 A lt2 s) (@lem317100 A lt2 s)). Qed.
Lemma lem317124 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term37 A lt2 s) = (term37 A lt2 s).
Proof. exact (eq_refl (term37 A lt2 s)). Qed.
Lemma lem317125 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term159 A lt2 s) = (term160 A lt2 s).
Proof. exact (MK_COMB (@lem317124 A lt2 s) (@lem317103 A lt2 s)). Qed.
Lemma lem317128 {A : Type'} (lt2 : type1402 A) : (term161 A lt2) = (term161 A lt2).
Proof. exact (eq_refl (term161 A lt2)). Qed.
Lemma lem317129 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term153 A lt2 s) = (term162 A lt2 s).
Proof. exact (MK_COMB (@lem317128 A lt2) (@lem317125 A lt2 s)). Qed.
Lemma lem317132 {A : Type'} (s : nat -> A) : (term163 A s) = (term164 A s).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem317129 A lt2 s)). Qed.
Lemma lem317133 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem317134 {A : Type'} (s : nat -> A) : (term165 A s) = (term166 A s).
Proof. exact (MK_COMB (@lem317133 A) (@lem317132 A s)). Qed.
Lemma lem317139 {A : Type'} : (term167 A) = (term168 A).
Proof. exact (fun_ext (fun s : nat -> A => @lem317134 A s)). Qed.
Lemma lem317140 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem317149 {A : Type'} : (term169 A) = (term170 A).
Proof. exact (MK_COMB (@lem317140 A) (@lem317139 A)). Qed.
Lemma lem317150 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term96 A lt2 s j) = (term96 A lt2 s j).
Proof. exact (eq_refl (term96 A lt2 s j)). Qed.
Lemma lem317151 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term97 A lt2 s) = (term97 A lt2 s).
Proof. exact (fun_ext (fun j : nat => @lem317150 A lt2 s j)). Qed.
Lemma lem317152 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem317153 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term35 A lt2 s) = (term35 A lt2 s).
Proof. exact (MK_COMB (@lem317152) (@lem317151 A lt2 s)). Qed.
Lemma lem317162 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (x : nat) : (term118 A y lt2 z s x) = (term118 A y lt2 z s x).
Proof. exact (eq_refl (term118 A y lt2 z s x)). Qed.
Lemma lem317163 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term120 A y lt2 s x) = (term120 A y lt2 s x).
Proof. exact (fun_ext (fun z : nat => @lem317162 A y lt2 z s x)). Qed.
Lemma lem317164 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem317165 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term122 A y lt2 s x) = (term122 A y lt2 s x).
Proof. exact (MK_COMB (@lem317164) (@lem317163 A y lt2 s x)). Qed.
Lemma lem317166 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term124 A lt2 s x) = (term124 A lt2 s x).
Proof. exact (fun_ext (fun y : nat => @lem317165 A y lt2 s x)). Qed.
Lemma lem317167 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem317168 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term126 A lt2 s x) = (term126 A lt2 s x).
Proof. exact (MK_COMB (@lem317167) (@lem317166 A lt2 s x)). Qed.
Lemma lem317169 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term128 A lt2 s) = (term128 A lt2 s).
Proof. exact (fun_ext (fun x : nat => @lem317168 A lt2 s x)). Qed.
Lemma lem317170 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem317171 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term130 A lt2 s) = (term130 A lt2 s).
Proof. exact (MK_COMB (@lem317170) (@lem317169 A lt2 s)). Qed.
Lemma lem317172 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem317173 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term132 A lt2 s) = (term132 A lt2 s).
Proof. exact (MK_COMB (@lem317172) (@lem317171 A lt2 s)). Qed.
Lemma lem317174 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term138 A lt2 s) = (term138 A lt2 s).
Proof. exact (MK_COMB (@lem317173 A lt2 s) (@lem317153 A lt2 s)). Qed.
Lemma lem317175 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term96 A lt2 s n) = (term96 A lt2 s n).
Proof. exact (eq_refl (term96 A lt2 s n)). Qed.
Lemma lem317176 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term97 A lt2 s) = (term97 A lt2 s).
Proof. exact (fun_ext (fun n : nat => @lem317175 A lt2 s n)). Qed.
Lemma lem317177 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem317178 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term35 A lt2 s) = (term35 A lt2 s).
Proof. exact (MK_COMB (@lem317177) (@lem317176 A lt2 s)). Qed.
Lemma lem317179 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem317180 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term37 A lt2 s) = (term37 A lt2 s).
Proof. exact (MK_COMB (@lem317179) (@lem317178 A lt2 s)). Qed.
Lemma lem317181 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term160 A lt2 s) = (term160 A lt2 s).
Proof. exact (MK_COMB (@lem317180 A lt2 s) (@lem317174 A lt2 s)). Qed.
Lemma lem317190 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) (z : A) : (term171 A y lt2 x z) = (term171 A y lt2 x z).
Proof. exact (eq_refl (term171 A y lt2 x z)). Qed.
Lemma lem317191 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) : (term172 A y lt2 x) = (term172 A y lt2 x).
Proof. exact (fun_ext (fun z : A => @lem317190 A y lt2 x z)). Qed.
Lemma lem317192 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem317193 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) : (term173 A y lt2 x) = (term173 A y lt2 x).
Proof. exact (MK_COMB (@lem317192 A) (@lem317191 A y lt2 x)). Qed.
Lemma lem317194 {A : Type'} (lt2 : type1402 A) (x : A) : (term174 A lt2 x) = (term174 A lt2 x).
Proof. exact (fun_ext (fun y : A => @lem317193 A y lt2 x)). Qed.
Lemma lem317195 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem317196 {A : Type'} (lt2 : type1402 A) (x : A) : (term175 A lt2 x) = (term175 A lt2 x).
Proof. exact (MK_COMB (@lem317195 A) (@lem317194 A lt2 x)). Qed.
Lemma lem317197 {A : Type'} (lt2 : type1402 A) : (term176 A lt2) = (term176 A lt2).
Proof. exact (fun_ext (fun x : A => @lem317196 A lt2 x)). Qed.
Lemma lem317198 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem317199 {A : Type'} (lt2 : type1402 A) : (term25 A lt2) = (term25 A lt2).
Proof. exact (MK_COMB (@lem317198 A) (@lem317197 A lt2)). Qed.
Lemma lem317200 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem317201 {A : Type'} (lt2 : type1402 A) : (term161 A lt2) = (term161 A lt2).
Proof. exact (MK_COMB (@lem317200) (@lem317199 A lt2)). Qed.
Lemma lem317202 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term162 A lt2 s) = (term162 A lt2 s).
Proof. exact (MK_COMB (@lem317201 A lt2) (@lem317181 A lt2 s)). Qed.
Lemma lem317203 {A : Type'} (s : nat -> A) : (term164 A s) = (term164 A s).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem317202 A lt2 s)). Qed.
Lemma lem317204 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem317205 {A : Type'} (s : nat -> A) : (term166 A s) = (term166 A s).
Proof. exact (MK_COMB (@lem317204 A) (@lem317203 A s)). Qed.
Lemma lem317206 {A : Type'} : (term168 A) = (term168 A).
Proof. exact (fun_ext (fun s : nat -> A => @lem317205 A s)). Qed.
Lemma lem317207 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem317208 {A : Type'} : (term170 A) = (term170 A).
Proof. exact (MK_COMB (@lem317207 A) (@lem317206 A)). Qed.
Lemma lem317285 {A : Type'} : (term169 A) = (term170 A).
Proof. exact (TRANS (@lem317149 A) (@lem317208 A)). Qed.
Lemma lem317286 {A : Type'} : (term170 A) = (term169 A).
Proof. exact (SYM (@lem317285 A)). Qed.
Lemma lem317287 {A : Type'} (lt2 : type1402 A) (h1 : term25 A lt2) : term25 A lt2.
Proof. exact (h1). Qed.
Lemma lem317288 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term35 A lt2 s) : term35 A lt2 s.
Proof. exact (h1). Qed.
Lemma lem317290 (p : Prop) : p = (term150 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem317291 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term138 A lt2 s) = (term151 A lt2 s).
Proof. exact (@lem317290 (term138 A lt2 s)). Qed.
Lemma lem317292 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term151 A lt2 s) = (term138 A lt2 s).
Proof. exact (SYM (@lem317291 A lt2 s)). Qed.
Lemma lem317293 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term152 A lt2 s) : term152 A lt2 s.
Proof. exact (h1). Qed.
Lemma lem317300 {A : Type'} (x : A) (lt2 : type1402 A) (y : A) (z : A) : (term177 A x lt2 y z) = (term178 A x lt2 y z).
Proof. exact (@lem17045 (lt2 x y) (lt2 y z)). Qed.
Lemma lem317301 {A : Type'} (lt2 : type1402 A) (x : A) (z : A) : (lt2 x z) = (lt2 x z).
Proof. exact (eq_refl (lt2 x z)). Qed.
Lemma lem317302 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem317303 {A : Type'} (x : A) (lt2 : type1402 A) (y : A) (z : A) : (term179 A x lt2 y z) = (term180 A x lt2 y z).
Proof. exact (MK_COMB (@lem317302) (@lem317300 A x lt2 y z)). Qed.
Lemma lem317304 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) (z : A) : (term181 A y lt2 x z) = (term182 A y lt2 x z).
Proof. exact (MK_COMB (@lem317303 A x lt2 y z) (@lem317301 A lt2 x z)). Qed.
Lemma lem317305 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) (z : A) : (term171 A y lt2 x z) = (term181 A y lt2 x z).
Proof. exact (@lem17265 (term183 A x lt2 y z) (lt2 x z)). Qed.
Lemma lem317306 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) (z : A) : (term171 A y lt2 x z) = (term182 A y lt2 x z).
Proof. exact (TRANS (@lem317305 A y lt2 x z) (@lem317304 A y lt2 x z)). Qed.
Lemma lem317307 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) : (term172 A y lt2 x) = (term184 A y lt2 x).
Proof. exact (fun_ext (fun z : A => @lem317306 A y lt2 x z)). Qed.
Lemma lem317308 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem317309 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) : (term173 A y lt2 x) = (term185 A y lt2 x).
Proof. exact (MK_COMB (@lem317308 A) (@lem317307 A y lt2 x)). Qed.
Lemma lem317310 {A : Type'} (lt2 : type1402 A) (x : A) : (term174 A lt2 x) = (term186 A lt2 x).
Proof. exact (fun_ext (fun y : A => @lem317309 A y lt2 x)). Qed.
Lemma lem317311 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem317312 {A : Type'} (lt2 : type1402 A) (x : A) : (term175 A lt2 x) = (term187 A lt2 x).
Proof. exact (MK_COMB (@lem317311 A) (@lem317310 A lt2 x)). Qed.
Lemma lem317313 {A : Type'} (lt2 : type1402 A) : (term176 A lt2) = (term188 A lt2).
Proof. exact (fun_ext (fun x : A => @lem317312 A lt2 x)). Qed.
Lemma lem317314 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem317375 {A : Type'} (lt2 : type1402 A) : (term25 A lt2) = (term189 A lt2).
Proof. exact (MK_COMB (@lem317314 A) (@lem317313 A lt2)). Qed.
Lemma lem317376 {A : Type'} (lt2 : type1402 A) (h1 : term25 A lt2) : term189 A lt2.
Proof. exact (EQ_MP (@lem317375 A lt2) (@lem317287 A lt2 h1)). Qed.
Lemma lem317377 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term96 A lt2 s n) = (term96 A lt2 s n).
Proof. exact (eq_refl (term96 A lt2 s n)). Qed.
Lemma lem317378 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term97 A lt2 s) = (term97 A lt2 s).
Proof. exact (fun_ext (fun n : nat => @lem317377 A lt2 s n)). Qed.
Lemma lem317379 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem317388 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term35 A lt2 s) = (term35 A lt2 s).
Proof. exact (MK_COMB (@lem317379) (@lem317378 A lt2 s)). Qed.
Lemma lem317389 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term35 A lt2 s) : term35 A lt2 s.
Proof. exact (EQ_MP (@lem317388 A lt2 s) (@lem317288 A lt2 s h1)). Qed.
Lemma lem317400 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (x : nat) : (term190 A y lt2 z s x) = (term191 A y lt2 z s x).
Proof. exact (@lem17362 (term114 A x lt2 z s y) (term89 A lt2 z s x)). Qed.
Lemma lem317401 (P : nat -> Prop) : (term192 P) = (term193 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem317402 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term194 A y lt2 s x) = (term195 A y lt2 s x).
Proof. exact (@lem317401 (term120 A y lt2 s x)). Qed.
Lemma lem317403 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (x : nat) : (term196 A y lt2 s x z) = (term118 A y lt2 z s x).
Proof. exact (eq_refl (term196 A y lt2 s x z)). Qed.
Lemma lem317404 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem317405 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (x : nat) : (term197 A y lt2 s x z) = (term190 A y lt2 z s x).
Proof. exact (MK_COMB (@lem317404) (@lem317403 A y lt2 z s x)). Qed.
Lemma lem317406 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (x : nat) : (term197 A y lt2 s x z) = (term191 A y lt2 z s x).
Proof. exact (TRANS (@lem317405 A y lt2 z s x) (@lem317400 A y lt2 z s x)). Qed.
Lemma lem317407 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term198 A y lt2 s x) = (term199 A y lt2 s x).
Proof. exact (fun_ext (fun z : nat => @lem317406 A y lt2 z s x)). Qed.
Lemma lem317408 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem317409 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term195 A y lt2 s x) = (term200 A y lt2 s x).
Proof. exact (MK_COMB (@lem317408) (@lem317407 A y lt2 s x)). Qed.
Lemma lem317410 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term194 A y lt2 s x) = (term200 A y lt2 s x).
Proof. exact (TRANS (@lem317402 A y lt2 s x) (@lem317409 A y lt2 s x)). Qed.
Lemma lem317411 (P : nat -> Prop) : (term192 P) = (term193 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem317412 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term201 A lt2 s x) = (term202 A lt2 s x).
Proof. exact (@lem317411 (term124 A lt2 s x)). Qed.
Lemma lem317413 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term203 A lt2 s x y) = (term122 A y lt2 s x).
Proof. exact (eq_refl (term203 A lt2 s x y)). Qed.
Lemma lem317414 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem317415 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term204 A lt2 s x y) = (term194 A y lt2 s x).
Proof. exact (MK_COMB (@lem317414) (@lem317413 A y lt2 s x)). Qed.
Lemma lem317416 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term204 A lt2 s x y) = (term200 A y lt2 s x).
Proof. exact (TRANS (@lem317415 A y lt2 s x) (@lem317410 A y lt2 s x)). Qed.
Lemma lem317417 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term205 A lt2 s x) = (term206 A lt2 s x).
Proof. exact (fun_ext (fun y : nat => @lem317416 A y lt2 s x)). Qed.
Lemma lem317418 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem317419 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term202 A lt2 s x) = (term207 A lt2 s x).
Proof. exact (MK_COMB (@lem317418) (@lem317417 A lt2 s x)). Qed.
Lemma lem317420 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term201 A lt2 s x) = (term207 A lt2 s x).
Proof. exact (TRANS (@lem317412 A lt2 s x) (@lem317419 A lt2 s x)). Qed.
Lemma lem317421 (P : nat -> Prop) : (term192 P) = (term193 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem317422 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term208 A lt2 s) = (term209 A lt2 s).
Proof. exact (@lem317421 (term128 A lt2 s)). Qed.
Lemma lem317423 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term210 A lt2 s x) = (term126 A lt2 s x).
Proof. exact (eq_refl (term210 A lt2 s x)). Qed.
Lemma lem317424 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem317425 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term211 A lt2 s x) = (term201 A lt2 s x).
Proof. exact (MK_COMB (@lem317424) (@lem317423 A lt2 s x)). Qed.
Lemma lem317426 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term211 A lt2 s x) = (term207 A lt2 s x).
Proof. exact (TRANS (@lem317425 A lt2 s x) (@lem317420 A lt2 s x)). Qed.
Lemma lem317427 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term212 A lt2 s) = (term213 A lt2 s).
Proof. exact (fun_ext (fun x : nat => @lem317426 A lt2 s x)). Qed.
Lemma lem317428 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem317429 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term209 A lt2 s) = (term214 A lt2 s).
Proof. exact (MK_COMB (@lem317428) (@lem317427 A lt2 s)). Qed.
Lemma lem317430 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term208 A lt2 s) = (term214 A lt2 s).
Proof. exact (TRANS (@lem317422 A lt2 s) (@lem317429 A lt2 s)). Qed.
Lemma lem317432 (P : nat -> Prop) : (term192 P) = (term193 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem317433 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term215 A lt2 s) = (term216 A lt2 s).
Proof. exact (@lem317432 (term97 A lt2 s)). Qed.
Lemma lem317434 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term217 A lt2 s j) = (term96 A lt2 s j).
Proof. exact (eq_refl (term217 A lt2 s j)). Qed.
Lemma lem317435 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem317437 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term218 A lt2 s j) = (term219 A lt2 s j).
Proof. exact (MK_COMB (@lem317435) (@lem317434 A lt2 s j)). Qed.
Lemma lem317438 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term220 A lt2 s) = (term221 A lt2 s).
Proof. exact (fun_ext (fun j : nat => @lem317437 A lt2 s j)). Qed.
Lemma lem317439 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem317440 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term216 A lt2 s) = (term222 A lt2 s).
Proof. exact (MK_COMB (@lem317439) (@lem317438 A lt2 s)). Qed.
Lemma lem317441 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term215 A lt2 s) = (term222 A lt2 s).
Proof. exact (TRANS (@lem317433 A lt2 s) (@lem317440 A lt2 s)). Qed.
Lemma lem317442 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem317443 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term223 A lt2 s) = (term224 A lt2 s).
Proof. exact (MK_COMB (@lem317442) (@lem317430 A lt2 s)). Qed.
Lemma lem317444 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term225 A lt2 s) = (term226 A lt2 s).
Proof. exact (MK_COMB (@lem317443 A lt2 s) (@lem317441 A lt2 s)). Qed.
Lemma lem317445 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term152 A lt2 s) = (term225 A lt2 s).
Proof. exact (@lem17045 (term130 A lt2 s) (term35 A lt2 s)). Qed.
Lemma lem317446 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term152 A lt2 s) = (term226 A lt2 s).
Proof. exact (TRANS (@lem317445 A lt2 s) (@lem317444 A lt2 s)). Qed.
Lemma lem317509 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term227 A P Q) = (term228 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem317510 (P : nat -> Prop) (Q : nat -> Prop) : (term229 P Q) = (term230 P Q).
Proof. exact (@lem317509 nat P Q). Qed.
Lemma lem317511 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term231 A lt2 s) = (term232 A lt2 s).
Proof. exact (@lem317510 (term213 A lt2 s) (term221 A lt2 s)). Qed.
Lemma lem317512 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term233 A lt2 s j) = (term207 A lt2 s j).
Proof. exact (eq_refl (term233 A lt2 s j)). Qed.
Lemma lem317513 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term234 A lt2 s) = (term213 A lt2 s).
Proof. exact (fun_ext (fun j : nat => @lem317512 A lt2 s j)). Qed.
Lemma lem317514 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem317515 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term235 A lt2 s) = (term214 A lt2 s).
Proof. exact (MK_COMB (@lem317514) (@lem317513 A lt2 s)). Qed.
Lemma lem317516 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem317517 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term236 A lt2 s) = (term224 A lt2 s).
Proof. exact (MK_COMB (@lem317516) (@lem317515 A lt2 s)). Qed.
Lemma lem317518 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term237 A lt2 s j) = (term219 A lt2 s j).
Proof. exact (eq_refl (term237 A lt2 s j)). Qed.
Lemma lem317519 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term238 A lt2 s) = (term221 A lt2 s).
Proof. exact (fun_ext (fun j : nat => @lem317518 A lt2 s j)). Qed.
Lemma lem317520 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem317521 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term239 A lt2 s) = (term222 A lt2 s).
Proof. exact (MK_COMB (@lem317520) (@lem317519 A lt2 s)). Qed.
Lemma lem317522 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term231 A lt2 s) = (term226 A lt2 s).
Proof. exact (MK_COMB (@lem317517 A lt2 s) (@lem317521 A lt2 s)). Qed.
Lemma lem317523 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem317524 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term240 A lt2 s) = (term241 A lt2 s).
Proof. exact (MK_COMB (@lem317523) (@lem317522 A lt2 s)). Qed.
Lemma lem317525 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term233 A lt2 s j) = (term207 A lt2 s j).
Proof. exact (eq_refl (term233 A lt2 s j)). Qed.
Lemma lem317526 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem317527 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term242 A lt2 s j) = (term243 A lt2 s j).
Proof. exact (MK_COMB (@lem317526) (@lem317525 A lt2 s j)). Qed.
Lemma lem317528 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term237 A lt2 s j) = (term219 A lt2 s j).
Proof. exact (eq_refl (term237 A lt2 s j)). Qed.
Lemma lem317529 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term244 A lt2 s j) = (term245 A lt2 s j).
Proof. exact (MK_COMB (@lem317527 A lt2 s j) (@lem317528 A lt2 s j)). Qed.
Lemma lem317530 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term246 A lt2 s) = (term247 A lt2 s).
Proof. exact (fun_ext (fun j : nat => @lem317529 A lt2 s j)). Qed.
Lemma lem317531 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem317532 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term232 A lt2 s) = (term248 A lt2 s).
Proof. exact (MK_COMB (@lem317531) (@lem317530 A lt2 s)). Qed.
Lemma lem317533 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : ((term231 A lt2 s) = (term232 A lt2 s)) = ((term226 A lt2 s) = (term248 A lt2 s)).
Proof. exact (MK_COMB (@lem317524 A lt2 s) (@lem317532 A lt2 s)). Qed.
Lemma lem317534 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term226 A lt2 s) = (term248 A lt2 s).
Proof. exact (EQ_MP (@lem317533 A lt2 s) (@lem317511 A lt2 s)). Qed.
Lemma lem317537 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term249 A lt2 s) = (term249 A lt2 s).
Proof. exact (eq_refl (term249 A lt2 s)). Qed.
Lemma lem317538 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term249 A lt2 s) = ((term226 A lt2 s) = (term248 A lt2 s)).
Proof. exact (eq_refl (term249 A lt2 s)). Qed.
Lemma lem317539 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term250 A lt2 s) = (term250 A lt2 s).
Proof. exact (eq_refl (term250 A lt2 s)). Qed.
Lemma lem317540 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : ((term249 A lt2 s) = (term249 A lt2 s)) = ((term249 A lt2 s) = ((term226 A lt2 s) = (term248 A lt2 s))).
Proof. exact (MK_COMB (@lem317539 A lt2 s) (@lem317538 A lt2 s)). Qed.
Lemma lem317541 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term249 A lt2 s) = ((term226 A lt2 s) = (term248 A lt2 s)).
Proof. exact (eq_refl (term249 A lt2 s)). Qed.
Lemma lem317542 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem317543 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term250 A lt2 s) = (term251 A lt2 s).
Proof. exact (MK_COMB (@lem317542) (@lem317541 A lt2 s)). Qed.
Lemma lem317544 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : ((term226 A lt2 s) = (term248 A lt2 s)) = ((term226 A lt2 s) = (term248 A lt2 s)).
Proof. exact (eq_refl ((term226 A lt2 s) = (term248 A lt2 s))). Qed.
Lemma lem317545 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : ((term249 A lt2 s) = ((term226 A lt2 s) = (term248 A lt2 s))) = (((term226 A lt2 s) = (term248 A lt2 s)) = ((term226 A lt2 s) = (term248 A lt2 s))).
Proof. exact (MK_COMB (@lem317543 A lt2 s) (@lem317544 A lt2 s)). Qed.
Lemma lem317546 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : ((term249 A lt2 s) = (term249 A lt2 s)) = (((term226 A lt2 s) = (term248 A lt2 s)) = ((term226 A lt2 s) = (term248 A lt2 s))).
Proof. exact (TRANS (@lem317540 A lt2 s) (@lem317545 A lt2 s)). Qed.
Lemma lem317547 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : ((term226 A lt2 s) = (term248 A lt2 s)) = ((term226 A lt2 s) = (term248 A lt2 s)).
Proof. exact (EQ_MP (@lem317546 A lt2 s) (@lem317537 A lt2 s)). Qed.
Lemma lem317548 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term226 A lt2 s) = (term248 A lt2 s).
Proof. exact (EQ_MP (@lem317547 A lt2 s) (@lem317534 A lt2 s)). Qed.
Lemma lem317550 {A : Type'} (P : A -> Prop) (Q : Prop) : (term252 A P Q) = (term253 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem317551 (P : nat -> Prop) (Q : Prop) : (term254 P Q) = (term255 P Q).
Proof. exact (@lem317550 nat P Q). Qed.
Lemma lem317552 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term256 A lt2 s j) = (term257 A lt2 s j).
Proof. exact (@lem317551 (term206 A lt2 s j) (term219 A lt2 s j)). Qed.
Lemma lem317553 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term258 A lt2 s j y) = (term200 A y lt2 s j).
Proof. exact (eq_refl (term258 A lt2 s j y)). Qed.
Lemma lem317554 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term259 A lt2 s j) = (term206 A lt2 s j).
Proof. exact (fun_ext (fun y : nat => @lem317553 A y lt2 s j)). Qed.
Lemma lem317555 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem317556 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term260 A lt2 s j) = (term207 A lt2 s j).
Proof. exact (MK_COMB (@lem317555) (@lem317554 A lt2 s j)). Qed.
Lemma lem317557 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem317558 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term261 A lt2 s j) = (term243 A lt2 s j).
Proof. exact (MK_COMB (@lem317557) (@lem317556 A lt2 s j)). Qed.
Lemma lem317559 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term219 A lt2 s j) = (term219 A lt2 s j).
Proof. exact (eq_refl (term219 A lt2 s j)). Qed.
Lemma lem317560 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term256 A lt2 s j) = (term245 A lt2 s j).
Proof. exact (MK_COMB (@lem317558 A lt2 s j) (@lem317559 A lt2 s j)). Qed.
Lemma lem317561 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem317562 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term262 A lt2 s j) = (term263 A lt2 s j).
Proof. exact (MK_COMB (@lem317561) (@lem317560 A lt2 s j)). Qed.
Lemma lem317563 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term258 A lt2 s j y) = (term200 A y lt2 s j).
Proof. exact (eq_refl (term258 A lt2 s j y)). Qed.
Lemma lem317564 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem317565 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term264 A lt2 s j y) = (term265 A y lt2 s j).
Proof. exact (MK_COMB (@lem317564) (@lem317563 A y lt2 s j)). Qed.
Lemma lem317566 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term219 A lt2 s j) = (term219 A lt2 s j).
Proof. exact (eq_refl (term219 A lt2 s j)). Qed.
Lemma lem317567 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term266 A y lt2 s j) = (term267 A y lt2 s j).
Proof. exact (MK_COMB (@lem317565 A y lt2 s j) (@lem317566 A lt2 s j)). Qed.
Lemma lem317568 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term268 A lt2 s j) = (term269 A lt2 s j).
Proof. exact (fun_ext (fun y : nat => @lem317567 A y lt2 s j)). Qed.
Lemma lem317569 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem317570 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term257 A lt2 s j) = (term270 A lt2 s j).
Proof. exact (MK_COMB (@lem317569) (@lem317568 A lt2 s j)). Qed.
Lemma lem317571 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) : ((term256 A lt2 s j) = (term257 A lt2 s j)) = ((term245 A lt2 s j) = (term270 A lt2 s j)).
Proof. exact (MK_COMB (@lem317562 A lt2 s j) (@lem317570 A lt2 s j)). Qed.
Lemma lem317572 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term245 A lt2 s j) = (term270 A lt2 s j).
Proof. exact (EQ_MP (@lem317571 A lt2 s j) (@lem317552 A lt2 s j)). Qed.
Lemma lem317574 {A : Type'} (P : A -> Prop) (Q : Prop) : (term252 A P Q) = (term253 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem317575 (P : nat -> Prop) (Q : Prop) : (term254 P Q) = (term255 P Q).
Proof. exact (@lem317574 nat P Q). Qed.
Lemma lem317576 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term271 A y lt2 s j) = (term272 A y lt2 s j).
Proof. exact (@lem317575 (term199 A y lt2 s j) (term219 A lt2 s j)). Qed.
Lemma lem317577 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (j : nat) : (term273 A y lt2 s j z) = (term191 A y lt2 z s j).
Proof. exact (eq_refl (term273 A y lt2 s j z)). Qed.
Lemma lem317578 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term274 A y lt2 s j) = (term199 A y lt2 s j).
Proof. exact (fun_ext (fun z : nat => @lem317577 A y lt2 z s j)). Qed.
Lemma lem317579 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem317580 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term275 A y lt2 s j) = (term200 A y lt2 s j).
Proof. exact (MK_COMB (@lem317579) (@lem317578 A y lt2 s j)). Qed.
Lemma lem317581 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem317582 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term276 A y lt2 s j) = (term265 A y lt2 s j).
Proof. exact (MK_COMB (@lem317581) (@lem317580 A y lt2 s j)). Qed.
Lemma lem317583 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term219 A lt2 s j) = (term219 A lt2 s j).
Proof. exact (eq_refl (term219 A lt2 s j)). Qed.
Lemma lem317584 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term271 A y lt2 s j) = (term267 A y lt2 s j).
Proof. exact (MK_COMB (@lem317582 A y lt2 s j) (@lem317583 A lt2 s j)). Qed.
Lemma lem317585 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem317586 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term277 A y lt2 s j) = (term278 A y lt2 s j).
Proof. exact (MK_COMB (@lem317585) (@lem317584 A y lt2 s j)). Qed.
Lemma lem317587 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (j : nat) : (term273 A y lt2 s j z) = (term191 A y lt2 z s j).
Proof. exact (eq_refl (term273 A y lt2 s j z)). Qed.
Lemma lem317588 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem317589 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (j : nat) : (term279 A y lt2 s j z) = (term280 A y lt2 z s j).
Proof. exact (MK_COMB (@lem317588) (@lem317587 A y lt2 z s j)). Qed.
Lemma lem317590 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term219 A lt2 s j) = (term219 A lt2 s j).
Proof. exact (eq_refl (term219 A lt2 s j)). Qed.
Lemma lem317591 {A : Type'} (y : nat) (z : nat) (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term281 A y z lt2 s j) = (term282 A y z lt2 s j).
Proof. exact (MK_COMB (@lem317589 A y lt2 z s j) (@lem317590 A lt2 s j)). Qed.
Lemma lem317592 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term283 A y lt2 s j) = (term284 A y lt2 s j).
Proof. exact (fun_ext (fun z : nat => @lem317591 A y z lt2 s j)). Qed.
Lemma lem317593 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem317594 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term272 A y lt2 s j) = (term285 A y lt2 s j).
Proof. exact (MK_COMB (@lem317593) (@lem317592 A y lt2 s j)). Qed.
Lemma lem317595 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (j : nat) : ((term271 A y lt2 s j) = (term272 A y lt2 s j)) = ((term267 A y lt2 s j) = (term285 A y lt2 s j)).
Proof. exact (MK_COMB (@lem317586 A y lt2 s j) (@lem317594 A y lt2 s j)). Qed.
Lemma lem317596 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term267 A y lt2 s j) = (term285 A y lt2 s j).
Proof. exact (EQ_MP (@lem317595 A y lt2 s j) (@lem317576 A y lt2 s j)). Qed.
Lemma lem317597 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term269 A lt2 s j) = (term286 A lt2 s j).
Proof. exact (fun_ext (fun y : nat => @lem317596 A y lt2 s j)). Qed.
Lemma lem317598 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem317599 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term270 A lt2 s j) = (term287 A lt2 s j).
Proof. exact (MK_COMB (@lem317598) (@lem317597 A lt2 s j)). Qed.
Lemma lem317600 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term245 A lt2 s j) = (term287 A lt2 s j).
Proof. exact (TRANS (@lem317572 A lt2 s j) (@lem317599 A lt2 s j)). Qed.
Lemma lem317601 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term247 A lt2 s) = (term288 A lt2 s).
Proof. exact (fun_ext (fun j : nat => @lem317600 A lt2 s j)). Qed.
Lemma lem317602 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem317603 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term248 A lt2 s) = (term289 A lt2 s).
Proof. exact (MK_COMB (@lem317602) (@lem317601 A lt2 s)). Qed.
Lemma lem317605 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term226 A lt2 s) = (term289 A lt2 s).
Proof. exact (TRANS (@lem317548 A lt2 s) (@lem317603 A lt2 s)). Qed.
Lemma lem317606 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term152 A lt2 s) = (term289 A lt2 s).
Proof. exact (TRANS (@lem317446 A lt2 s) (@lem317605 A lt2 s)). Qed.
Lemma lem317607 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term152 A lt2 s) : term289 A lt2 s.
Proof. exact (EQ_MP (@lem317606 A lt2 s) (@lem317293 A lt2 s h1)). Qed.
Lemma lem317608 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) (h1 : term287 A lt2 s j) : term287 A lt2 s j.
Proof. exact (h1). Qed.
Lemma lem317609 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (j : nat) (h1 : term285 A y lt2 s j) : term285 A y lt2 s j.
Proof. exact (h1). Qed.
Lemma lem317635 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) (z : A) : (term182 A y lt2 x z) = (term182 A y lt2 x z).
Proof. exact (eq_refl (term182 A y lt2 x z)). Qed.
Lemma lem317636 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) : (term184 A y lt2 x) = (term184 A y lt2 x).
Proof. exact (fun_ext (fun z : A => @lem317635 A y lt2 x z)). Qed.
Lemma lem317637 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem317638 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) : (term185 A y lt2 x) = (term185 A y lt2 x).
Proof. exact (MK_COMB (@lem317637 A) (@lem317636 A y lt2 x)). Qed.
Lemma lem317639 {A : Type'} (lt2 : type1402 A) (x : A) : (term186 A lt2 x) = (term186 A lt2 x).
Proof. exact (fun_ext (fun y : A => @lem317638 A y lt2 x)). Qed.
Lemma lem317640 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem317641 {A : Type'} (lt2 : type1402 A) (x : A) : (term187 A lt2 x) = (term187 A lt2 x).
Proof. exact (MK_COMB (@lem317640 A) (@lem317639 A lt2 x)). Qed.
Lemma lem317642 {A : Type'} (lt2 : type1402 A) : (term188 A lt2) = (term188 A lt2).
Proof. exact (fun_ext (fun x : A => @lem317641 A lt2 x)). Qed.
Lemma lem317643 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem317644 {A : Type'} (lt2 : type1402 A) : (term189 A lt2) = (term189 A lt2).
Proof. exact (MK_COMB (@lem317643 A) (@lem317642 A lt2)). Qed.
Lemma lem317645 {A : Type'} (lt2 : type1402 A) (h1 : term25 A lt2) : term189 A lt2.
Proof. exact (EQ_MP (@lem317644 A lt2) (@lem317376 A lt2 h1)). Qed.
Lemma lem317656 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term96 A lt2 s n) = (term96 A lt2 s n).
Proof. exact (eq_refl (term96 A lt2 s n)). Qed.
Lemma lem317657 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term97 A lt2 s) = (term97 A lt2 s).
Proof. exact (fun_ext (fun n : nat => @lem317656 A lt2 s n)). Qed.
Lemma lem317658 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem317659 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term35 A lt2 s) = (term35 A lt2 s).
Proof. exact (MK_COMB (@lem317658) (@lem317657 A lt2 s)). Qed.
Lemma lem317660 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term35 A lt2 s) : term35 A lt2 s.
Proof. exact (EQ_MP (@lem317659 A lt2 s) (@lem317389 A lt2 s h1)). Qed.
Lemma lem317712 {A : Type'} (y : nat) (z : nat) (lt2 : type1402 A) (s : nat -> A) (j : nat) (h1 : term282 A y z lt2 s j) : term282 A y z lt2 s j.
Proof. exact (h1). Qed.
Lemma lem317713 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (j : nat) (h1 : term191 A y lt2 z s j) : term191 A y lt2 z s j.
Proof. exact (h1). Qed.
Lemma lem317716 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (j : nat) (h1 : term191 A y lt2 z s j) : term114 A j lt2 z s y.
Proof. exact (proj1 (@lem317713 A y lt2 z s j h1)). Qed.
Lemma lem317732 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) (z : A) : (term182 A y lt2 x z) = (term182 A y lt2 x z).
Proof. exact (eq_refl (term182 A y lt2 x z)). Qed.
Lemma lem317733 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) : (term184 A y lt2 x) = (term184 A y lt2 x).
Proof. exact (fun_ext (fun z : A => @lem317732 A y lt2 x z)). Qed.
Lemma lem317734 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem317735 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) : (term185 A y lt2 x) = (term185 A y lt2 x).
Proof. exact (MK_COMB (@lem317734 A) (@lem317733 A y lt2 x)). Qed.
Lemma lem317736 {A : Type'} (lt2 : type1402 A) (x : A) : (term186 A lt2 x) = (term186 A lt2 x).
Proof. exact (fun_ext (fun y : A => @lem317735 A y lt2 x)). Qed.
Lemma lem317737 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem317738 {A : Type'} (lt2 : type1402 A) (x : A) : (term187 A lt2 x) = (term187 A lt2 x).
Proof. exact (MK_COMB (@lem317737 A) (@lem317736 A lt2 x)). Qed.
Lemma lem317739 {A : Type'} (lt2 : type1402 A) : (term188 A lt2) = (term188 A lt2).
Proof. exact (fun_ext (fun x : A => @lem317738 A lt2 x)). Qed.
Lemma lem317740 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem317742 {A : Type'} (lt2 : type1402 A) : (term189 A lt2) = (term189 A lt2).
Proof. exact (MK_COMB (@lem317740 A) (@lem317739 A lt2)). Qed.
Lemma lem317743 {A : Type'} (lt2 : type1402 A) (h1 : term25 A lt2) : term189 A lt2.
Proof. exact (EQ_MP (@lem317742 A lt2) (@lem317645 A lt2 h1)). Qed.
Lemma lem317789 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term96 A lt2 s n) = (term96 A lt2 s n).
Proof. exact (eq_refl (term96 A lt2 s n)). Qed.
Lemma lem317790 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term97 A lt2 s) = (term97 A lt2 s).
Proof. exact (fun_ext (fun n : nat => @lem317789 A lt2 s n)). Qed.
Lemma lem317791 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem317793 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term35 A lt2 s) = (term35 A lt2 s).
Proof. exact (MK_COMB (@lem317791) (@lem317790 A lt2 s)). Qed.
Lemma lem317794 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term35 A lt2 s) : term35 A lt2 s.
Proof. exact (EQ_MP (@lem317793 A lt2 s) (@lem317660 A lt2 s h1)). Qed.
Lemma lem317798 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) (h1 : term219 A lt2 s j) : term219 A lt2 s j.
Proof. exact (h1). Qed.
Lemma lem317799 {A : Type'} (_6991 : A) (lt2 : type1402 A) (h1 : term25 A lt2) : term290 A lt2 _6991.
Proof. exact (@lem317743 A lt2 h1 _6991). Qed.
Lemma lem317800 {A : Type'} (lt2 : type1402 A) (_6991 : A) : (term290 A lt2 _6991) = (term187 A lt2 _6991).
Proof. exact (eq_refl (term290 A lt2 _6991)). Qed.
Lemma lem317801 {A : Type'} (_6991 : A) (lt2 : type1402 A) (h1 : term25 A lt2) : term187 A lt2 _6991.
Proof. exact (EQ_MP (@lem317800 A lt2 _6991) (@lem317799 A _6991 lt2 h1)). Qed.
Lemma lem317802 {A : Type'} (_6991 : A) (_6992 : A) (lt2 : type1402 A) (h1 : term25 A lt2) : term291 A lt2 _6991 _6992.
Proof. exact (@lem317801 A _6991 lt2 h1 _6992). Qed.
Lemma lem317803 {A : Type'} (_6992 : A) (lt2 : type1402 A) (_6991 : A) : (term291 A lt2 _6991 _6992) = (term185 A _6992 lt2 _6991).
Proof. exact (eq_refl (term291 A lt2 _6991 _6992)). Qed.
Lemma lem317804 {A : Type'} (_6992 : A) (_6991 : A) (lt2 : type1402 A) (h1 : term25 A lt2) : term185 A _6992 lt2 _6991.
Proof. exact (EQ_MP (@lem317803 A _6992 lt2 _6991) (@lem317802 A _6991 _6992 lt2 h1)). Qed.
Lemma lem317805 {A : Type'} (_6992 : A) (_6991 : A) (_6993 : A) (lt2 : type1402 A) (h1 : term25 A lt2) : term292 A _6992 lt2 _6991 _6993.
Proof. exact (@lem317804 A _6992 _6991 lt2 h1 _6993). Qed.
Lemma lem317806 {A : Type'} (_6992 : A) (lt2 : type1402 A) (_6991 : A) (_6993 : A) : (term292 A _6992 lt2 _6991 _6993) = (term182 A _6992 lt2 _6991 _6993).
Proof. exact (eq_refl (term292 A _6992 lt2 _6991 _6993)). Qed.
Lemma lem317807 {A : Type'} (_6992 : A) (_6991 : A) (_6993 : A) (lt2 : type1402 A) (h1 : term25 A lt2) : term182 A _6992 lt2 _6991 _6993.
Proof. exact (EQ_MP (@lem317806 A _6992 lt2 _6991 _6993) (@lem317805 A _6992 _6991 _6993 lt2 h1)). Qed.
Lemma lem317820 {A : Type'} (_6998 : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term35 A lt2 s) : term217 A lt2 s _6998.
Proof. exact (@lem317794 A lt2 s h1 _6998). Qed.
Lemma lem317821 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_6998 : nat) : (term217 A lt2 s _6998) = (term96 A lt2 s _6998).
Proof. exact (eq_refl (term217 A lt2 s _6998)). Qed.
Lemma lem317833 {A : Type'} (_6992 : A) (lt2 : type1402 A) (_6991 : A) (_6993 : A) : (term182 A _6992 lt2 _6991 _6993) = (term293 A _6992 lt2 _6991 _6993).
Proof. exact (@lem316647 (term294 A lt2 _6991 _6992) (term294 A lt2 _6992 _6993) (lt2 _6991 _6993)). Qed.
Lemma lem317834 {A : Type'} (_6992 : A) (_6991 : A) (_6993 : A) (lt2 : type1402 A) (h1 : term25 A lt2) : term293 A _6992 lt2 _6991 _6993.
Proof. exact (EQ_MP (@lem317833 A _6992 lt2 _6991 _6993) (@lem317807 A _6992 _6991 _6993 lt2 h1)). Qed.
Lemma lem317838 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (j : nat) (h1 : term191 A y lt2 z s j) : term295 A lt2 z s j.
Proof. exact (proj2 (@lem317713 A y lt2 z s j h1)). Qed.
Lemma lem317858 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) (h1 : term219 A lt2 s j) : term219 A lt2 s j.
Proof. exact (h1). Qed.
Lemma lem317860 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (j : nat) (h1 : term191 A y lt2 z s j) : term89 A lt2 z s y.
Proof. exact (proj2 (@lem317716 A y lt2 z s j h1)). Qed.
Lemma lem317861 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (j : nat) (h1 : term191 A y lt2 z s j) : term296 A lt2 z s y.
Proof. exact (fun h0 : term295 A lt2 z s y => @lem317860 A y lt2 z s j h1). Qed.
Lemma lem317863 (p : Prop) : (term297 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem317864 {A : Type'} (lt2 : type1402 A) (z : nat) (s : nat -> A) (y : nat) : (term296 A lt2 z s y) = (term89 A lt2 z s y).
Proof. exact (@lem317863 (term89 A lt2 z s y)). Qed.
Lemma lem317865 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (j : nat) (h1 : term191 A y lt2 z s j) : term89 A lt2 z s y.
Proof. exact (EQ_MP (@lem317864 A lt2 z s y) (@lem317861 A y lt2 z s j h1)). Qed.
Lemma lem317867 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (j : nat) (h1 : term191 A y lt2 z s j) : term89 A lt2 y s j.
Proof. exact (proj1 (@lem317716 A y lt2 z s j h1)). Qed.
Lemma lem317868 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (j : nat) (h1 : term191 A y lt2 z s j) : term296 A lt2 y s j.
Proof. exact (fun h0 : term295 A lt2 y s j => @lem317867 A y lt2 z s j h1). Qed.
Lemma lem317870 (p : Prop) : (term297 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem317871 {A : Type'} (lt2 : type1402 A) (y : nat) (s : nat -> A) (j : nat) : (term296 A lt2 y s j) = (term89 A lt2 y s j).
Proof. exact (@lem317870 (term89 A lt2 y s j)). Qed.
Lemma lem317872 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (j : nat) (h1 : term191 A y lt2 z s j) : term89 A lt2 y s j.
Proof. exact (EQ_MP (@lem317871 A lt2 y s j) (@lem317868 A y lt2 z s j h1)). Qed.
Lemma lem317888 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem317889 {A : Type'} (_6991 : A) (lt2 : type1402 A) (_6992 : A) (_6993 : A) : (term298 A _6992 lt2 _6991 _6993) = (term299 A _6991 lt2 _6992 _6993).
Proof. exact (@lem317888 (lt2 _6991 _6993) (term294 A lt2 _6992 _6993)). Qed.
Lemma lem317895 {A : Type'} (lt2 : type1402 A) (_6991 : A) (_6992 : A) : (term300 A lt2 _6991 _6992) = (term300 A lt2 _6991 _6992).
Proof. exact (eq_refl (term300 A lt2 _6991 _6992)). Qed.
Lemma lem317896 {A : Type'} (_6991 : A) (lt2 : type1402 A) (_6992 : A) (_6993 : A) : (term293 A _6992 lt2 _6991 _6993) = (term301 A _6991 lt2 _6992 _6993).
Proof. exact (MK_COMB (@lem317895 A lt2 _6991 _6992) (@lem317889 A _6991 lt2 _6992 _6993)). Qed.
Lemma lem317900 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem317901 {A : Type'} (_6991 : A) (lt2 : type1402 A) (_6992 : A) (_6993 : A) : (term301 A _6991 lt2 _6992 _6993) = (term302 A _6991 lt2 _6992 _6993).
Proof. exact (@lem317900 (lt2 _6991 _6993) (term294 A lt2 _6991 _6992) (term294 A lt2 _6992 _6993)). Qed.
Lemma lem317917 {A : Type'} (_6991 : A) (lt2 : type1402 A) (_6992 : A) (_6993 : A) : (term293 A _6992 lt2 _6991 _6993) = (term302 A _6991 lt2 _6992 _6993).
Proof. exact (TRANS (@lem317896 A _6991 lt2 _6992 _6993) (@lem317901 A _6991 lt2 _6992 _6993)). Qed.
Lemma lem317918 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem317919 {A : Type'} (_6991 : A) (lt2 : type1402 A) (_6992 : A) (_6993 : A) : (term303 A _6992 lt2 _6991 _6993) = (term304 A _6991 lt2 _6992 _6993).
Proof. exact (MK_COMB (@lem317918) (@lem317917 A _6991 lt2 _6992 _6993)). Qed.
Lemma lem317935 {A : Type'} (_6991 : A) (lt2 : type1402 A) (_6992 : A) (_6993 : A) : (term302 A _6991 lt2 _6992 _6993) = (term302 A _6991 lt2 _6992 _6993).
Proof. exact (eq_refl (term302 A _6991 lt2 _6992 _6993)). Qed.
Lemma lem317936 {A : Type'} (_6991 : A) (lt2 : type1402 A) (_6992 : A) (_6993 : A) : ((term293 A _6992 lt2 _6991 _6993) = (term302 A _6991 lt2 _6992 _6993)) = ((term302 A _6991 lt2 _6992 _6993) = (term302 A _6991 lt2 _6992 _6993)).
Proof. exact (MK_COMB (@lem317919 A _6991 lt2 _6992 _6993) (@lem317935 A _6991 lt2 _6992 _6993)). Qed.
Lemma lem317938 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem317939 (x : Prop) : (x = x) = True.
Proof. exact (@lem317938 Prop x). Qed.
Lemma lem317940 {A : Type'} (_6991 : A) (lt2 : type1402 A) (_6992 : A) (_6993 : A) : ((term302 A _6991 lt2 _6992 _6993) = (term302 A _6991 lt2 _6992 _6993)) = True.
Proof. exact (@lem317939 (term302 A _6991 lt2 _6992 _6993)). Qed.
Lemma lem317941 {A : Type'} (_6991 : A) (lt2 : type1402 A) (_6992 : A) (_6993 : A) : ((term293 A _6992 lt2 _6991 _6993) = (term302 A _6991 lt2 _6992 _6993)) = True.
Proof. exact (TRANS (@lem317936 A _6991 lt2 _6992 _6993) (@lem317940 A _6991 lt2 _6992 _6993)). Qed.
Lemma lem317942 {A : Type'} (_6991 : A) (lt2 : type1402 A) (_6992 : A) (_6993 : A) : True = ((term293 A _6992 lt2 _6991 _6993) = (term302 A _6991 lt2 _6992 _6993)).
Proof. exact (SYM (@lem317941 A _6991 lt2 _6992 _6993)). Qed.
Lemma lem317943 {A : Type'} (_6991 : A) (lt2 : type1402 A) (_6992 : A) (_6993 : A) : (term293 A _6992 lt2 _6991 _6993) = (term302 A _6991 lt2 _6992 _6993).
Proof. exact (EQ_MP (@lem317942 A _6991 lt2 _6992 _6993) (@lem0)). Qed.
Lemma lem317944 {A : Type'} (_6991 : A) (_6992 : A) (_6993 : A) (lt2 : type1402 A) (h1 : term25 A lt2) : term302 A _6991 lt2 _6992 _6993.
Proof. exact (EQ_MP (@lem317943 A _6991 lt2 _6992 _6993) (@lem317834 A _6992 _6991 _6993 lt2 h1)). Qed.
Lemma lem317946 (b : Prop) (a : Prop) : (a \/ b) = (term305 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem317947 {A : Type'} (_6992 : A) (lt2 : type1402 A) (_6991 : A) (_6993 : A) : (term302 A _6991 lt2 _6992 _6993) = (term306 A _6992 lt2 _6991 _6993).
Proof. exact (@lem317946 (term178 A _6991 lt2 _6992 _6993) (lt2 _6991 _6993)). Qed.
Lemma lem317949 (a : Prop) (b : Prop) : (term307 a b) = (term308 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem317950 {A : Type'} (_6991 : A) (lt2 : type1402 A) (_6992 : A) (_6993 : A) : (term309 A _6991 lt2 _6992 _6993) = (term310 A _6991 lt2 _6992 _6993).
Proof. exact (@lem317949 (term294 A lt2 _6991 _6992) (term294 A lt2 _6992 _6993)). Qed.
Lemma lem317952 (a : Prop) : (term158 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem317953 {A : Type'} (lt2 : type1402 A) (_6991 : A) (_6992 : A) : (term311 A lt2 _6991 _6992) = (lt2 _6991 _6992).
Proof. exact (@lem317952 (lt2 _6991 _6992)). Qed.
Lemma lem317954 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem317955 {A : Type'} (lt2 : type1402 A) (_6991 : A) (_6992 : A) : (term312 A lt2 _6991 _6992) = (term313 A lt2 _6991 _6992).
Proof. exact (MK_COMB (@lem317954) (@lem317953 A lt2 _6991 _6992)). Qed.
Lemma lem317957 (a : Prop) : (term158 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem317958 {A : Type'} (lt2 : type1402 A) (_6992 : A) (_6993 : A) : (term311 A lt2 _6992 _6993) = (lt2 _6992 _6993).
Proof. exact (@lem317957 (lt2 _6992 _6993)). Qed.
Lemma lem317959 {A : Type'} (_6991 : A) (lt2 : type1402 A) (_6992 : A) (_6993 : A) : (term310 A _6991 lt2 _6992 _6993) = (term183 A _6991 lt2 _6992 _6993).
Proof. exact (MK_COMB (@lem317955 A lt2 _6991 _6992) (@lem317958 A lt2 _6992 _6993)). Qed.
Lemma lem317960 {A : Type'} (_6991 : A) (lt2 : type1402 A) (_6992 : A) (_6993 : A) : (term309 A _6991 lt2 _6992 _6993) = (term183 A _6991 lt2 _6992 _6993).
Proof. exact (TRANS (@lem317950 A _6991 lt2 _6992 _6993) (@lem317959 A _6991 lt2 _6992 _6993)). Qed.
Lemma lem317961 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem317962 {A : Type'} (_6991 : A) (lt2 : type1402 A) (_6992 : A) (_6993 : A) : (term314 A _6991 lt2 _6992 _6993) = (term315 A _6991 lt2 _6992 _6993).
Proof. exact (MK_COMB (@lem317961) (@lem317960 A _6991 lt2 _6992 _6993)). Qed.
Lemma lem317963 {A : Type'} (lt2 : type1402 A) (_6991 : A) (_6993 : A) : (lt2 _6991 _6993) = (lt2 _6991 _6993).
Proof. exact (eq_refl (lt2 _6991 _6993)). Qed.
Lemma lem317964 {A : Type'} (_6992 : A) (lt2 : type1402 A) (_6991 : A) (_6993 : A) : (term306 A _6992 lt2 _6991 _6993) = (term171 A _6992 lt2 _6991 _6993).
Proof. exact (MK_COMB (@lem317962 A _6991 lt2 _6992 _6993) (@lem317963 A lt2 _6991 _6993)). Qed.
Lemma lem317965 {A : Type'} (_6992 : A) (lt2 : type1402 A) (_6991 : A) (_6993 : A) : (term302 A _6991 lt2 _6992 _6993) = (term171 A _6992 lt2 _6991 _6993).
Proof. exact (TRANS (@lem317947 A _6992 lt2 _6991 _6993) (@lem317964 A _6992 lt2 _6991 _6993)). Qed.
Lemma lem317967 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (j : nat) (h1 : term191 A y lt2 z s j) : term316 A z lt2 y s j.
Proof. exact (conj (@lem317865 A y lt2 z s j h1) (@lem317872 A y lt2 z s j h1)). Qed.
Lemma lem317969 {A : Type'} (_6992 : A) (_6991 : A) (_6993 : A) (lt2 : type1402 A) (h1 : term25 A lt2) : term171 A _6992 lt2 _6991 _6993.
Proof. exact (EQ_MP (@lem317965 A _6992 lt2 _6991 _6993) (@lem317944 A _6991 _6992 _6993 lt2 h1)). Qed.
Lemma lem317970 {A : Type'} (_6992 : A) (_6991 : A) (_6993 : A) (lt2 : type1402 A) (h1 : term25 A lt2) : term171 A _6992 lt2 _6991 _6993.
Proof. exact (@lem317969 A _6992 _6991 _6993 lt2 h1). Qed.
Lemma lem317971 {A : Type'} (y : nat) (z : nat) (s : nat -> A) (j : nat) (lt2 : type1402 A) (h1 : term25 A lt2) : term317 A y lt2 z s j.
Proof. exact (@lem317970 A (s y) (s z) (s j) lt2 h1). Qed.
Lemma lem317974 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (j : nat) (h1 : term25 A lt2) (h2 : term191 A y lt2 z s j) : term89 A lt2 z s j.
Proof. exact (@lem317971 A y z s j lt2 h1 (@lem317967 A y lt2 z s j h2)). Qed.
Lemma lem317975 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (j : nat) (h1 : term25 A lt2) (h2 : term191 A y lt2 z s j) : term296 A lt2 z s j.
Proof. exact (fun h0 : term295 A lt2 z s j => @lem317974 A y lt2 z s j h1 h2). Qed.
Lemma lem317977 (p : Prop) : (term297 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem317978 {A : Type'} (lt2 : type1402 A) (z : nat) (s : nat -> A) (j : nat) : (term296 A lt2 z s j) = (term89 A lt2 z s j).
Proof. exact (@lem317977 (term89 A lt2 z s j)). Qed.
Lemma lem317979 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (j : nat) (h1 : term25 A lt2) (h2 : term191 A y lt2 z s j) : term89 A lt2 z s j.
Proof. exact (EQ_MP (@lem317978 A lt2 z s j) (@lem317975 A y lt2 z s j h1 h2)). Qed.
Lemma lem317982 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem317984 {A : Type'} (lt2 : type1402 A) (z : nat) (s : nat -> A) (j : nat) : (term295 A lt2 z s j) = (term318 A lt2 z s j).
Proof. exact (@lem317982 (term89 A lt2 z s j)). Qed.
Lemma lem317987 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (j : nat) (h1 : term191 A y lt2 z s j) : term318 A lt2 z s j.
Proof. exact (EQ_MP (@lem317984 A lt2 z s j) (@lem317838 A y lt2 z s j h1)). Qed.
Lemma lem317990 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (j : nat) (h1 : term25 A lt2) (h2 : term191 A y lt2 z s j) : False.
Proof. exact (@lem317987 A y lt2 z s j h2 (@lem317979 A y lt2 z s j h1 h2)). Qed.
Lemma lem317991 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (j : nat) (h1 : term25 A lt2) (h2 : term191 A y lt2 z s j) : term319.
Proof. exact (fun h0 : ~ False => @lem317990 A y lt2 z s j h1 h2). Qed.
Lemma lem317993 (p : Prop) : (term297 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem317994 : term319 = False.
Proof. exact (@lem317993 False). Qed.
Lemma lem317995 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (j : nat) (h1 : term25 A lt2) (h2 : term191 A y lt2 z s j) : False.
Proof. exact (EQ_MP (@lem317994) (@lem317991 A y lt2 z s j h1 h2)). Qed.
Lemma lem317997 {A : Type'} (_6998 : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term35 A lt2 s) : term96 A lt2 s _6998.
Proof. exact (EQ_MP (@lem317821 A lt2 s _6998) (@lem317820 A _6998 lt2 s h1)). Qed.
Lemma lem317998 {A : Type'} (j : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term35 A lt2 s) : term96 A lt2 s j.
Proof. exact (@lem317997 A j lt2 s h1). Qed.
Lemma lem317999 {A : Type'} (j : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term35 A lt2 s) : term320 A lt2 s j.
Proof. exact (fun h0 : term219 A lt2 s j => @lem317998 A j lt2 s h1). Qed.
Lemma lem318001 (p : Prop) : (term297 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem318002 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term320 A lt2 s j) = (term96 A lt2 s j).
Proof. exact (@lem318001 (term96 A lt2 s j)). Qed.
Lemma lem318003 {A : Type'} (j : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term35 A lt2 s) : term96 A lt2 s j.
Proof. exact (EQ_MP (@lem318002 A lt2 s j) (@lem317999 A j lt2 s h1)). Qed.
Lemma lem318006 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem318008 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) : (term219 A lt2 s j) = (term321 A lt2 s j).
Proof. exact (@lem318006 (term96 A lt2 s j)). Qed.
Lemma lem318011 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) (h1 : term219 A lt2 s j) : term321 A lt2 s j.
Proof. exact (EQ_MP (@lem318008 A lt2 s j) (@lem317858 A lt2 s j h1)). Qed.
Lemma lem318014 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) (h1 : term35 A lt2 s) (h2 : term219 A lt2 s j) : False.
Proof. exact (@lem318011 A lt2 s j h2 (@lem318003 A j lt2 s h1)). Qed.
Lemma lem318015 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) (h1 : term35 A lt2 s) (h2 : term219 A lt2 s j) : term319.
Proof. exact (fun h0 : ~ False => @lem318014 A lt2 s j h1 h2). Qed.
Lemma lem318017 (p : Prop) : (term297 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem318018 : term319 = False.
Proof. exact (@lem318017 False). Qed.
Lemma lem318019 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) (h1 : term35 A lt2 s) (h2 : term219 A lt2 s j) : False.
Proof. exact (EQ_MP (@lem318018) (@lem318015 A lt2 s j h1 h2)). Qed.
Lemma lem318020 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) (h1 : term35 A lt2 s) (h2 : term219 A lt2 s j) : (term219 A lt2 s j) = False.
Proof. exact (prop_ext (fun h3 : term219 A lt2 s j => @lem318019 A lt2 s j h1 h2) (fun h3 : False => @lem317858 A lt2 s j h2)). Qed.
Lemma lem318021 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) (h1 : term35 A lt2 s) (h2 : term219 A lt2 s j) : False.
Proof. exact (EQ_MP (@lem318020 A lt2 s j h1 h2) (@lem317858 A lt2 s j h2)). Qed.
Lemma lem318022 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) (h1 : term35 A lt2 s) (h2 : term219 A lt2 s j) : (term219 A lt2 s j) = False.
Proof. exact (prop_ext (fun h3 : term219 A lt2 s j => @lem318021 A lt2 s j h1 h2) (fun h3 : False => @lem317798 A lt2 s j h2)). Qed.
Lemma lem318023 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) (h1 : term35 A lt2 s) (h2 : term219 A lt2 s j) : False.
Proof. exact (EQ_MP (@lem318022 A lt2 s j h1 h2) (@lem317798 A lt2 s j h2)). Qed.
Lemma lem318024 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) (h1 : term35 A lt2 s) (h2 : term219 A lt2 s j) : (term219 A lt2 s j) = False.
Proof. exact (prop_ext (fun h3 : term219 A lt2 s j => @lem318023 A lt2 s j h1 h2) (fun h3 : False => @lem317798 A lt2 s j h2)). Qed.
Lemma lem318025 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) (h1 : term35 A lt2 s) (h2 : term219 A lt2 s j) : False.
Proof. exact (EQ_MP (@lem318024 A lt2 s j h1 h2) (@lem317798 A lt2 s j h2)). Qed.
Lemma lem318026 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) (h1 : term35 A lt2 s) (h2 : term219 A lt2 s j) : (term35 A lt2 s) = False.
Proof. exact (prop_ext (fun h3 : term35 A lt2 s => @lem318025 A lt2 s j h1 h2) (fun h3 : False => @lem317794 A lt2 s h1)). Qed.
Lemma lem318027 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) (h1 : term35 A lt2 s) (h2 : term219 A lt2 s j) : False.
Proof. exact (EQ_MP (@lem318026 A lt2 s j h1 h2) (@lem317794 A lt2 s h1)). Qed.
Lemma lem318028 {A : Type'} (y : nat) (z : nat) (lt2 : type1402 A) (s : nat -> A) (j : nat) (h1 : term25 A lt2) (h2 : term35 A lt2 s) (h3 : term282 A y z lt2 s j) : False.
Proof. exact (or_elim (@lem317712 A y z lt2 s j h3) (fun h0 : term191 A y lt2 z s j => @lem317995 A y lt2 z s j h1 h0) (fun h0 : term219 A lt2 s j => @lem318027 A lt2 s j h2 h0)). Qed.
Lemma lem318029 {A : Type'} (y : nat) (z : nat) (lt2 : type1402 A) (s : nat -> A) (j : nat) (h1 : term25 A lt2) (h2 : term35 A lt2 s) (h3 : term282 A y z lt2 s j) : (term282 A y z lt2 s j) = False.
Proof. exact (prop_ext (fun h4 : term282 A y z lt2 s j => @lem318028 A y z lt2 s j h1 h2 h3) (fun h4 : False => @lem317712 A y z lt2 s j h3)). Qed.
Lemma lem318030 {A : Type'} (y : nat) (z : nat) (lt2 : type1402 A) (s : nat -> A) (j : nat) (h1 : term25 A lt2) (h2 : term35 A lt2 s) (h3 : term282 A y z lt2 s j) : False.
Proof. exact (EQ_MP (@lem318029 A y z lt2 s j h1 h2 h3) (@lem317712 A y z lt2 s j h3)). Qed.
Lemma lem318031 {A : Type'} (y : nat) (z : nat) (lt2 : type1402 A) (s : nat -> A) (j : nat) (h1 : term25 A lt2) (h2 : term35 A lt2 s) (h3 : term282 A y z lt2 s j) : (term35 A lt2 s) = False.
Proof. exact (prop_ext (fun h4 : term35 A lt2 s => @lem318030 A y z lt2 s j h1 h2 h3) (fun h4 : False => @lem317660 A lt2 s h2)). Qed.
Lemma lem318032 {A : Type'} (y : nat) (z : nat) (lt2 : type1402 A) (s : nat -> A) (j : nat) (h1 : term25 A lt2) (h2 : term35 A lt2 s) (h3 : term282 A y z lt2 s j) : False.
Proof. exact (EQ_MP (@lem318031 A y z lt2 s j h1 h2 h3) (@lem317660 A lt2 s h2)). Qed.
Lemma lem318033 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (j : nat) (h1 : term25 A lt2) (h2 : term35 A lt2 s) (h3 : term285 A y lt2 s j) : False.
Proof. exact (ex_elim (@lem317609 A y lt2 s j h3) (fun z : nat => fun h0 : term284 A y lt2 s j z => @lem318032 A y z lt2 s j h1 h2 h0)). Qed.
Lemma lem318034 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (j : nat) (h1 : term25 A lt2) (h2 : term35 A lt2 s) (h3 : term287 A lt2 s j) : False.
Proof. exact (ex_elim (@lem317608 A lt2 s j h3) (fun y : nat => fun h0 : term286 A lt2 s j y => @lem318033 A y lt2 s j h1 h2 h0)). Qed.
Lemma lem318035 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term25 A lt2) (h2 : term35 A lt2 s) (h3 : term152 A lt2 s) : False.
Proof. exact (ex_elim (@lem317607 A lt2 s h3) (fun j : nat => fun h0 : term288 A lt2 s j => @lem318034 A lt2 s j h1 h2 h0)). Qed.
Lemma lem318036 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term25 A lt2) (h2 : term35 A lt2 s) (h3 : term152 A lt2 s) : (term35 A lt2 s) = False.
Proof. exact (prop_ext (fun h4 : term35 A lt2 s => @lem318035 A lt2 s h1 h2 h3) (fun h4 : False => @lem317389 A lt2 s h2)). Qed.
Lemma lem318037 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term25 A lt2) (h2 : term35 A lt2 s) (h3 : term152 A lt2 s) : False.
Proof. exact (EQ_MP (@lem318036 A lt2 s h1 h2 h3) (@lem317389 A lt2 s h2)). Qed.
Lemma lem318038 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term25 A lt2) (h2 : term35 A lt2 s) (h3 : term152 A lt2 s) : (term152 A lt2 s) = False.
Proof. exact (prop_ext (fun h4 : term152 A lt2 s => @lem318037 A lt2 s h1 h2 h3) (fun h4 : False => @lem317293 A lt2 s h3)). Qed.
Lemma lem318039 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term25 A lt2) (h2 : term35 A lt2 s) (h3 : term152 A lt2 s) : False.
Proof. exact (EQ_MP (@lem318038 A lt2 s h1 h2 h3) (@lem317293 A lt2 s h3)). Qed.
Lemma lem318040 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term25 A lt2) (h2 : term35 A lt2 s) : term151 A lt2 s.
Proof. exact (fun h0 : term152 A lt2 s => @lem318039 A lt2 s h1 h2 h0). Qed.
Lemma lem318041 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term25 A lt2) (h2 : term35 A lt2 s) : term138 A lt2 s.
Proof. exact (EQ_MP (@lem317292 A lt2 s) (@lem318040 A lt2 s h1 h2)). Qed.
Lemma lem318042 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (h1 : term25 A lt2) : term160 A lt2 s.
Proof. exact (fun h0 : term35 A lt2 s => @lem318041 A lt2 s h1 h0). Qed.
Lemma lem318043 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term162 A lt2 s.
Proof. exact (fun h0 : term25 A lt2 => @lem318042 A s lt2 h0). Qed.
Lemma lem318048 {A : Type'} (s : nat -> A) : term166 A s.
Proof. exact (fun lt2 : type1402 A => @lem318043 A lt2 s). Qed.
Lemma lem318053 {A : Type'} : term170 A.
Proof. exact (fun s : nat -> A => @lem318048 A s). Qed.
Lemma lem318054 {A : Type'} : term169 A.
Proof. exact (EQ_MP (@lem317286 A) (@lem318053 A)). Qed.
Lemma lem318055 {A : Type'} (s : nat -> A) : term322 A s.
Proof. exact (@lem318054 A s). Qed.
Lemma lem318056 {A : Type'} (s : nat -> A) : (term322 A s) = (term165 A s).
Proof. exact (eq_refl (term322 A s)). Qed.
Lemma lem318057 {A : Type'} (s : nat -> A) : term165 A s.
Proof. exact (EQ_MP (@lem318056 A s) (@lem318055 A s)). Qed.
Lemma lem318058 {A : Type'} (s : nat -> A) (lt2 : type1402 A) : term323 A s lt2.
Proof. exact (@lem318057 A s lt2). Qed.
Lemma lem318059 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term323 A s lt2) = (term153 A lt2 s).
Proof. exact (eq_refl (term323 A s lt2)). Qed.
Lemma lem318060 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term153 A lt2 s.
Proof. exact (EQ_MP (@lem318059 A lt2 s) (@lem318058 A s lt2)). Qed.
Lemma lem318062 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term153 A lt2 s.
Proof. exact (@lem317062 A lt2 s (@lem318060 A lt2 s)). Qed.
Lemma lem318063 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (h1 : term25 A lt2) : term159 A lt2 s.
Proof. exact (@lem318062 A lt2 s (@lem316684 A lt2 h1)). Qed.
Lemma lem318064 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term25 A lt2) (h2 : term35 A lt2 s) : term151 A lt2 s.
Proof. exact (@lem318063 A s lt2 h1 (@lem316980 A lt2 s h2)). Qed.
Lemma lem318065 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term25 A lt2) (h2 : term35 A lt2 s) (h3 : term152 A lt2 s) : False.
Proof. exact (@lem318064 A lt2 s h1 h2 (@lem317046 A lt2 s h3)). Qed.
Lemma lem318066 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term25 A lt2) (h2 : term35 A lt2 s) (h3 : term152 A lt2 s) : (term152 A lt2 s) = False.
Proof. exact (prop_ext (fun h4 : term152 A lt2 s => @lem318065 A lt2 s h1 h2 h3) (fun h4 : False => @lem317046 A lt2 s h3)). Qed.
Lemma lem318067 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term25 A lt2) (h2 : term35 A lt2 s) (h3 : term152 A lt2 s) : False.
Proof. exact (EQ_MP (@lem318066 A lt2 s h1 h2 h3) (@lem317046 A lt2 s h3)). Qed.
Lemma lem318068 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term25 A lt2) (h2 : term35 A lt2 s) : term151 A lt2 s.
Proof. exact (fun h0 : term152 A lt2 s => @lem318067 A lt2 s h1 h2 h0). Qed.
Lemma lem318069 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term25 A lt2) (h2 : term35 A lt2 s) : term138 A lt2 s.
Proof. exact (EQ_MP (@lem317045 A lt2 s) (@lem318068 A lt2 s h1 h2)). Qed.
Lemma lem318070 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term25 A lt2) (h2 : term35 A lt2 s) : term39 A lt2 s.
Proof. exact (@lem317041 A lt2 s (@lem318069 A lt2 s h1 h2)). Qed.
Lemma lem318072 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (h1 : term25 A lt2) : term41 A lt2 s.
Proof. exact (fun h0 : term35 A lt2 s => @lem318070 A lt2 s h1 h0). Qed.
Lemma lem318077 {A : Type'} (lt2 : type1402 A) : term67 A lt2.
Proof. exact (fun s : nat -> A => @lem316979 A lt2 s). Qed.
Lemma lem318082 {A : Type'} (lt2 : type1402 A) (h1 : term25 A lt2) : term45 A lt2.
Proof. exact (fun s : nat -> A => @lem318072 A s lt2 h1). Qed.
Lemma lem318083 {A : Type'} (lt2 : type1402 A) : term73 A lt2.
Proof. exact (@lem316773 A lt2 (@lem318077 A lt2)). Qed.
Lemma lem318084 {A : Type'} (lt2 : type1402 A) (h1 : term25 A lt2) : term57 A lt2.
Proof. exact (@lem316746 A lt2 (@lem318082 A lt2 h1)). Qed.
Lemma lem318085 {A : Type'} (lt2 : type1402 A) (h1 : term25 A lt2) : term324 A lt2.
Proof. exact (conj (@lem318084 A lt2 h1) (@lem318083 A lt2)). Qed.
Lemma lem318086 {A : Type'} (lt2 : type1402 A) : (term324 A lt2) = ((term50 A lt2) = (term55 A lt2)).
Proof. exact (@lem32 (term50 A lt2) (term55 A lt2)). Qed.
Lemma lem318087 {A : Type'} (lt2 : type1402 A) (h1 : term25 A lt2) : (term50 A lt2) = (term55 A lt2).
Proof. exact (EQ_MP (@lem318086 A lt2) (@lem318085 A lt2 h1)). Qed.
Lemma lem318088 {A : Type'} (lt2 : type1402 A) (h1 : term25 A lt2) : (term26 A lt2) = (term29 A lt2).
Proof. exact (MK_COMB (@lem316719) (@lem318087 A lt2 h1)). Qed.
Lemma lem318089 {A : Type'} (lt2 : type1402 A) (h1 : term25 A lt2) : (@WF A lt2) = (term29 A lt2).
Proof. exact (EQ_MP (@lem316718 A lt2) (@lem318088 A lt2 h1)). Qed.
Lemma lem318090 {A : Type'} (lt2 : type1402 A) : term325 A lt2.
Proof. exact (fun h0 : term25 A lt2 => @lem318089 A lt2 h0). Qed.
Lemma lem318095 {A : Type'} : term326 A.
Proof. exact (fun lt2 : type1402 A => @lem318090 A lt2). Qed.
