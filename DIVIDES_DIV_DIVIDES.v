Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIVIDES_DIV_DIVIDES_term_abbrevs.
Require Import INT_DIVIDES_DIV_DIVIDES_spec.
Require Import INT_OF_NUM_DIV_spec.
Require Import INT_OF_NUM_EQ_spec.
Require Import INT_OF_NUM_MUL_spec.
Require Import num_divides_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem3112689 (m : nat) (n : nat) (h1 : (term0 m n) = (term1 m n)) : (term0 m n) = (term1 m n).
Proof. exact (h1). Qed.
Lemma lem3112690 (m : nat) (n : nat) (h1 : (term0 m n) = (term1 m n)) : (term1 m n) = (term0 m n).
Proof. exact (SYM (@lem3112689 m n h1)). Qed.
Lemma lem3112691 (m : nat) (n : nat) (h1 : (term1 m n) = (term0 m n)) : (term1 m n) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem3112692 (m : nat) (n : nat) (h1 : (term1 m n) = (term0 m n)) : (term0 m n) = (term1 m n).
Proof. exact (SYM (@lem3112691 m n h1)). Qed.
Lemma lem3112693 (m : nat) (n : nat) : ((term0 m n) = (term1 m n)) = ((term1 m n) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (term1 m n) => @lem3112690 m n h1) (fun h1 : (term1 m n) = (term0 m n) => @lem3112692 m n h1)). Qed.
Lemma lem3112694 (m : nat) : (term2 m) = (term3 m).
Proof. exact (fun_ext (fun n : nat => @lem3112693 m n)). Qed.
Lemma lem3112695 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112696 (m : nat) : (term4 m) = (term5 m).
Proof. exact (MK_COMB (@lem3112695) (@lem3112694 m)). Qed.
Lemma lem3112697 : term6 = term7.
Proof. exact (fun_ext (fun m : nat => @lem3112696 m)). Qed.
Lemma lem3112698 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112699 : term8 = term9.
Proof. exact (MK_COMB (@lem3112698) (@lem3112697)). Qed.
Lemma lem3112700 : term9.
Proof. exact (EQ_MP (@lem3112699) (@lem2307381)). Qed.
Lemma lem3112703 (m : nat) (n : nat) (h1 : (term10 m n) = (term11 m n)) : (term10 m n) = (term11 m n).
Proof. exact (h1). Qed.
Lemma lem3112704 (m : nat) (n : nat) (h1 : (term10 m n) = (term11 m n)) : (term11 m n) = (term10 m n).
Proof. exact (SYM (@lem3112703 m n h1)). Qed.
Lemma lem3112705 (m : nat) (n : nat) (h1 : (term11 m n) = (term10 m n)) : (term11 m n) = (term10 m n).
Proof. exact (h1). Qed.
Lemma lem3112706 (m : nat) (n : nat) (h1 : (term11 m n) = (term10 m n)) : (term10 m n) = (term11 m n).
Proof. exact (SYM (@lem3112705 m n h1)). Qed.
Lemma lem3112707 (m : nat) (n : nat) : ((term10 m n) = (term11 m n)) = ((term11 m n) = (term10 m n)).
Proof. exact (prop_ext (fun h1 : (term10 m n) = (term11 m n) => @lem3112704 m n h1) (fun h1 : (term11 m n) = (term10 m n) => @lem3112706 m n h1)). Qed.
Lemma lem3112708 (m : nat) : (term12 m) = (term13 m).
Proof. exact (fun_ext (fun n : nat => @lem3112707 m n)). Qed.
Lemma lem3112709 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112710 (m : nat) : (term14 m) = (term15 m).
Proof. exact (MK_COMB (@lem3112709) (@lem3112708 m)). Qed.
Lemma lem3112711 : term16 = term17.
Proof. exact (fun_ext (fun m : nat => @lem3112710 m)). Qed.
Lemma lem3112712 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112713 : term18 = term19.
Proof. exact (MK_COMB (@lem3112712) (@lem3112711)). Qed.
Lemma lem3112714 : term19.
Proof. exact (EQ_MP (@lem3112713) (@lem2538105)). Qed.
Lemma lem3112717 (m : nat) (n : nat) (h1 : ((int_of_num m) = (int_of_num n)) = (m = n)) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (h1). Qed.
Lemma lem3112718 (m : nat) (n : nat) (h1 : ((int_of_num m) = (int_of_num n)) = (m = n)) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (SYM (@lem3112717 m n h1)). Qed.
Lemma lem3112719 (m : nat) (n : nat) (h1 : (m = n) = ((int_of_num m) = (int_of_num n))) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (h1). Qed.
Lemma lem3112720 (m : nat) (n : nat) (h1 : (m = n) = ((int_of_num m) = (int_of_num n))) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (SYM (@lem3112719 m n h1)). Qed.
Lemma lem3112721 (m : nat) (n : nat) : (((int_of_num m) = (int_of_num n)) = (m = n)) = ((m = n) = ((int_of_num m) = (int_of_num n))).
Proof. exact (prop_ext (fun h1 : ((int_of_num m) = (int_of_num n)) = (m = n) => @lem3112718 m n h1) (fun h1 : (m = n) = ((int_of_num m) = (int_of_num n)) => @lem3112720 m n h1)). Qed.
Lemma lem3112722 (m : nat) : (term20 m) = (term21 m).
Proof. exact (fun_ext (fun n : nat => @lem3112721 m n)). Qed.
Lemma lem3112723 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112724 (m : nat) : (term22 m) = (term23 m).
Proof. exact (MK_COMB (@lem3112723) (@lem3112722 m)). Qed.
Lemma lem3112725 : term24 = term25.
Proof. exact (fun_ext (fun m : nat => @lem3112724 m)). Qed.
Lemma lem3112726 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112727 : term26 = term27.
Proof. exact (MK_COMB (@lem3112726) (@lem3112725)). Qed.
Lemma lem3112728 : term27.
Proof. exact (EQ_MP (@lem3112727) (@lem2307147)). Qed.
Lemma lem3112729 (n : int) : term28 n.
Proof. exact (@lem2737101 n). Qed.
Lemma lem3112730 (n : int) : (term28 n) = (term29 n).
Proof. exact (eq_refl (term28 n)). Qed.
Lemma lem3112731 (n : int) : term29 n.
Proof. exact (EQ_MP (@lem3112730 n) (@lem3112729 n)). Qed.
Lemma lem3112732 (n : int) (d : int) : term30 n d.
Proof. exact (@lem3112731 n d). Qed.
Lemma lem3112733 (n : int) (d : int) : (term30 n d) = (term31 n d).
Proof. exact (eq_refl (term30 n d)). Qed.
Lemma lem3112734 (n : int) (d : int) : term31 n d.
Proof. exact (EQ_MP (@lem3112733 n d) (@lem3112732 n d)). Qed.
Lemma lem3112735 (n : int) (d : int) (e : int) : term32 n d e.
Proof. exact (@lem3112734 n d e). Qed.
Lemma lem3112736 (n : int) (d : int) (e : int) : (term32 n d e) = (term33 n d e).
Proof. exact (eq_refl (term32 n d e)). Qed.
Lemma lem3112737 (n : int) (d : int) (e : int) : term33 n d e.
Proof. exact (EQ_MP (@lem3112736 n d e) (@lem3112735 n d e)). Qed.
Lemma lem3112738 (n : int) (d : int) (e : int) : (term33 n d e) = ((term33 n d e) = True).
Proof. exact (@lem7 (term33 n d e)). Qed.
Lemma lem3112740 (m : nat) : term34 m.
Proof. exact (@lem3112700 m). Qed.
Lemma lem3112741 (m : nat) : (term34 m) = (term5 m).
Proof. exact (eq_refl (term34 m)). Qed.
Lemma lem3112742 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem3112741 m) (@lem3112740 m)). Qed.
Lemma lem3112743 (m : nat) (n : nat) : term35 m n.
Proof. exact (@lem3112742 m n). Qed.
Lemma lem3112744 (m : nat) (n : nat) : (term35 m n) = ((term1 m n) = (term0 m n)).
Proof. exact (eq_refl (term35 m n)). Qed.
Lemma lem3112746 (a : nat) : term36 a.
Proof. exact (@lem2836659 a). Qed.
Lemma lem3112747 (a : nat) : (term36 a) = (term37 a).
Proof. exact (eq_refl (term36 a)). Qed.
Lemma lem3112748 (a : nat) : term37 a.
Proof. exact (EQ_MP (@lem3112747 a) (@lem3112746 a)). Qed.
Lemma lem3112749 (a : nat) (b : nat) : term38 a b.
Proof. exact (@lem3112748 a b). Qed.
Lemma lem3112750 (a : nat) (b : nat) : (term38 a b) = ((num_divides a b) = (term39 a b)).
Proof. exact (eq_refl (term38 a b)). Qed.
Lemma lem3112752 (m : nat) : term40 m.
Proof. exact (@lem3112714 m). Qed.
Lemma lem3112753 (m : nat) : (term40 m) = (term15 m).
Proof. exact (eq_refl (term40 m)). Qed.
Lemma lem3112754 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem3112753 m) (@lem3112752 m)). Qed.
Lemma lem3112755 (m : nat) (n : nat) : term41 m n.
Proof. exact (@lem3112754 m n). Qed.
Lemma lem3112756 (m : nat) (n : nat) : (term41 m n) = ((term11 m n) = (term10 m n)).
Proof. exact (eq_refl (term41 m n)). Qed.
Lemma lem3112758 (m : nat) : term42 m.
Proof. exact (@lem3112728 m). Qed.
Lemma lem3112759 (m : nat) : (term42 m) = (term23 m).
Proof. exact (eq_refl (term42 m)). Qed.
Lemma lem3112760 (m : nat) : term23 m.
Proof. exact (EQ_MP (@lem3112759 m) (@lem3112758 m)). Qed.
Lemma lem3112761 (m : nat) (n : nat) : term43 m n.
Proof. exact (@lem3112760 m n). Qed.
Lemma lem3112762 (m : nat) (n : nat) : (term43 m n) = ((m = n) = ((int_of_num m) = (int_of_num n))).
Proof. exact (eq_refl (term43 m n)). Qed.
Lemma lem3112781 (a : nat) (b : nat) : (num_divides a b) = (term39 a b).
Proof. exact (EQ_MP (@lem3112750 a b) (@lem3112749 a b)). Qed.
Lemma lem3112782 (d : nat) (n : nat) : (num_divides d n) = (term39 d n).
Proof. exact (@lem3112781 d n). Qed.
Lemma lem3112783 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3112784 (d : nat) (n : nat) : (term44 d n) = (term45 d n).
Proof. exact (MK_COMB (@lem3112783) (@lem3112782 d n)). Qed.
Lemma lem3112792 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem3112762 m n) (@lem3112761 m n)). Qed.
Lemma lem3112793 (n : nat) : (n = (NUMERAL 0)) = ((int_of_num n) = term46).
Proof. exact (@lem3112792 n (NUMERAL 0)). Qed.
Lemma lem3112798 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3112799 (n : nat) : (term47 n) = (term48 n).
Proof. exact (MK_COMB (@lem3112798) (@lem3112793 n)). Qed.
Lemma lem3112803 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem3112762 m n) (@lem3112761 m n)). Qed.
Lemma lem3112804 (e : nat) : (e = (NUMERAL 0)) = ((int_of_num e) = term46).
Proof. exact (@lem3112803 e (NUMERAL 0)). Qed.
Lemma lem3112809 (n : nat) (e : nat) : (term49 n e) = (term50 n e).
Proof. exact (MK_COMB (@lem3112799 n) (@lem3112804 e)). Qed.
Lemma lem3112814 (d : nat) (n : nat) (e : nat) : (term51 d n e) = (term52 d n e).
Proof. exact (MK_COMB (@lem3112784 d n) (@lem3112809 n e)). Qed.
Lemma lem3112817 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3112818 (d : nat) (n : nat) (e : nat) : (term53 d n e) = (term54 d n e).
Proof. exact (MK_COMB (@lem3112817) (@lem3112814 d n e)). Qed.
Lemma lem3112824 (a : nat) (b : nat) : (num_divides a b) = (term39 a b).
Proof. exact (EQ_MP (@lem3112750 a b) (@lem3112749 a b)). Qed.
Lemma lem3112825 (n : nat) (d : nat) (e : nat) : (term55 n d e) = (term56 n d e).
Proof. exact (@lem3112824 (Nat.div n d) e). Qed.
Lemma lem3112827 (m : nat) (n : nat) : (term11 m n) = (term10 m n).
Proof. exact (EQ_MP (@lem3112756 m n) (@lem3112755 m n)). Qed.
Lemma lem3112828 (n : nat) (d : nat) : (term11 n d) = (term10 n d).
Proof. exact (@lem3112827 n d). Qed.
Lemma lem3112829 : int_divides = int_divides.
Proof. exact (eq_refl int_divides). Qed.
Lemma lem3112830 (n : nat) (d : nat) : (term57 n d) = (term58 n d).
Proof. exact (MK_COMB (@lem3112829) (@lem3112828 n d)). Qed.
Lemma lem3112831 (e : nat) : (int_of_num e) = (int_of_num e).
Proof. exact (eq_refl (int_of_num e)). Qed.
Lemma lem3112832 (n : nat) (d : nat) (e : nat) : (term56 n d e) = (term59 n d e).
Proof. exact (MK_COMB (@lem3112830 n d) (@lem3112831 e)). Qed.
Lemma lem3112833 (n : nat) (d : nat) (e : nat) : (term55 n d e) = (term59 n d e).
Proof. exact (TRANS (@lem3112825 n d e) (@lem3112832 n d e)). Qed.
Lemma lem3112834 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3112835 (n : nat) (d : nat) (e : nat) : (term60 n d e) = (term61 n d e).
Proof. exact (MK_COMB (@lem3112834) (@lem3112833 n d e)). Qed.
Lemma lem3112837 (a : nat) (b : nat) : (num_divides a b) = (term39 a b).
Proof. exact (EQ_MP (@lem3112750 a b) (@lem3112749 a b)). Qed.
Lemma lem3112838 (n : nat) (d : nat) (e : nat) : (term62 n d e) = (term63 n d e).
Proof. exact (@lem3112837 n (Nat.mul d e)). Qed.
Lemma lem3112840 (m : nat) (n : nat) : (term1 m n) = (term0 m n).
Proof. exact (EQ_MP (@lem3112744 m n) (@lem3112743 m n)). Qed.
Lemma lem3112841 (d : nat) (e : nat) : (term1 d e) = (term0 d e).
Proof. exact (@lem3112840 d e). Qed.
Lemma lem3112842 (n : nat) : (term64 n) = (term64 n).
Proof. exact (eq_refl (term64 n)). Qed.
Lemma lem3112843 (n : nat) (d : nat) (e : nat) : (term63 n d e) = (term65 n d e).
Proof. exact (MK_COMB (@lem3112842 n) (@lem3112841 d e)). Qed.
Lemma lem3112844 (n : nat) (d : nat) (e : nat) : (term62 n d e) = (term65 n d e).
Proof. exact (TRANS (@lem3112838 n d e) (@lem3112843 n d e)). Qed.
Lemma lem3112845 (n : nat) (d : nat) (e : nat) : ((term55 n d e) = (term62 n d e)) = ((term59 n d e) = (term65 n d e)).
Proof. exact (MK_COMB (@lem3112835 n d e) (@lem3112844 n d e)). Qed.
Lemma lem3112850 (n : nat) (d : nat) (e : nat) : (term66 n d e) = (term67 n d e).
Proof. exact (MK_COMB (@lem3112818 d n e) (@lem3112845 n d e)). Qed.
Lemma lem3112852 (n : int) (d : int) (e : int) : (term33 n d e) = True.
Proof. exact (EQ_MP (@lem3112738 n d e) (@lem3112737 n d e)). Qed.
Lemma lem3112853 (n : nat) (d : nat) (e : nat) : (term67 n d e) = True.
Proof. exact (@lem3112852 (int_of_num n) (int_of_num d) (int_of_num e)). Qed.
Lemma lem3112854 (n : nat) (d : nat) (e : nat) : (term66 n d e) = True.
Proof. exact (TRANS (@lem3112850 n d e) (@lem3112853 n d e)). Qed.
Lemma lem3112855 (n : nat) (d : nat) : (term68 n d) = term69.
Proof. exact (fun_ext (fun e : nat => @lem3112854 n d e)). Qed.
Lemma lem3112856 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112857 (n : nat) (d : nat) : (term70 n d) = term71.
Proof. exact (MK_COMB (@lem3112856) (@lem3112855 n d)). Qed.
Lemma lem3112859 {A : Type'} (t : Prop) : (term72 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3112860 (t : Prop) : (term73 t) = t.
Proof. exact (@lem3112859 nat t). Qed.
Lemma lem3112861 : term71 = True.
Proof. exact (@lem3112860 True). Qed.
Lemma lem3112862 (n : nat) (d : nat) : (term70 n d) = True.
Proof. exact (TRANS (@lem3112857 n d) (@lem3112861)). Qed.
Lemma lem3112863 (n : nat) : (term74 n) = term69.
Proof. exact (fun_ext (fun d : nat => @lem3112862 n d)). Qed.
Lemma lem3112864 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112865 (n : nat) : (term75 n) = term71.
Proof. exact (MK_COMB (@lem3112864) (@lem3112863 n)). Qed.
Lemma lem3112867 {A : Type'} (t : Prop) : (term72 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3112868 (t : Prop) : (term73 t) = t.
Proof. exact (@lem3112867 nat t). Qed.
Lemma lem3112869 : term71 = True.
Proof. exact (@lem3112868 True). Qed.
Lemma lem3112870 (n : nat) : (term75 n) = True.
Proof. exact (TRANS (@lem3112865 n) (@lem3112869)). Qed.
Lemma lem3112871 : term76 = term69.
Proof. exact (fun_ext (fun n : nat => @lem3112870 n)). Qed.
Lemma lem3112872 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112873 : term77 = term71.
Proof. exact (MK_COMB (@lem3112872) (@lem3112871)). Qed.
Lemma lem3112875 {A : Type'} (t : Prop) : (term72 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3112876 (t : Prop) : (term73 t) = t.
Proof. exact (@lem3112875 nat t). Qed.
Lemma lem3112877 : term71 = True.
Proof. exact (@lem3112876 True). Qed.
Lemma lem3112878 : term77 = True.
Proof. exact (TRANS (@lem3112873) (@lem3112877)). Qed.
Lemma lem3112879 : True = term77.
Proof. exact (SYM (@lem3112878)). Qed.
Lemma lem3112880 : term77.
Proof. exact (EQ_MP (@lem3112879) (@lem0)). Qed.
