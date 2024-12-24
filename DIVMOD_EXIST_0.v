Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIVMOD_EXIST_0_term_abbrevs.
Require Import DIVMOD_EXIST_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import EXISTS_REFL_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import RIGHT_EXISTS_AND_THM_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem154677 (n : nat) : term0 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem154678 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem154679 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem154678 n) (@lem154677 n)). Qed.
Lemma lem154681 (n : nat) (h1 : term2 n) : term2 n.
Proof. exact (h1). Qed.
Lemma lem154682 {A : Type'} (a : A) : term3 A a.
Proof. exact (@lem4363 A a). Qed.
Lemma lem154683 {A : Type'} (a : A) : (term3 A a) = (term4 A a).
Proof. exact (eq_refl (term3 A a)). Qed.
Lemma lem154684 {A : Type'} (a : A) : term4 A a.
Proof. exact (EQ_MP (@lem154683 A a) (@lem154682 A a)). Qed.
Lemma lem154685 {A : Type'} (a : A) : (term4 A a) = ((term4 A a) = True).
Proof. exact (@lem7 (term4 A a)). Qed.
Lemma lem154687 {A : Type'} (P : Prop) : term5 A P.
Proof. exact (@lem5751 A P). Qed.
Lemma lem154688 {A : Type'} (P : Prop) : (term5 A P) = (term6 A P).
Proof. exact (eq_refl (term5 A P)). Qed.
Lemma lem154689 {A : Type'} (P : Prop) : term6 A P.
Proof. exact (EQ_MP (@lem154688 A P) (@lem154687 A P)). Qed.
Lemma lem154690 {A : Type'} (P : Prop) (Q : A -> Prop) : term7 A P Q.
Proof. exact (@lem154689 A P Q). Qed.
Lemma lem154691 {A : Type'} (P : Prop) (Q : A -> Prop) : (term7 A P Q) = ((term8 A P Q) = (term9 A P Q)).
Proof. exact (eq_refl (term7 A P Q)). Qed.
Lemma lem154719 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term10 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem154720 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term11 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem154719 _2963 g t e g' t' e'). Qed.
Lemma lem154721 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term12 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem154720 _2963 g t e g' t'). Qed.
Lemma lem154722 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term13 _2963 g t e.
Proof. exact (fun g' : Prop => @lem154721 _2963 g t e g'). Qed.
Lemma lem154723 (g : Prop) (t : Prop) (e : Prop) : term14 g t e.
Proof. exact (@lem154722 Prop g t e). Qed.
Lemma lem154724 (m : nat) (q : nat) (r : nat) (n : nat) : term15 m q r n.
Proof. exact (@lem154723 (n = (NUMERAL 0)) (term16 q r m) (term17 m q r n)). Qed.
Lemma lem154725 (m : nat) (q : nat) (r : nat) (n : nat) (g' : Prop) : term18 m q r n g'.
Proof. exact (@lem154724 m q r n g'). Qed.
Lemma lem154726 (m : nat) (q : nat) (r : nat) (n : nat) (g' : Prop) : (term18 m q r n g') = (term19 m q r n g').
Proof. exact (eq_refl (term18 m q r n g')). Qed.
Lemma lem154727 (m : nat) (q : nat) (r : nat) (n : nat) (g' : Prop) : term19 m q r n g'.
Proof. exact (EQ_MP (@lem154726 m q r n g') (@lem154725 m q r n g')). Qed.
Lemma lem154728 (m : nat) (q : nat) (r : nat) (n : nat) (g' : Prop) (t' : Prop) : term20 m q r n g' t'.
Proof. exact (@lem154727 m q r n g' t'). Qed.
Lemma lem154729 (m : nat) (q : nat) (r : nat) (n : nat) (g' : Prop) (t' : Prop) : (term20 m q r n g' t') = (term21 m q r n g' t').
Proof. exact (eq_refl (term20 m q r n g' t')). Qed.
Lemma lem154730 (m : nat) (q : nat) (r : nat) (n : nat) (g' : Prop) (t' : Prop) : term21 m q r n g' t'.
Proof. exact (EQ_MP (@lem154729 m q r n g' t') (@lem154728 m q r n g' t')). Qed.
Lemma lem154731 (m : nat) (q : nat) (r : nat) (n : nat) (g' : Prop) (t' : Prop) (e' : Prop) : term22 m q r n g' t' e'.
Proof. exact (@lem154730 m q r n g' t' e'). Qed.
Lemma lem154732 (m : nat) (q : nat) (r : nat) (n : nat) (g' : Prop) (t' : Prop) (e' : Prop) : (term22 m q r n g' t' e') = (term23 m q r n g' t' e').
Proof. exact (eq_refl (term22 m q r n g' t' e')). Qed.
Lemma lem154733 (m : nat) (q : nat) (r : nat) (n : nat) (g' : Prop) (t' : Prop) (e' : Prop) : term23 m q r n g' t' e'.
Proof. exact (EQ_MP (@lem154732 m q r n g' t' e') (@lem154731 m q r n g' t' e')). Qed.
Lemma lem154737 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem154738 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem154739 (n : nat) (h1 : n = (NUMERAL 0)) : (@eq nat n) = term24.
Proof. exact (MK_COMB (@lem154738) (@lem154737 n h1)). Qed.
Lemma lem154740 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem154741 (n : nat) (h1 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem154739 n h1) (@lem154740)). Qed.
Lemma lem154743 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem154744 (x : nat) : (x = x) = True.
Proof. exact (@lem154743 nat x). Qed.
Lemma lem154745 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem154744 (NUMERAL 0)). Qed.
Lemma lem154746 (n : nat) (h1 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem154741 n h1) (@lem154745)). Qed.
Lemma lem154747 (m : nat) (q : nat) (r : nat) (n : nat) (t' : Prop) (e' : Prop) : term25 m q r n t' e'.
Proof. exact (@lem154733 m q r n True t' e'). Qed.
Lemma lem154748 (m : nat) (q : nat) (r : nat) (t' : Prop) (e' : Prop) (n : nat) (h1 : n = (NUMERAL 0)) : term26 m q r n t' e'.
Proof. exact (@lem154747 m q r n t' e' (@lem154746 n h1)). Qed.
Lemma lem154760 (q : nat) (r : nat) (m : nat) : (term16 q r m) = (term16 q r m).
Proof. exact (eq_refl (term16 q r m)). Qed.
Lemma lem154761 (q : nat) (r : nat) (m : nat) : term27 q r m.
Proof. exact (fun h0 : True => @lem154760 q r m). Qed.
Lemma lem154762 (q : nat) (r : nat) (m : nat) (e' : Prop) (n : nat) (h1 : n = (NUMERAL 0)) : term28 n q r m e'.
Proof. exact (@lem154748 m q r (term16 q r m) e' n h1). Qed.
Lemma lem154763 (q : nat) (r : nat) (m : nat) (e' : Prop) (n : nat) (h1 : n = (NUMERAL 0)) : term29 n q r m e'.
Proof. exact (@lem154762 q r m e' n h1 (@lem154761 q r m)). Qed.
Lemma lem154772 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem154773 (q : nat) : (Nat.mul q) = (Nat.mul q).
Proof. exact (eq_refl (Nat.mul q)). Qed.
Lemma lem154774 (q : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.mul q n) = (term30 q).
Proof. exact (MK_COMB (@lem154773 q) (@lem154772 n h1)). Qed.
Lemma lem154775 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem154776 (q : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term31 q n) = (term32 q).
Proof. exact (MK_COMB (@lem154775) (@lem154774 q n h1)). Qed.
Lemma lem154777 (r : nat) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem154778 (q : nat) (r : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term33 q n r) = (term34 q r).
Proof. exact (MK_COMB (@lem154776 q n h1) (@lem154777 r)). Qed.
Lemma lem154779 (m : nat) : (@eq nat m) = (@eq nat m).
Proof. exact (eq_refl (@eq nat m)). Qed.
Lemma lem154780 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (m = (term33 q n r)) = (m = (term34 q r)).
Proof. exact (MK_COMB (@lem154779 m) (@lem154778 q r n h1)). Qed.
Lemma lem154783 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem154784 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term35 m q n r) = (term36 m q r).
Proof. exact (MK_COMB (@lem154783) (@lem154780 m q r n h1)). Qed.
Lemma lem154788 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem154789 (r : nat) : (Peano.lt r) = (Peano.lt r).
Proof. exact (eq_refl (Peano.lt r)). Qed.
Lemma lem154790 (r : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Peano.lt r n) = (term37 r).
Proof. exact (MK_COMB (@lem154789 r) (@lem154788 n h1)). Qed.
Lemma lem154791 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term17 m q r n) = (term38 m q r).
Proof. exact (MK_COMB (@lem154784 m q r n h1) (@lem154790 r n h1)). Qed.
Lemma lem154796 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : n = (NUMERAL 0)) : term39 n m q r.
Proof. exact (fun h0 : ~ True => @lem154791 m q r n h1). Qed.
Lemma lem154797 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : n = (NUMERAL 0)) : term40 n m q r.
Proof. exact (@lem154763 q r m (term38 m q r) n h1). Qed.
Lemma lem154798 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term41 m q r n) = (term42 m q r).
Proof. exact (@lem154797 m q r n h1 (@lem154796 m q r n h1)). Qed.
Lemma lem154800 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem154801 (t2 : Prop) (t1 : Prop) : (@COND Prop True t1 t2) = t1.
Proof. exact (@lem154800 Prop t2 t1). Qed.
Lemma lem154802 (q : nat) (r : nat) (m : nat) : (term42 m q r) = (term16 q r m).
Proof. exact (@lem154801 (term38 m q r) (term16 q r m)). Qed.
Lemma lem154809 (q : nat) (r : nat) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term41 m q r n) = (term16 q r m).
Proof. exact (TRANS (@lem154798 m q r n h1) (@lem154802 q r m)). Qed.
Lemma lem154810 (q : nat) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term43 m q n) = (term44 q m).
Proof. exact (fun_ext (fun r : nat => @lem154809 q r m n h1)). Qed.
Lemma lem154817 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem154818 (q : nat) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term45 m q n) = (term46 q m).
Proof. exact (MK_COMB (@lem154817) (@lem154810 q m n h1)). Qed.
Lemma lem154820 {A : Type'} (P : Prop) (Q : A -> Prop) : (term8 A P Q) = (term9 A P Q).
Proof. exact (EQ_MP (@lem154691 A P Q) (@lem154690 A P Q)). Qed.
Lemma lem154821 (P : Prop) (Q : nat -> Prop) : (term47 P Q) = (term48 P Q).
Proof. exact (@lem154820 nat P Q). Qed.
Lemma lem154822 (q : nat) (m : nat) : (term49 q m) = (term50 q m).
Proof. exact (@lem154821 (q = (NUMERAL 0)) (term51 m)). Qed.
Lemma lem154823 (r : nat) (m : nat) : (term52 m r) = (r = m).
Proof. exact (eq_refl (term52 m r)). Qed.
Lemma lem154824 (q : nat) : (term53 q) = (term53 q).
Proof. exact (eq_refl (term53 q)). Qed.
Lemma lem154825 (q : nat) (r : nat) (m : nat) : (term54 q m r) = (term16 q r m).
Proof. exact (MK_COMB (@lem154824 q) (@lem154823 r m)). Qed.
Lemma lem154826 (q : nat) (m : nat) : (term55 q m) = (term44 q m).
Proof. exact (fun_ext (fun r : nat => @lem154825 q r m)). Qed.
Lemma lem154827 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem154828 (q : nat) (m : nat) : (term49 q m) = (term46 q m).
Proof. exact (MK_COMB (@lem154827) (@lem154826 q m)). Qed.
Lemma lem154829 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem154830 (q : nat) (m : nat) : (term56 q m) = (term57 q m).
Proof. exact (MK_COMB (@lem154829) (@lem154828 q m)). Qed.
Lemma lem154831 (r : nat) (m : nat) : (term52 m r) = (r = m).
Proof. exact (eq_refl (term52 m r)). Qed.
Lemma lem154832 (m : nat) : (term58 m) = (term51 m).
Proof. exact (fun_ext (fun r : nat => @lem154831 r m)). Qed.
Lemma lem154833 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem154834 (m : nat) : (term59 m) = (term60 m).
Proof. exact (MK_COMB (@lem154833) (@lem154832 m)). Qed.
Lemma lem154835 (q : nat) : (term53 q) = (term53 q).
Proof. exact (eq_refl (term53 q)). Qed.
Lemma lem154836 (q : nat) (m : nat) : (term50 q m) = (term61 q m).
Proof. exact (MK_COMB (@lem154835 q) (@lem154834 m)). Qed.
Lemma lem154837 (q : nat) (m : nat) : ((term49 q m) = (term50 q m)) = ((term46 q m) = (term61 q m)).
Proof. exact (MK_COMB (@lem154830 q m) (@lem154836 q m)). Qed.
Lemma lem154838 (q : nat) (m : nat) : (term46 q m) = (term61 q m).
Proof. exact (EQ_MP (@lem154837 q m) (@lem154822 q m)). Qed.
Lemma lem154844 {A : Type'} (a : A) : (term4 A a) = True.
Proof. exact (EQ_MP (@lem154685 A a) (@lem154684 A a)). Qed.
Lemma lem154845 (a : nat) : (term60 a) = True.
Proof. exact (@lem154844 nat a). Qed.
Lemma lem154846 (m : nat) : (term60 m) = True.
Proof. exact (@lem154845 m). Qed.
Lemma lem154847 (q : nat) : (term53 q) = (term53 q).
Proof. exact (eq_refl (term53 q)). Qed.
Lemma lem154848 (m : nat) (q : nat) : (term61 q m) = (term62 q).
Proof. exact (MK_COMB (@lem154847 q) (@lem154846 m)). Qed.
Lemma lem154850 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem154851 (q : nat) : (term62 q) = (q = (NUMERAL 0)).
Proof. exact (@lem154850 (q = (NUMERAL 0))). Qed.
Lemma lem154854 (m : nat) (q : nat) : (term61 q m) = (q = (NUMERAL 0)).
Proof. exact (TRANS (@lem154848 m q) (@lem154851 q)). Qed.
Lemma lem154855 (m : nat) (q : nat) : (term46 q m) = (q = (NUMERAL 0)).
Proof. exact (TRANS (@lem154838 q m) (@lem154854 m q)). Qed.
Lemma lem154856 (m : nat) (q : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term45 m q n) = (q = (NUMERAL 0)).
Proof. exact (TRANS (@lem154818 q m n h1) (@lem154855 m q)). Qed.
Lemma lem154857 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term63 m n) = term64.
Proof. exact (fun_ext (fun q : nat => @lem154856 m q n h1)). Qed.
Lemma lem154860 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem154861 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term65 m n) = term66.
Proof. exact (MK_COMB (@lem154860) (@lem154857 m n h1)). Qed.
Lemma lem154863 {A : Type'} (a : A) : (term4 A a) = True.
Proof. exact (EQ_MP (@lem154685 A a) (@lem154684 A a)). Qed.
Lemma lem154864 (a : nat) : (term60 a) = True.
Proof. exact (@lem154863 nat a). Qed.
Lemma lem154865 : term66 = True.
Proof. exact (@lem154864 (NUMERAL 0)). Qed.
Lemma lem154866 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term65 m n) = True.
Proof. exact (TRANS (@lem154861 m n h1) (@lem154865)). Qed.
Lemma lem154867 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : True = (term65 m n).
Proof. exact (SYM (@lem154866 m n h1)). Qed.
Lemma lem154868 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : term65 m n.
Proof. exact (EQ_MP (@lem154867 m n h1) (@lem0)). Qed.
Lemma lem154880 (m : nat) : term67 m.
Proof. exact (@lem154676 m). Qed.
Lemma lem154881 (m : nat) : (term67 m) = (term68 m).
Proof. exact (eq_refl (term67 m)). Qed.
Lemma lem154882 (m : nat) : term68 m.
Proof. exact (EQ_MP (@lem154881 m) (@lem154880 m)). Qed.
Lemma lem154883 (m : nat) (n : nat) : term69 m n.
Proof. exact (@lem154882 m n). Qed.
Lemma lem154884 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (eq_refl (term69 m n)). Qed.
Lemma lem154885 (m : nat) (n : nat) : term70 m n.
Proof. exact (EQ_MP (@lem154884 m n) (@lem154883 m n)). Qed.
Lemma lem154886 (n : nat) (h1 : term2 n) : term2 n.
Proof. exact (h1). Qed.
Lemma lem154887 (m : nat) (n : nat) (h1 : term2 n) : term71 m n.
Proof. exact (@lem154885 m n (@lem154886 n h1)). Qed.
Lemma lem154888 (m : nat) (n : nat) : (term71 m n) = ((term71 m n) = True).
Proof. exact (@lem7 (term71 m n)). Qed.
Lemma lem154889 (m : nat) (n : nat) (h1 : term2 n) : (term71 m n) = True.
Proof. exact (EQ_MP (@lem154888 m n) (@lem154887 m n h1)). Qed.
Lemma lem154895 (n : nat) : term72 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem154919 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term10 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem154920 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term11 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem154919 _2963 g t e g' t' e'). Qed.
Lemma lem154921 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term12 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem154920 _2963 g t e g' t'). Qed.
Lemma lem154922 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term13 _2963 g t e.
Proof. exact (fun g' : Prop => @lem154921 _2963 g t e g'). Qed.
Lemma lem154923 (g : Prop) (t : Prop) (e : Prop) : term14 g t e.
Proof. exact (@lem154922 Prop g t e). Qed.
Lemma lem154924 (m : nat) (q : nat) (r : nat) (n : nat) : term15 m q r n.
Proof. exact (@lem154923 (n = (NUMERAL 0)) (term16 q r m) (term17 m q r n)). Qed.
Lemma lem154925 (m : nat) (q : nat) (r : nat) (n : nat) (g' : Prop) : term18 m q r n g'.
Proof. exact (@lem154924 m q r n g'). Qed.
Lemma lem154926 (m : nat) (q : nat) (r : nat) (n : nat) (g' : Prop) : (term18 m q r n g') = (term19 m q r n g').
Proof. exact (eq_refl (term18 m q r n g')). Qed.
Lemma lem154927 (m : nat) (q : nat) (r : nat) (n : nat) (g' : Prop) : term19 m q r n g'.
Proof. exact (EQ_MP (@lem154926 m q r n g') (@lem154925 m q r n g')). Qed.
Lemma lem154928 (m : nat) (q : nat) (r : nat) (n : nat) (g' : Prop) (t' : Prop) : term20 m q r n g' t'.
Proof. exact (@lem154927 m q r n g' t'). Qed.
Lemma lem154929 (m : nat) (q : nat) (r : nat) (n : nat) (g' : Prop) (t' : Prop) : (term20 m q r n g' t') = (term21 m q r n g' t').
Proof. exact (eq_refl (term20 m q r n g' t')). Qed.
Lemma lem154930 (m : nat) (q : nat) (r : nat) (n : nat) (g' : Prop) (t' : Prop) : term21 m q r n g' t'.
Proof. exact (EQ_MP (@lem154929 m q r n g' t') (@lem154928 m q r n g' t')). Qed.
Lemma lem154931 (m : nat) (q : nat) (r : nat) (n : nat) (g' : Prop) (t' : Prop) (e' : Prop) : term22 m q r n g' t' e'.
Proof. exact (@lem154930 m q r n g' t' e'). Qed.
Lemma lem154932 (m : nat) (q : nat) (r : nat) (n : nat) (g' : Prop) (t' : Prop) (e' : Prop) : (term22 m q r n g' t' e') = (term23 m q r n g' t' e').
Proof. exact (eq_refl (term22 m q r n g' t' e')). Qed.
Lemma lem154933 (m : nat) (q : nat) (r : nat) (n : nat) (g' : Prop) (t' : Prop) (e' : Prop) : term23 m q r n g' t' e'.
Proof. exact (EQ_MP (@lem154932 m q r n g' t' e') (@lem154931 m q r n g' t' e')). Qed.
Lemma lem154935 (n : nat) (h1 : term2 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem154895 n (@lem154681 n h1)). Qed.
Lemma lem154936 (m : nat) (q : nat) (r : nat) (n : nat) (t' : Prop) (e' : Prop) : term73 m q r n t' e'.
Proof. exact (@lem154933 m q r n False t' e'). Qed.
Lemma lem154937 (m : nat) (q : nat) (r : nat) (t' : Prop) (e' : Prop) (n : nat) (h1 : term2 n) : term74 m q r n t' e'.
Proof. exact (@lem154936 m q r n t' e' (@lem154935 n h1)). Qed.
Lemma lem154947 (q : nat) (r : nat) (m : nat) : (term16 q r m) = (term16 q r m).
Proof. exact (eq_refl (term16 q r m)). Qed.
Lemma lem154948 (q : nat) (r : nat) (m : nat) : term75 q r m.
Proof. exact (fun h0 : False => @lem154947 q r m). Qed.
Lemma lem154949 (q : nat) (r : nat) (m : nat) (e' : Prop) (n : nat) (h1 : term2 n) : term76 n q r m e'.
Proof. exact (@lem154937 m q r (term16 q r m) e' n h1). Qed.
Lemma lem154950 (q : nat) (r : nat) (m : nat) (e' : Prop) (n : nat) (h1 : term2 n) : term77 n q r m e'.
Proof. exact (@lem154949 q r m e' n h1 (@lem154948 q r m)). Qed.
Lemma lem154960 (m : nat) (q : nat) (r : nat) (n : nat) : (term17 m q r n) = (term17 m q r n).
Proof. exact (eq_refl (term17 m q r n)). Qed.
Lemma lem154961 (m : nat) (q : nat) (r : nat) (n : nat) : term78 m q r n.
Proof. exact (fun h0 : ~ False => @lem154960 m q r n). Qed.
Lemma lem154962 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term2 n) : term79 m q r n.
Proof. exact (@lem154950 q r m (term17 m q r n) n h1). Qed.
Lemma lem154963 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term2 n) : (term41 m q r n) = (term80 m q r n).
Proof. exact (@lem154962 m q r n h1 (@lem154961 m q r n)). Qed.
Lemma lem154965 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem154966 (t1 : Prop) (t2 : Prop) : (@COND Prop False t1 t2) = t2.
Proof. exact (@lem154965 Prop t1 t2). Qed.
Lemma lem154967 (m : nat) (q : nat) (r : nat) (n : nat) : (term80 m q r n) = (term17 m q r n).
Proof. exact (@lem154966 (term16 q r m) (term17 m q r n)). Qed.
Lemma lem154972 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term2 n) : (term41 m q r n) = (term17 m q r n).
Proof. exact (TRANS (@lem154963 m q r n h1) (@lem154967 m q r n)). Qed.
Lemma lem154973 (m : nat) (q : nat) (n : nat) (h1 : term2 n) : (term43 m q n) = (term81 m q n).
Proof. exact (fun_ext (fun r : nat => @lem154972 m q r n h1)). Qed.
Lemma lem154978 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem154979 (m : nat) (q : nat) (n : nat) (h1 : term2 n) : (term45 m q n) = (term82 m q n).
Proof. exact (MK_COMB (@lem154978) (@lem154973 m q n h1)). Qed.
Lemma lem155008 (m : nat) (n : nat) (h1 : term2 n) : (term63 m n) = (term83 m n).
Proof. exact (fun_ext (fun q : nat => @lem154979 m q n h1)). Qed.
Lemma lem155037 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem155038 (m : nat) (n : nat) (h1 : term2 n) : (term65 m n) = (term71 m n).
Proof. exact (MK_COMB (@lem155037) (@lem155008 m n h1)). Qed.
Lemma lem155040 (m : nat) (n : nat) : term84 m n.
Proof. exact (fun h0 : term2 n => @lem154889 m n h0). Qed.
Lemma lem155042 (n : nat) (h1 : term2 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem154895 n (@lem154681 n h1)). Qed.
Lemma lem155043 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem155044 (n : nat) (h1 : term2 n) : (term2 n) = (~ False).
Proof. exact (MK_COMB (@lem155043) (@lem155042 n h1)). Qed.
Lemma lem155046 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem155047 (n : nat) (h1 : term2 n) : (term2 n) = True.
Proof. exact (TRANS (@lem155044 n h1) (@lem155046)). Qed.
Lemma lem155048 (n : nat) (h1 : term2 n) : True = (term2 n).
Proof. exact (SYM (@lem155047 n h1)). Qed.
Lemma lem155049 (n : nat) (h1 : term2 n) : term2 n.
Proof. exact (EQ_MP (@lem155048 n h1) (@lem0)). Qed.
Lemma lem155050 (m : nat) (n : nat) (h1 : term2 n) : (term71 m n) = True.
Proof. exact (@lem155040 m n (@lem155049 n h1)). Qed.
Lemma lem155051 (m : nat) (n : nat) (h1 : term2 n) : (term65 m n) = True.
Proof. exact (TRANS (@lem155038 m n h1) (@lem155050 m n h1)). Qed.
Lemma lem155052 (m : nat) (n : nat) (h1 : term2 n) : True = (term65 m n).
Proof. exact (SYM (@lem155051 m n h1)). Qed.
Lemma lem155053 (m : nat) (n : nat) (h1 : term2 n) : term65 m n.
Proof. exact (EQ_MP (@lem155052 m n h1) (@lem0)). Qed.
Lemma lem155054 (m : nat) (n : nat) : term65 m n.
Proof. exact (or_elim (@lem154679 n) (fun h0 : n = (NUMERAL 0) => @lem154868 m n h0) (fun h0 : term2 n => @lem155053 m n h0)). Qed.
Lemma lem155059 (m : nat) : term85 m.
Proof. exact (fun n : nat => @lem155054 m n). Qed.
Lemma lem155064 : term86.
Proof. exact (fun m : nat => @lem155059 m). Qed.
