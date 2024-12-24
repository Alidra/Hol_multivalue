Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_CONST_NUMSEG_term_abbrevs.
Require Import CARD_NUMSEG_spec.
Require Import FINITE_NUMSEG_spec.
Require Import SUM_CONST_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem7213741 (m : nat) : term0 m.
Proof. exact (@lem5393502 m). Qed.
Lemma lem7213742 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem7213743 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem7213742 m) (@lem7213741 m)). Qed.
Lemma lem7213744 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem7213743 m n). Qed.
Lemma lem7213745 (n : nat) (m : nat) : (term2 m n) = ((term3 m n) = (term4 n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem7213747 (m : nat) : term5 m.
Proof. exact (@lem5329299 m). Qed.
Lemma lem7213748 (m : nat) : (term5 m) = (term6 m).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem7213749 (m : nat) : term6 m.
Proof. exact (EQ_MP (@lem7213748 m) (@lem7213747 m)). Qed.
Lemma lem7213750 (m : nat) (n : nat) : term7 m n.
Proof. exact (@lem7213749 m n). Qed.
Lemma lem7213751 (m : nat) (n : nat) : (term7 m n) = (term8 m n).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem7213752 (m : nat) (n : nat) : term8 m n.
Proof. exact (EQ_MP (@lem7213751 m n) (@lem7213750 m n)). Qed.
Lemma lem7213753 (m : nat) (n : nat) : (term8 m n) = ((term8 m n) = True).
Proof. exact (@lem7 (term8 m n)). Qed.
Lemma lem7213755 {_132484 : Type'} (c : real) : term9 _132484 c.
Proof. exact (@lem7085323 _132484 c). Qed.
Lemma lem7213756 {_132484 : Type'} (c : real) : (term9 _132484 c) = (term10 _132484 c).
Proof. exact (eq_refl (term9 _132484 c)). Qed.
Lemma lem7213757 {_132484 : Type'} (c : real) : term10 _132484 c.
Proof. exact (EQ_MP (@lem7213756 _132484 c) (@lem7213755 _132484 c)). Qed.
Lemma lem7213758 {_132484 : Type'} (c : real) (s : _132484 -> Prop) : term11 _132484 c s.
Proof. exact (@lem7213757 _132484 c s). Qed.
Lemma lem7213759 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term11 _132484 c s) = (term12 _132484 s c).
Proof. exact (eq_refl (term11 _132484 c s)). Qed.
Lemma lem7213760 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : term12 _132484 s c.
Proof. exact (EQ_MP (@lem7213759 _132484 s c) (@lem7213758 _132484 c s)). Qed.
Lemma lem7213761 {_132484 : Type'} (s : _132484 -> Prop) (h1 : @FINITE _132484 s) : @FINITE _132484 s.
Proof. exact (h1). Qed.
Lemma lem7213762 {_132484 : Type'} (c : real) (s : _132484 -> Prop) (h1 : @FINITE _132484 s) : (term13 _132484 s c) = (term14 _132484 s c).
Proof. exact (@lem7213760 _132484 s c (@lem7213761 _132484 s h1)). Qed.
Lemma lem7213783 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : term12 _132484 s c.
Proof. exact (fun h0 : @FINITE _132484 s => @lem7213762 _132484 c s h0). Qed.
Lemma lem7213784 (s : nat -> Prop) (c : real) : term15 s c.
Proof. exact (@lem7213783 nat s c). Qed.
Lemma lem7213785 (m : nat) (n : nat) (c : real) : term16 m n c.
Proof. exact (@lem7213784 (dotdot m n) c). Qed.
Lemma lem7213787 (m : nat) (n : nat) : (term8 m n) = True.
Proof. exact (EQ_MP (@lem7213753 m n) (@lem7213752 m n)). Qed.
Lemma lem7213788 (m : nat) (n : nat) : True = (term8 m n).
Proof. exact (SYM (@lem7213787 m n)). Qed.
Lemma lem7213789 (m : nat) (n : nat) : term8 m n.
Proof. exact (EQ_MP (@lem7213788 m n) (@lem0)). Qed.
Lemma lem7213790 (m : nat) (n : nat) (c : real) : (term17 m n c) = (term18 m n c).
Proof. exact (@lem7213785 m n c (@lem7213789 m n)). Qed.
Lemma lem7213792 (n : nat) (m : nat) : (term3 m n) = (term4 n m).
Proof. exact (EQ_MP (@lem7213745 n m) (@lem7213744 m n)). Qed.
Lemma lem7213793 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7213794 (n : nat) (m : nat) : (term19 m n) = (term20 n m).
Proof. exact (MK_COMB (@lem7213793) (@lem7213792 n m)). Qed.
Lemma lem7213795 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7213796 (n : nat) (m : nat) : (term21 m n) = (term22 n m).
Proof. exact (MK_COMB (@lem7213795) (@lem7213794 n m)). Qed.
Lemma lem7213797 (c : real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem7213798 (n : nat) (m : nat) (c : real) : (term18 m n c) = (term23 n m c).
Proof. exact (MK_COMB (@lem7213796 n m) (@lem7213797 c)). Qed.
Lemma lem7213799 (n : nat) (m : nat) (c : real) : (term17 m n c) = (term23 n m c).
Proof. exact (TRANS (@lem7213790 m n c) (@lem7213798 n m c)). Qed.
Lemma lem7213800 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7213801 (n : nat) (m : nat) (c : real) : (term24 m n c) = (term25 n m c).
Proof. exact (MK_COMB (@lem7213800) (@lem7213799 n m c)). Qed.
Lemma lem7213802 (n : nat) (m : nat) (c : real) : (term23 n m c) = (term23 n m c).
Proof. exact (eq_refl (term23 n m c)). Qed.
Lemma lem7213803 (n : nat) (m : nat) (c : real) : ((term17 m n c) = (term23 n m c)) = ((term23 n m c) = (term23 n m c)).
Proof. exact (MK_COMB (@lem7213801 n m c) (@lem7213802 n m c)). Qed.
Lemma lem7213805 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7213806 (x : real) : (x = x) = True.
Proof. exact (@lem7213805 real x). Qed.
Lemma lem7213807 (n : nat) (m : nat) (c : real) : ((term23 n m c) = (term23 n m c)) = True.
Proof. exact (@lem7213806 (term23 n m c)). Qed.
Lemma lem7213808 (n : nat) (m : nat) (c : real) : ((term17 m n c) = (term23 n m c)) = True.
Proof. exact (TRANS (@lem7213803 n m c) (@lem7213807 n m c)). Qed.
Lemma lem7213809 (m : nat) (c : real) : (term26 m c) = term27.
Proof. exact (fun_ext (fun n : nat => @lem7213808 n m c)). Qed.
Lemma lem7213810 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7213811 (m : nat) (c : real) : (term28 m c) = term29.
Proof. exact (MK_COMB (@lem7213810) (@lem7213809 m c)). Qed.
Lemma lem7213813 {A : Type'} (t : Prop) : (term30 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7213814 (t : Prop) : (term31 t) = t.
Proof. exact (@lem7213813 nat t). Qed.
Lemma lem7213815 : term29 = True.
Proof. exact (@lem7213814 True). Qed.
Lemma lem7213816 (m : nat) (c : real) : (term28 m c) = True.
Proof. exact (TRANS (@lem7213811 m c) (@lem7213815)). Qed.
Lemma lem7213817 (c : real) : (term32 c) = term27.
Proof. exact (fun_ext (fun m : nat => @lem7213816 m c)). Qed.
Lemma lem7213818 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7213819 (c : real) : (term33 c) = term29.
Proof. exact (MK_COMB (@lem7213818) (@lem7213817 c)). Qed.
Lemma lem7213821 {A : Type'} (t : Prop) : (term30 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7213822 (t : Prop) : (term31 t) = t.
Proof. exact (@lem7213821 nat t). Qed.
Lemma lem7213823 : term29 = True.
Proof. exact (@lem7213822 True). Qed.
Lemma lem7213824 (c : real) : (term33 c) = True.
Proof. exact (TRANS (@lem7213819 c) (@lem7213823)). Qed.
Lemma lem7213825 : term34 = term35.
Proof. exact (fun_ext (fun c : real => @lem7213824 c)). Qed.
Lemma lem7213826 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7213827 : term36 = term37.
Proof. exact (MK_COMB (@lem7213826) (@lem7213825)). Qed.
Lemma lem7213829 {A : Type'} (t : Prop) : (term30 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7213830 (t : Prop) : (term38 t) = t.
Proof. exact (@lem7213829 real t). Qed.
Lemma lem7213831 : term37 = True.
Proof. exact (@lem7213830 True). Qed.
Lemma lem7213832 : term36 = True.
Proof. exact (TRANS (@lem7213827) (@lem7213831)). Qed.
Lemma lem7213833 : True = term36.
Proof. exact (SYM (@lem7213832)). Qed.
Lemma lem7213834 : term36.
Proof. exact (EQ_MP (@lem7213833) (@lem0)). Qed.
