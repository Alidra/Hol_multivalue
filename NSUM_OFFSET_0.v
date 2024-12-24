Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_OFFSET_0_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import NSUM_OFFSET_spec.
Require Import SUB_ADD_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem7048731 (m : nat) (n : nat) (f : nat -> nat) (p : nat) (h1 : (term0 m n p f) = (term1 m n f p)) : (term0 m n p f) = (term1 m n f p).
Proof. exact (h1). Qed.
Lemma lem7048732 (m : nat) (n : nat) (f : nat -> nat) (p : nat) (h1 : (term0 m n p f) = (term1 m n f p)) : (term1 m n f p) = (term0 m n p f).
Proof. exact (SYM (@lem7048731 m n f p h1)). Qed.
Lemma lem7048733 (m : nat) (n : nat) (p : nat) (f : nat -> nat) (h1 : (term1 m n f p) = (term0 m n p f)) : (term1 m n f p) = (term0 m n p f).
Proof. exact (h1). Qed.
Lemma lem7048734 (m : nat) (n : nat) (p : nat) (f : nat -> nat) (h1 : (term1 m n f p) = (term0 m n p f)) : (term0 m n p f) = (term1 m n f p).
Proof. exact (SYM (@lem7048733 m n p f h1)). Qed.
Lemma lem7048735 (m : nat) (n : nat) (p : nat) (f : nat -> nat) : ((term0 m n p f) = (term1 m n f p)) = ((term1 m n f p) = (term0 m n p f)).
Proof. exact (prop_ext (fun h1 : (term0 m n p f) = (term1 m n f p) => @lem7048732 m n f p h1) (fun h1 : (term1 m n f p) = (term0 m n p f) => @lem7048734 m n p f h1)). Qed.
Lemma lem7048736 (m : nat) (p : nat) (f : nat -> nat) : (term2 m f p) = (term3 m p f).
Proof. exact (fun_ext (fun n : nat => @lem7048735 m n p f)). Qed.
Lemma lem7048737 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7048738 (m : nat) (p : nat) (f : nat -> nat) : (term4 m f p) = (term5 m p f).
Proof. exact (MK_COMB (@lem7048737) (@lem7048736 m p f)). Qed.
Lemma lem7048739 (p : nat) (f : nat -> nat) : (term6 f p) = (term7 p f).
Proof. exact (fun_ext (fun m : nat => @lem7048738 m p f)). Qed.
Lemma lem7048740 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7048741 (p : nat) (f : nat -> nat) : (term8 f p) = (term9 p f).
Proof. exact (MK_COMB (@lem7048740) (@lem7048739 p f)). Qed.
Lemma lem7048742 (p : nat) : (term10 p) = (term11 p).
Proof. exact (fun_ext (fun f : nat -> nat => @lem7048741 p f)). Qed.
Lemma lem7048743 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7048744 (p : nat) : (term12 p) = (term13 p).
Proof. exact (MK_COMB (@lem7048743) (@lem7048742 p)). Qed.
Lemma lem7048745 : term14 = term15.
Proof. exact (fun_ext (fun p : nat => @lem7048744 p)). Qed.
Lemma lem7048746 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7048747 : term16 = term17.
Proof. exact (MK_COMB (@lem7048746) (@lem7048745)). Qed.
Lemma lem7048748 : term17.
Proof. exact (EQ_MP (@lem7048747) (@lem7048726)). Qed.
Lemma lem7048749 (m : nat) : term18 m.
Proof. exact (@lem136494 m). Qed.
Lemma lem7048750 (m : nat) : (term18 m) = (term19 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem7048751 (m : nat) : term19 m.
Proof. exact (EQ_MP (@lem7048750 m) (@lem7048749 m)). Qed.
Lemma lem7048752 (m : nat) (n : nat) : term20 m n.
Proof. exact (@lem7048751 m n). Qed.
Lemma lem7048753 (n : nat) (m : nat) : (term20 m n) = (term21 n m).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem7048754 (n : nat) (m : nat) : term21 n m.
Proof. exact (EQ_MP (@lem7048753 n m) (@lem7048752 m n)). Qed.
Lemma lem7048755 (n : nat) (m : nat) (h1 : Peano.le n m) : Peano.le n m.
Proof. exact (h1). Qed.
Lemma lem7048756 (n : nat) (m : nat) (h1 : Peano.le n m) : (term22 m n) = m.
Proof. exact (@lem7048754 n m (@lem7048755 n m h1)). Qed.
Lemma lem7048782 : term23.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem7048783 (n : nat) : term24 n.
Proof. exact (@lem7048782 n). Qed.
Lemma lem7048784 (n : nat) : (term24 n) = ((term25 n) = n).
Proof. exact (eq_refl (term24 n)). Qed.
Lemma lem7048786 (p : nat) : term26 p.
Proof. exact (@lem7048748 p). Qed.
Lemma lem7048787 (p : nat) : (term26 p) = (term13 p).
Proof. exact (eq_refl (term26 p)). Qed.
Lemma lem7048788 (p : nat) : term13 p.
Proof. exact (EQ_MP (@lem7048787 p) (@lem7048786 p)). Qed.
Lemma lem7048789 (p : nat) (f : nat -> nat) : term27 p f.
Proof. exact (@lem7048788 p f). Qed.
Lemma lem7048790 (p : nat) (f : nat -> nat) : (term27 p f) = (term9 p f).
Proof. exact (eq_refl (term27 p f)). Qed.
Lemma lem7048791 (p : nat) (f : nat -> nat) : term9 p f.
Proof. exact (EQ_MP (@lem7048790 p f) (@lem7048789 p f)). Qed.
Lemma lem7048792 (p : nat) (f : nat -> nat) (m : nat) : term28 p f m.
Proof. exact (@lem7048791 p f m). Qed.
Lemma lem7048793 (m : nat) (p : nat) (f : nat -> nat) : (term28 p f m) = (term5 m p f).
Proof. exact (eq_refl (term28 p f m)). Qed.
Lemma lem7048794 (m : nat) (p : nat) (f : nat -> nat) : term5 m p f.
Proof. exact (EQ_MP (@lem7048793 m p f) (@lem7048792 p f m)). Qed.
Lemma lem7048795 (m : nat) (p : nat) (f : nat -> nat) (n : nat) : term29 m p f n.
Proof. exact (@lem7048794 m p f n). Qed.
Lemma lem7048796 (m : nat) (n : nat) (p : nat) (f : nat -> nat) : (term29 m p f n) = ((term1 m n f p) = (term0 m n p f)).
Proof. exact (eq_refl (term29 m p f n)). Qed.
Lemma lem7048813 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term30 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7048814 (p : Prop) (q : Prop) (p' : Prop) : term31 p q p'.
Proof. exact (fun q' : Prop => @lem7048813 p q p' q'). Qed.
Lemma lem7048815 (p : Prop) (q : Prop) : term32 p q.
Proof. exact (fun p' : Prop => @lem7048814 p q p'). Qed.
Lemma lem7048816 (n : nat) (f : nat -> nat) (m : nat) : term33 n f m.
Proof. exact (@lem7048815 (Peano.le m n) ((term34 m n f) = (term35 n f m))). Qed.
Lemma lem7048817 (n : nat) (f : nat -> nat) (m : nat) (p' : Prop) : term36 n f m p'.
Proof. exact (@lem7048816 n f m p'). Qed.
Lemma lem7048818 (n : nat) (f : nat -> nat) (m : nat) (p' : Prop) : (term36 n f m p') = (term37 n f m p').
Proof. exact (eq_refl (term36 n f m p')). Qed.
Lemma lem7048819 (n : nat) (f : nat -> nat) (m : nat) (p' : Prop) : term37 n f m p'.
Proof. exact (EQ_MP (@lem7048818 n f m p') (@lem7048817 n f m p')). Qed.
Lemma lem7048820 (n : nat) (f : nat -> nat) (m : nat) (p' : Prop) (q' : Prop) : term38 n f m p' q'.
Proof. exact (@lem7048819 n f m p' q'). Qed.
Lemma lem7048821 (n : nat) (f : nat -> nat) (m : nat) (p' : Prop) (q' : Prop) : (term38 n f m p' q') = (term39 n f m p' q').
Proof. exact (eq_refl (term38 n f m p' q')). Qed.
Lemma lem7048822 (n : nat) (f : nat -> nat) (m : nat) (p' : Prop) (q' : Prop) : term39 n f m p' q'.
Proof. exact (EQ_MP (@lem7048821 n f m p' q') (@lem7048820 n f m p' q')). Qed.
Lemma lem7048823 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem7048824 (f : nat -> nat) (m : nat) (n : nat) (q' : Prop) : term40 f m n q'.
Proof. exact (@lem7048822 n f m (Peano.le m n) q'). Qed.
Lemma lem7048825 (f : nat -> nat) (m : nat) (n : nat) (q' : Prop) : term41 f m n q'.
Proof. exact (@lem7048824 f m n q' (@lem7048823 m n)). Qed.
Lemma lem7048826 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem7048827 (m : nat) (n : nat) : (Peano.le m n) = ((Peano.le m n) = True).
Proof. exact (@lem7 (Peano.le m n)). Qed.
Lemma lem7048832 (m : nat) (n : nat) (p : nat) (f : nat -> nat) : (term1 m n f p) = (term0 m n p f).
Proof. exact (EQ_MP (@lem7048796 m n p f) (@lem7048795 m p f n)). Qed.
Lemma lem7048833 (n : nat) (m : nat) (f : nat -> nat) : (term35 n f m) = (term42 n m f).
Proof. exact (@lem7048832 (NUMERAL 0) (Nat.sub n m) m f). Qed.
Lemma lem7048835 (n : nat) : (term25 n) = n.
Proof. exact (EQ_MP (@lem7048784 n) (@lem7048783 n)). Qed.
Lemma lem7048836 (m : nat) : (term25 m) = m.
Proof. exact (@lem7048835 m). Qed.
Lemma lem7048837 : dotdot = dotdot.
Proof. exact (eq_refl dotdot). Qed.
Lemma lem7048838 (m : nat) : (term43 m) = (dotdot m).
Proof. exact (MK_COMB (@lem7048837) (@lem7048836 m)). Qed.
Lemma lem7048840 (n : nat) (m : nat) : term21 n m.
Proof. exact (fun h0 : Peano.le n m => @lem7048756 n m h0). Qed.
Lemma lem7048841 (m : nat) (n : nat) : term21 m n.
Proof. exact (@lem7048840 m n). Qed.
Lemma lem7048843 (m : nat) (n : nat) (h1 : Peano.le m n) : (Peano.le m n) = True.
Proof. exact (EQ_MP (@lem7048827 m n) (@lem7048826 m n h1)). Qed.
Lemma lem7048844 (m : nat) (n : nat) (h1 : Peano.le m n) : True = (Peano.le m n).
Proof. exact (SYM (@lem7048843 m n h1)). Qed.
Lemma lem7048845 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (EQ_MP (@lem7048844 m n h1) (@lem0)). Qed.
Lemma lem7048846 (m : nat) (n : nat) (h1 : Peano.le m n) : (term22 n m) = n.
Proof. exact (@lem7048841 m n (@lem7048845 m n h1)). Qed.
Lemma lem7048847 (m : nat) (n : nat) (h1 : Peano.le m n) : (term44 n m) = (dotdot m n).
Proof. exact (MK_COMB (@lem7048838 m) (@lem7048846 m n h1)). Qed.
Lemma lem7048848 : (@nsum nat) = (@nsum nat).
Proof. exact (eq_refl (@nsum nat)). Qed.
Lemma lem7048849 (m : nat) (n : nat) (h1 : Peano.le m n) : (term45 n m) = (term46 m n).
Proof. exact (MK_COMB (@lem7048848) (@lem7048847 m n h1)). Qed.
Lemma lem7048850 (f : nat -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7048851 (f : nat -> nat) (m : nat) (n : nat) (h1 : Peano.le m n) : (term42 n m f) = (term34 m n f).
Proof. exact (MK_COMB (@lem7048849 m n h1) (@lem7048850 f)). Qed.
Lemma lem7048852 (f : nat -> nat) (m : nat) (n : nat) (h1 : Peano.le m n) : (term35 n f m) = (term34 m n f).
Proof. exact (TRANS (@lem7048833 n m f) (@lem7048851 f m n h1)). Qed.
Lemma lem7048853 (m : nat) (n : nat) (f : nat -> nat) : (term47 m n f) = (term47 m n f).
Proof. exact (eq_refl (term47 m n f)). Qed.
Lemma lem7048854 (f : nat -> nat) (m : nat) (n : nat) (h1 : Peano.le m n) : ((term34 m n f) = (term35 n f m)) = ((term34 m n f) = (term34 m n f)).
Proof. exact (MK_COMB (@lem7048853 m n f) (@lem7048852 f m n h1)). Qed.
Lemma lem7048856 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7048857 (x : nat) : (x = x) = True.
Proof. exact (@lem7048856 nat x). Qed.
Lemma lem7048858 (m : nat) (n : nat) (f : nat -> nat) : ((term34 m n f) = (term34 m n f)) = True.
Proof. exact (@lem7048857 (term34 m n f)). Qed.
Lemma lem7048859 (f : nat -> nat) (m : nat) (n : nat) (h1 : Peano.le m n) : ((term34 m n f) = (term35 n f m)) = True.
Proof. exact (TRANS (@lem7048854 f m n h1) (@lem7048858 m n f)). Qed.
Lemma lem7048860 (n : nat) (f : nat -> nat) (m : nat) : term48 n f m.
Proof. exact (fun h0 : Peano.le m n => @lem7048859 f m n h0). Qed.
Lemma lem7048861 (f : nat -> nat) (m : nat) (n : nat) : term49 f m n.
Proof. exact (@lem7048825 f m n True). Qed.
Lemma lem7048862 (f : nat -> nat) (m : nat) (n : nat) : (term50 n f m) = (term51 m n).
Proof. exact (@lem7048861 f m n (@lem7048860 n f m)). Qed.
Lemma lem7048864 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7048865 (m : nat) (n : nat) : (term51 m n) = True.
Proof. exact (@lem7048864 (Peano.le m n)). Qed.
Lemma lem7048866 (n : nat) (f : nat -> nat) (m : nat) : (term50 n f m) = True.
Proof. exact (TRANS (@lem7048862 f m n) (@lem7048865 m n)). Qed.
Lemma lem7048867 (f : nat -> nat) (m : nat) : (term52 f m) = term53.
Proof. exact (fun_ext (fun n : nat => @lem7048866 n f m)). Qed.
Lemma lem7048868 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7048869 (f : nat -> nat) (m : nat) : (term54 f m) = term55.
Proof. exact (MK_COMB (@lem7048868) (@lem7048867 f m)). Qed.
Lemma lem7048871 {A : Type'} (t : Prop) : (term56 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7048872 (t : Prop) : (term57 t) = t.
Proof. exact (@lem7048871 nat t). Qed.
Lemma lem7048873 : term55 = True.
Proof. exact (@lem7048872 True). Qed.
Lemma lem7048874 (f : nat -> nat) (m : nat) : (term54 f m) = True.
Proof. exact (TRANS (@lem7048869 f m) (@lem7048873)). Qed.
Lemma lem7048875 (f : nat -> nat) : (term58 f) = term53.
Proof. exact (fun_ext (fun m : nat => @lem7048874 f m)). Qed.
Lemma lem7048876 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7048877 (f : nat -> nat) : (term59 f) = term55.
Proof. exact (MK_COMB (@lem7048876) (@lem7048875 f)). Qed.
Lemma lem7048879 {A : Type'} (t : Prop) : (term56 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7048880 (t : Prop) : (term57 t) = t.
Proof. exact (@lem7048879 nat t). Qed.
Lemma lem7048881 : term55 = True.
Proof. exact (@lem7048880 True). Qed.
Lemma lem7048882 (f : nat -> nat) : (term59 f) = True.
Proof. exact (TRANS (@lem7048877 f) (@lem7048881)). Qed.
Lemma lem7048883 : term60 = term61.
Proof. exact (fun_ext (fun f : nat -> nat => @lem7048882 f)). Qed.
Lemma lem7048884 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7048885 : term62 = term63.
Proof. exact (MK_COMB (@lem7048884) (@lem7048883)). Qed.
Lemma lem7048887 {A : Type'} (t : Prop) : (term56 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7048888 (t : Prop) : (term64 t) = t.
Proof. exact (@lem7048887 (nat -> nat) t). Qed.
Lemma lem7048889 : term63 = True.
Proof. exact (@lem7048888 True). Qed.
Lemma lem7048890 : term62 = True.
Proof. exact (TRANS (@lem7048885) (@lem7048889)). Qed.
Lemma lem7048891 : True = term62.
Proof. exact (SYM (@lem7048890)). Qed.
Lemma lem7048892 : term62.
Proof. exact (EQ_MP (@lem7048891) (@lem0)). Qed.
