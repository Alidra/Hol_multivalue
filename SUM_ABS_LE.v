Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_ABS_LE_term_abbrevs.
Require Import SUM_ABS_spec.
Require Import SUM_LE_spec.
Require Import thm0_spec.
Require Import thm1339577_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem7083750 {_132081 : Type'} (h1 : term0 _132081) : term0 _132081.
Proof. exact (h1). Qed.
Lemma lem7083751 {_132081 : Type'} (f : _132081 -> real) (h1 : term0 _132081) : term1 _132081 f.
Proof. exact (@lem7083750 _132081 h1 f). Qed.
Lemma lem7083752 {_132081 : Type'} (f : _132081 -> real) : (term1 _132081 f) = (term2 _132081 f).
Proof. exact (eq_refl (term1 _132081 f)). Qed.
Lemma lem7083753 {_132081 : Type'} (f : _132081 -> real) (h1 : term0 _132081) : term2 _132081 f.
Proof. exact (EQ_MP (@lem7083752 _132081 f) (@lem7083751 _132081 f h1)). Qed.
Lemma lem7083754 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (h1 : term0 _132081) : term3 _132081 f g.
Proof. exact (@lem7083753 _132081 f h1 g). Qed.
Lemma lem7083755 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : (term3 _132081 f g) = (term4 _132081 f g).
Proof. exact (eq_refl (term3 _132081 f g)). Qed.
Lemma lem7083756 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (h1 : term0 _132081) : term4 _132081 f g.
Proof. exact (EQ_MP (@lem7083755 _132081 f g) (@lem7083754 _132081 f g h1)). Qed.
Lemma lem7083757 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (s : _132081 -> Prop) (h1 : term0 _132081) : term5 _132081 f g s.
Proof. exact (@lem7083756 _132081 f g h1 s). Qed.
Lemma lem7083758 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) : (term5 _132081 f g s) = (term6 _132081 f s g).
Proof. exact (eq_refl (term5 _132081 f g s)). Qed.
Lemma lem7083759 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) (h1 : term0 _132081) : term6 _132081 f s g.
Proof. exact (EQ_MP (@lem7083758 _132081 f s g) (@lem7083757 _132081 f g s h1)). Qed.
Lemma lem7083760 {_132081 : Type'} (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term7 _132081 s f g) : term7 _132081 s f g.
Proof. exact (h1). Qed.
Lemma lem7083761 {_132081 : Type'} (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term0 _132081) (h2 : term7 _132081 s f g) : term8 _132081 f s g.
Proof. exact (@lem7083759 _132081 f s g h1 (@lem7083760 _132081 s f g h2)). Qed.
Lemma lem7083762 {_132081 : Type'} (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term7 _132081 s f g) : term9 _132081 f s g.
Proof. exact (fun h0 : term0 _132081 => @lem7083761 _132081 s f g h0 h1). Qed.
Lemma lem7083763 {_132081 : Type'} (h1 : term0 _132081) : term0 _132081.
Proof. exact (h1). Qed.
Lemma lem7083764 {_132081 : Type'} (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term0 _132081) (h2 : term7 _132081 s f g) : term8 _132081 f s g.
Proof. exact (@lem7083762 _132081 s f g h2 (@lem7083763 _132081 h1)). Qed.
Lemma lem7083765 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) (h1 : term0 _132081) : term6 _132081 f s g.
Proof. exact (fun h0 : term7 _132081 s f g => @lem7083764 _132081 s f g h1 h0). Qed.
Lemma lem7083766 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (h1 : term0 _132081) : term10 _132081 f s.
Proof. exact (fun g : _132081 -> real => @lem7083765 _132081 f s g h1). Qed.
Lemma lem7083767 {_132081 : Type'} (f : _132081 -> real) (h1 : term0 _132081) : term11 _132081 f.
Proof. exact (fun s : _132081 -> Prop => @lem7083766 _132081 f s h1). Qed.
Lemma lem7083768 {_132081 : Type'} (h1 : term0 _132081) : term12 _132081.
Proof. exact (fun f : _132081 -> real => @lem7083767 _132081 f h1). Qed.
Lemma lem7083769 {_132081 : Type'} : term13 _132081.
Proof. exact (fun h0 : term0 _132081 => @lem7083768 _132081 h0). Qed.
Lemma lem7083770 {_132081 : Type'} : term12 _132081.
Proof. exact (@lem7083769 _132081 (@lem7071845 _132081)). Qed.
Lemma lem7083771 {_132081 : Type'} (f : _132081 -> real) : term14 _132081 f.
Proof. exact (@lem7083770 _132081 f). Qed.
Lemma lem7083772 {_132081 : Type'} (f : _132081 -> real) : (term14 _132081 f) = (term11 _132081 f).
Proof. exact (eq_refl (term14 _132081 f)). Qed.
Lemma lem7083773 {_132081 : Type'} (f : _132081 -> real) : term11 _132081 f.
Proof. exact (EQ_MP (@lem7083772 _132081 f) (@lem7083771 _132081 f)). Qed.
Lemma lem7083774 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) : term15 _132081 f s.
Proof. exact (@lem7083773 _132081 f s). Qed.
Lemma lem7083775 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) : (term15 _132081 f s) = (term10 _132081 f s).
Proof. exact (eq_refl (term15 _132081 f s)). Qed.
Lemma lem7083776 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) : term10 _132081 f s.
Proof. exact (EQ_MP (@lem7083775 _132081 f s) (@lem7083774 _132081 f s)). Qed.
Lemma lem7083777 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) : term16 _132081 f s g.
Proof. exact (@lem7083776 _132081 f s g). Qed.
Lemma lem7083778 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) : (term16 _132081 f s g) = (term6 _132081 f s g).
Proof. exact (eq_refl (term16 _132081 f s g)). Qed.
Lemma lem7083780 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem7083781 (x : real) (h1 : term17) : term18 x.
Proof. exact (@lem7083780 h1 x). Qed.
Lemma lem7083782 (x : real) : (term18 x) = (term19 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem7083783 (x : real) (h1 : term17) : term19 x.
Proof. exact (EQ_MP (@lem7083782 x) (@lem7083781 x h1)). Qed.
Lemma lem7083784 (x : real) (y : real) (h1 : term17) : term20 x y.
Proof. exact (@lem7083783 x h1 y). Qed.
Lemma lem7083785 (y : real) (x : real) : (term20 x y) = (term21 y x).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem7083786 (y : real) (x : real) (h1 : term17) : term21 y x.
Proof. exact (EQ_MP (@lem7083785 y x) (@lem7083784 x y h1)). Qed.
Lemma lem7083787 (y : real) (x : real) (z : real) (h1 : term17) : term22 y x z.
Proof. exact (@lem7083786 y x h1 z). Qed.
Lemma lem7083788 (y : real) (x : real) (z : real) : (term22 y x z) = (term23 y x z).
Proof. exact (eq_refl (term22 y x z)). Qed.
Lemma lem7083789 (y : real) (x : real) (z : real) (h1 : term17) : term23 y x z.
Proof. exact (EQ_MP (@lem7083788 y x z) (@lem7083787 y x z h1)). Qed.
Lemma lem7083790 (x : real) (y : real) (z : real) (h1 : term24 x y z) : term24 x y z.
Proof. exact (h1). Qed.
Lemma lem7083791 (x : real) (y : real) (z : real) (h1 : term17) (h2 : term24 x y z) : real_le x z.
Proof. exact (@lem7083789 y x z h1 (@lem7083790 x y z h2)). Qed.
Lemma lem7083792 (x : real) (y : real) (z : real) (h1 : term24 x y z) : term25 x z.
Proof. exact (fun h0 : term17 => @lem7083791 x y z h0 h1). Qed.
Lemma lem7083793 (x : real) (z : real) (h1 : term26 x z) : term26 x z.
Proof. exact (h1). Qed.
Lemma lem7083794 (x : real) (z : real) (h1 : term26 x z) : term25 x z.
Proof. exact (ex_elim (@lem7083793 x z h1) (fun y : real => fun h0 : term27 x z y => @lem7083792 x y z h0)). Qed.
Lemma lem7083795 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem7083796 (x : real) (z : real) (h1 : term17) (h2 : term26 x z) : real_le x z.
Proof. exact (@lem7083794 x z h2 (@lem7083795 h1)). Qed.
Lemma lem7083797 (x : real) (z : real) (h1 : term17) : term28 x z.
Proof. exact (fun h0 : term26 x z => @lem7083796 x z h1 h0). Qed.
Lemma lem7083798 (x : real) (h1 : term17) : term29 x.
Proof. exact (fun z : real => @lem7083797 x z h1). Qed.
Lemma lem7083799 (h1 : term17) : term30.
Proof. exact (fun x : real => @lem7083798 x h1). Qed.
Lemma lem7083800 : term31.
Proof. exact (fun h0 : term17 => @lem7083799 h0). Qed.
Lemma lem7083801 : term30.
Proof. exact (@lem7083800 (@lem1339577)). Qed.
Lemma lem7083802 (x : real) : term32 x.
Proof. exact (@lem7083801 x). Qed.
Lemma lem7083803 (x : real) : (term32 x) = (term29 x).
Proof. exact (eq_refl (term32 x)). Qed.
Lemma lem7083804 (x : real) : term29 x.
Proof. exact (EQ_MP (@lem7083803 x) (@lem7083802 x)). Qed.
Lemma lem7083805 (x : real) (z : real) : term33 x z.
Proof. exact (@lem7083804 x z). Qed.
Lemma lem7083806 (x : real) (z : real) : (term33 x z) = (term28 x z).
Proof. exact (eq_refl (term33 x z)). Qed.
Lemma lem7083808 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term34 A s f g) : term34 A s f g.
Proof. exact (h1). Qed.
Lemma lem7083809 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term35 A s f g) : term35 A s f g.
Proof. exact (h1). Qed.
Lemma lem7083810 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7083812 (x : real) (z : real) : term28 x z.
Proof. exact (EQ_MP (@lem7083806 x z) (@lem7083805 x z)). Qed.
Lemma lem7083813 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : term36 A f s g.
Proof. exact (@lem7083812 (term37 A s f) (@sum A s g)). Qed.
Lemma lem7083814 {_132408 : Type'} (f : _132408 -> real) : term38 _132408 f.
Proof. exact (@lem7083749 _132408 f). Qed.
Lemma lem7083815 {_132408 : Type'} (f : _132408 -> real) : (term38 _132408 f) = (term39 _132408 f).
Proof. exact (eq_refl (term38 _132408 f)). Qed.
Lemma lem7083816 {_132408 : Type'} (f : _132408 -> real) : term39 _132408 f.
Proof. exact (EQ_MP (@lem7083815 _132408 f) (@lem7083814 _132408 f)). Qed.
Lemma lem7083817 {_132408 : Type'} (f : _132408 -> real) (s : _132408 -> Prop) : term40 _132408 f s.
Proof. exact (@lem7083816 _132408 f s). Qed.
Lemma lem7083818 {_132408 : Type'} (s : _132408 -> Prop) (f : _132408 -> real) : (term40 _132408 f s) = (term41 _132408 s f).
Proof. exact (eq_refl (term40 _132408 f s)). Qed.
Lemma lem7083819 {_132408 : Type'} (s : _132408 -> Prop) (f : _132408 -> real) : term41 _132408 s f.
Proof. exact (EQ_MP (@lem7083818 _132408 s f) (@lem7083817 _132408 f s)). Qed.
Lemma lem7083820 {_132408 : Type'} (s : _132408 -> Prop) (h1 : @FINITE _132408 s) : @FINITE _132408 s.
Proof. exact (h1). Qed.
Lemma lem7083821 {_132408 : Type'} (f : _132408 -> real) (s : _132408 -> Prop) (h1 : @FINITE _132408 s) : term42 _132408 s f.
Proof. exact (@lem7083819 _132408 s f (@lem7083820 _132408 s h1)). Qed.
Lemma lem7083822 {_132408 : Type'} (s : _132408 -> Prop) (f : _132408 -> real) : (term42 _132408 s f) = ((term42 _132408 s f) = True).
Proof. exact (@lem7 (term42 _132408 s f)). Qed.
Lemma lem7083823 {_132408 : Type'} (f : _132408 -> real) (s : _132408 -> Prop) (h1 : @FINITE _132408 s) : (term42 _132408 s f) = True.
Proof. exact (EQ_MP (@lem7083822 _132408 s f) (@lem7083821 _132408 f s h1)). Qed.
Lemma lem7083829 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem7083846 {_132408 : Type'} (s : _132408 -> Prop) (f : _132408 -> real) : term43 _132408 s f.
Proof. exact (fun h0 : @FINITE _132408 s => @lem7083823 _132408 f s h0). Qed.
Lemma lem7083847 {A : Type'} (s : A -> Prop) (f : A -> real) : term43 A s f.
Proof. exact (@lem7083846 A s f). Qed.
Lemma lem7083849 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem7083829 A s) (@lem7083810 A s h1)). Qed.
Lemma lem7083850 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : True = (@FINITE A s).
Proof. exact (SYM (@lem7083849 A s h1)). Qed.
Lemma lem7083851 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem7083850 A s h1) (@lem0)). Qed.
Lemma lem7083852 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : @FINITE A s) : (term42 A s f) = True.
Proof. exact (@lem7083847 A s f (@lem7083851 A s h1)). Qed.
Lemma lem7083853 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7083854 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : @FINITE A s) : (term44 A s f) = (and True).
Proof. exact (MK_COMB (@lem7083853) (@lem7083852 A f s h1)). Qed.
Lemma lem7083855 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term45 A f s g) = (term45 A f s g).
Proof. exact (eq_refl (term45 A f s g)). Qed.
Lemma lem7083856 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (h1 : @FINITE A s) : (term46 A f s g) = (term47 A f s g).
Proof. exact (MK_COMB (@lem7083854 A f s h1) (@lem7083855 A f s g)). Qed.
Lemma lem7083858 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7083859 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term47 A f s g) = (term45 A f s g).
Proof. exact (@lem7083858 (term45 A f s g)). Qed.
Lemma lem7083860 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (h1 : @FINITE A s) : (term46 A f s g) = (term45 A f s g).
Proof. exact (TRANS (@lem7083856 A f g s h1) (@lem7083859 A f s g)). Qed.
Lemma lem7083861 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (h1 : @FINITE A s) : (term45 A f s g) = (term46 A f s g).
Proof. exact (SYM (@lem7083860 A f g s h1)). Qed.
Lemma lem7083863 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) : term6 _132081 f s g.
Proof. exact (EQ_MP (@lem7083778 _132081 f s g) (@lem7083777 _132081 f s g)). Qed.
Lemma lem7083864 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : term6 A f s g.
Proof. exact (@lem7083863 A f s g). Qed.
Lemma lem7083865 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : term48 A f s g.
Proof. exact (@lem7083864 A (term49 A f) s g). Qed.
Lemma lem7083866 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem7083868 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term35 A s f g) : term50 A s f g x.
Proof. exact (@lem7083809 A s f g h1 x). Qed.
Lemma lem7083869 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (x : A) : (term50 A s f g x) = (term51 A s f g x).
Proof. exact (eq_refl (term50 A s f g x)). Qed.
Lemma lem7083870 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term35 A s f g) : term51 A s f g x.
Proof. exact (EQ_MP (@lem7083869 A s f g x) (@lem7083868 A x s f g h1)). Qed.
Lemma lem7083871 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (x : A) : (term51 A s f g x) = ((term51 A s f g x) = True).
Proof. exact (@lem7 (term51 A s f g x)). Qed.
Lemma lem7083876 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem7083866 A s) (@lem7083810 A s h1)). Qed.
Lemma lem7083877 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7083878 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term52 A s) = (and True).
Proof. exact (MK_COMB (@lem7083877) (@lem7083876 A s h1)). Qed.
Lemma lem7083886 {A B : Type'} (f : A -> B) (y : A) : (term53 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7083887 {A : Type'} (f : A -> real) (y : A) : (term54 A f y) = (f y).
Proof. exact (@lem7083886 A real f y). Qed.
Lemma lem7083888 {A : Type'} (f : A -> real) (x : A) : (term55 A f x) = (term56 A f x).
Proof. exact (@lem7083887 A (term49 A f) x). Qed.
Lemma lem7083889 {A : Type'} (f : A -> real) (x : A) : (term56 A f x) = (term57 A f x).
Proof. exact (eq_refl (term56 A f x)). Qed.
Lemma lem7083890 {A : Type'} (f : A -> real) : (term58 A f) = (term49 A f).
Proof. exact (fun_ext (fun x : A => @lem7083889 A f x)). Qed.
Lemma lem7083891 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7083892 {A : Type'} (f : A -> real) (x : A) : (term55 A f x) = (term56 A f x).
Proof. exact (MK_COMB (@lem7083890 A f) (@lem7083891 A x)). Qed.
Lemma lem7083893 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7083894 {A : Type'} (f : A -> real) (x : A) : (term59 A f x) = (term60 A f x).
Proof. exact (MK_COMB (@lem7083893) (@lem7083892 A f x)). Qed.
Lemma lem7083895 {A : Type'} (f : A -> real) (x : A) : (term56 A f x) = (term57 A f x).
Proof. exact (eq_refl (term56 A f x)). Qed.
Lemma lem7083896 {A : Type'} (f : A -> real) (x : A) : ((term55 A f x) = (term56 A f x)) = ((term56 A f x) = (term57 A f x)).
Proof. exact (MK_COMB (@lem7083894 A f x) (@lem7083895 A f x)). Qed.
Lemma lem7083897 {A : Type'} (f : A -> real) (x : A) : (term56 A f x) = (term57 A f x).
Proof. exact (EQ_MP (@lem7083896 A f x) (@lem7083888 A f x)). Qed.
Lemma lem7083898 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7083899 {A : Type'} (f : A -> real) (x : A) : (term61 A f x) = (term62 A f x).
Proof. exact (MK_COMB (@lem7083898) (@lem7083897 A f x)). Qed.
Lemma lem7083900 {A : Type'} (g : A -> real) (x : A) : (g x) = (g x).
Proof. exact (eq_refl (g x)). Qed.
Lemma lem7083901 {A : Type'} (f : A -> real) (g : A -> real) (x : A) : (term63 A f g x) = (term64 A f g x).
Proof. exact (MK_COMB (@lem7083899 A f x) (@lem7083900 A g x)). Qed.
Lemma lem7083902 {A : Type'} (x : A) (s : A -> Prop) : (term65 A x s) = (term65 A x s).
Proof. exact (eq_refl (term65 A x s)). Qed.
Lemma lem7083903 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (x : A) : (term66 A s f g x) = (term51 A s f g x).
Proof. exact (MK_COMB (@lem7083902 A x s) (@lem7083901 A f g x)). Qed.
Lemma lem7083905 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term35 A s f g) : (term51 A s f g x) = True.
Proof. exact (EQ_MP (@lem7083871 A s f g x) (@lem7083870 A x s f g h1)). Qed.
Lemma lem7083906 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term35 A s f g) : (term51 A s f g x) = True.
Proof. exact (@lem7083905 A x s f g h1). Qed.
Lemma lem7083907 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term35 A s f g) : (term66 A s f g x) = True.
Proof. exact (TRANS (@lem7083903 A s f g x) (@lem7083906 A x s f g h1)). Qed.
Lemma lem7083908 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term35 A s f g) : (term67 A s f g) = (term68 A).
Proof. exact (fun_ext (fun x : A => @lem7083907 A x s f g h1)). Qed.
Lemma lem7083909 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7083910 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term35 A s f g) : (term69 A s f g) = (term70 A).
Proof. exact (MK_COMB (@lem7083909 A) (@lem7083908 A s f g h1)). Qed.
Lemma lem7083912 {A : Type'} (t : Prop) : (term71 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7083913 {A : Type'} (t : Prop) : (term71 A t) = t.
Proof. exact (@lem7083912 A t). Qed.
Lemma lem7083914 {A : Type'} : (term70 A) = True.
Proof. exact (@lem7083913 A True). Qed.
Lemma lem7083915 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term35 A s f g) : (term69 A s f g) = True.
Proof. exact (TRANS (@lem7083910 A s f g h1) (@lem7083914 A)). Qed.
Lemma lem7083916 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (h1 : term35 A s f g) (h2 : @FINITE A s) : (term72 A s f g) = (True /\ True).
Proof. exact (MK_COMB (@lem7083878 A s h2) (@lem7083915 A s f g h1)). Qed.
Lemma lem7083918 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7083919 : (True /\ True) = True.
Proof. exact (@lem7083918 True). Qed.
Lemma lem7083920 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (h1 : term35 A s f g) (h2 : @FINITE A s) : (term72 A s f g) = True.
Proof. exact (TRANS (@lem7083916 A f g s h1 h2) (@lem7083919)). Qed.
Lemma lem7083921 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (h1 : term35 A s f g) (h2 : @FINITE A s) : True = (term72 A s f g).
Proof. exact (SYM (@lem7083920 A f g s h1 h2)). Qed.
Lemma lem7083922 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (h1 : term35 A s f g) (h2 : @FINITE A s) : term72 A s f g.
Proof. exact (EQ_MP (@lem7083921 A f g s h1 h2) (@lem0)). Qed.
Lemma lem7083923 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (h1 : term35 A s f g) (h2 : @FINITE A s) : term45 A f s g.
Proof. exact (@lem7083865 A f s g (@lem7083922 A f g s h1 h2)). Qed.
Lemma lem7083924 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (h1 : term35 A s f g) (h2 : @FINITE A s) : term46 A f s g.
Proof. exact (EQ_MP (@lem7083861 A f g s h2) (@lem7083923 A f g s h1 h2)). Qed.
Lemma lem7083925 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (h1 : term35 A s f g) (h2 : @FINITE A s) : term73 A f s g.
Proof. exact (ex_intro (term74 A f s g) (term75 A s f) (@lem7083924 A f g s h1 h2)). Qed.
Lemma lem7083926 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (h1 : term35 A s f g) (h2 : @FINITE A s) : term76 A f s g.
Proof. exact (@lem7083813 A f s g (@lem7083925 A f g s h1 h2)). Qed.
Lemma lem7083927 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term34 A s f g) : term35 A s f g.
Proof. exact (proj2 (@lem7083808 A s f g h1)). Qed.
Lemma lem7083928 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term34 A s f g) : @FINITE A s.
Proof. exact (proj1 (@lem7083808 A s f g h1)). Qed.
Lemma lem7083929 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (h1 : term35 A s f g) (h2 : @FINITE A s) : (term35 A s f g) = (term76 A f s g).
Proof. exact (prop_ext (fun h3 : term35 A s f g => @lem7083926 A f g s h1 h2) (fun h3 : term76 A f s g => @lem7083809 A s f g h1)). Qed.
Lemma lem7083930 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (h1 : term35 A s f g) (h2 : @FINITE A s) : term76 A f s g.
Proof. exact (EQ_MP (@lem7083929 A f g s h1 h2) (@lem7083809 A s f g h1)). Qed.
Lemma lem7083931 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (h1 : term35 A s f g) (h2 : @FINITE A s) : (@FINITE A s) = (term76 A f s g).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem7083930 A f g s h1 h2) (fun h3 : term76 A f s g => @lem7083810 A s h2)). Qed.
Lemma lem7083932 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (h1 : term35 A s f g) (h2 : @FINITE A s) : term76 A f s g.
Proof. exact (EQ_MP (@lem7083931 A f g s h1 h2) (@lem7083810 A s h2)). Qed.
Lemma lem7083933 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : @FINITE A s) (h2 : term34 A s f g) : (term35 A s f g) = (term76 A f s g).
Proof. exact (prop_ext (fun h3 : term35 A s f g => @lem7083932 A f g s h3 h1) (fun h3 : term76 A f s g => @lem7083927 A s f g h2)). Qed.
Lemma lem7083934 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : @FINITE A s) (h2 : term34 A s f g) : term76 A f s g.
Proof. exact (EQ_MP (@lem7083933 A s f g h1 h2) (@lem7083927 A s f g h2)). Qed.
Lemma lem7083935 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term34 A s f g) : (@FINITE A s) = (term76 A f s g).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem7083934 A s f g h2 h1) (fun h2 : term76 A f s g => @lem7083928 A s f g h1)). Qed.
Lemma lem7083936 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term34 A s f g) : term76 A f s g.
Proof. exact (EQ_MP (@lem7083935 A s f g h1) (@lem7083928 A s f g h1)). Qed.
Lemma lem7083937 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : term77 A f s g.
Proof. exact (fun h0 : term34 A s f g => @lem7083936 A s f g h0). Qed.
Lemma lem7083942 {A : Type'} (f : A -> real) (g : A -> real) : term78 A f g.
Proof. exact (fun s : A -> Prop => @lem7083937 A f s g). Qed.
Lemma lem7083947 {A : Type'} (f : A -> real) : term79 A f.
Proof. exact (fun g : A -> real => @lem7083942 A f g). Qed.
Lemma lem7083952 {A : Type'} : term80 A.
Proof. exact (fun f : A -> real => @lem7083947 A f). Qed.
