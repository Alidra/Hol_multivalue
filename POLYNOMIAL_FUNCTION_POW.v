Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import POLYNOMIAL_FUNCTION_POW_term_abbrevs.
Require Import POLYNOMIAL_FUNCTION_CONST_spec.
Require Import POLYNOMIAL_FUNCTION_MUL_spec.
Require Import RIGHT_FORALL_IMP_THM_spec.
Require Import thm0_spec.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Require Import thm1344313_spec.
Require Import thm1344314_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem7581712 {A : Type'} (P : Prop) : term0 A P.
Proof. exact (@lem6534 A P). Qed.
Lemma lem7581713 {A : Type'} (P : Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem7581714 {A : Type'} (P : Prop) : term1 A P.
Proof. exact (EQ_MP (@lem7581713 A P) (@lem7581712 A P)). Qed.
Lemma lem7581715 {A : Type'} (P : Prop) (Q : A -> Prop) : term2 A P Q.
Proof. exact (@lem7581714 A P Q). Qed.
Lemma lem7581716 {A : Type'} (P : Prop) (Q : A -> Prop) : (term2 A P Q) = ((term3 A P Q) = (term4 A P Q)).
Proof. exact (eq_refl (term2 A P Q)). Qed.
Lemma lem7581723 {A : Type'} (P : Prop) (Q : A -> Prop) : (term3 A P Q) = (term4 A P Q).
Proof. exact (EQ_MP (@lem7581716 A P Q) (@lem7581715 A P Q)). Qed.
Lemma lem7581724 (P : Prop) (Q : nat -> Prop) : (term5 P Q) = (term6 P Q).
Proof. exact (@lem7581723 nat P Q). Qed.
Lemma lem7581725 (p : real -> real) : (term7 p) = (term8 p).
Proof. exact (@lem7581724 (polynomial_function p) (term9 p)). Qed.
Lemma lem7581726 (p : real -> real) (n : nat) : (term10 p n) = (term11 p n).
Proof. exact (eq_refl (term10 p n)). Qed.
Lemma lem7581727 (p : real -> real) : (term12 p) = (term12 p).
Proof. exact (eq_refl (term12 p)). Qed.
Lemma lem7581728 (p : real -> real) (n : nat) : (term13 p n) = (term14 p n).
Proof. exact (MK_COMB (@lem7581727 p) (@lem7581726 p n)). Qed.
Lemma lem7581729 (p : real -> real) : (term15 p) = (term16 p).
Proof. exact (fun_ext (fun n : nat => @lem7581728 p n)). Qed.
Lemma lem7581730 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7581731 (p : real -> real) : (term7 p) = (term17 p).
Proof. exact (MK_COMB (@lem7581730) (@lem7581729 p)). Qed.
Lemma lem7581732 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7581733 (p : real -> real) : (term18 p) = (term19 p).
Proof. exact (MK_COMB (@lem7581732) (@lem7581731 p)). Qed.
Lemma lem7581734 (p : real -> real) (n : nat) : (term10 p n) = (term11 p n).
Proof. exact (eq_refl (term10 p n)). Qed.
Lemma lem7581735 (p : real -> real) : (term20 p) = (term9 p).
Proof. exact (fun_ext (fun n : nat => @lem7581734 p n)). Qed.
Lemma lem7581736 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7581737 (p : real -> real) : (term21 p) = (term22 p).
Proof. exact (MK_COMB (@lem7581736) (@lem7581735 p)). Qed.
Lemma lem7581738 (p : real -> real) : (term12 p) = (term12 p).
Proof. exact (eq_refl (term12 p)). Qed.
Lemma lem7581739 (p : real -> real) : (term8 p) = (term23 p).
Proof. exact (MK_COMB (@lem7581738 p) (@lem7581737 p)). Qed.
Lemma lem7581740 (p : real -> real) : ((term7 p) = (term8 p)) = ((term17 p) = (term23 p)).
Proof. exact (MK_COMB (@lem7581733 p) (@lem7581739 p)). Qed.
Lemma lem7581741 (p : real -> real) : (term17 p) = (term23 p).
Proof. exact (EQ_MP (@lem7581740 p) (@lem7581725 p)). Qed.
Lemma lem7581748 : term24 = term25.
Proof. exact (fun_ext (fun p : real -> real => @lem7581741 p)). Qed.
Lemma lem7581749 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7581750 : term26 = term27.
Proof. exact (MK_COMB (@lem7581749) (@lem7581748)). Qed.
Lemma lem7581775 : term27 = term26.
Proof. exact (SYM (@lem7581750)). Qed.
Lemma lem7581776 (p : real -> real) (h1 : polynomial_function p) : polynomial_function p.
Proof. exact (h1). Qed.
Lemma lem7581778 (P : nat -> Prop) : term28 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem7581779 (p : real -> real) : term29 p.
Proof. exact (@lem7581778 (term9 p)). Qed.
Lemma lem7581780 (p : real -> real) : (term30 p) = (term31 p).
Proof. exact (eq_refl (term30 p)). Qed.
Lemma lem7581781 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7581782 (p : real -> real) : (term32 p) = (term33 p).
Proof. exact (MK_COMB (@lem7581781) (@lem7581780 p)). Qed.
Lemma lem7581783 (p : real -> real) (n : nat) : (term10 p n) = (term11 p n).
Proof. exact (eq_refl (term10 p n)). Qed.
Lemma lem7581784 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7581785 (p : real -> real) (n : nat) : (term34 p n) = (term35 p n).
Proof. exact (MK_COMB (@lem7581784) (@lem7581783 p n)). Qed.
Lemma lem7581786 (p : real -> real) (n : nat) : (term36 p n) = (term37 p n).
Proof. exact (eq_refl (term36 p n)). Qed.
Lemma lem7581787 (p : real -> real) (n : nat) : (term38 p n) = (term39 p n).
Proof. exact (MK_COMB (@lem7581785 p n) (@lem7581786 p n)). Qed.
Lemma lem7581788 (p : real -> real) : (term40 p) = (term41 p).
Proof. exact (fun_ext (fun n : nat => @lem7581787 p n)). Qed.
Lemma lem7581789 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7581790 (p : real -> real) : (term42 p) = (term43 p).
Proof. exact (MK_COMB (@lem7581789) (@lem7581788 p)). Qed.
Lemma lem7581791 (p : real -> real) : (term44 p) = (term45 p).
Proof. exact (MK_COMB (@lem7581782 p) (@lem7581790 p)). Qed.
Lemma lem7581792 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7581793 (p : real -> real) : (term46 p) = (term47 p).
Proof. exact (MK_COMB (@lem7581792) (@lem7581791 p)). Qed.
Lemma lem7581794 (p : real -> real) (n : nat) : (term10 p n) = (term11 p n).
Proof. exact (eq_refl (term10 p n)). Qed.
Lemma lem7581795 (p : real -> real) : (term20 p) = (term9 p).
Proof. exact (fun_ext (fun n : nat => @lem7581794 p n)). Qed.
Lemma lem7581796 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7581797 (p : real -> real) : (term21 p) = (term22 p).
Proof. exact (MK_COMB (@lem7581796) (@lem7581795 p)). Qed.
Lemma lem7581798 (p : real -> real) : (term29 p) = (term48 p).
Proof. exact (MK_COMB (@lem7581793 p) (@lem7581797 p)). Qed.
Lemma lem7581799 (p : real -> real) : term48 p.
Proof. exact (EQ_MP (@lem7581798 p) (@lem7581779 p)). Qed.
Lemma lem7581800 (p : real -> real) (n : nat) (h1 : term11 p n) : term11 p n.
Proof. exact (h1). Qed.
Lemma lem7581816 (c : real) : term49 c.
Proof. exact (@lem7553635 c). Qed.
Lemma lem7581817 (c : real) : (term49 c) = (term50 c).
Proof. exact (eq_refl (term49 c)). Qed.
Lemma lem7581818 (c : real) : term50 c.
Proof. exact (EQ_MP (@lem7581817 c) (@lem7581816 c)). Qed.
Lemma lem7581819 (c : real) : (term50 c) = ((term50 c) = True).
Proof. exact (@lem7 (term50 c)). Qed.
Lemma lem7581832 (x : real) : (term51 x) = term52.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem7581833 (p : real -> real) (x : real) : (term53 p x) = term52.
Proof. exact (@lem7581832 (p x)). Qed.
Lemma lem7581834 (p : real -> real) : (term54 p) = term55.
Proof. exact (fun_ext (fun x : real => @lem7581833 p x)). Qed.
Lemma lem7581835 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7581836 (p : real -> real) : (term31 p) = term56.
Proof. exact (MK_COMB (@lem7581835) (@lem7581834 p)). Qed.
Lemma lem7581838 (c : real) : (term50 c) = True.
Proof. exact (EQ_MP (@lem7581819 c) (@lem7581818 c)). Qed.
Lemma lem7581839 : term56 = True.
Proof. exact (@lem7581838 term52). Qed.
Lemma lem7581840 (p : real -> real) : (term31 p) = True.
Proof. exact (TRANS (@lem7581836 p) (@lem7581839)). Qed.
Lemma lem7581841 (p : real -> real) : True = (term31 p).
Proof. exact (SYM (@lem7581840 p)). Qed.
Lemma lem7581842 (p : real -> real) : term31 p.
Proof. exact (EQ_MP (@lem7581841 p) (@lem0)). Qed.
Lemma lem7581843 (p : real -> real) : term57 p.
Proof. exact (@lem7577427 p). Qed.
Lemma lem7581844 (p : real -> real) : (term57 p) = (term58 p).
Proof. exact (eq_refl (term57 p)). Qed.
Lemma lem7581845 (p : real -> real) : term58 p.
Proof. exact (EQ_MP (@lem7581844 p) (@lem7581843 p)). Qed.
Lemma lem7581846 (p : real -> real) (q : real -> real) : term59 p q.
Proof. exact (@lem7581845 p q). Qed.
Lemma lem7581847 (p : real -> real) (q : real -> real) : (term59 p q) = (term60 p q).
Proof. exact (eq_refl (term59 p q)). Qed.
Lemma lem7581848 (p : real -> real) (q : real -> real) : term60 p q.
Proof. exact (EQ_MP (@lem7581847 p q) (@lem7581846 p q)). Qed.
Lemma lem7581849 (p : real -> real) (q : real -> real) (h1 : term61 p q) : term61 p q.
Proof. exact (h1). Qed.
Lemma lem7581850 (p : real -> real) (q : real -> real) (h1 : term61 p q) : term62 p q.
Proof. exact (@lem7581848 p q (@lem7581849 p q h1)). Qed.
Lemma lem7581851 (p : real -> real) (q : real -> real) : (term62 p q) = ((term62 p q) = True).
Proof. exact (@lem7 (term62 p q)). Qed.
Lemma lem7581852 (p : real -> real) (q : real -> real) (h1 : term61 p q) : (term62 p q) = True.
Proof. exact (EQ_MP (@lem7581851 p q) (@lem7581850 p q h1)). Qed.
Lemma lem7581863 (x : real) : term63 x.
Proof. exact (EQ_MP (@lem1344314 x) (@lem1344313 x)). Qed.
Lemma lem7581864 (x : real) (n : nat) : term64 x n.
Proof. exact (@lem7581863 x n). Qed.
Lemma lem7581865 (x : real) (n : nat) : (term64 x n) = ((term65 x n) = (term66 x n)).
Proof. exact (eq_refl (term64 x n)). Qed.
Lemma lem7581868 (p : real -> real) : (polynomial_function p) = ((polynomial_function p) = True).
Proof. exact (@lem7 (polynomial_function p)). Qed.
Lemma lem7581870 (p : real -> real) (n : nat) : (term11 p n) = ((term11 p n) = True).
Proof. exact (@lem7 (term11 p n)). Qed.
Lemma lem7581876 (x : real) (n : nat) : (term65 x n) = (term66 x n).
Proof. exact (EQ_MP (@lem7581865 x n) (@lem7581864 x n)). Qed.
Lemma lem7581877 (p : real -> real) (x : real) (n : nat) : (term67 p x n) = (term68 p x n).
Proof. exact (@lem7581876 (p x) n). Qed.
Lemma lem7581878 (p : real -> real) (n : nat) : (term69 p n) = (term70 p n).
Proof. exact (fun_ext (fun x : real => @lem7581877 p x n)). Qed.
Lemma lem7581879 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7581880 (p : real -> real) (n : nat) : (term37 p n) = (term71 p n).
Proof. exact (MK_COMB (@lem7581879) (@lem7581878 p n)). Qed.
Lemma lem7581882 (p : real -> real) (q : real -> real) : term72 p q.
Proof. exact (fun h0 : term61 p q => @lem7581852 p q h0). Qed.
Lemma lem7581883 (p : real -> real) (n : nat) : term73 p n.
Proof. exact (@lem7581882 p (term74 p n)). Qed.
Lemma lem7581884 (p : real -> real) (x : real) (n : nat) : (term75 p n x) = (term76 p x n).
Proof. exact (eq_refl (term75 p n x)). Qed.
Lemma lem7581885 (p : real -> real) (x : real) : (term77 p x) = (term77 p x).
Proof. exact (eq_refl (term77 p x)). Qed.
Lemma lem7581886 (p : real -> real) (x : real) (n : nat) : (term78 p n x) = (term68 p x n).
Proof. exact (MK_COMB (@lem7581885 p x) (@lem7581884 p x n)). Qed.
Lemma lem7581887 (p : real -> real) (n : nat) : (term79 p n) = (term70 p n).
Proof. exact (fun_ext (fun x : real => @lem7581886 p x n)). Qed.
Lemma lem7581888 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7581889 (p : real -> real) (n : nat) : (term80 p n) = (term71 p n).
Proof. exact (MK_COMB (@lem7581888) (@lem7581887 p n)). Qed.
Lemma lem7581890 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7581891 (p : real -> real) (n : nat) : (term81 p n) = (term82 p n).
Proof. exact (MK_COMB (@lem7581890) (@lem7581889 p n)). Qed.
Lemma lem7581892 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem7581893 (p : real -> real) (n : nat) : ((term80 p n) = True) = ((term71 p n) = True).
Proof. exact (MK_COMB (@lem7581891 p n) (@lem7581892)). Qed.
Lemma lem7581894 (p : real -> real) (n : nat) : (term83 p n) = (term83 p n).
Proof. exact (eq_refl (term83 p n)). Qed.
Lemma lem7581895 (p : real -> real) (n : nat) : (term73 p n) = (term84 p n).
Proof. exact (MK_COMB (@lem7581894 p n) (@lem7581893 p n)). Qed.
Lemma lem7581896 (p : real -> real) (n : nat) : term84 p n.
Proof. exact (EQ_MP (@lem7581895 p n) (@lem7581883 p n)). Qed.
Lemma lem7581900 (p : real -> real) (h1 : polynomial_function p) : (polynomial_function p) = True.
Proof. exact (EQ_MP (@lem7581868 p) (@lem7581776 p h1)). Qed.
Lemma lem7581901 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7581902 (p : real -> real) (h1 : polynomial_function p) : (term85 p) = (and True).
Proof. exact (MK_COMB (@lem7581901) (@lem7581900 p h1)). Qed.
Lemma lem7581904 (p : real -> real) (n : nat) (h1 : term11 p n) : (term11 p n) = True.
Proof. exact (EQ_MP (@lem7581870 p n) (@lem7581800 p n h1)). Qed.
Lemma lem7581905 (p : real -> real) (n : nat) (h1 : polynomial_function p) (h2 : term11 p n) : (term86 p n) = (True /\ True).
Proof. exact (MK_COMB (@lem7581902 p h1) (@lem7581904 p n h2)). Qed.
Lemma lem7581907 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7581908 : (True /\ True) = True.
Proof. exact (@lem7581907 True). Qed.
Lemma lem7581909 (p : real -> real) (n : nat) (h1 : polynomial_function p) (h2 : term11 p n) : (term86 p n) = True.
Proof. exact (TRANS (@lem7581905 p n h1 h2) (@lem7581908)). Qed.
Lemma lem7581910 (p : real -> real) (n : nat) (h1 : polynomial_function p) (h2 : term11 p n) : True = (term86 p n).
Proof. exact (SYM (@lem7581909 p n h1 h2)). Qed.
Lemma lem7581911 (p : real -> real) (n : nat) (h1 : polynomial_function p) (h2 : term11 p n) : term86 p n.
Proof. exact (EQ_MP (@lem7581910 p n h1 h2) (@lem0)). Qed.
Lemma lem7581912 (p : real -> real) (n : nat) (h1 : polynomial_function p) (h2 : term11 p n) : (term71 p n) = True.
Proof. exact (@lem7581896 p n (@lem7581911 p n h1 h2)). Qed.
Lemma lem7581913 (p : real -> real) (n : nat) (h1 : polynomial_function p) (h2 : term11 p n) : (term37 p n) = True.
Proof. exact (TRANS (@lem7581880 p n) (@lem7581912 p n h1 h2)). Qed.
Lemma lem7581914 (p : real -> real) (n : nat) (h1 : polynomial_function p) (h2 : term11 p n) : True = (term37 p n).
Proof. exact (SYM (@lem7581913 p n h1 h2)). Qed.
Lemma lem7581915 (p : real -> real) (n : nat) (h1 : polynomial_function p) (h2 : term11 p n) : term37 p n.
Proof. exact (EQ_MP (@lem7581914 p n h1 h2) (@lem0)). Qed.
Lemma lem7581916 (n : nat) (p : real -> real) (h1 : polynomial_function p) : term39 p n.
Proof. exact (fun h0 : term11 p n => @lem7581915 p n h1 h0). Qed.
Lemma lem7581921 (p : real -> real) (h1 : polynomial_function p) : term43 p.
Proof. exact (fun n : nat => @lem7581916 n p h1). Qed.
Lemma lem7581922 (p : real -> real) (h1 : polynomial_function p) : term45 p.
Proof. exact (conj (@lem7581842 p) (@lem7581921 p h1)). Qed.
Lemma lem7581923 (p : real -> real) (h1 : polynomial_function p) : term22 p.
Proof. exact (@lem7581799 p (@lem7581922 p h1)). Qed.
Lemma lem7581924 (p : real -> real) : term23 p.
Proof. exact (fun h0 : polynomial_function p => @lem7581923 p h0). Qed.
Lemma lem7581929 : term27.
Proof. exact (fun p : real -> real => @lem7581924 p). Qed.
Lemma lem7581930 : term26.
Proof. exact (EQ_MP (@lem7581775) (@lem7581929)). Qed.
