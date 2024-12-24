Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LT_ADD2_term_abbrevs.
Require Import LTE_ADD2_spec.
Require Import LT_IMP_LE_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem101791 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem101792 (m : nat) (h1 : term0) : term1 m.
Proof. exact (@lem101791 h1 m). Qed.
Lemma lem101793 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem101794 (m : nat) (h1 : term0) : term2 m.
Proof. exact (EQ_MP (@lem101793 m) (@lem101792 m h1)). Qed.
Lemma lem101795 (m : nat) (n : nat) (h1 : term0) : term3 m n.
Proof. exact (@lem101794 m h1 n). Qed.
Lemma lem101796 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem101797 (m : nat) (n : nat) (h1 : term0) : term4 m n.
Proof. exact (EQ_MP (@lem101796 m n) (@lem101795 m n h1)). Qed.
Lemma lem101798 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem101799 (m : nat) (n : nat) (h1 : term0) (h2 : Peano.lt m n) : Peano.le m n.
Proof. exact (@lem101797 m n h1 (@lem101798 m n h2)). Qed.
Lemma lem101800 (m : nat) (n : nat) (h1 : Peano.lt m n) : term5 m n.
Proof. exact (fun h0 : term0 => @lem101799 m n h0 h1). Qed.
Lemma lem101801 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem101802 (m : nat) (n : nat) (h1 : term0) (h2 : Peano.lt m n) : Peano.le m n.
Proof. exact (@lem101800 m n h2 (@lem101801 h1)). Qed.
Lemma lem101803 (m : nat) (n : nat) (h1 : term0) : term4 m n.
Proof. exact (fun h0 : Peano.lt m n => @lem101802 m n h1 h0). Qed.
Lemma lem101804 (m : nat) (h1 : term0) : term2 m.
Proof. exact (fun n : nat => @lem101803 m n h1). Qed.
Lemma lem101805 (h1 : term0) : term0.
Proof. exact (fun m : nat => @lem101804 m h1). Qed.
Lemma lem101806 : term6.
Proof. exact (fun h0 : term0 => @lem101805 h0). Qed.
Lemma lem101807 : term0.
Proof. exact (@lem101806 (@lem98439)). Qed.
Lemma lem101808 (m : nat) : term1 m.
Proof. exact (@lem101807 m). Qed.
Lemma lem101809 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem101810 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem101809 m) (@lem101808 m)). Qed.
Lemma lem101811 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem101810 m n). Qed.
Lemma lem101812 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem101814 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem101815 (m : nat) (h1 : term7) : term8 m.
Proof. exact (@lem101814 h1 m). Qed.
Lemma lem101816 (m : nat) : (term8 m) = (term9 m).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem101817 (m : nat) (h1 : term7) : term9 m.
Proof. exact (EQ_MP (@lem101816 m) (@lem101815 m h1)). Qed.
Lemma lem101818 (m : nat) (n : nat) (h1 : term7) : term10 m n.
Proof. exact (@lem101817 m h1 n). Qed.
Lemma lem101819 (m : nat) (n : nat) : (term10 m n) = (term11 m n).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem101820 (m : nat) (n : nat) (h1 : term7) : term11 m n.
Proof. exact (EQ_MP (@lem101819 m n) (@lem101818 m n h1)). Qed.
Lemma lem101821 (m : nat) (n : nat) (p : nat) (h1 : term7) : term12 m n p.
Proof. exact (@lem101820 m n h1 p). Qed.
Lemma lem101822 (m : nat) (n : nat) (p : nat) : (term12 m n p) = (term13 m n p).
Proof. exact (eq_refl (term12 m n p)). Qed.
Lemma lem101823 (m : nat) (n : nat) (p : nat) (h1 : term7) : term13 m n p.
Proof. exact (EQ_MP (@lem101822 m n p) (@lem101821 m n p h1)). Qed.
Lemma lem101824 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term7) : term14 m n p q.
Proof. exact (@lem101823 m n p h1 q). Qed.
Lemma lem101825 (m : nat) (n : nat) (p : nat) (q : nat) : (term14 m n p q) = (term15 m n p q).
Proof. exact (eq_refl (term14 m n p q)). Qed.
Lemma lem101826 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term7) : term15 m n p q.
Proof. exact (EQ_MP (@lem101825 m n p q) (@lem101824 m n p q h1)). Qed.
Lemma lem101827 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term16 m p n q) : term16 m p n q.
Proof. exact (h1). Qed.
Lemma lem101828 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term7) (h2 : term16 m p n q) : term17 m n p q.
Proof. exact (@lem101826 m n p q h1 (@lem101827 m p n q h2)). Qed.
Lemma lem101829 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term16 m p n q) : term18 m n p q.
Proof. exact (fun h0 : term7 => @lem101828 m p n q h0 h1). Qed.
Lemma lem101830 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem101831 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term7) (h2 : term16 m p n q) : term17 m n p q.
Proof. exact (@lem101829 m p n q h2 (@lem101830 h1)). Qed.
Lemma lem101832 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term7) : term15 m n p q.
Proof. exact (fun h0 : term16 m p n q => @lem101831 m p n q h1 h0). Qed.
Lemma lem101833 (m : nat) (n : nat) (p : nat) (h1 : term7) : term13 m n p.
Proof. exact (fun q : nat => @lem101832 m n p q h1). Qed.
Lemma lem101834 (m : nat) (n : nat) (h1 : term7) : term11 m n.
Proof. exact (fun p : nat => @lem101833 m n p h1). Qed.
Lemma lem101835 (m : nat) (h1 : term7) : term9 m.
Proof. exact (fun n : nat => @lem101834 m n h1). Qed.
Lemma lem101836 (h1 : term7) : term7.
Proof. exact (fun m : nat => @lem101835 m h1). Qed.
Lemma lem101837 : term19.
Proof. exact (fun h0 : term7 => @lem101836 h0). Qed.
Lemma lem101838 : term7.
Proof. exact (@lem101837 (@lem101790)). Qed.
Lemma lem101839 (m : nat) : term8 m.
Proof. exact (@lem101838 m). Qed.
Lemma lem101840 (m : nat) : (term8 m) = (term9 m).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem101841 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem101840 m) (@lem101839 m)). Qed.
Lemma lem101842 (m : nat) (n : nat) : term10 m n.
Proof. exact (@lem101841 m n). Qed.
Lemma lem101843 (m : nat) (n : nat) : (term10 m n) = (term11 m n).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem101844 (m : nat) (n : nat) : term11 m n.
Proof. exact (EQ_MP (@lem101843 m n) (@lem101842 m n)). Qed.
Lemma lem101845 (m : nat) (n : nat) (p : nat) : term12 m n p.
Proof. exact (@lem101844 m n p). Qed.
Lemma lem101846 (m : nat) (n : nat) (p : nat) : (term12 m n p) = (term13 m n p).
Proof. exact (eq_refl (term12 m n p)). Qed.
Lemma lem101847 (m : nat) (n : nat) (p : nat) : term13 m n p.
Proof. exact (EQ_MP (@lem101846 m n p) (@lem101845 m n p)). Qed.
Lemma lem101848 (m : nat) (n : nat) (p : nat) (q : nat) : term14 m n p q.
Proof. exact (@lem101847 m n p q). Qed.
Lemma lem101849 (m : nat) (n : nat) (p : nat) (q : nat) : (term14 m n p q) = (term15 m n p q).
Proof. exact (eq_refl (term14 m n p q)). Qed.
Lemma lem101851 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term20 m p n q) : term20 m p n q.
Proof. exact (h1). Qed.
Lemma lem101852 (n : nat) (q : nat) (h1 : Peano.lt n q) : Peano.lt n q.
Proof. exact (h1). Qed.
Lemma lem101853 (m : nat) (p : nat) (h1 : Peano.lt m p) : Peano.lt m p.
Proof. exact (h1). Qed.
Lemma lem101855 (m : nat) (n : nat) (p : nat) (q : nat) : term15 m n p q.
Proof. exact (EQ_MP (@lem101849 m n p q) (@lem101848 m n p q)). Qed.
Lemma lem101856 (m : nat) (p : nat) : (Peano.lt m p) = ((Peano.lt m p) = True).
Proof. exact (@lem7 (Peano.lt m p)). Qed.
Lemma lem101863 (m : nat) (p : nat) (h1 : Peano.lt m p) : (Peano.lt m p) = True.
Proof. exact (EQ_MP (@lem101856 m p) (@lem101853 m p h1)). Qed.
Lemma lem101864 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem101865 (m : nat) (p : nat) (h1 : Peano.lt m p) : (term21 m p) = (and True).
Proof. exact (MK_COMB (@lem101864) (@lem101863 m p h1)). Qed.
Lemma lem101866 (n : nat) (q : nat) : (Peano.le n q) = (Peano.le n q).
Proof. exact (eq_refl (Peano.le n q)). Qed.
Lemma lem101867 (n : nat) (q : nat) (m : nat) (p : nat) (h1 : Peano.lt m p) : (term16 m p n q) = (term22 n q).
Proof. exact (MK_COMB (@lem101865 m p h1) (@lem101866 n q)). Qed.
Lemma lem101869 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem101870 (n : nat) (q : nat) : (term22 n q) = (Peano.le n q).
Proof. exact (@lem101869 (Peano.le n q)). Qed.
Lemma lem101871 (n : nat) (q : nat) (m : nat) (p : nat) (h1 : Peano.lt m p) : (term16 m p n q) = (Peano.le n q).
Proof. exact (TRANS (@lem101867 n q m p h1) (@lem101870 n q)). Qed.
Lemma lem101872 (n : nat) (q : nat) (m : nat) (p : nat) (h1 : Peano.lt m p) : (Peano.le n q) = (term16 m p n q).
Proof. exact (SYM (@lem101871 n q m p h1)). Qed.
Lemma lem101874 (m : nat) (n : nat) : term4 m n.
Proof. exact (EQ_MP (@lem101812 m n) (@lem101811 m n)). Qed.
Lemma lem101875 (n : nat) (q : nat) : term4 n q.
Proof. exact (@lem101874 n q). Qed.
Lemma lem101878 (n : nat) (q : nat) : (Peano.lt n q) = ((Peano.lt n q) = True).
Proof. exact (@lem7 (Peano.lt n q)). Qed.
Lemma lem101881 (n : nat) (q : nat) (h1 : Peano.lt n q) : (Peano.lt n q) = True.
Proof. exact (EQ_MP (@lem101878 n q) (@lem101852 n q h1)). Qed.
Lemma lem101882 (n : nat) (q : nat) (h1 : Peano.lt n q) : True = (Peano.lt n q).
Proof. exact (SYM (@lem101881 n q h1)). Qed.
Lemma lem101883 (n : nat) (q : nat) (h1 : Peano.lt n q) : Peano.lt n q.
Proof. exact (EQ_MP (@lem101882 n q h1) (@lem0)). Qed.
Lemma lem101884 (n : nat) (q : nat) (h1 : Peano.lt n q) : Peano.le n q.
Proof. exact (@lem101875 n q (@lem101883 n q h1)). Qed.
Lemma lem101885 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : Peano.lt m p) (h2 : Peano.lt n q) : term16 m p n q.
Proof. exact (EQ_MP (@lem101872 n q m p h1) (@lem101884 n q h2)). Qed.
Lemma lem101886 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : Peano.lt m p) (h2 : Peano.lt n q) : term17 m n p q.
Proof. exact (@lem101855 m n p q (@lem101885 m p n q h1 h2)). Qed.
Lemma lem101887 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term20 m p n q) : Peano.lt n q.
Proof. exact (proj2 (@lem101851 m p n q h1)). Qed.
Lemma lem101888 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term20 m p n q) : Peano.lt m p.
Proof. exact (proj1 (@lem101851 m p n q h1)). Qed.
Lemma lem101889 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : Peano.lt m p) (h2 : Peano.lt n q) : (Peano.lt n q) = (term17 m n p q).
Proof. exact (prop_ext (fun h3 : Peano.lt n q => @lem101886 m p n q h1 h2) (fun h3 : term17 m n p q => @lem101852 n q h2)). Qed.
Lemma lem101890 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : Peano.lt m p) (h2 : Peano.lt n q) : term17 m n p q.
Proof. exact (EQ_MP (@lem101889 m p n q h1 h2) (@lem101852 n q h2)). Qed.
Lemma lem101891 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : Peano.lt m p) (h2 : Peano.lt n q) : (Peano.lt m p) = (term17 m n p q).
Proof. exact (prop_ext (fun h3 : Peano.lt m p => @lem101890 m p n q h1 h2) (fun h3 : term17 m n p q => @lem101853 m p h1)). Qed.
Lemma lem101892 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : Peano.lt m p) (h2 : Peano.lt n q) : term17 m n p q.
Proof. exact (EQ_MP (@lem101891 m p n q h1 h2) (@lem101853 m p h1)). Qed.
Lemma lem101893 (n : nat) (q : nat) (m : nat) (p : nat) (h1 : term20 m p n q) (h2 : Peano.lt m p) : (Peano.lt n q) = (term17 m n p q).
Proof. exact (prop_ext (fun h3 : Peano.lt n q => @lem101892 m p n q h2 h3) (fun h3 : term17 m n p q => @lem101887 m p n q h1)). Qed.
Lemma lem101894 (n : nat) (q : nat) (m : nat) (p : nat) (h1 : term20 m p n q) (h2 : Peano.lt m p) : term17 m n p q.
Proof. exact (EQ_MP (@lem101893 n q m p h1 h2) (@lem101887 m p n q h1)). Qed.
Lemma lem101895 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term20 m p n q) : (Peano.lt m p) = (term17 m n p q).
Proof. exact (prop_ext (fun h2 : Peano.lt m p => @lem101894 n q m p h1 h2) (fun h2 : term17 m n p q => @lem101888 m p n q h1)). Qed.
Lemma lem101896 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term20 m p n q) : term17 m n p q.
Proof. exact (EQ_MP (@lem101895 m p n q h1) (@lem101888 m p n q h1)). Qed.
Lemma lem101897 (m : nat) (n : nat) (p : nat) (q : nat) : term23 m n p q.
Proof. exact (fun h0 : term20 m p n q => @lem101896 m p n q h0). Qed.
Lemma lem101902 (m : nat) (n : nat) (p : nat) : term24 m n p.
Proof. exact (fun q : nat => @lem101897 m n p q). Qed.
Lemma lem101907 (m : nat) (n : nat) : term25 m n.
Proof. exact (fun p : nat => @lem101902 m n p). Qed.
Lemma lem101912 (m : nat) : term26 m.
Proof. exact (fun n : nat => @lem101907 m n). Qed.
Lemma lem101917 : term27.
Proof. exact (fun m : nat => @lem101912 m). Qed.
