Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_ADD_LCANCEL_term_abbrevs.
Require Import DIST_LADD_spec.
Require Import NADD_ADD_spec.
Require Import nadd_eq_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1823_spec.
Lemma lem1274817 (m : nat) : term0 m.
Proof. exact (@lem1245075 m). Qed.
Lemma lem1274818 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1274819 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1274818 m) (@lem1274817 m)). Qed.
Lemma lem1274820 (m : nat) (p : nat) : term2 m p.
Proof. exact (@lem1274819 m p). Qed.
Lemma lem1274821 (m : nat) (p : nat) : (term2 m p) = (term3 m p).
Proof. exact (eq_refl (term2 m p)). Qed.
Lemma lem1274822 (m : nat) (p : nat) : term3 m p.
Proof. exact (EQ_MP (@lem1274821 m p) (@lem1274820 m p)). Qed.
Lemma lem1274823 (m : nat) (p : nat) (n : nat) : term4 m p n.
Proof. exact (@lem1274822 m p n). Qed.
Lemma lem1274824 (m : nat) (n : nat) (p : nat) : (term4 m p n) = ((term5 n m p) = (term6 n p)).
Proof. exact (eq_refl (term4 m p n)). Qed.
Lemma lem1274826 (x : nadd) : term7 x.
Proof. exact (@lem1274104 x). Qed.
Lemma lem1274827 (x : nadd) : (term7 x) = (term8 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem1274828 (x : nadd) : term8 x.
Proof. exact (EQ_MP (@lem1274827 x) (@lem1274826 x)). Qed.
Lemma lem1274829 (x : nadd) (y : nadd) : term9 x y.
Proof. exact (@lem1274828 x y). Qed.
Lemma lem1274830 (x : nadd) (y : nadd) : (term9 x y) = ((term10 x y) = (term11 x y)).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem1274832 (x : nadd) : term12 x.
Proof. exact (@lem1267930 x). Qed.
Lemma lem1274833 (x : nadd) : (term12 x) = (term13 x).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem1274834 (x : nadd) : term13 x.
Proof. exact (EQ_MP (@lem1274833 x) (@lem1274832 x)). Qed.
Lemma lem1274835 (x : nadd) (y : nadd) : term14 x y.
Proof. exact (@lem1274834 x y). Qed.
Lemma lem1274836 (x : nadd) (y : nadd) : (term14 x y) = ((nadd_eq x y) = (term15 x y)).
Proof. exact (eq_refl (term14 x y)). Qed.
Lemma lem1274841 (x : nadd) (y : nadd) : (nadd_eq x y) = (term15 x y).
Proof. exact (EQ_MP (@lem1274836 x y) (@lem1274835 x y)). Qed.
Lemma lem1274842 (y : nadd) (x : nadd) (z : nadd) : (term16 y x z) = (term17 y x z).
Proof. exact (@lem1274841 (nadd_add x y) (nadd_add x z)). Qed.
Lemma lem1274852 (x : nadd) (y : nadd) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem1274830 x y) (@lem1274829 x y)). Qed.
Lemma lem1274853 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1274854 (x : nadd) (y : nadd) (n : nat) : (term18 x y n) = (term19 x y n).
Proof. exact (MK_COMB (@lem1274852 x y) (@lem1274853 n)). Qed.
Lemma lem1274856 {A B : Type'} (f : A -> B) (y : A) : (term20 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1274857 (f : nat -> nat) (y : nat) : (term21 f y) = (f y).
Proof. exact (@lem1274856 nat nat f y). Qed.
Lemma lem1274858 (x : nadd) (y : nadd) (n : nat) : (term22 x y n) = (term19 x y n).
Proof. exact (@lem1274857 (term11 x y) n). Qed.
Lemma lem1274859 (x : nadd) (y : nadd) (n : nat) : (term19 x y n) = (term23 x y n).
Proof. exact (eq_refl (term19 x y n)). Qed.
Lemma lem1274860 (x : nadd) (y : nadd) : (term24 x y) = (term11 x y).
Proof. exact (fun_ext (fun n : nat => @lem1274859 x y n)). Qed.
Lemma lem1274861 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1274862 (x : nadd) (y : nadd) (n : nat) : (term22 x y n) = (term19 x y n).
Proof. exact (MK_COMB (@lem1274860 x y) (@lem1274861 n)). Qed.
Lemma lem1274863 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1274864 (x : nadd) (y : nadd) (n : nat) : (term25 x y n) = (term26 x y n).
Proof. exact (MK_COMB (@lem1274863) (@lem1274862 x y n)). Qed.
Lemma lem1274865 (x : nadd) (y : nadd) (n : nat) : (term19 x y n) = (term23 x y n).
Proof. exact (eq_refl (term19 x y n)). Qed.
Lemma lem1274866 (x : nadd) (y : nadd) (n : nat) : ((term22 x y n) = (term19 x y n)) = ((term19 x y n) = (term23 x y n)).
Proof. exact (MK_COMB (@lem1274864 x y n) (@lem1274865 x y n)). Qed.
Lemma lem1274867 (x : nadd) (y : nadd) (n : nat) : (term19 x y n) = (term23 x y n).
Proof. exact (EQ_MP (@lem1274866 x y n) (@lem1274858 x y n)). Qed.
Lemma lem1274868 (x : nadd) (y : nadd) (n : nat) : (term18 x y n) = (term23 x y n).
Proof. exact (TRANS (@lem1274854 x y n) (@lem1274867 x y n)). Qed.
Lemma lem1274869 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1274870 (x : nadd) (y : nadd) (n : nat) : (term27 x y n) = (term28 x y n).
Proof. exact (MK_COMB (@lem1274869) (@lem1274868 x y n)). Qed.
Lemma lem1274872 (x : nadd) (y : nadd) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem1274830 x y) (@lem1274829 x y)). Qed.
Lemma lem1274873 (x : nadd) (z : nadd) : (term10 x z) = (term11 x z).
Proof. exact (@lem1274872 x z). Qed.
Lemma lem1274874 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1274875 (x : nadd) (z : nadd) (n : nat) : (term18 x z n) = (term19 x z n).
Proof. exact (MK_COMB (@lem1274873 x z) (@lem1274874 n)). Qed.
Lemma lem1274877 {A B : Type'} (f : A -> B) (y : A) : (term20 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1274878 (f : nat -> nat) (y : nat) : (term21 f y) = (f y).
Proof. exact (@lem1274877 nat nat f y). Qed.
Lemma lem1274879 (x : nadd) (z : nadd) (n : nat) : (term22 x z n) = (term19 x z n).
Proof. exact (@lem1274878 (term11 x z) n). Qed.
Lemma lem1274880 (x : nadd) (z : nadd) (n : nat) : (term19 x z n) = (term23 x z n).
Proof. exact (eq_refl (term19 x z n)). Qed.
Lemma lem1274881 (x : nadd) (z : nadd) : (term24 x z) = (term11 x z).
Proof. exact (fun_ext (fun n : nat => @lem1274880 x z n)). Qed.
Lemma lem1274882 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1274883 (x : nadd) (z : nadd) (n : nat) : (term22 x z n) = (term19 x z n).
Proof. exact (MK_COMB (@lem1274881 x z) (@lem1274882 n)). Qed.
Lemma lem1274884 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1274885 (x : nadd) (z : nadd) (n : nat) : (term25 x z n) = (term26 x z n).
Proof. exact (MK_COMB (@lem1274884) (@lem1274883 x z n)). Qed.
Lemma lem1274886 (x : nadd) (z : nadd) (n : nat) : (term19 x z n) = (term23 x z n).
Proof. exact (eq_refl (term19 x z n)). Qed.
Lemma lem1274887 (x : nadd) (z : nadd) (n : nat) : ((term22 x z n) = (term19 x z n)) = ((term19 x z n) = (term23 x z n)).
Proof. exact (MK_COMB (@lem1274885 x z n) (@lem1274886 x z n)). Qed.
Lemma lem1274888 (x : nadd) (z : nadd) (n : nat) : (term19 x z n) = (term23 x z n).
Proof. exact (EQ_MP (@lem1274887 x z n) (@lem1274879 x z n)). Qed.
Lemma lem1274889 (x : nadd) (z : nadd) (n : nat) : (term18 x z n) = (term23 x z n).
Proof. exact (TRANS (@lem1274875 x z n) (@lem1274888 x z n)). Qed.
Lemma lem1274890 (y : nadd) (x : nadd) (z : nadd) (n : nat) : (term29 y x z n) = (term30 y x z n).
Proof. exact (MK_COMB (@lem1274870 x y n) (@lem1274889 x z n)). Qed.
Lemma lem1274891 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1274892 (y : nadd) (x : nadd) (z : nadd) (n : nat) : (term31 y x z n) = (term32 y x z n).
Proof. exact (MK_COMB (@lem1274891) (@lem1274890 y x z n)). Qed.
Lemma lem1274894 (m : nat) (n : nat) (p : nat) : (term5 n m p) = (term6 n p).
Proof. exact (EQ_MP (@lem1274824 m n p) (@lem1274823 m p n)). Qed.
Lemma lem1274895 (x : nadd) (y : nadd) (z : nadd) (n : nat) : (term32 y x z n) = (term33 y z n).
Proof. exact (@lem1274894 (dest_nadd x n) (dest_nadd y n) (dest_nadd z n)). Qed.
Lemma lem1274896 (x : nadd) (y : nadd) (z : nadd) (n : nat) : (term31 y x z n) = (term33 y z n).
Proof. exact (TRANS (@lem1274892 y x z n) (@lem1274895 x y z n)). Qed.
Lemma lem1274897 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1274898 (x : nadd) (y : nadd) (z : nadd) (n : nat) : (term34 y x z n) = (term35 y z n).
Proof. exact (MK_COMB (@lem1274897) (@lem1274896 x y z n)). Qed.
Lemma lem1274899 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1274900 (x : nadd) (y : nadd) (z : nadd) (n : nat) (B : nat) : (term36 y x z n B) = (term37 y z n B).
Proof. exact (MK_COMB (@lem1274898 x y z n) (@lem1274899 B)). Qed.
Lemma lem1274901 (x : nadd) (y : nadd) (z : nadd) (B : nat) : (term38 y x z B) = (term39 y z B).
Proof. exact (fun_ext (fun n : nat => @lem1274900 x y z n B)). Qed.
Lemma lem1274902 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1274903 (x : nadd) (y : nadd) (z : nadd) (B : nat) : (term40 y x z B) = (term41 y z B).
Proof. exact (MK_COMB (@lem1274902) (@lem1274901 x y z B)). Qed.
Lemma lem1274908 (x : nadd) (y : nadd) (z : nadd) : (term42 y x z) = (term43 y z).
Proof. exact (fun_ext (fun B : nat => @lem1274903 x y z B)). Qed.
Lemma lem1274909 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1274910 (x : nadd) (y : nadd) (z : nadd) : (term17 y x z) = (term15 y z).
Proof. exact (MK_COMB (@lem1274909) (@lem1274908 x y z)). Qed.
Lemma lem1274915 (x : nadd) (y : nadd) (z : nadd) : (term16 y x z) = (term15 y z).
Proof. exact (TRANS (@lem1274842 y x z) (@lem1274910 x y z)). Qed.
Lemma lem1274916 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1274917 (x : nadd) (y : nadd) (z : nadd) : (term44 y x z) = (term45 y z).
Proof. exact (MK_COMB (@lem1274916) (@lem1274915 x y z)). Qed.
Lemma lem1274919 (x : nadd) (y : nadd) : (nadd_eq x y) = (term15 x y).
Proof. exact (EQ_MP (@lem1274836 x y) (@lem1274835 x y)). Qed.
Lemma lem1274920 (y : nadd) (z : nadd) : (nadd_eq y z) = (term15 y z).
Proof. exact (@lem1274919 y z). Qed.
Lemma lem1274929 (x : nadd) (y : nadd) (z : nadd) : (term46 x y z) = (term47 y z).
Proof. exact (MK_COMB (@lem1274917 x y z) (@lem1274920 y z)). Qed.
Lemma lem1274931 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1274932 (y : nadd) (z : nadd) : (term47 y z) = True.
Proof. exact (@lem1274931 (term15 y z)). Qed.
Lemma lem1274933 (x : nadd) (y : nadd) (z : nadd) : (term46 x y z) = True.
Proof. exact (TRANS (@lem1274929 x y z) (@lem1274932 y z)). Qed.
Lemma lem1274934 (x : nadd) (y : nadd) (z : nadd) : True = (term46 x y z).
Proof. exact (SYM (@lem1274933 x y z)). Qed.
Lemma lem1274935 (x : nadd) (y : nadd) (z : nadd) : term46 x y z.
Proof. exact (EQ_MP (@lem1274934 x y z) (@lem0)). Qed.
Lemma lem1274940 (x : nadd) (y : nadd) : term48 x y.
Proof. exact (fun z : nadd => @lem1274935 x y z). Qed.
Lemma lem1274945 (x : nadd) : term49 x.
Proof. exact (fun y : nadd => @lem1274940 x y). Qed.
Lemma lem1274950 : term50.
Proof. exact (fun x : nadd => @lem1274945 x). Qed.
