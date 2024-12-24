Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIST_TRIANGLES_LE_term_abbrevs.
Require Import ADD_ASSOC_spec.
Require Import ADD_SYM_spec.
Require Import DIST_SYM_spec.
Require Import DIST_TRIANGLE_LE_spec.
Require Import LE_ADD2_spec.
Require Import LE_ADD_LCANCEL_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem1259807 (m : nat) : term0 m.
Proof. exact (@lem1244997 m). Qed.
Lemma lem1259808 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1259809 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1259808 m) (@lem1259807 m)). Qed.
Lemma lem1259810 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1259809 m n). Qed.
Lemma lem1259811 (n : nat) (m : nat) : (term2 m n) = ((term3 m n) = (term3 n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1259813 (m : nat) : term4 m.
Proof. exact (@lem100902 m). Qed.
Lemma lem1259814 (m : nat) : (term4 m) = (term5 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem1259815 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem1259814 m) (@lem1259813 m)). Qed.
Lemma lem1259816 (m : nat) (n : nat) : term6 m n.
Proof. exact (@lem1259815 m n). Qed.
Lemma lem1259817 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem1259818 (m : nat) (n : nat) : term7 m n.
Proof. exact (EQ_MP (@lem1259817 m n) (@lem1259816 m n)). Qed.
Lemma lem1259819 (m : nat) (n : nat) (p : nat) : term8 m n p.
Proof. exact (@lem1259818 m n p). Qed.
Lemma lem1259820 (m : nat) (n : nat) (p : nat) : (term8 m n p) = ((term9 n m p) = (Peano.le n p)).
Proof. exact (eq_refl (term8 m n p)). Qed.
Lemma lem1259822 (m : nat) : term10 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem1259823 (m : nat) : (term10 m) = (term11 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem1259824 (m : nat) : term11 m.
Proof. exact (EQ_MP (@lem1259823 m) (@lem1259822 m)). Qed.
Lemma lem1259825 (m : nat) (n : nat) : term12 m n.
Proof. exact (@lem1259824 m n). Qed.
Lemma lem1259826 (n : nat) (m : nat) : (term12 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term12 m n)). Qed.
Lemma lem1259828 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem1259829 (m : nat) (h1 : term13) : term14 m.
Proof. exact (@lem1259828 h1 m). Qed.
Lemma lem1259830 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem1259831 (m : nat) (h1 : term13) : term15 m.
Proof. exact (EQ_MP (@lem1259830 m) (@lem1259829 m h1)). Qed.
Lemma lem1259832 (m : nat) (n : nat) (h1 : term13) : term16 m n.
Proof. exact (@lem1259831 m h1 n). Qed.
Lemma lem1259833 (n : nat) (m : nat) : (term16 m n) = (term17 n m).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem1259834 (n : nat) (m : nat) (h1 : term13) : term17 n m.
Proof. exact (EQ_MP (@lem1259833 n m) (@lem1259832 m n h1)). Qed.
Lemma lem1259835 (n : nat) (m : nat) (p : nat) (h1 : term13) : term18 n m p.
Proof. exact (@lem1259834 n m h1 p). Qed.
Lemma lem1259836 (n : nat) (m : nat) (p : nat) : (term18 n m p) = (term19 n m p).
Proof. exact (eq_refl (term18 n m p)). Qed.
Lemma lem1259837 (n : nat) (m : nat) (p : nat) (h1 : term13) : term19 n m p.
Proof. exact (EQ_MP (@lem1259836 n m p) (@lem1259835 n m p h1)). Qed.
Lemma lem1259838 (n : nat) (m : nat) (p : nat) (q : nat) (h1 : term13) : term20 n m p q.
Proof. exact (@lem1259837 n m p h1 q). Qed.
Lemma lem1259839 (n : nat) (m : nat) (p : nat) (q : nat) : (term20 n m p q) = (term21 n m p q).
Proof. exact (eq_refl (term20 n m p q)). Qed.
Lemma lem1259840 (n : nat) (m : nat) (p : nat) (q : nat) (h1 : term13) : term21 n m p q.
Proof. exact (EQ_MP (@lem1259839 n m p q) (@lem1259838 n m p q h1)). Qed.
Lemma lem1259841 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term22 m n p q) : term22 m n p q.
Proof. exact (h1). Qed.
Lemma lem1259842 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term13) (h2 : term22 m n p q) : term23 m p q.
Proof. exact (@lem1259840 n m p q h1 (@lem1259841 m n p q h2)). Qed.
Lemma lem1259843 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term22 m n p q) : term24 m p q.
Proof. exact (fun h0 : term13 => @lem1259842 m n p q h0 h1). Qed.
Lemma lem1259844 (m : nat) (p : nat) (q : nat) (h1 : term25 m p q) : term25 m p q.
Proof. exact (h1). Qed.
Lemma lem1259845 (m : nat) (p : nat) (q : nat) (h1 : term25 m p q) : term24 m p q.
Proof. exact (ex_elim (@lem1259844 m p q h1) (fun n : nat => fun h0 : term26 m p q n => @lem1259843 m n p q h0)). Qed.
Lemma lem1259846 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem1259847 (m : nat) (p : nat) (q : nat) (h1 : term13) (h2 : term25 m p q) : term23 m p q.
Proof. exact (@lem1259845 m p q h2 (@lem1259846 h1)). Qed.
Lemma lem1259848 (m : nat) (p : nat) (q : nat) (h1 : term13) : term27 m p q.
Proof. exact (fun h0 : term25 m p q => @lem1259847 m p q h1 h0). Qed.
Lemma lem1259849 (m : nat) (p : nat) (h1 : term13) : term28 m p.
Proof. exact (fun q : nat => @lem1259848 m p q h1). Qed.
Lemma lem1259850 (m : nat) (h1 : term13) : term29 m.
Proof. exact (fun p : nat => @lem1259849 m p h1). Qed.
Lemma lem1259851 (h1 : term13) : term30.
Proof. exact (fun m : nat => @lem1259850 m h1). Qed.
Lemma lem1259852 : term31.
Proof. exact (fun h0 : term13 => @lem1259851 h0). Qed.
Lemma lem1259853 : term30.
Proof. exact (@lem1259852 (@lem1259806)). Qed.
Lemma lem1259854 (m : nat) : term32 m.
Proof. exact (@lem1259853 m). Qed.
Lemma lem1259855 (m : nat) : (term32 m) = (term29 m).
Proof. exact (eq_refl (term32 m)). Qed.
Lemma lem1259856 (m : nat) : term29 m.
Proof. exact (EQ_MP (@lem1259855 m) (@lem1259854 m)). Qed.
Lemma lem1259857 (m : nat) (p : nat) : term33 m p.
Proof. exact (@lem1259856 m p). Qed.
Lemma lem1259858 (m : nat) (p : nat) : (term33 m p) = (term28 m p).
Proof. exact (eq_refl (term33 m p)). Qed.
Lemma lem1259859 (m : nat) (p : nat) : term28 m p.
Proof. exact (EQ_MP (@lem1259858 m p) (@lem1259857 m p)). Qed.
Lemma lem1259860 (m : nat) (p : nat) (q : nat) : term34 m p q.
Proof. exact (@lem1259859 m p q). Qed.
Lemma lem1259861 (m : nat) (p : nat) (q : nat) : (term34 m p q) = (term27 m p q).
Proof. exact (eq_refl (term34 m p q)). Qed.
Lemma lem1259863 (h1 : term35) : term35.
Proof. exact (h1). Qed.
Lemma lem1259864 (m : nat) (h1 : term35) : term36 m.
Proof. exact (@lem1259863 h1 m). Qed.
Lemma lem1259865 (m : nat) : (term36 m) = (term37 m).
Proof. exact (eq_refl (term36 m)). Qed.
Lemma lem1259866 (m : nat) (h1 : term35) : term37 m.
Proof. exact (EQ_MP (@lem1259865 m) (@lem1259864 m h1)). Qed.
Lemma lem1259867 (m : nat) (n : nat) (h1 : term35) : term38 m n.
Proof. exact (@lem1259866 m h1 n). Qed.
Lemma lem1259868 (m : nat) (n : nat) : (term38 m n) = (term39 m n).
Proof. exact (eq_refl (term38 m n)). Qed.
Lemma lem1259869 (m : nat) (n : nat) (h1 : term35) : term39 m n.
Proof. exact (EQ_MP (@lem1259868 m n) (@lem1259867 m n h1)). Qed.
Lemma lem1259870 (m : nat) (n : nat) (p : nat) (h1 : term35) : term40 m n p.
Proof. exact (@lem1259869 m n h1 p). Qed.
Lemma lem1259871 (m : nat) (n : nat) (p : nat) : (term40 m n p) = (term41 m n p).
Proof. exact (eq_refl (term40 m n p)). Qed.
Lemma lem1259872 (m : nat) (n : nat) (p : nat) (h1 : term35) : term41 m n p.
Proof. exact (EQ_MP (@lem1259871 m n p) (@lem1259870 m n p h1)). Qed.
Lemma lem1259873 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term35) : term42 m n p q.
Proof. exact (@lem1259872 m n p h1 q). Qed.
Lemma lem1259874 (m : nat) (n : nat) (p : nat) (q : nat) : (term42 m n p q) = (term43 m n p q).
Proof. exact (eq_refl (term42 m n p q)). Qed.
Lemma lem1259875 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term35) : term43 m n p q.
Proof. exact (EQ_MP (@lem1259874 m n p q) (@lem1259873 m n p q h1)). Qed.
Lemma lem1259876 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term44 m p n q) : term44 m p n q.
Proof. exact (h1). Qed.
Lemma lem1259877 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term35) (h2 : term44 m p n q) : term45 m n p q.
Proof. exact (@lem1259875 m n p q h1 (@lem1259876 m p n q h2)). Qed.
Lemma lem1259878 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term44 m p n q) : term46 m n p q.
Proof. exact (fun h0 : term35 => @lem1259877 m p n q h0 h1). Qed.
Lemma lem1259879 (h1 : term35) : term35.
Proof. exact (h1). Qed.
Lemma lem1259880 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term35) (h2 : term44 m p n q) : term45 m n p q.
Proof. exact (@lem1259878 m p n q h2 (@lem1259879 h1)). Qed.
Lemma lem1259881 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term35) : term43 m n p q.
Proof. exact (fun h0 : term44 m p n q => @lem1259880 m p n q h1 h0). Qed.
Lemma lem1259882 (m : nat) (n : nat) (p : nat) (h1 : term35) : term41 m n p.
Proof. exact (fun q : nat => @lem1259881 m n p q h1). Qed.
Lemma lem1259883 (m : nat) (n : nat) (h1 : term35) : term39 m n.
Proof. exact (fun p : nat => @lem1259882 m n p h1). Qed.
Lemma lem1259884 (m : nat) (h1 : term35) : term37 m.
Proof. exact (fun n : nat => @lem1259883 m n h1). Qed.
Lemma lem1259885 (h1 : term35) : term35.
Proof. exact (fun m : nat => @lem1259884 m h1). Qed.
Lemma lem1259886 : term47.
Proof. exact (fun h0 : term35 => @lem1259885 h0). Qed.
Lemma lem1259887 : term35.
Proof. exact (@lem1259886 (@lem101399)). Qed.
Lemma lem1259888 (m : nat) : term36 m.
Proof. exact (@lem1259887 m). Qed.
Lemma lem1259889 (m : nat) : (term36 m) = (term37 m).
Proof. exact (eq_refl (term36 m)). Qed.
Lemma lem1259890 (m : nat) : term37 m.
Proof. exact (EQ_MP (@lem1259889 m) (@lem1259888 m)). Qed.
Lemma lem1259891 (m : nat) (n : nat) : term38 m n.
Proof. exact (@lem1259890 m n). Qed.
Lemma lem1259892 (m : nat) (n : nat) : (term38 m n) = (term39 m n).
Proof. exact (eq_refl (term38 m n)). Qed.
Lemma lem1259893 (m : nat) (n : nat) : term39 m n.
Proof. exact (EQ_MP (@lem1259892 m n) (@lem1259891 m n)). Qed.
Lemma lem1259894 (m : nat) (n : nat) (p : nat) : term40 m n p.
Proof. exact (@lem1259893 m n p). Qed.
Lemma lem1259895 (m : nat) (n : nat) (p : nat) : (term40 m n p) = (term41 m n p).
Proof. exact (eq_refl (term40 m n p)). Qed.
Lemma lem1259896 (m : nat) (n : nat) (p : nat) : term41 m n p.
Proof. exact (EQ_MP (@lem1259895 m n p) (@lem1259894 m n p)). Qed.
Lemma lem1259897 (m : nat) (n : nat) (p : nat) (q : nat) : term42 m n p q.
Proof. exact (@lem1259896 m n p q). Qed.
Lemma lem1259898 (m : nat) (n : nat) (p : nat) (q : nat) : (term42 m n p q) = (term43 m n p q).
Proof. exact (eq_refl (term42 m n p q)). Qed.
Lemma lem1259903 (m : nat) (n : nat) (p : nat) (h1 : (term48 m n p) = (term49 m n p)) : (term48 m n p) = (term49 m n p).
Proof. exact (h1). Qed.
Lemma lem1259904 (m : nat) (n : nat) (p : nat) (h1 : (term48 m n p) = (term49 m n p)) : (term49 m n p) = (term48 m n p).
Proof. exact (SYM (@lem1259903 m n p h1)). Qed.
Lemma lem1259905 (m : nat) (n : nat) (p : nat) (h1 : (term49 m n p) = (term48 m n p)) : (term49 m n p) = (term48 m n p).
Proof. exact (h1). Qed.
Lemma lem1259906 (m : nat) (n : nat) (p : nat) (h1 : (term49 m n p) = (term48 m n p)) : (term48 m n p) = (term49 m n p).
Proof. exact (SYM (@lem1259905 m n p h1)). Qed.
Lemma lem1259907 (m : nat) (n : nat) (p : nat) : ((term48 m n p) = (term49 m n p)) = ((term49 m n p) = (term48 m n p)).
Proof. exact (prop_ext (fun h1 : (term48 m n p) = (term49 m n p) => @lem1259904 m n p h1) (fun h1 : (term49 m n p) = (term48 m n p) => @lem1259906 m n p h1)). Qed.
Lemma lem1259908 (m : nat) (n : nat) : (term50 m n) = (term51 m n).
Proof. exact (fun_ext (fun p : nat => @lem1259907 m n p)). Qed.
Lemma lem1259909 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1259910 (m : nat) (n : nat) : (term52 m n) = (term53 m n).
Proof. exact (MK_COMB (@lem1259909) (@lem1259908 m n)). Qed.
Lemma lem1259911 (m : nat) : (term54 m) = (term55 m).
Proof. exact (fun_ext (fun n : nat => @lem1259910 m n)). Qed.
Lemma lem1259912 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1259913 (m : nat) : (term56 m) = (term57 m).
Proof. exact (MK_COMB (@lem1259912) (@lem1259911 m)). Qed.
Lemma lem1259914 : term58 = term59.
Proof. exact (fun_ext (fun m : nat => @lem1259913 m)). Qed.
Lemma lem1259915 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1259916 : term60 = term61.
Proof. exact (MK_COMB (@lem1259915) (@lem1259914)). Qed.
Lemma lem1259917 : term61.
Proof. exact (EQ_MP (@lem1259916) (@lem77960)). Qed.
Lemma lem1259918 (m : nat) : term62 m.
Proof. exact (@lem1259917 m). Qed.
Lemma lem1259919 (m : nat) : (term62 m) = (term57 m).
Proof. exact (eq_refl (term62 m)). Qed.
Lemma lem1259920 (m : nat) : term57 m.
Proof. exact (EQ_MP (@lem1259919 m) (@lem1259918 m)). Qed.
Lemma lem1259921 (m : nat) (n : nat) : term63 m n.
Proof. exact (@lem1259920 m n). Qed.
Lemma lem1259922 (m : nat) (n : nat) : (term63 m n) = (term53 m n).
Proof. exact (eq_refl (term63 m n)). Qed.
Lemma lem1259923 (m : nat) (n : nat) : term53 m n.
Proof. exact (EQ_MP (@lem1259922 m n) (@lem1259921 m n)). Qed.
Lemma lem1259924 (m : nat) (n : nat) (p : nat) : term64 m n p.
Proof. exact (@lem1259923 m n p). Qed.
Lemma lem1259925 (m : nat) (n : nat) (p : nat) : (term64 m n p) = ((term49 m n p) = (term48 m n p)).
Proof. exact (eq_refl (term64 m n p)). Qed.
Lemma lem1259927 (m : nat) : term10 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem1259928 (m : nat) : (term10 m) = (term11 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem1259929 (m : nat) : term11 m.
Proof. exact (EQ_MP (@lem1259928 m) (@lem1259927 m)). Qed.
Lemma lem1259930 (m : nat) (n : nat) : term12 m n.
Proof. exact (@lem1259929 m n). Qed.
Lemma lem1259931 (n : nat) (m : nat) : (term12 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term12 m n)). Qed.
Lemma lem1259933 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem1259934 (m : nat) (h1 : term13) : term14 m.
Proof. exact (@lem1259933 h1 m). Qed.
Lemma lem1259935 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem1259936 (m : nat) (h1 : term13) : term15 m.
Proof. exact (EQ_MP (@lem1259935 m) (@lem1259934 m h1)). Qed.
Lemma lem1259937 (m : nat) (n : nat) (h1 : term13) : term16 m n.
Proof. exact (@lem1259936 m h1 n). Qed.
Lemma lem1259938 (n : nat) (m : nat) : (term16 m n) = (term17 n m).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem1259939 (n : nat) (m : nat) (h1 : term13) : term17 n m.
Proof. exact (EQ_MP (@lem1259938 n m) (@lem1259937 m n h1)). Qed.
Lemma lem1259940 (n : nat) (m : nat) (p : nat) (h1 : term13) : term18 n m p.
Proof. exact (@lem1259939 n m h1 p). Qed.
Lemma lem1259941 (n : nat) (m : nat) (p : nat) : (term18 n m p) = (term19 n m p).
Proof. exact (eq_refl (term18 n m p)). Qed.
Lemma lem1259942 (n : nat) (m : nat) (p : nat) (h1 : term13) : term19 n m p.
Proof. exact (EQ_MP (@lem1259941 n m p) (@lem1259940 n m p h1)). Qed.
Lemma lem1259943 (n : nat) (m : nat) (p : nat) (q : nat) (h1 : term13) : term20 n m p q.
Proof. exact (@lem1259942 n m p h1 q). Qed.
Lemma lem1259944 (n : nat) (m : nat) (p : nat) (q : nat) : (term20 n m p q) = (term21 n m p q).
Proof. exact (eq_refl (term20 n m p q)). Qed.
Lemma lem1259945 (n : nat) (m : nat) (p : nat) (q : nat) (h1 : term13) : term21 n m p q.
Proof. exact (EQ_MP (@lem1259944 n m p q) (@lem1259943 n m p q h1)). Qed.
Lemma lem1259946 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term22 m n p q) : term22 m n p q.
Proof. exact (h1). Qed.
Lemma lem1259947 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term13) (h2 : term22 m n p q) : term23 m p q.
Proof. exact (@lem1259945 n m p q h1 (@lem1259946 m n p q h2)). Qed.
Lemma lem1259948 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term22 m n p q) : term24 m p q.
Proof. exact (fun h0 : term13 => @lem1259947 m n p q h0 h1). Qed.
Lemma lem1259949 (m : nat) (p : nat) (q : nat) (h1 : term25 m p q) : term25 m p q.
Proof. exact (h1). Qed.
Lemma lem1259950 (m : nat) (p : nat) (q : nat) (h1 : term25 m p q) : term24 m p q.
Proof. exact (ex_elim (@lem1259949 m p q h1) (fun n : nat => fun h0 : term26 m p q n => @lem1259948 m n p q h0)). Qed.
Lemma lem1259951 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem1259952 (m : nat) (p : nat) (q : nat) (h1 : term13) (h2 : term25 m p q) : term23 m p q.
Proof. exact (@lem1259950 m p q h2 (@lem1259951 h1)). Qed.
Lemma lem1259953 (m : nat) (p : nat) (q : nat) (h1 : term13) : term27 m p q.
Proof. exact (fun h0 : term25 m p q => @lem1259952 m p q h1 h0). Qed.
Lemma lem1259954 (m : nat) (p : nat) (h1 : term13) : term28 m p.
Proof. exact (fun q : nat => @lem1259953 m p q h1). Qed.
Lemma lem1259955 (m : nat) (h1 : term13) : term29 m.
Proof. exact (fun p : nat => @lem1259954 m p h1). Qed.
Lemma lem1259956 (h1 : term13) : term30.
Proof. exact (fun m : nat => @lem1259955 m h1). Qed.
Lemma lem1259957 : term31.
Proof. exact (fun h0 : term13 => @lem1259956 h0). Qed.
Lemma lem1259958 : term30.
Proof. exact (@lem1259957 (@lem1259806)). Qed.
Lemma lem1259959 (m : nat) : term32 m.
Proof. exact (@lem1259958 m). Qed.
Lemma lem1259960 (m : nat) : (term32 m) = (term29 m).
Proof. exact (eq_refl (term32 m)). Qed.
Lemma lem1259961 (m : nat) : term29 m.
Proof. exact (EQ_MP (@lem1259960 m) (@lem1259959 m)). Qed.
Lemma lem1259962 (m : nat) (p : nat) : term33 m p.
Proof. exact (@lem1259961 m p). Qed.
Lemma lem1259963 (m : nat) (p : nat) : (term33 m p) = (term28 m p).
Proof. exact (eq_refl (term33 m p)). Qed.
Lemma lem1259964 (m : nat) (p : nat) : term28 m p.
Proof. exact (EQ_MP (@lem1259963 m p) (@lem1259962 m p)). Qed.
Lemma lem1259965 (m : nat) (p : nat) (q : nat) : term34 m p q.
Proof. exact (@lem1259964 m p q). Qed.
Lemma lem1259966 (m : nat) (p : nat) (q : nat) : (term34 m p q) = (term27 m p q).
Proof. exact (eq_refl (term34 m p q)). Qed.
Lemma lem1259968 (m : nat) (n : nat) (r : nat) (p : nat) (q : nat) (s : nat) (h1 : term65 m n r p q s) : term65 m n r p q s.
Proof. exact (h1). Qed.
Lemma lem1259969 (p : nat) (q : nat) (s : nat) (h1 : term23 p q s) : term23 p q s.
Proof. exact (h1). Qed.
Lemma lem1259970 (m : nat) (n : nat) (r : nat) (h1 : term23 m n r) : term23 m n r.
Proof. exact (h1). Qed.
Lemma lem1259972 (m : nat) (p : nat) (q : nat) : term27 m p q.
Proof. exact (EQ_MP (@lem1259966 m p q) (@lem1259965 m p q)). Qed.
Lemma lem1259973 (m : nat) (p : nat) (n : nat) (q : nat) (r : nat) (s : nat) : term66 m p n q r s.
Proof. exact (@lem1259972 m p (term67 n q r s)). Qed.
Lemma lem1259975 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem1259931 n m) (@lem1259930 m n)). Qed.
Lemma lem1259976 (r : nat) (s : nat) (n : nat) (q : nat) : (term67 n q r s) = (term68 r s n q).
Proof. exact (@lem1259975 (Nat.add r s) (term3 n q)). Qed.
Lemma lem1259977 (m : nat) (n : nat) (p : nat) : (term69 m n p) = (term69 m n p).
Proof. exact (eq_refl (term69 m n p)). Qed.
Lemma lem1259978 (m : nat) (p : nat) (r : nat) (s : nat) (n : nat) (q : nat) : (term70 m p n q r s) = (term71 m p r s n q).
Proof. exact (MK_COMB (@lem1259977 m n p) (@lem1259976 r s n q)). Qed.
Lemma lem1259979 (m : nat) (p : nat) (n : nat) (q : nat) (r : nat) (s : nat) : (term71 m p r s n q) = (term70 m p n q r s).
Proof. exact (SYM (@lem1259978 m p r s n q)). Qed.
Lemma lem1259981 (m : nat) (n : nat) (p : nat) : (term49 m n p) = (term48 m n p).
Proof. exact (EQ_MP (@lem1259925 m n p) (@lem1259924 m n p)). Qed.
Lemma lem1259982 (r : nat) (s : nat) (n : nat) (q : nat) : (term68 r s n q) = (term72 r s n q).
Proof. exact (@lem1259981 r s (term3 n q)). Qed.
Lemma lem1259983 (m : nat) (n : nat) (p : nat) : (term69 m n p) = (term69 m n p).
Proof. exact (eq_refl (term69 m n p)). Qed.
Lemma lem1259984 (m : nat) (p : nat) (r : nat) (s : nat) (n : nat) (q : nat) : (term71 m p r s n q) = (term73 m p r s n q).
Proof. exact (MK_COMB (@lem1259983 m n p) (@lem1259982 r s n q)). Qed.
Lemma lem1259985 (m : nat) (p : nat) (r : nat) (s : nat) (n : nat) (q : nat) : (term73 m p r s n q) = (term71 m p r s n q).
Proof. exact (SYM (@lem1259984 m p r s n q)). Qed.
Lemma lem1259987 (m : nat) (n : nat) (p : nat) (q : nat) : term43 m n p q.
Proof. exact (EQ_MP (@lem1259898 m n p q) (@lem1259897 m n p q)). Qed.
Lemma lem1259988 (m : nat) (p : nat) (r : nat) (s : nat) (n : nat) (q : nat) : term74 m p r s n q.
Proof. exact (@lem1259987 (term3 m n) (term3 n p) r (term75 s n q)). Qed.
Lemma lem1259989 (m : nat) (n : nat) (r : nat) : (term23 m n r) = ((term23 m n r) = True).
Proof. exact (@lem7 (term23 m n r)). Qed.
Lemma lem1259996 (m : nat) (n : nat) (r : nat) (h1 : term23 m n r) : (term23 m n r) = True.
Proof. exact (EQ_MP (@lem1259989 m n r) (@lem1259970 m n r h1)). Qed.
Lemma lem1259997 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1259998 (m : nat) (n : nat) (r : nat) (h1 : term23 m n r) : (term76 m n r) = (and True).
Proof. exact (MK_COMB (@lem1259997) (@lem1259996 m n r h1)). Qed.
Lemma lem1259999 (p : nat) (s : nat) (n : nat) (q : nat) : (term77 p s n q) = (term77 p s n q).
Proof. exact (eq_refl (term77 p s n q)). Qed.
Lemma lem1260000 (p : nat) (s : nat) (q : nat) (m : nat) (n : nat) (r : nat) (h1 : term23 m n r) : (term78 m r p s n q) = (term79 p s n q).
Proof. exact (MK_COMB (@lem1259998 m n r h1) (@lem1259999 p s n q)). Qed.
Lemma lem1260002 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1260003 (p : nat) (s : nat) (n : nat) (q : nat) : (term79 p s n q) = (term77 p s n q).
Proof. exact (@lem1260002 (term77 p s n q)). Qed.
Lemma lem1260004 (p : nat) (s : nat) (q : nat) (m : nat) (n : nat) (r : nat) (h1 : term23 m n r) : (term78 m r p s n q) = (term77 p s n q).
Proof. exact (TRANS (@lem1260000 p s q m n r h1) (@lem1260003 p s n q)). Qed.
Lemma lem1260005 (p : nat) (s : nat) (q : nat) (m : nat) (n : nat) (r : nat) (h1 : term23 m n r) : (term77 p s n q) = (term78 m r p s n q).
Proof. exact (SYM (@lem1260004 p s q m n r h1)). Qed.
Lemma lem1260007 (m : nat) (p : nat) (q : nat) : term27 m p q.
Proof. exact (EQ_MP (@lem1259861 m p q) (@lem1259860 m p q)). Qed.
Lemma lem1260008 (p : nat) (s : nat) (n : nat) (q : nat) : term80 p s n q.
Proof. exact (@lem1260007 n p (term75 s n q)). Qed.
Lemma lem1260010 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem1259826 n m) (@lem1259825 m n)). Qed.
Lemma lem1260011 (n : nat) (q : nat) (s : nat) : (term75 s n q) = (term81 n q s).
Proof. exact (@lem1260010 (term3 n q) s). Qed.
Lemma lem1260012 (n : nat) (q : nat) (p : nat) : (term69 n q p) = (term69 n q p).
Proof. exact (eq_refl (term69 n q p)). Qed.
Lemma lem1260013 (p : nat) (n : nat) (q : nat) (s : nat) : (term82 p s n q) = (term83 p n q s).
Proof. exact (MK_COMB (@lem1260012 n q p) (@lem1260011 n q s)). Qed.
Lemma lem1260014 (p : nat) (s : nat) (n : nat) (q : nat) : (term83 p n q s) = (term82 p s n q).
Proof. exact (SYM (@lem1260013 p n q s)). Qed.
Lemma lem1260016 (m : nat) (n : nat) (p : nat) : (term9 n m p) = (Peano.le n p).
Proof. exact (EQ_MP (@lem1259820 m n p) (@lem1259819 m n p)). Qed.
Lemma lem1260017 (n : nat) (q : nat) (p : nat) (s : nat) : (term83 p n q s) = (term23 q p s).
Proof. exact (@lem1260016 (term3 n q) (term3 q p) s). Qed.
Lemma lem1260018 (p : nat) (n : nat) (q : nat) (s : nat) : (term23 q p s) = (term83 p n q s).
Proof. exact (SYM (@lem1260017 n q p s)). Qed.
Lemma lem1260020 (n : nat) (m : nat) : (term3 m n) = (term3 n m).
Proof. exact (EQ_MP (@lem1259811 n m) (@lem1259810 m n)). Qed.
Lemma lem1260021 (p : nat) (q : nat) : (term3 q p) = (term3 p q).
Proof. exact (@lem1260020 p q). Qed.
Lemma lem1260022 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1260023 (p : nat) (q : nat) : (term84 q p) = (term84 p q).
Proof. exact (MK_COMB (@lem1260022) (@lem1260021 p q)). Qed.
Lemma lem1260024 (s : nat) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem1260025 (p : nat) (q : nat) (s : nat) : (term23 q p s) = (term23 p q s).
Proof. exact (MK_COMB (@lem1260023 p q) (@lem1260024 s)). Qed.
Lemma lem1260026 (q : nat) (p : nat) (s : nat) : (term23 p q s) = (term23 q p s).
Proof. exact (SYM (@lem1260025 p q s)). Qed.
Lemma lem1260029 (p : nat) (q : nat) (s : nat) : (term23 p q s) = ((term23 p q s) = True).
Proof. exact (@lem7 (term23 p q s)). Qed.
Lemma lem1260032 (p : nat) (q : nat) (s : nat) (h1 : term23 p q s) : (term23 p q s) = True.
Proof. exact (EQ_MP (@lem1260029 p q s) (@lem1259969 p q s h1)). Qed.
Lemma lem1260033 (p : nat) (q : nat) (s : nat) (h1 : term23 p q s) : True = (term23 p q s).
Proof. exact (SYM (@lem1260032 p q s h1)). Qed.
Lemma lem1260034 (p : nat) (q : nat) (s : nat) (h1 : term23 p q s) : term23 p q s.
Proof. exact (EQ_MP (@lem1260033 p q s h1) (@lem0)). Qed.
Lemma lem1260035 (p : nat) (q : nat) (s : nat) (h1 : term23 p q s) : term23 q p s.
Proof. exact (EQ_MP (@lem1260026 q p s) (@lem1260034 p q s h1)). Qed.
Lemma lem1260036 (n : nat) (p : nat) (q : nat) (s : nat) (h1 : term23 p q s) : term83 p n q s.
Proof. exact (EQ_MP (@lem1260018 p n q s) (@lem1260035 p q s h1)). Qed.
Lemma lem1260037 (n : nat) (p : nat) (q : nat) (s : nat) (h1 : term23 p q s) : term82 p s n q.
Proof. exact (EQ_MP (@lem1260014 p s n q) (@lem1260036 n p q s h1)). Qed.
Lemma lem1260038 (n : nat) (p : nat) (q : nat) (s : nat) (h1 : term23 p q s) : term85 p s n q.
Proof. exact (ex_intro (term86 p s n q) q (@lem1260037 n p q s h1)). Qed.
Lemma lem1260039 (n : nat) (p : nat) (q : nat) (s : nat) (h1 : term23 p q s) : term77 p s n q.
Proof. exact (@lem1260008 p s n q (@lem1260038 n p q s h1)). Qed.
Lemma lem1260040 (m : nat) (n : nat) (r : nat) (p : nat) (q : nat) (s : nat) (h1 : term23 m n r) (h2 : term23 p q s) : term78 m r p s n q.
Proof. exact (EQ_MP (@lem1260005 p s q m n r h1) (@lem1260039 n p q s h2)). Qed.
Lemma lem1260041 (m : nat) (n : nat) (r : nat) (p : nat) (q : nat) (s : nat) (h1 : term23 m n r) (h2 : term23 p q s) : term73 m p r s n q.
Proof. exact (@lem1259988 m p r s n q (@lem1260040 m n r p q s h1 h2)). Qed.
Lemma lem1260042 (m : nat) (n : nat) (r : nat) (p : nat) (q : nat) (s : nat) (h1 : term23 m n r) (h2 : term23 p q s) : term71 m p r s n q.
Proof. exact (EQ_MP (@lem1259985 m p r s n q) (@lem1260041 m n r p q s h1 h2)). Qed.
Lemma lem1260043 (m : nat) (n : nat) (r : nat) (p : nat) (q : nat) (s : nat) (h1 : term23 m n r) (h2 : term23 p q s) : term70 m p n q r s.
Proof. exact (EQ_MP (@lem1259979 m p n q r s) (@lem1260042 m n r p q s h1 h2)). Qed.
Lemma lem1260044 (m : nat) (n : nat) (r : nat) (p : nat) (q : nat) (s : nat) (h1 : term23 m n r) (h2 : term23 p q s) : term87 m p n q r s.
Proof. exact (ex_intro (term88 m p n q r s) n (@lem1260043 m n r p q s h1 h2)). Qed.
Lemma lem1260045 (m : nat) (n : nat) (r : nat) (p : nat) (q : nat) (s : nat) (h1 : term23 m n r) (h2 : term23 p q s) : term89 m p n q r s.
Proof. exact (@lem1259973 m p n q r s (@lem1260044 m n r p q s h1 h2)). Qed.
Lemma lem1260046 (m : nat) (n : nat) (r : nat) (p : nat) (q : nat) (s : nat) (h1 : term65 m n r p q s) : term23 p q s.
Proof. exact (proj2 (@lem1259968 m n r p q s h1)). Qed.
Lemma lem1260047 (m : nat) (n : nat) (r : nat) (p : nat) (q : nat) (s : nat) (h1 : term65 m n r p q s) : term23 m n r.
Proof. exact (proj1 (@lem1259968 m n r p q s h1)). Qed.
Lemma lem1260048 (m : nat) (n : nat) (r : nat) (p : nat) (q : nat) (s : nat) (h1 : term23 m n r) (h2 : term23 p q s) : (term23 p q s) = (term89 m p n q r s).
Proof. exact (prop_ext (fun h3 : term23 p q s => @lem1260045 m n r p q s h1 h2) (fun h3 : term89 m p n q r s => @lem1259969 p q s h2)). Qed.
Lemma lem1260049 (m : nat) (n : nat) (r : nat) (p : nat) (q : nat) (s : nat) (h1 : term23 m n r) (h2 : term23 p q s) : term89 m p n q r s.
Proof. exact (EQ_MP (@lem1260048 m n r p q s h1 h2) (@lem1259969 p q s h2)). Qed.
Lemma lem1260050 (m : nat) (n : nat) (r : nat) (p : nat) (q : nat) (s : nat) (h1 : term23 m n r) (h2 : term23 p q s) : (term23 m n r) = (term89 m p n q r s).
Proof. exact (prop_ext (fun h3 : term23 m n r => @lem1260049 m n r p q s h1 h2) (fun h3 : term89 m p n q r s => @lem1259970 m n r h1)). Qed.
Lemma lem1260051 (m : nat) (n : nat) (r : nat) (p : nat) (q : nat) (s : nat) (h1 : term23 m n r) (h2 : term23 p q s) : term89 m p n q r s.
Proof. exact (EQ_MP (@lem1260050 m n r p q s h1 h2) (@lem1259970 m n r h1)). Qed.
Lemma lem1260052 (p : nat) (q : nat) (s : nat) (m : nat) (n : nat) (r : nat) (h1 : term65 m n r p q s) (h2 : term23 m n r) : (term23 p q s) = (term89 m p n q r s).
Proof. exact (prop_ext (fun h3 : term23 p q s => @lem1260051 m n r p q s h2 h3) (fun h3 : term89 m p n q r s => @lem1260046 m n r p q s h1)). Qed.
Lemma lem1260053 (p : nat) (q : nat) (s : nat) (m : nat) (n : nat) (r : nat) (h1 : term65 m n r p q s) (h2 : term23 m n r) : term89 m p n q r s.
Proof. exact (EQ_MP (@lem1260052 p q s m n r h1 h2) (@lem1260046 m n r p q s h1)). Qed.
Lemma lem1260054 (m : nat) (n : nat) (r : nat) (p : nat) (q : nat) (s : nat) (h1 : term65 m n r p q s) : (term23 m n r) = (term89 m p n q r s).
Proof. exact (prop_ext (fun h2 : term23 m n r => @lem1260053 p q s m n r h1 h2) (fun h2 : term89 m p n q r s => @lem1260047 m n r p q s h1)). Qed.
Lemma lem1260055 (m : nat) (n : nat) (r : nat) (p : nat) (q : nat) (s : nat) (h1 : term65 m n r p q s) : term89 m p n q r s.
Proof. exact (EQ_MP (@lem1260054 m n r p q s h1) (@lem1260047 m n r p q s h1)). Qed.
Lemma lem1260056 (m : nat) (p : nat) (n : nat) (q : nat) (r : nat) (s : nat) : term90 m p n q r s.
Proof. exact (fun h0 : term65 m n r p q s => @lem1260055 m n r p q s h0). Qed.
Lemma lem1260061 (m : nat) (p : nat) (n : nat) (q : nat) (r : nat) : term91 m p n q r.
Proof. exact (fun s : nat => @lem1260056 m p n q r s). Qed.
Lemma lem1260066 (m : nat) (p : nat) (n : nat) (q : nat) : term92 m p n q.
Proof. exact (fun r : nat => @lem1260061 m p n q r). Qed.
Lemma lem1260071 (m : nat) (p : nat) (n : nat) : term93 m p n.
Proof. exact (fun q : nat => @lem1260066 m p n q). Qed.
Lemma lem1260076 (m : nat) (n : nat) : term94 m n.
Proof. exact (fun p : nat => @lem1260071 m p n). Qed.
Lemma lem1260081 (m : nat) : term95 m.
Proof. exact (fun n : nat => @lem1260076 m n). Qed.
Lemma lem1260086 : term96.
Proof. exact (fun m : nat => @lem1260081 m). Qed.
