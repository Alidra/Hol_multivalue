Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_ARCH_MULT_term_abbrevs.
Require Import ADD_ASSOC_spec.
Require Import ADD_SYM_spec.
Require Import DIST_RZERO_spec.
Require Import LEFT_ADD_DISTRIB_spec.
Require Import LE_ADD_RCANCEL_spec.
Require Import LE_MULT_RCANCEL_spec.
Require Import LE_TRANS_spec.
Require Import LT_IMP_LE_spec.
Require Import MULT_CLAUSES_spec.
Require Import MULT_SYM_spec.
Require Import NADD_CAUCHY_spec.
Require Import NADD_MUL_spec.
Require Import NADD_OF_NUM_spec.
Require Import NOT_EXISTS_THM_spec.
Require Import NOT_FORALL_THM_spec.
Require Import NOT_LE_spec.
Require Import RIGHT_ADD_DISTRIB_spec.
Require Import nadd_eq_spec.
Require Import nadd_le_spec.
Require Import thm1247096_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1843_spec.
Require Import thm37_spec.
Require Import thm7_spec.
Lemma lem1285827 (m : nat) : term0 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem1285828 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1285829 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1285828 m) (@lem1285827 m)). Qed.
Lemma lem1285830 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1285829 m n). Qed.
Lemma lem1285831 (n : nat) (m : nat) : (term2 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1285833 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1285834 (m : nat) (h1 : term3) : term4 m.
Proof. exact (@lem1285833 h1 m). Qed.
Lemma lem1285835 (m : nat) : (term4 m) = (term5 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem1285836 (m : nat) (h1 : term3) : term5 m.
Proof. exact (EQ_MP (@lem1285835 m) (@lem1285834 m h1)). Qed.
Lemma lem1285837 (m : nat) (n : nat) (h1 : term3) : term6 m n.
Proof. exact (@lem1285836 m h1 n). Qed.
Lemma lem1285838 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem1285839 (m : nat) (n : nat) (h1 : term3) : term7 m n.
Proof. exact (EQ_MP (@lem1285838 m n) (@lem1285837 m n h1)). Qed.
Lemma lem1285840 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem1285841 (m : nat) (n : nat) (h1 : term3) (h2 : Peano.lt m n) : Peano.le m n.
Proof. exact (@lem1285839 m n h1 (@lem1285840 m n h2)). Qed.
Lemma lem1285842 (m : nat) (n : nat) (h1 : Peano.lt m n) : term8 m n.
Proof. exact (fun h0 : term3 => @lem1285841 m n h0 h1). Qed.
Lemma lem1285843 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1285844 (m : nat) (n : nat) (h1 : term3) (h2 : Peano.lt m n) : Peano.le m n.
Proof. exact (@lem1285842 m n h2 (@lem1285843 h1)). Qed.
Lemma lem1285845 (m : nat) (n : nat) (h1 : term3) : term7 m n.
Proof. exact (fun h0 : Peano.lt m n => @lem1285844 m n h1 h0). Qed.
Lemma lem1285846 (m : nat) (h1 : term3) : term5 m.
Proof. exact (fun n : nat => @lem1285845 m n h1). Qed.
Lemma lem1285847 (h1 : term3) : term3.
Proof. exact (fun m : nat => @lem1285846 m h1). Qed.
Lemma lem1285848 : term9.
Proof. exact (fun h0 : term3 => @lem1285847 h0). Qed.
Lemma lem1285849 : term3.
Proof. exact (@lem1285848 (@lem98439)). Qed.
Lemma lem1285850 (m : nat) : term4 m.
Proof. exact (@lem1285849 m). Qed.
Lemma lem1285851 (m : nat) : (term4 m) = (term5 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem1285852 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem1285851 m) (@lem1285850 m)). Qed.
Lemma lem1285853 (m : nat) (n : nat) : term6 m n.
Proof. exact (@lem1285852 m n). Qed.
Lemma lem1285854 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem1285856 (m : nat) : term10 m.
Proof. exact (@lem104289 m). Qed.
Lemma lem1285857 (m : nat) : (term10 m) = (term11 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem1285858 (m : nat) : term11 m.
Proof. exact (EQ_MP (@lem1285857 m) (@lem1285856 m)). Qed.
Lemma lem1285859 (m : nat) (n : nat) : term12 m n.
Proof. exact (@lem1285858 m n). Qed.
Lemma lem1285860 (m : nat) (n : nat) : (term12 m n) = (term13 m n).
Proof. exact (eq_refl (term12 m n)). Qed.
Lemma lem1285861 (m : nat) (n : nat) : term13 m n.
Proof. exact (EQ_MP (@lem1285860 m n) (@lem1285859 m n)). Qed.
Lemma lem1285862 (m : nat) (n : nat) (p : nat) : term14 m n p.
Proof. exact (@lem1285861 m n p). Qed.
Lemma lem1285863 (m : nat) (n : nat) (p : nat) : (term14 m n p) = ((term15 m n p) = (term16 m n p)).
Proof. exact (eq_refl (term14 m n p)). Qed.
Lemma lem1285865 (m : nat) : term17 m.
Proof. exact (@lem81820 m). Qed.
Lemma lem1285866 (m : nat) : (term17 m) = (term18 m).
Proof. exact (eq_refl (term17 m)). Qed.
Lemma lem1285867 (m : nat) : term18 m.
Proof. exact (EQ_MP (@lem1285866 m) (@lem1285865 m)). Qed.
Lemma lem1285868 (m : nat) (n : nat) : term19 m n.
Proof. exact (@lem1285867 m n). Qed.
Lemma lem1285869 (n : nat) (m : nat) : (term19 m n) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem1285874 (m : nat) (n : nat) (p : nat) (h1 : (term20 m n p) = (term21 m n p)) : (term20 m n p) = (term21 m n p).
Proof. exact (h1). Qed.
Lemma lem1285875 (m : nat) (n : nat) (p : nat) (h1 : (term20 m n p) = (term21 m n p)) : (term21 m n p) = (term20 m n p).
Proof. exact (SYM (@lem1285874 m n p h1)). Qed.
Lemma lem1285876 (m : nat) (n : nat) (p : nat) (h1 : (term21 m n p) = (term20 m n p)) : (term21 m n p) = (term20 m n p).
Proof. exact (h1). Qed.
Lemma lem1285877 (m : nat) (n : nat) (p : nat) (h1 : (term21 m n p) = (term20 m n p)) : (term20 m n p) = (term21 m n p).
Proof. exact (SYM (@lem1285876 m n p h1)). Qed.
Lemma lem1285878 (m : nat) (n : nat) (p : nat) : ((term20 m n p) = (term21 m n p)) = ((term21 m n p) = (term20 m n p)).
Proof. exact (prop_ext (fun h1 : (term20 m n p) = (term21 m n p) => @lem1285875 m n p h1) (fun h1 : (term21 m n p) = (term20 m n p) => @lem1285877 m n p h1)). Qed.
Lemma lem1285879 (m : nat) (n : nat) : (term22 m n) = (term23 m n).
Proof. exact (fun_ext (fun p : nat => @lem1285878 m n p)). Qed.
Lemma lem1285880 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1285881 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (MK_COMB (@lem1285880) (@lem1285879 m n)). Qed.
Lemma lem1285882 (m : nat) : (term26 m) = (term27 m).
Proof. exact (fun_ext (fun n : nat => @lem1285881 m n)). Qed.
Lemma lem1285883 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1285884 (m : nat) : (term28 m) = (term29 m).
Proof. exact (MK_COMB (@lem1285883) (@lem1285882 m)). Qed.
Lemma lem1285885 : term30 = term31.
Proof. exact (fun_ext (fun m : nat => @lem1285884 m)). Qed.
Lemma lem1285886 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1285887 : term32 = term33.
Proof. exact (MK_COMB (@lem1285886) (@lem1285885)). Qed.
Lemma lem1285888 : term33.
Proof. exact (EQ_MP (@lem1285887) (@lem82128)). Qed.
Lemma lem1285889 (m : nat) : term34 m.
Proof. exact (@lem1285888 m). Qed.
Lemma lem1285890 (m : nat) : (term34 m) = (term29 m).
Proof. exact (eq_refl (term34 m)). Qed.
Lemma lem1285891 (m : nat) : term29 m.
Proof. exact (EQ_MP (@lem1285890 m) (@lem1285889 m)). Qed.
Lemma lem1285892 (m : nat) (n : nat) : term35 m n.
Proof. exact (@lem1285891 m n). Qed.
Lemma lem1285893 (m : nat) (n : nat) : (term35 m n) = (term25 m n).
Proof. exact (eq_refl (term35 m n)). Qed.
Lemma lem1285894 (m : nat) (n : nat) : term25 m n.
Proof. exact (EQ_MP (@lem1285893 m n) (@lem1285892 m n)). Qed.
Lemma lem1285895 (m : nat) (n : nat) (p : nat) : term36 m n p.
Proof. exact (@lem1285894 m n p). Qed.
Lemma lem1285896 (m : nat) (n : nat) (p : nat) : (term36 m n p) = ((term21 m n p) = (term20 m n p)).
Proof. exact (eq_refl (term36 m n p)). Qed.
Lemma lem1285898 (m : nat) : term37 m.
Proof. exact (@lem1247096 m). Qed.
Lemma lem1285899 (m : nat) : (term37 m) = (term38 m).
Proof. exact (eq_refl (term37 m)). Qed.
Lemma lem1285900 (m : nat) : term38 m.
Proof. exact (EQ_MP (@lem1285899 m) (@lem1285898 m)). Qed.
Lemma lem1285901 (m : nat) (n : nat) : term39 m n.
Proof. exact (@lem1285900 m n). Qed.
Lemma lem1285902 (n : nat) (m : nat) : (term39 m n) = (term40 n m).
Proof. exact (eq_refl (term39 m n)). Qed.
Lemma lem1285903 (n : nat) (m : nat) : term40 n m.
Proof. exact (EQ_MP (@lem1285902 n m) (@lem1285901 m n)). Qed.
Lemma lem1285904 (n : nat) (m : nat) (p : nat) : term41 n m p.
Proof. exact (@lem1285903 n m p). Qed.
Lemma lem1285905 (n : nat) (m : nat) (p : nat) : (term41 n m p) = ((term42 m n p) = (term43 n m p)).
Proof. exact (eq_refl (term41 n m p)). Qed.
Lemma lem1285907 (h1 : term44) : term44.
Proof. exact (h1). Qed.
Lemma lem1285908 (m : nat) (h1 : term44) : term45 m.
Proof. exact (@lem1285907 h1 m). Qed.
Lemma lem1285909 (m : nat) : (term45 m) = (term46 m).
Proof. exact (eq_refl (term45 m)). Qed.
Lemma lem1285910 (m : nat) (h1 : term44) : term46 m.
Proof. exact (EQ_MP (@lem1285909 m) (@lem1285908 m h1)). Qed.
Lemma lem1285911 (m : nat) (n : nat) (h1 : term44) : term47 m n.
Proof. exact (@lem1285910 m h1 n). Qed.
Lemma lem1285912 (n : nat) (m : nat) : (term47 m n) = (term48 n m).
Proof. exact (eq_refl (term47 m n)). Qed.
Lemma lem1285913 (n : nat) (m : nat) (h1 : term44) : term48 n m.
Proof. exact (EQ_MP (@lem1285912 n m) (@lem1285911 m n h1)). Qed.
Lemma lem1285914 (n : nat) (m : nat) (p : nat) (h1 : term44) : term49 n m p.
Proof. exact (@lem1285913 n m h1 p). Qed.
Lemma lem1285915 (n : nat) (m : nat) (p : nat) : (term49 n m p) = (term50 n m p).
Proof. exact (eq_refl (term49 n m p)). Qed.
Lemma lem1285916 (n : nat) (m : nat) (p : nat) (h1 : term44) : term50 n m p.
Proof. exact (EQ_MP (@lem1285915 n m p) (@lem1285914 n m p h1)). Qed.
Lemma lem1285917 (m : nat) (n : nat) (p : nat) (h1 : term51 m n p) : term51 m n p.
Proof. exact (h1). Qed.
Lemma lem1285918 (m : nat) (n : nat) (p : nat) (h1 : term44) (h2 : term51 m n p) : Peano.le m p.
Proof. exact (@lem1285916 n m p h1 (@lem1285917 m n p h2)). Qed.
Lemma lem1285919 (m : nat) (n : nat) (p : nat) (h1 : term51 m n p) : term52 m p.
Proof. exact (fun h0 : term44 => @lem1285918 m n p h0 h1). Qed.
Lemma lem1285920 (m : nat) (p : nat) (h1 : term53 m p) : term53 m p.
Proof. exact (h1). Qed.
Lemma lem1285921 (m : nat) (p : nat) (h1 : term53 m p) : term52 m p.
Proof. exact (ex_elim (@lem1285920 m p h1) (fun n : nat => fun h0 : term54 m p n => @lem1285919 m n p h0)). Qed.
Lemma lem1285922 (h1 : term44) : term44.
Proof. exact (h1). Qed.
Lemma lem1285923 (m : nat) (p : nat) (h1 : term44) (h2 : term53 m p) : Peano.le m p.
Proof. exact (@lem1285921 m p h2 (@lem1285922 h1)). Qed.
Lemma lem1285924 (m : nat) (p : nat) (h1 : term44) : term55 m p.
Proof. exact (fun h0 : term53 m p => @lem1285923 m p h1 h0). Qed.
Lemma lem1285925 (m : nat) (h1 : term44) : term56 m.
Proof. exact (fun p : nat => @lem1285924 m p h1). Qed.
Lemma lem1285926 (h1 : term44) : term57.
Proof. exact (fun m : nat => @lem1285925 m h1). Qed.
Lemma lem1285927 : term58.
Proof. exact (fun h0 : term44 => @lem1285926 h0). Qed.
Lemma lem1285928 : term57.
Proof. exact (@lem1285927 (@lem93743)). Qed.
Lemma lem1285929 (m : nat) : term59 m.
Proof. exact (@lem1285928 m). Qed.
Lemma lem1285930 (m : nat) : (term59 m) = (term56 m).
Proof. exact (eq_refl (term59 m)). Qed.
Lemma lem1285931 (m : nat) : term56 m.
Proof. exact (EQ_MP (@lem1285930 m) (@lem1285929 m)). Qed.
Lemma lem1285932 (m : nat) (p : nat) : term60 m p.
Proof. exact (@lem1285931 m p). Qed.
Lemma lem1285933 (m : nat) (p : nat) : (term60 m p) = (term55 m p).
Proof. exact (eq_refl (term60 m p)). Qed.
Lemma lem1285938 (n : nat) (m : nat) (p : nat) (h1 : (term61 m n p) = (term62 n m p)) : (term61 m n p) = (term62 n m p).
Proof. exact (h1). Qed.
Lemma lem1285939 (n : nat) (m : nat) (p : nat) (h1 : (term61 m n p) = (term62 n m p)) : (term62 n m p) = (term61 m n p).
Proof. exact (SYM (@lem1285938 n m p h1)). Qed.
Lemma lem1285940 (m : nat) (n : nat) (p : nat) (h1 : (term62 n m p) = (term61 m n p)) : (term62 n m p) = (term61 m n p).
Proof. exact (h1). Qed.
Lemma lem1285941 (m : nat) (n : nat) (p : nat) (h1 : (term62 n m p) = (term61 m n p)) : (term61 m n p) = (term62 n m p).
Proof. exact (SYM (@lem1285940 m n p h1)). Qed.
Lemma lem1285942 (m : nat) (n : nat) (p : nat) : ((term61 m n p) = (term62 n m p)) = ((term62 n m p) = (term61 m n p)).
Proof. exact (prop_ext (fun h1 : (term61 m n p) = (term62 n m p) => @lem1285939 n m p h1) (fun h1 : (term62 n m p) = (term61 m n p) => @lem1285941 m n p h1)). Qed.
Lemma lem1285943 (m : nat) (n : nat) : (term63 n m) = (term64 m n).
Proof. exact (fun_ext (fun p : nat => @lem1285942 m n p)). Qed.
Lemma lem1285944 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1285945 (m : nat) (n : nat) : (term65 n m) = (term66 m n).
Proof. exact (MK_COMB (@lem1285944) (@lem1285943 m n)). Qed.
Lemma lem1285946 (m : nat) : (term67 m) = (term68 m).
Proof. exact (fun_ext (fun n : nat => @lem1285945 m n)). Qed.
Lemma lem1285947 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1285948 (m : nat) : (term69 m) = (term70 m).
Proof. exact (MK_COMB (@lem1285947) (@lem1285946 m)). Qed.
Lemma lem1285949 : term71 = term72.
Proof. exact (fun_ext (fun m : nat => @lem1285948 m)). Qed.
Lemma lem1285950 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1285951 : term73 = term74.
Proof. exact (MK_COMB (@lem1285950) (@lem1285949)). Qed.
Lemma lem1285952 : term74.
Proof. exact (EQ_MP (@lem1285951) (@lem82055)). Qed.
Lemma lem1285956 (m : nat) (n : nat) (p : nat) (h1 : (term75 m n p) = (term76 m n p)) : (term75 m n p) = (term76 m n p).
Proof. exact (h1). Qed.
Lemma lem1285957 (m : nat) (n : nat) (p : nat) (h1 : (term75 m n p) = (term76 m n p)) : (term76 m n p) = (term75 m n p).
Proof. exact (SYM (@lem1285956 m n p h1)). Qed.
Lemma lem1285958 (m : nat) (n : nat) (p : nat) (h1 : (term76 m n p) = (term75 m n p)) : (term76 m n p) = (term75 m n p).
Proof. exact (h1). Qed.
Lemma lem1285959 (m : nat) (n : nat) (p : nat) (h1 : (term76 m n p) = (term75 m n p)) : (term75 m n p) = (term76 m n p).
Proof. exact (SYM (@lem1285958 m n p h1)). Qed.
Lemma lem1285960 (m : nat) (n : nat) (p : nat) : ((term75 m n p) = (term76 m n p)) = ((term76 m n p) = (term75 m n p)).
Proof. exact (prop_ext (fun h1 : (term75 m n p) = (term76 m n p) => @lem1285957 m n p h1) (fun h1 : (term76 m n p) = (term75 m n p) => @lem1285959 m n p h1)). Qed.
Lemma lem1285961 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (fun_ext (fun p : nat => @lem1285960 m n p)). Qed.
Lemma lem1285962 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1285963 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (MK_COMB (@lem1285962) (@lem1285961 m n)). Qed.
Lemma lem1285964 (m : nat) : (term81 m) = (term82 m).
Proof. exact (fun_ext (fun n : nat => @lem1285963 m n)). Qed.
Lemma lem1285965 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1285966 (m : nat) : (term83 m) = (term84 m).
Proof. exact (MK_COMB (@lem1285965) (@lem1285964 m)). Qed.
Lemma lem1285967 : term85 = term86.
Proof. exact (fun_ext (fun m : nat => @lem1285966 m)). Qed.
Lemma lem1285968 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1285969 : term87 = term88.
Proof. exact (MK_COMB (@lem1285968) (@lem1285967)). Qed.
Lemma lem1285970 : term88.
Proof. exact (EQ_MP (@lem1285969) (@lem77960)). Qed.
Lemma lem1285971 (m : nat) : term89 m.
Proof. exact (@lem1285952 m). Qed.
Lemma lem1285972 (m : nat) : (term89 m) = (term70 m).
Proof. exact (eq_refl (term89 m)). Qed.
Lemma lem1285973 (m : nat) : term70 m.
Proof. exact (EQ_MP (@lem1285972 m) (@lem1285971 m)). Qed.
Lemma lem1285974 (m : nat) (n : nat) : term90 m n.
Proof. exact (@lem1285973 m n). Qed.
Lemma lem1285975 (m : nat) (n : nat) : (term90 m n) = (term66 m n).
Proof. exact (eq_refl (term90 m n)). Qed.
Lemma lem1285976 (m : nat) (n : nat) : term66 m n.
Proof. exact (EQ_MP (@lem1285975 m n) (@lem1285974 m n)). Qed.
Lemma lem1285977 (m : nat) (n : nat) (p : nat) : term91 m n p.
Proof. exact (@lem1285976 m n p). Qed.
Lemma lem1285978 (m : nat) (n : nat) (p : nat) : (term91 m n p) = ((term62 n m p) = (term61 m n p)).
Proof. exact (eq_refl (term91 m n p)). Qed.
Lemma lem1285980 (m : nat) : term92 m.
Proof. exact (@lem1285970 m). Qed.
Lemma lem1285981 (m : nat) : (term92 m) = (term84 m).
Proof. exact (eq_refl (term92 m)). Qed.
Lemma lem1285982 (m : nat) : term84 m.
Proof. exact (EQ_MP (@lem1285981 m) (@lem1285980 m)). Qed.
Lemma lem1285983 (m : nat) (n : nat) : term93 m n.
Proof. exact (@lem1285982 m n). Qed.
Lemma lem1285984 (m : nat) (n : nat) : (term93 m n) = (term80 m n).
Proof. exact (eq_refl (term93 m n)). Qed.
Lemma lem1285985 (m : nat) (n : nat) : term80 m n.
Proof. exact (EQ_MP (@lem1285984 m n) (@lem1285983 m n)). Qed.
Lemma lem1285986 (m : nat) (n : nat) (p : nat) : term94 m n p.
Proof. exact (@lem1285985 m n p). Qed.
Lemma lem1285987 (m : nat) (n : nat) (p : nat) : (term94 m n p) = ((term76 m n p) = (term75 m n p)).
Proof. exact (eq_refl (term94 m n p)). Qed.
Lemma lem1285989 (m : nat) : term95 m.
Proof. exact (@lem100973 m). Qed.
Lemma lem1285990 (m : nat) : (term95 m) = (term96 m).
Proof. exact (eq_refl (term95 m)). Qed.
Lemma lem1285991 (m : nat) : term96 m.
Proof. exact (EQ_MP (@lem1285990 m) (@lem1285989 m)). Qed.
Lemma lem1285992 (m : nat) (n : nat) : term97 m n.
Proof. exact (@lem1285991 m n). Qed.
Lemma lem1285993 (m : nat) (n : nat) : (term97 m n) = (term98 m n).
Proof. exact (eq_refl (term97 m n)). Qed.
Lemma lem1285994 (m : nat) (n : nat) : term98 m n.
Proof. exact (EQ_MP (@lem1285993 m n) (@lem1285992 m n)). Qed.
Lemma lem1285995 (m : nat) (n : nat) (p : nat) : term99 m n p.
Proof. exact (@lem1285994 m n p). Qed.
Lemma lem1285996 (p : nat) (m : nat) (n : nat) : (term99 m n p) = ((term100 m n p) = (Peano.le m n)).
Proof. exact (eq_refl (term99 m n p)). Qed.
Lemma lem1285997 (p : nat) (m : nat) (n : nat) : (term100 m n p) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1285996 p m n) (@lem1285995 m n p)). Qed.
Lemma lem1286000 (p : nat) (m : nat) (n : nat) : term101 p m n.
Proof. exact (@lem37 (term100 m n p) (Peano.le m n)). Qed.
Lemma lem1286001 (p : nat) (m : nat) (n : nat) : term102 p m n.
Proof. exact (@lem1286000 p m n (@lem1285997 p m n)). Qed.
Lemma lem1286002 (p : nat) (m : nat) : term103 p m.
Proof. exact (fun n : nat => @lem1286001 p m n). Qed.
Lemma lem1286003 (p : nat) : term104 p.
Proof. exact (fun m : nat => @lem1286002 p m). Qed.
Lemma lem1286004 : term105.
Proof. exact (fun p : nat => @lem1286003 p). Qed.
Lemma lem1286005 (h1 : term105) : term105.
Proof. exact (h1). Qed.
Lemma lem1286006 (p : nat) (h1 : term105) : term106 p.
Proof. exact (@lem1286005 h1 p). Qed.
Lemma lem1286007 (p : nat) : (term106 p) = (term104 p).
Proof. exact (eq_refl (term106 p)). Qed.
Lemma lem1286008 (p : nat) (h1 : term105) : term104 p.
Proof. exact (EQ_MP (@lem1286007 p) (@lem1286006 p h1)). Qed.
Lemma lem1286009 (p : nat) (m : nat) (h1 : term105) : term107 p m.
Proof. exact (@lem1286008 p h1 m). Qed.
Lemma lem1286010 (p : nat) (m : nat) : (term107 p m) = (term103 p m).
Proof. exact (eq_refl (term107 p m)). Qed.
Lemma lem1286011 (p : nat) (m : nat) (h1 : term105) : term103 p m.
Proof. exact (EQ_MP (@lem1286010 p m) (@lem1286009 p m h1)). Qed.
Lemma lem1286012 (p : nat) (m : nat) (n : nat) (h1 : term105) : term108 p m n.
Proof. exact (@lem1286011 p m h1 n). Qed.
Lemma lem1286013 (p : nat) (m : nat) (n : nat) : (term108 p m n) = (term102 p m n).
Proof. exact (eq_refl (term108 p m n)). Qed.
Lemma lem1286014 (p : nat) (m : nat) (n : nat) (h1 : term105) : term102 p m n.
Proof. exact (EQ_MP (@lem1286013 p m n) (@lem1286012 p m n h1)). Qed.
Lemma lem1286015 (m : nat) (n : nat) (p : nat) (h1 : term100 m n p) : term100 m n p.
Proof. exact (h1). Qed.
Lemma lem1286016 (m : nat) (n : nat) (p : nat) (h1 : term105) (h2 : term100 m n p) : Peano.le m n.
Proof. exact (@lem1286014 p m n h1 (@lem1286015 m n p h2)). Qed.
Lemma lem1286017 (m : nat) (n : nat) (p : nat) (h1 : term100 m n p) : term109 m n.
Proof. exact (fun h0 : term105 => @lem1286016 m n p h0 h1). Qed.
Lemma lem1286018 (m : nat) (n : nat) (h1 : term110 m n) : term110 m n.
Proof. exact (h1). Qed.
Lemma lem1286019 (m : nat) (n : nat) (h1 : term110 m n) : term109 m n.
Proof. exact (ex_elim (@lem1286018 m n h1) (fun p : nat => fun h0 : term111 m n p => @lem1286017 m n p h0)). Qed.
Lemma lem1286020 (h1 : term105) : term105.
Proof. exact (h1). Qed.
Lemma lem1286021 (m : nat) (n : nat) (h1 : term105) (h2 : term110 m n) : Peano.le m n.
Proof. exact (@lem1286019 m n h2 (@lem1286020 h1)). Qed.
Lemma lem1286022 (m : nat) (n : nat) (h1 : term105) : term112 m n.
Proof. exact (fun h0 : term110 m n => @lem1286021 m n h1 h0). Qed.
Lemma lem1286023 (m : nat) (h1 : term105) : term113 m.
Proof. exact (fun n : nat => @lem1286022 m n h1). Qed.
Lemma lem1286024 (h1 : term105) : term114.
Proof. exact (fun m : nat => @lem1286023 m h1). Qed.
Lemma lem1286025 : term115.
Proof. exact (fun h0 : term105 => @lem1286024 h0). Qed.
Lemma lem1286026 : term114.
Proof. exact (@lem1286025 (@lem1286004)). Qed.
Lemma lem1286027 (m : nat) : term116 m.
Proof. exact (@lem1286026 m). Qed.
Lemma lem1286028 (m : nat) : (term116 m) = (term113 m).
Proof. exact (eq_refl (term116 m)). Qed.
Lemma lem1286029 (m : nat) : term113 m.
Proof. exact (EQ_MP (@lem1286028 m) (@lem1286027 m)). Qed.
Lemma lem1286030 (m : nat) (n : nat) : term117 m n.
Proof. exact (@lem1286029 m n). Qed.
Lemma lem1286031 (m : nat) (n : nat) : (term117 m n) = (term112 m n).
Proof. exact (eq_refl (term117 m n)). Qed.
Lemma lem1286033 (k : nat) : term118 k.
Proof. exact (@lem1268972 k). Qed.
Lemma lem1286034 (k : nat) : (term118 k) = ((term119 k) = (term120 k)).
Proof. exact (eq_refl (term118 k)). Qed.
Lemma lem1286036 (x : nadd) : term121 x.
Proof. exact (@lem1277879 x). Qed.
Lemma lem1286037 (x : nadd) : (term121 x) = (term122 x).
Proof. exact (eq_refl (term121 x)). Qed.
Lemma lem1286038 (x : nadd) : term122 x.
Proof. exact (EQ_MP (@lem1286037 x) (@lem1286036 x)). Qed.
Lemma lem1286039 (x : nadd) (y : nadd) : term123 x y.
Proof. exact (@lem1286038 x y). Qed.
Lemma lem1286040 (x : nadd) (y : nadd) : (term123 x y) = ((term124 x y) = (term125 x y)).
Proof. exact (eq_refl (term123 x y)). Qed.
Lemma lem1286042 (m : nat) : term126 m.
Proof. exact (@lem97961 m). Qed.
Lemma lem1286043 (m : nat) : (term126 m) = (term127 m).
Proof. exact (eq_refl (term126 m)). Qed.
Lemma lem1286044 (m : nat) : term127 m.
Proof. exact (EQ_MP (@lem1286043 m) (@lem1286042 m)). Qed.
Lemma lem1286045 (m : nat) (n : nat) : term128 m n.
Proof. exact (@lem1286044 m n). Qed.
Lemma lem1286046 (n : nat) (m : nat) : (term128 m n) = ((term129 m n) = (Peano.lt n m)).
Proof. exact (eq_refl (term128 m n)). Qed.
Lemma lem1286048 (n : nat) : term130 n.
Proof. exact (@lem1244936 n). Qed.
Lemma lem1286049 (n : nat) : (term130 n) = ((term131 n) = n).
Proof. exact (eq_refl (term130 n)). Qed.
Lemma lem1286081 : term132.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem1286082 (n : nat) : term133 n.
Proof. exact (@lem1286081 n). Qed.
Lemma lem1286083 (n : nat) : (term133 n) = ((term134 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term133 n)). Qed.
Lemma lem1286085 (k : nat) : term118 k.
Proof. exact (@lem1268972 k). Qed.
Lemma lem1286086 (k : nat) : (term118 k) = ((term119 k) = (term120 k)).
Proof. exact (eq_refl (term118 k)). Qed.
Lemma lem1286088 {A : Type'} (P : A -> Prop) : term135 A P.
Proof. exact (@lem10884 A P). Qed.
Lemma lem1286089 {A : Type'} (P : A -> Prop) : (term135 A P) = ((term136 A P) = (term137 A P)).
Proof. exact (eq_refl (term135 A P)). Qed.
Lemma lem1286091 (x : nadd) : term138 x.
Proof. exact (@lem1262851 x). Qed.
Lemma lem1286092 (x : nadd) : (term138 x) = (term139 x).
Proof. exact (eq_refl (term138 x)). Qed.
Lemma lem1286093 (x : nadd) : term139 x.
Proof. exact (EQ_MP (@lem1286092 x) (@lem1286091 x)). Qed.
Lemma lem1286094 (x : nadd) (B : nat) (h1 : term140 x B) : term140 x B.
Proof. exact (h1). Qed.
Lemma lem1286095 {A : Type'} (P : A -> Prop) : term141 A P.
Proof. exact (@lem10660 A P). Qed.
Lemma lem1286096 {A : Type'} (P : A -> Prop) : (term141 A P) = ((term142 A P) = (term143 A P)).
Proof. exact (eq_refl (term141 A P)). Qed.
Lemma lem1286098 (x : nadd) : term144 x.
Proof. exact (@lem1269692 x). Qed.
Lemma lem1286099 (x : nadd) : (term144 x) = (term145 x).
Proof. exact (eq_refl (term144 x)). Qed.
Lemma lem1286100 (x : nadd) : term145 x.
Proof. exact (EQ_MP (@lem1286099 x) (@lem1286098 x)). Qed.
Lemma lem1286101 (x : nadd) (y : nadd) : term146 x y.
Proof. exact (@lem1286100 x y). Qed.
Lemma lem1286102 (x : nadd) (y : nadd) : (term146 x y) = ((nadd_le x y) = (term147 x y)).
Proof. exact (eq_refl (term146 x y)). Qed.
Lemma lem1286104 (x : nadd) : term148 x.
Proof. exact (@lem1267930 x). Qed.
Lemma lem1286105 (x : nadd) : (term148 x) = (term149 x).
Proof. exact (eq_refl (term148 x)). Qed.
Lemma lem1286106 (x : nadd) : term149 x.
Proof. exact (EQ_MP (@lem1286105 x) (@lem1286104 x)). Qed.
Lemma lem1286107 (x : nadd) (y : nadd) : term150 x y.
Proof. exact (@lem1286106 x y). Qed.
Lemma lem1286108 (x : nadd) (y : nadd) : (term150 x y) = ((nadd_eq x y) = (term151 x y)).
Proof. exact (eq_refl (term150 x y)). Qed.
Lemma lem1286113 (x : nadd) (y : nadd) : (nadd_eq x y) = (term151 x y).
Proof. exact (EQ_MP (@lem1286108 x y) (@lem1286107 x y)). Qed.
Lemma lem1286114 (x : nadd) : (term152 x) = (term153 x).
Proof. exact (@lem1286113 x term154). Qed.
Lemma lem1286123 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1286124 (x : nadd) : (term155 x) = (term156 x).
Proof. exact (MK_COMB (@lem1286123) (@lem1286114 x)). Qed.
Lemma lem1286126 {A : Type'} (P : A -> Prop) : (term142 A P) = (term143 A P).
Proof. exact (EQ_MP (@lem1286096 A P) (@lem1286095 A P)). Qed.
Lemma lem1286127 (P : nat -> Prop) : (term157 P) = (term158 P).
Proof. exact (@lem1286126 nat P). Qed.
Lemma lem1286128 (x : nadd) : (term159 x) = (term160 x).
Proof. exact (@lem1286127 (term161 x)). Qed.
Lemma lem1286129 (x : nadd) (B : nat) : (term162 x B) = (term163 x B).
Proof. exact (eq_refl (term162 x B)). Qed.
Lemma lem1286130 (x : nadd) : (term164 x) = (term161 x).
Proof. exact (fun_ext (fun B : nat => @lem1286129 x B)). Qed.
Lemma lem1286131 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1286132 (x : nadd) : (term165 x) = (term153 x).
Proof. exact (MK_COMB (@lem1286131) (@lem1286130 x)). Qed.
Lemma lem1286133 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1286134 (x : nadd) : (term159 x) = (term156 x).
Proof. exact (MK_COMB (@lem1286133) (@lem1286132 x)). Qed.
Lemma lem1286135 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1286136 (x : nadd) : (term166 x) = (term167 x).
Proof. exact (MK_COMB (@lem1286135) (@lem1286134 x)). Qed.
Lemma lem1286137 (x : nadd) (B : nat) : (term162 x B) = (term163 x B).
Proof. exact (eq_refl (term162 x B)). Qed.
Lemma lem1286138 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1286139 (x : nadd) (B : nat) : (term168 x B) = (term169 x B).
Proof. exact (MK_COMB (@lem1286138) (@lem1286137 x B)). Qed.
Lemma lem1286140 (x : nadd) : (term170 x) = (term171 x).
Proof. exact (fun_ext (fun B : nat => @lem1286139 x B)). Qed.
Lemma lem1286141 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1286142 (x : nadd) : (term160 x) = (term172 x).
Proof. exact (MK_COMB (@lem1286141) (@lem1286140 x)). Qed.
Lemma lem1286143 (x : nadd) : ((term159 x) = (term160 x)) = ((term156 x) = (term172 x)).
Proof. exact (MK_COMB (@lem1286136 x) (@lem1286142 x)). Qed.
Lemma lem1286144 (x : nadd) : (term156 x) = (term172 x).
Proof. exact (EQ_MP (@lem1286143 x) (@lem1286128 x)). Qed.
Lemma lem1286153 (x : nadd) : (term155 x) = (term172 x).
Proof. exact (TRANS (@lem1286124 x) (@lem1286144 x)). Qed.
Lemma lem1286154 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1286155 (x : nadd) : (term173 x) = (term174 x).
Proof. exact (MK_COMB (@lem1286154) (@lem1286153 x)). Qed.
Lemma lem1286161 (x : nadd) (y : nadd) : (nadd_le x y) = (term147 x y).
Proof. exact (EQ_MP (@lem1286102 x y) (@lem1286101 x y)). Qed.
Lemma lem1286162 (k : nat) (N : nat) (x : nadd) : (term175 k N x) = (term176 k N x).
Proof. exact (@lem1286161 (nadd_of_num k) (term177 N x)). Qed.
Lemma lem1286171 (k : nat) (x : nadd) : (term178 k x) = (term179 k x).
Proof. exact (fun_ext (fun N : nat => @lem1286162 k N x)). Qed.
Lemma lem1286172 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1286173 (k : nat) (x : nadd) : (term180 k x) = (term181 k x).
Proof. exact (MK_COMB (@lem1286172) (@lem1286171 k x)). Qed.
Lemma lem1286178 (k : nat) (x : nadd) : (term182 k x) = (term183 k x).
Proof. exact (MK_COMB (@lem1286155 x) (@lem1286173 k x)). Qed.
Lemma lem1286181 (k : nat) (x : nadd) : (term183 k x) = (term182 k x).
Proof. exact (SYM (@lem1286178 k x)). Qed.
Lemma lem1286182 (x : nadd) (h1 : term172 x) : term172 x.
Proof. exact (h1). Qed.
Lemma lem1286183 (B : nat) (k : nat) (x : nadd) (h1 : term172 x) : term184 x B k.
Proof. exact (@lem1286182 x h1 (Nat.add B k)). Qed.
Lemma lem1286184 (x : nadd) (B : nat) (k : nat) : (term184 x B k) = (term185 x B k).
Proof. exact (eq_refl (term184 x B k)). Qed.
Lemma lem1286185 (B : nat) (k : nat) (x : nadd) (h1 : term172 x) : term185 x B k.
Proof. exact (EQ_MP (@lem1286184 x B k) (@lem1286183 B k x h1)). Qed.
Lemma lem1286189 {A : Type'} (P : A -> Prop) : (term136 A P) = (term137 A P).
Proof. exact (EQ_MP (@lem1286089 A P) (@lem1286088 A P)). Qed.
Lemma lem1286190 (P : nat -> Prop) : (term186 P) = (term187 P).
Proof. exact (@lem1286189 nat P). Qed.
Lemma lem1286191 (x : nadd) (B : nat) (k : nat) : (term188 x B k) = (term189 x B k).
Proof. exact (@lem1286190 (term190 x B k)). Qed.
Lemma lem1286192 (x : nadd) (n : nat) (B : nat) (k : nat) : (term191 x B k n) = (term192 x n B k).
Proof. exact (eq_refl (term191 x B k n)). Qed.
Lemma lem1286193 (x : nadd) (B : nat) (k : nat) : (term193 x B k) = (term190 x B k).
Proof. exact (fun_ext (fun n : nat => @lem1286192 x n B k)). Qed.
Lemma lem1286194 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1286195 (x : nadd) (B : nat) (k : nat) : (term194 x B k) = (term195 x B k).
Proof. exact (MK_COMB (@lem1286194) (@lem1286193 x B k)). Qed.
Lemma lem1286196 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1286197 (x : nadd) (B : nat) (k : nat) : (term188 x B k) = (term185 x B k).
Proof. exact (MK_COMB (@lem1286196) (@lem1286195 x B k)). Qed.
Lemma lem1286198 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1286199 (x : nadd) (B : nat) (k : nat) : (term196 x B k) = (term197 x B k).
Proof. exact (MK_COMB (@lem1286198) (@lem1286197 x B k)). Qed.
Lemma lem1286200 (x : nadd) (n : nat) (B : nat) (k : nat) : (term191 x B k n) = (term192 x n B k).
Proof. exact (eq_refl (term191 x B k n)). Qed.
Lemma lem1286201 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1286202 (x : nadd) (n : nat) (B : nat) (k : nat) : (term198 x B k n) = (term199 x n B k).
Proof. exact (MK_COMB (@lem1286201) (@lem1286200 x n B k)). Qed.
Lemma lem1286203 (x : nadd) (B : nat) (k : nat) : (term200 x B k) = (term201 x B k).
Proof. exact (fun_ext (fun n : nat => @lem1286202 x n B k)). Qed.
Lemma lem1286204 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1286205 (x : nadd) (B : nat) (k : nat) : (term189 x B k) = (term202 x B k).
Proof. exact (MK_COMB (@lem1286204) (@lem1286203 x B k)). Qed.
Lemma lem1286206 (x : nadd) (B : nat) (k : nat) : ((term188 x B k) = (term189 x B k)) = ((term185 x B k) = (term202 x B k)).
Proof. exact (MK_COMB (@lem1286199 x B k) (@lem1286205 x B k)). Qed.
Lemma lem1286207 (x : nadd) (B : nat) (k : nat) : (term185 x B k) = (term202 x B k).
Proof. exact (EQ_MP (@lem1286206 x B k) (@lem1286191 x B k)). Qed.
Lemma lem1286213 (k : nat) : (term119 k) = (term120 k).
Proof. exact (EQ_MP (@lem1286086 k) (@lem1286085 k)). Qed.
Lemma lem1286214 : term203 = term204.
Proof. exact (@lem1286213 (NUMERAL 0)). Qed.
Lemma lem1286215 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1286216 (n : nat) : (term205 n) = (term206 n).
Proof. exact (MK_COMB (@lem1286214) (@lem1286215 n)). Qed.
Lemma lem1286218 {A B : Type'} (f : A -> B) (y : A) : (term207 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1286219 (f : nat -> nat) (y : nat) : (term208 f y) = (f y).
Proof. exact (@lem1286218 nat nat f y). Qed.
Lemma lem1286220 (n : nat) : (term209 n) = (term206 n).
Proof. exact (@lem1286219 term204 n). Qed.
Lemma lem1286221 (n : nat) : (term206 n) = (term134 n).
Proof. exact (eq_refl (term206 n)). Qed.
Lemma lem1286222 : term210 = term204.
Proof. exact (fun_ext (fun n : nat => @lem1286221 n)). Qed.
Lemma lem1286223 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1286224 (n : nat) : (term209 n) = (term206 n).
Proof. exact (MK_COMB (@lem1286222) (@lem1286223 n)). Qed.
Lemma lem1286225 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1286226 (n : nat) : (term211 n) = (term212 n).
Proof. exact (MK_COMB (@lem1286225) (@lem1286224 n)). Qed.
Lemma lem1286227 (n : nat) : (term206 n) = (term134 n).
Proof. exact (eq_refl (term206 n)). Qed.
Lemma lem1286228 (n : nat) : ((term209 n) = (term206 n)) = ((term206 n) = (term134 n)).
Proof. exact (MK_COMB (@lem1286226 n) (@lem1286227 n)). Qed.
Lemma lem1286229 (n : nat) : (term206 n) = (term134 n).
Proof. exact (EQ_MP (@lem1286228 n) (@lem1286220 n)). Qed.
Lemma lem1286230 (n : nat) : (term205 n) = (term134 n).
Proof. exact (TRANS (@lem1286216 n) (@lem1286229 n)). Qed.
Lemma lem1286231 (x : nadd) (n : nat) : (term213 x n) = (term213 x n).
Proof. exact (eq_refl (term213 x n)). Qed.
Lemma lem1286232 (x : nadd) (n : nat) : (term214 x n) = (term215 x n).
Proof. exact (MK_COMB (@lem1286231 x n) (@lem1286230 n)). Qed.
Lemma lem1286233 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1286234 (x : nadd) (n : nat) : (term216 x n) = (term217 x n).
Proof. exact (MK_COMB (@lem1286233) (@lem1286232 x n)). Qed.
Lemma lem1286235 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1286236 (x : nadd) (n : nat) : (term218 x n) = (term219 x n).
Proof. exact (MK_COMB (@lem1286235) (@lem1286234 x n)). Qed.
Lemma lem1286237 (B : nat) (k : nat) : (Nat.add B k) = (Nat.add B k).
Proof. exact (eq_refl (Nat.add B k)). Qed.
Lemma lem1286238 (x : nadd) (n : nat) (B : nat) (k : nat) : (term192 x n B k) = (term220 x n B k).
Proof. exact (MK_COMB (@lem1286236 x n) (@lem1286237 B k)). Qed.
Lemma lem1286239 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1286240 (x : nadd) (n : nat) (B : nat) (k : nat) : (term199 x n B k) = (term221 x n B k).
Proof. exact (MK_COMB (@lem1286239) (@lem1286238 x n B k)). Qed.
Lemma lem1286241 (x : nadd) (B : nat) (k : nat) : (term201 x B k) = (term222 x B k).
Proof. exact (fun_ext (fun n : nat => @lem1286240 x n B k)). Qed.
Lemma lem1286242 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1286243 (x : nadd) (B : nat) (k : nat) : (term202 x B k) = (term223 x B k).
Proof. exact (MK_COMB (@lem1286242) (@lem1286241 x B k)). Qed.
Lemma lem1286248 (x : nadd) (B : nat) (k : nat) : (term185 x B k) = (term223 x B k).
Proof. exact (TRANS (@lem1286207 x B k) (@lem1286243 x B k)). Qed.
Lemma lem1286249 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1286250 (x : nadd) (B : nat) (k : nat) : (term224 x B k) = (term225 x B k).
Proof. exact (MK_COMB (@lem1286249) (@lem1286248 x B k)). Qed.
Lemma lem1286264 (k : nat) : (term119 k) = (term120 k).
Proof. exact (EQ_MP (@lem1286086 k) (@lem1286085 k)). Qed.
Lemma lem1286265 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1286266 (k : nat) (n : nat) : (term226 k n) = (term227 k n).
Proof. exact (MK_COMB (@lem1286264 k) (@lem1286265 n)). Qed.
Lemma lem1286268 {A B : Type'} (f : A -> B) (y : A) : (term207 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1286269 (f : nat -> nat) (y : nat) : (term208 f y) = (f y).
Proof. exact (@lem1286268 nat nat f y). Qed.
Lemma lem1286270 (k : nat) (n : nat) : (term228 k n) = (term227 k n).
Proof. exact (@lem1286269 (term120 k) n). Qed.
Lemma lem1286271 (k : nat) (n : nat) : (term227 k n) = (Nat.mul k n).
Proof. exact (eq_refl (term227 k n)). Qed.
Lemma lem1286272 (k : nat) : (term229 k) = (term120 k).
Proof. exact (fun_ext (fun n : nat => @lem1286271 k n)). Qed.
Lemma lem1286273 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1286274 (k : nat) (n : nat) : (term228 k n) = (term227 k n).
Proof. exact (MK_COMB (@lem1286272 k) (@lem1286273 n)). Qed.
Lemma lem1286275 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1286276 (k : nat) (n : nat) : (term230 k n) = (term231 k n).
Proof. exact (MK_COMB (@lem1286275) (@lem1286274 k n)). Qed.
Lemma lem1286277 (k : nat) (n : nat) : (term227 k n) = (Nat.mul k n).
Proof. exact (eq_refl (term227 k n)). Qed.
Lemma lem1286278 (k : nat) (n : nat) : ((term228 k n) = (term227 k n)) = ((term227 k n) = (Nat.mul k n)).
Proof. exact (MK_COMB (@lem1286276 k n) (@lem1286277 k n)). Qed.
Lemma lem1286279 (k : nat) (n : nat) : (term227 k n) = (Nat.mul k n).
Proof. exact (EQ_MP (@lem1286278 k n) (@lem1286270 k n)). Qed.
Lemma lem1286280 (k : nat) (n : nat) : (term226 k n) = (Nat.mul k n).
Proof. exact (TRANS (@lem1286266 k n) (@lem1286279 k n)). Qed.
Lemma lem1286281 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1286282 (k : nat) (n : nat) : (term232 k n) = (term233 k n).
Proof. exact (MK_COMB (@lem1286281) (@lem1286280 k n)). Qed.
Lemma lem1286283 (N : nat) (x : nadd) (n : nat) (B : nat) : (term234 N x n B) = (term234 N x n B).
Proof. exact (eq_refl (term234 N x n B)). Qed.
Lemma lem1286284 (k : nat) (N : nat) (x : nadd) (n : nat) (B : nat) : (term235 k N x n B) = (term236 k N x n B).
Proof. exact (MK_COMB (@lem1286282 k n) (@lem1286283 N x n B)). Qed.
Lemma lem1286285 (k : nat) (N : nat) (x : nadd) (B : nat) : (term237 k N x B) = (term238 k N x B).
Proof. exact (fun_ext (fun n : nat => @lem1286284 k N x n B)). Qed.
Lemma lem1286286 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1286287 (k : nat) (N : nat) (x : nadd) (B : nat) : (term239 k N x B) = (term240 k N x B).
Proof. exact (MK_COMB (@lem1286286) (@lem1286285 k N x B)). Qed.
Lemma lem1286292 (k : nat) (N : nat) (x : nadd) : (term241 k N x) = (term242 k N x).
Proof. exact (fun_ext (fun B : nat => @lem1286287 k N x B)). Qed.
Lemma lem1286293 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1286294 (k : nat) (N : nat) (x : nadd) : (term176 k N x) = (term243 k N x).
Proof. exact (MK_COMB (@lem1286293) (@lem1286292 k N x)). Qed.
Lemma lem1286299 (k : nat) (x : nadd) : (term179 k x) = (term244 k x).
Proof. exact (fun_ext (fun N : nat => @lem1286294 k N x)). Qed.
Lemma lem1286300 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1286301 (k : nat) (x : nadd) : (term181 k x) = (term245 k x).
Proof. exact (MK_COMB (@lem1286300) (@lem1286299 k x)). Qed.
Lemma lem1286306 (B : nat) (k : nat) (x : nadd) : (term246 B k x) = (term247 B k x).
Proof. exact (MK_COMB (@lem1286250 x B k) (@lem1286301 k x)). Qed.
Lemma lem1286309 (B : nat) (k : nat) (x : nadd) : (term247 B k x) = (term246 B k x).
Proof. exact (SYM (@lem1286306 B k x)). Qed.
Lemma lem1286317 (n : nat) (m : nat) : (term129 m n) = (Peano.lt n m).
Proof. exact (EQ_MP (@lem1286046 n m) (@lem1286045 m n)). Qed.
Lemma lem1286318 (B : nat) (k : nat) (x : nadd) (n : nat) : (term221 x n B k) = (term248 B k x n).
Proof. exact (@lem1286317 (Nat.add B k) (term217 x n)). Qed.
Lemma lem1286320 (n : nat) : (term134 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1286083 n) (@lem1286082 n)). Qed.
Lemma lem1286321 (x : nadd) (n : nat) : (term213 x n) = (term213 x n).
Proof. exact (eq_refl (term213 x n)). Qed.
Lemma lem1286322 (x : nadd) (n : nat) : (term215 x n) = (term249 x n).
Proof. exact (MK_COMB (@lem1286321 x n) (@lem1286320 n)). Qed.
Lemma lem1286323 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1286324 (x : nadd) (n : nat) : (term217 x n) = (term250 x n).
Proof. exact (MK_COMB (@lem1286323) (@lem1286322 x n)). Qed.
Lemma lem1286326 (n : nat) : (term131 n) = n.
Proof. exact (EQ_MP (@lem1286049 n) (@lem1286048 n)). Qed.
Lemma lem1286327 (x : nadd) (n : nat) : (term250 x n) = (dest_nadd x n).
Proof. exact (@lem1286326 (dest_nadd x n)). Qed.
Lemma lem1286328 (x : nadd) (n : nat) : (term217 x n) = (dest_nadd x n).
Proof. exact (TRANS (@lem1286324 x n) (@lem1286327 x n)). Qed.
Lemma lem1286329 (B : nat) (k : nat) : (term251 B k) = (term251 B k).
Proof. exact (eq_refl (term251 B k)). Qed.
Lemma lem1286330 (B : nat) (k : nat) (x : nadd) (n : nat) : (term248 B k x n) = (term252 B k x n).
Proof. exact (MK_COMB (@lem1286329 B k) (@lem1286328 x n)). Qed.
Lemma lem1286331 (B : nat) (k : nat) (x : nadd) (n : nat) : (term221 x n B k) = (term252 B k x n).
Proof. exact (TRANS (@lem1286318 B k x n) (@lem1286330 B k x n)). Qed.
Lemma lem1286332 (B : nat) (k : nat) (x : nadd) : (term222 x B k) = (term253 B k x).
Proof. exact (fun_ext (fun n : nat => @lem1286331 B k x n)). Qed.
Lemma lem1286333 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1286334 (B : nat) (k : nat) (x : nadd) : (term223 x B k) = (term254 B k x).
Proof. exact (MK_COMB (@lem1286333) (@lem1286332 B k x)). Qed.
Lemma lem1286339 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1286340 (B : nat) (k : nat) (x : nadd) : (term225 x B k) = (term255 B k x).
Proof. exact (MK_COMB (@lem1286339) (@lem1286334 B k x)). Qed.
Lemma lem1286353 (k : nat) (x : nadd) : (term245 k x) = (term245 k x).
Proof. exact (eq_refl (term245 k x)). Qed.
Lemma lem1286354 (B : nat) (k : nat) (x : nadd) : (term247 B k x) = (term256 B k x).
Proof. exact (MK_COMB (@lem1286340 B k x) (@lem1286353 k x)). Qed.
Lemma lem1286357 (B : nat) (k : nat) (x : nadd) : (term256 B k x) = (term247 B k x).
Proof. exact (SYM (@lem1286354 B k x)). Qed.
Lemma lem1286358 (B : nat) (k : nat) (x : nadd) (h1 : term254 B k x) : term254 B k x.
Proof. exact (h1). Qed.
Lemma lem1286361 (x : nadd) (y : nadd) : (term124 x y) = (term125 x y).
Proof. exact (EQ_MP (@lem1286040 x y) (@lem1286039 x y)). Qed.
Lemma lem1286362 (N : nat) (x : nadd) : (term257 N x) = (term258 N x).
Proof. exact (@lem1286361 (nadd_of_num N) x). Qed.
Lemma lem1286364 (k : nat) : (term119 k) = (term120 k).
Proof. exact (EQ_MP (@lem1286034 k) (@lem1286033 k)). Qed.
Lemma lem1286365 (N : nat) : (term119 N) = (term120 N).
Proof. exact (@lem1286364 N). Qed.
Lemma lem1286366 (x : nadd) (n : nat) : (dest_nadd x n) = (dest_nadd x n).
Proof. exact (eq_refl (dest_nadd x n)). Qed.
Lemma lem1286367 (N : nat) (x : nadd) (n : nat) : (term259 N x n) = (term260 N x n).
Proof. exact (MK_COMB (@lem1286365 N) (@lem1286366 x n)). Qed.
Lemma lem1286369 {A B : Type'} (f : A -> B) (y : A) : (term207 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1286370 (f : nat -> nat) (y : nat) : (term208 f y) = (f y).
Proof. exact (@lem1286369 nat nat f y). Qed.
Lemma lem1286371 (N : nat) (x : nadd) (n : nat) : (term261 N x n) = (term260 N x n).
Proof. exact (@lem1286370 (term120 N) (dest_nadd x n)). Qed.
Lemma lem1286372 (N : nat) (n : nat) : (term227 N n) = (Nat.mul N n).
Proof. exact (eq_refl (term227 N n)). Qed.
Lemma lem1286373 (N : nat) : (term229 N) = (term120 N).
Proof. exact (fun_ext (fun n : nat => @lem1286372 N n)). Qed.
Lemma lem1286374 (x : nadd) (n : nat) : (dest_nadd x n) = (dest_nadd x n).
Proof. exact (eq_refl (dest_nadd x n)). Qed.
Lemma lem1286375 (N : nat) (x : nadd) (n : nat) : (term261 N x n) = (term260 N x n).
Proof. exact (MK_COMB (@lem1286373 N) (@lem1286374 x n)). Qed.
Lemma lem1286376 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1286377 (N : nat) (x : nadd) (n : nat) : (term262 N x n) = (term263 N x n).
Proof. exact (MK_COMB (@lem1286376) (@lem1286375 N x n)). Qed.
Lemma lem1286378 (N : nat) (x : nadd) (n : nat) : (term260 N x n) = (term264 N x n).
Proof. exact (eq_refl (term260 N x n)). Qed.
Lemma lem1286379 (N : nat) (x : nadd) (n : nat) : ((term261 N x n) = (term260 N x n)) = ((term260 N x n) = (term264 N x n)).
Proof. exact (MK_COMB (@lem1286377 N x n) (@lem1286378 N x n)). Qed.
Lemma lem1286380 (N : nat) (x : nadd) (n : nat) : (term260 N x n) = (term264 N x n).
Proof. exact (EQ_MP (@lem1286379 N x n) (@lem1286371 N x n)). Qed.
Lemma lem1286381 (N : nat) (x : nadd) (n : nat) : (term259 N x n) = (term264 N x n).
Proof. exact (TRANS (@lem1286367 N x n) (@lem1286380 N x n)). Qed.
Lemma lem1286382 (N : nat) (x : nadd) : (term258 N x) = (term265 N x).
Proof. exact (fun_ext (fun n : nat => @lem1286381 N x n)). Qed.
Lemma lem1286383 (N : nat) (x : nadd) : (term257 N x) = (term265 N x).
Proof. exact (TRANS (@lem1286362 N x) (@lem1286382 N x)). Qed.
Lemma lem1286384 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem1286385 (N : nat) (x : nadd) (i : nat) : (term266 N x i) = (term267 N x i).
Proof. exact (MK_COMB (@lem1286383 N x) (@lem1286384 i)). Qed.
Lemma lem1286387 {A B : Type'} (f : A -> B) (y : A) : (term207 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1286388 (f : nat -> nat) (y : nat) : (term208 f y) = (f y).
Proof. exact (@lem1286387 nat nat f y). Qed.
Lemma lem1286389 (N : nat) (x : nadd) (i : nat) : (term268 N x i) = (term267 N x i).
Proof. exact (@lem1286388 (term265 N x) i). Qed.
Lemma lem1286390 (N : nat) (x : nadd) (n : nat) : (term267 N x n) = (term264 N x n).
Proof. exact (eq_refl (term267 N x n)). Qed.
Lemma lem1286391 (N : nat) (x : nadd) : (term269 N x) = (term265 N x).
Proof. exact (fun_ext (fun n : nat => @lem1286390 N x n)). Qed.
Lemma lem1286392 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem1286393 (N : nat) (x : nadd) (i : nat) : (term268 N x i) = (term267 N x i).
Proof. exact (MK_COMB (@lem1286391 N x) (@lem1286392 i)). Qed.
Lemma lem1286394 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1286395 (N : nat) (x : nadd) (i : nat) : (term270 N x i) = (term271 N x i).
Proof. exact (MK_COMB (@lem1286394) (@lem1286393 N x i)). Qed.
Lemma lem1286396 (N : nat) (x : nadd) (i : nat) : (term267 N x i) = (term264 N x i).
Proof. exact (eq_refl (term267 N x i)). Qed.
Lemma lem1286397 (N : nat) (x : nadd) (i : nat) : ((term268 N x i) = (term267 N x i)) = ((term267 N x i) = (term264 N x i)).
Proof. exact (MK_COMB (@lem1286395 N x i) (@lem1286396 N x i)). Qed.
Lemma lem1286398 (N : nat) (x : nadd) (i : nat) : (term267 N x i) = (term264 N x i).
Proof. exact (EQ_MP (@lem1286397 N x i) (@lem1286389 N x i)). Qed.
Lemma lem1286399 (N : nat) (x : nadd) (i : nat) : (term266 N x i) = (term264 N x i).
Proof. exact (TRANS (@lem1286385 N x i) (@lem1286398 N x i)). Qed.
Lemma lem1286400 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1286401 (N : nat) (x : nadd) (i : nat) : (term272 N x i) = (term273 N x i).
Proof. exact (MK_COMB (@lem1286400) (@lem1286399 N x i)). Qed.
Lemma lem1286402 (B : nat) (N : nat) : (Nat.mul B N) = (Nat.mul B N).
Proof. exact (eq_refl (Nat.mul B N)). Qed.
Lemma lem1286403 (x : nadd) (i : nat) (B : nat) (N : nat) : (term274 x i B N) = (term275 x i B N).
Proof. exact (MK_COMB (@lem1286401 N x i) (@lem1286402 B N)). Qed.
Lemma lem1286404 (k : nat) (i : nat) : (term233 k i) = (term233 k i).
Proof. exact (eq_refl (term233 k i)). Qed.
Lemma lem1286405 (k : nat) (x : nadd) (i : nat) (B : nat) (N : nat) : (term276 k x i B N) = (term277 k x i B N).
Proof. exact (MK_COMB (@lem1286404 k i) (@lem1286403 x i B N)). Qed.
Lemma lem1286406 (k : nat) (x : nadd) (i : nat) (B : nat) (N : nat) : (term277 k x i B N) = (term276 k x i B N).
Proof. exact (SYM (@lem1286405 k x i B N)). Qed.
Lemma lem1286408 (m : nat) (n : nat) : term112 m n.
Proof. exact (EQ_MP (@lem1286031 m n) (@lem1286030 m n)). Qed.
Lemma lem1286409 (k : nat) (x : nadd) (i : nat) (B : nat) (N : nat) : term278 k x i B N.
Proof. exact (@lem1286408 (Nat.mul k i) (term275 x i B N)). Qed.
Lemma lem1286413 (m : nat) (n : nat) (p : nat) : (term76 m n p) = (term75 m n p).
Proof. exact (EQ_MP (@lem1285987 m n p) (@lem1285986 m n p)). Qed.
Lemma lem1286414 (x : nadd) (N : nat) (B : nat) (i : nat) : (term279 x N B i) = (term280 x N B i).
Proof. exact (@lem1286413 (term264 N x i) (Nat.mul B N) (Nat.mul B i)). Qed.
Lemma lem1286416 (m : nat) (n : nat) (p : nat) : (term62 n m p) = (term61 m n p).
Proof. exact (EQ_MP (@lem1285978 m n p) (@lem1285977 m n p)). Qed.
Lemma lem1286417 (B : nat) (N : nat) (i : nat) : (term62 N B i) = (term61 B N i).
Proof. exact (@lem1286416 B N i). Qed.
Lemma lem1286418 (N : nat) (x : nadd) (i : nat) : (term273 N x i) = (term273 N x i).
Proof. exact (eq_refl (term273 N x i)). Qed.
Lemma lem1286419 (x : nadd) (B : nat) (N : nat) (i : nat) : (term280 x N B i) = (term281 x B N i).
Proof. exact (MK_COMB (@lem1286418 N x i) (@lem1286417 B N i)). Qed.
Lemma lem1286422 (x : nadd) (B : nat) (N : nat) (i : nat) : (term279 x N B i) = (term281 x B N i).
Proof. exact (TRANS (@lem1286414 x N B i) (@lem1286419 x B N i)). Qed.
Lemma lem1286423 (k : nat) (B : nat) (i : nat) : (term282 k B i) = (term282 k B i).
Proof. exact (eq_refl (term282 k B i)). Qed.
Lemma lem1286424 (k : nat) (x : nadd) (B : nat) (N : nat) (i : nat) : (term283 k x N B i) = (term284 k x B N i).
Proof. exact (MK_COMB (@lem1286423 k B i) (@lem1286422 x B N i)). Qed.
Lemma lem1286425 (k : nat) (x : nadd) (N : nat) (B : nat) (i : nat) : (term284 k x B N i) = (term283 k x N B i).
Proof. exact (SYM (@lem1286424 k x B N i)). Qed.
Lemma lem1286427 (m : nat) (p : nat) : term55 m p.
Proof. exact (EQ_MP (@lem1285933 m p) (@lem1285932 m p)). Qed.
Lemma lem1286428 (k : nat) (x : nadd) (B : nat) (N : nat) (i : nat) : term285 k x B N i.
Proof. exact (@lem1286427 (term21 k B i) (term281 x B N i)). Qed.
Lemma lem1286438 (n : nat) (m : nat) (p : nat) : (term42 m n p) = (term43 n m p).
Proof. exact (EQ_MP (@lem1285905 n m p) (@lem1285904 n m p)). Qed.
Lemma lem1286439 (x : nadd) (B : nat) (m : nat) (n : nat) : (term286 x B m n) = (term287 x B m n).
Proof. exact (@lem1286438 (term264 n x m) (term264 m x n) (term61 B m n)). Qed.
Lemma lem1286442 (x : nadd) (B : nat) (m : nat) : (term288 x B m) = (term289 x B m).
Proof. exact (fun_ext (fun n : nat => @lem1286439 x B m n)). Qed.
Lemma lem1286443 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1286444 (x : nadd) (B : nat) (m : nat) : (term290 x B m) = (term291 x B m).
Proof. exact (MK_COMB (@lem1286443) (@lem1286442 x B m)). Qed.
Lemma lem1286449 (x : nadd) (B : nat) : (term292 x B) = (term293 x B).
Proof. exact (fun_ext (fun m : nat => @lem1286444 x B m)). Qed.
Lemma lem1286450 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1286451 (x : nadd) (B : nat) : (term140 x B) = (term294 x B).
Proof. exact (MK_COMB (@lem1286450) (@lem1286449 x B)). Qed.
Lemma lem1286456 (x : nadd) (B : nat) (h1 : term140 x B) : term294 x B.
Proof. exact (EQ_MP (@lem1286451 x B) (@lem1286094 x B h1)). Qed.
Lemma lem1286458 (B : nat) (k : nat) (x : nadd) (N : nat) (h1 : term252 B k x N) : term252 B k x N.
Proof. exact (h1). Qed.
Lemma lem1286459 (m : nat) (x : nadd) (B : nat) (h1 : term140 x B) : term295 x B m.
Proof. exact (@lem1286456 x B h1 m). Qed.
Lemma lem1286460 (x : nadd) (B : nat) (m : nat) : (term295 x B m) = (term291 x B m).
Proof. exact (eq_refl (term295 x B m)). Qed.
Lemma lem1286461 (m : nat) (x : nadd) (B : nat) (h1 : term140 x B) : term291 x B m.
Proof. exact (EQ_MP (@lem1286460 x B m) (@lem1286459 m x B h1)). Qed.
Lemma lem1286462 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term140 x B) : term296 x B m n.
Proof. exact (@lem1286461 m x B h1 n). Qed.
Lemma lem1286463 (x : nadd) (B : nat) (m : nat) (n : nat) : (term296 x B m n) = (term287 x B m n).
Proof. exact (eq_refl (term296 x B m n)). Qed.
Lemma lem1286464 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term140 x B) : term287 x B m n.
Proof. exact (EQ_MP (@lem1286463 x B m n) (@lem1286462 m n x B h1)). Qed.
Lemma lem1286465 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term140 x B) : term297 x B m n.
Proof. exact (proj2 (@lem1286464 m n x B h1)). Qed.
Lemma lem1286466 (x : nadd) (B : nat) (m : nat) (n : nat) : (term297 x B m n) = ((term297 x B m n) = True).
Proof. exact (@lem7 (term297 x B m n)). Qed.
Lemma lem1286476 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term140 x B) : (term297 x B m n) = True.
Proof. exact (EQ_MP (@lem1286466 x B m n) (@lem1286465 m n x B h1)). Qed.
Lemma lem1286477 (N : nat) (i : nat) (x : nadd) (B : nat) (h1 : term140 x B) : (term297 x B N i) = True.
Proof. exact (@lem1286476 N i x B h1). Qed.
Lemma lem1286478 (k : nat) (B : nat) (i : nat) (x : nadd) (N : nat) : (term298 k B i x N) = (term298 k B i x N).
Proof. exact (eq_refl (term298 k B i x N)). Qed.
Lemma lem1286479 (k : nat) (i : nat) (N : nat) (x : nadd) (B : nat) (h1 : term140 x B) : (term299 k x B N i) = (term300 k B i x N).
Proof. exact (MK_COMB (@lem1286478 k B i x N) (@lem1286477 N i x B h1)). Qed.
Lemma lem1286481 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1286482 (k : nat) (B : nat) (i : nat) (x : nadd) (N : nat) : (term300 k B i x N) = (term301 k B i x N).
Proof. exact (@lem1286481 (term301 k B i x N)). Qed.
Lemma lem1286483 (k : nat) (i : nat) (N : nat) (x : nadd) (B : nat) (h1 : term140 x B) : (term299 k x B N i) = (term301 k B i x N).
Proof. exact (TRANS (@lem1286479 k i N x B h1) (@lem1286482 k B i x N)). Qed.
Lemma lem1286484 (k : nat) (N : nat) (i : nat) (x : nadd) (B : nat) (h1 : term140 x B) : (term301 k B i x N) = (term299 k x B N i).
Proof. exact (SYM (@lem1286483 k i N x B h1)). Qed.
Lemma lem1286486 (m : nat) (n : nat) (p : nat) : (term21 m n p) = (term20 m n p).
Proof. exact (EQ_MP (@lem1285896 m n p) (@lem1285895 m n p)). Qed.
Lemma lem1286487 (k : nat) (B : nat) (i : nat) : (term21 k B i) = (term20 k B i).
Proof. exact (@lem1286486 k B i). Qed.
Lemma lem1286488 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1286489 (k : nat) (B : nat) (i : nat) : (term282 k B i) = (term302 k B i).
Proof. exact (MK_COMB (@lem1286488) (@lem1286487 k B i)). Qed.
Lemma lem1286490 (i : nat) (x : nadd) (N : nat) : (term264 i x N) = (term264 i x N).
Proof. exact (eq_refl (term264 i x N)). Qed.
Lemma lem1286491 (k : nat) (B : nat) (i : nat) (x : nadd) (N : nat) : (term301 k B i x N) = (term303 k B i x N).
Proof. exact (MK_COMB (@lem1286489 k B i) (@lem1286490 i x N)). Qed.
Lemma lem1286492 (k : nat) (B : nat) (i : nat) (x : nadd) (N : nat) : (term303 k B i x N) = (term301 k B i x N).
Proof. exact (SYM (@lem1286491 k B i x N)). Qed.
Lemma lem1286494 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem1285869 n m) (@lem1285868 m n)). Qed.
Lemma lem1286495 (x : nadd) (N : nat) (i : nat) : (term264 i x N) = (term304 x N i).
Proof. exact (@lem1286494 (dest_nadd x N) i). Qed.
Lemma lem1286496 (k : nat) (B : nat) (i : nat) : (term302 k B i) = (term302 k B i).
Proof. exact (eq_refl (term302 k B i)). Qed.
Lemma lem1286497 (k : nat) (B : nat) (x : nadd) (N : nat) (i : nat) : (term303 k B i x N) = (term305 k B x N i).
Proof. exact (MK_COMB (@lem1286496 k B i) (@lem1286495 x N i)). Qed.
Lemma lem1286498 (k : nat) (B : nat) (i : nat) (x : nadd) (N : nat) : (term305 k B x N i) = (term303 k B i x N).
Proof. exact (SYM (@lem1286497 k B x N i)). Qed.
Lemma lem1286500 (m : nat) (n : nat) (p : nat) : (term15 m n p) = (term16 m n p).
Proof. exact (EQ_MP (@lem1285863 m n p) (@lem1285862 m n p)). Qed.
Lemma lem1286501 (k : nat) (B : nat) (x : nadd) (N : nat) (i : nat) : (term305 k B x N i) = (term306 k B x N i).
Proof. exact (@lem1286500 (Nat.add k B) (dest_nadd x N) i). Qed.
Lemma lem1286506 (k : nat) (B : nat) (x : nadd) (N : nat) (i : nat) : (term306 k B x N i) = (term305 k B x N i).
Proof. exact (SYM (@lem1286501 k B x N i)). Qed.
Lemma lem1286508 (m : nat) (n : nat) : term7 m n.
Proof. exact (EQ_MP (@lem1285854 m n) (@lem1285853 m n)). Qed.
Lemma lem1286509 (k : nat) (B : nat) (x : nadd) (N : nat) : term307 k B x N.
Proof. exact (@lem1286508 (Nat.add k B) (dest_nadd x N)). Qed.
Lemma lem1286511 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem1285831 n m) (@lem1285830 m n)). Qed.
Lemma lem1286512 (B : nat) (k : nat) : (Nat.add k B) = (Nat.add B k).
Proof. exact (@lem1286511 B k). Qed.
Lemma lem1286513 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem1286514 (B : nat) (k : nat) : (term251 k B) = (term251 B k).
Proof. exact (MK_COMB (@lem1286513) (@lem1286512 B k)). Qed.
Lemma lem1286515 (x : nadd) (N : nat) : (dest_nadd x N) = (dest_nadd x N).
Proof. exact (eq_refl (dest_nadd x N)). Qed.
Lemma lem1286516 (B : nat) (k : nat) (x : nadd) (N : nat) : (term252 k B x N) = (term252 B k x N).
Proof. exact (MK_COMB (@lem1286514 B k) (@lem1286515 x N)). Qed.
Lemma lem1286517 (k : nat) (B : nat) (x : nadd) (N : nat) : (term252 B k x N) = (term252 k B x N).
Proof. exact (SYM (@lem1286516 B k x N)). Qed.
Lemma lem1286518 (B : nat) (k : nat) (x : nadd) (N : nat) (h1 : term252 B k x N) : term252 k B x N.
Proof. exact (EQ_MP (@lem1286517 k B x N) (@lem1286458 B k x N h1)). Qed.
Lemma lem1286519 (B : nat) (k : nat) (x : nadd) (N : nat) (h1 : term252 B k x N) : term308 k B x N.
Proof. exact (@lem1286509 k B x N (@lem1286518 B k x N h1)). Qed.
Lemma lem1286520 (i : nat) (B : nat) (k : nat) (x : nadd) (N : nat) (h1 : term252 B k x N) : term306 k B x N i.
Proof. exact (or_intro1 (@lem1286519 B k x N h1) (i = (NUMERAL 0))). Qed.
Lemma lem1286521 (i : nat) (B : nat) (k : nat) (x : nadd) (N : nat) (h1 : term252 B k x N) : term305 k B x N i.
Proof. exact (EQ_MP (@lem1286506 k B x N i) (@lem1286520 i B k x N h1)). Qed.
Lemma lem1286522 (i : nat) (B : nat) (k : nat) (x : nadd) (N : nat) (h1 : term252 B k x N) : term303 k B i x N.
Proof. exact (EQ_MP (@lem1286498 k B i x N) (@lem1286521 i B k x N h1)). Qed.
Lemma lem1286523 (i : nat) (B : nat) (k : nat) (x : nadd) (N : nat) (h1 : term252 B k x N) : term301 k B i x N.
Proof. exact (EQ_MP (@lem1286492 k B i x N) (@lem1286522 i B k x N h1)). Qed.
Lemma lem1286524 (i : nat) (B : nat) (k : nat) (x : nadd) (N : nat) (h1 : term140 x B) (h2 : term252 B k x N) : term299 k x B N i.
Proof. exact (EQ_MP (@lem1286484 k N i x B h1) (@lem1286523 i B k x N h2)). Qed.
Lemma lem1286525 (i : nat) (B : nat) (k : nat) (x : nadd) (N : nat) (h1 : term140 x B) (h2 : term252 B k x N) : (term252 B k x N) = (term299 k x B N i).
Proof. exact (prop_ext (fun h3 : term252 B k x N => @lem1286524 i B k x N h1 h2) (fun h3 : term299 k x B N i => @lem1286458 B k x N h2)). Qed.
Lemma lem1286526 (i : nat) (B : nat) (k : nat) (x : nadd) (N : nat) (h1 : term140 x B) (h2 : term252 B k x N) : term299 k x B N i.
Proof. exact (EQ_MP (@lem1286525 i B k x N h1 h2) (@lem1286458 B k x N h2)). Qed.
Lemma lem1286527 (i : nat) (B : nat) (k : nat) (x : nadd) (N : nat) (h1 : term140 x B) (h2 : term252 B k x N) : term309 k x B N i.
Proof. exact (ex_intro (term310 k x B N i) (term264 i x N) (@lem1286526 i B k x N h1 h2)). Qed.
Lemma lem1286528 (i : nat) (B : nat) (k : nat) (x : nadd) (N : nat) (h1 : term140 x B) (h2 : term252 B k x N) : term284 k x B N i.
Proof. exact (@lem1286428 k x B N i (@lem1286527 i B k x N h1 h2)). Qed.
Lemma lem1286529 (i : nat) (B : nat) (k : nat) (x : nadd) (N : nat) (h1 : term140 x B) (h2 : term252 B k x N) : term283 k x N B i.
Proof. exact (EQ_MP (@lem1286425 k x N B i) (@lem1286528 i B k x N h1 h2)). Qed.
Lemma lem1286530 (i : nat) (B : nat) (k : nat) (x : nadd) (N : nat) (h1 : term140 x B) (h2 : term252 B k x N) : term311 k x i B N.
Proof. exact (ex_intro (term312 k x i B N) (Nat.mul B i) (@lem1286529 i B k x N h1 h2)). Qed.
Lemma lem1286531 (i : nat) (B : nat) (k : nat) (x : nadd) (N : nat) (h1 : term140 x B) (h2 : term252 B k x N) : term277 k x i B N.
Proof. exact (@lem1286409 k x i B N (@lem1286530 i B k x N h1 h2)). Qed.
Lemma lem1286532 (i : nat) (B : nat) (k : nat) (x : nadd) (N : nat) (h1 : term140 x B) (h2 : term252 B k x N) : term276 k x i B N.
Proof. exact (EQ_MP (@lem1286406 k x i B N) (@lem1286531 i B k x N h1 h2)). Qed.
Lemma lem1286537 (B : nat) (k : nat) (x : nadd) (N : nat) (h1 : term140 x B) (h2 : term252 B k x N) : term313 k x B N.
Proof. exact (fun i : nat => @lem1286532 i B k x N h1 h2). Qed.
Lemma lem1286538 (B : nat) (k : nat) (x : nadd) (N : nat) (h1 : term140 x B) (h2 : term252 B k x N) : term243 k N x.
Proof. exact (ex_intro (term242 k N x) (Nat.mul B N) (@lem1286537 B k x N h1 h2)). Qed.
Lemma lem1286539 (B : nat) (k : nat) (x : nadd) (N : nat) (h1 : term140 x B) (h2 : term252 B k x N) : term245 k x.
Proof. exact (ex_intro (term244 k x) N (@lem1286538 B k x N h1 h2)). Qed.
Lemma lem1286540 (B : nat) (k : nat) (x : nadd) (h1 : term140 x B) (h2 : term254 B k x) : term245 k x.
Proof. exact (ex_elim (@lem1286358 B k x h2) (fun N : nat => fun h0 : term253 B k x N => @lem1286539 B k x N h1 h0)). Qed.
Lemma lem1286541 (k : nat) (x : nadd) (B : nat) (h1 : term140 x B) : term256 B k x.
Proof. exact (fun h0 : term254 B k x => @lem1286540 B k x h1 h0). Qed.
Lemma lem1286542 (k : nat) (x : nadd) (B : nat) (h1 : term140 x B) : term247 B k x.
Proof. exact (EQ_MP (@lem1286357 B k x) (@lem1286541 k x B h1)). Qed.
Lemma lem1286543 (k : nat) (x : nadd) (B : nat) (h1 : term140 x B) : term246 B k x.
Proof. exact (EQ_MP (@lem1286309 B k x) (@lem1286542 k x B h1)). Qed.
Lemma lem1286544 (k : nat) (B : nat) (x : nadd) (h1 : term140 x B) (h2 : term172 x) : term181 k x.
Proof. exact (@lem1286543 k x B h1 (@lem1286185 B k x h2)). Qed.
Lemma lem1286545 (k : nat) (x : nadd) (B : nat) (h1 : term140 x B) : term183 k x.
Proof. exact (fun h0 : term172 x => @lem1286544 k B x h1 h0). Qed.
Lemma lem1286546 (k : nat) (x : nadd) : term183 k x.
Proof. exact (ex_elim (@lem1286093 x) (fun B : nat => fun h0 : term314 x B => @lem1286545 k x B h0)). Qed.
Lemma lem1286547 (k : nat) (x : nadd) : term182 k x.
Proof. exact (EQ_MP (@lem1286181 k x) (@lem1286546 k x)). Qed.
Lemma lem1286552 (x : nadd) : term315 x.
Proof. exact (fun k : nat => @lem1286547 k x). Qed.
Lemma lem1286557 : term316.
Proof. exact (fun x : nadd => @lem1286552 x). Qed.
