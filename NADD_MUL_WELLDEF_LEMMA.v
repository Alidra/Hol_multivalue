Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_MUL_WELLDEF_LEMMA_term_abbrevs.
Require Import LE_MULT_LCANCEL_spec.
Require Import LE_TRANS_spec.
Require Import NADD_DIST_spec.
Require Import NADD_MUL_spec.
Require Import nadd_eq_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1832_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem1278841 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1278842 (m : nat) (h1 : term0) : term1 m.
Proof. exact (@lem1278841 h1 m). Qed.
Lemma lem1278843 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1278844 (m : nat) (h1 : term0) : term2 m.
Proof. exact (EQ_MP (@lem1278843 m) (@lem1278842 m h1)). Qed.
Lemma lem1278845 (m : nat) (n : nat) (h1 : term0) : term3 m n.
Proof. exact (@lem1278844 m h1 n). Qed.
Lemma lem1278846 (n : nat) (m : nat) : (term3 m n) = (term4 n m).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem1278847 (n : nat) (m : nat) (h1 : term0) : term4 n m.
Proof. exact (EQ_MP (@lem1278846 n m) (@lem1278845 m n h1)). Qed.
Lemma lem1278848 (n : nat) (m : nat) (p : nat) (h1 : term0) : term5 n m p.
Proof. exact (@lem1278847 n m h1 p). Qed.
Lemma lem1278849 (n : nat) (m : nat) (p : nat) : (term5 n m p) = (term6 n m p).
Proof. exact (eq_refl (term5 n m p)). Qed.
Lemma lem1278850 (n : nat) (m : nat) (p : nat) (h1 : term0) : term6 n m p.
Proof. exact (EQ_MP (@lem1278849 n m p) (@lem1278848 n m p h1)). Qed.
Lemma lem1278851 (m : nat) (n : nat) (p : nat) (h1 : term7 m n p) : term7 m n p.
Proof. exact (h1). Qed.
Lemma lem1278852 (m : nat) (n : nat) (p : nat) (h1 : term0) (h2 : term7 m n p) : Peano.le m p.
Proof. exact (@lem1278850 n m p h1 (@lem1278851 m n p h2)). Qed.
Lemma lem1278853 (m : nat) (n : nat) (p : nat) (h1 : term7 m n p) : term8 m p.
Proof. exact (fun h0 : term0 => @lem1278852 m n p h0 h1). Qed.
Lemma lem1278854 (m : nat) (p : nat) (h1 : term9 m p) : term9 m p.
Proof. exact (h1). Qed.
Lemma lem1278855 (m : nat) (p : nat) (h1 : term9 m p) : term8 m p.
Proof. exact (ex_elim (@lem1278854 m p h1) (fun n : nat => fun h0 : term10 m p n => @lem1278853 m n p h0)). Qed.
Lemma lem1278856 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1278857 (m : nat) (p : nat) (h1 : term0) (h2 : term9 m p) : Peano.le m p.
Proof. exact (@lem1278855 m p h2 (@lem1278856 h1)). Qed.
Lemma lem1278858 (m : nat) (p : nat) (h1 : term0) : term11 m p.
Proof. exact (fun h0 : term9 m p => @lem1278857 m p h1 h0). Qed.
Lemma lem1278859 (m : nat) (h1 : term0) : term12 m.
Proof. exact (fun p : nat => @lem1278858 m p h1). Qed.
Lemma lem1278860 (h1 : term0) : term13.
Proof. exact (fun m : nat => @lem1278859 m h1). Qed.
Lemma lem1278861 : term14.
Proof. exact (fun h0 : term0 => @lem1278860 h0). Qed.
Lemma lem1278862 : term13.
Proof. exact (@lem1278861 (@lem93743)). Qed.
Lemma lem1278863 (m : nat) : term15 m.
Proof. exact (@lem1278862 m). Qed.
Lemma lem1278864 (m : nat) : (term15 m) = (term12 m).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem1278865 (m : nat) : term12 m.
Proof. exact (EQ_MP (@lem1278864 m) (@lem1278863 m)). Qed.
Lemma lem1278866 (m : nat) (p : nat) : term16 m p.
Proof. exact (@lem1278865 m p). Qed.
Lemma lem1278867 (m : nat) (p : nat) : (term16 m p) = (term11 m p).
Proof. exact (eq_refl (term16 m p)). Qed.
Lemma lem1278869 (x : nadd) : term17 x.
Proof. exact (@lem1267115 x). Qed.
Lemma lem1278870 (x : nadd) : (term17 x) = (term18 x).
Proof. exact (eq_refl (term17 x)). Qed.
Lemma lem1278871 (x : nadd) : term18 x.
Proof. exact (EQ_MP (@lem1278870 x) (@lem1278869 x)). Qed.
Lemma lem1278872 (x : nadd) (B2 : nat) (h1 : term19 x B2) : term19 x B2.
Proof. exact (h1). Qed.
Lemma lem1278873 (x : nadd) : term20 x.
Proof. exact (@lem1277879 x). Qed.
Lemma lem1278874 (x : nadd) : (term20 x) = (term21 x).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem1278875 (x : nadd) : term21 x.
Proof. exact (EQ_MP (@lem1278874 x) (@lem1278873 x)). Qed.
Lemma lem1278876 (x : nadd) (y : nadd) : term22 x y.
Proof. exact (@lem1278875 x y). Qed.
Lemma lem1278877 (x : nadd) (y : nadd) : (term22 x y) = ((term23 x y) = (term24 x y)).
Proof. exact (eq_refl (term22 x y)). Qed.
Lemma lem1278879 (x : nadd) : term25 x.
Proof. exact (@lem1267930 x). Qed.
Lemma lem1278880 (x : nadd) : (term25 x) = (term26 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1278881 (x : nadd) : term26 x.
Proof. exact (EQ_MP (@lem1278880 x) (@lem1278879 x)). Qed.
Lemma lem1278882 (x : nadd) (y : nadd) : term27 x y.
Proof. exact (@lem1278881 x y). Qed.
Lemma lem1278883 (x : nadd) (y : nadd) : (term27 x y) = ((nadd_eq x y) = (term28 x y)).
Proof. exact (eq_refl (term27 x y)). Qed.
Lemma lem1278888 (x : nadd) (y : nadd) : (nadd_eq x y) = (term28 x y).
Proof. exact (EQ_MP (@lem1278883 x y) (@lem1278882 x y)). Qed.
Lemma lem1278889 (y : nadd) (y' : nadd) : (nadd_eq y y') = (term28 y y').
Proof. exact (@lem1278888 y y'). Qed.
Lemma lem1278898 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1278899 (y : nadd) (y' : nadd) : (term29 y y') = (term30 y y').
Proof. exact (MK_COMB (@lem1278898) (@lem1278889 y y')). Qed.
Lemma lem1278901 (x : nadd) (y : nadd) : (nadd_eq x y) = (term28 x y).
Proof. exact (EQ_MP (@lem1278883 x y) (@lem1278882 x y)). Qed.
Lemma lem1278902 (y : nadd) (x : nadd) (y' : nadd) : (term31 y x y') = (term32 y x y').
Proof. exact (@lem1278901 (nadd_mul x y) (nadd_mul x y')). Qed.
Lemma lem1278912 (x : nadd) (y : nadd) : (term23 x y) = (term24 x y).
Proof. exact (EQ_MP (@lem1278877 x y) (@lem1278876 x y)). Qed.
Lemma lem1278913 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1278914 (x : nadd) (y : nadd) (n : nat) : (term33 x y n) = (term34 x y n).
Proof. exact (MK_COMB (@lem1278912 x y) (@lem1278913 n)). Qed.
Lemma lem1278916 {A B : Type'} (f : A -> B) (y : A) : (term35 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1278917 (f : nat -> nat) (y : nat) : (term36 f y) = (f y).
Proof. exact (@lem1278916 nat nat f y). Qed.
Lemma lem1278918 (x : nadd) (y : nadd) (n : nat) : (term37 x y n) = (term34 x y n).
Proof. exact (@lem1278917 (term24 x y) n). Qed.
Lemma lem1278919 (x : nadd) (y : nadd) (n : nat) : (term34 x y n) = (term38 x y n).
Proof. exact (eq_refl (term34 x y n)). Qed.
Lemma lem1278920 (x : nadd) (y : nadd) : (term39 x y) = (term24 x y).
Proof. exact (fun_ext (fun n : nat => @lem1278919 x y n)). Qed.
Lemma lem1278921 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1278922 (x : nadd) (y : nadd) (n : nat) : (term37 x y n) = (term34 x y n).
Proof. exact (MK_COMB (@lem1278920 x y) (@lem1278921 n)). Qed.
Lemma lem1278923 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1278924 (x : nadd) (y : nadd) (n : nat) : (term40 x y n) = (term41 x y n).
Proof. exact (MK_COMB (@lem1278923) (@lem1278922 x y n)). Qed.
Lemma lem1278925 (x : nadd) (y : nadd) (n : nat) : (term34 x y n) = (term38 x y n).
Proof. exact (eq_refl (term34 x y n)). Qed.
Lemma lem1278926 (x : nadd) (y : nadd) (n : nat) : ((term37 x y n) = (term34 x y n)) = ((term34 x y n) = (term38 x y n)).
Proof. exact (MK_COMB (@lem1278924 x y n) (@lem1278925 x y n)). Qed.
Lemma lem1278927 (x : nadd) (y : nadd) (n : nat) : (term34 x y n) = (term38 x y n).
Proof. exact (EQ_MP (@lem1278926 x y n) (@lem1278918 x y n)). Qed.
Lemma lem1278928 (x : nadd) (y : nadd) (n : nat) : (term33 x y n) = (term38 x y n).
Proof. exact (TRANS (@lem1278914 x y n) (@lem1278927 x y n)). Qed.
Lemma lem1278929 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1278930 (x : nadd) (y : nadd) (n : nat) : (term42 x y n) = (term43 x y n).
Proof. exact (MK_COMB (@lem1278929) (@lem1278928 x y n)). Qed.
Lemma lem1278932 (x : nadd) (y : nadd) : (term23 x y) = (term24 x y).
Proof. exact (EQ_MP (@lem1278877 x y) (@lem1278876 x y)). Qed.
Lemma lem1278933 (x : nadd) (y' : nadd) : (term23 x y') = (term24 x y').
Proof. exact (@lem1278932 x y'). Qed.
Lemma lem1278934 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1278935 (x : nadd) (y' : nadd) (n : nat) : (term33 x y' n) = (term34 x y' n).
Proof. exact (MK_COMB (@lem1278933 x y') (@lem1278934 n)). Qed.
Lemma lem1278937 {A B : Type'} (f : A -> B) (y : A) : (term35 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1278938 (f : nat -> nat) (y : nat) : (term36 f y) = (f y).
Proof. exact (@lem1278937 nat nat f y). Qed.
Lemma lem1278939 (x : nadd) (y' : nadd) (n : nat) : (term37 x y' n) = (term34 x y' n).
Proof. exact (@lem1278938 (term24 x y') n). Qed.
Lemma lem1278940 (x : nadd) (y' : nadd) (n : nat) : (term34 x y' n) = (term38 x y' n).
Proof. exact (eq_refl (term34 x y' n)). Qed.
Lemma lem1278941 (x : nadd) (y' : nadd) : (term39 x y') = (term24 x y').
Proof. exact (fun_ext (fun n : nat => @lem1278940 x y' n)). Qed.
Lemma lem1278942 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1278943 (x : nadd) (y' : nadd) (n : nat) : (term37 x y' n) = (term34 x y' n).
Proof. exact (MK_COMB (@lem1278941 x y') (@lem1278942 n)). Qed.
Lemma lem1278944 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1278945 (x : nadd) (y' : nadd) (n : nat) : (term40 x y' n) = (term41 x y' n).
Proof. exact (MK_COMB (@lem1278944) (@lem1278943 x y' n)). Qed.
Lemma lem1278946 (x : nadd) (y' : nadd) (n : nat) : (term34 x y' n) = (term38 x y' n).
Proof. exact (eq_refl (term34 x y' n)). Qed.
Lemma lem1278947 (x : nadd) (y' : nadd) (n : nat) : ((term37 x y' n) = (term34 x y' n)) = ((term34 x y' n) = (term38 x y' n)).
Proof. exact (MK_COMB (@lem1278945 x y' n) (@lem1278946 x y' n)). Qed.
Lemma lem1278948 (x : nadd) (y' : nadd) (n : nat) : (term34 x y' n) = (term38 x y' n).
Proof. exact (EQ_MP (@lem1278947 x y' n) (@lem1278939 x y' n)). Qed.
Lemma lem1278949 (x : nadd) (y' : nadd) (n : nat) : (term33 x y' n) = (term38 x y' n).
Proof. exact (TRANS (@lem1278935 x y' n) (@lem1278948 x y' n)). Qed.
Lemma lem1278950 (y : nadd) (x : nadd) (y' : nadd) (n : nat) : (term44 y x y' n) = (term45 y x y' n).
Proof. exact (MK_COMB (@lem1278930 x y n) (@lem1278949 x y' n)). Qed.
Lemma lem1278951 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1278952 (y : nadd) (x : nadd) (y' : nadd) (n : nat) : (term46 y x y' n) = (term47 y x y' n).
Proof. exact (MK_COMB (@lem1278951) (@lem1278950 y x y' n)). Qed.
Lemma lem1278953 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1278954 (y : nadd) (x : nadd) (y' : nadd) (n : nat) : (term48 y x y' n) = (term49 y x y' n).
Proof. exact (MK_COMB (@lem1278953) (@lem1278952 y x y' n)). Qed.
Lemma lem1278955 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1278956 (y : nadd) (x : nadd) (y' : nadd) (n : nat) (B : nat) : (term50 y x y' n B) = (term51 y x y' n B).
Proof. exact (MK_COMB (@lem1278954 y x y' n) (@lem1278955 B)). Qed.
Lemma lem1278957 (y : nadd) (x : nadd) (y' : nadd) (B : nat) : (term52 y x y' B) = (term53 y x y' B).
Proof. exact (fun_ext (fun n : nat => @lem1278956 y x y' n B)). Qed.
Lemma lem1278958 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1278959 (y : nadd) (x : nadd) (y' : nadd) (B : nat) : (term54 y x y' B) = (term55 y x y' B).
Proof. exact (MK_COMB (@lem1278958) (@lem1278957 y x y' B)). Qed.
Lemma lem1278964 (y : nadd) (x : nadd) (y' : nadd) : (term56 y x y') = (term57 y x y').
Proof. exact (fun_ext (fun B : nat => @lem1278959 y x y' B)). Qed.
Lemma lem1278965 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1278966 (y : nadd) (x : nadd) (y' : nadd) : (term32 y x y') = (term58 y x y').
Proof. exact (MK_COMB (@lem1278965) (@lem1278964 y x y')). Qed.
Lemma lem1278971 (y : nadd) (x : nadd) (y' : nadd) : (term31 y x y') = (term58 y x y').
Proof. exact (TRANS (@lem1278902 y x y') (@lem1278966 y x y')). Qed.
Lemma lem1278972 (y : nadd) (x : nadd) (y' : nadd) : (term59 y x y') = (term60 y x y').
Proof. exact (MK_COMB (@lem1278899 y y') (@lem1278971 y x y')). Qed.
Lemma lem1278975 (y : nadd) (x : nadd) (y' : nadd) : (term60 y x y') = (term59 y x y').
Proof. exact (SYM (@lem1278972 y x y')). Qed.
Lemma lem1278976 (y : nadd) (y' : nadd) (h1 : term28 y y') : term28 y y'.
Proof. exact (h1). Qed.
Lemma lem1278977 (y : nadd) (y' : nadd) (B1 : nat) (h1 : term61 y y' B1) : term61 y y' B1.
Proof. exact (h1). Qed.
Lemma lem1278979 (m : nat) (p : nat) : term11 m p.
Proof. exact (EQ_MP (@lem1278867 m p) (@lem1278866 m p)). Qed.
Lemma lem1278980 (y : nadd) (x : nadd) (y' : nadd) (n : nat) (B2 : nat) (B1 : nat) : term62 y x y' n B2 B1.
Proof. exact (@lem1278979 (term47 y x y' n) (Nat.mul B2 B1)). Qed.
Lemma lem1278981 (m : nat) : term63 m.
Proof. exact (@lem104208 m). Qed.
Lemma lem1278982 (m : nat) : (term63 m) = (term64 m).
Proof. exact (eq_refl (term63 m)). Qed.
Lemma lem1278983 (m : nat) : term64 m.
Proof. exact (EQ_MP (@lem1278982 m) (@lem1278981 m)). Qed.
Lemma lem1278984 (m : nat) (n : nat) : term65 m n.
Proof. exact (@lem1278983 m n). Qed.
Lemma lem1278985 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (eq_refl (term65 m n)). Qed.
Lemma lem1278986 (m : nat) (n : nat) : term66 m n.
Proof. exact (EQ_MP (@lem1278985 m n) (@lem1278984 m n)). Qed.
Lemma lem1278987 (m : nat) (n : nat) (p : nat) : term67 m n p.
Proof. exact (@lem1278986 m n p). Qed.
Lemma lem1278988 (m : nat) (n : nat) (p : nat) : (term67 m n p) = ((term68 n m p) = (term69 m n p)).
Proof. exact (eq_refl (term67 m n p)). Qed.
Lemma lem1278990 (n : nat) (y : nadd) (y' : nadd) (B1 : nat) (h1 : term61 y y' B1) : term70 y y' B1 n.
Proof. exact (@lem1278977 y y' B1 h1 n). Qed.
Lemma lem1278991 (y : nadd) (y' : nadd) (n : nat) (B1 : nat) : (term70 y y' B1 n) = (term71 y y' n B1).
Proof. exact (eq_refl (term70 y y' B1 n)). Qed.
Lemma lem1278992 (n : nat) (y : nadd) (y' : nadd) (B1 : nat) (h1 : term61 y y' B1) : term71 y y' n B1.
Proof. exact (EQ_MP (@lem1278991 y y' n B1) (@lem1278990 n y y' B1 h1)). Qed.
Lemma lem1278993 (y : nadd) (y' : nadd) (n : nat) (B1 : nat) : (term71 y y' n B1) = ((term71 y y' n B1) = True).
Proof. exact (@lem7 (term71 y y' n B1)). Qed.
Lemma lem1278995 (m : nat) (x : nadd) (B2 : nat) (h1 : term19 x B2) : term72 x B2 m.
Proof. exact (@lem1278872 x B2 h1 m). Qed.
Lemma lem1278996 (x : nadd) (B2 : nat) (m : nat) : (term72 x B2 m) = (term73 x B2 m).
Proof. exact (eq_refl (term72 x B2 m)). Qed.
Lemma lem1278997 (m : nat) (x : nadd) (B2 : nat) (h1 : term19 x B2) : term73 x B2 m.
Proof. exact (EQ_MP (@lem1278996 x B2 m) (@lem1278995 m x B2 h1)). Qed.
Lemma lem1278998 (m : nat) (n : nat) (x : nadd) (B2 : nat) (h1 : term19 x B2) : term74 x B2 m n.
Proof. exact (@lem1278997 m x B2 h1 n). Qed.
Lemma lem1278999 (x : nadd) (B2 : nat) (m : nat) (n : nat) : (term74 x B2 m n) = (term75 x B2 m n).
Proof. exact (eq_refl (term74 x B2 m n)). Qed.
Lemma lem1279000 (m : nat) (n : nat) (x : nadd) (B2 : nat) (h1 : term19 x B2) : term75 x B2 m n.
Proof. exact (EQ_MP (@lem1278999 x B2 m n) (@lem1278998 m n x B2 h1)). Qed.
Lemma lem1279001 (x : nadd) (B2 : nat) (m : nat) (n : nat) : (term75 x B2 m n) = ((term75 x B2 m n) = True).
Proof. exact (@lem7 (term75 x B2 m n)). Qed.
Lemma lem1279006 (m : nat) (n : nat) (x : nadd) (B2 : nat) (h1 : term19 x B2) : (term75 x B2 m n) = True.
Proof. exact (EQ_MP (@lem1279001 x B2 m n) (@lem1279000 m n x B2 h1)). Qed.
Lemma lem1279007 (y : nadd) (y' : nadd) (n : nat) (x : nadd) (B2 : nat) (h1 : term19 x B2) : (term76 x B2 y y' n) = True.
Proof. exact (@lem1279006 (dest_nadd y n) (dest_nadd y' n) x B2 h1). Qed.
Lemma lem1279008 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1279009 (y : nadd) (y' : nadd) (n : nat) (x : nadd) (B2 : nat) (h1 : term19 x B2) : (term77 x B2 y y' n) = (and True).
Proof. exact (MK_COMB (@lem1279008) (@lem1279007 y y' n x B2 h1)). Qed.
Lemma lem1279011 (m : nat) (n : nat) (p : nat) : (term68 n m p) = (term69 m n p).
Proof. exact (EQ_MP (@lem1278988 m n p) (@lem1278987 m n p)). Qed.
Lemma lem1279012 (B2 : nat) (y : nadd) (y' : nadd) (n : nat) (B1 : nat) : (term78 y y' n B2 B1) = (term79 B2 y y' n B1).
Proof. exact (@lem1279011 B2 (term80 y y' n) B1). Qed.
Lemma lem1279018 (n : nat) (y : nadd) (y' : nadd) (B1 : nat) (h1 : term61 y y' B1) : (term71 y y' n B1) = True.
Proof. exact (EQ_MP (@lem1278993 y y' n B1) (@lem1278992 n y y' B1 h1)). Qed.
Lemma lem1279019 (B2 : nat) : (term81 B2) = (term81 B2).
Proof. exact (eq_refl (term81 B2)). Qed.
Lemma lem1279020 (n : nat) (B2 : nat) (y : nadd) (y' : nadd) (B1 : nat) (h1 : term61 y y' B1) : (term79 B2 y y' n B1) = (term82 B2).
Proof. exact (MK_COMB (@lem1279019 B2) (@lem1279018 n y y' B1 h1)). Qed.
Lemma lem1279022 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1279023 (B2 : nat) : (term82 B2) = True.
Proof. exact (@lem1279022 (B2 = (NUMERAL 0))). Qed.
Lemma lem1279024 (B2 : nat) (n : nat) (y : nadd) (y' : nadd) (B1 : nat) (h1 : term61 y y' B1) : (term79 B2 y y' n B1) = True.
Proof. exact (TRANS (@lem1279020 n B2 y y' B1 h1) (@lem1279023 B2)). Qed.
Lemma lem1279025 (n : nat) (B2 : nat) (y : nadd) (y' : nadd) (B1 : nat) (h1 : term61 y y' B1) : (term78 y y' n B2 B1) = True.
Proof. exact (TRANS (@lem1279012 B2 y y' n B1) (@lem1279024 B2 n y y' B1 h1)). Qed.
Lemma lem1279026 (n : nat) (x : nadd) (B2 : nat) (y : nadd) (y' : nadd) (B1 : nat) (h1 : term19 x B2) (h2 : term61 y y' B1) : (term83 x y y' n B2 B1) = (True /\ True).
Proof. exact (MK_COMB (@lem1279009 y y' n x B2 h1) (@lem1279025 n B2 y y' B1 h2)). Qed.
Lemma lem1279028 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1279029 : (True /\ True) = True.
Proof. exact (@lem1279028 True). Qed.
Lemma lem1279030 (n : nat) (x : nadd) (B2 : nat) (y : nadd) (y' : nadd) (B1 : nat) (h1 : term19 x B2) (h2 : term61 y y' B1) : (term83 x y y' n B2 B1) = True.
Proof. exact (TRANS (@lem1279026 n x B2 y y' B1 h1 h2) (@lem1279029)). Qed.
Lemma lem1279031 (n : nat) (x : nadd) (B2 : nat) (y : nadd) (y' : nadd) (B1 : nat) (h1 : term19 x B2) (h2 : term61 y y' B1) : True = (term83 x y y' n B2 B1).
Proof. exact (SYM (@lem1279030 n x B2 y y' B1 h1 h2)). Qed.
Lemma lem1279032 (n : nat) (x : nadd) (B2 : nat) (y : nadd) (y' : nadd) (B1 : nat) (h1 : term19 x B2) (h2 : term61 y y' B1) : term83 x y y' n B2 B1.
Proof. exact (EQ_MP (@lem1279031 n x B2 y y' B1 h1 h2) (@lem0)). Qed.
Lemma lem1279033 (n : nat) (x : nadd) (B2 : nat) (y : nadd) (y' : nadd) (B1 : nat) (h1 : term19 x B2) (h2 : term61 y y' B1) : term84 y x y' n B2 B1.
Proof. exact (ex_intro (term85 y x y' n B2 B1) (term86 B2 y y' n) (@lem1279032 n x B2 y y' B1 h1 h2)). Qed.
Lemma lem1279034 (n : nat) (x : nadd) (B2 : nat) (y : nadd) (y' : nadd) (B1 : nat) (h1 : term19 x B2) (h2 : term61 y y' B1) : term87 y x y' n B2 B1.
Proof. exact (@lem1278980 y x y' n B2 B1 (@lem1279033 n x B2 y y' B1 h1 h2)). Qed.
Lemma lem1279039 (x : nadd) (B2 : nat) (y : nadd) (y' : nadd) (B1 : nat) (h1 : term19 x B2) (h2 : term61 y y' B1) : term88 y x y' B2 B1.
Proof. exact (fun n : nat => @lem1279034 n x B2 y y' B1 h1 h2). Qed.
Lemma lem1279040 (x : nadd) (B2 : nat) (y : nadd) (y' : nadd) (B1 : nat) (h1 : term19 x B2) (h2 : term61 y y' B1) : term58 y x y'.
Proof. exact (ex_intro (term57 y x y') (Nat.mul B2 B1) (@lem1279039 x B2 y y' B1 h1 h2)). Qed.
Lemma lem1279041 (x : nadd) (y : nadd) (y' : nadd) (B1 : nat) (h1 : term61 y y' B1) : term58 y x y'.
Proof. exact (ex_elim (@lem1278871 x) (fun B2 : nat => fun h0 : term89 x B2 => @lem1279040 x B2 y y' B1 h0 h1)). Qed.
Lemma lem1279042 (x : nadd) (y : nadd) (y' : nadd) (h1 : term28 y y') : term58 y x y'.
Proof. exact (ex_elim (@lem1278976 y y' h1) (fun B1 : nat => fun h0 : term90 y y' B1 => @lem1279041 x y y' B1 h0)). Qed.
Lemma lem1279043 (y : nadd) (x : nadd) (y' : nadd) : term60 y x y'.
Proof. exact (fun h0 : term28 y y' => @lem1279042 x y y' h0). Qed.
Lemma lem1279044 (y : nadd) (x : nadd) (y' : nadd) : term59 y x y'.
Proof. exact (EQ_MP (@lem1278975 y x y') (@lem1279043 y x y')). Qed.
Lemma lem1279049 (y : nadd) (x : nadd) : term91 y x.
Proof. exact (fun y' : nadd => @lem1279044 y x y'). Qed.
Lemma lem1279054 (x : nadd) : term92 x.
Proof. exact (fun y : nadd => @lem1279049 y x). Qed.
Lemma lem1279059 : term93.
Proof. exact (fun x : nadd => @lem1279054 x). Qed.
