Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_MUL_LINV_LEMMA1_term_abbrevs.
Require Import DIST_RADD_0_spec.
Require Import DIVISION_spec.
Require Import LT_IMP_LE_spec.
Require Import MULT_SYM_spec.
Require Import nadd_rinv_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Lemma lem1301913 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1301914 (m : nat) (h1 : term0) : term1 m.
Proof. exact (@lem1301913 h1 m). Qed.
Lemma lem1301915 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1301916 (m : nat) (h1 : term0) : term2 m.
Proof. exact (EQ_MP (@lem1301915 m) (@lem1301914 m h1)). Qed.
Lemma lem1301917 (m : nat) (n : nat) (h1 : term0) : term3 m n.
Proof. exact (@lem1301916 m h1 n). Qed.
Lemma lem1301918 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem1301919 (m : nat) (n : nat) (h1 : term0) : term4 m n.
Proof. exact (EQ_MP (@lem1301918 m n) (@lem1301917 m n h1)). Qed.
Lemma lem1301920 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem1301921 (m : nat) (n : nat) (h1 : term0) (h2 : Peano.lt m n) : Peano.le m n.
Proof. exact (@lem1301919 m n h1 (@lem1301920 m n h2)). Qed.
Lemma lem1301922 (m : nat) (n : nat) (h1 : Peano.lt m n) : term5 m n.
Proof. exact (fun h0 : term0 => @lem1301921 m n h0 h1). Qed.
Lemma lem1301923 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1301924 (m : nat) (n : nat) (h1 : term0) (h2 : Peano.lt m n) : Peano.le m n.
Proof. exact (@lem1301922 m n h2 (@lem1301923 h1)). Qed.
Lemma lem1301925 (m : nat) (n : nat) (h1 : term0) : term4 m n.
Proof. exact (fun h0 : Peano.lt m n => @lem1301924 m n h1 h0). Qed.
Lemma lem1301926 (m : nat) (h1 : term0) : term2 m.
Proof. exact (fun n : nat => @lem1301925 m n h1). Qed.
Lemma lem1301927 (h1 : term0) : term0.
Proof. exact (fun m : nat => @lem1301926 m h1). Qed.
Lemma lem1301928 : term6.
Proof. exact (fun h0 : term0 => @lem1301927 h0). Qed.
Lemma lem1301929 : term0.
Proof. exact (@lem1301928 (@lem98439)). Qed.
Lemma lem1301930 (m : nat) : term1 m.
Proof. exact (@lem1301929 m). Qed.
Lemma lem1301931 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1301932 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem1301931 m) (@lem1301930 m)). Qed.
Lemma lem1301933 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem1301932 m n). Qed.
Lemma lem1301934 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem1301936 (m : nat) : term7 m.
Proof. exact (@lem1245295 m). Qed.
Lemma lem1301937 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem1301938 (m : nat) : term8 m.
Proof. exact (EQ_MP (@lem1301937 m) (@lem1301936 m)). Qed.
Lemma lem1301939 (m : nat) (n : nat) : term9 m n.
Proof. exact (@lem1301938 m n). Qed.
Lemma lem1301940 (m : nat) (n : nat) : (term9 m n) = ((term10 m n) = n).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem1301942 (m : nat) : term11 m.
Proof. exact (@lem81820 m). Qed.
Lemma lem1301943 (m : nat) : (term11 m) = (term12 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem1301944 (m : nat) : term12 m.
Proof. exact (EQ_MP (@lem1301943 m) (@lem1301942 m)). Qed.
Lemma lem1301945 (m : nat) (n : nat) : term13 m n.
Proof. exact (@lem1301944 m n). Qed.
Lemma lem1301946 (n : nat) (m : nat) : (term13 m n) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term13 m n)). Qed.
Lemma lem1301948 (x : nadd) : term14 x.
Proof. exact (@lem1300973 x). Qed.
Lemma lem1301949 (x : nadd) : (term14 x) = ((nadd_rinv x) = (term15 x)).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem1301951 (h1 : term16) : term16.
Proof. exact (h1). Qed.
Lemma lem1301952 (m : nat) (h1 : term16) : term17 m.
Proof. exact (@lem1301951 h1 m). Qed.
Lemma lem1301953 (m : nat) : (term17 m) = (term18 m).
Proof. exact (eq_refl (term17 m)). Qed.
Lemma lem1301954 (m : nat) (h1 : term16) : term18 m.
Proof. exact (EQ_MP (@lem1301953 m) (@lem1301952 m h1)). Qed.
Lemma lem1301955 (m : nat) (n : nat) (h1 : term16) : term19 m n.
Proof. exact (@lem1301954 m h1 n). Qed.
Lemma lem1301956 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem1301957 (m : nat) (n : nat) (h1 : term16) : term20 m n.
Proof. exact (EQ_MP (@lem1301956 m n) (@lem1301955 m n h1)). Qed.
Lemma lem1301958 (n : nat) (h1 : term21 n) : term21 n.
Proof. exact (h1). Qed.
Lemma lem1301959 (m : nat) (n : nat) (h1 : term16) (h2 : term21 n) : term22 m n.
Proof. exact (@lem1301957 m n h1 (@lem1301958 n h2)). Qed.
Lemma lem1301960 (n : nat) (h1 : term16) (h2 : term21 n) : term23 n.
Proof. exact (fun m : nat => @lem1301959 m n h1 h2). Qed.
Lemma lem1301961 (n : nat) (h1 : term16) : term24 n.
Proof. exact (fun h0 : term21 n => @lem1301960 n h1 h0). Qed.
Lemma lem1301962 (h1 : term16) : term25.
Proof. exact (fun n : nat => @lem1301961 n h1). Qed.
Lemma lem1301963 : term26.
Proof. exact (fun h0 : term16 => @lem1301962 h0). Qed.
Lemma lem1301964 : term25.
Proof. exact (@lem1301963 (@lem157261)). Qed.
Lemma lem1301965 (n : nat) : term27 n.
Proof. exact (@lem1301964 n). Qed.
Lemma lem1301966 (n : nat) : (term27 n) = (term24 n).
Proof. exact (eq_refl (term27 n)). Qed.
Lemma lem1301968 (x : nadd) (n : nat) (h1 : term28 x n) : term28 x n.
Proof. exact (h1). Qed.
Lemma lem1301970 (n : nat) : term24 n.
Proof. exact (EQ_MP (@lem1301966 n) (@lem1301965 n)). Qed.
Lemma lem1301971 (x : nadd) (n : nat) : term29 x n.
Proof. exact (@lem1301970 (dest_nadd x n)). Qed.
Lemma lem1301972 (x : nadd) (n : nat) (h1 : term28 x n) : term30 x n.
Proof. exact (@lem1301971 x n (@lem1301968 x n h1)). Qed.
Lemma lem1301973 (x : nadd) (n : nat) (h1 : term30 x n) : term30 x n.
Proof. exact (h1). Qed.
Lemma lem1301974 (x : nadd) (n : nat) (h1 : term30 x n) : term31 x n.
Proof. exact (@lem1301973 x n h1 (Nat.mul n n)). Qed.
Lemma lem1301975 (x : nadd) (n : nat) : (term31 x n) = (term32 x n).
Proof. exact (eq_refl (term31 x n)). Qed.
Lemma lem1301976 (x : nadd) (n : nat) (h1 : term30 x n) : term32 x n.
Proof. exact (EQ_MP (@lem1301975 x n) (@lem1301974 x n h1)). Qed.
Lemma lem1301977 (x : nadd) (n : nat) (h1 : term33 x n) : term33 x n.
Proof. exact (h1). Qed.
Lemma lem1301978 (x : nadd) (n : nat) (h1 : (Nat.mul n n) = (term34 x n)) : (Nat.mul n n) = (term34 x n).
Proof. exact (h1). Qed.
Lemma lem1301979 (x : nadd) (n : nat) : (term35 x n) = (term35 x n).
Proof. exact (eq_refl (term35 x n)). Qed.
Lemma lem1301980 (x : nadd) (n : nat) (h1 : (Nat.mul n n) = (term34 x n)) : (term36 x n) = (term37 x n).
Proof. exact (MK_COMB (@lem1301979 x n) (@lem1301978 x n h1)). Qed.
Lemma lem1301981 (x : nadd) (n : nat) : (term37 x n) = (term38 x n).
Proof. exact (eq_refl (term37 x n)). Qed.
Lemma lem1301982 (x : nadd) (n : nat) : (term39 x n) = (term39 x n).
Proof. exact (eq_refl (term39 x n)). Qed.
Lemma lem1301983 (x : nadd) (n : nat) : ((term36 x n) = (term37 x n)) = ((term36 x n) = (term38 x n)).
Proof. exact (MK_COMB (@lem1301982 x n) (@lem1301981 x n)). Qed.
Lemma lem1301984 (x : nadd) (n : nat) : (term36 x n) = (term40 x n).
Proof. exact (eq_refl (term36 x n)). Qed.
Lemma lem1301985 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1301986 (x : nadd) (n : nat) : (term39 x n) = (term41 x n).
Proof. exact (MK_COMB (@lem1301985) (@lem1301984 x n)). Qed.
Lemma lem1301987 (x : nadd) (n : nat) : (term38 x n) = (term38 x n).
Proof. exact (eq_refl (term38 x n)). Qed.
Lemma lem1301988 (x : nadd) (n : nat) : ((term36 x n) = (term38 x n)) = ((term40 x n) = (term38 x n)).
Proof. exact (MK_COMB (@lem1301986 x n) (@lem1301987 x n)). Qed.
Lemma lem1301989 (x : nadd) (n : nat) : ((term36 x n) = (term37 x n)) = ((term40 x n) = (term38 x n)).
Proof. exact (TRANS (@lem1301983 x n) (@lem1301988 x n)). Qed.
Lemma lem1301990 (x : nadd) (n : nat) (h1 : (Nat.mul n n) = (term34 x n)) : (term40 x n) = (term38 x n).
Proof. exact (EQ_MP (@lem1301989 x n) (@lem1301980 x n h1)). Qed.
Lemma lem1301991 (x : nadd) (n : nat) (h1 : (Nat.mul n n) = (term34 x n)) : (term38 x n) = (term40 x n).
Proof. exact (SYM (@lem1301990 x n h1)). Qed.
Lemma lem1301993 (x : nadd) : (nadd_rinv x) = (term15 x).
Proof. exact (EQ_MP (@lem1301949 x) (@lem1301948 x)). Qed.
Lemma lem1301994 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1301995 (x : nadd) (n : nat) : (nadd_rinv x n) = (term42 x n).
Proof. exact (MK_COMB (@lem1301993 x) (@lem1301994 n)). Qed.
Lemma lem1301997 {A B : Type'} (f : A -> B) (y : A) : (term43 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1301998 (f : nat -> nat) (y : nat) : (term44 f y) = (f y).
Proof. exact (@lem1301997 nat nat f y). Qed.
Lemma lem1301999 (x : nadd) (n : nat) : (term45 x n) = (term42 x n).
Proof. exact (@lem1301998 (term15 x) n). Qed.
Lemma lem1302000 (x : nadd) (n : nat) : (term42 x n) = (term46 x n).
Proof. exact (eq_refl (term42 x n)). Qed.
Lemma lem1302001 (x : nadd) : (term47 x) = (term15 x).
Proof. exact (fun_ext (fun n : nat => @lem1302000 x n)). Qed.
Lemma lem1302002 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1302003 (x : nadd) (n : nat) : (term45 x n) = (term42 x n).
Proof. exact (MK_COMB (@lem1302001 x) (@lem1302002 n)). Qed.
Lemma lem1302004 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1302005 (x : nadd) (n : nat) : (term48 x n) = (term49 x n).
Proof. exact (MK_COMB (@lem1302004) (@lem1302003 x n)). Qed.
Lemma lem1302006 (x : nadd) (n : nat) : (term42 x n) = (term46 x n).
Proof. exact (eq_refl (term42 x n)). Qed.
Lemma lem1302007 (x : nadd) (n : nat) : ((term45 x n) = (term42 x n)) = ((term42 x n) = (term46 x n)).
Proof. exact (MK_COMB (@lem1302005 x n) (@lem1302006 x n)). Qed.
Lemma lem1302008 (x : nadd) (n : nat) : (term42 x n) = (term46 x n).
Proof. exact (EQ_MP (@lem1302007 x n) (@lem1301999 x n)). Qed.
Lemma lem1302009 (x : nadd) (n : nat) : (nadd_rinv x n) = (term46 x n).
Proof. exact (TRANS (@lem1301995 x n) (@lem1302008 x n)). Qed.
Lemma lem1302010 (x : nadd) (n : nat) : (term50 x n) = (term50 x n).
Proof. exact (eq_refl (term50 x n)). Qed.
Lemma lem1302011 (x : nadd) (n : nat) : (term51 x n) = (term52 x n).
Proof. exact (MK_COMB (@lem1302010 x n) (@lem1302009 x n)). Qed.
Lemma lem1302012 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1302013 (x : nadd) (n : nat) : (term53 x n) = (term54 x n).
Proof. exact (MK_COMB (@lem1302012) (@lem1302011 x n)). Qed.
Lemma lem1302014 (x : nadd) (n : nat) : (term34 x n) = (term34 x n).
Proof. exact (eq_refl (term34 x n)). Qed.
Lemma lem1302015 (x : nadd) (n : nat) : (term55 x n) = (term56 x n).
Proof. exact (MK_COMB (@lem1302013 x n) (@lem1302014 x n)). Qed.
Lemma lem1302016 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1302017 (x : nadd) (n : nat) : (term57 x n) = (term58 x n).
Proof. exact (MK_COMB (@lem1302016) (@lem1302015 x n)). Qed.
Lemma lem1302018 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1302019 (x : nadd) (n : nat) : (term59 x n) = (term60 x n).
Proof. exact (MK_COMB (@lem1302018) (@lem1302017 x n)). Qed.
Lemma lem1302020 (x : nadd) (n : nat) : (dest_nadd x n) = (dest_nadd x n).
Proof. exact (eq_refl (dest_nadd x n)). Qed.
Lemma lem1302021 (x : nadd) (n : nat) : (term38 x n) = (term61 x n).
Proof. exact (MK_COMB (@lem1302019 x n) (@lem1302020 x n)). Qed.
Lemma lem1302022 (x : nadd) (n : nat) : (term61 x n) = (term38 x n).
Proof. exact (SYM (@lem1302021 x n)). Qed.
Lemma lem1302024 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem1301946 n m) (@lem1301945 m n)). Qed.
Lemma lem1302025 (x : nadd) (n : nat) : (term52 x n) = (term62 x n).
Proof. exact (@lem1302024 (term46 x n) (dest_nadd x n)). Qed.
Lemma lem1302026 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1302027 (x : nadd) (n : nat) : (term54 x n) = (term63 x n).
Proof. exact (MK_COMB (@lem1302026) (@lem1302025 x n)). Qed.
Lemma lem1302028 (x : nadd) (n : nat) : (term34 x n) = (term34 x n).
Proof. exact (eq_refl (term34 x n)). Qed.
Lemma lem1302029 (x : nadd) (n : nat) : (term56 x n) = (term64 x n).
Proof. exact (MK_COMB (@lem1302027 x n) (@lem1302028 x n)). Qed.
Lemma lem1302030 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1302031 (x : nadd) (n : nat) : (term58 x n) = (term65 x n).
Proof. exact (MK_COMB (@lem1302030) (@lem1302029 x n)). Qed.
Lemma lem1302032 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1302033 (x : nadd) (n : nat) : (term60 x n) = (term66 x n).
Proof. exact (MK_COMB (@lem1302032) (@lem1302031 x n)). Qed.
Lemma lem1302034 (x : nadd) (n : nat) : (dest_nadd x n) = (dest_nadd x n).
Proof. exact (eq_refl (dest_nadd x n)). Qed.
Lemma lem1302035 (x : nadd) (n : nat) : (term61 x n) = (term67 x n).
Proof. exact (MK_COMB (@lem1302033 x n) (@lem1302034 x n)). Qed.
Lemma lem1302036 (x : nadd) (n : nat) : (term67 x n) = (term61 x n).
Proof. exact (SYM (@lem1302035 x n)). Qed.
Lemma lem1302038 (m : nat) (n : nat) : (term10 m n) = n.
Proof. exact (EQ_MP (@lem1301940 m n) (@lem1301939 m n)). Qed.
Lemma lem1302039 (x : nadd) (n : nat) : (term65 x n) = (term68 x n).
Proof. exact (@lem1302038 (term62 x n) (term68 x n)). Qed.
Lemma lem1302040 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1302041 (x : nadd) (n : nat) : (term66 x n) = (term69 x n).
Proof. exact (MK_COMB (@lem1302040) (@lem1302039 x n)). Qed.
Lemma lem1302042 (x : nadd) (n : nat) : (dest_nadd x n) = (dest_nadd x n).
Proof. exact (eq_refl (dest_nadd x n)). Qed.
Lemma lem1302043 (x : nadd) (n : nat) : (term67 x n) = (term70 x n).
Proof. exact (MK_COMB (@lem1302041 x n) (@lem1302042 x n)). Qed.
Lemma lem1302044 (x : nadd) (n : nat) : (term70 x n) = (term67 x n).
Proof. exact (SYM (@lem1302043 x n)). Qed.
Lemma lem1302046 (m : nat) (n : nat) : term4 m n.
Proof. exact (EQ_MP (@lem1301934 m n) (@lem1301933 m n)). Qed.
Lemma lem1302047 (x : nadd) (n : nat) : term71 x n.
Proof. exact (@lem1302046 (term68 x n) (dest_nadd x n)). Qed.
Lemma lem1302049 (x : nadd) (n : nat) (h1 : term33 x n) : term33 x n.
Proof. exact (h1). Qed.
Lemma lem1302050 (x : nadd) (n : nat) (h1 : term33 x n) : term70 x n.
Proof. exact (@lem1302047 x n (@lem1302049 x n h1)). Qed.
Lemma lem1302051 (x : nadd) (n : nat) (h1 : term33 x n) : term67 x n.
Proof. exact (EQ_MP (@lem1302044 x n) (@lem1302050 x n h1)). Qed.
Lemma lem1302052 (x : nadd) (n : nat) (h1 : term33 x n) : term61 x n.
Proof. exact (EQ_MP (@lem1302036 x n) (@lem1302051 x n h1)). Qed.
Lemma lem1302053 (x : nadd) (n : nat) (h1 : term33 x n) : term38 x n.
Proof. exact (EQ_MP (@lem1302022 x n) (@lem1302052 x n h1)). Qed.
Lemma lem1302054 (x : nadd) (n : nat) (h1 : term30 x n) : term33 x n.
Proof. exact (proj2 (@lem1301976 x n h1)). Qed.
Lemma lem1302055 (x : nadd) (n : nat) (h1 : term30 x n) : (Nat.mul n n) = (term34 x n).
Proof. exact (proj1 (@lem1301976 x n h1)). Qed.
Lemma lem1302056 (x : nadd) (n : nat) (h1 : term33 x n) : (term33 x n) = (term38 x n).
Proof. exact (prop_ext (fun h2 : term33 x n => @lem1302053 x n h1) (fun h2 : term38 x n => @lem1301977 x n h1)). Qed.
Lemma lem1302057 (x : nadd) (n : nat) (h1 : term33 x n) : term38 x n.
Proof. exact (EQ_MP (@lem1302056 x n h1) (@lem1301977 x n h1)). Qed.
Lemma lem1302058 (x : nadd) (n : nat) (h1 : term33 x n) (h2 : (Nat.mul n n) = (term34 x n)) : term40 x n.
Proof. exact (EQ_MP (@lem1301991 x n h2) (@lem1302057 x n h1)). Qed.
Lemma lem1302059 (x : nadd) (n : nat) (h1 : term30 x n) (h2 : (Nat.mul n n) = (term34 x n)) : (term33 x n) = (term40 x n).
Proof. exact (prop_ext (fun h3 : term33 x n => @lem1302058 x n h3 h2) (fun h3 : term40 x n => @lem1302054 x n h1)). Qed.
Lemma lem1302060 (x : nadd) (n : nat) (h1 : term30 x n) (h2 : (Nat.mul n n) = (term34 x n)) : term40 x n.
Proof. exact (EQ_MP (@lem1302059 x n h1 h2) (@lem1302054 x n h1)). Qed.
Lemma lem1302061 (x : nadd) (n : nat) (h1 : term30 x n) : ((Nat.mul n n) = (term34 x n)) = (term40 x n).
Proof. exact (prop_ext (fun h2 : (Nat.mul n n) = (term34 x n) => @lem1302060 x n h1 h2) (fun h2 : term40 x n => @lem1302055 x n h1)). Qed.
Lemma lem1302062 (x : nadd) (n : nat) (h1 : term30 x n) : term40 x n.
Proof. exact (EQ_MP (@lem1302061 x n h1) (@lem1302055 x n h1)). Qed.
Lemma lem1302063 (x : nadd) (n : nat) : term72 x n.
Proof. exact (fun h0 : term30 x n => @lem1302062 x n h0). Qed.
Lemma lem1302064 (x : nadd) (n : nat) (h1 : term28 x n) : term40 x n.
Proof. exact (@lem1302063 x n (@lem1301972 x n h1)). Qed.
Lemma lem1302065 (x : nadd) (n : nat) : term73 x n.
Proof. exact (fun h0 : term28 x n => @lem1302064 x n h0). Qed.
Lemma lem1302070 (x : nadd) : term74 x.
Proof. exact (fun n : nat => @lem1302065 x n). Qed.
Lemma lem1302075 : term75.
Proof. exact (fun x : nadd => @lem1302070 x). Qed.
