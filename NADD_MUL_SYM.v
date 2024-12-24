Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_MUL_SYM_term_abbrevs.
Require Import ADD_AC_spec.
Require Import BOUNDS_DIVIDED_spec.
Require Import DIST_LMUL_spec.
Require Import DIST_SYM_spec.
Require Import LE_ADD2_spec.
Require Import MULT_SYM_spec.
Require Import NADD_ALTMUL_spec.
Require Import NADD_MUL_spec.
Require Import REFL_CLAUSE_spec.
Require Import RIGHT_ADD_DISTRIB_spec.
Require Import nadd_eq_spec.
Require Import thm0_spec.
Require Import thm1259719_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1842_spec.
Require Import thm272809_spec.
Require Import thm7_spec.
Lemma lem1277880 (m : nat) : term0 m.
Proof. exact (@lem81820 m). Qed.
Lemma lem1277881 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1277882 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1277881 m) (@lem1277880 m)). Qed.
Lemma lem1277883 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1277882 m n). Qed.
Lemma lem1277884 (n : nat) (m : nat) : (term2 m n) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1277886 (m : nat) : term3 m.
Proof. exact (@lem1244997 m). Qed.
Lemma lem1277887 (m : nat) : (term3 m) = (term4 m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem1277888 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem1277887 m) (@lem1277886 m)). Qed.
Lemma lem1277889 (m : nat) (n : nat) : term5 m n.
Proof. exact (@lem1277888 m n). Qed.
Lemma lem1277890 (n : nat) (m : nat) : (term5 m n) = ((term6 m n) = (term6 n m)).
Proof. exact (eq_refl (term5 m n)). Qed.
Lemma lem1277892 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem1277893 (m : nat) (h1 : term7) : term8 m.
Proof. exact (@lem1277892 h1 m). Qed.
Lemma lem1277894 (m : nat) : (term8 m) = (term9 m).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem1277895 (m : nat) (h1 : term7) : term9 m.
Proof. exact (EQ_MP (@lem1277894 m) (@lem1277893 m h1)). Qed.
Lemma lem1277896 (m : nat) (n : nat) (h1 : term7) : term10 m n.
Proof. exact (@lem1277895 m h1 n). Qed.
Lemma lem1277897 (m : nat) (n : nat) : (term10 m n) = (term11 m n).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem1277898 (m : nat) (n : nat) (h1 : term7) : term11 m n.
Proof. exact (EQ_MP (@lem1277897 m n) (@lem1277896 m n h1)). Qed.
Lemma lem1277899 (m : nat) (n : nat) (p : nat) (h1 : term7) : term12 m n p.
Proof. exact (@lem1277898 m n h1 p). Qed.
Lemma lem1277900 (m : nat) (n : nat) (p : nat) : (term12 m n p) = (term13 m n p).
Proof. exact (eq_refl (term12 m n p)). Qed.
Lemma lem1277901 (m : nat) (n : nat) (p : nat) (h1 : term7) : term13 m n p.
Proof. exact (EQ_MP (@lem1277900 m n p) (@lem1277899 m n p h1)). Qed.
Lemma lem1277902 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term7) : term14 m n p q.
Proof. exact (@lem1277901 m n p h1 q). Qed.
Lemma lem1277903 (m : nat) (n : nat) (p : nat) (q : nat) : (term14 m n p q) = (term15 m n p q).
Proof. exact (eq_refl (term14 m n p q)). Qed.
Lemma lem1277904 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term7) : term15 m n p q.
Proof. exact (EQ_MP (@lem1277903 m n p q) (@lem1277902 m n p q h1)). Qed.
Lemma lem1277905 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term16 m p n q) : term16 m p n q.
Proof. exact (h1). Qed.
Lemma lem1277906 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term7) (h2 : term16 m p n q) : term17 m n p q.
Proof. exact (@lem1277904 m n p q h1 (@lem1277905 m p n q h2)). Qed.
Lemma lem1277907 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term16 m p n q) : term18 m n p q.
Proof. exact (fun h0 : term7 => @lem1277906 m p n q h0 h1). Qed.
Lemma lem1277908 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem1277909 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term7) (h2 : term16 m p n q) : term17 m n p q.
Proof. exact (@lem1277907 m p n q h2 (@lem1277908 h1)). Qed.
Lemma lem1277910 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term7) : term15 m n p q.
Proof. exact (fun h0 : term16 m p n q => @lem1277909 m p n q h1 h0). Qed.
Lemma lem1277911 (m : nat) (n : nat) (p : nat) (h1 : term7) : term13 m n p.
Proof. exact (fun q : nat => @lem1277910 m n p q h1). Qed.
Lemma lem1277912 (m : nat) (n : nat) (h1 : term7) : term11 m n.
Proof. exact (fun p : nat => @lem1277911 m n p h1). Qed.
Lemma lem1277913 (m : nat) (h1 : term7) : term9 m.
Proof. exact (fun n : nat => @lem1277912 m n h1). Qed.
Lemma lem1277914 (h1 : term7) : term7.
Proof. exact (fun m : nat => @lem1277913 m h1). Qed.
Lemma lem1277915 : term19.
Proof. exact (fun h0 : term7 => @lem1277914 h0). Qed.
Lemma lem1277916 : term7.
Proof. exact (@lem1277915 (@lem101399)). Qed.
Lemma lem1277917 (m : nat) : term8 m.
Proof. exact (@lem1277916 m). Qed.
Lemma lem1277918 (m : nat) : (term8 m) = (term9 m).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem1277919 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem1277918 m) (@lem1277917 m)). Qed.
Lemma lem1277920 (m : nat) (n : nat) : term10 m n.
Proof. exact (@lem1277919 m n). Qed.
Lemma lem1277921 (m : nat) (n : nat) : (term10 m n) = (term11 m n).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem1277922 (m : nat) (n : nat) : term11 m n.
Proof. exact (EQ_MP (@lem1277921 m n) (@lem1277920 m n)). Qed.
Lemma lem1277923 (m : nat) (n : nat) (p : nat) : term12 m n p.
Proof. exact (@lem1277922 m n p). Qed.
Lemma lem1277924 (m : nat) (n : nat) (p : nat) : (term12 m n p) = (term13 m n p).
Proof. exact (eq_refl (term12 m n p)). Qed.
Lemma lem1277925 (m : nat) (n : nat) (p : nat) : term13 m n p.
Proof. exact (EQ_MP (@lem1277924 m n p) (@lem1277923 m n p)). Qed.
Lemma lem1277926 (m : nat) (n : nat) (p : nat) (q : nat) : term14 m n p q.
Proof. exact (@lem1277925 m n p q). Qed.
Lemma lem1277927 (m : nat) (n : nat) (p : nat) (q : nat) : (term14 m n p q) = (term15 m n p q).
Proof. exact (eq_refl (term14 m n p q)). Qed.
Lemma lem1277929 (m : nat) : term20 m.
Proof. exact (@lem1259719 m). Qed.
Lemma lem1277930 (m : nat) : (term20 m) = (term21 m).
Proof. exact (eq_refl (term20 m)). Qed.
Lemma lem1277931 (m : nat) : term21 m.
Proof. exact (EQ_MP (@lem1277930 m) (@lem1277929 m)). Qed.
Lemma lem1277932 (m : nat) (n : nat) : term22 m n.
Proof. exact (@lem1277931 m n). Qed.
Lemma lem1277933 (m : nat) (n : nat) : (term22 m n) = (term23 m n).
Proof. exact (eq_refl (term22 m n)). Qed.
Lemma lem1277934 (m : nat) (n : nat) : term23 m n.
Proof. exact (EQ_MP (@lem1277933 m n) (@lem1277932 m n)). Qed.
Lemma lem1277935 (m : nat) (n : nat) (p : nat) : term24 m n p.
Proof. exact (@lem1277934 m n p). Qed.
Lemma lem1277936 (m : nat) (n : nat) (p : nat) : (term24 m n p) = (term25 m n p).
Proof. exact (eq_refl (term24 m n p)). Qed.
Lemma lem1277937 (m : nat) (n : nat) (p : nat) : term25 m n p.
Proof. exact (EQ_MP (@lem1277936 m n p) (@lem1277935 m n p)). Qed.
Lemma lem1277938 (h1 : term26) : term26.
Proof. exact (h1). Qed.
Lemma lem1277939 (m : nat) (h1 : term26) : term27 m.
Proof. exact (@lem1277938 h1 m). Qed.
Lemma lem1277940 (m : nat) : (term27 m) = (term28 m).
Proof. exact (eq_refl (term27 m)). Qed.
Lemma lem1277941 (m : nat) (h1 : term26) : term28 m.
Proof. exact (EQ_MP (@lem1277940 m) (@lem1277939 m h1)). Qed.
Lemma lem1277942 (m : nat) (n : nat) (h1 : term26) : term29 m n.
Proof. exact (@lem1277941 m h1 n). Qed.
Lemma lem1277943 (n : nat) (m : nat) : (term29 m n) = (term30 n m).
Proof. exact (eq_refl (term29 m n)). Qed.
Lemma lem1277944 (n : nat) (m : nat) (h1 : term26) : term30 n m.
Proof. exact (EQ_MP (@lem1277943 n m) (@lem1277942 m n h1)). Qed.
Lemma lem1277945 (n : nat) (m : nat) (p : nat) (h1 : term26) : term31 n m p.
Proof. exact (@lem1277944 n m h1 p). Qed.
Lemma lem1277946 (n : nat) (m : nat) (p : nat) : (term31 n m p) = (term32 n m p).
Proof. exact (eq_refl (term31 n m p)). Qed.
Lemma lem1277947 (n : nat) (m : nat) (p : nat) (h1 : term26) : term32 n m p.
Proof. exact (EQ_MP (@lem1277946 n m p) (@lem1277945 n m p h1)). Qed.
Lemma lem1277948 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem1277949 (p : nat) (m : nat) (n : nat) (h1 : term26) (h2 : Peano.le m n) : term33 n m p.
Proof. exact (@lem1277947 n m p h1 (@lem1277948 m n h2)). Qed.
Lemma lem1277950 (m : nat) (n : nat) (h1 : term26) (h2 : Peano.le m n) : term34 n m.
Proof. exact (fun p : nat => @lem1277949 p m n h1 h2). Qed.
Lemma lem1277951 (n : nat) (m : nat) (h1 : term26) : term35 n m.
Proof. exact (fun h0 : Peano.le m n => @lem1277950 m n h1 h0). Qed.
Lemma lem1277952 (m : nat) (h1 : term26) : term36 m.
Proof. exact (fun n : nat => @lem1277951 n m h1). Qed.
Lemma lem1277953 (h1 : term26) : term37.
Proof. exact (fun m : nat => @lem1277952 m h1). Qed.
Lemma lem1277954 : term38.
Proof. exact (fun h0 : term26 => @lem1277953 h0). Qed.
Lemma lem1277955 : term37.
Proof. exact (@lem1277954 (@lem272809)). Qed.
Lemma lem1277956 (m : nat) : term39 m.
Proof. exact (@lem1277955 m). Qed.
Lemma lem1277957 (m : nat) : (term39 m) = (term36 m).
Proof. exact (eq_refl (term39 m)). Qed.
Lemma lem1277958 (m : nat) : term36 m.
Proof. exact (EQ_MP (@lem1277957 m) (@lem1277956 m)). Qed.
Lemma lem1277959 (m : nat) (n : nat) : term40 m n.
Proof. exact (@lem1277958 m n). Qed.
Lemma lem1277960 (n : nat) (m : nat) : (term40 m n) = (term35 n m).
Proof. exact (eq_refl (term40 m n)). Qed.
Lemma lem1277963 (n : nat) (m : nat) : term35 n m.
Proof. exact (EQ_MP (@lem1277960 n m) (@lem1277959 m n)). Qed.
Lemma lem1277964 (n : nat) (m : nat) (p : nat) : term41 n m p.
Proof. exact (@lem1277963 (term42 m n p) (term6 m p)). Qed.
Lemma lem1277965 (n : nat) (m : nat) (p : nat) : term43 n m p.
Proof. exact (@lem1277964 n m p (@lem1277937 m n p)). Qed.
Lemma lem1277966 (n : nat) (m : nat) : term44 n m.
Proof. exact (fun p : nat => @lem1277965 n m p). Qed.
Lemma lem1277967 (n : nat) : term45 n.
Proof. exact (fun m : nat => @lem1277966 n m). Qed.
Lemma lem1277968 : term46.
Proof. exact (fun n : nat => @lem1277967 n). Qed.
Lemma lem1277969 (h1 : term46) : term46.
Proof. exact (h1). Qed.
Lemma lem1277970 (n : nat) (h1 : term46) : term47 n.
Proof. exact (@lem1277969 h1 n). Qed.
Lemma lem1277971 (n : nat) : (term47 n) = (term45 n).
Proof. exact (eq_refl (term47 n)). Qed.
Lemma lem1277972 (n : nat) (h1 : term46) : term45 n.
Proof. exact (EQ_MP (@lem1277971 n) (@lem1277970 n h1)). Qed.
Lemma lem1277973 (n : nat) (m : nat) (h1 : term46) : term48 n m.
Proof. exact (@lem1277972 n h1 m). Qed.
Lemma lem1277974 (n : nat) (m : nat) : (term48 n m) = (term44 n m).
Proof. exact (eq_refl (term48 n m)). Qed.
Lemma lem1277975 (n : nat) (m : nat) (h1 : term46) : term44 n m.
Proof. exact (EQ_MP (@lem1277974 n m) (@lem1277973 n m h1)). Qed.
Lemma lem1277976 (n : nat) (m : nat) (p : nat) (h1 : term46) : term49 n m p.
Proof. exact (@lem1277975 n m h1 p). Qed.
Lemma lem1277977 (n : nat) (m : nat) (p : nat) : (term49 n m p) = (term43 n m p).
Proof. exact (eq_refl (term49 n m p)). Qed.
Lemma lem1277978 (n : nat) (m : nat) (p : nat) (h1 : term46) : term43 n m p.
Proof. exact (EQ_MP (@lem1277977 n m p) (@lem1277976 n m p h1)). Qed.
Lemma lem1277979 (n : nat) (m : nat) (p : nat) (p' : nat) (h1 : term46) : term50 n m p p'.
Proof. exact (@lem1277978 n m p h1 p'). Qed.
Lemma lem1277980 (n : nat) (m : nat) (p : nat) (p' : nat) : (term50 n m p p') = (term51 n m p p').
Proof. exact (eq_refl (term50 n m p p')). Qed.
Lemma lem1277981 (n : nat) (m : nat) (p : nat) (p' : nat) (h1 : term46) : term51 n m p p'.
Proof. exact (EQ_MP (@lem1277980 n m p p') (@lem1277979 n m p p' h1)). Qed.
Lemma lem1277982 (m : nat) (n : nat) (p : nat) (p' : nat) (h1 : term52 m n p p') : term52 m n p p'.
Proof. exact (h1). Qed.
Lemma lem1277983 (m : nat) (n : nat) (p : nat) (p' : nat) (h1 : term46) (h2 : term52 m n p p') : term53 m p p'.
Proof. exact (@lem1277981 n m p p' h1 (@lem1277982 m n p p' h2)). Qed.
Lemma lem1277984 (m : nat) (n : nat) (p : nat) (p' : nat) (h1 : term52 m n p p') : term54 m p p'.
Proof. exact (fun h0 : term46 => @lem1277983 m n p p' h0 h1). Qed.
Lemma lem1277985 (m : nat) (p : nat) (p' : nat) (h1 : term55 m p p') : term55 m p p'.
Proof. exact (h1). Qed.
Lemma lem1277986 (m : nat) (p : nat) (p' : nat) (h1 : term55 m p p') : term54 m p p'.
Proof. exact (ex_elim (@lem1277985 m p p' h1) (fun n : nat => fun h0 : term56 m p p' n => @lem1277984 m n p p' h0)). Qed.
Lemma lem1277987 (h1 : term46) : term46.
Proof. exact (h1). Qed.
Lemma lem1277988 (m : nat) (p : nat) (p' : nat) (h1 : term46) (h2 : term55 m p p') : term53 m p p'.
Proof. exact (@lem1277986 m p p' h2 (@lem1277987 h1)). Qed.
Lemma lem1277989 (m : nat) (p : nat) (p' : nat) (h1 : term46) : term57 m p p'.
Proof. exact (fun h0 : term55 m p p' => @lem1277988 m p p' h1 h0). Qed.
Lemma lem1277990 (m : nat) (p : nat) (h1 : term46) : term58 m p.
Proof. exact (fun p' : nat => @lem1277989 m p p' h1). Qed.
Lemma lem1277991 (m : nat) (h1 : term46) : term59 m.
Proof. exact (fun p : nat => @lem1277990 m p h1). Qed.
Lemma lem1277992 (h1 : term46) : term60.
Proof. exact (fun m : nat => @lem1277991 m h1). Qed.
Lemma lem1277993 : term61.
Proof. exact (fun h0 : term46 => @lem1277992 h0). Qed.
Lemma lem1277994 : term60.
Proof. exact (@lem1277993 (@lem1277968)). Qed.
Lemma lem1277995 (m : nat) : term62 m.
Proof. exact (@lem1277994 m). Qed.
Lemma lem1277996 (m : nat) : (term62 m) = (term59 m).
Proof. exact (eq_refl (term62 m)). Qed.
Lemma lem1277997 (m : nat) : term59 m.
Proof. exact (EQ_MP (@lem1277996 m) (@lem1277995 m)). Qed.
Lemma lem1277998 (m : nat) (p : nat) : term63 m p.
Proof. exact (@lem1277997 m p). Qed.
Lemma lem1277999 (m : nat) (p : nat) : (term63 m p) = (term58 m p).
Proof. exact (eq_refl (term63 m p)). Qed.
Lemma lem1278000 (m : nat) (p : nat) : term58 m p.
Proof. exact (EQ_MP (@lem1277999 m p) (@lem1277998 m p)). Qed.
Lemma lem1278001 (m : nat) (p : nat) (p' : nat) : term64 m p p'.
Proof. exact (@lem1278000 m p p'). Qed.
Lemma lem1278002 (m : nat) (p : nat) (p' : nat) : (term64 m p p') = (term57 m p p').
Proof. exact (eq_refl (term64 m p p')). Qed.
Lemma lem1278004 {A : Type'} (x : A) : term65 A x.
Proof. exact (@lem317 A x). Qed.
Lemma lem1278005 {A : Type'} (x : A) : (term65 A x) = ((x = x) = True).
Proof. exact (eq_refl (term65 A x)). Qed.
Lemma lem1278007 (n : nat) (m : nat) (p : nat) : term66 n m p.
Proof. exact (proj2 (@lem79120 n m p)). Qed.
Lemma lem1278014 (m : nat) (n : nat) (p : nat) : (term67 m n p) = (term68 m n p).
Proof. exact (proj1 (@lem1278007 n m p)). Qed.
Lemma lem1278015 (a : nat) (b : nat) (c : nat) (d : nat) : (term69 a b c d) = (term70 a b c d).
Proof. exact (@lem1278014 a b (Nat.add c d)). Qed.
Lemma lem1278031 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1278032 (a : nat) (b : nat) (c : nat) (d : nat) : (term71 a b c d) = (term72 a b c d).
Proof. exact (MK_COMB (@lem1278031) (@lem1278015 a b c d)). Qed.
Lemma lem1278034 (m : nat) (n : nat) (p : nat) : (term67 m n p) = (term68 m n p).
Proof. exact (proj1 (@lem1278007 n m p)). Qed.
Lemma lem1278035 (a : nat) (c : nat) (b : nat) (d : nat) : (term69 a c b d) = (term70 a c b d).
Proof. exact (@lem1278034 a c (Nat.add b d)). Qed.
Lemma lem1278043 (n : nat) (m : nat) (p : nat) : (term68 m n p) = (term68 n m p).
Proof. exact (proj2 (@lem1278007 n m p)). Qed.
Lemma lem1278044 (b : nat) (c : nat) (d : nat) : (term68 c b d) = (term68 b c d).
Proof. exact (@lem1278043 b c d). Qed.
Lemma lem1278054 (a : nat) : (Nat.add a) = (Nat.add a).
Proof. exact (eq_refl (Nat.add a)). Qed.
Lemma lem1278055 (a : nat) (b : nat) (c : nat) (d : nat) : (term70 a c b d) = (term70 a b c d).
Proof. exact (MK_COMB (@lem1278054 a) (@lem1278044 b c d)). Qed.
Lemma lem1278062 (a : nat) (b : nat) (c : nat) (d : nat) : (term69 a c b d) = (term70 a b c d).
Proof. exact (TRANS (@lem1278035 a c b d) (@lem1278055 a b c d)). Qed.
Lemma lem1278063 (a : nat) (b : nat) (c : nat) (d : nat) : ((term69 a b c d) = (term69 a c b d)) = ((term70 a b c d) = (term70 a b c d)).
Proof. exact (MK_COMB (@lem1278032 a b c d) (@lem1278062 a b c d)). Qed.
Lemma lem1278065 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1278005 A x) (@lem1278004 A x)). Qed.
Lemma lem1278066 (x : nat) : (x = x) = True.
Proof. exact (@lem1278065 nat x). Qed.
Lemma lem1278067 (a : nat) (b : nat) (c : nat) (d : nat) : ((term70 a b c d) = (term70 a b c d)) = True.
Proof. exact (@lem1278066 (term70 a b c d)). Qed.
Lemma lem1278068 (a : nat) (c : nat) (b : nat) (d : nat) : ((term69 a b c d) = (term69 a c b d)) = True.
Proof. exact (TRANS (@lem1278063 a b c d) (@lem1278067 a b c d)). Qed.
Lemma lem1278069 (a : nat) (c : nat) (b : nat) (d : nat) : True = ((term69 a b c d) = (term69 a c b d)).
Proof. exact (SYM (@lem1278068 a c b d)). Qed.
Lemma lem1278071 (m : nat) : term73 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem1278072 (m : nat) : (term73 m) = (term74 m).
Proof. exact (eq_refl (term73 m)). Qed.
Lemma lem1278073 (m : nat) : term74 m.
Proof. exact (EQ_MP (@lem1278072 m) (@lem1278071 m)). Qed.
Lemma lem1278074 (m : nat) (n : nat) : term75 m n.
Proof. exact (@lem1278073 m n). Qed.
Lemma lem1278075 (m : nat) (n : nat) : (term75 m n) = (term76 m n).
Proof. exact (eq_refl (term75 m n)). Qed.
Lemma lem1278076 (m : nat) (n : nat) : term76 m n.
Proof. exact (EQ_MP (@lem1278075 m n) (@lem1278074 m n)). Qed.
Lemma lem1278077 (m : nat) (n : nat) (p : nat) : term77 m n p.
Proof. exact (@lem1278076 m n p). Qed.
Lemma lem1278078 (m : nat) (n : nat) (p : nat) : (term77 m n p) = ((term78 m n p) = (term79 m n p)).
Proof. exact (eq_refl (term77 m n p)). Qed.
Lemma lem1278080 (m : nat) : term80 m.
Proof. exact (@lem1245388 m). Qed.
Lemma lem1278081 (m : nat) : (term80 m) = (term81 m).
Proof. exact (eq_refl (term80 m)). Qed.
Lemma lem1278082 (m : nat) : term81 m.
Proof. exact (EQ_MP (@lem1278081 m) (@lem1278080 m)). Qed.
Lemma lem1278083 (m : nat) (n : nat) : term82 m n.
Proof. exact (@lem1278082 m n). Qed.
Lemma lem1278084 (n : nat) (m : nat) : (term82 m n) = (term83 n m).
Proof. exact (eq_refl (term82 m n)). Qed.
Lemma lem1278085 (n : nat) (m : nat) : term83 n m.
Proof. exact (EQ_MP (@lem1278084 n m) (@lem1278083 m n)). Qed.
Lemma lem1278086 (n : nat) (m : nat) (p : nat) : term84 n m p.
Proof. exact (@lem1278085 n m p). Qed.
Lemma lem1278087 (n : nat) (m : nat) (p : nat) : (term84 n m p) = ((term85 m n p) = (term86 n m p)).
Proof. exact (eq_refl (term84 n m p)). Qed.
Lemma lem1278089 (P : nat -> nat) : term87 P.
Proof. exact (@lem1261317 P). Qed.
Lemma lem1278090 (P : nat -> nat) : (term87 P) = ((term88 P) = (term89 P)).
Proof. exact (eq_refl (term87 P)). Qed.
Lemma lem1278092 (y : nadd) : term90 y.
Proof. exact (@lem1267473 y). Qed.
Lemma lem1278093 (y : nadd) : (term90 y) = (term91 y).
Proof. exact (eq_refl (term90 y)). Qed.
Lemma lem1278094 (y : nadd) : term91 y.
Proof. exact (EQ_MP (@lem1278093 y) (@lem1278092 y)). Qed.
Lemma lem1278095 (y : nadd) (x : nadd) : term92 y x.
Proof. exact (@lem1278094 y x). Qed.
Lemma lem1278096 (y : nadd) (x : nadd) : (term92 y x) = (term93 y x).
Proof. exact (eq_refl (term92 y x)). Qed.
Lemma lem1278097 (y : nadd) (x : nadd) : term93 y x.
Proof. exact (EQ_MP (@lem1278096 y x) (@lem1278095 y x)). Qed.
Lemma lem1278098 (y : nadd) (x : nadd) (A2 : nat) (h1 : term94 y x A2) : term94 y x A2.
Proof. exact (h1). Qed.
Lemma lem1278099 (x : nadd) : term90 x.
Proof. exact (@lem1267473 x). Qed.
Lemma lem1278100 (x : nadd) : (term90 x) = (term91 x).
Proof. exact (eq_refl (term90 x)). Qed.
Lemma lem1278101 (x : nadd) : term91 x.
Proof. exact (EQ_MP (@lem1278100 x) (@lem1278099 x)). Qed.
Lemma lem1278102 (x : nadd) (y : nadd) : term92 x y.
Proof. exact (@lem1278101 x y). Qed.
Lemma lem1278103 (x : nadd) (y : nadd) : (term92 x y) = (term93 x y).
Proof. exact (eq_refl (term92 x y)). Qed.
Lemma lem1278104 (x : nadd) (y : nadd) : term93 x y.
Proof. exact (EQ_MP (@lem1278103 x y) (@lem1278102 x y)). Qed.
Lemma lem1278105 (x : nadd) (y : nadd) (A1 : nat) (h1 : term94 x y A1) : term94 x y A1.
Proof. exact (h1). Qed.
Lemma lem1278106 (x : nadd) : term95 x.
Proof. exact (@lem1277879 x). Qed.
Lemma lem1278107 (x : nadd) : (term95 x) = (term96 x).
Proof. exact (eq_refl (term95 x)). Qed.
Lemma lem1278108 (x : nadd) : term96 x.
Proof. exact (EQ_MP (@lem1278107 x) (@lem1278106 x)). Qed.
Lemma lem1278109 (x : nadd) (y : nadd) : term97 x y.
Proof. exact (@lem1278108 x y). Qed.
Lemma lem1278110 (x : nadd) (y : nadd) : (term97 x y) = ((term98 x y) = (term99 x y)).
Proof. exact (eq_refl (term97 x y)). Qed.
Lemma lem1278112 (x : nadd) : term100 x.
Proof. exact (@lem1267930 x). Qed.
Lemma lem1278113 (x : nadd) : (term100 x) = (term101 x).
Proof. exact (eq_refl (term100 x)). Qed.
Lemma lem1278114 (x : nadd) : term101 x.
Proof. exact (EQ_MP (@lem1278113 x) (@lem1278112 x)). Qed.
Lemma lem1278115 (x : nadd) (y : nadd) : term102 x y.
Proof. exact (@lem1278114 x y). Qed.
Lemma lem1278116 (x : nadd) (y : nadd) : (term102 x y) = ((nadd_eq x y) = (term103 x y)).
Proof. exact (eq_refl (term102 x y)). Qed.
Lemma lem1278119 (x : nadd) (y : nadd) : (nadd_eq x y) = (term103 x y).
Proof. exact (EQ_MP (@lem1278116 x y) (@lem1278115 x y)). Qed.
Lemma lem1278120 (y : nadd) (x : nadd) : (term104 y x) = (term105 y x).
Proof. exact (@lem1278119 (nadd_mul x y) (nadd_mul y x)). Qed.
Lemma lem1278130 (x : nadd) (y : nadd) : (term98 x y) = (term99 x y).
Proof. exact (EQ_MP (@lem1278110 x y) (@lem1278109 x y)). Qed.
Lemma lem1278131 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1278132 (x : nadd) (y : nadd) (n : nat) : (term106 x y n) = (term107 x y n).
Proof. exact (MK_COMB (@lem1278130 x y) (@lem1278131 n)). Qed.
Lemma lem1278134 {A B : Type'} (f : A -> B) (y : A) : (term108 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1278135 (f : nat -> nat) (y : nat) : (term109 f y) = (f y).
Proof. exact (@lem1278134 nat nat f y). Qed.
Lemma lem1278136 (x : nadd) (y : nadd) (n : nat) : (term110 x y n) = (term107 x y n).
Proof. exact (@lem1278135 (term99 x y) n). Qed.
Lemma lem1278137 (x : nadd) (y : nadd) (n : nat) : (term107 x y n) = (term111 x y n).
Proof. exact (eq_refl (term107 x y n)). Qed.
Lemma lem1278138 (x : nadd) (y : nadd) : (term112 x y) = (term99 x y).
Proof. exact (fun_ext (fun n : nat => @lem1278137 x y n)). Qed.
Lemma lem1278139 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1278140 (x : nadd) (y : nadd) (n : nat) : (term110 x y n) = (term107 x y n).
Proof. exact (MK_COMB (@lem1278138 x y) (@lem1278139 n)). Qed.
Lemma lem1278141 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1278142 (x : nadd) (y : nadd) (n : nat) : (term113 x y n) = (term114 x y n).
Proof. exact (MK_COMB (@lem1278141) (@lem1278140 x y n)). Qed.
Lemma lem1278143 (x : nadd) (y : nadd) (n : nat) : (term107 x y n) = (term111 x y n).
Proof. exact (eq_refl (term107 x y n)). Qed.
Lemma lem1278144 (x : nadd) (y : nadd) (n : nat) : ((term110 x y n) = (term107 x y n)) = ((term107 x y n) = (term111 x y n)).
Proof. exact (MK_COMB (@lem1278142 x y n) (@lem1278143 x y n)). Qed.
Lemma lem1278145 (x : nadd) (y : nadd) (n : nat) : (term107 x y n) = (term111 x y n).
Proof. exact (EQ_MP (@lem1278144 x y n) (@lem1278136 x y n)). Qed.
Lemma lem1278146 (x : nadd) (y : nadd) (n : nat) : (term106 x y n) = (term111 x y n).
Proof. exact (TRANS (@lem1278132 x y n) (@lem1278145 x y n)). Qed.
Lemma lem1278147 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1278148 (x : nadd) (y : nadd) (n : nat) : (term115 x y n) = (term116 x y n).
Proof. exact (MK_COMB (@lem1278147) (@lem1278146 x y n)). Qed.
Lemma lem1278150 (x : nadd) (y : nadd) : (term98 x y) = (term99 x y).
Proof. exact (EQ_MP (@lem1278110 x y) (@lem1278109 x y)). Qed.
Lemma lem1278151 (y : nadd) (x : nadd) : (term98 y x) = (term99 y x).
Proof. exact (@lem1278150 y x). Qed.
Lemma lem1278152 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1278153 (y : nadd) (x : nadd) (n : nat) : (term106 y x n) = (term107 y x n).
Proof. exact (MK_COMB (@lem1278151 y x) (@lem1278152 n)). Qed.
Lemma lem1278155 {A B : Type'} (f : A -> B) (y : A) : (term108 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1278156 (f : nat -> nat) (y : nat) : (term109 f y) = (f y).
Proof. exact (@lem1278155 nat nat f y). Qed.
Lemma lem1278157 (y : nadd) (x : nadd) (n : nat) : (term110 y x n) = (term107 y x n).
Proof. exact (@lem1278156 (term99 y x) n). Qed.
Lemma lem1278158 (y : nadd) (x : nadd) (n : nat) : (term107 y x n) = (term111 y x n).
Proof. exact (eq_refl (term107 y x n)). Qed.
Lemma lem1278159 (y : nadd) (x : nadd) : (term112 y x) = (term99 y x).
Proof. exact (fun_ext (fun n : nat => @lem1278158 y x n)). Qed.
Lemma lem1278160 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1278161 (y : nadd) (x : nadd) (n : nat) : (term110 y x n) = (term107 y x n).
Proof. exact (MK_COMB (@lem1278159 y x) (@lem1278160 n)). Qed.
Lemma lem1278162 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1278163 (y : nadd) (x : nadd) (n : nat) : (term113 y x n) = (term114 y x n).
Proof. exact (MK_COMB (@lem1278162) (@lem1278161 y x n)). Qed.
Lemma lem1278164 (y : nadd) (x : nadd) (n : nat) : (term107 y x n) = (term111 y x n).
Proof. exact (eq_refl (term107 y x n)). Qed.
Lemma lem1278165 (y : nadd) (x : nadd) (n : nat) : ((term110 y x n) = (term107 y x n)) = ((term107 y x n) = (term111 y x n)).
Proof. exact (MK_COMB (@lem1278163 y x n) (@lem1278164 y x n)). Qed.
Lemma lem1278166 (y : nadd) (x : nadd) (n : nat) : (term107 y x n) = (term111 y x n).
Proof. exact (EQ_MP (@lem1278165 y x n) (@lem1278157 y x n)). Qed.
Lemma lem1278167 (y : nadd) (x : nadd) (n : nat) : (term106 y x n) = (term111 y x n).
Proof. exact (TRANS (@lem1278153 y x n) (@lem1278166 y x n)). Qed.
Lemma lem1278168 (y : nadd) (x : nadd) (n : nat) : (term117 y x n) = (term118 y x n).
Proof. exact (MK_COMB (@lem1278148 x y n) (@lem1278167 y x n)). Qed.
Lemma lem1278169 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1278170 (y : nadd) (x : nadd) (n : nat) : (term119 y x n) = (term120 y x n).
Proof. exact (MK_COMB (@lem1278169) (@lem1278168 y x n)). Qed.
Lemma lem1278171 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1278172 (y : nadd) (x : nadd) (n : nat) : (term121 y x n) = (term122 y x n).
Proof. exact (MK_COMB (@lem1278171) (@lem1278170 y x n)). Qed.
Lemma lem1278173 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1278174 (y : nadd) (x : nadd) (n : nat) (B : nat) : (term123 y x n B) = (term124 y x n B).
Proof. exact (MK_COMB (@lem1278172 y x n) (@lem1278173 B)). Qed.
Lemma lem1278175 (y : nadd) (x : nadd) (B : nat) : (term125 y x B) = (term126 y x B).
Proof. exact (fun_ext (fun n : nat => @lem1278174 y x n B)). Qed.
Lemma lem1278176 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1278177 (y : nadd) (x : nadd) (B : nat) : (term127 y x B) = (term128 y x B).
Proof. exact (MK_COMB (@lem1278176) (@lem1278175 y x B)). Qed.
Lemma lem1278182 (y : nadd) (x : nadd) : (term129 y x) = (term130 y x).
Proof. exact (fun_ext (fun B : nat => @lem1278177 y x B)). Qed.
Lemma lem1278183 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1278184 (y : nadd) (x : nadd) : (term105 y x) = (term131 y x).
Proof. exact (MK_COMB (@lem1278183) (@lem1278182 y x)). Qed.
Lemma lem1278189 (y : nadd) (x : nadd) : (term104 y x) = (term131 y x).
Proof. exact (TRANS (@lem1278120 y x) (@lem1278184 y x)). Qed.
Lemma lem1278190 (y : nadd) (x : nadd) : (term131 y x) = (term104 y x).
Proof. exact (SYM (@lem1278189 y x)). Qed.
Lemma lem1278191 (x : nadd) (y : nadd) (A1 : nat) (h1 : term94 x y A1) : term94 x y A1.
Proof. exact (h1). Qed.
Lemma lem1278192 (x : nadd) (y : nadd) (A1 : nat) (B1 : nat) (h1 : term132 x y A1 B1) : term132 x y A1 B1.
Proof. exact (h1). Qed.
Lemma lem1278193 (y : nadd) (x : nadd) (A2 : nat) (h1 : term94 y x A2) : term94 y x A2.
Proof. exact (h1). Qed.
Lemma lem1278194 (y : nadd) (x : nadd) (A2 : nat) (B2 : nat) (h1 : term132 y x A2 B2) : term132 y x A2 B2.
Proof. exact (h1). Qed.
Lemma lem1278196 (P : nat -> nat) : (term88 P) = (term89 P).
Proof. exact (EQ_MP (@lem1278090 P) (@lem1278089 P)). Qed.
Lemma lem1278197 (y : nadd) (x : nadd) : (term133 y x) = (term134 y x).
Proof. exact (@lem1278196 (term135 y x)). Qed.
Lemma lem1278198 (y : nadd) (x : nadd) (n : nat) : (term136 y x n) = (term120 y x n).
Proof. exact (eq_refl (term136 y x n)). Qed.
Lemma lem1278199 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1278200 (y : nadd) (x : nadd) (n : nat) : (term137 y x n) = (term122 y x n).
Proof. exact (MK_COMB (@lem1278199) (@lem1278198 y x n)). Qed.
Lemma lem1278201 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1278202 (y : nadd) (x : nadd) (n : nat) (B : nat) : (term138 y x n B) = (term124 y x n B).
Proof. exact (MK_COMB (@lem1278200 y x n) (@lem1278201 B)). Qed.
Lemma lem1278203 (y : nadd) (x : nadd) (B : nat) : (term139 y x B) = (term126 y x B).
Proof. exact (fun_ext (fun n : nat => @lem1278202 y x n B)). Qed.
Lemma lem1278204 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1278205 (y : nadd) (x : nadd) (B : nat) : (term140 y x B) = (term128 y x B).
Proof. exact (MK_COMB (@lem1278204) (@lem1278203 y x B)). Qed.
Lemma lem1278206 (y : nadd) (x : nadd) : (term141 y x) = (term130 y x).
Proof. exact (fun_ext (fun B : nat => @lem1278205 y x B)). Qed.
Lemma lem1278207 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1278208 (y : nadd) (x : nadd) : (term133 y x) = (term131 y x).
Proof. exact (MK_COMB (@lem1278207) (@lem1278206 y x)). Qed.
Lemma lem1278209 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1278210 (y : nadd) (x : nadd) : (term142 y x) = (term143 y x).
Proof. exact (MK_COMB (@lem1278209) (@lem1278208 y x)). Qed.
Lemma lem1278211 (y : nadd) (x : nadd) (n : nat) : (term136 y x n) = (term120 y x n).
Proof. exact (eq_refl (term136 y x n)). Qed.
Lemma lem1278212 (n : nat) : (Nat.mul n) = (Nat.mul n).
Proof. exact (eq_refl (Nat.mul n)). Qed.
Lemma lem1278213 (y : nadd) (x : nadd) (n : nat) : (term144 y x n) = (term145 y x n).
Proof. exact (MK_COMB (@lem1278212 n) (@lem1278211 y x n)). Qed.
Lemma lem1278214 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1278215 (y : nadd) (x : nadd) (n : nat) : (term146 y x n) = (term147 y x n).
Proof. exact (MK_COMB (@lem1278214) (@lem1278213 y x n)). Qed.
Lemma lem1278216 (A : nat) (n : nat) (B : nat) : (term148 A n B) = (term148 A n B).
Proof. exact (eq_refl (term148 A n B)). Qed.
Lemma lem1278217 (y : nadd) (x : nadd) (A : nat) (n : nat) (B : nat) : (term149 y x A n B) = (term150 y x A n B).
Proof. exact (MK_COMB (@lem1278215 y x n) (@lem1278216 A n B)). Qed.
Lemma lem1278218 (y : nadd) (x : nadd) (A : nat) (B : nat) : (term151 y x A B) = (term152 y x A B).
Proof. exact (fun_ext (fun n : nat => @lem1278217 y x A n B)). Qed.
Lemma lem1278219 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1278220 (y : nadd) (x : nadd) (A : nat) (B : nat) : (term153 y x A B) = (term154 y x A B).
Proof. exact (MK_COMB (@lem1278219) (@lem1278218 y x A B)). Qed.
Lemma lem1278221 (y : nadd) (x : nadd) (A : nat) : (term155 y x A) = (term156 y x A).
Proof. exact (fun_ext (fun B : nat => @lem1278220 y x A B)). Qed.
Lemma lem1278222 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1278223 (y : nadd) (x : nadd) (A : nat) : (term157 y x A) = (term158 y x A).
Proof. exact (MK_COMB (@lem1278222) (@lem1278221 y x A)). Qed.
Lemma lem1278224 (y : nadd) (x : nadd) : (term159 y x) = (term160 y x).
Proof. exact (fun_ext (fun A : nat => @lem1278223 y x A)). Qed.
Lemma lem1278225 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1278226 (y : nadd) (x : nadd) : (term134 y x) = (term161 y x).
Proof. exact (MK_COMB (@lem1278225) (@lem1278224 y x)). Qed.
Lemma lem1278227 (y : nadd) (x : nadd) : ((term133 y x) = (term134 y x)) = ((term131 y x) = (term161 y x)).
Proof. exact (MK_COMB (@lem1278210 y x) (@lem1278226 y x)). Qed.
Lemma lem1278228 (y : nadd) (x : nadd) : (term131 y x) = (term161 y x).
Proof. exact (EQ_MP (@lem1278227 y x) (@lem1278197 y x)). Qed.
Lemma lem1278243 (y : nadd) (x : nadd) : (term161 y x) = (term131 y x).
Proof. exact (SYM (@lem1278228 y x)). Qed.
Lemma lem1278257 (n : nat) (m : nat) (p : nat) : (term85 m n p) = (term86 n m p).
Proof. exact (EQ_MP (@lem1278087 n m p) (@lem1278086 n m p)). Qed.
Lemma lem1278258 (y : nadd) (x : nadd) (n : nat) : (term145 y x n) = (term162 y x n).
Proof. exact (@lem1278257 (term111 x y n) n (term111 y x n)). Qed.
Lemma lem1278259 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1278260 (y : nadd) (x : nadd) (n : nat) : (term147 y x n) = (term163 y x n).
Proof. exact (MK_COMB (@lem1278259) (@lem1278258 y x n)). Qed.
Lemma lem1278261 (A : nat) (n : nat) (B : nat) : (term148 A n B) = (term148 A n B).
Proof. exact (eq_refl (term148 A n B)). Qed.
Lemma lem1278262 (y : nadd) (x : nadd) (A : nat) (n : nat) (B : nat) : (term150 y x A n B) = (term164 y x A n B).
Proof. exact (MK_COMB (@lem1278260 y x n) (@lem1278261 A n B)). Qed.
Lemma lem1278263 (y : nadd) (x : nadd) (A : nat) (B : nat) : (term152 y x A B) = (term165 y x A B).
Proof. exact (fun_ext (fun n : nat => @lem1278262 y x A n B)). Qed.
Lemma lem1278264 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1278265 (y : nadd) (x : nadd) (A : nat) (B : nat) : (term154 y x A B) = (term166 y x A B).
Proof. exact (MK_COMB (@lem1278264) (@lem1278263 y x A B)). Qed.
Lemma lem1278270 (y : nadd) (x : nadd) (A : nat) : (term156 y x A) = (term167 y x A).
Proof. exact (fun_ext (fun B : nat => @lem1278265 y x A B)). Qed.
Lemma lem1278271 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1278272 (y : nadd) (x : nadd) (A : nat) : (term158 y x A) = (term168 y x A).
Proof. exact (MK_COMB (@lem1278271) (@lem1278270 y x A)). Qed.
Lemma lem1278277 (y : nadd) (x : nadd) : (term160 y x) = (term169 y x).
Proof. exact (fun_ext (fun A : nat => @lem1278272 y x A)). Qed.
Lemma lem1278278 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1278279 (y : nadd) (x : nadd) : (term161 y x) = (term170 y x).
Proof. exact (MK_COMB (@lem1278278) (@lem1278277 y x)). Qed.
Lemma lem1278284 (y : nadd) (x : nadd) : (term170 y x) = (term161 y x).
Proof. exact (SYM (@lem1278279 y x)). Qed.
Lemma lem1278286 (m : nat) (n : nat) (p : nat) : (term78 m n p) = (term79 m n p).
Proof. exact (EQ_MP (@lem1278078 m n p) (@lem1278077 m n p)). Qed.
Lemma lem1278287 (A1 : nat) (A2 : nat) (n : nat) : (term78 A1 A2 n) = (term79 A1 A2 n).
Proof. exact (@lem1278286 A1 A2 n). Qed.
Lemma lem1278288 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1278289 (A1 : nat) (A2 : nat) (n : nat) : (term171 A1 A2 n) = (term172 A1 A2 n).
Proof. exact (MK_COMB (@lem1278288) (@lem1278287 A1 A2 n)). Qed.
Lemma lem1278290 (B1 : nat) (B2 : nat) : (Nat.add B1 B2) = (Nat.add B1 B2).
Proof. exact (eq_refl (Nat.add B1 B2)). Qed.
Lemma lem1278291 (A1 : nat) (A2 : nat) (n : nat) (B1 : nat) (B2 : nat) : (term173 A1 A2 n B1 B2) = (term174 A1 A2 n B1 B2).
Proof. exact (MK_COMB (@lem1278289 A1 A2 n) (@lem1278290 B1 B2)). Qed.
Lemma lem1278292 (y : nadd) (x : nadd) (n : nat) : (term163 y x n) = (term163 y x n).
Proof. exact (eq_refl (term163 y x n)). Qed.
Lemma lem1278293 (y : nadd) (x : nadd) (A1 : nat) (A2 : nat) (n : nat) (B1 : nat) (B2 : nat) : (term175 y x A1 A2 n B1 B2) = (term176 y x A1 A2 n B1 B2).
Proof. exact (MK_COMB (@lem1278292 y x n) (@lem1278291 A1 A2 n B1 B2)). Qed.
Lemma lem1278294 (y : nadd) (x : nadd) (A1 : nat) (A2 : nat) (n : nat) (B1 : nat) (B2 : nat) : (term176 y x A1 A2 n B1 B2) = (term175 y x A1 A2 n B1 B2).
Proof. exact (SYM (@lem1278293 y x A1 A2 n B1 B2)). Qed.
Lemma lem1278296 (a : nat) (c : nat) (b : nat) (d : nat) : (term69 a b c d) = (term69 a c b d).
Proof. exact (EQ_MP (@lem1278069 a c b d) (@lem0)). Qed.
Lemma lem1278297 (A1 : nat) (B1 : nat) (A2 : nat) (n : nat) (B2 : nat) : (term174 A1 A2 n B1 B2) = (term177 A1 B1 A2 n B2).
Proof. exact (@lem1278296 (Nat.mul A1 n) B1 (Nat.mul A2 n) B2). Qed.
Lemma lem1278298 (y : nadd) (x : nadd) (n : nat) : (term163 y x n) = (term163 y x n).
Proof. exact (eq_refl (term163 y x n)). Qed.
Lemma lem1278299 (y : nadd) (x : nadd) (A1 : nat) (B1 : nat) (A2 : nat) (n : nat) (B2 : nat) : (term176 y x A1 A2 n B1 B2) = (term178 y x A1 B1 A2 n B2).
Proof. exact (MK_COMB (@lem1278298 y x n) (@lem1278297 A1 B1 A2 n B2)). Qed.
Lemma lem1278300 (y : nadd) (x : nadd) (A1 : nat) (A2 : nat) (n : nat) (B1 : nat) (B2 : nat) : (term178 y x A1 B1 A2 n B2) = (term176 y x A1 A2 n B1 B2).
Proof. exact (SYM (@lem1278299 y x A1 B1 A2 n B2)). Qed.
Lemma lem1278302 (m : nat) (p : nat) (p' : nat) : term57 m p p'.
Proof. exact (EQ_MP (@lem1278002 m p p') (@lem1278001 m p p')). Qed.
Lemma lem1278303 (y : nadd) (x : nadd) (A1 : nat) (B1 : nat) (A2 : nat) (n : nat) (B2 : nat) : term179 y x A1 B1 A2 n B2.
Proof. exact (@lem1278302 (term180 x y n) (term180 y x n) (term177 A1 B1 A2 n B2)). Qed.
Lemma lem1278305 (m : nat) (n : nat) (p : nat) (q : nat) : term15 m n p q.
Proof. exact (EQ_MP (@lem1277927 m n p q) (@lem1277926 m n p q)). Qed.
Lemma lem1278306 (y : nadd) (x : nadd) (A1 : nat) (B1 : nat) (A2 : nat) (n : nat) (B2 : nat) : term181 y x A1 B1 A2 n B2.
Proof. exact (@lem1278305 (term182 x y n) (term183 y x n) (term148 A1 n B1) (term148 A2 n B2)). Qed.
Lemma lem1278307 (n : nat) (x : nadd) (y : nadd) (A1 : nat) (B1 : nat) (h1 : term132 x y A1 B1) : term184 x y A1 B1 n.
Proof. exact (@lem1278192 x y A1 B1 h1 n). Qed.
Lemma lem1278308 (x : nadd) (y : nadd) (A1 : nat) (n : nat) (B1 : nat) : (term184 x y A1 B1 n) = (term185 x y A1 n B1).
Proof. exact (eq_refl (term184 x y A1 B1 n)). Qed.
Lemma lem1278309 (n : nat) (x : nadd) (y : nadd) (A1 : nat) (B1 : nat) (h1 : term132 x y A1 B1) : term185 x y A1 n B1.
Proof. exact (EQ_MP (@lem1278308 x y A1 n B1) (@lem1278307 n x y A1 B1 h1)). Qed.
Lemma lem1278310 (x : nadd) (y : nadd) (A1 : nat) (n : nat) (B1 : nat) : (term185 x y A1 n B1) = ((term185 x y A1 n B1) = True).
Proof. exact (@lem7 (term185 x y A1 n B1)). Qed.
Lemma lem1278320 (n : nat) (x : nadd) (y : nadd) (A1 : nat) (B1 : nat) (h1 : term132 x y A1 B1) : (term185 x y A1 n B1) = True.
Proof. exact (EQ_MP (@lem1278310 x y A1 n B1) (@lem1278309 n x y A1 B1 h1)). Qed.
Lemma lem1278321 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1278322 (n : nat) (x : nadd) (y : nadd) (A1 : nat) (B1 : nat) (h1 : term132 x y A1 B1) : (term186 x y A1 n B1) = (and True).
Proof. exact (MK_COMB (@lem1278321) (@lem1278320 n x y A1 B1 h1)). Qed.
Lemma lem1278323 (y : nadd) (x : nadd) (A2 : nat) (n : nat) (B2 : nat) : (term187 y x A2 n B2) = (term187 y x A2 n B2).
Proof. exact (eq_refl (term187 y x A2 n B2)). Qed.
Lemma lem1278324 (A2 : nat) (n : nat) (B2 : nat) (x : nadd) (y : nadd) (A1 : nat) (B1 : nat) (h1 : term132 x y A1 B1) : (term188 A1 B1 y x A2 n B2) = (term189 y x A2 n B2).
Proof. exact (MK_COMB (@lem1278322 n x y A1 B1 h1) (@lem1278323 y x A2 n B2)). Qed.
Lemma lem1278326 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1278327 (y : nadd) (x : nadd) (A2 : nat) (n : nat) (B2 : nat) : (term189 y x A2 n B2) = (term187 y x A2 n B2).
Proof. exact (@lem1278326 (term187 y x A2 n B2)). Qed.
Lemma lem1278328 (A2 : nat) (n : nat) (B2 : nat) (x : nadd) (y : nadd) (A1 : nat) (B1 : nat) (h1 : term132 x y A1 B1) : (term188 A1 B1 y x A2 n B2) = (term187 y x A2 n B2).
Proof. exact (TRANS (@lem1278324 A2 n B2 x y A1 B1 h1) (@lem1278327 y x A2 n B2)). Qed.
Lemma lem1278329 (A2 : nat) (n : nat) (B2 : nat) (x : nadd) (y : nadd) (A1 : nat) (B1 : nat) (h1 : term132 x y A1 B1) : (term187 y x A2 n B2) = (term188 A1 B1 y x A2 n B2).
Proof. exact (SYM (@lem1278328 A2 n B2 x y A1 B1 h1)). Qed.
Lemma lem1278331 (n : nat) (m : nat) : (term6 m n) = (term6 n m).
Proof. exact (EQ_MP (@lem1277890 n m) (@lem1277889 m n)). Qed.
Lemma lem1278332 (x : nadd) (y : nadd) (n : nat) : (term183 y x n) = (term190 x y n).
Proof. exact (@lem1278331 (term180 y x n) (term191 x y n)). Qed.
Lemma lem1278333 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1278334 (x : nadd) (y : nadd) (n : nat) : (term192 y x n) = (term193 x y n).
Proof. exact (MK_COMB (@lem1278333) (@lem1278332 x y n)). Qed.
Lemma lem1278335 (A2 : nat) (n : nat) (B2 : nat) : (term148 A2 n B2) = (term148 A2 n B2).
Proof. exact (eq_refl (term148 A2 n B2)). Qed.
Lemma lem1278336 (x : nadd) (y : nadd) (A2 : nat) (n : nat) (B2 : nat) : (term187 y x A2 n B2) = (term194 x y A2 n B2).
Proof. exact (MK_COMB (@lem1278334 x y n) (@lem1278335 A2 n B2)). Qed.
Lemma lem1278337 (y : nadd) (x : nadd) (A2 : nat) (n : nat) (B2 : nat) : (term194 x y A2 n B2) = (term187 y x A2 n B2).
Proof. exact (SYM (@lem1278336 x y A2 n B2)). Qed.
Lemma lem1278339 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem1277884 n m) (@lem1277883 m n)). Qed.
Lemma lem1278340 (y : nadd) (x : nadd) (n : nat) : (term191 x y n) = (term191 y x n).
Proof. exact (@lem1278339 (dest_nadd y n) (dest_nadd x n)). Qed.
Lemma lem1278341 (y : nadd) (x : nadd) (n : nat) : (term195 y x n) = (term195 y x n).
Proof. exact (eq_refl (term195 y x n)). Qed.
Lemma lem1278342 (y : nadd) (x : nadd) (n : nat) : (term196 x y n) = (term197 y x n).
Proof. exact (MK_COMB (@lem1278341 y x n) (@lem1278340 y x n)). Qed.
Lemma lem1278343 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1278344 (y : nadd) (x : nadd) (n : nat) : (term190 x y n) = (term182 y x n).
Proof. exact (MK_COMB (@lem1278343) (@lem1278342 y x n)). Qed.
Lemma lem1278345 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1278346 (y : nadd) (x : nadd) (n : nat) : (term193 x y n) = (term198 y x n).
Proof. exact (MK_COMB (@lem1278345) (@lem1278344 y x n)). Qed.
Lemma lem1278347 (A2 : nat) (n : nat) (B2 : nat) : (term148 A2 n B2) = (term148 A2 n B2).
Proof. exact (eq_refl (term148 A2 n B2)). Qed.
Lemma lem1278348 (y : nadd) (x : nadd) (A2 : nat) (n : nat) (B2 : nat) : (term194 x y A2 n B2) = (term185 y x A2 n B2).
Proof. exact (MK_COMB (@lem1278346 y x n) (@lem1278347 A2 n B2)). Qed.
Lemma lem1278349 (x : nadd) (y : nadd) (A2 : nat) (n : nat) (B2 : nat) : (term185 y x A2 n B2) = (term194 x y A2 n B2).
Proof. exact (SYM (@lem1278348 y x A2 n B2)). Qed.
Lemma lem1278355 (n : nat) (y : nadd) (x : nadd) (A2 : nat) (B2 : nat) (h1 : term132 y x A2 B2) : term184 y x A2 B2 n.
Proof. exact (@lem1278194 y x A2 B2 h1 n). Qed.
Lemma lem1278356 (y : nadd) (x : nadd) (A2 : nat) (n : nat) (B2 : nat) : (term184 y x A2 B2 n) = (term185 y x A2 n B2).
Proof. exact (eq_refl (term184 y x A2 B2 n)). Qed.
Lemma lem1278357 (n : nat) (y : nadd) (x : nadd) (A2 : nat) (B2 : nat) (h1 : term132 y x A2 B2) : term185 y x A2 n B2.
Proof. exact (EQ_MP (@lem1278356 y x A2 n B2) (@lem1278355 n y x A2 B2 h1)). Qed.
Lemma lem1278358 (y : nadd) (x : nadd) (A2 : nat) (n : nat) (B2 : nat) : (term185 y x A2 n B2) = ((term185 y x A2 n B2) = True).
Proof. exact (@lem7 (term185 y x A2 n B2)). Qed.
Lemma lem1278361 (n : nat) (y : nadd) (x : nadd) (A2 : nat) (B2 : nat) (h1 : term132 y x A2 B2) : (term185 y x A2 n B2) = True.
Proof. exact (EQ_MP (@lem1278358 y x A2 n B2) (@lem1278357 n y x A2 B2 h1)). Qed.
Lemma lem1278362 (n : nat) (y : nadd) (x : nadd) (A2 : nat) (B2 : nat) (h1 : term132 y x A2 B2) : True = (term185 y x A2 n B2).
Proof. exact (SYM (@lem1278361 n y x A2 B2 h1)). Qed.
Lemma lem1278363 (n : nat) (y : nadd) (x : nadd) (A2 : nat) (B2 : nat) (h1 : term132 y x A2 B2) : term185 y x A2 n B2.
Proof. exact (EQ_MP (@lem1278362 n y x A2 B2 h1) (@lem0)). Qed.
Lemma lem1278364 (n : nat) (y : nadd) (x : nadd) (A2 : nat) (B2 : nat) (h1 : term132 y x A2 B2) : term194 x y A2 n B2.
Proof. exact (EQ_MP (@lem1278349 x y A2 n B2) (@lem1278363 n y x A2 B2 h1)). Qed.
Lemma lem1278365 (n : nat) (y : nadd) (x : nadd) (A2 : nat) (B2 : nat) (h1 : term132 y x A2 B2) : term187 y x A2 n B2.
Proof. exact (EQ_MP (@lem1278337 y x A2 n B2) (@lem1278364 n y x A2 B2 h1)). Qed.
Lemma lem1278366 (n : nat) (A1 : nat) (B1 : nat) (y : nadd) (x : nadd) (A2 : nat) (B2 : nat) (h1 : term132 x y A1 B1) (h2 : term132 y x A2 B2) : term188 A1 B1 y x A2 n B2.
Proof. exact (EQ_MP (@lem1278329 A2 n B2 x y A1 B1 h1) (@lem1278365 n y x A2 B2 h2)). Qed.
Lemma lem1278367 (n : nat) (A1 : nat) (B1 : nat) (y : nadd) (x : nadd) (A2 : nat) (B2 : nat) (h1 : term132 x y A1 B1) (h2 : term132 y x A2 B2) : term199 y x A1 B1 A2 n B2.
Proof. exact (@lem1278306 y x A1 B1 A2 n B2 (@lem1278366 n A1 B1 y x A2 B2 h1 h2)). Qed.
Lemma lem1278368 (n : nat) (A1 : nat) (B1 : nat) (y : nadd) (x : nadd) (A2 : nat) (B2 : nat) (h1 : term132 x y A1 B1) (h2 : term132 y x A2 B2) : term200 y x A1 B1 A2 n B2.
Proof. exact (ex_intro (term201 y x A1 B1 A2 n B2) (term191 x y n) (@lem1278367 n A1 B1 y x A2 B2 h1 h2)). Qed.
Lemma lem1278369 (n : nat) (A1 : nat) (B1 : nat) (y : nadd) (x : nadd) (A2 : nat) (B2 : nat) (h1 : term132 x y A1 B1) (h2 : term132 y x A2 B2) : term178 y x A1 B1 A2 n B2.
Proof. exact (@lem1278303 y x A1 B1 A2 n B2 (@lem1278368 n A1 B1 y x A2 B2 h1 h2)). Qed.
Lemma lem1278370 (n : nat) (A1 : nat) (B1 : nat) (y : nadd) (x : nadd) (A2 : nat) (B2 : nat) (h1 : term132 x y A1 B1) (h2 : term132 y x A2 B2) : term176 y x A1 A2 n B1 B2.
Proof. exact (EQ_MP (@lem1278300 y x A1 A2 n B1 B2) (@lem1278369 n A1 B1 y x A2 B2 h1 h2)). Qed.
Lemma lem1278371 (n : nat) (A1 : nat) (B1 : nat) (y : nadd) (x : nadd) (A2 : nat) (B2 : nat) (h1 : term132 x y A1 B1) (h2 : term132 y x A2 B2) : term175 y x A1 A2 n B1 B2.
Proof. exact (EQ_MP (@lem1278294 y x A1 A2 n B1 B2) (@lem1278370 n A1 B1 y x A2 B2 h1 h2)). Qed.
Lemma lem1278376 (A1 : nat) (B1 : nat) (y : nadd) (x : nadd) (A2 : nat) (B2 : nat) (h1 : term132 x y A1 B1) (h2 : term132 y x A2 B2) : term202 y x A1 A2 B1 B2.
Proof. exact (fun n : nat => @lem1278371 n A1 B1 y x A2 B2 h1 h2). Qed.
Lemma lem1278377 (A1 : nat) (B1 : nat) (y : nadd) (x : nadd) (A2 : nat) (B2 : nat) (h1 : term132 x y A1 B1) (h2 : term132 y x A2 B2) : term203 y x A1 A2.
Proof. exact (ex_intro (term204 y x A1 A2) (Nat.add B1 B2) (@lem1278376 A1 B1 y x A2 B2 h1 h2)). Qed.
Lemma lem1278378 (A1 : nat) (B1 : nat) (y : nadd) (x : nadd) (A2 : nat) (B2 : nat) (h1 : term132 x y A1 B1) (h2 : term132 y x A2 B2) : term170 y x.
Proof. exact (ex_intro (term169 y x) (Nat.add A1 A2) (@lem1278377 A1 B1 y x A2 B2 h1 h2)). Qed.
Lemma lem1278379 (A1 : nat) (B1 : nat) (y : nadd) (x : nadd) (A2 : nat) (B2 : nat) (h1 : term132 x y A1 B1) (h2 : term132 y x A2 B2) : term161 y x.
Proof. exact (EQ_MP (@lem1278284 y x) (@lem1278378 A1 B1 y x A2 B2 h1 h2)). Qed.
Lemma lem1278380 (A1 : nat) (B1 : nat) (y : nadd) (x : nadd) (A2 : nat) (B2 : nat) (h1 : term132 x y A1 B1) (h2 : term132 y x A2 B2) : term131 y x.
Proof. exact (EQ_MP (@lem1278243 y x) (@lem1278379 A1 B1 y x A2 B2 h1 h2)). Qed.
Lemma lem1278381 (A1 : nat) (B1 : nat) (y : nadd) (x : nadd) (A2 : nat) (h1 : term132 x y A1 B1) (h2 : term94 y x A2) : term131 y x.
Proof. exact (ex_elim (@lem1278193 y x A2 h2) (fun B2 : nat => fun h0 : term205 y x A2 B2 => @lem1278380 A1 B1 y x A2 B2 h1 h0)). Qed.
Lemma lem1278382 (A2 : nat) (x : nadd) (y : nadd) (A1 : nat) (B1 : nat) (h1 : term132 x y A1 B1) : term206 A2 y x.
Proof. exact (fun h0 : term94 y x A2 => @lem1278381 A1 B1 y x A2 h1 h0). Qed.
Lemma lem1278383 (A1 : nat) (B1 : nat) (y : nadd) (x : nadd) (A2 : nat) (h1 : term132 x y A1 B1) (h2 : term94 y x A2) : term131 y x.
Proof. exact (@lem1278382 A2 x y A1 B1 h1 (@lem1278098 y x A2 h2)). Qed.
Lemma lem1278384 (x : nadd) (y : nadd) (A1 : nat) (B1 : nat) (h1 : term132 x y A1 B1) : term131 y x.
Proof. exact (ex_elim (@lem1278097 y x) (fun A2 : nat => fun h0 : term207 y x A2 => @lem1278383 A1 B1 y x A2 h1 h0)). Qed.
Lemma lem1278385 (x : nadd) (y : nadd) (A1 : nat) (h1 : term94 x y A1) : term131 y x.
Proof. exact (ex_elim (@lem1278191 x y A1 h1) (fun B1 : nat => fun h0 : term205 x y A1 B1 => @lem1278384 x y A1 B1 h0)). Qed.
Lemma lem1278386 (A1 : nat) (y : nadd) (x : nadd) : term208 A1 y x.
Proof. exact (fun h0 : term94 x y A1 => @lem1278385 x y A1 h0). Qed.
Lemma lem1278387 (x : nadd) (y : nadd) (A1 : nat) (h1 : term94 x y A1) : term131 y x.
Proof. exact (@lem1278386 A1 y x (@lem1278105 x y A1 h1)). Qed.
Lemma lem1278388 (y : nadd) (x : nadd) : term131 y x.
Proof. exact (ex_elim (@lem1278104 x y) (fun A1 : nat => fun h0 : term207 x y A1 => @lem1278387 x y A1 h0)). Qed.
Lemma lem1278389 (y : nadd) (x : nadd) : term104 y x.
Proof. exact (EQ_MP (@lem1278190 y x) (@lem1278388 y x)). Qed.
Lemma lem1278394 (x : nadd) : term209 x.
Proof. exact (fun y : nadd => @lem1278389 y x). Qed.
Lemma lem1278399 : term210.
Proof. exact (fun x : nadd => @lem1278394 x). Qed.
