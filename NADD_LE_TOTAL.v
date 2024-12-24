Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_LE_TOTAL_term_abbrevs.
Require Import ADD_AC_spec.
Require Import AND_FORALL_THM_spec.
Require Import DE_MORGAN_THM_spec.
Require Import LEFT_ADD_DISTRIB_spec.
Require Import LEFT_AND_EXISTS_THM_spec.
Require Import LE_ADD2_spec.
Require Import LE_MULT_LCANCEL_spec.
Require Import LT_ADD2_spec.
Require Import MULT_SYM_spec.
Require Import NADD_CAUCHY_spec.
Require Import NADD_LE_TOTAL_LEMMA_spec.
Require Import NOT_DEF_spec.
Require Import NOT_LE_spec.
Require Import NOT_LT_spec.
Require Import REFL_CLAUSE_spec.
Require Import RIGHT_ADD_DISTRIB_spec.
Require Import RIGHT_AND_EXISTS_THM_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1247096_spec.
Require Import thm1823_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem1271825 (m : nat) : term0 m.
Proof. exact (@lem1247096 m). Qed.
Lemma lem1271826 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1271827 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1271826 m) (@lem1271825 m)). Qed.
Lemma lem1271828 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1271827 m n). Qed.
Lemma lem1271829 (n : nat) (m : nat) : (term2 m n) = (term3 n m).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1271830 (n : nat) (m : nat) : term3 n m.
Proof. exact (EQ_MP (@lem1271829 n m) (@lem1271828 m n)). Qed.
Lemma lem1271831 (n : nat) (m : nat) (p : nat) : term4 n m p.
Proof. exact (@lem1271830 n m p). Qed.
Lemma lem1271832 (n : nat) (m : nat) (p : nat) : (term4 n m p) = ((term5 m n p) = (term6 n m p)).
Proof. exact (eq_refl (term4 n m p)). Qed.
Lemma lem1271834 (m : nat) : term7 m.
Proof. exact (@lem81820 m). Qed.
Lemma lem1271835 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem1271836 (m : nat) : term8 m.
Proof. exact (EQ_MP (@lem1271835 m) (@lem1271834 m)). Qed.
Lemma lem1271837 (m : nat) (n : nat) : term9 m n.
Proof. exact (@lem1271836 m n). Qed.
Lemma lem1271838 (n : nat) (m : nat) : (term9 m n) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem1271843 (m : nat) (n : nat) (p : nat) (h1 : (term10 m n p) = (term11 m n p)) : (term10 m n p) = (term11 m n p).
Proof. exact (h1). Qed.
Lemma lem1271844 (m : nat) (n : nat) (p : nat) (h1 : (term10 m n p) = (term11 m n p)) : (term11 m n p) = (term10 m n p).
Proof. exact (SYM (@lem1271843 m n p h1)). Qed.
Lemma lem1271845 (m : nat) (n : nat) (p : nat) (h1 : (term11 m n p) = (term10 m n p)) : (term11 m n p) = (term10 m n p).
Proof. exact (h1). Qed.
Lemma lem1271846 (m : nat) (n : nat) (p : nat) (h1 : (term11 m n p) = (term10 m n p)) : (term10 m n p) = (term11 m n p).
Proof. exact (SYM (@lem1271845 m n p h1)). Qed.
Lemma lem1271847 (m : nat) (n : nat) (p : nat) : ((term10 m n p) = (term11 m n p)) = ((term11 m n p) = (term10 m n p)).
Proof. exact (prop_ext (fun h1 : (term10 m n p) = (term11 m n p) => @lem1271844 m n p h1) (fun h1 : (term11 m n p) = (term10 m n p) => @lem1271846 m n p h1)). Qed.
Lemma lem1271848 (m : nat) (n : nat) : (term12 m n) = (term13 m n).
Proof. exact (fun_ext (fun p : nat => @lem1271847 m n p)). Qed.
Lemma lem1271849 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1271850 (m : nat) (n : nat) : (term14 m n) = (term15 m n).
Proof. exact (MK_COMB (@lem1271849) (@lem1271848 m n)). Qed.
Lemma lem1271851 (m : nat) : (term16 m) = (term17 m).
Proof. exact (fun_ext (fun n : nat => @lem1271850 m n)). Qed.
Lemma lem1271852 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1271853 (m : nat) : (term18 m) = (term19 m).
Proof. exact (MK_COMB (@lem1271852) (@lem1271851 m)). Qed.
Lemma lem1271854 : term20 = term21.
Proof. exact (fun_ext (fun m : nat => @lem1271853 m)). Qed.
Lemma lem1271855 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1271856 : term22 = term23.
Proof. exact (MK_COMB (@lem1271855) (@lem1271854)). Qed.
Lemma lem1271857 : term23.
Proof. exact (EQ_MP (@lem1271856) (@lem82128)). Qed.
Lemma lem1271858 (m : nat) : term24 m.
Proof. exact (@lem1271857 m). Qed.
Lemma lem1271859 (m : nat) : (term24 m) = (term19 m).
Proof. exact (eq_refl (term24 m)). Qed.
Lemma lem1271860 (m : nat) : term19 m.
Proof. exact (EQ_MP (@lem1271859 m) (@lem1271858 m)). Qed.
Lemma lem1271861 (m : nat) (n : nat) : term25 m n.
Proof. exact (@lem1271860 m n). Qed.
Lemma lem1271862 (m : nat) (n : nat) : (term25 m n) = (term15 m n).
Proof. exact (eq_refl (term25 m n)). Qed.
Lemma lem1271863 (m : nat) (n : nat) : term15 m n.
Proof. exact (EQ_MP (@lem1271862 m n) (@lem1271861 m n)). Qed.
Lemma lem1271864 (m : nat) (n : nat) (p : nat) : term26 m n p.
Proof. exact (@lem1271863 m n p). Qed.
Lemma lem1271865 (m : nat) (n : nat) (p : nat) : (term26 m n p) = ((term11 m n p) = (term10 m n p)).
Proof. exact (eq_refl (term26 m n p)). Qed.
Lemma lem1271867 (h1 : term27) : term27.
Proof. exact (h1). Qed.
Lemma lem1271868 (m : nat) (h1 : term27) : term28 m.
Proof. exact (@lem1271867 h1 m). Qed.
Lemma lem1271869 (m : nat) : (term28 m) = (term29 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem1271870 (m : nat) (h1 : term27) : term29 m.
Proof. exact (EQ_MP (@lem1271869 m) (@lem1271868 m h1)). Qed.
Lemma lem1271871 (m : nat) (n : nat) (h1 : term27) : term30 m n.
Proof. exact (@lem1271870 m h1 n). Qed.
Lemma lem1271872 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (eq_refl (term30 m n)). Qed.
Lemma lem1271873 (m : nat) (n : nat) (h1 : term27) : term31 m n.
Proof. exact (EQ_MP (@lem1271872 m n) (@lem1271871 m n h1)). Qed.
Lemma lem1271874 (m : nat) (n : nat) (p : nat) (h1 : term27) : term32 m n p.
Proof. exact (@lem1271873 m n h1 p). Qed.
Lemma lem1271875 (m : nat) (n : nat) (p : nat) : (term32 m n p) = (term33 m n p).
Proof. exact (eq_refl (term32 m n p)). Qed.
Lemma lem1271876 (m : nat) (n : nat) (p : nat) (h1 : term27) : term33 m n p.
Proof. exact (EQ_MP (@lem1271875 m n p) (@lem1271874 m n p h1)). Qed.
Lemma lem1271877 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term27) : term34 m n p q.
Proof. exact (@lem1271876 m n p h1 q). Qed.
Lemma lem1271878 (m : nat) (n : nat) (p : nat) (q : nat) : (term34 m n p q) = (term35 m n p q).
Proof. exact (eq_refl (term34 m n p q)). Qed.
Lemma lem1271879 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term27) : term35 m n p q.
Proof. exact (EQ_MP (@lem1271878 m n p q) (@lem1271877 m n p q h1)). Qed.
Lemma lem1271880 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term36 m p n q) : term36 m p n q.
Proof. exact (h1). Qed.
Lemma lem1271881 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term27) (h2 : term36 m p n q) : term37 m n p q.
Proof. exact (@lem1271879 m n p q h1 (@lem1271880 m p n q h2)). Qed.
Lemma lem1271882 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term36 m p n q) : term38 m n p q.
Proof. exact (fun h0 : term27 => @lem1271881 m p n q h0 h1). Qed.
Lemma lem1271883 (h1 : term27) : term27.
Proof. exact (h1). Qed.
Lemma lem1271884 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term27) (h2 : term36 m p n q) : term37 m n p q.
Proof. exact (@lem1271882 m p n q h2 (@lem1271883 h1)). Qed.
Lemma lem1271885 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term27) : term35 m n p q.
Proof. exact (fun h0 : term36 m p n q => @lem1271884 m p n q h1 h0). Qed.
Lemma lem1271886 (m : nat) (n : nat) (p : nat) (h1 : term27) : term33 m n p.
Proof. exact (fun q : nat => @lem1271885 m n p q h1). Qed.
Lemma lem1271887 (m : nat) (n : nat) (h1 : term27) : term31 m n.
Proof. exact (fun p : nat => @lem1271886 m n p h1). Qed.
Lemma lem1271888 (m : nat) (h1 : term27) : term29 m.
Proof. exact (fun n : nat => @lem1271887 m n h1). Qed.
Lemma lem1271889 (h1 : term27) : term27.
Proof. exact (fun m : nat => @lem1271888 m h1). Qed.
Lemma lem1271890 : term39.
Proof. exact (fun h0 : term27 => @lem1271889 h0). Qed.
Lemma lem1271891 : term27.
Proof. exact (@lem1271890 (@lem101399)). Qed.
Lemma lem1271892 (m : nat) : term28 m.
Proof. exact (@lem1271891 m). Qed.
Lemma lem1271893 (m : nat) : (term28 m) = (term29 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem1271894 (m : nat) : term29 m.
Proof. exact (EQ_MP (@lem1271893 m) (@lem1271892 m)). Qed.
Lemma lem1271895 (m : nat) (n : nat) : term30 m n.
Proof. exact (@lem1271894 m n). Qed.
Lemma lem1271896 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (eq_refl (term30 m n)). Qed.
Lemma lem1271897 (m : nat) (n : nat) : term31 m n.
Proof. exact (EQ_MP (@lem1271896 m n) (@lem1271895 m n)). Qed.
Lemma lem1271898 (m : nat) (n : nat) (p : nat) : term32 m n p.
Proof. exact (@lem1271897 m n p). Qed.
Lemma lem1271899 (m : nat) (n : nat) (p : nat) : (term32 m n p) = (term33 m n p).
Proof. exact (eq_refl (term32 m n p)). Qed.
Lemma lem1271900 (m : nat) (n : nat) (p : nat) : term33 m n p.
Proof. exact (EQ_MP (@lem1271899 m n p) (@lem1271898 m n p)). Qed.
Lemma lem1271901 (m : nat) (n : nat) (p : nat) (q : nat) : term34 m n p q.
Proof. exact (@lem1271900 m n p q). Qed.
Lemma lem1271902 (m : nat) (n : nat) (p : nat) (q : nat) : (term34 m n p q) = (term35 m n p q).
Proof. exact (eq_refl (term34 m n p q)). Qed.
Lemma lem1271904 {A : Type'} (x : A) : term40 A x.
Proof. exact (@lem317 A x). Qed.
Lemma lem1271905 {A : Type'} (x : A) : (term40 A x) = ((x = x) = True).
Proof. exact (eq_refl (term40 A x)). Qed.
Lemma lem1271907 (n : nat) (m : nat) (p : nat) : term41 n m p.
Proof. exact (proj2 (@lem79120 n m p)). Qed.
Lemma lem1271914 (m : nat) (n : nat) (p : nat) : (term42 m n p) = (term43 m n p).
Proof. exact (proj1 (@lem1271907 n m p)). Qed.
Lemma lem1271915 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) (f : nat) : (term44 a b c d e f) = (term45 a b c d e f).
Proof. exact (@lem1271914 a (Nat.add b c) (term43 d e f)). Qed.
Lemma lem1271923 (m : nat) (n : nat) (p : nat) : (term42 m n p) = (term43 m n p).
Proof. exact (proj1 (@lem1271907 n m p)). Qed.
Lemma lem1271924 (b : nat) (c : nat) (d : nat) (e : nat) (f : nat) : (term46 b c d e f) = (term47 b c d e f).
Proof. exact (@lem1271923 b c (term43 d e f)). Qed.
Lemma lem1271946 (a : nat) : (Nat.add a) = (Nat.add a).
Proof. exact (eq_refl (Nat.add a)). Qed.
Lemma lem1271947 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) (f : nat) : (term45 a b c d e f) = (term48 a b c d e f).
Proof. exact (MK_COMB (@lem1271946 a) (@lem1271924 b c d e f)). Qed.
Lemma lem1271954 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) (f : nat) : (term44 a b c d e f) = (term48 a b c d e f).
Proof. exact (TRANS (@lem1271915 a b c d e f) (@lem1271947 a b c d e f)). Qed.
Lemma lem1271955 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1271956 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) (f : nat) : (term49 a b c d e f) = (term50 a b c d e f).
Proof. exact (MK_COMB (@lem1271955) (@lem1271954 a b c d e f)). Qed.
Lemma lem1271958 (m : nat) (n : nat) (p : nat) : (term42 m n p) = (term43 m n p).
Proof. exact (proj1 (@lem1271907 n m p)). Qed.
Lemma lem1271959 (d : nat) (b : nat) (e : nat) (a : nat) (c : nat) (f : nat) : (term44 d b e a c f) = (term45 d b e a c f).
Proof. exact (@lem1271958 d (Nat.add b e) (term43 a c f)). Qed.
Lemma lem1271967 (m : nat) (n : nat) (p : nat) : (term42 m n p) = (term43 m n p).
Proof. exact (proj1 (@lem1271907 n m p)). Qed.
Lemma lem1271968 (b : nat) (e : nat) (a : nat) (c : nat) (f : nat) : (term46 b e a c f) = (term47 b e a c f).
Proof. exact (@lem1271967 b e (term43 a c f)). Qed.
Lemma lem1271976 (n : nat) (m : nat) (p : nat) : (term43 m n p) = (term43 n m p).
Proof. exact (proj2 (@lem1271907 n m p)). Qed.
Lemma lem1271977 (a : nat) (e : nat) (c : nat) (f : nat) : (term51 e a c f) = (term51 a e c f).
Proof. exact (@lem1271976 a e (Nat.add c f)). Qed.
Lemma lem1271985 (n : nat) (m : nat) (p : nat) : (term43 m n p) = (term43 n m p).
Proof. exact (proj2 (@lem1271907 n m p)). Qed.
Lemma lem1271986 (c : nat) (e : nat) (f : nat) : (term43 e c f) = (term43 c e f).
Proof. exact (@lem1271985 c e f). Qed.
Lemma lem1271996 (a : nat) : (Nat.add a) = (Nat.add a).
Proof. exact (eq_refl (Nat.add a)). Qed.
Lemma lem1271997 (a : nat) (c : nat) (e : nat) (f : nat) : (term51 a e c f) = (term51 a c e f).
Proof. exact (MK_COMB (@lem1271996 a) (@lem1271986 c e f)). Qed.
Lemma lem1272004 (a : nat) (c : nat) (e : nat) (f : nat) : (term51 e a c f) = (term51 a c e f).
Proof. exact (TRANS (@lem1271977 a e c f) (@lem1271997 a c e f)). Qed.
Lemma lem1272005 (b : nat) : (Nat.add b) = (Nat.add b).
Proof. exact (eq_refl (Nat.add b)). Qed.
Lemma lem1272006 (b : nat) (a : nat) (c : nat) (e : nat) (f : nat) : (term47 b e a c f) = (term47 b a c e f).
Proof. exact (MK_COMB (@lem1272005 b) (@lem1272004 a c e f)). Qed.
Lemma lem1272008 (n : nat) (m : nat) (p : nat) : (term43 m n p) = (term43 n m p).
Proof. exact (proj2 (@lem1271907 n m p)). Qed.
Lemma lem1272009 (a : nat) (b : nat) (c : nat) (e : nat) (f : nat) : (term47 b a c e f) = (term47 a b c e f).
Proof. exact (@lem1272008 a b (term43 c e f)). Qed.
Lemma lem1272031 (a : nat) (b : nat) (c : nat) (e : nat) (f : nat) : (term47 b e a c f) = (term47 a b c e f).
Proof. exact (TRANS (@lem1272006 b a c e f) (@lem1272009 a b c e f)). Qed.
Lemma lem1272032 (a : nat) (b : nat) (c : nat) (e : nat) (f : nat) : (term46 b e a c f) = (term47 a b c e f).
Proof. exact (TRANS (@lem1271968 b e a c f) (@lem1272031 a b c e f)). Qed.
Lemma lem1272033 (d : nat) : (Nat.add d) = (Nat.add d).
Proof. exact (eq_refl (Nat.add d)). Qed.
Lemma lem1272034 (d : nat) (a : nat) (b : nat) (c : nat) (e : nat) (f : nat) : (term45 d b e a c f) = (term48 d a b c e f).
Proof. exact (MK_COMB (@lem1272033 d) (@lem1272032 a b c e f)). Qed.
Lemma lem1272036 (n : nat) (m : nat) (p : nat) : (term43 m n p) = (term43 n m p).
Proof. exact (proj2 (@lem1271907 n m p)). Qed.
Lemma lem1272037 (a : nat) (d : nat) (b : nat) (c : nat) (e : nat) (f : nat) : (term48 d a b c e f) = (term48 a d b c e f).
Proof. exact (@lem1272036 a d (term51 b c e f)). Qed.
Lemma lem1272045 (n : nat) (m : nat) (p : nat) : (term43 m n p) = (term43 n m p).
Proof. exact (proj2 (@lem1271907 n m p)). Qed.
Lemma lem1272046 (b : nat) (d : nat) (c : nat) (e : nat) (f : nat) : (term47 d b c e f) = (term47 b d c e f).
Proof. exact (@lem1272045 b d (term43 c e f)). Qed.
Lemma lem1272054 (n : nat) (m : nat) (p : nat) : (term43 m n p) = (term43 n m p).
Proof. exact (proj2 (@lem1271907 n m p)). Qed.
Lemma lem1272055 (c : nat) (d : nat) (e : nat) (f : nat) : (term51 d c e f) = (term51 c d e f).
Proof. exact (@lem1272054 c d (Nat.add e f)). Qed.
Lemma lem1272071 (b : nat) : (Nat.add b) = (Nat.add b).
Proof. exact (eq_refl (Nat.add b)). Qed.
Lemma lem1272072 (b : nat) (c : nat) (d : nat) (e : nat) (f : nat) : (term47 b d c e f) = (term47 b c d e f).
Proof. exact (MK_COMB (@lem1272071 b) (@lem1272055 c d e f)). Qed.
Lemma lem1272079 (b : nat) (c : nat) (d : nat) (e : nat) (f : nat) : (term47 d b c e f) = (term47 b c d e f).
Proof. exact (TRANS (@lem1272046 b d c e f) (@lem1272072 b c d e f)). Qed.
Lemma lem1272080 (a : nat) : (Nat.add a) = (Nat.add a).
Proof. exact (eq_refl (Nat.add a)). Qed.
Lemma lem1272081 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) (f : nat) : (term48 a d b c e f) = (term48 a b c d e f).
Proof. exact (MK_COMB (@lem1272080 a) (@lem1272079 b c d e f)). Qed.
Lemma lem1272088 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) (f : nat) : (term48 d a b c e f) = (term48 a b c d e f).
Proof. exact (TRANS (@lem1272037 a d b c e f) (@lem1272081 a b c d e f)). Qed.
Lemma lem1272089 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) (f : nat) : (term45 d b e a c f) = (term48 a b c d e f).
Proof. exact (TRANS (@lem1272034 d a b c e f) (@lem1272088 a b c d e f)). Qed.
Lemma lem1272090 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) (f : nat) : (term44 d b e a c f) = (term48 a b c d e f).
Proof. exact (TRANS (@lem1271959 d b e a c f) (@lem1272089 a b c d e f)). Qed.
Lemma lem1272091 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) (f : nat) : ((term44 a b c d e f) = (term44 d b e a c f)) = ((term48 a b c d e f) = (term48 a b c d e f)).
Proof. exact (MK_COMB (@lem1271956 a b c d e f) (@lem1272090 a b c d e f)). Qed.
Lemma lem1272093 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1271905 A x) (@lem1271904 A x)). Qed.
Lemma lem1272094 (x : nat) : (x = x) = True.
Proof. exact (@lem1272093 nat x). Qed.
Lemma lem1272095 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) (f : nat) : ((term48 a b c d e f) = (term48 a b c d e f)) = True.
Proof. exact (@lem1272094 (term48 a b c d e f)). Qed.
Lemma lem1272096 (d : nat) (b : nat) (e : nat) (a : nat) (c : nat) (f : nat) : ((term44 a b c d e f) = (term44 d b e a c f)) = True.
Proof. exact (TRANS (@lem1272091 a b c d e f) (@lem1272095 a b c d e f)). Qed.
Lemma lem1272097 (d : nat) (b : nat) (e : nat) (a : nat) (c : nat) (f : nat) : True = ((term44 a b c d e f) = (term44 d b e a c f)).
Proof. exact (SYM (@lem1272096 d b e a c f)). Qed.
Lemma lem1272099 (m : nat) : term52 m.
Proof. exact (@lem82055 m). Qed.
Lemma lem1272100 (m : nat) : (term52 m) = (term53 m).
Proof. exact (eq_refl (term52 m)). Qed.
Lemma lem1272101 (m : nat) : term53 m.
Proof. exact (EQ_MP (@lem1272100 m) (@lem1272099 m)). Qed.
Lemma lem1272102 (m : nat) (n : nat) : term54 m n.
Proof. exact (@lem1272101 m n). Qed.
Lemma lem1272103 (n : nat) (m : nat) : (term54 m n) = (term55 n m).
Proof. exact (eq_refl (term54 m n)). Qed.
Lemma lem1272104 (n : nat) (m : nat) : term55 n m.
Proof. exact (EQ_MP (@lem1272103 n m) (@lem1272102 m n)). Qed.
Lemma lem1272105 (n : nat) (m : nat) (p : nat) : term56 n m p.
Proof. exact (@lem1272104 n m p). Qed.
Lemma lem1272106 (n : nat) (m : nat) (p : nat) : (term56 n m p) = ((term57 m n p) = (term58 n m p)).
Proof. exact (eq_refl (term56 n m p)). Qed.
Lemma lem1272108 (m : nat) : term59 m.
Proof. exact (@lem98377 m). Qed.
Lemma lem1272109 (m : nat) : (term59 m) = (term60 m).
Proof. exact (eq_refl (term59 m)). Qed.
Lemma lem1272110 (m : nat) : term60 m.
Proof. exact (EQ_MP (@lem1272109 m) (@lem1272108 m)). Qed.
Lemma lem1272111 (m : nat) (n : nat) : term61 m n.
Proof. exact (@lem1272110 m n). Qed.
Lemma lem1272112 (n : nat) (m : nat) : (term61 m n) = ((term62 m n) = (Peano.le n m)).
Proof. exact (eq_refl (term61 m n)). Qed.
Lemma lem1272114 (m : nat) : term63 m.
Proof. exact (@lem101917 m). Qed.
Lemma lem1272115 (m : nat) : (term63 m) = (term64 m).
Proof. exact (eq_refl (term63 m)). Qed.
Lemma lem1272116 (m : nat) : term64 m.
Proof. exact (EQ_MP (@lem1272115 m) (@lem1272114 m)). Qed.
Lemma lem1272117 (m : nat) (n : nat) : term65 m n.
Proof. exact (@lem1272116 m n). Qed.
Lemma lem1272118 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (eq_refl (term65 m n)). Qed.
Lemma lem1272119 (m : nat) (n : nat) : term66 m n.
Proof. exact (EQ_MP (@lem1272118 m n) (@lem1272117 m n)). Qed.
Lemma lem1272120 (m : nat) (n : nat) (p : nat) : term67 m n p.
Proof. exact (@lem1272119 m n p). Qed.
Lemma lem1272121 (m : nat) (n : nat) (p : nat) : (term67 m n p) = (term68 m n p).
Proof. exact (eq_refl (term67 m n p)). Qed.
Lemma lem1272122 (m : nat) (n : nat) (p : nat) : term68 m n p.
Proof. exact (EQ_MP (@lem1272121 m n p) (@lem1272120 m n p)). Qed.
Lemma lem1272123 (m : nat) (n : nat) (p : nat) (q : nat) : term69 m n p q.
Proof. exact (@lem1272122 m n p q). Qed.
Lemma lem1272124 (m : nat) (n : nat) (p : nat) (q : nat) : (term69 m n p q) = (term70 m n p q).
Proof. exact (eq_refl (term69 m n p q)). Qed.
Lemma lem1272126 (m : nat) : term71 m.
Proof. exact (@lem97961 m). Qed.
Lemma lem1272127 (m : nat) : (term71 m) = (term72 m).
Proof. exact (eq_refl (term71 m)). Qed.
Lemma lem1272128 (m : nat) : term72 m.
Proof. exact (EQ_MP (@lem1272127 m) (@lem1272126 m)). Qed.
Lemma lem1272129 (m : nat) (n : nat) : term73 m n.
Proof. exact (@lem1272128 m n). Qed.
Lemma lem1272130 (n : nat) (m : nat) : (term73 m n) = ((term74 m n) = (Peano.lt n m)).
Proof. exact (eq_refl (term73 m n)). Qed.
Lemma lem1272135 (m : nat) (n : nat) (p : nat) (h1 : (term75 n m p) = (term76 m n p)) : (term75 n m p) = (term76 m n p).
Proof. exact (h1). Qed.
Lemma lem1272136 (m : nat) (n : nat) (p : nat) (h1 : (term75 n m p) = (term76 m n p)) : (term76 m n p) = (term75 n m p).
Proof. exact (SYM (@lem1272135 m n p h1)). Qed.
Lemma lem1272137 (n : nat) (m : nat) (p : nat) (h1 : (term76 m n p) = (term75 n m p)) : (term76 m n p) = (term75 n m p).
Proof. exact (h1). Qed.
Lemma lem1272138 (n : nat) (m : nat) (p : nat) (h1 : (term76 m n p) = (term75 n m p)) : (term75 n m p) = (term76 m n p).
Proof. exact (SYM (@lem1272137 n m p h1)). Qed.
Lemma lem1272139 (n : nat) (m : nat) (p : nat) : ((term75 n m p) = (term76 m n p)) = ((term76 m n p) = (term75 n m p)).
Proof. exact (prop_ext (fun h1 : (term75 n m p) = (term76 m n p) => @lem1272136 m n p h1) (fun h1 : (term76 m n p) = (term75 n m p) => @lem1272138 n m p h1)). Qed.
Lemma lem1272140 (n : nat) (m : nat) : (term77 m n) = (term78 n m).
Proof. exact (fun_ext (fun p : nat => @lem1272139 n m p)). Qed.
Lemma lem1272141 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1272142 (n : nat) (m : nat) : (term79 m n) = (term80 n m).
Proof. exact (MK_COMB (@lem1272141) (@lem1272140 n m)). Qed.
Lemma lem1272143 (m : nat) : (term81 m) = (term82 m).
Proof. exact (fun_ext (fun n : nat => @lem1272142 n m)). Qed.
Lemma lem1272144 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1272145 (m : nat) : (term83 m) = (term84 m).
Proof. exact (MK_COMB (@lem1272144) (@lem1272143 m)). Qed.
Lemma lem1272146 : term85 = term86.
Proof. exact (fun_ext (fun m : nat => @lem1272145 m)). Qed.
Lemma lem1272147 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1272148 : term87 = term88.
Proof. exact (MK_COMB (@lem1272147) (@lem1272146)). Qed.
Lemma lem1272149 : term88.
Proof. exact (EQ_MP (@lem1272148) (@lem104208)). Qed.
Lemma lem1272150 (m : nat) : term89 m.
Proof. exact (@lem1272149 m). Qed.
Lemma lem1272151 (m : nat) : (term89 m) = (term84 m).
Proof. exact (eq_refl (term89 m)). Qed.
Lemma lem1272152 (m : nat) : term84 m.
Proof. exact (EQ_MP (@lem1272151 m) (@lem1272150 m)). Qed.
Lemma lem1272153 (m : nat) (n : nat) : term90 m n.
Proof. exact (@lem1272152 m n). Qed.
Lemma lem1272154 (n : nat) (m : nat) : (term90 m n) = (term80 n m).
Proof. exact (eq_refl (term90 m n)). Qed.
Lemma lem1272155 (n : nat) (m : nat) : term80 n m.
Proof. exact (EQ_MP (@lem1272154 n m) (@lem1272153 m n)). Qed.
Lemma lem1272156 (n : nat) (m : nat) (p : nat) : term91 n m p.
Proof. exact (@lem1272155 n m p). Qed.
Lemma lem1272157 (n : nat) (m : nat) (p : nat) : (term91 n m p) = ((term76 m n p) = (term75 n m p)).
Proof. exact (eq_refl (term91 n m p)). Qed.
Lemma lem1272159 (m : nat) : term59 m.
Proof. exact (@lem98377 m). Qed.
Lemma lem1272160 (m : nat) : (term59 m) = (term60 m).
Proof. exact (eq_refl (term59 m)). Qed.
Lemma lem1272161 (m : nat) : term60 m.
Proof. exact (EQ_MP (@lem1272160 m) (@lem1272159 m)). Qed.
Lemma lem1272162 (m : nat) (n : nat) : term61 m n.
Proof. exact (@lem1272161 m n). Qed.
Lemma lem1272163 (n : nat) (m : nat) : (term61 m n) = ((term62 m n) = (Peano.le n m)).
Proof. exact (eq_refl (term61 m n)). Qed.
Lemma lem1272286 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (h1 : term92 a b c d) : term92 a b c d.
Proof. exact (h1). Qed.
Lemma lem1272287 (c : Prop) (b : Prop) (h1 : term93 c b) : term93 c b.
Proof. exact (h1). Qed.
Lemma lem1272288 (c : Prop) (h1 : c) : c.
Proof. exact (h1). Qed.
Lemma lem1272289 (b : Prop) (h1 : ~ b) : ~ b.
Proof. exact (h1). Qed.
Lemma lem1272290 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (h1 : term92 a b c d) : term94 c d.
Proof. exact (proj2 (@lem1272286 a b c d h1)). Qed.
Lemma lem1272293 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (h1 : term92 a b c d) : ~ c.
Proof. exact (proj1 (@lem1272290 a b c d h1)). Qed.
Lemma lem1272294 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem1272295 (c : Prop) : (~ c) = (term95 c).
Proof. exact (MK_COMB (@lem56) (@lem1272294 c)). Qed.
Lemma lem1272296 (c : Prop) : (term95 c) = (c -> False).
Proof. exact (eq_refl (term95 c)). Qed.
Lemma lem1272297 (c : Prop) : (term96 c) = (term96 c).
Proof. exact (eq_refl (term96 c)). Qed.
Lemma lem1272298 (c : Prop) : ((~ c) = (term95 c)) = ((~ c) = (c -> False)).
Proof. exact (MK_COMB (@lem1272297 c) (@lem1272296 c)). Qed.
Lemma lem1272299 (c : Prop) : (~ c) = (c -> False).
Proof. exact (EQ_MP (@lem1272298 c) (@lem1272295 c)). Qed.
Lemma lem1272300 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (h1 : term92 a b c d) : c -> False.
Proof. exact (EQ_MP (@lem1272299 c) (@lem1272293 a b c d h1)). Qed.
Lemma lem1272316 (c : Prop) (h1 : c) : c.
Proof. exact (h1). Qed.
Lemma lem1272317 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (h1 : c) (h2 : term92 a b c d) : False.
Proof. exact (@lem1272300 a b c d h2 (@lem1272316 c h1)). Qed.
Lemma lem1272318 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (h1 : c) (h2 : term92 a b c d) : c = False.
Proof. exact (prop_ext (fun h3 : c => @lem1272317 a b c d h1 h2) (fun h3 : False => @lem1272288 c h1)). Qed.
Lemma lem1272319 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (h1 : c) (h2 : term92 a b c d) : False.
Proof. exact (EQ_MP (@lem1272318 a b c d h1 h2) (@lem1272288 c h1)). Qed.
Lemma lem1272320 (b : Prop) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem1272321 (b : Prop) : (~ b) = (term95 b).
Proof. exact (MK_COMB (@lem56) (@lem1272320 b)). Qed.
Lemma lem1272322 (b : Prop) : (term95 b) = (b -> False).
Proof. exact (eq_refl (term95 b)). Qed.
Lemma lem1272323 (b : Prop) : (term96 b) = (term96 b).
Proof. exact (eq_refl (term96 b)). Qed.
Lemma lem1272324 (b : Prop) : ((~ b) = (term95 b)) = ((~ b) = (b -> False)).
Proof. exact (MK_COMB (@lem1272323 b) (@lem1272322 b)). Qed.
Lemma lem1272325 (b : Prop) : (~ b) = (b -> False).
Proof. exact (EQ_MP (@lem1272324 b) (@lem1272321 b)). Qed.
Lemma lem1272326 (b : Prop) (h1 : ~ b) : b -> False.
Proof. exact (EQ_MP (@lem1272325 b) (@lem1272289 b h1)). Qed.
Lemma lem1272328 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (h1 : term92 a b c d) : term94 a b.
Proof. exact (proj1 (@lem1272286 a b c d h1)). Qed.
Lemma lem1272338 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (h1 : term92 a b c d) : b.
Proof. exact (proj2 (@lem1272328 a b c d h1)). Qed.
Lemma lem1272363 (b : Prop) (h1 : b) : b.
Proof. exact (h1). Qed.
Lemma lem1272364 (b : Prop) (h1 : b) (h2 : ~ b) : False.
Proof. exact (@lem1272326 b h2 (@lem1272363 b h1)). Qed.
Lemma lem1272365 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (h1 : ~ b) (h2 : term92 a b c d) : b = False.
Proof. exact (prop_ext (fun h3 : b => @lem1272364 b h3 h1) (fun h3 : False => @lem1272338 a b c d h2)). Qed.
Lemma lem1272366 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (h1 : ~ b) (h2 : term92 a b c d) : False.
Proof. exact (EQ_MP (@lem1272365 a b c d h1 h2) (@lem1272338 a b c d h2)). Qed.
Lemma lem1272367 (a : Prop) (d : Prop) (c : Prop) (b : Prop) (h1 : term92 a b c d) (h2 : term93 c b) : False.
Proof. exact (or_elim (@lem1272287 c b h2) (fun h0 : c => @lem1272319 a b c d h0 h1) (fun h0 : ~ b => @lem1272366 a b c d h0 h1)). Qed.
Lemma lem1272368 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (h1 : term92 a b c d) : term97 c b.
Proof. exact (fun h0 : term93 c b => @lem1272367 a d c b h1 h0). Qed.
Lemma lem1272369 (c : Prop) (b : Prop) : (term97 c b) = (term98 c b).
Proof. exact (@lem69 (term93 c b)). Qed.
Lemma lem1272370 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (h1 : term92 a b c d) : term98 c b.
Proof. exact (EQ_MP (@lem1272369 c b) (@lem1272368 a b c d h1)). Qed.
Lemma lem1272371 (a : Prop) (d : Prop) (h1 : term93 a d) : term93 a d.
Proof. exact (h1). Qed.
Lemma lem1272372 (a : Prop) (h1 : a) : a.
Proof. exact (h1). Qed.
Lemma lem1272373 (d : Prop) (h1 : ~ d) : ~ d.
Proof. exact (h1). Qed.
Lemma lem1272375 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (h1 : term92 a b c d) : term94 a b.
Proof. exact (proj1 (@lem1272286 a b c d h1)). Qed.
Lemma lem1272386 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (h1 : term92 a b c d) : ~ a.
Proof. exact (proj1 (@lem1272375 a b c d h1)). Qed.
Lemma lem1272387 (a : Prop) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1272388 (a : Prop) : (~ a) = (term95 a).
Proof. exact (MK_COMB (@lem56) (@lem1272387 a)). Qed.
Lemma lem1272389 (a : Prop) : (term95 a) = (a -> False).
Proof. exact (eq_refl (term95 a)). Qed.
Lemma lem1272390 (a : Prop) : (term96 a) = (term96 a).
Proof. exact (eq_refl (term96 a)). Qed.
Lemma lem1272391 (a : Prop) : ((~ a) = (term95 a)) = ((~ a) = (a -> False)).
Proof. exact (MK_COMB (@lem1272390 a) (@lem1272389 a)). Qed.
Lemma lem1272392 (a : Prop) : (~ a) = (a -> False).
Proof. exact (EQ_MP (@lem1272391 a) (@lem1272388 a)). Qed.
Lemma lem1272393 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (h1 : term92 a b c d) : a -> False.
Proof. exact (EQ_MP (@lem1272392 a) (@lem1272386 a b c d h1)). Qed.
Lemma lem1272394 (a : Prop) (h1 : a) : a.
Proof. exact (h1). Qed.
Lemma lem1272395 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (h1 : a) (h2 : term92 a b c d) : False.
Proof. exact (@lem1272393 a b c d h2 (@lem1272394 a h1)). Qed.
Lemma lem1272396 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (h1 : a) (h2 : term92 a b c d) : a = False.
Proof. exact (prop_ext (fun h3 : a => @lem1272395 a b c d h1 h2) (fun h3 : False => @lem1272372 a h1)). Qed.
Lemma lem1272397 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (h1 : a) (h2 : term92 a b c d) : False.
Proof. exact (EQ_MP (@lem1272396 a b c d h1 h2) (@lem1272372 a h1)). Qed.
Lemma lem1272398 (d : Prop) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem1272399 (d : Prop) : (~ d) = (term95 d).
Proof. exact (MK_COMB (@lem56) (@lem1272398 d)). Qed.
Lemma lem1272400 (d : Prop) : (term95 d) = (d -> False).
Proof. exact (eq_refl (term95 d)). Qed.
Lemma lem1272401 (d : Prop) : (term96 d) = (term96 d).
Proof. exact (eq_refl (term96 d)). Qed.
Lemma lem1272402 (d : Prop) : ((~ d) = (term95 d)) = ((~ d) = (d -> False)).
Proof. exact (MK_COMB (@lem1272401 d) (@lem1272400 d)). Qed.
Lemma lem1272403 (d : Prop) : (~ d) = (d -> False).
Proof. exact (EQ_MP (@lem1272402 d) (@lem1272399 d)). Qed.
Lemma lem1272404 (d : Prop) (h1 : ~ d) : d -> False.
Proof. exact (EQ_MP (@lem1272403 d) (@lem1272373 d h1)). Qed.
Lemma lem1272405 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (h1 : term92 a b c d) : term94 c d.
Proof. exact (proj2 (@lem1272286 a b c d h1)). Qed.
Lemma lem1272407 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (h1 : term92 a b c d) : d.
Proof. exact (proj2 (@lem1272405 a b c d h1)). Qed.
Lemma lem1272441 (d : Prop) (h1 : d) : d.
Proof. exact (h1). Qed.
Lemma lem1272442 (d : Prop) (h1 : d) (h2 : ~ d) : False.
Proof. exact (@lem1272404 d h2 (@lem1272441 d h1)). Qed.
Lemma lem1272443 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (h1 : ~ d) (h2 : term92 a b c d) : d = False.
Proof. exact (prop_ext (fun h3 : d => @lem1272442 d h3 h1) (fun h3 : False => @lem1272407 a b c d h2)). Qed.
Lemma lem1272444 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (h1 : ~ d) (h2 : term92 a b c d) : False.
Proof. exact (EQ_MP (@lem1272443 a b c d h1 h2) (@lem1272407 a b c d h2)). Qed.
Lemma lem1272445 (b : Prop) (c : Prop) (a : Prop) (d : Prop) (h1 : term92 a b c d) (h2 : term93 a d) : False.
Proof. exact (or_elim (@lem1272371 a d h2) (fun h0 : a => @lem1272397 a b c d h0 h1) (fun h0 : ~ d => @lem1272444 a b c d h0 h1)). Qed.
Lemma lem1272446 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (h1 : term92 a b c d) : term97 a d.
Proof. exact (fun h0 : term93 a d => @lem1272445 b c a d h1 h0). Qed.
Lemma lem1272447 (a : Prop) (d : Prop) : (term97 a d) = (term98 a d).
Proof. exact (@lem69 (term93 a d)). Qed.
Lemma lem1272448 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (h1 : term92 a b c d) : term98 a d.
Proof. exact (EQ_MP (@lem1272447 a d) (@lem1272446 a b c d h1)). Qed.
Lemma lem1272449 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (h1 : term92 a b c d) : term99 c b a d.
Proof. exact (conj (@lem1272370 a b c d h1) (@lem1272448 a b c d h1)). Qed.
Lemma lem1272451 {A : Type'} (P : A -> Prop) : term100 A P.
Proof. exact (@lem5881 A P). Qed.
Lemma lem1272452 {A : Type'} (P : A -> Prop) : (term100 A P) = (term101 A P).
Proof. exact (eq_refl (term100 A P)). Qed.
Lemma lem1272453 {A : Type'} (P : A -> Prop) : term101 A P.
Proof. exact (EQ_MP (@lem1272452 A P) (@lem1272451 A P)). Qed.
Lemma lem1272454 {A : Type'} (P : A -> Prop) (Q : Prop) : term102 A P Q.
Proof. exact (@lem1272453 A P Q). Qed.
Lemma lem1272455 {A : Type'} (P : A -> Prop) (Q : Prop) : (term102 A P Q) = ((term103 A P Q) = (term104 A P Q)).
Proof. exact (eq_refl (term102 A P Q)). Qed.
Lemma lem1272457 {A : Type'} (P : Prop) : term105 A P.
Proof. exact (@lem5950 A P). Qed.
Lemma lem1272458 {A : Type'} (P : Prop) : (term105 A P) = (term106 A P).
Proof. exact (eq_refl (term105 A P)). Qed.
Lemma lem1272459 {A : Type'} (P : Prop) : term106 A P.
Proof. exact (EQ_MP (@lem1272458 A P) (@lem1272457 A P)). Qed.
Lemma lem1272460 {A : Type'} (P : Prop) (Q : A -> Prop) : term107 A P Q.
Proof. exact (@lem1272459 A P Q). Qed.
Lemma lem1272461 {A : Type'} (P : Prop) (Q : A -> Prop) : (term107 A P Q) = ((term108 A P Q) = (term109 A P Q)).
Proof. exact (eq_refl (term107 A P Q)). Qed.
Lemma lem1272463 {A : Type'} (P : A -> Prop) : term110 A P.
Proof. exact (@lem5146 A P). Qed.
Lemma lem1272464 {A : Type'} (P : A -> Prop) : (term110 A P) = (term111 A P).
Proof. exact (eq_refl (term110 A P)). Qed.
Lemma lem1272465 {A : Type'} (P : A -> Prop) : term111 A P.
Proof. exact (EQ_MP (@lem1272464 A P) (@lem1272463 A P)). Qed.
Lemma lem1272466 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term112 A P Q.
Proof. exact (@lem1272465 A P Q). Qed.
Lemma lem1272467 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term112 A P Q) = ((term113 A P Q) = (term114 A P Q)).
Proof. exact (eq_refl (term112 A P Q)). Qed.
Lemma lem1272469 (x : nadd) : term115 x.
Proof. exact (@lem1271824 x). Qed.
Lemma lem1272470 (x : nadd) : (term115 x) = (term116 x).
Proof. exact (eq_refl (term115 x)). Qed.
Lemma lem1272471 (x : nadd) : term116 x.
Proof. exact (EQ_MP (@lem1272470 x) (@lem1272469 x)). Qed.
Lemma lem1272472 (x : nadd) (y : nadd) : term117 x y.
Proof. exact (@lem1272471 x y). Qed.
Lemma lem1272473 (y : nadd) (x : nadd) : (term117 x y) = (term118 y x).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1272475 (t1 : Prop) : term119 t1.
Proof. exact (@lem10089 t1). Qed.
Lemma lem1272476 (t1 : Prop) : (term119 t1) = (term120 t1).
Proof. exact (eq_refl (term119 t1)). Qed.
Lemma lem1272477 (t1 : Prop) : term120 t1.
Proof. exact (EQ_MP (@lem1272476 t1) (@lem1272475 t1)). Qed.
Lemma lem1272478 (t1 : Prop) (t2 : Prop) : term121 t1 t2.
Proof. exact (@lem1272477 t1 t2). Qed.
Lemma lem1272479 (t1 : Prop) (t2 : Prop) : (term121 t1 t2) = (term122 t1 t2).
Proof. exact (eq_refl (term121 t1 t2)). Qed.
Lemma lem1272480 (t1 : Prop) (t2 : Prop) : term122 t1 t2.
Proof. exact (EQ_MP (@lem1272479 t1 t2) (@lem1272478 t1 t2)). Qed.
Lemma lem1272483 (y : nadd) : term123 y.
Proof. exact (@lem1262851 y). Qed.
Lemma lem1272484 (y : nadd) : (term123 y) = (term124 y).
Proof. exact (eq_refl (term123 y)). Qed.
Lemma lem1272485 (y : nadd) : term124 y.
Proof. exact (EQ_MP (@lem1272484 y) (@lem1272483 y)). Qed.
Lemma lem1272486 (y : nadd) (B2 : nat) (h1 : term125 y B2) : term125 y B2.
Proof. exact (h1). Qed.
Lemma lem1272487 (x : nadd) : term123 x.
Proof. exact (@lem1262851 x). Qed.
Lemma lem1272488 (x : nadd) : (term123 x) = (term124 x).
Proof. exact (eq_refl (term123 x)). Qed.
Lemma lem1272489 (x : nadd) : term124 x.
Proof. exact (EQ_MP (@lem1272488 x) (@lem1272487 x)). Qed.
Lemma lem1272490 (x : nadd) (B1 : nat) (h1 : term125 x B1) : term125 x B1.
Proof. exact (h1). Qed.
Lemma lem1272494 (t : Prop) : (term126 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem1272495 (a : Prop) : (term126 a) = a.
Proof. exact (@lem1272494 a). Qed.
Lemma lem1272496 (a : Prop) : (@eq Prop a) = (@eq Prop a).
Proof. exact (eq_refl (@eq Prop a)). Qed.
Lemma lem1272497 (a : Prop) : (a = (term126 a)) = (a = a).
Proof. exact (MK_COMB (@lem1272496 a) (@lem1272495 a)). Qed.
Lemma lem1272499 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1272500 (x : Prop) : (x = x) = True.
Proof. exact (@lem1272499 Prop x). Qed.
Lemma lem1272501 (a : Prop) : (a = a) = True.
Proof. exact (@lem1272500 a). Qed.
Lemma lem1272502 (a : Prop) : (a = (term126 a)) = True.
Proof. exact (TRANS (@lem1272497 a) (@lem1272501 a)). Qed.
Lemma lem1272503 (a : Prop) : True = (a = (term126 a)).
Proof. exact (SYM (@lem1272502 a)). Qed.
Lemma lem1272506 (a : Prop) : a = (term126 a).
Proof. exact (EQ_MP (@lem1272503 a) (@lem0)). Qed.
Lemma lem1272507 (y : nadd) (x : nadd) : (term127 y x) = (term128 y x).
Proof. exact (@lem1272506 (term127 y x)). Qed.
Lemma lem1272508 (y : nadd) (x : nadd) : (term128 y x) = (term127 y x).
Proof. exact (SYM (@lem1272507 y x)). Qed.
Lemma lem1272510 (t1 : Prop) (t2 : Prop) : (term129 t1 t2) = (term130 t1 t2).
Proof. exact (proj2 (@lem1272480 t1 t2)). Qed.
Lemma lem1272511 (y : nadd) (x : nadd) : (term131 y x) = (term132 y x).
Proof. exact (@lem1272510 (nadd_le x y) (nadd_le y x)). Qed.
Lemma lem1272512 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1272513 (y : nadd) (x : nadd) : (term128 y x) = (term133 y x).
Proof. exact (MK_COMB (@lem1272512) (@lem1272511 y x)). Qed.
Lemma lem1272514 (y : nadd) (x : nadd) : (term133 y x) = (term128 y x).
Proof. exact (SYM (@lem1272513 y x)). Qed.
Lemma lem1272515 (y : nadd) (x : nadd) (h1 : term132 y x) : term132 y x.
Proof. exact (h1). Qed.
Lemma lem1272516 (y : nadd) (x : nadd) (h1 : term132 y x) : term134 y x.
Proof. exact (proj2 (@lem1272515 y x h1)). Qed.
Lemma lem1272517 (y : nadd) (x : nadd) (h1 : term132 y x) : term134 x y.
Proof. exact (proj1 (@lem1272515 y x h1)). Qed.
Lemma lem1272519 (y : nadd) (x : nadd) : term118 y x.
Proof. exact (EQ_MP (@lem1272473 y x) (@lem1272472 x y)). Qed.
Lemma lem1272520 (y : nadd) (x : nadd) (h1 : term132 y x) : term135 y x.
Proof. exact (@lem1272519 y x (@lem1272517 y x h1)). Qed.
Lemma lem1272522 (y : nadd) (x : nadd) : term118 y x.
Proof. exact (EQ_MP (@lem1272473 y x) (@lem1272472 x y)). Qed.
Lemma lem1272523 (x : nadd) (y : nadd) : term118 x y.
Proof. exact (@lem1272522 x y). Qed.
Lemma lem1272524 (y : nadd) (x : nadd) (h1 : term132 y x) : term135 x y.
Proof. exact (@lem1272523 x y (@lem1272516 y x h1)). Qed.
Lemma lem1272525 (y : nadd) (x : nadd) (h1 : term132 y x) : term136 x y.
Proof. exact (conj (@lem1272520 y x h1) (@lem1272524 y x h1)). Qed.
Lemma lem1272527 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1272528 (x : nadd) (y : nadd) : (term137 x y) = (term138 x y).
Proof. exact (@lem1272527 (term136 x y)). Qed.
Lemma lem1272530 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term113 A P Q) = (term114 A P Q).
Proof. exact (EQ_MP (@lem1272467 A P Q) (@lem1272466 A P Q)). Qed.
Lemma lem1272531 (P : nat -> Prop) (Q : nat -> Prop) : (term139 P Q) = (term140 P Q).
Proof. exact (@lem1272530 nat P Q). Qed.
Lemma lem1272532 (x : nadd) (y : nadd) : (term141 x y) = (term142 x y).
Proof. exact (@lem1272531 (term143 y x) (term143 x y)). Qed.
Lemma lem1272533 (y : nadd) (B : nat) (x : nadd) : (term144 y x B) = (term145 y B x).
Proof. exact (eq_refl (term144 y x B)). Qed.
Lemma lem1272534 (y : nadd) (x : nadd) : (term146 y x) = (term143 y x).
Proof. exact (fun_ext (fun B : nat => @lem1272533 y B x)). Qed.
Lemma lem1272535 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1272536 (y : nadd) (x : nadd) : (term147 y x) = (term135 y x).
Proof. exact (MK_COMB (@lem1272535) (@lem1272534 y x)). Qed.
Lemma lem1272537 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1272538 (y : nadd) (x : nadd) : (term148 y x) = (term149 y x).
Proof. exact (MK_COMB (@lem1272537) (@lem1272536 y x)). Qed.
Lemma lem1272539 (x : nadd) (B : nat) (y : nadd) : (term144 x y B) = (term145 x B y).
Proof. exact (eq_refl (term144 x y B)). Qed.
Lemma lem1272540 (x : nadd) (y : nadd) : (term146 x y) = (term143 x y).
Proof. exact (fun_ext (fun B : nat => @lem1272539 x B y)). Qed.
Lemma lem1272541 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1272542 (x : nadd) (y : nadd) : (term147 x y) = (term135 x y).
Proof. exact (MK_COMB (@lem1272541) (@lem1272540 x y)). Qed.
Lemma lem1272543 (x : nadd) (y : nadd) : (term141 x y) = (term136 x y).
Proof. exact (MK_COMB (@lem1272538 y x) (@lem1272542 x y)). Qed.
Lemma lem1272544 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1272545 (x : nadd) (y : nadd) : (term150 x y) = (term151 x y).
Proof. exact (MK_COMB (@lem1272544) (@lem1272543 x y)). Qed.
Lemma lem1272546 (y : nadd) (B : nat) (x : nadd) : (term144 y x B) = (term145 y B x).
Proof. exact (eq_refl (term144 y x B)). Qed.
Lemma lem1272547 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1272548 (y : nadd) (B : nat) (x : nadd) : (term152 y x B) = (term153 y B x).
Proof. exact (MK_COMB (@lem1272547) (@lem1272546 y B x)). Qed.
Lemma lem1272549 (x : nadd) (B : nat) (y : nadd) : (term144 x y B) = (term145 x B y).
Proof. exact (eq_refl (term144 x y B)). Qed.
Lemma lem1272550 (x : nadd) (B : nat) (y : nadd) : (term154 x y B) = (term155 x B y).
Proof. exact (MK_COMB (@lem1272548 y B x) (@lem1272549 x B y)). Qed.
Lemma lem1272551 (x : nadd) (y : nadd) : (term156 x y) = (term157 x y).
Proof. exact (fun_ext (fun B : nat => @lem1272550 x B y)). Qed.
Lemma lem1272552 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1272553 (x : nadd) (y : nadd) : (term142 x y) = (term158 x y).
Proof. exact (MK_COMB (@lem1272552) (@lem1272551 x y)). Qed.
Lemma lem1272554 (x : nadd) (y : nadd) : ((term141 x y) = (term142 x y)) = ((term136 x y) = (term158 x y)).
Proof. exact (MK_COMB (@lem1272545 x y) (@lem1272553 x y)). Qed.
Lemma lem1272555 (x : nadd) (y : nadd) : (term136 x y) = (term158 x y).
Proof. exact (EQ_MP (@lem1272554 x y) (@lem1272532 x y)). Qed.
Lemma lem1272578 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1272579 (x : nadd) (y : nadd) : (term138 x y) = (term159 x y).
Proof. exact (MK_COMB (@lem1272578) (@lem1272555 x y)). Qed.
Lemma lem1272580 (x : nadd) (y : nadd) : (term137 x y) = (term159 x y).
Proof. exact (TRANS (@lem1272528 x y) (@lem1272579 x y)). Qed.
Lemma lem1272581 (x : nadd) (y : nadd) : (term159 x y) = (term137 x y).
Proof. exact (SYM (@lem1272580 x y)). Qed.
Lemma lem1272582 (x : nadd) (y : nadd) (h1 : term158 x y) : term158 x y.
Proof. exact (h1). Qed.
Lemma lem1272583 (B1 : nat) (B2 : nat) (x : nadd) (y : nadd) (h1 : term158 x y) : term160 x y B1 B2.
Proof. exact (@lem1272582 x y h1 (Nat.add B1 B2)). Qed.
Lemma lem1272584 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) : (term160 x y B1 B2) = (term161 x B1 B2 y).
Proof. exact (eq_refl (term160 x y B1 B2)). Qed.
Lemma lem1272585 (B1 : nat) (B2 : nat) (x : nadd) (y : nadd) (h1 : term158 x y) : term161 x B1 B2 y.
Proof. exact (EQ_MP (@lem1272584 x B1 B2 y) (@lem1272583 B1 B2 x y h1)). Qed.
Lemma lem1272587 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1272588 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) : (term162 x B1 B2 y) = (term163 x B1 B2 y).
Proof. exact (@lem1272587 (term161 x B1 B2 y)). Qed.
Lemma lem1272590 {A : Type'} (P : Prop) (Q : A -> Prop) : (term108 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem1272461 A P Q) (@lem1272460 A P Q)). Qed.
Lemma lem1272591 (P : Prop) (Q : nat -> Prop) : (term164 P Q) = (term165 P Q).
Proof. exact (@lem1272590 nat P Q). Qed.
Lemma lem1272592 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) : (term166 x B1 B2 y) = (term167 x B1 B2 y).
Proof. exact (@lem1272591 (term168 y B1 B2 x) (term169 x B1 B2 y)). Qed.
Lemma lem1272593 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) (n : nat) : (term170 x B1 B2 y n) = (term171 x B1 B2 y n).
Proof. exact (eq_refl (term170 x B1 B2 y n)). Qed.
Lemma lem1272594 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) : (term172 x B1 B2 y) = (term169 x B1 B2 y).
Proof. exact (fun_ext (fun n : nat => @lem1272593 x B1 B2 y n)). Qed.
Lemma lem1272595 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1272596 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) : (term173 x B1 B2 y) = (term168 x B1 B2 y).
Proof. exact (MK_COMB (@lem1272595) (@lem1272594 x B1 B2 y)). Qed.
Lemma lem1272597 (y : nadd) (B1 : nat) (B2 : nat) (x : nadd) : (term174 y B1 B2 x) = (term174 y B1 B2 x).
Proof. exact (eq_refl (term174 y B1 B2 x)). Qed.
Lemma lem1272598 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) : (term166 x B1 B2 y) = (term161 x B1 B2 y).
Proof. exact (MK_COMB (@lem1272597 y B1 B2 x) (@lem1272596 x B1 B2 y)). Qed.
Lemma lem1272599 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1272600 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) : (term175 x B1 B2 y) = (term176 x B1 B2 y).
Proof. exact (MK_COMB (@lem1272599) (@lem1272598 x B1 B2 y)). Qed.
Lemma lem1272601 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) (n : nat) : (term170 x B1 B2 y n) = (term171 x B1 B2 y n).
Proof. exact (eq_refl (term170 x B1 B2 y n)). Qed.
Lemma lem1272602 (y : nadd) (B1 : nat) (B2 : nat) (x : nadd) : (term174 y B1 B2 x) = (term174 y B1 B2 x).
Proof. exact (eq_refl (term174 y B1 B2 x)). Qed.
Lemma lem1272603 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) (n : nat) : (term177 x B1 B2 y n) = (term178 x B1 B2 y n).
Proof. exact (MK_COMB (@lem1272602 y B1 B2 x) (@lem1272601 x B1 B2 y n)). Qed.
Lemma lem1272604 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) : (term179 x B1 B2 y) = (term180 x B1 B2 y).
Proof. exact (fun_ext (fun n : nat => @lem1272603 x B1 B2 y n)). Qed.
Lemma lem1272605 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1272606 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) : (term167 x B1 B2 y) = (term181 x B1 B2 y).
Proof. exact (MK_COMB (@lem1272605) (@lem1272604 x B1 B2 y)). Qed.
Lemma lem1272607 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) : ((term166 x B1 B2 y) = (term167 x B1 B2 y)) = ((term161 x B1 B2 y) = (term181 x B1 B2 y)).
Proof. exact (MK_COMB (@lem1272600 x B1 B2 y) (@lem1272606 x B1 B2 y)). Qed.
Lemma lem1272608 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) : (term161 x B1 B2 y) = (term181 x B1 B2 y).
Proof. exact (EQ_MP (@lem1272607 x B1 B2 y) (@lem1272592 x B1 B2 y)). Qed.
Lemma lem1272627 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1272628 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) : (term163 x B1 B2 y) = (term182 x B1 B2 y).
Proof. exact (MK_COMB (@lem1272627) (@lem1272608 x B1 B2 y)). Qed.
Lemma lem1272629 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) : (term162 x B1 B2 y) = (term182 x B1 B2 y).
Proof. exact (TRANS (@lem1272588 x B1 B2 y) (@lem1272628 x B1 B2 y)). Qed.
Lemma lem1272630 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) : (term182 x B1 B2 y) = (term162 x B1 B2 y).
Proof. exact (SYM (@lem1272629 x B1 B2 y)). Qed.
Lemma lem1272636 {A : Type'} (P : A -> Prop) (Q : Prop) : (term103 A P Q) = (term104 A P Q).
Proof. exact (EQ_MP (@lem1272455 A P Q) (@lem1272454 A P Q)). Qed.
Lemma lem1272637 (P : nat -> Prop) (Q : Prop) : (term183 P Q) = (term184 P Q).
Proof. exact (@lem1272636 nat P Q). Qed.
Lemma lem1272638 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) (n : nat) : (term185 x B1 B2 y n) = (term186 x B1 B2 y n).
Proof. exact (@lem1272637 (term169 y B1 B2 x) (term171 x B1 B2 y n)). Qed.
Lemma lem1272639 (y : nadd) (B1 : nat) (B2 : nat) (x : nadd) (n : nat) : (term170 y B1 B2 x n) = (term171 y B1 B2 x n).
Proof. exact (eq_refl (term170 y B1 B2 x n)). Qed.
Lemma lem1272640 (y : nadd) (B1 : nat) (B2 : nat) (x : nadd) : (term172 y B1 B2 x) = (term169 y B1 B2 x).
Proof. exact (fun_ext (fun n : nat => @lem1272639 y B1 B2 x n)). Qed.
Lemma lem1272641 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1272642 (y : nadd) (B1 : nat) (B2 : nat) (x : nadd) : (term173 y B1 B2 x) = (term168 y B1 B2 x).
Proof. exact (MK_COMB (@lem1272641) (@lem1272640 y B1 B2 x)). Qed.
Lemma lem1272643 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1272644 (y : nadd) (B1 : nat) (B2 : nat) (x : nadd) : (term187 y B1 B2 x) = (term174 y B1 B2 x).
Proof. exact (MK_COMB (@lem1272643) (@lem1272642 y B1 B2 x)). Qed.
Lemma lem1272645 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) (n : nat) : (term171 x B1 B2 y n) = (term171 x B1 B2 y n).
Proof. exact (eq_refl (term171 x B1 B2 y n)). Qed.
Lemma lem1272646 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) (n : nat) : (term185 x B1 B2 y n) = (term178 x B1 B2 y n).
Proof. exact (MK_COMB (@lem1272644 y B1 B2 x) (@lem1272645 x B1 B2 y n)). Qed.
Lemma lem1272647 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1272648 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) (n : nat) : (term188 x B1 B2 y n) = (term189 x B1 B2 y n).
Proof. exact (MK_COMB (@lem1272647) (@lem1272646 x B1 B2 y n)). Qed.
Lemma lem1272649 (y : nadd) (B1 : nat) (B2 : nat) (x : nadd) (n' : nat) : (term170 y B1 B2 x n') = (term171 y B1 B2 x n').
Proof. exact (eq_refl (term170 y B1 B2 x n')). Qed.
Lemma lem1272650 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1272651 (y : nadd) (B1 : nat) (B2 : nat) (x : nadd) (n' : nat) : (term190 y B1 B2 x n') = (term191 y B1 B2 x n').
Proof. exact (MK_COMB (@lem1272650) (@lem1272649 y B1 B2 x n')). Qed.
Lemma lem1272652 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) (n : nat) : (term171 x B1 B2 y n) = (term171 x B1 B2 y n).
Proof. exact (eq_refl (term171 x B1 B2 y n)). Qed.
Lemma lem1272653 (n' : nat) (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) (n : nat) : (term192 n' x B1 B2 y n) = (term193 n' x B1 B2 y n).
Proof. exact (MK_COMB (@lem1272651 y B1 B2 x n') (@lem1272652 x B1 B2 y n)). Qed.
Lemma lem1272654 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) (n : nat) : (term194 x B1 B2 y n) = (term195 x B1 B2 y n).
Proof. exact (fun_ext (fun n' : nat => @lem1272653 n' x B1 B2 y n)). Qed.
Lemma lem1272655 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1272656 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) (n : nat) : (term186 x B1 B2 y n) = (term196 x B1 B2 y n).
Proof. exact (MK_COMB (@lem1272655) (@lem1272654 x B1 B2 y n)). Qed.
Lemma lem1272657 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) (n : nat) : ((term185 x B1 B2 y n) = (term186 x B1 B2 y n)) = ((term178 x B1 B2 y n) = (term196 x B1 B2 y n)).
Proof. exact (MK_COMB (@lem1272648 x B1 B2 y n) (@lem1272656 x B1 B2 y n)). Qed.
Lemma lem1272658 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) (n : nat) : (term178 x B1 B2 y n) = (term196 x B1 B2 y n).
Proof. exact (EQ_MP (@lem1272657 x B1 B2 y n) (@lem1272638 x B1 B2 y n)). Qed.
Lemma lem1272673 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) : (term180 x B1 B2 y) = (term197 x B1 B2 y).
Proof. exact (fun_ext (fun n : nat => @lem1272658 x B1 B2 y n)). Qed.
Lemma lem1272674 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1272675 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) : (term181 x B1 B2 y) = (term198 x B1 B2 y).
Proof. exact (MK_COMB (@lem1272674) (@lem1272673 x B1 B2 y)). Qed.
Lemma lem1272680 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1272681 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) : (term182 x B1 B2 y) = (term199 x B1 B2 y).
Proof. exact (MK_COMB (@lem1272680) (@lem1272675 x B1 B2 y)). Qed.
Lemma lem1272682 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) : (term199 x B1 B2 y) = (term182 x B1 B2 y).
Proof. exact (SYM (@lem1272681 x B1 B2 y)). Qed.
Lemma lem1272683 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) (h1 : term198 x B1 B2 y) : term198 x B1 B2 y.
Proof. exact (h1). Qed.
Lemma lem1272684 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) (m : nat) (h1 : term196 x B1 B2 y m) : term196 x B1 B2 y m.
Proof. exact (h1). Qed.
Lemma lem1272685 (n : nat) (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) (m : nat) (h1 : term193 n x B1 B2 y m) : term193 n x B1 B2 y m.
Proof. exact (h1). Qed.
Lemma lem1272686 (n : nat) (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) (m : nat) (h1 : term193 n x B1 B2 y m) : term193 n x B1 B2 y m.
Proof. exact (h1). Qed.
Lemma lem1272688 (c : Prop) (b : Prop) (a : Prop) (d : Prop) : term200 c b a d.
Proof. exact (fun h0 : term92 a b c d => @lem1272449 a b c d h0). Qed.
Lemma lem1272689 (n : nat) (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) (m : nat) : term201 n x B1 B2 y m.
Proof. exact (@lem1272688 (m = (NUMERAL 0)) (term202 y B1 B2 x n) (n = (NUMERAL 0)) (term202 x B1 B2 y m)). Qed.
Lemma lem1272690 (n : nat) (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) (m : nat) (h1 : term193 n x B1 B2 y m) : term203 n x B1 B2 y m.
Proof. exact (@lem1272689 n x B1 B2 y m (@lem1272686 n x B1 B2 y m h1)). Qed.
Lemma lem1272692 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1272693 (n : nat) (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) (m : nat) : (term204 n x B1 B2 y m) = (term205 n x B1 B2 y m).
Proof. exact (@lem1272692 (term203 n x B1 B2 y m)). Qed.
Lemma lem1272701 (n : nat) (m : nat) : (term62 m n) = (Peano.le n m).
Proof. exact (EQ_MP (@lem1272163 n m) (@lem1272162 m n)). Qed.
Lemma lem1272702 (x : nadd) (y : nadd) (n : nat) (B1 : nat) (B2 : nat) : (term206 y B1 B2 x n) = (term207 x y n B1 B2).
Proof. exact (@lem1272701 (dest_nadd x n) (term208 y n B1 B2)). Qed.
Lemma lem1272703 (m : nat) : (term209 m) = (term209 m).
Proof. exact (eq_refl (term209 m)). Qed.
Lemma lem1272704 (m : nat) (x : nadd) (y : nadd) (n : nat) (B1 : nat) (B2 : nat) : (term210 m y B1 B2 x n) = (term211 m x y n B1 B2).
Proof. exact (MK_COMB (@lem1272703 m) (@lem1272702 x y n B1 B2)). Qed.
Lemma lem1272706 (n : nat) (m : nat) (p : nat) : (term76 m n p) = (term75 n m p).
Proof. exact (EQ_MP (@lem1272157 n m p) (@lem1272156 n m p)). Qed.
Lemma lem1272707 (x : nadd) (m : nat) (y : nadd) (n : nat) (B1 : nat) (B2 : nat) : (term211 m x y n B1 B2) = (term212 x m y n B1 B2).
Proof. exact (@lem1272706 (dest_nadd x n) m (term208 y n B1 B2)). Qed.
Lemma lem1272708 (x : nadd) (m : nat) (y : nadd) (n : nat) (B1 : nat) (B2 : nat) : (term210 m y B1 B2 x n) = (term212 x m y n B1 B2).
Proof. exact (TRANS (@lem1272704 m x y n B1 B2) (@lem1272707 x m y n B1 B2)). Qed.
Lemma lem1272709 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1272710 (x : nadd) (m : nat) (y : nadd) (n : nat) (B1 : nat) (B2 : nat) : (term213 m y B1 B2 x n) = (term214 x m y n B1 B2).
Proof. exact (MK_COMB (@lem1272709) (@lem1272708 x m y n B1 B2)). Qed.
Lemma lem1272711 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1272712 (x : nadd) (m : nat) (y : nadd) (n : nat) (B1 : nat) (B2 : nat) : (term215 m y B1 B2 x n) = (term216 x m y n B1 B2).
Proof. exact (MK_COMB (@lem1272711) (@lem1272710 x m y n B1 B2)). Qed.
Lemma lem1272718 (n : nat) (m : nat) : (term62 m n) = (Peano.le n m).
Proof. exact (EQ_MP (@lem1272163 n m) (@lem1272162 m n)). Qed.
Lemma lem1272719 (y : nadd) (x : nadd) (m : nat) (B1 : nat) (B2 : nat) : (term206 x B1 B2 y m) = (term207 y x m B1 B2).
Proof. exact (@lem1272718 (dest_nadd y m) (term208 x m B1 B2)). Qed.
Lemma lem1272720 (n : nat) : (term209 n) = (term209 n).
Proof. exact (eq_refl (term209 n)). Qed.
Lemma lem1272721 (n : nat) (y : nadd) (x : nadd) (m : nat) (B1 : nat) (B2 : nat) : (term210 n x B1 B2 y m) = (term211 n y x m B1 B2).
Proof. exact (MK_COMB (@lem1272720 n) (@lem1272719 y x m B1 B2)). Qed.
Lemma lem1272723 (n : nat) (m : nat) (p : nat) : (term76 m n p) = (term75 n m p).
Proof. exact (EQ_MP (@lem1272157 n m p) (@lem1272156 n m p)). Qed.
Lemma lem1272724 (y : nadd) (n : nat) (x : nadd) (m : nat) (B1 : nat) (B2 : nat) : (term211 n y x m B1 B2) = (term212 y n x m B1 B2).
Proof. exact (@lem1272723 (dest_nadd y m) n (term208 x m B1 B2)). Qed.
Lemma lem1272725 (y : nadd) (n : nat) (x : nadd) (m : nat) (B1 : nat) (B2 : nat) : (term210 n x B1 B2 y m) = (term212 y n x m B1 B2).
Proof. exact (TRANS (@lem1272721 n y x m B1 B2) (@lem1272724 y n x m B1 B2)). Qed.
Lemma lem1272726 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1272727 (y : nadd) (n : nat) (x : nadd) (m : nat) (B1 : nat) (B2 : nat) : (term213 n x B1 B2 y m) = (term214 y n x m B1 B2).
Proof. exact (MK_COMB (@lem1272726) (@lem1272725 y n x m B1 B2)). Qed.
Lemma lem1272728 (y : nadd) (n : nat) (x : nadd) (m : nat) (B1 : nat) (B2 : nat) : (term203 n x B1 B2 y m) = (term217 y n x m B1 B2).
Proof. exact (MK_COMB (@lem1272712 x m y n B1 B2) (@lem1272727 y n x m B1 B2)). Qed.
Lemma lem1272731 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1272732 (y : nadd) (n : nat) (x : nadd) (m : nat) (B1 : nat) (B2 : nat) : (term205 n x B1 B2 y m) = (term218 y n x m B1 B2).
Proof. exact (MK_COMB (@lem1272731) (@lem1272728 y n x m B1 B2)). Qed.
Lemma lem1272733 (y : nadd) (n : nat) (x : nadd) (m : nat) (B1 : nat) (B2 : nat) : (term204 n x B1 B2 y m) = (term218 y n x m B1 B2).
Proof. exact (TRANS (@lem1272693 n x B1 B2 y m) (@lem1272732 y n x m B1 B2)). Qed.
Lemma lem1272734 (n : nat) (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) (m : nat) : (term218 y n x m B1 B2) = (term204 n x B1 B2 y m).
Proof. exact (SYM (@lem1272733 y n x m B1 B2)). Qed.
Lemma lem1272738 (n : nat) (m : nat) : (term74 m n) = (Peano.lt n m).
Proof. exact (EQ_MP (@lem1272130 n m) (@lem1272129 m n)). Qed.
Lemma lem1272739 (y : nadd) (B1 : nat) (B2 : nat) (m : nat) (x : nadd) (n : nat) : (term214 x m y n B1 B2) = (term219 y B1 B2 m x n).
Proof. exact (@lem1272738 (term220 m y n B1 B2) (term221 m x n)). Qed.
Lemma lem1272740 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1272741 (y : nadd) (B1 : nat) (B2 : nat) (m : nat) (x : nadd) (n : nat) : (term216 x m y n B1 B2) = (term222 y B1 B2 m x n).
Proof. exact (MK_COMB (@lem1272740) (@lem1272739 y B1 B2 m x n)). Qed.
Lemma lem1272743 (n : nat) (m : nat) : (term74 m n) = (Peano.lt n m).
Proof. exact (EQ_MP (@lem1272130 n m) (@lem1272129 m n)). Qed.
Lemma lem1272744 (x : nadd) (B1 : nat) (B2 : nat) (n : nat) (y : nadd) (m : nat) : (term214 y n x m B1 B2) = (term219 x B1 B2 n y m).
Proof. exact (@lem1272743 (term220 n x m B1 B2) (term221 n y m)). Qed.
Lemma lem1272745 (x : nadd) (B1 : nat) (B2 : nat) (n : nat) (y : nadd) (m : nat) : (term217 y n x m B1 B2) = (term223 x B1 B2 n y m).
Proof. exact (MK_COMB (@lem1272741 y B1 B2 m x n) (@lem1272744 x B1 B2 n y m)). Qed.
Lemma lem1272748 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1272749 (x : nadd) (B1 : nat) (B2 : nat) (n : nat) (y : nadd) (m : nat) : (term218 y n x m B1 B2) = (term224 x B1 B2 n y m).
Proof. exact (MK_COMB (@lem1272748) (@lem1272745 x B1 B2 n y m)). Qed.
Lemma lem1272750 (y : nadd) (n : nat) (x : nadd) (m : nat) (B1 : nat) (B2 : nat) : (term224 x B1 B2 n y m) = (term218 y n x m B1 B2).
Proof. exact (SYM (@lem1272749 x B1 B2 n y m)). Qed.
Lemma lem1272751 (x : nadd) (B1 : nat) (B2 : nat) (n : nat) (y : nadd) (m : nat) (h1 : term223 x B1 B2 n y m) : term223 x B1 B2 n y m.
Proof. exact (h1). Qed.
Lemma lem1272753 (m : nat) (n : nat) (p : nat) (q : nat) : term70 m n p q.
Proof. exact (EQ_MP (@lem1272124 m n p q) (@lem1272123 m n p q)). Qed.
Lemma lem1272754 (B1 : nat) (B2 : nat) (x : nadd) (n : nat) (y : nadd) (m : nat) : term225 B1 B2 x n y m.
Proof. exact (@lem1272753 (term220 m y n B1 B2) (term220 n x m B1 B2) (term221 m x n) (term221 n y m)). Qed.
Lemma lem1272755 (x : nadd) (B1 : nat) (B2 : nat) (n : nat) (y : nadd) (m : nat) (h1 : term223 x B1 B2 n y m) : term226 B1 B2 x n y m.
Proof. exact (@lem1272754 B1 B2 x n y m (@lem1272751 x B1 B2 n y m h1)). Qed.
Lemma lem1272757 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1272758 (B1 : nat) (B2 : nat) (x : nadd) (n : nat) (y : nadd) (m : nat) : (term227 B1 B2 x n y m) = (term228 B1 B2 x n y m).
Proof. exact (@lem1272757 (term226 B1 B2 x n y m)). Qed.
Lemma lem1272760 (n : nat) (m : nat) : (term62 m n) = (Peano.le n m).
Proof. exact (EQ_MP (@lem1272112 n m) (@lem1272111 m n)). Qed.
Lemma lem1272761 (y : nadd) (n : nat) (x : nadd) (m : nat) (B1 : nat) (B2 : nat) : (term228 B1 B2 x n y m) = (term229 y n x m B1 B2).
Proof. exact (@lem1272760 (term230 x n y m) (term231 y n x m B1 B2)). Qed.
Lemma lem1272762 (y : nadd) (n : nat) (x : nadd) (m : nat) (B1 : nat) (B2 : nat) : (term227 B1 B2 x n y m) = (term229 y n x m B1 B2).
Proof. exact (TRANS (@lem1272758 B1 B2 x n y m) (@lem1272761 y n x m B1 B2)). Qed.
Lemma lem1272763 (B1 : nat) (B2 : nat) (x : nadd) (n : nat) (y : nadd) (m : nat) : (term229 y n x m B1 B2) = (term227 B1 B2 x n y m).
Proof. exact (SYM (@lem1272762 y n x m B1 B2)). Qed.
Lemma lem1272765 (n : nat) (m : nat) (p : nat) : (term57 m n p) = (term58 n m p).
Proof. exact (EQ_MP (@lem1272106 n m p) (@lem1272105 n m p)). Qed.
Lemma lem1272766 (y : nadd) (n : nat) (m : nat) (B1 : nat) (B2 : nat) : (term220 m y n B1 B2) = (term232 y n m B1 B2).
Proof. exact (@lem1272765 (dest_nadd y n) m (Nat.add B1 B2)). Qed.
Lemma lem1272768 (n : nat) (m : nat) (p : nat) : (term57 m n p) = (term58 n m p).
Proof. exact (EQ_MP (@lem1272106 n m p) (@lem1272105 n m p)). Qed.
Lemma lem1272769 (B1 : nat) (m : nat) (B2 : nat) : (term57 m B1 B2) = (term58 B1 m B2).
Proof. exact (@lem1272768 B1 m B2). Qed.
Lemma lem1272770 (m : nat) (y : nadd) (n : nat) : (term233 m y n) = (term233 m y n).
Proof. exact (eq_refl (term233 m y n)). Qed.
Lemma lem1272771 (y : nadd) (n : nat) (B1 : nat) (m : nat) (B2 : nat) : (term232 y n m B1 B2) = (term234 y n B1 m B2).
Proof. exact (MK_COMB (@lem1272770 m y n) (@lem1272769 B1 m B2)). Qed.
Lemma lem1272772 (y : nadd) (n : nat) (B1 : nat) (m : nat) (B2 : nat) : (term220 m y n B1 B2) = (term234 y n B1 m B2).
Proof. exact (TRANS (@lem1272766 y n m B1 B2) (@lem1272771 y n B1 m B2)). Qed.
Lemma lem1272773 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1272774 (y : nadd) (n : nat) (B1 : nat) (m : nat) (B2 : nat) : (term235 m y n B1 B2) = (term236 y n B1 m B2).
Proof. exact (MK_COMB (@lem1272773) (@lem1272772 y n B1 m B2)). Qed.
Lemma lem1272776 (n : nat) (m : nat) (p : nat) : (term57 m n p) = (term58 n m p).
Proof. exact (EQ_MP (@lem1272106 n m p) (@lem1272105 n m p)). Qed.
Lemma lem1272777 (x : nadd) (m : nat) (n : nat) (B1 : nat) (B2 : nat) : (term220 n x m B1 B2) = (term232 x m n B1 B2).
Proof. exact (@lem1272776 (dest_nadd x m) n (Nat.add B1 B2)). Qed.
Lemma lem1272779 (n : nat) (m : nat) (p : nat) : (term57 m n p) = (term58 n m p).
Proof. exact (EQ_MP (@lem1272106 n m p) (@lem1272105 n m p)). Qed.
Lemma lem1272780 (B1 : nat) (n : nat) (B2 : nat) : (term57 n B1 B2) = (term58 B1 n B2).
Proof. exact (@lem1272779 B1 n B2). Qed.
Lemma lem1272781 (n : nat) (x : nadd) (m : nat) : (term233 n x m) = (term233 n x m).
Proof. exact (eq_refl (term233 n x m)). Qed.
Lemma lem1272782 (x : nadd) (m : nat) (B1 : nat) (n : nat) (B2 : nat) : (term232 x m n B1 B2) = (term234 x m B1 n B2).
Proof. exact (MK_COMB (@lem1272781 n x m) (@lem1272780 B1 n B2)). Qed.
Lemma lem1272783 (x : nadd) (m : nat) (B1 : nat) (n : nat) (B2 : nat) : (term220 n x m B1 B2) = (term234 x m B1 n B2).
Proof. exact (TRANS (@lem1272777 x m n B1 B2) (@lem1272782 x m B1 n B2)). Qed.
Lemma lem1272784 (y : nadd) (x : nadd) (m : nat) (B1 : nat) (n : nat) (B2 : nat) : (term231 y n x m B1 B2) = (term237 y x m B1 n B2).
Proof. exact (MK_COMB (@lem1272774 y n B1 m B2) (@lem1272783 x m B1 n B2)). Qed.
Lemma lem1272785 (x : nadd) (n : nat) (y : nadd) (m : nat) : (term238 x n y m) = (term238 x n y m).
Proof. exact (eq_refl (term238 x n y m)). Qed.
Lemma lem1272786 (y : nadd) (x : nadd) (m : nat) (B1 : nat) (n : nat) (B2 : nat) : (term229 y n x m B1 B2) = (term239 y x m B1 n B2).
Proof. exact (MK_COMB (@lem1272785 x n y m) (@lem1272784 y x m B1 n B2)). Qed.
Lemma lem1272787 (y : nadd) (n : nat) (x : nadd) (m : nat) (B1 : nat) (B2 : nat) : (term239 y x m B1 n B2) = (term229 y n x m B1 B2).
Proof. exact (SYM (@lem1272786 y x m B1 n B2)). Qed.
Lemma lem1272789 (d : nat) (b : nat) (e : nat) (a : nat) (c : nat) (f : nat) : (term44 a b c d e f) = (term44 d b e a c f).
Proof. exact (EQ_MP (@lem1272097 d b e a c f) (@lem0)). Qed.
Lemma lem1272790 (x : nadd) (B1 : nat) (y : nadd) (m : nat) (n : nat) (B2 : nat) : (term237 y x m B1 n B2) = (term240 x B1 y m n B2).
Proof. exact (@lem1272789 (term221 n x m) (Nat.mul m B1) (Nat.mul n B1) (term221 m y n) (Nat.mul m B2) (Nat.mul n B2)). Qed.
Lemma lem1272791 (x : nadd) (n : nat) (y : nadd) (m : nat) : (term238 x n y m) = (term238 x n y m).
Proof. exact (eq_refl (term238 x n y m)). Qed.
Lemma lem1272792 (x : nadd) (B1 : nat) (y : nadd) (m : nat) (n : nat) (B2 : nat) : (term239 y x m B1 n B2) = (term241 x B1 y m n B2).
Proof. exact (MK_COMB (@lem1272791 x n y m) (@lem1272790 x B1 y m n B2)). Qed.
Lemma lem1272793 (y : nadd) (x : nadd) (m : nat) (B1 : nat) (n : nat) (B2 : nat) : (term241 x B1 y m n B2) = (term239 y x m B1 n B2).
Proof. exact (SYM (@lem1272792 x B1 y m n B2)). Qed.
Lemma lem1272795 (m : nat) (n : nat) (p : nat) (q : nat) : term35 m n p q.
Proof. exact (EQ_MP (@lem1271902 m n p q) (@lem1271901 m n p q)). Qed.
Lemma lem1272796 (x : nadd) (B1 : nat) (y : nadd) (m : nat) (n : nat) (B2 : nat) : term242 x B1 y m n B2.
Proof. exact (@lem1272795 (term221 m x n) (term221 n y m) (term243 x m n B1) (term244 y m n B2)). Qed.
Lemma lem1272800 (m : nat) (n : nat) (p : nat) : (term11 m n p) = (term10 m n p).
Proof. exact (EQ_MP (@lem1271865 m n p) (@lem1271864 m n p)). Qed.
Lemma lem1272801 (m : nat) (n : nat) (B1 : nat) : (term11 m n B1) = (term10 m n B1).
Proof. exact (@lem1272800 m n B1). Qed.
Lemma lem1272802 (n : nat) (x : nadd) (m : nat) : (term233 n x m) = (term233 n x m).
Proof. exact (eq_refl (term233 n x m)). Qed.
Lemma lem1272803 (x : nadd) (m : nat) (n : nat) (B1 : nat) : (term243 x m n B1) = (term245 x m n B1).
Proof. exact (MK_COMB (@lem1272802 n x m) (@lem1272801 m n B1)). Qed.
Lemma lem1272806 (m : nat) (x : nadd) (n : nat) : (term246 m x n) = (term246 m x n).
Proof. exact (eq_refl (term246 m x n)). Qed.
Lemma lem1272807 (x : nadd) (m : nat) (n : nat) (B1 : nat) : (term247 x m n B1) = (term248 x m n B1).
Proof. exact (MK_COMB (@lem1272806 m x n) (@lem1272803 x m n B1)). Qed.
Lemma lem1272808 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1272809 (x : nadd) (m : nat) (n : nat) (B1 : nat) : (term249 x m n B1) = (term250 x m n B1).
Proof. exact (MK_COMB (@lem1272808) (@lem1272807 x m n B1)). Qed.
Lemma lem1272811 (m : nat) (n : nat) (p : nat) : (term11 m n p) = (term10 m n p).
Proof. exact (EQ_MP (@lem1271865 m n p) (@lem1271864 m n p)). Qed.
Lemma lem1272812 (m : nat) (n : nat) (B2 : nat) : (term11 m n B2) = (term10 m n B2).
Proof. exact (@lem1272811 m n B2). Qed.
Lemma lem1272813 (m : nat) (y : nadd) (n : nat) : (term233 m y n) = (term233 m y n).
Proof. exact (eq_refl (term233 m y n)). Qed.
Lemma lem1272814 (y : nadd) (m : nat) (n : nat) (B2 : nat) : (term244 y m n B2) = (term251 y m n B2).
Proof. exact (MK_COMB (@lem1272813 m y n) (@lem1272812 m n B2)). Qed.
Lemma lem1272817 (n : nat) (y : nadd) (m : nat) : (term246 n y m) = (term246 n y m).
Proof. exact (eq_refl (term246 n y m)). Qed.
Lemma lem1272818 (y : nadd) (m : nat) (n : nat) (B2 : nat) : (term252 y m n B2) = (term253 y m n B2).
Proof. exact (MK_COMB (@lem1272817 n y m) (@lem1272814 y m n B2)). Qed.
Lemma lem1272819 (x : nadd) (B1 : nat) (y : nadd) (m : nat) (n : nat) (B2 : nat) : (term254 x B1 y m n B2) = (term255 x B1 y m n B2).
Proof. exact (MK_COMB (@lem1272809 x m n B1) (@lem1272818 y m n B2)). Qed.
Lemma lem1272822 (x : nadd) (B1 : nat) (y : nadd) (m : nat) (n : nat) (B2 : nat) : (term255 x B1 y m n B2) = (term254 x B1 y m n B2).
Proof. exact (SYM (@lem1272819 x B1 y m n B2)). Qed.
Lemma lem1272824 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem1271838 n m) (@lem1271837 m n)). Qed.
Lemma lem1272825 (B1 : nat) (m : nat) (n : nat) : (term10 m n B1) = (term57 B1 m n).
Proof. exact (@lem1272824 B1 (Nat.add m n)). Qed.
Lemma lem1272826 (n : nat) (x : nadd) (m : nat) : (term233 n x m) = (term233 n x m).
Proof. exact (eq_refl (term233 n x m)). Qed.
Lemma lem1272827 (x : nadd) (B1 : nat) (m : nat) (n : nat) : (term245 x m n B1) = (term256 x B1 m n).
Proof. exact (MK_COMB (@lem1272826 n x m) (@lem1272825 B1 m n)). Qed.
Lemma lem1272828 (m : nat) (x : nadd) (n : nat) : (term246 m x n) = (term246 m x n).
Proof. exact (eq_refl (term246 m x n)). Qed.
Lemma lem1272829 (x : nadd) (B1 : nat) (m : nat) (n : nat) : (term248 x m n B1) = (term257 x B1 m n).
Proof. exact (MK_COMB (@lem1272828 m x n) (@lem1272827 x B1 m n)). Qed.
Lemma lem1272830 (x : nadd) (m : nat) (n : nat) (B1 : nat) : (term257 x B1 m n) = (term248 x m n B1).
Proof. exact (SYM (@lem1272829 x B1 m n)). Qed.
Lemma lem1272832 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem1271838 n m) (@lem1271837 m n)). Qed.
Lemma lem1272833 (B2 : nat) (m : nat) (n : nat) : (term10 m n B2) = (term57 B2 m n).
Proof. exact (@lem1272832 B2 (Nat.add m n)). Qed.
Lemma lem1272834 (m : nat) (y : nadd) (n : nat) : (term233 m y n) = (term233 m y n).
Proof. exact (eq_refl (term233 m y n)). Qed.
Lemma lem1272835 (y : nadd) (B2 : nat) (m : nat) (n : nat) : (term251 y m n B2) = (term258 y B2 m n).
Proof. exact (MK_COMB (@lem1272834 m y n) (@lem1272833 B2 m n)). Qed.
Lemma lem1272836 (n : nat) (y : nadd) (m : nat) : (term246 n y m) = (term246 n y m).
Proof. exact (eq_refl (term246 n y m)). Qed.
Lemma lem1272837 (y : nadd) (B2 : nat) (m : nat) (n : nat) : (term253 y m n B2) = (term259 y B2 m n).
Proof. exact (MK_COMB (@lem1272836 n y m) (@lem1272835 y B2 m n)). Qed.
Lemma lem1272838 (y : nadd) (m : nat) (n : nat) (B2 : nat) : (term259 y B2 m n) = (term253 y m n B2).
Proof. exact (SYM (@lem1272837 y B2 m n)). Qed.
Lemma lem1272848 (n : nat) (m : nat) (p : nat) : (term5 m n p) = (term6 n m p).
Proof. exact (EQ_MP (@lem1271832 n m p) (@lem1271831 n m p)). Qed.
Lemma lem1272849 (x : nadd) (B1 : nat) (m : nat) (n : nat) : (term260 x B1 m n) = (term261 x B1 m n).
Proof. exact (@lem1272848 (term221 n x m) (term221 m x n) (term57 B1 m n)). Qed.
Lemma lem1272852 (x : nadd) (B1 : nat) (m : nat) : (term262 x B1 m) = (term263 x B1 m).
Proof. exact (fun_ext (fun n : nat => @lem1272849 x B1 m n)). Qed.
Lemma lem1272853 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1272854 (x : nadd) (B1 : nat) (m : nat) : (term264 x B1 m) = (term265 x B1 m).
Proof. exact (MK_COMB (@lem1272853) (@lem1272852 x B1 m)). Qed.
Lemma lem1272859 (x : nadd) (B1 : nat) : (term266 x B1) = (term267 x B1).
Proof. exact (fun_ext (fun m : nat => @lem1272854 x B1 m)). Qed.
Lemma lem1272860 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1272861 (x : nadd) (B1 : nat) : (term125 x B1) = (term268 x B1).
Proof. exact (MK_COMB (@lem1272860) (@lem1272859 x B1)). Qed.
Lemma lem1272866 (x : nadd) (B1 : nat) (h1 : term125 x B1) : term268 x B1.
Proof. exact (EQ_MP (@lem1272861 x B1) (@lem1272490 x B1 h1)). Qed.
Lemma lem1272932 (n : nat) (m : nat) (p : nat) : (term5 m n p) = (term6 n m p).
Proof. exact (EQ_MP (@lem1271832 n m p) (@lem1271831 n m p)). Qed.
Lemma lem1272933 (y : nadd) (B2 : nat) (m : nat) (n : nat) : (term260 y B2 m n) = (term261 y B2 m n).
Proof. exact (@lem1272932 (term221 n y m) (term221 m y n) (term57 B2 m n)). Qed.
Lemma lem1272936 (y : nadd) (B2 : nat) (m : nat) : (term262 y B2 m) = (term263 y B2 m).
Proof. exact (fun_ext (fun n : nat => @lem1272933 y B2 m n)). Qed.
Lemma lem1272937 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1272938 (y : nadd) (B2 : nat) (m : nat) : (term264 y B2 m) = (term265 y B2 m).
Proof. exact (MK_COMB (@lem1272937) (@lem1272936 y B2 m)). Qed.
Lemma lem1272943 (y : nadd) (B2 : nat) : (term266 y B2) = (term267 y B2).
Proof. exact (fun_ext (fun m : nat => @lem1272938 y B2 m)). Qed.
Lemma lem1272944 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1272945 (y : nadd) (B2 : nat) : (term125 y B2) = (term268 y B2).
Proof. exact (MK_COMB (@lem1272944) (@lem1272943 y B2)). Qed.
Lemma lem1272950 (y : nadd) (B2 : nat) (h1 : term125 y B2) : term268 y B2.
Proof. exact (EQ_MP (@lem1272945 y B2) (@lem1272486 y B2 h1)). Qed.
Lemma lem1272951 (m : nat) (x : nadd) (B1 : nat) (h1 : term125 x B1) : term269 x B1 m.
Proof. exact (@lem1272866 x B1 h1 m). Qed.
Lemma lem1272952 (x : nadd) (B1 : nat) (m : nat) : (term269 x B1 m) = (term265 x B1 m).
Proof. exact (eq_refl (term269 x B1 m)). Qed.
Lemma lem1272953 (m : nat) (x : nadd) (B1 : nat) (h1 : term125 x B1) : term265 x B1 m.
Proof. exact (EQ_MP (@lem1272952 x B1 m) (@lem1272951 m x B1 h1)). Qed.
Lemma lem1272954 (m : nat) (n : nat) (x : nadd) (B1 : nat) (h1 : term125 x B1) : term270 x B1 m n.
Proof. exact (@lem1272953 m x B1 h1 n). Qed.
Lemma lem1272955 (x : nadd) (B1 : nat) (m : nat) (n : nat) : (term270 x B1 m n) = (term261 x B1 m n).
Proof. exact (eq_refl (term270 x B1 m n)). Qed.
Lemma lem1272956 (m : nat) (n : nat) (x : nadd) (B1 : nat) (h1 : term125 x B1) : term261 x B1 m n.
Proof. exact (EQ_MP (@lem1272955 x B1 m n) (@lem1272954 m n x B1 h1)). Qed.
Lemma lem1272960 (m : nat) (n : nat) (x : nadd) (B1 : nat) (h1 : term125 x B1) : term257 x B1 m n.
Proof. exact (proj1 (@lem1272956 m n x B1 h1)). Qed.
Lemma lem1272961 (x : nadd) (B1 : nat) (m : nat) (n : nat) : (term257 x B1 m n) = ((term257 x B1 m n) = True).
Proof. exact (@lem7 (term257 x B1 m n)). Qed.
Lemma lem1272978 (m : nat) (n : nat) (x : nadd) (B1 : nat) (h1 : term125 x B1) : (term257 x B1 m n) = True.
Proof. exact (EQ_MP (@lem1272961 x B1 m n) (@lem1272960 m n x B1 h1)). Qed.
Lemma lem1272979 (m : nat) (n : nat) (x : nadd) (B1 : nat) (h1 : term125 x B1) : True = (term257 x B1 m n).
Proof. exact (SYM (@lem1272978 m n x B1 h1)). Qed.
Lemma lem1272980 (m : nat) (n : nat) (x : nadd) (B1 : nat) (h1 : term125 x B1) : term257 x B1 m n.
Proof. exact (EQ_MP (@lem1272979 m n x B1 h1) (@lem0)). Qed.
Lemma lem1272993 (m : nat) (y : nadd) (B2 : nat) (h1 : term125 y B2) : term269 y B2 m.
Proof. exact (@lem1272950 y B2 h1 m). Qed.
Lemma lem1272994 (y : nadd) (B2 : nat) (m : nat) : (term269 y B2 m) = (term265 y B2 m).
Proof. exact (eq_refl (term269 y B2 m)). Qed.
Lemma lem1272995 (m : nat) (y : nadd) (B2 : nat) (h1 : term125 y B2) : term265 y B2 m.
Proof. exact (EQ_MP (@lem1272994 y B2 m) (@lem1272993 m y B2 h1)). Qed.
Lemma lem1272996 (m : nat) (n : nat) (y : nadd) (B2 : nat) (h1 : term125 y B2) : term270 y B2 m n.
Proof. exact (@lem1272995 m y B2 h1 n). Qed.
Lemma lem1272997 (y : nadd) (B2 : nat) (m : nat) (n : nat) : (term270 y B2 m n) = (term261 y B2 m n).
Proof. exact (eq_refl (term270 y B2 m n)). Qed.
Lemma lem1272998 (m : nat) (n : nat) (y : nadd) (B2 : nat) (h1 : term125 y B2) : term261 y B2 m n.
Proof. exact (EQ_MP (@lem1272997 y B2 m n) (@lem1272996 m n y B2 h1)). Qed.
Lemma lem1272999 (m : nat) (n : nat) (y : nadd) (B2 : nat) (h1 : term125 y B2) : term259 y B2 m n.
Proof. exact (proj2 (@lem1272998 m n y B2 h1)). Qed.
Lemma lem1273000 (y : nadd) (B2 : nat) (m : nat) (n : nat) : (term259 y B2 m n) = ((term259 y B2 m n) = True).
Proof. exact (@lem7 (term259 y B2 m n)). Qed.
Lemma lem1273006 (m : nat) (n : nat) (y : nadd) (B2 : nat) (h1 : term125 y B2) : (term259 y B2 m n) = True.
Proof. exact (EQ_MP (@lem1273000 y B2 m n) (@lem1272999 m n y B2 h1)). Qed.
Lemma lem1273007 (m : nat) (n : nat) (y : nadd) (B2 : nat) (h1 : term125 y B2) : True = (term259 y B2 m n).
Proof. exact (SYM (@lem1273006 m n y B2 h1)). Qed.
Lemma lem1273008 (m : nat) (n : nat) (y : nadd) (B2 : nat) (h1 : term125 y B2) : term259 y B2 m n.
Proof. exact (EQ_MP (@lem1273007 m n y B2 h1) (@lem0)). Qed.
Lemma lem1273009 (m : nat) (n : nat) (y : nadd) (B2 : nat) (h1 : term125 y B2) : term253 y m n B2.
Proof. exact (EQ_MP (@lem1272838 y m n B2) (@lem1273008 m n y B2 h1)). Qed.
Lemma lem1273010 (m : nat) (n : nat) (x : nadd) (B1 : nat) (h1 : term125 x B1) : term248 x m n B1.
Proof. exact (EQ_MP (@lem1272830 x m n B1) (@lem1272980 m n x B1 h1)). Qed.
Lemma lem1273011 (m : nat) (n : nat) (x : nadd) (B1 : nat) (y : nadd) (B2 : nat) (h1 : term125 x B1) (h2 : term125 y B2) : term255 x B1 y m n B2.
Proof. exact (conj (@lem1273010 m n x B1 h1) (@lem1273009 m n y B2 h2)). Qed.
Lemma lem1273012 (m : nat) (n : nat) (x : nadd) (B1 : nat) (y : nadd) (B2 : nat) (h1 : term125 x B1) (h2 : term125 y B2) : term254 x B1 y m n B2.
Proof. exact (EQ_MP (@lem1272822 x B1 y m n B2) (@lem1273011 m n x B1 y B2 h1 h2)). Qed.
Lemma lem1273013 (m : nat) (n : nat) (x : nadd) (B1 : nat) (y : nadd) (B2 : nat) (h1 : term125 x B1) (h2 : term125 y B2) : term241 x B1 y m n B2.
Proof. exact (@lem1272796 x B1 y m n B2 (@lem1273012 m n x B1 y B2 h1 h2)). Qed.
Lemma lem1273014 (m : nat) (n : nat) (x : nadd) (B1 : nat) (y : nadd) (B2 : nat) (h1 : term125 x B1) (h2 : term125 y B2) : term239 y x m B1 n B2.
Proof. exact (EQ_MP (@lem1272793 y x m B1 n B2) (@lem1273013 m n x B1 y B2 h1 h2)). Qed.
Lemma lem1273015 (n : nat) (m : nat) (x : nadd) (B1 : nat) (y : nadd) (B2 : nat) (h1 : term125 x B1) (h2 : term125 y B2) : term229 y n x m B1 B2.
Proof. exact (EQ_MP (@lem1272787 y n x m B1 B2) (@lem1273014 m n x B1 y B2 h1 h2)). Qed.
Lemma lem1273016 (n : nat) (m : nat) (x : nadd) (B1 : nat) (y : nadd) (B2 : nat) (h1 : term125 x B1) (h2 : term125 y B2) : term227 B1 B2 x n y m.
Proof. exact (EQ_MP (@lem1272763 B1 B2 x n y m) (@lem1273015 n m x B1 y B2 h1 h2)). Qed.
Lemma lem1273017 (x : nadd) (B1 : nat) (B2 : nat) (n : nat) (y : nadd) (m : nat) (h1 : term125 x B1) (h2 : term125 y B2) (h3 : term223 x B1 B2 n y m) : False.
Proof. exact (@lem1273016 n m x B1 y B2 h1 h2 (@lem1272755 x B1 B2 n y m h3)). Qed.
Lemma lem1273018 (n : nat) (m : nat) (x : nadd) (B1 : nat) (y : nadd) (B2 : nat) (h1 : term125 x B1) (h2 : term125 y B2) : term271 x B1 B2 n y m.
Proof. exact (fun h0 : term223 x B1 B2 n y m => @lem1273017 x B1 B2 n y m h1 h2 h0). Qed.
Lemma lem1273019 (x : nadd) (B1 : nat) (B2 : nat) (n : nat) (y : nadd) (m : nat) : (term271 x B1 B2 n y m) = (term224 x B1 B2 n y m).
Proof. exact (@lem69 (term223 x B1 B2 n y m)). Qed.
Lemma lem1273020 (n : nat) (m : nat) (x : nadd) (B1 : nat) (y : nadd) (B2 : nat) (h1 : term125 x B1) (h2 : term125 y B2) : term224 x B1 B2 n y m.
Proof. exact (EQ_MP (@lem1273019 x B1 B2 n y m) (@lem1273018 n m x B1 y B2 h1 h2)). Qed.
Lemma lem1273021 (n : nat) (m : nat) (x : nadd) (B1 : nat) (y : nadd) (B2 : nat) (h1 : term125 x B1) (h2 : term125 y B2) : term218 y n x m B1 B2.
Proof. exact (EQ_MP (@lem1272750 y n x m B1 B2) (@lem1273020 n m x B1 y B2 h1 h2)). Qed.
Lemma lem1273022 (n : nat) (m : nat) (x : nadd) (B1 : nat) (y : nadd) (B2 : nat) (h1 : term125 x B1) (h2 : term125 y B2) : term204 n x B1 B2 y m.
Proof. exact (EQ_MP (@lem1272734 n x B1 B2 y m) (@lem1273021 n m x B1 y B2 h1 h2)). Qed.
Lemma lem1273023 (n : nat) (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) (m : nat) (h1 : term125 x B1) (h2 : term125 y B2) (h3 : term193 n x B1 B2 y m) : False.
Proof. exact (@lem1273022 n m x B1 y B2 h1 h2 (@lem1272690 n x B1 B2 y m h3)). Qed.
Lemma lem1273024 (n : nat) (m : nat) (x : nadd) (B1 : nat) (y : nadd) (B2 : nat) (h1 : term125 x B1) (h2 : term125 y B2) : term272 n x B1 B2 y m.
Proof. exact (fun h0 : term193 n x B1 B2 y m => @lem1273023 n x B1 B2 y m h1 h2 h0). Qed.
Lemma lem1273025 (n : nat) (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) (m : nat) (h1 : term125 x B1) (h2 : term125 y B2) (h3 : term193 n x B1 B2 y m) : False.
Proof. exact (@lem1273024 n m x B1 y B2 h1 h2 (@lem1272685 n x B1 B2 y m h3)). Qed.
Lemma lem1273026 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) (m : nat) (h1 : term125 x B1) (h2 : term125 y B2) (h3 : term196 x B1 B2 y m) : False.
Proof. exact (ex_elim (@lem1272684 x B1 B2 y m h3) (fun n : nat => fun h0 : term195 x B1 B2 y m n => @lem1273025 n x B1 B2 y m h1 h2 h0)). Qed.
Lemma lem1273027 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) (h1 : term125 x B1) (h2 : term125 y B2) (h3 : term198 x B1 B2 y) : False.
Proof. exact (ex_elim (@lem1272683 x B1 B2 y h3) (fun m : nat => fun h0 : term197 x B1 B2 y m => @lem1273026 x B1 B2 y m h1 h2 h0)). Qed.
Lemma lem1273028 (x : nadd) (B1 : nat) (y : nadd) (B2 : nat) (h1 : term125 x B1) (h2 : term125 y B2) : term273 x B1 B2 y.
Proof. exact (fun h0 : term198 x B1 B2 y => @lem1273027 x B1 B2 y h1 h2 h0). Qed.
Lemma lem1273029 (x : nadd) (B1 : nat) (B2 : nat) (y : nadd) : (term273 x B1 B2 y) = (term199 x B1 B2 y).
Proof. exact (@lem69 (term198 x B1 B2 y)). Qed.
Lemma lem1273030 (x : nadd) (B1 : nat) (y : nadd) (B2 : nat) (h1 : term125 x B1) (h2 : term125 y B2) : term199 x B1 B2 y.
Proof. exact (EQ_MP (@lem1273029 x B1 B2 y) (@lem1273028 x B1 y B2 h1 h2)). Qed.
Lemma lem1273031 (x : nadd) (B1 : nat) (y : nadd) (B2 : nat) (h1 : term125 x B1) (h2 : term125 y B2) : term182 x B1 B2 y.
Proof. exact (EQ_MP (@lem1272682 x B1 B2 y) (@lem1273030 x B1 y B2 h1 h2)). Qed.
Lemma lem1273032 (x : nadd) (B1 : nat) (y : nadd) (B2 : nat) (h1 : term125 x B1) (h2 : term125 y B2) : term162 x B1 B2 y.
Proof. exact (EQ_MP (@lem1272630 x B1 B2 y) (@lem1273031 x B1 y B2 h1 h2)). Qed.
Lemma lem1273033 (B1 : nat) (B2 : nat) (x : nadd) (y : nadd) (h1 : term125 x B1) (h2 : term125 y B2) (h3 : term158 x y) : False.
Proof. exact (@lem1273032 x B1 y B2 h1 h2 (@lem1272585 B1 B2 x y h3)). Qed.
Lemma lem1273034 (x : nadd) (B1 : nat) (y : nadd) (B2 : nat) (h1 : term125 x B1) (h2 : term125 y B2) : term274 x y.
Proof. exact (fun h0 : term158 x y => @lem1273033 B1 B2 x y h1 h2 h0). Qed.
Lemma lem1273035 (x : nadd) (y : nadd) : (term274 x y) = (term159 x y).
Proof. exact (@lem69 (term158 x y)). Qed.
Lemma lem1273036 (x : nadd) (B1 : nat) (y : nadd) (B2 : nat) (h1 : term125 x B1) (h2 : term125 y B2) : term159 x y.
Proof. exact (EQ_MP (@lem1273035 x y) (@lem1273034 x B1 y B2 h1 h2)). Qed.
Lemma lem1273037 (x : nadd) (B1 : nat) (y : nadd) (B2 : nat) (h1 : term125 x B1) (h2 : term125 y B2) : term137 x y.
Proof. exact (EQ_MP (@lem1272581 x y) (@lem1273036 x B1 y B2 h1 h2)). Qed.
Lemma lem1273038 (B1 : nat) (B2 : nat) (y : nadd) (x : nadd) (h1 : term125 x B1) (h2 : term125 y B2) (h3 : term132 y x) : False.
Proof. exact (@lem1273037 x B1 y B2 h1 h2 (@lem1272525 y x h3)). Qed.
Lemma lem1273039 (x : nadd) (B1 : nat) (y : nadd) (B2 : nat) (h1 : term125 x B1) (h2 : term125 y B2) : term275 y x.
Proof. exact (fun h0 : term132 y x => @lem1273038 B1 B2 y x h1 h2 h0). Qed.
Lemma lem1273040 (y : nadd) (x : nadd) : (term275 y x) = (term133 y x).
Proof. exact (@lem69 (term132 y x)). Qed.
Lemma lem1273041 (x : nadd) (B1 : nat) (y : nadd) (B2 : nat) (h1 : term125 x B1) (h2 : term125 y B2) : term133 y x.
Proof. exact (EQ_MP (@lem1273040 y x) (@lem1273039 x B1 y B2 h1 h2)). Qed.
Lemma lem1273042 (x : nadd) (B1 : nat) (y : nadd) (B2 : nat) (h1 : term125 x B1) (h2 : term125 y B2) : term128 y x.
Proof. exact (EQ_MP (@lem1272514 y x) (@lem1273041 x B1 y B2 h1 h2)). Qed.
Lemma lem1273043 (y : nadd) (x : nadd) (B1 : nat) (h1 : term125 x B1) : term128 y x.
Proof. exact (ex_elim (@lem1272485 y) (fun B2 : nat => fun h0 : term276 y B2 => @lem1273042 x B1 y B2 h1 h0)). Qed.
Lemma lem1273044 (y : nadd) (x : nadd) : term128 y x.
Proof. exact (ex_elim (@lem1272489 x) (fun B1 : nat => fun h0 : term276 x B1 => @lem1273043 y x B1 h0)). Qed.
Lemma lem1273045 (y : nadd) (x : nadd) : term127 y x.
Proof. exact (EQ_MP (@lem1272508 y x) (@lem1273044 y x)). Qed.
Lemma lem1273050 (x : nadd) : term277 x.
Proof. exact (fun y : nadd => @lem1273045 y x). Qed.
Lemma lem1273055 : term278.
Proof. exact (fun x : nadd => @lem1273050 x). Qed.
