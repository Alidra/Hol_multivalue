Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_LE_ANTISYM_term_abbrevs.
Require Import ADD_ASSOC_spec.
Require Import LE_ADD_spec.
Require Import LE_ADD_RCANCEL_spec.
Require Import nadd_eq_spec.
Require Import nadd_le_spec.
Require Import thm0_spec.
Require Import thm1247096_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm272809_spec.
Require Import thm32_spec.
Require Import thm7_spec.
Lemma lem1270881 (m : nat) : term0 m.
Proof. exact (@lem1247096 m). Qed.
Lemma lem1270882 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1270883 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1270882 m) (@lem1270881 m)). Qed.
Lemma lem1270884 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1270883 m n). Qed.
Lemma lem1270885 (n : nat) (m : nat) : (term2 m n) = (term3 n m).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1270886 (n : nat) (m : nat) : term3 n m.
Proof. exact (EQ_MP (@lem1270885 n m) (@lem1270884 m n)). Qed.
Lemma lem1270887 (n : nat) (m : nat) (p : nat) : term4 n m p.
Proof. exact (@lem1270886 n m p). Qed.
Lemma lem1270888 (n : nat) (m : nat) (p : nat) : (term4 n m p) = ((term5 m n p) = (term6 n m p)).
Proof. exact (eq_refl (term4 n m p)). Qed.
Lemma lem1270890 (x : nadd) : term7 x.
Proof. exact (@lem1267930 x). Qed.
Lemma lem1270891 (x : nadd) : (term7 x) = (term8 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem1270892 (x : nadd) : term8 x.
Proof. exact (EQ_MP (@lem1270891 x) (@lem1270890 x)). Qed.
Lemma lem1270893 (x : nadd) (y : nadd) : term9 x y.
Proof. exact (@lem1270892 x y). Qed.
Lemma lem1270894 (x : nadd) (y : nadd) : (term9 x y) = ((nadd_eq x y) = (term10 x y)).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem1270896 (x : nadd) : term11 x.
Proof. exact (@lem1269692 x). Qed.
Lemma lem1270897 (x : nadd) : (term11 x) = (term12 x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem1270898 (x : nadd) : term12 x.
Proof. exact (EQ_MP (@lem1270897 x) (@lem1270896 x)). Qed.
Lemma lem1270899 (x : nadd) (y : nadd) : term13 x y.
Proof. exact (@lem1270898 x y). Qed.
Lemma lem1270900 (x : nadd) (y : nadd) : (term13 x y) = ((nadd_le x y) = (term14 x y)).
Proof. exact (eq_refl (term13 x y)). Qed.
Lemma lem1270907 (x : nadd) (y : nadd) : (nadd_le x y) = (term14 x y).
Proof. exact (EQ_MP (@lem1270900 x y) (@lem1270899 x y)). Qed.
Lemma lem1270916 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1270917 (x : nadd) (y : nadd) : (term15 x y) = (term16 x y).
Proof. exact (MK_COMB (@lem1270916) (@lem1270907 x y)). Qed.
Lemma lem1270919 (x : nadd) (y : nadd) : (nadd_le x y) = (term14 x y).
Proof. exact (EQ_MP (@lem1270900 x y) (@lem1270899 x y)). Qed.
Lemma lem1270920 (y : nadd) (x : nadd) : (nadd_le y x) = (term14 y x).
Proof. exact (@lem1270919 y x). Qed.
Lemma lem1270929 (y : nadd) (x : nadd) : (term17 y x) = (term18 y x).
Proof. exact (MK_COMB (@lem1270917 x y) (@lem1270920 y x)). Qed.
Lemma lem1270932 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1270933 (y : nadd) (x : nadd) : (term19 y x) = (term20 y x).
Proof. exact (MK_COMB (@lem1270932) (@lem1270929 y x)). Qed.
Lemma lem1270935 (x : nadd) (y : nadd) : (nadd_eq x y) = (term10 x y).
Proof. exact (EQ_MP (@lem1270894 x y) (@lem1270893 x y)). Qed.
Lemma lem1270945 (n : nat) (m : nat) (p : nat) : (term5 m n p) = (term6 n m p).
Proof. exact (EQ_MP (@lem1270888 n m p) (@lem1270887 n m p)). Qed.
Lemma lem1270946 (y : nadd) (x : nadd) (n : nat) (B : nat) : (term21 x y n B) = (term22 y x n B).
Proof. exact (@lem1270945 (dest_nadd y n) (dest_nadd x n) B). Qed.
Lemma lem1270949 (y : nadd) (x : nadd) (B : nat) : (term23 x y B) = (term24 y x B).
Proof. exact (fun_ext (fun n : nat => @lem1270946 y x n B)). Qed.
Lemma lem1270950 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1270951 (y : nadd) (x : nadd) (B : nat) : (term25 x y B) = (term26 y x B).
Proof. exact (MK_COMB (@lem1270950) (@lem1270949 y x B)). Qed.
Lemma lem1270956 (y : nadd) (x : nadd) : (term27 x y) = (term28 y x).
Proof. exact (fun_ext (fun B : nat => @lem1270951 y x B)). Qed.
Lemma lem1270957 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1270958 (y : nadd) (x : nadd) : (term10 x y) = (term29 y x).
Proof. exact (MK_COMB (@lem1270957) (@lem1270956 y x)). Qed.
Lemma lem1270963 (y : nadd) (x : nadd) : (nadd_eq x y) = (term29 y x).
Proof. exact (TRANS (@lem1270935 x y) (@lem1270958 y x)). Qed.
Lemma lem1270964 (y : nadd) (x : nadd) : ((term17 y x) = (nadd_eq x y)) = ((term18 y x) = (term29 y x)).
Proof. exact (MK_COMB (@lem1270933 y x) (@lem1270963 y x)). Qed.
Lemma lem1270967 (x : nadd) (y : nadd) : ((term18 y x) = (term29 y x)) = ((term17 y x) = (nadd_eq x y)).
Proof. exact (SYM (@lem1270964 y x)). Qed.
Lemma lem1270968 (y : nadd) (x : nadd) (h1 : term18 y x) : term18 y x.
Proof. exact (h1). Qed.
Lemma lem1270969 (y : nadd) (x : nadd) (h1 : term14 y x) : term14 y x.
Proof. exact (h1). Qed.
Lemma lem1270970 (y : nadd) (x : nadd) (B2 : nat) (h1 : term30 y x B2) : term30 y x B2.
Proof. exact (h1). Qed.
Lemma lem1270971 (x : nadd) (y : nadd) (h1 : term14 x y) : term14 x y.
Proof. exact (h1). Qed.
Lemma lem1270972 (x : nadd) (y : nadd) (B1 : nat) (h1 : term30 x y B1) : term30 x y B1.
Proof. exact (h1). Qed.
Lemma lem1271030 (n : nat) (x : nadd) (y : nadd) (B1 : nat) (h1 : term30 x y B1) : term31 x y B1 n.
Proof. exact (@lem1270972 x y B1 h1 n). Qed.
Lemma lem1271031 (x : nadd) (y : nadd) (n : nat) (B1 : nat) : (term31 x y B1 n) = (term32 x y n B1).
Proof. exact (eq_refl (term31 x y B1 n)). Qed.
Lemma lem1271032 (n : nat) (x : nadd) (y : nadd) (B1 : nat) (h1 : term30 x y B1) : term32 x y n B1.
Proof. exact (EQ_MP (@lem1271031 x y n B1) (@lem1271030 n x y B1 h1)). Qed.
Lemma lem1271033 (h1 : term33) : term33.
Proof. exact (h1). Qed.
Lemma lem1271034 (m : nat) (h1 : term33) : term34 m.
Proof. exact (@lem1271033 h1 m). Qed.
Lemma lem1271035 (m : nat) : (term34 m) = (term35 m).
Proof. exact (eq_refl (term34 m)). Qed.
Lemma lem1271036 (m : nat) (h1 : term33) : term35 m.
Proof. exact (EQ_MP (@lem1271035 m) (@lem1271034 m h1)). Qed.
Lemma lem1271037 (m : nat) (n : nat) (h1 : term33) : term36 m n.
Proof. exact (@lem1271036 m h1 n). Qed.
Lemma lem1271038 (n : nat) (m : nat) : (term36 m n) = (term37 n m).
Proof. exact (eq_refl (term36 m n)). Qed.
Lemma lem1271039 (n : nat) (m : nat) (h1 : term33) : term37 n m.
Proof. exact (EQ_MP (@lem1271038 n m) (@lem1271037 m n h1)). Qed.
Lemma lem1271040 (n : nat) (m : nat) (p : nat) (h1 : term33) : term38 n m p.
Proof. exact (@lem1271039 n m h1 p). Qed.
Lemma lem1271041 (n : nat) (m : nat) (p : nat) : (term38 n m p) = (term39 n m p).
Proof. exact (eq_refl (term38 n m p)). Qed.
Lemma lem1271042 (n : nat) (m : nat) (p : nat) (h1 : term33) : term39 n m p.
Proof. exact (EQ_MP (@lem1271041 n m p) (@lem1271040 n m p h1)). Qed.
Lemma lem1271043 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem1271044 (p : nat) (m : nat) (n : nat) (h1 : term33) (h2 : Peano.le m n) : term40 n m p.
Proof. exact (@lem1271042 n m p h1 (@lem1271043 m n h2)). Qed.
Lemma lem1271045 (m : nat) (n : nat) (h1 : term33) (h2 : Peano.le m n) : term41 n m.
Proof. exact (fun p : nat => @lem1271044 p m n h1 h2). Qed.
Lemma lem1271046 (n : nat) (m : nat) (h1 : term33) : term42 n m.
Proof. exact (fun h0 : Peano.le m n => @lem1271045 m n h1 h0). Qed.
Lemma lem1271047 (m : nat) (h1 : term33) : term43 m.
Proof. exact (fun n : nat => @lem1271046 n m h1). Qed.
Lemma lem1271048 (h1 : term33) : term44.
Proof. exact (fun m : nat => @lem1271047 m h1). Qed.
Lemma lem1271049 : term45.
Proof. exact (fun h0 : term33 => @lem1271048 h0). Qed.
Lemma lem1271050 : term44.
Proof. exact (@lem1271049 (@lem272809)). Qed.
Lemma lem1271051 (m : nat) : term46 m.
Proof. exact (@lem1271050 m). Qed.
Lemma lem1271052 (m : nat) : (term46 m) = (term43 m).
Proof. exact (eq_refl (term46 m)). Qed.
Lemma lem1271053 (m : nat) : term43 m.
Proof. exact (EQ_MP (@lem1271052 m) (@lem1271051 m)). Qed.
Lemma lem1271054 (m : nat) (n : nat) : term47 m n.
Proof. exact (@lem1271053 m n). Qed.
Lemma lem1271055 (n : nat) (m : nat) : (term47 m n) = (term42 n m).
Proof. exact (eq_refl (term47 m n)). Qed.
Lemma lem1271058 (n : nat) (m : nat) : term42 n m.
Proof. exact (EQ_MP (@lem1271055 n m) (@lem1271054 m n)). Qed.
Lemma lem1271059 (y : nadd) (B1 : nat) (x : nadd) (n : nat) : term48 y B1 x n.
Proof. exact (@lem1271058 (term49 y n B1) (dest_nadd x n)). Qed.
Lemma lem1271060 (n : nat) (x : nadd) (y : nadd) (B1 : nat) (h1 : term30 x y B1) : term50 y B1 x n.
Proof. exact (@lem1271059 y B1 x n (@lem1271032 n x y B1 h1)). Qed.
Lemma lem1271061 (x : nadd) (y : nadd) (B1 : nat) (h1 : term30 x y B1) : term51 y B1 x.
Proof. exact (fun n : nat => @lem1271060 n x y B1 h1). Qed.
Lemma lem1271062 (y : nadd) (B1 : nat) (x : nadd) (h1 : term51 y B1 x) : term51 y B1 x.
Proof. exact (h1). Qed.
Lemma lem1271063 (n : nat) (y : nadd) (B1 : nat) (x : nadd) (h1 : term51 y B1 x) : term52 y B1 x n.
Proof. exact (@lem1271062 y B1 x h1 n). Qed.
Lemma lem1271064 (y : nadd) (B1 : nat) (x : nadd) (n : nat) : (term52 y B1 x n) = (term50 y B1 x n).
Proof. exact (eq_refl (term52 y B1 x n)). Qed.
Lemma lem1271065 (n : nat) (y : nadd) (B1 : nat) (x : nadd) (h1 : term51 y B1 x) : term50 y B1 x n.
Proof. exact (EQ_MP (@lem1271064 y B1 x n) (@lem1271063 n y B1 x h1)). Qed.
Lemma lem1271066 (n : nat) (p : nat) (y : nadd) (B1 : nat) (x : nadd) (h1 : term51 y B1 x) : term53 y B1 x n p.
Proof. exact (@lem1271065 n y B1 x h1 p). Qed.
Lemma lem1271067 (y : nadd) (B1 : nat) (x : nadd) (n : nat) (p : nat) : (term53 y B1 x n p) = (term54 y B1 x n p).
Proof. exact (eq_refl (term53 y B1 x n p)). Qed.
Lemma lem1271068 (n : nat) (p : nat) (y : nadd) (B1 : nat) (x : nadd) (h1 : term51 y B1 x) : term54 y B1 x n p.
Proof. exact (EQ_MP (@lem1271067 y B1 x n p) (@lem1271066 n p y B1 x h1)). Qed.
Lemma lem1271069 (y : nadd) (n : nat) (B1 : nat) (p : nat) (h1 : term55 y n B1 p) : term55 y n B1 p.
Proof. exact (h1). Qed.
Lemma lem1271070 (x : nadd) (y : nadd) (n : nat) (B1 : nat) (p : nat) (h1 : term51 y B1 x) (h2 : term55 y n B1 p) : term56 x n p.
Proof. exact (@lem1271068 n p y B1 x h1 (@lem1271069 y n B1 p h2)). Qed.
Lemma lem1271071 (x : nadd) (y : nadd) (n : nat) (B1 : nat) (p : nat) (h1 : term55 y n B1 p) : term57 y B1 x n p.
Proof. exact (fun h0 : term51 y B1 x => @lem1271070 x y n B1 p h0 h1). Qed.
Lemma lem1271072 (y : nadd) (B1 : nat) (x : nadd) (h1 : term51 y B1 x) : term51 y B1 x.
Proof. exact (h1). Qed.
Lemma lem1271073 (x : nadd) (y : nadd) (n : nat) (B1 : nat) (p : nat) (h1 : term51 y B1 x) (h2 : term55 y n B1 p) : term56 x n p.
Proof. exact (@lem1271071 x y n B1 p h2 (@lem1271072 y B1 x h1)). Qed.
Lemma lem1271074 (n : nat) (p : nat) (y : nadd) (B1 : nat) (x : nadd) (h1 : term51 y B1 x) : term54 y B1 x n p.
Proof. exact (fun h0 : term55 y n B1 p => @lem1271073 x y n B1 p h1 h0). Qed.
Lemma lem1271075 (n : nat) (y : nadd) (B1 : nat) (x : nadd) (h1 : term51 y B1 x) : term50 y B1 x n.
Proof. exact (fun p : nat => @lem1271074 n p y B1 x h1). Qed.
Lemma lem1271076 (y : nadd) (B1 : nat) (x : nadd) (h1 : term51 y B1 x) : term51 y B1 x.
Proof. exact (fun n : nat => @lem1271075 n y B1 x h1). Qed.
Lemma lem1271077 (y : nadd) (B1 : nat) (x : nadd) : term58 y B1 x.
Proof. exact (fun h0 : term51 y B1 x => @lem1271076 y B1 x h0). Qed.
Lemma lem1271078 (x : nadd) (y : nadd) (B1 : nat) (h1 : term30 x y B1) : term51 y B1 x.
Proof. exact (@lem1271077 y B1 x (@lem1271061 x y B1 h1)). Qed.
Lemma lem1271079 (n : nat) (x : nadd) (y : nadd) (B1 : nat) (h1 : term30 x y B1) : term52 y B1 x n.
Proof. exact (@lem1271078 x y B1 h1 n). Qed.
Lemma lem1271080 (y : nadd) (B1 : nat) (x : nadd) (n : nat) : (term52 y B1 x n) = (term50 y B1 x n).
Proof. exact (eq_refl (term52 y B1 x n)). Qed.
Lemma lem1271081 (n : nat) (x : nadd) (y : nadd) (B1 : nat) (h1 : term30 x y B1) : term50 y B1 x n.
Proof. exact (EQ_MP (@lem1271080 y B1 x n) (@lem1271079 n x y B1 h1)). Qed.
Lemma lem1271082 (n : nat) (p : nat) (x : nadd) (y : nadd) (B1 : nat) (h1 : term30 x y B1) : term53 y B1 x n p.
Proof. exact (@lem1271081 n x y B1 h1 p). Qed.
Lemma lem1271083 (y : nadd) (B1 : nat) (x : nadd) (n : nat) (p : nat) : (term53 y B1 x n p) = (term54 y B1 x n p).
Proof. exact (eq_refl (term53 y B1 x n p)). Qed.
Lemma lem1271086 (n : nat) (p : nat) (x : nadd) (y : nadd) (B1 : nat) (h1 : term30 x y B1) : term54 y B1 x n p.
Proof. exact (EQ_MP (@lem1271083 y B1 x n p) (@lem1271082 n p x y B1 h1)). Qed.
Lemma lem1271087 (n : nat) (B2 : nat) (x : nadd) (y : nadd) (B1 : nat) (h1 : term30 x y B1) : term59 x y n B1 B2.
Proof. exact (@lem1271086 n (term60 y n B1 B2) x y B1 h1). Qed.
Lemma lem1271088 (n : nat) (y : nadd) (x : nadd) (B2 : nat) (h1 : term30 y x B2) : term31 y x B2 n.
Proof. exact (@lem1270970 y x B2 h1 n). Qed.
Lemma lem1271089 (y : nadd) (x : nadd) (n : nat) (B2 : nat) : (term31 y x B2 n) = (term32 y x n B2).
Proof. exact (eq_refl (term31 y x B2 n)). Qed.
Lemma lem1271090 (n : nat) (y : nadd) (x : nadd) (B2 : nat) (h1 : term30 y x B2) : term32 y x n B2.
Proof. exact (EQ_MP (@lem1271089 y x n B2) (@lem1271088 n y x B2 h1)). Qed.
Lemma lem1271091 (h1 : term33) : term33.
Proof. exact (h1). Qed.
Lemma lem1271092 (m : nat) (h1 : term33) : term34 m.
Proof. exact (@lem1271091 h1 m). Qed.
Lemma lem1271093 (m : nat) : (term34 m) = (term35 m).
Proof. exact (eq_refl (term34 m)). Qed.
Lemma lem1271094 (m : nat) (h1 : term33) : term35 m.
Proof. exact (EQ_MP (@lem1271093 m) (@lem1271092 m h1)). Qed.
Lemma lem1271095 (m : nat) (n : nat) (h1 : term33) : term36 m n.
Proof. exact (@lem1271094 m h1 n). Qed.
Lemma lem1271096 (n : nat) (m : nat) : (term36 m n) = (term37 n m).
Proof. exact (eq_refl (term36 m n)). Qed.
Lemma lem1271097 (n : nat) (m : nat) (h1 : term33) : term37 n m.
Proof. exact (EQ_MP (@lem1271096 n m) (@lem1271095 m n h1)). Qed.
Lemma lem1271098 (n : nat) (m : nat) (p : nat) (h1 : term33) : term38 n m p.
Proof. exact (@lem1271097 n m h1 p). Qed.
Lemma lem1271099 (n : nat) (m : nat) (p : nat) : (term38 n m p) = (term39 n m p).
Proof. exact (eq_refl (term38 n m p)). Qed.
Lemma lem1271100 (n : nat) (m : nat) (p : nat) (h1 : term33) : term39 n m p.
Proof. exact (EQ_MP (@lem1271099 n m p) (@lem1271098 n m p h1)). Qed.
Lemma lem1271101 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem1271102 (p : nat) (m : nat) (n : nat) (h1 : term33) (h2 : Peano.le m n) : term40 n m p.
Proof. exact (@lem1271100 n m p h1 (@lem1271101 m n h2)). Qed.
Lemma lem1271103 (m : nat) (n : nat) (h1 : term33) (h2 : Peano.le m n) : term41 n m.
Proof. exact (fun p : nat => @lem1271102 p m n h1 h2). Qed.
Lemma lem1271104 (n : nat) (m : nat) (h1 : term33) : term42 n m.
Proof. exact (fun h0 : Peano.le m n => @lem1271103 m n h1 h0). Qed.
Lemma lem1271105 (m : nat) (h1 : term33) : term43 m.
Proof. exact (fun n : nat => @lem1271104 n m h1). Qed.
Lemma lem1271106 (h1 : term33) : term44.
Proof. exact (fun m : nat => @lem1271105 m h1). Qed.
Lemma lem1271107 : term45.
Proof. exact (fun h0 : term33 => @lem1271106 h0). Qed.
Lemma lem1271108 : term44.
Proof. exact (@lem1271107 (@lem272809)). Qed.
Lemma lem1271109 (m : nat) : term46 m.
Proof. exact (@lem1271108 m). Qed.
Lemma lem1271110 (m : nat) : (term46 m) = (term43 m).
Proof. exact (eq_refl (term46 m)). Qed.
Lemma lem1271111 (m : nat) : term43 m.
Proof. exact (EQ_MP (@lem1271110 m) (@lem1271109 m)). Qed.
Lemma lem1271112 (m : nat) (n : nat) : term47 m n.
Proof. exact (@lem1271111 m n). Qed.
Lemma lem1271113 (n : nat) (m : nat) : (term47 m n) = (term42 n m).
Proof. exact (eq_refl (term47 m n)). Qed.
Lemma lem1271116 (n : nat) (m : nat) : term42 n m.
Proof. exact (EQ_MP (@lem1271113 n m) (@lem1271112 m n)). Qed.
Lemma lem1271117 (x : nadd) (B2 : nat) (y : nadd) (n : nat) : term48 x B2 y n.
Proof. exact (@lem1271116 (term49 x n B2) (dest_nadd y n)). Qed.
Lemma lem1271118 (n : nat) (y : nadd) (x : nadd) (B2 : nat) (h1 : term30 y x B2) : term50 x B2 y n.
Proof. exact (@lem1271117 x B2 y n (@lem1271090 n y x B2 h1)). Qed.
Lemma lem1271119 (y : nadd) (x : nadd) (B2 : nat) (h1 : term30 y x B2) : term51 x B2 y.
Proof. exact (fun n : nat => @lem1271118 n y x B2 h1). Qed.
Lemma lem1271120 (x : nadd) (B2 : nat) (y : nadd) (h1 : term51 x B2 y) : term51 x B2 y.
Proof. exact (h1). Qed.
Lemma lem1271121 (n : nat) (x : nadd) (B2 : nat) (y : nadd) (h1 : term51 x B2 y) : term52 x B2 y n.
Proof. exact (@lem1271120 x B2 y h1 n). Qed.
Lemma lem1271122 (x : nadd) (B2 : nat) (y : nadd) (n : nat) : (term52 x B2 y n) = (term50 x B2 y n).
Proof. exact (eq_refl (term52 x B2 y n)). Qed.
Lemma lem1271123 (n : nat) (x : nadd) (B2 : nat) (y : nadd) (h1 : term51 x B2 y) : term50 x B2 y n.
Proof. exact (EQ_MP (@lem1271122 x B2 y n) (@lem1271121 n x B2 y h1)). Qed.
Lemma lem1271124 (n : nat) (p : nat) (x : nadd) (B2 : nat) (y : nadd) (h1 : term51 x B2 y) : term53 x B2 y n p.
Proof. exact (@lem1271123 n x B2 y h1 p). Qed.
Lemma lem1271125 (x : nadd) (B2 : nat) (y : nadd) (n : nat) (p : nat) : (term53 x B2 y n p) = (term54 x B2 y n p).
Proof. exact (eq_refl (term53 x B2 y n p)). Qed.
Lemma lem1271126 (n : nat) (p : nat) (x : nadd) (B2 : nat) (y : nadd) (h1 : term51 x B2 y) : term54 x B2 y n p.
Proof. exact (EQ_MP (@lem1271125 x B2 y n p) (@lem1271124 n p x B2 y h1)). Qed.
Lemma lem1271127 (x : nadd) (n : nat) (B2 : nat) (p : nat) (h1 : term55 x n B2 p) : term55 x n B2 p.
Proof. exact (h1). Qed.
Lemma lem1271128 (y : nadd) (x : nadd) (n : nat) (B2 : nat) (p : nat) (h1 : term51 x B2 y) (h2 : term55 x n B2 p) : term56 y n p.
Proof. exact (@lem1271126 n p x B2 y h1 (@lem1271127 x n B2 p h2)). Qed.
Lemma lem1271129 (y : nadd) (x : nadd) (n : nat) (B2 : nat) (p : nat) (h1 : term55 x n B2 p) : term57 x B2 y n p.
Proof. exact (fun h0 : term51 x B2 y => @lem1271128 y x n B2 p h0 h1). Qed.
Lemma lem1271130 (x : nadd) (B2 : nat) (y : nadd) (h1 : term51 x B2 y) : term51 x B2 y.
Proof. exact (h1). Qed.
Lemma lem1271131 (y : nadd) (x : nadd) (n : nat) (B2 : nat) (p : nat) (h1 : term51 x B2 y) (h2 : term55 x n B2 p) : term56 y n p.
Proof. exact (@lem1271129 y x n B2 p h2 (@lem1271130 x B2 y h1)). Qed.
Lemma lem1271132 (n : nat) (p : nat) (x : nadd) (B2 : nat) (y : nadd) (h1 : term51 x B2 y) : term54 x B2 y n p.
Proof. exact (fun h0 : term55 x n B2 p => @lem1271131 y x n B2 p h1 h0). Qed.
Lemma lem1271133 (n : nat) (x : nadd) (B2 : nat) (y : nadd) (h1 : term51 x B2 y) : term50 x B2 y n.
Proof. exact (fun p : nat => @lem1271132 n p x B2 y h1). Qed.
Lemma lem1271134 (x : nadd) (B2 : nat) (y : nadd) (h1 : term51 x B2 y) : term51 x B2 y.
Proof. exact (fun n : nat => @lem1271133 n x B2 y h1). Qed.
Lemma lem1271135 (x : nadd) (B2 : nat) (y : nadd) : term58 x B2 y.
Proof. exact (fun h0 : term51 x B2 y => @lem1271134 x B2 y h0). Qed.
Lemma lem1271136 (y : nadd) (x : nadd) (B2 : nat) (h1 : term30 y x B2) : term51 x B2 y.
Proof. exact (@lem1271135 x B2 y (@lem1271119 y x B2 h1)). Qed.
Lemma lem1271137 (n : nat) (y : nadd) (x : nadd) (B2 : nat) (h1 : term30 y x B2) : term52 x B2 y n.
Proof. exact (@lem1271136 y x B2 h1 n). Qed.
Lemma lem1271138 (x : nadd) (B2 : nat) (y : nadd) (n : nat) : (term52 x B2 y n) = (term50 x B2 y n).
Proof. exact (eq_refl (term52 x B2 y n)). Qed.
Lemma lem1271139 (n : nat) (y : nadd) (x : nadd) (B2 : nat) (h1 : term30 y x B2) : term50 x B2 y n.
Proof. exact (EQ_MP (@lem1271138 x B2 y n) (@lem1271137 n y x B2 h1)). Qed.
Lemma lem1271140 (n : nat) (p : nat) (y : nadd) (x : nadd) (B2 : nat) (h1 : term30 y x B2) : term53 x B2 y n p.
Proof. exact (@lem1271139 n y x B2 h1 p). Qed.
Lemma lem1271141 (x : nadd) (B2 : nat) (y : nadd) (n : nat) (p : nat) : (term53 x B2 y n p) = (term54 x B2 y n p).
Proof. exact (eq_refl (term53 x B2 y n p)). Qed.
Lemma lem1271144 (n : nat) (p : nat) (y : nadd) (x : nadd) (B2 : nat) (h1 : term30 y x B2) : term54 x B2 y n p.
Proof. exact (EQ_MP (@lem1271141 x B2 y n p) (@lem1271140 n p y x B2 h1)). Qed.
Lemma lem1271145 (n : nat) (B1 : nat) (y : nadd) (x : nadd) (B2 : nat) (h1 : term30 y x B2) : term61 y x n B1 B2.
Proof. exact (@lem1271144 n (term60 x n B1 B2) y x B2 h1). Qed.
Lemma lem1271154 (m : nat) : term62 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem1271155 (m : nat) : (term62 m) = (term63 m).
Proof. exact (eq_refl (term62 m)). Qed.
Lemma lem1271156 (m : nat) : term63 m.
Proof. exact (EQ_MP (@lem1271155 m) (@lem1271154 m)). Qed.
Lemma lem1271157 (m : nat) (n : nat) : term64 m n.
Proof. exact (@lem1271156 m n). Qed.
Lemma lem1271158 (m : nat) (n : nat) : (term64 m n) = (term65 m n).
Proof. exact (eq_refl (term64 m n)). Qed.
Lemma lem1271159 (m : nat) (n : nat) : term65 m n.
Proof. exact (EQ_MP (@lem1271158 m n) (@lem1271157 m n)). Qed.
Lemma lem1271160 (m : nat) (n : nat) : (term65 m n) = ((term65 m n) = True).
Proof. exact (@lem7 (term65 m n)). Qed.
Lemma lem1271171 (m : nat) : term66 m.
Proof. exact (@lem77960 m). Qed.
Lemma lem1271172 (m : nat) : (term66 m) = (term67 m).
Proof. exact (eq_refl (term66 m)). Qed.
Lemma lem1271173 (m : nat) : term67 m.
Proof. exact (EQ_MP (@lem1271172 m) (@lem1271171 m)). Qed.
Lemma lem1271174 (m : nat) (n : nat) : term68 m n.
Proof. exact (@lem1271173 m n). Qed.
Lemma lem1271175 (m : nat) (n : nat) : (term68 m n) = (term69 m n).
Proof. exact (eq_refl (term68 m n)). Qed.
Lemma lem1271176 (m : nat) (n : nat) : term69 m n.
Proof. exact (EQ_MP (@lem1271175 m n) (@lem1271174 m n)). Qed.
Lemma lem1271177 (m : nat) (n : nat) (p : nat) : term70 m n p.
Proof. exact (@lem1271176 m n p). Qed.
Lemma lem1271178 (m : nat) (n : nat) (p : nat) : (term70 m n p) = ((term71 m n p) = (term72 m n p)).
Proof. exact (eq_refl (term70 m n p)). Qed.
Lemma lem1271197 (m : nat) (n : nat) (p : nat) : (term71 m n p) = (term72 m n p).
Proof. exact (EQ_MP (@lem1271178 m n p) (@lem1271177 m n p)). Qed.
Lemma lem1271198 (y : nadd) (n : nat) (B1 : nat) (B2 : nat) : (term60 y n B1 B2) = (term73 y n B1 B2).
Proof. exact (@lem1271197 (dest_nadd y n) B1 B2). Qed.
Lemma lem1271199 (y : nadd) (n : nat) (B1 : nat) : (term74 y n B1) = (term74 y n B1).
Proof. exact (eq_refl (term74 y n B1)). Qed.
Lemma lem1271200 (y : nadd) (n : nat) (B1 : nat) (B2 : nat) : (term75 y n B1 B2) = (term76 y n B1 B2).
Proof. exact (MK_COMB (@lem1271199 y n B1) (@lem1271198 y n B1 B2)). Qed.
Lemma lem1271206 (m : nat) (n : nat) : (term65 m n) = True.
Proof. exact (EQ_MP (@lem1271160 m n) (@lem1271159 m n)). Qed.
Lemma lem1271207 (y : nadd) (n : nat) (B1 : nat) (B2 : nat) : (term76 y n B1 B2) = True.
Proof. exact (@lem1271206 (term49 y n B1) B2). Qed.
Lemma lem1271208 (y : nadd) (n : nat) (B1 : nat) (B2 : nat) : (term75 y n B1 B2) = True.
Proof. exact (TRANS (@lem1271200 y n B1 B2) (@lem1271207 y n B1 B2)). Qed.
Lemma lem1271209 (y : nadd) (n : nat) (B1 : nat) (B2 : nat) : True = (term75 y n B1 B2).
Proof. exact (SYM (@lem1271208 y n B1 B2)). Qed.
Lemma lem1271210 (y : nadd) (n : nat) (B1 : nat) (B2 : nat) : term75 y n B1 B2.
Proof. exact (EQ_MP (@lem1271209 y n B1 B2) (@lem0)). Qed.
Lemma lem1271219 (m : nat) : term62 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem1271220 (m : nat) : (term62 m) = (term63 m).
Proof. exact (eq_refl (term62 m)). Qed.
Lemma lem1271221 (m : nat) : term63 m.
Proof. exact (EQ_MP (@lem1271220 m) (@lem1271219 m)). Qed.
Lemma lem1271222 (m : nat) (n : nat) : term64 m n.
Proof. exact (@lem1271221 m n). Qed.
Lemma lem1271223 (m : nat) (n : nat) : (term64 m n) = (term65 m n).
Proof. exact (eq_refl (term64 m n)). Qed.
Lemma lem1271224 (m : nat) (n : nat) : term65 m n.
Proof. exact (EQ_MP (@lem1271223 m n) (@lem1271222 m n)). Qed.
Lemma lem1271225 (m : nat) (n : nat) : (term65 m n) = ((term65 m n) = True).
Proof. exact (@lem7 (term65 m n)). Qed.
Lemma lem1271227 (m : nat) : term77 m.
Proof. exact (@lem100973 m). Qed.
Lemma lem1271228 (m : nat) : (term77 m) = (term78 m).
Proof. exact (eq_refl (term77 m)). Qed.
Lemma lem1271229 (m : nat) : term78 m.
Proof. exact (EQ_MP (@lem1271228 m) (@lem1271227 m)). Qed.
Lemma lem1271230 (m : nat) (n : nat) : term79 m n.
Proof. exact (@lem1271229 m n). Qed.
Lemma lem1271231 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (eq_refl (term79 m n)). Qed.
Lemma lem1271232 (m : nat) (n : nat) : term80 m n.
Proof. exact (EQ_MP (@lem1271231 m n) (@lem1271230 m n)). Qed.
Lemma lem1271233 (m : nat) (n : nat) (p : nat) : term81 m n p.
Proof. exact (@lem1271232 m n p). Qed.
Lemma lem1271234 (p : nat) (m : nat) (n : nat) : (term81 m n p) = ((term82 m n p) = (Peano.le m n)).
Proof. exact (eq_refl (term81 m n p)). Qed.
Lemma lem1271236 (m : nat) : term66 m.
Proof. exact (@lem77960 m). Qed.
Lemma lem1271237 (m : nat) : (term66 m) = (term67 m).
Proof. exact (eq_refl (term66 m)). Qed.
Lemma lem1271238 (m : nat) : term67 m.
Proof. exact (EQ_MP (@lem1271237 m) (@lem1271236 m)). Qed.
Lemma lem1271239 (m : nat) (n : nat) : term68 m n.
Proof. exact (@lem1271238 m n). Qed.
Lemma lem1271240 (m : nat) (n : nat) : (term68 m n) = (term69 m n).
Proof. exact (eq_refl (term68 m n)). Qed.
Lemma lem1271241 (m : nat) (n : nat) : term69 m n.
Proof. exact (EQ_MP (@lem1271240 m n) (@lem1271239 m n)). Qed.
Lemma lem1271242 (m : nat) (n : nat) (p : nat) : term70 m n p.
Proof. exact (@lem1271241 m n p). Qed.
Lemma lem1271243 (m : nat) (n : nat) (p : nat) : (term70 m n p) = ((term71 m n p) = (term72 m n p)).
Proof. exact (eq_refl (term70 m n p)). Qed.
Lemma lem1271262 (m : nat) (n : nat) (p : nat) : (term71 m n p) = (term72 m n p).
Proof. exact (EQ_MP (@lem1271243 m n p) (@lem1271242 m n p)). Qed.
Lemma lem1271263 (x : nadd) (n : nat) (B1 : nat) (B2 : nat) : (term60 x n B1 B2) = (term73 x n B1 B2).
Proof. exact (@lem1271262 (dest_nadd x n) B1 B2). Qed.
Lemma lem1271264 (x : nadd) (n : nat) (B2 : nat) : (term74 x n B2) = (term74 x n B2).
Proof. exact (eq_refl (term74 x n B2)). Qed.
Lemma lem1271265 (x : nadd) (n : nat) (B1 : nat) (B2 : nat) : (term83 x n B1 B2) = (term84 x n B1 B2).
Proof. exact (MK_COMB (@lem1271264 x n B2) (@lem1271263 x n B1 B2)). Qed.
Lemma lem1271267 (p : nat) (m : nat) (n : nat) : (term82 m n p) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1271234 p m n) (@lem1271233 m n p)). Qed.
Lemma lem1271268 (B2 : nat) (x : nadd) (n : nat) (B1 : nat) : (term84 x n B1 B2) = (term85 x n B1).
Proof. exact (@lem1271267 B2 (dest_nadd x n) (term49 x n B1)). Qed.
Lemma lem1271272 (m : nat) (n : nat) : (term65 m n) = True.
Proof. exact (EQ_MP (@lem1271225 m n) (@lem1271224 m n)). Qed.
Lemma lem1271273 (x : nadd) (n : nat) (B1 : nat) : (term85 x n B1) = True.
Proof. exact (@lem1271272 (dest_nadd x n) B1). Qed.
Lemma lem1271274 (x : nadd) (n : nat) (B1 : nat) (B2 : nat) : (term84 x n B1 B2) = True.
Proof. exact (TRANS (@lem1271268 B2 x n B1) (@lem1271273 x n B1)). Qed.
Lemma lem1271275 (x : nadd) (n : nat) (B1 : nat) (B2 : nat) : (term83 x n B1 B2) = True.
Proof. exact (TRANS (@lem1271265 x n B1 B2) (@lem1271274 x n B1 B2)). Qed.
Lemma lem1271276 (x : nadd) (n : nat) (B1 : nat) (B2 : nat) : True = (term83 x n B1 B2).
Proof. exact (SYM (@lem1271275 x n B1 B2)). Qed.
Lemma lem1271277 (x : nadd) (n : nat) (B1 : nat) (B2 : nat) : term83 x n B1 B2.
Proof. exact (EQ_MP (@lem1271276 x n B1 B2) (@lem0)). Qed.
Lemma lem1271278 (n : nat) (B1 : nat) (y : nadd) (x : nadd) (B2 : nat) (h1 : term30 y x B2) : term86 y x n B1 B2.
Proof. exact (@lem1271145 n B1 y x B2 h1 (@lem1271277 x n B1 B2)). Qed.
Lemma lem1271279 (n : nat) (B2 : nat) (x : nadd) (y : nadd) (B1 : nat) (h1 : term30 x y B1) : term86 x y n B1 B2.
Proof. exact (@lem1271087 n B2 x y B1 h1 (@lem1271210 y n B1 B2)). Qed.
Lemma lem1271280 (n : nat) (B1 : nat) (y : nadd) (x : nadd) (B2 : nat) (h1 : term30 x y B1) (h2 : term30 y x B2) : term87 y x n B1 B2.
Proof. exact (conj (@lem1271279 n B2 x y B1 h1) (@lem1271278 n B1 y x B2 h2)). Qed.
Lemma lem1271285 (B1 : nat) (y : nadd) (x : nadd) (B2 : nat) (h1 : term30 x y B1) (h2 : term30 y x B2) : term88 y x B1 B2.
Proof. exact (fun n : nat => @lem1271280 n B1 y x B2 h1 h2). Qed.
Lemma lem1271286 (B1 : nat) (y : nadd) (x : nadd) (B2 : nat) (h1 : term30 x y B1) (h2 : term30 y x B2) : term29 y x.
Proof. exact (ex_intro (term28 y x) (Nat.add B1 B2) (@lem1271285 B1 y x B2 h1 h2)). Qed.
Lemma lem1271287 (y : nadd) (x : nadd) (h1 : term18 y x) : term14 y x.
Proof. exact (proj2 (@lem1270968 y x h1)). Qed.
Lemma lem1271288 (y : nadd) (x : nadd) (h1 : term18 y x) : term14 x y.
Proof. exact (proj1 (@lem1270968 y x h1)). Qed.
Lemma lem1271289 (B1 : nat) (y : nadd) (x : nadd) (h1 : term30 x y B1) (h2 : term14 y x) : term29 y x.
Proof. exact (ex_elim (@lem1270969 y x h2) (fun B2 : nat => fun h0 : term89 y x B2 => @lem1271286 B1 y x B2 h1 h0)). Qed.
Lemma lem1271290 (y : nadd) (x : nadd) (h1 : term14 x y) (h2 : term14 y x) : term29 y x.
Proof. exact (ex_elim (@lem1270971 x y h1) (fun B1 : nat => fun h0 : term89 x y B1 => @lem1271289 B1 y x h0 h2)). Qed.
Lemma lem1271291 (y : nadd) (x : nadd) (h1 : term14 x y) (h2 : term18 y x) : (term14 y x) = (term29 y x).
Proof. exact (prop_ext (fun h3 : term14 y x => @lem1271290 y x h1 h3) (fun h3 : term29 y x => @lem1271287 y x h2)). Qed.
Lemma lem1271292 (y : nadd) (x : nadd) (h1 : term14 x y) (h2 : term18 y x) : term29 y x.
Proof. exact (EQ_MP (@lem1271291 y x h1 h2) (@lem1271287 y x h2)). Qed.
Lemma lem1271293 (y : nadd) (x : nadd) (h1 : term18 y x) : (term14 x y) = (term29 y x).
Proof. exact (prop_ext (fun h2 : term14 x y => @lem1271292 y x h2 h1) (fun h2 : term29 y x => @lem1271288 y x h1)). Qed.
Lemma lem1271294 (y : nadd) (x : nadd) (h1 : term18 y x) : term29 y x.
Proof. exact (EQ_MP (@lem1271293 y x h1) (@lem1271288 y x h1)). Qed.
Lemma lem1271295 (y : nadd) (x : nadd) : term90 y x.
Proof. exact (fun h0 : term18 y x => @lem1271294 y x h0). Qed.
Lemma lem1271296 (y : nadd) (x : nadd) (h1 : term29 y x) : term29 y x.
Proof. exact (h1). Qed.
Lemma lem1271297 (y : nadd) (x : nadd) (B : nat) (h1 : term26 y x B) : term26 y x B.
Proof. exact (h1). Qed.
Lemma lem1271298 (n : nat) (y : nadd) (x : nadd) (B : nat) (h1 : term26 y x B) : term91 y x B n.
Proof. exact (@lem1271297 y x B h1 n). Qed.
Lemma lem1271299 (y : nadd) (x : nadd) (n : nat) (B : nat) : (term91 y x B n) = (term22 y x n B).
Proof. exact (eq_refl (term91 y x B n)). Qed.
Lemma lem1271300 (n : nat) (y : nadd) (x : nadd) (B : nat) (h1 : term26 y x B) : term22 y x n B.
Proof. exact (EQ_MP (@lem1271299 y x n B) (@lem1271298 n y x B h1)). Qed.
Lemma lem1271304 (n : nat) (y : nadd) (x : nadd) (B : nat) (h1 : term26 y x B) : term32 x y n B.
Proof. exact (proj1 (@lem1271300 n y x B h1)). Qed.
Lemma lem1271305 (x : nadd) (y : nadd) (n : nat) (B : nat) : (term32 x y n B) = ((term32 x y n B) = True).
Proof. exact (@lem7 (term32 x y n B)). Qed.
Lemma lem1271312 (n : nat) (y : nadd) (x : nadd) (B : nat) (h1 : term26 y x B) : (term32 x y n B) = True.
Proof. exact (EQ_MP (@lem1271305 x y n B) (@lem1271304 n y x B h1)). Qed.
Lemma lem1271313 (y : nadd) (x : nadd) (B : nat) (h1 : term26 y x B) : (term92 x y B) = term93.
Proof. exact (fun_ext (fun n : nat => @lem1271312 n y x B h1)). Qed.
Lemma lem1271314 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1271315 (y : nadd) (x : nadd) (B : nat) (h1 : term26 y x B) : (term30 x y B) = term94.
Proof. exact (MK_COMB (@lem1271314) (@lem1271313 y x B h1)). Qed.
Lemma lem1271317 {A : Type'} (t : Prop) : (term95 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1271318 (t : Prop) : (term96 t) = t.
Proof. exact (@lem1271317 nat t). Qed.
Lemma lem1271319 : term94 = True.
Proof. exact (@lem1271318 True). Qed.
Lemma lem1271320 (y : nadd) (x : nadd) (B : nat) (h1 : term26 y x B) : (term30 x y B) = True.
Proof. exact (TRANS (@lem1271315 y x B h1) (@lem1271319)). Qed.
Lemma lem1271321 (y : nadd) (x : nadd) (B : nat) (h1 : term26 y x B) : True = (term30 x y B).
Proof. exact (SYM (@lem1271320 y x B h1)). Qed.
Lemma lem1271322 (y : nadd) (x : nadd) (B : nat) (h1 : term26 y x B) : term30 x y B.
Proof. exact (EQ_MP (@lem1271321 y x B h1) (@lem0)). Qed.
Lemma lem1271323 (n : nat) (y : nadd) (x : nadd) (B : nat) (h1 : term26 y x B) : term91 y x B n.
Proof. exact (@lem1271297 y x B h1 n). Qed.
Lemma lem1271324 (y : nadd) (x : nadd) (n : nat) (B : nat) : (term91 y x B n) = (term22 y x n B).
Proof. exact (eq_refl (term91 y x B n)). Qed.
Lemma lem1271325 (n : nat) (y : nadd) (x : nadd) (B : nat) (h1 : term26 y x B) : term22 y x n B.
Proof. exact (EQ_MP (@lem1271324 y x n B) (@lem1271323 n y x B h1)). Qed.
Lemma lem1271326 (n : nat) (y : nadd) (x : nadd) (B : nat) (h1 : term26 y x B) : term32 y x n B.
Proof. exact (proj2 (@lem1271325 n y x B h1)). Qed.
Lemma lem1271327 (y : nadd) (x : nadd) (n : nat) (B : nat) : (term32 y x n B) = ((term32 y x n B) = True).
Proof. exact (@lem7 (term32 y x n B)). Qed.
Lemma lem1271337 (n : nat) (y : nadd) (x : nadd) (B : nat) (h1 : term26 y x B) : (term32 y x n B) = True.
Proof. exact (EQ_MP (@lem1271327 y x n B) (@lem1271326 n y x B h1)). Qed.
Lemma lem1271338 (y : nadd) (x : nadd) (B : nat) (h1 : term26 y x B) : (term92 y x B) = term93.
Proof. exact (fun_ext (fun n : nat => @lem1271337 n y x B h1)). Qed.
Lemma lem1271339 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1271340 (y : nadd) (x : nadd) (B : nat) (h1 : term26 y x B) : (term30 y x B) = term94.
Proof. exact (MK_COMB (@lem1271339) (@lem1271338 y x B h1)). Qed.
Lemma lem1271342 {A : Type'} (t : Prop) : (term95 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1271343 (t : Prop) : (term96 t) = t.
Proof. exact (@lem1271342 nat t). Qed.
Lemma lem1271344 : term94 = True.
Proof. exact (@lem1271343 True). Qed.
Lemma lem1271345 (y : nadd) (x : nadd) (B : nat) (h1 : term26 y x B) : (term30 y x B) = True.
Proof. exact (TRANS (@lem1271340 y x B h1) (@lem1271344)). Qed.
Lemma lem1271346 (y : nadd) (x : nadd) (B : nat) (h1 : term26 y x B) : True = (term30 y x B).
Proof. exact (SYM (@lem1271345 y x B h1)). Qed.
Lemma lem1271347 (y : nadd) (x : nadd) (B : nat) (h1 : term26 y x B) : term30 y x B.
Proof. exact (EQ_MP (@lem1271346 y x B h1) (@lem0)). Qed.
Lemma lem1271348 (y : nadd) (x : nadd) (B : nat) (h1 : term26 y x B) : term14 y x.
Proof. exact (ex_intro (term89 y x) B (@lem1271347 y x B h1)). Qed.
Lemma lem1271349 (y : nadd) (x : nadd) (B : nat) (h1 : term26 y x B) : term14 x y.
Proof. exact (ex_intro (term89 x y) B (@lem1271322 y x B h1)). Qed.
Lemma lem1271350 (y : nadd) (x : nadd) (B : nat) (h1 : term26 y x B) : term18 y x.
Proof. exact (conj (@lem1271349 y x B h1) (@lem1271348 y x B h1)). Qed.
Lemma lem1271351 (y : nadd) (x : nadd) (h1 : term29 y x) : term18 y x.
Proof. exact (ex_elim (@lem1271296 y x h1) (fun B : nat => fun h0 : term28 y x B => @lem1271350 y x B h0)). Qed.
Lemma lem1271352 (y : nadd) (x : nadd) : term97 y x.
Proof. exact (fun h0 : term29 y x => @lem1271351 y x h0). Qed.
Lemma lem1271353 (y : nadd) (x : nadd) : term98 y x.
Proof. exact (conj (@lem1271295 y x) (@lem1271352 y x)). Qed.
Lemma lem1271354 (y : nadd) (x : nadd) : (term98 y x) = ((term18 y x) = (term29 y x)).
Proof. exact (@lem32 (term18 y x) (term29 y x)). Qed.
Lemma lem1271355 (y : nadd) (x : nadd) : (term18 y x) = (term29 y x).
Proof. exact (EQ_MP (@lem1271354 y x) (@lem1271353 y x)). Qed.
Lemma lem1271356 (x : nadd) (y : nadd) : (term17 y x) = (nadd_eq x y).
Proof. exact (EQ_MP (@lem1270967 x y) (@lem1271355 y x)). Qed.
Lemma lem1271361 (x : nadd) : term99 x.
Proof. exact (fun y : nadd => @lem1271356 x y). Qed.
Lemma lem1271366 : term100.
Proof. exact (fun x : nadd => @lem1271361 x). Qed.
