Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_ADD_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1338912_spec.
Require Import thm1338986_spec.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Require Import thm1344313_spec.
Require Import thm1344314_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem1595896 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1595897 (x : real) : term1 x.
Proof. exact (@lem1595896 (term2 x)). Qed.
Lemma lem1595898 (x : real) : (term3 x) = (term4 x).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem1595899 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1595900 (x : real) : (term5 x) = (term6 x).
Proof. exact (MK_COMB (@lem1595899) (@lem1595898 x)). Qed.
Lemma lem1595901 (m : nat) (x : real) : (term7 x m) = (term8 m x).
Proof. exact (eq_refl (term7 x m)). Qed.
Lemma lem1595902 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1595903 (m : nat) (x : real) : (term9 x m) = (term10 m x).
Proof. exact (MK_COMB (@lem1595902) (@lem1595901 m x)). Qed.
Lemma lem1595904 (m : nat) (x : real) : (term11 x m) = (term12 m x).
Proof. exact (eq_refl (term11 x m)). Qed.
Lemma lem1595905 (m : nat) (x : real) : (term13 x m) = (term14 m x).
Proof. exact (MK_COMB (@lem1595903 m x) (@lem1595904 m x)). Qed.
Lemma lem1595906 (x : real) : (term15 x) = (term16 x).
Proof. exact (fun_ext (fun m : nat => @lem1595905 m x)). Qed.
Lemma lem1595907 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1595908 (x : real) : (term17 x) = (term18 x).
Proof. exact (MK_COMB (@lem1595907) (@lem1595906 x)). Qed.
Lemma lem1595909 (x : real) : (term19 x) = (term20 x).
Proof. exact (MK_COMB (@lem1595900 x) (@lem1595908 x)). Qed.
Lemma lem1595910 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1595911 (x : real) : (term21 x) = (term22 x).
Proof. exact (MK_COMB (@lem1595910) (@lem1595909 x)). Qed.
Lemma lem1595912 (m : nat) (x : real) : (term7 x m) = (term8 m x).
Proof. exact (eq_refl (term7 x m)). Qed.
Lemma lem1595913 (x : real) : (term23 x) = (term2 x).
Proof. exact (fun_ext (fun m : nat => @lem1595912 m x)). Qed.
Lemma lem1595914 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1595915 (x : real) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem1595914) (@lem1595913 x)). Qed.
Lemma lem1595916 (x : real) : (term1 x) = (term26 x).
Proof. exact (MK_COMB (@lem1595911 x) (@lem1595915 x)). Qed.
Lemma lem1595917 (x : real) : term26 x.
Proof. exact (EQ_MP (@lem1595916 x) (@lem1595897 x)). Qed.
Lemma lem1595918 (m : nat) (x : real) (h1 : term8 m x) : term8 m x.
Proof. exact (h1). Qed.
Lemma lem1595928 (x : real) : term27 x.
Proof. exact (@lem1338986 x). Qed.
Lemma lem1595929 (x : real) : (term27 x) = ((term28 x) = x).
Proof. exact (eq_refl (term27 x)). Qed.
Lemma lem1595956 : term29.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem1595957 (n : nat) : term30 n.
Proof. exact (@lem1595956 n). Qed.
Lemma lem1595958 (n : nat) : (term30 n) = ((term31 n) = n).
Proof. exact (eq_refl (term30 n)). Qed.
Lemma lem1595967 (n : nat) : (term31 n) = n.
Proof. exact (EQ_MP (@lem1595958 n) (@lem1595957 n)). Qed.
Lemma lem1595968 (x : real) : (real_pow x) = (real_pow x).
Proof. exact (eq_refl (real_pow x)). Qed.
Lemma lem1595969 (x : real) (n : nat) : (term32 x n) = (real_pow x n).
Proof. exact (MK_COMB (@lem1595968 x) (@lem1595967 n)). Qed.
Lemma lem1595970 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1595971 (x : real) (n : nat) : (term33 x n) = (term34 x n).
Proof. exact (MK_COMB (@lem1595970) (@lem1595969 x n)). Qed.
Lemma lem1595973 (x : real) : (term35 x) = term36.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1595974 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1595975 (x : real) : (term37 x) = term38.
Proof. exact (MK_COMB (@lem1595974) (@lem1595973 x)). Qed.
Lemma lem1595976 (x : real) (n : nat) : (real_pow x n) = (real_pow x n).
Proof. exact (eq_refl (real_pow x n)). Qed.
Lemma lem1595977 (x : real) (n : nat) : (term39 x n) = (term40 x n).
Proof. exact (MK_COMB (@lem1595975 x) (@lem1595976 x n)). Qed.
Lemma lem1595979 (x : real) : (term28 x) = x.
Proof. exact (EQ_MP (@lem1595929 x) (@lem1595928 x)). Qed.
Lemma lem1595980 (x : real) (n : nat) : (term40 x n) = (real_pow x n).
Proof. exact (@lem1595979 (real_pow x n)). Qed.
Lemma lem1595981 (x : real) (n : nat) : (term39 x n) = (real_pow x n).
Proof. exact (TRANS (@lem1595977 x n) (@lem1595980 x n)). Qed.
Lemma lem1595982 (x : real) (n : nat) : ((term32 x n) = (term39 x n)) = ((real_pow x n) = (real_pow x n)).
Proof. exact (MK_COMB (@lem1595971 x n) (@lem1595981 x n)). Qed.
Lemma lem1595984 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1595985 (x : real) : (x = x) = True.
Proof. exact (@lem1595984 real x). Qed.
Lemma lem1595986 (x : real) (n : nat) : ((real_pow x n) = (real_pow x n)) = True.
Proof. exact (@lem1595985 (real_pow x n)). Qed.
Lemma lem1595987 (x : real) (n : nat) : ((term32 x n) = (term39 x n)) = True.
Proof. exact (TRANS (@lem1595982 x n) (@lem1595986 x n)). Qed.
Lemma lem1595988 (x : real) : (term41 x) = term42.
Proof. exact (fun_ext (fun n : nat => @lem1595987 x n)). Qed.
Lemma lem1595989 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1595990 (x : real) : (term4 x) = term43.
Proof. exact (MK_COMB (@lem1595989) (@lem1595988 x)). Qed.
Lemma lem1595992 {A : Type'} (t : Prop) : (term44 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1595993 (t : Prop) : (term45 t) = t.
Proof. exact (@lem1595992 nat t). Qed.
Lemma lem1595994 : term43 = True.
Proof. exact (@lem1595993 True). Qed.
Lemma lem1595995 (x : real) : (term4 x) = True.
Proof. exact (TRANS (@lem1595990 x) (@lem1595994)). Qed.
Lemma lem1595996 (x : real) : True = (term4 x).
Proof. exact (SYM (@lem1595995 x)). Qed.
Lemma lem1595997 (x : real) : term4 x.
Proof. exact (EQ_MP (@lem1595996 x) (@lem0)). Qed.
Lemma lem1595998 (x : real) : term46 x.
Proof. exact (@lem1338912 x). Qed.
Lemma lem1595999 (x : real) : (term46 x) = (term47 x).
Proof. exact (eq_refl (term46 x)). Qed.
Lemma lem1596000 (x : real) : term47 x.
Proof. exact (EQ_MP (@lem1595999 x) (@lem1595998 x)). Qed.
Lemma lem1596001 (x : real) (y : real) : term48 x y.
Proof. exact (@lem1596000 x y). Qed.
Lemma lem1596002 (x : real) (y : real) : (term48 x y) = (term49 x y).
Proof. exact (eq_refl (term48 x y)). Qed.
Lemma lem1596003 (x : real) (y : real) : term49 x y.
Proof. exact (EQ_MP (@lem1596002 x y) (@lem1596001 x y)). Qed.
Lemma lem1596004 (x : real) (y : real) (z : real) : term50 x y z.
Proof. exact (@lem1596003 x y z). Qed.
Lemma lem1596005 (x : real) (y : real) (z : real) : (term50 x y z) = ((term51 x y z) = (term52 x y z)).
Proof. exact (eq_refl (term50 x y z)). Qed.
Lemma lem1596010 (x : real) : term53 x.
Proof. exact (EQ_MP (@lem1344314 x) (@lem1344313 x)). Qed.
Lemma lem1596011 (x : real) (n : nat) : term54 x n.
Proof. exact (@lem1596010 x n). Qed.
Lemma lem1596012 (x : real) (n : nat) : (term54 x n) = ((term55 x n) = (term56 x n)).
Proof. exact (eq_refl (term54 x n)). Qed.
Lemma lem1596015 : term57.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem1596016 : term58.
Proof. exact (proj2 (@lem1596015)). Qed.
Lemma lem1596024 : term59.
Proof. exact (proj1 (@lem1596016)). Qed.
Lemma lem1596025 (m : nat) : term60 m.
Proof. exact (@lem1596024 m). Qed.
Lemma lem1596026 (m : nat) : (term60 m) = (term61 m).
Proof. exact (eq_refl (term60 m)). Qed.
Lemma lem1596027 (m : nat) : term61 m.
Proof. exact (EQ_MP (@lem1596026 m) (@lem1596025 m)). Qed.
Lemma lem1596028 (m : nat) (n : nat) : term62 m n.
Proof. exact (@lem1596027 m n). Qed.
Lemma lem1596029 (m : nat) (n : nat) : (term62 m n) = ((term63 m n) = (term64 m n)).
Proof. exact (eq_refl (term62 m n)). Qed.
Lemma lem1596039 (n : nat) (m : nat) (x : real) (h1 : term8 m x) : term65 m x n.
Proof. exact (@lem1595918 m x h1 n). Qed.
Lemma lem1596040 (m : nat) (x : real) (n : nat) : (term65 m x n) = ((term66 x m n) = (term67 m x n)).
Proof. exact (eq_refl (term65 m x n)). Qed.
Lemma lem1596049 (m : nat) (n : nat) : (term63 m n) = (term64 m n).
Proof. exact (EQ_MP (@lem1596029 m n) (@lem1596028 m n)). Qed.
Lemma lem1596050 (x : real) : (real_pow x) = (real_pow x).
Proof. exact (eq_refl (real_pow x)). Qed.
Lemma lem1596051 (x : real) (m : nat) (n : nat) : (term68 x m n) = (term69 x m n).
Proof. exact (MK_COMB (@lem1596050 x) (@lem1596049 m n)). Qed.
Lemma lem1596053 (x : real) (n : nat) : (term55 x n) = (term56 x n).
Proof. exact (EQ_MP (@lem1596012 x n) (@lem1596011 x n)). Qed.
Lemma lem1596054 (x : real) (m : nat) (n : nat) : (term69 x m n) = (term70 x m n).
Proof. exact (@lem1596053 x (Nat.add m n)). Qed.
Lemma lem1596056 (n : nat) (m : nat) (x : real) (h1 : term8 m x) : (term66 x m n) = (term67 m x n).
Proof. exact (EQ_MP (@lem1596040 m x n) (@lem1596039 n m x h1)). Qed.
Lemma lem1596057 (x : real) : (real_mul x) = (real_mul x).
Proof. exact (eq_refl (real_mul x)). Qed.
Lemma lem1596058 (n : nat) (m : nat) (x : real) (h1 : term8 m x) : (term70 x m n) = (term71 m x n).
Proof. exact (MK_COMB (@lem1596057 x) (@lem1596056 n m x h1)). Qed.
Lemma lem1596060 (x : real) (y : real) (z : real) : (term51 x y z) = (term52 x y z).
Proof. exact (EQ_MP (@lem1596005 x y z) (@lem1596004 x y z)). Qed.
Lemma lem1596061 (m : nat) (x : real) (n : nat) : (term71 m x n) = (term72 m x n).
Proof. exact (@lem1596060 x (real_pow x m) (real_pow x n)). Qed.
Lemma lem1596062 (n : nat) (m : nat) (x : real) (h1 : term8 m x) : (term70 x m n) = (term72 m x n).
Proof. exact (TRANS (@lem1596058 n m x h1) (@lem1596061 m x n)). Qed.
Lemma lem1596063 (n : nat) (m : nat) (x : real) (h1 : term8 m x) : (term69 x m n) = (term72 m x n).
Proof. exact (TRANS (@lem1596054 x m n) (@lem1596062 n m x h1)). Qed.
Lemma lem1596064 (n : nat) (m : nat) (x : real) (h1 : term8 m x) : (term68 x m n) = (term72 m x n).
Proof. exact (TRANS (@lem1596051 x m n) (@lem1596063 n m x h1)). Qed.
Lemma lem1596065 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1596066 (n : nat) (m : nat) (x : real) (h1 : term8 m x) : (term73 x m n) = (term74 m x n).
Proof. exact (MK_COMB (@lem1596065) (@lem1596064 n m x h1)). Qed.
Lemma lem1596068 (x : real) (n : nat) : (term55 x n) = (term56 x n).
Proof. exact (EQ_MP (@lem1596012 x n) (@lem1596011 x n)). Qed.
Lemma lem1596069 (x : real) (m : nat) : (term55 x m) = (term56 x m).
Proof. exact (@lem1596068 x m). Qed.
Lemma lem1596070 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1596071 (x : real) (m : nat) : (term75 x m) = (term76 x m).
Proof. exact (MK_COMB (@lem1596070) (@lem1596069 x m)). Qed.
Lemma lem1596072 (x : real) (n : nat) : (real_pow x n) = (real_pow x n).
Proof. exact (eq_refl (real_pow x n)). Qed.
Lemma lem1596073 (m : nat) (x : real) (n : nat) : (term77 m x n) = (term72 m x n).
Proof. exact (MK_COMB (@lem1596071 x m) (@lem1596072 x n)). Qed.
Lemma lem1596074 (n : nat) (m : nat) (x : real) (h1 : term8 m x) : ((term68 x m n) = (term77 m x n)) = ((term72 m x n) = (term72 m x n)).
Proof. exact (MK_COMB (@lem1596066 n m x h1) (@lem1596073 m x n)). Qed.
Lemma lem1596076 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1596077 (x : real) : (x = x) = True.
Proof. exact (@lem1596076 real x). Qed.
Lemma lem1596078 (m : nat) (x : real) (n : nat) : ((term72 m x n) = (term72 m x n)) = True.
Proof. exact (@lem1596077 (term72 m x n)). Qed.
Lemma lem1596079 (n : nat) (m : nat) (x : real) (h1 : term8 m x) : ((term68 x m n) = (term77 m x n)) = True.
Proof. exact (TRANS (@lem1596074 n m x h1) (@lem1596078 m x n)). Qed.
Lemma lem1596080 (m : nat) (x : real) (h1 : term8 m x) : (term78 m x) = term42.
Proof. exact (fun_ext (fun n : nat => @lem1596079 n m x h1)). Qed.
Lemma lem1596081 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1596082 (m : nat) (x : real) (h1 : term8 m x) : (term12 m x) = term43.
Proof. exact (MK_COMB (@lem1596081) (@lem1596080 m x h1)). Qed.
Lemma lem1596084 {A : Type'} (t : Prop) : (term44 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1596085 (t : Prop) : (term45 t) = t.
Proof. exact (@lem1596084 nat t). Qed.
Lemma lem1596086 : term43 = True.
Proof. exact (@lem1596085 True). Qed.
Lemma lem1596087 (m : nat) (x : real) (h1 : term8 m x) : (term12 m x) = True.
Proof. exact (TRANS (@lem1596082 m x h1) (@lem1596086)). Qed.
Lemma lem1596088 (m : nat) (x : real) (h1 : term8 m x) : True = (term12 m x).
Proof. exact (SYM (@lem1596087 m x h1)). Qed.
Lemma lem1596089 (m : nat) (x : real) (h1 : term8 m x) : term12 m x.
Proof. exact (EQ_MP (@lem1596088 m x h1) (@lem0)). Qed.
Lemma lem1596090 (m : nat) (x : real) : term14 m x.
Proof. exact (fun h0 : term8 m x => @lem1596089 m x h0). Qed.
Lemma lem1596095 (x : real) : term18 x.
Proof. exact (fun m : nat => @lem1596090 m x). Qed.
Lemma lem1596096 (x : real) : term20 x.
Proof. exact (conj (@lem1595997 x) (@lem1596095 x)). Qed.
Lemma lem1596097 (x : real) : term25 x.
Proof. exact (@lem1595917 x (@lem1596096 x)). Qed.
Lemma lem1596102 : term79.
Proof. exact (fun x : real => @lem1596097 x). Qed.
