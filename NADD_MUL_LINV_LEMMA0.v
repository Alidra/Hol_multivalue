Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_MUL_LINV_LEMMA0_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import BOUNDS_IGNORE_spec.
Require Import DIVISION_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import LE_0_spec.
Require Import LE_ADD_spec.
Require Import LE_MULT_LCANCEL_spec.
Require Import LE_MULT_RCANCEL_spec.
Require Import LE_REFL_spec.
Require Import LE_TRANS_spec.
Require Import MULT_ASSOC_spec.
Require Import MULT_CLAUSES_spec.
Require Import MULT_SYM_spec.
Require Import NADD_LBOUND_spec.
Require Import NOT_SUC_spec.
Require Import nadd_rinv_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1822_spec.
Require Import thm1832_spec.
Require Import thm1834_spec.
Require Import thm1842_spec.
Require Import thm1856_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm89498_spec.
Lemma lem1300974 (m : nat) : term0 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem1300975 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1300976 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1300975 m) (@lem1300974 m)). Qed.
Lemma lem1300977 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1300976 m n). Qed.
Lemma lem1300978 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1300979 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem1300978 m n) (@lem1300977 m n)). Qed.
Lemma lem1300980 (m : nat) (n : nat) : (term3 m n) = ((term3 m n) = True).
Proof. exact (@lem7 (term3 m n)). Qed.
Lemma lem1300982 (m : nat) : term4 m.
Proof. exact (@lem81820 m). Qed.
Lemma lem1300983 (m : nat) : (term4 m) = (term5 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem1300984 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem1300983 m) (@lem1300982 m)). Qed.
Lemma lem1300985 (m : nat) (n : nat) : term6 m n.
Proof. exact (@lem1300984 m n). Qed.
Lemma lem1300986 (n : nat) (m : nat) : (term6 m n) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem1300988 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem1300989 (m : nat) (h1 : term7) : term8 m.
Proof. exact (@lem1300988 h1 m). Qed.
Lemma lem1300990 (m : nat) : (term8 m) = (term9 m).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem1300991 (m : nat) (h1 : term7) : term9 m.
Proof. exact (EQ_MP (@lem1300990 m) (@lem1300989 m h1)). Qed.
Lemma lem1300992 (m : nat) (n : nat) (h1 : term7) : term10 m n.
Proof. exact (@lem1300991 m h1 n). Qed.
Lemma lem1300993 (m : nat) (n : nat) : (term10 m n) = (term11 m n).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem1300994 (m : nat) (n : nat) (h1 : term7) : term11 m n.
Proof. exact (EQ_MP (@lem1300993 m n) (@lem1300992 m n h1)). Qed.
Lemma lem1300995 (n : nat) (h1 : term12 n) : term12 n.
Proof. exact (h1). Qed.
Lemma lem1300996 (m : nat) (n : nat) (h1 : term7) (h2 : term12 n) : term13 m n.
Proof. exact (@lem1300994 m n h1 (@lem1300995 n h2)). Qed.
Lemma lem1300997 (n : nat) (h1 : term7) (h2 : term12 n) : term14 n.
Proof. exact (fun m : nat => @lem1300996 m n h1 h2). Qed.
Lemma lem1300998 (n : nat) (h1 : term7) : term15 n.
Proof. exact (fun h0 : term12 n => @lem1300997 n h1 h0). Qed.
Lemma lem1300999 (h1 : term7) : term16.
Proof. exact (fun n : nat => @lem1300998 n h1). Qed.
Lemma lem1301000 : term17.
Proof. exact (fun h0 : term7 => @lem1300999 h0). Qed.
Lemma lem1301001 : term16.
Proof. exact (@lem1301000 (@lem157261)). Qed.
Lemma lem1301002 (n : nat) : term18 n.
Proof. exact (@lem1301001 n). Qed.
Lemma lem1301003 (n : nat) : (term18 n) = (term15 n).
Proof. exact (eq_refl (term18 n)). Qed.
Lemma lem1301005 (x : nadd) (n : nat) : term19 x n.
Proof. exact (@lem9784 ((dest_nadd x n) = (NUMERAL 0))). Qed.
Lemma lem1301006 (x : nadd) (n : nat) : (term19 x n) = (term20 x n).
Proof. exact (eq_refl (term19 x n)). Qed.
Lemma lem1301007 (x : nadd) (n : nat) : term20 x n.
Proof. exact (EQ_MP (@lem1301006 x n) (@lem1301005 x n)). Qed.
Lemma lem1301009 (x : nadd) (n : nat) (h1 : term21 x n) : term21 x n.
Proof. exact (h1). Qed.
Lemma lem1301013 (m : nat) (n : nat) (p : nat) (h1 : (term22 m n p) = (term23 m n p)) : (term22 m n p) = (term23 m n p).
Proof. exact (h1). Qed.
Lemma lem1301014 (m : nat) (n : nat) (p : nat) (h1 : (term22 m n p) = (term23 m n p)) : (term23 m n p) = (term22 m n p).
Proof. exact (SYM (@lem1301013 m n p h1)). Qed.
Lemma lem1301015 (m : nat) (n : nat) (p : nat) (h1 : (term23 m n p) = (term22 m n p)) : (term23 m n p) = (term22 m n p).
Proof. exact (h1). Qed.
Lemma lem1301016 (m : nat) (n : nat) (p : nat) (h1 : (term23 m n p) = (term22 m n p)) : (term22 m n p) = (term23 m n p).
Proof. exact (SYM (@lem1301015 m n p h1)). Qed.
Lemma lem1301017 (m : nat) (n : nat) (p : nat) : ((term22 m n p) = (term23 m n p)) = ((term23 m n p) = (term22 m n p)).
Proof. exact (prop_ext (fun h1 : (term22 m n p) = (term23 m n p) => @lem1301014 m n p h1) (fun h1 : (term23 m n p) = (term22 m n p) => @lem1301016 m n p h1)). Qed.
Lemma lem1301018 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (fun_ext (fun p : nat => @lem1301017 m n p)). Qed.
Lemma lem1301019 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1301020 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (MK_COMB (@lem1301019) (@lem1301018 m n)). Qed.
Lemma lem1301021 (m : nat) : (term28 m) = (term29 m).
Proof. exact (fun_ext (fun n : nat => @lem1301020 m n)). Qed.
Lemma lem1301022 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1301023 (m : nat) : (term30 m) = (term31 m).
Proof. exact (MK_COMB (@lem1301022) (@lem1301021 m)). Qed.
Lemma lem1301024 : term32 = term33.
Proof. exact (fun_ext (fun m : nat => @lem1301023 m)). Qed.
Lemma lem1301025 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1301026 : term34 = term35.
Proof. exact (MK_COMB (@lem1301025) (@lem1301024)). Qed.
Lemma lem1301027 : term35.
Proof. exact (EQ_MP (@lem1301026) (@lem82357)). Qed.
Lemma lem1301028 (m : nat) : term36 m.
Proof. exact (@lem104208 m). Qed.
Lemma lem1301029 (m : nat) : (term36 m) = (term37 m).
Proof. exact (eq_refl (term36 m)). Qed.
Lemma lem1301030 (m : nat) : term37 m.
Proof. exact (EQ_MP (@lem1301029 m) (@lem1301028 m)). Qed.
Lemma lem1301031 (m : nat) (n : nat) : term38 m n.
Proof. exact (@lem1301030 m n). Qed.
Lemma lem1301032 (m : nat) (n : nat) : (term38 m n) = (term39 m n).
Proof. exact (eq_refl (term38 m n)). Qed.
Lemma lem1301033 (m : nat) (n : nat) : term39 m n.
Proof. exact (EQ_MP (@lem1301032 m n) (@lem1301031 m n)). Qed.
Lemma lem1301034 (m : nat) (n : nat) (p : nat) : term40 m n p.
Proof. exact (@lem1301033 m n p). Qed.
Lemma lem1301035 (m : nat) (n : nat) (p : nat) : (term40 m n p) = ((term41 n m p) = (term42 m n p)).
Proof. exact (eq_refl (term40 m n p)). Qed.
Lemma lem1301037 (m : nat) : term43 m.
Proof. exact (@lem1301027 m). Qed.
Lemma lem1301038 (m : nat) : (term43 m) = (term31 m).
Proof. exact (eq_refl (term43 m)). Qed.
Lemma lem1301039 (m : nat) : term31 m.
Proof. exact (EQ_MP (@lem1301038 m) (@lem1301037 m)). Qed.
Lemma lem1301040 (m : nat) (n : nat) : term44 m n.
Proof. exact (@lem1301039 m n). Qed.
Lemma lem1301041 (m : nat) (n : nat) : (term44 m n) = (term27 m n).
Proof. exact (eq_refl (term44 m n)). Qed.
Lemma lem1301042 (m : nat) (n : nat) : term27 m n.
Proof. exact (EQ_MP (@lem1301041 m n) (@lem1301040 m n)). Qed.
Lemma lem1301043 (m : nat) (n : nat) (p : nat) : term45 m n p.
Proof. exact (@lem1301042 m n p). Qed.
Lemma lem1301044 (m : nat) (n : nat) (p : nat) : (term45 m n p) = ((term23 m n p) = (term22 m n p)).
Proof. exact (eq_refl (term45 m n p)). Qed.
Lemma lem1301046 (m : nat) : term4 m.
Proof. exact (@lem81820 m). Qed.
Lemma lem1301047 (m : nat) : (term4 m) = (term5 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem1301048 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem1301047 m) (@lem1301046 m)). Qed.
Lemma lem1301049 (m : nat) (n : nat) : term6 m n.
Proof. exact (@lem1301048 m n). Qed.
Lemma lem1301050 (n : nat) (m : nat) : (term6 m n) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem1301052 (h1 : term46) : term46.
Proof. exact (h1). Qed.
Lemma lem1301053 (m : nat) (h1 : term46) : term47 m.
Proof. exact (@lem1301052 h1 m). Qed.
Lemma lem1301054 (m : nat) : (term47 m) = (term48 m).
Proof. exact (eq_refl (term47 m)). Qed.
Lemma lem1301055 (m : nat) (h1 : term46) : term48 m.
Proof. exact (EQ_MP (@lem1301054 m) (@lem1301053 m h1)). Qed.
Lemma lem1301056 (m : nat) (n : nat) (h1 : term46) : term49 m n.
Proof. exact (@lem1301055 m h1 n). Qed.
Lemma lem1301057 (n : nat) (m : nat) : (term49 m n) = (term50 n m).
Proof. exact (eq_refl (term49 m n)). Qed.
Lemma lem1301058 (n : nat) (m : nat) (h1 : term46) : term50 n m.
Proof. exact (EQ_MP (@lem1301057 n m) (@lem1301056 m n h1)). Qed.
Lemma lem1301059 (n : nat) (m : nat) (p : nat) (h1 : term46) : term51 n m p.
Proof. exact (@lem1301058 n m h1 p). Qed.
Lemma lem1301060 (n : nat) (m : nat) (p : nat) : (term51 n m p) = (term52 n m p).
Proof. exact (eq_refl (term51 n m p)). Qed.
Lemma lem1301061 (n : nat) (m : nat) (p : nat) (h1 : term46) : term52 n m p.
Proof. exact (EQ_MP (@lem1301060 n m p) (@lem1301059 n m p h1)). Qed.
Lemma lem1301062 (m : nat) (n : nat) (p : nat) (h1 : term53 m n p) : term53 m n p.
Proof. exact (h1). Qed.
Lemma lem1301063 (m : nat) (n : nat) (p : nat) (h1 : term46) (h2 : term53 m n p) : Peano.le m p.
Proof. exact (@lem1301061 n m p h1 (@lem1301062 m n p h2)). Qed.
Lemma lem1301064 (m : nat) (n : nat) (p : nat) (h1 : term53 m n p) : term54 m p.
Proof. exact (fun h0 : term46 => @lem1301063 m n p h0 h1). Qed.
Lemma lem1301065 (m : nat) (p : nat) (h1 : term55 m p) : term55 m p.
Proof. exact (h1). Qed.
Lemma lem1301066 (m : nat) (p : nat) (h1 : term55 m p) : term54 m p.
Proof. exact (ex_elim (@lem1301065 m p h1) (fun n : nat => fun h0 : term56 m p n => @lem1301064 m n p h0)). Qed.
Lemma lem1301067 (h1 : term46) : term46.
Proof. exact (h1). Qed.
Lemma lem1301068 (m : nat) (p : nat) (h1 : term46) (h2 : term55 m p) : Peano.le m p.
Proof. exact (@lem1301066 m p h2 (@lem1301067 h1)). Qed.
Lemma lem1301069 (m : nat) (p : nat) (h1 : term46) : term57 m p.
Proof. exact (fun h0 : term55 m p => @lem1301068 m p h1 h0). Qed.
Lemma lem1301070 (m : nat) (h1 : term46) : term58 m.
Proof. exact (fun p : nat => @lem1301069 m p h1). Qed.
Lemma lem1301071 (h1 : term46) : term59.
Proof. exact (fun m : nat => @lem1301070 m h1). Qed.
Lemma lem1301072 : term60.
Proof. exact (fun h0 : term46 => @lem1301071 h0). Qed.
Lemma lem1301073 : term59.
Proof. exact (@lem1301072 (@lem93743)). Qed.
Lemma lem1301074 (m : nat) : term61 m.
Proof. exact (@lem1301073 m). Qed.
Lemma lem1301075 (m : nat) : (term61 m) = (term58 m).
Proof. exact (eq_refl (term61 m)). Qed.
Lemma lem1301076 (m : nat) : term58 m.
Proof. exact (EQ_MP (@lem1301075 m) (@lem1301074 m)). Qed.
Lemma lem1301077 (m : nat) (p : nat) : term62 m p.
Proof. exact (@lem1301076 m p). Qed.
Lemma lem1301078 (m : nat) (p : nat) : (term62 m p) = (term57 m p).
Proof. exact (eq_refl (term62 m p)). Qed.
Lemma lem1301080 (h1 : term46) : term46.
Proof. exact (h1). Qed.
Lemma lem1301081 (m : nat) (h1 : term46) : term47 m.
Proof. exact (@lem1301080 h1 m). Qed.
Lemma lem1301082 (m : nat) : (term47 m) = (term48 m).
Proof. exact (eq_refl (term47 m)). Qed.
Lemma lem1301083 (m : nat) (h1 : term46) : term48 m.
Proof. exact (EQ_MP (@lem1301082 m) (@lem1301081 m h1)). Qed.
Lemma lem1301084 (m : nat) (n : nat) (h1 : term46) : term49 m n.
Proof. exact (@lem1301083 m h1 n). Qed.
Lemma lem1301085 (n : nat) (m : nat) : (term49 m n) = (term50 n m).
Proof. exact (eq_refl (term49 m n)). Qed.
Lemma lem1301086 (n : nat) (m : nat) (h1 : term46) : term50 n m.
Proof. exact (EQ_MP (@lem1301085 n m) (@lem1301084 m n h1)). Qed.
Lemma lem1301087 (n : nat) (m : nat) (p : nat) (h1 : term46) : term51 n m p.
Proof. exact (@lem1301086 n m h1 p). Qed.
Lemma lem1301088 (n : nat) (m : nat) (p : nat) : (term51 n m p) = (term52 n m p).
Proof. exact (eq_refl (term51 n m p)). Qed.
Lemma lem1301089 (n : nat) (m : nat) (p : nat) (h1 : term46) : term52 n m p.
Proof. exact (EQ_MP (@lem1301088 n m p) (@lem1301087 n m p h1)). Qed.
Lemma lem1301090 (m : nat) (n : nat) (p : nat) (h1 : term53 m n p) : term53 m n p.
Proof. exact (h1). Qed.
Lemma lem1301091 (m : nat) (n : nat) (p : nat) (h1 : term46) (h2 : term53 m n p) : Peano.le m p.
Proof. exact (@lem1301089 n m p h1 (@lem1301090 m n p h2)). Qed.
Lemma lem1301092 (m : nat) (n : nat) (p : nat) (h1 : term53 m n p) : term54 m p.
Proof. exact (fun h0 : term46 => @lem1301091 m n p h0 h1). Qed.
Lemma lem1301093 (m : nat) (p : nat) (h1 : term55 m p) : term55 m p.
Proof. exact (h1). Qed.
Lemma lem1301094 (m : nat) (p : nat) (h1 : term55 m p) : term54 m p.
Proof. exact (ex_elim (@lem1301093 m p h1) (fun n : nat => fun h0 : term56 m p n => @lem1301092 m n p h0)). Qed.
Lemma lem1301095 (h1 : term46) : term46.
Proof. exact (h1). Qed.
Lemma lem1301096 (m : nat) (p : nat) (h1 : term46) (h2 : term55 m p) : Peano.le m p.
Proof. exact (@lem1301094 m p h2 (@lem1301095 h1)). Qed.
Lemma lem1301097 (m : nat) (p : nat) (h1 : term46) : term57 m p.
Proof. exact (fun h0 : term55 m p => @lem1301096 m p h1 h0). Qed.
Lemma lem1301098 (m : nat) (h1 : term46) : term58 m.
Proof. exact (fun p : nat => @lem1301097 m p h1). Qed.
Lemma lem1301099 (h1 : term46) : term59.
Proof. exact (fun m : nat => @lem1301098 m h1). Qed.
Lemma lem1301100 : term60.
Proof. exact (fun h0 : term46 => @lem1301099 h0). Qed.
Lemma lem1301101 : term59.
Proof. exact (@lem1301100 (@lem93743)). Qed.
Lemma lem1301102 (m : nat) : term61 m.
Proof. exact (@lem1301101 m). Qed.
Lemma lem1301103 (m : nat) : (term61 m) = (term58 m).
Proof. exact (eq_refl (term61 m)). Qed.
Lemma lem1301104 (m : nat) : term58 m.
Proof. exact (EQ_MP (@lem1301103 m) (@lem1301102 m)). Qed.
Lemma lem1301105 (m : nat) (p : nat) : term62 m p.
Proof. exact (@lem1301104 m p). Qed.
Lemma lem1301106 (m : nat) (p : nat) : (term62 m p) = (term57 m p).
Proof. exact (eq_refl (term62 m p)). Qed.
Lemma lem1301108 (n : nat) : term63 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem1301109 (n : nat) : (term63 n) = (term64 n).
Proof. exact (eq_refl (term63 n)). Qed.
Lemma lem1301110 (n : nat) : term64 n.
Proof. exact (EQ_MP (@lem1301109 n) (@lem1301108 n)). Qed.
Lemma lem1301112 (n : nat) (h1 : term12 n) : term12 n.
Proof. exact (h1). Qed.
Lemma lem1301113 (x : nadd) (n : nat) : term65 x n.
Proof. exact (@lem104289 (nadd_rinv x n)). Qed.
Lemma lem1301114 (x : nadd) (n : nat) : (term65 x n) = (term66 x n).
Proof. exact (eq_refl (term65 x n)). Qed.
Lemma lem1301115 (x : nadd) (n : nat) : term66 x n.
Proof. exact (EQ_MP (@lem1301114 x n) (@lem1301113 x n)). Qed.
Lemma lem1301116 (x : nadd) (A : nat) (n : nat) : term67 x A n.
Proof. exact (@lem1301115 x n (Nat.mul A n)). Qed.
Lemma lem1301117 (x : nadd) (A : nat) (n : nat) : (term67 x A n) = (term68 x A n).
Proof. exact (eq_refl (term67 x A n)). Qed.
Lemma lem1301118 (x : nadd) (A : nat) (n : nat) : term68 x A n.
Proof. exact (EQ_MP (@lem1301117 x A n) (@lem1301116 x A n)). Qed.
Lemma lem1301119 (x : nadd) (A : nat) (n : nat) : term69 x A n.
Proof. exact (@lem1301118 x A n n). Qed.
Lemma lem1301120 (x : nadd) (A : nat) (n : nat) : (term69 x A n) = ((term70 x A n) = (term71 x A n)).
Proof. exact (eq_refl (term69 x A n)). Qed.
Lemma lem1301121 (x : nadd) (A : nat) (n : nat) : (term70 x A n) = (term71 x A n).
Proof. exact (EQ_MP (@lem1301120 x A n) (@lem1301119 x A n)). Qed.
Lemma lem1301122 : term72.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem1301138 : term73.
Proof. exact (proj1 (@lem1301122)). Qed.
Lemma lem1301139 (m : nat) : term74 m.
Proof. exact (@lem1301138 m). Qed.
Lemma lem1301140 (m : nat) : (term74 m) = ((term75 m) = m).
Proof. exact (eq_refl (term74 m)). Qed.
Lemma lem1301146 (x : nadd) : term76 x.
Proof. exact (@lem1300501 x). Qed.
Lemma lem1301147 (x : nadd) : (term76 x) = (term77 x).
Proof. exact (eq_refl (term76 x)). Qed.
Lemma lem1301149 (P : nat -> nat) : term78 P.
Proof. exact (@lem1262185 P). Qed.
Lemma lem1301150 (P : nat -> nat) : (term78 P) = (term79 P).
Proof. exact (eq_refl (term78 P)). Qed.
Lemma lem1301151 (P : nat -> nat) : term79 P.
Proof. exact (EQ_MP (@lem1301150 P) (@lem1301149 P)). Qed.
Lemma lem1301152 (P : nat -> nat) (Q : nat -> nat) : term80 P Q.
Proof. exact (@lem1301151 P Q). Qed.
Lemma lem1301153 (P : nat -> nat) (Q : nat -> nat) : (term80 P Q) = ((term81 P Q) = (term82 P Q)).
Proof. exact (eq_refl (term80 P Q)). Qed.
Lemma lem1301155 (x : nadd) (h1 : term83 x) : term83 x.
Proof. exact (h1). Qed.
Lemma lem1301161 (P : nat -> nat) (Q : nat -> nat) : (term81 P Q) = (term82 P Q).
Proof. exact (EQ_MP (@lem1301153 P Q) (@lem1301152 P Q)). Qed.
Lemma lem1301162 (x : nadd) (A : nat) : (term84 x A) = (term85 x A).
Proof. exact (@lem1301161 (term86 x) (term87 A)). Qed.
Lemma lem1301163 (x : nadd) (n : nat) : (term88 x n) = (nadd_rinv x n).
Proof. exact (eq_refl (term88 x n)). Qed.
Lemma lem1301164 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1301165 (x : nadd) (n : nat) : (term89 x n) = (term90 x n).
Proof. exact (MK_COMB (@lem1301164) (@lem1301163 x n)). Qed.
Lemma lem1301166 (A : nat) (n : nat) : (term91 A n) = (Nat.mul A n).
Proof. exact (eq_refl (term91 A n)). Qed.
Lemma lem1301167 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1301168 (A : nat) (n : nat) : (term92 A n) = (term93 A n).
Proof. exact (MK_COMB (@lem1301167) (@lem1301166 A n)). Qed.
Lemma lem1301169 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1301170 (A : nat) (n : nat) (B : nat) : (term94 A n B) = (term95 A n B).
Proof. exact (MK_COMB (@lem1301168 A n) (@lem1301169 B)). Qed.
Lemma lem1301171 (x : nadd) (A : nat) (n : nat) (B : nat) : (term96 x A n B) = (term97 x A n B).
Proof. exact (MK_COMB (@lem1301165 x n) (@lem1301170 A n B)). Qed.
Lemma lem1301172 (x : nadd) (A : nat) (B : nat) : (term98 x A B) = (term99 x A B).
Proof. exact (fun_ext (fun n : nat => @lem1301171 x A n B)). Qed.
Lemma lem1301173 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1301174 (x : nadd) (A : nat) (B : nat) : (term100 x A B) = (term101 x A B).
Proof. exact (MK_COMB (@lem1301173) (@lem1301172 x A B)). Qed.
Lemma lem1301175 (x : nadd) (A : nat) : (term102 x A) = (term103 x A).
Proof. exact (fun_ext (fun B : nat => @lem1301174 x A B)). Qed.
Lemma lem1301176 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1301177 (x : nadd) (A : nat) : (term84 x A) = (term104 x A).
Proof. exact (MK_COMB (@lem1301176) (@lem1301175 x A)). Qed.
Lemma lem1301178 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1301179 (x : nadd) (A : nat) : (term105 x A) = (term106 x A).
Proof. exact (MK_COMB (@lem1301178) (@lem1301177 x A)). Qed.
Lemma lem1301180 (x : nadd) (n : nat) : (term88 x n) = (nadd_rinv x n).
Proof. exact (eq_refl (term88 x n)). Qed.
Lemma lem1301181 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1301182 (x : nadd) (n : nat) : (term89 x n) = (term90 x n).
Proof. exact (MK_COMB (@lem1301181) (@lem1301180 x n)). Qed.
Lemma lem1301183 (A : nat) (n : nat) : (term91 A n) = (Nat.mul A n).
Proof. exact (eq_refl (term91 A n)). Qed.
Lemma lem1301184 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1301185 (A : nat) (n : nat) : (term92 A n) = (term93 A n).
Proof. exact (MK_COMB (@lem1301184) (@lem1301183 A n)). Qed.
Lemma lem1301186 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1301187 (A : nat) (n : nat) (B : nat) : (term94 A n B) = (term95 A n B).
Proof. exact (MK_COMB (@lem1301185 A n) (@lem1301186 B)). Qed.
Lemma lem1301188 (x : nadd) (A : nat) (n : nat) (B : nat) : (term96 x A n B) = (term97 x A n B).
Proof. exact (MK_COMB (@lem1301182 x n) (@lem1301187 A n B)). Qed.
Lemma lem1301189 (N : nat) (n : nat) : (term107 N n) = (term107 N n).
Proof. exact (eq_refl (term107 N n)). Qed.
Lemma lem1301190 (N : nat) (x : nadd) (A : nat) (n : nat) (B : nat) : (term108 N x A n B) = (term109 N x A n B).
Proof. exact (MK_COMB (@lem1301189 N n) (@lem1301188 x A n B)). Qed.
Lemma lem1301191 (N : nat) (x : nadd) (A : nat) (B : nat) : (term110 N x A B) = (term111 N x A B).
Proof. exact (fun_ext (fun n : nat => @lem1301190 N x A n B)). Qed.
Lemma lem1301192 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1301193 (N : nat) (x : nadd) (A : nat) (B : nat) : (term112 N x A B) = (term113 N x A B).
Proof. exact (MK_COMB (@lem1301192) (@lem1301191 N x A B)). Qed.
Lemma lem1301194 (x : nadd) (A : nat) (B : nat) : (term114 x A B) = (term115 x A B).
Proof. exact (fun_ext (fun N : nat => @lem1301193 N x A B)). Qed.
Lemma lem1301195 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1301196 (x : nadd) (A : nat) (B : nat) : (term116 x A B) = (term117 x A B).
Proof. exact (MK_COMB (@lem1301195) (@lem1301194 x A B)). Qed.
Lemma lem1301197 (x : nadd) (A : nat) : (term118 x A) = (term119 x A).
Proof. exact (fun_ext (fun B : nat => @lem1301196 x A B)). Qed.
Lemma lem1301198 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1301199 (x : nadd) (A : nat) : (term85 x A) = (term120 x A).
Proof. exact (MK_COMB (@lem1301198) (@lem1301197 x A)). Qed.
Lemma lem1301200 (x : nadd) (A : nat) : ((term84 x A) = (term85 x A)) = ((term104 x A) = (term120 x A)).
Proof. exact (MK_COMB (@lem1301179 x A) (@lem1301199 x A)). Qed.
Lemma lem1301201 (x : nadd) (A : nat) : (term104 x A) = (term120 x A).
Proof. exact (EQ_MP (@lem1301200 x A) (@lem1301162 x A)). Qed.
Lemma lem1301202 (x : nadd) : (term121 x) = (term122 x).
Proof. exact (fun_ext (fun A : nat => @lem1301201 x A)). Qed.
Lemma lem1301203 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1301204 (x : nadd) : (term123 x) = (term124 x).
Proof. exact (MK_COMB (@lem1301203) (@lem1301202 x)). Qed.
Lemma lem1301205 (x : nadd) : (term124 x) = (term123 x).
Proof. exact (SYM (@lem1301204 x)). Qed.
Lemma lem1301207 (x : nadd) : term77 x.
Proof. exact (EQ_MP (@lem1301147 x) (@lem1301146 x)). Qed.
Lemma lem1301208 (x : nadd) (h1 : term83 x) : term125 x.
Proof. exact (@lem1301207 x (@lem1301155 x h1)). Qed.
Lemma lem1301209 (x : nadd) (h1 : term125 x) : term125 x.
Proof. exact (h1). Qed.
Lemma lem1301210 (A : nat) (x : nadd) (h1 : term126 A x) : term126 A x.
Proof. exact (h1). Qed.
Lemma lem1301211 (N : nat) (A : nat) (x : nadd) (h1 : term127 N A x) : term127 N A x.
Proof. exact (h1). Qed.
Lemma lem1301212 (N : nat) (n : nat) (h1 : term128 N n) : term128 N n.
Proof. exact (h1). Qed.
Lemma lem1301214 (m : nat) : (term75 m) = m.
Proof. exact (EQ_MP (@lem1301140 m) (@lem1301139 m)). Qed.
Lemma lem1301215 (A : nat) (n : nat) : (term129 A n) = (Nat.mul A n).
Proof. exact (@lem1301214 (Nat.mul A n)). Qed.
Lemma lem1301216 (x : nadd) (n : nat) : (term90 x n) = (term90 x n).
Proof. exact (eq_refl (term90 x n)). Qed.
Lemma lem1301217 (x : nadd) (A : nat) (n : nat) : (term130 x A n) = (term131 x A n).
Proof. exact (MK_COMB (@lem1301216 x n) (@lem1301215 A n)). Qed.
Lemma lem1301218 (x : nadd) (A : nat) (n : nat) : (term131 x A n) = (term130 x A n).
Proof. exact (SYM (@lem1301217 x A n)). Qed.
Lemma lem1301219 (n : nat) : term132 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem1301220 (n : nat) : (term132 n) = (term133 n).
Proof. exact (eq_refl (term132 n)). Qed.
Lemma lem1301221 (n : nat) : term133 n.
Proof. exact (EQ_MP (@lem1301220 n) (@lem1301219 n)). Qed.
Lemma lem1301222 (n : nat) : term134 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem1301242 : term135.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem1301243 (m : nat) : term136 m.
Proof. exact (@lem1301242 m). Qed.
Lemma lem1301244 (m : nat) : (term136 m) = ((term137 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl (term136 m)). Qed.
Lemma lem1301256 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1301257 (N : nat) : (term138 N) = (term138 N).
Proof. exact (eq_refl (term138 N)). Qed.
Lemma lem1301258 (N : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term128 N n) = (term139 N).
Proof. exact (MK_COMB (@lem1301257 N) (@lem1301256 n h1)). Qed.
Lemma lem1301260 (m : nat) : (term137 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1301244 m) (@lem1301243 m)). Qed.
Lemma lem1301261 (N : nat) : (term139 N) = ((S N) = (NUMERAL 0)).
Proof. exact (@lem1301260 (S N)). Qed.
Lemma lem1301263 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1301222 n (@lem1301221 n)). Qed.
Lemma lem1301264 (N : nat) : ((S N) = (NUMERAL 0)) = False.
Proof. exact (@lem1301263 N). Qed.
Lemma lem1301265 (N : nat) : (term139 N) = False.
Proof. exact (TRANS (@lem1301261 N) (@lem1301264 N)). Qed.
Lemma lem1301266 (N : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term128 N n) = False.
Proof. exact (TRANS (@lem1301258 N n h1) (@lem1301265 N)). Qed.
Lemma lem1301267 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1301268 (N : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term140 N n) = (imp False).
Proof. exact (MK_COMB (@lem1301267) (@lem1301266 N n h1)). Qed.
Lemma lem1301276 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1301277 (x : nadd) : (nadd_rinv x) = (nadd_rinv x).
Proof. exact (eq_refl (nadd_rinv x)). Qed.
Lemma lem1301278 (x : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : (nadd_rinv x n) = (term141 x).
Proof. exact (MK_COMB (@lem1301277 x) (@lem1301276 n h1)). Qed.
Lemma lem1301279 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem1301280 (x : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : (term142 x n) = (term143 x).
Proof. exact (MK_COMB (@lem1301279) (@lem1301278 x n h1)). Qed.
Lemma lem1301282 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1301283 (x : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : (term144 x n) = (term145 x).
Proof. exact (MK_COMB (@lem1301280 x n h1) (@lem1301282 n h1)). Qed.
Lemma lem1301284 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1301285 (x : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : (term146 x n) = (term147 x).
Proof. exact (MK_COMB (@lem1301284) (@lem1301283 x n h1)). Qed.
Lemma lem1301287 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1301288 (A : nat) : (Nat.mul A) = (Nat.mul A).
Proof. exact (eq_refl (Nat.mul A)). Qed.
Lemma lem1301289 (A : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.mul A n) = (term148 A).
Proof. exact (MK_COMB (@lem1301288 A) (@lem1301287 n h1)). Qed.
Lemma lem1301290 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem1301291 (A : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term149 A n) = (term150 A).
Proof. exact (MK_COMB (@lem1301290) (@lem1301289 A n h1)). Qed.
Lemma lem1301293 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1301294 (A : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term151 A n) = (term152 A).
Proof. exact (MK_COMB (@lem1301291 A n h1) (@lem1301293 n h1)). Qed.
Lemma lem1301295 (x : nadd) (A : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term70 x A n) = (term153 x A).
Proof. exact (MK_COMB (@lem1301285 x n h1) (@lem1301294 A n h1)). Qed.
Lemma lem1301296 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1301297 (x : nadd) (A : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term154 x A n) = (term155 x A).
Proof. exact (MK_COMB (@lem1301296) (@lem1301295 x A n h1)). Qed.
Lemma lem1301301 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1301302 (x : nadd) : (nadd_rinv x) = (nadd_rinv x).
Proof. exact (eq_refl (nadd_rinv x)). Qed.
Lemma lem1301303 (x : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : (nadd_rinv x n) = (term141 x).
Proof. exact (MK_COMB (@lem1301302 x) (@lem1301301 n h1)). Qed.
Lemma lem1301304 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1301305 (x : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : (term90 x n) = (term156 x).
Proof. exact (MK_COMB (@lem1301304) (@lem1301303 x n h1)). Qed.
Lemma lem1301307 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1301308 (A : nat) : (Nat.mul A) = (Nat.mul A).
Proof. exact (eq_refl (Nat.mul A)). Qed.
Lemma lem1301309 (A : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.mul A n) = (term148 A).
Proof. exact (MK_COMB (@lem1301308 A) (@lem1301307 n h1)). Qed.
Lemma lem1301310 (x : nadd) (A : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term131 x A n) = (term157 x A).
Proof. exact (MK_COMB (@lem1301305 x n h1) (@lem1301309 A n h1)). Qed.
Lemma lem1301311 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1301312 (x : nadd) (A : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term158 x A n) = (term159 x A).
Proof. exact (MK_COMB (@lem1301311) (@lem1301310 x A n h1)). Qed.
Lemma lem1301316 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1301317 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1301318 (n : nat) (h1 : n = (NUMERAL 0)) : (@eq nat n) = term160.
Proof. exact (MK_COMB (@lem1301317) (@lem1301316 n h1)). Qed.
Lemma lem1301319 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1301320 (n : nat) (h1 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1301318 n h1) (@lem1301319)). Qed.
Lemma lem1301322 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1301323 (x : nat) : (x = x) = True.
Proof. exact (@lem1301322 nat x). Qed.
Lemma lem1301324 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1301323 (NUMERAL 0)). Qed.
Lemma lem1301325 (n : nat) (h1 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem1301320 n h1) (@lem1301324)). Qed.
Lemma lem1301326 (x : nadd) (A : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term71 x A n) = (term161 x A).
Proof. exact (MK_COMB (@lem1301312 x A n h1) (@lem1301325 n h1)). Qed.
Lemma lem1301328 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1301329 (x : nadd) (A : nat) : (term161 x A) = True.
Proof. exact (@lem1301328 (term157 x A)). Qed.
Lemma lem1301330 (x : nadd) (A : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term71 x A n) = True.
Proof. exact (TRANS (@lem1301326 x A n h1) (@lem1301329 x A)). Qed.
Lemma lem1301331 (x : nadd) (A : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term70 x A n) = (term71 x A n)) = ((term153 x A) = True).
Proof. exact (MK_COMB (@lem1301297 x A n h1) (@lem1301330 x A n h1)). Qed.
Lemma lem1301333 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem1301334 (x : nadd) (A : nat) : ((term153 x A) = True) = (term153 x A).
Proof. exact (@lem1301333 (term153 x A)). Qed.
Lemma lem1301335 (x : nadd) (A : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term70 x A n) = (term71 x A n)) = (term153 x A).
Proof. exact (TRANS (@lem1301331 x A n h1) (@lem1301334 x A)). Qed.
Lemma lem1301336 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1301337 (x : nadd) (A : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term162 x A n) = (term163 x A).
Proof. exact (MK_COMB (@lem1301336) (@lem1301335 x A n h1)). Qed.
Lemma lem1301339 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1301340 (x : nadd) : (nadd_rinv x) = (nadd_rinv x).
Proof. exact (eq_refl (nadd_rinv x)). Qed.
Lemma lem1301341 (x : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : (nadd_rinv x n) = (term141 x).
Proof. exact (MK_COMB (@lem1301340 x) (@lem1301339 n h1)). Qed.
Lemma lem1301342 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1301343 (x : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : (term90 x n) = (term156 x).
Proof. exact (MK_COMB (@lem1301342) (@lem1301341 x n h1)). Qed.
Lemma lem1301345 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1301346 (A : nat) : (Nat.mul A) = (Nat.mul A).
Proof. exact (eq_refl (Nat.mul A)). Qed.
Lemma lem1301347 (A : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.mul A n) = (term148 A).
Proof. exact (MK_COMB (@lem1301346 A) (@lem1301345 n h1)). Qed.
Lemma lem1301348 (x : nadd) (A : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term131 x A n) = (term157 x A).
Proof. exact (MK_COMB (@lem1301343 x n h1) (@lem1301347 A n h1)). Qed.
Lemma lem1301349 (x : nadd) (A : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term164 x A n) = (term165 x A).
Proof. exact (MK_COMB (@lem1301337 x A n h1) (@lem1301348 x A n h1)). Qed.
Lemma lem1301352 (N : nat) (x : nadd) (A : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term166 N x A n) = (term167 x A).
Proof. exact (MK_COMB (@lem1301268 N n h1) (@lem1301349 x A n h1)). Qed.
Lemma lem1301354 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1301355 (x : nadd) (A : nat) : (term167 x A) = True.
Proof. exact (@lem1301354 (term165 x A)). Qed.
Lemma lem1301356 (N : nat) (x : nadd) (A : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term166 N x A n) = True.
Proof. exact (TRANS (@lem1301352 N x A n h1) (@lem1301355 x A)). Qed.
Lemma lem1301357 (N : nat) (x : nadd) (A : nat) (n : nat) (h1 : n = (NUMERAL 0)) : True = (term166 N x A n).
Proof. exact (SYM (@lem1301356 N x A n h1)). Qed.
Lemma lem1301358 (N : nat) (x : nadd) (A : nat) (n : nat) (h1 : n = (NUMERAL 0)) : term166 N x A n.
Proof. exact (EQ_MP (@lem1301357 N x A n h1) (@lem0)). Qed.
Lemma lem1301393 (n : nat) : term168 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem1301417 (n : nat) (h1 : term12 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem1301393 n (@lem1301112 n h1)). Qed.
Lemma lem1301418 (x : nadd) (A : nat) (n : nat) : (term158 x A n) = (term158 x A n).
Proof. exact (eq_refl (term158 x A n)). Qed.
Lemma lem1301419 (x : nadd) (A : nat) (n : nat) (h1 : term12 n) : (term71 x A n) = (term169 x A n).
Proof. exact (MK_COMB (@lem1301418 x A n) (@lem1301417 n h1)). Qed.
Lemma lem1301421 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem1301422 (x : nadd) (A : nat) (n : nat) : (term169 x A n) = (term131 x A n).
Proof. exact (@lem1301421 (term131 x A n)). Qed.
Lemma lem1301423 (x : nadd) (A : nat) (n : nat) (h1 : term12 n) : (term71 x A n) = (term131 x A n).
Proof. exact (TRANS (@lem1301419 x A n h1) (@lem1301422 x A n)). Qed.
Lemma lem1301424 (x : nadd) (A : nat) (n : nat) : (term154 x A n) = (term154 x A n).
Proof. exact (eq_refl (term154 x A n)). Qed.
Lemma lem1301425 (x : nadd) (A : nat) (n : nat) (h1 : term12 n) : ((term70 x A n) = (term71 x A n)) = ((term70 x A n) = (term131 x A n)).
Proof. exact (MK_COMB (@lem1301424 x A n) (@lem1301423 x A n h1)). Qed.
Lemma lem1301428 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1301429 (x : nadd) (A : nat) (n : nat) (h1 : term12 n) : (term162 x A n) = (term170 x A n).
Proof. exact (MK_COMB (@lem1301428) (@lem1301425 x A n h1)). Qed.
Lemma lem1301430 (x : nadd) (A : nat) (n : nat) : (term131 x A n) = (term131 x A n).
Proof. exact (eq_refl (term131 x A n)). Qed.
Lemma lem1301431 (x : nadd) (A : nat) (n : nat) (h1 : term12 n) : (term164 x A n) = (term171 x A n).
Proof. exact (MK_COMB (@lem1301429 x A n h1) (@lem1301430 x A n)). Qed.
Lemma lem1301436 (N : nat) (n : nat) : (term140 N n) = (term140 N n).
Proof. exact (eq_refl (term140 N n)). Qed.
Lemma lem1301437 (N : nat) (x : nadd) (A : nat) (n : nat) (h1 : term12 n) : (term166 N x A n) = (term172 N x A n).
Proof. exact (MK_COMB (@lem1301436 N n) (@lem1301431 x A n h1)). Qed.
Lemma lem1301440 (N : nat) (x : nadd) (A : nat) (n : nat) (h1 : term12 n) : (term172 N x A n) = (term166 N x A n).
Proof. exact (SYM (@lem1301437 N x A n h1)). Qed.
Lemma lem1301441 (N : nat) (n : nat) (h1 : term128 N n) : term128 N n.
Proof. exact (h1). Qed.
Lemma lem1301442 (x : nadd) (A : nat) (n : nat) (h1 : (term70 x A n) = (term131 x A n)) : (term70 x A n) = (term131 x A n).
Proof. exact (h1). Qed.
Lemma lem1301443 (x : nadd) (A : nat) (n : nat) (h1 : (term70 x A n) = (term131 x A n)) : (term131 x A n) = (term70 x A n).
Proof. exact (SYM (@lem1301442 x A n h1)). Qed.
Lemma lem1301444 : term173 = term173.
Proof. exact (eq_refl term173). Qed.
Lemma lem1301445 (x : nadd) (A : nat) (n : nat) (h1 : (term70 x A n) = (term131 x A n)) : (term174 x A n) = (term175 x A n).
Proof. exact (MK_COMB (@lem1301444) (@lem1301443 x A n h1)). Qed.
Lemma lem1301446 (x : nadd) (A : nat) (n : nat) : (term175 x A n) = (term70 x A n).
Proof. exact (eq_refl (term175 x A n)). Qed.
Lemma lem1301447 (x : nadd) (A : nat) (n : nat) : (term176 x A n) = (term176 x A n).
Proof. exact (eq_refl (term176 x A n)). Qed.
Lemma lem1301448 (x : nadd) (A : nat) (n : nat) : ((term174 x A n) = (term175 x A n)) = ((term174 x A n) = (term70 x A n)).
Proof. exact (MK_COMB (@lem1301447 x A n) (@lem1301446 x A n)). Qed.
Lemma lem1301449 (x : nadd) (A : nat) (n : nat) : (term174 x A n) = (term131 x A n).
Proof. exact (eq_refl (term174 x A n)). Qed.
Lemma lem1301450 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1301451 (x : nadd) (A : nat) (n : nat) : (term176 x A n) = (term177 x A n).
Proof. exact (MK_COMB (@lem1301450) (@lem1301449 x A n)). Qed.
Lemma lem1301452 (x : nadd) (A : nat) (n : nat) : (term70 x A n) = (term70 x A n).
Proof. exact (eq_refl (term70 x A n)). Qed.
Lemma lem1301453 (x : nadd) (A : nat) (n : nat) : ((term174 x A n) = (term70 x A n)) = ((term131 x A n) = (term70 x A n)).
Proof. exact (MK_COMB (@lem1301451 x A n) (@lem1301452 x A n)). Qed.
Lemma lem1301454 (x : nadd) (A : nat) (n : nat) : ((term174 x A n) = (term175 x A n)) = ((term131 x A n) = (term70 x A n)).
Proof. exact (TRANS (@lem1301448 x A n) (@lem1301453 x A n)). Qed.
Lemma lem1301455 (x : nadd) (A : nat) (n : nat) (h1 : (term70 x A n) = (term131 x A n)) : (term131 x A n) = (term70 x A n).
Proof. exact (EQ_MP (@lem1301454 x A n) (@lem1301445 x A n h1)). Qed.
Lemma lem1301456 (x : nadd) (A : nat) (n : nat) (h1 : (term70 x A n) = (term131 x A n)) : (term70 x A n) = (term131 x A n).
Proof. exact (SYM (@lem1301455 x A n h1)). Qed.
Lemma lem1301458 (m : nat) (p : nat) : term57 m p.
Proof. exact (EQ_MP (@lem1301106 m p) (@lem1301105 m p)). Qed.
Lemma lem1301459 (x : nadd) (A : nat) (n : nat) : term178 x A n.
Proof. exact (@lem1301458 (term144 x n) (term151 A n)). Qed.
Lemma lem1301460 (m : nat) : term36 m.
Proof. exact (@lem104208 m). Qed.
Lemma lem1301461 (m : nat) : (term36 m) = (term37 m).
Proof. exact (eq_refl (term36 m)). Qed.
Lemma lem1301462 (m : nat) : term37 m.
Proof. exact (EQ_MP (@lem1301461 m) (@lem1301460 m)). Qed.
Lemma lem1301463 (m : nat) (n : nat) : term38 m n.
Proof. exact (@lem1301462 m n). Qed.
Lemma lem1301464 (m : nat) (n : nat) : (term38 m n) = (term39 m n).
Proof. exact (eq_refl (term38 m n)). Qed.
Lemma lem1301465 (m : nat) (n : nat) : term39 m n.
Proof. exact (EQ_MP (@lem1301464 m n) (@lem1301463 m n)). Qed.
Lemma lem1301466 (m : nat) (n : nat) (p : nat) : term40 m n p.
Proof. exact (@lem1301465 m n p). Qed.
Lemma lem1301467 (m : nat) (n : nat) (p : nat) : (term40 m n p) = ((term41 n m p) = (term42 m n p)).
Proof. exact (eq_refl (term40 m n p)). Qed.
Lemma lem1301494 (m : nat) (n : nat) (p : nat) : (term41 n m p) = (term42 m n p).
Proof. exact (EQ_MP (@lem1301467 m n p) (@lem1301466 m n p)). Qed.
Lemma lem1301495 (A : nat) (x : nadd) (n : nat) : (term179 A x n) = (term180 A x n).
Proof. exact (@lem1301494 (nadd_rinv x n) n (term181 A x n)). Qed.
Lemma lem1301500 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1301501 (A : nat) (x : nadd) (n : nat) : (term182 A x n) = (term183 A x n).
Proof. exact (MK_COMB (@lem1301500) (@lem1301495 A x n)). Qed.
Lemma lem1301504 (x : nadd) (A : nat) (n : nat) : (term184 x A n) = (term184 x A n).
Proof. exact (eq_refl (term184 x A n)). Qed.
Lemma lem1301505 (x : nadd) (A : nat) (n : nat) : (term185 x A n) = (term186 x A n).
Proof. exact (MK_COMB (@lem1301501 A x n) (@lem1301504 x A n)). Qed.
Lemma lem1301508 (x : nadd) (A : nat) (n : nat) : (term186 x A n) = (term185 x A n).
Proof. exact (SYM (@lem1301505 x A n)). Qed.
Lemma lem1301509 (N : nat) (A : nat) (x : nadd) (h1 : term127 N A x) : term127 N A x.
Proof. exact (h1). Qed.
Lemma lem1301510 (n : nat) (N : nat) (A : nat) (x : nadd) (h1 : term127 N A x) : term187 N A x n.
Proof. exact (@lem1301509 N A x h1 n). Qed.
Lemma lem1301511 (N : nat) (A : nat) (x : nadd) (n : nat) : (term187 N A x n) = (term188 N A x n).
Proof. exact (eq_refl (term187 N A x n)). Qed.
Lemma lem1301512 (n : nat) (N : nat) (A : nat) (x : nadd) (h1 : term127 N A x) : term188 N A x n.
Proof. exact (EQ_MP (@lem1301511 N A x n) (@lem1301510 n N A x h1)). Qed.
Lemma lem1301513 (N : nat) (n : nat) (h1 : Peano.le N n) : Peano.le N n.
Proof. exact (h1). Qed.
Lemma lem1301514 (A : nat) (x : nadd) (N : nat) (n : nat) (h1 : term127 N A x) (h2 : Peano.le N n) : term189 A x n.
Proof. exact (@lem1301512 n N A x h1 (@lem1301513 N n h2)). Qed.
Lemma lem1301515 (A : nat) (x : nadd) (N : nat) (n : nat) (h1 : Peano.le N n) : term190 N A x n.
Proof. exact (fun h0 : term127 N A x => @lem1301514 A x N n h0 h1). Qed.
Lemma lem1301516 (N : nat) (A : nat) (x : nadd) (h1 : term127 N A x) : term127 N A x.
Proof. exact (h1). Qed.
Lemma lem1301517 (A : nat) (x : nadd) (N : nat) (n : nat) (h1 : term127 N A x) (h2 : Peano.le N n) : term189 A x n.
Proof. exact (@lem1301515 A x N n h2 (@lem1301516 N A x h1)). Qed.
Lemma lem1301518 (n : nat) (N : nat) (A : nat) (x : nadd) (h1 : term127 N A x) : term188 N A x n.
Proof. exact (fun h0 : Peano.le N n => @lem1301517 A x N n h1 h0). Qed.
Lemma lem1301519 (N : nat) (A : nat) (x : nadd) (h1 : term127 N A x) : term127 N A x.
Proof. exact (fun n : nat => @lem1301518 n N A x h1). Qed.
Lemma lem1301520 (N : nat) (A : nat) (x : nadd) : term191 N A x.
Proof. exact (fun h0 : term127 N A x => @lem1301519 N A x h0). Qed.
Lemma lem1301521 (N : nat) (A : nat) (x : nadd) (h1 : term127 N A x) : term127 N A x.
Proof. exact (@lem1301520 N A x (@lem1301211 N A x h1)). Qed.
Lemma lem1301522 (n : nat) (N : nat) (A : nat) (x : nadd) (h1 : term127 N A x) : term187 N A x n.
Proof. exact (@lem1301521 N A x h1 n). Qed.
Lemma lem1301523 (N : nat) (A : nat) (x : nadd) (n : nat) : (term187 N A x n) = (term188 N A x n).
Proof. exact (eq_refl (term187 N A x n)). Qed.
Lemma lem1301526 (n : nat) (N : nat) (A : nat) (x : nadd) (h1 : term127 N A x) : term188 N A x n.
Proof. exact (EQ_MP (@lem1301523 N A x n) (@lem1301522 n N A x h1)). Qed.
Lemma lem1301528 (m : nat) (p : nat) : term57 m p.
Proof. exact (EQ_MP (@lem1301078 m p) (@lem1301077 m p)). Qed.
Lemma lem1301529 (N : nat) (n : nat) : term57 N n.
Proof. exact (@lem1301528 N n). Qed.
Lemma lem1301530 (n : nat) : term192 n.
Proof. exact (@lem91603 n). Qed.
Lemma lem1301531 (n : nat) : (term192 n) = (Peano.le n n).
Proof. exact (eq_refl (term192 n)). Qed.
Lemma lem1301532 (n : nat) : Peano.le n n.
Proof. exact (EQ_MP (@lem1301531 n) (@lem1301530 n)). Qed.
Lemma lem1301533 (n : nat) : (Peano.le n n) = ((Peano.le n n) = True).
Proof. exact (@lem7 (Peano.le n n)). Qed.
Lemma lem1301535 : term193.
Proof. exact (proj2 (@lem89498)). Qed.
Lemma lem1301536 (m : nat) : term194 m.
Proof. exact (@lem1301535 m). Qed.
Lemma lem1301537 (m : nat) : (term194 m) = (term195 m).
Proof. exact (eq_refl (term194 m)). Qed.
Lemma lem1301538 (m : nat) : term195 m.
Proof. exact (EQ_MP (@lem1301537 m) (@lem1301536 m)). Qed.
Lemma lem1301539 (m : nat) (n : nat) : term196 m n.
Proof. exact (@lem1301538 m n). Qed.
Lemma lem1301540 (m : nat) (n : nat) : (term196 m n) = ((term197 m n) = (term198 m n)).
Proof. exact (eq_refl (term196 m n)). Qed.
Lemma lem1301566 (N : nat) (n : nat) : (term128 N n) = ((term128 N n) = True).
Proof. exact (@lem7 (term128 N n)). Qed.
Lemma lem1301571 (m : nat) (n : nat) : (term197 m n) = (term198 m n).
Proof. exact (EQ_MP (@lem1301540 m n) (@lem1301539 m n)). Qed.
Lemma lem1301572 (N : nat) : (term199 N) = (term200 N).
Proof. exact (@lem1301571 N N). Qed.
Lemma lem1301578 (n : nat) : (Peano.le n n) = True.
Proof. exact (EQ_MP (@lem1301533 n) (@lem1301532 n)). Qed.
Lemma lem1301579 (N : nat) : (Peano.le N N) = True.
Proof. exact (@lem1301578 N). Qed.
Lemma lem1301580 (N : nat) : (term201 N) = (term201 N).
Proof. exact (eq_refl (term201 N)). Qed.
Lemma lem1301581 (N : nat) : (term200 N) = (term202 N).
Proof. exact (MK_COMB (@lem1301580 N) (@lem1301579 N)). Qed.
Lemma lem1301583 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1301584 (N : nat) : (term202 N) = True.
Proof. exact (@lem1301583 (N = (S N))). Qed.
Lemma lem1301585 (N : nat) : (term200 N) = True.
Proof. exact (TRANS (@lem1301581 N) (@lem1301584 N)). Qed.
Lemma lem1301586 (N : nat) : (term199 N) = True.
Proof. exact (TRANS (@lem1301572 N) (@lem1301585 N)). Qed.
Lemma lem1301587 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1301588 (N : nat) : (term203 N) = (and True).
Proof. exact (MK_COMB (@lem1301587) (@lem1301586 N)). Qed.
Lemma lem1301590 (N : nat) (n : nat) (h1 : term128 N n) : (term128 N n) = True.
Proof. exact (EQ_MP (@lem1301566 N n) (@lem1301441 N n h1)). Qed.
Lemma lem1301591 (N : nat) (n : nat) (h1 : term128 N n) : (term204 N n) = (True /\ True).
Proof. exact (MK_COMB (@lem1301588 N) (@lem1301590 N n h1)). Qed.
Lemma lem1301593 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1301594 : (True /\ True) = True.
Proof. exact (@lem1301593 True). Qed.
Lemma lem1301595 (N : nat) (n : nat) (h1 : term128 N n) : (term204 N n) = True.
Proof. exact (TRANS (@lem1301591 N n h1) (@lem1301594)). Qed.
Lemma lem1301596 (N : nat) (n : nat) (h1 : term128 N n) : True = (term204 N n).
Proof. exact (SYM (@lem1301595 N n h1)). Qed.
Lemma lem1301597 (N : nat) (n : nat) (h1 : term128 N n) : term204 N n.
Proof. exact (EQ_MP (@lem1301596 N n h1) (@lem0)). Qed.
Lemma lem1301598 (N : nat) (n : nat) (h1 : term128 N n) : term55 N n.
Proof. exact (ex_intro (term56 N n) (S N) (@lem1301597 N n h1)). Qed.
Lemma lem1301599 (N : nat) (n : nat) (h1 : term128 N n) : Peano.le N n.
Proof. exact (@lem1301529 N n (@lem1301598 N n h1)). Qed.
Lemma lem1301600 (A : nat) (x : nadd) (N : nat) (n : nat) (h1 : term127 N A x) (h2 : term128 N n) : term189 A x n.
Proof. exact (@lem1301526 n N A x h1 (@lem1301599 N n h2)). Qed.
Lemma lem1301601 (A : nat) (x : nadd) (N : nat) (n : nat) (h1 : term127 N A x) (h2 : term128 N n) : term180 A x n.
Proof. exact (or_intro2 ((nadd_rinv x n) = (NUMERAL 0)) (@lem1301600 A x N n h1 h2)). Qed.
Lemma lem1301603 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem1301050 n m) (@lem1301049 m n)). Qed.
Lemma lem1301604 (A : nat) (x : nadd) (n : nat) : (term205 A x n) = (term206 A x n).
Proof. exact (@lem1301603 (term181 A x n) (nadd_rinv x n)). Qed.
Lemma lem1301605 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1301606 (A : nat) (x : nadd) (n : nat) : (term207 A x n) = (term208 A x n).
Proof. exact (MK_COMB (@lem1301605) (@lem1301604 A x n)). Qed.
Lemma lem1301607 (A : nat) (n : nat) : (term151 A n) = (term151 A n).
Proof. exact (eq_refl (term151 A n)). Qed.
Lemma lem1301608 (x : nadd) (A : nat) (n : nat) : (term184 x A n) = (term209 x A n).
Proof. exact (MK_COMB (@lem1301606 A x n) (@lem1301607 A n)). Qed.
Lemma lem1301609 (x : nadd) (A : nat) (n : nat) : (term209 x A n) = (term184 x A n).
Proof. exact (SYM (@lem1301608 x A n)). Qed.
Lemma lem1301613 (m : nat) (n : nat) (p : nat) : (term23 m n p) = (term22 m n p).
Proof. exact (EQ_MP (@lem1301044 m n p) (@lem1301043 m n p)). Qed.
Lemma lem1301614 (A : nat) (x : nadd) (n : nat) : (term206 A x n) = (term210 A x n).
Proof. exact (@lem1301613 A (dest_nadd x n) (nadd_rinv x n)). Qed.
Lemma lem1301615 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1301616 (A : nat) (x : nadd) (n : nat) : (term208 A x n) = (term211 A x n).
Proof. exact (MK_COMB (@lem1301615) (@lem1301614 A x n)). Qed.
Lemma lem1301618 (m : nat) (n : nat) (p : nat) : (term23 m n p) = (term22 m n p).
Proof. exact (EQ_MP (@lem1301044 m n p) (@lem1301043 m n p)). Qed.
Lemma lem1301619 (A : nat) (n : nat) : (term151 A n) = (term212 A n).
Proof. exact (@lem1301618 A n n). Qed.
Lemma lem1301620 (x : nadd) (A : nat) (n : nat) : (term209 x A n) = (term213 x A n).
Proof. exact (MK_COMB (@lem1301616 A x n) (@lem1301619 A n)). Qed.
Lemma lem1301622 (m : nat) (n : nat) (p : nat) : (term41 n m p) = (term42 m n p).
Proof. exact (EQ_MP (@lem1301035 m n p) (@lem1301034 m n p)). Qed.
Lemma lem1301623 (A : nat) (x : nadd) (n : nat) : (term213 x A n) = (term214 A x n).
Proof. exact (@lem1301622 A (term215 x n) (Nat.mul n n)). Qed.
Lemma lem1301630 (A : nat) (x : nadd) (n : nat) : (term209 x A n) = (term214 A x n).
Proof. exact (TRANS (@lem1301620 x A n) (@lem1301623 A x n)). Qed.
Lemma lem1301631 (x : nadd) (A : nat) (n : nat) : (term214 A x n) = (term209 x A n).
Proof. exact (SYM (@lem1301630 A x n)). Qed.
Lemma lem1301632 (x : nadd) : term216 x.
Proof. exact (@lem1300973 x). Qed.
Lemma lem1301633 (x : nadd) : (term216 x) = ((nadd_rinv x) = (term217 x)).
Proof. exact (eq_refl (term216 x)). Qed.
Lemma lem1301635 (n : nat) : term218 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem1301636 (n : nat) : (term218 n) = (term219 n).
Proof. exact (eq_refl (term218 n)). Qed.
Lemma lem1301637 (n : nat) : term219 n.
Proof. exact (EQ_MP (@lem1301636 n) (@lem1301635 n)). Qed.
Lemma lem1301638 (n : nat) : (term219 n) = ((term219 n) = True).
Proof. exact (@lem7 (term219 n)). Qed.
Lemma lem1301670 : term220.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem1301671 (n : nat) : term221 n.
Proof. exact (@lem1301670 n). Qed.
Lemma lem1301672 (n : nat) : (term221 n) = ((term222 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term221 n)). Qed.
Lemma lem1301697 (x : nadd) (n : nat) (h1 : (dest_nadd x n) = (NUMERAL 0)) : (dest_nadd x n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1301698 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem1301699 (x : nadd) (n : nat) (h1 : (dest_nadd x n) = (NUMERAL 0)) : (term223 x n) = term224.
Proof. exact (MK_COMB (@lem1301698) (@lem1301697 x n h1)). Qed.
Lemma lem1301701 (x : nadd) : (nadd_rinv x) = (term217 x).
Proof. exact (EQ_MP (@lem1301633 x) (@lem1301632 x)). Qed.
Lemma lem1301706 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1301707 (x : nadd) (n : nat) : (nadd_rinv x n) = (term225 x n).
Proof. exact (MK_COMB (@lem1301701 x) (@lem1301706 n)). Qed.
Lemma lem1301709 {A B : Type'} (f : A -> B) (y : A) : (term226 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1301710 (f : nat -> nat) (y : nat) : (term227 f y) = (f y).
Proof. exact (@lem1301709 nat nat f y). Qed.
Lemma lem1301711 (x : nadd) (n : nat) : (term228 x n) = (term225 x n).
Proof. exact (@lem1301710 (term217 x) n). Qed.
Lemma lem1301712 (x : nadd) (n : nat) : (term225 x n) = (term229 x n).
Proof. exact (eq_refl (term225 x n)). Qed.
Lemma lem1301713 (x : nadd) : (term230 x) = (term217 x).
Proof. exact (fun_ext (fun n : nat => @lem1301712 x n)). Qed.
Lemma lem1301714 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1301715 (x : nadd) (n : nat) : (term228 x n) = (term225 x n).
Proof. exact (MK_COMB (@lem1301713 x) (@lem1301714 n)). Qed.
Lemma lem1301716 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1301717 (x : nadd) (n : nat) : (term231 x n) = (term232 x n).
Proof. exact (MK_COMB (@lem1301716) (@lem1301715 x n)). Qed.
Lemma lem1301718 (x : nadd) (n : nat) : (term225 x n) = (term229 x n).
Proof. exact (eq_refl (term225 x n)). Qed.
Lemma lem1301719 (x : nadd) (n : nat) : ((term228 x n) = (term225 x n)) = ((term225 x n) = (term229 x n)).
Proof. exact (MK_COMB (@lem1301717 x n) (@lem1301718 x n)). Qed.
Lemma lem1301720 (x : nadd) (n : nat) : (term225 x n) = (term229 x n).
Proof. exact (EQ_MP (@lem1301719 x n) (@lem1301711 x n)). Qed.
Lemma lem1301722 (x : nadd) (n : nat) (h1 : (dest_nadd x n) = (NUMERAL 0)) : (dest_nadd x n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1301723 (n : nat) : (term233 n) = (term233 n).
Proof. exact (eq_refl (term233 n)). Qed.
Lemma lem1301724 (x : nadd) (n : nat) (h1 : (dest_nadd x n) = (NUMERAL 0)) : (term229 x n) = (term234 n).
Proof. exact (MK_COMB (@lem1301723 n) (@lem1301722 x n h1)). Qed.
Lemma lem1301725 (x : nadd) (n : nat) (h1 : (dest_nadd x n) = (NUMERAL 0)) : (term225 x n) = (term234 n).
Proof. exact (TRANS (@lem1301720 x n) (@lem1301724 x n h1)). Qed.
Lemma lem1301726 (x : nadd) (n : nat) (h1 : (dest_nadd x n) = (NUMERAL 0)) : (nadd_rinv x n) = (term234 n).
Proof. exact (TRANS (@lem1301707 x n) (@lem1301725 x n h1)). Qed.
Lemma lem1301727 (x : nadd) (n : nat) (h1 : (dest_nadd x n) = (NUMERAL 0)) : (term215 x n) = (term235 n).
Proof. exact (MK_COMB (@lem1301699 x n h1) (@lem1301726 x n h1)). Qed.
Lemma lem1301729 (n : nat) : (term222 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1301672 n) (@lem1301671 n)). Qed.
Lemma lem1301730 (n : nat) : (term235 n) = (NUMERAL 0).
Proof. exact (@lem1301729 (term234 n)). Qed.
Lemma lem1301731 (x : nadd) (n : nat) (h1 : (dest_nadd x n) = (NUMERAL 0)) : (term215 x n) = (NUMERAL 0).
Proof. exact (TRANS (@lem1301727 x n h1) (@lem1301730 n)). Qed.
Lemma lem1301732 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1301733 (x : nadd) (n : nat) (h1 : (dest_nadd x n) = (NUMERAL 0)) : (term236 x n) = term237.
Proof. exact (MK_COMB (@lem1301732) (@lem1301731 x n h1)). Qed.
Lemma lem1301734 (n : nat) : (Nat.mul n n) = (Nat.mul n n).
Proof. exact (eq_refl (Nat.mul n n)). Qed.
Lemma lem1301735 (x : nadd) (n : nat) (h1 : (dest_nadd x n) = (NUMERAL 0)) : (term238 x n) = (term239 n).
Proof. exact (MK_COMB (@lem1301733 x n h1) (@lem1301734 n)). Qed.
Lemma lem1301737 (n : nat) : (term219 n) = True.
Proof. exact (EQ_MP (@lem1301638 n) (@lem1301637 n)). Qed.
Lemma lem1301738 (n : nat) : (term239 n) = True.
Proof. exact (@lem1301737 (Nat.mul n n)). Qed.
Lemma lem1301739 (x : nadd) (n : nat) (h1 : (dest_nadd x n) = (NUMERAL 0)) : (term238 x n) = True.
Proof. exact (TRANS (@lem1301735 x n h1) (@lem1301738 n)). Qed.
Lemma lem1301740 (x : nadd) (n : nat) (h1 : (dest_nadd x n) = (NUMERAL 0)) : True = (term238 x n).
Proof. exact (SYM (@lem1301739 x n h1)). Qed.
Lemma lem1301741 (x : nadd) (n : nat) (h1 : (dest_nadd x n) = (NUMERAL 0)) : term238 x n.
Proof. exact (EQ_MP (@lem1301740 x n h1) (@lem0)). Qed.
Lemma lem1301742 (x : nadd) : term216 x.
Proof. exact (@lem1300973 x). Qed.
Lemma lem1301743 (x : nadd) : (term216 x) = ((nadd_rinv x) = (term217 x)).
Proof. exact (eq_refl (term216 x)). Qed.
Lemma lem1301820 (x : nadd) : (nadd_rinv x) = (term217 x).
Proof. exact (EQ_MP (@lem1301743 x) (@lem1301742 x)). Qed.
Lemma lem1301821 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1301822 (x : nadd) (n : nat) : (nadd_rinv x n) = (term225 x n).
Proof. exact (MK_COMB (@lem1301820 x) (@lem1301821 n)). Qed.
Lemma lem1301824 {A B : Type'} (f : A -> B) (y : A) : (term226 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1301825 (f : nat -> nat) (y : nat) : (term227 f y) = (f y).
Proof. exact (@lem1301824 nat nat f y). Qed.
Lemma lem1301826 (x : nadd) (n : nat) : (term228 x n) = (term225 x n).
Proof. exact (@lem1301825 (term217 x) n). Qed.
Lemma lem1301827 (x : nadd) (n : nat) : (term225 x n) = (term229 x n).
Proof. exact (eq_refl (term225 x n)). Qed.
Lemma lem1301828 (x : nadd) : (term230 x) = (term217 x).
Proof. exact (fun_ext (fun n : nat => @lem1301827 x n)). Qed.
Lemma lem1301829 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1301830 (x : nadd) (n : nat) : (term228 x n) = (term225 x n).
Proof. exact (MK_COMB (@lem1301828 x) (@lem1301829 n)). Qed.
Lemma lem1301831 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1301832 (x : nadd) (n : nat) : (term231 x n) = (term232 x n).
Proof. exact (MK_COMB (@lem1301831) (@lem1301830 x n)). Qed.
Lemma lem1301833 (x : nadd) (n : nat) : (term225 x n) = (term229 x n).
Proof. exact (eq_refl (term225 x n)). Qed.
Lemma lem1301834 (x : nadd) (n : nat) : ((term228 x n) = (term225 x n)) = ((term225 x n) = (term229 x n)).
Proof. exact (MK_COMB (@lem1301832 x n) (@lem1301833 x n)). Qed.
Lemma lem1301835 (x : nadd) (n : nat) : (term225 x n) = (term229 x n).
Proof. exact (EQ_MP (@lem1301834 x n) (@lem1301826 x n)). Qed.
Lemma lem1301836 (x : nadd) (n : nat) : (nadd_rinv x n) = (term229 x n).
Proof. exact (TRANS (@lem1301822 x n) (@lem1301835 x n)). Qed.
Lemma lem1301837 (x : nadd) (n : nat) : (term223 x n) = (term223 x n).
Proof. exact (eq_refl (term223 x n)). Qed.
Lemma lem1301838 (x : nadd) (n : nat) : (term215 x n) = (term240 x n).
Proof. exact (MK_COMB (@lem1301837 x n) (@lem1301836 x n)). Qed.
Lemma lem1301839 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1301840 (x : nadd) (n : nat) : (term236 x n) = (term241 x n).
Proof. exact (MK_COMB (@lem1301839) (@lem1301838 x n)). Qed.
Lemma lem1301841 (n : nat) : (Nat.mul n n) = (Nat.mul n n).
Proof. exact (eq_refl (Nat.mul n n)). Qed.
Lemma lem1301842 (x : nadd) (n : nat) : (term238 x n) = (term242 x n).
Proof. exact (MK_COMB (@lem1301840 x n) (@lem1301841 n)). Qed.
Lemma lem1301843 (x : nadd) (n : nat) : (term242 x n) = (term238 x n).
Proof. exact (SYM (@lem1301842 x n)). Qed.
Lemma lem1301845 (n : nat) : term15 n.
Proof. exact (EQ_MP (@lem1301003 n) (@lem1301002 n)). Qed.
Lemma lem1301846 (x : nadd) (n : nat) : term243 x n.
Proof. exact (@lem1301845 (dest_nadd x n)). Qed.
Lemma lem1301847 (x : nadd) (n : nat) (h1 : term21 x n) : term244 x n.
Proof. exact (@lem1301846 x n (@lem1301009 x n h1)). Qed.
Lemma lem1301848 (x : nadd) (n : nat) (h1 : term244 x n) : term244 x n.
Proof. exact (h1). Qed.
Lemma lem1301849 (m : nat) (x : nadd) (n : nat) (h1 : term244 x n) : term245 x n m.
Proof. exact (@lem1301848 x n h1 m). Qed.
Lemma lem1301850 (m : nat) (x : nadd) (n : nat) : (term245 x n m) = (term246 m x n).
Proof. exact (eq_refl (term245 x n m)). Qed.
Lemma lem1301851 (m : nat) (x : nadd) (n : nat) (h1 : term244 x n) : term246 m x n.
Proof. exact (EQ_MP (@lem1301850 m x n) (@lem1301849 m x n h1)). Qed.
Lemma lem1301854 (m : nat) (x : nadd) (n : nat) (h1 : term244 x n) : m = (term247 m x n).
Proof. exact (proj1 (@lem1301851 m x n h1)). Qed.
Lemma lem1301855 (x : nadd) (n : nat) (h1 : term244 x n) : (Nat.mul n n) = (term248 x n).
Proof. exact (@lem1301854 (Nat.mul n n) x n h1). Qed.
Lemma lem1301856 (x : nadd) (n : nat) : (term241 x n) = (term241 x n).
Proof. exact (eq_refl (term241 x n)). Qed.
Lemma lem1301857 (x : nadd) (n : nat) (h1 : term244 x n) : (term242 x n) = (term249 x n).
Proof. exact (MK_COMB (@lem1301856 x n) (@lem1301855 x n h1)). Qed.
Lemma lem1301858 (x : nadd) (n : nat) (h1 : term244 x n) : (term249 x n) = (term242 x n).
Proof. exact (SYM (@lem1301857 x n h1)). Qed.
Lemma lem1301860 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem1300986 n m) (@lem1300985 m n)). Qed.
Lemma lem1301861 (x : nadd) (n : nat) : (term240 x n) = (term250 x n).
Proof. exact (@lem1301860 (term229 x n) (dest_nadd x n)). Qed.
Lemma lem1301862 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1301863 (x : nadd) (n : nat) : (term241 x n) = (term251 x n).
Proof. exact (MK_COMB (@lem1301862) (@lem1301861 x n)). Qed.
Lemma lem1301864 (x : nadd) (n : nat) : (term248 x n) = (term248 x n).
Proof. exact (eq_refl (term248 x n)). Qed.
Lemma lem1301865 (x : nadd) (n : nat) : (term249 x n) = (term252 x n).
Proof. exact (MK_COMB (@lem1301863 x n) (@lem1301864 x n)). Qed.
Lemma lem1301866 (x : nadd) (n : nat) : (term252 x n) = (term249 x n).
Proof. exact (SYM (@lem1301865 x n)). Qed.
Lemma lem1301868 (m : nat) (n : nat) : (term3 m n) = True.
Proof. exact (EQ_MP (@lem1300980 m n) (@lem1300979 m n)). Qed.
Lemma lem1301869 (x : nadd) (n : nat) : (term252 x n) = True.
Proof. exact (@lem1301868 (term250 x n) (term253 x n)). Qed.
Lemma lem1301870 (x : nadd) (n : nat) : True = (term252 x n).
Proof. exact (SYM (@lem1301869 x n)). Qed.
Lemma lem1301871 (x : nadd) (n : nat) : term252 x n.
Proof. exact (EQ_MP (@lem1301870 x n) (@lem0)). Qed.
Lemma lem1301872 (x : nadd) (n : nat) : term249 x n.
Proof. exact (EQ_MP (@lem1301866 x n) (@lem1301871 x n)). Qed.
Lemma lem1301873 (x : nadd) (n : nat) (h1 : term244 x n) : term242 x n.
Proof. exact (EQ_MP (@lem1301858 x n h1) (@lem1301872 x n)). Qed.
Lemma lem1301874 (x : nadd) (n : nat) : term254 x n.
Proof. exact (fun h0 : term244 x n => @lem1301873 x n h0). Qed.
Lemma lem1301875 (x : nadd) (n : nat) (h1 : term21 x n) : term242 x n.
Proof. exact (@lem1301874 x n (@lem1301847 x n h1)). Qed.
Lemma lem1301876 (x : nadd) (n : nat) (h1 : term21 x n) : term238 x n.
Proof. exact (EQ_MP (@lem1301843 x n) (@lem1301875 x n h1)). Qed.
Lemma lem1301877 (x : nadd) (n : nat) : term238 x n.
Proof. exact (or_elim (@lem1301007 x n) (fun h0 : (dest_nadd x n) = (NUMERAL 0) => @lem1301741 x n h0) (fun h0 : term21 x n => @lem1301876 x n h0)). Qed.
Lemma lem1301878 (A : nat) (x : nadd) (n : nat) : term214 A x n.
Proof. exact (or_intro2 (A = (NUMERAL 0)) (@lem1301877 x n)). Qed.
Lemma lem1301879 (x : nadd) (A : nat) (n : nat) : term209 x A n.
Proof. exact (EQ_MP (@lem1301631 x A n) (@lem1301878 A x n)). Qed.
Lemma lem1301880 (x : nadd) (A : nat) (n : nat) : term184 x A n.
Proof. exact (EQ_MP (@lem1301609 x A n) (@lem1301879 x A n)). Qed.
Lemma lem1301881 (A : nat) (x : nadd) (N : nat) (n : nat) (h1 : term127 N A x) (h2 : term128 N n) : term186 x A n.
Proof. exact (conj (@lem1301601 A x N n h1 h2) (@lem1301880 x A n)). Qed.
Lemma lem1301882 (A : nat) (x : nadd) (N : nat) (n : nat) (h1 : term127 N A x) (h2 : term128 N n) : term185 x A n.
Proof. exact (EQ_MP (@lem1301508 x A n) (@lem1301881 A x N n h1 h2)). Qed.
Lemma lem1301883 (A : nat) (x : nadd) (N : nat) (n : nat) (h1 : term127 N A x) (h2 : term128 N n) : term255 x A n.
Proof. exact (ex_intro (term256 x A n) (term205 A x n) (@lem1301882 A x N n h1 h2)). Qed.
Lemma lem1301884 (A : nat) (x : nadd) (N : nat) (n : nat) (h1 : term127 N A x) (h2 : term128 N n) : term70 x A n.
Proof. exact (@lem1301459 x A n (@lem1301883 A x N n h1 h2)). Qed.
Lemma lem1301885 (N : nat) (x : nadd) (A : nat) (n : nat) (h1 : term127 N A x) (h2 : term128 N n) (h3 : (term70 x A n) = (term131 x A n)) : term131 x A n.
Proof. exact (EQ_MP (@lem1301456 x A n h3) (@lem1301884 A x N n h1 h2)). Qed.
Lemma lem1301886 (A : nat) (x : nadd) (N : nat) (n : nat) (h1 : term127 N A x) (h2 : term128 N n) : term171 x A n.
Proof. exact (fun h0 : (term70 x A n) = (term131 x A n) => @lem1301885 N x A n h1 h2 h0). Qed.
Lemma lem1301887 (n : nat) (N : nat) (A : nat) (x : nadd) (h1 : term127 N A x) : term172 N x A n.
Proof. exact (fun h0 : term128 N n => @lem1301886 A x N n h1 h0). Qed.
Lemma lem1301888 (N : nat) (A : nat) (x : nadd) (n : nat) (h1 : term127 N A x) (h2 : term12 n) : term166 N x A n.
Proof. exact (EQ_MP (@lem1301440 N x A n h2) (@lem1301887 n N A x h1)). Qed.
Lemma lem1301889 (n : nat) (N : nat) (A : nat) (x : nadd) (h1 : term127 N A x) : term166 N x A n.
Proof. exact (or_elim (@lem1301110 n) (fun h0 : n = (NUMERAL 0) => @lem1301358 N x A n h0) (fun h0 : term12 n => @lem1301888 N A x n h1 h0)). Qed.
Lemma lem1301890 (A : nat) (x : nadd) (N : nat) (n : nat) (h1 : term127 N A x) (h2 : term128 N n) : term164 x A n.
Proof. exact (@lem1301889 n N A x h1 (@lem1301212 N n h2)). Qed.
Lemma lem1301891 (A : nat) (x : nadd) (N : nat) (n : nat) (h1 : term127 N A x) (h2 : term128 N n) : term131 x A n.
Proof. exact (@lem1301890 A x N n h1 h2 (@lem1301121 x A n)). Qed.
Lemma lem1301892 (A : nat) (x : nadd) (N : nat) (n : nat) (h1 : term127 N A x) (h2 : term128 N n) : term130 x A n.
Proof. exact (EQ_MP (@lem1301218 x A n) (@lem1301891 A x N n h1 h2)). Qed.
Lemma lem1301893 (n : nat) (N : nat) (A : nat) (x : nadd) (h1 : term127 N A x) : term257 N x A n.
Proof. exact (fun h0 : term128 N n => @lem1301892 A x N n h1 h0). Qed.
Lemma lem1301898 (N : nat) (A : nat) (x : nadd) (h1 : term127 N A x) : term258 N x A.
Proof. exact (fun n : nat => @lem1301893 n N A x h1). Qed.
Lemma lem1301899 (N : nat) (A : nat) (x : nadd) (h1 : term127 N A x) : term259 x A.
Proof. exact (ex_intro (term260 x A) (S N) (@lem1301898 N A x h1)). Qed.
Lemma lem1301900 (N : nat) (A : nat) (x : nadd) (h1 : term127 N A x) : term120 x A.
Proof. exact (ex_intro (term119 x A) (NUMERAL 0) (@lem1301899 N A x h1)). Qed.
Lemma lem1301901 (N : nat) (A : nat) (x : nadd) (h1 : term127 N A x) : term124 x.
Proof. exact (ex_intro (term122 x) A (@lem1301900 N A x h1)). Qed.
Lemma lem1301902 (A : nat) (x : nadd) (h1 : term126 A x) : term124 x.
Proof. exact (ex_elim (@lem1301210 A x h1) (fun N : nat => fun h0 : term261 A x N => @lem1301901 N A x h0)). Qed.
Lemma lem1301903 (x : nadd) (h1 : term125 x) : term124 x.
Proof. exact (ex_elim (@lem1301209 x h1) (fun A : nat => fun h0 : term262 x A => @lem1301902 A x h0)). Qed.
Lemma lem1301904 (x : nadd) : term263 x.
Proof. exact (fun h0 : term125 x => @lem1301903 x h0). Qed.
Lemma lem1301905 (x : nadd) (h1 : term83 x) : term124 x.
Proof. exact (@lem1301904 x (@lem1301208 x h1)). Qed.
Lemma lem1301906 (x : nadd) (h1 : term83 x) : term123 x.
Proof. exact (EQ_MP (@lem1301205 x) (@lem1301905 x h1)). Qed.
Lemma lem1301907 (x : nadd) : term264 x.
Proof. exact (fun h0 : term83 x => @lem1301906 x h0). Qed.
Lemma lem1301912 : term265.
Proof. exact (fun x : nadd => @lem1301907 x). Qed.
