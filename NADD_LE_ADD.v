Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_LE_ADD_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import LE_ADD_spec.
Require Import NADD_ADD_spec.
Require Import nadd_le_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem1274951 (m : nat) : term0 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem1274952 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1274953 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1274952 m) (@lem1274951 m)). Qed.
Lemma lem1274954 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1274953 m n). Qed.
Lemma lem1274955 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1274956 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem1274955 m n) (@lem1274954 m n)). Qed.
Lemma lem1274957 (m : nat) (n : nat) : (term3 m n) = ((term3 m n) = True).
Proof. exact (@lem7 (term3 m n)). Qed.
Lemma lem1274959 : term4.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem1274975 : term5.
Proof. exact (proj1 (@lem1274959)). Qed.
Lemma lem1274976 (m : nat) : term6 m.
Proof. exact (@lem1274975 m). Qed.
Lemma lem1274977 (m : nat) : (term6 m) = ((term7 m) = m).
Proof. exact (eq_refl (term6 m)). Qed.
Lemma lem1274983 (x : nadd) : term8 x.
Proof. exact (@lem1274104 x). Qed.
Lemma lem1274984 (x : nadd) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1274985 (x : nadd) : term9 x.
Proof. exact (EQ_MP (@lem1274984 x) (@lem1274983 x)). Qed.
Lemma lem1274986 (x : nadd) (y : nadd) : term10 x y.
Proof. exact (@lem1274985 x y). Qed.
Lemma lem1274987 (x : nadd) (y : nadd) : (term10 x y) = ((term11 x y) = (term12 x y)).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem1274989 (x : nadd) : term13 x.
Proof. exact (@lem1269692 x). Qed.
Lemma lem1274990 (x : nadd) : (term13 x) = (term14 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem1274991 (x : nadd) : term14 x.
Proof. exact (EQ_MP (@lem1274990 x) (@lem1274989 x)). Qed.
Lemma lem1274992 (x : nadd) (y : nadd) : term15 x y.
Proof. exact (@lem1274991 x y). Qed.
Lemma lem1274993 (x : nadd) (y : nadd) : (term15 x y) = ((nadd_le x y) = (term16 x y)).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem1274996 (x : nadd) (y : nadd) : (nadd_le x y) = (term16 x y).
Proof. exact (EQ_MP (@lem1274993 x y) (@lem1274992 x y)). Qed.
Lemma lem1274997 (x : nadd) (y : nadd) : (term17 x y) = (term18 x y).
Proof. exact (@lem1274996 x (nadd_add x y)). Qed.
Lemma lem1275007 (x : nadd) (y : nadd) : (term11 x y) = (term12 x y).
Proof. exact (EQ_MP (@lem1274987 x y) (@lem1274986 x y)). Qed.
Lemma lem1275008 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1275009 (x : nadd) (y : nadd) (n : nat) : (term19 x y n) = (term20 x y n).
Proof. exact (MK_COMB (@lem1275007 x y) (@lem1275008 n)). Qed.
Lemma lem1275011 {A B : Type'} (f : A -> B) (y : A) : (term21 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1275012 (f : nat -> nat) (y : nat) : (term22 f y) = (f y).
Proof. exact (@lem1275011 nat nat f y). Qed.
Lemma lem1275013 (x : nadd) (y : nadd) (n : nat) : (term23 x y n) = (term20 x y n).
Proof. exact (@lem1275012 (term12 x y) n). Qed.
Lemma lem1275014 (x : nadd) (y : nadd) (n : nat) : (term20 x y n) = (term24 x y n).
Proof. exact (eq_refl (term20 x y n)). Qed.
Lemma lem1275015 (x : nadd) (y : nadd) : (term25 x y) = (term12 x y).
Proof. exact (fun_ext (fun n : nat => @lem1275014 x y n)). Qed.
Lemma lem1275016 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1275017 (x : nadd) (y : nadd) (n : nat) : (term23 x y n) = (term20 x y n).
Proof. exact (MK_COMB (@lem1275015 x y) (@lem1275016 n)). Qed.
Lemma lem1275018 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1275019 (x : nadd) (y : nadd) (n : nat) : (term26 x y n) = (term27 x y n).
Proof. exact (MK_COMB (@lem1275018) (@lem1275017 x y n)). Qed.
Lemma lem1275020 (x : nadd) (y : nadd) (n : nat) : (term20 x y n) = (term24 x y n).
Proof. exact (eq_refl (term20 x y n)). Qed.
Lemma lem1275021 (x : nadd) (y : nadd) (n : nat) : ((term23 x y n) = (term20 x y n)) = ((term20 x y n) = (term24 x y n)).
Proof. exact (MK_COMB (@lem1275019 x y n) (@lem1275020 x y n)). Qed.
Lemma lem1275022 (x : nadd) (y : nadd) (n : nat) : (term20 x y n) = (term24 x y n).
Proof. exact (EQ_MP (@lem1275021 x y n) (@lem1275013 x y n)). Qed.
Lemma lem1275023 (x : nadd) (y : nadd) (n : nat) : (term19 x y n) = (term24 x y n).
Proof. exact (TRANS (@lem1275009 x y n) (@lem1275022 x y n)). Qed.
Lemma lem1275024 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1275025 (x : nadd) (y : nadd) (n : nat) : (term28 x y n) = (term29 x y n).
Proof. exact (MK_COMB (@lem1275024) (@lem1275023 x y n)). Qed.
Lemma lem1275026 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1275027 (x : nadd) (y : nadd) (n : nat) (B : nat) : (term30 x y n B) = (term31 x y n B).
Proof. exact (MK_COMB (@lem1275025 x y n) (@lem1275026 B)). Qed.
Lemma lem1275028 (x : nadd) (n : nat) : (term32 x n) = (term32 x n).
Proof. exact (eq_refl (term32 x n)). Qed.
Lemma lem1275029 (x : nadd) (y : nadd) (n : nat) (B : nat) : (term33 x y n B) = (term34 x y n B).
Proof. exact (MK_COMB (@lem1275028 x n) (@lem1275027 x y n B)). Qed.
Lemma lem1275030 (x : nadd) (y : nadd) (B : nat) : (term35 x y B) = (term36 x y B).
Proof. exact (fun_ext (fun n : nat => @lem1275029 x y n B)). Qed.
Lemma lem1275031 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1275032 (x : nadd) (y : nadd) (B : nat) : (term37 x y B) = (term38 x y B).
Proof. exact (MK_COMB (@lem1275031) (@lem1275030 x y B)). Qed.
Lemma lem1275037 (x : nadd) (y : nadd) : (term39 x y) = (term40 x y).
Proof. exact (fun_ext (fun B : nat => @lem1275032 x y B)). Qed.
Lemma lem1275038 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1275039 (x : nadd) (y : nadd) : (term18 x y) = (term41 x y).
Proof. exact (MK_COMB (@lem1275038) (@lem1275037 x y)). Qed.
Lemma lem1275044 (x : nadd) (y : nadd) : (term17 x y) = (term41 x y).
Proof. exact (TRANS (@lem1274997 x y) (@lem1275039 x y)). Qed.
Lemma lem1275045 (x : nadd) (y : nadd) : (term41 x y) = (term17 x y).
Proof. exact (SYM (@lem1275044 x y)). Qed.
Lemma lem1275053 (m : nat) : (term7 m) = m.
Proof. exact (EQ_MP (@lem1274977 m) (@lem1274976 m)). Qed.
Lemma lem1275054 (x : nadd) (y : nadd) (n : nat) : (term42 x y n) = (term24 x y n).
Proof. exact (@lem1275053 (term24 x y n)). Qed.
Lemma lem1275055 (x : nadd) (n : nat) : (term32 x n) = (term32 x n).
Proof. exact (eq_refl (term32 x n)). Qed.
Lemma lem1275056 (x : nadd) (y : nadd) (n : nat) : (term43 x y n) = (term44 x y n).
Proof. exact (MK_COMB (@lem1275055 x n) (@lem1275054 x y n)). Qed.
Lemma lem1275058 (m : nat) (n : nat) : (term3 m n) = True.
Proof. exact (EQ_MP (@lem1274957 m n) (@lem1274956 m n)). Qed.
Lemma lem1275059 (x : nadd) (y : nadd) (n : nat) : (term44 x y n) = True.
Proof. exact (@lem1275058 (dest_nadd x n) (dest_nadd y n)). Qed.
Lemma lem1275060 (x : nadd) (y : nadd) (n : nat) : (term43 x y n) = True.
Proof. exact (TRANS (@lem1275056 x y n) (@lem1275059 x y n)). Qed.
Lemma lem1275061 (x : nadd) (y : nadd) : (term45 x y) = term46.
Proof. exact (fun_ext (fun n : nat => @lem1275060 x y n)). Qed.
Lemma lem1275062 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1275063 (x : nadd) (y : nadd) : (term47 x y) = term48.
Proof. exact (MK_COMB (@lem1275062) (@lem1275061 x y)). Qed.
Lemma lem1275065 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1275066 (t : Prop) : (term50 t) = t.
Proof. exact (@lem1275065 nat t). Qed.
Lemma lem1275067 : term48 = True.
Proof. exact (@lem1275066 True). Qed.
Lemma lem1275068 (x : nadd) (y : nadd) : (term47 x y) = True.
Proof. exact (TRANS (@lem1275063 x y) (@lem1275067)). Qed.
Lemma lem1275069 (x : nadd) (y : nadd) : True = (term47 x y).
Proof. exact (SYM (@lem1275068 x y)). Qed.
Lemma lem1275070 (x : nadd) (y : nadd) : term47 x y.
Proof. exact (EQ_MP (@lem1275069 x y) (@lem0)). Qed.
Lemma lem1275071 (x : nadd) (y : nadd) : term41 x y.
Proof. exact (ex_intro (term40 x y) (NUMERAL 0) (@lem1275070 x y)). Qed.
Lemma lem1275072 (x : nadd) (y : nadd) : term17 x y.
Proof. exact (EQ_MP (@lem1275045 x y) (@lem1275071 x y)). Qed.
Lemma lem1275077 (x : nadd) : term51 x.
Proof. exact (fun y : nadd => @lem1275072 x y). Qed.
Lemma lem1275082 : term52.
Proof. exact (fun x : nadd => @lem1275077 x). Qed.
