Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXP_1_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import MULT_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm80360_spec.
Require Import thm86199_spec.
Lemma lem87886 : term0.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem87902 : term1.
Proof. exact (proj1 (@lem87886)). Qed.
Lemma lem87903 (m : nat) : term2 m.
Proof. exact (@lem87902 m). Qed.
Lemma lem87904 (m : nat) : (term2 m) = ((term3 m) = m).
Proof. exact (eq_refl (term2 m)). Qed.
Lemma lem87910 : term4.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem87911 : term5.
Proof. exact (proj2 (@lem87910)). Qed.
Lemma lem87912 : term6.
Proof. exact (proj2 (@lem87911)). Qed.
Lemma lem87913 : term7.
Proof. exact (proj2 (@lem87912)). Qed.
Lemma lem87914 : term8.
Proof. exact (proj2 (@lem87913)). Qed.
Lemma lem87915 (m : nat) : term9 m.
Proof. exact (@lem87914 m). Qed.
Lemma lem87916 (m : nat) : (term9 m) = (term10 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem87917 (m : nat) : term10 m.
Proof. exact (EQ_MP (@lem87916 m) (@lem87915 m)). Qed.
Lemma lem87918 (m : nat) (n : nat) : term11 m n.
Proof. exact (@lem87917 m n). Qed.
Lemma lem87919 (m : nat) (n : nat) : (term11 m n) = ((term12 m n) = (term13 m n)).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem87936 : term14.
Proof. exact (proj1 (@lem87910)). Qed.
Lemma lem87937 (m : nat) : term15 m.
Proof. exact (@lem87936 m). Qed.
Lemma lem87938 (m : nat) : (term15 m) = ((term16 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem87944 : term17.
Proof. exact (proj2 (@lem86199)). Qed.
Lemma lem87945 (m : nat) : term18 m.
Proof. exact (@lem87944 m). Qed.
Lemma lem87946 (m : nat) : (term18 m) = (term19 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem87947 (m : nat) : term19 m.
Proof. exact (EQ_MP (@lem87946 m) (@lem87945 m)). Qed.
Lemma lem87948 (m : nat) (n : nat) : term20 m n.
Proof. exact (@lem87947 m n). Qed.
Lemma lem87949 (m : nat) (n : nat) : (term20 m n) = ((term21 m n) = (term22 m n)).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem87951 : term23.
Proof. exact (proj1 (@lem86199)). Qed.
Lemma lem87952 (m : nat) : term24 m.
Proof. exact (@lem87951 m). Qed.
Lemma lem87953 (m : nat) : (term24 m) = ((term25 m) = term26).
Proof. exact (eq_refl (term24 m)). Qed.
Lemma lem87962 : term26 = term27.
Proof. exact (EQ_MP (@lem80360) (@lem0)). Qed.
Lemma lem87963 (n : nat) : (Nat.pow n) = (Nat.pow n).
Proof. exact (eq_refl (Nat.pow n)). Qed.
Lemma lem87964 (n : nat) : (term28 n) = (term29 n).
Proof. exact (MK_COMB (@lem87963 n) (@lem87962)). Qed.
Lemma lem87966 (m : nat) (n : nat) : (term21 m n) = (term22 m n).
Proof. exact (EQ_MP (@lem87949 m n) (@lem87948 m n)). Qed.
Lemma lem87967 (n : nat) : (term29 n) = (term30 n).
Proof. exact (@lem87966 n (NUMERAL 0)). Qed.
Lemma lem87969 (m : nat) : (term25 m) = term26.
Proof. exact (EQ_MP (@lem87953 m) (@lem87952 m)). Qed.
Lemma lem87970 (n : nat) : (term25 n) = term26.
Proof. exact (@lem87969 n). Qed.
Lemma lem87972 : term26 = term27.
Proof. exact (EQ_MP (@lem80360) (@lem0)). Qed.
Lemma lem87973 (n : nat) : (term25 n) = term27.
Proof. exact (TRANS (@lem87970 n) (@lem87972)). Qed.
Lemma lem87974 (n : nat) : (Nat.mul n) = (Nat.mul n).
Proof. exact (eq_refl (Nat.mul n)). Qed.
Lemma lem87975 (n : nat) : (term30 n) = (term31 n).
Proof. exact (MK_COMB (@lem87974 n) (@lem87973 n)). Qed.
Lemma lem87977 (m : nat) (n : nat) : (term12 m n) = (term13 m n).
Proof. exact (EQ_MP (@lem87919 m n) (@lem87918 m n)). Qed.
Lemma lem87978 (n : nat) : (term31 n) = (term32 n).
Proof. exact (@lem87977 n (NUMERAL 0)). Qed.
Lemma lem87980 (m : nat) : (term16 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem87938 m) (@lem87937 m)). Qed.
Lemma lem87981 (n : nat) : (term16 n) = (NUMERAL 0).
Proof. exact (@lem87980 n). Qed.
Lemma lem87982 (n : nat) : (Nat.add n) = (Nat.add n).
Proof. exact (eq_refl (Nat.add n)). Qed.
Lemma lem87983 (n : nat) : (term32 n) = (term3 n).
Proof. exact (MK_COMB (@lem87982 n) (@lem87981 n)). Qed.
Lemma lem87985 (m : nat) : (term3 m) = m.
Proof. exact (EQ_MP (@lem87904 m) (@lem87903 m)). Qed.
Lemma lem87986 (n : nat) : (term3 n) = n.
Proof. exact (@lem87985 n). Qed.
Lemma lem87987 (n : nat) : (term32 n) = n.
Proof. exact (TRANS (@lem87983 n) (@lem87986 n)). Qed.
Lemma lem87988 (n : nat) : (term31 n) = n.
Proof. exact (TRANS (@lem87978 n) (@lem87987 n)). Qed.
Lemma lem87989 (n : nat) : (term30 n) = n.
Proof. exact (TRANS (@lem87975 n) (@lem87988 n)). Qed.
Lemma lem87990 (n : nat) : (term29 n) = n.
Proof. exact (TRANS (@lem87967 n) (@lem87989 n)). Qed.
Lemma lem87991 (n : nat) : (term28 n) = n.
Proof. exact (TRANS (@lem87964 n) (@lem87990 n)). Qed.
Lemma lem87992 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem87993 (n : nat) : (term33 n) = (@eq nat n).
Proof. exact (MK_COMB (@lem87992) (@lem87991 n)). Qed.
Lemma lem87994 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem87995 (n : nat) : ((term28 n) = n) = (n = n).
Proof. exact (MK_COMB (@lem87993 n) (@lem87994 n)). Qed.
Lemma lem87997 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem87998 (x : nat) : (x = x) = True.
Proof. exact (@lem87997 nat x). Qed.
Lemma lem87999 (n : nat) : (n = n) = True.
Proof. exact (@lem87998 n). Qed.
Lemma lem88000 (n : nat) : ((term28 n) = n) = True.
Proof. exact (TRANS (@lem87995 n) (@lem87999 n)). Qed.
Lemma lem88001 : term34 = term35.
Proof. exact (fun_ext (fun n : nat => @lem88000 n)). Qed.
Lemma lem88002 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem88003 : term36 = term37.
Proof. exact (MK_COMB (@lem88002) (@lem88001)). Qed.
Lemma lem88005 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem88006 (t : Prop) : (term39 t) = t.
Proof. exact (@lem88005 nat t). Qed.
Lemma lem88007 : term37 = True.
Proof. exact (@lem88006 True). Qed.
Lemma lem88008 : term36 = True.
Proof. exact (TRANS (@lem88003) (@lem88007)). Qed.
Lemma lem88009 : True = term36.
Proof. exact (SYM (@lem88008)). Qed.
Lemma lem88010 : term36.
Proof. exact (EQ_MP (@lem88009) (@lem0)). Qed.
