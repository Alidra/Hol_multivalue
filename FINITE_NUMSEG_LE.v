Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_NUMSEG_LE_term_abbrevs.
Require Import HAS_SIZE_spec.
Require Import HAS_SIZE_NUMSEG_LE_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem4621937 {_100044 : Type'} (s : _100044 -> Prop) : term0 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem4621938 {_100044 : Type'} (s : _100044 -> Prop) : (term0 _100044 s) = (term1 _100044 s).
Proof. exact (eq_refl (term0 _100044 s)). Qed.
Lemma lem4621939 {_100044 : Type'} (s : _100044 -> Prop) : term1 _100044 s.
Proof. exact (EQ_MP (@lem4621938 _100044 s) (@lem4621937 _100044 s)). Qed.
Lemma lem4621940 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term2 _100044 s n.
Proof. exact (@lem4621939 _100044 s n). Qed.
Lemma lem4621941 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term2 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term3 _100044 s n)).
Proof. exact (eq_refl (term2 _100044 s n)). Qed.
Lemma lem4621948 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term3 _100044 s n).
Proof. exact (EQ_MP (@lem4621941 _100044 s n) (@lem4621940 _100044 s n)). Qed.
Lemma lem4621949 (s : nat -> Prop) (n : nat) : (@HAS_SIZE nat s n) = (term4 s n).
Proof. exact (@lem4621948 nat s n). Qed.
Lemma lem4621950 (n : nat) : (term5 n) = (term6 n).
Proof. exact (@lem4621949 (term7 n) (term8 n)). Qed.
Lemma lem4621963 : term9 = term10.
Proof. exact (fun_ext (fun n : nat => @lem4621950 n)). Qed.
Lemma lem4621964 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4621965 : term11 = term12.
Proof. exact (MK_COMB (@lem4621964) (@lem4621963)). Qed.
Lemma lem4621970 : term12.
Proof. exact (EQ_MP (@lem4621965) (@lem4621936)). Qed.
Lemma lem4621971 (n : nat) : term13 n.
Proof. exact (@lem4621970 n). Qed.
Lemma lem4621972 (n : nat) : (term13 n) = (term6 n).
Proof. exact (eq_refl (term13 n)). Qed.
Lemma lem4621973 (n : nat) : term6 n.
Proof. exact (EQ_MP (@lem4621972 n) (@lem4621971 n)). Qed.
Lemma lem4621975 (n : nat) : term14 n.
Proof. exact (proj1 (@lem4621973 n)). Qed.
Lemma lem4621976 (n : nat) : (term14 n) = ((term14 n) = True).
Proof. exact (@lem7 (term14 n)). Qed.
Lemma lem4621983 (n : nat) : (term14 n) = True.
Proof. exact (EQ_MP (@lem4621976 n) (@lem4621975 n)). Qed.
Lemma lem4621984 : term15 = term16.
Proof. exact (fun_ext (fun n : nat => @lem4621983 n)). Qed.
Lemma lem4621985 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4621986 : term17 = term18.
Proof. exact (MK_COMB (@lem4621985) (@lem4621984)). Qed.
Lemma lem4621988 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4621989 (t : Prop) : (term20 t) = t.
Proof. exact (@lem4621988 nat t). Qed.
Lemma lem4621990 : term18 = True.
Proof. exact (@lem4621989 True). Qed.
Lemma lem4621991 : term17 = True.
Proof. exact (TRANS (@lem4621986) (@lem4621990)). Qed.
Lemma lem4621992 : True = term17.
Proof. exact (SYM (@lem4621991)). Qed.
Lemma lem4621993 : term17.
Proof. exact (EQ_MP (@lem4621992) (@lem0)). Qed.
