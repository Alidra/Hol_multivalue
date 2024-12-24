Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_NUMSEG_LE_term_abbrevs.
Require Import HAS_SIZE_spec.
Require Import HAS_SIZE_NUMSEG_LE_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem4621994 {_100044 : Type'} (s : _100044 -> Prop) : term0 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem4621995 {_100044 : Type'} (s : _100044 -> Prop) : (term0 _100044 s) = (term1 _100044 s).
Proof. exact (eq_refl (term0 _100044 s)). Qed.
Lemma lem4621996 {_100044 : Type'} (s : _100044 -> Prop) : term1 _100044 s.
Proof. exact (EQ_MP (@lem4621995 _100044 s) (@lem4621994 _100044 s)). Qed.
Lemma lem4621997 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term2 _100044 s n.
Proof. exact (@lem4621996 _100044 s n). Qed.
Lemma lem4621998 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term2 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term3 _100044 s n)).
Proof. exact (eq_refl (term2 _100044 s n)). Qed.
Lemma lem4622005 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term3 _100044 s n).
Proof. exact (EQ_MP (@lem4621998 _100044 s n) (@lem4621997 _100044 s n)). Qed.
Lemma lem4622006 (s : nat -> Prop) (n : nat) : (@HAS_SIZE nat s n) = (term4 s n).
Proof. exact (@lem4622005 nat s n). Qed.
Lemma lem4622007 (n : nat) : (term5 n) = (term6 n).
Proof. exact (@lem4622006 (term7 n) (term8 n)). Qed.
Lemma lem4622020 : term9 = term10.
Proof. exact (fun_ext (fun n : nat => @lem4622007 n)). Qed.
Lemma lem4622021 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4622022 : term11 = term12.
Proof. exact (MK_COMB (@lem4622021) (@lem4622020)). Qed.
Lemma lem4622027 : term12.
Proof. exact (EQ_MP (@lem4622022) (@lem4621936)). Qed.
Lemma lem4622028 (n : nat) : term13 n.
Proof. exact (@lem4622027 n). Qed.
Lemma lem4622029 (n : nat) : (term13 n) = (term6 n).
Proof. exact (eq_refl (term13 n)). Qed.
Lemma lem4622030 (n : nat) : term6 n.
Proof. exact (EQ_MP (@lem4622029 n) (@lem4622028 n)). Qed.
Lemma lem4622042 (n : nat) : (term14 n) = (term8 n).
Proof. exact (proj2 (@lem4622030 n)). Qed.
Lemma lem4622043 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4622044 (n : nat) : (term15 n) = (term16 n).
Proof. exact (MK_COMB (@lem4622043) (@lem4622042 n)). Qed.
Lemma lem4622045 (n : nat) : (term8 n) = (term8 n).
Proof. exact (eq_refl (term8 n)). Qed.
Lemma lem4622046 (n : nat) : ((term14 n) = (term8 n)) = ((term8 n) = (term8 n)).
Proof. exact (MK_COMB (@lem4622044 n) (@lem4622045 n)). Qed.
Lemma lem4622048 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4622049 (x : nat) : (x = x) = True.
Proof. exact (@lem4622048 nat x). Qed.
Lemma lem4622050 (n : nat) : ((term8 n) = (term8 n)) = True.
Proof. exact (@lem4622049 (term8 n)). Qed.
Lemma lem4622051 (n : nat) : ((term14 n) = (term8 n)) = True.
Proof. exact (TRANS (@lem4622046 n) (@lem4622050 n)). Qed.
Lemma lem4622052 : term17 = term18.
Proof. exact (fun_ext (fun n : nat => @lem4622051 n)). Qed.
Lemma lem4622053 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4622054 : term19 = term20.
Proof. exact (MK_COMB (@lem4622053) (@lem4622052)). Qed.
Lemma lem4622056 {A : Type'} (t : Prop) : (term21 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4622057 (t : Prop) : (term22 t) = t.
Proof. exact (@lem4622056 nat t). Qed.
Lemma lem4622058 : term20 = True.
Proof. exact (@lem4622057 True). Qed.
Lemma lem4622059 : term19 = True.
Proof. exact (TRANS (@lem4622054) (@lem4622058)). Qed.
Lemma lem4622060 : True = term19.
Proof. exact (SYM (@lem4622059)). Qed.
Lemma lem4622061 : term19.
Proof. exact (EQ_MP (@lem4622060) (@lem0)). Qed.
