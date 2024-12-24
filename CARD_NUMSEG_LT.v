Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_NUMSEG_LT_term_abbrevs.
Require Import HAS_SIZE_spec.
Require Import HAS_SIZE_NUMSEG_LT_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem4621385 {_100044 : Type'} (s : _100044 -> Prop) : term0 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem4621386 {_100044 : Type'} (s : _100044 -> Prop) : (term0 _100044 s) = (term1 _100044 s).
Proof. exact (eq_refl (term0 _100044 s)). Qed.
Lemma lem4621387 {_100044 : Type'} (s : _100044 -> Prop) : term1 _100044 s.
Proof. exact (EQ_MP (@lem4621386 _100044 s) (@lem4621385 _100044 s)). Qed.
Lemma lem4621388 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term2 _100044 s n.
Proof. exact (@lem4621387 _100044 s n). Qed.
Lemma lem4621389 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term2 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term3 _100044 s n)).
Proof. exact (eq_refl (term2 _100044 s n)). Qed.
Lemma lem4621396 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term3 _100044 s n).
Proof. exact (EQ_MP (@lem4621389 _100044 s n) (@lem4621388 _100044 s n)). Qed.
Lemma lem4621397 (s : nat -> Prop) (n : nat) : (@HAS_SIZE nat s n) = (term4 s n).
Proof. exact (@lem4621396 nat s n). Qed.
Lemma lem4621398 (n : nat) : (term5 n) = (term6 n).
Proof. exact (@lem4621397 (term7 n) n). Qed.
Lemma lem4621411 : term8 = term9.
Proof. exact (fun_ext (fun n : nat => @lem4621398 n)). Qed.
Lemma lem4621412 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4621413 : term10 = term11.
Proof. exact (MK_COMB (@lem4621412) (@lem4621411)). Qed.
Lemma lem4621418 : term11.
Proof. exact (EQ_MP (@lem4621413) (@lem4621384)). Qed.
Lemma lem4621419 (n : nat) : term12 n.
Proof. exact (@lem4621418 n). Qed.
Lemma lem4621420 (n : nat) : (term12 n) = (term6 n).
Proof. exact (eq_refl (term12 n)). Qed.
Lemma lem4621421 (n : nat) : term6 n.
Proof. exact (EQ_MP (@lem4621420 n) (@lem4621419 n)). Qed.
Lemma lem4621433 (n : nat) : (term13 n) = n.
Proof. exact (proj2 (@lem4621421 n)). Qed.
Lemma lem4621434 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4621435 (n : nat) : (term14 n) = (@eq nat n).
Proof. exact (MK_COMB (@lem4621434) (@lem4621433 n)). Qed.
Lemma lem4621436 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem4621437 (n : nat) : ((term13 n) = n) = (n = n).
Proof. exact (MK_COMB (@lem4621435 n) (@lem4621436 n)). Qed.
Lemma lem4621439 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4621440 (x : nat) : (x = x) = True.
Proof. exact (@lem4621439 nat x). Qed.
Lemma lem4621441 (n : nat) : (n = n) = True.
Proof. exact (@lem4621440 n). Qed.
Lemma lem4621442 (n : nat) : ((term13 n) = n) = True.
Proof. exact (TRANS (@lem4621437 n) (@lem4621441 n)). Qed.
Lemma lem4621443 : term15 = term16.
Proof. exact (fun_ext (fun n : nat => @lem4621442 n)). Qed.
Lemma lem4621444 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4621445 : term17 = term18.
Proof. exact (MK_COMB (@lem4621444) (@lem4621443)). Qed.
Lemma lem4621447 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4621448 (t : Prop) : (term20 t) = t.
Proof. exact (@lem4621447 nat t). Qed.
Lemma lem4621449 : term18 = True.
Proof. exact (@lem4621448 True). Qed.
Lemma lem4621450 : term17 = True.
Proof. exact (TRANS (@lem4621445) (@lem4621449)). Qed.
Lemma lem4621451 : True = term17.
Proof. exact (SYM (@lem4621450)). Qed.
Lemma lem4621452 : term17.
Proof. exact (EQ_MP (@lem4621451) (@lem0)). Qed.
