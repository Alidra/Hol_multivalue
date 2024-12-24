Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ZPOW_INV_term_abbrevs.
Require Import REAL_INV_ZPOW_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem3174479 (x : real) : term0 x.
Proof. exact (@lem3174478 x). Qed.
Lemma lem3174480 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem3174481 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem3174480 x) (@lem3174479 x)). Qed.
Lemma lem3174482 (x : real) (n : int) : term2 x n.
Proof. exact (@lem3174481 x n). Qed.
Lemma lem3174483 (x : real) (n : int) : (term2 x n) = ((term3 x n) = (term4 x n)).
Proof. exact (eq_refl (term2 x n)). Qed.
Lemma lem3174496 (x : real) (n : int) : (term3 x n) = (term4 x n).
Proof. exact (EQ_MP (@lem3174483 x n) (@lem3174482 x n)). Qed.
Lemma lem3174497 (x : real) (n : int) : (term5 x n) = (term5 x n).
Proof. exact (eq_refl (term5 x n)). Qed.
Lemma lem3174498 (x : real) (n : int) : ((term4 x n) = (term3 x n)) = ((term4 x n) = (term4 x n)).
Proof. exact (MK_COMB (@lem3174497 x n) (@lem3174496 x n)). Qed.
Lemma lem3174500 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3174501 (x : real) : (x = x) = True.
Proof. exact (@lem3174500 real x). Qed.
Lemma lem3174502 (x : real) (n : int) : ((term4 x n) = (term4 x n)) = True.
Proof. exact (@lem3174501 (term4 x n)). Qed.
Lemma lem3174503 (x : real) (n : int) : ((term4 x n) = (term3 x n)) = True.
Proof. exact (TRANS (@lem3174498 x n) (@lem3174502 x n)). Qed.
Lemma lem3174504 (x : real) : (term6 x) = term7.
Proof. exact (fun_ext (fun n : int => @lem3174503 x n)). Qed.
Lemma lem3174505 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3174506 (x : real) : (term8 x) = term9.
Proof. exact (MK_COMB (@lem3174505) (@lem3174504 x)). Qed.
Lemma lem3174508 {A : Type'} (t : Prop) : (term10 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3174509 (t : Prop) : (term11 t) = t.
Proof. exact (@lem3174508 int t). Qed.
Lemma lem3174510 : term9 = True.
Proof. exact (@lem3174509 True). Qed.
Lemma lem3174511 (x : real) : (term8 x) = True.
Proof. exact (TRANS (@lem3174506 x) (@lem3174510)). Qed.
Lemma lem3174512 : term12 = term13.
Proof. exact (fun_ext (fun x : real => @lem3174511 x)). Qed.
Lemma lem3174513 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3174514 : term14 = term15.
Proof. exact (MK_COMB (@lem3174513) (@lem3174512)). Qed.
Lemma lem3174516 {A : Type'} (t : Prop) : (term10 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3174517 (t : Prop) : (term16 t) = t.
Proof. exact (@lem3174516 real t). Qed.
Lemma lem3174518 : term15 = True.
Proof. exact (@lem3174517 True). Qed.
Lemma lem3174519 : term14 = True.
Proof. exact (TRANS (@lem3174514) (@lem3174518)). Qed.
Lemma lem3174520 : True = term14.
Proof. exact (SYM (@lem3174519)). Qed.
Lemma lem3174521 : term14.
Proof. exact (EQ_MP (@lem3174520) (@lem0)). Qed.
