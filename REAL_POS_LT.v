Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POS_LT_term_abbrevs.
Require Import LT_0_spec.
Require Import LT_NZ_spec.
Require Import REAL_LT_NZ_spec.
Require Import thm0_spec.
Require Import thm1340231_spec.
Require Import thm7_spec.
Lemma lem1384525 (n : nat) (h1 : (term0 n) = (term1 n)) : (term0 n) = (term1 n).
Proof. exact (h1). Qed.
Lemma lem1384526 (n : nat) (h1 : (term0 n) = (term1 n)) : (term1 n) = (term0 n).
Proof. exact (SYM (@lem1384525 n h1)). Qed.
Lemma lem1384527 (n : nat) (h1 : (term1 n) = (term0 n)) : (term1 n) = (term0 n).
Proof. exact (h1). Qed.
Lemma lem1384528 (n : nat) (h1 : (term1 n) = (term0 n)) : (term0 n) = (term1 n).
Proof. exact (SYM (@lem1384527 n h1)). Qed.
Lemma lem1384529 (n : nat) : ((term0 n) = (term1 n)) = ((term1 n) = (term0 n)).
Proof. exact (prop_ext (fun h1 : (term0 n) = (term1 n) => @lem1384526 n h1) (fun h1 : (term1 n) = (term0 n) => @lem1384528 n h1)). Qed.
Lemma lem1384530 : term2 = term3.
Proof. exact (fun_ext (fun n : nat => @lem1384529 n)). Qed.
Lemma lem1384531 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1384532 : term4 = term5.
Proof. exact (MK_COMB (@lem1384531) (@lem1384530)). Qed.
Lemma lem1384533 : term5.
Proof. exact (EQ_MP (@lem1384532) (@lem98731)). Qed.
Lemma lem1384534 (n : nat) : term6 n.
Proof. exact (@lem91530 n). Qed.
Lemma lem1384535 (n : nat) : (term6 n) = (term7 n).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem1384536 (n : nat) : term7 n.
Proof. exact (EQ_MP (@lem1384535 n) (@lem1384534 n)). Qed.
Lemma lem1384537 (n : nat) : (term7 n) = ((term7 n) = True).
Proof. exact (@lem7 (term7 n)). Qed.
Lemma lem1384539 (n : nat) : term8 n.
Proof. exact (@lem1384533 n). Qed.
Lemma lem1384540 (n : nat) : (term8 n) = ((term1 n) = (term0 n)).
Proof. exact (eq_refl (term8 n)). Qed.
Lemma lem1384543 (n : nat) (h1 : (term9 n) = (term10 n)) : (term9 n) = (term10 n).
Proof. exact (h1). Qed.
Lemma lem1384544 (n : nat) (h1 : (term9 n) = (term10 n)) : (term10 n) = (term9 n).
Proof. exact (SYM (@lem1384543 n h1)). Qed.
Lemma lem1384545 (n : nat) (h1 : (term10 n) = (term9 n)) : (term10 n) = (term9 n).
Proof. exact (h1). Qed.
Lemma lem1384546 (n : nat) (h1 : (term10 n) = (term9 n)) : (term9 n) = (term10 n).
Proof. exact (SYM (@lem1384545 n h1)). Qed.
Lemma lem1384547 (n : nat) : ((term9 n) = (term10 n)) = ((term10 n) = (term9 n)).
Proof. exact (prop_ext (fun h1 : (term9 n) = (term10 n) => @lem1384544 n h1) (fun h1 : (term10 n) = (term9 n) => @lem1384546 n h1)). Qed.
Lemma lem1384548 : term11 = term12.
Proof. exact (fun_ext (fun n : nat => @lem1384547 n)). Qed.
Lemma lem1384549 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1384550 : term13 = term14.
Proof. exact (MK_COMB (@lem1384549) (@lem1384548)). Qed.
Lemma lem1384551 : term14.
Proof. exact (EQ_MP (@lem1384550) (@lem1384523)). Qed.
Lemma lem1384552 (n : nat) : term15 n.
Proof. exact (@lem1384551 (S n)). Qed.
Lemma lem1384553 (n : nat) : (term15 n) = ((term16 n) = (term17 n)).
Proof. exact (eq_refl (term15 n)). Qed.
Lemma lem1384555 (m : nat) : term18 m.
Proof. exact (@lem1340231 m). Qed.
Lemma lem1384556 (m : nat) : (term18 m) = (term19 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem1384557 (m : nat) : term19 m.
Proof. exact (EQ_MP (@lem1384556 m) (@lem1384555 m)). Qed.
Lemma lem1384558 (m : nat) (n : nat) : term20 m n.
Proof. exact (@lem1384557 m n). Qed.
Lemma lem1384559 (m : nat) (n : nat) : (term20 m n) = (((real_of_num m) = (real_of_num n)) = (m = n)).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem1384562 (n : nat) : (term16 n) = (term17 n).
Proof. exact (EQ_MP (@lem1384553 n) (@lem1384552 n)). Qed.
Lemma lem1384564 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem1384559 m n) (@lem1384558 m n)). Qed.
Lemma lem1384565 (n : nat) : ((term21 n) = term22) = ((S n) = (NUMERAL 0)).
Proof. exact (@lem1384564 (S n) (NUMERAL 0)). Qed.
Lemma lem1384568 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1384569 (n : nat) : (term17 n) = (term23 n).
Proof. exact (MK_COMB (@lem1384568) (@lem1384565 n)). Qed.
Lemma lem1384570 (n : nat) : (term16 n) = (term23 n).
Proof. exact (TRANS (@lem1384562 n) (@lem1384569 n)). Qed.
Lemma lem1384571 (n : nat) : (term23 n) = (term16 n).
Proof. exact (SYM (@lem1384570 n)). Qed.
Lemma lem1384573 (n : nat) : (term1 n) = (term0 n).
Proof. exact (EQ_MP (@lem1384540 n) (@lem1384539 n)). Qed.
Lemma lem1384574 (n : nat) : (term23 n) = (term7 n).
Proof. exact (@lem1384573 (S n)). Qed.
Lemma lem1384576 (n : nat) : (term7 n) = True.
Proof. exact (EQ_MP (@lem1384537 n) (@lem1384536 n)). Qed.
Lemma lem1384577 (n : nat) : (term23 n) = True.
Proof. exact (TRANS (@lem1384574 n) (@lem1384576 n)). Qed.
Lemma lem1384578 (n : nat) : True = (term23 n).
Proof. exact (SYM (@lem1384577 n)). Qed.
Lemma lem1384579 (n : nat) : term23 n.
Proof. exact (EQ_MP (@lem1384578 n) (@lem0)). Qed.
Lemma lem1384580 (n : nat) : term16 n.
Proof. exact (EQ_MP (@lem1384571 n) (@lem1384579 n)). Qed.
Lemma lem1384585 : term24.
Proof. exact (fun n : nat => @lem1384580 n). Qed.
