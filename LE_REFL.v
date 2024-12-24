Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LE_REFL_term_abbrevs.
Require Import thm0_spec.
Require Import thm1831_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm89498_spec.
Lemma lem91531 : term0.
Proof. exact (proj2 (@lem89498)). Qed.
Lemma lem91532 (m : nat) : term1 m.
Proof. exact (@lem91531 m). Qed.
Lemma lem91533 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem91534 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem91533 m) (@lem91532 m)). Qed.
Lemma lem91535 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem91534 m n). Qed.
Lemma lem91536 (m : nat) (n : nat) : (term3 m n) = ((term4 m n) = (term5 m n)).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem91538 : term6.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem91539 (m : nat) : term7 m.
Proof. exact (@lem91538 m). Qed.
Lemma lem91540 (m : nat) : (term7 m) = ((term8 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem91543 (P : nat -> Prop) : term9 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem91544 : term10.
Proof. exact (@lem91543 term11). Qed.
Lemma lem91545 : term12 = term13.
Proof. exact (eq_refl term12). Qed.
Lemma lem91546 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem91547 : term14 = term15.
Proof. exact (MK_COMB (@lem91546) (@lem91545)). Qed.
Lemma lem91548 (n : nat) : (term16 n) = (Peano.le n n).
Proof. exact (eq_refl (term16 n)). Qed.
Lemma lem91549 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem91550 (n : nat) : (term17 n) = (term18 n).
Proof. exact (MK_COMB (@lem91549) (@lem91548 n)). Qed.
Lemma lem91551 (n : nat) : (term19 n) = (term20 n).
Proof. exact (eq_refl (term19 n)). Qed.
Lemma lem91552 (n : nat) : (term21 n) = (term22 n).
Proof. exact (MK_COMB (@lem91550 n) (@lem91551 n)). Qed.
Lemma lem91553 : term23 = term24.
Proof. exact (fun_ext (fun n : nat => @lem91552 n)). Qed.
Lemma lem91554 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem91555 : term25 = term26.
Proof. exact (MK_COMB (@lem91554) (@lem91553)). Qed.
Lemma lem91556 : term27 = term28.
Proof. exact (MK_COMB (@lem91547) (@lem91555)). Qed.
Lemma lem91557 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem91558 : term29 = term30.
Proof. exact (MK_COMB (@lem91557) (@lem91556)). Qed.
Lemma lem91559 (n : nat) : (term16 n) = (Peano.le n n).
Proof. exact (eq_refl (term16 n)). Qed.
Lemma lem91560 : term31 = term11.
Proof. exact (fun_ext (fun n : nat => @lem91559 n)). Qed.
Lemma lem91561 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem91562 : term32 = term33.
Proof. exact (MK_COMB (@lem91561) (@lem91560)). Qed.
Lemma lem91563 : term10 = term34.
Proof. exact (MK_COMB (@lem91558) (@lem91562)). Qed.
Lemma lem91564 : term34.
Proof. exact (EQ_MP (@lem91563) (@lem91544)). Qed.
Lemma lem91567 (m : nat) : (term8 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem91540 m) (@lem91539 m)). Qed.
Lemma lem91568 : term13 = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (@lem91567 (NUMERAL 0)). Qed.
Lemma lem91570 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem91571 (x : nat) : (x = x) = True.
Proof. exact (@lem91570 nat x). Qed.
Lemma lem91572 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem91571 (NUMERAL 0)). Qed.
Lemma lem91573 : term13 = True.
Proof. exact (TRANS (@lem91568) (@lem91572)). Qed.
Lemma lem91574 : True = term13.
Proof. exact (SYM (@lem91573)). Qed.
Lemma lem91575 : term13.
Proof. exact (EQ_MP (@lem91574) (@lem0)). Qed.
Lemma lem91577 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (EQ_MP (@lem91536 m n) (@lem91535 m n)). Qed.
Lemma lem91578 (n : nat) : (term20 n) = (term35 n).
Proof. exact (@lem91577 (S n) n). Qed.
Lemma lem91582 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem91583 (x : nat) : (x = x) = True.
Proof. exact (@lem91582 nat x). Qed.
Lemma lem91584 (n : nat) : ((S n) = (S n)) = True.
Proof. exact (@lem91583 (S n)). Qed.
Lemma lem91585 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem91586 (n : nat) : (term36 n) = (or True).
Proof. exact (MK_COMB (@lem91585) (@lem91584 n)). Qed.
Lemma lem91587 (n : nat) : (term37 n) = (term37 n).
Proof. exact (eq_refl (term37 n)). Qed.
Lemma lem91588 (n : nat) : (term35 n) = (term38 n).
Proof. exact (MK_COMB (@lem91586 n) (@lem91587 n)). Qed.
Lemma lem91590 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem91591 (n : nat) : (term38 n) = True.
Proof. exact (@lem91590 (term37 n)). Qed.
Lemma lem91592 (n : nat) : (term35 n) = True.
Proof. exact (TRANS (@lem91588 n) (@lem91591 n)). Qed.
Lemma lem91593 (n : nat) : (term20 n) = True.
Proof. exact (TRANS (@lem91578 n) (@lem91592 n)). Qed.
Lemma lem91594 (n : nat) : True = (term20 n).
Proof. exact (SYM (@lem91593 n)). Qed.
Lemma lem91595 (n : nat) : term20 n.
Proof. exact (EQ_MP (@lem91594 n) (@lem0)). Qed.
Lemma lem91596 (n : nat) : term22 n.
Proof. exact (fun h0 : Peano.le n n => @lem91595 n). Qed.
Lemma lem91601 : term26.
Proof. exact (fun n : nat => @lem91596 n). Qed.
Lemma lem91602 : term28.
Proof. exact (conj (@lem91575) (@lem91601)). Qed.
Lemma lem91603 : term33.
Proof. exact (@lem91564 (@lem91602)). Qed.
