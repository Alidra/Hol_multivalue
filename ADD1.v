Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ADD1_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import BIT1_THM_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem80552 : term0.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem80553 : term1.
Proof. exact (proj2 (@lem80552)). Qed.
Lemma lem80554 : term2.
Proof. exact (proj2 (@lem80553)). Qed.
Lemma lem80555 (m : nat) : term3 m.
Proof. exact (@lem80554 m). Qed.
Lemma lem80556 (m : nat) : (term3 m) = (term4 m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem80557 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem80556 m) (@lem80555 m)). Qed.
Lemma lem80558 (m : nat) (n : nat) : term5 m n.
Proof. exact (@lem80557 m n). Qed.
Lemma lem80559 (m : nat) (n : nat) : (term5 m n) = ((term6 m n) = (term7 m n)).
Proof. exact (eq_refl (term5 m n)). Qed.
Lemma lem80568 : term8.
Proof. exact (proj1 (@lem80552)). Qed.
Lemma lem80569 (m : nat) : term9 m.
Proof. exact (@lem80568 m). Qed.
Lemma lem80570 (m : nat) : (term9 m) = ((term10 m) = m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem80572 : term11.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem80573 (n : nat) : term12 n.
Proof. exact (@lem80572 n). Qed.
Lemma lem80574 (n : nat) : (term12 n) = ((term13 n) = n).
Proof. exact (eq_refl (term12 n)). Qed.
Lemma lem80576 (n : nat) : term14 n.
Proof. exact (@lem80210 n). Qed.
Lemma lem80577 (n : nat) : (term14 n) = ((term15 n) = (term16 n)).
Proof. exact (eq_refl (term14 n)). Qed.
Lemma lem80586 (n : nat) : (term15 n) = (term16 n).
Proof. exact (EQ_MP (@lem80577 n) (@lem80576 n)). Qed.
Lemma lem80587 : term17 = term18.
Proof. exact (@lem80586 0). Qed.
Lemma lem80589 (n : nat) : (term13 n) = n.
Proof. exact (EQ_MP (@lem80574 n) (@lem80573 n)). Qed.
Lemma lem80590 : term19 = (NUMERAL 0).
Proof. exact (@lem80589 (NUMERAL 0)). Qed.
Lemma lem80591 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem80592 : term18 = term20.
Proof. exact (MK_COMB (@lem80591) (@lem80590)). Qed.
Lemma lem80593 : term17 = term20.
Proof. exact (TRANS (@lem80587) (@lem80592)). Qed.
Lemma lem80594 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem80595 (m : nat) : (term21 m) = (term22 m).
Proof. exact (MK_COMB (@lem80594 m) (@lem80593)). Qed.
Lemma lem80597 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (EQ_MP (@lem80559 m n) (@lem80558 m n)). Qed.
Lemma lem80598 (m : nat) : (term22 m) = (term23 m).
Proof. exact (@lem80597 m (NUMERAL 0)). Qed.
Lemma lem80600 (m : nat) : (term10 m) = m.
Proof. exact (EQ_MP (@lem80570 m) (@lem80569 m)). Qed.
Lemma lem80601 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem80602 (m : nat) : (term23 m) = (S m).
Proof. exact (MK_COMB (@lem80601) (@lem80600 m)). Qed.
Lemma lem80603 (m : nat) : (term22 m) = (S m).
Proof. exact (TRANS (@lem80598 m) (@lem80602 m)). Qed.
Lemma lem80604 (m : nat) : (term21 m) = (S m).
Proof. exact (TRANS (@lem80595 m) (@lem80603 m)). Qed.
Lemma lem80605 (m : nat) : (term24 m) = (term24 m).
Proof. exact (eq_refl (term24 m)). Qed.
Lemma lem80606 (m : nat) : ((S m) = (term21 m)) = ((S m) = (S m)).
Proof. exact (MK_COMB (@lem80605 m) (@lem80604 m)). Qed.
Lemma lem80608 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem80609 (x : nat) : (x = x) = True.
Proof. exact (@lem80608 nat x). Qed.
Lemma lem80610 (m : nat) : ((S m) = (S m)) = True.
Proof. exact (@lem80609 (S m)). Qed.
Lemma lem80611 (m : nat) : ((S m) = (term21 m)) = True.
Proof. exact (TRANS (@lem80606 m) (@lem80610 m)). Qed.
Lemma lem80612 : term25 = term26.
Proof. exact (fun_ext (fun m : nat => @lem80611 m)). Qed.
Lemma lem80613 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem80614 : term27 = term28.
Proof. exact (MK_COMB (@lem80613) (@lem80612)). Qed.
Lemma lem80616 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem80617 (t : Prop) : (term30 t) = t.
Proof. exact (@lem80616 nat t). Qed.
Lemma lem80618 : term28 = True.
Proof. exact (@lem80617 True). Qed.
Lemma lem80619 : term27 = True.
Proof. exact (TRANS (@lem80614) (@lem80618)). Qed.
Lemma lem80620 : True = term27.
Proof. exact (SYM (@lem80619)). Qed.
Lemma lem80621 : term27.
Proof. exact (EQ_MP (@lem80620) (@lem0)). Qed.
