Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXP_LT_0_term_abbrevs.
Require Import DE_MORGAN_THM_spec.
Require Import EXP_EQ_0_spec.
Require Import NOT_LE_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm89498_spec.
Lemma lem146575 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.lt n m)) : (term0 m n) = (Peano.lt n m).
Proof. exact (h1). Qed.
Lemma lem146576 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.lt n m)) : (Peano.lt n m) = (term0 m n).
Proof. exact (SYM (@lem146575 n m h1)). Qed.
Lemma lem146577 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term0 m n)) : (Peano.lt n m) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem146578 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term0 m n)) : (term0 m n) = (Peano.lt n m).
Proof. exact (SYM (@lem146577 m n h1)). Qed.
Lemma lem146579 (m : nat) (n : nat) : ((term0 m n) = (Peano.lt n m)) = ((Peano.lt n m) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (Peano.lt n m) => @lem146576 n m h1) (fun h1 : (Peano.lt n m) = (term0 m n) => @lem146578 m n h1)). Qed.
Lemma lem146580 (m : nat) : (term1 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem146579 m n)). Qed.
Lemma lem146581 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem146582 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem146581) (@lem146580 m)). Qed.
Lemma lem146583 : term5 = term6.
Proof. exact (fun_ext (fun m : nat => @lem146582 m)). Qed.
Lemma lem146584 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem146585 : term7 = term8.
Proof. exact (MK_COMB (@lem146584) (@lem146583)). Qed.
Lemma lem146586 : term8.
Proof. exact (EQ_MP (@lem146585) (@lem97961)). Qed.
Lemma lem146587 (t1 : Prop) : term9 t1.
Proof. exact (@lem10089 t1). Qed.
Lemma lem146588 (t1 : Prop) : (term9 t1) = (term10 t1).
Proof. exact (eq_refl (term9 t1)). Qed.
Lemma lem146589 (t1 : Prop) : term10 t1.
Proof. exact (EQ_MP (@lem146588 t1) (@lem146587 t1)). Qed.
Lemma lem146590 (t1 : Prop) (t2 : Prop) : term11 t1 t2.
Proof. exact (@lem146589 t1 t2). Qed.
Lemma lem146591 (t1 : Prop) (t2 : Prop) : (term11 t1 t2) = (term12 t1 t2).
Proof. exact (eq_refl (term11 t1 t2)). Qed.
Lemma lem146592 (t1 : Prop) (t2 : Prop) : term12 t1 t2.
Proof. exact (EQ_MP (@lem146591 t1 t2) (@lem146590 t1 t2)). Qed.
Lemma lem146595 (m : nat) : term13 m.
Proof. exact (@lem86997 m). Qed.
Lemma lem146596 (m : nat) : (term13 m) = (term14 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem146597 (m : nat) : term14 m.
Proof. exact (EQ_MP (@lem146596 m) (@lem146595 m)). Qed.
Lemma lem146598 (m : nat) (n : nat) : term15 m n.
Proof. exact (@lem146597 m n). Qed.
Lemma lem146599 (m : nat) (n : nat) : (term15 m n) = (((Nat.pow m n) = (NUMERAL 0)) = (term16 m n)).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem146608 : term17.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem146609 (m : nat) : term18 m.
Proof. exact (@lem146608 m). Qed.
Lemma lem146610 (m : nat) : (term18 m) = ((term19 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem146612 (m : nat) : term20 m.
Proof. exact (@lem146586 m). Qed.
Lemma lem146613 (m : nat) : (term20 m) = (term4 m).
Proof. exact (eq_refl (term20 m)). Qed.
Lemma lem146614 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem146613 m) (@lem146612 m)). Qed.
Lemma lem146615 (m : nat) (n : nat) : term21 m n.
Proof. exact (@lem146614 m n). Qed.
Lemma lem146616 (m : nat) (n : nat) : (term21 m n) = ((Peano.lt n m) = (term0 m n)).
Proof. exact (eq_refl (term21 m n)). Qed.
Lemma lem146629 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem146616 m n) (@lem146615 m n)). Qed.
Lemma lem146630 (x : nat) (n : nat) : (term22 x n) = (term23 x n).
Proof. exact (@lem146629 (Nat.pow x n) (NUMERAL 0)). Qed.
Lemma lem146632 (m : nat) : (term19 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem146610 m) (@lem146609 m)). Qed.
Lemma lem146633 (x : nat) (n : nat) : (term24 x n) = ((Nat.pow x n) = (NUMERAL 0)).
Proof. exact (@lem146632 (Nat.pow x n)). Qed.
Lemma lem146635 (m : nat) (n : nat) : ((Nat.pow m n) = (NUMERAL 0)) = (term16 m n).
Proof. exact (EQ_MP (@lem146599 m n) (@lem146598 m n)). Qed.
Lemma lem146636 (x : nat) (n : nat) : ((Nat.pow x n) = (NUMERAL 0)) = (term16 x n).
Proof. exact (@lem146635 x n). Qed.
Lemma lem146639 (x : nat) (n : nat) : (term24 x n) = (term16 x n).
Proof. exact (TRANS (@lem146633 x n) (@lem146636 x n)). Qed.
Lemma lem146644 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem146645 (x : nat) (n : nat) : (term23 x n) = (term25 x n).
Proof. exact (MK_COMB (@lem146644) (@lem146639 x n)). Qed.
Lemma lem146647 (t1 : Prop) (t2 : Prop) : (term26 t1 t2) = (term27 t1 t2).
Proof. exact (proj1 (@lem146592 t1 t2)). Qed.
Lemma lem146648 (x : nat) (n : nat) : (term25 x n) = (term28 x n).
Proof. exact (@lem146647 (x = (NUMERAL 0)) (term29 n)). Qed.
Lemma lem146654 (t : Prop) : (term30 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem146655 (n : nat) : (term31 n) = (n = (NUMERAL 0)).
Proof. exact (@lem146654 (n = (NUMERAL 0))). Qed.
Lemma lem146658 (x : nat) : (term32 x) = (term32 x).
Proof. exact (eq_refl (term32 x)). Qed.
Lemma lem146659 (x : nat) (n : nat) : (term28 x n) = (term33 x n).
Proof. exact (MK_COMB (@lem146658 x) (@lem146655 n)). Qed.
Lemma lem146662 (x : nat) (n : nat) : (term25 x n) = (term33 x n).
Proof. exact (TRANS (@lem146648 x n) (@lem146659 x n)). Qed.
Lemma lem146663 (x : nat) (n : nat) : (term23 x n) = (term33 x n).
Proof. exact (TRANS (@lem146645 x n) (@lem146662 x n)). Qed.
Lemma lem146664 (x : nat) (n : nat) : (term22 x n) = (term33 x n).
Proof. exact (TRANS (@lem146630 x n) (@lem146663 x n)). Qed.
Lemma lem146665 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem146666 (x : nat) (n : nat) : (term34 x n) = (term35 x n).
Proof. exact (MK_COMB (@lem146665) (@lem146664 x n)). Qed.
Lemma lem146673 (x : nat) (n : nat) : (term33 x n) = (term33 x n).
Proof. exact (eq_refl (term33 x n)). Qed.
Lemma lem146674 (x : nat) (n : nat) : ((term22 x n) = (term33 x n)) = ((term33 x n) = (term33 x n)).
Proof. exact (MK_COMB (@lem146666 x n) (@lem146673 x n)). Qed.
Lemma lem146676 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem146677 (x : Prop) : (x = x) = True.
Proof. exact (@lem146676 Prop x). Qed.
Lemma lem146678 (x : nat) (n : nat) : ((term33 x n) = (term33 x n)) = True.
Proof. exact (@lem146677 (term33 x n)). Qed.
Lemma lem146679 (x : nat) (n : nat) : ((term22 x n) = (term33 x n)) = True.
Proof. exact (TRANS (@lem146674 x n) (@lem146678 x n)). Qed.
Lemma lem146680 (n : nat) : (term36 n) = term37.
Proof. exact (fun_ext (fun x : nat => @lem146679 x n)). Qed.
Lemma lem146681 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem146682 (n : nat) : (term38 n) = term39.
Proof. exact (MK_COMB (@lem146681) (@lem146680 n)). Qed.
Lemma lem146684 {A : Type'} (t : Prop) : (term40 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem146685 (t : Prop) : (term41 t) = t.
Proof. exact (@lem146684 nat t). Qed.
Lemma lem146686 : term39 = True.
Proof. exact (@lem146685 True). Qed.
Lemma lem146687 (n : nat) : (term38 n) = True.
Proof. exact (TRANS (@lem146682 n) (@lem146686)). Qed.
Lemma lem146688 : term42 = term37.
Proof. exact (fun_ext (fun n : nat => @lem146687 n)). Qed.
Lemma lem146689 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem146690 : term43 = term39.
Proof. exact (MK_COMB (@lem146689) (@lem146688)). Qed.
Lemma lem146692 {A : Type'} (t : Prop) : (term40 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem146693 (t : Prop) : (term41 t) = t.
Proof. exact (@lem146692 nat t). Qed.
Lemma lem146694 : term39 = True.
Proof. exact (@lem146693 True). Qed.
Lemma lem146695 : term43 = True.
Proof. exact (TRANS (@lem146690) (@lem146694)). Qed.
Lemma lem146696 : True = term43.
Proof. exact (SYM (@lem146695)). Qed.
Lemma lem146697 : term43.
Proof. exact (EQ_MP (@lem146696) (@lem0)). Qed.
