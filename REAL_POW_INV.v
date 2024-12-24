Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_INV_term_abbrevs.
Require Import REAL_INV_MUL_spec.
Require Import thm0_spec.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Require Import thm1344313_spec.
Require Import thm1344314_spec.
Require Import thm1592014_spec.
Require Import thm1592030_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem1595572 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1595573 (x : real) : term1 x.
Proof. exact (@lem1595572 (term2 x)). Qed.
Lemma lem1595574 (x : real) : (term3 x) = ((term4 x) = (term5 x)).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem1595575 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1595576 (x : real) : (term6 x) = (term7 x).
Proof. exact (MK_COMB (@lem1595575) (@lem1595574 x)). Qed.
Lemma lem1595577 (x : real) (n : nat) : (term8 x n) = ((term9 x n) = (term10 x n)).
Proof. exact (eq_refl (term8 x n)). Qed.
Lemma lem1595578 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1595579 (x : real) (n : nat) : (term11 x n) = (term12 x n).
Proof. exact (MK_COMB (@lem1595578) (@lem1595577 x n)). Qed.
Lemma lem1595580 (x : real) (n : nat) : (term13 x n) = ((term14 x n) = (term15 x n)).
Proof. exact (eq_refl (term13 x n)). Qed.
Lemma lem1595581 (x : real) (n : nat) : (term16 x n) = (term17 x n).
Proof. exact (MK_COMB (@lem1595579 x n) (@lem1595580 x n)). Qed.
Lemma lem1595582 (x : real) : (term18 x) = (term19 x).
Proof. exact (fun_ext (fun n : nat => @lem1595581 x n)). Qed.
Lemma lem1595583 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1595584 (x : real) : (term20 x) = (term21 x).
Proof. exact (MK_COMB (@lem1595583) (@lem1595582 x)). Qed.
Lemma lem1595585 (x : real) : (term22 x) = (term23 x).
Proof. exact (MK_COMB (@lem1595576 x) (@lem1595584 x)). Qed.
Lemma lem1595586 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1595587 (x : real) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem1595586) (@lem1595585 x)). Qed.
Lemma lem1595588 (x : real) (n : nat) : (term8 x n) = ((term9 x n) = (term10 x n)).
Proof. exact (eq_refl (term8 x n)). Qed.
Lemma lem1595589 (x : real) : (term26 x) = (term2 x).
Proof. exact (fun_ext (fun n : nat => @lem1595588 x n)). Qed.
Lemma lem1595590 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1595591 (x : real) : (term27 x) = (term28 x).
Proof. exact (MK_COMB (@lem1595590) (@lem1595589 x)). Qed.
Lemma lem1595592 (x : real) : (term1 x) = (term29 x).
Proof. exact (MK_COMB (@lem1595587 x) (@lem1595591 x)). Qed.
Lemma lem1595593 (x : real) : term29 x.
Proof. exact (EQ_MP (@lem1595592 x) (@lem1595573 x)). Qed.
Lemma lem1595609 (x : real) : (term30 x) = term31.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1595610 (x : real) : (term4 x) = term31.
Proof. exact (@lem1595609 (real_inv x)). Qed.
Lemma lem1595611 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1595612 (x : real) : (term32 x) = term33.
Proof. exact (MK_COMB (@lem1595611) (@lem1595610 x)). Qed.
Lemma lem1595614 (x : real) : (term30 x) = term31.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1595615 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1595616 (x : real) : (term5 x) = term34.
Proof. exact (MK_COMB (@lem1595615) (@lem1595614 x)). Qed.
Lemma lem1595618 : term34 = term31.
Proof. exact (@lem1592014 (@lem1592030)). Qed.
Lemma lem1595619 (x : real) : (term5 x) = term31.
Proof. exact (TRANS (@lem1595616 x) (@lem1595618)). Qed.
Lemma lem1595620 (x : real) : ((term4 x) = (term5 x)) = (term31 = term31).
Proof. exact (MK_COMB (@lem1595612 x) (@lem1595619 x)). Qed.
Lemma lem1595622 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1595623 (x : real) : (x = x) = True.
Proof. exact (@lem1595622 real x). Qed.
Lemma lem1595624 : (term31 = term31) = True.
Proof. exact (@lem1595623 term31). Qed.
Lemma lem1595625 (x : real) : ((term4 x) = (term5 x)) = True.
Proof. exact (TRANS (@lem1595620 x) (@lem1595624)). Qed.
Lemma lem1595626 (x : real) : True = ((term4 x) = (term5 x)).
Proof. exact (SYM (@lem1595625 x)). Qed.
Lemma lem1595627 (x : real) : (term4 x) = (term5 x).
Proof. exact (EQ_MP (@lem1595626 x) (@lem0)). Qed.
Lemma lem1595628 (x : real) : term35 x.
Proof. exact (@lem1595294 x). Qed.
Lemma lem1595629 (x : real) : (term35 x) = (term36 x).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem1595630 (x : real) : term36 x.
Proof. exact (EQ_MP (@lem1595629 x) (@lem1595628 x)). Qed.
Lemma lem1595631 (x : real) (y : real) : term37 x y.
Proof. exact (@lem1595630 x y). Qed.
Lemma lem1595632 (x : real) (y : real) : (term37 x y) = ((term38 x y) = (term39 x y)).
Proof. exact (eq_refl (term37 x y)). Qed.
Lemma lem1595634 (x : real) : term40 x.
Proof. exact (EQ_MP (@lem1344314 x) (@lem1344313 x)). Qed.
Lemma lem1595635 (x : real) (n : nat) : term41 x n.
Proof. exact (@lem1595634 x n). Qed.
Lemma lem1595636 (x : real) (n : nat) : (term41 x n) = ((term42 x n) = (term43 x n)).
Proof. exact (eq_refl (term41 x n)). Qed.
Lemma lem1595642 (x : real) (n : nat) : (term42 x n) = (term43 x n).
Proof. exact (EQ_MP (@lem1595636 x n) (@lem1595635 x n)). Qed.
Lemma lem1595643 (x : real) (n : nat) : (term14 x n) = (term44 x n).
Proof. exact (@lem1595642 (real_inv x) n). Qed.
Lemma lem1595645 (x : real) (n : nat) (h1 : (term9 x n) = (term10 x n)) : (term9 x n) = (term10 x n).
Proof. exact (h1). Qed.
Lemma lem1595646 (x : real) : (term45 x) = (term45 x).
Proof. exact (eq_refl (term45 x)). Qed.
Lemma lem1595647 (x : real) (n : nat) (h1 : (term9 x n) = (term10 x n)) : (term44 x n) = (term46 x n).
Proof. exact (MK_COMB (@lem1595646 x) (@lem1595645 x n h1)). Qed.
Lemma lem1595648 (x : real) (n : nat) (h1 : (term9 x n) = (term10 x n)) : (term14 x n) = (term46 x n).
Proof. exact (TRANS (@lem1595643 x n) (@lem1595647 x n h1)). Qed.
Lemma lem1595649 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1595650 (x : real) (n : nat) (h1 : (term9 x n) = (term10 x n)) : (term47 x n) = (term48 x n).
Proof. exact (MK_COMB (@lem1595649) (@lem1595648 x n h1)). Qed.
Lemma lem1595652 (x : real) (n : nat) : (term42 x n) = (term43 x n).
Proof. exact (EQ_MP (@lem1595636 x n) (@lem1595635 x n)). Qed.
Lemma lem1595653 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1595654 (x : real) (n : nat) : (term15 x n) = (term49 x n).
Proof. exact (MK_COMB (@lem1595653) (@lem1595652 x n)). Qed.
Lemma lem1595656 (x : real) (y : real) : (term38 x y) = (term39 x y).
Proof. exact (EQ_MP (@lem1595632 x y) (@lem1595631 x y)). Qed.
Lemma lem1595657 (x : real) (n : nat) : (term49 x n) = (term46 x n).
Proof. exact (@lem1595656 x (real_pow x n)). Qed.
Lemma lem1595658 (x : real) (n : nat) : (term15 x n) = (term46 x n).
Proof. exact (TRANS (@lem1595654 x n) (@lem1595657 x n)). Qed.
Lemma lem1595659 (x : real) (n : nat) (h1 : (term9 x n) = (term10 x n)) : ((term14 x n) = (term15 x n)) = ((term46 x n) = (term46 x n)).
Proof. exact (MK_COMB (@lem1595650 x n h1) (@lem1595658 x n)). Qed.
Lemma lem1595661 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1595662 (x : real) : (x = x) = True.
Proof. exact (@lem1595661 real x). Qed.
Lemma lem1595663 (x : real) (n : nat) : ((term46 x n) = (term46 x n)) = True.
Proof. exact (@lem1595662 (term46 x n)). Qed.
Lemma lem1595664 (x : real) (n : nat) (h1 : (term9 x n) = (term10 x n)) : ((term14 x n) = (term15 x n)) = True.
Proof. exact (TRANS (@lem1595659 x n h1) (@lem1595663 x n)). Qed.
Lemma lem1595665 (x : real) (n : nat) (h1 : (term9 x n) = (term10 x n)) : True = ((term14 x n) = (term15 x n)).
Proof. exact (SYM (@lem1595664 x n h1)). Qed.
Lemma lem1595666 (x : real) (n : nat) (h1 : (term9 x n) = (term10 x n)) : (term14 x n) = (term15 x n).
Proof. exact (EQ_MP (@lem1595665 x n h1) (@lem0)). Qed.
Lemma lem1595667 (x : real) (n : nat) : term17 x n.
Proof. exact (fun h0 : (term9 x n) = (term10 x n) => @lem1595666 x n h0). Qed.
Lemma lem1595672 (x : real) : term21 x.
Proof. exact (fun n : nat => @lem1595667 x n). Qed.
Lemma lem1595673 (x : real) : term23 x.
Proof. exact (conj (@lem1595627 x) (@lem1595672 x)). Qed.
Lemma lem1595674 (x : real) : term28 x.
Proof. exact (@lem1595593 x (@lem1595673 x)). Qed.
Lemma lem1595679 : term50.
Proof. exact (fun x : real => @lem1595674 x). Qed.
