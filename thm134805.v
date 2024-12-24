Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm134805_term_abbrevs.
Require Import BETA_THM_spec.
Require Import SKOLEM_THM_spec.
Require Import thm75635_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem134556 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem421 A B f). Qed.
Lemma lem134557 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem134558 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem134557 A B f) (@lem134556 A B f)). Qed.
Lemma lem134559 {A B : Type'} (f : A -> B) (y : A) : term2 A B f y.
Proof. exact (@lem134558 A B f y). Qed.
Lemma lem134560 {A B : Type'} (f : A -> B) (y : A) : (term2 A B f y) = ((term3 A B f y) = (f y)).
Proof. exact (eq_refl (term2 A B f y)). Qed.
Lemma lem134563 (minus' : type1606) (_2762 : type1606) (h1 : minus' = (term4 _2762)) : minus' = (term4 _2762).
Proof. exact (h1). Qed.
Lemma lem134564 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem134565 (m : nat) (minus' : type1606) (_2762 : type1606) (h1 : minus' = (term4 _2762)) : (minus' m) = (term5 _2762 m).
Proof. exact (MK_COMB (@lem134563 minus' _2762 h1) (@lem134564 m)). Qed.
Lemma lem134567 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem134560 A B f y) (@lem134559 A B f y)). Qed.
Lemma lem134568 (f : type1606) (y : nat) : (term6 f y) = (f y).
Proof. exact (@lem134567 nat (nat -> nat) f y). Qed.
Lemma lem134569 (_2762 : type1606) (m : nat) : (term7 _2762 m) = (term5 _2762 m).
Proof. exact (@lem134568 (term4 _2762) m). Qed.
Lemma lem134570 (_2762 : type1606) (_2760 : nat) : (term5 _2762 _2760) = (term8 _2762 _2760).
Proof. exact (eq_refl (term5 _2762 _2760)). Qed.
Lemma lem134571 (_2762 : type1606) : (term9 _2762) = (term4 _2762).
Proof. exact (fun_ext (fun _2760 : nat => @lem134570 _2762 _2760)). Qed.
Lemma lem134572 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem134573 (_2762 : type1606) (m : nat) : (term7 _2762 m) = (term5 _2762 m).
Proof. exact (MK_COMB (@lem134571 _2762) (@lem134572 m)). Qed.
Lemma lem134574 : (@eq (nat -> nat)) = (@eq (nat -> nat)).
Proof. exact (eq_refl (@eq (nat -> nat))). Qed.
Lemma lem134575 (_2762 : type1606) (m : nat) : (term10 _2762 m) = (term11 _2762 m).
Proof. exact (MK_COMB (@lem134574) (@lem134573 _2762 m)). Qed.
Lemma lem134576 (_2762 : type1606) (m : nat) : (term5 _2762 m) = (term8 _2762 m).
Proof. exact (eq_refl (term5 _2762 m)). Qed.
Lemma lem134577 (_2762 : type1606) (m : nat) : ((term7 _2762 m) = (term5 _2762 m)) = ((term5 _2762 m) = (term8 _2762 m)).
Proof. exact (MK_COMB (@lem134575 _2762 m) (@lem134576 _2762 m)). Qed.
Lemma lem134578 (_2762 : type1606) (m : nat) : (term5 _2762 m) = (term8 _2762 m).
Proof. exact (EQ_MP (@lem134577 _2762 m) (@lem134569 _2762 m)). Qed.
Lemma lem134579 (m : nat) (minus' : type1606) (_2762 : type1606) (h1 : minus' = (term4 _2762)) : (minus' m) = (term8 _2762 m).
Proof. exact (TRANS (@lem134565 m minus' _2762 h1) (@lem134578 _2762 m)). Qed.
Lemma lem134580 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem134581 (m : nat) (minus' : type1606) (_2762 : type1606) (h1 : minus' = (term4 _2762)) : (term12 minus' m) = (term13 _2762 m).
Proof. exact (MK_COMB (@lem134579 m minus' _2762 h1) (@lem134580)). Qed.
Lemma lem134583 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem134560 A B f y) (@lem134559 A B f y)). Qed.
Lemma lem134584 (f : nat -> nat) (y : nat) : (term14 f y) = (f y).
Proof. exact (@lem134583 nat nat f y). Qed.
Lemma lem134585 (_2762 : type1606) (m : nat) : (term15 _2762 m) = (term13 _2762 m).
Proof. exact (@lem134584 (term8 _2762 m) (NUMERAL 0)). Qed.
Lemma lem134586 (_2762 : type1606) (_2761 : nat) (m : nat) : (term16 _2762 m _2761) = (_2762 _2761 m).
Proof. exact (eq_refl (term16 _2762 m _2761)). Qed.
Lemma lem134587 (_2762 : type1606) (m : nat) : (term17 _2762 m) = (term8 _2762 m).
Proof. exact (fun_ext (fun _2761 : nat => @lem134586 _2762 _2761 m)). Qed.
Lemma lem134588 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem134589 (_2762 : type1606) (m : nat) : (term15 _2762 m) = (term13 _2762 m).
Proof. exact (MK_COMB (@lem134587 _2762 m) (@lem134588)). Qed.
Lemma lem134590 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem134591 (_2762 : type1606) (m : nat) : (term18 _2762 m) = (term19 _2762 m).
Proof. exact (MK_COMB (@lem134590) (@lem134589 _2762 m)). Qed.
Lemma lem134592 (_2762 : type1606) (m : nat) : (term13 _2762 m) = (term20 _2762 m).
Proof. exact (eq_refl (term13 _2762 m)). Qed.
Lemma lem134593 (_2762 : type1606) (m : nat) : ((term15 _2762 m) = (term13 _2762 m)) = ((term13 _2762 m) = (term20 _2762 m)).
Proof. exact (MK_COMB (@lem134591 _2762 m) (@lem134592 _2762 m)). Qed.
Lemma lem134594 (_2762 : type1606) (m : nat) : (term13 _2762 m) = (term20 _2762 m).
Proof. exact (EQ_MP (@lem134593 _2762 m) (@lem134585 _2762 m)). Qed.
Lemma lem134595 (m : nat) (minus' : type1606) (_2762 : type1606) (h1 : minus' = (term4 _2762)) : (term12 minus' m) = (term20 _2762 m).
Proof. exact (TRANS (@lem134581 m minus' _2762 h1) (@lem134594 _2762 m)). Qed.
Lemma lem134596 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem134597 (m : nat) (minus' : type1606) (_2762 : type1606) (h1 : minus' = (term4 _2762)) : (term21 minus' m) = (term22 _2762 m).
Proof. exact (MK_COMB (@lem134596) (@lem134595 m minus' _2762 h1)). Qed.
Lemma lem134598 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem134599 (m : nat) (minus' : type1606) (_2762 : type1606) (h1 : minus' = (term4 _2762)) : ((term12 minus' m) = m) = ((term20 _2762 m) = m).
Proof. exact (MK_COMB (@lem134597 m minus' _2762 h1) (@lem134598 m)). Qed.
Lemma lem134600 (minus' : type1606) (_2762 : type1606) (h1 : minus' = (term4 _2762)) : (term23 minus') = (term24 _2762).
Proof. exact (fun_ext (fun m : nat => @lem134599 m minus' _2762 h1)). Qed.
Lemma lem134601 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem134602 (minus' : type1606) (_2762 : type1606) (h1 : minus' = (term4 _2762)) : (term25 minus') = (term26 _2762).
Proof. exact (MK_COMB (@lem134601) (@lem134600 minus' _2762 h1)). Qed.
Lemma lem134603 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem134604 (minus' : type1606) (_2762 : type1606) (h1 : minus' = (term4 _2762)) : (term27 minus') = (term28 _2762).
Proof. exact (MK_COMB (@lem134603) (@lem134602 minus' _2762 h1)). Qed.
Lemma lem134606 (minus' : type1606) (_2762 : type1606) (h1 : minus' = (term4 _2762)) : minus' = (term4 _2762).
Proof. exact (h1). Qed.
Lemma lem134607 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem134608 (m : nat) (minus' : type1606) (_2762 : type1606) (h1 : minus' = (term4 _2762)) : (minus' m) = (term5 _2762 m).
Proof. exact (MK_COMB (@lem134606 minus' _2762 h1) (@lem134607 m)). Qed.
Lemma lem134610 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem134560 A B f y) (@lem134559 A B f y)). Qed.
Lemma lem134611 (f : type1606) (y : nat) : (term6 f y) = (f y).
Proof. exact (@lem134610 nat (nat -> nat) f y). Qed.
Lemma lem134612 (_2762 : type1606) (m : nat) : (term7 _2762 m) = (term5 _2762 m).
Proof. exact (@lem134611 (term4 _2762) m). Qed.
Lemma lem134613 (_2762 : type1606) (_2760 : nat) : (term5 _2762 _2760) = (term8 _2762 _2760).
Proof. exact (eq_refl (term5 _2762 _2760)). Qed.
Lemma lem134614 (_2762 : type1606) : (term9 _2762) = (term4 _2762).
Proof. exact (fun_ext (fun _2760 : nat => @lem134613 _2762 _2760)). Qed.
Lemma lem134615 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem134616 (_2762 : type1606) (m : nat) : (term7 _2762 m) = (term5 _2762 m).
Proof. exact (MK_COMB (@lem134614 _2762) (@lem134615 m)). Qed.
Lemma lem134617 : (@eq (nat -> nat)) = (@eq (nat -> nat)).
Proof. exact (eq_refl (@eq (nat -> nat))). Qed.
Lemma lem134618 (_2762 : type1606) (m : nat) : (term10 _2762 m) = (term11 _2762 m).
Proof. exact (MK_COMB (@lem134617) (@lem134616 _2762 m)). Qed.
Lemma lem134619 (_2762 : type1606) (m : nat) : (term5 _2762 m) = (term8 _2762 m).
Proof. exact (eq_refl (term5 _2762 m)). Qed.
Lemma lem134620 (_2762 : type1606) (m : nat) : ((term7 _2762 m) = (term5 _2762 m)) = ((term5 _2762 m) = (term8 _2762 m)).
Proof. exact (MK_COMB (@lem134618 _2762 m) (@lem134619 _2762 m)). Qed.
Lemma lem134621 (_2762 : type1606) (m : nat) : (term5 _2762 m) = (term8 _2762 m).
Proof. exact (EQ_MP (@lem134620 _2762 m) (@lem134612 _2762 m)). Qed.
Lemma lem134622 (m : nat) (minus' : type1606) (_2762 : type1606) (h1 : minus' = (term4 _2762)) : (minus' m) = (term8 _2762 m).
Proof. exact (TRANS (@lem134608 m minus' _2762 h1) (@lem134621 _2762 m)). Qed.
Lemma lem134623 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem134624 (m : nat) (n : nat) (minus' : type1606) (_2762 : type1606) (h1 : minus' = (term4 _2762)) : (term29 minus' m n) = (term30 _2762 m n).
Proof. exact (MK_COMB (@lem134622 m minus' _2762 h1) (@lem134623 n)). Qed.
Lemma lem134626 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem134560 A B f y) (@lem134559 A B f y)). Qed.
Lemma lem134627 (f : nat -> nat) (y : nat) : (term14 f y) = (f y).
Proof. exact (@lem134626 nat nat f y). Qed.
Lemma lem134628 (_2762 : type1606) (m : nat) (n : nat) : (term31 _2762 m n) = (term30 _2762 m n).
Proof. exact (@lem134627 (term8 _2762 m) (S n)). Qed.
Lemma lem134629 (_2762 : type1606) (_2761 : nat) (m : nat) : (term16 _2762 m _2761) = (_2762 _2761 m).
Proof. exact (eq_refl (term16 _2762 m _2761)). Qed.
Lemma lem134630 (_2762 : type1606) (m : nat) : (term17 _2762 m) = (term8 _2762 m).
Proof. exact (fun_ext (fun _2761 : nat => @lem134629 _2762 _2761 m)). Qed.
Lemma lem134631 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem134632 (_2762 : type1606) (m : nat) (n : nat) : (term31 _2762 m n) = (term30 _2762 m n).
Proof. exact (MK_COMB (@lem134630 _2762 m) (@lem134631 n)). Qed.
Lemma lem134633 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem134634 (_2762 : type1606) (m : nat) (n : nat) : (term32 _2762 m n) = (term33 _2762 m n).
Proof. exact (MK_COMB (@lem134633) (@lem134632 _2762 m n)). Qed.
Lemma lem134635 (_2762 : type1606) (n : nat) (m : nat) : (term30 _2762 m n) = (term34 _2762 n m).
Proof. exact (eq_refl (term30 _2762 m n)). Qed.
Lemma lem134636 (_2762 : type1606) (n : nat) (m : nat) : ((term31 _2762 m n) = (term30 _2762 m n)) = ((term30 _2762 m n) = (term34 _2762 n m)).
Proof. exact (MK_COMB (@lem134634 _2762 m n) (@lem134635 _2762 n m)). Qed.
Lemma lem134637 (_2762 : type1606) (n : nat) (m : nat) : (term30 _2762 m n) = (term34 _2762 n m).
Proof. exact (EQ_MP (@lem134636 _2762 n m) (@lem134628 _2762 m n)). Qed.
Lemma lem134638 (n : nat) (m : nat) (minus' : type1606) (_2762 : type1606) (h1 : minus' = (term4 _2762)) : (term29 minus' m n) = (term34 _2762 n m).
Proof. exact (TRANS (@lem134624 m n minus' _2762 h1) (@lem134637 _2762 n m)). Qed.
Lemma lem134639 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem134640 (n : nat) (m : nat) (minus' : type1606) (_2762 : type1606) (h1 : minus' = (term4 _2762)) : (term35 minus' m n) = (term36 _2762 n m).
Proof. exact (MK_COMB (@lem134639) (@lem134638 n m minus' _2762 h1)). Qed.
Lemma lem134642 (minus' : type1606) (_2762 : type1606) (h1 : minus' = (term4 _2762)) : minus' = (term4 _2762).
Proof. exact (h1). Qed.
Lemma lem134643 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem134644 (m : nat) (minus' : type1606) (_2762 : type1606) (h1 : minus' = (term4 _2762)) : (minus' m) = (term5 _2762 m).
Proof. exact (MK_COMB (@lem134642 minus' _2762 h1) (@lem134643 m)). Qed.
Lemma lem134646 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem134560 A B f y) (@lem134559 A B f y)). Qed.
Lemma lem134647 (f : type1606) (y : nat) : (term6 f y) = (f y).
Proof. exact (@lem134646 nat (nat -> nat) f y). Qed.
Lemma lem134648 (_2762 : type1606) (m : nat) : (term7 _2762 m) = (term5 _2762 m).
Proof. exact (@lem134647 (term4 _2762) m). Qed.
Lemma lem134649 (_2762 : type1606) (_2760 : nat) : (term5 _2762 _2760) = (term8 _2762 _2760).
Proof. exact (eq_refl (term5 _2762 _2760)). Qed.
Lemma lem134650 (_2762 : type1606) : (term9 _2762) = (term4 _2762).
Proof. exact (fun_ext (fun _2760 : nat => @lem134649 _2762 _2760)). Qed.
Lemma lem134651 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem134652 (_2762 : type1606) (m : nat) : (term7 _2762 m) = (term5 _2762 m).
Proof. exact (MK_COMB (@lem134650 _2762) (@lem134651 m)). Qed.
Lemma lem134653 : (@eq (nat -> nat)) = (@eq (nat -> nat)).
Proof. exact (eq_refl (@eq (nat -> nat))). Qed.
Lemma lem134654 (_2762 : type1606) (m : nat) : (term10 _2762 m) = (term11 _2762 m).
Proof. exact (MK_COMB (@lem134653) (@lem134652 _2762 m)). Qed.
Lemma lem134655 (_2762 : type1606) (m : nat) : (term5 _2762 m) = (term8 _2762 m).
Proof. exact (eq_refl (term5 _2762 m)). Qed.
Lemma lem134656 (_2762 : type1606) (m : nat) : ((term7 _2762 m) = (term5 _2762 m)) = ((term5 _2762 m) = (term8 _2762 m)).
Proof. exact (MK_COMB (@lem134654 _2762 m) (@lem134655 _2762 m)). Qed.
Lemma lem134657 (_2762 : type1606) (m : nat) : (term5 _2762 m) = (term8 _2762 m).
Proof. exact (EQ_MP (@lem134656 _2762 m) (@lem134648 _2762 m)). Qed.
Lemma lem134658 (m : nat) (minus' : type1606) (_2762 : type1606) (h1 : minus' = (term4 _2762)) : (minus' m) = (term8 _2762 m).
Proof. exact (TRANS (@lem134644 m minus' _2762 h1) (@lem134657 _2762 m)). Qed.
Lemma lem134659 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem134660 (m : nat) (n : nat) (minus' : type1606) (_2762 : type1606) (h1 : minus' = (term4 _2762)) : (minus' m n) = (term16 _2762 m n).
Proof. exact (MK_COMB (@lem134658 m minus' _2762 h1) (@lem134659 n)). Qed.
Lemma lem134662 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem134560 A B f y) (@lem134559 A B f y)). Qed.
Lemma lem134663 (f : nat -> nat) (y : nat) : (term14 f y) = (f y).
Proof. exact (@lem134662 nat nat f y). Qed.
Lemma lem134664 (_2762 : type1606) (m : nat) (n : nat) : (term37 _2762 m n) = (term16 _2762 m n).
Proof. exact (@lem134663 (term8 _2762 m) n). Qed.
Lemma lem134665 (_2762 : type1606) (_2761 : nat) (m : nat) : (term16 _2762 m _2761) = (_2762 _2761 m).
Proof. exact (eq_refl (term16 _2762 m _2761)). Qed.
Lemma lem134666 (_2762 : type1606) (m : nat) : (term17 _2762 m) = (term8 _2762 m).
Proof. exact (fun_ext (fun _2761 : nat => @lem134665 _2762 _2761 m)). Qed.
Lemma lem134667 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem134668 (_2762 : type1606) (m : nat) (n : nat) : (term37 _2762 m n) = (term16 _2762 m n).
Proof. exact (MK_COMB (@lem134666 _2762 m) (@lem134667 n)). Qed.
Lemma lem134669 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem134670 (_2762 : type1606) (m : nat) (n : nat) : (term38 _2762 m n) = (term39 _2762 m n).
Proof. exact (MK_COMB (@lem134669) (@lem134668 _2762 m n)). Qed.
Lemma lem134671 (_2762 : type1606) (n : nat) (m : nat) : (term16 _2762 m n) = (_2762 n m).
Proof. exact (eq_refl (term16 _2762 m n)). Qed.
Lemma lem134672 (_2762 : type1606) (n : nat) (m : nat) : ((term37 _2762 m n) = (term16 _2762 m n)) = ((term16 _2762 m n) = (_2762 n m)).
Proof. exact (MK_COMB (@lem134670 _2762 m n) (@lem134671 _2762 n m)). Qed.
Lemma lem134673 (_2762 : type1606) (n : nat) (m : nat) : (term16 _2762 m n) = (_2762 n m).
Proof. exact (EQ_MP (@lem134672 _2762 n m) (@lem134664 _2762 m n)). Qed.
Lemma lem134674 (n : nat) (m : nat) (minus' : type1606) (_2762 : type1606) (h1 : minus' = (term4 _2762)) : (minus' m n) = (_2762 n m).
Proof. exact (TRANS (@lem134660 m n minus' _2762 h1) (@lem134673 _2762 n m)). Qed.
Lemma lem134675 : Nat.pred = Nat.pred.
Proof. exact (eq_refl Nat.pred). Qed.
Lemma lem134676 (n : nat) (m : nat) (minus' : type1606) (_2762 : type1606) (h1 : minus' = (term4 _2762)) : (term40 minus' m n) = (term40 _2762 n m).
Proof. exact (MK_COMB (@lem134675) (@lem134674 n m minus' _2762 h1)). Qed.
Lemma lem134677 (n : nat) (m : nat) (minus' : type1606) (_2762 : type1606) (h1 : minus' = (term4 _2762)) : ((term29 minus' m n) = (term40 minus' m n)) = ((term34 _2762 n m) = (term40 _2762 n m)).
Proof. exact (MK_COMB (@lem134640 n m minus' _2762 h1) (@lem134676 n m minus' _2762 h1)). Qed.
Lemma lem134678 (m : nat) (minus' : type1606) (_2762 : type1606) (h1 : minus' = (term4 _2762)) : (term41 minus' m) = (term42 _2762 m).
Proof. exact (fun_ext (fun n : nat => @lem134677 n m minus' _2762 h1)). Qed.
Lemma lem134679 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem134680 (m : nat) (minus' : type1606) (_2762 : type1606) (h1 : minus' = (term4 _2762)) : (term43 minus' m) = (term44 _2762 m).
Proof. exact (MK_COMB (@lem134679) (@lem134678 m minus' _2762 h1)). Qed.
Lemma lem134681 (minus' : type1606) (_2762 : type1606) (h1 : minus' = (term4 _2762)) : (term45 minus') = (term46 _2762).
Proof. exact (fun_ext (fun m : nat => @lem134680 m minus' _2762 h1)). Qed.
Lemma lem134682 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem134683 (minus' : type1606) (_2762 : type1606) (h1 : minus' = (term4 _2762)) : (term47 minus') = (term48 _2762).
Proof. exact (MK_COMB (@lem134682) (@lem134681 minus' _2762 h1)). Qed.
Lemma lem134684 (minus' : type1606) (_2762 : type1606) (h1 : minus' = (term4 _2762)) : (term49 minus') = (term50 _2762).
Proof. exact (MK_COMB (@lem134604 minus' _2762 h1) (@lem134683 minus' _2762 h1)). Qed.
Lemma lem134685 (_2762 : type1606) (h1 : (term51 _2762) = term52) : (term51 _2762) = term52.
Proof. exact (h1). Qed.
Lemma lem134686 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem134687 (m : nat) (_2762 : type1606) (h1 : (term51 _2762) = term52) : (term20 _2762 m) = (term53 m).
Proof. exact (MK_COMB (@lem134685 _2762 h1) (@lem134686 m)). Qed.
Lemma lem134688 (m : nat) : (term53 m) = m.
Proof. exact (eq_refl (term53 m)). Qed.
Lemma lem134689 (_2762 : type1606) (m : nat) : (term22 _2762 m) = (term22 _2762 m).
Proof. exact (eq_refl (term22 _2762 m)). Qed.
Lemma lem134690 (_2762 : type1606) (m : nat) : ((term20 _2762 m) = (term53 m)) = ((term20 _2762 m) = m).
Proof. exact (MK_COMB (@lem134689 _2762 m) (@lem134688 m)). Qed.
Lemma lem134691 (m : nat) (_2762 : type1606) (h1 : (term51 _2762) = term52) : (term20 _2762 m) = m.
Proof. exact (EQ_MP (@lem134690 _2762 m) (@lem134687 m _2762 h1)). Qed.
Lemma lem134692 (_2762 : type1606) (h1 : (term51 _2762) = term52) : term26 _2762.
Proof. exact (fun m : nat => @lem134691 m _2762 h1). Qed.
Lemma lem134693 (_2762 : type1606) (h1 : term54 _2762) : term54 _2762.
Proof. exact (h1). Qed.
Lemma lem134694 (n : nat) (_2762 : type1606) (h1 : term54 _2762) : term55 _2762 n.
Proof. exact (@lem134693 _2762 h1 n). Qed.
Lemma lem134695 (_2762 : type1606) (n : nat) : (term55 _2762 n) = ((term56 _2762 n) = (term57 _2762 n)).
Proof. exact (eq_refl (term55 _2762 n)). Qed.
Lemma lem134696 (n : nat) (_2762 : type1606) (h1 : term54 _2762) : (term56 _2762 n) = (term57 _2762 n).
Proof. exact (EQ_MP (@lem134695 _2762 n) (@lem134694 n _2762 h1)). Qed.
Lemma lem134697 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem134698 (n : nat) (m : nat) (_2762 : type1606) (h1 : term54 _2762) : (term34 _2762 n m) = (term58 _2762 n m).
Proof. exact (MK_COMB (@lem134696 n _2762 h1) (@lem134697 m)). Qed.
Lemma lem134699 (_2762 : type1606) (n : nat) (m : nat) : (term58 _2762 n m) = (term40 _2762 n m).
Proof. exact (eq_refl (term58 _2762 n m)). Qed.
Lemma lem134700 (_2762 : type1606) (n : nat) (m : nat) : (term36 _2762 n m) = (term36 _2762 n m).
Proof. exact (eq_refl (term36 _2762 n m)). Qed.
Lemma lem134701 (_2762 : type1606) (n : nat) (m : nat) : ((term34 _2762 n m) = (term58 _2762 n m)) = ((term34 _2762 n m) = (term40 _2762 n m)).
Proof. exact (MK_COMB (@lem134700 _2762 n m) (@lem134699 _2762 n m)). Qed.
Lemma lem134702 (n : nat) (m : nat) (_2762 : type1606) (h1 : term54 _2762) : (term34 _2762 n m) = (term40 _2762 n m).
Proof. exact (EQ_MP (@lem134701 _2762 n m) (@lem134698 n m _2762 h1)). Qed.
Lemma lem134703 (m : nat) (_2762 : type1606) (h1 : term54 _2762) : term44 _2762 m.
Proof. exact (fun n : nat => @lem134702 n m _2762 h1). Qed.
Lemma lem134704 (_2762 : type1606) (h1 : term54 _2762) : term48 _2762.
Proof. exact (fun m : nat => @lem134703 m _2762 h1). Qed.
Lemma lem134705 (_2762 : type1606) (h1 : term59 _2762) : term59 _2762.
Proof. exact (h1). Qed.
Lemma lem134706 (_2762 : type1606) (h1 : term59 _2762) : term54 _2762.
Proof. exact (proj2 (@lem134705 _2762 h1)). Qed.
Lemma lem134707 (_2762 : type1606) (h1 : term59 _2762) : (term51 _2762) = term52.
Proof. exact (proj1 (@lem134705 _2762 h1)). Qed.
Lemma lem134708 (_2762 : type1606) (h1 : term59 _2762) : ((term51 _2762) = term52) = (term26 _2762).
Proof. exact (prop_ext (fun h2 : (term51 _2762) = term52 => @lem134692 _2762 h2) (fun h2 : term26 _2762 => @lem134707 _2762 h1)). Qed.
Lemma lem134709 (_2762 : type1606) (h1 : term59 _2762) : term26 _2762.
Proof. exact (EQ_MP (@lem134708 _2762 h1) (@lem134707 _2762 h1)). Qed.
Lemma lem134710 (_2762 : type1606) (h1 : term59 _2762) : (term54 _2762) = (term48 _2762).
Proof. exact (prop_ext (fun h2 : term54 _2762 => @lem134704 _2762 h2) (fun h2 : term48 _2762 => @lem134706 _2762 h1)). Qed.
Lemma lem134711 (_2762 : type1606) (h1 : term59 _2762) : term48 _2762.
Proof. exact (EQ_MP (@lem134710 _2762 h1) (@lem134706 _2762 h1)). Qed.
Lemma lem134712 (_2762 : type1606) (h1 : term59 _2762) : term50 _2762.
Proof. exact (conj (@lem134709 _2762 h1) (@lem134711 _2762 h1)). Qed.
Lemma lem134713 {A : Type'} (e : A) : term60 A e.
Proof. exact (@lem75635 A e). Qed.
Lemma lem134714 {A : Type'} (e : A) : (term60 A e) = (term61 A e).
Proof. exact (eq_refl (term60 A e)). Qed.
Lemma lem134715 {A : Type'} (e : A) : term61 A e.
Proof. exact (EQ_MP (@lem134714 A e) (@lem134713 A e)). Qed.
Lemma lem134716 {A : Type'} (e : A) (f : type1423 A) : term62 A e f.
Proof. exact (@lem134715 A e f). Qed.
Lemma lem134717 {A : Type'} (e : A) (f : type1423 A) : (term62 A e f) = (term63 A e f).
Proof. exact (eq_refl (term62 A e f)). Qed.
Lemma lem134718 {A : Type'} (e : A) (f : type1423 A) : term63 A e f.
Proof. exact (EQ_MP (@lem134717 A e f) (@lem134716 A e f)). Qed.
Lemma lem134719 (e : nat -> nat) (f : type1000) : term64 e f.
Proof. exact (@lem134718 (nat -> nat) e f). Qed.
Lemma lem134720 : term65.
Proof. exact (@lem134719 term52 term66). Qed.
Lemma lem134721 (fn : type1606) (n : nat) : (term67 fn n) = (term68 fn n).
Proof. exact (eq_refl (term67 fn n)). Qed.
Lemma lem134722 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem134723 (fn : type1606) (n : nat) : (term69 fn n) = (term70 fn n).
Proof. exact (MK_COMB (@lem134721 fn n) (@lem134722 n)). Qed.
Lemma lem134724 (fn : type1606) (n : nat) : (term70 fn n) = (term57 fn n).
Proof. exact (eq_refl (term70 fn n)). Qed.
Lemma lem134725 (fn : type1606) (n : nat) : (term69 fn n) = (term57 fn n).
Proof. exact (TRANS (@lem134723 fn n) (@lem134724 fn n)). Qed.
Lemma lem134726 (fn : type1606) (n : nat) : (term71 fn n) = (term71 fn n).
Proof. exact (eq_refl (term71 fn n)). Qed.
Lemma lem134727 (fn : type1606) (n : nat) : ((term56 fn n) = (term69 fn n)) = ((term56 fn n) = (term57 fn n)).
Proof. exact (MK_COMB (@lem134726 fn n) (@lem134725 fn n)). Qed.
Lemma lem134728 (fn : type1606) : (term72 fn) = (term73 fn).
Proof. exact (fun_ext (fun n : nat => @lem134727 fn n)). Qed.
Lemma lem134729 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem134730 (fn : type1606) : (term74 fn) = (term54 fn).
Proof. exact (MK_COMB (@lem134729) (@lem134728 fn)). Qed.
Lemma lem134731 (fn : type1606) : (term75 fn) = (term75 fn).
Proof. exact (eq_refl (term75 fn)). Qed.
Lemma lem134732 (fn : type1606) : (term76 fn) = (term59 fn).
Proof. exact (MK_COMB (@lem134731 fn) (@lem134730 fn)). Qed.
Lemma lem134733 : term77 = term78.
Proof. exact (fun_ext (fun fn : type1606 => @lem134732 fn)). Qed.
Lemma lem134734 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem134735 : term65 = term79.
Proof. exact (MK_COMB (@lem134734) (@lem134733)). Qed.
Lemma lem134736 : term79.
Proof. exact (EQ_MP (@lem134735) (@lem134720)). Qed.
Lemma lem134737 (_2762 : type1606) (h1 : term59 _2762) : term59 _2762.
Proof. exact (h1). Qed.
Lemma lem134738 (_2762 : type1606) (h1 : term59 _2762) : term54 _2762.
Proof. exact (proj2 (@lem134737 _2762 h1)). Qed.
Lemma lem134739 (_2762 : type1606) (h1 : term59 _2762) : (term51 _2762) = term52.
Proof. exact (proj1 (@lem134737 _2762 h1)). Qed.
Lemma lem134740 (_2762 : type1606) (h1 : term59 _2762) : term59 _2762.
Proof. exact (conj (@lem134739 _2762 h1) (@lem134738 _2762 h1)). Qed.
Lemma lem134741 (_2762 : type1606) (h1 : term59 _2762) : term79.
Proof. exact (ex_intro term78 _2762 (@lem134740 _2762 h1)). Qed.
Lemma lem134742 (h1 : term79) : term79.
Proof. exact (h1). Qed.
Lemma lem134743 (h1 : term79) : term79.
Proof. exact (ex_elim (@lem134742 h1) (fun _2762 : type1606 => fun h0 : term78 _2762 => @lem134741 _2762 h0)). Qed.
Lemma lem134744 : term79 = term79.
Proof. exact (prop_ext (fun h1 : term79 => @lem134743 h1) (fun h1 : term79 => @lem134736)). Qed.
Lemma lem134745 : term79.
Proof. exact (EQ_MP (@lem134744) (@lem134736)). Qed.
Lemma lem134746 (_2762 : type1606) (h1 : term59 _2762) : term80.
Proof. exact (ex_intro term81 _2762 (@lem134712 _2762 h1)). Qed.
Lemma lem134747 (h1 : term79) : term79.
Proof. exact (h1). Qed.
Lemma lem134748 (h1 : term79) : term80.
Proof. exact (ex_elim (@lem134747 h1) (fun _2762 : type1606 => fun h0 : term78 _2762 => @lem134746 _2762 h0)). Qed.
Lemma lem134749 : term79 = term80.
Proof. exact (prop_ext (fun h1 : term79 => @lem134748 h1) (fun h1 : term80 => @lem134745)). Qed.
Lemma lem134750 : term80.
Proof. exact (EQ_MP (@lem134749) (@lem134745)). Qed.
Lemma lem134751 (_2762 : type1606) (h1 : term50 _2762) : term50 _2762.
Proof. exact (h1). Qed.
Lemma lem134752 (minus' : type1606) (_2762 : type1606) (h1 : minus' = (term4 _2762)) : (term50 _2762) = (term49 minus').
Proof. exact (SYM (@lem134684 minus' _2762 h1)). Qed.
Lemma lem134753 (minus' : type1606) (_2762 : type1606) (h1 : term50 _2762) (h2 : minus' = (term4 _2762)) : term49 minus'.
Proof. exact (EQ_MP (@lem134752 minus' _2762 h2) (@lem134751 _2762 h1)). Qed.
Lemma lem134754 (minus' : type1606) (_2762 : type1606) (h1 : term50 _2762) (h2 : minus' = (term4 _2762)) : term82.
Proof. exact (ex_intro term83 minus' (@lem134753 minus' _2762 h1 h2)). Qed.
Lemma lem134755 (_2762 : type1606) : (term4 _2762) = (term4 _2762).
Proof. exact (eq_refl (term4 _2762)). Qed.
Lemma lem134756 (minus' : type1606) (_2762 : type1606) (h1 : term50 _2762) : term84 minus' _2762.
Proof. exact (fun h0 : minus' = (term4 _2762) => @lem134754 minus' _2762 h1 h0). Qed.
Lemma lem134757 (_2762 : type1606) (h1 : term50 _2762) : term85 _2762.
Proof. exact (@lem134756 (term4 _2762) _2762 h1). Qed.
Lemma lem134758 (_2762 : type1606) (h1 : term50 _2762) : term82.
Proof. exact (@lem134757 _2762 h1 (@lem134755 _2762)). Qed.
Lemma lem134759 (h1 : term80) : term80.
Proof. exact (h1). Qed.
Lemma lem134760 (h1 : term80) : term82.
Proof. exact (ex_elim (@lem134759 h1) (fun _2762 : type1606 => fun h0 : term81 _2762 => @lem134758 _2762 h0)). Qed.
Lemma lem134761 : term80 = term82.
Proof. exact (prop_ext (fun h1 : term80 => @lem134760 h1) (fun h1 : term82 => @lem134750)). Qed.
Lemma lem134762 : term82.
Proof. exact (EQ_MP (@lem134761) (@lem134750)). Qed.
Lemma lem134763 : term86.
Proof. exact (fun _2766 : nat => @lem134762). Qed.
Lemma lem134764 {A B : Type'} (P : type1413 A B) : term87 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem134765 {A B : Type'} (P : type1413 A B) : (term87 A B P) = ((term88 A B P) = (term89 A B P)).
Proof. exact (eq_refl (term87 A B P)). Qed.
Lemma lem134768 {A B : Type'} (P : type1413 A B) : (term88 A B P) = (term89 A B P).
Proof. exact (EQ_MP (@lem134765 A B P) (@lem134764 A B P)). Qed.
Lemma lem134769 (P : type1581) : (term90 P) = (term91 P).
Proof. exact (@lem134768 nat type1606 P). Qed.
Lemma lem134770 : term92 = term93.
Proof. exact (@lem134769 term94). Qed.
Lemma lem134771 (_2766 : nat) : (term95 _2766) = term83.
Proof. exact (eq_refl (term95 _2766)). Qed.
Lemma lem134772 (minus' : type1606) : minus' = minus'.
Proof. exact (eq_refl minus'). Qed.
Lemma lem134773 (_2766 : nat) (minus' : type1606) : (term96 _2766 minus') = (term97 minus').
Proof. exact (MK_COMB (@lem134771 _2766) (@lem134772 minus')). Qed.
Lemma lem134774 (minus' : type1606) : (term97 minus') = (term49 minus').
Proof. exact (eq_refl (term97 minus')). Qed.
Lemma lem134775 (_2766 : nat) (minus' : type1606) : (term96 _2766 minus') = (term49 minus').
Proof. exact (TRANS (@lem134773 _2766 minus') (@lem134774 minus')). Qed.
Lemma lem134776 (_2766 : nat) : (term98 _2766) = term83.
Proof. exact (fun_ext (fun minus' : type1606 => @lem134775 _2766 minus')). Qed.
Lemma lem134777 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem134778 (_2766 : nat) : (term99 _2766) = term82.
Proof. exact (MK_COMB (@lem134777) (@lem134776 _2766)). Qed.
Lemma lem134779 : term100 = term101.
Proof. exact (fun_ext (fun _2766 : nat => @lem134778 _2766)). Qed.
Lemma lem134780 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem134781 : term92 = term86.
Proof. exact (MK_COMB (@lem134780) (@lem134779)). Qed.
Lemma lem134782 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem134783 : term102 = term103.
Proof. exact (MK_COMB (@lem134782) (@lem134781)). Qed.
Lemma lem134784 (_2766 : nat) : (term95 _2766) = term83.
Proof. exact (eq_refl (term95 _2766)). Qed.
Lemma lem134785 (minus' : type1602) (_2766 : nat) : (minus' _2766) = (minus' _2766).
Proof. exact (eq_refl (minus' _2766)). Qed.
Lemma lem134786 (minus' : type1602) (_2766 : nat) : (term104 minus' _2766) = (term105 minus' _2766).
Proof. exact (MK_COMB (@lem134784 _2766) (@lem134785 minus' _2766)). Qed.
Lemma lem134787 (minus' : type1602) (_2766 : nat) : (term105 minus' _2766) = (term106 minus' _2766).
Proof. exact (eq_refl (term105 minus' _2766)). Qed.
Lemma lem134788 (minus' : type1602) (_2766 : nat) : (term104 minus' _2766) = (term106 minus' _2766).
Proof. exact (TRANS (@lem134786 minus' _2766) (@lem134787 minus' _2766)). Qed.
Lemma lem134789 (minus' : type1602) : (term107 minus') = (term108 minus').
Proof. exact (fun_ext (fun _2766 : nat => @lem134788 minus' _2766)). Qed.
Lemma lem134790 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem134791 (minus' : type1602) : (term109 minus') = (term110 minus').
Proof. exact (MK_COMB (@lem134790) (@lem134789 minus')). Qed.
Lemma lem134792 : term111 = term112.
Proof. exact (fun_ext (fun minus' : type1602 => @lem134791 minus')). Qed.
Lemma lem134793 : (@ex (nat -> nat -> nat -> nat)) = (@ex (nat -> nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat -> nat))). Qed.
Lemma lem134794 : term93 = term113.
Proof. exact (MK_COMB (@lem134793) (@lem134792)). Qed.
Lemma lem134795 : (term92 = term93) = (term86 = term113).
Proof. exact (MK_COMB (@lem134783) (@lem134794)). Qed.
Lemma lem134796 : term86 = term113.
Proof. exact (EQ_MP (@lem134795) (@lem134770)). Qed.
Lemma lem134797 : term113.
Proof. exact (EQ_MP (@lem134796) (@lem134763)). Qed.
Lemma lem134799 {A : Type'} : (@ex A) = (term114 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem134800 : (@ex (nat -> nat -> nat -> nat)) = term115.
Proof. exact (@lem134799 type1602). Qed.
Lemma lem134801 : term112 = term112.
Proof. exact (eq_refl term112). Qed.
Lemma lem134802 : term113 = term116.
Proof. exact (MK_COMB (@lem134800) (@lem134801)). Qed.
Lemma lem134803 : term116 = term117.
Proof. exact (eq_refl term116). Qed.
Lemma lem134804 : term113 = term117.
Proof. exact (TRANS (@lem134802) (@lem134803)). Qed.
Lemma lem134805 : term117.
Proof. exact (EQ_MP (@lem134804) (@lem134797)). Qed.
