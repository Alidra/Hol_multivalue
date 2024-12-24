Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIMINDEX_HAS_SIZE_FINITE_PROD_term_abbrevs.
Require Import DIMINDEX_UNIV_spec.
Require Import DISJ_ACI_spec.
Require Import HAS_SIZE_IMAGE_INJ_spec.
Require Import HAS_SIZE_NUMSEG_1_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm1843_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm7919632_spec.
Require Import thm7919719_spec.
Require Import thm7921507_spec.
Lemma lem7921519 (n : nat) : term0 n.
Proof. exact (@lem5400760 n). Qed.
Lemma lem7921520 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem7921521 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem7921520 n) (@lem7921519 n)). Qed.
Lemma lem7921522 (n : nat) : (term1 n) = ((term1 n) = True).
Proof. exact (@lem7 (term1 n)). Qed.
Lemma lem7921524 {A : Type'} (s : A -> Prop) : term2 A s.
Proof. exact (@lem7594688 A s). Qed.
Lemma lem7921525 {A : Type'} (s : A -> Prop) : (term2 A s) = ((@dimindex A s) = (@dimindex A (@UNIV A))).
Proof. exact (eq_refl (term2 A s)). Qed.
Lemma lem7921527 {A B : Type'} (h1 : term3 A B) : term3 A B.
Proof. exact (h1). Qed.
Lemma lem7921528 {A B : Type'} (f : A -> B) (h1 : term3 A B) : term4 A B f.
Proof. exact (@lem7921527 A B h1 f). Qed.
Lemma lem7921529 {A B : Type'} (f : A -> B) : (term4 A B f) = (term5 A B f).
Proof. exact (eq_refl (term4 A B f)). Qed.
Lemma lem7921530 {A B : Type'} (f : A -> B) (h1 : term3 A B) : term5 A B f.
Proof. exact (EQ_MP (@lem7921529 A B f) (@lem7921528 A B f h1)). Qed.
Lemma lem7921531 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term3 A B) : term6 A B f s.
Proof. exact (@lem7921530 A B f h1 s). Qed.
Lemma lem7921532 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term6 A B f s) = (term7 A B f s).
Proof. exact (eq_refl (term6 A B f s)). Qed.
Lemma lem7921533 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term3 A B) : term7 A B f s.
Proof. exact (EQ_MP (@lem7921532 A B f s) (@lem7921531 A B f s h1)). Qed.
Lemma lem7921534 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term3 A B) : term8 A B f s n.
Proof. exact (@lem7921533 A B f s h1 n). Qed.
Lemma lem7921535 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term8 A B f s n) = (term9 A B f s n).
Proof. exact (eq_refl (term8 A B f s n)). Qed.
Lemma lem7921536 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term3 A B) : term9 A B f s n.
Proof. exact (EQ_MP (@lem7921535 A B f s n) (@lem7921534 A B f s n h1)). Qed.
Lemma lem7921537 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term10 A B f s n) : term10 A B f s n.
Proof. exact (h1). Qed.
Lemma lem7921538 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term3 A B) (h2 : term10 A B f s n) : term11 A B f s n.
Proof. exact (@lem7921536 A B f s n h1 (@lem7921537 A B f s n h2)). Qed.
Lemma lem7921539 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term10 A B f s n) : term12 A B f s n.
Proof. exact (fun h0 : term3 A B => @lem7921538 A B f s n h0 h1). Qed.
Lemma lem7921540 {A B : Type'} (h1 : term3 A B) : term3 A B.
Proof. exact (h1). Qed.
Lemma lem7921541 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term3 A B) (h2 : term10 A B f s n) : term11 A B f s n.
Proof. exact (@lem7921539 A B f s n h2 (@lem7921540 A B h1)). Qed.
Lemma lem7921542 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term3 A B) : term9 A B f s n.
Proof. exact (fun h0 : term10 A B f s n => @lem7921541 A B f s n h1 h0). Qed.
Lemma lem7921543 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term3 A B) : term7 A B f s.
Proof. exact (fun n : nat => @lem7921542 A B f s n h1). Qed.
Lemma lem7921544 {A B : Type'} (f : A -> B) (h1 : term3 A B) : term5 A B f.
Proof. exact (fun s : A -> Prop => @lem7921543 A B f s h1). Qed.
Lemma lem7921545 {A B : Type'} (h1 : term3 A B) : term3 A B.
Proof. exact (fun f : A -> B => @lem7921544 A B f h1). Qed.
Lemma lem7921546 {A B : Type'} : term13 A B.
Proof. exact (fun h0 : term3 A B => @lem7921545 A B h0). Qed.
Lemma lem7921547 {A B : Type'} : term3 A B.
Proof. exact (@lem7921546 A B (@lem4004559 A B)). Qed.
Lemma lem7921548 {A B : Type'} (f : A -> B) : term4 A B f.
Proof. exact (@lem7921547 A B f). Qed.
Lemma lem7921549 {A B : Type'} (f : A -> B) : (term4 A B f) = (term5 A B f).
Proof. exact (eq_refl (term4 A B f)). Qed.
Lemma lem7921550 {A B : Type'} (f : A -> B) : term5 A B f.
Proof. exact (EQ_MP (@lem7921549 A B f) (@lem7921548 A B f)). Qed.
Lemma lem7921551 {A B : Type'} (f : A -> B) (s : A -> Prop) : term6 A B f s.
Proof. exact (@lem7921550 A B f s). Qed.
Lemma lem7921552 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term6 A B f s) = (term7 A B f s).
Proof. exact (eq_refl (term6 A B f s)). Qed.
Lemma lem7921553 {A B : Type'} (f : A -> B) (s : A -> Prop) : term7 A B f s.
Proof. exact (EQ_MP (@lem7921552 A B f s) (@lem7921551 A B f s)). Qed.
Lemma lem7921554 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : term8 A B f s n.
Proof. exact (@lem7921553 A B f s n). Qed.
Lemma lem7921555 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term8 A B f s n) = (term9 A B f s n).
Proof. exact (eq_refl (term8 A B f s n)). Qed.
Lemma lem7921558 {A B : Type'} : (@UNIV (finite_prod A B)) = (term14 A B).
Proof. exact (EQ_MP (@lem7919719 A B) (@lem7921507 A B)). Qed.
Lemma lem7921559 {M N : Type'} : (@UNIV (finite_prod M N)) = (term14 M N).
Proof. exact (@lem7921558 M N). Qed.
Lemma lem7921564 {M N : Type'} : (@HAS_SIZE (finite_prod M N)) = (@HAS_SIZE (finite_prod M N)).
Proof. exact (eq_refl (@HAS_SIZE (finite_prod M N))). Qed.
Lemma lem7921565 {M N : Type'} : (@HAS_SIZE (finite_prod M N) (@UNIV (finite_prod M N))) = (term15 M N).
Proof. exact (MK_COMB (@lem7921564 M N) (@lem7921559 M N)). Qed.
Lemma lem7921574 {M N : Type'} : (term16 M N) = (term16 M N).
Proof. exact (eq_refl (term16 M N)). Qed.
Lemma lem7921575 {M N : Type'} : (term17 M N) = (term18 M N).
Proof. exact (MK_COMB (@lem7921565 M N) (@lem7921574 M N)). Qed.
Lemma lem7921584 {M N : Type'} : (term18 M N) = (term17 M N).
Proof. exact (SYM (@lem7921575 M N)). Qed.
Lemma lem7921586 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : term9 A B f s n.
Proof. exact (EQ_MP (@lem7921555 A B f s n) (@lem7921554 A B f s n)). Qed.
Lemma lem7921587 {M N : Type'} (f : type1558 M N) (s : nat -> Prop) (n : nat) : term19 M N f s n.
Proof. exact (@lem7921586 nat (finite_prod M N) f s n). Qed.
Lemma lem7921588 {M N : Type'} : term20 M N.
Proof. exact (@lem7921587 M N (@mk_finite_prod M N) (term21 M N) (term16 M N)). Qed.
Lemma lem7921604 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (@dimindex A (@UNIV A)).
Proof. exact (EQ_MP (@lem7921525 A s) (@lem7921524 A s)). Qed.
Lemma lem7921605 {M : Type'} (s : M -> Prop) : (@dimindex M s) = (@dimindex M (@UNIV M)).
Proof. exact (@lem7921604 M s). Qed.
Lemma lem7921606 {M : Type'} : (@dimindex M (@UNIV M)) = (@dimindex M (@UNIV M)).
Proof. exact (@lem7921605 M (@UNIV M)). Qed.
Lemma lem7921607 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem7921608 {M : Type'} : (term22 M) = (term22 M).
Proof. exact (MK_COMB (@lem7921607) (@lem7921606 M)). Qed.
Lemma lem7921610 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (@dimindex A (@UNIV A)).
Proof. exact (EQ_MP (@lem7921525 A s) (@lem7921524 A s)). Qed.
Lemma lem7921611 {N : Type'} (s : N -> Prop) : (@dimindex N s) = (@dimindex N (@UNIV N)).
Proof. exact (@lem7921610 N s). Qed.
Lemma lem7921612 {N : Type'} : (@dimindex N (@UNIV N)) = (@dimindex N (@UNIV N)).
Proof. exact (@lem7921611 N (@UNIV N)). Qed.
Lemma lem7921613 {M N : Type'} : (term16 M N) = (term16 M N).
Proof. exact (MK_COMB (@lem7921608 M) (@lem7921612 N)). Qed.
Lemma lem7921614 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem7921615 {M N : Type'} : (term21 M N) = (term21 M N).
Proof. exact (MK_COMB (@lem7921614) (@lem7921613 M N)). Qed.
Lemma lem7921616 (x : nat) : (@IN nat x) = (@IN nat x).
Proof. exact (eq_refl (@IN nat x)). Qed.
Lemma lem7921617 {M N : Type'} (x : nat) : (term24 M N x) = (term24 M N x).
Proof. exact (MK_COMB (@lem7921616 x) (@lem7921615 M N)). Qed.
Lemma lem7921618 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7921619 {M N : Type'} (x : nat) : (term25 M N x) = (term25 M N x).
Proof. exact (MK_COMB (@lem7921618) (@lem7921617 M N x)). Qed.
Lemma lem7921623 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (@dimindex A (@UNIV A)).
Proof. exact (EQ_MP (@lem7921525 A s) (@lem7921524 A s)). Qed.
Lemma lem7921624 {M : Type'} (s : M -> Prop) : (@dimindex M s) = (@dimindex M (@UNIV M)).
Proof. exact (@lem7921623 M s). Qed.
Lemma lem7921625 {M : Type'} : (@dimindex M (@UNIV M)) = (@dimindex M (@UNIV M)).
Proof. exact (@lem7921624 M (@UNIV M)). Qed.
Lemma lem7921626 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem7921627 {M : Type'} : (term22 M) = (term22 M).
Proof. exact (MK_COMB (@lem7921626) (@lem7921625 M)). Qed.
Lemma lem7921629 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (@dimindex A (@UNIV A)).
Proof. exact (EQ_MP (@lem7921525 A s) (@lem7921524 A s)). Qed.
Lemma lem7921630 {N : Type'} (s : N -> Prop) : (@dimindex N s) = (@dimindex N (@UNIV N)).
Proof. exact (@lem7921629 N s). Qed.
Lemma lem7921631 {N : Type'} : (@dimindex N (@UNIV N)) = (@dimindex N (@UNIV N)).
Proof. exact (@lem7921630 N (@UNIV N)). Qed.
Lemma lem7921632 {M N : Type'} : (term16 M N) = (term16 M N).
Proof. exact (MK_COMB (@lem7921627 M) (@lem7921631 N)). Qed.
Lemma lem7921633 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem7921634 {M N : Type'} : (term21 M N) = (term21 M N).
Proof. exact (MK_COMB (@lem7921633) (@lem7921632 M N)). Qed.
Lemma lem7921635 (y : nat) : (@IN nat y) = (@IN nat y).
Proof. exact (eq_refl (@IN nat y)). Qed.
Lemma lem7921636 {M N : Type'} (y : nat) : (term24 M N y) = (term24 M N y).
Proof. exact (MK_COMB (@lem7921635 y) (@lem7921634 M N)). Qed.
Lemma lem7921637 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7921638 {M N : Type'} (y : nat) : (term25 M N y) = (term25 M N y).
Proof. exact (MK_COMB (@lem7921637) (@lem7921636 M N y)). Qed.
Lemma lem7921641 {M N : Type'} (x : nat) (y : nat) : ((@mk_finite_prod M N x) = (@mk_finite_prod M N y)) = ((@mk_finite_prod M N x) = (@mk_finite_prod M N y)).
Proof. exact (eq_refl ((@mk_finite_prod M N x) = (@mk_finite_prod M N y))). Qed.
Lemma lem7921642 {M N : Type'} (x : nat) (y : nat) : (term26 M N x y) = (term26 M N x y).
Proof. exact (MK_COMB (@lem7921638 M N y) (@lem7921641 M N x y)). Qed.
Lemma lem7921643 {M N : Type'} (x : nat) (y : nat) : (term27 M N x y) = (term27 M N x y).
Proof. exact (MK_COMB (@lem7921619 M N x) (@lem7921642 M N x y)). Qed.
Lemma lem7921644 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7921645 {M N : Type'} (x : nat) (y : nat) : (term28 M N x y) = (term28 M N x y).
Proof. exact (MK_COMB (@lem7921644) (@lem7921643 M N x y)). Qed.
Lemma lem7921648 (x : nat) (y : nat) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem7921649 {M N : Type'} (x : nat) (y : nat) : (term29 M N x y) = (term29 M N x y).
Proof. exact (MK_COMB (@lem7921645 M N x y) (@lem7921648 x y)). Qed.
Lemma lem7921650 {M N : Type'} (x : nat) : (term30 M N x) = (term30 M N x).
Proof. exact (fun_ext (fun y : nat => @lem7921649 M N x y)). Qed.
Lemma lem7921651 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7921652 {M N : Type'} (x : nat) : (term31 M N x) = (term31 M N x).
Proof. exact (MK_COMB (@lem7921651) (@lem7921650 M N x)). Qed.
Lemma lem7921653 {M N : Type'} : (term32 M N) = (term32 M N).
Proof. exact (fun_ext (fun x : nat => @lem7921652 M N x)). Qed.
Lemma lem7921654 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7921655 {M N : Type'} : (term33 M N) = (term33 M N).
Proof. exact (MK_COMB (@lem7921654) (@lem7921653 M N)). Qed.
Lemma lem7921656 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7921657 {M N : Type'} : (term34 M N) = (term34 M N).
Proof. exact (MK_COMB (@lem7921656) (@lem7921655 M N)). Qed.
Lemma lem7921659 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (@dimindex A (@UNIV A)).
Proof. exact (EQ_MP (@lem7921525 A s) (@lem7921524 A s)). Qed.
Lemma lem7921660 {M : Type'} (s : M -> Prop) : (@dimindex M s) = (@dimindex M (@UNIV M)).
Proof. exact (@lem7921659 M s). Qed.
Lemma lem7921661 {M : Type'} : (@dimindex M (@UNIV M)) = (@dimindex M (@UNIV M)).
Proof. exact (@lem7921660 M (@UNIV M)). Qed.
Lemma lem7921662 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem7921663 {M : Type'} : (term22 M) = (term22 M).
Proof. exact (MK_COMB (@lem7921662) (@lem7921661 M)). Qed.
Lemma lem7921665 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (@dimindex A (@UNIV A)).
Proof. exact (EQ_MP (@lem7921525 A s) (@lem7921524 A s)). Qed.
Lemma lem7921666 {N : Type'} (s : N -> Prop) : (@dimindex N s) = (@dimindex N (@UNIV N)).
Proof. exact (@lem7921665 N s). Qed.
Lemma lem7921667 {N : Type'} : (@dimindex N (@UNIV N)) = (@dimindex N (@UNIV N)).
Proof. exact (@lem7921666 N (@UNIV N)). Qed.
Lemma lem7921668 {M N : Type'} : (term16 M N) = (term16 M N).
Proof. exact (MK_COMB (@lem7921663 M) (@lem7921667 N)). Qed.
Lemma lem7921669 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem7921670 {M N : Type'} : (term21 M N) = (term21 M N).
Proof. exact (MK_COMB (@lem7921669) (@lem7921668 M N)). Qed.
Lemma lem7921671 : (@HAS_SIZE nat) = (@HAS_SIZE nat).
Proof. exact (eq_refl (@HAS_SIZE nat)). Qed.
Lemma lem7921672 {M N : Type'} : (term35 M N) = (term35 M N).
Proof. exact (MK_COMB (@lem7921671) (@lem7921670 M N)). Qed.
Lemma lem7921674 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (@dimindex A (@UNIV A)).
Proof. exact (EQ_MP (@lem7921525 A s) (@lem7921524 A s)). Qed.
Lemma lem7921675 {M : Type'} (s : M -> Prop) : (@dimindex M s) = (@dimindex M (@UNIV M)).
Proof. exact (@lem7921674 M s). Qed.
Lemma lem7921676 {M : Type'} : (@dimindex M (@UNIV M)) = (@dimindex M (@UNIV M)).
Proof. exact (@lem7921675 M (@UNIV M)). Qed.
Lemma lem7921677 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem7921678 {M : Type'} : (term22 M) = (term22 M).
Proof. exact (MK_COMB (@lem7921677) (@lem7921676 M)). Qed.
Lemma lem7921680 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (@dimindex A (@UNIV A)).
Proof. exact (EQ_MP (@lem7921525 A s) (@lem7921524 A s)). Qed.
Lemma lem7921681 {N : Type'} (s : N -> Prop) : (@dimindex N s) = (@dimindex N (@UNIV N)).
Proof. exact (@lem7921680 N s). Qed.
Lemma lem7921682 {N : Type'} : (@dimindex N (@UNIV N)) = (@dimindex N (@UNIV N)).
Proof. exact (@lem7921681 N (@UNIV N)). Qed.
Lemma lem7921683 {M N : Type'} : (term16 M N) = (term16 M N).
Proof. exact (MK_COMB (@lem7921678 M) (@lem7921682 N)). Qed.
Lemma lem7921684 {M N : Type'} : (term36 M N) = (term36 M N).
Proof. exact (MK_COMB (@lem7921672 M N) (@lem7921683 M N)). Qed.
Lemma lem7921685 {M N : Type'} : (term37 M N) = (term37 M N).
Proof. exact (MK_COMB (@lem7921657 M N) (@lem7921684 M N)). Qed.
Lemma lem7921686 {M N : Type'} : (term37 M N) = (term37 M N).
Proof. exact (SYM (@lem7921685 M N)). Qed.
Lemma lem7921708 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem7921522 n) (@lem7921521 n)). Qed.
Lemma lem7921709 {M N : Type'} : (term36 M N) = True.
Proof. exact (@lem7921708 (term16 M N)). Qed.
Lemma lem7921710 {M N : Type'} : (term34 M N) = (term34 M N).
Proof. exact (eq_refl (term34 M N)). Qed.
Lemma lem7921711 {M N : Type'} : (term37 M N) = (term38 M N).
Proof. exact (MK_COMB (@lem7921710 M N) (@lem7921709 M N)). Qed.
Lemma lem7921713 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem7921714 {M N : Type'} : (term38 M N) = (term33 M N).
Proof. exact (@lem7921713 (term33 M N)). Qed.
Lemma lem7921733 {M N : Type'} : (term37 M N) = (term33 M N).
Proof. exact (TRANS (@lem7921711 M N) (@lem7921714 M N)). Qed.
Lemma lem7921734 {M N : Type'} : (term33 M N) = (term37 M N).
Proof. exact (SYM (@lem7921733 M N)). Qed.
Lemma lem7921736 (p : Prop) : p = (term39 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7921737 {M N : Type'} : (term33 M N) = (term40 M N).
Proof. exact (@lem7921736 (term33 M N)). Qed.
Lemma lem7921738 {M N : Type'} : (term40 M N) = (term33 M N).
Proof. exact (SYM (@lem7921737 M N)). Qed.
Lemma lem7921739 {M N : Type'} (h1 : term41 M N) : term41 M N.
Proof. exact (h1). Qed.
Lemma lem7921740 {M N : Type'} : term42 M N.
Proof. exact (@lem7919632 M N). Qed.
Lemma lem7921742 {B M : Type'} : term43 B M.
Proof. exact (@lem7919632 M B). Qed.
Lemma lem7921743 {B N : Type'} : term43 B N.
Proof. exact (@lem7919632 N B). Qed.
Lemma lem7921746 {A M : Type'} : term42 A M.
Proof. exact (@lem7919632 A M). Qed.
Lemma lem7921747 {A N : Type'} : term42 A N.
Proof. exact (@lem7919632 A N). Qed.
Lemma lem7921752 {A B M N : Type'} (h1 : term44 A B M N) : term44 A B M N.
Proof. exact (h1). Qed.
Lemma lem7921753 {A B M N : Type'} : term45 A B M N.
Proof. exact (fun h0 : term44 A B M N => @lem7921752 A B M N h0). Qed.
Lemma lem7921754 {A B M N : Type'} (h1 : term45 A B M N) : term45 A B M N.
Proof. exact (h1). Qed.
Lemma lem7921755 {A B M N : Type'} (h1 : term44 A B M N) : term44 A B M N.
Proof. exact (h1). Qed.
Lemma lem7921756 {A B M N : Type'} (h1 : term44 A B M N) (h2 : term45 A B M N) : term44 A B M N.
Proof. exact (@lem7921754 A B M N h2 (@lem7921755 A B M N h1)). Qed.
Lemma lem7921757 {A B M N : Type'} (h1 : term44 A B M N) : term46 A B M N.
Proof. exact (fun h0 : term45 A B M N => @lem7921756 A B M N h1 h0). Qed.
Lemma lem7921758 {A B M N : Type'} (h1 : term45 A B M N) : term45 A B M N.
Proof. exact (h1). Qed.
Lemma lem7921759 {A B M N : Type'} (h1 : term44 A B M N) (h2 : term45 A B M N) : term44 A B M N.
Proof. exact (@lem7921757 A B M N h1 (@lem7921758 A B M N h2)). Qed.
Lemma lem7921760 {A B M N : Type'} (h1 : term45 A B M N) : term45 A B M N.
Proof. exact (fun h0 : term44 A B M N => @lem7921759 A B M N h0 h1). Qed.
Lemma lem7921761 {A B M N : Type'} : term47 A B M N.
Proof. exact (fun h0 : term45 A B M N => @lem7921760 A B M N h0). Qed.
Lemma lem7921764 {A B M N : Type'} : term45 A B M N.
Proof. exact (@lem7921761 A B M N (@lem7921753 A B M N)). Qed.
Lemma lem7921765 {A B M N : Type'} : term45 A B M N.
Proof. exact (@lem7921764 A B M N). Qed.
Lemma lem7921843 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7921844 {B N : Type'} : (term48 B N) = (term49 B N).
Proof. exact (@lem7921843 (term43 B N)). Qed.
Lemma lem7921855 {M N : Type'} : (term50 M N) = (term50 M N).
Proof. exact (eq_refl (term50 M N)). Qed.
Lemma lem7921856 {B M N : Type'} : (term51 B M N) = (term52 B M N).
Proof. exact (MK_COMB (@lem7921855 M N) (@lem7921844 B N)). Qed.
Lemma lem7921859 {B M : Type'} : (term53 B M) = (term53 B M).
Proof. exact (eq_refl (term53 B M)). Qed.
Lemma lem7921860 {B M N : Type'} : (term54 B M N) = (term55 B M N).
Proof. exact (MK_COMB (@lem7921859 B M) (@lem7921856 B M N)). Qed.
Lemma lem7921863 {A N : Type'} : (term50 A N) = (term50 A N).
Proof. exact (eq_refl (term50 A N)). Qed.
Lemma lem7921864 {A B M N : Type'} : (term56 A B M N) = (term57 A B M N).
Proof. exact (MK_COMB (@lem7921863 A N) (@lem7921860 B M N)). Qed.
Lemma lem7921867 {A M : Type'} : (term50 A M) = (term50 A M).
Proof. exact (eq_refl (term50 A M)). Qed.
Lemma lem7921868 {A B M N : Type'} : (term58 A B M N) = (term59 A B M N).
Proof. exact (MK_COMB (@lem7921867 A M) (@lem7921864 A B M N)). Qed.
Lemma lem7921871 {A B : Type'} : (term50 A B) = (term50 A B).
Proof. exact (eq_refl (term50 A B)). Qed.
Lemma lem7921872 {A B M N : Type'} : (term60 A B M N) = (term61 A B M N).
Proof. exact (MK_COMB (@lem7921871 A B) (@lem7921868 A B M N)). Qed.
Lemma lem7921875 {M N : Type'} : (term62 M N) = (term62 M N).
Proof. exact (eq_refl (term62 M N)). Qed.
Lemma lem7921882 {A B M N : Type'} : (term44 A B M N) = (term63 A B M N).
Proof. exact (MK_COMB (@lem7921875 M N) (@lem7921872 A B M N)). Qed.
Lemma lem7921887 {B N : Type'} (r : nat) : ((term64 B N r) = ((term65 B N r) = r)) = ((term64 B N r) = ((term65 B N r) = r)).
Proof. exact (eq_refl ((term64 B N r) = ((term65 B N r) = r))). Qed.
Lemma lem7921888 {B N : Type'} : (term66 B N) = (term66 B N).
Proof. exact (fun_ext (fun r : nat => @lem7921887 B N r)). Qed.
Lemma lem7921889 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7921890 {B N : Type'} : (term67 B N) = (term67 B N).
Proof. exact (MK_COMB (@lem7921889) (@lem7921888 B N)). Qed.
Lemma lem7921891 {B N : Type'} (a : finite_prod N B) : ((term68 B N a) = a) = ((term68 B N a) = a).
Proof. exact (eq_refl ((term68 B N a) = a)). Qed.
Lemma lem7921892 {B N : Type'} : (term69 B N) = (term69 B N).
Proof. exact (fun_ext (fun a : finite_prod N B => @lem7921891 B N a)). Qed.
Lemma lem7921893 {B N : Type'} : (@all (finite_prod N B)) = (@all (finite_prod N B)).
Proof. exact (eq_refl (@all (finite_prod N B))). Qed.
Lemma lem7921894 {B N : Type'} : (term70 B N) = (term70 B N).
Proof. exact (MK_COMB (@lem7921893 B N) (@lem7921892 B N)). Qed.
Lemma lem7921895 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7921896 {B N : Type'} : (term71 B N) = (term71 B N).
Proof. exact (MK_COMB (@lem7921895) (@lem7921894 B N)). Qed.
Lemma lem7921897 {B N : Type'} : (term43 B N) = (term43 B N).
Proof. exact (MK_COMB (@lem7921896 B N) (@lem7921890 B N)). Qed.
Lemma lem7921898 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7921899 {B N : Type'} : (term49 B N) = (term49 B N).
Proof. exact (MK_COMB (@lem7921898) (@lem7921897 B N)). Qed.
Lemma lem7921904 {M N : Type'} (r : nat) : ((term24 M N r) = ((term72 M N r) = r)) = ((term24 M N r) = ((term72 M N r) = r)).
Proof. exact (eq_refl ((term24 M N r) = ((term72 M N r) = r))). Qed.
Lemma lem7921905 {M N : Type'} : (term73 M N) = (term73 M N).
Proof. exact (fun_ext (fun r : nat => @lem7921904 M N r)). Qed.
Lemma lem7921906 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7921907 {M N : Type'} : (term74 M N) = (term74 M N).
Proof. exact (MK_COMB (@lem7921906) (@lem7921905 M N)). Qed.
Lemma lem7921908 {M N : Type'} (a : finite_prod M N) : ((term75 M N a) = a) = ((term75 M N a) = a).
Proof. exact (eq_refl ((term75 M N a) = a)). Qed.
Lemma lem7921909 {M N : Type'} : (term76 M N) = (term76 M N).
Proof. exact (fun_ext (fun a : finite_prod M N => @lem7921908 M N a)). Qed.
Lemma lem7921910 {M N : Type'} : (@all (finite_prod M N)) = (@all (finite_prod M N)).
Proof. exact (eq_refl (@all (finite_prod M N))). Qed.
Lemma lem7921911 {M N : Type'} : (term77 M N) = (term77 M N).
Proof. exact (MK_COMB (@lem7921910 M N) (@lem7921909 M N)). Qed.
Lemma lem7921912 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7921913 {M N : Type'} : (term78 M N) = (term78 M N).
Proof. exact (MK_COMB (@lem7921912) (@lem7921911 M N)). Qed.
Lemma lem7921914 {M N : Type'} : (term42 M N) = (term42 M N).
Proof. exact (MK_COMB (@lem7921913 M N) (@lem7921907 M N)). Qed.
Lemma lem7921915 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7921916 {M N : Type'} : (term50 M N) = (term50 M N).
Proof. exact (MK_COMB (@lem7921915) (@lem7921914 M N)). Qed.
Lemma lem7921917 {B M N : Type'} : (term52 B M N) = (term52 B M N).
Proof. exact (MK_COMB (@lem7921916 M N) (@lem7921899 B N)). Qed.
Lemma lem7921922 {B M : Type'} (r : nat) : ((term64 B M r) = ((term65 B M r) = r)) = ((term64 B M r) = ((term65 B M r) = r)).
Proof. exact (eq_refl ((term64 B M r) = ((term65 B M r) = r))). Qed.
Lemma lem7921923 {B M : Type'} : (term66 B M) = (term66 B M).
Proof. exact (fun_ext (fun r : nat => @lem7921922 B M r)). Qed.
Lemma lem7921924 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7921925 {B M : Type'} : (term67 B M) = (term67 B M).
Proof. exact (MK_COMB (@lem7921924) (@lem7921923 B M)). Qed.
Lemma lem7921926 {B M : Type'} (a : finite_prod M B) : ((term68 B M a) = a) = ((term68 B M a) = a).
Proof. exact (eq_refl ((term68 B M a) = a)). Qed.
Lemma lem7921927 {B M : Type'} : (term69 B M) = (term69 B M).
Proof. exact (fun_ext (fun a : finite_prod M B => @lem7921926 B M a)). Qed.
Lemma lem7921928 {B M : Type'} : (@all (finite_prod M B)) = (@all (finite_prod M B)).
Proof. exact (eq_refl (@all (finite_prod M B))). Qed.
Lemma lem7921929 {B M : Type'} : (term70 B M) = (term70 B M).
Proof. exact (MK_COMB (@lem7921928 B M) (@lem7921927 B M)). Qed.
Lemma lem7921930 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7921931 {B M : Type'} : (term71 B M) = (term71 B M).
Proof. exact (MK_COMB (@lem7921930) (@lem7921929 B M)). Qed.
Lemma lem7921932 {B M : Type'} : (term43 B M) = (term43 B M).
Proof. exact (MK_COMB (@lem7921931 B M) (@lem7921925 B M)). Qed.
Lemma lem7921933 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7921934 {B M : Type'} : (term53 B M) = (term53 B M).
Proof. exact (MK_COMB (@lem7921933) (@lem7921932 B M)). Qed.
Lemma lem7921935 {B M N : Type'} : (term55 B M N) = (term55 B M N).
Proof. exact (MK_COMB (@lem7921934 B M) (@lem7921917 B M N)). Qed.
Lemma lem7921940 {A N : Type'} (r : nat) : ((term24 A N r) = ((term72 A N r) = r)) = ((term24 A N r) = ((term72 A N r) = r)).
Proof. exact (eq_refl ((term24 A N r) = ((term72 A N r) = r))). Qed.
Lemma lem7921941 {A N : Type'} : (term73 A N) = (term73 A N).
Proof. exact (fun_ext (fun r : nat => @lem7921940 A N r)). Qed.
Lemma lem7921942 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7921943 {A N : Type'} : (term74 A N) = (term74 A N).
Proof. exact (MK_COMB (@lem7921942) (@lem7921941 A N)). Qed.
Lemma lem7921944 {A N : Type'} (a : finite_prod A N) : ((term75 A N a) = a) = ((term75 A N a) = a).
Proof. exact (eq_refl ((term75 A N a) = a)). Qed.
Lemma lem7921945 {A N : Type'} : (term76 A N) = (term76 A N).
Proof. exact (fun_ext (fun a : finite_prod A N => @lem7921944 A N a)). Qed.
Lemma lem7921946 {A N : Type'} : (@all (finite_prod A N)) = (@all (finite_prod A N)).
Proof. exact (eq_refl (@all (finite_prod A N))). Qed.
Lemma lem7921947 {A N : Type'} : (term77 A N) = (term77 A N).
Proof. exact (MK_COMB (@lem7921946 A N) (@lem7921945 A N)). Qed.
Lemma lem7921948 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7921949 {A N : Type'} : (term78 A N) = (term78 A N).
Proof. exact (MK_COMB (@lem7921948) (@lem7921947 A N)). Qed.
Lemma lem7921950 {A N : Type'} : (term42 A N) = (term42 A N).
Proof. exact (MK_COMB (@lem7921949 A N) (@lem7921943 A N)). Qed.
Lemma lem7921951 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7921952 {A N : Type'} : (term50 A N) = (term50 A N).
Proof. exact (MK_COMB (@lem7921951) (@lem7921950 A N)). Qed.
Lemma lem7921953 {A B M N : Type'} : (term57 A B M N) = (term57 A B M N).
Proof. exact (MK_COMB (@lem7921952 A N) (@lem7921935 B M N)). Qed.
Lemma lem7921958 {A M : Type'} (r : nat) : ((term24 A M r) = ((term72 A M r) = r)) = ((term24 A M r) = ((term72 A M r) = r)).
Proof. exact (eq_refl ((term24 A M r) = ((term72 A M r) = r))). Qed.
Lemma lem7921959 {A M : Type'} : (term73 A M) = (term73 A M).
Proof. exact (fun_ext (fun r : nat => @lem7921958 A M r)). Qed.
Lemma lem7921960 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7921961 {A M : Type'} : (term74 A M) = (term74 A M).
Proof. exact (MK_COMB (@lem7921960) (@lem7921959 A M)). Qed.
Lemma lem7921962 {A M : Type'} (a : finite_prod A M) : ((term75 A M a) = a) = ((term75 A M a) = a).
Proof. exact (eq_refl ((term75 A M a) = a)). Qed.
Lemma lem7921963 {A M : Type'} : (term76 A M) = (term76 A M).
Proof. exact (fun_ext (fun a : finite_prod A M => @lem7921962 A M a)). Qed.
Lemma lem7921964 {A M : Type'} : (@all (finite_prod A M)) = (@all (finite_prod A M)).
Proof. exact (eq_refl (@all (finite_prod A M))). Qed.
Lemma lem7921965 {A M : Type'} : (term77 A M) = (term77 A M).
Proof. exact (MK_COMB (@lem7921964 A M) (@lem7921963 A M)). Qed.
Lemma lem7921966 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7921967 {A M : Type'} : (term78 A M) = (term78 A M).
Proof. exact (MK_COMB (@lem7921966) (@lem7921965 A M)). Qed.
Lemma lem7921968 {A M : Type'} : (term42 A M) = (term42 A M).
Proof. exact (MK_COMB (@lem7921967 A M) (@lem7921961 A M)). Qed.
Lemma lem7921969 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7921970 {A M : Type'} : (term50 A M) = (term50 A M).
Proof. exact (MK_COMB (@lem7921969) (@lem7921968 A M)). Qed.
Lemma lem7921971 {A B M N : Type'} : (term59 A B M N) = (term59 A B M N).
Proof. exact (MK_COMB (@lem7921970 A M) (@lem7921953 A B M N)). Qed.
Lemma lem7921976 {A B : Type'} (r : nat) : ((term24 A B r) = ((term72 A B r) = r)) = ((term24 A B r) = ((term72 A B r) = r)).
Proof. exact (eq_refl ((term24 A B r) = ((term72 A B r) = r))). Qed.
Lemma lem7921977 {A B : Type'} : (term73 A B) = (term73 A B).
Proof. exact (fun_ext (fun r : nat => @lem7921976 A B r)). Qed.
Lemma lem7921978 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7921979 {A B : Type'} : (term74 A B) = (term74 A B).
Proof. exact (MK_COMB (@lem7921978) (@lem7921977 A B)). Qed.
Lemma lem7921980 {A B : Type'} (a : finite_prod A B) : ((term75 A B a) = a) = ((term75 A B a) = a).
Proof. exact (eq_refl ((term75 A B a) = a)). Qed.
Lemma lem7921981 {A B : Type'} : (term76 A B) = (term76 A B).
Proof. exact (fun_ext (fun a : finite_prod A B => @lem7921980 A B a)). Qed.
Lemma lem7921982 {A B : Type'} : (@all (finite_prod A B)) = (@all (finite_prod A B)).
Proof. exact (eq_refl (@all (finite_prod A B))). Qed.
Lemma lem7921983 {A B : Type'} : (term77 A B) = (term77 A B).
Proof. exact (MK_COMB (@lem7921982 A B) (@lem7921981 A B)). Qed.
Lemma lem7921984 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7921985 {A B : Type'} : (term78 A B) = (term78 A B).
Proof. exact (MK_COMB (@lem7921984) (@lem7921983 A B)). Qed.
Lemma lem7921986 {A B : Type'} : (term42 A B) = (term42 A B).
Proof. exact (MK_COMB (@lem7921985 A B) (@lem7921979 A B)). Qed.
Lemma lem7921987 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7921988 {A B : Type'} : (term50 A B) = (term50 A B).
Proof. exact (MK_COMB (@lem7921987) (@lem7921986 A B)). Qed.
Lemma lem7921989 {A B M N : Type'} : (term61 A B M N) = (term61 A B M N).
Proof. exact (MK_COMB (@lem7921988 A B) (@lem7921971 A B M N)). Qed.
Lemma lem7922002 {M N : Type'} (x : nat) (y : nat) : (term29 M N x y) = (term29 M N x y).
Proof. exact (eq_refl (term29 M N x y)). Qed.
Lemma lem7922003 {M N : Type'} (x : nat) : (term30 M N x) = (term30 M N x).
Proof. exact (fun_ext (fun y : nat => @lem7922002 M N x y)). Qed.
Lemma lem7922004 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7922005 {M N : Type'} (x : nat) : (term31 M N x) = (term31 M N x).
Proof. exact (MK_COMB (@lem7922004) (@lem7922003 M N x)). Qed.
Lemma lem7922006 {M N : Type'} : (term32 M N) = (term32 M N).
Proof. exact (fun_ext (fun x : nat => @lem7922005 M N x)). Qed.
Lemma lem7922007 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7922008 {M N : Type'} : (term33 M N) = (term33 M N).
Proof. exact (MK_COMB (@lem7922007) (@lem7922006 M N)). Qed.
Lemma lem7922009 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7922010 {M N : Type'} : (term41 M N) = (term41 M N).
Proof. exact (MK_COMB (@lem7922009) (@lem7922008 M N)). Qed.
Lemma lem7922011 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7922012 {M N : Type'} : (term62 M N) = (term62 M N).
Proof. exact (MK_COMB (@lem7922011) (@lem7922010 M N)). Qed.
Lemma lem7922013 {A B M N : Type'} : (term63 A B M N) = (term63 A B M N).
Proof. exact (MK_COMB (@lem7922012 M N) (@lem7921989 A B M N)). Qed.
Lemma lem7922130 {A B M N : Type'} : (term44 A B M N) = (term63 A B M N).
Proof. exact (TRANS (@lem7921882 A B M N) (@lem7922013 A B M N)). Qed.
Lemma lem7922131 {A B M N : Type'} : (term63 A B M N) = (term44 A B M N).
Proof. exact (SYM (@lem7922130 A B M N)). Qed.
Lemma lem7922132 {M N : Type'} (h1 : term41 M N) : term41 M N.
Proof. exact (h1). Qed.
Lemma lem7922137 {M N : Type'} (h1 : term42 M N) : term42 M N.
Proof. exact (h1). Qed.
Lemma lem7922153 {M N : Type'} (x : nat) (y : nat) : (term79 M N x y) = (term80 M N x y).
Proof. exact (@lem17362 (term27 M N x y) (x = y)). Qed.
Lemma lem7922154 (P : nat -> Prop) : (term81 P) = (term82 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7922155 {M N : Type'} (x : nat) : (term83 M N x) = (term84 M N x).
Proof. exact (@lem7922154 (term30 M N x)). Qed.
Lemma lem7922156 {M N : Type'} (x : nat) (y : nat) : (term85 M N x y) = (term29 M N x y).
Proof. exact (eq_refl (term85 M N x y)). Qed.
Lemma lem7922157 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7922158 {M N : Type'} (x : nat) (y : nat) : (term86 M N x y) = (term79 M N x y).
Proof. exact (MK_COMB (@lem7922157) (@lem7922156 M N x y)). Qed.
Lemma lem7922159 {M N : Type'} (x : nat) (y : nat) : (term86 M N x y) = (term80 M N x y).
Proof. exact (TRANS (@lem7922158 M N x y) (@lem7922153 M N x y)). Qed.
Lemma lem7922160 {M N : Type'} (x : nat) : (term87 M N x) = (term88 M N x).
Proof. exact (fun_ext (fun y : nat => @lem7922159 M N x y)). Qed.
Lemma lem7922161 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7922162 {M N : Type'} (x : nat) : (term84 M N x) = (term89 M N x).
Proof. exact (MK_COMB (@lem7922161) (@lem7922160 M N x)). Qed.
Lemma lem7922163 {M N : Type'} (x : nat) : (term83 M N x) = (term89 M N x).
Proof. exact (TRANS (@lem7922155 M N x) (@lem7922162 M N x)). Qed.
Lemma lem7922164 (P : nat -> Prop) : (term81 P) = (term82 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7922165 {M N : Type'} : (term41 M N) = (term90 M N).
Proof. exact (@lem7922164 (term32 M N)). Qed.
Lemma lem7922166 {M N : Type'} (x : nat) : (term91 M N x) = (term31 M N x).
Proof. exact (eq_refl (term91 M N x)). Qed.
Lemma lem7922167 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7922168 {M N : Type'} (x : nat) : (term92 M N x) = (term83 M N x).
Proof. exact (MK_COMB (@lem7922167) (@lem7922166 M N x)). Qed.
Lemma lem7922169 {M N : Type'} (x : nat) : (term92 M N x) = (term89 M N x).
Proof. exact (TRANS (@lem7922168 M N x) (@lem7922163 M N x)). Qed.
Lemma lem7922170 {M N : Type'} : (term93 M N) = (term94 M N).
Proof. exact (fun_ext (fun x : nat => @lem7922169 M N x)). Qed.
Lemma lem7922171 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7922172 {M N : Type'} : (term90 M N) = (term95 M N).
Proof. exact (MK_COMB (@lem7922171) (@lem7922170 M N)). Qed.
Lemma lem7922229 {M N : Type'} : (term41 M N) = (term95 M N).
Proof. exact (TRANS (@lem7922165 M N) (@lem7922172 M N)). Qed.
Lemma lem7922230 {M N : Type'} (h1 : term41 M N) : term95 M N.
Proof. exact (EQ_MP (@lem7922229 M N) (@lem7922132 M N h1)). Qed.
Lemma lem7922863 {M N : Type'} (a : finite_prod M N) : ((term75 M N a) = a) = ((term75 M N a) = a).
Proof. exact (eq_refl ((term75 M N a) = a)). Qed.
Lemma lem7922864 {M N : Type'} : (term76 M N) = (term76 M N).
Proof. exact (fun_ext (fun a : finite_prod M N => @lem7922863 M N a)). Qed.
Lemma lem7922865 {M N : Type'} : (@all (finite_prod M N)) = (@all (finite_prod M N)).
Proof. exact (eq_refl (@all (finite_prod M N))). Qed.
Lemma lem7922866 {M N : Type'} : (term77 M N) = (term77 M N).
Proof. exact (MK_COMB (@lem7922865 M N) (@lem7922864 M N)). Qed.
Lemma lem7922881 {M N : Type'} (r : nat) : ((term24 M N r) = ((term72 M N r) = r)) = (term96 M N r).
Proof. exact (@lem17784 (term24 M N r) ((term72 M N r) = r)). Qed.
Lemma lem7922882 {M N : Type'} : (term73 M N) = (term97 M N).
Proof. exact (fun_ext (fun r : nat => @lem7922881 M N r)). Qed.
Lemma lem7922883 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7922884 {M N : Type'} : (term74 M N) = (term98 M N).
Proof. exact (MK_COMB (@lem7922883) (@lem7922882 M N)). Qed.
Lemma lem7922885 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7922886 {M N : Type'} : (term78 M N) = (term78 M N).
Proof. exact (MK_COMB (@lem7922885) (@lem7922866 M N)). Qed.
Lemma lem7922887 {M N : Type'} : (term42 M N) = (term99 M N).
Proof. exact (MK_COMB (@lem7922886 M N) (@lem7922884 M N)). Qed.
Lemma lem7922893 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term100 A P Q) = (term101 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7922894 (P : nat -> Prop) (Q : nat -> Prop) : (term102 P Q) = (term103 P Q).
Proof. exact (@lem7922893 nat P Q). Qed.
Lemma lem7922895 {M N : Type'} : (term104 M N) = (term105 M N).
Proof. exact (@lem7922894 (term106 M N) (term107 M N)). Qed.
Lemma lem7922896 {M N : Type'} (r : nat) : (term108 M N r) = (term109 M N r).
Proof. exact (eq_refl (term108 M N r)). Qed.
Lemma lem7922897 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7922898 {M N : Type'} (r : nat) : (term110 M N r) = (term111 M N r).
Proof. exact (MK_COMB (@lem7922897) (@lem7922896 M N r)). Qed.
Lemma lem7922899 {M N : Type'} (r : nat) : (term112 M N r) = (term113 M N r).
Proof. exact (eq_refl (term112 M N r)). Qed.
Lemma lem7922900 {M N : Type'} (r : nat) : (term114 M N r) = (term96 M N r).
Proof. exact (MK_COMB (@lem7922898 M N r) (@lem7922899 M N r)). Qed.
Lemma lem7922901 {M N : Type'} : (term115 M N) = (term97 M N).
Proof. exact (fun_ext (fun r : nat => @lem7922900 M N r)). Qed.
Lemma lem7922902 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7922903 {M N : Type'} : (term104 M N) = (term98 M N).
Proof. exact (MK_COMB (@lem7922902) (@lem7922901 M N)). Qed.
Lemma lem7922904 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7922905 {M N : Type'} : (term116 M N) = (term117 M N).
Proof. exact (MK_COMB (@lem7922904) (@lem7922903 M N)). Qed.
Lemma lem7922906 {M N : Type'} (r : nat) : (term108 M N r) = (term109 M N r).
Proof. exact (eq_refl (term108 M N r)). Qed.
Lemma lem7922907 {M N : Type'} : (term118 M N) = (term106 M N).
Proof. exact (fun_ext (fun r : nat => @lem7922906 M N r)). Qed.
Lemma lem7922908 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7922909 {M N : Type'} : (term119 M N) = (term120 M N).
Proof. exact (MK_COMB (@lem7922908) (@lem7922907 M N)). Qed.
Lemma lem7922910 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7922911 {M N : Type'} : (term121 M N) = (term122 M N).
Proof. exact (MK_COMB (@lem7922910) (@lem7922909 M N)). Qed.
Lemma lem7922912 {M N : Type'} (r : nat) : (term112 M N r) = (term113 M N r).
Proof. exact (eq_refl (term112 M N r)). Qed.
Lemma lem7922913 {M N : Type'} : (term123 M N) = (term107 M N).
Proof. exact (fun_ext (fun r : nat => @lem7922912 M N r)). Qed.
Lemma lem7922914 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7922915 {M N : Type'} : (term124 M N) = (term125 M N).
Proof. exact (MK_COMB (@lem7922914) (@lem7922913 M N)). Qed.
Lemma lem7922916 {M N : Type'} : (term105 M N) = (term126 M N).
Proof. exact (MK_COMB (@lem7922911 M N) (@lem7922915 M N)). Qed.
Lemma lem7922917 {M N : Type'} : ((term104 M N) = (term105 M N)) = ((term98 M N) = (term126 M N)).
Proof. exact (MK_COMB (@lem7922905 M N) (@lem7922916 M N)). Qed.
Lemma lem7922918 {M N : Type'} : (term98 M N) = (term126 M N).
Proof. exact (EQ_MP (@lem7922917 M N) (@lem7922895 M N)). Qed.
Lemma lem7923015 {M N : Type'} : (term78 M N) = (term78 M N).
Proof. exact (eq_refl (term78 M N)). Qed.
Lemma lem7923018 {M N : Type'} : (term99 M N) = (term127 M N).
Proof. exact (MK_COMB (@lem7923015 M N) (@lem7922918 M N)). Qed.
Lemma lem7923019 {M N : Type'} : (term42 M N) = (term127 M N).
Proof. exact (TRANS (@lem7922887 M N) (@lem7923018 M N)). Qed.
Lemma lem7923020 {M N : Type'} (h1 : term42 M N) : term127 M N.
Proof. exact (EQ_MP (@lem7923019 M N) (@lem7922137 M N h1)). Qed.
Lemma lem7923179 {M N : Type'} (x : nat) (h1 : term89 M N x) : term89 M N x.
Proof. exact (h1). Qed.
Lemma lem7923595 {M N : Type'} (r : nat) : (term113 M N r) = (term113 M N r).
Proof. exact (eq_refl (term113 M N r)). Qed.
Lemma lem7923596 {M N : Type'} : (term107 M N) = (term107 M N).
Proof. exact (fun_ext (fun r : nat => @lem7923595 M N r)). Qed.
Lemma lem7923597 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7923598 {M N : Type'} : (term125 M N) = (term125 M N).
Proof. exact (MK_COMB (@lem7923597) (@lem7923596 M N)). Qed.
Lemma lem7923633 {M N : Type'} (r : nat) : (term109 M N r) = (term109 M N r).
Proof. exact (eq_refl (term109 M N r)). Qed.
Lemma lem7923634 {M N : Type'} : (term106 M N) = (term106 M N).
Proof. exact (fun_ext (fun r : nat => @lem7923633 M N r)). Qed.
Lemma lem7923635 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7923636 {M N : Type'} : (term120 M N) = (term120 M N).
Proof. exact (MK_COMB (@lem7923635) (@lem7923634 M N)). Qed.
Lemma lem7923637 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7923638 {M N : Type'} : (term122 M N) = (term122 M N).
Proof. exact (MK_COMB (@lem7923637) (@lem7923636 M N)). Qed.
Lemma lem7923639 {M N : Type'} : (term126 M N) = (term126 M N).
Proof. exact (MK_COMB (@lem7923638 M N) (@lem7923598 M N)). Qed.
Lemma lem7923648 {M N : Type'} (a : finite_prod M N) : ((term75 M N a) = a) = ((term75 M N a) = a).
Proof. exact (eq_refl ((term75 M N a) = a)). Qed.
Lemma lem7923649 {M N : Type'} : (term76 M N) = (term76 M N).
Proof. exact (fun_ext (fun a : finite_prod M N => @lem7923648 M N a)). Qed.
Lemma lem7923650 {M N : Type'} : (@all (finite_prod M N)) = (@all (finite_prod M N)).
Proof. exact (eq_refl (@all (finite_prod M N))). Qed.
Lemma lem7923651 {M N : Type'} : (term77 M N) = (term77 M N).
Proof. exact (MK_COMB (@lem7923650 M N) (@lem7923649 M N)). Qed.
Lemma lem7923652 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7923653 {M N : Type'} : (term78 M N) = (term78 M N).
Proof. exact (MK_COMB (@lem7923652) (@lem7923651 M N)). Qed.
Lemma lem7923654 {M N : Type'} : (term127 M N) = (term127 M N).
Proof. exact (MK_COMB (@lem7923653 M N) (@lem7923639 M N)). Qed.
Lemma lem7923655 {M N : Type'} (h1 : term42 M N) : term127 M N.
Proof. exact (EQ_MP (@lem7923654 M N) (@lem7923020 M N h1)). Qed.
Lemma lem7923818 {M N : Type'} (x : nat) (y : nat) (h1 : term80 M N x y) : term80 M N x y.
Proof. exact (h1). Qed.
Lemma lem7923820 {M N : Type'} (x : nat) (y : nat) (h1 : term80 M N x y) : term27 M N x y.
Proof. exact (proj1 (@lem7923818 M N x y h1)). Qed.
Lemma lem7923821 {M N : Type'} (x : nat) (y : nat) (h1 : term80 M N x y) : term26 M N x y.
Proof. exact (proj2 (@lem7923820 M N x y h1)). Qed.
Lemma lem7923829 {M N : Type'} (h1 : term42 M N) : term126 M N.
Proof. exact (proj2 (@lem7923655 M N h1)). Qed.
Lemma lem7923831 {M N : Type'} (h1 : term42 M N) : term125 M N.
Proof. exact (proj2 (@lem7923829 M N h1)). Qed.
Lemma lem7923925 {M N : Type'} (r : nat) : (term113 M N r) = (term113 M N r).
Proof. exact (eq_refl (term113 M N r)). Qed.
Lemma lem7923926 {M N : Type'} : (term107 M N) = (term107 M N).
Proof. exact (fun_ext (fun r : nat => @lem7923925 M N r)). Qed.
Lemma lem7923927 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7923929 {M N : Type'} : (term125 M N) = (term125 M N).
Proof. exact (MK_COMB (@lem7923927) (@lem7923926 M N)). Qed.
Lemma lem7923930 {M N : Type'} (h1 : term42 M N) : term125 M N.
Proof. exact (EQ_MP (@lem7923929 M N) (@lem7923831 M N h1)). Qed.
Lemma lem7924078 {M N : Type'} (_103722 : nat) (h1 : term42 M N) : term112 M N _103722.
Proof. exact (@lem7923930 M N h1 _103722). Qed.
Lemma lem7924079 {M N : Type'} (_103722 : nat) : (term112 M N _103722) = (term113 M N _103722).
Proof. exact (eq_refl (term112 M N _103722)). Qed.
Lemma lem7924118 {M N : Type'} (x : nat) (y : nat) (h1 : term80 M N x y) : term128 x y.
Proof. exact (proj2 (@lem7923818 M N x y h1)). Qed.
Lemma lem7924152 {M N : Type'} (_103722 : nat) (h1 : term42 M N) : term113 M N _103722.
Proof. exact (EQ_MP (@lem7924079 M N _103722) (@lem7924078 M N _103722 h1)). Qed.
Lemma lem7924300 {M N : Type'} : (@dest_finite_prod M N) = (@dest_finite_prod M N).
Proof. exact (eq_refl (@dest_finite_prod M N)). Qed.
Lemma lem7924301 {M N : Type'} (_103757 : finite_prod M N) (_103758 : finite_prod M N) (h1 : _103757 = _103758) : _103757 = _103758.
Proof. exact (h1). Qed.
Lemma lem7924302 {M N : Type'} (_103757 : finite_prod M N) (_103758 : finite_prod M N) (h1 : _103757 = _103758) : (@dest_finite_prod M N _103757) = (@dest_finite_prod M N _103758).
Proof. exact (MK_COMB (@lem7924300 M N) (@lem7924301 M N _103757 _103758 h1)). Qed.
Lemma lem7924303 {M N : Type'} (_103757 : finite_prod M N) (_103758 : finite_prod M N) : term129 M N _103757 _103758.
Proof. exact (fun h0 : _103757 = _103758 => @lem7924302 M N _103757 _103758 h0). Qed.
Lemma lem7924305 (a : Prop) (b : Prop) : (a -> b) = (term130 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7924306 {M N : Type'} (_103757 : finite_prod M N) (_103758 : finite_prod M N) : (term129 M N _103757 _103758) = (term131 M N _103757 _103758).
Proof. exact (@lem7924305 (_103757 = _103758) ((@dest_finite_prod M N _103757) = (@dest_finite_prod M N _103758))). Qed.
Lemma lem7924307 {M N : Type'} (_103757 : finite_prod M N) (_103758 : finite_prod M N) : term131 M N _103757 _103758.
Proof. exact (EQ_MP (@lem7924306 M N _103757 _103758) (@lem7924303 M N _103757 _103758)). Qed.
Lemma lem7924405 (x : nat) (y : nat) (z : nat) : term132 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem7924427 {M N : Type'} (x : nat) (y : nat) (h1 : term80 M N x y) : (@mk_finite_prod M N x) = (@mk_finite_prod M N y).
Proof. exact (proj2 (@lem7923821 M N x y h1)). Qed.
Lemma lem7924428 {M N : Type'} (x : nat) (y : nat) (h1 : term80 M N x y) : term133 M N x y.
Proof. exact (fun h0 : term134 M N x y => @lem7924427 M N x y h1). Qed.
Lemma lem7924430 (p : Prop) : (term135 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7924431 {M N : Type'} (x : nat) (y : nat) : (term133 M N x y) = ((@mk_finite_prod M N x) = (@mk_finite_prod M N y)).
Proof. exact (@lem7924430 ((@mk_finite_prod M N x) = (@mk_finite_prod M N y))). Qed.
Lemma lem7924432 {M N : Type'} (x : nat) (y : nat) (h1 : term80 M N x y) : (@mk_finite_prod M N x) = (@mk_finite_prod M N y).
Proof. exact (EQ_MP (@lem7924431 M N x y) (@lem7924428 M N x y h1)). Qed.
Lemma lem7924438 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7924439 {M N : Type'} (_103757 : finite_prod M N) (_103758 : finite_prod M N) : (term131 M N _103757 _103758) = (term136 M N _103757 _103758).
Proof. exact (@lem7924438 ((@dest_finite_prod M N _103757) = (@dest_finite_prod M N _103758)) (term137 M N _103757 _103758)). Qed.
Lemma lem7924449 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7924450 {M N : Type'} (_103757 : finite_prod M N) (_103758 : finite_prod M N) : (term138 M N _103757 _103758) = (term139 M N _103757 _103758).
Proof. exact (MK_COMB (@lem7924449) (@lem7924439 M N _103757 _103758)). Qed.
Lemma lem7924460 {M N : Type'} (_103757 : finite_prod M N) (_103758 : finite_prod M N) : (term136 M N _103757 _103758) = (term136 M N _103757 _103758).
Proof. exact (eq_refl (term136 M N _103757 _103758)). Qed.
Lemma lem7924461 {M N : Type'} (_103757 : finite_prod M N) (_103758 : finite_prod M N) : ((term131 M N _103757 _103758) = (term136 M N _103757 _103758)) = ((term136 M N _103757 _103758) = (term136 M N _103757 _103758)).
Proof. exact (MK_COMB (@lem7924450 M N _103757 _103758) (@lem7924460 M N _103757 _103758)). Qed.
Lemma lem7924463 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7924464 (x : Prop) : (x = x) = True.
Proof. exact (@lem7924463 Prop x). Qed.
Lemma lem7924465 {M N : Type'} (_103757 : finite_prod M N) (_103758 : finite_prod M N) : ((term136 M N _103757 _103758) = (term136 M N _103757 _103758)) = True.
Proof. exact (@lem7924464 (term136 M N _103757 _103758)). Qed.
Lemma lem7924466 {M N : Type'} (_103757 : finite_prod M N) (_103758 : finite_prod M N) : ((term131 M N _103757 _103758) = (term136 M N _103757 _103758)) = True.
Proof. exact (TRANS (@lem7924461 M N _103757 _103758) (@lem7924465 M N _103757 _103758)). Qed.
Lemma lem7924467 {M N : Type'} (_103757 : finite_prod M N) (_103758 : finite_prod M N) : True = ((term131 M N _103757 _103758) = (term136 M N _103757 _103758)).
Proof. exact (SYM (@lem7924466 M N _103757 _103758)). Qed.
Lemma lem7924468 {M N : Type'} (_103757 : finite_prod M N) (_103758 : finite_prod M N) : (term131 M N _103757 _103758) = (term136 M N _103757 _103758).
Proof. exact (EQ_MP (@lem7924467 M N _103757 _103758) (@lem0)). Qed.
Lemma lem7924469 {M N : Type'} (_103757 : finite_prod M N) (_103758 : finite_prod M N) : term136 M N _103757 _103758.
Proof. exact (EQ_MP (@lem7924468 M N _103757 _103758) (@lem7924307 M N _103757 _103758)). Qed.
Lemma lem7924471 (b : Prop) (a : Prop) : (a \/ b) = (term140 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7924472 {M N : Type'} (_103757 : finite_prod M N) (_103758 : finite_prod M N) : (term136 M N _103757 _103758) = (term141 M N _103757 _103758).
Proof. exact (@lem7924471 (term137 M N _103757 _103758) ((@dest_finite_prod M N _103757) = (@dest_finite_prod M N _103758))). Qed.
Lemma lem7924474 (a : Prop) : (term142 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7924475 {M N : Type'} (_103757 : finite_prod M N) (_103758 : finite_prod M N) : (term143 M N _103757 _103758) = (_103757 = _103758).
Proof. exact (@lem7924474 (_103757 = _103758)). Qed.
Lemma lem7924476 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7924477 {M N : Type'} (_103757 : finite_prod M N) (_103758 : finite_prod M N) : (term144 M N _103757 _103758) = (term145 M N _103757 _103758).
Proof. exact (MK_COMB (@lem7924476) (@lem7924475 M N _103757 _103758)). Qed.
Lemma lem7924478 {M N : Type'} (_103757 : finite_prod M N) (_103758 : finite_prod M N) : ((@dest_finite_prod M N _103757) = (@dest_finite_prod M N _103758)) = ((@dest_finite_prod M N _103757) = (@dest_finite_prod M N _103758)).
Proof. exact (eq_refl ((@dest_finite_prod M N _103757) = (@dest_finite_prod M N _103758))). Qed.
Lemma lem7924479 {M N : Type'} (_103757 : finite_prod M N) (_103758 : finite_prod M N) : (term141 M N _103757 _103758) = (term129 M N _103757 _103758).
Proof. exact (MK_COMB (@lem7924477 M N _103757 _103758) (@lem7924478 M N _103757 _103758)). Qed.
Lemma lem7924480 {M N : Type'} (_103757 : finite_prod M N) (_103758 : finite_prod M N) : (term136 M N _103757 _103758) = (term129 M N _103757 _103758).
Proof. exact (TRANS (@lem7924472 M N _103757 _103758) (@lem7924479 M N _103757 _103758)). Qed.
Lemma lem7924483 {M N : Type'} (_103757 : finite_prod M N) (_103758 : finite_prod M N) : term129 M N _103757 _103758.
Proof. exact (EQ_MP (@lem7924480 M N _103757 _103758) (@lem7924469 M N _103757 _103758)). Qed.
Lemma lem7924484 {M N : Type'} (_103757 : finite_prod M N) (_103758 : finite_prod M N) : term129 M N _103757 _103758.
Proof. exact (@lem7924483 M N _103757 _103758). Qed.
Lemma lem7924485 {M N : Type'} (x : nat) (y : nat) : term146 M N x y.
Proof. exact (@lem7924484 M N (@mk_finite_prod M N x) (@mk_finite_prod M N y)). Qed.
Lemma lem7924488 {M N : Type'} (x : nat) (y : nat) (h1 : term80 M N x y) : (term72 M N x) = (term72 M N y).
Proof. exact (@lem7924485 M N x y (@lem7924432 M N x y h1)). Qed.
Lemma lem7924489 {M N : Type'} (x : nat) (y : nat) (h1 : term80 M N x y) : term147 M N x y.
Proof. exact (fun h0 : term148 M N x y => @lem7924488 M N x y h1). Qed.
Lemma lem7924491 (p : Prop) : (term135 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7924492 {M N : Type'} (x : nat) (y : nat) : (term147 M N x y) = ((term72 M N x) = (term72 M N y)).
Proof. exact (@lem7924491 ((term72 M N x) = (term72 M N y))). Qed.
Lemma lem7924493 {M N : Type'} (x : nat) (y : nat) (h1 : term80 M N x y) : (term72 M N x) = (term72 M N y).
Proof. exact (EQ_MP (@lem7924492 M N x y) (@lem7924489 M N x y h1)). Qed.
Lemma lem7924495 {M N : Type'} (x : nat) (y : nat) (h1 : term80 M N x y) : term24 M N x.
Proof. exact (proj1 (@lem7923820 M N x y h1)). Qed.
Lemma lem7924496 {M N : Type'} (x : nat) (y : nat) (h1 : term80 M N x y) : term149 M N x.
Proof. exact (fun h0 : term150 M N x => @lem7924495 M N x y h1). Qed.
Lemma lem7924498 (p : Prop) : (term135 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7924499 {M N : Type'} (x : nat) : (term149 M N x) = (term24 M N x).
Proof. exact (@lem7924498 (term24 M N x)). Qed.
Lemma lem7924500 {M N : Type'} (x : nat) (y : nat) (h1 : term80 M N x y) : term24 M N x.
Proof. exact (EQ_MP (@lem7924499 M N x) (@lem7924496 M N x y h1)). Qed.
Lemma lem7924506 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7924507 {M N : Type'} (_103722 : nat) : (term113 M N _103722) = (term151 M N _103722).
Proof. exact (@lem7924506 ((term72 M N _103722) = _103722) (term150 M N _103722)). Qed.
Lemma lem7924515 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7924516 {M N : Type'} (_103722 : nat) : (term152 M N _103722) = (term153 M N _103722).
Proof. exact (MK_COMB (@lem7924515) (@lem7924507 M N _103722)). Qed.
Lemma lem7924524 {M N : Type'} (_103722 : nat) : (term151 M N _103722) = (term151 M N _103722).
Proof. exact (eq_refl (term151 M N _103722)). Qed.
Lemma lem7924525 {M N : Type'} (_103722 : nat) : ((term113 M N _103722) = (term151 M N _103722)) = ((term151 M N _103722) = (term151 M N _103722)).
Proof. exact (MK_COMB (@lem7924516 M N _103722) (@lem7924524 M N _103722)). Qed.
Lemma lem7924527 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7924528 (x : Prop) : (x = x) = True.
Proof. exact (@lem7924527 Prop x). Qed.
Lemma lem7924529 {M N : Type'} (_103722 : nat) : ((term151 M N _103722) = (term151 M N _103722)) = True.
Proof. exact (@lem7924528 (term151 M N _103722)). Qed.
Lemma lem7924530 {M N : Type'} (_103722 : nat) : ((term113 M N _103722) = (term151 M N _103722)) = True.
Proof. exact (TRANS (@lem7924525 M N _103722) (@lem7924529 M N _103722)). Qed.
Lemma lem7924531 {M N : Type'} (_103722 : nat) : True = ((term113 M N _103722) = (term151 M N _103722)).
Proof. exact (SYM (@lem7924530 M N _103722)). Qed.
Lemma lem7924532 {M N : Type'} (_103722 : nat) : (term113 M N _103722) = (term151 M N _103722).
Proof. exact (EQ_MP (@lem7924531 M N _103722) (@lem0)). Qed.
Lemma lem7924533 {M N : Type'} (_103722 : nat) (h1 : term42 M N) : term151 M N _103722.
Proof. exact (EQ_MP (@lem7924532 M N _103722) (@lem7924152 M N _103722 h1)). Qed.
Lemma lem7924535 (b : Prop) (a : Prop) : (a \/ b) = (term140 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7924536 {M N : Type'} (_103722 : nat) : (term151 M N _103722) = (term154 M N _103722).
Proof. exact (@lem7924535 (term150 M N _103722) ((term72 M N _103722) = _103722)). Qed.
Lemma lem7924538 (a : Prop) : (term142 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7924539 {M N : Type'} (_103722 : nat) : (term155 M N _103722) = (term24 M N _103722).
Proof. exact (@lem7924538 (term24 M N _103722)). Qed.
Lemma lem7924540 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7924541 {M N : Type'} (_103722 : nat) : (term156 M N _103722) = (term157 M N _103722).
Proof. exact (MK_COMB (@lem7924540) (@lem7924539 M N _103722)). Qed.
Lemma lem7924542 {M N : Type'} (_103722 : nat) : ((term72 M N _103722) = _103722) = ((term72 M N _103722) = _103722).
Proof. exact (eq_refl ((term72 M N _103722) = _103722)). Qed.
Lemma lem7924543 {M N : Type'} (_103722 : nat) : (term154 M N _103722) = (term158 M N _103722).
Proof. exact (MK_COMB (@lem7924541 M N _103722) (@lem7924542 M N _103722)). Qed.
Lemma lem7924544 {M N : Type'} (_103722 : nat) : (term151 M N _103722) = (term158 M N _103722).
Proof. exact (TRANS (@lem7924536 M N _103722) (@lem7924543 M N _103722)). Qed.
Lemma lem7924547 {M N : Type'} (_103722 : nat) (h1 : term42 M N) : term158 M N _103722.
Proof. exact (EQ_MP (@lem7924544 M N _103722) (@lem7924533 M N _103722 h1)). Qed.
Lemma lem7924548 {M N : Type'} (x : nat) (h1 : term42 M N) : term158 M N x.
Proof. exact (@lem7924547 M N x h1). Qed.
Lemma lem7924551 {M N : Type'} (x : nat) (y : nat) (h1 : term42 M N) (h2 : term80 M N x y) : (term72 M N x) = x.
Proof. exact (@lem7924548 M N x h1 (@lem7924500 M N x y h2)). Qed.
Lemma lem7924552 {M N : Type'} (x : nat) (y : nat) (h1 : term42 M N) (h2 : term80 M N x y) : term159 M N x.
Proof. exact (fun h0 : term160 M N x => @lem7924551 M N x y h1 h2). Qed.
Lemma lem7924554 (p : Prop) : (term135 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7924555 {M N : Type'} (x : nat) : (term159 M N x) = ((term72 M N x) = x).
Proof. exact (@lem7924554 ((term72 M N x) = x)). Qed.
Lemma lem7924556 {M N : Type'} (x : nat) (y : nat) (h1 : term42 M N) (h2 : term80 M N x y) : (term72 M N x) = x.
Proof. exact (EQ_MP (@lem7924555 M N x) (@lem7924552 M N x y h1 h2)). Qed.
Lemma lem7924574 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7924575 (y : nat) (x : nat) (z : nat) : (term161 x y z) = (term162 y x z).
Proof. exact (@lem7924574 (y = z) (term128 x z)). Qed.
Lemma lem7924585 (x : nat) (y : nat) : (term163 x y) = (term163 x y).
Proof. exact (eq_refl (term163 x y)). Qed.
Lemma lem7924586 (y : nat) (x : nat) (z : nat) : (term132 x y z) = (term164 y x z).
Proof. exact (MK_COMB (@lem7924585 x y) (@lem7924575 y x z)). Qed.
Lemma lem7924590 (q : Prop) (p : Prop) (r : Prop) : (term165 p q r) = (term165 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7924591 (y : nat) (x : nat) (z : nat) : (term164 y x z) = (term166 y x z).
Proof. exact (@lem7924590 (y = z) (term128 x y) (term128 x z)). Qed.
Lemma lem7924613 (y : nat) (x : nat) (z : nat) : (term132 x y z) = (term166 y x z).
Proof. exact (TRANS (@lem7924586 y x z) (@lem7924591 y x z)). Qed.
Lemma lem7924614 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7924615 (y : nat) (x : nat) (z : nat) : (term167 x y z) = (term168 y x z).
Proof. exact (MK_COMB (@lem7924614) (@lem7924613 y x z)). Qed.
Lemma lem7924637 (y : nat) (x : nat) (z : nat) : (term166 y x z) = (term166 y x z).
Proof. exact (eq_refl (term166 y x z)). Qed.
Lemma lem7924638 (y : nat) (x : nat) (z : nat) : ((term132 x y z) = (term166 y x z)) = ((term166 y x z) = (term166 y x z)).
Proof. exact (MK_COMB (@lem7924615 y x z) (@lem7924637 y x z)). Qed.
Lemma lem7924640 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7924641 (x : Prop) : (x = x) = True.
Proof. exact (@lem7924640 Prop x). Qed.
Lemma lem7924642 (y : nat) (x : nat) (z : nat) : ((term166 y x z) = (term166 y x z)) = True.
Proof. exact (@lem7924641 (term166 y x z)). Qed.
Lemma lem7924643 (y : nat) (x : nat) (z : nat) : ((term132 x y z) = (term166 y x z)) = True.
Proof. exact (TRANS (@lem7924638 y x z) (@lem7924642 y x z)). Qed.
Lemma lem7924644 (y : nat) (x : nat) (z : nat) : True = ((term132 x y z) = (term166 y x z)).
Proof. exact (SYM (@lem7924643 y x z)). Qed.
Lemma lem7924645 (y : nat) (x : nat) (z : nat) : (term132 x y z) = (term166 y x z).
Proof. exact (EQ_MP (@lem7924644 y x z) (@lem0)). Qed.
Lemma lem7924646 (y : nat) (x : nat) (z : nat) : term166 y x z.
Proof. exact (EQ_MP (@lem7924645 y x z) (@lem7924405 x y z)). Qed.
Lemma lem7924648 (b : Prop) (a : Prop) : (a \/ b) = (term140 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7924649 (x : nat) (y : nat) (z : nat) : (term166 y x z) = (term169 x y z).
Proof. exact (@lem7924648 (term170 y x z) (y = z)). Qed.
Lemma lem7924651 (a : Prop) (b : Prop) : (term171 a b) = (term172 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7924652 (y : nat) (x : nat) (z : nat) : (term173 y x z) = (term174 y x z).
Proof. exact (@lem7924651 (term128 x y) (term128 x z)). Qed.
Lemma lem7924654 (a : Prop) : (term142 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7924655 (x : nat) (y : nat) : (term175 x y) = (x = y).
Proof. exact (@lem7924654 (x = y)). Qed.
Lemma lem7924656 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7924657 (x : nat) (y : nat) : (term176 x y) = (term177 x y).
Proof. exact (MK_COMB (@lem7924656) (@lem7924655 x y)). Qed.
Lemma lem7924659 (a : Prop) : (term142 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7924660 (x : nat) (z : nat) : (term175 x z) = (x = z).
Proof. exact (@lem7924659 (x = z)). Qed.
Lemma lem7924661 (y : nat) (x : nat) (z : nat) : (term174 y x z) = (term178 y x z).
Proof. exact (MK_COMB (@lem7924657 x y) (@lem7924660 x z)). Qed.
Lemma lem7924662 (y : nat) (x : nat) (z : nat) : (term173 y x z) = (term178 y x z).
Proof. exact (TRANS (@lem7924652 y x z) (@lem7924661 y x z)). Qed.
Lemma lem7924663 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7924664 (y : nat) (x : nat) (z : nat) : (term179 y x z) = (term180 y x z).
Proof. exact (MK_COMB (@lem7924663) (@lem7924662 y x z)). Qed.
Lemma lem7924665 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem7924666 (x : nat) (y : nat) (z : nat) : (term169 x y z) = (term181 x y z).
Proof. exact (MK_COMB (@lem7924664 y x z) (@lem7924665 y z)). Qed.
Lemma lem7924667 (x : nat) (y : nat) (z : nat) : (term166 y x z) = (term181 x y z).
Proof. exact (TRANS (@lem7924649 x y z) (@lem7924666 x y z)). Qed.
Lemma lem7924669 {M N : Type'} (x : nat) (y : nat) (h1 : term42 M N) (h2 : term80 M N x y) : term182 M N y x.
Proof. exact (conj (@lem7924493 M N x y h2) (@lem7924556 M N x y h1 h2)). Qed.
Lemma lem7924671 (x : nat) (y : nat) (z : nat) : term181 x y z.
Proof. exact (EQ_MP (@lem7924667 x y z) (@lem7924646 y x z)). Qed.
Lemma lem7924672 {M N : Type'} (y : nat) (x : nat) : term183 M N y x.
Proof. exact (@lem7924671 (term72 M N x) (term72 M N y) x). Qed.
Lemma lem7924675 {M N : Type'} (x : nat) (y : nat) (h1 : term42 M N) (h2 : term80 M N x y) : (term72 M N y) = x.
Proof. exact (@lem7924672 M N y x (@lem7924669 M N x y h1 h2)). Qed.
Lemma lem7924676 {M N : Type'} (x : nat) (y : nat) (h1 : term42 M N) (h2 : term80 M N x y) : term184 M N y x.
Proof. exact (fun h0 : term185 M N y x => @lem7924675 M N x y h1 h2). Qed.
Lemma lem7924678 (p : Prop) : (term135 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7924679 {M N : Type'} (y : nat) (x : nat) : (term184 M N y x) = ((term72 M N y) = x).
Proof. exact (@lem7924678 ((term72 M N y) = x)). Qed.
Lemma lem7924680 {M N : Type'} (x : nat) (y : nat) (h1 : term42 M N) (h2 : term80 M N x y) : (term72 M N y) = x.
Proof. exact (EQ_MP (@lem7924679 M N y x) (@lem7924676 M N x y h1 h2)). Qed.
Lemma lem7924682 {M N : Type'} (x : nat) (y : nat) (h1 : term80 M N x y) : term24 M N y.
Proof. exact (proj1 (@lem7923821 M N x y h1)). Qed.
Lemma lem7924683 {M N : Type'} (x : nat) (y : nat) (h1 : term80 M N x y) : term149 M N y.
Proof. exact (fun h0 : term150 M N y => @lem7924682 M N x y h1). Qed.
Lemma lem7924685 (p : Prop) : (term135 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7924686 {M N : Type'} (y : nat) : (term149 M N y) = (term24 M N y).
Proof. exact (@lem7924685 (term24 M N y)). Qed.
Lemma lem7924687 {M N : Type'} (x : nat) (y : nat) (h1 : term80 M N x y) : term24 M N y.
Proof. exact (EQ_MP (@lem7924686 M N y) (@lem7924683 M N x y h1)). Qed.
Lemma lem7924689 {M N : Type'} (_103722 : nat) (h1 : term42 M N) : term158 M N _103722.
Proof. exact (EQ_MP (@lem7924544 M N _103722) (@lem7924533 M N _103722 h1)). Qed.
Lemma lem7924690 {M N : Type'} (y : nat) (h1 : term42 M N) : term158 M N y.
Proof. exact (@lem7924689 M N y h1). Qed.
Lemma lem7924693 {M N : Type'} (x : nat) (y : nat) (h1 : term42 M N) (h2 : term80 M N x y) : (term72 M N y) = y.
Proof. exact (@lem7924690 M N y h1 (@lem7924687 M N x y h2)). Qed.
Lemma lem7924694 {M N : Type'} (x : nat) (y : nat) (h1 : term42 M N) (h2 : term80 M N x y) : term159 M N y.
Proof. exact (fun h0 : term160 M N y => @lem7924693 M N x y h1 h2). Qed.
Lemma lem7924696 (p : Prop) : (term135 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7924697 {M N : Type'} (y : nat) : (term159 M N y) = ((term72 M N y) = y).
Proof. exact (@lem7924696 ((term72 M N y) = y)). Qed.
Lemma lem7924698 {M N : Type'} (x : nat) (y : nat) (h1 : term42 M N) (h2 : term80 M N x y) : (term72 M N y) = y.
Proof. exact (EQ_MP (@lem7924697 M N y) (@lem7924694 M N x y h1 h2)). Qed.
Lemma lem7924699 {M N : Type'} (x : nat) (y : nat) (h1 : term42 M N) (h2 : term80 M N x y) : term186 M N x y.
Proof. exact (conj (@lem7924680 M N x y h1 h2) (@lem7924698 M N x y h1 h2)). Qed.
Lemma lem7924701 (x : nat) (y : nat) (z : nat) : term181 x y z.
Proof. exact (EQ_MP (@lem7924667 x y z) (@lem7924646 y x z)). Qed.
Lemma lem7924702 {M N : Type'} (x : nat) (y : nat) : term187 M N x y.
Proof. exact (@lem7924701 (term72 M N y) x y). Qed.
Lemma lem7924705 {M N : Type'} (x : nat) (y : nat) (h1 : term42 M N) (h2 : term80 M N x y) : x = y.
Proof. exact (@lem7924702 M N x y (@lem7924699 M N x y h1 h2)). Qed.
Lemma lem7924706 {M N : Type'} (x : nat) (y : nat) (h1 : term42 M N) (h2 : term80 M N x y) : term188 x y.
Proof. exact (fun h0 : term128 x y => @lem7924705 M N x y h1 h2). Qed.
Lemma lem7924708 (p : Prop) : (term135 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7924709 (x : nat) (y : nat) : (term188 x y) = (x = y).
Proof. exact (@lem7924708 (x = y)). Qed.
Lemma lem7924710 {M N : Type'} (x : nat) (y : nat) (h1 : term42 M N) (h2 : term80 M N x y) : x = y.
Proof. exact (EQ_MP (@lem7924709 x y) (@lem7924706 M N x y h1 h2)). Qed.
Lemma lem7924713 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7924715 (x : nat) (y : nat) : (term128 x y) = (term189 x y).
Proof. exact (@lem7924713 (x = y)). Qed.
Lemma lem7924718 {M N : Type'} (x : nat) (y : nat) (h1 : term80 M N x y) : term189 x y.
Proof. exact (EQ_MP (@lem7924715 x y) (@lem7924118 M N x y h1)). Qed.
Lemma lem7924721 {M N : Type'} (x : nat) (y : nat) (h1 : term42 M N) (h2 : term80 M N x y) : False.
Proof. exact (@lem7924718 M N x y h2 (@lem7924710 M N x y h1 h2)). Qed.
Lemma lem7924722 {M N : Type'} (x : nat) (y : nat) (h1 : term42 M N) (h2 : term80 M N x y) : term190.
Proof. exact (fun h0 : ~ False => @lem7924721 M N x y h1 h2). Qed.
Lemma lem7924724 (p : Prop) : (term135 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7924725 : term190 = False.
Proof. exact (@lem7924724 False). Qed.
Lemma lem7924726 {M N : Type'} (x : nat) (y : nat) (h1 : term42 M N) (h2 : term80 M N x y) : False.
Proof. exact (EQ_MP (@lem7924725) (@lem7924722 M N x y h1 h2)). Qed.
Lemma lem7924727 {M N : Type'} (x : nat) (y : nat) (h1 : term42 M N) (h2 : term80 M N x y) : (term80 M N x y) = False.
Proof. exact (prop_ext (fun h3 : term80 M N x y => @lem7924726 M N x y h1 h2) (fun h3 : False => @lem7923818 M N x y h2)). Qed.
Lemma lem7924728 {M N : Type'} (x : nat) (y : nat) (h1 : term42 M N) (h2 : term80 M N x y) : False.
Proof. exact (EQ_MP (@lem7924727 M N x y h1 h2) (@lem7923818 M N x y h2)). Qed.
Lemma lem7924729 {M N : Type'} (x : nat) (h1 : term89 M N x) (h2 : term42 M N) : False.
Proof. exact (ex_elim (@lem7923179 M N x h1) (fun y : nat => fun h0 : term88 M N x y => @lem7924728 M N x y h2 h0)). Qed.
Lemma lem7924730 {M N : Type'} (h1 : term41 M N) (h2 : term42 M N) : False.
Proof. exact (ex_elim (@lem7922230 M N h1) (fun x : nat => fun h0 : term94 M N x => @lem7924729 M N x h0 h2)). Qed.
Lemma lem7924731 {B M N : Type'} (h1 : term41 M N) (h2 : term42 M N) : term48 B N.
Proof. exact (fun h0 : term43 B N => @lem7924730 M N h1 h2). Qed.
Lemma lem7924732 {B N : Type'} : (term48 B N) = (term49 B N).
Proof. exact (@lem69 (term43 B N)). Qed.
Lemma lem7924733 {B M N : Type'} (h1 : term41 M N) (h2 : term42 M N) : term49 B N.
Proof. exact (EQ_MP (@lem7924732 B N) (@lem7924731 B M N h1 h2)). Qed.
Lemma lem7924734 {B M N : Type'} (h1 : term41 M N) : term52 B M N.
Proof. exact (fun h0 : term42 M N => @lem7924733 B M N h1 h0). Qed.
Lemma lem7924735 {B M N : Type'} (h1 : term41 M N) : term55 B M N.
Proof. exact (fun h0 : term43 B M => @lem7924734 B M N h1). Qed.
Lemma lem7924736 {A B M N : Type'} (h1 : term41 M N) : term57 A B M N.
Proof. exact (fun h0 : term42 A N => @lem7924735 B M N h1). Qed.
Lemma lem7924737 {A B M N : Type'} (h1 : term41 M N) : term59 A B M N.
Proof. exact (fun h0 : term42 A M => @lem7924736 A B M N h1). Qed.
Lemma lem7924738 {A B M N : Type'} (h1 : term41 M N) : term61 A B M N.
Proof. exact (fun h0 : term42 A B => @lem7924737 A B M N h1). Qed.
Lemma lem7924739 {A B M N : Type'} : term63 A B M N.
Proof. exact (fun h0 : term41 M N => @lem7924738 A B M N h0). Qed.
Lemma lem7924740 {A B M N : Type'} : term44 A B M N.
Proof. exact (EQ_MP (@lem7922131 A B M N) (@lem7924739 A B M N)). Qed.
Lemma lem7924742 {A B M N : Type'} : term44 A B M N.
Proof. exact (@lem7921765 A B M N (@lem7924740 A B M N)). Qed.
Lemma lem7924743 {A B M N : Type'} (h1 : term41 M N) : term60 A B M N.
Proof. exact (@lem7924742 A B M N (@lem7921739 M N h1)). Qed.
Lemma lem7924744 {A B M N : Type'} (h1 : term41 M N) : term58 A B M N.
Proof. exact (@lem7924743 A B M N h1 (@lem7919632 A B)). Qed.
Lemma lem7924745 {A B M N : Type'} (h1 : term41 M N) : term56 A B M N.
Proof. exact (@lem7924744 A B M N h1 (@lem7921746 A M)). Qed.
Lemma lem7924746 {B M N : Type'} (h1 : term41 M N) : term54 B M N.
Proof. exact (@lem7924745 Prop B M N h1 (@lem7921747 Prop N)). Qed.
Lemma lem7924747 {B M N : Type'} (h1 : term41 M N) : term51 B M N.
Proof. exact (@lem7924746 B M N h1 (@lem7921742 B M)). Qed.
Lemma lem7924748 {B M N : Type'} (h1 : term41 M N) : term48 B N.
Proof. exact (@lem7924747 B M N h1 (@lem7921740 M N)). Qed.
Lemma lem7924749 {M N : Type'} (h1 : term41 M N) : False.
Proof. exact (@lem7924748 Prop M N h1 (@lem7921743 Prop N)). Qed.
Lemma lem7924750 {M N : Type'} (h1 : term41 M N) : (term41 M N) = False.
Proof. exact (prop_ext (fun h2 : term41 M N => @lem7924749 M N h1) (fun h2 : False => @lem7921739 M N h1)). Qed.
Lemma lem7924751 {M N : Type'} (h1 : term41 M N) : False.
Proof. exact (EQ_MP (@lem7924750 M N h1) (@lem7921739 M N h1)). Qed.
Lemma lem7924752 {M N : Type'} : term40 M N.
Proof. exact (fun h0 : term41 M N => @lem7924751 M N h0). Qed.
Lemma lem7924753 {M N : Type'} : term33 M N.
Proof. exact (EQ_MP (@lem7921738 M N) (@lem7924752 M N)). Qed.
Lemma lem7924754 {M N : Type'} : term37 M N.
Proof. exact (EQ_MP (@lem7921734 M N) (@lem7924753 M N)). Qed.
Lemma lem7924755 {M N : Type'} : term37 M N.
Proof. exact (EQ_MP (@lem7921686 M N) (@lem7924754 M N)). Qed.
Lemma lem7924756 {M N : Type'} : term18 M N.
Proof. exact (@lem7921588 M N (@lem7924755 M N)). Qed.
Lemma lem7924757 {M N : Type'} : term17 M N.
Proof. exact (EQ_MP (@lem7921584 M N) (@lem7924756 M N)). Qed.
