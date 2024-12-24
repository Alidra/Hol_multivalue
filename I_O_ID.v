Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import I_O_ID_term_abbrevs.
Require Import FUN_EQ_THM_spec.
Require Import I_THM_spec.
Require Import o_DEF_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem15585 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem15584 A x). Qed.
Lemma lem15586 {A : Type'} (x : A) : (term0 A x) = ((@I A x) = x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem15588 {A B C : Type'} (f : B -> C) : term1 A B C f.
Proof. exact (@lem15397 A B C f). Qed.
Lemma lem15589 {A B C : Type'} (f : B -> C) : (term1 A B C f) = (term2 A B C f).
Proof. exact (eq_refl (term1 A B C f)). Qed.
Lemma lem15590 {A B C : Type'} (f : B -> C) : term2 A B C f.
Proof. exact (EQ_MP (@lem15589 A B C f) (@lem15588 A B C f)). Qed.
Lemma lem15591 {A B C : Type'} (f : B -> C) (g : A -> B) : term3 A B C f g.
Proof. exact (@lem15590 A B C f g). Qed.
Lemma lem15592 {A B C : Type'} (f : B -> C) (g : A -> B) : (term3 A B C f g) = ((@o A B C f g) = (term4 A B C f g)).
Proof. exact (eq_refl (term3 A B C f g)). Qed.
Lemma lem15594 {A B : Type'} (f : A -> B) : term5 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem15595 {A B : Type'} (f : A -> B) : (term5 A B f) = (term6 A B f).
Proof. exact (eq_refl (term5 A B f)). Qed.
Lemma lem15596 {A B : Type'} (f : A -> B) : term6 A B f.
Proof. exact (EQ_MP (@lem15595 A B f) (@lem15594 A B f)). Qed.
Lemma lem15597 {A B : Type'} (f : A -> B) (g : A -> B) : term7 A B f g.
Proof. exact (@lem15596 A B f g). Qed.
Lemma lem15598 {A B : Type'} (f : A -> B) (g : A -> B) : (term7 A B f g) = ((f = g) = (term8 A B f g)).
Proof. exact (eq_refl (term7 A B f g)). Qed.
Lemma lem15603 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term8 A B f g).
Proof. exact (EQ_MP (@lem15598 A B f g) (@lem15597 A B f g)). Qed.
Lemma lem15604 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term8 A B f g).
Proof. exact (@lem15603 A B f g). Qed.
Lemma lem15605 {A B : Type'} (f : A -> B) : ((@o A B B (@I B) f) = f) = (term9 A B f).
Proof. exact (@lem15604 A B (@o A B B (@I B) f) f). Qed.
Lemma lem15615 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term4 A B C f g).
Proof. exact (EQ_MP (@lem15592 A B C f g) (@lem15591 A B C f g)). Qed.
Lemma lem15616 {A B : Type'} (f : B -> B) (g : A -> B) : (@o A B B f g) = (term10 A B f g).
Proof. exact (@lem15615 A B B f g). Qed.
Lemma lem15617 {A B : Type'} (f : A -> B) : (@o A B B (@I B) f) = (term11 A B f).
Proof. exact (@lem15616 A B (@I B) f). Qed.
Lemma lem15619 {A : Type'} (x : A) : (@I A x) = x.
Proof. exact (EQ_MP (@lem15586 A x) (@lem15585 A x)). Qed.
Lemma lem15620 {B : Type'} (x : B) : (@I B x) = x.
Proof. exact (@lem15619 B x). Qed.
Lemma lem15621 {A B : Type'} (f : A -> B) (x : A) : (term12 A B f x) = (f x).
Proof. exact (@lem15620 B (f x)). Qed.
Lemma lem15622 {A B : Type'} (f : A -> B) : (term11 A B f) = (term13 A B f).
Proof. exact (fun_ext (fun x : A => @lem15621 A B f x)). Qed.
Lemma lem15623 {A B : Type'} (f : A -> B) : (@o A B B (@I B) f) = (term13 A B f).
Proof. exact (TRANS (@lem15617 A B f) (@lem15622 A B f)). Qed.
Lemma lem15624 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem15625 {A B : Type'} (f : A -> B) (x : A) : (@o A B B (@I B) f x) = (term14 A B f x).
Proof. exact (MK_COMB (@lem15623 A B f) (@lem15624 A x)). Qed.
Lemma lem15627 {A B : Type'} (f : A -> B) (y : A) : (term14 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem15628 {A B : Type'} (f : A -> B) (y : A) : (term14 A B f y) = (f y).
Proof. exact (@lem15627 A B f y). Qed.
Lemma lem15629 {A B : Type'} (f : A -> B) (x : A) : (term14 A B f x) = (f x).
Proof. exact (@lem15628 A B f x). Qed.
Lemma lem15630 {A B : Type'} (f : A -> B) (x : A) : (@o A B B (@I B) f x) = (f x).
Proof. exact (TRANS (@lem15625 A B f x) (@lem15629 A B f x)). Qed.
Lemma lem15631 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem15632 {A B : Type'} (f : A -> B) (x : A) : (term15 A B f x) = (term16 A B f x).
Proof. exact (MK_COMB (@lem15631 B) (@lem15630 A B f x)). Qed.
Lemma lem15633 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem15634 {A B : Type'} (f : A -> B) (x : A) : ((@o A B B (@I B) f x) = (f x)) = ((f x) = (f x)).
Proof. exact (MK_COMB (@lem15632 A B f x) (@lem15633 A B f x)). Qed.
Lemma lem15636 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem15637 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem15636 B x). Qed.
Lemma lem15638 {A B : Type'} (f : A -> B) (x : A) : ((f x) = (f x)) = True.
Proof. exact (@lem15637 B (f x)). Qed.
Lemma lem15639 {A B : Type'} (f : A -> B) (x : A) : ((@o A B B (@I B) f x) = (f x)) = True.
Proof. exact (TRANS (@lem15634 A B f x) (@lem15638 A B f x)). Qed.
Lemma lem15640 {A B : Type'} (f : A -> B) : (term17 A B f) = (term18 A).
Proof. exact (fun_ext (fun x : A => @lem15639 A B f x)). Qed.
Lemma lem15641 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem15642 {A B : Type'} (f : A -> B) : (term9 A B f) = (term19 A).
Proof. exact (MK_COMB (@lem15641 A) (@lem15640 A B f)). Qed.
Lemma lem15644 {A : Type'} (t : Prop) : (term20 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem15645 {A : Type'} (t : Prop) : (term20 A t) = t.
Proof. exact (@lem15644 A t). Qed.
Lemma lem15646 {A : Type'} : (term19 A) = True.
Proof. exact (@lem15645 A True). Qed.
Lemma lem15647 {A B : Type'} (f : A -> B) : (term9 A B f) = True.
Proof. exact (TRANS (@lem15642 A B f) (@lem15646 A)). Qed.
Lemma lem15648 {A B : Type'} (f : A -> B) : ((@o A B B (@I B) f) = f) = True.
Proof. exact (TRANS (@lem15605 A B f) (@lem15647 A B f)). Qed.
Lemma lem15649 {A B : Type'} (f : A -> B) : True = ((@o A B B (@I B) f) = f).
Proof. exact (SYM (@lem15648 A B f)). Qed.
Lemma lem15650 {A B : Type'} (f : A -> B) : (@o A B B (@I B) f) = f.
Proof. exact (EQ_MP (@lem15649 A B f) (@lem0)). Qed.
Lemma lem15654 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term8 A B f g).
Proof. exact (EQ_MP (@lem15598 A B f g) (@lem15597 A B f g)). Qed.
Lemma lem15655 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term8 A B f g).
Proof. exact (@lem15654 A B f g). Qed.
Lemma lem15656 {A B : Type'} (f : A -> B) : ((@o A A B f (@I A)) = f) = (term21 A B f).
Proof. exact (@lem15655 A B (@o A A B f (@I A)) f). Qed.
Lemma lem15666 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term4 A B C f g).
Proof. exact (EQ_MP (@lem15592 A B C f g) (@lem15591 A B C f g)). Qed.
Lemma lem15667 {A B : Type'} (f : A -> B) (g : A -> A) : (@o A A B f g) = (term22 A B f g).
Proof. exact (@lem15666 A A B f g). Qed.
Lemma lem15668 {A B : Type'} (f : A -> B) : (@o A A B f (@I A)) = (term23 A B f).
Proof. exact (@lem15667 A B f (@I A)). Qed.
Lemma lem15670 {A : Type'} (x : A) : (@I A x) = x.
Proof. exact (EQ_MP (@lem15586 A x) (@lem15585 A x)). Qed.
Lemma lem15671 {A : Type'} (x : A) : (@I A x) = x.
Proof. exact (@lem15670 A x). Qed.
Lemma lem15672 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem15673 {A B : Type'} (f : A -> B) (x : A) : (term24 A B f x) = (f x).
Proof. exact (MK_COMB (@lem15672 A B f) (@lem15671 A x)). Qed.
Lemma lem15674 {A B : Type'} (f : A -> B) : (term23 A B f) = (term13 A B f).
Proof. exact (fun_ext (fun x : A => @lem15673 A B f x)). Qed.
Lemma lem15675 {A B : Type'} (f : A -> B) : (@o A A B f (@I A)) = (term13 A B f).
Proof. exact (TRANS (@lem15668 A B f) (@lem15674 A B f)). Qed.
Lemma lem15676 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem15677 {A B : Type'} (f : A -> B) (x : A) : (@o A A B f (@I A) x) = (term14 A B f x).
Proof. exact (MK_COMB (@lem15675 A B f) (@lem15676 A x)). Qed.
Lemma lem15679 {A B : Type'} (f : A -> B) (y : A) : (term14 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem15680 {A B : Type'} (f : A -> B) (y : A) : (term14 A B f y) = (f y).
Proof. exact (@lem15679 A B f y). Qed.
Lemma lem15681 {A B : Type'} (f : A -> B) (x : A) : (term14 A B f x) = (f x).
Proof. exact (@lem15680 A B f x). Qed.
Lemma lem15682 {A B : Type'} (f : A -> B) (x : A) : (@o A A B f (@I A) x) = (f x).
Proof. exact (TRANS (@lem15677 A B f x) (@lem15681 A B f x)). Qed.
Lemma lem15683 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem15684 {A B : Type'} (f : A -> B) (x : A) : (term25 A B f x) = (term16 A B f x).
Proof. exact (MK_COMB (@lem15683 B) (@lem15682 A B f x)). Qed.
Lemma lem15685 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem15686 {A B : Type'} (f : A -> B) (x : A) : ((@o A A B f (@I A) x) = (f x)) = ((f x) = (f x)).
Proof. exact (MK_COMB (@lem15684 A B f x) (@lem15685 A B f x)). Qed.
Lemma lem15688 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem15689 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem15688 B x). Qed.
Lemma lem15690 {A B : Type'} (f : A -> B) (x : A) : ((f x) = (f x)) = True.
Proof. exact (@lem15689 B (f x)). Qed.
Lemma lem15691 {A B : Type'} (f : A -> B) (x : A) : ((@o A A B f (@I A) x) = (f x)) = True.
Proof. exact (TRANS (@lem15686 A B f x) (@lem15690 A B f x)). Qed.
Lemma lem15692 {A B : Type'} (f : A -> B) : (term26 A B f) = (term18 A).
Proof. exact (fun_ext (fun x : A => @lem15691 A B f x)). Qed.
Lemma lem15693 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem15694 {A B : Type'} (f : A -> B) : (term21 A B f) = (term19 A).
Proof. exact (MK_COMB (@lem15693 A) (@lem15692 A B f)). Qed.
Lemma lem15696 {A : Type'} (t : Prop) : (term20 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem15697 {A : Type'} (t : Prop) : (term20 A t) = t.
Proof. exact (@lem15696 A t). Qed.
Lemma lem15698 {A : Type'} : (term19 A) = True.
Proof. exact (@lem15697 A True). Qed.
Lemma lem15699 {A B : Type'} (f : A -> B) : (term21 A B f) = True.
Proof. exact (TRANS (@lem15694 A B f) (@lem15698 A)). Qed.
Lemma lem15700 {A B : Type'} (f : A -> B) : ((@o A A B f (@I A)) = f) = True.
Proof. exact (TRANS (@lem15656 A B f) (@lem15699 A B f)). Qed.
Lemma lem15701 {A B : Type'} (f : A -> B) : True = ((@o A A B f (@I A)) = f).
Proof. exact (SYM (@lem15700 A B f)). Qed.
Lemma lem15702 {A B : Type'} (f : A -> B) : (@o A A B f (@I A)) = f.
Proof. exact (EQ_MP (@lem15701 A B f) (@lem0)). Qed.
Lemma lem15703 {A B : Type'} (f : A -> B) : term27 A B f.
Proof. exact (conj (@lem15650 A B f) (@lem15702 A B f)). Qed.
Lemma lem15708 {A B : Type'} : term28 A B.
Proof. exact (fun f : A -> B => @lem15703 A B f). Qed.
