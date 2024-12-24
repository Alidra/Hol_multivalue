Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DISJOINT_CROSS_term_abbrevs.
Require Import CROSS_EQ_EMPTY_spec.
Require Import DISJOINT_spec.
Require Import INTER_CROSS_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem4380561 {_103840 _103844 : Type'} (s : _103840 -> Prop) : term0 _103840 _103844 s.
Proof. exact (@lem4326997 _103840 _103844 s). Qed.
Lemma lem4380562 {_103840 _103844 : Type'} (s : _103840 -> Prop) : (term0 _103840 _103844 s) = (term1 _103840 _103844 s).
Proof. exact (eq_refl (term0 _103840 _103844 s)). Qed.
Lemma lem4380563 {_103840 _103844 : Type'} (s : _103840 -> Prop) : term1 _103840 _103844 s.
Proof. exact (EQ_MP (@lem4380562 _103840 _103844 s) (@lem4380561 _103840 _103844 s)). Qed.
Lemma lem4380564 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : term2 _103840 _103844 s t.
Proof. exact (@lem4380563 _103840 _103844 s t). Qed.
Lemma lem4380565 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term2 _103840 _103844 s t) = (((@CROSS _103844 _103840 s t) = (@EMPTY (prod _103840 _103844))) = (term3 _103840 _103844 s t)).
Proof. exact (eq_refl (term2 _103840 _103844 s t)). Qed.
Lemma lem4380567 {_104663 _104666 : Type'} (s : _104663 -> Prop) : term4 _104663 _104666 s.
Proof. exact (@lem4362894 _104663 _104666 s). Qed.
Lemma lem4380568 {_104663 _104666 : Type'} (s : _104663 -> Prop) : (term4 _104663 _104666 s) = (term5 _104663 _104666 s).
Proof. exact (eq_refl (term4 _104663 _104666 s)). Qed.
Lemma lem4380569 {_104663 _104666 : Type'} (s : _104663 -> Prop) : term5 _104663 _104666 s.
Proof. exact (EQ_MP (@lem4380568 _104663 _104666 s) (@lem4380567 _104663 _104666 s)). Qed.
Lemma lem4380570 {_104663 _104666 : Type'} (s : _104663 -> Prop) (s' : _104663 -> Prop) : term6 _104663 _104666 s s'.
Proof. exact (@lem4380569 _104663 _104666 s s'). Qed.
Lemma lem4380571 {_104663 _104666 : Type'} (s : _104663 -> Prop) (s' : _104663 -> Prop) : (term6 _104663 _104666 s s') = (term7 _104663 _104666 s s').
Proof. exact (eq_refl (term6 _104663 _104666 s s')). Qed.
Lemma lem4380572 {_104663 _104666 : Type'} (s : _104663 -> Prop) (s' : _104663 -> Prop) : term7 _104663 _104666 s s'.
Proof. exact (EQ_MP (@lem4380571 _104663 _104666 s s') (@lem4380570 _104663 _104666 s s')). Qed.
Lemma lem4380573 {_104663 _104666 : Type'} (s : _104663 -> Prop) (s' : _104663 -> Prop) (t : _104666 -> Prop) : term8 _104663 _104666 s s' t.
Proof. exact (@lem4380572 _104663 _104666 s s' t). Qed.
Lemma lem4380574 {_104663 _104666 : Type'} (s : _104663 -> Prop) (s' : _104663 -> Prop) (t : _104666 -> Prop) : (term8 _104663 _104666 s s' t) = (term9 _104663 _104666 s s' t).
Proof. exact (eq_refl (term8 _104663 _104666 s s' t)). Qed.
Lemma lem4380575 {_104663 _104666 : Type'} (s : _104663 -> Prop) (s' : _104663 -> Prop) (t : _104666 -> Prop) : term9 _104663 _104666 s s' t.
Proof. exact (EQ_MP (@lem4380574 _104663 _104666 s s' t) (@lem4380573 _104663 _104666 s s' t)). Qed.
Lemma lem4380576 {_104663 _104666 : Type'} (s : _104663 -> Prop) (s' : _104663 -> Prop) (t : _104666 -> Prop) (t' : _104666 -> Prop) : term10 _104663 _104666 s s' t t'.
Proof. exact (@lem4380575 _104663 _104666 s s' t t'). Qed.
Lemma lem4380577 {_104663 _104666 : Type'} (s : _104663 -> Prop) (s' : _104663 -> Prop) (t : _104666 -> Prop) (t' : _104666 -> Prop) : (term10 _104663 _104666 s s' t t') = ((term11 _104663 _104666 s t s' t') = (term12 _104663 _104666 s s' t t')).
Proof. exact (eq_refl (term10 _104663 _104666 s s' t t')). Qed.
Lemma lem4380579 {A : Type'} (s : A -> Prop) : term13 A s.
Proof. exact (@lem3196110 A s). Qed.
Lemma lem4380580 {A : Type'} (s : A -> Prop) : (term13 A s) = (term14 A s).
Proof. exact (eq_refl (term13 A s)). Qed.
Lemma lem4380581 {A : Type'} (s : A -> Prop) : term14 A s.
Proof. exact (EQ_MP (@lem4380580 A s) (@lem4380579 A s)). Qed.
Lemma lem4380582 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term15 A s t.
Proof. exact (@lem4380581 A s t). Qed.
Lemma lem4380583 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term15 A s t) = ((@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A))).
Proof. exact (eq_refl (term15 A s t)). Qed.
Lemma lem4380604 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem4380583 A s t) (@lem4380582 A s t)). Qed.
Lemma lem4380605 {A B : Type'} (s : type1210 A B) (t : type1210 A B) : (@DISJOINT (prod A B) s t) = ((@INTER (prod A B) s t) = (@EMPTY (prod A B))).
Proof. exact (@lem4380604 (prod A B) s t). Qed.
Lemma lem4380606 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : (term16 A B s t s' t') = ((term11 A B s t s' t') = (@EMPTY (prod A B))).
Proof. exact (@lem4380605 A B (@CROSS B A s t) (@CROSS B A s' t')). Qed.
Lemma lem4380610 {_104663 _104666 : Type'} (s : _104663 -> Prop) (s' : _104663 -> Prop) (t : _104666 -> Prop) (t' : _104666 -> Prop) : (term11 _104663 _104666 s t s' t') = (term12 _104663 _104666 s s' t t').
Proof. exact (EQ_MP (@lem4380577 _104663 _104666 s s' t t') (@lem4380576 _104663 _104666 s s' t t')). Qed.
Lemma lem4380611 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term11 A B s t s' t') = (term12 A B s s' t t').
Proof. exact (@lem4380610 A B s s' t t'). Qed.
Lemma lem4380612 {A B : Type'} : (@eq ((prod A B) -> Prop)) = (@eq ((prod A B) -> Prop)).
Proof. exact (eq_refl (@eq ((prod A B) -> Prop))). Qed.
Lemma lem4380613 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term17 A B s t s' t') = (term18 A B s s' t t').
Proof. exact (MK_COMB (@lem4380612 A B) (@lem4380611 A B s s' t t')). Qed.
Lemma lem4380614 {A B : Type'} : (@EMPTY (prod A B)) = (@EMPTY (prod A B)).
Proof. exact (eq_refl (@EMPTY (prod A B))). Qed.
Lemma lem4380615 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : ((term11 A B s t s' t') = (@EMPTY (prod A B))) = ((term12 A B s s' t t') = (@EMPTY (prod A B))).
Proof. exact (MK_COMB (@lem4380613 A B s s' t t') (@lem4380614 A B)). Qed.
Lemma lem4380617 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : ((@CROSS _103844 _103840 s t) = (@EMPTY (prod _103840 _103844))) = (term3 _103840 _103844 s t).
Proof. exact (EQ_MP (@lem4380565 _103840 _103844 s t) (@lem4380564 _103840 _103844 s t)). Qed.
Lemma lem4380618 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : ((@CROSS B A s t) = (@EMPTY (prod A B))) = (term3 A B s t).
Proof. exact (@lem4380617 A B s t). Qed.
Lemma lem4380619 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : ((term12 A B s s' t t') = (@EMPTY (prod A B))) = (term19 A B s s' t t').
Proof. exact (@lem4380618 A B (@INTER A s s') (@INTER B t t')). Qed.
Lemma lem4380626 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : ((term11 A B s t s' t') = (@EMPTY (prod A B))) = (term19 A B s s' t t').
Proof. exact (TRANS (@lem4380615 A B s s' t t') (@lem4380619 A B s s' t t')). Qed.
Lemma lem4380627 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term16 A B s t s' t') = (term19 A B s s' t t').
Proof. exact (TRANS (@lem4380606 A B s t s' t') (@lem4380626 A B s s' t t')). Qed.
Lemma lem4380628 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4380629 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term20 A B s t s' t') = (term21 A B s s' t t').
Proof. exact (MK_COMB (@lem4380628) (@lem4380627 A B s s' t t')). Qed.
Lemma lem4380633 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem4380583 A s t) (@lem4380582 A s t)). Qed.
Lemma lem4380634 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (@lem4380633 A s t). Qed.
Lemma lem4380635 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (@DISJOINT A s s') = ((@INTER A s s') = (@EMPTY A)).
Proof. exact (@lem4380634 A s s'). Qed.
Lemma lem4380638 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4380639 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term22 A s s') = (term23 A s s').
Proof. exact (MK_COMB (@lem4380638) (@lem4380635 A s s')). Qed.
Lemma lem4380641 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem4380583 A s t) (@lem4380582 A s t)). Qed.
Lemma lem4380642 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@DISJOINT B s t) = ((@INTER B s t) = (@EMPTY B)).
Proof. exact (@lem4380641 B s t). Qed.
Lemma lem4380643 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (@DISJOINT B t t') = ((@INTER B t t') = (@EMPTY B)).
Proof. exact (@lem4380642 B t t'). Qed.
Lemma lem4380646 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term24 A B s s' t t') = (term19 A B s s' t t').
Proof. exact (MK_COMB (@lem4380639 A s s') (@lem4380643 B t t')). Qed.
Lemma lem4380649 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : ((term16 A B s t s' t') = (term24 A B s s' t t')) = ((term19 A B s s' t t') = (term19 A B s s' t t')).
Proof. exact (MK_COMB (@lem4380629 A B s s' t t') (@lem4380646 A B s s' t t')). Qed.
Lemma lem4380651 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4380652 (x : Prop) : (x = x) = True.
Proof. exact (@lem4380651 Prop x). Qed.
Lemma lem4380653 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : ((term19 A B s s' t t') = (term19 A B s s' t t')) = True.
Proof. exact (@lem4380652 (term19 A B s s' t t')). Qed.
Lemma lem4380654 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : ((term16 A B s t s' t') = (term24 A B s s' t t')) = True.
Proof. exact (TRANS (@lem4380649 A B s s' t t') (@lem4380653 A B s s' t t')). Qed.
Lemma lem4380655 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) : (term25 A B s s' t) = (term26 B).
Proof. exact (fun_ext (fun t' : B -> Prop => @lem4380654 A B s s' t t')). Qed.
Lemma lem4380656 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4380657 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) : (term27 A B s s' t) = (term28 B).
Proof. exact (MK_COMB (@lem4380656 B) (@lem4380655 A B s s' t)). Qed.
Lemma lem4380659 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4380660 {B : Type'} (t : Prop) : (term30 B t) = t.
Proof. exact (@lem4380659 (B -> Prop) t). Qed.
Lemma lem4380661 {B : Type'} : (term28 B) = True.
Proof. exact (@lem4380660 B True). Qed.
Lemma lem4380662 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) : (term27 A B s s' t) = True.
Proof. exact (TRANS (@lem4380657 A B s s' t) (@lem4380661 B)). Qed.
Lemma lem4380663 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term31 A B s t) = (term26 A).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem4380662 A B s s' t)). Qed.
Lemma lem4380664 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4380665 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term32 A B s t) = (term28 A).
Proof. exact (MK_COMB (@lem4380664 A) (@lem4380663 A B s t)). Qed.
Lemma lem4380667 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4380668 {A : Type'} (t : Prop) : (term30 A t) = t.
Proof. exact (@lem4380667 (A -> Prop) t). Qed.
Lemma lem4380669 {A : Type'} : (term28 A) = True.
Proof. exact (@lem4380668 A True). Qed.
Lemma lem4380670 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term32 A B s t) = True.
Proof. exact (TRANS (@lem4380665 A B s t) (@lem4380669 A)). Qed.
Lemma lem4380671 {A B : Type'} (s : A -> Prop) : (term33 A B s) = (term26 B).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4380670 A B s t)). Qed.
Lemma lem4380672 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4380673 {A B : Type'} (s : A -> Prop) : (term34 A B s) = (term28 B).
Proof. exact (MK_COMB (@lem4380672 B) (@lem4380671 A B s)). Qed.
Lemma lem4380675 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4380676 {B : Type'} (t : Prop) : (term30 B t) = t.
Proof. exact (@lem4380675 (B -> Prop) t). Qed.
Lemma lem4380677 {B : Type'} : (term28 B) = True.
Proof. exact (@lem4380676 B True). Qed.
Lemma lem4380678 {A B : Type'} (s : A -> Prop) : (term34 A B s) = True.
Proof. exact (TRANS (@lem4380673 A B s) (@lem4380677 B)). Qed.
Lemma lem4380679 {A B : Type'} : (term35 A B) = (term26 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4380678 A B s)). Qed.
Lemma lem4380680 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4380681 {A B : Type'} : (term36 A B) = (term28 A).
Proof. exact (MK_COMB (@lem4380680 A) (@lem4380679 A B)). Qed.
Lemma lem4380683 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4380684 {A : Type'} (t : Prop) : (term30 A t) = t.
Proof. exact (@lem4380683 (A -> Prop) t). Qed.
Lemma lem4380685 {A : Type'} : (term28 A) = True.
Proof. exact (@lem4380684 A True). Qed.
Lemma lem4380686 {A B : Type'} : (term36 A B) = True.
Proof. exact (TRANS (@lem4380681 A B) (@lem4380685 A)). Qed.
Lemma lem4380687 {A B : Type'} : True = (term36 A B).
Proof. exact (SYM (@lem4380686 A B)). Qed.
Lemma lem4380688 {A B : Type'} : term36 A B.
Proof. exact (EQ_MP (@lem4380687 A B) (@lem0)). Qed.
