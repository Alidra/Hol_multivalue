Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RESTRICTION_THM_term_abbrevs.
Require Import FUN_EQ_THM_spec.
Require Import RESTRICTION_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem4386627 {A B : Type'} (s : A -> Prop) : term0 A B s.
Proof. exact (@lem4386626 A B s). Qed.
Lemma lem4386628 {A B : Type'} (s : A -> Prop) : (term0 A B s) = (term1 A B s).
Proof. exact (eq_refl (term0 A B s)). Qed.
Lemma lem4386629 {A B : Type'} (s : A -> Prop) : term1 A B s.
Proof. exact (EQ_MP (@lem4386628 A B s) (@lem4386627 A B s)). Qed.
Lemma lem4386630 {A B : Type'} (s : A -> Prop) (f : A -> B) : term2 A B s f.
Proof. exact (@lem4386629 A B s f). Qed.
Lemma lem4386631 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term2 A B s f) = (term3 A B s f).
Proof. exact (eq_refl (term2 A B s f)). Qed.
Lemma lem4386632 {A B : Type'} (s : A -> Prop) (f : A -> B) : term3 A B s f.
Proof. exact (EQ_MP (@lem4386631 A B s f) (@lem4386630 A B s f)). Qed.
Lemma lem4386633 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term4 A B s f x.
Proof. exact (@lem4386632 A B s f x). Qed.
Lemma lem4386634 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term4 A B s f x) = ((@RESTRICTION A B s f x) = (term5 A B s f x)).
Proof. exact (eq_refl (term4 A B s f x)). Qed.
Lemma lem4386636 {A B : Type'} (f : A -> B) : term6 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem4386637 {A B : Type'} (f : A -> B) : (term6 A B f) = (term7 A B f).
Proof. exact (eq_refl (term6 A B f)). Qed.
Lemma lem4386638 {A B : Type'} (f : A -> B) : term7 A B f.
Proof. exact (EQ_MP (@lem4386637 A B f) (@lem4386636 A B f)). Qed.
Lemma lem4386639 {A B : Type'} (f : A -> B) (g : A -> B) : term8 A B f g.
Proof. exact (@lem4386638 A B f g). Qed.
Lemma lem4386640 {A B : Type'} (f : A -> B) (g : A -> B) : (term8 A B f g) = ((f = g) = (term9 A B f g)).
Proof. exact (eq_refl (term8 A B f g)). Qed.
Lemma lem4386653 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term9 A B f g).
Proof. exact (EQ_MP (@lem4386640 A B f g) (@lem4386639 A B f g)). Qed.
Lemma lem4386654 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term9 A B f g).
Proof. exact (@lem4386653 A B f g). Qed.
Lemma lem4386655 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((@RESTRICTION A B s f) = (term10 A B s f)) = (term11 A B s f).
Proof. exact (@lem4386654 A B (@RESTRICTION A B s f) (term10 A B s f)). Qed.
Lemma lem4386665 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term5 A B s f x).
Proof. exact (EQ_MP (@lem4386634 A B s f x) (@lem4386633 A B s f x)). Qed.
Lemma lem4386666 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term5 A B s f x).
Proof. exact (@lem4386665 A B s f x). Qed.
Lemma lem4386667 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4386668 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term12 A B s f x) = (term13 A B s f x).
Proof. exact (MK_COMB (@lem4386667 B) (@lem4386666 A B s f x)). Qed.
Lemma lem4386670 {A B : Type'} (f : A -> B) (y : A) : (term14 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4386671 {A B : Type'} (f : A -> B) (y : A) : (term14 A B f y) = (f y).
Proof. exact (@lem4386670 A B f y). Qed.
Lemma lem4386672 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term15 A B s f x) = (term16 A B s f x).
Proof. exact (@lem4386671 A B (term10 A B s f) x). Qed.
Lemma lem4386673 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term16 A B s f x) = (term5 A B s f x).
Proof. exact (eq_refl (term16 A B s f x)). Qed.
Lemma lem4386674 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term17 A B s f) = (term10 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4386673 A B s f x)). Qed.
Lemma lem4386675 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4386676 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term15 A B s f x) = (term16 A B s f x).
Proof. exact (MK_COMB (@lem4386674 A B s f) (@lem4386675 A x)). Qed.
Lemma lem4386677 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4386678 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term18 A B s f x) = (term19 A B s f x).
Proof. exact (MK_COMB (@lem4386677 B) (@lem4386676 A B s f x)). Qed.
Lemma lem4386679 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term16 A B s f x) = (term5 A B s f x).
Proof. exact (eq_refl (term16 A B s f x)). Qed.
Lemma lem4386680 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : ((term15 A B s f x) = (term16 A B s f x)) = ((term16 A B s f x) = (term5 A B s f x)).
Proof. exact (MK_COMB (@lem4386678 A B s f x) (@lem4386679 A B s f x)). Qed.
Lemma lem4386681 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term16 A B s f x) = (term5 A B s f x).
Proof. exact (EQ_MP (@lem4386680 A B s f x) (@lem4386672 A B s f x)). Qed.
Lemma lem4386682 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : ((@RESTRICTION A B s f x) = (term16 A B s f x)) = ((term5 A B s f x) = (term5 A B s f x)).
Proof. exact (MK_COMB (@lem4386668 A B s f x) (@lem4386681 A B s f x)). Qed.
Lemma lem4386684 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4386685 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem4386684 B x). Qed.
Lemma lem4386686 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : ((term5 A B s f x) = (term5 A B s f x)) = True.
Proof. exact (@lem4386685 B (term5 A B s f x)). Qed.
Lemma lem4386687 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : ((@RESTRICTION A B s f x) = (term16 A B s f x)) = True.
Proof. exact (TRANS (@lem4386682 A B s f x) (@lem4386686 A B s f x)). Qed.
Lemma lem4386688 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term20 A B s f) = (term21 A).
Proof. exact (fun_ext (fun x : A => @lem4386687 A B s f x)). Qed.
Lemma lem4386689 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4386690 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term11 A B s f) = (term22 A).
Proof. exact (MK_COMB (@lem4386689 A) (@lem4386688 A B s f)). Qed.
Lemma lem4386692 {A : Type'} (t : Prop) : (term23 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4386693 {A : Type'} (t : Prop) : (term23 A t) = t.
Proof. exact (@lem4386692 A t). Qed.
Lemma lem4386694 {A : Type'} : (term22 A) = True.
Proof. exact (@lem4386693 A True). Qed.
Lemma lem4386695 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term11 A B s f) = True.
Proof. exact (TRANS (@lem4386690 A B s f) (@lem4386694 A)). Qed.
Lemma lem4386696 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((@RESTRICTION A B s f) = (term10 A B s f)) = True.
Proof. exact (TRANS (@lem4386655 A B s f) (@lem4386695 A B s f)). Qed.
Lemma lem4386697 {A B : Type'} (s : A -> Prop) : (term24 A B s) = (term25 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4386696 A B s f)). Qed.
Lemma lem4386698 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4386699 {A B : Type'} (s : A -> Prop) : (term26 A B s) = (term27 A B).
Proof. exact (MK_COMB (@lem4386698 A B) (@lem4386697 A B s)). Qed.
Lemma lem4386701 {A : Type'} (t : Prop) : (term23 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4386702 {A B : Type'} (t : Prop) : (term28 A B t) = t.
Proof. exact (@lem4386701 (A -> B) t). Qed.
Lemma lem4386703 {A B : Type'} : (term27 A B) = True.
Proof. exact (@lem4386702 A B True). Qed.
Lemma lem4386704 {A B : Type'} (s : A -> Prop) : (term26 A B s) = True.
Proof. exact (TRANS (@lem4386699 A B s) (@lem4386703 A B)). Qed.
Lemma lem4386705 {A B : Type'} : (term29 A B) = (term30 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4386704 A B s)). Qed.
Lemma lem4386706 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4386707 {A B : Type'} : (term31 A B) = (term32 A).
Proof. exact (MK_COMB (@lem4386706 A) (@lem4386705 A B)). Qed.
Lemma lem4386709 {A : Type'} (t : Prop) : (term23 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4386710 {A : Type'} (t : Prop) : (term33 A t) = t.
Proof. exact (@lem4386709 (A -> Prop) t). Qed.
Lemma lem4386711 {A : Type'} : (term32 A) = True.
Proof. exact (@lem4386710 A True). Qed.
Lemma lem4386712 {A B : Type'} : (term31 A B) = True.
Proof. exact (TRANS (@lem4386707 A B) (@lem4386711 A)). Qed.
Lemma lem4386713 {A B : Type'} : True = (term31 A B).
Proof. exact (SYM (@lem4386712 A B)). Qed.
Lemma lem4386714 {A B : Type'} : term31 A B.
Proof. exact (EQ_MP (@lem4386713 A B) (@lem0)). Qed.
