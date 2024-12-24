Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4374857_term_abbrevs.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1843_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211668_spec.
Require Import thm3211669_spec.
Require Import thm3211724_spec.
Require Import thm3211725_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4372190_spec.
Require Import thm4372255_spec.
Lemma lem4374546 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (h1 : term0 _104907 f) (h2 : g = (@EMPTY (_104908 -> Prop))) : term1 _104907 _104908 g f.
Proof. exact (conj (@lem4372255 _104908 g h2) (@lem4372190 _104907 f h1)). Qed.
Lemma lem4374554 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term2 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4374555 {_104908 : Type'} (s : type686 _104908) (t : type686 _104908) : (s = t) = (term3 _104908 s t).
Proof. exact (@lem4374554 (_104908 -> Prop) s t). Qed.
Lemma lem4374556 {_104908 : Type'} (g : type686 _104908) : (g = (@EMPTY (_104908 -> Prop))) = (term4 _104908 g).
Proof. exact (@lem4374555 _104908 g (@EMPTY (_104908 -> Prop))). Qed.
Lemma lem4374565 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4374566 {_104908 : Type'} (g : type686 _104908) : (term5 _104908 g) = (term6 _104908 g).
Proof. exact (MK_COMB (@lem4374565) (@lem4374556 _104908 g)). Qed.
Lemma lem4374570 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term2 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4374571 {_104907 : Type'} (s : type686 _104907) (t : type686 _104907) : (s = t) = (term3 _104907 s t).
Proof. exact (@lem4374570 (_104907 -> Prop) s t). Qed.
Lemma lem4374572 {_104907 : Type'} (f : type686 _104907) : (f = (@EMPTY (_104907 -> Prop))) = (term4 _104907 f).
Proof. exact (@lem4374571 _104907 f (@EMPTY (_104907 -> Prop))). Qed.
Lemma lem4374581 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4374582 {_104907 : Type'} (f : type686 _104907) : (term0 _104907 f) = (term7 _104907 f).
Proof. exact (MK_COMB (@lem4374581) (@lem4374572 _104907 f)). Qed.
Lemma lem4374583 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : (term1 _104907 _104908 g f) = (term8 _104907 _104908 g f).
Proof. exact (MK_COMB (@lem4374566 _104908 g) (@lem4374582 _104907 f)). Qed.
Lemma lem4374586 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4374587 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : (term9 _104907 _104908 g f) = (term10 _104907 _104908 g f).
Proof. exact (MK_COMB (@lem4374586) (@lem4374583 _104907 _104908 g f)). Qed.
Lemma lem4374610 {_104907 _104908 : Type'} (f : type686 _104907) : (term11 _104907 _104908 f) = (term11 _104907 _104908 f).
Proof. exact (eq_refl (term11 _104907 _104908 f)). Qed.
Lemma lem4374611 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : (term12 _104907 _104908 g f) = (term13 _104907 _104908 g f).
Proof. exact (MK_COMB (@lem4374587 _104907 _104908 g f) (@lem4374610 _104907 _104908 f)). Qed.
Lemma lem4374614 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : (term13 _104907 _104908 g f) = (term12 _104907 _104908 g f).
Proof. exact (SYM (@lem4374611 _104907 _104908 g f)). Qed.
Lemma lem4374626 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4374627 {_104908 : Type'} (P : type686 _104908) (x : _104908 -> Prop) : (@IN (_104908 -> Prop) x P) = (P x).
Proof. exact (@lem4374626 (_104908 -> Prop) P x). Qed.
Lemma lem4374628 {_104908 : Type'} (g : type686 _104908) (x : _104908 -> Prop) : (@IN (_104908 -> Prop) x g) = (g x).
Proof. exact (@lem4374627 _104908 g x). Qed.
Lemma lem4374629 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4374630 {_104908 : Type'} (g : type686 _104908) (x : _104908 -> Prop) : (term14 _104908 x g) = (term15 _104908 g x).
Proof. exact (MK_COMB (@lem4374629) (@lem4374628 _104908 g x)). Qed.
Lemma lem4374632 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4374633 {_104908 : Type'} (x : _104908 -> Prop) : (@IN (_104908 -> Prop) x (@EMPTY (_104908 -> Prop))) = False.
Proof. exact (@lem4374632 (_104908 -> Prop) x). Qed.
Lemma lem4374634 {_104908 : Type'} (g : type686 _104908) (x : _104908 -> Prop) : ((@IN (_104908 -> Prop) x g) = (@IN (_104908 -> Prop) x (@EMPTY (_104908 -> Prop)))) = ((g x) = False).
Proof. exact (MK_COMB (@lem4374630 _104908 g x) (@lem4374633 _104908 x)). Qed.
Lemma lem4374636 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4374637 {_104908 : Type'} (g : type686 _104908) (x : _104908 -> Prop) : ((g x) = False) = (term16 _104908 g x).
Proof. exact (@lem4374636 (g x)). Qed.
Lemma lem4374638 {_104908 : Type'} (g : type686 _104908) (x : _104908 -> Prop) : ((@IN (_104908 -> Prop) x g) = (@IN (_104908 -> Prop) x (@EMPTY (_104908 -> Prop)))) = (term16 _104908 g x).
Proof. exact (TRANS (@lem4374634 _104908 g x) (@lem4374637 _104908 g x)). Qed.
Lemma lem4374639 {_104908 : Type'} (g : type686 _104908) : (term17 _104908 g) = (term18 _104908 g).
Proof. exact (fun_ext (fun x : _104908 -> Prop => @lem4374638 _104908 g x)). Qed.
Lemma lem4374640 {_104908 : Type'} : (@all (_104908 -> Prop)) = (@all (_104908 -> Prop)).
Proof. exact (eq_refl (@all (_104908 -> Prop))). Qed.
Lemma lem4374641 {_104908 : Type'} (g : type686 _104908) : (term4 _104908 g) = (term19 _104908 g).
Proof. exact (MK_COMB (@lem4374640 _104908) (@lem4374639 _104908 g)). Qed.
Lemma lem4374646 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4374647 {_104908 : Type'} (g : type686 _104908) : (term6 _104908 g) = (term20 _104908 g).
Proof. exact (MK_COMB (@lem4374646) (@lem4374641 _104908 g)). Qed.
Lemma lem4374655 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4374656 {_104907 : Type'} (P : type686 _104907) (x : _104907 -> Prop) : (@IN (_104907 -> Prop) x P) = (P x).
Proof. exact (@lem4374655 (_104907 -> Prop) P x). Qed.
Lemma lem4374657 {_104907 : Type'} (f : type686 _104907) (x : _104907 -> Prop) : (@IN (_104907 -> Prop) x f) = (f x).
Proof. exact (@lem4374656 _104907 f x). Qed.
Lemma lem4374658 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4374659 {_104907 : Type'} (f : type686 _104907) (x : _104907 -> Prop) : (term14 _104907 x f) = (term15 _104907 f x).
Proof. exact (MK_COMB (@lem4374658) (@lem4374657 _104907 f x)). Qed.
Lemma lem4374661 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4374662 {_104907 : Type'} (x : _104907 -> Prop) : (@IN (_104907 -> Prop) x (@EMPTY (_104907 -> Prop))) = False.
Proof. exact (@lem4374661 (_104907 -> Prop) x). Qed.
Lemma lem4374663 {_104907 : Type'} (f : type686 _104907) (x : _104907 -> Prop) : ((@IN (_104907 -> Prop) x f) = (@IN (_104907 -> Prop) x (@EMPTY (_104907 -> Prop)))) = ((f x) = False).
Proof. exact (MK_COMB (@lem4374659 _104907 f x) (@lem4374662 _104907 x)). Qed.
Lemma lem4374665 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4374666 {_104907 : Type'} (f : type686 _104907) (x : _104907 -> Prop) : ((f x) = False) = (term16 _104907 f x).
Proof. exact (@lem4374665 (f x)). Qed.
Lemma lem4374667 {_104907 : Type'} (f : type686 _104907) (x : _104907 -> Prop) : ((@IN (_104907 -> Prop) x f) = (@IN (_104907 -> Prop) x (@EMPTY (_104907 -> Prop)))) = (term16 _104907 f x).
Proof. exact (TRANS (@lem4374663 _104907 f x) (@lem4374666 _104907 f x)). Qed.
Lemma lem4374668 {_104907 : Type'} (f : type686 _104907) : (term17 _104907 f) = (term18 _104907 f).
Proof. exact (fun_ext (fun x : _104907 -> Prop => @lem4374667 _104907 f x)). Qed.
Lemma lem4374669 {_104907 : Type'} : (@all (_104907 -> Prop)) = (@all (_104907 -> Prop)).
Proof. exact (eq_refl (@all (_104907 -> Prop))). Qed.
Lemma lem4374670 {_104907 : Type'} (f : type686 _104907) : (term4 _104907 f) = (term19 _104907 f).
Proof. exact (MK_COMB (@lem4374669 _104907) (@lem4374668 _104907 f)). Qed.
Lemma lem4374675 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4374676 {_104907 : Type'} (f : type686 _104907) : (term7 _104907 f) = (term21 _104907 f).
Proof. exact (MK_COMB (@lem4374675) (@lem4374670 _104907 f)). Qed.
Lemma lem4374677 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : (term8 _104907 _104908 g f) = (term22 _104907 _104908 g f).
Proof. exact (MK_COMB (@lem4374647 _104908 g) (@lem4374676 _104907 f)). Qed.
Lemma lem4374680 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4374681 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : (term10 _104907 _104908 g f) = (term23 _104907 _104908 g f).
Proof. exact (MK_COMB (@lem4374680) (@lem4374677 _104907 _104908 g f)). Qed.
Lemma lem4374695 {A : Type'} (s : type686 A) (x : A) : (term24 A x s) = (term25 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem4374696 {_104907 : Type'} (s : type686 _104907) (x : _104907) : (term24 _104907 x s) = (term25 _104907 s x).
Proof. exact (@lem4374695 _104907 s x). Qed.
Lemma lem4374697 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term24 _104907 p1 f) = (term25 _104907 f p1).
Proof. exact (@lem4374696 _104907 f p1). Qed.
Lemma lem4374705 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4374706 {_104907 : Type'} (P : type686 _104907) (x : _104907 -> Prop) : (@IN (_104907 -> Prop) x P) = (P x).
Proof. exact (@lem4374705 (_104907 -> Prop) P x). Qed.
Lemma lem4374707 {_104907 : Type'} (f : type686 _104907) (t : _104907 -> Prop) : (@IN (_104907 -> Prop) t f) = (f t).
Proof. exact (@lem4374706 _104907 f t). Qed.
Lemma lem4374708 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4374709 {_104907 : Type'} (f : type686 _104907) (t : _104907 -> Prop) : (term26 _104907 t f) = (term27 _104907 f t).
Proof. exact (MK_COMB (@lem4374708) (@lem4374707 _104907 f t)). Qed.
Lemma lem4374711 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4374712 {_104907 : Type'} (P : _104907 -> Prop) (x : _104907) : (@IN _104907 x P) = (P x).
Proof. exact (@lem4374711 _104907 P x). Qed.
Lemma lem4374713 {_104907 : Type'} (t : _104907 -> Prop) (p1 : _104907) : (@IN _104907 p1 t) = (t p1).
Proof. exact (@lem4374712 _104907 t p1). Qed.
Lemma lem4374714 {_104907 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) : (term28 _104907 f p1 t) = (term29 _104907 f t p1).
Proof. exact (MK_COMB (@lem4374709 _104907 f t) (@lem4374713 _104907 t p1)). Qed.
Lemma lem4374717 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term30 _104907 f p1) = (term31 _104907 f p1).
Proof. exact (fun_ext (fun t : _104907 -> Prop => @lem4374714 _104907 f t p1)). Qed.
Lemma lem4374718 {_104907 : Type'} : (@all (_104907 -> Prop)) = (@all (_104907 -> Prop)).
Proof. exact (eq_refl (@all (_104907 -> Prop))). Qed.
Lemma lem4374719 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term25 _104907 f p1) = (term32 _104907 f p1).
Proof. exact (MK_COMB (@lem4374718 _104907) (@lem4374717 _104907 f p1)). Qed.
Lemma lem4374724 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term24 _104907 p1 f) = (term32 _104907 f p1).
Proof. exact (TRANS (@lem4374697 _104907 f p1) (@lem4374719 _104907 f p1)). Qed.
Lemma lem4374725 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4374726 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term33 _104907 p1 f) = (term34 _104907 f p1).
Proof. exact (MK_COMB (@lem4374725) (@lem4374724 _104907 f p1)). Qed.
Lemma lem4374728 {A : Type'} (s : type686 A) (x : A) : (term24 A x s) = (term25 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem4374729 {_104908 : Type'} (s : type686 _104908) (x : _104908) : (term24 _104908 x s) = (term25 _104908 s x).
Proof. exact (@lem4374728 _104908 s x). Qed.
Lemma lem4374730 {_104908 : Type'} (p2 : _104908) : (term35 _104908 p2) = (term36 _104908 p2).
Proof. exact (@lem4374729 _104908 (@EMPTY (_104908 -> Prop)) p2). Qed.
Lemma lem4374738 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4374739 {_104908 : Type'} (x : _104908 -> Prop) : (@IN (_104908 -> Prop) x (@EMPTY (_104908 -> Prop))) = False.
Proof. exact (@lem4374738 (_104908 -> Prop) x). Qed.
Lemma lem4374740 {_104908 : Type'} (t : _104908 -> Prop) : (@IN (_104908 -> Prop) t (@EMPTY (_104908 -> Prop))) = False.
Proof. exact (@lem4374739 _104908 t). Qed.
Lemma lem4374741 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4374742 {_104908 : Type'} (t : _104908 -> Prop) : (term37 _104908 t) = (imp False).
Proof. exact (MK_COMB (@lem4374741) (@lem4374740 _104908 t)). Qed.
Lemma lem4374744 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4374745 {_104908 : Type'} (P : _104908 -> Prop) (x : _104908) : (@IN _104908 x P) = (P x).
Proof. exact (@lem4374744 _104908 P x). Qed.
Lemma lem4374746 {_104908 : Type'} (t : _104908 -> Prop) (p2 : _104908) : (@IN _104908 p2 t) = (t p2).
Proof. exact (@lem4374745 _104908 t p2). Qed.
Lemma lem4374747 {_104908 : Type'} (t : _104908 -> Prop) (p2 : _104908) : (term38 _104908 p2 t) = (term39 _104908 t p2).
Proof. exact (MK_COMB (@lem4374742 _104908 t) (@lem4374746 _104908 t p2)). Qed.
Lemma lem4374749 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4374750 {_104908 : Type'} (t : _104908 -> Prop) (p2 : _104908) : (term39 _104908 t p2) = True.
Proof. exact (@lem4374749 (t p2)). Qed.
Lemma lem4374751 {_104908 : Type'} (p2 : _104908) (t : _104908 -> Prop) : (term38 _104908 p2 t) = True.
Proof. exact (TRANS (@lem4374747 _104908 t p2) (@lem4374750 _104908 t p2)). Qed.
Lemma lem4374752 {_104908 : Type'} (p2 : _104908) : (term40 _104908 p2) = (term41 _104908).
Proof. exact (fun_ext (fun t : _104908 -> Prop => @lem4374751 _104908 p2 t)). Qed.
Lemma lem4374753 {_104908 : Type'} : (@all (_104908 -> Prop)) = (@all (_104908 -> Prop)).
Proof. exact (eq_refl (@all (_104908 -> Prop))). Qed.
Lemma lem4374754 {_104908 : Type'} (p2 : _104908) : (term36 _104908 p2) = (term42 _104908).
Proof. exact (MK_COMB (@lem4374753 _104908) (@lem4374752 _104908 p2)). Qed.
Lemma lem4374756 {A : Type'} (t : Prop) : (term43 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4374757 {_104908 : Type'} (t : Prop) : (term44 _104908 t) = t.
Proof. exact (@lem4374756 (_104908 -> Prop) t). Qed.
Lemma lem4374758 {_104908 : Type'} : (term42 _104908) = True.
Proof. exact (@lem4374757 _104908 True). Qed.
Lemma lem4374759 {_104908 : Type'} (p2 : _104908) : (term36 _104908 p2) = True.
Proof. exact (TRANS (@lem4374754 _104908 p2) (@lem4374758 _104908)). Qed.
Lemma lem4374760 {_104908 : Type'} (p2 : _104908) : (term35 _104908 p2) = True.
Proof. exact (TRANS (@lem4374730 _104908 p2) (@lem4374759 _104908 p2)). Qed.
Lemma lem4374761 {_104907 _104908 : Type'} (p2 : _104908) (f : type686 _104907) (p1 : _104907) : (term45 _104907 _104908 p1 f p2) = (term46 _104907 f p1).
Proof. exact (MK_COMB (@lem4374726 _104907 f p1) (@lem4374760 _104908 p2)). Qed.
Lemma lem4374763 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4374764 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term46 _104907 f p1) = (term32 _104907 f p1).
Proof. exact (@lem4374763 (term32 _104907 f p1)). Qed.
Lemma lem4374771 {_104907 _104908 : Type'} (p2 : _104908) (f : type686 _104907) (p1 : _104907) : (term45 _104907 _104908 p1 f p2) = (term32 _104907 f p1).
Proof. exact (TRANS (@lem4374761 _104907 _104908 p2 f p1) (@lem4374764 _104907 f p1)). Qed.
Lemma lem4374772 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4374773 {_104907 _104908 : Type'} (p2 : _104908) (f : type686 _104907) (p1 : _104907) : (term47 _104907 _104908 p1 f p2) = (term48 _104907 f p1).
Proof. exact (MK_COMB (@lem4374772) (@lem4374771 _104907 _104908 p2 f p1)). Qed.
Lemma lem4374781 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4374782 {_104907 : Type'} (P : type686 _104907) (x : _104907 -> Prop) : (@IN (_104907 -> Prop) x P) = (P x).
Proof. exact (@lem4374781 (_104907 -> Prop) P x). Qed.
Lemma lem4374783 {_104907 : Type'} (f : type686 _104907) (s : _104907 -> Prop) : (@IN (_104907 -> Prop) s f) = (f s).
Proof. exact (@lem4374782 _104907 f s). Qed.
Lemma lem4374784 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4374785 {_104907 : Type'} (f : type686 _104907) (s : _104907 -> Prop) : (term26 _104907 s f) = (term27 _104907 f s).
Proof. exact (MK_COMB (@lem4374784) (@lem4374783 _104907 f s)). Qed.
Lemma lem4374789 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4374790 {_104907 : Type'} (P : _104907 -> Prop) (x : _104907) : (@IN _104907 x P) = (P x).
Proof. exact (@lem4374789 _104907 P x). Qed.
Lemma lem4374791 {_104907 : Type'} (s : _104907 -> Prop) (p1 : _104907) : (@IN _104907 p1 s) = (s p1).
Proof. exact (@lem4374790 _104907 s p1). Qed.
Lemma lem4374792 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4374793 {_104907 : Type'} (s : _104907 -> Prop) (p1 : _104907) : (term49 _104907 p1 s) = (term50 _104907 s p1).
Proof. exact (MK_COMB (@lem4374792) (@lem4374791 _104907 s p1)). Qed.
Lemma lem4374795 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem4374796 {_104908 : Type'} (x : _104908) : (@IN _104908 x (@UNIV _104908)) = True.
Proof. exact (@lem4374795 _104908 x). Qed.
Lemma lem4374797 {_104908 : Type'} (p2 : _104908) : (@IN _104908 p2 (@UNIV _104908)) = True.
Proof. exact (@lem4374796 _104908 p2). Qed.
Lemma lem4374798 {_104907 _104908 : Type'} (p2 : _104908) (s : _104907 -> Prop) (p1 : _104907) : (term51 _104907 _104908 p1 s p2) = (term52 _104907 s p1).
Proof. exact (MK_COMB (@lem4374793 _104907 s p1) (@lem4374797 _104908 p2)). Qed.
Lemma lem4374800 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4374801 {_104907 : Type'} (s : _104907 -> Prop) (p1 : _104907) : (term52 _104907 s p1) = (s p1).
Proof. exact (@lem4374800 (s p1)). Qed.
Lemma lem4374802 {_104907 _104908 : Type'} (p2 : _104908) (s : _104907 -> Prop) (p1 : _104907) : (term51 _104907 _104908 p1 s p2) = (s p1).
Proof. exact (TRANS (@lem4374798 _104907 _104908 p2 s p1) (@lem4374801 _104907 s p1)). Qed.
Lemma lem4374803 {_104907 _104908 : Type'} (p2 : _104908) (f : type686 _104907) (s : _104907 -> Prop) (p1 : _104907) : (term53 _104907 _104908 f p1 s p2) = (term29 _104907 f s p1).
Proof. exact (MK_COMB (@lem4374785 _104907 f s) (@lem4374802 _104907 _104908 p2 s p1)). Qed.
Lemma lem4374806 {_104907 _104908 : Type'} (p2 : _104908) (f : type686 _104907) (p1 : _104907) : (term54 _104907 _104908 f p1 p2) = (term31 _104907 f p1).
Proof. exact (fun_ext (fun s : _104907 -> Prop => @lem4374803 _104907 _104908 p2 f s p1)). Qed.
Lemma lem4374807 {_104907 : Type'} : (@all (_104907 -> Prop)) = (@all (_104907 -> Prop)).
Proof. exact (eq_refl (@all (_104907 -> Prop))). Qed.
Lemma lem4374808 {_104907 _104908 : Type'} (p2 : _104908) (f : type686 _104907) (p1 : _104907) : (term55 _104907 _104908 f p1 p2) = (term32 _104907 f p1).
Proof. exact (MK_COMB (@lem4374807 _104907) (@lem4374806 _104907 _104908 p2 f p1)). Qed.
Lemma lem4374813 {_104907 _104908 : Type'} (p2 : _104908) (f : type686 _104907) (p1 : _104907) : ((term45 _104907 _104908 p1 f p2) = (term55 _104907 _104908 f p1 p2)) = ((term32 _104907 f p1) = (term32 _104907 f p1)).
Proof. exact (MK_COMB (@lem4374773 _104907 _104908 p2 f p1) (@lem4374808 _104907 _104908 p2 f p1)). Qed.
Lemma lem4374815 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4374816 (x : Prop) : (x = x) = True.
Proof. exact (@lem4374815 Prop x). Qed.
Lemma lem4374817 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : ((term32 _104907 f p1) = (term32 _104907 f p1)) = True.
Proof. exact (@lem4374816 (term32 _104907 f p1)). Qed.
Lemma lem4374820 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term56 _104907 f p1) = (term56 _104907 f p1).
Proof. exact (eq_refl (term56 _104907 f p1)). Qed.
Lemma lem4374821 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term56 _104907 f p1) = (((term32 _104907 f p1) = (term32 _104907 f p1)) = True).
Proof. exact (eq_refl (term56 _104907 f p1)). Qed.
Lemma lem4374822 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term57 _104907 f p1) = (term57 _104907 f p1).
Proof. exact (eq_refl (term57 _104907 f p1)). Qed.
Lemma lem4374823 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : ((term56 _104907 f p1) = (term56 _104907 f p1)) = ((term56 _104907 f p1) = (((term32 _104907 f p1) = (term32 _104907 f p1)) = True)).
Proof. exact (MK_COMB (@lem4374822 _104907 f p1) (@lem4374821 _104907 f p1)). Qed.
Lemma lem4374824 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term56 _104907 f p1) = (((term32 _104907 f p1) = (term32 _104907 f p1)) = True).
Proof. exact (eq_refl (term56 _104907 f p1)). Qed.
Lemma lem4374825 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4374826 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term57 _104907 f p1) = (term58 _104907 f p1).
Proof. exact (MK_COMB (@lem4374825) (@lem4374824 _104907 f p1)). Qed.
Lemma lem4374827 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (((term32 _104907 f p1) = (term32 _104907 f p1)) = True) = (((term32 _104907 f p1) = (term32 _104907 f p1)) = True).
Proof. exact (eq_refl (((term32 _104907 f p1) = (term32 _104907 f p1)) = True)). Qed.
Lemma lem4374828 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : ((term56 _104907 f p1) = (((term32 _104907 f p1) = (term32 _104907 f p1)) = True)) = ((((term32 _104907 f p1) = (term32 _104907 f p1)) = True) = (((term32 _104907 f p1) = (term32 _104907 f p1)) = True)).
Proof. exact (MK_COMB (@lem4374826 _104907 f p1) (@lem4374827 _104907 f p1)). Qed.
Lemma lem4374829 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : ((term56 _104907 f p1) = (term56 _104907 f p1)) = ((((term32 _104907 f p1) = (term32 _104907 f p1)) = True) = (((term32 _104907 f p1) = (term32 _104907 f p1)) = True)).
Proof. exact (TRANS (@lem4374823 _104907 f p1) (@lem4374828 _104907 f p1)). Qed.
Lemma lem4374830 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (((term32 _104907 f p1) = (term32 _104907 f p1)) = True) = (((term32 _104907 f p1) = (term32 _104907 f p1)) = True).
Proof. exact (EQ_MP (@lem4374829 _104907 f p1) (@lem4374820 _104907 f p1)). Qed.
Lemma lem4374831 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : ((term32 _104907 f p1) = (term32 _104907 f p1)) = True.
Proof. exact (EQ_MP (@lem4374830 _104907 f p1) (@lem4374817 _104907 f p1)). Qed.
Lemma lem4374832 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (p2 : _104908) : ((term45 _104907 _104908 p1 f p2) = (term55 _104907 _104908 f p1 p2)) = True.
Proof. exact (TRANS (@lem4374813 _104907 _104908 p2 f p1) (@lem4374831 _104907 f p1)). Qed.
Lemma lem4374833 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) : (term59 _104907 _104908 f p1) = (term60 _104908).
Proof. exact (fun_ext (fun p2 : _104908 => @lem4374832 _104907 _104908 f p1 p2)). Qed.
Lemma lem4374834 {_104908 : Type'} : (@all _104908) = (@all _104908).
Proof. exact (eq_refl (@all _104908)). Qed.
Lemma lem4374835 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) : (term61 _104907 _104908 f p1) = (term62 _104908).
Proof. exact (MK_COMB (@lem4374834 _104908) (@lem4374833 _104907 _104908 f p1)). Qed.
Lemma lem4374837 {A : Type'} (t : Prop) : (term43 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4374838 {_104908 : Type'} (t : Prop) : (term43 _104908 t) = t.
Proof. exact (@lem4374837 _104908 t). Qed.
Lemma lem4374839 {_104908 : Type'} : (term62 _104908) = True.
Proof. exact (@lem4374838 _104908 True). Qed.
Lemma lem4374840 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) : (term61 _104907 _104908 f p1) = True.
Proof. exact (TRANS (@lem4374835 _104907 _104908 f p1) (@lem4374839 _104908)). Qed.
Lemma lem4374841 {_104907 _104908 : Type'} (f : type686 _104907) : (term63 _104907 _104908 f) = (term60 _104907).
Proof. exact (fun_ext (fun p1 : _104907 => @lem4374840 _104907 _104908 f p1)). Qed.
Lemma lem4374842 {_104907 : Type'} : (@all _104907) = (@all _104907).
Proof. exact (eq_refl (@all _104907)). Qed.
Lemma lem4374843 {_104907 _104908 : Type'} (f : type686 _104907) : (term11 _104907 _104908 f) = (term62 _104907).
Proof. exact (MK_COMB (@lem4374842 _104907) (@lem4374841 _104907 _104908 f)). Qed.
Lemma lem4374845 {A : Type'} (t : Prop) : (term43 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4374846 {_104907 : Type'} (t : Prop) : (term43 _104907 t) = t.
Proof. exact (@lem4374845 _104907 t). Qed.
Lemma lem4374847 {_104907 : Type'} : (term62 _104907) = True.
Proof. exact (@lem4374846 _104907 True). Qed.
Lemma lem4374848 {_104907 _104908 : Type'} (f : type686 _104907) : (term11 _104907 _104908 f) = True.
Proof. exact (TRANS (@lem4374843 _104907 _104908 f) (@lem4374847 _104907)). Qed.
Lemma lem4374849 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : (term13 _104907 _104908 g f) = (term64 _104907 _104908 g f).
Proof. exact (MK_COMB (@lem4374681 _104907 _104908 g f) (@lem4374848 _104907 _104908 f)). Qed.
Lemma lem4374851 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4374852 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : (term64 _104907 _104908 g f) = True.
Proof. exact (@lem4374851 (term22 _104907 _104908 g f)). Qed.
Lemma lem4374853 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : (term13 _104907 _104908 g f) = True.
Proof. exact (TRANS (@lem4374849 _104907 _104908 g f) (@lem4374852 _104907 _104908 g f)). Qed.
Lemma lem4374854 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : True = (term13 _104907 _104908 g f).
Proof. exact (SYM (@lem4374853 _104907 _104908 g f)). Qed.
Lemma lem4374855 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : term13 _104907 _104908 g f.
Proof. exact (EQ_MP (@lem4374854 _104907 _104908 g f) (@lem0)). Qed.
Lemma lem4374856 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : term12 _104907 _104908 g f.
Proof. exact (EQ_MP (@lem4374614 _104907 _104908 g f) (@lem4374855 _104907 _104908 g f)). Qed.
Lemma lem4374857 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (h1 : term0 _104907 f) (h2 : g = (@EMPTY (_104908 -> Prop))) : term11 _104907 _104908 f.
Proof. exact (@lem4374856 _104907 _104908 g f (@lem4374546 _104907 _104908 f g h1 h2)). Qed.
