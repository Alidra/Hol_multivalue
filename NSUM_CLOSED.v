Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_CLOSED_term_abbrevs.
Require Import ITERATE_CLOSED_spec.
Require Import MONOIDAL_ADD_spec.
Require Import nsum_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm4211_spec.
Require Import thm6920431_spec.
Require Import thm6921992_spec.
Require Import thm7_spec.
Lemma lem7028682 {_126417 : Type'} (h1 : (@nsum _126417) = (@iterate nat _126417 Nat.add)) : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (h1). Qed.
Lemma lem7028683 {_126417 : Type'} (h1 : (@nsum _126417) = (@iterate nat _126417 Nat.add)) : (@iterate nat _126417 Nat.add) = (@nsum _126417).
Proof. exact (SYM (@lem7028682 _126417 h1)). Qed.
Lemma lem7028684 {_126417 : Type'} (h1 : (@iterate nat _126417 Nat.add) = (@nsum _126417)) : (@iterate nat _126417 Nat.add) = (@nsum _126417).
Proof. exact (h1). Qed.
Lemma lem7028685 {_126417 : Type'} (h1 : (@iterate nat _126417 Nat.add) = (@nsum _126417)) : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (SYM (@lem7028684 _126417 h1)). Qed.
Lemma lem7028686 {_126417 : Type'} : ((@nsum _126417) = (@iterate nat _126417 Nat.add)) = ((@iterate nat _126417 Nat.add) = (@nsum _126417)).
Proof. exact (prop_ext (fun h1 : (@nsum _126417) = (@iterate nat _126417 Nat.add) => @lem7028683 _126417 h1) (fun h1 : (@iterate nat _126417 Nat.add) = (@nsum _126417) => @lem7028685 _126417 h1)). Qed.
Lemma lem7028688 {A B : Type'} (op : type1400 B) : term0 A B op.
Proof. exact (@lem5782566 A B op). Qed.
Lemma lem7028689 {A B : Type'} (op : type1400 B) : (term0 A B op) = (term1 A B op).
Proof. exact (eq_refl (term0 A B op)). Qed.
Lemma lem7028692 {A B : Type'} (op : type1400 B) : term1 A B op.
Proof. exact (EQ_MP (@lem7028689 A B op) (@lem7028688 A B op)). Qed.
Lemma lem7028693 {A : Type'} (op : type1606) : term2 A op.
Proof. exact (@lem7028692 A nat op). Qed.
Lemma lem7028694 {A : Type'} : term3 A.
Proof. exact (@lem7028693 A Nat.add). Qed.
Lemma lem7028695 {A : Type'} : term4 A.
Proof. exact (@lem7028694 A (@lem6924403)). Qed.
Lemma lem7028696 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term5 A s P f) : term5 A s P f.
Proof. exact (h1). Qed.
Lemma lem7028697 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term6 A s P f) : term6 A s P f.
Proof. exact (h1). Qed.
Lemma lem7028698 (P : nat -> Prop) (h1 : term7 P) : term7 P.
Proof. exact (h1). Qed.
Lemma lem7028699 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term8 A s P f) : term8 A s P f.
Proof. exact (h1). Qed.
Lemma lem7028700 (P : nat -> Prop) (h1 : term9 P) : term9 P.
Proof. exact (h1). Qed.
Lemma lem7028701 {A : Type'} (h1 : term4 A) : term4 A.
Proof. exact (h1). Qed.
Lemma lem7028702 {A : Type'} (P : nat -> Prop) (h1 : term4 A) : term10 A P.
Proof. exact (@lem7028701 A h1 P). Qed.
Lemma lem7028703 {A : Type'} (P : nat -> Prop) : (term10 A P) = (term11 A P).
Proof. exact (eq_refl (term10 A P)). Qed.
Lemma lem7028704 {A : Type'} (P : nat -> Prop) (h1 : term4 A) : term11 A P.
Proof. exact (EQ_MP (@lem7028703 A P) (@lem7028702 A P h1)). Qed.
Lemma lem7028705 (P : nat -> Prop) : (term7 P) = ((term7 P) = True).
Proof. exact (@lem7 (term7 P)). Qed.
Lemma lem7028707 (x : nat) (P : nat -> Prop) (h1 : term9 P) : term12 P x.
Proof. exact (@lem7028700 P h1 x). Qed.
Lemma lem7028708 (P : nat -> Prop) (x : nat) : (term12 P x) = (term13 P x).
Proof. exact (eq_refl (term12 P x)). Qed.
Lemma lem7028709 (x : nat) (P : nat -> Prop) (h1 : term9 P) : term13 P x.
Proof. exact (EQ_MP (@lem7028708 P x) (@lem7028707 x P h1)). Qed.
Lemma lem7028710 (x : nat) (y : nat) (P : nat -> Prop) (h1 : term9 P) : term14 P x y.
Proof. exact (@lem7028709 x P h1 y). Qed.
Lemma lem7028711 (P : nat -> Prop) (x : nat) (y : nat) : (term14 P x y) = (term15 P x y).
Proof. exact (eq_refl (term14 P x y)). Qed.
Lemma lem7028712 (x : nat) (y : nat) (P : nat -> Prop) (h1 : term9 P) : term15 P x y.
Proof. exact (EQ_MP (@lem7028711 P x y) (@lem7028710 x y P h1)). Qed.
Lemma lem7028713 (x : nat) (P : nat -> Prop) (y : nat) (h1 : term16 x P y) : term16 x P y.
Proof. exact (h1). Qed.
Lemma lem7028714 (x : nat) (P : nat -> Prop) (y : nat) (h1 : term9 P) (h2 : term16 x P y) : term17 P x y.
Proof. exact (@lem7028712 x y P h1 (@lem7028713 x P y h2)). Qed.
Lemma lem7028715 (P : nat -> Prop) (x : nat) (y : nat) : (term17 P x y) = ((term17 P x y) = True).
Proof. exact (@lem7 (term17 P x y)). Qed.
Lemma lem7028716 (x : nat) (P : nat -> Prop) (y : nat) (h1 : term9 P) (h2 : term16 x P y) : (term17 P x y) = True.
Proof. exact (EQ_MP (@lem7028715 P x y) (@lem7028714 x P y h1 h2)). Qed.
Lemma lem7028722 {A : Type'} (a : A) (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term8 A s P f) : term18 A s P f a.
Proof. exact (@lem7028699 A s P f h1 a). Qed.
Lemma lem7028723 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (a : A) : (term18 A s P f a) = (term19 A s P f a).
Proof. exact (eq_refl (term18 A s P f a)). Qed.
Lemma lem7028724 {A : Type'} (a : A) (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term8 A s P f) : term19 A s P f a.
Proof. exact (EQ_MP (@lem7028723 A s P f a) (@lem7028722 A a s P f h1)). Qed.
Lemma lem7028725 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : @IN A a s.
Proof. exact (h1). Qed.
Lemma lem7028726 {A : Type'} (P : nat -> Prop) (f : A -> nat) (a : A) (s : A -> Prop) (h1 : term8 A s P f) (h2 : @IN A a s) : term20 A P f a.
Proof. exact (@lem7028724 A a s P f h1 (@lem7028725 A a s h2)). Qed.
Lemma lem7028727 {A : Type'} (P : nat -> Prop) (f : A -> nat) (a : A) : (term20 A P f a) = ((term20 A P f a) = True).
Proof. exact (@lem7 (term20 A P f a)). Qed.
Lemma lem7028728 {A : Type'} (P : nat -> Prop) (f : A -> nat) (a : A) (s : A -> Prop) (h1 : term8 A s P f) (h2 : @IN A a s) : (term20 A P f a) = True.
Proof. exact (EQ_MP (@lem7028727 A P f a) (@lem7028726 A P f a s h1 h2)). Qed.
Lemma lem7028737 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7028738 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem7028737 p q p' q'). Qed.
Lemma lem7028739 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem7028738 p q p'). Qed.
Lemma lem7028740 {A : Type'} (P : nat -> Prop) (s : A -> Prop) (f : A -> nat) : term24 A P s f.
Proof. exact (@lem7028739 (term11 A P) (term25 A P s f)). Qed.
Lemma lem7028741 {A : Type'} (P : nat -> Prop) (s : A -> Prop) (f : A -> nat) (p' : Prop) : term26 A P s f p'.
Proof. exact (@lem7028740 A P s f p'). Qed.
Lemma lem7028742 {A : Type'} (P : nat -> Prop) (s : A -> Prop) (f : A -> nat) (p' : Prop) : (term26 A P s f p') = (term27 A P s f p').
Proof. exact (eq_refl (term26 A P s f p')). Qed.
Lemma lem7028743 {A : Type'} (P : nat -> Prop) (s : A -> Prop) (f : A -> nat) (p' : Prop) : term27 A P s f p'.
Proof. exact (EQ_MP (@lem7028742 A P s f p') (@lem7028741 A P s f p')). Qed.
Lemma lem7028744 {A : Type'} (P : nat -> Prop) (s : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : term28 A P s f p' q'.
Proof. exact (@lem7028743 A P s f p' q'). Qed.
Lemma lem7028745 {A : Type'} (P : nat -> Prop) (s : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : (term28 A P s f p' q') = (term29 A P s f p' q').
Proof. exact (eq_refl (term28 A P s f p' q')). Qed.
Lemma lem7028746 {A : Type'} (P : nat -> Prop) (s : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : term29 A P s f p' q'.
Proof. exact (EQ_MP (@lem7028745 A P s f p' q') (@lem7028744 A P s f p' q')). Qed.
Lemma lem7028750 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7028751 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem7028750 p q p' q'). Qed.
Lemma lem7028752 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem7028751 p q p'). Qed.
Lemma lem7028753 {A : Type'} (P : nat -> Prop) : term30 A P.
Proof. exact (@lem7028752 (term31 P) (term32 A P)). Qed.
Lemma lem7028754 {A : Type'} (P : nat -> Prop) (p' : Prop) : term33 A P p'.
Proof. exact (@lem7028753 A P p'). Qed.
Lemma lem7028755 {A : Type'} (P : nat -> Prop) (p' : Prop) : (term33 A P p') = (term34 A P p').
Proof. exact (eq_refl (term33 A P p')). Qed.
Lemma lem7028756 {A : Type'} (P : nat -> Prop) (p' : Prop) : term34 A P p'.
Proof. exact (EQ_MP (@lem7028755 A P p') (@lem7028754 A P p')). Qed.
Lemma lem7028757 {A : Type'} (P : nat -> Prop) (p' : Prop) (q' : Prop) : term35 A P p' q'.
Proof. exact (@lem7028756 A P p' q'). Qed.
Lemma lem7028758 {A : Type'} (P : nat -> Prop) (p' : Prop) (q' : Prop) : (term35 A P p' q') = (term36 A P p' q').
Proof. exact (eq_refl (term35 A P p' q')). Qed.
Lemma lem7028759 {A : Type'} (P : nat -> Prop) (p' : Prop) (q' : Prop) : term36 A P p' q'.
Proof. exact (EQ_MP (@lem7028758 A P p' q') (@lem7028757 A P p' q')). Qed.
Lemma lem7028763 : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6920431) (@lem6921992)). Qed.
Lemma lem7028764 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem7028765 (P : nat -> Prop) : (term37 P) = (term7 P).
Proof. exact (MK_COMB (@lem7028764 P) (@lem7028763)). Qed.
Lemma lem7028767 (P : nat -> Prop) (h1 : term7 P) : (term7 P) = True.
Proof. exact (EQ_MP (@lem7028705 P) (@lem7028698 P h1)). Qed.
Lemma lem7028768 (P : nat -> Prop) (h1 : term7 P) : (term37 P) = True.
Proof. exact (TRANS (@lem7028765 P) (@lem7028767 P h1)). Qed.
Lemma lem7028769 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7028770 (P : nat -> Prop) (h1 : term7 P) : (term38 P) = (and True).
Proof. exact (MK_COMB (@lem7028769) (@lem7028768 P h1)). Qed.
Lemma lem7028782 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7028783 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem7028782 p q p' q'). Qed.
Lemma lem7028784 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem7028783 p q p'). Qed.
Lemma lem7028785 (P : nat -> Prop) (x : nat) (y : nat) : term39 P x y.
Proof. exact (@lem7028784 (term16 x P y) (term17 P x y)). Qed.
Lemma lem7028786 (P : nat -> Prop) (x : nat) (y : nat) (p' : Prop) : term40 P x y p'.
Proof. exact (@lem7028785 P x y p'). Qed.
Lemma lem7028787 (P : nat -> Prop) (x : nat) (y : nat) (p' : Prop) : (term40 P x y p') = (term41 P x y p').
Proof. exact (eq_refl (term40 P x y p')). Qed.
Lemma lem7028788 (P : nat -> Prop) (x : nat) (y : nat) (p' : Prop) : term41 P x y p'.
Proof. exact (EQ_MP (@lem7028787 P x y p') (@lem7028786 P x y p')). Qed.
Lemma lem7028789 (P : nat -> Prop) (x : nat) (y : nat) (p' : Prop) (q' : Prop) : term42 P x y p' q'.
Proof. exact (@lem7028788 P x y p' q'). Qed.
Lemma lem7028790 (P : nat -> Prop) (x : nat) (y : nat) (p' : Prop) (q' : Prop) : (term42 P x y p' q') = (term43 P x y p' q').
Proof. exact (eq_refl (term42 P x y p' q')). Qed.
Lemma lem7028791 (P : nat -> Prop) (x : nat) (y : nat) (p' : Prop) (q' : Prop) : term43 P x y p' q'.
Proof. exact (EQ_MP (@lem7028790 P x y p' q') (@lem7028789 P x y p' q')). Qed.
Lemma lem7028794 (x : nat) (P : nat -> Prop) (y : nat) : (term16 x P y) = (term16 x P y).
Proof. exact (eq_refl (term16 x P y)). Qed.
Lemma lem7028795 (x : nat) (P : nat -> Prop) (y : nat) (q' : Prop) : term44 x P y q'.
Proof. exact (@lem7028791 P x y (term16 x P y) q'). Qed.
Lemma lem7028796 (x : nat) (P : nat -> Prop) (y : nat) (q' : Prop) : term45 x P y q'.
Proof. exact (@lem7028795 x P y q' (@lem7028794 x P y)). Qed.
Lemma lem7028797 (x : nat) (P : nat -> Prop) (y : nat) (h1 : term16 x P y) : term16 x P y.
Proof. exact (h1). Qed.
Lemma lem7028798 (x : nat) (P : nat -> Prop) (y : nat) (h1 : term16 x P y) : P y.
Proof. exact (proj2 (@lem7028797 x P y h1)). Qed.
Lemma lem7028799 (P : nat -> Prop) (y : nat) : (P y) = ((P y) = True).
Proof. exact (@lem7 (P y)). Qed.
Lemma lem7028801 (x : nat) (P : nat -> Prop) (y : nat) (h1 : term16 x P y) : P x.
Proof. exact (proj1 (@lem7028797 x P y h1)). Qed.
Lemma lem7028802 (P : nat -> Prop) (x : nat) : (P x) = ((P x) = True).
Proof. exact (@lem7 (P x)). Qed.
Lemma lem7028805 (x : nat) (y : nat) (P : nat -> Prop) (h1 : term9 P) : term46 P x y.
Proof. exact (fun h0 : term16 x P y => @lem7028716 x P y h1 h0). Qed.
Lemma lem7028809 (x : nat) (P : nat -> Prop) (y : nat) (h1 : term16 x P y) : (P x) = True.
Proof. exact (EQ_MP (@lem7028802 P x) (@lem7028801 x P y h1)). Qed.
Lemma lem7028810 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7028811 (x : nat) (P : nat -> Prop) (y : nat) (h1 : term16 x P y) : (term47 P x) = (and True).
Proof. exact (MK_COMB (@lem7028810) (@lem7028809 x P y h1)). Qed.
Lemma lem7028813 (x : nat) (P : nat -> Prop) (y : nat) (h1 : term16 x P y) : (P y) = True.
Proof. exact (EQ_MP (@lem7028799 P y) (@lem7028798 x P y h1)). Qed.
Lemma lem7028814 (x : nat) (P : nat -> Prop) (y : nat) (h1 : term16 x P y) : (term16 x P y) = (True /\ True).
Proof. exact (MK_COMB (@lem7028811 x P y h1) (@lem7028813 x P y h1)). Qed.
Lemma lem7028816 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7028817 : (True /\ True) = True.
Proof. exact (@lem7028816 True). Qed.
Lemma lem7028818 (x : nat) (P : nat -> Prop) (y : nat) (h1 : term16 x P y) : (term16 x P y) = True.
Proof. exact (TRANS (@lem7028814 x P y h1) (@lem7028817)). Qed.
Lemma lem7028819 (x : nat) (P : nat -> Prop) (y : nat) (h1 : term16 x P y) : True = (term16 x P y).
Proof. exact (SYM (@lem7028818 x P y h1)). Qed.
Lemma lem7028820 (x : nat) (P : nat -> Prop) (y : nat) (h1 : term16 x P y) : term16 x P y.
Proof. exact (EQ_MP (@lem7028819 x P y h1) (@lem0)). Qed.
Lemma lem7028821 (x : nat) (P : nat -> Prop) (y : nat) (h1 : term9 P) (h2 : term16 x P y) : (term17 P x y) = True.
Proof. exact (@lem7028805 x y P h1 (@lem7028820 x P y h2)). Qed.
Lemma lem7028822 (x : nat) (y : nat) (P : nat -> Prop) (h1 : term9 P) : term46 P x y.
Proof. exact (fun h0 : term16 x P y => @lem7028821 x P y h1 h0). Qed.
Lemma lem7028823 (x : nat) (P : nat -> Prop) (y : nat) : term48 x P y.
Proof. exact (@lem7028796 x P y True). Qed.
Lemma lem7028824 (x : nat) (y : nat) (P : nat -> Prop) (h1 : term9 P) : (term15 P x y) = (term49 x P y).
Proof. exact (@lem7028823 x P y (@lem7028822 x y P h1)). Qed.
Lemma lem7028826 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7028827 (x : nat) (P : nat -> Prop) (y : nat) : (term49 x P y) = True.
Proof. exact (@lem7028826 (term16 x P y)). Qed.
Lemma lem7028828 (x : nat) (y : nat) (P : nat -> Prop) (h1 : term9 P) : (term15 P x y) = True.
Proof. exact (TRANS (@lem7028824 x y P h1) (@lem7028827 x P y)). Qed.
Lemma lem7028829 (x : nat) (P : nat -> Prop) (h1 : term9 P) : (term50 P x) = term51.
Proof. exact (fun_ext (fun y : nat => @lem7028828 x y P h1)). Qed.
Lemma lem7028830 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7028831 (x : nat) (P : nat -> Prop) (h1 : term9 P) : (term13 P x) = term52.
Proof. exact (MK_COMB (@lem7028830) (@lem7028829 x P h1)). Qed.
Lemma lem7028833 {A : Type'} (t : Prop) : (term53 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7028834 (t : Prop) : (term54 t) = t.
Proof. exact (@lem7028833 nat t). Qed.
Lemma lem7028835 : term52 = True.
Proof. exact (@lem7028834 True). Qed.
Lemma lem7028836 (x : nat) (P : nat -> Prop) (h1 : term9 P) : (term13 P x) = True.
Proof. exact (TRANS (@lem7028831 x P h1) (@lem7028835)). Qed.
Lemma lem7028837 (P : nat -> Prop) (h1 : term9 P) : (term55 P) = term51.
Proof. exact (fun_ext (fun x : nat => @lem7028836 x P h1)). Qed.
Lemma lem7028838 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7028839 (P : nat -> Prop) (h1 : term9 P) : (term9 P) = term52.
Proof. exact (MK_COMB (@lem7028838) (@lem7028837 P h1)). Qed.
Lemma lem7028841 {A : Type'} (t : Prop) : (term53 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7028842 (t : Prop) : (term54 t) = t.
Proof. exact (@lem7028841 nat t). Qed.
Lemma lem7028843 : term52 = True.
Proof. exact (@lem7028842 True). Qed.
Lemma lem7028844 (P : nat -> Prop) (h1 : term9 P) : (term9 P) = True.
Proof. exact (TRANS (@lem7028839 P h1) (@lem7028843)). Qed.
Lemma lem7028845 (P : nat -> Prop) (h1 : term9 P) (h2 : term7 P) : (term31 P) = (True /\ True).
Proof. exact (MK_COMB (@lem7028770 P h2) (@lem7028844 P h1)). Qed.
Lemma lem7028847 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7028848 : (True /\ True) = True.
Proof. exact (@lem7028847 True). Qed.
Lemma lem7028849 (P : nat -> Prop) (h1 : term9 P) (h2 : term7 P) : (term31 P) = True.
Proof. exact (TRANS (@lem7028845 P h1 h2) (@lem7028848)). Qed.
Lemma lem7028850 {A : Type'} (P : nat -> Prop) (q' : Prop) : term56 A P q'.
Proof. exact (@lem7028759 A P True q'). Qed.
Lemma lem7028851 {A : Type'} (q' : Prop) (P : nat -> Prop) (h1 : term9 P) (h2 : term7 P) : term57 A P q'.
Proof. exact (@lem7028850 A P q' (@lem7028849 P h1 h2)). Qed.
Lemma lem7028995 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7028996 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem7028995 p q p' q'). Qed.
Lemma lem7028997 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem7028996 p q p'). Qed.
Lemma lem7028998 {A : Type'} (P : nat -> Prop) (_93883 : A -> Prop) (f : A -> nat) : term58 A P _93883 f.
Proof. exact (@lem7028997 (term59 A _93883 P f) (term60 A P _93883 f)). Qed.
Lemma lem7028999 {A : Type'} (P : nat -> Prop) (_93883 : A -> Prop) (f : A -> nat) (p' : Prop) : term61 A P _93883 f p'.
Proof. exact (@lem7028998 A P _93883 f p'). Qed.
Lemma lem7029000 {A : Type'} (P : nat -> Prop) (_93883 : A -> Prop) (f : A -> nat) (p' : Prop) : (term61 A P _93883 f p') = (term62 A P _93883 f p').
Proof. exact (eq_refl (term61 A P _93883 f p')). Qed.
Lemma lem7029001 {A : Type'} (P : nat -> Prop) (_93883 : A -> Prop) (f : A -> nat) (p' : Prop) : term62 A P _93883 f p'.
Proof. exact (EQ_MP (@lem7029000 A P _93883 f p') (@lem7028999 A P _93883 f p')). Qed.
Lemma lem7029002 {A : Type'} (P : nat -> Prop) (_93883 : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : term63 A P _93883 f p' q'.
Proof. exact (@lem7029001 A P _93883 f p' q'). Qed.
Lemma lem7029003 {A : Type'} (P : nat -> Prop) (_93883 : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : (term63 A P _93883 f p' q') = (term64 A P _93883 f p' q').
Proof. exact (eq_refl (term63 A P _93883 f p' q')). Qed.
Lemma lem7029004 {A : Type'} (P : nat -> Prop) (_93883 : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : term64 A P _93883 f p' q'.
Proof. exact (EQ_MP (@lem7029003 A P _93883 f p' q') (@lem7029002 A P _93883 f p' q')). Qed.
Lemma lem7029012 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7029013 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem7029012 p q p' q'). Qed.
Lemma lem7029014 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem7029013 p q p'). Qed.
Lemma lem7029015 {A : Type'} (_93883 : A -> Prop) (P : nat -> Prop) (f : A -> nat) (x : A) : term65 A _93883 P f x.
Proof. exact (@lem7029014 (term66 A _93883 f x) (term20 A P f x)). Qed.
Lemma lem7029016 {A : Type'} (_93883 : A -> Prop) (P : nat -> Prop) (f : A -> nat) (x : A) (p' : Prop) : term67 A _93883 P f x p'.
Proof. exact (@lem7029015 A _93883 P f x p'). Qed.
Lemma lem7029017 {A : Type'} (_93883 : A -> Prop) (P : nat -> Prop) (f : A -> nat) (x : A) (p' : Prop) : (term67 A _93883 P f x p') = (term68 A _93883 P f x p').
Proof. exact (eq_refl (term67 A _93883 P f x p')). Qed.
Lemma lem7029018 {A : Type'} (_93883 : A -> Prop) (P : nat -> Prop) (f : A -> nat) (x : A) (p' : Prop) : term68 A _93883 P f x p'.
Proof. exact (EQ_MP (@lem7029017 A _93883 P f x p') (@lem7029016 A _93883 P f x p')). Qed.
Lemma lem7029019 {A : Type'} (_93883 : A -> Prop) (P : nat -> Prop) (f : A -> nat) (x : A) (p' : Prop) (q' : Prop) : term69 A _93883 P f x p' q'.
Proof. exact (@lem7029018 A _93883 P f x p' q'). Qed.
Lemma lem7029020 {A : Type'} (_93883 : A -> Prop) (P : nat -> Prop) (f : A -> nat) (x : A) (p' : Prop) (q' : Prop) : (term69 A _93883 P f x p' q') = (term70 A _93883 P f x p' q').
Proof. exact (eq_refl (term69 A _93883 P f x p' q')). Qed.
Lemma lem7029021 {A : Type'} (_93883 : A -> Prop) (P : nat -> Prop) (f : A -> nat) (x : A) (p' : Prop) (q' : Prop) : term70 A _93883 P f x p' q'.
Proof. exact (EQ_MP (@lem7029020 A _93883 P f x p' q') (@lem7029019 A _93883 P f x p' q')). Qed.
Lemma lem7029027 : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6920431) (@lem6921992)). Qed.
Lemma lem7029028 {A : Type'} (f : A -> nat) (x : A) : (term71 A f x) = (term71 A f x).
Proof. exact (eq_refl (term71 A f x)). Qed.
Lemma lem7029029 {A : Type'} (f : A -> nat) (x : A) : ((f x) = (@neutral nat Nat.add)) = ((f x) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem7029028 A f x) (@lem7029027)). Qed.
Lemma lem7029032 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7029033 {A : Type'} (f : A -> nat) (x : A) : (term72 A f x) = (term73 A f x).
Proof. exact (MK_COMB (@lem7029032) (@lem7029029 A f x)). Qed.
Lemma lem7029036 {A : Type'} (x : A) (_93883 : A -> Prop) : (term74 A x _93883) = (term74 A x _93883).
Proof. exact (eq_refl (term74 A x _93883)). Qed.
Lemma lem7029037 {A : Type'} (_93883 : A -> Prop) (f : A -> nat) (x : A) : (term66 A _93883 f x) = (term75 A _93883 f x).
Proof. exact (MK_COMB (@lem7029036 A x _93883) (@lem7029033 A f x)). Qed.
Lemma lem7029042 {A : Type'} (P : nat -> Prop) (_93883 : A -> Prop) (f : A -> nat) (x : A) (q' : Prop) : term76 A P _93883 f x q'.
Proof. exact (@lem7029021 A _93883 P f x (term75 A _93883 f x) q'). Qed.
Lemma lem7029043 {A : Type'} (P : nat -> Prop) (_93883 : A -> Prop) (f : A -> nat) (x : A) (q' : Prop) : term77 A P _93883 f x q'.
Proof. exact (@lem7029042 A P _93883 f x q' (@lem7029037 A _93883 f x)). Qed.
Lemma lem7029068 {A : Type'} (P : nat -> Prop) (f : A -> nat) (x : A) : (term20 A P f x) = (term20 A P f x).
Proof. exact (eq_refl (term20 A P f x)). Qed.
Lemma lem7029069 {A : Type'} (_93883 : A -> Prop) (P : nat -> Prop) (f : A -> nat) (x : A) : term78 A _93883 P f x.
Proof. exact (fun h0 : term75 A _93883 f x => @lem7029068 A P f x). Qed.
Lemma lem7029070 {A : Type'} (_93883 : A -> Prop) (P : nat -> Prop) (f : A -> nat) (x : A) : term79 A _93883 P f x.
Proof. exact (@lem7029043 A P _93883 f x (term20 A P f x)). Qed.
Lemma lem7029071 {A : Type'} (_93883 : A -> Prop) (P : nat -> Prop) (f : A -> nat) (x : A) : (term80 A _93883 P f x) = (term81 A _93883 P f x).
Proof. exact (@lem7029070 A _93883 P f x (@lem7029069 A _93883 P f x)). Qed.
Lemma lem7029130 {A : Type'} (_93883 : A -> Prop) (P : nat -> Prop) (f : A -> nat) : (term82 A _93883 P f) = (term83 A _93883 P f).
Proof. exact (fun_ext (fun x : A => @lem7029071 A _93883 P f x)). Qed.
Lemma lem7029189 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7029190 {A : Type'} (_93883 : A -> Prop) (P : nat -> Prop) (f : A -> nat) : (term59 A _93883 P f) = (term84 A _93883 P f).
Proof. exact (MK_COMB (@lem7029189 A) (@lem7029130 A _93883 P f)). Qed.
Lemma lem7029253 {A : Type'} (_93883 : A -> Prop) (P : nat -> Prop) (f : A -> nat) (q' : Prop) : term85 A _93883 P f q'.
Proof. exact (@lem7029004 A P _93883 f (term84 A _93883 P f) q'). Qed.
Lemma lem7029254 {A : Type'} (_93883 : A -> Prop) (P : nat -> Prop) (f : A -> nat) (q' : Prop) : term86 A _93883 P f q'.
Proof. exact (@lem7029253 A _93883 P f q' (@lem7029190 A _93883 P f)). Qed.
Lemma lem7029269 {_126417 : Type'} : (@iterate nat _126417 Nat.add) = (@nsum _126417).
Proof. exact (EQ_MP (@lem7028686 _126417) (@lem6920372 _126417)). Qed.
Lemma lem7029270 {A : Type'} : (@iterate nat A Nat.add) = (@nsum A).
Proof. exact (@lem7029269 A). Qed.
Lemma lem7029271 {A : Type'} (_93883 : A -> Prop) : _93883 = _93883.
Proof. exact (eq_refl _93883). Qed.
Lemma lem7029272 {A : Type'} (_93883 : A -> Prop) : (@iterate nat A Nat.add _93883) = (@nsum A _93883).
Proof. exact (MK_COMB (@lem7029270 A) (@lem7029271 A _93883)). Qed.
Lemma lem7029273 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7029274 {A : Type'} (_93883 : A -> Prop) (f : A -> nat) : (@iterate nat A Nat.add _93883 f) = (@nsum A _93883 f).
Proof. exact (MK_COMB (@lem7029272 A _93883) (@lem7029273 A f)). Qed.
Lemma lem7029275 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem7029276 {A : Type'} (P : nat -> Prop) (_93883 : A -> Prop) (f : A -> nat) : (term60 A P _93883 f) = (term25 A P _93883 f).
Proof. exact (MK_COMB (@lem7029275 P) (@lem7029274 A _93883 f)). Qed.
Lemma lem7029277 {A : Type'} (P : nat -> Prop) (_93883 : A -> Prop) (f : A -> nat) : term87 A P _93883 f.
Proof. exact (fun h0 : term84 A _93883 P f => @lem7029276 A P _93883 f). Qed.
Lemma lem7029278 {A : Type'} (P : nat -> Prop) (_93883 : A -> Prop) (f : A -> nat) : term88 A P _93883 f.
Proof. exact (@lem7029254 A _93883 P f (term25 A P _93883 f)). Qed.
Lemma lem7029279 {A : Type'} (P : nat -> Prop) (_93883 : A -> Prop) (f : A -> nat) : (term89 A P _93883 f) = (term90 A P _93883 f).
Proof. exact (@lem7029278 A P _93883 f (@lem7029277 A P _93883 f)). Qed.
Lemma lem7029439 {A : Type'} (P : nat -> Prop) (f : A -> nat) : (term91 A P f) = (term92 A P f).
Proof. exact (fun_ext (fun _93883 : A -> Prop => @lem7029279 A P _93883 f)). Qed.
Lemma lem7029701 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7029702 {A : Type'} (P : nat -> Prop) (f : A -> nat) : (term93 A P f) = (term94 A P f).
Proof. exact (MK_COMB (@lem7029701 A) (@lem7029439 A P f)). Qed.
Lemma lem7029968 {A : Type'} (P : nat -> Prop) : (term95 A P) = (term96 A P).
Proof. exact (fun_ext (fun f : A -> nat => @lem7029702 A P f)). Qed.
Lemma lem7030234 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7030235 {A : Type'} (P : nat -> Prop) : (term32 A P) = (term97 A P).
Proof. exact (MK_COMB (@lem7030234 A) (@lem7029968 A P)). Qed.
Lemma lem7030505 {A : Type'} (P : nat -> Prop) : term98 A P.
Proof. exact (fun h0 : True => @lem7030235 A P). Qed.
Lemma lem7030506 {A : Type'} (P : nat -> Prop) (h1 : term9 P) (h2 : term7 P) : term99 A P.
Proof. exact (@lem7028851 A (term97 A P) P h1 h2). Qed.
Lemma lem7030507 {A : Type'} (P : nat -> Prop) (h1 : term9 P) (h2 : term7 P) : (term11 A P) = (term100 A P).
Proof. exact (@lem7030506 A P h1 h2 (@lem7030505 A P)). Qed.
Lemma lem7030509 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem7030510 {A : Type'} (P : nat -> Prop) : (term100 A P) = (term97 A P).
Proof. exact (@lem7030509 (term97 A P)). Qed.
Lemma lem7030770 {A : Type'} (P : nat -> Prop) (h1 : term9 P) (h2 : term7 P) : (term11 A P) = (term97 A P).
Proof. exact (TRANS (@lem7030507 A P h1 h2) (@lem7030510 A P)). Qed.
Lemma lem7030771 {A : Type'} (s : A -> Prop) (f : A -> nat) (P : nat -> Prop) (q' : Prop) : term101 A s f P q'.
Proof. exact (@lem7028746 A P s f (term97 A P) q'). Qed.
Lemma lem7030772 {A : Type'} (s : A -> Prop) (f : A -> nat) (q' : Prop) (P : nat -> Prop) (h1 : term9 P) (h2 : term7 P) : term102 A s f P q'.
Proof. exact (@lem7030771 A s f P q' (@lem7030770 A P h1 h2)). Qed.
Lemma lem7030773 {A : Type'} (P : nat -> Prop) (h1 : term97 A P) : term97 A P.
Proof. exact (h1). Qed.
Lemma lem7030774 {A : Type'} (f : A -> nat) (P : nat -> Prop) (h1 : term97 A P) : term103 A P f.
Proof. exact (@lem7030773 A P h1 f). Qed.
Lemma lem7030775 {A : Type'} (P : nat -> Prop) (f : A -> nat) : (term103 A P f) = (term94 A P f).
Proof. exact (eq_refl (term103 A P f)). Qed.
Lemma lem7030776 {A : Type'} (f : A -> nat) (P : nat -> Prop) (h1 : term97 A P) : term94 A P f.
Proof. exact (EQ_MP (@lem7030775 A P f) (@lem7030774 A f P h1)). Qed.
Lemma lem7030777 {A : Type'} (f : A -> nat) (s : A -> Prop) (P : nat -> Prop) (h1 : term97 A P) : term104 A P f s.
Proof. exact (@lem7030776 A f P h1 s). Qed.
Lemma lem7030778 {A : Type'} (P : nat -> Prop) (s : A -> Prop) (f : A -> nat) : (term104 A P f s) = (term90 A P s f).
Proof. exact (eq_refl (term104 A P f s)). Qed.
Lemma lem7030779 {A : Type'} (s : A -> Prop) (f : A -> nat) (P : nat -> Prop) (h1 : term97 A P) : term90 A P s f.
Proof. exact (EQ_MP (@lem7030778 A P s f) (@lem7030777 A f s P h1)). Qed.
Lemma lem7030780 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term84 A s P f) : term84 A s P f.
Proof. exact (h1). Qed.
Lemma lem7030781 {A : Type'} (s : A -> Prop) (f : A -> nat) (P : nat -> Prop) (h1 : term84 A s P f) (h2 : term97 A P) : term25 A P s f.
Proof. exact (@lem7030779 A s f P h2 (@lem7030780 A s P f h1)). Qed.
Lemma lem7030782 {A : Type'} (P : nat -> Prop) (s : A -> Prop) (f : A -> nat) : (term25 A P s f) = ((term25 A P s f) = True).
Proof. exact (@lem7 (term25 A P s f)). Qed.
Lemma lem7030783 {A : Type'} (s : A -> Prop) (f : A -> nat) (P : nat -> Prop) (h1 : term84 A s P f) (h2 : term97 A P) : (term25 A P s f) = True.
Proof. exact (EQ_MP (@lem7030782 A P s f) (@lem7030781 A s f P h1 h2)). Qed.
Lemma lem7030790 {A : Type'} (s : A -> Prop) (f : A -> nat) (P : nat -> Prop) (h1 : term97 A P) : term105 A P s f.
Proof. exact (fun h0 : term84 A s P f => @lem7030783 A s f P h0 h1). Qed.
Lemma lem7030791 {A : Type'} (s : A -> Prop) (f : A -> nat) (P : nat -> Prop) (h1 : term97 A P) : term105 A P s f.
Proof. exact (@lem7030790 A s f P h1). Qed.
Lemma lem7030799 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7030800 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem7030799 p q p' q'). Qed.
Lemma lem7030801 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem7030800 p q p'). Qed.
Lemma lem7030802 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (x : A) : term106 A s P f x.
Proof. exact (@lem7030801 (term75 A s f x) (term20 A P f x)). Qed.
Lemma lem7030803 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (x : A) (p' : Prop) : term107 A s P f x p'.
Proof. exact (@lem7030802 A s P f x p'). Qed.
Lemma lem7030804 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (x : A) (p' : Prop) : (term107 A s P f x p') = (term108 A s P f x p').
Proof. exact (eq_refl (term107 A s P f x p')). Qed.
Lemma lem7030805 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (x : A) (p' : Prop) : term108 A s P f x p'.
Proof. exact (EQ_MP (@lem7030804 A s P f x p') (@lem7030803 A s P f x p')). Qed.
Lemma lem7030806 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (x : A) (p' : Prop) (q' : Prop) : term109 A s P f x p' q'.
Proof. exact (@lem7030805 A s P f x p' q'). Qed.
Lemma lem7030807 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (x : A) (p' : Prop) (q' : Prop) : (term109 A s P f x p' q') = (term110 A s P f x p' q').
Proof. exact (eq_refl (term109 A s P f x p' q')). Qed.
Lemma lem7030808 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (x : A) (p' : Prop) (q' : Prop) : term110 A s P f x p' q'.
Proof. exact (EQ_MP (@lem7030807 A s P f x p' q') (@lem7030806 A s P f x p' q')). Qed.
Lemma lem7030813 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term75 A s f x) = (term75 A s f x).
Proof. exact (eq_refl (term75 A s f x)). Qed.
Lemma lem7030814 {A : Type'} (P : nat -> Prop) (s : A -> Prop) (f : A -> nat) (x : A) (q' : Prop) : term111 A P s f x q'.
Proof. exact (@lem7030808 A s P f x (term75 A s f x) q'). Qed.
Lemma lem7030815 {A : Type'} (P : nat -> Prop) (s : A -> Prop) (f : A -> nat) (x : A) (q' : Prop) : term112 A P s f x q'.
Proof. exact (@lem7030814 A P s f x q' (@lem7030813 A s f x)). Qed.
Lemma lem7030816 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (h1 : term75 A s f x) : term75 A s f x.
Proof. exact (h1). Qed.
Lemma lem7030831 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (h1 : term75 A s f x) : @IN A x s.
Proof. exact (proj1 (@lem7030816 A s f x h1)). Qed.
Lemma lem7030832 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@IN A x s) = True).
Proof. exact (@lem7 (@IN A x s)). Qed.
Lemma lem7030835 {A : Type'} (a : A) (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term8 A s P f) : term113 A s P f a.
Proof. exact (fun h0 : @IN A a s => @lem7028728 A P f a s h1 h0). Qed.
Lemma lem7030836 {A : Type'} (a : A) (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term8 A s P f) : term113 A s P f a.
Proof. exact (@lem7030835 A a s P f h1). Qed.
Lemma lem7030837 {A : Type'} (x : A) (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term8 A s P f) : term113 A s P f x.
Proof. exact (@lem7030836 A x s P f h1). Qed.
Lemma lem7030839 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (h1 : term75 A s f x) : (@IN A x s) = True.
Proof. exact (EQ_MP (@lem7030832 A x s) (@lem7030831 A s f x h1)). Qed.
Lemma lem7030840 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (h1 : term75 A s f x) : True = (@IN A x s).
Proof. exact (SYM (@lem7030839 A s f x h1)). Qed.
Lemma lem7030841 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (h1 : term75 A s f x) : @IN A x s.
Proof. exact (EQ_MP (@lem7030840 A s f x h1) (@lem0)). Qed.
Lemma lem7030842 {A : Type'} (P : nat -> Prop) (s : A -> Prop) (f : A -> nat) (x : A) (h1 : term8 A s P f) (h2 : term75 A s f x) : (term20 A P f x) = True.
Proof. exact (@lem7030837 A x s P f h1 (@lem7030841 A s f x h2)). Qed.
Lemma lem7030843 {A : Type'} (x : A) (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term8 A s P f) : term114 A s P f x.
Proof. exact (fun h0 : term75 A s f x => @lem7030842 A P s f x h1 h0). Qed.
Lemma lem7030844 {A : Type'} (P : nat -> Prop) (s : A -> Prop) (f : A -> nat) (x : A) : term115 A P s f x.
Proof. exact (@lem7030815 A P s f x True). Qed.
Lemma lem7030845 {A : Type'} (x : A) (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term8 A s P f) : (term81 A s P f x) = (term116 A s f x).
Proof. exact (@lem7030844 A P s f x (@lem7030843 A x s P f h1)). Qed.
Lemma lem7030847 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7030848 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term116 A s f x) = True.
Proof. exact (@lem7030847 (term75 A s f x)). Qed.
Lemma lem7030849 {A : Type'} (x : A) (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term8 A s P f) : (term81 A s P f x) = True.
Proof. exact (TRANS (@lem7030845 A x s P f h1) (@lem7030848 A s f x)). Qed.
Lemma lem7030850 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term8 A s P f) : (term83 A s P f) = (term117 A).
Proof. exact (fun_ext (fun x : A => @lem7030849 A x s P f h1)). Qed.
Lemma lem7030851 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7030852 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term8 A s P f) : (term84 A s P f) = (term118 A).
Proof. exact (MK_COMB (@lem7030851 A) (@lem7030850 A s P f h1)). Qed.
Lemma lem7030854 {A : Type'} (t : Prop) : (term53 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7030855 {A : Type'} (t : Prop) : (term53 A t) = t.
Proof. exact (@lem7030854 A t). Qed.
Lemma lem7030856 {A : Type'} : (term118 A) = True.
Proof. exact (@lem7030855 A True). Qed.
Lemma lem7030857 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term8 A s P f) : (term84 A s P f) = True.
Proof. exact (TRANS (@lem7030852 A s P f h1) (@lem7030856 A)). Qed.
Lemma lem7030858 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term8 A s P f) : True = (term84 A s P f).
Proof. exact (SYM (@lem7030857 A s P f h1)). Qed.
Lemma lem7030859 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term8 A s P f) : term84 A s P f.
Proof. exact (EQ_MP (@lem7030858 A s P f h1) (@lem0)). Qed.
Lemma lem7030860 {A : Type'} (s : A -> Prop) (f : A -> nat) (P : nat -> Prop) (h1 : term8 A s P f) (h2 : term97 A P) : (term25 A P s f) = True.
Proof. exact (@lem7030791 A s f P h2 (@lem7030859 A s P f h1)). Qed.
Lemma lem7030861 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term8 A s P f) : term119 A P s f.
Proof. exact (fun h0 : term97 A P => @lem7030860 A s f P h1 h0). Qed.
Lemma lem7030862 {A : Type'} (s : A -> Prop) (f : A -> nat) (P : nat -> Prop) (h1 : term9 P) (h2 : term7 P) : term120 A s f P.
Proof. exact (@lem7030772 A s f True P h1 h2). Qed.
Lemma lem7030863 {A : Type'} (s : A -> Prop) (f : A -> nat) (P : nat -> Prop) (h1 : term8 A s P f) (h2 : term9 P) (h3 : term7 P) : (term121 A P s f) = (term122 A P).
Proof. exact (@lem7030862 A s f P h2 h3 (@lem7030861 A s P f h1)). Qed.
Lemma lem7030865 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7030866 {A : Type'} (P : nat -> Prop) : (term122 A P) = True.
Proof. exact (@lem7030865 (term97 A P)). Qed.
Lemma lem7030867 {A : Type'} (s : A -> Prop) (f : A -> nat) (P : nat -> Prop) (h1 : term8 A s P f) (h2 : term9 P) (h3 : term7 P) : (term121 A P s f) = True.
Proof. exact (TRANS (@lem7030863 A s f P h1 h2 h3) (@lem7030866 A P)). Qed.
Lemma lem7030868 {A : Type'} (s : A -> Prop) (f : A -> nat) (P : nat -> Prop) (h1 : term8 A s P f) (h2 : term9 P) (h3 : term7 P) : True = (term121 A P s f).
Proof. exact (SYM (@lem7030867 A s f P h1 h2 h3)). Qed.
Lemma lem7030869 {A : Type'} (s : A -> Prop) (f : A -> nat) (P : nat -> Prop) (h1 : term8 A s P f) (h2 : term9 P) (h3 : term7 P) : term121 A P s f.
Proof. exact (EQ_MP (@lem7030868 A s f P h1 h2 h3) (@lem0)). Qed.
Lemma lem7030870 {A : Type'} (s : A -> Prop) (f : A -> nat) (P : nat -> Prop) (h1 : term8 A s P f) (h2 : term4 A) (h3 : term9 P) (h4 : term7 P) : term25 A P s f.
Proof. exact (@lem7030869 A s f P h1 h3 h4 (@lem7028704 A P h2)). Qed.
Lemma lem7030871 {A : Type'} (s : A -> Prop) (f : A -> nat) (P : nat -> Prop) (h1 : term8 A s P f) (h2 : term9 P) (h3 : term7 P) : term123 A P s f.
Proof. exact (fun h0 : term4 A => @lem7030870 A s f P h1 h0 h2 h3). Qed.
Lemma lem7030872 {A : Type'} (s : A -> Prop) (f : A -> nat) (P : nat -> Prop) (h1 : term8 A s P f) (h2 : term9 P) (h3 : term7 P) : term25 A P s f.
Proof. exact (@lem7030871 A s f P h1 h2 h3 (@lem7028695 A)). Qed.
Lemma lem7030873 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term5 A s P f) : term6 A s P f.
Proof. exact (proj2 (@lem7028696 A s P f h1)). Qed.
Lemma lem7030874 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term5 A s P f) : term7 P.
Proof. exact (proj1 (@lem7028696 A s P f h1)). Qed.
Lemma lem7030875 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term6 A s P f) : term8 A s P f.
Proof. exact (proj2 (@lem7028697 A s P f h1)). Qed.
Lemma lem7030876 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term6 A s P f) : term9 P.
Proof. exact (proj1 (@lem7028697 A s P f h1)). Qed.
Lemma lem7030877 {A : Type'} (s : A -> Prop) (f : A -> nat) (P : nat -> Prop) (h1 : term8 A s P f) (h2 : term9 P) (h3 : term7 P) : (term8 A s P f) = (term25 A P s f).
Proof. exact (prop_ext (fun h4 : term8 A s P f => @lem7030872 A s f P h1 h2 h3) (fun h4 : term25 A P s f => @lem7028699 A s P f h1)). Qed.
Lemma lem7030878 {A : Type'} (s : A -> Prop) (f : A -> nat) (P : nat -> Prop) (h1 : term8 A s P f) (h2 : term9 P) (h3 : term7 P) : term25 A P s f.
Proof. exact (EQ_MP (@lem7030877 A s f P h1 h2 h3) (@lem7028699 A s P f h1)). Qed.
Lemma lem7030879 {A : Type'} (s : A -> Prop) (f : A -> nat) (P : nat -> Prop) (h1 : term8 A s P f) (h2 : term9 P) (h3 : term7 P) : (term9 P) = (term25 A P s f).
Proof. exact (prop_ext (fun h4 : term9 P => @lem7030878 A s f P h1 h2 h3) (fun h4 : term25 A P s f => @lem7028700 P h2)). Qed.
Lemma lem7030880 {A : Type'} (s : A -> Prop) (f : A -> nat) (P : nat -> Prop) (h1 : term8 A s P f) (h2 : term9 P) (h3 : term7 P) : term25 A P s f.
Proof. exact (EQ_MP (@lem7030879 A s f P h1 h2 h3) (@lem7028700 P h2)). Qed.
Lemma lem7030881 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term9 P) (h2 : term7 P) (h3 : term6 A s P f) : (term8 A s P f) = (term25 A P s f).
Proof. exact (prop_ext (fun h4 : term8 A s P f => @lem7030880 A s f P h4 h1 h2) (fun h4 : term25 A P s f => @lem7030875 A s P f h3)). Qed.
Lemma lem7030882 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term9 P) (h2 : term7 P) (h3 : term6 A s P f) : term25 A P s f.
Proof. exact (EQ_MP (@lem7030881 A s P f h1 h2 h3) (@lem7030875 A s P f h3)). Qed.
Lemma lem7030883 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term7 P) (h2 : term6 A s P f) : (term9 P) = (term25 A P s f).
Proof. exact (prop_ext (fun h3 : term9 P => @lem7030882 A s P f h3 h1 h2) (fun h3 : term25 A P s f => @lem7030876 A s P f h2)). Qed.
Lemma lem7030884 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term7 P) (h2 : term6 A s P f) : term25 A P s f.
Proof. exact (EQ_MP (@lem7030883 A s P f h1 h2) (@lem7030876 A s P f h2)). Qed.
Lemma lem7030885 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term7 P) (h2 : term6 A s P f) : (term7 P) = (term25 A P s f).
Proof. exact (prop_ext (fun h3 : term7 P => @lem7030884 A s P f h1 h2) (fun h3 : term25 A P s f => @lem7028698 P h1)). Qed.
Lemma lem7030886 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term7 P) (h2 : term6 A s P f) : term25 A P s f.
Proof. exact (EQ_MP (@lem7030885 A s P f h1 h2) (@lem7028698 P h1)). Qed.
Lemma lem7030887 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term7 P) (h2 : term5 A s P f) : (term6 A s P f) = (term25 A P s f).
Proof. exact (prop_ext (fun h3 : term6 A s P f => @lem7030886 A s P f h1 h3) (fun h3 : term25 A P s f => @lem7030873 A s P f h2)). Qed.
Lemma lem7030888 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term7 P) (h2 : term5 A s P f) : term25 A P s f.
Proof. exact (EQ_MP (@lem7030887 A s P f h1 h2) (@lem7030873 A s P f h2)). Qed.
Lemma lem7030889 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term5 A s P f) : (term7 P) = (term25 A P s f).
Proof. exact (prop_ext (fun h2 : term7 P => @lem7030888 A s P f h2 h1) (fun h2 : term25 A P s f => @lem7030874 A s P f h1)). Qed.
Lemma lem7030890 {A : Type'} (s : A -> Prop) (P : nat -> Prop) (f : A -> nat) (h1 : term5 A s P f) : term25 A P s f.
Proof. exact (EQ_MP (@lem7030889 A s P f h1) (@lem7030874 A s P f h1)). Qed.
Lemma lem7030891 {A : Type'} (P : nat -> Prop) (s : A -> Prop) (f : A -> nat) : term124 A P s f.
Proof. exact (fun h0 : term5 A s P f => @lem7030890 A s P f h0). Qed.
Lemma lem7030896 {A : Type'} (P : nat -> Prop) (f : A -> nat) : term125 A P f.
Proof. exact (fun s : A -> Prop => @lem7030891 A P s f). Qed.
Lemma lem7030901 {A : Type'} (P : nat -> Prop) : term126 A P.
Proof. exact (fun f : A -> nat => @lem7030896 A P f). Qed.
Lemma lem7030906 {A : Type'} : term127 A.
Proof. exact (fun P : nat -> Prop => @lem7030901 A P). Qed.
