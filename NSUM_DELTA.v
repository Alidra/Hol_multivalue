Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_DELTA_term_abbrevs.
Require Import ITERATE_DELTA_spec.
Require Import MONOIDAL_ADD_spec.
Require Import NEUTRAL_ADD_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm6920357_spec.
Require Import thm6920371_spec.
Require Import thm7_spec.
Lemma lem6960692 : (@monoidal nat Nat.add) = ((@monoidal nat Nat.add) = True).
Proof. exact (@lem7 (@monoidal nat Nat.add)). Qed.
Lemma lem6960694 {_121513 _121532 : Type'} (op : type1400 _121513) : term0 _121513 _121532 op.
Proof. exact (@lem5825973 _121513 _121532 op). Qed.
Lemma lem6960695 {_121513 _121532 : Type'} (op : type1400 _121513) : (term0 _121513 _121532 op) = (term1 _121513 _121532 op).
Proof. exact (eq_refl (term0 _121513 _121532 op)). Qed.
Lemma lem6960696 {_121513 _121532 : Type'} (op : type1400 _121513) : term1 _121513 _121532 op.
Proof. exact (EQ_MP (@lem6960695 _121513 _121532 op) (@lem6960694 _121513 _121532 op)). Qed.
Lemma lem6960697 {_121513 : Type'} (op : type1400 _121513) (h1 : @monoidal _121513 op) : @monoidal _121513 op.
Proof. exact (h1). Qed.
Lemma lem6960698 {_121513 _121532 : Type'} (op : type1400 _121513) (h1 : @monoidal _121513 op) : term2 _121513 _121532 op.
Proof. exact (@lem6960696 _121513 _121532 op (@lem6960697 _121513 op h1)). Qed.
Lemma lem6960699 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) (h1 : @monoidal _121513 op) : term3 _121513 _121532 op f.
Proof. exact (@lem6960698 _121513 _121532 op h1 f). Qed.
Lemma lem6960700 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) : (term3 _121513 _121532 op f) = (term4 _121513 _121532 f op).
Proof. exact (eq_refl (term3 _121513 _121532 op f)). Qed.
Lemma lem6960701 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) (h1 : @monoidal _121513 op) : term4 _121513 _121532 f op.
Proof. exact (EQ_MP (@lem6960700 _121513 _121532 f op) (@lem6960699 _121513 _121532 f op h1)). Qed.
Lemma lem6960702 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) : term5 _121513 _121532 f op a.
Proof. exact (@lem6960701 _121513 _121532 f op h1 a). Qed.
Lemma lem6960703 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term5 _121513 _121532 f op a) = (term6 _121513 _121532 f a op).
Proof. exact (eq_refl (term5 _121513 _121532 f op a)). Qed.
Lemma lem6960704 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) : term6 _121513 _121532 f a op.
Proof. exact (EQ_MP (@lem6960703 _121513 _121532 f a op) (@lem6960702 _121513 _121532 f a op h1)). Qed.
Lemma lem6960705 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (s : _121532 -> Prop) (op : type1400 _121513) (h1 : @monoidal _121513 op) : term7 _121513 _121532 f a op s.
Proof. exact (@lem6960704 _121513 _121532 f a op h1 s). Qed.
Lemma lem6960706 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term7 _121513 _121532 f a op s) = ((term8 _121513 _121532 s a f op) = (term9 _121513 _121532 s f a op)).
Proof. exact (eq_refl (term7 _121513 _121532 f a op s)). Qed.
Lemma lem6960707 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) : (term8 _121513 _121532 s a f op) = (term9 _121513 _121532 s f a op).
Proof. exact (EQ_MP (@lem6960706 _121513 _121532 s f a op) (@lem6960705 _121513 _121532 f a s op h1)). Qed.
Lemma lem6960713 (h1 : (@neutral nat Nat.add) = (NUMERAL 0)) : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem6960714 (h1 : (@neutral nat Nat.add) = (NUMERAL 0)) : (NUMERAL 0) = (@neutral nat Nat.add).
Proof. exact (SYM (@lem6960713 h1)). Qed.
Lemma lem6960715 (h1 : (NUMERAL 0) = (@neutral nat Nat.add)) : (NUMERAL 0) = (@neutral nat Nat.add).
Proof. exact (h1). Qed.
Lemma lem6960716 (h1 : (NUMERAL 0) = (@neutral nat Nat.add)) : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (SYM (@lem6960715 h1)). Qed.
Lemma lem6960717 : ((@neutral nat Nat.add) = (NUMERAL 0)) = ((NUMERAL 0) = (@neutral nat Nat.add)).
Proof. exact (prop_ext (fun h1 : (@neutral nat Nat.add) = (NUMERAL 0) => @lem6960714 h1) (fun h1 : (NUMERAL 0) = (@neutral nat Nat.add) => @lem6960716 h1)). Qed.
Lemma lem6960730 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6960731 {A : Type'} : (@nsum A) = (@iterate nat A Nat.add).
Proof. exact (@lem6960730 A). Qed.
Lemma lem6960732 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6960733 {A : Type'} (s : A -> Prop) : (@nsum A s) = (@iterate nat A Nat.add s).
Proof. exact (MK_COMB (@lem6960731 A) (@lem6960732 A s)). Qed.
Lemma lem6960739 : (NUMERAL 0) = (@neutral nat Nat.add).
Proof. exact (EQ_MP (@lem6960717) (@lem6921993)). Qed.
Lemma lem6960740 {A : Type'} (x : A) (a : A) (b : nat) : (term10 A x a b) = (term10 A x a b).
Proof. exact (eq_refl (term10 A x a b)). Qed.
Lemma lem6960741 {A : Type'} (x : A) (a : A) (b : nat) : (term11 A x a b) = (term12 A x a b).
Proof. exact (MK_COMB (@lem6960740 A x a b) (@lem6960739)). Qed.
Lemma lem6960744 {A : Type'} (a : A) (b : nat) : (term13 A a b) = (term14 A a b).
Proof. exact (fun_ext (fun x : A => @lem6960741 A x a b)). Qed.
Lemma lem6960745 {A : Type'} (s : A -> Prop) (a : A) (b : nat) : (term15 A s a b) = (term16 A s a b).
Proof. exact (MK_COMB (@lem6960733 A s) (@lem6960744 A a b)). Qed.
Lemma lem6960746 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6960747 {A : Type'} (s : A -> Prop) (a : A) (b : nat) : (term17 A s a b) = (term18 A s a b).
Proof. exact (MK_COMB (@lem6960746) (@lem6960745 A s a b)). Qed.
Lemma lem6960749 : (NUMERAL 0) = (@neutral nat Nat.add).
Proof. exact (EQ_MP (@lem6960717) (@lem6921993)). Qed.
Lemma lem6960750 {A : Type'} (a : A) (s : A -> Prop) (b : nat) : (term19 A a s b) = (term19 A a s b).
Proof. exact (eq_refl (term19 A a s b)). Qed.
Lemma lem6960751 {A : Type'} (a : A) (s : A -> Prop) (b : nat) : (term20 A a s b) = (term21 A a s b).
Proof. exact (MK_COMB (@lem6960750 A a s b) (@lem6960749)). Qed.
Lemma lem6960752 {A : Type'} (a : A) (s : A -> Prop) (b : nat) : ((term15 A s a b) = (term20 A a s b)) = ((term16 A s a b) = (term21 A a s b)).
Proof. exact (MK_COMB (@lem6960747 A s a b) (@lem6960751 A a s b)). Qed.
Lemma lem6960755 {A : Type'} (s : A -> Prop) (b : nat) : (term22 A s b) = (term23 A s b).
Proof. exact (fun_ext (fun a : A => @lem6960752 A a s b)). Qed.
Lemma lem6960756 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6960757 {A : Type'} (s : A -> Prop) (b : nat) : (term24 A s b) = (term25 A s b).
Proof. exact (MK_COMB (@lem6960756 A) (@lem6960755 A s b)). Qed.
Lemma lem6960762 {A : Type'} (b : nat) : (term26 A b) = (term27 A b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6960757 A s b)). Qed.
Lemma lem6960763 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6960764 {A : Type'} (b : nat) : (term28 A b) = (term29 A b).
Proof. exact (MK_COMB (@lem6960763 A) (@lem6960762 A b)). Qed.
Lemma lem6960769 {A : Type'} (b : nat) : (term29 A b) = (term28 A b).
Proof. exact (SYM (@lem6960764 A b)). Qed.
Lemma lem6960781 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : term30 _121513 _121532 s f a op.
Proof. exact (fun h0 : @monoidal _121513 op => @lem6960707 _121513 _121532 s f a op h0). Qed.
Lemma lem6960782 {A : Type'} (s : A -> Prop) (f : A -> nat) (a : A) (op : type1606) : term31 A s f a op.
Proof. exact (@lem6960781 nat A s f a op). Qed.
Lemma lem6960783 {A : Type'} (s : A -> Prop) (b : nat) (a : A) : term32 A s b a.
Proof. exact (@lem6960782 A s (term33 A b) a Nat.add). Qed.
Lemma lem6960784 {A : Type'} (x : A) (b : nat) : (term34 A b x) = b.
Proof. exact (eq_refl (term34 A b x)). Qed.
Lemma lem6960785 {A : Type'} (x : A) (a : A) : (term35 A x a) = (term35 A x a).
Proof. exact (eq_refl (term35 A x a)). Qed.
Lemma lem6960786 {A : Type'} (x : A) (a : A) (b : nat) : (term36 A a b x) = (term10 A x a b).
Proof. exact (MK_COMB (@lem6960785 A x a) (@lem6960784 A x b)). Qed.
Lemma lem6960787 : (@neutral nat Nat.add) = (@neutral nat Nat.add).
Proof. exact (eq_refl (@neutral nat Nat.add)). Qed.
Lemma lem6960788 {A : Type'} (x : A) (a : A) (b : nat) : (term37 A a b x) = (term12 A x a b).
Proof. exact (MK_COMB (@lem6960786 A x a b) (@lem6960787)). Qed.
Lemma lem6960789 {A : Type'} (a : A) (b : nat) : (term38 A a b) = (term14 A a b).
Proof. exact (fun_ext (fun x : A => @lem6960788 A x a b)). Qed.
Lemma lem6960790 {A : Type'} (s : A -> Prop) : (@iterate nat A Nat.add s) = (@iterate nat A Nat.add s).
Proof. exact (eq_refl (@iterate nat A Nat.add s)). Qed.
Lemma lem6960791 {A : Type'} (s : A -> Prop) (a : A) (b : nat) : (term39 A s a b) = (term16 A s a b).
Proof. exact (MK_COMB (@lem6960790 A s) (@lem6960789 A a b)). Qed.
Lemma lem6960792 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6960793 {A : Type'} (s : A -> Prop) (a : A) (b : nat) : (term40 A s a b) = (term18 A s a b).
Proof. exact (MK_COMB (@lem6960792) (@lem6960791 A s a b)). Qed.
Lemma lem6960794 {A : Type'} (a : A) (b : nat) : (term34 A b a) = b.
Proof. exact (eq_refl (term34 A b a)). Qed.
Lemma lem6960795 {A : Type'} (a : A) (s : A -> Prop) : (term41 A a s) = (term41 A a s).
Proof. exact (eq_refl (term41 A a s)). Qed.
Lemma lem6960796 {A : Type'} (a : A) (s : A -> Prop) (b : nat) : (term42 A s b a) = (term19 A a s b).
Proof. exact (MK_COMB (@lem6960795 A a s) (@lem6960794 A a b)). Qed.
Lemma lem6960797 : (@neutral nat Nat.add) = (@neutral nat Nat.add).
Proof. exact (eq_refl (@neutral nat Nat.add)). Qed.
Lemma lem6960798 {A : Type'} (a : A) (s : A -> Prop) (b : nat) : (term43 A s b a) = (term21 A a s b).
Proof. exact (MK_COMB (@lem6960796 A a s b) (@lem6960797)). Qed.
Lemma lem6960799 {A : Type'} (a : A) (s : A -> Prop) (b : nat) : ((term39 A s a b) = (term43 A s b a)) = ((term16 A s a b) = (term21 A a s b)).
Proof. exact (MK_COMB (@lem6960793 A s a b) (@lem6960798 A a s b)). Qed.
Lemma lem6960800 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem6960801 {A : Type'} (a : A) (s : A -> Prop) (b : nat) : (term32 A s b a) = (term45 A a s b).
Proof. exact (MK_COMB (@lem6960800) (@lem6960799 A a s b)). Qed.
Lemma lem6960802 {A : Type'} (a : A) (s : A -> Prop) (b : nat) : term45 A a s b.
Proof. exact (EQ_MP (@lem6960801 A a s b) (@lem6960783 A s b a)). Qed.
Lemma lem6960804 : (@monoidal nat Nat.add) = True.
Proof. exact (EQ_MP (@lem6960692) (@lem6924403)). Qed.
Lemma lem6960805 : True = (@monoidal nat Nat.add).
Proof. exact (SYM (@lem6960804)). Qed.
Lemma lem6960806 : @monoidal nat Nat.add.
Proof. exact (EQ_MP (@lem6960805) (@lem0)). Qed.
Lemma lem6960807 {A : Type'} (a : A) (s : A -> Prop) (b : nat) : (term16 A s a b) = (term21 A a s b).
Proof. exact (@lem6960802 A a s b (@lem6960806)). Qed.
Lemma lem6960841 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6960842 {A : Type'} (a : A) (s : A -> Prop) (b : nat) : (term18 A s a b) = (term46 A a s b).
Proof. exact (MK_COMB (@lem6960841) (@lem6960807 A a s b)). Qed.
Lemma lem6960909 {A : Type'} (a : A) (s : A -> Prop) (b : nat) : (term21 A a s b) = (term21 A a s b).
Proof. exact (eq_refl (term21 A a s b)). Qed.
Lemma lem6960910 {A : Type'} (a : A) (s : A -> Prop) (b : nat) : ((term16 A s a b) = (term21 A a s b)) = ((term21 A a s b) = (term21 A a s b)).
Proof. exact (MK_COMB (@lem6960842 A a s b) (@lem6960909 A a s b)). Qed.
Lemma lem6960912 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6960913 (x : nat) : (x = x) = True.
Proof. exact (@lem6960912 nat x). Qed.
Lemma lem6960914 {A : Type'} (a : A) (s : A -> Prop) (b : nat) : ((term21 A a s b) = (term21 A a s b)) = True.
Proof. exact (@lem6960913 (term21 A a s b)). Qed.
Lemma lem6960915 {A : Type'} (a : A) (s : A -> Prop) (b : nat) : ((term16 A s a b) = (term21 A a s b)) = True.
Proof. exact (TRANS (@lem6960910 A a s b) (@lem6960914 A a s b)). Qed.
Lemma lem6960916 {A : Type'} (s : A -> Prop) (b : nat) : (term23 A s b) = (term47 A).
Proof. exact (fun_ext (fun a : A => @lem6960915 A a s b)). Qed.
Lemma lem6960917 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6960918 {A : Type'} (s : A -> Prop) (b : nat) : (term25 A s b) = (term48 A).
Proof. exact (MK_COMB (@lem6960917 A) (@lem6960916 A s b)). Qed.
Lemma lem6960920 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6960921 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (@lem6960920 A t). Qed.
Lemma lem6960922 {A : Type'} : (term48 A) = True.
Proof. exact (@lem6960921 A True). Qed.
Lemma lem6960923 {A : Type'} (s : A -> Prop) (b : nat) : (term25 A s b) = True.
Proof. exact (TRANS (@lem6960918 A s b) (@lem6960922 A)). Qed.
Lemma lem6960924 {A : Type'} (b : nat) : (term27 A b) = (term50 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6960923 A s b)). Qed.
Lemma lem6960925 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6960926 {A : Type'} (b : nat) : (term29 A b) = (term51 A).
Proof. exact (MK_COMB (@lem6960925 A) (@lem6960924 A b)). Qed.
Lemma lem6960928 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6960929 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (@lem6960928 (A -> Prop) t). Qed.
Lemma lem6960930 {A : Type'} : (term51 A) = True.
Proof. exact (@lem6960929 A True). Qed.
Lemma lem6960931 {A : Type'} (b : nat) : (term29 A b) = True.
Proof. exact (TRANS (@lem6960926 A b) (@lem6960930 A)). Qed.
Lemma lem6960932 {A : Type'} (b : nat) : True = (term29 A b).
Proof. exact (SYM (@lem6960931 A b)). Qed.
Lemma lem6960933 {A : Type'} (b : nat) : term29 A b.
Proof. exact (EQ_MP (@lem6960932 A b) (@lem0)). Qed.
Lemma lem6960934 {A : Type'} (b : nat) : term28 A b.
Proof. exact (EQ_MP (@lem6960769 A b) (@lem6960933 A b)). Qed.
