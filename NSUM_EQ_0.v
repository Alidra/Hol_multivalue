Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_EQ_0_term_abbrevs.
Require Import ITERATE_EQ_NEUTRAL_spec.
Require Import MONOIDAL_ADD_spec.
Require Import NEUTRAL_ADD_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm196_spec.
Require Import thm197_spec.
Require Import thm4211_spec.
Require Import thm6920357_spec.
Require Import thm6920371_spec.
Require Import thm7_spec.
Lemma lem6930694 : (@monoidal nat Nat.add) = ((@monoidal nat Nat.add) = True).
Proof. exact (@lem7 (@monoidal nat Nat.add)). Qed.
Lemma lem6930696 {A B : Type'} (op : type1400 B) : term0 A B op.
Proof. exact (@lem5804540 A B op). Qed.
Lemma lem6930697 {A B : Type'} (op : type1400 B) : (term0 A B op) = (term1 A B op).
Proof. exact (eq_refl (term0 A B op)). Qed.
Lemma lem6930698 {A B : Type'} (op : type1400 B) : term1 A B op.
Proof. exact (EQ_MP (@lem6930697 A B op) (@lem6930696 A B op)). Qed.
Lemma lem6930699 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem6930700 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term2 A B op.
Proof. exact (@lem6930698 A B op (@lem6930699 B op h1)). Qed.
Lemma lem6930701 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term3 A B op f.
Proof. exact (@lem6930700 A B op h1 f). Qed.
Lemma lem6930702 {A B : Type'} (f : A -> B) (op : type1400 B) : (term3 A B op f) = (term4 A B f op).
Proof. exact (eq_refl (term3 A B op f)). Qed.
Lemma lem6930703 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term4 A B f op.
Proof. exact (EQ_MP (@lem6930702 A B f op) (@lem6930701 A B f op h1)). Qed.
Lemma lem6930704 {A B : Type'} (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term5 A B f op s.
Proof. exact (@lem6930703 A B f op h1 s). Qed.
Lemma lem6930705 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term5 A B f op s) = (term6 A B s f op).
Proof. exact (eq_refl (term5 A B f op s)). Qed.
Lemma lem6930706 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term6 A B s f op.
Proof. exact (EQ_MP (@lem6930705 A B s f op) (@lem6930704 A B f s op h1)). Qed.
Lemma lem6930707 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term7 A B s f op) : term7 A B s f op.
Proof. exact (h1). Qed.
Lemma lem6930708 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term7 A B s f op) (h2 : @monoidal B op) : (@iterate B A op s f) = (@neutral B op).
Proof. exact (@lem6930706 A B s f op h2 (@lem6930707 A B s f op h1)). Qed.
Lemma lem6930709 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term7 A B s f op) : term8 A B s f op.
Proof. exact (fun h0 : @monoidal B op => @lem6930708 A B s f op h1 h0). Qed.
Lemma lem6930710 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term9 A B s f op.
Proof. exact (fun h0 : term7 A B s f op => @lem6930709 A B s f op h0). Qed.
Lemma lem6930712 (p : Prop) (q : Prop) (r : Prop) : (term10 p q r) = (term11 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem6930717 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term9 A B s f op) = (term12 A B s f op).
Proof. exact (@lem6930712 (term7 A B s f op) (@monoidal B op) ((@iterate B A op s f) = (@neutral B op))). Qed.
Lemma lem6930719 (h1 : (@neutral nat Nat.add) = (NUMERAL 0)) : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem6930720 (h1 : (@neutral nat Nat.add) = (NUMERAL 0)) : (NUMERAL 0) = (@neutral nat Nat.add).
Proof. exact (SYM (@lem6930719 h1)). Qed.
Lemma lem6930721 (h1 : (NUMERAL 0) = (@neutral nat Nat.add)) : (NUMERAL 0) = (@neutral nat Nat.add).
Proof. exact (h1). Qed.
Lemma lem6930722 (h1 : (NUMERAL 0) = (@neutral nat Nat.add)) : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (SYM (@lem6930721 h1)). Qed.
Lemma lem6930723 : ((@neutral nat Nat.add) = (NUMERAL 0)) = ((NUMERAL 0) = (@neutral nat Nat.add)).
Proof. exact (prop_ext (fun h1 : (@neutral nat Nat.add) = (NUMERAL 0) => @lem6930720 h1) (fun h1 : (NUMERAL 0) = (@neutral nat Nat.add) => @lem6930722 h1)). Qed.
Lemma lem6930744 : (NUMERAL 0) = (@neutral nat Nat.add).
Proof. exact (EQ_MP (@lem6930723) (@lem6921993)). Qed.
Lemma lem6930745 {A : Type'} (f : A -> nat) (x : A) : (term13 A f x) = (term13 A f x).
Proof. exact (eq_refl (term13 A f x)). Qed.
Lemma lem6930746 {A : Type'} (f : A -> nat) (x : A) : ((f x) = (NUMERAL 0)) = ((f x) = (@neutral nat Nat.add)).
Proof. exact (MK_COMB (@lem6930745 A f x) (@lem6930744)). Qed.
Lemma lem6930749 {A : Type'} (x : A) (s : A -> Prop) : (term14 A x s) = (term14 A x s).
Proof. exact (eq_refl (term14 A x s)). Qed.
Lemma lem6930750 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term15 A s f x) = (term16 A s f x).
Proof. exact (MK_COMB (@lem6930749 A x s) (@lem6930746 A f x)). Qed.
Lemma lem6930753 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term17 A s f) = (term18 A s f).
Proof. exact (fun_ext (fun x : A => @lem6930750 A s f x)). Qed.
Lemma lem6930754 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6930755 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term19 A s f) = (term20 A s f).
Proof. exact (MK_COMB (@lem6930754 A) (@lem6930753 A s f)). Qed.
Lemma lem6930760 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6930761 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term21 A s f) = (term22 A s f).
Proof. exact (MK_COMB (@lem6930760) (@lem6930755 A s f)). Qed.
Lemma lem6930765 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6930766 {A : Type'} : (@nsum A) = (@iterate nat A Nat.add).
Proof. exact (@lem6930765 A). Qed.
Lemma lem6930767 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6930768 {A : Type'} (s : A -> Prop) : (@nsum A s) = (@iterate nat A Nat.add s).
Proof. exact (MK_COMB (@lem6930766 A) (@lem6930767 A s)). Qed.
Lemma lem6930769 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6930770 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@nsum A s f) = (@iterate nat A Nat.add s f).
Proof. exact (MK_COMB (@lem6930768 A s) (@lem6930769 A f)). Qed.
Lemma lem6930771 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6930772 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term23 A s f) = (term24 A s f).
Proof. exact (MK_COMB (@lem6930771) (@lem6930770 A s f)). Qed.
Lemma lem6930774 : (NUMERAL 0) = (@neutral nat Nat.add).
Proof. exact (EQ_MP (@lem6930723) (@lem6921993)). Qed.
Lemma lem6930775 {A : Type'} (s : A -> Prop) (f : A -> nat) : ((@nsum A s f) = (NUMERAL 0)) = ((@iterate nat A Nat.add s f) = (@neutral nat Nat.add)).
Proof. exact (MK_COMB (@lem6930772 A s f) (@lem6930774)). Qed.
Lemma lem6930778 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term25 A s f) = (term26 A s f).
Proof. exact (MK_COMB (@lem6930761 A s f) (@lem6930775 A s f)). Qed.
Lemma lem6930781 {A : Type'} (f : A -> nat) : (term27 A f) = (term28 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6930778 A s f)). Qed.
Lemma lem6930782 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6930783 {A : Type'} (f : A -> nat) : (term29 A f) = (term30 A f).
Proof. exact (MK_COMB (@lem6930782 A) (@lem6930781 A f)). Qed.
Lemma lem6930788 {A : Type'} : (term31 A) = (term32 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem6930783 A f)). Qed.
Lemma lem6930789 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6930790 {A : Type'} : (term33 A) = (term34 A).
Proof. exact (MK_COMB (@lem6930789 A) (@lem6930788 A)). Qed.
Lemma lem6930795 {A : Type'} : (term34 A) = (term33 A).
Proof. exact (SYM (@lem6930790 A)). Qed.
Lemma lem6930807 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term35 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6930808 (p : Prop) (q : Prop) (p' : Prop) : term36 p q p'.
Proof. exact (fun q' : Prop => @lem6930807 p q p' q'). Qed.
Lemma lem6930809 (p : Prop) (q : Prop) : term37 p q.
Proof. exact (fun p' : Prop => @lem6930808 p q p'). Qed.
Lemma lem6930810 {A : Type'} (s : A -> Prop) (f : A -> nat) : term38 A s f.
Proof. exact (@lem6930809 (term20 A s f) ((@iterate nat A Nat.add s f) = (@neutral nat Nat.add))). Qed.
Lemma lem6930811 {A : Type'} (s : A -> Prop) (f : A -> nat) (p' : Prop) : term39 A s f p'.
Proof. exact (@lem6930810 A s f p'). Qed.
Lemma lem6930812 {A : Type'} (s : A -> Prop) (f : A -> nat) (p' : Prop) : (term39 A s f p') = (term40 A s f p').
Proof. exact (eq_refl (term39 A s f p')). Qed.
Lemma lem6930813 {A : Type'} (s : A -> Prop) (f : A -> nat) (p' : Prop) : term40 A s f p'.
Proof. exact (EQ_MP (@lem6930812 A s f p') (@lem6930811 A s f p')). Qed.
Lemma lem6930814 {A : Type'} (s : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : term41 A s f p' q'.
Proof. exact (@lem6930813 A s f p' q'). Qed.
Lemma lem6930815 {A : Type'} (s : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : (term41 A s f p' q') = (term42 A s f p' q').
Proof. exact (eq_refl (term41 A s f p' q')). Qed.
Lemma lem6930816 {A : Type'} (s : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : term42 A s f p' q'.
Proof. exact (EQ_MP (@lem6930815 A s f p' q') (@lem6930814 A s f p' q')). Qed.
Lemma lem6930848 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term20 A s f) = (term20 A s f).
Proof. exact (eq_refl (term20 A s f)). Qed.
Lemma lem6930849 {A : Type'} (s : A -> Prop) (f : A -> nat) (q' : Prop) : term43 A s f q'.
Proof. exact (@lem6930816 A s f (term20 A s f) q'). Qed.
Lemma lem6930850 {A : Type'} (s : A -> Prop) (f : A -> nat) (q' : Prop) : term44 A s f q'.
Proof. exact (@lem6930849 A s f q' (@lem6930848 A s f)). Qed.
Lemma lem6930851 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term20 A s f) : term20 A s f.
Proof. exact (h1). Qed.
Lemma lem6930852 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (h1 : term20 A s f) : term45 A s f x.
Proof. exact (@lem6930851 A s f h1 x). Qed.
Lemma lem6930853 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term45 A s f x) = (term16 A s f x).
Proof. exact (eq_refl (term45 A s f x)). Qed.
Lemma lem6930854 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (h1 : term20 A s f) : term16 A s f x.
Proof. exact (EQ_MP (@lem6930853 A s f x) (@lem6930852 A x s f h1)). Qed.
Lemma lem6930855 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem6930856 {A : Type'} (f : A -> nat) (x : A) (s : A -> Prop) (h1 : term20 A s f) (h2 : @IN A x s) : (f x) = (@neutral nat Nat.add).
Proof. exact (@lem6930854 A x s f h1 (@lem6930855 A x s h2)). Qed.
Lemma lem6930865 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term12 A B s f op.
Proof. exact (EQ_MP (@lem6930717 A B s f op) (@lem6930710 A B s f op)). Qed.
Lemma lem6930866 {A : Type'} (s : A -> Prop) (f : A -> nat) (op : type1606) : term46 A s f op.
Proof. exact (@lem6930865 A nat s f op). Qed.
Lemma lem6930867 {A : Type'} (s : A -> Prop) (f : A -> nat) : term47 A s f.
Proof. exact (@lem6930866 A s f Nat.add). Qed.
Lemma lem6930877 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term35 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6930878 (p : Prop) (q : Prop) (p' : Prop) : term36 p q p'.
Proof. exact (fun q' : Prop => @lem6930877 p q p' q'). Qed.
Lemma lem6930879 (p : Prop) (q : Prop) : term37 p q.
Proof. exact (fun p' : Prop => @lem6930878 p q p'). Qed.
Lemma lem6930880 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : term48 A s f x.
Proof. exact (@lem6930879 (@IN A x s) ((f x) = (@neutral nat Nat.add))). Qed.
Lemma lem6930881 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (p' : Prop) : term49 A s f x p'.
Proof. exact (@lem6930880 A s f x p'). Qed.
Lemma lem6930882 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (p' : Prop) : (term49 A s f x p') = (term50 A s f x p').
Proof. exact (eq_refl (term49 A s f x p')). Qed.
Lemma lem6930883 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (p' : Prop) : term50 A s f x p'.
Proof. exact (EQ_MP (@lem6930882 A s f x p') (@lem6930881 A s f x p')). Qed.
Lemma lem6930884 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (p' : Prop) (q' : Prop) : term51 A s f x p' q'.
Proof. exact (@lem6930883 A s f x p' q'). Qed.
Lemma lem6930885 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (p' : Prop) (q' : Prop) : (term51 A s f x p' q') = (term52 A s f x p' q').
Proof. exact (eq_refl (term51 A s f x p' q')). Qed.
Lemma lem6930886 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (p' : Prop) (q' : Prop) : term52 A s f x p' q'.
Proof. exact (EQ_MP (@lem6930885 A s f x p' q') (@lem6930884 A s f x p' q')). Qed.
Lemma lem6930887 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem6930888 {A : Type'} (f : A -> nat) (x : A) (s : A -> Prop) (q' : Prop) : term53 A f x s q'.
Proof. exact (@lem6930886 A s f x (@IN A x s) q'). Qed.
Lemma lem6930889 {A : Type'} (f : A -> nat) (x : A) (s : A -> Prop) (q' : Prop) : term54 A f x s q'.
Proof. exact (@lem6930888 A f x s q' (@lem6930887 A x s)). Qed.
Lemma lem6930890 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem6930891 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@IN A x s) = True).
Proof. exact (@lem7 (@IN A x s)). Qed.
Lemma lem6930896 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (h1 : term20 A s f) : term16 A s f x.
Proof. exact (fun h0 : @IN A x s => @lem6930856 A f x s h1 h0). Qed.
Lemma lem6930897 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (h1 : term20 A s f) : term16 A s f x.
Proof. exact (@lem6930896 A x s f h1). Qed.
Lemma lem6930899 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (@IN A x s) = True.
Proof. exact (EQ_MP (@lem6930891 A x s) (@lem6930890 A x s h1)). Qed.
Lemma lem6930900 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : True = (@IN A x s).
Proof. exact (SYM (@lem6930899 A x s h1)). Qed.
Lemma lem6930901 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (EQ_MP (@lem6930900 A x s h1) (@lem0)). Qed.
Lemma lem6930902 {A : Type'} (f : A -> nat) (x : A) (s : A -> Prop) (h1 : term20 A s f) (h2 : @IN A x s) : (f x) = (@neutral nat Nat.add).
Proof. exact (@lem6930897 A x s f h1 (@lem6930901 A x s h2)). Qed.
Lemma lem6930903 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6930904 {A : Type'} (f : A -> nat) (x : A) (s : A -> Prop) (h1 : term20 A s f) (h2 : @IN A x s) : (term13 A f x) = term55.
Proof. exact (MK_COMB (@lem6930903) (@lem6930902 A f x s h1 h2)). Qed.
Lemma lem6930905 : (@neutral nat Nat.add) = (@neutral nat Nat.add).
Proof. exact (eq_refl (@neutral nat Nat.add)). Qed.
Lemma lem6930906 {A : Type'} (f : A -> nat) (x : A) (s : A -> Prop) (h1 : term20 A s f) (h2 : @IN A x s) : ((f x) = (@neutral nat Nat.add)) = ((@neutral nat Nat.add) = (@neutral nat Nat.add)).
Proof. exact (MK_COMB (@lem6930904 A f x s h1 h2) (@lem6930905)). Qed.
Lemma lem6930908 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6930909 (x : nat) : (x = x) = True.
Proof. exact (@lem6930908 nat x). Qed.
Lemma lem6930910 : ((@neutral nat Nat.add) = (@neutral nat Nat.add)) = True.
Proof. exact (@lem6930909 (@neutral nat Nat.add)). Qed.
Lemma lem6930911 {A : Type'} (f : A -> nat) (x : A) (s : A -> Prop) (h1 : term20 A s f) (h2 : @IN A x s) : ((f x) = (@neutral nat Nat.add)) = True.
Proof. exact (TRANS (@lem6930906 A f x s h1 h2) (@lem6930910)). Qed.
Lemma lem6930912 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (h1 : term20 A s f) : term56 A s f x.
Proof. exact (fun h0 : @IN A x s => @lem6930911 A f x s h1 h0). Qed.
Lemma lem6930913 {A : Type'} (f : A -> nat) (x : A) (s : A -> Prop) : term57 A f x s.
Proof. exact (@lem6930889 A f x s True). Qed.
Lemma lem6930914 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (h1 : term20 A s f) : (term16 A s f x) = (term58 A x s).
Proof. exact (@lem6930913 A f x s (@lem6930912 A x s f h1)). Qed.
Lemma lem6930916 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6930917 {A : Type'} (x : A) (s : A -> Prop) : (term58 A x s) = True.
Proof. exact (@lem6930916 (@IN A x s)). Qed.
Lemma lem6930918 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (h1 : term20 A s f) : (term16 A s f x) = True.
Proof. exact (TRANS (@lem6930914 A x s f h1) (@lem6930917 A x s)). Qed.
Lemma lem6930919 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term20 A s f) : (term18 A s f) = (term59 A).
Proof. exact (fun_ext (fun x : A => @lem6930918 A x s f h1)). Qed.
Lemma lem6930920 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6930921 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term20 A s f) : (term20 A s f) = (term60 A).
Proof. exact (MK_COMB (@lem6930920 A) (@lem6930919 A s f h1)). Qed.
Lemma lem6930923 {A : Type'} (t : Prop) : (term61 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6930924 {A : Type'} (t : Prop) : (term61 A t) = t.
Proof. exact (@lem6930923 A t). Qed.
Lemma lem6930925 {A : Type'} : (term60 A) = True.
Proof. exact (@lem6930924 A True). Qed.
Lemma lem6930926 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term20 A s f) : (term20 A s f) = True.
Proof. exact (TRANS (@lem6930921 A s f h1) (@lem6930925 A)). Qed.
Lemma lem6930927 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6930928 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term20 A s f) : (term62 A s f) = (and True).
Proof. exact (MK_COMB (@lem6930927) (@lem6930926 A s f h1)). Qed.
Lemma lem6930930 : (@monoidal nat Nat.add) = True.
Proof. exact (EQ_MP (@lem6930694) (@lem6924403)). Qed.
Lemma lem6930931 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term20 A s f) : (term63 A s f) = (True /\ True).
Proof. exact (MK_COMB (@lem6930928 A s f h1) (@lem6930930)). Qed.
Lemma lem6930933 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6930934 : (True /\ True) = True.
Proof. exact (@lem6930933 True). Qed.
Lemma lem6930935 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term20 A s f) : (term63 A s f) = True.
Proof. exact (TRANS (@lem6930931 A s f h1) (@lem6930934)). Qed.
Lemma lem6930936 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term20 A s f) : True = (term63 A s f).
Proof. exact (SYM (@lem6930935 A s f h1)). Qed.
Lemma lem6930937 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term20 A s f) : term63 A s f.
Proof. exact (EQ_MP (@lem6930936 A s f h1) (@lem0)). Qed.
Lemma lem6930938 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term20 A s f) : (@iterate nat A Nat.add s f) = (@neutral nat Nat.add).
Proof. exact (@lem6930867 A s f (@lem6930937 A s f h1)). Qed.
Lemma lem6930939 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6930940 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term20 A s f) : (term24 A s f) = term55.
Proof. exact (MK_COMB (@lem6930939) (@lem6930938 A s f h1)). Qed.
Lemma lem6930941 : (@neutral nat Nat.add) = (@neutral nat Nat.add).
Proof. exact (eq_refl (@neutral nat Nat.add)). Qed.
Lemma lem6930942 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term20 A s f) : ((@iterate nat A Nat.add s f) = (@neutral nat Nat.add)) = ((@neutral nat Nat.add) = (@neutral nat Nat.add)).
Proof. exact (MK_COMB (@lem6930940 A s f h1) (@lem6930941)). Qed.
Lemma lem6930944 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6930945 (x : nat) : (x = x) = True.
Proof. exact (@lem6930944 nat x). Qed.
Lemma lem6930946 : ((@neutral nat Nat.add) = (@neutral nat Nat.add)) = True.
Proof. exact (@lem6930945 (@neutral nat Nat.add)). Qed.
Lemma lem6930947 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term20 A s f) : ((@iterate nat A Nat.add s f) = (@neutral nat Nat.add)) = True.
Proof. exact (TRANS (@lem6930942 A s f h1) (@lem6930946)). Qed.
Lemma lem6930948 {A : Type'} (s : A -> Prop) (f : A -> nat) : term64 A s f.
Proof. exact (fun h0 : term20 A s f => @lem6930947 A s f h0). Qed.
Lemma lem6930949 {A : Type'} (s : A -> Prop) (f : A -> nat) : term65 A s f.
Proof. exact (@lem6930850 A s f True). Qed.
Lemma lem6930950 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term26 A s f) = (term66 A s f).
Proof. exact (@lem6930949 A s f (@lem6930948 A s f)). Qed.
Lemma lem6930952 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6930953 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term66 A s f) = True.
Proof. exact (@lem6930952 (term20 A s f)). Qed.
Lemma lem6930954 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term26 A s f) = True.
Proof. exact (TRANS (@lem6930950 A s f) (@lem6930953 A s f)). Qed.
Lemma lem6930955 {A : Type'} (f : A -> nat) : (term28 A f) = (term67 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6930954 A s f)). Qed.
Lemma lem6930956 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6930957 {A : Type'} (f : A -> nat) : (term30 A f) = (term68 A).
Proof. exact (MK_COMB (@lem6930956 A) (@lem6930955 A f)). Qed.
Lemma lem6930959 {A : Type'} (t : Prop) : (term61 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6930960 {A : Type'} (t : Prop) : (term69 A t) = t.
Proof. exact (@lem6930959 (A -> Prop) t). Qed.
Lemma lem6930961 {A : Type'} : (term68 A) = True.
Proof. exact (@lem6930960 A True). Qed.
Lemma lem6930962 {A : Type'} (f : A -> nat) : (term30 A f) = True.
Proof. exact (TRANS (@lem6930957 A f) (@lem6930961 A)). Qed.
Lemma lem6930963 {A : Type'} : (term32 A) = (term70 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem6930962 A f)). Qed.
Lemma lem6930964 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6930965 {A : Type'} : (term34 A) = (term71 A).
Proof. exact (MK_COMB (@lem6930964 A) (@lem6930963 A)). Qed.
Lemma lem6930967 {A : Type'} (t : Prop) : (term61 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6930968 {A : Type'} (t : Prop) : (term72 A t) = t.
Proof. exact (@lem6930967 (A -> nat) t). Qed.
Lemma lem6930969 {A : Type'} : (term71 A) = True.
Proof. exact (@lem6930968 A True). Qed.
Lemma lem6930970 {A : Type'} : (term34 A) = True.
Proof. exact (TRANS (@lem6930965 A) (@lem6930969 A)). Qed.
Lemma lem6930971 {A : Type'} : True = (term34 A).
Proof. exact (SYM (@lem6930970 A)). Qed.
Lemma lem6930972 {A : Type'} : term34 A.
Proof. exact (EQ_MP (@lem6930971 A) (@lem0)). Qed.
Lemma lem6930973 {A : Type'} : term33 A.
Proof. exact (EQ_MP (@lem6930795 A) (@lem6930972 A)). Qed.
