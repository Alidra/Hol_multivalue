Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_EQ_0_IFF_NUMSEG_term_abbrevs.
Require Import FINITE_NUMSEG_spec.
Require Import IN_NUMSEG_spec.
Require Import NSUM_EQ_0_IFF_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem7044636 (m : nat) : term0 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem7044637 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem7044638 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem7044637 m) (@lem7044636 m)). Qed.
Lemma lem7044639 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem7044638 m n). Qed.
Lemma lem7044640 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem7044641 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem7044640 m n) (@lem7044639 m n)). Qed.
Lemma lem7044642 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem7044641 m n p). Qed.
Lemma lem7044643 (m : nat) (p : nat) (n : nat) : (term4 m n p) = ((term5 p m n) = (term6 m p n)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem7044645 (m : nat) : term7 m.
Proof. exact (@lem5329299 m). Qed.
Lemma lem7044646 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem7044647 (m : nat) : term8 m.
Proof. exact (EQ_MP (@lem7044646 m) (@lem7044645 m)). Qed.
Lemma lem7044648 (m : nat) (n : nat) : term9 m n.
Proof. exact (@lem7044647 m n). Qed.
Lemma lem7044649 (m : nat) (n : nat) : (term9 m n) = (term10 m n).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem7044650 (m : nat) (n : nat) : term10 m n.
Proof. exact (EQ_MP (@lem7044649 m n) (@lem7044648 m n)). Qed.
Lemma lem7044651 (m : nat) (n : nat) : (term10 m n) = ((term10 m n) = True).
Proof. exact (@lem7 (term10 m n)). Qed.
Lemma lem7044653 {_127305 : Type'} (f : _127305 -> nat) (s : _127305 -> Prop) : term11 _127305 f s.
Proof. exact (@lem6954254 _127305 f s). Qed.
Lemma lem7044654 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term11 _127305 f s) = (term12 _127305 s f).
Proof. exact (eq_refl (term11 _127305 f s)). Qed.
Lemma lem7044655 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : term12 _127305 s f.
Proof. exact (EQ_MP (@lem7044654 _127305 s f) (@lem7044653 _127305 f s)). Qed.
Lemma lem7044656 {_127305 : Type'} (s : _127305 -> Prop) (h1 : @FINITE _127305 s) : @FINITE _127305 s.
Proof. exact (h1). Qed.
Lemma lem7044657 {_127305 : Type'} (f : _127305 -> nat) (s : _127305 -> Prop) (h1 : @FINITE _127305 s) : ((@nsum _127305 s f) = (NUMERAL 0)) = (term13 _127305 s f).
Proof. exact (@lem7044655 _127305 s f (@lem7044656 _127305 s h1)). Qed.
Lemma lem7044678 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : term12 _127305 s f.
Proof. exact (fun h0 : @FINITE _127305 s => @lem7044657 _127305 f s h0). Qed.
Lemma lem7044679 (s : nat -> Prop) (f : nat -> nat) : term14 s f.
Proof. exact (@lem7044678 nat s f). Qed.
Lemma lem7044680 (m : nat) (n : nat) (f : nat -> nat) : term15 m n f.
Proof. exact (@lem7044679 (dotdot m n) f). Qed.
Lemma lem7044682 (m : nat) (n : nat) : (term10 m n) = True.
Proof. exact (EQ_MP (@lem7044651 m n) (@lem7044650 m n)). Qed.
Lemma lem7044683 (m : nat) (n : nat) : True = (term10 m n).
Proof. exact (SYM (@lem7044682 m n)). Qed.
Lemma lem7044684 (m : nat) (n : nat) : term10 m n.
Proof. exact (EQ_MP (@lem7044683 m n) (@lem0)). Qed.
Lemma lem7044685 (m : nat) (n : nat) (f : nat -> nat) : ((term16 m n f) = (NUMERAL 0)) = (term17 m n f).
Proof. exact (@lem7044680 m n f (@lem7044684 m n)). Qed.
Lemma lem7044693 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term18 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7044694 (p : Prop) (q : Prop) (p' : Prop) : term19 p q p'.
Proof. exact (fun q' : Prop => @lem7044693 p q p' q'). Qed.
Lemma lem7044695 (p : Prop) (q : Prop) : term20 p q.
Proof. exact (fun p' : Prop => @lem7044694 p q p'). Qed.
Lemma lem7044696 (m : nat) (n : nat) (f : nat -> nat) (x : nat) : term21 m n f x.
Proof. exact (@lem7044695 (term5 x m n) ((f x) = (NUMERAL 0))). Qed.
Lemma lem7044697 (m : nat) (n : nat) (f : nat -> nat) (x : nat) (p' : Prop) : term22 m n f x p'.
Proof. exact (@lem7044696 m n f x p'). Qed.
Lemma lem7044698 (m : nat) (n : nat) (f : nat -> nat) (x : nat) (p' : Prop) : (term22 m n f x p') = (term23 m n f x p').
Proof. exact (eq_refl (term22 m n f x p')). Qed.
Lemma lem7044699 (m : nat) (n : nat) (f : nat -> nat) (x : nat) (p' : Prop) : term23 m n f x p'.
Proof. exact (EQ_MP (@lem7044698 m n f x p') (@lem7044697 m n f x p')). Qed.
Lemma lem7044700 (m : nat) (n : nat) (f : nat -> nat) (x : nat) (p' : Prop) (q' : Prop) : term24 m n f x p' q'.
Proof. exact (@lem7044699 m n f x p' q'). Qed.
Lemma lem7044701 (m : nat) (n : nat) (f : nat -> nat) (x : nat) (p' : Prop) (q' : Prop) : (term24 m n f x p' q') = (term25 m n f x p' q').
Proof. exact (eq_refl (term24 m n f x p' q')). Qed.
Lemma lem7044702 (m : nat) (n : nat) (f : nat -> nat) (x : nat) (p' : Prop) (q' : Prop) : term25 m n f x p' q'.
Proof. exact (EQ_MP (@lem7044701 m n f x p' q') (@lem7044700 m n f x p' q')). Qed.
Lemma lem7044704 (m : nat) (p : nat) (n : nat) : (term5 p m n) = (term6 m p n).
Proof. exact (EQ_MP (@lem7044643 m p n) (@lem7044642 m n p)). Qed.
Lemma lem7044705 (m : nat) (x : nat) (n : nat) : (term5 x m n) = (term6 m x n).
Proof. exact (@lem7044704 m x n). Qed.
Lemma lem7044708 (f : nat -> nat) (m : nat) (x : nat) (n : nat) (q' : Prop) : term26 f m x n q'.
Proof. exact (@lem7044702 m n f x (term6 m x n) q'). Qed.
Lemma lem7044709 (f : nat -> nat) (m : nat) (x : nat) (n : nat) (q' : Prop) : term27 f m x n q'.
Proof. exact (@lem7044708 f m x n q' (@lem7044705 m x n)). Qed.
Lemma lem7044719 (f : nat -> nat) (x : nat) : ((f x) = (NUMERAL 0)) = ((f x) = (NUMERAL 0)).
Proof. exact (eq_refl ((f x) = (NUMERAL 0))). Qed.
Lemma lem7044720 (m : nat) (n : nat) (f : nat -> nat) (x : nat) : term28 m n f x.
Proof. exact (fun h0 : term6 m x n => @lem7044719 f x). Qed.
Lemma lem7044721 (m : nat) (n : nat) (f : nat -> nat) (x : nat) : term29 m n f x.
Proof. exact (@lem7044709 f m x n ((f x) = (NUMERAL 0))). Qed.
Lemma lem7044722 (m : nat) (n : nat) (f : nat -> nat) (x : nat) : (term30 m n f x) = (term31 m n f x).
Proof. exact (@lem7044721 m n f x (@lem7044720 m n f x)). Qed.
Lemma lem7044758 (m : nat) (n : nat) (f : nat -> nat) : (term32 m n f) = (term33 m n f).
Proof. exact (fun_ext (fun x : nat => @lem7044722 m n f x)). Qed.
Lemma lem7044794 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7044795 (m : nat) (n : nat) (f : nat -> nat) : (term17 m n f) = (term34 m n f).
Proof. exact (MK_COMB (@lem7044794) (@lem7044758 m n f)). Qed.
Lemma lem7044835 (m : nat) (n : nat) (f : nat -> nat) : ((term16 m n f) = (NUMERAL 0)) = (term34 m n f).
Proof. exact (TRANS (@lem7044685 m n f) (@lem7044795 m n f)). Qed.
Lemma lem7044836 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7044837 (m : nat) (n : nat) (f : nat -> nat) : (term35 m n f) = (term36 m n f).
Proof. exact (MK_COMB (@lem7044836) (@lem7044835 m n f)). Qed.
Lemma lem7044916 (m : nat) (n : nat) (f : nat -> nat) : (term34 m n f) = (term34 m n f).
Proof. exact (eq_refl (term34 m n f)). Qed.
Lemma lem7044917 (m : nat) (n : nat) (f : nat -> nat) : (((term16 m n f) = (NUMERAL 0)) = (term34 m n f)) = ((term34 m n f) = (term34 m n f)).
Proof. exact (MK_COMB (@lem7044837 m n f) (@lem7044916 m n f)). Qed.
Lemma lem7044919 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7044920 (x : Prop) : (x = x) = True.
Proof. exact (@lem7044919 Prop x). Qed.
Lemma lem7044921 (m : nat) (n : nat) (f : nat -> nat) : ((term34 m n f) = (term34 m n f)) = True.
Proof. exact (@lem7044920 (term34 m n f)). Qed.
Lemma lem7044924 (m : nat) (n : nat) (f : nat -> nat) : (term37 m n f) = (term37 m n f).
Proof. exact (eq_refl (term37 m n f)). Qed.
Lemma lem7044925 (m : nat) (n : nat) (f : nat -> nat) : (term37 m n f) = (((term34 m n f) = (term34 m n f)) = True).
Proof. exact (eq_refl (term37 m n f)). Qed.
Lemma lem7044926 (m : nat) (n : nat) (f : nat -> nat) : (term38 m n f) = (term38 m n f).
Proof. exact (eq_refl (term38 m n f)). Qed.
Lemma lem7044927 (m : nat) (n : nat) (f : nat -> nat) : ((term37 m n f) = (term37 m n f)) = ((term37 m n f) = (((term34 m n f) = (term34 m n f)) = True)).
Proof. exact (MK_COMB (@lem7044926 m n f) (@lem7044925 m n f)). Qed.
Lemma lem7044928 (m : nat) (n : nat) (f : nat -> nat) : (term37 m n f) = (((term34 m n f) = (term34 m n f)) = True).
Proof. exact (eq_refl (term37 m n f)). Qed.
Lemma lem7044929 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7044930 (m : nat) (n : nat) (f : nat -> nat) : (term38 m n f) = (term39 m n f).
Proof. exact (MK_COMB (@lem7044929) (@lem7044928 m n f)). Qed.
Lemma lem7044931 (m : nat) (n : nat) (f : nat -> nat) : (((term34 m n f) = (term34 m n f)) = True) = (((term34 m n f) = (term34 m n f)) = True).
Proof. exact (eq_refl (((term34 m n f) = (term34 m n f)) = True)). Qed.
Lemma lem7044932 (m : nat) (n : nat) (f : nat -> nat) : ((term37 m n f) = (((term34 m n f) = (term34 m n f)) = True)) = ((((term34 m n f) = (term34 m n f)) = True) = (((term34 m n f) = (term34 m n f)) = True)).
Proof. exact (MK_COMB (@lem7044930 m n f) (@lem7044931 m n f)). Qed.
Lemma lem7044933 (m : nat) (n : nat) (f : nat -> nat) : ((term37 m n f) = (term37 m n f)) = ((((term34 m n f) = (term34 m n f)) = True) = (((term34 m n f) = (term34 m n f)) = True)).
Proof. exact (TRANS (@lem7044927 m n f) (@lem7044932 m n f)). Qed.
Lemma lem7044934 (m : nat) (n : nat) (f : nat -> nat) : (((term34 m n f) = (term34 m n f)) = True) = (((term34 m n f) = (term34 m n f)) = True).
Proof. exact (EQ_MP (@lem7044933 m n f) (@lem7044924 m n f)). Qed.
Lemma lem7044935 (m : nat) (n : nat) (f : nat -> nat) : ((term34 m n f) = (term34 m n f)) = True.
Proof. exact (EQ_MP (@lem7044934 m n f) (@lem7044921 m n f)). Qed.
Lemma lem7044936 (m : nat) (n : nat) (f : nat -> nat) : (((term16 m n f) = (NUMERAL 0)) = (term34 m n f)) = True.
Proof. exact (TRANS (@lem7044917 m n f) (@lem7044935 m n f)). Qed.
Lemma lem7044937 (m : nat) (f : nat -> nat) : (term40 m f) = term41.
Proof. exact (fun_ext (fun n : nat => @lem7044936 m n f)). Qed.
Lemma lem7044938 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7044939 (m : nat) (f : nat -> nat) : (term42 m f) = term43.
Proof. exact (MK_COMB (@lem7044938) (@lem7044937 m f)). Qed.
Lemma lem7044941 {A : Type'} (t : Prop) : (term44 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7044942 (t : Prop) : (term45 t) = t.
Proof. exact (@lem7044941 nat t). Qed.
Lemma lem7044943 : term43 = True.
Proof. exact (@lem7044942 True). Qed.
Lemma lem7044944 (m : nat) (f : nat -> nat) : (term42 m f) = True.
Proof. exact (TRANS (@lem7044939 m f) (@lem7044943)). Qed.
Lemma lem7044945 (f : nat -> nat) : (term46 f) = term41.
Proof. exact (fun_ext (fun m : nat => @lem7044944 m f)). Qed.
Lemma lem7044946 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7044947 (f : nat -> nat) : (term47 f) = term43.
Proof. exact (MK_COMB (@lem7044946) (@lem7044945 f)). Qed.
Lemma lem7044949 {A : Type'} (t : Prop) : (term44 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7044950 (t : Prop) : (term45 t) = t.
Proof. exact (@lem7044949 nat t). Qed.
Lemma lem7044951 : term43 = True.
Proof. exact (@lem7044950 True). Qed.
Lemma lem7044952 (f : nat -> nat) : (term47 f) = True.
Proof. exact (TRANS (@lem7044947 f) (@lem7044951)). Qed.
Lemma lem7044953 : term48 = term49.
Proof. exact (fun_ext (fun f : nat -> nat => @lem7044952 f)). Qed.
Lemma lem7044954 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7044955 : term50 = term51.
Proof. exact (MK_COMB (@lem7044954) (@lem7044953)). Qed.
Lemma lem7044957 {A : Type'} (t : Prop) : (term44 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7044958 (t : Prop) : (term52 t) = t.
Proof. exact (@lem7044957 (nat -> nat) t). Qed.
Lemma lem7044959 : term51 = True.
Proof. exact (@lem7044958 True). Qed.
Lemma lem7044960 : term50 = True.
Proof. exact (TRANS (@lem7044955) (@lem7044959)). Qed.
Lemma lem7044961 : True = term50.
Proof. exact (SYM (@lem7044960)). Qed.
Lemma lem7044962 : term50.
Proof. exact (EQ_MP (@lem7044961) (@lem0)). Qed.
