Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_UNION_term_abbrevs.
Require Import ITERATE_UNION_spec.
Require Import MONOIDAL_REAL_ADD_spec.
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
Require Import thm7_spec.
Require Import thm7064097_spec.
Require Import thm7064111_spec.
Lemma lem7067646 : (@monoidal real real_add) = ((@monoidal real real_add) = True).
Proof. exact (@lem7 (@monoidal real real_add)). Qed.
Lemma lem7067648 {_120592 _120607 : Type'} (op : type1400 _120607) : term0 _120592 _120607 op.
Proof. exact (@lem5764203 _120592 _120607 op). Qed.
Lemma lem7067649 {_120592 _120607 : Type'} (op : type1400 _120607) : (term0 _120592 _120607 op) = (term1 _120592 _120607 op).
Proof. exact (eq_refl (term0 _120592 _120607 op)). Qed.
Lemma lem7067650 {_120592 _120607 : Type'} (op : type1400 _120607) : term1 _120592 _120607 op.
Proof. exact (EQ_MP (@lem7067649 _120592 _120607 op) (@lem7067648 _120592 _120607 op)). Qed.
Lemma lem7067651 {_120607 : Type'} (op : type1400 _120607) (h1 : @monoidal _120607 op) : @monoidal _120607 op.
Proof. exact (h1). Qed.
Lemma lem7067652 {_120592 _120607 : Type'} (op : type1400 _120607) (h1 : @monoidal _120607 op) : term2 _120592 _120607 op.
Proof. exact (@lem7067650 _120592 _120607 op (@lem7067651 _120607 op h1)). Qed.
Lemma lem7067653 {_120592 _120607 : Type'} (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term3 _120592 _120607 op f.
Proof. exact (@lem7067652 _120592 _120607 op h1 f). Qed.
Lemma lem7067654 {_120592 _120607 : Type'} (op : type1400 _120607) (f : _120592 -> _120607) : (term3 _120592 _120607 op f) = (term4 _120592 _120607 op f).
Proof. exact (eq_refl (term3 _120592 _120607 op f)). Qed.
Lemma lem7067655 {_120592 _120607 : Type'} (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term4 _120592 _120607 op f.
Proof. exact (EQ_MP (@lem7067654 _120592 _120607 op f) (@lem7067653 _120592 _120607 f op h1)). Qed.
Lemma lem7067656 {_120592 _120607 : Type'} (f : _120592 -> _120607) (s : _120592 -> Prop) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term5 _120592 _120607 op f s.
Proof. exact (@lem7067655 _120592 _120607 f op h1 s). Qed.
Lemma lem7067657 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term5 _120592 _120607 op f s) = (term6 _120592 _120607 s op f).
Proof. exact (eq_refl (term5 _120592 _120607 op f s)). Qed.
Lemma lem7067658 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term6 _120592 _120607 s op f.
Proof. exact (EQ_MP (@lem7067657 _120592 _120607 s op f) (@lem7067656 _120592 _120607 f s op h1)). Qed.
Lemma lem7067659 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (t : _120592 -> Prop) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term7 _120592 _120607 s op f t.
Proof. exact (@lem7067658 _120592 _120607 s f op h1 t). Qed.
Lemma lem7067660 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term7 _120592 _120607 s op f t) = (term8 _120592 _120607 s op t f).
Proof. exact (eq_refl (term7 _120592 _120607 s op f t)). Qed.
Lemma lem7067661 {_120592 _120607 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term8 _120592 _120607 s op t f.
Proof. exact (EQ_MP (@lem7067660 _120592 _120607 s op t f) (@lem7067659 _120592 _120607 s f t op h1)). Qed.
Lemma lem7067662 {_120592 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) (h1 : term9 _120592 s t) : term9 _120592 s t.
Proof. exact (h1). Qed.
Lemma lem7067663 {_120592 _120607 : Type'} (f : _120592 -> _120607) (op : type1400 _120607) (s : _120592 -> Prop) (t : _120592 -> Prop) (h1 : @monoidal _120607 op) (h2 : term9 _120592 s t) : (term10 _120592 _120607 op s t f) = (term11 _120592 _120607 s op t f).
Proof. exact (@lem7067661 _120592 _120607 s t f op h1 (@lem7067662 _120592 s t h2)). Qed.
Lemma lem7067664 {_120592 _120607 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term8 _120592 _120607 s op t f.
Proof. exact (fun h0 : term9 _120592 s t => @lem7067663 _120592 _120607 f op s t h1 h0). Qed.
Lemma lem7067665 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : term12 _120592 _120607 s op t f.
Proof. exact (fun h0 : @monoidal _120607 op => @lem7067664 _120592 _120607 s t f op h0). Qed.
Lemma lem7067667 (p : Prop) (q : Prop) (r : Prop) : (term13 p q r) = (term14 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem7067672 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term12 _120592 _120607 s op t f) = (term15 _120592 _120607 s op t f).
Proof. exact (@lem7067667 (@monoidal _120607 op) (term9 _120592 s t) ((term10 _120592 _120607 op s t f) = (term11 _120592 _120607 s op t f))). Qed.
Lemma lem7067689 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term16 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7067690 (p : Prop) (q : Prop) (p' : Prop) : term17 p q p'.
Proof. exact (fun q' : Prop => @lem7067689 p q p' q'). Qed.
Lemma lem7067691 (p : Prop) (q : Prop) : term18 p q.
Proof. exact (fun p' : Prop => @lem7067690 p q p'). Qed.
Lemma lem7067692 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (f : _131550 -> real) : term19 _131550 s t f.
Proof. exact (@lem7067691 (term9 _131550 s t) ((term20 _131550 s t f) = (term21 _131550 s t f))). Qed.
Lemma lem7067693 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (f : _131550 -> real) (p' : Prop) : term22 _131550 s t f p'.
Proof. exact (@lem7067692 _131550 s t f p'). Qed.
Lemma lem7067694 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (f : _131550 -> real) (p' : Prop) : (term22 _131550 s t f p') = (term23 _131550 s t f p').
Proof. exact (eq_refl (term22 _131550 s t f p')). Qed.
Lemma lem7067695 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (f : _131550 -> real) (p' : Prop) : term23 _131550 s t f p'.
Proof. exact (EQ_MP (@lem7067694 _131550 s t f p') (@lem7067693 _131550 s t f p')). Qed.
Lemma lem7067696 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (f : _131550 -> real) (p' : Prop) (q' : Prop) : term24 _131550 s t f p' q'.
Proof. exact (@lem7067695 _131550 s t f p' q'). Qed.
Lemma lem7067697 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (f : _131550 -> real) (p' : Prop) (q' : Prop) : (term24 _131550 s t f p' q') = (term25 _131550 s t f p' q').
Proof. exact (eq_refl (term24 _131550 s t f p' q')). Qed.
Lemma lem7067698 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (f : _131550 -> real) (p' : Prop) (q' : Prop) : term25 _131550 s t f p' q'.
Proof. exact (EQ_MP (@lem7067697 _131550 s t f p' q') (@lem7067696 _131550 s t f p' q')). Qed.
Lemma lem7067703 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) : (term9 _131550 s t) = (term9 _131550 s t).
Proof. exact (eq_refl (term9 _131550 s t)). Qed.
Lemma lem7067704 {_131550 : Type'} (f : _131550 -> real) (s : _131550 -> Prop) (t : _131550 -> Prop) (q' : Prop) : term26 _131550 f s t q'.
Proof. exact (@lem7067698 _131550 s t f (term9 _131550 s t) q'). Qed.
Lemma lem7067705 {_131550 : Type'} (f : _131550 -> real) (s : _131550 -> Prop) (t : _131550 -> Prop) (q' : Prop) : term27 _131550 f s t q'.
Proof. exact (@lem7067704 _131550 f s t q' (@lem7067703 _131550 s t)). Qed.
Lemma lem7067706 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (h1 : term9 _131550 s t) : term9 _131550 s t.
Proof. exact (h1). Qed.
Lemma lem7067707 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (h1 : term9 _131550 s t) : term28 _131550 s t.
Proof. exact (proj2 (@lem7067706 _131550 s t h1)). Qed.
Lemma lem7067708 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (h1 : term9 _131550 s t) : @DISJOINT _131550 s t.
Proof. exact (proj2 (@lem7067707 _131550 s t h1)). Qed.
Lemma lem7067709 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) : (@DISJOINT _131550 s t) = ((@DISJOINT _131550 s t) = True).
Proof. exact (@lem7 (@DISJOINT _131550 s t)). Qed.
Lemma lem7067711 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (h1 : term9 _131550 s t) : @FINITE _131550 t.
Proof. exact (proj1 (@lem7067707 _131550 s t h1)). Qed.
Lemma lem7067712 {_131550 : Type'} (t : _131550 -> Prop) : (@FINITE _131550 t) = ((@FINITE _131550 t) = True).
Proof. exact (@lem7 (@FINITE _131550 t)). Qed.
Lemma lem7067714 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (h1 : term9 _131550 s t) : @FINITE _131550 s.
Proof. exact (proj1 (@lem7067706 _131550 s t h1)). Qed.
Lemma lem7067715 {_131550 : Type'} (s : _131550 -> Prop) : (@FINITE _131550 s) = ((@FINITE _131550 s) = True).
Proof. exact (@lem7 (@FINITE _131550 s)). Qed.
Lemma lem7067720 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7067721 {_131550 : Type'} : (@sum _131550) = (@iterate real _131550 real_add).
Proof. exact (@lem7067720 _131550). Qed.
Lemma lem7067722 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) : (@UNION _131550 s t) = (@UNION _131550 s t).
Proof. exact (eq_refl (@UNION _131550 s t)). Qed.
Lemma lem7067723 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) : (term29 _131550 s t) = (term30 _131550 s t).
Proof. exact (MK_COMB (@lem7067721 _131550) (@lem7067722 _131550 s t)). Qed.
Lemma lem7067724 {_131550 : Type'} (f : _131550 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7067725 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (f : _131550 -> real) : (term20 _131550 s t f) = (term31 _131550 s t f).
Proof. exact (MK_COMB (@lem7067723 _131550 s t) (@lem7067724 _131550 f)). Qed.
Lemma lem7067727 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : term15 _120592 _120607 s op t f.
Proof. exact (EQ_MP (@lem7067672 _120592 _120607 s op t f) (@lem7067665 _120592 _120607 s op t f)). Qed.
Lemma lem7067728 {_131550 : Type'} (s : _131550 -> Prop) (op : type1627) (t : _131550 -> Prop) (f : _131550 -> real) : term32 _131550 s op t f.
Proof. exact (@lem7067727 _131550 real s op t f). Qed.
Lemma lem7067729 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (f : _131550 -> real) : term33 _131550 s t f.
Proof. exact (@lem7067728 _131550 s real_add t f). Qed.
Lemma lem7067733 : (@monoidal real real_add) = True.
Proof. exact (EQ_MP (@lem7067646) (@lem7067132)). Qed.
Lemma lem7067734 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7067735 : term34 = (and True).
Proof. exact (MK_COMB (@lem7067734) (@lem7067733)). Qed.
Lemma lem7067739 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (h1 : term9 _131550 s t) : (@FINITE _131550 s) = True.
Proof. exact (EQ_MP (@lem7067715 _131550 s) (@lem7067714 _131550 s t h1)). Qed.
Lemma lem7067740 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7067741 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (h1 : term9 _131550 s t) : (term35 _131550 s) = (and True).
Proof. exact (MK_COMB (@lem7067740) (@lem7067739 _131550 s t h1)). Qed.
Lemma lem7067745 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (h1 : term9 _131550 s t) : (@FINITE _131550 t) = True.
Proof. exact (EQ_MP (@lem7067712 _131550 t) (@lem7067711 _131550 s t h1)). Qed.
Lemma lem7067746 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7067747 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (h1 : term9 _131550 s t) : (term35 _131550 t) = (and True).
Proof. exact (MK_COMB (@lem7067746) (@lem7067745 _131550 s t h1)). Qed.
Lemma lem7067749 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (h1 : term9 _131550 s t) : (@DISJOINT _131550 s t) = True.
Proof. exact (EQ_MP (@lem7067709 _131550 s t) (@lem7067708 _131550 s t h1)). Qed.
Lemma lem7067750 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (h1 : term9 _131550 s t) : (term28 _131550 s t) = (True /\ True).
Proof. exact (MK_COMB (@lem7067747 _131550 s t h1) (@lem7067749 _131550 s t h1)). Qed.
Lemma lem7067752 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7067753 : (True /\ True) = True.
Proof. exact (@lem7067752 True). Qed.
Lemma lem7067754 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (h1 : term9 _131550 s t) : (term28 _131550 s t) = True.
Proof. exact (TRANS (@lem7067750 _131550 s t h1) (@lem7067753)). Qed.
Lemma lem7067755 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (h1 : term9 _131550 s t) : (term9 _131550 s t) = (True /\ True).
Proof. exact (MK_COMB (@lem7067741 _131550 s t h1) (@lem7067754 _131550 s t h1)). Qed.
Lemma lem7067757 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7067758 : (True /\ True) = True.
Proof. exact (@lem7067757 True). Qed.
Lemma lem7067759 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (h1 : term9 _131550 s t) : (term9 _131550 s t) = True.
Proof. exact (TRANS (@lem7067755 _131550 s t h1) (@lem7067758)). Qed.
Lemma lem7067760 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (h1 : term9 _131550 s t) : (term36 _131550 s t) = (True /\ True).
Proof. exact (MK_COMB (@lem7067735) (@lem7067759 _131550 s t h1)). Qed.
Lemma lem7067762 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7067763 : (True /\ True) = True.
Proof. exact (@lem7067762 True). Qed.
Lemma lem7067764 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (h1 : term9 _131550 s t) : (term36 _131550 s t) = True.
Proof. exact (TRANS (@lem7067760 _131550 s t h1) (@lem7067763)). Qed.
Lemma lem7067765 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (h1 : term9 _131550 s t) : True = (term36 _131550 s t).
Proof. exact (SYM (@lem7067764 _131550 s t h1)). Qed.
Lemma lem7067766 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (h1 : term9 _131550 s t) : term36 _131550 s t.
Proof. exact (EQ_MP (@lem7067765 _131550 s t h1) (@lem0)). Qed.
Lemma lem7067767 {_131550 : Type'} (f : _131550 -> real) (s : _131550 -> Prop) (t : _131550 -> Prop) (h1 : term9 _131550 s t) : (term31 _131550 s t f) = (term37 _131550 s t f).
Proof. exact (@lem7067729 _131550 s t f (@lem7067766 _131550 s t h1)). Qed.
Lemma lem7067768 {_131550 : Type'} (f : _131550 -> real) (s : _131550 -> Prop) (t : _131550 -> Prop) (h1 : term9 _131550 s t) : (term20 _131550 s t f) = (term37 _131550 s t f).
Proof. exact (TRANS (@lem7067725 _131550 s t f) (@lem7067767 _131550 f s t h1)). Qed.
Lemma lem7067769 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7067770 {_131550 : Type'} (f : _131550 -> real) (s : _131550 -> Prop) (t : _131550 -> Prop) (h1 : term9 _131550 s t) : (term38 _131550 s t f) = (term39 _131550 s t f).
Proof. exact (MK_COMB (@lem7067769) (@lem7067768 _131550 f s t h1)). Qed.
Lemma lem7067772 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7067773 {_131550 : Type'} : (@sum _131550) = (@iterate real _131550 real_add).
Proof. exact (@lem7067772 _131550). Qed.
Lemma lem7067774 {_131550 : Type'} (s : _131550 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7067775 {_131550 : Type'} (s : _131550 -> Prop) : (@sum _131550 s) = (@iterate real _131550 real_add s).
Proof. exact (MK_COMB (@lem7067773 _131550) (@lem7067774 _131550 s)). Qed.
Lemma lem7067776 {_131550 : Type'} (f : _131550 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7067777 {_131550 : Type'} (s : _131550 -> Prop) (f : _131550 -> real) : (@sum _131550 s f) = (@iterate real _131550 real_add s f).
Proof. exact (MK_COMB (@lem7067775 _131550 s) (@lem7067776 _131550 f)). Qed.
Lemma lem7067778 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7067779 {_131550 : Type'} (s : _131550 -> Prop) (f : _131550 -> real) : (term40 _131550 s f) = (term41 _131550 s f).
Proof. exact (MK_COMB (@lem7067778) (@lem7067777 _131550 s f)). Qed.
Lemma lem7067781 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7067782 {_131550 : Type'} : (@sum _131550) = (@iterate real _131550 real_add).
Proof. exact (@lem7067781 _131550). Qed.
Lemma lem7067783 {_131550 : Type'} (t : _131550 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7067784 {_131550 : Type'} (t : _131550 -> Prop) : (@sum _131550 t) = (@iterate real _131550 real_add t).
Proof. exact (MK_COMB (@lem7067782 _131550) (@lem7067783 _131550 t)). Qed.
Lemma lem7067785 {_131550 : Type'} (f : _131550 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7067786 {_131550 : Type'} (t : _131550 -> Prop) (f : _131550 -> real) : (@sum _131550 t f) = (@iterate real _131550 real_add t f).
Proof. exact (MK_COMB (@lem7067784 _131550 t) (@lem7067785 _131550 f)). Qed.
Lemma lem7067787 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (f : _131550 -> real) : (term21 _131550 s t f) = (term37 _131550 s t f).
Proof. exact (MK_COMB (@lem7067779 _131550 s f) (@lem7067786 _131550 t f)). Qed.
Lemma lem7067788 {_131550 : Type'} (f : _131550 -> real) (s : _131550 -> Prop) (t : _131550 -> Prop) (h1 : term9 _131550 s t) : ((term20 _131550 s t f) = (term21 _131550 s t f)) = ((term37 _131550 s t f) = (term37 _131550 s t f)).
Proof. exact (MK_COMB (@lem7067770 _131550 f s t h1) (@lem7067787 _131550 s t f)). Qed.
Lemma lem7067790 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7067791 (x : real) : (x = x) = True.
Proof. exact (@lem7067790 real x). Qed.
Lemma lem7067792 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (f : _131550 -> real) : ((term37 _131550 s t f) = (term37 _131550 s t f)) = True.
Proof. exact (@lem7067791 (term37 _131550 s t f)). Qed.
Lemma lem7067793 {_131550 : Type'} (f : _131550 -> real) (s : _131550 -> Prop) (t : _131550 -> Prop) (h1 : term9 _131550 s t) : ((term20 _131550 s t f) = (term21 _131550 s t f)) = True.
Proof. exact (TRANS (@lem7067788 _131550 f s t h1) (@lem7067792 _131550 s t f)). Qed.
Lemma lem7067794 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (f : _131550 -> real) : term42 _131550 s t f.
Proof. exact (fun h0 : term9 _131550 s t => @lem7067793 _131550 f s t h0). Qed.
Lemma lem7067795 {_131550 : Type'} (f : _131550 -> real) (s : _131550 -> Prop) (t : _131550 -> Prop) : term43 _131550 f s t.
Proof. exact (@lem7067705 _131550 f s t True). Qed.
Lemma lem7067796 {_131550 : Type'} (f : _131550 -> real) (s : _131550 -> Prop) (t : _131550 -> Prop) : (term44 _131550 s t f) = (term45 _131550 s t).
Proof. exact (@lem7067795 _131550 f s t (@lem7067794 _131550 s t f)). Qed.
Lemma lem7067798 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7067799 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) : (term45 _131550 s t) = True.
Proof. exact (@lem7067798 (term9 _131550 s t)). Qed.
Lemma lem7067800 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (f : _131550 -> real) : (term44 _131550 s t f) = True.
Proof. exact (TRANS (@lem7067796 _131550 f s t) (@lem7067799 _131550 s t)). Qed.
Lemma lem7067801 {_131550 : Type'} (s : _131550 -> Prop) (f : _131550 -> real) : (term46 _131550 s f) = (term47 _131550).
Proof. exact (fun_ext (fun t : _131550 -> Prop => @lem7067800 _131550 s t f)). Qed.
Lemma lem7067802 {_131550 : Type'} : (@all (_131550 -> Prop)) = (@all (_131550 -> Prop)).
Proof. exact (eq_refl (@all (_131550 -> Prop))). Qed.
Lemma lem7067803 {_131550 : Type'} (s : _131550 -> Prop) (f : _131550 -> real) : (term48 _131550 s f) = (term49 _131550).
Proof. exact (MK_COMB (@lem7067802 _131550) (@lem7067801 _131550 s f)). Qed.
Lemma lem7067805 {A : Type'} (t : Prop) : (term50 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7067806 {_131550 : Type'} (t : Prop) : (term51 _131550 t) = t.
Proof. exact (@lem7067805 (_131550 -> Prop) t). Qed.
Lemma lem7067807 {_131550 : Type'} : (term49 _131550) = True.
Proof. exact (@lem7067806 _131550 True). Qed.
Lemma lem7067808 {_131550 : Type'} (s : _131550 -> Prop) (f : _131550 -> real) : (term48 _131550 s f) = True.
Proof. exact (TRANS (@lem7067803 _131550 s f) (@lem7067807 _131550)). Qed.
Lemma lem7067809 {_131550 : Type'} (f : _131550 -> real) : (term52 _131550 f) = (term47 _131550).
Proof. exact (fun_ext (fun s : _131550 -> Prop => @lem7067808 _131550 s f)). Qed.
Lemma lem7067810 {_131550 : Type'} : (@all (_131550 -> Prop)) = (@all (_131550 -> Prop)).
Proof. exact (eq_refl (@all (_131550 -> Prop))). Qed.
Lemma lem7067811 {_131550 : Type'} (f : _131550 -> real) : (term53 _131550 f) = (term49 _131550).
Proof. exact (MK_COMB (@lem7067810 _131550) (@lem7067809 _131550 f)). Qed.
Lemma lem7067813 {A : Type'} (t : Prop) : (term50 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7067814 {_131550 : Type'} (t : Prop) : (term51 _131550 t) = t.
Proof. exact (@lem7067813 (_131550 -> Prop) t). Qed.
Lemma lem7067815 {_131550 : Type'} : (term49 _131550) = True.
Proof. exact (@lem7067814 _131550 True). Qed.
Lemma lem7067816 {_131550 : Type'} (f : _131550 -> real) : (term53 _131550 f) = True.
Proof. exact (TRANS (@lem7067811 _131550 f) (@lem7067815 _131550)). Qed.
Lemma lem7067817 {_131550 : Type'} : (term54 _131550) = (term55 _131550).
Proof. exact (fun_ext (fun f : _131550 -> real => @lem7067816 _131550 f)). Qed.
Lemma lem7067818 {_131550 : Type'} : (@all (_131550 -> real)) = (@all (_131550 -> real)).
Proof. exact (eq_refl (@all (_131550 -> real))). Qed.
Lemma lem7067819 {_131550 : Type'} : (term56 _131550) = (term57 _131550).
Proof. exact (MK_COMB (@lem7067818 _131550) (@lem7067817 _131550)). Qed.
Lemma lem7067821 {A : Type'} (t : Prop) : (term50 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7067822 {_131550 : Type'} (t : Prop) : (term58 _131550 t) = t.
Proof. exact (@lem7067821 (_131550 -> real) t). Qed.
Lemma lem7067823 {_131550 : Type'} : (term57 _131550) = True.
Proof. exact (@lem7067822 _131550 True). Qed.
Lemma lem7067824 {_131550 : Type'} : (term56 _131550) = True.
Proof. exact (TRANS (@lem7067819 _131550) (@lem7067823 _131550)). Qed.
Lemma lem7067825 {_131550 : Type'} : True = (term56 _131550).
Proof. exact (SYM (@lem7067824 _131550)). Qed.
Lemma lem7067826 {_131550 : Type'} : term56 _131550.
Proof. exact (EQ_MP (@lem7067825 _131550) (@lem0)). Qed.
