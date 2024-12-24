Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_ADD_term_abbrevs.
Require Import ITERATE_OP_spec.
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
Lemma lem7068650 : (@monoidal real real_add) = ((@monoidal real real_add) = True).
Proof. exact (@lem7 (@monoidal real real_add)). Qed.
Lemma lem7068652 {_122572 _122573 : Type'} (op : type1400 _122573) : term0 _122572 _122573 op.
Proof. exact (@lem6013661 _122572 _122573 op). Qed.
Lemma lem7068653 {_122572 _122573 : Type'} (op : type1400 _122573) : (term0 _122572 _122573 op) = (term1 _122572 _122573 op).
Proof. exact (eq_refl (term0 _122572 _122573 op)). Qed.
Lemma lem7068654 {_122572 _122573 : Type'} (op : type1400 _122573) : term1 _122572 _122573 op.
Proof. exact (EQ_MP (@lem7068653 _122572 _122573 op) (@lem7068652 _122572 _122573 op)). Qed.
Lemma lem7068655 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : @monoidal _122573 op.
Proof. exact (h1). Qed.
Lemma lem7068656 {_122572 _122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : term2 _122572 _122573 op.
Proof. exact (@lem7068654 _122572 _122573 op (@lem7068655 _122573 op h1)). Qed.
Lemma lem7068657 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : term3 _122572 _122573 op f.
Proof. exact (@lem7068656 _122572 _122573 op h1 f). Qed.
Lemma lem7068658 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) : (term3 _122572 _122573 op f) = (term4 _122572 _122573 f op).
Proof. exact (eq_refl (term3 _122572 _122573 op f)). Qed.
Lemma lem7068659 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : term4 _122572 _122573 f op.
Proof. exact (EQ_MP (@lem7068658 _122572 _122573 f op) (@lem7068657 _122572 _122573 f op h1)). Qed.
Lemma lem7068660 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : term5 _122572 _122573 f op g.
Proof. exact (@lem7068659 _122572 _122573 f op h1 g). Qed.
Lemma lem7068661 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) : (term5 _122572 _122573 f op g) = (term6 _122572 _122573 f op g).
Proof. exact (eq_refl (term5 _122572 _122573 f op g)). Qed.
Lemma lem7068662 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : term6 _122572 _122573 f op g.
Proof. exact (EQ_MP (@lem7068661 _122572 _122573 f op g) (@lem7068660 _122572 _122573 f g op h1)). Qed.
Lemma lem7068663 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (s : _122572 -> Prop) (op : type1400 _122573) (h1 : @monoidal _122573 op) : term7 _122572 _122573 f op g s.
Proof. exact (@lem7068662 _122572 _122573 f g op h1 s). Qed.
Lemma lem7068664 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) : (term7 _122572 _122573 f op g s) = (term8 _122572 _122573 f op s g).
Proof. exact (eq_refl (term7 _122572 _122573 f op g s)). Qed.
Lemma lem7068665 {_122572 _122573 : Type'} (f : _122572 -> _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : term8 _122572 _122573 f op s g.
Proof. exact (EQ_MP (@lem7068664 _122572 _122573 f op s g) (@lem7068663 _122572 _122573 f g s op h1)). Qed.
Lemma lem7068666 {_122572 : Type'} (s : _122572 -> Prop) (h1 : @FINITE _122572 s) : @FINITE _122572 s.
Proof. exact (h1). Qed.
Lemma lem7068667 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (s : _122572 -> Prop) (op : type1400 _122573) (h1 : @FINITE _122572 s) (h2 : @monoidal _122573 op) : (term9 _122572 _122573 s op f g) = (term10 _122572 _122573 f op s g).
Proof. exact (@lem7068665 _122572 _122573 f s g op h2 (@lem7068666 _122572 s h1)). Qed.
Lemma lem7068668 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (s : _122572 -> Prop) (h1 : @FINITE _122572 s) : term11 _122572 _122573 f op s g.
Proof. exact (fun h0 : @monoidal _122573 op => @lem7068667 _122572 _122573 f g s op h1 h0). Qed.
Lemma lem7068669 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) : term12 _122572 _122573 f op s g.
Proof. exact (fun h0 : @FINITE _122572 s => @lem7068668 _122572 _122573 f op g s h0). Qed.
Lemma lem7068671 (p : Prop) (q : Prop) (r : Prop) : (term13 p q r) = (term14 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem7068676 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) : (term12 _122572 _122573 f op s g) = (term15 _122572 _122573 f op s g).
Proof. exact (@lem7068671 (@FINITE _122572 s) (@monoidal _122573 op) ((term9 _122572 _122573 s op f g) = (term10 _122572 _122573 f op s g))). Qed.
Lemma lem7068693 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term16 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7068694 (p : Prop) (q : Prop) (p' : Prop) : term17 p q p'.
Proof. exact (fun q' : Prop => @lem7068693 p q p' q'). Qed.
Lemma lem7068695 (p : Prop) (q : Prop) : term18 p q.
Proof. exact (fun p' : Prop => @lem7068694 p q p'). Qed.
Lemma lem7068696 {_131713 : Type'} (f : _131713 -> real) (s : _131713 -> Prop) (g : _131713 -> real) : term19 _131713 f s g.
Proof. exact (@lem7068695 (@FINITE _131713 s) ((term20 _131713 s f g) = (term21 _131713 f s g))). Qed.
Lemma lem7068697 {_131713 : Type'} (f : _131713 -> real) (s : _131713 -> Prop) (g : _131713 -> real) (p' : Prop) : term22 _131713 f s g p'.
Proof. exact (@lem7068696 _131713 f s g p'). Qed.
Lemma lem7068698 {_131713 : Type'} (f : _131713 -> real) (s : _131713 -> Prop) (g : _131713 -> real) (p' : Prop) : (term22 _131713 f s g p') = (term23 _131713 f s g p').
Proof. exact (eq_refl (term22 _131713 f s g p')). Qed.
Lemma lem7068699 {_131713 : Type'} (f : _131713 -> real) (s : _131713 -> Prop) (g : _131713 -> real) (p' : Prop) : term23 _131713 f s g p'.
Proof. exact (EQ_MP (@lem7068698 _131713 f s g p') (@lem7068697 _131713 f s g p')). Qed.
Lemma lem7068700 {_131713 : Type'} (f : _131713 -> real) (s : _131713 -> Prop) (g : _131713 -> real) (p' : Prop) (q' : Prop) : term24 _131713 f s g p' q'.
Proof. exact (@lem7068699 _131713 f s g p' q'). Qed.
Lemma lem7068701 {_131713 : Type'} (f : _131713 -> real) (s : _131713 -> Prop) (g : _131713 -> real) (p' : Prop) (q' : Prop) : (term24 _131713 f s g p' q') = (term25 _131713 f s g p' q').
Proof. exact (eq_refl (term24 _131713 f s g p' q')). Qed.
Lemma lem7068702 {_131713 : Type'} (f : _131713 -> real) (s : _131713 -> Prop) (g : _131713 -> real) (p' : Prop) (q' : Prop) : term25 _131713 f s g p' q'.
Proof. exact (EQ_MP (@lem7068701 _131713 f s g p' q') (@lem7068700 _131713 f s g p' q')). Qed.
Lemma lem7068703 {_131713 : Type'} (s : _131713 -> Prop) : (@FINITE _131713 s) = (@FINITE _131713 s).
Proof. exact (eq_refl (@FINITE _131713 s)). Qed.
Lemma lem7068704 {_131713 : Type'} (f : _131713 -> real) (g : _131713 -> real) (s : _131713 -> Prop) (q' : Prop) : term26 _131713 f g s q'.
Proof. exact (@lem7068702 _131713 f s g (@FINITE _131713 s) q'). Qed.
Lemma lem7068705 {_131713 : Type'} (f : _131713 -> real) (g : _131713 -> real) (s : _131713 -> Prop) (q' : Prop) : term27 _131713 f g s q'.
Proof. exact (@lem7068704 _131713 f g s q' (@lem7068703 _131713 s)). Qed.
Lemma lem7068706 {_131713 : Type'} (s : _131713 -> Prop) (h1 : @FINITE _131713 s) : @FINITE _131713 s.
Proof. exact (h1). Qed.
Lemma lem7068707 {_131713 : Type'} (s : _131713 -> Prop) : (@FINITE _131713 s) = ((@FINITE _131713 s) = True).
Proof. exact (@lem7 (@FINITE _131713 s)). Qed.
Lemma lem7068712 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7068713 {_131713 : Type'} : (@sum _131713) = (@iterate real _131713 real_add).
Proof. exact (@lem7068712 _131713). Qed.
Lemma lem7068714 {_131713 : Type'} (s : _131713 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7068715 {_131713 : Type'} (s : _131713 -> Prop) : (@sum _131713 s) = (@iterate real _131713 real_add s).
Proof. exact (MK_COMB (@lem7068713 _131713) (@lem7068714 _131713 s)). Qed.
Lemma lem7068716 {_131713 : Type'} (f : _131713 -> real) (g : _131713 -> real) : (term28 _131713 f g) = (term28 _131713 f g).
Proof. exact (eq_refl (term28 _131713 f g)). Qed.
Lemma lem7068717 {_131713 : Type'} (s : _131713 -> Prop) (f : _131713 -> real) (g : _131713 -> real) : (term20 _131713 s f g) = (term29 _131713 s f g).
Proof. exact (MK_COMB (@lem7068715 _131713 s) (@lem7068716 _131713 f g)). Qed.
Lemma lem7068719 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) : term15 _122572 _122573 f op s g.
Proof. exact (EQ_MP (@lem7068676 _122572 _122573 f op s g) (@lem7068669 _122572 _122573 f op s g)). Qed.
Lemma lem7068720 {_131713 : Type'} (f : _131713 -> real) (op : type1627) (s : _131713 -> Prop) (g : _131713 -> real) : term30 _131713 f op s g.
Proof. exact (@lem7068719 _131713 real f op s g). Qed.
Lemma lem7068721 {_131713 : Type'} (f : _131713 -> real) (s : _131713 -> Prop) (g : _131713 -> real) : term31 _131713 f s g.
Proof. exact (@lem7068720 _131713 f real_add s g). Qed.
Lemma lem7068725 {_131713 : Type'} (s : _131713 -> Prop) (h1 : @FINITE _131713 s) : (@FINITE _131713 s) = True.
Proof. exact (EQ_MP (@lem7068707 _131713 s) (@lem7068706 _131713 s h1)). Qed.
Lemma lem7068726 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7068727 {_131713 : Type'} (s : _131713 -> Prop) (h1 : @FINITE _131713 s) : (term32 _131713 s) = (and True).
Proof. exact (MK_COMB (@lem7068726) (@lem7068725 _131713 s h1)). Qed.
Lemma lem7068729 : (@monoidal real real_add) = True.
Proof. exact (EQ_MP (@lem7068650) (@lem7067132)). Qed.
Lemma lem7068730 {_131713 : Type'} (s : _131713 -> Prop) (h1 : @FINITE _131713 s) : (term33 _131713 s) = (True /\ True).
Proof. exact (MK_COMB (@lem7068727 _131713 s h1) (@lem7068729)). Qed.
Lemma lem7068732 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7068733 : (True /\ True) = True.
Proof. exact (@lem7068732 True). Qed.
Lemma lem7068734 {_131713 : Type'} (s : _131713 -> Prop) (h1 : @FINITE _131713 s) : (term33 _131713 s) = True.
Proof. exact (TRANS (@lem7068730 _131713 s h1) (@lem7068733)). Qed.
Lemma lem7068735 {_131713 : Type'} (s : _131713 -> Prop) (h1 : @FINITE _131713 s) : True = (term33 _131713 s).
Proof. exact (SYM (@lem7068734 _131713 s h1)). Qed.
Lemma lem7068736 {_131713 : Type'} (s : _131713 -> Prop) (h1 : @FINITE _131713 s) : term33 _131713 s.
Proof. exact (EQ_MP (@lem7068735 _131713 s h1) (@lem0)). Qed.
Lemma lem7068737 {_131713 : Type'} (f : _131713 -> real) (g : _131713 -> real) (s : _131713 -> Prop) (h1 : @FINITE _131713 s) : (term29 _131713 s f g) = (term34 _131713 f s g).
Proof. exact (@lem7068721 _131713 f s g (@lem7068736 _131713 s h1)). Qed.
Lemma lem7068738 {_131713 : Type'} (f : _131713 -> real) (g : _131713 -> real) (s : _131713 -> Prop) (h1 : @FINITE _131713 s) : (term20 _131713 s f g) = (term34 _131713 f s g).
Proof. exact (TRANS (@lem7068717 _131713 s f g) (@lem7068737 _131713 f g s h1)). Qed.
Lemma lem7068739 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7068740 {_131713 : Type'} (f : _131713 -> real) (g : _131713 -> real) (s : _131713 -> Prop) (h1 : @FINITE _131713 s) : (term35 _131713 s f g) = (term36 _131713 f s g).
Proof. exact (MK_COMB (@lem7068739) (@lem7068738 _131713 f g s h1)). Qed.
Lemma lem7068742 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7068743 {_131713 : Type'} : (@sum _131713) = (@iterate real _131713 real_add).
Proof. exact (@lem7068742 _131713). Qed.
Lemma lem7068744 {_131713 : Type'} (s : _131713 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7068745 {_131713 : Type'} (s : _131713 -> Prop) : (@sum _131713 s) = (@iterate real _131713 real_add s).
Proof. exact (MK_COMB (@lem7068743 _131713) (@lem7068744 _131713 s)). Qed.
Lemma lem7068746 {_131713 : Type'} (f : _131713 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7068747 {_131713 : Type'} (s : _131713 -> Prop) (f : _131713 -> real) : (@sum _131713 s f) = (@iterate real _131713 real_add s f).
Proof. exact (MK_COMB (@lem7068745 _131713 s) (@lem7068746 _131713 f)). Qed.
Lemma lem7068748 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7068749 {_131713 : Type'} (s : _131713 -> Prop) (f : _131713 -> real) : (term37 _131713 s f) = (term38 _131713 s f).
Proof. exact (MK_COMB (@lem7068748) (@lem7068747 _131713 s f)). Qed.
Lemma lem7068751 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7068752 {_131713 : Type'} : (@sum _131713) = (@iterate real _131713 real_add).
Proof. exact (@lem7068751 _131713). Qed.
Lemma lem7068753 {_131713 : Type'} (s : _131713 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7068754 {_131713 : Type'} (s : _131713 -> Prop) : (@sum _131713 s) = (@iterate real _131713 real_add s).
Proof. exact (MK_COMB (@lem7068752 _131713) (@lem7068753 _131713 s)). Qed.
Lemma lem7068755 {_131713 : Type'} (g : _131713 -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7068756 {_131713 : Type'} (s : _131713 -> Prop) (g : _131713 -> real) : (@sum _131713 s g) = (@iterate real _131713 real_add s g).
Proof. exact (MK_COMB (@lem7068754 _131713 s) (@lem7068755 _131713 g)). Qed.
Lemma lem7068757 {_131713 : Type'} (f : _131713 -> real) (s : _131713 -> Prop) (g : _131713 -> real) : (term21 _131713 f s g) = (term34 _131713 f s g).
Proof. exact (MK_COMB (@lem7068749 _131713 s f) (@lem7068756 _131713 s g)). Qed.
Lemma lem7068758 {_131713 : Type'} (f : _131713 -> real) (g : _131713 -> real) (s : _131713 -> Prop) (h1 : @FINITE _131713 s) : ((term20 _131713 s f g) = (term21 _131713 f s g)) = ((term34 _131713 f s g) = (term34 _131713 f s g)).
Proof. exact (MK_COMB (@lem7068740 _131713 f g s h1) (@lem7068757 _131713 f s g)). Qed.
Lemma lem7068760 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7068761 (x : real) : (x = x) = True.
Proof. exact (@lem7068760 real x). Qed.
Lemma lem7068762 {_131713 : Type'} (f : _131713 -> real) (s : _131713 -> Prop) (g : _131713 -> real) : ((term34 _131713 f s g) = (term34 _131713 f s g)) = True.
Proof. exact (@lem7068761 (term34 _131713 f s g)). Qed.
Lemma lem7068763 {_131713 : Type'} (f : _131713 -> real) (g : _131713 -> real) (s : _131713 -> Prop) (h1 : @FINITE _131713 s) : ((term20 _131713 s f g) = (term21 _131713 f s g)) = True.
Proof. exact (TRANS (@lem7068758 _131713 f g s h1) (@lem7068762 _131713 f s g)). Qed.
Lemma lem7068764 {_131713 : Type'} (f : _131713 -> real) (s : _131713 -> Prop) (g : _131713 -> real) : term39 _131713 f s g.
Proof. exact (fun h0 : @FINITE _131713 s => @lem7068763 _131713 f g s h0). Qed.
Lemma lem7068765 {_131713 : Type'} (f : _131713 -> real) (g : _131713 -> real) (s : _131713 -> Prop) : term40 _131713 f g s.
Proof. exact (@lem7068705 _131713 f g s True). Qed.
Lemma lem7068766 {_131713 : Type'} (f : _131713 -> real) (g : _131713 -> real) (s : _131713 -> Prop) : (term41 _131713 f s g) = (term42 _131713 s).
Proof. exact (@lem7068765 _131713 f g s (@lem7068764 _131713 f s g)). Qed.
Lemma lem7068768 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7068769 {_131713 : Type'} (s : _131713 -> Prop) : (term42 _131713 s) = True.
Proof. exact (@lem7068768 (@FINITE _131713 s)). Qed.
Lemma lem7068770 {_131713 : Type'} (f : _131713 -> real) (s : _131713 -> Prop) (g : _131713 -> real) : (term41 _131713 f s g) = True.
Proof. exact (TRANS (@lem7068766 _131713 f g s) (@lem7068769 _131713 s)). Qed.
Lemma lem7068771 {_131713 : Type'} (f : _131713 -> real) (g : _131713 -> real) : (term43 _131713 f g) = (term44 _131713).
Proof. exact (fun_ext (fun s : _131713 -> Prop => @lem7068770 _131713 f s g)). Qed.
Lemma lem7068772 {_131713 : Type'} : (@all (_131713 -> Prop)) = (@all (_131713 -> Prop)).
Proof. exact (eq_refl (@all (_131713 -> Prop))). Qed.
Lemma lem7068773 {_131713 : Type'} (f : _131713 -> real) (g : _131713 -> real) : (term45 _131713 f g) = (term46 _131713).
Proof. exact (MK_COMB (@lem7068772 _131713) (@lem7068771 _131713 f g)). Qed.
Lemma lem7068775 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7068776 {_131713 : Type'} (t : Prop) : (term48 _131713 t) = t.
Proof. exact (@lem7068775 (_131713 -> Prop) t). Qed.
Lemma lem7068777 {_131713 : Type'} : (term46 _131713) = True.
Proof. exact (@lem7068776 _131713 True). Qed.
Lemma lem7068778 {_131713 : Type'} (f : _131713 -> real) (g : _131713 -> real) : (term45 _131713 f g) = True.
Proof. exact (TRANS (@lem7068773 _131713 f g) (@lem7068777 _131713)). Qed.
Lemma lem7068779 {_131713 : Type'} (f : _131713 -> real) : (term49 _131713 f) = (term50 _131713).
Proof. exact (fun_ext (fun g : _131713 -> real => @lem7068778 _131713 f g)). Qed.
Lemma lem7068780 {_131713 : Type'} : (@all (_131713 -> real)) = (@all (_131713 -> real)).
Proof. exact (eq_refl (@all (_131713 -> real))). Qed.
Lemma lem7068781 {_131713 : Type'} (f : _131713 -> real) : (term51 _131713 f) = (term52 _131713).
Proof. exact (MK_COMB (@lem7068780 _131713) (@lem7068779 _131713 f)). Qed.
Lemma lem7068783 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7068784 {_131713 : Type'} (t : Prop) : (term53 _131713 t) = t.
Proof. exact (@lem7068783 (_131713 -> real) t). Qed.
Lemma lem7068785 {_131713 : Type'} : (term52 _131713) = True.
Proof. exact (@lem7068784 _131713 True). Qed.
Lemma lem7068786 {_131713 : Type'} (f : _131713 -> real) : (term51 _131713 f) = True.
Proof. exact (TRANS (@lem7068781 _131713 f) (@lem7068785 _131713)). Qed.
Lemma lem7068787 {_131713 : Type'} : (term54 _131713) = (term50 _131713).
Proof. exact (fun_ext (fun f : _131713 -> real => @lem7068786 _131713 f)). Qed.
Lemma lem7068788 {_131713 : Type'} : (@all (_131713 -> real)) = (@all (_131713 -> real)).
Proof. exact (eq_refl (@all (_131713 -> real))). Qed.
Lemma lem7068789 {_131713 : Type'} : (term55 _131713) = (term52 _131713).
Proof. exact (MK_COMB (@lem7068788 _131713) (@lem7068787 _131713)). Qed.
Lemma lem7068791 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7068792 {_131713 : Type'} (t : Prop) : (term53 _131713 t) = t.
Proof. exact (@lem7068791 (_131713 -> real) t). Qed.
Lemma lem7068793 {_131713 : Type'} : (term52 _131713) = True.
Proof. exact (@lem7068792 _131713 True). Qed.
Lemma lem7068794 {_131713 : Type'} : (term55 _131713) = True.
Proof. exact (TRANS (@lem7068789 _131713) (@lem7068793 _131713)). Qed.
Lemma lem7068795 {_131713 : Type'} : True = (term55 _131713).
Proof. exact (SYM (@lem7068794 _131713)). Qed.
Lemma lem7068796 {_131713 : Type'} : term55 _131713.
Proof. exact (EQ_MP (@lem7068795 _131713) (@lem0)). Qed.
