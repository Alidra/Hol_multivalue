Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_UNION_NONZERO_term_abbrevs.
Require Import ITERATE_UNION_NONZERO_spec.
Require Import MONOIDAL_REAL_ADD_spec.
Require Import NEUTRAL_REAL_ADD_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Require Import thm7064097_spec.
Require Import thm7064111_spec.
Lemma lem7178666 : (@monoidal real real_add) = ((@monoidal real real_add) = True).
Proof. exact (@lem7 (@monoidal real real_add)). Qed.
Lemma lem7178668 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem7178669 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term1 A B op.
Proof. exact (@lem7178668 A B h1 op). Qed.
Lemma lem7178670 {A B : Type'} (op : type1400 B) : (term1 A B op) = (term2 A B op).
Proof. exact (eq_refl (term1 A B op)). Qed.
Lemma lem7178671 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term2 A B op.
Proof. exact (EQ_MP (@lem7178670 A B op) (@lem7178669 A B op h1)). Qed.
Lemma lem7178672 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem7178673 {A B : Type'} (op : type1400 B) (h1 : term0 A B) (h2 : @monoidal B op) : term3 A B op.
Proof. exact (@lem7178671 A B op h1 (@lem7178672 B op h2)). Qed.
Lemma lem7178674 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term4 A B op.
Proof. exact (fun h0 : term0 A B => @lem7178673 A B op h0 h1). Qed.
Lemma lem7178675 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem7178676 {A B : Type'} (op : type1400 B) (h1 : term0 A B) (h2 : @monoidal B op) : term3 A B op.
Proof. exact (@lem7178674 A B op h2 (@lem7178675 A B h1)). Qed.
Lemma lem7178677 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term2 A B op.
Proof. exact (fun h0 : @monoidal B op => @lem7178676 A B op h1 h0). Qed.
Lemma lem7178678 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (fun op : type1400 B => @lem7178677 A B op h1). Qed.
Lemma lem7178679 {A B : Type'} : term5 A B.
Proof. exact (fun h0 : term0 A B => @lem7178678 A B h0). Qed.
Lemma lem7178680 {A B : Type'} : term0 A B.
Proof. exact (@lem7178679 A B (@lem6007453 A B)). Qed.
Lemma lem7178681 {A B : Type'} (op : type1400 B) : term1 A B op.
Proof. exact (@lem7178680 A B op). Qed.
Lemma lem7178682 {A B : Type'} (op : type1400 B) : (term1 A B op) = (term2 A B op).
Proof. exact (eq_refl (term1 A B op)). Qed.
Lemma lem7178684 (h1 : (@neutral real real_add) = term6) : (@neutral real real_add) = term6.
Proof. exact (h1). Qed.
Lemma lem7178685 (h1 : (@neutral real real_add) = term6) : term6 = (@neutral real real_add).
Proof. exact (SYM (@lem7178684 h1)). Qed.
Lemma lem7178686 (h1 : term6 = (@neutral real real_add)) : term6 = (@neutral real real_add).
Proof. exact (h1). Qed.
Lemma lem7178687 (h1 : term6 = (@neutral real real_add)) : (@neutral real real_add) = term6.
Proof. exact (SYM (@lem7178686 h1)). Qed.
Lemma lem7178688 : ((@neutral real real_add) = term6) = (term6 = (@neutral real real_add)).
Proof. exact (prop_ext (fun h1 : (@neutral real real_add) = term6 => @lem7178685 h1) (fun h1 : term6 = (@neutral real real_add) => @lem7178687 h1)). Qed.
Lemma lem7178717 : term6 = (@neutral real real_add).
Proof. exact (EQ_MP (@lem7178688) (@lem7065438)). Qed.
Lemma lem7178718 {_135252 : Type'} (f : _135252 -> real) (x : _135252) : (term7 _135252 f x) = (term7 _135252 f x).
Proof. exact (eq_refl (term7 _135252 f x)). Qed.
Lemma lem7178719 {_135252 : Type'} (f : _135252 -> real) (x : _135252) : ((f x) = term6) = ((f x) = (@neutral real real_add)).
Proof. exact (MK_COMB (@lem7178718 _135252 f x) (@lem7178717)). Qed.
Lemma lem7178722 {_135252 : Type'} (x : _135252) (s : _135252 -> Prop) (t : _135252 -> Prop) : (term8 _135252 x s t) = (term8 _135252 x s t).
Proof. exact (eq_refl (term8 _135252 x s t)). Qed.
Lemma lem7178723 {_135252 : Type'} (s : _135252 -> Prop) (t : _135252 -> Prop) (f : _135252 -> real) (x : _135252) : (term9 _135252 s t f x) = (term10 _135252 s t f x).
Proof. exact (MK_COMB (@lem7178722 _135252 x s t) (@lem7178719 _135252 f x)). Qed.
Lemma lem7178726 {_135252 : Type'} (s : _135252 -> Prop) (t : _135252 -> Prop) (f : _135252 -> real) : (term11 _135252 s t f) = (term12 _135252 s t f).
Proof. exact (fun_ext (fun x : _135252 => @lem7178723 _135252 s t f x)). Qed.
Lemma lem7178727 {_135252 : Type'} : (@all _135252) = (@all _135252).
Proof. exact (eq_refl (@all _135252)). Qed.
Lemma lem7178728 {_135252 : Type'} (s : _135252 -> Prop) (t : _135252 -> Prop) (f : _135252 -> real) : (term13 _135252 s t f) = (term14 _135252 s t f).
Proof. exact (MK_COMB (@lem7178727 _135252) (@lem7178726 _135252 s t f)). Qed.
Lemma lem7178733 {_135252 : Type'} (t : _135252 -> Prop) : (term15 _135252 t) = (term15 _135252 t).
Proof. exact (eq_refl (term15 _135252 t)). Qed.
Lemma lem7178734 {_135252 : Type'} (s : _135252 -> Prop) (t : _135252 -> Prop) (f : _135252 -> real) : (term16 _135252 s t f) = (term17 _135252 s t f).
Proof. exact (MK_COMB (@lem7178733 _135252 t) (@lem7178728 _135252 s t f)). Qed.
Lemma lem7178737 {_135252 : Type'} (s : _135252 -> Prop) : (term15 _135252 s) = (term15 _135252 s).
Proof. exact (eq_refl (term15 _135252 s)). Qed.
Lemma lem7178738 {_135252 : Type'} (s : _135252 -> Prop) (t : _135252 -> Prop) (f : _135252 -> real) : (term18 _135252 s t f) = (term19 _135252 s t f).
Proof. exact (MK_COMB (@lem7178737 _135252 s) (@lem7178734 _135252 s t f)). Qed.
Lemma lem7178741 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7178742 {_135252 : Type'} (s : _135252 -> Prop) (t : _135252 -> Prop) (f : _135252 -> real) : (term20 _135252 s t f) = (term21 _135252 s t f).
Proof. exact (MK_COMB (@lem7178741) (@lem7178738 _135252 s t f)). Qed.
Lemma lem7178746 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7178747 {_135252 : Type'} : (@sum _135252) = (@iterate real _135252 real_add).
Proof. exact (@lem7178746 _135252). Qed.
Lemma lem7178748 {_135252 : Type'} (s : _135252 -> Prop) (t : _135252 -> Prop) : (@UNION _135252 s t) = (@UNION _135252 s t).
Proof. exact (eq_refl (@UNION _135252 s t)). Qed.
Lemma lem7178749 {_135252 : Type'} (s : _135252 -> Prop) (t : _135252 -> Prop) : (term22 _135252 s t) = (term23 _135252 s t).
Proof. exact (MK_COMB (@lem7178747 _135252) (@lem7178748 _135252 s t)). Qed.
Lemma lem7178750 {_135252 : Type'} (f : _135252 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7178751 {_135252 : Type'} (s : _135252 -> Prop) (t : _135252 -> Prop) (f : _135252 -> real) : (term24 _135252 s t f) = (term25 _135252 s t f).
Proof. exact (MK_COMB (@lem7178749 _135252 s t) (@lem7178750 _135252 f)). Qed.
Lemma lem7178752 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7178753 {_135252 : Type'} (s : _135252 -> Prop) (t : _135252 -> Prop) (f : _135252 -> real) : (term26 _135252 s t f) = (term27 _135252 s t f).
Proof. exact (MK_COMB (@lem7178752) (@lem7178751 _135252 s t f)). Qed.
Lemma lem7178755 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7178756 {_135252 : Type'} : (@sum _135252) = (@iterate real _135252 real_add).
Proof. exact (@lem7178755 _135252). Qed.
Lemma lem7178757 {_135252 : Type'} (s : _135252 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7178758 {_135252 : Type'} (s : _135252 -> Prop) : (@sum _135252 s) = (@iterate real _135252 real_add s).
Proof. exact (MK_COMB (@lem7178756 _135252) (@lem7178757 _135252 s)). Qed.
Lemma lem7178759 {_135252 : Type'} (f : _135252 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7178760 {_135252 : Type'} (s : _135252 -> Prop) (f : _135252 -> real) : (@sum _135252 s f) = (@iterate real _135252 real_add s f).
Proof. exact (MK_COMB (@lem7178758 _135252 s) (@lem7178759 _135252 f)). Qed.
Lemma lem7178761 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7178762 {_135252 : Type'} (s : _135252 -> Prop) (f : _135252 -> real) : (term28 _135252 s f) = (term29 _135252 s f).
Proof. exact (MK_COMB (@lem7178761) (@lem7178760 _135252 s f)). Qed.
Lemma lem7178764 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7178765 {_135252 : Type'} : (@sum _135252) = (@iterate real _135252 real_add).
Proof. exact (@lem7178764 _135252). Qed.
Lemma lem7178766 {_135252 : Type'} (t : _135252 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7178767 {_135252 : Type'} (t : _135252 -> Prop) : (@sum _135252 t) = (@iterate real _135252 real_add t).
Proof. exact (MK_COMB (@lem7178765 _135252) (@lem7178766 _135252 t)). Qed.
Lemma lem7178768 {_135252 : Type'} (f : _135252 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7178769 {_135252 : Type'} (t : _135252 -> Prop) (f : _135252 -> real) : (@sum _135252 t f) = (@iterate real _135252 real_add t f).
Proof. exact (MK_COMB (@lem7178767 _135252 t) (@lem7178768 _135252 f)). Qed.
Lemma lem7178770 {_135252 : Type'} (s : _135252 -> Prop) (t : _135252 -> Prop) (f : _135252 -> real) : (term30 _135252 s t f) = (term31 _135252 s t f).
Proof. exact (MK_COMB (@lem7178762 _135252 s f) (@lem7178769 _135252 t f)). Qed.
Lemma lem7178771 {_135252 : Type'} (s : _135252 -> Prop) (t : _135252 -> Prop) (f : _135252 -> real) : ((term24 _135252 s t f) = (term30 _135252 s t f)) = ((term25 _135252 s t f) = (term31 _135252 s t f)).
Proof. exact (MK_COMB (@lem7178753 _135252 s t f) (@lem7178770 _135252 s t f)). Qed.
Lemma lem7178774 {_135252 : Type'} (s : _135252 -> Prop) (t : _135252 -> Prop) (f : _135252 -> real) : (term32 _135252 s t f) = (term33 _135252 s t f).
Proof. exact (MK_COMB (@lem7178742 _135252 s t f) (@lem7178771 _135252 s t f)). Qed.
Lemma lem7178777 {_135252 : Type'} (s : _135252 -> Prop) (f : _135252 -> real) : (term34 _135252 s f) = (term35 _135252 s f).
Proof. exact (fun_ext (fun t : _135252 -> Prop => @lem7178774 _135252 s t f)). Qed.
Lemma lem7178778 {_135252 : Type'} : (@all (_135252 -> Prop)) = (@all (_135252 -> Prop)).
Proof. exact (eq_refl (@all (_135252 -> Prop))). Qed.
Lemma lem7178779 {_135252 : Type'} (s : _135252 -> Prop) (f : _135252 -> real) : (term36 _135252 s f) = (term37 _135252 s f).
Proof. exact (MK_COMB (@lem7178778 _135252) (@lem7178777 _135252 s f)). Qed.
Lemma lem7178784 {_135252 : Type'} (f : _135252 -> real) : (term38 _135252 f) = (term39 _135252 f).
Proof. exact (fun_ext (fun s : _135252 -> Prop => @lem7178779 _135252 s f)). Qed.
Lemma lem7178785 {_135252 : Type'} : (@all (_135252 -> Prop)) = (@all (_135252 -> Prop)).
Proof. exact (eq_refl (@all (_135252 -> Prop))). Qed.
Lemma lem7178786 {_135252 : Type'} (f : _135252 -> real) : (term40 _135252 f) = (term41 _135252 f).
Proof. exact (MK_COMB (@lem7178785 _135252) (@lem7178784 _135252 f)). Qed.
Lemma lem7178791 {_135252 : Type'} : (term42 _135252) = (term43 _135252).
Proof. exact (fun_ext (fun f : _135252 -> real => @lem7178786 _135252 f)). Qed.
Lemma lem7178792 {_135252 : Type'} : (@all (_135252 -> real)) = (@all (_135252 -> real)).
Proof. exact (eq_refl (@all (_135252 -> real))). Qed.
Lemma lem7178793 {_135252 : Type'} : (term44 _135252) = (term45 _135252).
Proof. exact (MK_COMB (@lem7178792 _135252) (@lem7178791 _135252)). Qed.
Lemma lem7178798 {_135252 : Type'} : (term45 _135252) = (term44 _135252).
Proof. exact (SYM (@lem7178793 _135252)). Qed.
Lemma lem7178800 {A B : Type'} (op : type1400 B) : term2 A B op.
Proof. exact (EQ_MP (@lem7178682 A B op) (@lem7178681 A B op)). Qed.
Lemma lem7178801 {_135252 : Type'} (op : type1627) : term46 _135252 op.
Proof. exact (@lem7178800 _135252 real op). Qed.
Lemma lem7178802 {_135252 : Type'} : term47 _135252.
Proof. exact (@lem7178801 _135252 real_add). Qed.
Lemma lem7178804 : (@monoidal real real_add) = True.
Proof. exact (EQ_MP (@lem7178666) (@lem7067132)). Qed.
Lemma lem7178805 : True = (@monoidal real real_add).
Proof. exact (SYM (@lem7178804)). Qed.
Lemma lem7178806 : @monoidal real real_add.
Proof. exact (EQ_MP (@lem7178805) (@lem0)). Qed.
Lemma lem7178807 {_135252 : Type'} : term45 _135252.
Proof. exact (@lem7178802 _135252 (@lem7178806)). Qed.
Lemma lem7178808 {_135252 : Type'} : term44 _135252.
Proof. exact (EQ_MP (@lem7178798 _135252) (@lem7178807 _135252)). Qed.
