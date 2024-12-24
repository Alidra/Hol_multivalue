Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_OP_GEN_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import EQ_TRANS_spec.
Require Import FINITE_UNION_spec.
Require Import IN_UNION_spec.
Require Import ITERATE_OP_spec.
Require Import ITERATE_SUPERSET_spec.
Require Import ITERATE_SUPPORT_spec.
Require Import SUBSET_spec.
Require Import monoidal_spec.
Require Import support_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
Require Import thm19024_spec.
Require Import thm19025_spec.
Require Import thm19030_spec.
Require Import thm19031_spec.
Require Import thm19490_spec.
Require Import thm196_spec.
Require Import thm197_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem6160749 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3204949 A s). Qed.
Lemma lem6160750 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem6160751 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem6160750 A s) (@lem6160749 A s)). Qed.
Lemma lem6160752 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term2 A s t.
Proof. exact (@lem6160751 A s t). Qed.
Lemma lem6160753 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = (term3 A s t).
Proof. exact (eq_refl (term2 A s t)). Qed.
Lemma lem6160754 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term3 A s t.
Proof. exact (EQ_MP (@lem6160753 A s t) (@lem6160752 A s t)). Qed.
Lemma lem6160755 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term4 A s t x.
Proof. exact (@lem6160754 A s t x). Qed.
Lemma lem6160756 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term4 A s t x) = ((term5 A x s t) = (term6 A s x t)).
Proof. exact (eq_refl (term4 A s t x)). Qed.
Lemma lem6160758 {A : Type'} (s : A -> Prop) : term7 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem6160759 {A : Type'} (s : A -> Prop) : (term7 A s) = (term8 A s).
Proof. exact (eq_refl (term7 A s)). Qed.
Lemma lem6160760 {A : Type'} (s : A -> Prop) : term8 A s.
Proof. exact (EQ_MP (@lem6160759 A s) (@lem6160758 A s)). Qed.
Lemma lem6160761 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term9 A s t.
Proof. exact (@lem6160760 A s t). Qed.
Lemma lem6160762 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term9 A s t) = ((@SUBSET A s t) = (term10 A s t)).
Proof. exact (eq_refl (term9 A s t)). Qed.
Lemma lem6160788 {_83095 : Type'} : term11 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem6160789 {_83095 : Type'} (p : _83095 -> Prop) : term12 _83095 p.
Proof. exact (@lem6160788 _83095 p). Qed.
Lemma lem6160790 {_83095 : Type'} (p : _83095 -> Prop) : (term12 _83095 p) = (term13 _83095 p).
Proof. exact (eq_refl (term12 _83095 p)). Qed.
Lemma lem6160791 {_83095 : Type'} (p : _83095 -> Prop) : term13 _83095 p.
Proof. exact (EQ_MP (@lem6160790 _83095 p) (@lem6160789 _83095 p)). Qed.
Lemma lem6160792 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term14 _83095 p x.
Proof. exact (@lem6160791 _83095 p x). Qed.
Lemma lem6160793 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term14 _83095 p x) = ((term15 _83095 x p) = (p x)).
Proof. exact (eq_refl (term14 _83095 p x)). Qed.
Lemma lem6160802 {A B : Type'} (s : A -> Prop) : term16 A B s.
Proof. exact (@lem5716761 A B s). Qed.
Lemma lem6160803 {A B : Type'} (s : A -> Prop) : (term16 A B s) = (term17 A B s).
Proof. exact (eq_refl (term16 A B s)). Qed.
Lemma lem6160804 {A B : Type'} (s : A -> Prop) : term17 A B s.
Proof. exact (EQ_MP (@lem6160803 A B s) (@lem6160802 A B s)). Qed.
Lemma lem6160805 {A B : Type'} (s : A -> Prop) (f : A -> B) : term18 A B s f.
Proof. exact (@lem6160804 A B s f). Qed.
Lemma lem6160806 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term18 A B s f) = (term19 A B s f).
Proof. exact (eq_refl (term18 A B s f)). Qed.
Lemma lem6160807 {A B : Type'} (s : A -> Prop) (f : A -> B) : term19 A B s f.
Proof. exact (EQ_MP (@lem6160806 A B s f) (@lem6160805 A B s f)). Qed.
Lemma lem6160808 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term20 A B s f op.
Proof. exact (@lem6160807 A B s f op). Qed.
Lemma lem6160809 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term20 A B s f op) = ((@support A B op f s) = (term21 A B s f op)).
Proof. exact (eq_refl (term20 A B s f op)). Qed.
Lemma lem6160811 {A B : Type'} (op : type1400 B) : term22 A B op.
Proof. exact (@lem6016892 A B op). Qed.
Lemma lem6160812 {A B : Type'} (op : type1400 B) : (term22 A B op) = (term23 A B op).
Proof. exact (eq_refl (term22 A B op)). Qed.
Lemma lem6160814 {A : Type'} (h1 : term24 A) : term24 A.
Proof. exact (h1). Qed.
Lemma lem6160815 {A : Type'} (x : A) (h1 : term24 A) : term25 A x.
Proof. exact (@lem6160814 A h1 x). Qed.
Lemma lem6160816 {A : Type'} (x : A) : (term25 A x) = (term26 A x).
Proof. exact (eq_refl (term25 A x)). Qed.
Lemma lem6160817 {A : Type'} (x : A) (h1 : term24 A) : term26 A x.
Proof. exact (EQ_MP (@lem6160816 A x) (@lem6160815 A x h1)). Qed.
Lemma lem6160818 {A : Type'} (x : A) (y : A) (h1 : term24 A) : term27 A x y.
Proof. exact (@lem6160817 A x h1 y). Qed.
Lemma lem6160819 {A : Type'} (y : A) (x : A) : (term27 A x y) = (term28 A y x).
Proof. exact (eq_refl (term27 A x y)). Qed.
Lemma lem6160820 {A : Type'} (y : A) (x : A) (h1 : term24 A) : term28 A y x.
Proof. exact (EQ_MP (@lem6160819 A y x) (@lem6160818 A x y h1)). Qed.
Lemma lem6160821 {A : Type'} (y : A) (x : A) (z : A) (h1 : term24 A) : term29 A y x z.
Proof. exact (@lem6160820 A y x h1 z). Qed.
Lemma lem6160822 {A : Type'} (y : A) (x : A) (z : A) : (term29 A y x z) = (term30 A y x z).
Proof. exact (eq_refl (term29 A y x z)). Qed.
Lemma lem6160823 {A : Type'} (y : A) (x : A) (z : A) (h1 : term24 A) : term30 A y x z.
Proof. exact (EQ_MP (@lem6160822 A y x z) (@lem6160821 A y x z h1)). Qed.
Lemma lem6160824 {A : Type'} (x : A) (y : A) (z : A) (h1 : term31 A x y z) : term31 A x y z.
Proof. exact (h1). Qed.
Lemma lem6160825 {A : Type'} (x : A) (y : A) (z : A) (h1 : term24 A) (h2 : term31 A x y z) : x = z.
Proof. exact (@lem6160823 A y x z h1 (@lem6160824 A x y z h2)). Qed.
Lemma lem6160826 {A : Type'} (x : A) (y : A) (z : A) (h1 : term31 A x y z) : term32 A x z.
Proof. exact (fun h0 : term24 A => @lem6160825 A x y z h0 h1). Qed.
Lemma lem6160827 {A : Type'} (x : A) (z : A) (h1 : term33 A x z) : term33 A x z.
Proof. exact (h1). Qed.
Lemma lem6160828 {A : Type'} (x : A) (z : A) (h1 : term33 A x z) : term32 A x z.
Proof. exact (ex_elim (@lem6160827 A x z h1) (fun y : A => fun h0 : term34 A x z y => @lem6160826 A x y z h0)). Qed.
Lemma lem6160829 {A : Type'} (h1 : term24 A) : term24 A.
Proof. exact (h1). Qed.
Lemma lem6160830 {A : Type'} (x : A) (z : A) (h1 : term24 A) (h2 : term33 A x z) : x = z.
Proof. exact (@lem6160828 A x z h2 (@lem6160829 A h1)). Qed.
Lemma lem6160831 {A : Type'} (x : A) (z : A) (h1 : term24 A) : term35 A x z.
Proof. exact (fun h0 : term33 A x z => @lem6160830 A x z h1 h0). Qed.
Lemma lem6160832 {A : Type'} (x : A) (h1 : term24 A) : term36 A x.
Proof. exact (fun z : A => @lem6160831 A x z h1). Qed.
Lemma lem6160833 {A : Type'} (h1 : term24 A) : term37 A.
Proof. exact (fun x : A => @lem6160832 A x h1). Qed.
Lemma lem6160834 {A : Type'} : term38 A.
Proof. exact (fun h0 : term24 A => @lem6160833 A h0). Qed.
Lemma lem6160835 {A : Type'} : term37 A.
Proof. exact (@lem6160834 A (@lem403 A)). Qed.
Lemma lem6160836 {A : Type'} (x : A) : term39 A x.
Proof. exact (@lem6160835 A x). Qed.
Lemma lem6160837 {A : Type'} (x : A) : (term39 A x) = (term36 A x).
Proof. exact (eq_refl (term39 A x)). Qed.
Lemma lem6160838 {A : Type'} (x : A) : term36 A x.
Proof. exact (EQ_MP (@lem6160837 A x) (@lem6160836 A x)). Qed.
Lemma lem6160839 {A : Type'} (x : A) (z : A) : term40 A x z.
Proof. exact (@lem6160838 A x z). Qed.
Lemma lem6160840 {A : Type'} (x : A) (z : A) : (term40 A x z) = (term35 A x z).
Proof. exact (eq_refl (term40 A x z)). Qed.
Lemma lem6160845 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) (h1 : (term41 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f)) : (term41 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f).
Proof. exact (h1). Qed.
Lemma lem6160846 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) (h1 : (term41 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f)) : (@iterate _120296 _120308 op s f) = (term41 _120296 _120308 op s f).
Proof. exact (SYM (@lem6160845 _120296 _120308 op s f h1)). Qed.
Lemma lem6160847 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) (h1 : (@iterate _120296 _120308 op s f) = (term41 _120296 _120308 op s f)) : (@iterate _120296 _120308 op s f) = (term41 _120296 _120308 op s f).
Proof. exact (h1). Qed.
Lemma lem6160848 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) (h1 : (@iterate _120296 _120308 op s f) = (term41 _120296 _120308 op s f)) : (term41 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f).
Proof. exact (SYM (@lem6160847 _120296 _120308 op s f h1)). Qed.
Lemma lem6160849 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : ((term41 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f)) = ((@iterate _120296 _120308 op s f) = (term41 _120296 _120308 op s f)).
Proof. exact (prop_ext (fun h1 : (term41 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f) => @lem6160846 _120296 _120308 op s f h1) (fun h1 : (@iterate _120296 _120308 op s f) = (term41 _120296 _120308 op s f) => @lem6160848 _120296 _120308 op s f h1)). Qed.
Lemma lem6160850 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : (term42 _120296 _120308 op f) = (term43 _120296 _120308 op f).
Proof. exact (fun_ext (fun s : _120308 -> Prop => @lem6160849 _120296 _120308 op s f)). Qed.
Lemma lem6160851 {_120308 : Type'} : (@all (_120308 -> Prop)) = (@all (_120308 -> Prop)).
Proof. exact (eq_refl (@all (_120308 -> Prop))). Qed.
Lemma lem6160852 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : (term44 _120296 _120308 op f) = (term45 _120296 _120308 op f).
Proof. exact (MK_COMB (@lem6160851 _120308) (@lem6160850 _120296 _120308 op f)). Qed.
Lemma lem6160853 {_120296 _120308 : Type'} (op : type1400 _120296) : (term46 _120296 _120308 op) = (term47 _120296 _120308 op).
Proof. exact (fun_ext (fun f : _120308 -> _120296 => @lem6160852 _120296 _120308 op f)). Qed.
Lemma lem6160854 {_120296 _120308 : Type'} : (@all (_120308 -> _120296)) = (@all (_120308 -> _120296)).
Proof. exact (eq_refl (@all (_120308 -> _120296))). Qed.
Lemma lem6160855 {_120296 _120308 : Type'} (op : type1400 _120296) : (term48 _120296 _120308 op) = (term49 _120296 _120308 op).
Proof. exact (MK_COMB (@lem6160854 _120296 _120308) (@lem6160853 _120296 _120308 op)). Qed.
Lemma lem6160856 {_120296 _120308 : Type'} : (term50 _120296 _120308) = (term51 _120296 _120308).
Proof. exact (fun_ext (fun op : type1400 _120296 => @lem6160855 _120296 _120308 op)). Qed.
Lemma lem6160857 {_120296 : Type'} : (@all (_120296 -> _120296 -> _120296)) = (@all (_120296 -> _120296 -> _120296)).
Proof. exact (eq_refl (@all (_120296 -> _120296 -> _120296))). Qed.
Lemma lem6160858 {_120296 _120308 : Type'} : (term52 _120296 _120308) = (term53 _120296 _120308).
Proof. exact (MK_COMB (@lem6160857 _120296) (@lem6160856 _120296 _120308)). Qed.
Lemma lem6160859 {_120296 _120308 : Type'} : term53 _120296 _120308.
Proof. exact (EQ_MP (@lem6160858 _120296 _120308) (@lem5737860 _120296 _120308)). Qed.
Lemma lem6160860 {_120296 _120308 : Type'} (op : type1400 _120296) : term54 _120296 _120308 op.
Proof. exact (@lem6160859 _120296 _120308 op). Qed.
Lemma lem6160861 {_120296 _120308 : Type'} (op : type1400 _120296) : (term54 _120296 _120308 op) = (term49 _120296 _120308 op).
Proof. exact (eq_refl (term54 _120296 _120308 op)). Qed.
Lemma lem6160862 {_120296 _120308 : Type'} (op : type1400 _120296) : term49 _120296 _120308 op.
Proof. exact (EQ_MP (@lem6160861 _120296 _120308 op) (@lem6160860 _120296 _120308 op)). Qed.
Lemma lem6160863 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : term55 _120296 _120308 op f.
Proof. exact (@lem6160862 _120296 _120308 op f). Qed.
Lemma lem6160864 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : (term55 _120296 _120308 op f) = (term45 _120296 _120308 op f).
Proof. exact (eq_refl (term55 _120296 _120308 op f)). Qed.
Lemma lem6160865 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : term45 _120296 _120308 op f.
Proof. exact (EQ_MP (@lem6160864 _120296 _120308 op f) (@lem6160863 _120296 _120308 op f)). Qed.
Lemma lem6160866 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) (s : _120308 -> Prop) : term56 _120296 _120308 op f s.
Proof. exact (@lem6160865 _120296 _120308 op f s). Qed.
Lemma lem6160867 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : (term56 _120296 _120308 op f s) = ((@iterate _120296 _120308 op s f) = (term41 _120296 _120308 op s f)).
Proof. exact (eq_refl (term56 _120296 _120308 op f s)). Qed.
Lemma lem6160869 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem6160870 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (s : A -> Prop) (h1 : term57 A B f op g s) : term57 A B f op g s.
Proof. exact (h1). Qed.
Lemma lem6160871 {A B : Type'} (op : type1400 B) (g : A -> B) (s : A -> Prop) (h1 : term58 A B op g s) : term58 A B op g s.
Proof. exact (h1). Qed.
Lemma lem6160872 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term58 A B op f s) : term58 A B op f s.
Proof. exact (h1). Qed.
Lemma lem6160876 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : (@iterate _120296 _120308 op s f) = (term41 _120296 _120308 op s f).
Proof. exact (EQ_MP (@lem6160867 _120296 _120308 op s f) (@lem6160866 _120296 _120308 op f s)). Qed.
Lemma lem6160877 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (@iterate B A op s f) = (term59 A B op s f).
Proof. exact (@lem6160876 B A op s f). Qed.
Lemma lem6160878 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (g : A -> B) : (term60 A B s op f g) = (term61 A B s op f g).
Proof. exact (@lem6160877 A B op s (term62 A B op f g)). Qed.
Lemma lem6160879 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6160880 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (g : A -> B) : (term63 A B s op f g) = (term64 A B s op f g).
Proof. exact (MK_COMB (@lem6160879 B) (@lem6160878 A B s op f g)). Qed.
Lemma lem6160882 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : (@iterate _120296 _120308 op s f) = (term41 _120296 _120308 op s f).
Proof. exact (EQ_MP (@lem6160867 _120296 _120308 op s f) (@lem6160866 _120296 _120308 op f s)). Qed.
Lemma lem6160883 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (@iterate B A op s f) = (term59 A B op s f).
Proof. exact (@lem6160882 B A op s f). Qed.
Lemma lem6160884 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6160885 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term65 A B op s f) = (term66 A B op s f).
Proof. exact (MK_COMB (@lem6160884 B op) (@lem6160883 A B op s f)). Qed.
Lemma lem6160887 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : (@iterate _120296 _120308 op s f) = (term41 _120296 _120308 op s f).
Proof. exact (EQ_MP (@lem6160867 _120296 _120308 op s f) (@lem6160866 _120296 _120308 op f s)). Qed.
Lemma lem6160888 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (@iterate B A op s f) = (term59 A B op s f).
Proof. exact (@lem6160887 B A op s f). Qed.
Lemma lem6160889 {A B : Type'} (op : type1400 B) (s : A -> Prop) (g : A -> B) : (@iterate B A op s g) = (term59 A B op s g).
Proof. exact (@lem6160888 A B op s g). Qed.
Lemma lem6160890 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term67 A B f op s g) = (term68 A B f op s g).
Proof. exact (MK_COMB (@lem6160885 A B op s f) (@lem6160889 A B op s g)). Qed.
Lemma lem6160891 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : ((term60 A B s op f g) = (term67 A B f op s g)) = ((term61 A B s op f g) = (term68 A B f op s g)).
Proof. exact (MK_COMB (@lem6160880 A B s op f g) (@lem6160890 A B f op s g)). Qed.
Lemma lem6160892 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : ((term61 A B s op f g) = (term68 A B f op s g)) = ((term60 A B s op f g) = (term67 A B f op s g)).
Proof. exact (SYM (@lem6160891 A B f op s g)). Qed.
Lemma lem6160894 {A : Type'} (x : A) (z : A) : term35 A x z.
Proof. exact (EQ_MP (@lem6160840 A x z) (@lem6160839 A x z)). Qed.
Lemma lem6160895 {B : Type'} (x : B) (z : B) : term35 B x z.
Proof. exact (@lem6160894 B x z). Qed.
Lemma lem6160896 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : term69 A B f op s g.
Proof. exact (@lem6160895 B (term61 A B s op f g) (term68 A B f op s g)). Qed.
Lemma lem6160897 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (g : A -> B) (h1 : (term61 A B s op f g) = (term70 A B s op f g)) : (term61 A B s op f g) = (term70 A B s op f g).
Proof. exact (h1). Qed.
Lemma lem6160898 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (g : A -> B) (h1 : (term61 A B s op f g) = (term70 A B s op f g)) : (term70 A B s op f g) = (term61 A B s op f g).
Proof. exact (SYM (@lem6160897 A B s op f g h1)). Qed.
Lemma lem6160899 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (g : A -> B) (h1 : (term70 A B s op f g) = (term61 A B s op f g)) : (term70 A B s op f g) = (term61 A B s op f g).
Proof. exact (h1). Qed.
Lemma lem6160900 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (g : A -> B) (h1 : (term70 A B s op f g) = (term61 A B s op f g)) : (term61 A B s op f g) = (term70 A B s op f g).
Proof. exact (SYM (@lem6160899 A B s op f g h1)). Qed.
Lemma lem6160901 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (g : A -> B) : ((term61 A B s op f g) = (term70 A B s op f g)) = ((term70 A B s op f g) = (term61 A B s op f g)).
Proof. exact (prop_ext (fun h1 : (term61 A B s op f g) = (term70 A B s op f g) => @lem6160898 A B s op f g h1) (fun h1 : (term70 A B s op f g) = (term61 A B s op f g) => @lem6160900 A B s op f g h1)). Qed.
Lemma lem6160902 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (g : A -> B) : ((term70 A B s op f g) = (term61 A B s op f g)) = ((term61 A B s op f g) = (term70 A B s op f g)).
Proof. exact (SYM (@lem6160901 A B s op f g)). Qed.
Lemma lem6160903 {A : Type'} (s : A -> Prop) : term71 A s.
Proof. exact (@lem3606772 A s). Qed.
Lemma lem6160904 {A : Type'} (s : A -> Prop) : (term71 A s) = (term72 A s).
Proof. exact (eq_refl (term71 A s)). Qed.
Lemma lem6160905 {A : Type'} (s : A -> Prop) : term72 A s.
Proof. exact (EQ_MP (@lem6160904 A s) (@lem6160903 A s)). Qed.
Lemma lem6160906 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term73 A s t.
Proof. exact (@lem6160905 A s t). Qed.
Lemma lem6160907 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term73 A s t) = ((term74 A s t) = (term75 A s t)).
Proof. exact (eq_refl (term73 A s t)). Qed.
Lemma lem6160909 {_122572 _122573 : Type'} (op : type1400 _122573) : term76 _122572 _122573 op.
Proof. exact (@lem6013661 _122572 _122573 op). Qed.
Lemma lem6160910 {_122572 _122573 : Type'} (op : type1400 _122573) : (term76 _122572 _122573 op) = (term77 _122572 _122573 op).
Proof. exact (eq_refl (term76 _122572 _122573 op)). Qed.
Lemma lem6160911 {_122572 _122573 : Type'} (op : type1400 _122573) : term77 _122572 _122573 op.
Proof. exact (EQ_MP (@lem6160910 _122572 _122573 op) (@lem6160909 _122572 _122573 op)). Qed.
Lemma lem6160912 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : @monoidal _122573 op.
Proof. exact (h1). Qed.
Lemma lem6160913 {_122572 _122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : term78 _122572 _122573 op.
Proof. exact (@lem6160911 _122572 _122573 op (@lem6160912 _122573 op h1)). Qed.
Lemma lem6160914 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : term79 _122572 _122573 op f.
Proof. exact (@lem6160913 _122572 _122573 op h1 f). Qed.
Lemma lem6160915 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) : (term79 _122572 _122573 op f) = (term80 _122572 _122573 f op).
Proof. exact (eq_refl (term79 _122572 _122573 op f)). Qed.
Lemma lem6160916 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : term80 _122572 _122573 f op.
Proof. exact (EQ_MP (@lem6160915 _122572 _122573 f op) (@lem6160914 _122572 _122573 f op h1)). Qed.
Lemma lem6160917 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : term81 _122572 _122573 f op g.
Proof. exact (@lem6160916 _122572 _122573 f op h1 g). Qed.
Lemma lem6160918 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) : (term81 _122572 _122573 f op g) = (term82 _122572 _122573 f op g).
Proof. exact (eq_refl (term81 _122572 _122573 f op g)). Qed.
Lemma lem6160919 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : term82 _122572 _122573 f op g.
Proof. exact (EQ_MP (@lem6160918 _122572 _122573 f op g) (@lem6160917 _122572 _122573 f g op h1)). Qed.
Lemma lem6160920 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (s : _122572 -> Prop) (op : type1400 _122573) (h1 : @monoidal _122573 op) : term83 _122572 _122573 f op g s.
Proof. exact (@lem6160919 _122572 _122573 f g op h1 s). Qed.
Lemma lem6160921 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) : (term83 _122572 _122573 f op g s) = (term84 _122572 _122573 f op s g).
Proof. exact (eq_refl (term83 _122572 _122573 f op g s)). Qed.
Lemma lem6160922 {_122572 _122573 : Type'} (f : _122572 -> _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : term84 _122572 _122573 f op s g.
Proof. exact (EQ_MP (@lem6160921 _122572 _122573 f op s g) (@lem6160920 _122572 _122573 f g s op h1)). Qed.
Lemma lem6160923 {_122572 : Type'} (s : _122572 -> Prop) (h1 : @FINITE _122572 s) : @FINITE _122572 s.
Proof. exact (h1). Qed.
Lemma lem6160924 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (s : _122572 -> Prop) (op : type1400 _122573) (h1 : @FINITE _122572 s) (h2 : @monoidal _122573 op) : (term60 _122572 _122573 s op f g) = (term67 _122572 _122573 f op s g).
Proof. exact (@lem6160922 _122572 _122573 f s g op h2 (@lem6160923 _122572 s h1)). Qed.
Lemma lem6160925 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (s : _122572 -> Prop) (h1 : @FINITE _122572 s) : term85 _122572 _122573 f op s g.
Proof. exact (fun h0 : @monoidal _122573 op => @lem6160924 _122572 _122573 f g s op h1 h0). Qed.
Lemma lem6160926 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) : term86 _122572 _122573 f op s g.
Proof. exact (fun h0 : @FINITE _122572 s => @lem6160925 _122572 _122573 f op g s h0). Qed.
Lemma lem6160928 (p : Prop) (q : Prop) (r : Prop) : (term87 p q r) = (term88 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem6160933 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) : (term86 _122572 _122573 f op s g) = (term89 _122572 _122573 f op s g).
Proof. exact (@lem6160928 (@FINITE _122572 s) (@monoidal _122573 op) ((term60 _122572 _122573 s op f g) = (term67 _122572 _122573 f op s g))). Qed.
Lemma lem6160935 {B : Type'} (op : type1400 B) : (@monoidal B op) = ((@monoidal B op) = True).
Proof. exact (@lem7 (@monoidal B op)). Qed.
Lemma lem6160937 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term58 A B op f s) = ((term58 A B op f s) = True).
Proof. exact (@lem7 (term58 A B op f s)). Qed.
Lemma lem6160939 {A B : Type'} (op : type1400 B) (g : A -> B) (s : A -> Prop) : (term58 A B op g s) = ((term58 A B op g s) = True).
Proof. exact (@lem7 (term58 A B op g s)). Qed.
Lemma lem6160944 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) : term89 _122572 _122573 f op s g.
Proof. exact (EQ_MP (@lem6160933 _122572 _122573 f op s g) (@lem6160926 _122572 _122573 f op s g)). Qed.
Lemma lem6160945 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : term89 A B f op s g.
Proof. exact (@lem6160944 A B f op s g). Qed.
Lemma lem6160946 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : term90 A B f op s g.
Proof. exact (@lem6160945 A B f op (term91 A B f op g s) g). Qed.
Lemma lem6160950 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term74 A s t) = (term75 A s t).
Proof. exact (EQ_MP (@lem6160907 A s t) (@lem6160906 A s t)). Qed.
Lemma lem6160951 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term74 A s t) = (term75 A s t).
Proof. exact (@lem6160950 A s t). Qed.
Lemma lem6160952 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (s : A -> Prop) : (term92 A B f op g s) = (term57 A B f op g s).
Proof. exact (@lem6160951 A (@support A B op f s) (@support A B op g s)). Qed.
Lemma lem6160956 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term58 A B op f s) : (term58 A B op f s) = True.
Proof. exact (EQ_MP (@lem6160937 A B op f s) (@lem6160872 A B op f s h1)). Qed.
Lemma lem6160957 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6160958 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term58 A B op f s) : (term93 A B op f s) = (and True).
Proof. exact (MK_COMB (@lem6160957) (@lem6160956 A B op f s h1)). Qed.
Lemma lem6160960 {A B : Type'} (op : type1400 B) (g : A -> B) (s : A -> Prop) (h1 : term58 A B op g s) : (term58 A B op g s) = True.
Proof. exact (EQ_MP (@lem6160939 A B op g s) (@lem6160871 A B op g s h1)). Qed.
Lemma lem6160961 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (s : A -> Prop) (h1 : term58 A B op f s) (h2 : term58 A B op g s) : (term57 A B f op g s) = (True /\ True).
Proof. exact (MK_COMB (@lem6160958 A B op f s h1) (@lem6160960 A B op g s h2)). Qed.
Lemma lem6160963 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6160964 : (True /\ True) = True.
Proof. exact (@lem6160963 True). Qed.
Lemma lem6160965 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (s : A -> Prop) (h1 : term58 A B op f s) (h2 : term58 A B op g s) : (term57 A B f op g s) = True.
Proof. exact (TRANS (@lem6160961 A B f op g s h1 h2) (@lem6160964)). Qed.
Lemma lem6160966 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (s : A -> Prop) (h1 : term58 A B op f s) (h2 : term58 A B op g s) : (term92 A B f op g s) = True.
Proof. exact (TRANS (@lem6160952 A B f op g s) (@lem6160965 A B f op g s h1 h2)). Qed.
Lemma lem6160967 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6160968 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (s : A -> Prop) (h1 : term58 A B op f s) (h2 : term58 A B op g s) : (term94 A B f op g s) = (and True).
Proof. exact (MK_COMB (@lem6160967) (@lem6160966 A B f op g s h1 h2)). Qed.
Lemma lem6160970 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = True.
Proof. exact (EQ_MP (@lem6160935 B op) (@lem6160869 B op h1)). Qed.
Lemma lem6160971 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : (term95 A B f g s op) = (True /\ True).
Proof. exact (MK_COMB (@lem6160968 A B f op g s h1 h2) (@lem6160970 B op h3)). Qed.
Lemma lem6160973 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6160974 : (True /\ True) = True.
Proof. exact (@lem6160973 True). Qed.
Lemma lem6160975 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : (term95 A B f g s op) = True.
Proof. exact (TRANS (@lem6160971 A B f g s op h1 h2 h3) (@lem6160974)). Qed.
Lemma lem6160976 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : True = (term95 A B f g s op).
Proof. exact (SYM (@lem6160975 A B f g s op h1 h2 h3)). Qed.
Lemma lem6160977 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : term95 A B f g s op.
Proof. exact (EQ_MP (@lem6160976 A B f g s op h1 h2 h3) (@lem0)). Qed.
Lemma lem6160978 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : (term70 A B s op f g) = (term96 A B f op s g).
Proof. exact (@lem6160946 A B f op s g (@lem6160977 A B f g s op h1 h2 h3)). Qed.
Lemma lem6160979 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6160980 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : (term97 A B s op f g) = (term98 A B f op s g).
Proof. exact (MK_COMB (@lem6160979 B) (@lem6160978 A B f g s op h1 h2 h3)). Qed.
Lemma lem6160981 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term68 A B f op s g) = (term68 A B f op s g).
Proof. exact (eq_refl (term68 A B f op s g)). Qed.
Lemma lem6160982 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : ((term70 A B s op f g) = (term68 A B f op s g)) = ((term96 A B f op s g) = (term68 A B f op s g)).
Proof. exact (MK_COMB (@lem6160980 A B f g s op h1 h2 h3) (@lem6160981 A B f op s g)). Qed.
Lemma lem6160985 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : ((term96 A B f op s g) = (term68 A B f op s g)) = ((term70 A B s op f g) = (term68 A B f op s g)).
Proof. exact (SYM (@lem6160982 A B f g s op h1 h2 h3)). Qed.
Lemma lem6160986 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6160992 {A B : Type'} (op : type1400 B) : term23 A B op.
Proof. exact (EQ_MP (@lem6160812 A B op) (@lem6160811 A B op)). Qed.
Lemma lem6160993 {A B : Type'} (op : type1400 B) : term23 A B op.
Proof. exact (@lem6160992 A B op). Qed.
Lemma lem6160994 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term99 A B op.
Proof. exact (@lem6160993 A B op (@lem6160869 B op h1)). Qed.
Lemma lem6160995 {A B : Type'} (op : type1400 B) (h1 : term99 A B op) : term99 A B op.
Proof. exact (h1). Qed.
Lemma lem6160996 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : term99 A B op) : term100 A B op f.
Proof. exact (@lem6160995 A B op h1 f). Qed.
Lemma lem6160997 {A B : Type'} (op : type1400 B) (f : A -> B) : (term100 A B op f) = (term101 A B op f).
Proof. exact (eq_refl (term100 A B op f)). Qed.
Lemma lem6160998 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : term99 A B op) : term101 A B op f.
Proof. exact (EQ_MP (@lem6160997 A B op f) (@lem6160996 A B f op h1)). Qed.
Lemma lem6160999 {A B : Type'} (f : A -> B) (u : A -> Prop) (op : type1400 B) (h1 : term99 A B op) : term102 A B op f u.
Proof. exact (@lem6160998 A B f op h1 u). Qed.
Lemma lem6161000 {A B : Type'} (op : type1400 B) (u : A -> Prop) (f : A -> B) : (term102 A B op f u) = (term103 A B op u f).
Proof. exact (eq_refl (term102 A B op f u)). Qed.
Lemma lem6161001 {A B : Type'} (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term99 A B op) : term103 A B op u f.
Proof. exact (EQ_MP (@lem6161000 A B op u f) (@lem6160999 A B f u op h1)). Qed.
Lemma lem6161002 {A B : Type'} (u : A -> Prop) (f : A -> B) (v : A -> Prop) (op : type1400 B) (h1 : term99 A B op) : term104 A B op u f v.
Proof. exact (@lem6161001 A B u f op h1 v). Qed.
Lemma lem6161003 {A B : Type'} (v : A -> Prop) (op : type1400 B) (u : A -> Prop) (f : A -> B) : (term104 A B op u f v) = (term105 A B v op u f).
Proof. exact (eq_refl (term104 A B op u f v)). Qed.
Lemma lem6161004 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term99 A B op) : term105 A B v op u f.
Proof. exact (EQ_MP (@lem6161003 A B v op u f) (@lem6161002 A B u f v op h1)). Qed.
Lemma lem6161005 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term106 A B v u f op) : term106 A B v u f op.
Proof. exact (h1). Qed.
Lemma lem6161006 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term99 A B op) (h2 : term106 A B v u f op) : (@iterate B A op v f) = (@iterate B A op u f).
Proof. exact (@lem6161004 A B v u f op h1 (@lem6161005 A B v u f op h2)). Qed.
Lemma lem6161007 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term106 A B v u f op) : term107 A B v op u f.
Proof. exact (fun h0 : term99 A B op => @lem6161006 A B v u f op h0 h1). Qed.
Lemma lem6161008 {A B : Type'} (op : type1400 B) (h1 : term99 A B op) : term99 A B op.
Proof. exact (h1). Qed.
Lemma lem6161009 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term99 A B op) (h2 : term106 A B v u f op) : (@iterate B A op v f) = (@iterate B A op u f).
Proof. exact (@lem6161007 A B v u f op h2 (@lem6161008 A B op h1)). Qed.
Lemma lem6161010 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term99 A B op) : term105 A B v op u f.
Proof. exact (fun h0 : term106 A B v u f op => @lem6161009 A B v u f op h1 h0). Qed.
Lemma lem6161011 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (op : type1400 B) (h1 : term99 A B op) : term108 A B v op u.
Proof. exact (fun f : A -> B => @lem6161010 A B v u f op h1). Qed.
Lemma lem6161012 {A B : Type'} (v : A -> Prop) (op : type1400 B) (h1 : term99 A B op) : term109 A B v op.
Proof. exact (fun u : A -> Prop => @lem6161011 A B v u op h1). Qed.
Lemma lem6161013 {A B : Type'} (op : type1400 B) (h1 : term99 A B op) : term110 A B op.
Proof. exact (fun v : A -> Prop => @lem6161012 A B v op h1). Qed.
Lemma lem6161014 {A B : Type'} (op : type1400 B) : term111 A B op.
Proof. exact (fun h0 : term99 A B op => @lem6161013 A B op h0). Qed.
Lemma lem6161015 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term110 A B op.
Proof. exact (@lem6161014 A B op (@lem6160994 A B op h1)). Qed.
Lemma lem6161016 {A B : Type'} (v : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term112 A B op v.
Proof. exact (@lem6161015 A B op h1 v). Qed.
Lemma lem6161017 {A B : Type'} (v : A -> Prop) (op : type1400 B) : (term112 A B op v) = (term109 A B v op).
Proof. exact (eq_refl (term112 A B op v)). Qed.
Lemma lem6161018 {A B : Type'} (v : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term109 A B v op.
Proof. exact (EQ_MP (@lem6161017 A B v op) (@lem6161016 A B v op h1)). Qed.
Lemma lem6161019 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term113 A B v op u.
Proof. exact (@lem6161018 A B v op h1 u). Qed.
Lemma lem6161020 {A B : Type'} (v : A -> Prop) (op : type1400 B) (u : A -> Prop) : (term113 A B v op u) = (term108 A B v op u).
Proof. exact (eq_refl (term113 A B v op u)). Qed.
Lemma lem6161021 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term108 A B v op u.
Proof. exact (EQ_MP (@lem6161020 A B v op u) (@lem6161019 A B v u op h1)). Qed.
Lemma lem6161022 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term114 A B v op u f.
Proof. exact (@lem6161021 A B v u op h1 f). Qed.
Lemma lem6161023 {A B : Type'} (v : A -> Prop) (op : type1400 B) (u : A -> Prop) (f : A -> B) : (term114 A B v op u f) = (term105 A B v op u f).
Proof. exact (eq_refl (term114 A B v op u f)). Qed.
Lemma lem6161026 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term105 A B v op u f.
Proof. exact (EQ_MP (@lem6161023 A B v op u f) (@lem6161022 A B v u f op h1)). Qed.
Lemma lem6161027 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term105 A B v op u f.
Proof. exact (@lem6161026 A B v u f op h1). Qed.
Lemma lem6161028 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term115 A B s op f g.
Proof. exact (@lem6161027 A B (term91 A B f op g s) (term116 A B op f g s) (term62 A B op f g) op h1). Qed.
Lemma lem6161034 {A B : Type'} (op : type1400 B) : term23 A B op.
Proof. exact (EQ_MP (@lem6160812 A B op) (@lem6160811 A B op)). Qed.
Lemma lem6161035 {A B : Type'} (op : type1400 B) : term23 A B op.
Proof. exact (@lem6161034 A B op). Qed.
Lemma lem6161036 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term99 A B op.
Proof. exact (@lem6161035 A B op (@lem6160869 B op h1)). Qed.
Lemma lem6161037 {A B : Type'} (op : type1400 B) (h1 : term99 A B op) : term99 A B op.
Proof. exact (h1). Qed.
Lemma lem6161038 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : term99 A B op) : term100 A B op f.
Proof. exact (@lem6161037 A B op h1 f). Qed.
Lemma lem6161039 {A B : Type'} (op : type1400 B) (f : A -> B) : (term100 A B op f) = (term101 A B op f).
Proof. exact (eq_refl (term100 A B op f)). Qed.
Lemma lem6161040 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : term99 A B op) : term101 A B op f.
Proof. exact (EQ_MP (@lem6161039 A B op f) (@lem6161038 A B f op h1)). Qed.
Lemma lem6161041 {A B : Type'} (f : A -> B) (u : A -> Prop) (op : type1400 B) (h1 : term99 A B op) : term102 A B op f u.
Proof. exact (@lem6161040 A B f op h1 u). Qed.
Lemma lem6161042 {A B : Type'} (op : type1400 B) (u : A -> Prop) (f : A -> B) : (term102 A B op f u) = (term103 A B op u f).
Proof. exact (eq_refl (term102 A B op f u)). Qed.
Lemma lem6161043 {A B : Type'} (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term99 A B op) : term103 A B op u f.
Proof. exact (EQ_MP (@lem6161042 A B op u f) (@lem6161041 A B f u op h1)). Qed.
Lemma lem6161044 {A B : Type'} (u : A -> Prop) (f : A -> B) (v : A -> Prop) (op : type1400 B) (h1 : term99 A B op) : term104 A B op u f v.
Proof. exact (@lem6161043 A B u f op h1 v). Qed.
Lemma lem6161045 {A B : Type'} (v : A -> Prop) (op : type1400 B) (u : A -> Prop) (f : A -> B) : (term104 A B op u f v) = (term105 A B v op u f).
Proof. exact (eq_refl (term104 A B op u f v)). Qed.
Lemma lem6161046 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term99 A B op) : term105 A B v op u f.
Proof. exact (EQ_MP (@lem6161045 A B v op u f) (@lem6161044 A B u f v op h1)). Qed.
Lemma lem6161047 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term106 A B v u f op) : term106 A B v u f op.
Proof. exact (h1). Qed.
Lemma lem6161048 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term99 A B op) (h2 : term106 A B v u f op) : (@iterate B A op v f) = (@iterate B A op u f).
Proof. exact (@lem6161046 A B v u f op h1 (@lem6161047 A B v u f op h2)). Qed.
Lemma lem6161049 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term106 A B v u f op) : term107 A B v op u f.
Proof. exact (fun h0 : term99 A B op => @lem6161048 A B v u f op h0 h1). Qed.
Lemma lem6161050 {A B : Type'} (op : type1400 B) (h1 : term99 A B op) : term99 A B op.
Proof. exact (h1). Qed.
Lemma lem6161051 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term99 A B op) (h2 : term106 A B v u f op) : (@iterate B A op v f) = (@iterate B A op u f).
Proof. exact (@lem6161049 A B v u f op h2 (@lem6161050 A B op h1)). Qed.
Lemma lem6161052 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term99 A B op) : term105 A B v op u f.
Proof. exact (fun h0 : term106 A B v u f op => @lem6161051 A B v u f op h1 h0). Qed.
Lemma lem6161053 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (op : type1400 B) (h1 : term99 A B op) : term108 A B v op u.
Proof. exact (fun f : A -> B => @lem6161052 A B v u f op h1). Qed.
Lemma lem6161054 {A B : Type'} (v : A -> Prop) (op : type1400 B) (h1 : term99 A B op) : term109 A B v op.
Proof. exact (fun u : A -> Prop => @lem6161053 A B v u op h1). Qed.
Lemma lem6161055 {A B : Type'} (op : type1400 B) (h1 : term99 A B op) : term110 A B op.
Proof. exact (fun v : A -> Prop => @lem6161054 A B v op h1). Qed.
Lemma lem6161056 {A B : Type'} (op : type1400 B) : term111 A B op.
Proof. exact (fun h0 : term99 A B op => @lem6161055 A B op h0). Qed.
Lemma lem6161057 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term110 A B op.
Proof. exact (@lem6161056 A B op (@lem6161036 A B op h1)). Qed.
Lemma lem6161058 {A B : Type'} (v : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term112 A B op v.
Proof. exact (@lem6161057 A B op h1 v). Qed.
Lemma lem6161059 {A B : Type'} (v : A -> Prop) (op : type1400 B) : (term112 A B op v) = (term109 A B v op).
Proof. exact (eq_refl (term112 A B op v)). Qed.
Lemma lem6161060 {A B : Type'} (v : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term109 A B v op.
Proof. exact (EQ_MP (@lem6161059 A B v op) (@lem6161058 A B v op h1)). Qed.
Lemma lem6161061 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term113 A B v op u.
Proof. exact (@lem6161060 A B v op h1 u). Qed.
Lemma lem6161062 {A B : Type'} (v : A -> Prop) (op : type1400 B) (u : A -> Prop) : (term113 A B v op u) = (term108 A B v op u).
Proof. exact (eq_refl (term113 A B v op u)). Qed.
Lemma lem6161063 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term108 A B v op u.
Proof. exact (EQ_MP (@lem6161062 A B v op u) (@lem6161061 A B v u op h1)). Qed.
Lemma lem6161064 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term114 A B v op u f.
Proof. exact (@lem6161063 A B v u op h1 f). Qed.
Lemma lem6161065 {A B : Type'} (v : A -> Prop) (op : type1400 B) (u : A -> Prop) (f : A -> B) : (term114 A B v op u f) = (term105 A B v op u f).
Proof. exact (eq_refl (term114 A B v op u f)). Qed.
Lemma lem6161068 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term105 A B v op u f.
Proof. exact (EQ_MP (@lem6161065 A B v op u f) (@lem6161064 A B v u f op h1)). Qed.
Lemma lem6161069 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term105 A B v op u f.
Proof. exact (@lem6161068 A B v u f op h1). Qed.
Lemma lem6161070 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term117 A B g op s f.
Proof. exact (@lem6161069 A B (term91 A B f op g s) (@support A B op f s) f op h1). Qed.
Lemma lem6161076 {A B : Type'} (op : type1400 B) : term23 A B op.
Proof. exact (EQ_MP (@lem6160812 A B op) (@lem6160811 A B op)). Qed.
Lemma lem6161077 {A B : Type'} (op : type1400 B) : term23 A B op.
Proof. exact (@lem6161076 A B op). Qed.
Lemma lem6161078 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term99 A B op.
Proof. exact (@lem6161077 A B op (@lem6160869 B op h1)). Qed.
Lemma lem6161079 {A B : Type'} (op : type1400 B) (h1 : term99 A B op) : term99 A B op.
Proof. exact (h1). Qed.
Lemma lem6161080 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : term99 A B op) : term100 A B op f.
Proof. exact (@lem6161079 A B op h1 f). Qed.
Lemma lem6161081 {A B : Type'} (op : type1400 B) (f : A -> B) : (term100 A B op f) = (term101 A B op f).
Proof. exact (eq_refl (term100 A B op f)). Qed.
Lemma lem6161082 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : term99 A B op) : term101 A B op f.
Proof. exact (EQ_MP (@lem6161081 A B op f) (@lem6161080 A B f op h1)). Qed.
Lemma lem6161083 {A B : Type'} (f : A -> B) (u : A -> Prop) (op : type1400 B) (h1 : term99 A B op) : term102 A B op f u.
Proof. exact (@lem6161082 A B f op h1 u). Qed.
Lemma lem6161084 {A B : Type'} (op : type1400 B) (u : A -> Prop) (f : A -> B) : (term102 A B op f u) = (term103 A B op u f).
Proof. exact (eq_refl (term102 A B op f u)). Qed.
Lemma lem6161085 {A B : Type'} (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term99 A B op) : term103 A B op u f.
Proof. exact (EQ_MP (@lem6161084 A B op u f) (@lem6161083 A B f u op h1)). Qed.
Lemma lem6161086 {A B : Type'} (u : A -> Prop) (f : A -> B) (v : A -> Prop) (op : type1400 B) (h1 : term99 A B op) : term104 A B op u f v.
Proof. exact (@lem6161085 A B u f op h1 v). Qed.
Lemma lem6161087 {A B : Type'} (v : A -> Prop) (op : type1400 B) (u : A -> Prop) (f : A -> B) : (term104 A B op u f v) = (term105 A B v op u f).
Proof. exact (eq_refl (term104 A B op u f v)). Qed.
Lemma lem6161088 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term99 A B op) : term105 A B v op u f.
Proof. exact (EQ_MP (@lem6161087 A B v op u f) (@lem6161086 A B u f v op h1)). Qed.
Lemma lem6161089 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term106 A B v u f op) : term106 A B v u f op.
Proof. exact (h1). Qed.
Lemma lem6161090 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term99 A B op) (h2 : term106 A B v u f op) : (@iterate B A op v f) = (@iterate B A op u f).
Proof. exact (@lem6161088 A B v u f op h1 (@lem6161089 A B v u f op h2)). Qed.
Lemma lem6161091 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term106 A B v u f op) : term107 A B v op u f.
Proof. exact (fun h0 : term99 A B op => @lem6161090 A B v u f op h0 h1). Qed.
Lemma lem6161092 {A B : Type'} (op : type1400 B) (h1 : term99 A B op) : term99 A B op.
Proof. exact (h1). Qed.
Lemma lem6161093 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term99 A B op) (h2 : term106 A B v u f op) : (@iterate B A op v f) = (@iterate B A op u f).
Proof. exact (@lem6161091 A B v u f op h2 (@lem6161092 A B op h1)). Qed.
Lemma lem6161094 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term99 A B op) : term105 A B v op u f.
Proof. exact (fun h0 : term106 A B v u f op => @lem6161093 A B v u f op h1 h0). Qed.
Lemma lem6161095 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (op : type1400 B) (h1 : term99 A B op) : term108 A B v op u.
Proof. exact (fun f : A -> B => @lem6161094 A B v u f op h1). Qed.
Lemma lem6161096 {A B : Type'} (v : A -> Prop) (op : type1400 B) (h1 : term99 A B op) : term109 A B v op.
Proof. exact (fun u : A -> Prop => @lem6161095 A B v u op h1). Qed.
Lemma lem6161097 {A B : Type'} (op : type1400 B) (h1 : term99 A B op) : term110 A B op.
Proof. exact (fun v : A -> Prop => @lem6161096 A B v op h1). Qed.
Lemma lem6161098 {A B : Type'} (op : type1400 B) : term111 A B op.
Proof. exact (fun h0 : term99 A B op => @lem6161097 A B op h0). Qed.
Lemma lem6161099 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term110 A B op.
Proof. exact (@lem6161098 A B op (@lem6161078 A B op h1)). Qed.
Lemma lem6161100 {A B : Type'} (v : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term112 A B op v.
Proof. exact (@lem6161099 A B op h1 v). Qed.
Lemma lem6161101 {A B : Type'} (v : A -> Prop) (op : type1400 B) : (term112 A B op v) = (term109 A B v op).
Proof. exact (eq_refl (term112 A B op v)). Qed.
Lemma lem6161102 {A B : Type'} (v : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term109 A B v op.
Proof. exact (EQ_MP (@lem6161101 A B v op) (@lem6161100 A B v op h1)). Qed.
Lemma lem6161103 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term113 A B v op u.
Proof. exact (@lem6161102 A B v op h1 u). Qed.
Lemma lem6161104 {A B : Type'} (v : A -> Prop) (op : type1400 B) (u : A -> Prop) : (term113 A B v op u) = (term108 A B v op u).
Proof. exact (eq_refl (term113 A B v op u)). Qed.
Lemma lem6161105 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term108 A B v op u.
Proof. exact (EQ_MP (@lem6161104 A B v op u) (@lem6161103 A B v u op h1)). Qed.
Lemma lem6161106 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term114 A B v op u f.
Proof. exact (@lem6161105 A B v u op h1 f). Qed.
Lemma lem6161107 {A B : Type'} (v : A -> Prop) (op : type1400 B) (u : A -> Prop) (f : A -> B) : (term114 A B v op u f) = (term105 A B v op u f).
Proof. exact (eq_refl (term114 A B v op u f)). Qed.
Lemma lem6161110 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term105 A B v op u f.
Proof. exact (EQ_MP (@lem6161107 A B v op u f) (@lem6161106 A B v u f op h1)). Qed.
Lemma lem6161111 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term105 A B v op u f.
Proof. exact (@lem6161110 A B v u f op h1). Qed.
Lemma lem6161112 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term118 A B f op s g.
Proof. exact (@lem6161111 A B (term91 A B f op g s) (@support A B op g s) g op h1). Qed.
Lemma lem6161116 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (EQ_MP (@lem6160762 A s t) (@lem6160761 A s t)). Qed.
Lemma lem6161117 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (@lem6161116 A s t). Qed.
Lemma lem6161118 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (s : A -> Prop) : (term119 A B f op g s) = (term120 A B f op g s).
Proof. exact (@lem6161117 A (term116 A B op f g s) (term91 A B f op g s)). Qed.
Lemma lem6161126 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (EQ_MP (@lem6160809 A B s f op) (@lem6160808 A B s f op)). Qed.
Lemma lem6161127 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (@lem6161126 A B s f op). Qed.
Lemma lem6161128 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term116 A B op f g s) = (term121 A B s f g op).
Proof. exact (@lem6161127 A B s (term62 A B op f g) op). Qed.
Lemma lem6161138 {A B : Type'} (f : A -> B) (y : A) : (term122 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6161139 {A B : Type'} (f : A -> B) (y : A) : (term122 A B f y) = (f y).
Proof. exact (@lem6161138 A B f y). Qed.
Lemma lem6161140 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x : A) : (term123 A B op f g x) = (term124 A B op f g x).
Proof. exact (@lem6161139 A B (term62 A B op f g) x). Qed.
Lemma lem6161141 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x : A) : (term124 A B op f g x) = (term125 A B op f g x).
Proof. exact (eq_refl (term124 A B op f g x)). Qed.
Lemma lem6161142 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) : (term126 A B op f g) = (term62 A B op f g).
Proof. exact (fun_ext (fun x : A => @lem6161141 A B op f g x)). Qed.
Lemma lem6161143 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6161144 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x : A) : (term123 A B op f g x) = (term124 A B op f g x).
Proof. exact (MK_COMB (@lem6161142 A B op f g) (@lem6161143 A x)). Qed.
Lemma lem6161145 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6161146 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x : A) : (term127 A B op f g x) = (term128 A B op f g x).
Proof. exact (MK_COMB (@lem6161145 B) (@lem6161144 A B op f g x)). Qed.
Lemma lem6161147 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x : A) : (term124 A B op f g x) = (term125 A B op f g x).
Proof. exact (eq_refl (term124 A B op f g x)). Qed.
Lemma lem6161148 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x : A) : ((term123 A B op f g x) = (term124 A B op f g x)) = ((term124 A B op f g x) = (term125 A B op f g x)).
Proof. exact (MK_COMB (@lem6161146 A B op f g x) (@lem6161147 A B op f g x)). Qed.
Lemma lem6161149 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x : A) : (term124 A B op f g x) = (term125 A B op f g x).
Proof. exact (EQ_MP (@lem6161148 A B op f g x) (@lem6161140 A B op f g x)). Qed.
Lemma lem6161150 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6161151 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x : A) : (term128 A B op f g x) = (term129 A B op f g x).
Proof. exact (MK_COMB (@lem6161150 B) (@lem6161149 A B op f g x)). Qed.
Lemma lem6161152 {B : Type'} (op : type1400 B) : (@neutral B op) = (@neutral B op).
Proof. exact (eq_refl (@neutral B op)). Qed.
Lemma lem6161153 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : ((term124 A B op f g x) = (@neutral B op)) = ((term125 A B op f g x) = (@neutral B op)).
Proof. exact (MK_COMB (@lem6161151 A B op f g x) (@lem6161152 B op)). Qed.
Lemma lem6161156 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6161157 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term130 A B f g x op) = (term131 A B f g x op).
Proof. exact (MK_COMB (@lem6161156) (@lem6161153 A B f g x op)). Qed.
Lemma lem6161158 {A : Type'} (x : A) (s : A -> Prop) : (term132 A x s) = (term132 A x s).
Proof. exact (eq_refl (term132 A x s)). Qed.
Lemma lem6161159 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term133 A B s f g x op) = (term134 A B s f g x op).
Proof. exact (MK_COMB (@lem6161158 A x s) (@lem6161157 A B f g x op)). Qed.
Lemma lem6161162 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem6161163 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term135 A B GEN_PVAR_237 s f g x op) = (term136 A B GEN_PVAR_237 s f g x op).
Proof. exact (MK_COMB (@lem6161162 A GEN_PVAR_237) (@lem6161159 A B s f g x op)). Qed.
Lemma lem6161164 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6161165 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (x : A) : (term137 A B GEN_PVAR_237 s f g op x) = (term138 A B GEN_PVAR_237 s f g op x).
Proof. exact (MK_COMB (@lem6161163 A B GEN_PVAR_237 s f g x op) (@lem6161164 A x)). Qed.
Lemma lem6161166 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term139 A B GEN_PVAR_237 s f g op) = (term140 A B GEN_PVAR_237 s f g op).
Proof. exact (fun_ext (fun x : A => @lem6161165 A B GEN_PVAR_237 s f g op x)). Qed.
Lemma lem6161167 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6161168 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term141 A B GEN_PVAR_237 s f g op) = (term142 A B GEN_PVAR_237 s f g op).
Proof. exact (MK_COMB (@lem6161167 A) (@lem6161166 A B GEN_PVAR_237 s f g op)). Qed.
Lemma lem6161173 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term143 A B s f g op) = (term144 A B s f g op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem6161168 A B GEN_PVAR_237 s f g op)). Qed.
Lemma lem6161174 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6161175 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term121 A B s f g op) = (term145 A B s f g op).
Proof. exact (MK_COMB (@lem6161174 A) (@lem6161173 A B s f g op)). Qed.
Lemma lem6161176 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term116 A B op f g s) = (term145 A B s f g op).
Proof. exact (TRANS (@lem6161128 A B s f g op) (@lem6161175 A B s f g op)). Qed.
Lemma lem6161177 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6161178 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term146 A B x op f g s) = (term147 A B x s f g op).
Proof. exact (MK_COMB (@lem6161177 A x) (@lem6161176 A B s f g op)). Qed.
Lemma lem6161180 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term15 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem6160793 _83095 p x) (@lem6160792 _83095 p x)). Qed.
Lemma lem6161181 {A : Type'} (p : A -> Prop) (x : A) : (term15 A x p) = (p x).
Proof. exact (@lem6161180 A p x). Qed.
Lemma lem6161182 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (x : A) : (term148 A B x s f g op) = (term149 A B s f g op x).
Proof. exact (@lem6161181 A (term150 A B s f g op) x). Qed.
Lemma lem6161183 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term149 A B s f g op x) = (term134 A B s f g x op).
Proof. exact (eq_refl (term149 A B s f g op x)). Qed.
Lemma lem6161184 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem6161185 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term151 A B GEN_PVAR_237 s f g op x) = (term136 A B GEN_PVAR_237 s f g x op).
Proof. exact (MK_COMB (@lem6161184 A GEN_PVAR_237) (@lem6161183 A B s f g x op)). Qed.
Lemma lem6161186 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6161187 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (x : A) : (term152 A B GEN_PVAR_237 s f g op x) = (term138 A B GEN_PVAR_237 s f g op x).
Proof. exact (MK_COMB (@lem6161185 A B GEN_PVAR_237 s f g x op) (@lem6161186 A x)). Qed.
Lemma lem6161188 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term153 A B GEN_PVAR_237 s f g op) = (term140 A B GEN_PVAR_237 s f g op).
Proof. exact (fun_ext (fun x : A => @lem6161187 A B GEN_PVAR_237 s f g op x)). Qed.
Lemma lem6161189 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6161190 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term154 A B GEN_PVAR_237 s f g op) = (term142 A B GEN_PVAR_237 s f g op).
Proof. exact (MK_COMB (@lem6161189 A) (@lem6161188 A B GEN_PVAR_237 s f g op)). Qed.
Lemma lem6161191 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term155 A B s f g op) = (term144 A B s f g op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem6161190 A B GEN_PVAR_237 s f g op)). Qed.
Lemma lem6161192 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6161193 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term156 A B s f g op) = (term145 A B s f g op).
Proof. exact (MK_COMB (@lem6161192 A) (@lem6161191 A B s f g op)). Qed.
Lemma lem6161194 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6161195 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term148 A B x s f g op) = (term147 A B x s f g op).
Proof. exact (MK_COMB (@lem6161194 A x) (@lem6161193 A B s f g op)). Qed.
Lemma lem6161196 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6161197 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term157 A B x s f g op) = (term158 A B x s f g op).
Proof. exact (MK_COMB (@lem6161196) (@lem6161195 A B x s f g op)). Qed.
Lemma lem6161198 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term149 A B s f g op x) = (term134 A B s f g x op).
Proof. exact (eq_refl (term149 A B s f g op x)). Qed.
Lemma lem6161199 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : ((term148 A B x s f g op) = (term149 A B s f g op x)) = ((term147 A B x s f g op) = (term134 A B s f g x op)).
Proof. exact (MK_COMB (@lem6161197 A B x s f g op) (@lem6161198 A B s f g x op)). Qed.
Lemma lem6161200 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term147 A B x s f g op) = (term134 A B s f g x op).
Proof. exact (EQ_MP (@lem6161199 A B s f g x op) (@lem6161182 A B s f g op x)). Qed.
Lemma lem6161205 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term146 A B x op f g s) = (term134 A B s f g x op).
Proof. exact (TRANS (@lem6161178 A B x s f g op) (@lem6161200 A B s f g x op)). Qed.
Lemma lem6161206 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6161207 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term159 A B x op f g s) = (term160 A B s f g x op).
Proof. exact (MK_COMB (@lem6161206) (@lem6161205 A B s f g x op)). Qed.
Lemma lem6161209 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term5 A x s t) = (term6 A s x t).
Proof. exact (EQ_MP (@lem6160756 A s x t) (@lem6160755 A s t x)). Qed.
Lemma lem6161210 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term5 A x s t) = (term6 A s x t).
Proof. exact (@lem6161209 A s x t). Qed.
Lemma lem6161211 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (g : A -> B) (s : A -> Prop) : (term161 A B x f op g s) = (term162 A B f x op g s).
Proof. exact (@lem6161210 A (@support A B op f s) x (@support A B op g s)). Qed.
Lemma lem6161215 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (EQ_MP (@lem6160809 A B s f op) (@lem6160808 A B s f op)). Qed.
Lemma lem6161216 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (@lem6161215 A B s f op). Qed.
Lemma lem6161225 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6161226 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term163 A B x op f s) = (term164 A B x s f op).
Proof. exact (MK_COMB (@lem6161225 A x) (@lem6161216 A B s f op)). Qed.
Lemma lem6161228 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term15 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem6160793 _83095 p x) (@lem6160792 _83095 p x)). Qed.
Lemma lem6161229 {A : Type'} (p : A -> Prop) (x : A) : (term15 A x p) = (p x).
Proof. exact (@lem6161228 A p x). Qed.
Lemma lem6161230 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term165 A B x s f op) = (term166 A B s f op x).
Proof. exact (@lem6161229 A (term167 A B s f op) x). Qed.
Lemma lem6161231 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term166 A B s f op x) = (term168 A B s f x op).
Proof. exact (eq_refl (term166 A B s f op x)). Qed.
Lemma lem6161232 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem6161233 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term169 A B GEN_PVAR_237 s f op x) = (term170 A B GEN_PVAR_237 s f x op).
Proof. exact (MK_COMB (@lem6161232 A GEN_PVAR_237) (@lem6161231 A B s f x op)). Qed.
Lemma lem6161234 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6161235 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term171 A B GEN_PVAR_237 s f op x) = (term172 A B GEN_PVAR_237 s f op x).
Proof. exact (MK_COMB (@lem6161233 A B GEN_PVAR_237 s f x op) (@lem6161234 A x)). Qed.
Lemma lem6161236 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term173 A B GEN_PVAR_237 s f op) = (term174 A B GEN_PVAR_237 s f op).
Proof. exact (fun_ext (fun x : A => @lem6161235 A B GEN_PVAR_237 s f op x)). Qed.
Lemma lem6161237 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6161238 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term175 A B GEN_PVAR_237 s f op) = (term176 A B GEN_PVAR_237 s f op).
Proof. exact (MK_COMB (@lem6161237 A) (@lem6161236 A B GEN_PVAR_237 s f op)). Qed.
Lemma lem6161239 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term177 A B s f op) = (term178 A B s f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem6161238 A B GEN_PVAR_237 s f op)). Qed.
Lemma lem6161240 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6161241 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term179 A B s f op) = (term21 A B s f op).
Proof. exact (MK_COMB (@lem6161240 A) (@lem6161239 A B s f op)). Qed.
Lemma lem6161242 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6161243 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term165 A B x s f op) = (term164 A B x s f op).
Proof. exact (MK_COMB (@lem6161242 A x) (@lem6161241 A B s f op)). Qed.
Lemma lem6161244 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6161245 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term180 A B x s f op) = (term181 A B x s f op).
Proof. exact (MK_COMB (@lem6161244) (@lem6161243 A B x s f op)). Qed.
Lemma lem6161246 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term166 A B s f op x) = (term168 A B s f x op).
Proof. exact (eq_refl (term166 A B s f op x)). Qed.
Lemma lem6161247 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : ((term165 A B x s f op) = (term166 A B s f op x)) = ((term164 A B x s f op) = (term168 A B s f x op)).
Proof. exact (MK_COMB (@lem6161245 A B x s f op) (@lem6161246 A B s f x op)). Qed.
Lemma lem6161248 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term164 A B x s f op) = (term168 A B s f x op).
Proof. exact (EQ_MP (@lem6161247 A B s f x op) (@lem6161230 A B s f op x)). Qed.
Lemma lem6161253 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term163 A B x op f s) = (term168 A B s f x op).
Proof. exact (TRANS (@lem6161226 A B x s f op) (@lem6161248 A B s f x op)). Qed.
Lemma lem6161254 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6161255 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term182 A B x op f s) = (term183 A B s f x op).
Proof. exact (MK_COMB (@lem6161254) (@lem6161253 A B s f x op)). Qed.
Lemma lem6161257 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (EQ_MP (@lem6160809 A B s f op) (@lem6160808 A B s f op)). Qed.
Lemma lem6161258 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (@lem6161257 A B s f op). Qed.
Lemma lem6161259 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) : (@support A B op g s) = (term21 A B s g op).
Proof. exact (@lem6161258 A B s g op). Qed.
Lemma lem6161268 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6161269 {A B : Type'} (x : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term163 A B x op g s) = (term164 A B x s g op).
Proof. exact (MK_COMB (@lem6161268 A x) (@lem6161259 A B s g op)). Qed.
Lemma lem6161271 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term15 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem6160793 _83095 p x) (@lem6160792 _83095 p x)). Qed.
Lemma lem6161272 {A : Type'} (p : A -> Prop) (x : A) : (term15 A x p) = (p x).
Proof. exact (@lem6161271 A p x). Qed.
Lemma lem6161273 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) (x : A) : (term165 A B x s g op) = (term166 A B s g op x).
Proof. exact (@lem6161272 A (term167 A B s g op) x). Qed.
Lemma lem6161274 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term166 A B s g op x) = (term168 A B s g x op).
Proof. exact (eq_refl (term166 A B s g op x)). Qed.
Lemma lem6161275 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem6161276 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term169 A B GEN_PVAR_237 s g op x) = (term170 A B GEN_PVAR_237 s g x op).
Proof. exact (MK_COMB (@lem6161275 A GEN_PVAR_237) (@lem6161274 A B s g x op)). Qed.
Lemma lem6161277 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6161278 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) (x : A) : (term171 A B GEN_PVAR_237 s g op x) = (term172 A B GEN_PVAR_237 s g op x).
Proof. exact (MK_COMB (@lem6161276 A B GEN_PVAR_237 s g x op) (@lem6161277 A x)). Qed.
Lemma lem6161279 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term173 A B GEN_PVAR_237 s g op) = (term174 A B GEN_PVAR_237 s g op).
Proof. exact (fun_ext (fun x : A => @lem6161278 A B GEN_PVAR_237 s g op x)). Qed.
Lemma lem6161280 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6161281 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term175 A B GEN_PVAR_237 s g op) = (term176 A B GEN_PVAR_237 s g op).
Proof. exact (MK_COMB (@lem6161280 A) (@lem6161279 A B GEN_PVAR_237 s g op)). Qed.
Lemma lem6161282 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term177 A B s g op) = (term178 A B s g op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem6161281 A B GEN_PVAR_237 s g op)). Qed.
Lemma lem6161283 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6161284 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term179 A B s g op) = (term21 A B s g op).
Proof. exact (MK_COMB (@lem6161283 A) (@lem6161282 A B s g op)). Qed.
Lemma lem6161285 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6161286 {A B : Type'} (x : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term165 A B x s g op) = (term164 A B x s g op).
Proof. exact (MK_COMB (@lem6161285 A x) (@lem6161284 A B s g op)). Qed.
Lemma lem6161287 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6161288 {A B : Type'} (x : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term180 A B x s g op) = (term181 A B x s g op).
Proof. exact (MK_COMB (@lem6161287) (@lem6161286 A B x s g op)). Qed.
Lemma lem6161289 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term166 A B s g op x) = (term168 A B s g x op).
Proof. exact (eq_refl (term166 A B s g op x)). Qed.
Lemma lem6161290 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : ((term165 A B x s g op) = (term166 A B s g op x)) = ((term164 A B x s g op) = (term168 A B s g x op)).
Proof. exact (MK_COMB (@lem6161288 A B x s g op) (@lem6161289 A B s g x op)). Qed.
Lemma lem6161291 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term164 A B x s g op) = (term168 A B s g x op).
Proof. exact (EQ_MP (@lem6161290 A B s g x op) (@lem6161273 A B s g op x)). Qed.
Lemma lem6161296 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term163 A B x op g s) = (term168 A B s g x op).
Proof. exact (TRANS (@lem6161269 A B x s g op) (@lem6161291 A B s g x op)). Qed.
Lemma lem6161297 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term162 A B f x op g s) = (term184 A B f s g x op).
Proof. exact (MK_COMB (@lem6161255 A B s f x op) (@lem6161296 A B s g x op)). Qed.
Lemma lem6161300 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term161 A B x f op g s) = (term184 A B f s g x op).
Proof. exact (TRANS (@lem6161211 A B f x op g s) (@lem6161297 A B f s g x op)). Qed.
Lemma lem6161301 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term185 A B x f op g s) = (term186 A B f s g x op).
Proof. exact (MK_COMB (@lem6161207 A B s f g x op) (@lem6161300 A B f s g x op)). Qed.
Lemma lem6161304 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term187 A B f op g s) = (term188 A B f s g op).
Proof. exact (fun_ext (fun x : A => @lem6161301 A B f s g x op)). Qed.
Lemma lem6161305 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6161306 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term120 A B f op g s) = (term189 A B f s g op).
Proof. exact (MK_COMB (@lem6161305 A) (@lem6161304 A B f s g op)). Qed.
Lemma lem6161311 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term119 A B f op g s) = (term189 A B f s g op).
Proof. exact (TRANS (@lem6161118 A B f op g s) (@lem6161306 A B f s g op)). Qed.
Lemma lem6161312 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6161313 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term190 A B f op g s) = (term191 A B f s g op).
Proof. exact (MK_COMB (@lem6161312) (@lem6161311 A B f s g op)). Qed.
Lemma lem6161323 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term5 A x s t) = (term6 A s x t).
Proof. exact (EQ_MP (@lem6160756 A s x t) (@lem6160755 A s t x)). Qed.
Lemma lem6161324 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term5 A x s t) = (term6 A s x t).
Proof. exact (@lem6161323 A s x t). Qed.
Lemma lem6161325 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (g : A -> B) (s : A -> Prop) : (term161 A B x f op g s) = (term162 A B f x op g s).
Proof. exact (@lem6161324 A (@support A B op f s) x (@support A B op g s)). Qed.
Lemma lem6161329 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (EQ_MP (@lem6160809 A B s f op) (@lem6160808 A B s f op)). Qed.
Lemma lem6161330 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (@lem6161329 A B s f op). Qed.
Lemma lem6161339 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6161340 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term163 A B x op f s) = (term164 A B x s f op).
Proof. exact (MK_COMB (@lem6161339 A x) (@lem6161330 A B s f op)). Qed.
Lemma lem6161342 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term15 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem6160793 _83095 p x) (@lem6160792 _83095 p x)). Qed.
Lemma lem6161343 {A : Type'} (p : A -> Prop) (x : A) : (term15 A x p) = (p x).
Proof. exact (@lem6161342 A p x). Qed.
Lemma lem6161344 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term165 A B x s f op) = (term166 A B s f op x).
Proof. exact (@lem6161343 A (term167 A B s f op) x). Qed.
Lemma lem6161345 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term166 A B s f op x) = (term168 A B s f x op).
Proof. exact (eq_refl (term166 A B s f op x)). Qed.
Lemma lem6161346 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem6161347 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term169 A B GEN_PVAR_237 s f op x) = (term170 A B GEN_PVAR_237 s f x op).
Proof. exact (MK_COMB (@lem6161346 A GEN_PVAR_237) (@lem6161345 A B s f x op)). Qed.
Lemma lem6161348 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6161349 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term171 A B GEN_PVAR_237 s f op x) = (term172 A B GEN_PVAR_237 s f op x).
Proof. exact (MK_COMB (@lem6161347 A B GEN_PVAR_237 s f x op) (@lem6161348 A x)). Qed.
Lemma lem6161350 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term173 A B GEN_PVAR_237 s f op) = (term174 A B GEN_PVAR_237 s f op).
Proof. exact (fun_ext (fun x : A => @lem6161349 A B GEN_PVAR_237 s f op x)). Qed.
Lemma lem6161351 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6161352 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term175 A B GEN_PVAR_237 s f op) = (term176 A B GEN_PVAR_237 s f op).
Proof. exact (MK_COMB (@lem6161351 A) (@lem6161350 A B GEN_PVAR_237 s f op)). Qed.
Lemma lem6161353 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term177 A B s f op) = (term178 A B s f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem6161352 A B GEN_PVAR_237 s f op)). Qed.
Lemma lem6161354 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6161355 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term179 A B s f op) = (term21 A B s f op).
Proof. exact (MK_COMB (@lem6161354 A) (@lem6161353 A B s f op)). Qed.
Lemma lem6161356 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6161357 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term165 A B x s f op) = (term164 A B x s f op).
Proof. exact (MK_COMB (@lem6161356 A x) (@lem6161355 A B s f op)). Qed.
Lemma lem6161358 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6161359 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term180 A B x s f op) = (term181 A B x s f op).
Proof. exact (MK_COMB (@lem6161358) (@lem6161357 A B x s f op)). Qed.
Lemma lem6161360 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term166 A B s f op x) = (term168 A B s f x op).
Proof. exact (eq_refl (term166 A B s f op x)). Qed.
Lemma lem6161361 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : ((term165 A B x s f op) = (term166 A B s f op x)) = ((term164 A B x s f op) = (term168 A B s f x op)).
Proof. exact (MK_COMB (@lem6161359 A B x s f op) (@lem6161360 A B s f x op)). Qed.
Lemma lem6161362 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term164 A B x s f op) = (term168 A B s f x op).
Proof. exact (EQ_MP (@lem6161361 A B s f x op) (@lem6161344 A B s f op x)). Qed.
Lemma lem6161367 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term163 A B x op f s) = (term168 A B s f x op).
Proof. exact (TRANS (@lem6161340 A B x s f op) (@lem6161362 A B s f x op)). Qed.
Lemma lem6161368 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6161369 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term182 A B x op f s) = (term183 A B s f x op).
Proof. exact (MK_COMB (@lem6161368) (@lem6161367 A B s f x op)). Qed.
Lemma lem6161371 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (EQ_MP (@lem6160809 A B s f op) (@lem6160808 A B s f op)). Qed.
Lemma lem6161372 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (@lem6161371 A B s f op). Qed.
Lemma lem6161373 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) : (@support A B op g s) = (term21 A B s g op).
Proof. exact (@lem6161372 A B s g op). Qed.
Lemma lem6161382 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6161383 {A B : Type'} (x : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term163 A B x op g s) = (term164 A B x s g op).
Proof. exact (MK_COMB (@lem6161382 A x) (@lem6161373 A B s g op)). Qed.
Lemma lem6161385 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term15 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem6160793 _83095 p x) (@lem6160792 _83095 p x)). Qed.
Lemma lem6161386 {A : Type'} (p : A -> Prop) (x : A) : (term15 A x p) = (p x).
Proof. exact (@lem6161385 A p x). Qed.
Lemma lem6161387 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) (x : A) : (term165 A B x s g op) = (term166 A B s g op x).
Proof. exact (@lem6161386 A (term167 A B s g op) x). Qed.
Lemma lem6161388 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term166 A B s g op x) = (term168 A B s g x op).
Proof. exact (eq_refl (term166 A B s g op x)). Qed.
Lemma lem6161389 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem6161390 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term169 A B GEN_PVAR_237 s g op x) = (term170 A B GEN_PVAR_237 s g x op).
Proof. exact (MK_COMB (@lem6161389 A GEN_PVAR_237) (@lem6161388 A B s g x op)). Qed.
Lemma lem6161391 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6161392 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) (x : A) : (term171 A B GEN_PVAR_237 s g op x) = (term172 A B GEN_PVAR_237 s g op x).
Proof. exact (MK_COMB (@lem6161390 A B GEN_PVAR_237 s g x op) (@lem6161391 A x)). Qed.
Lemma lem6161393 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term173 A B GEN_PVAR_237 s g op) = (term174 A B GEN_PVAR_237 s g op).
Proof. exact (fun_ext (fun x : A => @lem6161392 A B GEN_PVAR_237 s g op x)). Qed.
Lemma lem6161394 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6161395 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term175 A B GEN_PVAR_237 s g op) = (term176 A B GEN_PVAR_237 s g op).
Proof. exact (MK_COMB (@lem6161394 A) (@lem6161393 A B GEN_PVAR_237 s g op)). Qed.
Lemma lem6161396 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term177 A B s g op) = (term178 A B s g op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem6161395 A B GEN_PVAR_237 s g op)). Qed.
Lemma lem6161397 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6161398 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term179 A B s g op) = (term21 A B s g op).
Proof. exact (MK_COMB (@lem6161397 A) (@lem6161396 A B s g op)). Qed.
Lemma lem6161399 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6161400 {A B : Type'} (x : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term165 A B x s g op) = (term164 A B x s g op).
Proof. exact (MK_COMB (@lem6161399 A x) (@lem6161398 A B s g op)). Qed.
Lemma lem6161401 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6161402 {A B : Type'} (x : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term180 A B x s g op) = (term181 A B x s g op).
Proof. exact (MK_COMB (@lem6161401) (@lem6161400 A B x s g op)). Qed.
Lemma lem6161403 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term166 A B s g op x) = (term168 A B s g x op).
Proof. exact (eq_refl (term166 A B s g op x)). Qed.
Lemma lem6161404 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : ((term165 A B x s g op) = (term166 A B s g op x)) = ((term164 A B x s g op) = (term168 A B s g x op)).
Proof. exact (MK_COMB (@lem6161402 A B x s g op) (@lem6161403 A B s g x op)). Qed.
Lemma lem6161405 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term164 A B x s g op) = (term168 A B s g x op).
Proof. exact (EQ_MP (@lem6161404 A B s g x op) (@lem6161387 A B s g op x)). Qed.
Lemma lem6161410 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term163 A B x op g s) = (term168 A B s g x op).
Proof. exact (TRANS (@lem6161383 A B x s g op) (@lem6161405 A B s g x op)). Qed.
Lemma lem6161411 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term162 A B f x op g s) = (term184 A B f s g x op).
Proof. exact (MK_COMB (@lem6161369 A B s f x op) (@lem6161410 A B s g x op)). Qed.
Lemma lem6161414 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term161 A B x f op g s) = (term184 A B f s g x op).
Proof. exact (TRANS (@lem6161325 A B f x op g s) (@lem6161411 A B f s g x op)). Qed.
Lemma lem6161415 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6161416 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term192 A B x f op g s) = (term193 A B f s g x op).
Proof. exact (MK_COMB (@lem6161415) (@lem6161414 A B f s g x op)). Qed.
Lemma lem6161418 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (EQ_MP (@lem6160809 A B s f op) (@lem6160808 A B s f op)). Qed.
Lemma lem6161419 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (@lem6161418 A B s f op). Qed.
Lemma lem6161420 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term116 A B op f g s) = (term121 A B s f g op).
Proof. exact (@lem6161419 A B s (term62 A B op f g) op). Qed.
Lemma lem6161430 {A B : Type'} (f : A -> B) (y : A) : (term122 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6161431 {A B : Type'} (f : A -> B) (y : A) : (term122 A B f y) = (f y).
Proof. exact (@lem6161430 A B f y). Qed.
Lemma lem6161432 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x : A) : (term123 A B op f g x) = (term124 A B op f g x).
Proof. exact (@lem6161431 A B (term62 A B op f g) x). Qed.
Lemma lem6161433 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x : A) : (term124 A B op f g x) = (term125 A B op f g x).
Proof. exact (eq_refl (term124 A B op f g x)). Qed.
Lemma lem6161434 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) : (term126 A B op f g) = (term62 A B op f g).
Proof. exact (fun_ext (fun x : A => @lem6161433 A B op f g x)). Qed.
Lemma lem6161435 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6161436 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x : A) : (term123 A B op f g x) = (term124 A B op f g x).
Proof. exact (MK_COMB (@lem6161434 A B op f g) (@lem6161435 A x)). Qed.
Lemma lem6161437 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6161438 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x : A) : (term127 A B op f g x) = (term128 A B op f g x).
Proof. exact (MK_COMB (@lem6161437 B) (@lem6161436 A B op f g x)). Qed.
Lemma lem6161439 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x : A) : (term124 A B op f g x) = (term125 A B op f g x).
Proof. exact (eq_refl (term124 A B op f g x)). Qed.
Lemma lem6161440 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x : A) : ((term123 A B op f g x) = (term124 A B op f g x)) = ((term124 A B op f g x) = (term125 A B op f g x)).
Proof. exact (MK_COMB (@lem6161438 A B op f g x) (@lem6161439 A B op f g x)). Qed.
Lemma lem6161441 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x : A) : (term124 A B op f g x) = (term125 A B op f g x).
Proof. exact (EQ_MP (@lem6161440 A B op f g x) (@lem6161432 A B op f g x)). Qed.
Lemma lem6161442 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6161443 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x : A) : (term128 A B op f g x) = (term129 A B op f g x).
Proof. exact (MK_COMB (@lem6161442 B) (@lem6161441 A B op f g x)). Qed.
Lemma lem6161444 {B : Type'} (op : type1400 B) : (@neutral B op) = (@neutral B op).
Proof. exact (eq_refl (@neutral B op)). Qed.
Lemma lem6161445 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : ((term124 A B op f g x) = (@neutral B op)) = ((term125 A B op f g x) = (@neutral B op)).
Proof. exact (MK_COMB (@lem6161443 A B op f g x) (@lem6161444 B op)). Qed.
Lemma lem6161448 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6161449 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term130 A B f g x op) = (term131 A B f g x op).
Proof. exact (MK_COMB (@lem6161448) (@lem6161445 A B f g x op)). Qed.
Lemma lem6161450 {A : Type'} (x : A) (s : A -> Prop) : (term132 A x s) = (term132 A x s).
Proof. exact (eq_refl (term132 A x s)). Qed.
Lemma lem6161451 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term133 A B s f g x op) = (term134 A B s f g x op).
Proof. exact (MK_COMB (@lem6161450 A x s) (@lem6161449 A B f g x op)). Qed.
Lemma lem6161454 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem6161455 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term135 A B GEN_PVAR_237 s f g x op) = (term136 A B GEN_PVAR_237 s f g x op).
Proof. exact (MK_COMB (@lem6161454 A GEN_PVAR_237) (@lem6161451 A B s f g x op)). Qed.
Lemma lem6161456 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6161457 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (x : A) : (term137 A B GEN_PVAR_237 s f g op x) = (term138 A B GEN_PVAR_237 s f g op x).
Proof. exact (MK_COMB (@lem6161455 A B GEN_PVAR_237 s f g x op) (@lem6161456 A x)). Qed.
Lemma lem6161458 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term139 A B GEN_PVAR_237 s f g op) = (term140 A B GEN_PVAR_237 s f g op).
Proof. exact (fun_ext (fun x : A => @lem6161457 A B GEN_PVAR_237 s f g op x)). Qed.
Lemma lem6161459 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6161460 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term141 A B GEN_PVAR_237 s f g op) = (term142 A B GEN_PVAR_237 s f g op).
Proof. exact (MK_COMB (@lem6161459 A) (@lem6161458 A B GEN_PVAR_237 s f g op)). Qed.
Lemma lem6161465 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term143 A B s f g op) = (term144 A B s f g op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem6161460 A B GEN_PVAR_237 s f g op)). Qed.
Lemma lem6161466 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6161467 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term121 A B s f g op) = (term145 A B s f g op).
Proof. exact (MK_COMB (@lem6161466 A) (@lem6161465 A B s f g op)). Qed.
Lemma lem6161468 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term116 A B op f g s) = (term145 A B s f g op).
Proof. exact (TRANS (@lem6161420 A B s f g op) (@lem6161467 A B s f g op)). Qed.
Lemma lem6161469 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6161470 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term146 A B x op f g s) = (term147 A B x s f g op).
Proof. exact (MK_COMB (@lem6161469 A x) (@lem6161468 A B s f g op)). Qed.
Lemma lem6161472 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term15 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem6160793 _83095 p x) (@lem6160792 _83095 p x)). Qed.
Lemma lem6161473 {A : Type'} (p : A -> Prop) (x : A) : (term15 A x p) = (p x).
Proof. exact (@lem6161472 A p x). Qed.
Lemma lem6161474 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (x : A) : (term148 A B x s f g op) = (term149 A B s f g op x).
Proof. exact (@lem6161473 A (term150 A B s f g op) x). Qed.
Lemma lem6161475 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term149 A B s f g op x) = (term134 A B s f g x op).
Proof. exact (eq_refl (term149 A B s f g op x)). Qed.
Lemma lem6161476 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem6161477 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term151 A B GEN_PVAR_237 s f g op x) = (term136 A B GEN_PVAR_237 s f g x op).
Proof. exact (MK_COMB (@lem6161476 A GEN_PVAR_237) (@lem6161475 A B s f g x op)). Qed.
Lemma lem6161478 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6161479 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (x : A) : (term152 A B GEN_PVAR_237 s f g op x) = (term138 A B GEN_PVAR_237 s f g op x).
Proof. exact (MK_COMB (@lem6161477 A B GEN_PVAR_237 s f g x op) (@lem6161478 A x)). Qed.
Lemma lem6161480 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term153 A B GEN_PVAR_237 s f g op) = (term140 A B GEN_PVAR_237 s f g op).
Proof. exact (fun_ext (fun x : A => @lem6161479 A B GEN_PVAR_237 s f g op x)). Qed.
Lemma lem6161481 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6161482 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term154 A B GEN_PVAR_237 s f g op) = (term142 A B GEN_PVAR_237 s f g op).
Proof. exact (MK_COMB (@lem6161481 A) (@lem6161480 A B GEN_PVAR_237 s f g op)). Qed.
Lemma lem6161483 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term155 A B s f g op) = (term144 A B s f g op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem6161482 A B GEN_PVAR_237 s f g op)). Qed.
Lemma lem6161484 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6161485 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term156 A B s f g op) = (term145 A B s f g op).
Proof. exact (MK_COMB (@lem6161484 A) (@lem6161483 A B s f g op)). Qed.
Lemma lem6161486 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6161487 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term148 A B x s f g op) = (term147 A B x s f g op).
Proof. exact (MK_COMB (@lem6161486 A x) (@lem6161485 A B s f g op)). Qed.
Lemma lem6161488 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6161489 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term157 A B x s f g op) = (term158 A B x s f g op).
Proof. exact (MK_COMB (@lem6161488) (@lem6161487 A B x s f g op)). Qed.
Lemma lem6161490 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term149 A B s f g op x) = (term134 A B s f g x op).
Proof. exact (eq_refl (term149 A B s f g op x)). Qed.
Lemma lem6161491 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : ((term148 A B x s f g op) = (term149 A B s f g op x)) = ((term147 A B x s f g op) = (term134 A B s f g x op)).
Proof. exact (MK_COMB (@lem6161489 A B x s f g op) (@lem6161490 A B s f g x op)). Qed.
Lemma lem6161492 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term147 A B x s f g op) = (term134 A B s f g x op).
Proof. exact (EQ_MP (@lem6161491 A B s f g x op) (@lem6161474 A B s f g op x)). Qed.
Lemma lem6161497 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term146 A B x op f g s) = (term134 A B s f g x op).
Proof. exact (TRANS (@lem6161470 A B x s f g op) (@lem6161492 A B s f g x op)). Qed.
Lemma lem6161498 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6161499 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term194 A B x op f g s) = (term195 A B s f g x op).
Proof. exact (MK_COMB (@lem6161498) (@lem6161497 A B s f g x op)). Qed.
Lemma lem6161500 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term196 A B x op f g s) = (term197 A B s f g x op).
Proof. exact (MK_COMB (@lem6161416 A B f s g x op) (@lem6161499 A B s f g x op)). Qed.
Lemma lem6161503 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6161504 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term198 A B x op f g s) = (term199 A B s f g x op).
Proof. exact (MK_COMB (@lem6161503) (@lem6161500 A B s f g x op)). Qed.
Lemma lem6161508 {A B : Type'} (f : A -> B) (y : A) : (term122 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6161509 {A B : Type'} (f : A -> B) (y : A) : (term122 A B f y) = (f y).
Proof. exact (@lem6161508 A B f y). Qed.
Lemma lem6161510 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x : A) : (term123 A B op f g x) = (term124 A B op f g x).
Proof. exact (@lem6161509 A B (term62 A B op f g) x). Qed.
Lemma lem6161511 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x : A) : (term124 A B op f g x) = (term125 A B op f g x).
Proof. exact (eq_refl (term124 A B op f g x)). Qed.
Lemma lem6161512 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) : (term126 A B op f g) = (term62 A B op f g).
Proof. exact (fun_ext (fun x : A => @lem6161511 A B op f g x)). Qed.
Lemma lem6161513 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6161514 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x : A) : (term123 A B op f g x) = (term124 A B op f g x).
Proof. exact (MK_COMB (@lem6161512 A B op f g) (@lem6161513 A x)). Qed.
Lemma lem6161515 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6161516 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x : A) : (term127 A B op f g x) = (term128 A B op f g x).
Proof. exact (MK_COMB (@lem6161515 B) (@lem6161514 A B op f g x)). Qed.
Lemma lem6161517 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x : A) : (term124 A B op f g x) = (term125 A B op f g x).
Proof. exact (eq_refl (term124 A B op f g x)). Qed.
Lemma lem6161518 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x : A) : ((term123 A B op f g x) = (term124 A B op f g x)) = ((term124 A B op f g x) = (term125 A B op f g x)).
Proof. exact (MK_COMB (@lem6161516 A B op f g x) (@lem6161517 A B op f g x)). Qed.
Lemma lem6161519 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x : A) : (term124 A B op f g x) = (term125 A B op f g x).
Proof. exact (EQ_MP (@lem6161518 A B op f g x) (@lem6161510 A B op f g x)). Qed.
Lemma lem6161520 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6161521 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x : A) : (term128 A B op f g x) = (term129 A B op f g x).
Proof. exact (MK_COMB (@lem6161520 B) (@lem6161519 A B op f g x)). Qed.
Lemma lem6161522 {B : Type'} (op : type1400 B) : (@neutral B op) = (@neutral B op).
Proof. exact (eq_refl (@neutral B op)). Qed.
Lemma lem6161523 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : ((term124 A B op f g x) = (@neutral B op)) = ((term125 A B op f g x) = (@neutral B op)).
Proof. exact (MK_COMB (@lem6161521 A B op f g x) (@lem6161522 B op)). Qed.
Lemma lem6161526 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term200 A B s f g x op) = (term201 A B s f g x op).
Proof. exact (MK_COMB (@lem6161504 A B s f g x op) (@lem6161523 A B f g x op)). Qed.
Lemma lem6161529 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term202 A B s f g op) = (term203 A B s f g op).
Proof. exact (fun_ext (fun x : A => @lem6161526 A B s f g x op)). Qed.
Lemma lem6161530 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6161531 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term204 A B s f g op) = (term205 A B s f g op).
Proof. exact (MK_COMB (@lem6161530 A) (@lem6161529 A B s f g op)). Qed.
Lemma lem6161536 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term206 A B s f g op) = (term207 A B s f g op).
Proof. exact (MK_COMB (@lem6161313 A B f s g op) (@lem6161531 A B s f g op)). Qed.
Lemma lem6161539 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term207 A B s f g op) = (term206 A B s f g op).
Proof. exact (SYM (@lem6161536 A B s f g op)). Qed.
Lemma lem6161543 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (EQ_MP (@lem6160762 A s t) (@lem6160761 A s t)). Qed.
Lemma lem6161544 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (@lem6161543 A s t). Qed.
Lemma lem6161545 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (s : A -> Prop) : (term208 A B f op g s) = (term209 A B f op g s).
Proof. exact (@lem6161544 A (@support A B op f s) (term91 A B f op g s)). Qed.
Lemma lem6161553 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (EQ_MP (@lem6160809 A B s f op) (@lem6160808 A B s f op)). Qed.
Lemma lem6161554 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (@lem6161553 A B s f op). Qed.
Lemma lem6161563 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6161564 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term163 A B x op f s) = (term164 A B x s f op).
Proof. exact (MK_COMB (@lem6161563 A x) (@lem6161554 A B s f op)). Qed.
Lemma lem6161566 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term15 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem6160793 _83095 p x) (@lem6160792 _83095 p x)). Qed.
Lemma lem6161567 {A : Type'} (p : A -> Prop) (x : A) : (term15 A x p) = (p x).
Proof. exact (@lem6161566 A p x). Qed.
Lemma lem6161568 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term165 A B x s f op) = (term166 A B s f op x).
Proof. exact (@lem6161567 A (term167 A B s f op) x). Qed.
Lemma lem6161569 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term166 A B s f op x) = (term168 A B s f x op).
Proof. exact (eq_refl (term166 A B s f op x)). Qed.
Lemma lem6161570 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem6161571 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term169 A B GEN_PVAR_237 s f op x) = (term170 A B GEN_PVAR_237 s f x op).
Proof. exact (MK_COMB (@lem6161570 A GEN_PVAR_237) (@lem6161569 A B s f x op)). Qed.
Lemma lem6161572 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6161573 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term171 A B GEN_PVAR_237 s f op x) = (term172 A B GEN_PVAR_237 s f op x).
Proof. exact (MK_COMB (@lem6161571 A B GEN_PVAR_237 s f x op) (@lem6161572 A x)). Qed.
Lemma lem6161574 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term173 A B GEN_PVAR_237 s f op) = (term174 A B GEN_PVAR_237 s f op).
Proof. exact (fun_ext (fun x : A => @lem6161573 A B GEN_PVAR_237 s f op x)). Qed.
Lemma lem6161575 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6161576 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term175 A B GEN_PVAR_237 s f op) = (term176 A B GEN_PVAR_237 s f op).
Proof. exact (MK_COMB (@lem6161575 A) (@lem6161574 A B GEN_PVAR_237 s f op)). Qed.
Lemma lem6161577 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term177 A B s f op) = (term178 A B s f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem6161576 A B GEN_PVAR_237 s f op)). Qed.
Lemma lem6161578 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6161579 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term179 A B s f op) = (term21 A B s f op).
Proof. exact (MK_COMB (@lem6161578 A) (@lem6161577 A B s f op)). Qed.
Lemma lem6161580 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6161581 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term165 A B x s f op) = (term164 A B x s f op).
Proof. exact (MK_COMB (@lem6161580 A x) (@lem6161579 A B s f op)). Qed.
Lemma lem6161582 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6161583 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term180 A B x s f op) = (term181 A B x s f op).
Proof. exact (MK_COMB (@lem6161582) (@lem6161581 A B x s f op)). Qed.
Lemma lem6161584 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term166 A B s f op x) = (term168 A B s f x op).
Proof. exact (eq_refl (term166 A B s f op x)). Qed.
Lemma lem6161585 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : ((term165 A B x s f op) = (term166 A B s f op x)) = ((term164 A B x s f op) = (term168 A B s f x op)).
Proof. exact (MK_COMB (@lem6161583 A B x s f op) (@lem6161584 A B s f x op)). Qed.
Lemma lem6161586 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term164 A B x s f op) = (term168 A B s f x op).
Proof. exact (EQ_MP (@lem6161585 A B s f x op) (@lem6161568 A B s f op x)). Qed.
Lemma lem6161591 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term163 A B x op f s) = (term168 A B s f x op).
Proof. exact (TRANS (@lem6161564 A B x s f op) (@lem6161586 A B s f x op)). Qed.
Lemma lem6161592 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6161593 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term210 A B x op f s) = (term211 A B s f x op).
Proof. exact (MK_COMB (@lem6161592) (@lem6161591 A B s f x op)). Qed.
Lemma lem6161595 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term5 A x s t) = (term6 A s x t).
Proof. exact (EQ_MP (@lem6160756 A s x t) (@lem6160755 A s t x)). Qed.
Lemma lem6161596 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term5 A x s t) = (term6 A s x t).
Proof. exact (@lem6161595 A s x t). Qed.
Lemma lem6161597 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (g : A -> B) (s : A -> Prop) : (term161 A B x f op g s) = (term162 A B f x op g s).
Proof. exact (@lem6161596 A (@support A B op f s) x (@support A B op g s)). Qed.
Lemma lem6161601 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (EQ_MP (@lem6160809 A B s f op) (@lem6160808 A B s f op)). Qed.
Lemma lem6161602 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (@lem6161601 A B s f op). Qed.
Lemma lem6161611 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6161612 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term163 A B x op f s) = (term164 A B x s f op).
Proof. exact (MK_COMB (@lem6161611 A x) (@lem6161602 A B s f op)). Qed.
Lemma lem6161614 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term15 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem6160793 _83095 p x) (@lem6160792 _83095 p x)). Qed.
Lemma lem6161615 {A : Type'} (p : A -> Prop) (x : A) : (term15 A x p) = (p x).
Proof. exact (@lem6161614 A p x). Qed.
Lemma lem6161616 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term165 A B x s f op) = (term166 A B s f op x).
Proof. exact (@lem6161615 A (term167 A B s f op) x). Qed.
Lemma lem6161617 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term166 A B s f op x) = (term168 A B s f x op).
Proof. exact (eq_refl (term166 A B s f op x)). Qed.
Lemma lem6161618 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem6161619 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term169 A B GEN_PVAR_237 s f op x) = (term170 A B GEN_PVAR_237 s f x op).
Proof. exact (MK_COMB (@lem6161618 A GEN_PVAR_237) (@lem6161617 A B s f x op)). Qed.
Lemma lem6161620 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6161621 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term171 A B GEN_PVAR_237 s f op x) = (term172 A B GEN_PVAR_237 s f op x).
Proof. exact (MK_COMB (@lem6161619 A B GEN_PVAR_237 s f x op) (@lem6161620 A x)). Qed.
Lemma lem6161622 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term173 A B GEN_PVAR_237 s f op) = (term174 A B GEN_PVAR_237 s f op).
Proof. exact (fun_ext (fun x : A => @lem6161621 A B GEN_PVAR_237 s f op x)). Qed.
Lemma lem6161623 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6161624 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term175 A B GEN_PVAR_237 s f op) = (term176 A B GEN_PVAR_237 s f op).
Proof. exact (MK_COMB (@lem6161623 A) (@lem6161622 A B GEN_PVAR_237 s f op)). Qed.
Lemma lem6161625 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term177 A B s f op) = (term178 A B s f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem6161624 A B GEN_PVAR_237 s f op)). Qed.
Lemma lem6161626 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6161627 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term179 A B s f op) = (term21 A B s f op).
Proof. exact (MK_COMB (@lem6161626 A) (@lem6161625 A B s f op)). Qed.
Lemma lem6161628 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6161629 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term165 A B x s f op) = (term164 A B x s f op).
Proof. exact (MK_COMB (@lem6161628 A x) (@lem6161627 A B s f op)). Qed.
Lemma lem6161630 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6161631 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term180 A B x s f op) = (term181 A B x s f op).
Proof. exact (MK_COMB (@lem6161630) (@lem6161629 A B x s f op)). Qed.
Lemma lem6161632 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term166 A B s f op x) = (term168 A B s f x op).
Proof. exact (eq_refl (term166 A B s f op x)). Qed.
Lemma lem6161633 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : ((term165 A B x s f op) = (term166 A B s f op x)) = ((term164 A B x s f op) = (term168 A B s f x op)).
Proof. exact (MK_COMB (@lem6161631 A B x s f op) (@lem6161632 A B s f x op)). Qed.
Lemma lem6161634 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term164 A B x s f op) = (term168 A B s f x op).
Proof. exact (EQ_MP (@lem6161633 A B s f x op) (@lem6161616 A B s f op x)). Qed.
Lemma lem6161639 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term163 A B x op f s) = (term168 A B s f x op).
Proof. exact (TRANS (@lem6161612 A B x s f op) (@lem6161634 A B s f x op)). Qed.
Lemma lem6161640 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6161641 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term182 A B x op f s) = (term183 A B s f x op).
Proof. exact (MK_COMB (@lem6161640) (@lem6161639 A B s f x op)). Qed.
Lemma lem6161643 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (EQ_MP (@lem6160809 A B s f op) (@lem6160808 A B s f op)). Qed.
Lemma lem6161644 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (@lem6161643 A B s f op). Qed.
Lemma lem6161645 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) : (@support A B op g s) = (term21 A B s g op).
Proof. exact (@lem6161644 A B s g op). Qed.
Lemma lem6161654 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6161655 {A B : Type'} (x : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term163 A B x op g s) = (term164 A B x s g op).
Proof. exact (MK_COMB (@lem6161654 A x) (@lem6161645 A B s g op)). Qed.
Lemma lem6161657 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term15 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem6160793 _83095 p x) (@lem6160792 _83095 p x)). Qed.
Lemma lem6161658 {A : Type'} (p : A -> Prop) (x : A) : (term15 A x p) = (p x).
Proof. exact (@lem6161657 A p x). Qed.
Lemma lem6161659 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) (x : A) : (term165 A B x s g op) = (term166 A B s g op x).
Proof. exact (@lem6161658 A (term167 A B s g op) x). Qed.
Lemma lem6161660 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term166 A B s g op x) = (term168 A B s g x op).
Proof. exact (eq_refl (term166 A B s g op x)). Qed.
Lemma lem6161661 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem6161662 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term169 A B GEN_PVAR_237 s g op x) = (term170 A B GEN_PVAR_237 s g x op).
Proof. exact (MK_COMB (@lem6161661 A GEN_PVAR_237) (@lem6161660 A B s g x op)). Qed.
Lemma lem6161663 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6161664 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) (x : A) : (term171 A B GEN_PVAR_237 s g op x) = (term172 A B GEN_PVAR_237 s g op x).
Proof. exact (MK_COMB (@lem6161662 A B GEN_PVAR_237 s g x op) (@lem6161663 A x)). Qed.
Lemma lem6161665 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term173 A B GEN_PVAR_237 s g op) = (term174 A B GEN_PVAR_237 s g op).
Proof. exact (fun_ext (fun x : A => @lem6161664 A B GEN_PVAR_237 s g op x)). Qed.
Lemma lem6161666 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6161667 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term175 A B GEN_PVAR_237 s g op) = (term176 A B GEN_PVAR_237 s g op).
Proof. exact (MK_COMB (@lem6161666 A) (@lem6161665 A B GEN_PVAR_237 s g op)). Qed.
Lemma lem6161668 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term177 A B s g op) = (term178 A B s g op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem6161667 A B GEN_PVAR_237 s g op)). Qed.
Lemma lem6161669 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6161670 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term179 A B s g op) = (term21 A B s g op).
Proof. exact (MK_COMB (@lem6161669 A) (@lem6161668 A B s g op)). Qed.
Lemma lem6161671 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6161672 {A B : Type'} (x : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term165 A B x s g op) = (term164 A B x s g op).
Proof. exact (MK_COMB (@lem6161671 A x) (@lem6161670 A B s g op)). Qed.
Lemma lem6161673 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6161674 {A B : Type'} (x : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term180 A B x s g op) = (term181 A B x s g op).
Proof. exact (MK_COMB (@lem6161673) (@lem6161672 A B x s g op)). Qed.
Lemma lem6161675 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term166 A B s g op x) = (term168 A B s g x op).
Proof. exact (eq_refl (term166 A B s g op x)). Qed.
Lemma lem6161676 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : ((term165 A B x s g op) = (term166 A B s g op x)) = ((term164 A B x s g op) = (term168 A B s g x op)).
Proof. exact (MK_COMB (@lem6161674 A B x s g op) (@lem6161675 A B s g x op)). Qed.
Lemma lem6161677 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term164 A B x s g op) = (term168 A B s g x op).
Proof. exact (EQ_MP (@lem6161676 A B s g x op) (@lem6161659 A B s g op x)). Qed.
Lemma lem6161682 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term163 A B x op g s) = (term168 A B s g x op).
Proof. exact (TRANS (@lem6161655 A B x s g op) (@lem6161677 A B s g x op)). Qed.
Lemma lem6161683 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term162 A B f x op g s) = (term184 A B f s g x op).
Proof. exact (MK_COMB (@lem6161641 A B s f x op) (@lem6161682 A B s g x op)). Qed.
Lemma lem6161686 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term161 A B x f op g s) = (term184 A B f s g x op).
Proof. exact (TRANS (@lem6161597 A B f x op g s) (@lem6161683 A B f s g x op)). Qed.
Lemma lem6161687 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term212 A B x f op g s) = (term213 A B f s g x op).
Proof. exact (MK_COMB (@lem6161593 A B s f x op) (@lem6161686 A B f s g x op)). Qed.
Lemma lem6161690 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term214 A B f op g s) = (term215 A B f s g op).
Proof. exact (fun_ext (fun x : A => @lem6161687 A B f s g x op)). Qed.
Lemma lem6161691 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6161692 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term209 A B f op g s) = (term216 A B f s g op).
Proof. exact (MK_COMB (@lem6161691 A) (@lem6161690 A B f s g op)). Qed.
Lemma lem6161697 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term208 A B f op g s) = (term216 A B f s g op).
Proof. exact (TRANS (@lem6161545 A B f op g s) (@lem6161692 A B f s g op)). Qed.
Lemma lem6161698 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6161699 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term217 A B f op g s) = (term218 A B f s g op).
Proof. exact (MK_COMB (@lem6161698) (@lem6161697 A B f s g op)). Qed.
Lemma lem6161709 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term5 A x s t) = (term6 A s x t).
Proof. exact (EQ_MP (@lem6160756 A s x t) (@lem6160755 A s t x)). Qed.
Lemma lem6161710 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term5 A x s t) = (term6 A s x t).
Proof. exact (@lem6161709 A s x t). Qed.
Lemma lem6161711 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (g : A -> B) (s : A -> Prop) : (term161 A B x f op g s) = (term162 A B f x op g s).
Proof. exact (@lem6161710 A (@support A B op f s) x (@support A B op g s)). Qed.
Lemma lem6161715 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (EQ_MP (@lem6160809 A B s f op) (@lem6160808 A B s f op)). Qed.
Lemma lem6161716 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (@lem6161715 A B s f op). Qed.
Lemma lem6161725 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6161726 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term163 A B x op f s) = (term164 A B x s f op).
Proof. exact (MK_COMB (@lem6161725 A x) (@lem6161716 A B s f op)). Qed.
Lemma lem6161728 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term15 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem6160793 _83095 p x) (@lem6160792 _83095 p x)). Qed.
Lemma lem6161729 {A : Type'} (p : A -> Prop) (x : A) : (term15 A x p) = (p x).
Proof. exact (@lem6161728 A p x). Qed.
Lemma lem6161730 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term165 A B x s f op) = (term166 A B s f op x).
Proof. exact (@lem6161729 A (term167 A B s f op) x). Qed.
Lemma lem6161731 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term166 A B s f op x) = (term168 A B s f x op).
Proof. exact (eq_refl (term166 A B s f op x)). Qed.
Lemma lem6161732 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem6161733 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term169 A B GEN_PVAR_237 s f op x) = (term170 A B GEN_PVAR_237 s f x op).
Proof. exact (MK_COMB (@lem6161732 A GEN_PVAR_237) (@lem6161731 A B s f x op)). Qed.
Lemma lem6161734 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6161735 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term171 A B GEN_PVAR_237 s f op x) = (term172 A B GEN_PVAR_237 s f op x).
Proof. exact (MK_COMB (@lem6161733 A B GEN_PVAR_237 s f x op) (@lem6161734 A x)). Qed.
Lemma lem6161736 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term173 A B GEN_PVAR_237 s f op) = (term174 A B GEN_PVAR_237 s f op).
Proof. exact (fun_ext (fun x : A => @lem6161735 A B GEN_PVAR_237 s f op x)). Qed.
Lemma lem6161737 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6161738 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term175 A B GEN_PVAR_237 s f op) = (term176 A B GEN_PVAR_237 s f op).
Proof. exact (MK_COMB (@lem6161737 A) (@lem6161736 A B GEN_PVAR_237 s f op)). Qed.
Lemma lem6161739 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term177 A B s f op) = (term178 A B s f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem6161738 A B GEN_PVAR_237 s f op)). Qed.
Lemma lem6161740 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6161741 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term179 A B s f op) = (term21 A B s f op).
Proof. exact (MK_COMB (@lem6161740 A) (@lem6161739 A B s f op)). Qed.
Lemma lem6161742 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6161743 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term165 A B x s f op) = (term164 A B x s f op).
Proof. exact (MK_COMB (@lem6161742 A x) (@lem6161741 A B s f op)). Qed.
Lemma lem6161744 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6161745 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term180 A B x s f op) = (term181 A B x s f op).
Proof. exact (MK_COMB (@lem6161744) (@lem6161743 A B x s f op)). Qed.
Lemma lem6161746 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term166 A B s f op x) = (term168 A B s f x op).
Proof. exact (eq_refl (term166 A B s f op x)). Qed.
Lemma lem6161747 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : ((term165 A B x s f op) = (term166 A B s f op x)) = ((term164 A B x s f op) = (term168 A B s f x op)).
Proof. exact (MK_COMB (@lem6161745 A B x s f op) (@lem6161746 A B s f x op)). Qed.
Lemma lem6161748 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term164 A B x s f op) = (term168 A B s f x op).
Proof. exact (EQ_MP (@lem6161747 A B s f x op) (@lem6161730 A B s f op x)). Qed.
Lemma lem6161753 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term163 A B x op f s) = (term168 A B s f x op).
Proof. exact (TRANS (@lem6161726 A B x s f op) (@lem6161748 A B s f x op)). Qed.
Lemma lem6161754 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6161755 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term182 A B x op f s) = (term183 A B s f x op).
Proof. exact (MK_COMB (@lem6161754) (@lem6161753 A B s f x op)). Qed.
Lemma lem6161757 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (EQ_MP (@lem6160809 A B s f op) (@lem6160808 A B s f op)). Qed.
Lemma lem6161758 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (@lem6161757 A B s f op). Qed.
Lemma lem6161759 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) : (@support A B op g s) = (term21 A B s g op).
Proof. exact (@lem6161758 A B s g op). Qed.
Lemma lem6161768 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6161769 {A B : Type'} (x : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term163 A B x op g s) = (term164 A B x s g op).
Proof. exact (MK_COMB (@lem6161768 A x) (@lem6161759 A B s g op)). Qed.
Lemma lem6161771 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term15 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem6160793 _83095 p x) (@lem6160792 _83095 p x)). Qed.
Lemma lem6161772 {A : Type'} (p : A -> Prop) (x : A) : (term15 A x p) = (p x).
Proof. exact (@lem6161771 A p x). Qed.
Lemma lem6161773 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) (x : A) : (term165 A B x s g op) = (term166 A B s g op x).
Proof. exact (@lem6161772 A (term167 A B s g op) x). Qed.
Lemma lem6161774 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term166 A B s g op x) = (term168 A B s g x op).
Proof. exact (eq_refl (term166 A B s g op x)). Qed.
Lemma lem6161775 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem6161776 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term169 A B GEN_PVAR_237 s g op x) = (term170 A B GEN_PVAR_237 s g x op).
Proof. exact (MK_COMB (@lem6161775 A GEN_PVAR_237) (@lem6161774 A B s g x op)). Qed.
Lemma lem6161777 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6161778 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) (x : A) : (term171 A B GEN_PVAR_237 s g op x) = (term172 A B GEN_PVAR_237 s g op x).
Proof. exact (MK_COMB (@lem6161776 A B GEN_PVAR_237 s g x op) (@lem6161777 A x)). Qed.
Lemma lem6161779 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term173 A B GEN_PVAR_237 s g op) = (term174 A B GEN_PVAR_237 s g op).
Proof. exact (fun_ext (fun x : A => @lem6161778 A B GEN_PVAR_237 s g op x)). Qed.
Lemma lem6161780 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6161781 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term175 A B GEN_PVAR_237 s g op) = (term176 A B GEN_PVAR_237 s g op).
Proof. exact (MK_COMB (@lem6161780 A) (@lem6161779 A B GEN_PVAR_237 s g op)). Qed.
Lemma lem6161782 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term177 A B s g op) = (term178 A B s g op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem6161781 A B GEN_PVAR_237 s g op)). Qed.
Lemma lem6161783 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6161784 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term179 A B s g op) = (term21 A B s g op).
Proof. exact (MK_COMB (@lem6161783 A) (@lem6161782 A B s g op)). Qed.
Lemma lem6161785 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6161786 {A B : Type'} (x : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term165 A B x s g op) = (term164 A B x s g op).
Proof. exact (MK_COMB (@lem6161785 A x) (@lem6161784 A B s g op)). Qed.
Lemma lem6161787 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6161788 {A B : Type'} (x : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term180 A B x s g op) = (term181 A B x s g op).
Proof. exact (MK_COMB (@lem6161787) (@lem6161786 A B x s g op)). Qed.
Lemma lem6161789 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term166 A B s g op x) = (term168 A B s g x op).
Proof. exact (eq_refl (term166 A B s g op x)). Qed.
Lemma lem6161790 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : ((term165 A B x s g op) = (term166 A B s g op x)) = ((term164 A B x s g op) = (term168 A B s g x op)).
Proof. exact (MK_COMB (@lem6161788 A B x s g op) (@lem6161789 A B s g x op)). Qed.
Lemma lem6161791 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term164 A B x s g op) = (term168 A B s g x op).
Proof. exact (EQ_MP (@lem6161790 A B s g x op) (@lem6161773 A B s g op x)). Qed.
Lemma lem6161796 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term163 A B x op g s) = (term168 A B s g x op).
Proof. exact (TRANS (@lem6161769 A B x s g op) (@lem6161791 A B s g x op)). Qed.
Lemma lem6161797 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term162 A B f x op g s) = (term184 A B f s g x op).
Proof. exact (MK_COMB (@lem6161755 A B s f x op) (@lem6161796 A B s g x op)). Qed.
Lemma lem6161800 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term161 A B x f op g s) = (term184 A B f s g x op).
Proof. exact (TRANS (@lem6161711 A B f x op g s) (@lem6161797 A B f s g x op)). Qed.
Lemma lem6161801 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6161802 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term192 A B x f op g s) = (term193 A B f s g x op).
Proof. exact (MK_COMB (@lem6161801) (@lem6161800 A B f s g x op)). Qed.
Lemma lem6161804 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (EQ_MP (@lem6160809 A B s f op) (@lem6160808 A B s f op)). Qed.
Lemma lem6161805 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (@lem6161804 A B s f op). Qed.
Lemma lem6161814 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6161815 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term163 A B x op f s) = (term164 A B x s f op).
Proof. exact (MK_COMB (@lem6161814 A x) (@lem6161805 A B s f op)). Qed.
Lemma lem6161817 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term15 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem6160793 _83095 p x) (@lem6160792 _83095 p x)). Qed.
Lemma lem6161818 {A : Type'} (p : A -> Prop) (x : A) : (term15 A x p) = (p x).
Proof. exact (@lem6161817 A p x). Qed.
Lemma lem6161819 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term165 A B x s f op) = (term166 A B s f op x).
Proof. exact (@lem6161818 A (term167 A B s f op) x). Qed.
Lemma lem6161820 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term166 A B s f op x) = (term168 A B s f x op).
Proof. exact (eq_refl (term166 A B s f op x)). Qed.
Lemma lem6161821 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem6161822 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term169 A B GEN_PVAR_237 s f op x) = (term170 A B GEN_PVAR_237 s f x op).
Proof. exact (MK_COMB (@lem6161821 A GEN_PVAR_237) (@lem6161820 A B s f x op)). Qed.
Lemma lem6161823 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6161824 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term171 A B GEN_PVAR_237 s f op x) = (term172 A B GEN_PVAR_237 s f op x).
Proof. exact (MK_COMB (@lem6161822 A B GEN_PVAR_237 s f x op) (@lem6161823 A x)). Qed.
Lemma lem6161825 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term173 A B GEN_PVAR_237 s f op) = (term174 A B GEN_PVAR_237 s f op).
Proof. exact (fun_ext (fun x : A => @lem6161824 A B GEN_PVAR_237 s f op x)). Qed.
Lemma lem6161826 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6161827 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term175 A B GEN_PVAR_237 s f op) = (term176 A B GEN_PVAR_237 s f op).
Proof. exact (MK_COMB (@lem6161826 A) (@lem6161825 A B GEN_PVAR_237 s f op)). Qed.
Lemma lem6161828 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term177 A B s f op) = (term178 A B s f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem6161827 A B GEN_PVAR_237 s f op)). Qed.
Lemma lem6161829 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6161830 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term179 A B s f op) = (term21 A B s f op).
Proof. exact (MK_COMB (@lem6161829 A) (@lem6161828 A B s f op)). Qed.
Lemma lem6161831 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6161832 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term165 A B x s f op) = (term164 A B x s f op).
Proof. exact (MK_COMB (@lem6161831 A x) (@lem6161830 A B s f op)). Qed.
Lemma lem6161833 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6161834 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term180 A B x s f op) = (term181 A B x s f op).
Proof. exact (MK_COMB (@lem6161833) (@lem6161832 A B x s f op)). Qed.
Lemma lem6161835 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term166 A B s f op x) = (term168 A B s f x op).
Proof. exact (eq_refl (term166 A B s f op x)). Qed.
Lemma lem6161836 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : ((term165 A B x s f op) = (term166 A B s f op x)) = ((term164 A B x s f op) = (term168 A B s f x op)).
Proof. exact (MK_COMB (@lem6161834 A B x s f op) (@lem6161835 A B s f x op)). Qed.
Lemma lem6161837 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term164 A B x s f op) = (term168 A B s f x op).
Proof. exact (EQ_MP (@lem6161836 A B s f x op) (@lem6161819 A B s f op x)). Qed.
Lemma lem6161842 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term163 A B x op f s) = (term168 A B s f x op).
Proof. exact (TRANS (@lem6161815 A B x s f op) (@lem6161837 A B s f x op)). Qed.
Lemma lem6161843 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6161844 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term219 A B x op f s) = (term220 A B s f x op).
Proof. exact (MK_COMB (@lem6161843) (@lem6161842 A B s f x op)). Qed.
Lemma lem6161845 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term221 A B g x op f s) = (term222 A B g s f x op).
Proof. exact (MK_COMB (@lem6161802 A B f s g x op) (@lem6161844 A B s f x op)). Qed.
Lemma lem6161848 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6161849 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term223 A B g x op f s) = (term224 A B g s f x op).
Proof. exact (MK_COMB (@lem6161848) (@lem6161845 A B g s f x op)). Qed.
Lemma lem6161852 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : ((f x) = (@neutral B op)) = ((f x) = (@neutral B op)).
Proof. exact (eq_refl ((f x) = (@neutral B op))). Qed.
Lemma lem6161853 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term225 A B g s f x op) = (term226 A B g s f x op).
Proof. exact (MK_COMB (@lem6161849 A B g s f x op) (@lem6161852 A B f x op)). Qed.
Lemma lem6161856 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term227 A B g s f op) = (term228 A B g s f op).
Proof. exact (fun_ext (fun x : A => @lem6161853 A B g s f x op)). Qed.
Lemma lem6161857 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6161858 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term229 A B g s f op) = (term230 A B g s f op).
Proof. exact (MK_COMB (@lem6161857 A) (@lem6161856 A B g s f op)). Qed.
Lemma lem6161863 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term231 A B g s f op) = (term232 A B g s f op).
Proof. exact (MK_COMB (@lem6161699 A B f s g op) (@lem6161858 A B g s f op)). Qed.
Lemma lem6161866 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term232 A B g s f op) = (term231 A B g s f op).
Proof. exact (SYM (@lem6161863 A B g s f op)). Qed.
Lemma lem6161870 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (EQ_MP (@lem6160762 A s t) (@lem6160761 A s t)). Qed.
Lemma lem6161871 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (@lem6161870 A s t). Qed.
Lemma lem6161872 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (s : A -> Prop) : (term233 A B f op g s) = (term234 A B f op g s).
Proof. exact (@lem6161871 A (@support A B op g s) (term91 A B f op g s)). Qed.
Lemma lem6161880 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (EQ_MP (@lem6160809 A B s f op) (@lem6160808 A B s f op)). Qed.
Lemma lem6161881 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (@lem6161880 A B s f op). Qed.
Lemma lem6161882 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) : (@support A B op g s) = (term21 A B s g op).
Proof. exact (@lem6161881 A B s g op). Qed.
Lemma lem6161891 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6161892 {A B : Type'} (x : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term163 A B x op g s) = (term164 A B x s g op).
Proof. exact (MK_COMB (@lem6161891 A x) (@lem6161882 A B s g op)). Qed.
Lemma lem6161894 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term15 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem6160793 _83095 p x) (@lem6160792 _83095 p x)). Qed.
Lemma lem6161895 {A : Type'} (p : A -> Prop) (x : A) : (term15 A x p) = (p x).
Proof. exact (@lem6161894 A p x). Qed.
Lemma lem6161896 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) (x : A) : (term165 A B x s g op) = (term166 A B s g op x).
Proof. exact (@lem6161895 A (term167 A B s g op) x). Qed.
Lemma lem6161897 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term166 A B s g op x) = (term168 A B s g x op).
Proof. exact (eq_refl (term166 A B s g op x)). Qed.
Lemma lem6161898 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem6161899 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term169 A B GEN_PVAR_237 s g op x) = (term170 A B GEN_PVAR_237 s g x op).
Proof. exact (MK_COMB (@lem6161898 A GEN_PVAR_237) (@lem6161897 A B s g x op)). Qed.
Lemma lem6161900 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6161901 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) (x : A) : (term171 A B GEN_PVAR_237 s g op x) = (term172 A B GEN_PVAR_237 s g op x).
Proof. exact (MK_COMB (@lem6161899 A B GEN_PVAR_237 s g x op) (@lem6161900 A x)). Qed.
Lemma lem6161902 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term173 A B GEN_PVAR_237 s g op) = (term174 A B GEN_PVAR_237 s g op).
Proof. exact (fun_ext (fun x : A => @lem6161901 A B GEN_PVAR_237 s g op x)). Qed.
Lemma lem6161903 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6161904 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term175 A B GEN_PVAR_237 s g op) = (term176 A B GEN_PVAR_237 s g op).
Proof. exact (MK_COMB (@lem6161903 A) (@lem6161902 A B GEN_PVAR_237 s g op)). Qed.
Lemma lem6161905 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term177 A B s g op) = (term178 A B s g op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem6161904 A B GEN_PVAR_237 s g op)). Qed.
Lemma lem6161906 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6161907 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term179 A B s g op) = (term21 A B s g op).
Proof. exact (MK_COMB (@lem6161906 A) (@lem6161905 A B s g op)). Qed.
Lemma lem6161908 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6161909 {A B : Type'} (x : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term165 A B x s g op) = (term164 A B x s g op).
Proof. exact (MK_COMB (@lem6161908 A x) (@lem6161907 A B s g op)). Qed.
Lemma lem6161910 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6161911 {A B : Type'} (x : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term180 A B x s g op) = (term181 A B x s g op).
Proof. exact (MK_COMB (@lem6161910) (@lem6161909 A B x s g op)). Qed.
Lemma lem6161912 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term166 A B s g op x) = (term168 A B s g x op).
Proof. exact (eq_refl (term166 A B s g op x)). Qed.
Lemma lem6161913 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : ((term165 A B x s g op) = (term166 A B s g op x)) = ((term164 A B x s g op) = (term168 A B s g x op)).
Proof. exact (MK_COMB (@lem6161911 A B x s g op) (@lem6161912 A B s g x op)). Qed.
Lemma lem6161914 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term164 A B x s g op) = (term168 A B s g x op).
Proof. exact (EQ_MP (@lem6161913 A B s g x op) (@lem6161896 A B s g op x)). Qed.
Lemma lem6161919 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term163 A B x op g s) = (term168 A B s g x op).
Proof. exact (TRANS (@lem6161892 A B x s g op) (@lem6161914 A B s g x op)). Qed.
Lemma lem6161920 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6161921 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term210 A B x op g s) = (term211 A B s g x op).
Proof. exact (MK_COMB (@lem6161920) (@lem6161919 A B s g x op)). Qed.
Lemma lem6161923 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term5 A x s t) = (term6 A s x t).
Proof. exact (EQ_MP (@lem6160756 A s x t) (@lem6160755 A s t x)). Qed.
Lemma lem6161924 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term5 A x s t) = (term6 A s x t).
Proof. exact (@lem6161923 A s x t). Qed.
Lemma lem6161925 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (g : A -> B) (s : A -> Prop) : (term161 A B x f op g s) = (term162 A B f x op g s).
Proof. exact (@lem6161924 A (@support A B op f s) x (@support A B op g s)). Qed.
Lemma lem6161929 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (EQ_MP (@lem6160809 A B s f op) (@lem6160808 A B s f op)). Qed.
Lemma lem6161930 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (@lem6161929 A B s f op). Qed.
Lemma lem6161939 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6161940 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term163 A B x op f s) = (term164 A B x s f op).
Proof. exact (MK_COMB (@lem6161939 A x) (@lem6161930 A B s f op)). Qed.
Lemma lem6161942 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term15 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem6160793 _83095 p x) (@lem6160792 _83095 p x)). Qed.
Lemma lem6161943 {A : Type'} (p : A -> Prop) (x : A) : (term15 A x p) = (p x).
Proof. exact (@lem6161942 A p x). Qed.
Lemma lem6161944 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term165 A B x s f op) = (term166 A B s f op x).
Proof. exact (@lem6161943 A (term167 A B s f op) x). Qed.
Lemma lem6161945 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term166 A B s f op x) = (term168 A B s f x op).
Proof. exact (eq_refl (term166 A B s f op x)). Qed.
Lemma lem6161946 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem6161947 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term169 A B GEN_PVAR_237 s f op x) = (term170 A B GEN_PVAR_237 s f x op).
Proof. exact (MK_COMB (@lem6161946 A GEN_PVAR_237) (@lem6161945 A B s f x op)). Qed.
Lemma lem6161948 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6161949 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term171 A B GEN_PVAR_237 s f op x) = (term172 A B GEN_PVAR_237 s f op x).
Proof. exact (MK_COMB (@lem6161947 A B GEN_PVAR_237 s f x op) (@lem6161948 A x)). Qed.
Lemma lem6161950 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term173 A B GEN_PVAR_237 s f op) = (term174 A B GEN_PVAR_237 s f op).
Proof. exact (fun_ext (fun x : A => @lem6161949 A B GEN_PVAR_237 s f op x)). Qed.
Lemma lem6161951 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6161952 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term175 A B GEN_PVAR_237 s f op) = (term176 A B GEN_PVAR_237 s f op).
Proof. exact (MK_COMB (@lem6161951 A) (@lem6161950 A B GEN_PVAR_237 s f op)). Qed.
Lemma lem6161953 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term177 A B s f op) = (term178 A B s f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem6161952 A B GEN_PVAR_237 s f op)). Qed.
Lemma lem6161954 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6161955 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term179 A B s f op) = (term21 A B s f op).
Proof. exact (MK_COMB (@lem6161954 A) (@lem6161953 A B s f op)). Qed.
Lemma lem6161956 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6161957 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term165 A B x s f op) = (term164 A B x s f op).
Proof. exact (MK_COMB (@lem6161956 A x) (@lem6161955 A B s f op)). Qed.
Lemma lem6161958 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6161959 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term180 A B x s f op) = (term181 A B x s f op).
Proof. exact (MK_COMB (@lem6161958) (@lem6161957 A B x s f op)). Qed.
Lemma lem6161960 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term166 A B s f op x) = (term168 A B s f x op).
Proof. exact (eq_refl (term166 A B s f op x)). Qed.
Lemma lem6161961 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : ((term165 A B x s f op) = (term166 A B s f op x)) = ((term164 A B x s f op) = (term168 A B s f x op)).
Proof. exact (MK_COMB (@lem6161959 A B x s f op) (@lem6161960 A B s f x op)). Qed.
Lemma lem6161962 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term164 A B x s f op) = (term168 A B s f x op).
Proof. exact (EQ_MP (@lem6161961 A B s f x op) (@lem6161944 A B s f op x)). Qed.
Lemma lem6161967 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term163 A B x op f s) = (term168 A B s f x op).
Proof. exact (TRANS (@lem6161940 A B x s f op) (@lem6161962 A B s f x op)). Qed.
Lemma lem6161968 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6161969 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term182 A B x op f s) = (term183 A B s f x op).
Proof. exact (MK_COMB (@lem6161968) (@lem6161967 A B s f x op)). Qed.
Lemma lem6161971 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (EQ_MP (@lem6160809 A B s f op) (@lem6160808 A B s f op)). Qed.
Lemma lem6161972 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (@lem6161971 A B s f op). Qed.
Lemma lem6161973 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) : (@support A B op g s) = (term21 A B s g op).
Proof. exact (@lem6161972 A B s g op). Qed.
Lemma lem6161982 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6161983 {A B : Type'} (x : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term163 A B x op g s) = (term164 A B x s g op).
Proof. exact (MK_COMB (@lem6161982 A x) (@lem6161973 A B s g op)). Qed.
Lemma lem6161985 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term15 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem6160793 _83095 p x) (@lem6160792 _83095 p x)). Qed.
Lemma lem6161986 {A : Type'} (p : A -> Prop) (x : A) : (term15 A x p) = (p x).
Proof. exact (@lem6161985 A p x). Qed.
Lemma lem6161987 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) (x : A) : (term165 A B x s g op) = (term166 A B s g op x).
Proof. exact (@lem6161986 A (term167 A B s g op) x). Qed.
Lemma lem6161988 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term166 A B s g op x) = (term168 A B s g x op).
Proof. exact (eq_refl (term166 A B s g op x)). Qed.
Lemma lem6161989 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem6161990 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term169 A B GEN_PVAR_237 s g op x) = (term170 A B GEN_PVAR_237 s g x op).
Proof. exact (MK_COMB (@lem6161989 A GEN_PVAR_237) (@lem6161988 A B s g x op)). Qed.
Lemma lem6161991 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6161992 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) (x : A) : (term171 A B GEN_PVAR_237 s g op x) = (term172 A B GEN_PVAR_237 s g op x).
Proof. exact (MK_COMB (@lem6161990 A B GEN_PVAR_237 s g x op) (@lem6161991 A x)). Qed.
Lemma lem6161993 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term173 A B GEN_PVAR_237 s g op) = (term174 A B GEN_PVAR_237 s g op).
Proof. exact (fun_ext (fun x : A => @lem6161992 A B GEN_PVAR_237 s g op x)). Qed.
Lemma lem6161994 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6161995 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term175 A B GEN_PVAR_237 s g op) = (term176 A B GEN_PVAR_237 s g op).
Proof. exact (MK_COMB (@lem6161994 A) (@lem6161993 A B GEN_PVAR_237 s g op)). Qed.
Lemma lem6161996 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term177 A B s g op) = (term178 A B s g op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem6161995 A B GEN_PVAR_237 s g op)). Qed.
Lemma lem6161997 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6161998 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term179 A B s g op) = (term21 A B s g op).
Proof. exact (MK_COMB (@lem6161997 A) (@lem6161996 A B s g op)). Qed.
Lemma lem6161999 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6162000 {A B : Type'} (x : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term165 A B x s g op) = (term164 A B x s g op).
Proof. exact (MK_COMB (@lem6161999 A x) (@lem6161998 A B s g op)). Qed.
Lemma lem6162001 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6162002 {A B : Type'} (x : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term180 A B x s g op) = (term181 A B x s g op).
Proof. exact (MK_COMB (@lem6162001) (@lem6162000 A B x s g op)). Qed.
Lemma lem6162003 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term166 A B s g op x) = (term168 A B s g x op).
Proof. exact (eq_refl (term166 A B s g op x)). Qed.
Lemma lem6162004 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : ((term165 A B x s g op) = (term166 A B s g op x)) = ((term164 A B x s g op) = (term168 A B s g x op)).
Proof. exact (MK_COMB (@lem6162002 A B x s g op) (@lem6162003 A B s g x op)). Qed.
Lemma lem6162005 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term164 A B x s g op) = (term168 A B s g x op).
Proof. exact (EQ_MP (@lem6162004 A B s g x op) (@lem6161987 A B s g op x)). Qed.
Lemma lem6162010 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term163 A B x op g s) = (term168 A B s g x op).
Proof. exact (TRANS (@lem6161983 A B x s g op) (@lem6162005 A B s g x op)). Qed.
Lemma lem6162011 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term162 A B f x op g s) = (term184 A B f s g x op).
Proof. exact (MK_COMB (@lem6161969 A B s f x op) (@lem6162010 A B s g x op)). Qed.
Lemma lem6162014 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term161 A B x f op g s) = (term184 A B f s g x op).
Proof. exact (TRANS (@lem6161925 A B f x op g s) (@lem6162011 A B f s g x op)). Qed.
Lemma lem6162015 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term235 A B x f op g s) = (term236 A B f s g x op).
Proof. exact (MK_COMB (@lem6161921 A B s g x op) (@lem6162014 A B f s g x op)). Qed.
Lemma lem6162018 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term237 A B f op g s) = (term238 A B f s g op).
Proof. exact (fun_ext (fun x : A => @lem6162015 A B f s g x op)). Qed.
Lemma lem6162019 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6162020 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term234 A B f op g s) = (term239 A B f s g op).
Proof. exact (MK_COMB (@lem6162019 A) (@lem6162018 A B f s g op)). Qed.
Lemma lem6162025 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term233 A B f op g s) = (term239 A B f s g op).
Proof. exact (TRANS (@lem6161872 A B f op g s) (@lem6162020 A B f s g op)). Qed.
Lemma lem6162026 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6162027 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term240 A B f op g s) = (term241 A B f s g op).
Proof. exact (MK_COMB (@lem6162026) (@lem6162025 A B f s g op)). Qed.
Lemma lem6162037 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term5 A x s t) = (term6 A s x t).
Proof. exact (EQ_MP (@lem6160756 A s x t) (@lem6160755 A s t x)). Qed.
Lemma lem6162038 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term5 A x s t) = (term6 A s x t).
Proof. exact (@lem6162037 A s x t). Qed.
Lemma lem6162039 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (g : A -> B) (s : A -> Prop) : (term161 A B x f op g s) = (term162 A B f x op g s).
Proof. exact (@lem6162038 A (@support A B op f s) x (@support A B op g s)). Qed.
Lemma lem6162043 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (EQ_MP (@lem6160809 A B s f op) (@lem6160808 A B s f op)). Qed.
Lemma lem6162044 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (@lem6162043 A B s f op). Qed.
Lemma lem6162053 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6162054 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term163 A B x op f s) = (term164 A B x s f op).
Proof. exact (MK_COMB (@lem6162053 A x) (@lem6162044 A B s f op)). Qed.
Lemma lem6162056 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term15 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem6160793 _83095 p x) (@lem6160792 _83095 p x)). Qed.
Lemma lem6162057 {A : Type'} (p : A -> Prop) (x : A) : (term15 A x p) = (p x).
Proof. exact (@lem6162056 A p x). Qed.
Lemma lem6162058 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term165 A B x s f op) = (term166 A B s f op x).
Proof. exact (@lem6162057 A (term167 A B s f op) x). Qed.
Lemma lem6162059 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term166 A B s f op x) = (term168 A B s f x op).
Proof. exact (eq_refl (term166 A B s f op x)). Qed.
Lemma lem6162060 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem6162061 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term169 A B GEN_PVAR_237 s f op x) = (term170 A B GEN_PVAR_237 s f x op).
Proof. exact (MK_COMB (@lem6162060 A GEN_PVAR_237) (@lem6162059 A B s f x op)). Qed.
Lemma lem6162062 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6162063 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term171 A B GEN_PVAR_237 s f op x) = (term172 A B GEN_PVAR_237 s f op x).
Proof. exact (MK_COMB (@lem6162061 A B GEN_PVAR_237 s f x op) (@lem6162062 A x)). Qed.
Lemma lem6162064 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term173 A B GEN_PVAR_237 s f op) = (term174 A B GEN_PVAR_237 s f op).
Proof. exact (fun_ext (fun x : A => @lem6162063 A B GEN_PVAR_237 s f op x)). Qed.
Lemma lem6162065 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6162066 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term175 A B GEN_PVAR_237 s f op) = (term176 A B GEN_PVAR_237 s f op).
Proof. exact (MK_COMB (@lem6162065 A) (@lem6162064 A B GEN_PVAR_237 s f op)). Qed.
Lemma lem6162067 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term177 A B s f op) = (term178 A B s f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem6162066 A B GEN_PVAR_237 s f op)). Qed.
Lemma lem6162068 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6162069 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term179 A B s f op) = (term21 A B s f op).
Proof. exact (MK_COMB (@lem6162068 A) (@lem6162067 A B s f op)). Qed.
Lemma lem6162070 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6162071 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term165 A B x s f op) = (term164 A B x s f op).
Proof. exact (MK_COMB (@lem6162070 A x) (@lem6162069 A B s f op)). Qed.
Lemma lem6162072 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6162073 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term180 A B x s f op) = (term181 A B x s f op).
Proof. exact (MK_COMB (@lem6162072) (@lem6162071 A B x s f op)). Qed.
Lemma lem6162074 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term166 A B s f op x) = (term168 A B s f x op).
Proof. exact (eq_refl (term166 A B s f op x)). Qed.
Lemma lem6162075 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : ((term165 A B x s f op) = (term166 A B s f op x)) = ((term164 A B x s f op) = (term168 A B s f x op)).
Proof. exact (MK_COMB (@lem6162073 A B x s f op) (@lem6162074 A B s f x op)). Qed.
Lemma lem6162076 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term164 A B x s f op) = (term168 A B s f x op).
Proof. exact (EQ_MP (@lem6162075 A B s f x op) (@lem6162058 A B s f op x)). Qed.
Lemma lem6162081 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term163 A B x op f s) = (term168 A B s f x op).
Proof. exact (TRANS (@lem6162054 A B x s f op) (@lem6162076 A B s f x op)). Qed.
Lemma lem6162082 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6162083 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term182 A B x op f s) = (term183 A B s f x op).
Proof. exact (MK_COMB (@lem6162082) (@lem6162081 A B s f x op)). Qed.
Lemma lem6162085 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (EQ_MP (@lem6160809 A B s f op) (@lem6160808 A B s f op)). Qed.
Lemma lem6162086 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (@lem6162085 A B s f op). Qed.
Lemma lem6162087 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) : (@support A B op g s) = (term21 A B s g op).
Proof. exact (@lem6162086 A B s g op). Qed.
Lemma lem6162096 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6162097 {A B : Type'} (x : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term163 A B x op g s) = (term164 A B x s g op).
Proof. exact (MK_COMB (@lem6162096 A x) (@lem6162087 A B s g op)). Qed.
Lemma lem6162099 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term15 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem6160793 _83095 p x) (@lem6160792 _83095 p x)). Qed.
Lemma lem6162100 {A : Type'} (p : A -> Prop) (x : A) : (term15 A x p) = (p x).
Proof. exact (@lem6162099 A p x). Qed.
Lemma lem6162101 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) (x : A) : (term165 A B x s g op) = (term166 A B s g op x).
Proof. exact (@lem6162100 A (term167 A B s g op) x). Qed.
Lemma lem6162102 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term166 A B s g op x) = (term168 A B s g x op).
Proof. exact (eq_refl (term166 A B s g op x)). Qed.
Lemma lem6162103 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem6162104 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term169 A B GEN_PVAR_237 s g op x) = (term170 A B GEN_PVAR_237 s g x op).
Proof. exact (MK_COMB (@lem6162103 A GEN_PVAR_237) (@lem6162102 A B s g x op)). Qed.
Lemma lem6162105 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6162106 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) (x : A) : (term171 A B GEN_PVAR_237 s g op x) = (term172 A B GEN_PVAR_237 s g op x).
Proof. exact (MK_COMB (@lem6162104 A B GEN_PVAR_237 s g x op) (@lem6162105 A x)). Qed.
Lemma lem6162107 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term173 A B GEN_PVAR_237 s g op) = (term174 A B GEN_PVAR_237 s g op).
Proof. exact (fun_ext (fun x : A => @lem6162106 A B GEN_PVAR_237 s g op x)). Qed.
Lemma lem6162108 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6162109 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term175 A B GEN_PVAR_237 s g op) = (term176 A B GEN_PVAR_237 s g op).
Proof. exact (MK_COMB (@lem6162108 A) (@lem6162107 A B GEN_PVAR_237 s g op)). Qed.
Lemma lem6162110 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term177 A B s g op) = (term178 A B s g op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem6162109 A B GEN_PVAR_237 s g op)). Qed.
Lemma lem6162111 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6162112 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term179 A B s g op) = (term21 A B s g op).
Proof. exact (MK_COMB (@lem6162111 A) (@lem6162110 A B s g op)). Qed.
Lemma lem6162113 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6162114 {A B : Type'} (x : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term165 A B x s g op) = (term164 A B x s g op).
Proof. exact (MK_COMB (@lem6162113 A x) (@lem6162112 A B s g op)). Qed.
Lemma lem6162115 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6162116 {A B : Type'} (x : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term180 A B x s g op) = (term181 A B x s g op).
Proof. exact (MK_COMB (@lem6162115) (@lem6162114 A B x s g op)). Qed.
Lemma lem6162117 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term166 A B s g op x) = (term168 A B s g x op).
Proof. exact (eq_refl (term166 A B s g op x)). Qed.
Lemma lem6162118 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : ((term165 A B x s g op) = (term166 A B s g op x)) = ((term164 A B x s g op) = (term168 A B s g x op)).
Proof. exact (MK_COMB (@lem6162116 A B x s g op) (@lem6162117 A B s g x op)). Qed.
Lemma lem6162119 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term164 A B x s g op) = (term168 A B s g x op).
Proof. exact (EQ_MP (@lem6162118 A B s g x op) (@lem6162101 A B s g op x)). Qed.
Lemma lem6162124 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term163 A B x op g s) = (term168 A B s g x op).
Proof. exact (TRANS (@lem6162097 A B x s g op) (@lem6162119 A B s g x op)). Qed.
Lemma lem6162125 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term162 A B f x op g s) = (term184 A B f s g x op).
Proof. exact (MK_COMB (@lem6162083 A B s f x op) (@lem6162124 A B s g x op)). Qed.
Lemma lem6162128 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term161 A B x f op g s) = (term184 A B f s g x op).
Proof. exact (TRANS (@lem6162039 A B f x op g s) (@lem6162125 A B f s g x op)). Qed.
Lemma lem6162129 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6162130 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term192 A B x f op g s) = (term193 A B f s g x op).
Proof. exact (MK_COMB (@lem6162129) (@lem6162128 A B f s g x op)). Qed.
Lemma lem6162132 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (EQ_MP (@lem6160809 A B s f op) (@lem6160808 A B s f op)). Qed.
Lemma lem6162133 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (@lem6162132 A B s f op). Qed.
Lemma lem6162134 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) : (@support A B op g s) = (term21 A B s g op).
Proof. exact (@lem6162133 A B s g op). Qed.
Lemma lem6162143 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6162144 {A B : Type'} (x : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term163 A B x op g s) = (term164 A B x s g op).
Proof. exact (MK_COMB (@lem6162143 A x) (@lem6162134 A B s g op)). Qed.
Lemma lem6162146 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term15 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem6160793 _83095 p x) (@lem6160792 _83095 p x)). Qed.
Lemma lem6162147 {A : Type'} (p : A -> Prop) (x : A) : (term15 A x p) = (p x).
Proof. exact (@lem6162146 A p x). Qed.
Lemma lem6162148 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) (x : A) : (term165 A B x s g op) = (term166 A B s g op x).
Proof. exact (@lem6162147 A (term167 A B s g op) x). Qed.
Lemma lem6162149 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term166 A B s g op x) = (term168 A B s g x op).
Proof. exact (eq_refl (term166 A B s g op x)). Qed.
Lemma lem6162150 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem6162151 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term169 A B GEN_PVAR_237 s g op x) = (term170 A B GEN_PVAR_237 s g x op).
Proof. exact (MK_COMB (@lem6162150 A GEN_PVAR_237) (@lem6162149 A B s g x op)). Qed.
Lemma lem6162152 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6162153 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) (x : A) : (term171 A B GEN_PVAR_237 s g op x) = (term172 A B GEN_PVAR_237 s g op x).
Proof. exact (MK_COMB (@lem6162151 A B GEN_PVAR_237 s g x op) (@lem6162152 A x)). Qed.
Lemma lem6162154 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term173 A B GEN_PVAR_237 s g op) = (term174 A B GEN_PVAR_237 s g op).
Proof. exact (fun_ext (fun x : A => @lem6162153 A B GEN_PVAR_237 s g op x)). Qed.
Lemma lem6162155 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6162156 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term175 A B GEN_PVAR_237 s g op) = (term176 A B GEN_PVAR_237 s g op).
Proof. exact (MK_COMB (@lem6162155 A) (@lem6162154 A B GEN_PVAR_237 s g op)). Qed.
Lemma lem6162157 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term177 A B s g op) = (term178 A B s g op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem6162156 A B GEN_PVAR_237 s g op)). Qed.
Lemma lem6162158 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6162159 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term179 A B s g op) = (term21 A B s g op).
Proof. exact (MK_COMB (@lem6162158 A) (@lem6162157 A B s g op)). Qed.
Lemma lem6162160 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6162161 {A B : Type'} (x : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term165 A B x s g op) = (term164 A B x s g op).
Proof. exact (MK_COMB (@lem6162160 A x) (@lem6162159 A B s g op)). Qed.
Lemma lem6162162 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6162163 {A B : Type'} (x : A) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term180 A B x s g op) = (term181 A B x s g op).
Proof. exact (MK_COMB (@lem6162162) (@lem6162161 A B x s g op)). Qed.
Lemma lem6162164 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term166 A B s g op x) = (term168 A B s g x op).
Proof. exact (eq_refl (term166 A B s g op x)). Qed.
Lemma lem6162165 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : ((term165 A B x s g op) = (term166 A B s g op x)) = ((term164 A B x s g op) = (term168 A B s g x op)).
Proof. exact (MK_COMB (@lem6162163 A B x s g op) (@lem6162164 A B s g x op)). Qed.
Lemma lem6162166 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term164 A B x s g op) = (term168 A B s g x op).
Proof. exact (EQ_MP (@lem6162165 A B s g x op) (@lem6162148 A B s g op x)). Qed.
Lemma lem6162171 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term163 A B x op g s) = (term168 A B s g x op).
Proof. exact (TRANS (@lem6162144 A B x s g op) (@lem6162166 A B s g x op)). Qed.
Lemma lem6162172 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6162173 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term219 A B x op g s) = (term220 A B s g x op).
Proof. exact (MK_COMB (@lem6162172) (@lem6162171 A B s g x op)). Qed.
Lemma lem6162174 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term242 A B f x op g s) = (term243 A B f s g x op).
Proof. exact (MK_COMB (@lem6162130 A B f s g x op) (@lem6162173 A B s g x op)). Qed.
Lemma lem6162177 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6162178 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term244 A B f x op g s) = (term245 A B f s g x op).
Proof. exact (MK_COMB (@lem6162177) (@lem6162174 A B f s g x op)). Qed.
Lemma lem6162181 {A B : Type'} (g : A -> B) (x : A) (op : type1400 B) : ((g x) = (@neutral B op)) = ((g x) = (@neutral B op)).
Proof. exact (eq_refl ((g x) = (@neutral B op))). Qed.
Lemma lem6162182 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term246 A B f s g x op) = (term247 A B f s g x op).
Proof. exact (MK_COMB (@lem6162178 A B f s g x op) (@lem6162181 A B g x op)). Qed.
Lemma lem6162185 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term248 A B f s g op) = (term249 A B f s g op).
Proof. exact (fun_ext (fun x : A => @lem6162182 A B f s g x op)). Qed.
Lemma lem6162186 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6162187 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term250 A B f s g op) = (term251 A B f s g op).
Proof. exact (MK_COMB (@lem6162186 A) (@lem6162185 A B f s g op)). Qed.
Lemma lem6162192 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term252 A B f s g op) = (term253 A B f s g op).
Proof. exact (MK_COMB (@lem6162027 A B f s g op) (@lem6162187 A B f s g op)). Qed.
Lemma lem6162195 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term253 A B f s g op) = (term252 A B f s g op).
Proof. exact (SYM (@lem6162192 A B f s g op)). Qed.
Lemma lem6162197 (p : Prop) : p = (term254 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6162198 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term207 A B s f g op) = (term255 A B s f g op).
Proof. exact (@lem6162197 (term207 A B s f g op)). Qed.
Lemma lem6162199 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term255 A B s f g op) = (term207 A B s f g op).
Proof. exact (SYM (@lem6162198 A B s f g op)). Qed.
Lemma lem6162200 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term256 A B s f g op) : term256 A B s f g op.
Proof. exact (h1). Qed.
Lemma lem6162201 {B : Type'} : term257 B.
Proof. exact (@lem5712802 B). Qed.
Lemma lem6162206 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term258 A B s f g op) : term258 A B s f g op.
Proof. exact (h1). Qed.
Lemma lem6162207 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : term259 A B s f g op.
Proof. exact (fun h0 : term258 A B s f g op => @lem6162206 A B s f g op h0). Qed.
Lemma lem6162208 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term259 A B s f g op) : term259 A B s f g op.
Proof. exact (h1). Qed.
Lemma lem6162209 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term258 A B s f g op) : term258 A B s f g op.
Proof. exact (h1). Qed.
Lemma lem6162210 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term258 A B s f g op) (h2 : term259 A B s f g op) : term258 A B s f g op.
Proof. exact (@lem6162208 A B s f g op h2 (@lem6162209 A B s f g op h1)). Qed.
Lemma lem6162211 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term258 A B s f g op) : term260 A B s f g op.
Proof. exact (fun h0 : term259 A B s f g op => @lem6162210 A B s f g op h1 h0). Qed.
Lemma lem6162212 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term259 A B s f g op) : term259 A B s f g op.
Proof. exact (h1). Qed.
Lemma lem6162213 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term258 A B s f g op) (h2 : term259 A B s f g op) : term258 A B s f g op.
Proof. exact (@lem6162211 A B s f g op h1 (@lem6162212 A B s f g op h2)). Qed.
Lemma lem6162214 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term259 A B s f g op) : term259 A B s f g op.
Proof. exact (fun h0 : term258 A B s f g op => @lem6162213 A B s f g op h0 h1). Qed.
Lemma lem6162215 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : term261 A B s f g op.
Proof. exact (fun h0 : term259 A B s f g op => @lem6162214 A B s f g op h0). Qed.
Lemma lem6162218 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : term259 A B s f g op.
Proof. exact (@lem6162215 A B s f g op (@lem6162207 A B s f g op)). Qed.
Lemma lem6162219 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : term259 A B s f g op.
Proof. exact (@lem6162218 A B s f g op). Qed.
Lemma lem6162277 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6162278 {B : Type'} : (term262 B) = (term263 B).
Proof. exact (@lem6162277 (term257 B)). Qed.
Lemma lem6162311 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term264 A B s f g op) = (term264 A B s f g op).
Proof. exact (eq_refl (term264 A B s f g op)). Qed.
Lemma lem6162312 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term265 A B s f g op) = (term266 A B s f g op).
Proof. exact (MK_COMB (@lem6162311 A B s f g op) (@lem6162278 B)). Qed.
Lemma lem6162315 {A B : Type'} (op : type1400 B) (g : A -> B) (s : A -> Prop) : (term267 A B op g s) = (term267 A B op g s).
Proof. exact (eq_refl (term267 A B op g s)). Qed.
Lemma lem6162316 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term268 A B s f g op) = (term269 A B s f g op).
Proof. exact (MK_COMB (@lem6162315 A B op g s) (@lem6162312 A B s f g op)). Qed.
Lemma lem6162319 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term267 A B op f s) = (term267 A B op f s).
Proof. exact (eq_refl (term267 A B op f s)). Qed.
Lemma lem6162320 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term270 A B s f g op) = (term271 A B s f g op).
Proof. exact (MK_COMB (@lem6162319 A B op f s) (@lem6162316 A B s f g op)). Qed.
Lemma lem6162323 {B : Type'} (op : type1400 B) : (term272 B op) = (term272 B op).
Proof. exact (eq_refl (term272 B op)). Qed.
Lemma lem6162324 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term258 A B s f g op) = (term273 A B s f g op).
Proof. exact (MK_COMB (@lem6162323 B op) (@lem6162320 A B s f g op)). Qed.
Lemma lem6162327 {A B : Type'} (f : A -> B) (g : A -> B) (op : type1400 B) : (term274 A B f g op) = (term275 A B f g op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6162324 A B s f g op)). Qed.
Lemma lem6162328 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6162329 {A B : Type'} (f : A -> B) (g : A -> B) (op : type1400 B) : (term276 A B f g op) = (term277 A B f g op).
Proof. exact (MK_COMB (@lem6162328 A) (@lem6162327 A B f g op)). Qed.
Lemma lem6162334 {A B : Type'} (g : A -> B) (op : type1400 B) : (term278 A B g op) = (term279 A B g op).
Proof. exact (fun_ext (fun f : A -> B => @lem6162329 A B f g op)). Qed.
Lemma lem6162335 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem6162336 {A B : Type'} (g : A -> B) (op : type1400 B) : (term280 A B g op) = (term281 A B g op).
Proof. exact (MK_COMB (@lem6162335 A B) (@lem6162334 A B g op)). Qed.
Lemma lem6162341 {A B : Type'} (op : type1400 B) : (term282 A B op) = (term283 A B op).
Proof. exact (fun_ext (fun g : A -> B => @lem6162336 A B g op)). Qed.
Lemma lem6162342 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem6162343 {A B : Type'} (op : type1400 B) : (term284 A B op) = (term285 A B op).
Proof. exact (MK_COMB (@lem6162342 A B) (@lem6162341 A B op)). Qed.
Lemma lem6162348 {A B : Type'} : (term286 A B) = (term287 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6162343 A B op)). Qed.
Lemma lem6162349 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6162358 {A B : Type'} : (term288 A B) = (term289 A B).
Proof. exact (MK_COMB (@lem6162349 B) (@lem6162348 A B)). Qed.
Lemma lem6162359 {B : Type'} (op : type1400 B) (x : B) : ((term290 B op x) = x) = ((term290 B op x) = x).
Proof. exact (eq_refl ((term290 B op x) = x)). Qed.
Lemma lem6162360 {B : Type'} (op : type1400 B) : (term291 B op) = (term291 B op).
Proof. exact (fun_ext (fun x : B => @lem6162359 B op x)). Qed.
Lemma lem6162361 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6162362 {B : Type'} (op : type1400 B) : (term292 B op) = (term292 B op).
Proof. exact (MK_COMB (@lem6162361 B) (@lem6162360 B op)). Qed.
Lemma lem6162363 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : ((term293 B x op y z) = (term294 B op x y z)) = ((term293 B x op y z) = (term294 B op x y z)).
Proof. exact (eq_refl ((term293 B x op y z) = (term294 B op x y z))). Qed.
Lemma lem6162364 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term295 B op x y) = (term295 B op x y).
Proof. exact (fun_ext (fun z : B => @lem6162363 B op x y z)). Qed.
Lemma lem6162365 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6162366 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term296 B op x y) = (term296 B op x y).
Proof. exact (MK_COMB (@lem6162365 B) (@lem6162364 B op x y)). Qed.
Lemma lem6162367 {B : Type'} (op : type1400 B) (x : B) : (term297 B op x) = (term297 B op x).
Proof. exact (fun_ext (fun y : B => @lem6162366 B op x y)). Qed.
Lemma lem6162368 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6162369 {B : Type'} (op : type1400 B) (x : B) : (term298 B op x) = (term298 B op x).
Proof. exact (MK_COMB (@lem6162368 B) (@lem6162367 B op x)). Qed.
Lemma lem6162370 {B : Type'} (op : type1400 B) : (term299 B op) = (term299 B op).
Proof. exact (fun_ext (fun x : B => @lem6162369 B op x)). Qed.
Lemma lem6162371 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6162372 {B : Type'} (op : type1400 B) : (term300 B op) = (term300 B op).
Proof. exact (MK_COMB (@lem6162371 B) (@lem6162370 B op)). Qed.
Lemma lem6162373 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6162374 {B : Type'} (op : type1400 B) : (term301 B op) = (term301 B op).
Proof. exact (MK_COMB (@lem6162373) (@lem6162372 B op)). Qed.
Lemma lem6162375 {B : Type'} (op : type1400 B) : (term302 B op) = (term302 B op).
Proof. exact (MK_COMB (@lem6162374 B op) (@lem6162362 B op)). Qed.
Lemma lem6162376 {B : Type'} (op : type1400 B) (y : B) (x : B) : ((op x y) = (op y x)) = ((op x y) = (op y x)).
Proof. exact (eq_refl ((op x y) = (op y x))). Qed.
Lemma lem6162377 {B : Type'} (op : type1400 B) (x : B) : (term303 B op x) = (term303 B op x).
Proof. exact (fun_ext (fun y : B => @lem6162376 B op y x)). Qed.
Lemma lem6162378 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6162379 {B : Type'} (op : type1400 B) (x : B) : (term304 B op x) = (term304 B op x).
Proof. exact (MK_COMB (@lem6162378 B) (@lem6162377 B op x)). Qed.
Lemma lem6162380 {B : Type'} (op : type1400 B) : (term305 B op) = (term305 B op).
Proof. exact (fun_ext (fun x : B => @lem6162379 B op x)). Qed.
Lemma lem6162381 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6162382 {B : Type'} (op : type1400 B) : (term306 B op) = (term306 B op).
Proof. exact (MK_COMB (@lem6162381 B) (@lem6162380 B op)). Qed.
Lemma lem6162383 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6162384 {B : Type'} (op : type1400 B) : (term307 B op) = (term307 B op).
Proof. exact (MK_COMB (@lem6162383) (@lem6162382 B op)). Qed.
Lemma lem6162385 {B : Type'} (op : type1400 B) : (term308 B op) = (term308 B op).
Proof. exact (MK_COMB (@lem6162384 B op) (@lem6162375 B op)). Qed.
Lemma lem6162388 {B : Type'} (op : type1400 B) : (term309 B op) = (term309 B op).
Proof. exact (eq_refl (term309 B op)). Qed.
Lemma lem6162389 {B : Type'} (op : type1400 B) : ((@monoidal B op) = (term308 B op)) = ((@monoidal B op) = (term308 B op)).
Proof. exact (MK_COMB (@lem6162388 B op) (@lem6162385 B op)). Qed.
Lemma lem6162390 {B : Type'} : (term310 B) = (term310 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6162389 B op)). Qed.
Lemma lem6162391 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6162392 {B : Type'} : (term257 B) = (term257 B).
Proof. exact (MK_COMB (@lem6162391 B) (@lem6162390 B)). Qed.
Lemma lem6162393 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6162394 {B : Type'} : (term263 B) = (term263 B).
Proof. exact (MK_COMB (@lem6162393) (@lem6162392 B)). Qed.
Lemma lem6162427 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term201 A B s f g x op) = (term201 A B s f g x op).
Proof. exact (eq_refl (term201 A B s f g x op)). Qed.
Lemma lem6162428 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term203 A B s f g op) = (term203 A B s f g op).
Proof. exact (fun_ext (fun x : A => @lem6162427 A B s f g x op)). Qed.
Lemma lem6162429 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6162430 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term205 A B s f g op) = (term205 A B s f g op).
Proof. exact (MK_COMB (@lem6162429 A) (@lem6162428 A B s f g op)). Qed.
Lemma lem6162457 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term186 A B f s g x op) = (term186 A B f s g x op).
Proof. exact (eq_refl (term186 A B f s g x op)). Qed.
Lemma lem6162458 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term188 A B f s g op) = (term188 A B f s g op).
Proof. exact (fun_ext (fun x : A => @lem6162457 A B f s g x op)). Qed.
Lemma lem6162459 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6162460 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term189 A B f s g op) = (term189 A B f s g op).
Proof. exact (MK_COMB (@lem6162459 A) (@lem6162458 A B f s g op)). Qed.
Lemma lem6162461 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6162462 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term191 A B f s g op) = (term191 A B f s g op).
Proof. exact (MK_COMB (@lem6162461) (@lem6162460 A B f s g op)). Qed.
Lemma lem6162463 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term207 A B s f g op) = (term207 A B s f g op).
Proof. exact (MK_COMB (@lem6162462 A B f s g op) (@lem6162430 A B s f g op)). Qed.
Lemma lem6162464 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6162465 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term256 A B s f g op) = (term256 A B s f g op).
Proof. exact (MK_COMB (@lem6162464) (@lem6162463 A B s f g op)). Qed.
Lemma lem6162466 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6162467 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term264 A B s f g op) = (term264 A B s f g op).
Proof. exact (MK_COMB (@lem6162466) (@lem6162465 A B s f g op)). Qed.
Lemma lem6162468 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term266 A B s f g op) = (term266 A B s f g op).
Proof. exact (MK_COMB (@lem6162467 A B s f g op) (@lem6162394 B)). Qed.
Lemma lem6162471 {A B : Type'} (op : type1400 B) (g : A -> B) (s : A -> Prop) : (term267 A B op g s) = (term267 A B op g s).
Proof. exact (eq_refl (term267 A B op g s)). Qed.
Lemma lem6162472 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term269 A B s f g op) = (term269 A B s f g op).
Proof. exact (MK_COMB (@lem6162471 A B op g s) (@lem6162468 A B s f g op)). Qed.
Lemma lem6162475 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term267 A B op f s) = (term267 A B op f s).
Proof. exact (eq_refl (term267 A B op f s)). Qed.
Lemma lem6162476 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term271 A B s f g op) = (term271 A B s f g op).
Proof. exact (MK_COMB (@lem6162475 A B op f s) (@lem6162472 A B s f g op)). Qed.
Lemma lem6162479 {B : Type'} (op : type1400 B) : (term272 B op) = (term272 B op).
Proof. exact (eq_refl (term272 B op)). Qed.
Lemma lem6162480 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term273 A B s f g op) = (term273 A B s f g op).
Proof. exact (MK_COMB (@lem6162479 B op) (@lem6162476 A B s f g op)). Qed.
Lemma lem6162481 {A B : Type'} (f : A -> B) (g : A -> B) (op : type1400 B) : (term275 A B f g op) = (term275 A B f g op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6162480 A B s f g op)). Qed.
Lemma lem6162482 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6162483 {A B : Type'} (f : A -> B) (g : A -> B) (op : type1400 B) : (term277 A B f g op) = (term277 A B f g op).
Proof. exact (MK_COMB (@lem6162482 A) (@lem6162481 A B f g op)). Qed.
Lemma lem6162484 {A B : Type'} (g : A -> B) (op : type1400 B) : (term279 A B g op) = (term279 A B g op).
Proof. exact (fun_ext (fun f : A -> B => @lem6162483 A B f g op)). Qed.
Lemma lem6162485 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem6162486 {A B : Type'} (g : A -> B) (op : type1400 B) : (term281 A B g op) = (term281 A B g op).
Proof. exact (MK_COMB (@lem6162485 A B) (@lem6162484 A B g op)). Qed.
Lemma lem6162487 {A B : Type'} (op : type1400 B) : (term283 A B op) = (term283 A B op).
Proof. exact (fun_ext (fun g : A -> B => @lem6162486 A B g op)). Qed.
Lemma lem6162488 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem6162489 {A B : Type'} (op : type1400 B) : (term285 A B op) = (term285 A B op).
Proof. exact (MK_COMB (@lem6162488 A B) (@lem6162487 A B op)). Qed.
Lemma lem6162490 {A B : Type'} : (term287 A B) = (term287 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6162489 A B op)). Qed.
Lemma lem6162491 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6162492 {A B : Type'} : (term289 A B) = (term289 A B).
Proof. exact (MK_COMB (@lem6162491 B) (@lem6162490 A B)). Qed.
Lemma lem6162609 {A B : Type'} : (term288 A B) = (term289 A B).
Proof. exact (TRANS (@lem6162358 A B) (@lem6162492 A B)). Qed.
Lemma lem6162610 {A B : Type'} : (term289 A B) = (term288 A B).
Proof. exact (SYM (@lem6162609 A B)). Qed.
Lemma lem6162614 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term256 A B s f g op) : term256 A B s f g op.
Proof. exact (h1). Qed.
Lemma lem6162615 {B : Type'} (h1 : term257 B) : term257 B.
Proof. exact (h1). Qed.
Lemma lem6162621 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem6162642 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term311 A B f x op) = ((f x) = (@neutral B op)).
Proof. exact (@lem16933 ((f x) = (@neutral B op))). Qed.
Lemma lem6162644 {A : Type'} (x : A) (s : A -> Prop) : (term312 A x s) = (term312 A x s).
Proof. exact (eq_refl (term312 A x s)). Qed.
Lemma lem6162645 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term313 A B s f x op) = (term314 A B s f x op).
Proof. exact (MK_COMB (@lem6162644 A x s) (@lem6162642 A B f x op)). Qed.
Lemma lem6162646 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term220 A B s f x op) = (term313 A B s f x op).
Proof. exact (@lem17045 (@IN A x s) (term315 A B f x op)). Qed.
Lemma lem6162647 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term220 A B s f x op) = (term314 A B s f x op).
Proof. exact (TRANS (@lem6162646 A B s f x op) (@lem6162645 A B s f x op)). Qed.
Lemma lem6162651 {A B : Type'} (g : A -> B) (x : A) (op : type1400 B) : (term311 A B g x op) = ((g x) = (@neutral B op)).
Proof. exact (@lem16933 ((g x) = (@neutral B op))). Qed.
Lemma lem6162653 {A : Type'} (x : A) (s : A -> Prop) : (term312 A x s) = (term312 A x s).
Proof. exact (eq_refl (term312 A x s)). Qed.
Lemma lem6162654 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term313 A B s g x op) = (term314 A B s g x op).
Proof. exact (MK_COMB (@lem6162653 A x s) (@lem6162651 A B g x op)). Qed.
Lemma lem6162655 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term220 A B s g x op) = (term313 A B s g x op).
Proof. exact (@lem17045 (@IN A x s) (term315 A B g x op)). Qed.
Lemma lem6162656 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term220 A B s g x op) = (term314 A B s g x op).
Proof. exact (TRANS (@lem6162655 A B s g x op) (@lem6162654 A B s g x op)). Qed.
Lemma lem6162657 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6162658 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term316 A B s f x op) = (term317 A B s f x op).
Proof. exact (MK_COMB (@lem6162657) (@lem6162647 A B s f x op)). Qed.
Lemma lem6162659 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term318 A B f s g x op) = (term319 A B f s g x op).
Proof. exact (MK_COMB (@lem6162658 A B s f x op) (@lem6162656 A B s g x op)). Qed.
Lemma lem6162660 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term320 A B f s g x op) = (term318 A B f s g x op).
Proof. exact (@lem17160 (term168 A B s f x op) (term168 A B s g x op)). Qed.
Lemma lem6162661 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term320 A B f s g x op) = (term319 A B f s g x op).
Proof. exact (TRANS (@lem6162660 A B f s g x op) (@lem6162659 A B f s g x op)). Qed.
Lemma lem6162663 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term321 A B s f g x op) = (term321 A B s f g x op).
Proof. exact (eq_refl (term321 A B s f g x op)). Qed.
Lemma lem6162664 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term322 A B f s g x op) = (term323 A B f s g x op).
Proof. exact (MK_COMB (@lem6162663 A B s f g x op) (@lem6162661 A B f s g x op)). Qed.
Lemma lem6162665 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term324 A B f s g x op) = (term322 A B f s g x op).
Proof. exact (@lem17362 (term134 A B s f g x op) (term184 A B f s g x op)). Qed.
Lemma lem6162666 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term324 A B f s g x op) = (term323 A B f s g x op).
Proof. exact (TRANS (@lem6162665 A B f s g x op) (@lem6162664 A B f s g x op)). Qed.
Lemma lem6162667 {A : Type'} (P : A -> Prop) : (term325 A P) = (term326 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem6162668 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term327 A B f s g op) = (term328 A B f s g op).
Proof. exact (@lem6162667 A (term188 A B f s g op)). Qed.
Lemma lem6162669 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term329 A B f s g op x) = (term186 A B f s g x op).
Proof. exact (eq_refl (term329 A B f s g op x)). Qed.
Lemma lem6162670 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6162671 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term330 A B f s g op x) = (term324 A B f s g x op).
Proof. exact (MK_COMB (@lem6162670) (@lem6162669 A B f s g x op)). Qed.
Lemma lem6162672 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term330 A B f s g op x) = (term323 A B f s g x op).
Proof. exact (TRANS (@lem6162671 A B f s g x op) (@lem6162666 A B f s g x op)). Qed.
Lemma lem6162673 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term331 A B f s g op) = (term332 A B f s g op).
Proof. exact (fun_ext (fun x : A => @lem6162672 A B f s g x op)). Qed.
Lemma lem6162674 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6162675 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term328 A B f s g op) = (term333 A B f s g op).
Proof. exact (MK_COMB (@lem6162674 A) (@lem6162673 A B f s g op)). Qed.
Lemma lem6162676 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term327 A B f s g op) = (term333 A B f s g op).
Proof. exact (TRANS (@lem6162668 A B f s g op) (@lem6162675 A B f s g op)). Qed.
Lemma lem6162693 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term334 A B f g x op) = ((term125 A B op f g x) = (@neutral B op)).
Proof. exact (@lem16933 ((term125 A B op f g x) = (@neutral B op))). Qed.
Lemma lem6162695 {A : Type'} (x : A) (s : A -> Prop) : (term312 A x s) = (term312 A x s).
Proof. exact (eq_refl (term312 A x s)). Qed.
Lemma lem6162696 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term335 A B s f g x op) = (term336 A B s f g x op).
Proof. exact (MK_COMB (@lem6162695 A x s) (@lem6162693 A B f g x op)). Qed.
Lemma lem6162697 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term195 A B s f g x op) = (term335 A B s f g x op).
Proof. exact (@lem17045 (@IN A x s) (term131 A B f g x op)). Qed.
Lemma lem6162698 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term195 A B s f g x op) = (term336 A B s f g x op).
Proof. exact (TRANS (@lem6162697 A B s f g x op) (@lem6162696 A B s f g x op)). Qed.
Lemma lem6162700 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term193 A B f s g x op) = (term193 A B f s g x op).
Proof. exact (eq_refl (term193 A B f s g x op)). Qed.
Lemma lem6162701 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term197 A B s f g x op) = (term337 A B s f g x op).
Proof. exact (MK_COMB (@lem6162700 A B f s g x op) (@lem6162698 A B s f g x op)). Qed.
Lemma lem6162702 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term131 A B f g x op) = (term131 A B f g x op).
Proof. exact (eq_refl (term131 A B f g x op)). Qed.
Lemma lem6162703 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6162704 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term338 A B s f g x op) = (term339 A B s f g x op).
Proof. exact (MK_COMB (@lem6162703) (@lem6162701 A B s f g x op)). Qed.
Lemma lem6162705 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term340 A B s f g x op) = (term341 A B s f g x op).
Proof. exact (MK_COMB (@lem6162704 A B s f g x op) (@lem6162702 A B f g x op)). Qed.
Lemma lem6162706 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term342 A B s f g x op) = (term340 A B s f g x op).
Proof. exact (@lem17362 (term197 A B s f g x op) ((term125 A B op f g x) = (@neutral B op))). Qed.
Lemma lem6162707 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term342 A B s f g x op) = (term341 A B s f g x op).
Proof. exact (TRANS (@lem6162706 A B s f g x op) (@lem6162705 A B s f g x op)). Qed.
Lemma lem6162708 {A : Type'} (P : A -> Prop) : (term325 A P) = (term326 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem6162709 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term343 A B s f g op) = (term344 A B s f g op).
Proof. exact (@lem6162708 A (term203 A B s f g op)). Qed.
Lemma lem6162710 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term345 A B s f g op x) = (term201 A B s f g x op).
Proof. exact (eq_refl (term345 A B s f g op x)). Qed.
Lemma lem6162711 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6162712 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term346 A B s f g op x) = (term342 A B s f g x op).
Proof. exact (MK_COMB (@lem6162711) (@lem6162710 A B s f g x op)). Qed.
Lemma lem6162713 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term346 A B s f g op x) = (term341 A B s f g x op).
Proof. exact (TRANS (@lem6162712 A B s f g x op) (@lem6162707 A B s f g x op)). Qed.
Lemma lem6162714 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term347 A B s f g op) = (term348 A B s f g op).
Proof. exact (fun_ext (fun x : A => @lem6162713 A B s f g x op)). Qed.
Lemma lem6162715 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6162716 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term344 A B s f g op) = (term349 A B s f g op).
Proof. exact (MK_COMB (@lem6162715 A) (@lem6162714 A B s f g op)). Qed.
Lemma lem6162717 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term343 A B s f g op) = (term349 A B s f g op).
Proof. exact (TRANS (@lem6162709 A B s f g op) (@lem6162716 A B s f g op)). Qed.
Lemma lem6162718 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6162719 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term350 A B f s g op) = (term351 A B f s g op).
Proof. exact (MK_COMB (@lem6162718) (@lem6162676 A B f s g op)). Qed.
Lemma lem6162720 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term352 A B s f g op) = (term353 A B s f g op).
Proof. exact (MK_COMB (@lem6162719 A B f s g op) (@lem6162717 A B s f g op)). Qed.
Lemma lem6162721 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term256 A B s f g op) = (term352 A B s f g op).
Proof. exact (@lem17045 (term189 A B f s g op) (term205 A B s f g op)). Qed.
Lemma lem6162722 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term256 A B s f g op) = (term353 A B s f g op).
Proof. exact (TRANS (@lem6162721 A B s f g op) (@lem6162720 A B s f g op)). Qed.
Lemma lem6162821 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term354 A P Q) = (term355 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem6162822 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term354 A P Q) = (term355 A P Q).
Proof. exact (@lem6162821 A P Q). Qed.
Lemma lem6162823 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term356 A B s f g op) = (term357 A B s f g op).
Proof. exact (@lem6162822 A (term332 A B f s g op) (term348 A B s f g op)). Qed.
Lemma lem6162824 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term358 A B f s g op x) = (term323 A B f s g x op).
Proof. exact (eq_refl (term358 A B f s g op x)). Qed.
Lemma lem6162825 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term359 A B f s g op) = (term332 A B f s g op).
Proof. exact (fun_ext (fun x : A => @lem6162824 A B f s g x op)). Qed.
Lemma lem6162826 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6162827 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term360 A B f s g op) = (term333 A B f s g op).
Proof. exact (MK_COMB (@lem6162826 A) (@lem6162825 A B f s g op)). Qed.
Lemma lem6162828 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6162829 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term361 A B f s g op) = (term351 A B f s g op).
Proof. exact (MK_COMB (@lem6162828) (@lem6162827 A B f s g op)). Qed.
Lemma lem6162830 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term362 A B s f g op x) = (term341 A B s f g x op).
Proof. exact (eq_refl (term362 A B s f g op x)). Qed.
Lemma lem6162831 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term363 A B s f g op) = (term348 A B s f g op).
Proof. exact (fun_ext (fun x : A => @lem6162830 A B s f g x op)). Qed.
Lemma lem6162832 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6162833 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term364 A B s f g op) = (term349 A B s f g op).
Proof. exact (MK_COMB (@lem6162832 A) (@lem6162831 A B s f g op)). Qed.
Lemma lem6162834 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term356 A B s f g op) = (term353 A B s f g op).
Proof. exact (MK_COMB (@lem6162829 A B f s g op) (@lem6162833 A B s f g op)). Qed.
Lemma lem6162835 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6162836 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term365 A B s f g op) = (term366 A B s f g op).
Proof. exact (MK_COMB (@lem6162835) (@lem6162834 A B s f g op)). Qed.
Lemma lem6162837 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term358 A B f s g op x) = (term323 A B f s g x op).
Proof. exact (eq_refl (term358 A B f s g op x)). Qed.
Lemma lem6162838 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6162839 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term367 A B f s g op x) = (term368 A B f s g x op).
Proof. exact (MK_COMB (@lem6162838) (@lem6162837 A B f s g x op)). Qed.
Lemma lem6162840 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term362 A B s f g op x) = (term341 A B s f g x op).
Proof. exact (eq_refl (term362 A B s f g op x)). Qed.
Lemma lem6162841 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : (term369 A B s f g op x) = (term370 A B s f g x op).
Proof. exact (MK_COMB (@lem6162839 A B f s g x op) (@lem6162840 A B s f g x op)). Qed.
Lemma lem6162842 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term371 A B s f g op) = (term372 A B s f g op).
Proof. exact (fun_ext (fun x : A => @lem6162841 A B s f g x op)). Qed.
Lemma lem6162843 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6162844 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term357 A B s f g op) = (term373 A B s f g op).
Proof. exact (MK_COMB (@lem6162843 A) (@lem6162842 A B s f g op)). Qed.
Lemma lem6162845 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : ((term356 A B s f g op) = (term357 A B s f g op)) = ((term353 A B s f g op) = (term373 A B s f g op)).
Proof. exact (MK_COMB (@lem6162836 A B s f g op) (@lem6162844 A B s f g op)). Qed.
Lemma lem6162847 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term353 A B s f g op) = (term373 A B s f g op).
Proof. exact (EQ_MP (@lem6162845 A B s f g op) (@lem6162823 A B s f g op)). Qed.
Lemma lem6162848 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term256 A B s f g op) = (term373 A B s f g op).
Proof. exact (TRANS (@lem6162722 A B s f g op) (@lem6162847 A B s f g op)). Qed.
Lemma lem6162849 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term256 A B s f g op) : term373 A B s f g op.
Proof. exact (EQ_MP (@lem6162848 A B s f g op) (@lem6162614 A B s f g op h1)). Qed.
Lemma lem6162853 {B : Type'} (op : type1400 B) (y : B) (x : B) : ((op x y) = (op y x)) = ((op x y) = (op y x)).
Proof. exact (eq_refl ((op x y) = (op y x))). Qed.
Lemma lem6162854 {B : Type'} (P : B -> Prop) : (term325 B P) = (term326 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem6162855 {B : Type'} (op : type1400 B) (x : B) : (term374 B op x) = (term375 B op x).
Proof. exact (@lem6162854 B (term303 B op x)). Qed.
Lemma lem6162856 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term376 B op x y) = ((op x y) = (op y x)).
Proof. exact (eq_refl (term376 B op x y)). Qed.
Lemma lem6162857 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6162859 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term377 B op x y) = (term378 B op y x).
Proof. exact (MK_COMB (@lem6162857) (@lem6162856 B op y x)). Qed.
Lemma lem6162860 {B : Type'} (op : type1400 B) (x : B) : (term379 B op x) = (term380 B op x).
Proof. exact (fun_ext (fun y : B => @lem6162859 B op y x)). Qed.
Lemma lem6162861 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6162862 {B : Type'} (op : type1400 B) (x : B) : (term375 B op x) = (term381 B op x).
Proof. exact (MK_COMB (@lem6162861 B) (@lem6162860 B op x)). Qed.
Lemma lem6162863 {B : Type'} (op : type1400 B) (x : B) : (term374 B op x) = (term381 B op x).
Proof. exact (TRANS (@lem6162855 B op x) (@lem6162862 B op x)). Qed.
Lemma lem6162864 {B : Type'} (op : type1400 B) (x : B) : (term303 B op x) = (term303 B op x).
Proof. exact (fun_ext (fun y : B => @lem6162853 B op y x)). Qed.
Lemma lem6162865 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6162866 {B : Type'} (op : type1400 B) (x : B) : (term304 B op x) = (term304 B op x).
Proof. exact (MK_COMB (@lem6162865 B) (@lem6162864 B op x)). Qed.
Lemma lem6162867 {B : Type'} (P : B -> Prop) : (term325 B P) = (term326 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem6162868 {B : Type'} (op : type1400 B) : (term382 B op) = (term383 B op).
Proof. exact (@lem6162867 B (term305 B op)). Qed.
Lemma lem6162869 {B : Type'} (op : type1400 B) (x : B) : (term384 B op x) = (term304 B op x).
Proof. exact (eq_refl (term384 B op x)). Qed.
Lemma lem6162870 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6162871 {B : Type'} (op : type1400 B) (x : B) : (term385 B op x) = (term374 B op x).
Proof. exact (MK_COMB (@lem6162870) (@lem6162869 B op x)). Qed.
Lemma lem6162872 {B : Type'} (op : type1400 B) (x : B) : (term385 B op x) = (term381 B op x).
Proof. exact (TRANS (@lem6162871 B op x) (@lem6162863 B op x)). Qed.
Lemma lem6162873 {B : Type'} (op : type1400 B) : (term386 B op) = (term387 B op).
Proof. exact (fun_ext (fun x : B => @lem6162872 B op x)). Qed.
Lemma lem6162874 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6162875 {B : Type'} (op : type1400 B) : (term383 B op) = (term388 B op).
Proof. exact (MK_COMB (@lem6162874 B) (@lem6162873 B op)). Qed.
Lemma lem6162876 {B : Type'} (op : type1400 B) : (term382 B op) = (term388 B op).
Proof. exact (TRANS (@lem6162868 B op) (@lem6162875 B op)). Qed.
Lemma lem6162877 {B : Type'} (op : type1400 B) : (term305 B op) = (term305 B op).
Proof. exact (fun_ext (fun x : B => @lem6162866 B op x)). Qed.
Lemma lem6162878 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6162879 {B : Type'} (op : type1400 B) : (term306 B op) = (term306 B op).
Proof. exact (MK_COMB (@lem6162878 B) (@lem6162877 B op)). Qed.
Lemma lem6162881 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : ((term293 B x op y z) = (term294 B op x y z)) = ((term293 B x op y z) = (term294 B op x y z)).
Proof. exact (eq_refl ((term293 B x op y z) = (term294 B op x y z))). Qed.
Lemma lem6162882 {B : Type'} (P : B -> Prop) : (term325 B P) = (term326 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem6162883 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term389 B op x y) = (term390 B op x y).
Proof. exact (@lem6162882 B (term295 B op x y)). Qed.
Lemma lem6162884 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term391 B op x y z) = ((term293 B x op y z) = (term294 B op x y z)).
Proof. exact (eq_refl (term391 B op x y z)). Qed.
Lemma lem6162885 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6162887 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term392 B op x y z) = (term393 B op x y z).
Proof. exact (MK_COMB (@lem6162885) (@lem6162884 B op x y z)). Qed.
Lemma lem6162888 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term394 B op x y) = (term395 B op x y).
Proof. exact (fun_ext (fun z : B => @lem6162887 B op x y z)). Qed.
Lemma lem6162889 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6162890 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term390 B op x y) = (term396 B op x y).
Proof. exact (MK_COMB (@lem6162889 B) (@lem6162888 B op x y)). Qed.
Lemma lem6162891 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term389 B op x y) = (term396 B op x y).
Proof. exact (TRANS (@lem6162883 B op x y) (@lem6162890 B op x y)). Qed.
Lemma lem6162892 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term295 B op x y) = (term295 B op x y).
Proof. exact (fun_ext (fun z : B => @lem6162881 B op x y z)). Qed.
Lemma lem6162893 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6162894 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term296 B op x y) = (term296 B op x y).
Proof. exact (MK_COMB (@lem6162893 B) (@lem6162892 B op x y)). Qed.
Lemma lem6162895 {B : Type'} (P : B -> Prop) : (term325 B P) = (term326 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem6162896 {B : Type'} (op : type1400 B) (x : B) : (term397 B op x) = (term398 B op x).
Proof. exact (@lem6162895 B (term297 B op x)). Qed.
Lemma lem6162897 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term399 B op x y) = (term296 B op x y).
Proof. exact (eq_refl (term399 B op x y)). Qed.
Lemma lem6162898 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6162899 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term400 B op x y) = (term389 B op x y).
Proof. exact (MK_COMB (@lem6162898) (@lem6162897 B op x y)). Qed.
Lemma lem6162900 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term400 B op x y) = (term396 B op x y).
Proof. exact (TRANS (@lem6162899 B op x y) (@lem6162891 B op x y)). Qed.
Lemma lem6162901 {B : Type'} (op : type1400 B) (x : B) : (term401 B op x) = (term402 B op x).
Proof. exact (fun_ext (fun y : B => @lem6162900 B op x y)). Qed.
Lemma lem6162902 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6162903 {B : Type'} (op : type1400 B) (x : B) : (term398 B op x) = (term403 B op x).
Proof. exact (MK_COMB (@lem6162902 B) (@lem6162901 B op x)). Qed.
Lemma lem6162904 {B : Type'} (op : type1400 B) (x : B) : (term397 B op x) = (term403 B op x).
Proof. exact (TRANS (@lem6162896 B op x) (@lem6162903 B op x)). Qed.
Lemma lem6162905 {B : Type'} (op : type1400 B) (x : B) : (term297 B op x) = (term297 B op x).
Proof. exact (fun_ext (fun y : B => @lem6162894 B op x y)). Qed.
Lemma lem6162906 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6162907 {B : Type'} (op : type1400 B) (x : B) : (term298 B op x) = (term298 B op x).
Proof. exact (MK_COMB (@lem6162906 B) (@lem6162905 B op x)). Qed.
Lemma lem6162908 {B : Type'} (P : B -> Prop) : (term325 B P) = (term326 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem6162909 {B : Type'} (op : type1400 B) : (term404 B op) = (term405 B op).
Proof. exact (@lem6162908 B (term299 B op)). Qed.
Lemma lem6162910 {B : Type'} (op : type1400 B) (x : B) : (term406 B op x) = (term298 B op x).
Proof. exact (eq_refl (term406 B op x)). Qed.
Lemma lem6162911 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6162912 {B : Type'} (op : type1400 B) (x : B) : (term407 B op x) = (term397 B op x).
Proof. exact (MK_COMB (@lem6162911) (@lem6162910 B op x)). Qed.
Lemma lem6162913 {B : Type'} (op : type1400 B) (x : B) : (term407 B op x) = (term403 B op x).
Proof. exact (TRANS (@lem6162912 B op x) (@lem6162904 B op x)). Qed.
Lemma lem6162914 {B : Type'} (op : type1400 B) : (term408 B op) = (term409 B op).
Proof. exact (fun_ext (fun x : B => @lem6162913 B op x)). Qed.
Lemma lem6162915 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6162916 {B : Type'} (op : type1400 B) : (term405 B op) = (term410 B op).
Proof. exact (MK_COMB (@lem6162915 B) (@lem6162914 B op)). Qed.
Lemma lem6162917 {B : Type'} (op : type1400 B) : (term404 B op) = (term410 B op).
Proof. exact (TRANS (@lem6162909 B op) (@lem6162916 B op)). Qed.
Lemma lem6162918 {B : Type'} (op : type1400 B) : (term299 B op) = (term299 B op).
Proof. exact (fun_ext (fun x : B => @lem6162907 B op x)). Qed.
Lemma lem6162919 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6162920 {B : Type'} (op : type1400 B) : (term300 B op) = (term300 B op).
Proof. exact (MK_COMB (@lem6162919 B) (@lem6162918 B op)). Qed.
Lemma lem6162922 {B : Type'} (op : type1400 B) (x : B) : ((term290 B op x) = x) = ((term290 B op x) = x).
Proof. exact (eq_refl ((term290 B op x) = x)). Qed.
Lemma lem6162923 {B : Type'} (P : B -> Prop) : (term325 B P) = (term326 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem6162924 {B : Type'} (op : type1400 B) : (term411 B op) = (term412 B op).
Proof. exact (@lem6162923 B (term291 B op)). Qed.
Lemma lem6162925 {B : Type'} (op : type1400 B) (x : B) : (term413 B op x) = ((term290 B op x) = x).
Proof. exact (eq_refl (term413 B op x)). Qed.
Lemma lem6162926 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6162928 {B : Type'} (op : type1400 B) (x : B) : (term414 B op x) = (term415 B op x).
Proof. exact (MK_COMB (@lem6162926) (@lem6162925 B op x)). Qed.
Lemma lem6162929 {B : Type'} (op : type1400 B) : (term416 B op) = (term417 B op).
Proof. exact (fun_ext (fun x : B => @lem6162928 B op x)). Qed.
Lemma lem6162930 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6162931 {B : Type'} (op : type1400 B) : (term412 B op) = (term418 B op).
Proof. exact (MK_COMB (@lem6162930 B) (@lem6162929 B op)). Qed.
Lemma lem6162932 {B : Type'} (op : type1400 B) : (term411 B op) = (term418 B op).
Proof. exact (TRANS (@lem6162924 B op) (@lem6162931 B op)). Qed.
Lemma lem6162933 {B : Type'} (op : type1400 B) : (term291 B op) = (term291 B op).
Proof. exact (fun_ext (fun x : B => @lem6162922 B op x)). Qed.
Lemma lem6162934 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6162935 {B : Type'} (op : type1400 B) : (term292 B op) = (term292 B op).
Proof. exact (MK_COMB (@lem6162934 B) (@lem6162933 B op)). Qed.
Lemma lem6162936 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6162937 {B : Type'} (op : type1400 B) : (term419 B op) = (term420 B op).
Proof. exact (MK_COMB (@lem6162936) (@lem6162917 B op)). Qed.
Lemma lem6162938 {B : Type'} (op : type1400 B) : (term421 B op) = (term422 B op).
Proof. exact (MK_COMB (@lem6162937 B op) (@lem6162932 B op)). Qed.
Lemma lem6162939 {B : Type'} (op : type1400 B) : (term423 B op) = (term421 B op).
Proof. exact (@lem17045 (term300 B op) (term292 B op)). Qed.
Lemma lem6162940 {B : Type'} (op : type1400 B) : (term423 B op) = (term422 B op).
Proof. exact (TRANS (@lem6162939 B op) (@lem6162938 B op)). Qed.
Lemma lem6162941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6162942 {B : Type'} (op : type1400 B) : (term301 B op) = (term301 B op).
Proof. exact (MK_COMB (@lem6162941) (@lem6162920 B op)). Qed.
Lemma lem6162943 {B : Type'} (op : type1400 B) : (term302 B op) = (term302 B op).
Proof. exact (MK_COMB (@lem6162942 B op) (@lem6162935 B op)). Qed.
Lemma lem6162944 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6162945 {B : Type'} (op : type1400 B) : (term424 B op) = (term425 B op).
Proof. exact (MK_COMB (@lem6162944) (@lem6162876 B op)). Qed.
Lemma lem6162946 {B : Type'} (op : type1400 B) : (term426 B op) = (term427 B op).
Proof. exact (MK_COMB (@lem6162945 B op) (@lem6162940 B op)). Qed.
Lemma lem6162947 {B : Type'} (op : type1400 B) : (term428 B op) = (term426 B op).
Proof. exact (@lem17045 (term306 B op) (term302 B op)). Qed.
Lemma lem6162948 {B : Type'} (op : type1400 B) : (term428 B op) = (term427 B op).
Proof. exact (TRANS (@lem6162947 B op) (@lem6162946 B op)). Qed.
Lemma lem6162949 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6162950 {B : Type'} (op : type1400 B) : (term307 B op) = (term307 B op).
Proof. exact (MK_COMB (@lem6162949) (@lem6162879 B op)). Qed.
Lemma lem6162951 {B : Type'} (op : type1400 B) : (term308 B op) = (term308 B op).
Proof. exact (MK_COMB (@lem6162950 B op) (@lem6162943 B op)). Qed.
Lemma lem6162953 {B : Type'} (op : type1400 B) : (term429 B op) = (term429 B op).
Proof. exact (eq_refl (term429 B op)). Qed.
Lemma lem6162954 {B : Type'} (op : type1400 B) : (term430 B op) = (term430 B op).
Proof. exact (MK_COMB (@lem6162953 B op) (@lem6162951 B op)). Qed.
Lemma lem6162956 {B : Type'} (op : type1400 B) : (term431 B op) = (term431 B op).
Proof. exact (eq_refl (term431 B op)). Qed.
Lemma lem6162957 {B : Type'} (op : type1400 B) : (term432 B op) = (term433 B op).
Proof. exact (MK_COMB (@lem6162956 B op) (@lem6162948 B op)). Qed.
Lemma lem6162958 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6162959 {B : Type'} (op : type1400 B) : (term434 B op) = (term435 B op).
Proof. exact (MK_COMB (@lem6162958) (@lem6162957 B op)). Qed.
Lemma lem6162960 {B : Type'} (op : type1400 B) : (term436 B op) = (term437 B op).
Proof. exact (MK_COMB (@lem6162959 B op) (@lem6162954 B op)). Qed.
Lemma lem6162961 {B : Type'} (op : type1400 B) : ((@monoidal B op) = (term308 B op)) = (term436 B op).
Proof. exact (@lem17784 (@monoidal B op) (term308 B op)). Qed.
Lemma lem6162962 {B : Type'} (op : type1400 B) : ((@monoidal B op) = (term308 B op)) = (term437 B op).
Proof. exact (TRANS (@lem6162961 B op) (@lem6162960 B op)). Qed.
Lemma lem6162963 {B : Type'} : (term310 B) = (term438 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6162962 B op)). Qed.
Lemma lem6162964 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6162965 {B : Type'} : (term257 B) = (term439 B).
Proof. exact (MK_COMB (@lem6162964 B) (@lem6162963 B)). Qed.
Lemma lem6162967 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term440 A P Q) = (term441 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6162968 {B : Type'} (P : type403 B) (Q : type403 B) : (term442 B P Q) = (term443 B P Q).
Proof. exact (@lem6162967 (type1400 B) P Q). Qed.
Lemma lem6162969 {B : Type'} : (term444 B) = (term445 B).
Proof. exact (@lem6162968 B (term446 B) (term447 B)). Qed.
Lemma lem6162970 {B : Type'} (op : type1400 B) : (term448 B op) = (term433 B op).
Proof. exact (eq_refl (term448 B op)). Qed.
Lemma lem6162971 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6162972 {B : Type'} (op : type1400 B) : (term449 B op) = (term435 B op).
Proof. exact (MK_COMB (@lem6162971) (@lem6162970 B op)). Qed.
Lemma lem6162973 {B : Type'} (op : type1400 B) : (term450 B op) = (term430 B op).
Proof. exact (eq_refl (term450 B op)). Qed.
Lemma lem6162974 {B : Type'} (op : type1400 B) : (term451 B op) = (term437 B op).
Proof. exact (MK_COMB (@lem6162972 B op) (@lem6162973 B op)). Qed.
Lemma lem6162975 {B : Type'} : (term452 B) = (term438 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6162974 B op)). Qed.
Lemma lem6162976 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6162977 {B : Type'} : (term444 B) = (term439 B).
Proof. exact (MK_COMB (@lem6162976 B) (@lem6162975 B)). Qed.
Lemma lem6162978 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6162979 {B : Type'} : (term453 B) = (term454 B).
Proof. exact (MK_COMB (@lem6162978) (@lem6162977 B)). Qed.
Lemma lem6162980 {B : Type'} (op : type1400 B) : (term448 B op) = (term433 B op).
Proof. exact (eq_refl (term448 B op)). Qed.
Lemma lem6162981 {B : Type'} : (term455 B) = (term446 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6162980 B op)). Qed.
Lemma lem6162982 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6162983 {B : Type'} : (term456 B) = (term457 B).
Proof. exact (MK_COMB (@lem6162982 B) (@lem6162981 B)). Qed.
Lemma lem6162984 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6162985 {B : Type'} : (term458 B) = (term459 B).
Proof. exact (MK_COMB (@lem6162984) (@lem6162983 B)). Qed.
Lemma lem6162986 {B : Type'} (op : type1400 B) : (term450 B op) = (term430 B op).
Proof. exact (eq_refl (term450 B op)). Qed.
Lemma lem6162987 {B : Type'} : (term460 B) = (term447 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6162986 B op)). Qed.
Lemma lem6162988 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6162989 {B : Type'} : (term461 B) = (term462 B).
Proof. exact (MK_COMB (@lem6162988 B) (@lem6162987 B)). Qed.
Lemma lem6162990 {B : Type'} : (term445 B) = (term463 B).
Proof. exact (MK_COMB (@lem6162985 B) (@lem6162989 B)). Qed.
Lemma lem6162991 {B : Type'} : ((term444 B) = (term445 B)) = ((term439 B) = (term463 B)).
Proof. exact (MK_COMB (@lem6162979 B) (@lem6162990 B)). Qed.
Lemma lem6162992 {B : Type'} : (term439 B) = (term463 B).
Proof. exact (EQ_MP (@lem6162991 B) (@lem6162969 B)). Qed.
Lemma lem6163118 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term354 A P Q) = (term355 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem6163119 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term354 B P Q) = (term355 B P Q).
Proof. exact (@lem6163118 B P Q). Qed.
Lemma lem6163120 {B : Type'} (op : type1400 B) : (term464 B op) = (term465 B op).
Proof. exact (@lem6163119 B (term409 B op) (term417 B op)). Qed.
Lemma lem6163121 {B : Type'} (op : type1400 B) (x : B) : (term466 B op x) = (term403 B op x).
Proof. exact (eq_refl (term466 B op x)). Qed.
Lemma lem6163122 {B : Type'} (op : type1400 B) : (term467 B op) = (term409 B op).
Proof. exact (fun_ext (fun x : B => @lem6163121 B op x)). Qed.
Lemma lem6163123 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6163124 {B : Type'} (op : type1400 B) : (term468 B op) = (term410 B op).
Proof. exact (MK_COMB (@lem6163123 B) (@lem6163122 B op)). Qed.
Lemma lem6163125 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6163126 {B : Type'} (op : type1400 B) : (term469 B op) = (term420 B op).
Proof. exact (MK_COMB (@lem6163125) (@lem6163124 B op)). Qed.
Lemma lem6163127 {B : Type'} (op : type1400 B) (x : B) : (term470 B op x) = (term415 B op x).
Proof. exact (eq_refl (term470 B op x)). Qed.
Lemma lem6163128 {B : Type'} (op : type1400 B) : (term471 B op) = (term417 B op).
Proof. exact (fun_ext (fun x : B => @lem6163127 B op x)). Qed.
Lemma lem6163129 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6163130 {B : Type'} (op : type1400 B) : (term472 B op) = (term418 B op).
Proof. exact (MK_COMB (@lem6163129 B) (@lem6163128 B op)). Qed.
Lemma lem6163131 {B : Type'} (op : type1400 B) : (term464 B op) = (term422 B op).
Proof. exact (MK_COMB (@lem6163126 B op) (@lem6163130 B op)). Qed.
Lemma lem6163132 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6163133 {B : Type'} (op : type1400 B) : (term473 B op) = (term474 B op).
Proof. exact (MK_COMB (@lem6163132) (@lem6163131 B op)). Qed.
Lemma lem6163134 {B : Type'} (op : type1400 B) (x : B) : (term466 B op x) = (term403 B op x).
Proof. exact (eq_refl (term466 B op x)). Qed.
Lemma lem6163135 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6163136 {B : Type'} (op : type1400 B) (x : B) : (term475 B op x) = (term476 B op x).
Proof. exact (MK_COMB (@lem6163135) (@lem6163134 B op x)). Qed.
Lemma lem6163137 {B : Type'} (op : type1400 B) (x : B) : (term470 B op x) = (term415 B op x).
Proof. exact (eq_refl (term470 B op x)). Qed.
Lemma lem6163138 {B : Type'} (op : type1400 B) (x : B) : (term477 B op x) = (term478 B op x).
Proof. exact (MK_COMB (@lem6163136 B op x) (@lem6163137 B op x)). Qed.
Lemma lem6163139 {B : Type'} (op : type1400 B) : (term479 B op) = (term480 B op).
Proof. exact (fun_ext (fun x : B => @lem6163138 B op x)). Qed.
Lemma lem6163140 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6163141 {B : Type'} (op : type1400 B) : (term465 B op) = (term481 B op).
Proof. exact (MK_COMB (@lem6163140 B) (@lem6163139 B op)). Qed.
Lemma lem6163142 {B : Type'} (op : type1400 B) : ((term464 B op) = (term465 B op)) = ((term422 B op) = (term481 B op)).
Proof. exact (MK_COMB (@lem6163133 B op) (@lem6163141 B op)). Qed.
Lemma lem6163143 {B : Type'} (op : type1400 B) : (term422 B op) = (term481 B op).
Proof. exact (EQ_MP (@lem6163142 B op) (@lem6163120 B op)). Qed.
Lemma lem6163145 {A : Type'} (P : A -> Prop) (Q : Prop) : (term482 A P Q) = (term483 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6163146 {B : Type'} (P : B -> Prop) (Q : Prop) : (term482 B P Q) = (term483 B P Q).
Proof. exact (@lem6163145 B P Q). Qed.
Lemma lem6163147 {B : Type'} (op : type1400 B) (x : B) : (term484 B op x) = (term485 B op x).
Proof. exact (@lem6163146 B (term402 B op x) (term415 B op x)). Qed.
Lemma lem6163148 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term486 B op x y) = (term396 B op x y).
Proof. exact (eq_refl (term486 B op x y)). Qed.
Lemma lem6163149 {B : Type'} (op : type1400 B) (x : B) : (term487 B op x) = (term402 B op x).
Proof. exact (fun_ext (fun y : B => @lem6163148 B op x y)). Qed.
Lemma lem6163150 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6163151 {B : Type'} (op : type1400 B) (x : B) : (term488 B op x) = (term403 B op x).
Proof. exact (MK_COMB (@lem6163150 B) (@lem6163149 B op x)). Qed.
Lemma lem6163152 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6163153 {B : Type'} (op : type1400 B) (x : B) : (term489 B op x) = (term476 B op x).
Proof. exact (MK_COMB (@lem6163152) (@lem6163151 B op x)). Qed.
Lemma lem6163154 {B : Type'} (op : type1400 B) (x : B) : (term415 B op x) = (term415 B op x).
Proof. exact (eq_refl (term415 B op x)). Qed.
Lemma lem6163155 {B : Type'} (op : type1400 B) (x : B) : (term484 B op x) = (term478 B op x).
Proof. exact (MK_COMB (@lem6163153 B op x) (@lem6163154 B op x)). Qed.
Lemma lem6163156 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6163157 {B : Type'} (op : type1400 B) (x : B) : (term490 B op x) = (term491 B op x).
Proof. exact (MK_COMB (@lem6163156) (@lem6163155 B op x)). Qed.
Lemma lem6163158 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term486 B op x y) = (term396 B op x y).
Proof. exact (eq_refl (term486 B op x y)). Qed.
Lemma lem6163159 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6163160 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term492 B op x y) = (term493 B op x y).
Proof. exact (MK_COMB (@lem6163159) (@lem6163158 B op x y)). Qed.
Lemma lem6163161 {B : Type'} (op : type1400 B) (x : B) : (term415 B op x) = (term415 B op x).
Proof. exact (eq_refl (term415 B op x)). Qed.
Lemma lem6163162 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term494 B y op x) = (term495 B y op x).
Proof. exact (MK_COMB (@lem6163160 B op x y) (@lem6163161 B op x)). Qed.
Lemma lem6163163 {B : Type'} (op : type1400 B) (x : B) : (term496 B op x) = (term497 B op x).
Proof. exact (fun_ext (fun y : B => @lem6163162 B y op x)). Qed.
Lemma lem6163164 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6163165 {B : Type'} (op : type1400 B) (x : B) : (term485 B op x) = (term498 B op x).
Proof. exact (MK_COMB (@lem6163164 B) (@lem6163163 B op x)). Qed.
Lemma lem6163166 {B : Type'} (op : type1400 B) (x : B) : ((term484 B op x) = (term485 B op x)) = ((term478 B op x) = (term498 B op x)).
Proof. exact (MK_COMB (@lem6163157 B op x) (@lem6163165 B op x)). Qed.
Lemma lem6163167 {B : Type'} (op : type1400 B) (x : B) : (term478 B op x) = (term498 B op x).
Proof. exact (EQ_MP (@lem6163166 B op x) (@lem6163147 B op x)). Qed.
Lemma lem6163169 {A : Type'} (P : A -> Prop) (Q : Prop) : (term482 A P Q) = (term483 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6163170 {B : Type'} (P : B -> Prop) (Q : Prop) : (term482 B P Q) = (term483 B P Q).
Proof. exact (@lem6163169 B P Q). Qed.
Lemma lem6163171 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term499 B y op x) = (term500 B y op x).
Proof. exact (@lem6163170 B (term395 B op x y) (term415 B op x)). Qed.
Lemma lem6163172 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term501 B op x y z) = (term393 B op x y z).
Proof. exact (eq_refl (term501 B op x y z)). Qed.
Lemma lem6163173 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term502 B op x y) = (term395 B op x y).
Proof. exact (fun_ext (fun z : B => @lem6163172 B op x y z)). Qed.
Lemma lem6163174 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6163175 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term503 B op x y) = (term396 B op x y).
Proof. exact (MK_COMB (@lem6163174 B) (@lem6163173 B op x y)). Qed.
Lemma lem6163176 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6163177 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term504 B op x y) = (term493 B op x y).
Proof. exact (MK_COMB (@lem6163176) (@lem6163175 B op x y)). Qed.
Lemma lem6163178 {B : Type'} (op : type1400 B) (x : B) : (term415 B op x) = (term415 B op x).
Proof. exact (eq_refl (term415 B op x)). Qed.
Lemma lem6163179 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term499 B y op x) = (term495 B y op x).
Proof. exact (MK_COMB (@lem6163177 B op x y) (@lem6163178 B op x)). Qed.
Lemma lem6163180 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6163181 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term505 B y op x) = (term506 B y op x).
Proof. exact (MK_COMB (@lem6163180) (@lem6163179 B y op x)). Qed.
Lemma lem6163182 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term501 B op x y z) = (term393 B op x y z).
Proof. exact (eq_refl (term501 B op x y z)). Qed.
Lemma lem6163183 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6163184 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term507 B op x y z) = (term508 B op x y z).
Proof. exact (MK_COMB (@lem6163183) (@lem6163182 B op x y z)). Qed.
Lemma lem6163185 {B : Type'} (op : type1400 B) (x : B) : (term415 B op x) = (term415 B op x).
Proof. exact (eq_refl (term415 B op x)). Qed.
Lemma lem6163186 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term509 B y z op x) = (term510 B y z op x).
Proof. exact (MK_COMB (@lem6163184 B op x y z) (@lem6163185 B op x)). Qed.
Lemma lem6163187 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term511 B y op x) = (term512 B y op x).
Proof. exact (fun_ext (fun z : B => @lem6163186 B y z op x)). Qed.
Lemma lem6163188 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6163189 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term500 B y op x) = (term513 B y op x).
Proof. exact (MK_COMB (@lem6163188 B) (@lem6163187 B y op x)). Qed.
Lemma lem6163190 {B : Type'} (y : B) (op : type1400 B) (x : B) : ((term499 B y op x) = (term500 B y op x)) = ((term495 B y op x) = (term513 B y op x)).
Proof. exact (MK_COMB (@lem6163181 B y op x) (@lem6163189 B y op x)). Qed.
Lemma lem6163191 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term495 B y op x) = (term513 B y op x).
Proof. exact (EQ_MP (@lem6163190 B y op x) (@lem6163171 B y op x)). Qed.
Lemma lem6163192 {B : Type'} (op : type1400 B) (x : B) : (term497 B op x) = (term514 B op x).
Proof. exact (fun_ext (fun y : B => @lem6163191 B y op x)). Qed.
Lemma lem6163193 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6163194 {B : Type'} (op : type1400 B) (x : B) : (term498 B op x) = (term515 B op x).
Proof. exact (MK_COMB (@lem6163193 B) (@lem6163192 B op x)). Qed.
Lemma lem6163195 {B : Type'} (op : type1400 B) (x : B) : (term478 B op x) = (term515 B op x).
Proof. exact (TRANS (@lem6163167 B op x) (@lem6163194 B op x)). Qed.
Lemma lem6163196 {B : Type'} (op : type1400 B) : (term480 B op) = (term516 B op).
Proof. exact (fun_ext (fun x : B => @lem6163195 B op x)). Qed.
Lemma lem6163197 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6163198 {B : Type'} (op : type1400 B) : (term481 B op) = (term517 B op).
Proof. exact (MK_COMB (@lem6163197 B) (@lem6163196 B op)). Qed.
Lemma lem6163199 {B : Type'} (op : type1400 B) : (term422 B op) = (term517 B op).
Proof. exact (TRANS (@lem6163143 B op) (@lem6163198 B op)). Qed.
Lemma lem6163200 {B : Type'} (op : type1400 B) : (term425 B op) = (term425 B op).
Proof. exact (eq_refl (term425 B op)). Qed.
Lemma lem6163201 {B : Type'} (op : type1400 B) : (term427 B op) = (term518 B op).
Proof. exact (MK_COMB (@lem6163200 B op) (@lem6163199 B op)). Qed.
Lemma lem6163203 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term354 A P Q) = (term355 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem6163204 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term354 B P Q) = (term355 B P Q).
Proof. exact (@lem6163203 B P Q). Qed.
Lemma lem6163205 {B : Type'} (op : type1400 B) : (term519 B op) = (term520 B op).
Proof. exact (@lem6163204 B (term387 B op) (term516 B op)). Qed.
Lemma lem6163206 {B : Type'} (op : type1400 B) (x : B) : (term521 B op x) = (term381 B op x).
Proof. exact (eq_refl (term521 B op x)). Qed.
Lemma lem6163207 {B : Type'} (op : type1400 B) : (term522 B op) = (term387 B op).
Proof. exact (fun_ext (fun x : B => @lem6163206 B op x)). Qed.
Lemma lem6163208 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6163209 {B : Type'} (op : type1400 B) : (term523 B op) = (term388 B op).
Proof. exact (MK_COMB (@lem6163208 B) (@lem6163207 B op)). Qed.
Lemma lem6163210 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6163211 {B : Type'} (op : type1400 B) : (term524 B op) = (term425 B op).
Proof. exact (MK_COMB (@lem6163210) (@lem6163209 B op)). Qed.
Lemma lem6163212 {B : Type'} (op : type1400 B) (x : B) : (term525 B op x) = (term515 B op x).
Proof. exact (eq_refl (term525 B op x)). Qed.
Lemma lem6163213 {B : Type'} (op : type1400 B) : (term526 B op) = (term516 B op).
Proof. exact (fun_ext (fun x : B => @lem6163212 B op x)). Qed.
Lemma lem6163214 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6163215 {B : Type'} (op : type1400 B) : (term527 B op) = (term517 B op).
Proof. exact (MK_COMB (@lem6163214 B) (@lem6163213 B op)). Qed.
Lemma lem6163216 {B : Type'} (op : type1400 B) : (term519 B op) = (term518 B op).
Proof. exact (MK_COMB (@lem6163211 B op) (@lem6163215 B op)). Qed.
Lemma lem6163217 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6163218 {B : Type'} (op : type1400 B) : (term528 B op) = (term529 B op).
Proof. exact (MK_COMB (@lem6163217) (@lem6163216 B op)). Qed.
Lemma lem6163219 {B : Type'} (op : type1400 B) (x : B) : (term521 B op x) = (term381 B op x).
Proof. exact (eq_refl (term521 B op x)). Qed.
Lemma lem6163220 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6163221 {B : Type'} (op : type1400 B) (x : B) : (term530 B op x) = (term531 B op x).
Proof. exact (MK_COMB (@lem6163220) (@lem6163219 B op x)). Qed.
Lemma lem6163222 {B : Type'} (op : type1400 B) (x : B) : (term525 B op x) = (term515 B op x).
Proof. exact (eq_refl (term525 B op x)). Qed.
Lemma lem6163223 {B : Type'} (op : type1400 B) (x : B) : (term532 B op x) = (term533 B op x).
Proof. exact (MK_COMB (@lem6163221 B op x) (@lem6163222 B op x)). Qed.
Lemma lem6163224 {B : Type'} (op : type1400 B) : (term534 B op) = (term535 B op).
Proof. exact (fun_ext (fun x : B => @lem6163223 B op x)). Qed.
Lemma lem6163225 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6163226 {B : Type'} (op : type1400 B) : (term520 B op) = (term536 B op).
Proof. exact (MK_COMB (@lem6163225 B) (@lem6163224 B op)). Qed.
Lemma lem6163227 {B : Type'} (op : type1400 B) : ((term519 B op) = (term520 B op)) = ((term518 B op) = (term536 B op)).
Proof. exact (MK_COMB (@lem6163218 B op) (@lem6163226 B op)). Qed.
Lemma lem6163228 {B : Type'} (op : type1400 B) : (term518 B op) = (term536 B op).
Proof. exact (EQ_MP (@lem6163227 B op) (@lem6163205 B op)). Qed.
Lemma lem6163230 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term354 A P Q) = (term355 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem6163231 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term354 B P Q) = (term355 B P Q).
Proof. exact (@lem6163230 B P Q). Qed.
Lemma lem6163232 {B : Type'} (op : type1400 B) (x : B) : (term537 B op x) = (term538 B op x).
Proof. exact (@lem6163231 B (term380 B op x) (term514 B op x)). Qed.
Lemma lem6163233 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term539 B op x y) = (term378 B op y x).
Proof. exact (eq_refl (term539 B op x y)). Qed.
Lemma lem6163234 {B : Type'} (op : type1400 B) (x : B) : (term540 B op x) = (term380 B op x).
Proof. exact (fun_ext (fun y : B => @lem6163233 B op y x)). Qed.
Lemma lem6163235 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6163236 {B : Type'} (op : type1400 B) (x : B) : (term541 B op x) = (term381 B op x).
Proof. exact (MK_COMB (@lem6163235 B) (@lem6163234 B op x)). Qed.
Lemma lem6163237 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6163238 {B : Type'} (op : type1400 B) (x : B) : (term542 B op x) = (term531 B op x).
Proof. exact (MK_COMB (@lem6163237) (@lem6163236 B op x)). Qed.
Lemma lem6163239 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term543 B op x y) = (term513 B y op x).
Proof. exact (eq_refl (term543 B op x y)). Qed.
Lemma lem6163240 {B : Type'} (op : type1400 B) (x : B) : (term544 B op x) = (term514 B op x).
Proof. exact (fun_ext (fun y : B => @lem6163239 B y op x)). Qed.
Lemma lem6163241 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6163242 {B : Type'} (op : type1400 B) (x : B) : (term545 B op x) = (term515 B op x).
Proof. exact (MK_COMB (@lem6163241 B) (@lem6163240 B op x)). Qed.
Lemma lem6163243 {B : Type'} (op : type1400 B) (x : B) : (term537 B op x) = (term533 B op x).
Proof. exact (MK_COMB (@lem6163238 B op x) (@lem6163242 B op x)). Qed.
Lemma lem6163244 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6163245 {B : Type'} (op : type1400 B) (x : B) : (term546 B op x) = (term547 B op x).
Proof. exact (MK_COMB (@lem6163244) (@lem6163243 B op x)). Qed.
Lemma lem6163246 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term539 B op x y) = (term378 B op y x).
Proof. exact (eq_refl (term539 B op x y)). Qed.
Lemma lem6163247 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6163248 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term548 B op x y) = (term549 B op y x).
Proof. exact (MK_COMB (@lem6163247) (@lem6163246 B op y x)). Qed.
Lemma lem6163249 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term543 B op x y) = (term513 B y op x).
Proof. exact (eq_refl (term543 B op x y)). Qed.
Lemma lem6163250 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term550 B op x y) = (term551 B y op x).
Proof. exact (MK_COMB (@lem6163248 B op y x) (@lem6163249 B y op x)). Qed.
Lemma lem6163251 {B : Type'} (op : type1400 B) (x : B) : (term552 B op x) = (term553 B op x).
Proof. exact (fun_ext (fun y : B => @lem6163250 B y op x)). Qed.
Lemma lem6163252 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6163253 {B : Type'} (op : type1400 B) (x : B) : (term538 B op x) = (term554 B op x).
Proof. exact (MK_COMB (@lem6163252 B) (@lem6163251 B op x)). Qed.
Lemma lem6163254 {B : Type'} (op : type1400 B) (x : B) : ((term537 B op x) = (term538 B op x)) = ((term533 B op x) = (term554 B op x)).
Proof. exact (MK_COMB (@lem6163245 B op x) (@lem6163253 B op x)). Qed.
Lemma lem6163255 {B : Type'} (op : type1400 B) (x : B) : (term533 B op x) = (term554 B op x).
Proof. exact (EQ_MP (@lem6163254 B op x) (@lem6163232 B op x)). Qed.
Lemma lem6163257 {A : Type'} (P : Prop) (Q : A -> Prop) : (term555 A P Q) = (term556 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6163258 {B : Type'} (P : Prop) (Q : B -> Prop) : (term555 B P Q) = (term556 B P Q).
Proof. exact (@lem6163257 B P Q). Qed.
Lemma lem6163259 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term557 B y op x) = (term558 B y op x).
Proof. exact (@lem6163258 B (term378 B op y x) (term512 B y op x)). Qed.
Lemma lem6163260 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term559 B y op x z) = (term510 B y z op x).
Proof. exact (eq_refl (term559 B y op x z)). Qed.
Lemma lem6163261 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term560 B y op x) = (term512 B y op x).
Proof. exact (fun_ext (fun z : B => @lem6163260 B y z op x)). Qed.
Lemma lem6163262 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6163263 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term561 B y op x) = (term513 B y op x).
Proof. exact (MK_COMB (@lem6163262 B) (@lem6163261 B y op x)). Qed.
Lemma lem6163264 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term549 B op y x) = (term549 B op y x).
Proof. exact (eq_refl (term549 B op y x)). Qed.
Lemma lem6163265 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term557 B y op x) = (term551 B y op x).
Proof. exact (MK_COMB (@lem6163264 B op y x) (@lem6163263 B y op x)). Qed.
Lemma lem6163266 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6163267 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term562 B y op x) = (term563 B y op x).
Proof. exact (MK_COMB (@lem6163266) (@lem6163265 B y op x)). Qed.
Lemma lem6163268 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term559 B y op x z) = (term510 B y z op x).
Proof. exact (eq_refl (term559 B y op x z)). Qed.
Lemma lem6163269 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term549 B op y x) = (term549 B op y x).
Proof. exact (eq_refl (term549 B op y x)). Qed.
Lemma lem6163270 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term564 B y op x z) = (term565 B y z op x).
Proof. exact (MK_COMB (@lem6163269 B op y x) (@lem6163268 B y z op x)). Qed.
Lemma lem6163271 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term566 B y op x) = (term567 B y op x).
Proof. exact (fun_ext (fun z : B => @lem6163270 B y z op x)). Qed.
Lemma lem6163272 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6163273 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term558 B y op x) = (term568 B y op x).
Proof. exact (MK_COMB (@lem6163272 B) (@lem6163271 B y op x)). Qed.
Lemma lem6163274 {B : Type'} (y : B) (op : type1400 B) (x : B) : ((term557 B y op x) = (term558 B y op x)) = ((term551 B y op x) = (term568 B y op x)).
Proof. exact (MK_COMB (@lem6163267 B y op x) (@lem6163273 B y op x)). Qed.
Lemma lem6163275 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term551 B y op x) = (term568 B y op x).
Proof. exact (EQ_MP (@lem6163274 B y op x) (@lem6163259 B y op x)). Qed.
Lemma lem6163276 {B : Type'} (op : type1400 B) (x : B) : (term553 B op x) = (term569 B op x).
Proof. exact (fun_ext (fun y : B => @lem6163275 B y op x)). Qed.
Lemma lem6163277 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6163278 {B : Type'} (op : type1400 B) (x : B) : (term554 B op x) = (term570 B op x).
Proof. exact (MK_COMB (@lem6163277 B) (@lem6163276 B op x)). Qed.
Lemma lem6163279 {B : Type'} (op : type1400 B) (x : B) : (term533 B op x) = (term570 B op x).
Proof. exact (TRANS (@lem6163255 B op x) (@lem6163278 B op x)). Qed.
Lemma lem6163280 {B : Type'} (op : type1400 B) : (term535 B op) = (term571 B op).
Proof. exact (fun_ext (fun x : B => @lem6163279 B op x)). Qed.
Lemma lem6163281 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6163282 {B : Type'} (op : type1400 B) : (term536 B op) = (term572 B op).
Proof. exact (MK_COMB (@lem6163281 B) (@lem6163280 B op)). Qed.
Lemma lem6163283 {B : Type'} (op : type1400 B) : (term518 B op) = (term572 B op).
Proof. exact (TRANS (@lem6163228 B op) (@lem6163282 B op)). Qed.
Lemma lem6163284 {B : Type'} (op : type1400 B) : (term427 B op) = (term572 B op).
Proof. exact (TRANS (@lem6163201 B op) (@lem6163283 B op)). Qed.
Lemma lem6163285 {B : Type'} (op : type1400 B) : (term431 B op) = (term431 B op).
Proof. exact (eq_refl (term431 B op)). Qed.
Lemma lem6163286 {B : Type'} (op : type1400 B) : (term433 B op) = (term573 B op).
Proof. exact (MK_COMB (@lem6163285 B op) (@lem6163284 B op)). Qed.
Lemma lem6163288 {A : Type'} (P : Prop) (Q : A -> Prop) : (term555 A P Q) = (term556 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6163289 {B : Type'} (P : Prop) (Q : B -> Prop) : (term555 B P Q) = (term556 B P Q).
Proof. exact (@lem6163288 B P Q). Qed.
Lemma lem6163290 {B : Type'} (op : type1400 B) : (term574 B op) = (term575 B op).
Proof. exact (@lem6163289 B (@monoidal B op) (term571 B op)). Qed.
Lemma lem6163291 {B : Type'} (op : type1400 B) (x : B) : (term576 B op x) = (term570 B op x).
Proof. exact (eq_refl (term576 B op x)). Qed.
Lemma lem6163292 {B : Type'} (op : type1400 B) : (term577 B op) = (term571 B op).
Proof. exact (fun_ext (fun x : B => @lem6163291 B op x)). Qed.
Lemma lem6163293 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6163294 {B : Type'} (op : type1400 B) : (term578 B op) = (term572 B op).
Proof. exact (MK_COMB (@lem6163293 B) (@lem6163292 B op)). Qed.
Lemma lem6163295 {B : Type'} (op : type1400 B) : (term431 B op) = (term431 B op).
Proof. exact (eq_refl (term431 B op)). Qed.
Lemma lem6163296 {B : Type'} (op : type1400 B) : (term574 B op) = (term573 B op).
Proof. exact (MK_COMB (@lem6163295 B op) (@lem6163294 B op)). Qed.
Lemma lem6163297 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6163298 {B : Type'} (op : type1400 B) : (term579 B op) = (term580 B op).
Proof. exact (MK_COMB (@lem6163297) (@lem6163296 B op)). Qed.
Lemma lem6163299 {B : Type'} (op : type1400 B) (x : B) : (term576 B op x) = (term570 B op x).
Proof. exact (eq_refl (term576 B op x)). Qed.
Lemma lem6163300 {B : Type'} (op : type1400 B) : (term431 B op) = (term431 B op).
Proof. exact (eq_refl (term431 B op)). Qed.
Lemma lem6163301 {B : Type'} (op : type1400 B) (x : B) : (term581 B op x) = (term582 B op x).
Proof. exact (MK_COMB (@lem6163300 B op) (@lem6163299 B op x)). Qed.
Lemma lem6163302 {B : Type'} (op : type1400 B) : (term583 B op) = (term584 B op).
Proof. exact (fun_ext (fun x : B => @lem6163301 B op x)). Qed.
Lemma lem6163303 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6163304 {B : Type'} (op : type1400 B) : (term575 B op) = (term585 B op).
Proof. exact (MK_COMB (@lem6163303 B) (@lem6163302 B op)). Qed.
Lemma lem6163305 {B : Type'} (op : type1400 B) : ((term574 B op) = (term575 B op)) = ((term573 B op) = (term585 B op)).
Proof. exact (MK_COMB (@lem6163298 B op) (@lem6163304 B op)). Qed.
Lemma lem6163306 {B : Type'} (op : type1400 B) : (term573 B op) = (term585 B op).
Proof. exact (EQ_MP (@lem6163305 B op) (@lem6163290 B op)). Qed.
Lemma lem6163308 {A : Type'} (P : Prop) (Q : A -> Prop) : (term555 A P Q) = (term556 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6163309 {B : Type'} (P : Prop) (Q : B -> Prop) : (term555 B P Q) = (term556 B P Q).
Proof. exact (@lem6163308 B P Q). Qed.
Lemma lem6163310 {B : Type'} (op : type1400 B) (x : B) : (term586 B op x) = (term587 B op x).
Proof. exact (@lem6163309 B (@monoidal B op) (term569 B op x)). Qed.
Lemma lem6163311 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term588 B op x y) = (term568 B y op x).
Proof. exact (eq_refl (term588 B op x y)). Qed.
Lemma lem6163312 {B : Type'} (op : type1400 B) (x : B) : (term589 B op x) = (term569 B op x).
Proof. exact (fun_ext (fun y : B => @lem6163311 B y op x)). Qed.
Lemma lem6163313 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6163314 {B : Type'} (op : type1400 B) (x : B) : (term590 B op x) = (term570 B op x).
Proof. exact (MK_COMB (@lem6163313 B) (@lem6163312 B op x)). Qed.
Lemma lem6163315 {B : Type'} (op : type1400 B) : (term431 B op) = (term431 B op).
Proof. exact (eq_refl (term431 B op)). Qed.
Lemma lem6163316 {B : Type'} (op : type1400 B) (x : B) : (term586 B op x) = (term582 B op x).
Proof. exact (MK_COMB (@lem6163315 B op) (@lem6163314 B op x)). Qed.
Lemma lem6163317 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6163318 {B : Type'} (op : type1400 B) (x : B) : (term591 B op x) = (term592 B op x).
Proof. exact (MK_COMB (@lem6163317) (@lem6163316 B op x)). Qed.
Lemma lem6163319 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term588 B op x y) = (term568 B y op x).
Proof. exact (eq_refl (term588 B op x y)). Qed.
Lemma lem6163320 {B : Type'} (op : type1400 B) : (term431 B op) = (term431 B op).
Proof. exact (eq_refl (term431 B op)). Qed.
Lemma lem6163321 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term593 B op x y) = (term594 B y op x).
Proof. exact (MK_COMB (@lem6163320 B op) (@lem6163319 B y op x)). Qed.
Lemma lem6163322 {B : Type'} (op : type1400 B) (x : B) : (term595 B op x) = (term596 B op x).
Proof. exact (fun_ext (fun y : B => @lem6163321 B y op x)). Qed.
Lemma lem6163323 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6163324 {B : Type'} (op : type1400 B) (x : B) : (term587 B op x) = (term597 B op x).
Proof. exact (MK_COMB (@lem6163323 B) (@lem6163322 B op x)). Qed.
Lemma lem6163325 {B : Type'} (op : type1400 B) (x : B) : ((term586 B op x) = (term587 B op x)) = ((term582 B op x) = (term597 B op x)).
Proof. exact (MK_COMB (@lem6163318 B op x) (@lem6163324 B op x)). Qed.
Lemma lem6163326 {B : Type'} (op : type1400 B) (x : B) : (term582 B op x) = (term597 B op x).
Proof. exact (EQ_MP (@lem6163325 B op x) (@lem6163310 B op x)). Qed.
Lemma lem6163328 {A : Type'} (P : Prop) (Q : A -> Prop) : (term555 A P Q) = (term556 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6163329 {B : Type'} (P : Prop) (Q : B -> Prop) : (term555 B P Q) = (term556 B P Q).
Proof. exact (@lem6163328 B P Q). Qed.
Lemma lem6163330 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term598 B y op x) = (term599 B y op x).
Proof. exact (@lem6163329 B (@monoidal B op) (term567 B y op x)). Qed.
Lemma lem6163331 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term600 B y op x z) = (term565 B y z op x).
Proof. exact (eq_refl (term600 B y op x z)). Qed.
Lemma lem6163332 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term601 B y op x) = (term567 B y op x).
Proof. exact (fun_ext (fun z : B => @lem6163331 B y z op x)). Qed.
Lemma lem6163333 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6163334 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term602 B y op x) = (term568 B y op x).
Proof. exact (MK_COMB (@lem6163333 B) (@lem6163332 B y op x)). Qed.
Lemma lem6163335 {B : Type'} (op : type1400 B) : (term431 B op) = (term431 B op).
Proof. exact (eq_refl (term431 B op)). Qed.
Lemma lem6163336 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term598 B y op x) = (term594 B y op x).
Proof. exact (MK_COMB (@lem6163335 B op) (@lem6163334 B y op x)). Qed.
Lemma lem6163337 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6163338 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term603 B y op x) = (term604 B y op x).
Proof. exact (MK_COMB (@lem6163337) (@lem6163336 B y op x)). Qed.
Lemma lem6163339 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term600 B y op x z) = (term565 B y z op x).
Proof. exact (eq_refl (term600 B y op x z)). Qed.
Lemma lem6163340 {B : Type'} (op : type1400 B) : (term431 B op) = (term431 B op).
Proof. exact (eq_refl (term431 B op)). Qed.
Lemma lem6163341 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term605 B y op x z) = (term606 B y z op x).
Proof. exact (MK_COMB (@lem6163340 B op) (@lem6163339 B y z op x)). Qed.
Lemma lem6163342 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term607 B y op x) = (term608 B y op x).
Proof. exact (fun_ext (fun z : B => @lem6163341 B y z op x)). Qed.
Lemma lem6163343 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6163344 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term599 B y op x) = (term609 B y op x).
Proof. exact (MK_COMB (@lem6163343 B) (@lem6163342 B y op x)). Qed.
Lemma lem6163345 {B : Type'} (y : B) (op : type1400 B) (x : B) : ((term598 B y op x) = (term599 B y op x)) = ((term594 B y op x) = (term609 B y op x)).
Proof. exact (MK_COMB (@lem6163338 B y op x) (@lem6163344 B y op x)). Qed.
Lemma lem6163346 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term594 B y op x) = (term609 B y op x).
Proof. exact (EQ_MP (@lem6163345 B y op x) (@lem6163330 B y op x)). Qed.
Lemma lem6163347 {B : Type'} (op : type1400 B) (x : B) : (term596 B op x) = (term610 B op x).
Proof. exact (fun_ext (fun y : B => @lem6163346 B y op x)). Qed.
Lemma lem6163348 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6163349 {B : Type'} (op : type1400 B) (x : B) : (term597 B op x) = (term611 B op x).
Proof. exact (MK_COMB (@lem6163348 B) (@lem6163347 B op x)). Qed.
Lemma lem6163350 {B : Type'} (op : type1400 B) (x : B) : (term582 B op x) = (term611 B op x).
Proof. exact (TRANS (@lem6163326 B op x) (@lem6163349 B op x)). Qed.
Lemma lem6163351 {B : Type'} (op : type1400 B) : (term584 B op) = (term612 B op).
Proof. exact (fun_ext (fun x : B => @lem6163350 B op x)). Qed.
Lemma lem6163352 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6163353 {B : Type'} (op : type1400 B) : (term585 B op) = (term613 B op).
Proof. exact (MK_COMB (@lem6163352 B) (@lem6163351 B op)). Qed.
Lemma lem6163354 {B : Type'} (op : type1400 B) : (term573 B op) = (term613 B op).
Proof. exact (TRANS (@lem6163306 B op) (@lem6163353 B op)). Qed.
Lemma lem6163355 {B : Type'} (op : type1400 B) : (term433 B op) = (term613 B op).
Proof. exact (TRANS (@lem6163286 B op) (@lem6163354 B op)). Qed.
Lemma lem6163356 {B : Type'} : (term446 B) = (term614 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6163355 B op)). Qed.
Lemma lem6163357 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6163358 {B : Type'} : (term457 B) = (term615 B).
Proof. exact (MK_COMB (@lem6163357 B) (@lem6163356 B)). Qed.
Lemma lem6163360 {A B : Type'} (P : type1413 A B) : (term616 A B P) = (term617 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6163361 {B : Type'} (P : type401 B) : (term618 B P) = (term619 B P).
Proof. exact (@lem6163360 (type1400 B) B P). Qed.
Lemma lem6163362 {B : Type'} : (term620 B) = (term621 B).
Proof. exact (@lem6163361 B (term622 B)). Qed.
Lemma lem6163363 {B : Type'} (op : type1400 B) : (term623 B op) = (term612 B op).
Proof. exact (eq_refl (term623 B op)). Qed.
Lemma lem6163364 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6163365 {B : Type'} (op : type1400 B) (x : B) : (term624 B op x) = (term625 B op x).
Proof. exact (MK_COMB (@lem6163363 B op) (@lem6163364 B x)). Qed.
Lemma lem6163366 {B : Type'} (op : type1400 B) (x : B) : (term625 B op x) = (term611 B op x).
Proof. exact (eq_refl (term625 B op x)). Qed.
Lemma lem6163367 {B : Type'} (op : type1400 B) (x : B) : (term624 B op x) = (term611 B op x).
Proof. exact (TRANS (@lem6163365 B op x) (@lem6163366 B op x)). Qed.
Lemma lem6163368 {B : Type'} (op : type1400 B) : (term626 B op) = (term612 B op).
Proof. exact (fun_ext (fun x : B => @lem6163367 B op x)). Qed.
Lemma lem6163369 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6163370 {B : Type'} (op : type1400 B) : (term627 B op) = (term613 B op).
Proof. exact (MK_COMB (@lem6163369 B) (@lem6163368 B op)). Qed.
Lemma lem6163371 {B : Type'} : (term628 B) = (term614 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6163370 B op)). Qed.
Lemma lem6163372 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6163373 {B : Type'} : (term620 B) = (term615 B).
Proof. exact (MK_COMB (@lem6163372 B) (@lem6163371 B)). Qed.
Lemma lem6163374 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6163375 {B : Type'} : (term629 B) = (term630 B).
Proof. exact (MK_COMB (@lem6163374) (@lem6163373 B)). Qed.
Lemma lem6163376 {B : Type'} (op : type1400 B) : (term623 B op) = (term612 B op).
Proof. exact (eq_refl (term623 B op)). Qed.
Lemma lem6163377 {B : Type'} (x : type402 B) (op : type1400 B) : (x op) = (x op).
Proof. exact (eq_refl (x op)). Qed.
Lemma lem6163378 {B : Type'} (x : type402 B) (op : type1400 B) : (term631 B x op) = (term632 B x op).
Proof. exact (MK_COMB (@lem6163376 B op) (@lem6163377 B x op)). Qed.
Lemma lem6163379 {B : Type'} (x : type402 B) (op : type1400 B) : (term632 B x op) = (term633 B x op).
Proof. exact (eq_refl (term632 B x op)). Qed.
Lemma lem6163380 {B : Type'} (x : type402 B) (op : type1400 B) : (term631 B x op) = (term633 B x op).
Proof. exact (TRANS (@lem6163378 B x op) (@lem6163379 B x op)). Qed.
Lemma lem6163381 {B : Type'} (x : type402 B) : (term634 B x) = (term635 B x).
Proof. exact (fun_ext (fun op : type1400 B => @lem6163380 B x op)). Qed.
Lemma lem6163382 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6163383 {B : Type'} (x : type402 B) : (term636 B x) = (term637 B x).
Proof. exact (MK_COMB (@lem6163382 B) (@lem6163381 B x)). Qed.
Lemma lem6163384 {B : Type'} : (term638 B) = (term639 B).
Proof. exact (fun_ext (fun x : type402 B => @lem6163383 B x)). Qed.
Lemma lem6163385 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6163386 {B : Type'} : (term621 B) = (term640 B).
Proof. exact (MK_COMB (@lem6163385 B) (@lem6163384 B)). Qed.
Lemma lem6163387 {B : Type'} : ((term620 B) = (term621 B)) = ((term615 B) = (term640 B)).
Proof. exact (MK_COMB (@lem6163375 B) (@lem6163386 B)). Qed.
Lemma lem6163388 {B : Type'} : (term615 B) = (term640 B).
Proof. exact (EQ_MP (@lem6163387 B) (@lem6163362 B)). Qed.
Lemma lem6163390 {A B : Type'} (P : type1413 A B) : (term616 A B P) = (term617 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6163391 {B : Type'} (P : type401 B) : (term618 B P) = (term619 B P).
Proof. exact (@lem6163390 (type1400 B) B P). Qed.
Lemma lem6163392 {B : Type'} (x : type402 B) : (term641 B x) = (term642 B x).
Proof. exact (@lem6163391 B (term643 B x)). Qed.
Lemma lem6163393 {B : Type'} (x : type402 B) (op : type1400 B) : (term644 B x op) = (term645 B x op).
Proof. exact (eq_refl (term644 B x op)). Qed.
Lemma lem6163394 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem6163395 {B : Type'} (x : type402 B) (op : type1400 B) (y : B) : (term646 B x op y) = (term647 B x op y).
Proof. exact (MK_COMB (@lem6163393 B x op) (@lem6163394 B y)). Qed.
Lemma lem6163396 {B : Type'} (y : B) (x : type402 B) (op : type1400 B) : (term647 B x op y) = (term648 B y x op).
Proof. exact (eq_refl (term647 B x op y)). Qed.
Lemma lem6163397 {B : Type'} (y : B) (x : type402 B) (op : type1400 B) : (term646 B x op y) = (term648 B y x op).
Proof. exact (TRANS (@lem6163395 B x op y) (@lem6163396 B y x op)). Qed.
Lemma lem6163398 {B : Type'} (x : type402 B) (op : type1400 B) : (term649 B x op) = (term645 B x op).
Proof. exact (fun_ext (fun y : B => @lem6163397 B y x op)). Qed.
Lemma lem6163399 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6163400 {B : Type'} (x : type402 B) (op : type1400 B) : (term650 B x op) = (term633 B x op).
Proof. exact (MK_COMB (@lem6163399 B) (@lem6163398 B x op)). Qed.
Lemma lem6163401 {B : Type'} (x : type402 B) : (term651 B x) = (term635 B x).
Proof. exact (fun_ext (fun op : type1400 B => @lem6163400 B x op)). Qed.
Lemma lem6163402 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6163403 {B : Type'} (x : type402 B) : (term641 B x) = (term637 B x).
Proof. exact (MK_COMB (@lem6163402 B) (@lem6163401 B x)). Qed.
Lemma lem6163404 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6163405 {B : Type'} (x : type402 B) : (term652 B x) = (term653 B x).
Proof. exact (MK_COMB (@lem6163404) (@lem6163403 B x)). Qed.
Lemma lem6163406 {B : Type'} (x : type402 B) (op : type1400 B) : (term644 B x op) = (term645 B x op).
Proof. exact (eq_refl (term644 B x op)). Qed.
Lemma lem6163407 {B : Type'} (y : type402 B) (op : type1400 B) : (y op) = (y op).
Proof. exact (eq_refl (y op)). Qed.
Lemma lem6163408 {B : Type'} (x : type402 B) (y : type402 B) (op : type1400 B) : (term654 B x y op) = (term655 B x y op).
Proof. exact (MK_COMB (@lem6163406 B x op) (@lem6163407 B y op)). Qed.
Lemma lem6163409 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term655 B x y op) = (term656 B y x op).
Proof. exact (eq_refl (term655 B x y op)). Qed.
Lemma lem6163410 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term654 B x y op) = (term656 B y x op).
Proof. exact (TRANS (@lem6163408 B x y op) (@lem6163409 B y x op)). Qed.
Lemma lem6163411 {B : Type'} (y : type402 B) (x : type402 B) : (term657 B x y) = (term658 B y x).
Proof. exact (fun_ext (fun op : type1400 B => @lem6163410 B y x op)). Qed.
Lemma lem6163412 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6163413 {B : Type'} (y : type402 B) (x : type402 B) : (term659 B x y) = (term660 B y x).
Proof. exact (MK_COMB (@lem6163412 B) (@lem6163411 B y x)). Qed.
Lemma lem6163414 {B : Type'} (x : type402 B) : (term661 B x) = (term662 B x).
Proof. exact (fun_ext (fun y : type402 B => @lem6163413 B y x)). Qed.
Lemma lem6163415 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6163416 {B : Type'} (x : type402 B) : (term642 B x) = (term663 B x).
Proof. exact (MK_COMB (@lem6163415 B) (@lem6163414 B x)). Qed.
Lemma lem6163417 {B : Type'} (x : type402 B) : ((term641 B x) = (term642 B x)) = ((term637 B x) = (term663 B x)).
Proof. exact (MK_COMB (@lem6163405 B x) (@lem6163416 B x)). Qed.
Lemma lem6163418 {B : Type'} (x : type402 B) : (term637 B x) = (term663 B x).
Proof. exact (EQ_MP (@lem6163417 B x) (@lem6163392 B x)). Qed.
Lemma lem6163420 {A B : Type'} (P : type1413 A B) : (term616 A B P) = (term617 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6163421 {B : Type'} (P : type401 B) : (term618 B P) = (term619 B P).
Proof. exact (@lem6163420 (type1400 B) B P). Qed.
Lemma lem6163422 {B : Type'} (y : type402 B) (x : type402 B) : (term664 B y x) = (term665 B y x).
Proof. exact (@lem6163421 B (term666 B y x)). Qed.
Lemma lem6163423 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term667 B y x op) = (term668 B y x op).
Proof. exact (eq_refl (term667 B y x op)). Qed.
Lemma lem6163424 {B : Type'} (z : B) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem6163425 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) (z : B) : (term669 B y x op z) = (term670 B y x op z).
Proof. exact (MK_COMB (@lem6163423 B y x op) (@lem6163424 B z)). Qed.
Lemma lem6163426 {B : Type'} (y : type402 B) (z : B) (x : type402 B) (op : type1400 B) : (term670 B y x op z) = (term671 B y z x op).
Proof. exact (eq_refl (term670 B y x op z)). Qed.
Lemma lem6163427 {B : Type'} (y : type402 B) (z : B) (x : type402 B) (op : type1400 B) : (term669 B y x op z) = (term671 B y z x op).
Proof. exact (TRANS (@lem6163425 B y x op z) (@lem6163426 B y z x op)). Qed.
Lemma lem6163428 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term672 B y x op) = (term668 B y x op).
Proof. exact (fun_ext (fun z : B => @lem6163427 B y z x op)). Qed.
Lemma lem6163429 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6163430 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term673 B y x op) = (term656 B y x op).
Proof. exact (MK_COMB (@lem6163429 B) (@lem6163428 B y x op)). Qed.
Lemma lem6163431 {B : Type'} (y : type402 B) (x : type402 B) : (term674 B y x) = (term658 B y x).
Proof. exact (fun_ext (fun op : type1400 B => @lem6163430 B y x op)). Qed.
Lemma lem6163432 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6163433 {B : Type'} (y : type402 B) (x : type402 B) : (term664 B y x) = (term660 B y x).
Proof. exact (MK_COMB (@lem6163432 B) (@lem6163431 B y x)). Qed.
Lemma lem6163434 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6163435 {B : Type'} (y : type402 B) (x : type402 B) : (term675 B y x) = (term676 B y x).
Proof. exact (MK_COMB (@lem6163434) (@lem6163433 B y x)). Qed.
Lemma lem6163436 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term667 B y x op) = (term668 B y x op).
Proof. exact (eq_refl (term667 B y x op)). Qed.
Lemma lem6163437 {B : Type'} (z : type402 B) (op : type1400 B) : (z op) = (z op).
Proof. exact (eq_refl (z op)). Qed.
Lemma lem6163438 {B : Type'} (y : type402 B) (x : type402 B) (z : type402 B) (op : type1400 B) : (term677 B y x z op) = (term678 B y x z op).
Proof. exact (MK_COMB (@lem6163436 B y x op) (@lem6163437 B z op)). Qed.
Lemma lem6163439 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (op : type1400 B) : (term678 B y x z op) = (term679 B y z x op).
Proof. exact (eq_refl (term678 B y x z op)). Qed.
Lemma lem6163440 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (op : type1400 B) : (term677 B y x z op) = (term679 B y z x op).
Proof. exact (TRANS (@lem6163438 B y x z op) (@lem6163439 B y z x op)). Qed.
Lemma lem6163441 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) : (term680 B y x z) = (term681 B y z x).
Proof. exact (fun_ext (fun op : type1400 B => @lem6163440 B y z x op)). Qed.
Lemma lem6163442 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6163443 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) : (term682 B y x z) = (term683 B y z x).
Proof. exact (MK_COMB (@lem6163442 B) (@lem6163441 B y z x)). Qed.
Lemma lem6163444 {B : Type'} (y : type402 B) (x : type402 B) : (term684 B y x) = (term685 B y x).
Proof. exact (fun_ext (fun z : type402 B => @lem6163443 B y z x)). Qed.
Lemma lem6163445 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6163446 {B : Type'} (y : type402 B) (x : type402 B) : (term665 B y x) = (term686 B y x).
Proof. exact (MK_COMB (@lem6163445 B) (@lem6163444 B y x)). Qed.
Lemma lem6163447 {B : Type'} (y : type402 B) (x : type402 B) : ((term664 B y x) = (term665 B y x)) = ((term660 B y x) = (term686 B y x)).
Proof. exact (MK_COMB (@lem6163435 B y x) (@lem6163446 B y x)). Qed.
Lemma lem6163448 {B : Type'} (y : type402 B) (x : type402 B) : (term660 B y x) = (term686 B y x).
Proof. exact (EQ_MP (@lem6163447 B y x) (@lem6163422 B y x)). Qed.
Lemma lem6163449 {B : Type'} (x : type402 B) : (term662 B x) = (term687 B x).
Proof. exact (fun_ext (fun y : type402 B => @lem6163448 B y x)). Qed.
Lemma lem6163450 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6163451 {B : Type'} (x : type402 B) : (term663 B x) = (term688 B x).
Proof. exact (MK_COMB (@lem6163450 B) (@lem6163449 B x)). Qed.
Lemma lem6163452 {B : Type'} (x : type402 B) : (term637 B x) = (term688 B x).
Proof. exact (TRANS (@lem6163418 B x) (@lem6163451 B x)). Qed.
Lemma lem6163453 {B : Type'} : (term639 B) = (term689 B).
Proof. exact (fun_ext (fun x : type402 B => @lem6163452 B x)). Qed.
Lemma lem6163454 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6163455 {B : Type'} : (term640 B) = (term690 B).
Proof. exact (MK_COMB (@lem6163454 B) (@lem6163453 B)). Qed.
Lemma lem6163456 {B : Type'} : (term615 B) = (term690 B).
Proof. exact (TRANS (@lem6163388 B) (@lem6163455 B)). Qed.
Lemma lem6163457 {B : Type'} : (term457 B) = (term690 B).
Proof. exact (TRANS (@lem6163358 B) (@lem6163456 B)). Qed.
Lemma lem6163458 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6163459 {B : Type'} : (term459 B) = (term691 B).
Proof. exact (MK_COMB (@lem6163458) (@lem6163457 B)). Qed.
Lemma lem6163460 {B : Type'} : (term462 B) = (term462 B).
Proof. exact (eq_refl (term462 B)). Qed.
Lemma lem6163461 {B : Type'} : (term463 B) = (term692 B).
Proof. exact (MK_COMB (@lem6163459 B) (@lem6163460 B)). Qed.
Lemma lem6163463 {A : Type'} (P : A -> Prop) (Q : Prop) : (term693 A P Q) = (term694 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6163464 {B : Type'} (P : type82 B) (Q : Prop) : (term695 B P Q) = (term696 B P Q).
Proof. exact (@lem6163463 (type402 B) P Q). Qed.
Lemma lem6163465 {B : Type'} : (term697 B) = (term698 B).
Proof. exact (@lem6163464 B (term689 B) (term462 B)). Qed.
Lemma lem6163466 {B : Type'} (x : type402 B) : (term699 B x) = (term688 B x).
Proof. exact (eq_refl (term699 B x)). Qed.
Lemma lem6163467 {B : Type'} : (term700 B) = (term689 B).
Proof. exact (fun_ext (fun x : type402 B => @lem6163466 B x)). Qed.
Lemma lem6163468 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6163469 {B : Type'} : (term701 B) = (term690 B).
Proof. exact (MK_COMB (@lem6163468 B) (@lem6163467 B)). Qed.
Lemma lem6163470 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6163471 {B : Type'} : (term702 B) = (term691 B).
Proof. exact (MK_COMB (@lem6163470) (@lem6163469 B)). Qed.
Lemma lem6163472 {B : Type'} : (term462 B) = (term462 B).
Proof. exact (eq_refl (term462 B)). Qed.
Lemma lem6163473 {B : Type'} : (term697 B) = (term692 B).
Proof. exact (MK_COMB (@lem6163471 B) (@lem6163472 B)). Qed.
Lemma lem6163474 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6163475 {B : Type'} : (term703 B) = (term704 B).
Proof. exact (MK_COMB (@lem6163474) (@lem6163473 B)). Qed.
Lemma lem6163476 {B : Type'} (x : type402 B) : (term699 B x) = (term688 B x).
Proof. exact (eq_refl (term699 B x)). Qed.
Lemma lem6163477 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6163478 {B : Type'} (x : type402 B) : (term705 B x) = (term706 B x).
Proof. exact (MK_COMB (@lem6163477) (@lem6163476 B x)). Qed.
Lemma lem6163479 {B : Type'} : (term462 B) = (term462 B).
Proof. exact (eq_refl (term462 B)). Qed.
Lemma lem6163480 {B : Type'} (x : type402 B) : (term707 B x) = (term708 B x).
Proof. exact (MK_COMB (@lem6163478 B x) (@lem6163479 B)). Qed.
Lemma lem6163481 {B : Type'} : (term709 B) = (term710 B).
Proof. exact (fun_ext (fun x : type402 B => @lem6163480 B x)). Qed.
Lemma lem6163482 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6163483 {B : Type'} : (term698 B) = (term711 B).
Proof. exact (MK_COMB (@lem6163482 B) (@lem6163481 B)). Qed.
Lemma lem6163484 {B : Type'} : ((term697 B) = (term698 B)) = ((term692 B) = (term711 B)).
Proof. exact (MK_COMB (@lem6163475 B) (@lem6163483 B)). Qed.
Lemma lem6163485 {B : Type'} : (term692 B) = (term711 B).
Proof. exact (EQ_MP (@lem6163484 B) (@lem6163465 B)). Qed.
Lemma lem6163487 {A : Type'} (P : A -> Prop) (Q : Prop) : (term693 A P Q) = (term694 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6163488 {B : Type'} (P : type82 B) (Q : Prop) : (term695 B P Q) = (term696 B P Q).
Proof. exact (@lem6163487 (type402 B) P Q). Qed.
Lemma lem6163489 {B : Type'} (x : type402 B) : (term712 B x) = (term713 B x).
Proof. exact (@lem6163488 B (term687 B x) (term462 B)). Qed.
Lemma lem6163490 {B : Type'} (y : type402 B) (x : type402 B) : (term714 B x y) = (term686 B y x).
Proof. exact (eq_refl (term714 B x y)). Qed.
Lemma lem6163491 {B : Type'} (x : type402 B) : (term715 B x) = (term687 B x).
Proof. exact (fun_ext (fun y : type402 B => @lem6163490 B y x)). Qed.
Lemma lem6163492 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6163493 {B : Type'} (x : type402 B) : (term716 B x) = (term688 B x).
Proof. exact (MK_COMB (@lem6163492 B) (@lem6163491 B x)). Qed.
Lemma lem6163494 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6163495 {B : Type'} (x : type402 B) : (term717 B x) = (term706 B x).
Proof. exact (MK_COMB (@lem6163494) (@lem6163493 B x)). Qed.
Lemma lem6163496 {B : Type'} : (term462 B) = (term462 B).
Proof. exact (eq_refl (term462 B)). Qed.
Lemma lem6163497 {B : Type'} (x : type402 B) : (term712 B x) = (term708 B x).
Proof. exact (MK_COMB (@lem6163495 B x) (@lem6163496 B)). Qed.
Lemma lem6163498 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6163499 {B : Type'} (x : type402 B) : (term718 B x) = (term719 B x).
Proof. exact (MK_COMB (@lem6163498) (@lem6163497 B x)). Qed.
Lemma lem6163500 {B : Type'} (y : type402 B) (x : type402 B) : (term714 B x y) = (term686 B y x).
Proof. exact (eq_refl (term714 B x y)). Qed.
Lemma lem6163501 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6163502 {B : Type'} (y : type402 B) (x : type402 B) : (term720 B x y) = (term721 B y x).
Proof. exact (MK_COMB (@lem6163501) (@lem6163500 B y x)). Qed.
Lemma lem6163503 {B : Type'} : (term462 B) = (term462 B).
Proof. exact (eq_refl (term462 B)). Qed.
Lemma lem6163504 {B : Type'} (y : type402 B) (x : type402 B) : (term722 B x y) = (term723 B y x).
Proof. exact (MK_COMB (@lem6163502 B y x) (@lem6163503 B)). Qed.
Lemma lem6163505 {B : Type'} (x : type402 B) : (term724 B x) = (term725 B x).
Proof. exact (fun_ext (fun y : type402 B => @lem6163504 B y x)). Qed.
Lemma lem6163506 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6163507 {B : Type'} (x : type402 B) : (term713 B x) = (term726 B x).
Proof. exact (MK_COMB (@lem6163506 B) (@lem6163505 B x)). Qed.
Lemma lem6163508 {B : Type'} (x : type402 B) : ((term712 B x) = (term713 B x)) = ((term708 B x) = (term726 B x)).
Proof. exact (MK_COMB (@lem6163499 B x) (@lem6163507 B x)). Qed.
Lemma lem6163509 {B : Type'} (x : type402 B) : (term708 B x) = (term726 B x).
Proof. exact (EQ_MP (@lem6163508 B x) (@lem6163489 B x)). Qed.
Lemma lem6163511 {A : Type'} (P : A -> Prop) (Q : Prop) : (term693 A P Q) = (term694 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6163512 {B : Type'} (P : type82 B) (Q : Prop) : (term695 B P Q) = (term696 B P Q).
Proof. exact (@lem6163511 (type402 B) P Q). Qed.
Lemma lem6163513 {B : Type'} (y : type402 B) (x : type402 B) : (term727 B y x) = (term728 B y x).
Proof. exact (@lem6163512 B (term685 B y x) (term462 B)). Qed.
Lemma lem6163514 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) : (term729 B y x z) = (term683 B y z x).
Proof. exact (eq_refl (term729 B y x z)). Qed.
Lemma lem6163515 {B : Type'} (y : type402 B) (x : type402 B) : (term730 B y x) = (term685 B y x).
Proof. exact (fun_ext (fun z : type402 B => @lem6163514 B y z x)). Qed.
Lemma lem6163516 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6163517 {B : Type'} (y : type402 B) (x : type402 B) : (term731 B y x) = (term686 B y x).
Proof. exact (MK_COMB (@lem6163516 B) (@lem6163515 B y x)). Qed.
Lemma lem6163518 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6163519 {B : Type'} (y : type402 B) (x : type402 B) : (term732 B y x) = (term721 B y x).
Proof. exact (MK_COMB (@lem6163518) (@lem6163517 B y x)). Qed.
Lemma lem6163520 {B : Type'} : (term462 B) = (term462 B).
Proof. exact (eq_refl (term462 B)). Qed.
Lemma lem6163521 {B : Type'} (y : type402 B) (x : type402 B) : (term727 B y x) = (term723 B y x).
Proof. exact (MK_COMB (@lem6163519 B y x) (@lem6163520 B)). Qed.
Lemma lem6163522 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6163523 {B : Type'} (y : type402 B) (x : type402 B) : (term733 B y x) = (term734 B y x).
Proof. exact (MK_COMB (@lem6163522) (@lem6163521 B y x)). Qed.
Lemma lem6163524 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) : (term729 B y x z) = (term683 B y z x).
Proof. exact (eq_refl (term729 B y x z)). Qed.
Lemma lem6163525 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6163526 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) : (term735 B y x z) = (term736 B y z x).
Proof. exact (MK_COMB (@lem6163525) (@lem6163524 B y z x)). Qed.
Lemma lem6163527 {B : Type'} : (term462 B) = (term462 B).
Proof. exact (eq_refl (term462 B)). Qed.
Lemma lem6163528 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) : (term737 B y x z) = (term738 B y z x).
Proof. exact (MK_COMB (@lem6163526 B y z x) (@lem6163527 B)). Qed.
Lemma lem6163529 {B : Type'} (y : type402 B) (x : type402 B) : (term739 B y x) = (term740 B y x).
Proof. exact (fun_ext (fun z : type402 B => @lem6163528 B y z x)). Qed.
Lemma lem6163530 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6163531 {B : Type'} (y : type402 B) (x : type402 B) : (term728 B y x) = (term741 B y x).
Proof. exact (MK_COMB (@lem6163530 B) (@lem6163529 B y x)). Qed.
Lemma lem6163532 {B : Type'} (y : type402 B) (x : type402 B) : ((term727 B y x) = (term728 B y x)) = ((term723 B y x) = (term741 B y x)).
Proof. exact (MK_COMB (@lem6163523 B y x) (@lem6163531 B y x)). Qed.
Lemma lem6163533 {B : Type'} (y : type402 B) (x : type402 B) : (term723 B y x) = (term741 B y x).
Proof. exact (EQ_MP (@lem6163532 B y x) (@lem6163513 B y x)). Qed.
Lemma lem6163534 {B : Type'} (x : type402 B) : (term725 B x) = (term742 B x).
Proof. exact (fun_ext (fun y : type402 B => @lem6163533 B y x)). Qed.
Lemma lem6163535 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6163536 {B : Type'} (x : type402 B) : (term726 B x) = (term743 B x).
Proof. exact (MK_COMB (@lem6163535 B) (@lem6163534 B x)). Qed.
Lemma lem6163537 {B : Type'} (x : type402 B) : (term708 B x) = (term743 B x).
Proof. exact (TRANS (@lem6163509 B x) (@lem6163536 B x)). Qed.
Lemma lem6163538 {B : Type'} : (term710 B) = (term744 B).
Proof. exact (fun_ext (fun x : type402 B => @lem6163537 B x)). Qed.
Lemma lem6163539 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6163540 {B : Type'} : (term711 B) = (term745 B).
Proof. exact (MK_COMB (@lem6163539 B) (@lem6163538 B)). Qed.
Lemma lem6163541 {B : Type'} : (term692 B) = (term745 B).
Proof. exact (TRANS (@lem6163485 B) (@lem6163540 B)). Qed.
Lemma lem6163542 {B : Type'} : (term463 B) = (term745 B).
Proof. exact (TRANS (@lem6163461 B) (@lem6163541 B)). Qed.
Lemma lem6163543 {B : Type'} : (term439 B) = (term745 B).
Proof. exact (TRANS (@lem6162992 B) (@lem6163542 B)). Qed.
Lemma lem6163544 {B : Type'} : (term257 B) = (term745 B).
Proof. exact (TRANS (@lem6162965 B) (@lem6163543 B)). Qed.
Lemma lem6163545 {B : Type'} (h1 : term257 B) : term745 B.
Proof. exact (EQ_MP (@lem6163544 B) (@lem6162615 B h1)). Qed.
Lemma lem6163546 {B : Type'} (x : type402 B) (h1 : term743 B x) : term743 B x.
Proof. exact (h1). Qed.
Lemma lem6163547 {B : Type'} (y : type402 B) (x : type402 B) (h1 : term741 B y x) : term741 B y x.
Proof. exact (h1). Qed.
Lemma lem6163548 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term738 B y z x) : term738 B y z x.
Proof. exact (h1). Qed.
Lemma lem6163549 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term370 A B s f g x' op) : term370 A B s f g x' op.
Proof. exact (h1). Qed.
Lemma lem6163554 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163555 {B : Type'} (f : type403 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> Prop) f x).
Proof. exact (@lem6163554 (type1400 B) Prop f x). Qed.
Lemma lem6163557 {B : Type'} (op : type1400 B) : (@monoidal B op) = (@I ((B -> B -> B) -> Prop) (@monoidal B) op).
Proof. exact (@lem6163555 B (@monoidal B) op). Qed.
Lemma lem6163627 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6163628 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6163633 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163634 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6163633 (type1400 B) B f x). Qed.
Lemma lem6163636 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem6163634 B (@neutral B) op). Qed.
Lemma lem6163637 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6163638 {B : Type'} (op : type1400 B) : (term746 B op) = (term747 B op).
Proof. exact (MK_COMB (@lem6163628 B op) (@lem6163636 B op)). Qed.
Lemma lem6163639 {B : Type'} (op : type1400 B) (x : B) : (term290 B op x) = (term748 B op x).
Proof. exact (MK_COMB (@lem6163638 B op) (@lem6163637 B x)). Qed.
Lemma lem6163641 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163642 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem6163641 B (B -> B) f x). Qed.
Lemma lem6163643 {B : Type'} (op : type1400 B) : (term747 B op) = (term749 B op).
Proof. exact (@lem6163642 B op (@I ((B -> B -> B) -> B) (@neutral B) op)). Qed.
Lemma lem6163644 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6163645 {B : Type'} (op : type1400 B) (x : B) : (term748 B op x) = (term750 B op x).
Proof. exact (MK_COMB (@lem6163643 B op) (@lem6163644 B x)). Qed.
Lemma lem6163647 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163648 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem6163647 B B f x). Qed.
Lemma lem6163649 {B : Type'} (op : type1400 B) (x : B) : (term750 B op x) = (term751 B op x).
Proof. exact (@lem6163648 B (term749 B op) x). Qed.
Lemma lem6163650 {B : Type'} (op : type1400 B) (x : B) : (term748 B op x) = (term751 B op x).
Proof. exact (TRANS (@lem6163645 B op x) (@lem6163649 B op x)). Qed.
Lemma lem6163651 {B : Type'} (op : type1400 B) (x : B) : (term290 B op x) = (term751 B op x).
Proof. exact (TRANS (@lem6163639 B op x) (@lem6163650 B op x)). Qed.
Lemma lem6163652 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6163653 {B : Type'} (op : type1400 B) (x : B) : (term752 B op x) = (term753 B op x).
Proof. exact (MK_COMB (@lem6163627 B) (@lem6163651 B op x)). Qed.
Lemma lem6163654 {B : Type'} (op : type1400 B) (x : B) : ((term290 B op x) = x) = ((term751 B op x) = x).
Proof. exact (MK_COMB (@lem6163653 B op x) (@lem6163652 B x)). Qed.
Lemma lem6163655 {B : Type'} (op : type1400 B) : (term291 B op) = (term754 B op).
Proof. exact (fun_ext (fun x : B => @lem6163654 B op x)). Qed.
Lemma lem6163656 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6163657 {B : Type'} (op : type1400 B) : (term292 B op) = (term755 B op).
Proof. exact (MK_COMB (@lem6163656 B) (@lem6163655 B op)). Qed.
Lemma lem6163658 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6163667 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163668 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem6163667 B (B -> B) f x). Qed.
Lemma lem6163669 {B : Type'} (op : type1400 B) (y : B) : (op y) = (@I (B -> B -> B) op y).
Proof. exact (@lem6163668 B op y). Qed.
Lemma lem6163670 {B : Type'} (z : B) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem6163671 {B : Type'} (op : type1400 B) (y : B) (z : B) : (op y z) = (@I (B -> B -> B) op y z).
Proof. exact (MK_COMB (@lem6163669 B op y) (@lem6163670 B z)). Qed.
Lemma lem6163673 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163674 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem6163673 B B f x). Qed.
Lemma lem6163675 {B : Type'} (op : type1400 B) (y : B) (z : B) : (@I (B -> B -> B) op y z) = (term756 B op y z).
Proof. exact (@lem6163674 B (@I (B -> B -> B) op y) z). Qed.
Lemma lem6163677 {B : Type'} (op : type1400 B) (y : B) (z : B) : (op y z) = (term756 B op y z).
Proof. exact (TRANS (@lem6163671 B op y z) (@lem6163675 B op y z)). Qed.
Lemma lem6163678 {B : Type'} (op : type1400 B) (x : B) : (op x) = (op x).
Proof. exact (eq_refl (op x)). Qed.
Lemma lem6163679 {B : Type'} (x : B) (op : type1400 B) (y : B) (z : B) : (term293 B x op y z) = (term757 B x op y z).
Proof. exact (MK_COMB (@lem6163678 B op x) (@lem6163677 B op y z)). Qed.
Lemma lem6163681 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163682 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem6163681 B (B -> B) f x). Qed.
Lemma lem6163683 {B : Type'} (op : type1400 B) (x : B) : (op x) = (@I (B -> B -> B) op x).
Proof. exact (@lem6163682 B op x). Qed.
Lemma lem6163684 {B : Type'} (op : type1400 B) (y : B) (z : B) : (term756 B op y z) = (term756 B op y z).
Proof. exact (eq_refl (term756 B op y z)). Qed.
Lemma lem6163685 {B : Type'} (x : B) (op : type1400 B) (y : B) (z : B) : (term757 B x op y z) = (term758 B x op y z).
Proof. exact (MK_COMB (@lem6163683 B op x) (@lem6163684 B op y z)). Qed.
Lemma lem6163687 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163688 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem6163687 B B f x). Qed.
Lemma lem6163689 {B : Type'} (x : B) (op : type1400 B) (y : B) (z : B) : (term758 B x op y z) = (term759 B x op y z).
Proof. exact (@lem6163688 B (@I (B -> B -> B) op x) (term756 B op y z)). Qed.
Lemma lem6163690 {B : Type'} (x : B) (op : type1400 B) (y : B) (z : B) : (term757 B x op y z) = (term759 B x op y z).
Proof. exact (TRANS (@lem6163685 B x op y z) (@lem6163689 B x op y z)). Qed.
Lemma lem6163691 {B : Type'} (x : B) (op : type1400 B) (y : B) (z : B) : (term293 B x op y z) = (term759 B x op y z).
Proof. exact (TRANS (@lem6163679 B x op y z) (@lem6163690 B x op y z)). Qed.
Lemma lem6163692 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6163699 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163700 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem6163699 B (B -> B) f x). Qed.
Lemma lem6163701 {B : Type'} (op : type1400 B) (x : B) : (op x) = (@I (B -> B -> B) op x).
Proof. exact (@lem6163700 B op x). Qed.
Lemma lem6163702 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem6163703 {B : Type'} (op : type1400 B) (x : B) (y : B) : (op x y) = (@I (B -> B -> B) op x y).
Proof. exact (MK_COMB (@lem6163701 B op x) (@lem6163702 B y)). Qed.
Lemma lem6163705 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163706 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem6163705 B B f x). Qed.
Lemma lem6163707 {B : Type'} (op : type1400 B) (x : B) (y : B) : (@I (B -> B -> B) op x y) = (term756 B op x y).
Proof. exact (@lem6163706 B (@I (B -> B -> B) op x) y). Qed.
Lemma lem6163709 {B : Type'} (op : type1400 B) (x : B) (y : B) : (op x y) = (term756 B op x y).
Proof. exact (TRANS (@lem6163703 B op x y) (@lem6163707 B op x y)). Qed.
Lemma lem6163710 {B : Type'} (z : B) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem6163711 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term760 B op x y) = (term761 B op x y).
Proof. exact (MK_COMB (@lem6163692 B op) (@lem6163709 B op x y)). Qed.
Lemma lem6163712 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term294 B op x y z) = (term762 B op x y z).
Proof. exact (MK_COMB (@lem6163711 B op x y) (@lem6163710 B z)). Qed.
Lemma lem6163714 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163715 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem6163714 B (B -> B) f x). Qed.
Lemma lem6163716 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term761 B op x y) = (term763 B op x y).
Proof. exact (@lem6163715 B op (term756 B op x y)). Qed.
Lemma lem6163717 {B : Type'} (z : B) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem6163718 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term762 B op x y z) = (term764 B op x y z).
Proof. exact (MK_COMB (@lem6163716 B op x y) (@lem6163717 B z)). Qed.
Lemma lem6163720 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163721 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem6163720 B B f x). Qed.
Lemma lem6163722 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term764 B op x y z) = (term765 B op x y z).
Proof. exact (@lem6163721 B (term763 B op x y) z). Qed.
Lemma lem6163723 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term762 B op x y z) = (term765 B op x y z).
Proof. exact (TRANS (@lem6163718 B op x y z) (@lem6163722 B op x y z)). Qed.
Lemma lem6163724 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term294 B op x y z) = (term765 B op x y z).
Proof. exact (TRANS (@lem6163712 B op x y z) (@lem6163723 B op x y z)). Qed.
Lemma lem6163725 {B : Type'} (x : B) (op : type1400 B) (y : B) (z : B) : (term766 B x op y z) = (term767 B x op y z).
Proof. exact (MK_COMB (@lem6163658 B) (@lem6163691 B x op y z)). Qed.
Lemma lem6163726 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : ((term293 B x op y z) = (term294 B op x y z)) = ((term759 B x op y z) = (term765 B op x y z)).
Proof. exact (MK_COMB (@lem6163725 B x op y z) (@lem6163724 B op x y z)). Qed.
Lemma lem6163727 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term295 B op x y) = (term768 B op x y).
Proof. exact (fun_ext (fun z : B => @lem6163726 B op x y z)). Qed.
Lemma lem6163728 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6163729 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term296 B op x y) = (term769 B op x y).
Proof. exact (MK_COMB (@lem6163728 B) (@lem6163727 B op x y)). Qed.
Lemma lem6163730 {B : Type'} (op : type1400 B) (x : B) : (term297 B op x) = (term770 B op x).
Proof. exact (fun_ext (fun y : B => @lem6163729 B op x y)). Qed.
Lemma lem6163731 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6163732 {B : Type'} (op : type1400 B) (x : B) : (term298 B op x) = (term771 B op x).
Proof. exact (MK_COMB (@lem6163731 B) (@lem6163730 B op x)). Qed.
Lemma lem6163733 {B : Type'} (op : type1400 B) : (term299 B op) = (term772 B op).
Proof. exact (fun_ext (fun x : B => @lem6163732 B op x)). Qed.
Lemma lem6163734 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6163735 {B : Type'} (op : type1400 B) : (term300 B op) = (term773 B op).
Proof. exact (MK_COMB (@lem6163734 B) (@lem6163733 B op)). Qed.
Lemma lem6163736 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6163737 {B : Type'} (op : type1400 B) : (term301 B op) = (term774 B op).
Proof. exact (MK_COMB (@lem6163736) (@lem6163735 B op)). Qed.
Lemma lem6163738 {B : Type'} (op : type1400 B) : (term302 B op) = (term775 B op).
Proof. exact (MK_COMB (@lem6163737 B op) (@lem6163657 B op)). Qed.
Lemma lem6163739 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6163746 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163747 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem6163746 B (B -> B) f x). Qed.
Lemma lem6163748 {B : Type'} (op : type1400 B) (x : B) : (op x) = (@I (B -> B -> B) op x).
Proof. exact (@lem6163747 B op x). Qed.
Lemma lem6163749 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem6163750 {B : Type'} (op : type1400 B) (x : B) (y : B) : (op x y) = (@I (B -> B -> B) op x y).
Proof. exact (MK_COMB (@lem6163748 B op x) (@lem6163749 B y)). Qed.
Lemma lem6163752 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163753 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem6163752 B B f x). Qed.
Lemma lem6163754 {B : Type'} (op : type1400 B) (x : B) (y : B) : (@I (B -> B -> B) op x y) = (term756 B op x y).
Proof. exact (@lem6163753 B (@I (B -> B -> B) op x) y). Qed.
Lemma lem6163756 {B : Type'} (op : type1400 B) (x : B) (y : B) : (op x y) = (term756 B op x y).
Proof. exact (TRANS (@lem6163750 B op x y) (@lem6163754 B op x y)). Qed.
Lemma lem6163763 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163764 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem6163763 B (B -> B) f x). Qed.
Lemma lem6163765 {B : Type'} (op : type1400 B) (y : B) : (op y) = (@I (B -> B -> B) op y).
Proof. exact (@lem6163764 B op y). Qed.
Lemma lem6163766 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6163767 {B : Type'} (op : type1400 B) (y : B) (x : B) : (op y x) = (@I (B -> B -> B) op y x).
Proof. exact (MK_COMB (@lem6163765 B op y) (@lem6163766 B x)). Qed.
Lemma lem6163769 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163770 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem6163769 B B f x). Qed.
Lemma lem6163771 {B : Type'} (op : type1400 B) (y : B) (x : B) : (@I (B -> B -> B) op y x) = (term756 B op y x).
Proof. exact (@lem6163770 B (@I (B -> B -> B) op y) x). Qed.
Lemma lem6163773 {B : Type'} (op : type1400 B) (y : B) (x : B) : (op y x) = (term756 B op y x).
Proof. exact (TRANS (@lem6163767 B op y x) (@lem6163771 B op y x)). Qed.
Lemma lem6163774 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term776 B op x y) = (term777 B op x y).
Proof. exact (MK_COMB (@lem6163739 B) (@lem6163756 B op x y)). Qed.
Lemma lem6163775 {B : Type'} (op : type1400 B) (y : B) (x : B) : ((op x y) = (op y x)) = ((term756 B op x y) = (term756 B op y x)).
Proof. exact (MK_COMB (@lem6163774 B op x y) (@lem6163773 B op y x)). Qed.
Lemma lem6163776 {B : Type'} (op : type1400 B) (x : B) : (term303 B op x) = (term778 B op x).
Proof. exact (fun_ext (fun y : B => @lem6163775 B op y x)). Qed.
Lemma lem6163777 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6163778 {B : Type'} (op : type1400 B) (x : B) : (term304 B op x) = (term779 B op x).
Proof. exact (MK_COMB (@lem6163777 B) (@lem6163776 B op x)). Qed.
Lemma lem6163779 {B : Type'} (op : type1400 B) : (term305 B op) = (term780 B op).
Proof. exact (fun_ext (fun x : B => @lem6163778 B op x)). Qed.
Lemma lem6163780 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6163781 {B : Type'} (op : type1400 B) : (term306 B op) = (term781 B op).
Proof. exact (MK_COMB (@lem6163780 B) (@lem6163779 B op)). Qed.
Lemma lem6163782 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6163783 {B : Type'} (op : type1400 B) : (term307 B op) = (term782 B op).
Proof. exact (MK_COMB (@lem6163782) (@lem6163781 B op)). Qed.
Lemma lem6163784 {B : Type'} (op : type1400 B) : (term308 B op) = (term783 B op).
Proof. exact (MK_COMB (@lem6163783 B op) (@lem6163738 B op)). Qed.
Lemma lem6163785 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6163790 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163791 {B : Type'} (f : type403 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> Prop) f x).
Proof. exact (@lem6163790 (type1400 B) Prop f x). Qed.
Lemma lem6163793 {B : Type'} (op : type1400 B) : (@monoidal B op) = (@I ((B -> B -> B) -> Prop) (@monoidal B) op).
Proof. exact (@lem6163791 B (@monoidal B) op). Qed.
Lemma lem6163794 {B : Type'} (op : type1400 B) : (term784 B op) = (term785 B op).
Proof. exact (MK_COMB (@lem6163785) (@lem6163793 B op)). Qed.
Lemma lem6163795 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6163796 {B : Type'} (op : type1400 B) : (term429 B op) = (term786 B op).
Proof. exact (MK_COMB (@lem6163795) (@lem6163794 B op)). Qed.
Lemma lem6163797 {B : Type'} (op : type1400 B) : (term430 B op) = (term787 B op).
Proof. exact (MK_COMB (@lem6163796 B op) (@lem6163784 B op)). Qed.
Lemma lem6163798 {B : Type'} : (term447 B) = (term788 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6163797 B op)). Qed.
Lemma lem6163799 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6163800 {B : Type'} : (term462 B) = (term789 B).
Proof. exact (MK_COMB (@lem6163799 B) (@lem6163798 B)). Qed.
Lemma lem6163801 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6163802 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6163803 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6163808 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163809 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6163808 (type1400 B) B f x). Qed.
Lemma lem6163811 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem6163809 B (@neutral B) op). Qed.
Lemma lem6163816 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163817 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6163816 (type1400 B) B f x). Qed.
Lemma lem6163819 {B : Type'} (x : type402 B) (op : type1400 B) : (x op) = (@I ((B -> B -> B) -> B) x op).
Proof. exact (@lem6163817 B x op). Qed.
Lemma lem6163820 {B : Type'} (op : type1400 B) : (term746 B op) = (term747 B op).
Proof. exact (MK_COMB (@lem6163803 B op) (@lem6163811 B op)). Qed.
Lemma lem6163821 {B : Type'} (x : type402 B) (op : type1400 B) : (term790 B x op) = (term791 B x op).
Proof. exact (MK_COMB (@lem6163820 B op) (@lem6163819 B x op)). Qed.
Lemma lem6163823 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163824 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem6163823 B (B -> B) f x). Qed.
Lemma lem6163825 {B : Type'} (op : type1400 B) : (term747 B op) = (term749 B op).
Proof. exact (@lem6163824 B op (@I ((B -> B -> B) -> B) (@neutral B) op)). Qed.
Lemma lem6163826 {B : Type'} (x : type402 B) (op : type1400 B) : (@I ((B -> B -> B) -> B) x op) = (@I ((B -> B -> B) -> B) x op).
Proof. exact (eq_refl (@I ((B -> B -> B) -> B) x op)). Qed.
Lemma lem6163827 {B : Type'} (x : type402 B) (op : type1400 B) : (term791 B x op) = (term792 B x op).
Proof. exact (MK_COMB (@lem6163825 B op) (@lem6163826 B x op)). Qed.
Lemma lem6163829 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163830 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem6163829 B B f x). Qed.
Lemma lem6163831 {B : Type'} (x : type402 B) (op : type1400 B) : (term792 B x op) = (term793 B x op).
Proof. exact (@lem6163830 B (term749 B op) (@I ((B -> B -> B) -> B) x op)). Qed.
Lemma lem6163832 {B : Type'} (x : type402 B) (op : type1400 B) : (term791 B x op) = (term793 B x op).
Proof. exact (TRANS (@lem6163827 B x op) (@lem6163831 B x op)). Qed.
Lemma lem6163833 {B : Type'} (x : type402 B) (op : type1400 B) : (term790 B x op) = (term793 B x op).
Proof. exact (TRANS (@lem6163821 B x op) (@lem6163832 B x op)). Qed.
Lemma lem6163838 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163839 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6163838 (type1400 B) B f x). Qed.
Lemma lem6163841 {B : Type'} (x : type402 B) (op : type1400 B) : (x op) = (@I ((B -> B -> B) -> B) x op).
Proof. exact (@lem6163839 B x op). Qed.
Lemma lem6163842 {B : Type'} (x : type402 B) (op : type1400 B) : (term794 B x op) = (term795 B x op).
Proof. exact (MK_COMB (@lem6163802 B) (@lem6163833 B x op)). Qed.
Lemma lem6163843 {B : Type'} (x : type402 B) (op : type1400 B) : ((term790 B x op) = (x op)) = ((term793 B x op) = (@I ((B -> B -> B) -> B) x op)).
Proof. exact (MK_COMB (@lem6163842 B x op) (@lem6163841 B x op)). Qed.
Lemma lem6163844 {B : Type'} (x : type402 B) (op : type1400 B) : (term796 B x op) = (term797 B x op).
Proof. exact (MK_COMB (@lem6163801) (@lem6163843 B x op)). Qed.
Lemma lem6163845 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6163846 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6163847 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6163852 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163853 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6163852 (type1400 B) B f x). Qed.
Lemma lem6163855 {B : Type'} (x : type402 B) (op : type1400 B) : (x op) = (@I ((B -> B -> B) -> B) x op).
Proof. exact (@lem6163853 B x op). Qed.
Lemma lem6163856 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6163861 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163862 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6163861 (type1400 B) B f x). Qed.
Lemma lem6163864 {B : Type'} (y : type402 B) (op : type1400 B) : (y op) = (@I ((B -> B -> B) -> B) y op).
Proof. exact (@lem6163862 B y op). Qed.
Lemma lem6163869 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163870 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6163869 (type1400 B) B f x). Qed.
Lemma lem6163872 {B : Type'} (z : type402 B) (op : type1400 B) : (z op) = (@I ((B -> B -> B) -> B) z op).
Proof. exact (@lem6163870 B z op). Qed.
Lemma lem6163873 {B : Type'} (y : type402 B) (op : type1400 B) : (term798 B y op) = (term799 B y op).
Proof. exact (MK_COMB (@lem6163856 B op) (@lem6163864 B y op)). Qed.
Lemma lem6163874 {B : Type'} (y : type402 B) (z : type402 B) (op : type1400 B) : (term800 B y z op) = (term801 B y z op).
Proof. exact (MK_COMB (@lem6163873 B y op) (@lem6163872 B z op)). Qed.
Lemma lem6163876 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163877 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem6163876 B (B -> B) f x). Qed.
Lemma lem6163878 {B : Type'} (y : type402 B) (op : type1400 B) : (term799 B y op) = (term802 B y op).
Proof. exact (@lem6163877 B op (@I ((B -> B -> B) -> B) y op)). Qed.
Lemma lem6163879 {B : Type'} (z : type402 B) (op : type1400 B) : (@I ((B -> B -> B) -> B) z op) = (@I ((B -> B -> B) -> B) z op).
Proof. exact (eq_refl (@I ((B -> B -> B) -> B) z op)). Qed.
Lemma lem6163880 {B : Type'} (y : type402 B) (z : type402 B) (op : type1400 B) : (term801 B y z op) = (term803 B y z op).
Proof. exact (MK_COMB (@lem6163878 B y op) (@lem6163879 B z op)). Qed.
Lemma lem6163882 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163883 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem6163882 B B f x). Qed.
Lemma lem6163884 {B : Type'} (y : type402 B) (z : type402 B) (op : type1400 B) : (term803 B y z op) = (term804 B y z op).
Proof. exact (@lem6163883 B (term802 B y op) (@I ((B -> B -> B) -> B) z op)). Qed.
Lemma lem6163885 {B : Type'} (y : type402 B) (z : type402 B) (op : type1400 B) : (term801 B y z op) = (term804 B y z op).
Proof. exact (TRANS (@lem6163880 B y z op) (@lem6163884 B y z op)). Qed.
Lemma lem6163886 {B : Type'} (y : type402 B) (z : type402 B) (op : type1400 B) : (term800 B y z op) = (term804 B y z op).
Proof. exact (TRANS (@lem6163874 B y z op) (@lem6163885 B y z op)). Qed.
Lemma lem6163887 {B : Type'} (x : type402 B) (op : type1400 B) : (term798 B x op) = (term799 B x op).
Proof. exact (MK_COMB (@lem6163847 B op) (@lem6163855 B x op)). Qed.
Lemma lem6163888 {B : Type'} (x : type402 B) (y : type402 B) (z : type402 B) (op : type1400 B) : (term805 B x y z op) = (term806 B x y z op).
Proof. exact (MK_COMB (@lem6163887 B x op) (@lem6163886 B y z op)). Qed.
Lemma lem6163890 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163891 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem6163890 B (B -> B) f x). Qed.
Lemma lem6163892 {B : Type'} (x : type402 B) (op : type1400 B) : (term799 B x op) = (term802 B x op).
Proof. exact (@lem6163891 B op (@I ((B -> B -> B) -> B) x op)). Qed.
Lemma lem6163893 {B : Type'} (y : type402 B) (z : type402 B) (op : type1400 B) : (term804 B y z op) = (term804 B y z op).
Proof. exact (eq_refl (term804 B y z op)). Qed.
Lemma lem6163894 {B : Type'} (x : type402 B) (y : type402 B) (z : type402 B) (op : type1400 B) : (term806 B x y z op) = (term807 B x y z op).
Proof. exact (MK_COMB (@lem6163892 B x op) (@lem6163893 B y z op)). Qed.
Lemma lem6163896 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163897 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem6163896 B B f x). Qed.
Lemma lem6163898 {B : Type'} (x : type402 B) (y : type402 B) (z : type402 B) (op : type1400 B) : (term807 B x y z op) = (term808 B x y z op).
Proof. exact (@lem6163897 B (term802 B x op) (term804 B y z op)). Qed.
Lemma lem6163899 {B : Type'} (x : type402 B) (y : type402 B) (z : type402 B) (op : type1400 B) : (term806 B x y z op) = (term808 B x y z op).
Proof. exact (TRANS (@lem6163894 B x y z op) (@lem6163898 B x y z op)). Qed.
Lemma lem6163900 {B : Type'} (x : type402 B) (y : type402 B) (z : type402 B) (op : type1400 B) : (term805 B x y z op) = (term808 B x y z op).
Proof. exact (TRANS (@lem6163888 B x y z op) (@lem6163899 B x y z op)). Qed.
Lemma lem6163901 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6163902 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6163907 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163908 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6163907 (type1400 B) B f x). Qed.
Lemma lem6163910 {B : Type'} (x : type402 B) (op : type1400 B) : (x op) = (@I ((B -> B -> B) -> B) x op).
Proof. exact (@lem6163908 B x op). Qed.
Lemma lem6163915 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163916 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6163915 (type1400 B) B f x). Qed.
Lemma lem6163918 {B : Type'} (y : type402 B) (op : type1400 B) : (y op) = (@I ((B -> B -> B) -> B) y op).
Proof. exact (@lem6163916 B y op). Qed.
Lemma lem6163919 {B : Type'} (x : type402 B) (op : type1400 B) : (term798 B x op) = (term799 B x op).
Proof. exact (MK_COMB (@lem6163902 B op) (@lem6163910 B x op)). Qed.
Lemma lem6163920 {B : Type'} (x : type402 B) (y : type402 B) (op : type1400 B) : (term800 B x y op) = (term801 B x y op).
Proof. exact (MK_COMB (@lem6163919 B x op) (@lem6163918 B y op)). Qed.
Lemma lem6163922 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163923 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem6163922 B (B -> B) f x). Qed.
Lemma lem6163924 {B : Type'} (x : type402 B) (op : type1400 B) : (term799 B x op) = (term802 B x op).
Proof. exact (@lem6163923 B op (@I ((B -> B -> B) -> B) x op)). Qed.
Lemma lem6163925 {B : Type'} (y : type402 B) (op : type1400 B) : (@I ((B -> B -> B) -> B) y op) = (@I ((B -> B -> B) -> B) y op).
Proof. exact (eq_refl (@I ((B -> B -> B) -> B) y op)). Qed.
Lemma lem6163926 {B : Type'} (x : type402 B) (y : type402 B) (op : type1400 B) : (term801 B x y op) = (term803 B x y op).
Proof. exact (MK_COMB (@lem6163924 B x op) (@lem6163925 B y op)). Qed.
Lemma lem6163928 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163929 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem6163928 B B f x). Qed.
Lemma lem6163930 {B : Type'} (x : type402 B) (y : type402 B) (op : type1400 B) : (term803 B x y op) = (term804 B x y op).
Proof. exact (@lem6163929 B (term802 B x op) (@I ((B -> B -> B) -> B) y op)). Qed.
Lemma lem6163931 {B : Type'} (x : type402 B) (y : type402 B) (op : type1400 B) : (term801 B x y op) = (term804 B x y op).
Proof. exact (TRANS (@lem6163926 B x y op) (@lem6163930 B x y op)). Qed.
Lemma lem6163932 {B : Type'} (x : type402 B) (y : type402 B) (op : type1400 B) : (term800 B x y op) = (term804 B x y op).
Proof. exact (TRANS (@lem6163920 B x y op) (@lem6163931 B x y op)). Qed.
Lemma lem6163937 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163938 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6163937 (type1400 B) B f x). Qed.
Lemma lem6163940 {B : Type'} (z : type402 B) (op : type1400 B) : (z op) = (@I ((B -> B -> B) -> B) z op).
Proof. exact (@lem6163938 B z op). Qed.
Lemma lem6163941 {B : Type'} (x : type402 B) (y : type402 B) (op : type1400 B) : (term809 B x y op) = (term810 B x y op).
Proof. exact (MK_COMB (@lem6163901 B op) (@lem6163932 B x y op)). Qed.
Lemma lem6163942 {B : Type'} (x : type402 B) (y : type402 B) (z : type402 B) (op : type1400 B) : (term811 B x y z op) = (term812 B x y z op).
Proof. exact (MK_COMB (@lem6163941 B x y op) (@lem6163940 B z op)). Qed.
Lemma lem6163944 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163945 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem6163944 B (B -> B) f x). Qed.
Lemma lem6163946 {B : Type'} (x : type402 B) (y : type402 B) (op : type1400 B) : (term810 B x y op) = (term813 B x y op).
Proof. exact (@lem6163945 B op (term804 B x y op)). Qed.
Lemma lem6163947 {B : Type'} (z : type402 B) (op : type1400 B) : (@I ((B -> B -> B) -> B) z op) = (@I ((B -> B -> B) -> B) z op).
Proof. exact (eq_refl (@I ((B -> B -> B) -> B) z op)). Qed.
Lemma lem6163948 {B : Type'} (x : type402 B) (y : type402 B) (z : type402 B) (op : type1400 B) : (term812 B x y z op) = (term814 B x y z op).
Proof. exact (MK_COMB (@lem6163946 B x y op) (@lem6163947 B z op)). Qed.
Lemma lem6163950 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163951 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem6163950 B B f x). Qed.
Lemma lem6163952 {B : Type'} (x : type402 B) (y : type402 B) (z : type402 B) (op : type1400 B) : (term814 B x y z op) = (term815 B x y z op).
Proof. exact (@lem6163951 B (term813 B x y op) (@I ((B -> B -> B) -> B) z op)). Qed.
Lemma lem6163953 {B : Type'} (x : type402 B) (y : type402 B) (z : type402 B) (op : type1400 B) : (term812 B x y z op) = (term815 B x y z op).
Proof. exact (TRANS (@lem6163948 B x y z op) (@lem6163952 B x y z op)). Qed.
Lemma lem6163954 {B : Type'} (x : type402 B) (y : type402 B) (z : type402 B) (op : type1400 B) : (term811 B x y z op) = (term815 B x y z op).
Proof. exact (TRANS (@lem6163942 B x y z op) (@lem6163953 B x y z op)). Qed.
Lemma lem6163955 {B : Type'} (x : type402 B) (y : type402 B) (z : type402 B) (op : type1400 B) : (term816 B x y z op) = (term817 B x y z op).
Proof. exact (MK_COMB (@lem6163846 B) (@lem6163900 B x y z op)). Qed.
Lemma lem6163956 {B : Type'} (x : type402 B) (y : type402 B) (z : type402 B) (op : type1400 B) : ((term805 B x y z op) = (term811 B x y z op)) = ((term808 B x y z op) = (term815 B x y z op)).
Proof. exact (MK_COMB (@lem6163955 B x y z op) (@lem6163954 B x y z op)). Qed.
Lemma lem6163957 {B : Type'} (x : type402 B) (y : type402 B) (z : type402 B) (op : type1400 B) : (term818 B x y z op) = (term819 B x y z op).
Proof. exact (MK_COMB (@lem6163845) (@lem6163956 B x y z op)). Qed.
Lemma lem6163958 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6163959 {B : Type'} (x : type402 B) (y : type402 B) (z : type402 B) (op : type1400 B) : (term820 B x y z op) = (term821 B x y z op).
Proof. exact (MK_COMB (@lem6163958) (@lem6163957 B x y z op)). Qed.
Lemma lem6163960 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (op : type1400 B) : (term822 B y z x op) = (term823 B y z x op).
Proof. exact (MK_COMB (@lem6163959 B x y z op) (@lem6163844 B x op)). Qed.
Lemma lem6163961 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6163962 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6163963 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6163968 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163969 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6163968 (type1400 B) B f x). Qed.
Lemma lem6163971 {B : Type'} (x : type402 B) (op : type1400 B) : (x op) = (@I ((B -> B -> B) -> B) x op).
Proof. exact (@lem6163969 B x op). Qed.
Lemma lem6163976 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163977 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6163976 (type1400 B) B f x). Qed.
Lemma lem6163979 {B : Type'} (y : type402 B) (op : type1400 B) : (y op) = (@I ((B -> B -> B) -> B) y op).
Proof. exact (@lem6163977 B y op). Qed.
Lemma lem6163980 {B : Type'} (x : type402 B) (op : type1400 B) : (term798 B x op) = (term799 B x op).
Proof. exact (MK_COMB (@lem6163963 B op) (@lem6163971 B x op)). Qed.
Lemma lem6163981 {B : Type'} (x : type402 B) (y : type402 B) (op : type1400 B) : (term800 B x y op) = (term801 B x y op).
Proof. exact (MK_COMB (@lem6163980 B x op) (@lem6163979 B y op)). Qed.
Lemma lem6163983 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163984 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem6163983 B (B -> B) f x). Qed.
Lemma lem6163985 {B : Type'} (x : type402 B) (op : type1400 B) : (term799 B x op) = (term802 B x op).
Proof. exact (@lem6163984 B op (@I ((B -> B -> B) -> B) x op)). Qed.
Lemma lem6163986 {B : Type'} (y : type402 B) (op : type1400 B) : (@I ((B -> B -> B) -> B) y op) = (@I ((B -> B -> B) -> B) y op).
Proof. exact (eq_refl (@I ((B -> B -> B) -> B) y op)). Qed.
Lemma lem6163987 {B : Type'} (x : type402 B) (y : type402 B) (op : type1400 B) : (term801 B x y op) = (term803 B x y op).
Proof. exact (MK_COMB (@lem6163985 B x op) (@lem6163986 B y op)). Qed.
Lemma lem6163989 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6163990 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem6163989 B B f x). Qed.
Lemma lem6163991 {B : Type'} (x : type402 B) (y : type402 B) (op : type1400 B) : (term803 B x y op) = (term804 B x y op).
Proof. exact (@lem6163990 B (term802 B x op) (@I ((B -> B -> B) -> B) y op)). Qed.
Lemma lem6163992 {B : Type'} (x : type402 B) (y : type402 B) (op : type1400 B) : (term801 B x y op) = (term804 B x y op).
Proof. exact (TRANS (@lem6163987 B x y op) (@lem6163991 B x y op)). Qed.
Lemma lem6163993 {B : Type'} (x : type402 B) (y : type402 B) (op : type1400 B) : (term800 B x y op) = (term804 B x y op).
Proof. exact (TRANS (@lem6163981 B x y op) (@lem6163992 B x y op)). Qed.
Lemma lem6163994 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6163999 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164000 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6163999 (type1400 B) B f x). Qed.
Lemma lem6164002 {B : Type'} (y : type402 B) (op : type1400 B) : (y op) = (@I ((B -> B -> B) -> B) y op).
Proof. exact (@lem6164000 B y op). Qed.
Lemma lem6164007 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164008 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6164007 (type1400 B) B f x). Qed.
Lemma lem6164010 {B : Type'} (x : type402 B) (op : type1400 B) : (x op) = (@I ((B -> B -> B) -> B) x op).
Proof. exact (@lem6164008 B x op). Qed.
Lemma lem6164011 {B : Type'} (y : type402 B) (op : type1400 B) : (term798 B y op) = (term799 B y op).
Proof. exact (MK_COMB (@lem6163994 B op) (@lem6164002 B y op)). Qed.
Lemma lem6164012 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term800 B y x op) = (term801 B y x op).
Proof. exact (MK_COMB (@lem6164011 B y op) (@lem6164010 B x op)). Qed.
Lemma lem6164014 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164015 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem6164014 B (B -> B) f x). Qed.
Lemma lem6164016 {B : Type'} (y : type402 B) (op : type1400 B) : (term799 B y op) = (term802 B y op).
Proof. exact (@lem6164015 B op (@I ((B -> B -> B) -> B) y op)). Qed.
Lemma lem6164017 {B : Type'} (x : type402 B) (op : type1400 B) : (@I ((B -> B -> B) -> B) x op) = (@I ((B -> B -> B) -> B) x op).
Proof. exact (eq_refl (@I ((B -> B -> B) -> B) x op)). Qed.
Lemma lem6164018 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term801 B y x op) = (term803 B y x op).
Proof. exact (MK_COMB (@lem6164016 B y op) (@lem6164017 B x op)). Qed.
Lemma lem6164020 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164021 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem6164020 B B f x). Qed.
Lemma lem6164022 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term803 B y x op) = (term804 B y x op).
Proof. exact (@lem6164021 B (term802 B y op) (@I ((B -> B -> B) -> B) x op)). Qed.
Lemma lem6164023 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term801 B y x op) = (term804 B y x op).
Proof. exact (TRANS (@lem6164018 B y x op) (@lem6164022 B y x op)). Qed.
Lemma lem6164024 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term800 B y x op) = (term804 B y x op).
Proof. exact (TRANS (@lem6164012 B y x op) (@lem6164023 B y x op)). Qed.
Lemma lem6164025 {B : Type'} (x : type402 B) (y : type402 B) (op : type1400 B) : (term824 B x y op) = (term825 B x y op).
Proof. exact (MK_COMB (@lem6163962 B) (@lem6163993 B x y op)). Qed.
Lemma lem6164026 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : ((term800 B x y op) = (term800 B y x op)) = ((term804 B x y op) = (term804 B y x op)).
Proof. exact (MK_COMB (@lem6164025 B x y op) (@lem6164024 B y x op)). Qed.
Lemma lem6164027 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term826 B y x op) = (term827 B y x op).
Proof. exact (MK_COMB (@lem6163961) (@lem6164026 B y x op)). Qed.
Lemma lem6164028 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6164029 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term828 B y x op) = (term829 B y x op).
Proof. exact (MK_COMB (@lem6164028) (@lem6164027 B y x op)). Qed.
Lemma lem6164030 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (op : type1400 B) : (term830 B y z x op) = (term831 B y z x op).
Proof. exact (MK_COMB (@lem6164029 B y x op) (@lem6163960 B y z x op)). Qed.
Lemma lem6164035 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164036 {B : Type'} (f : type403 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> Prop) f x).
Proof. exact (@lem6164035 (type1400 B) Prop f x). Qed.
Lemma lem6164038 {B : Type'} (op : type1400 B) : (@monoidal B op) = (@I ((B -> B -> B) -> Prop) (@monoidal B) op).
Proof. exact (@lem6164036 B (@monoidal B) op). Qed.
Lemma lem6164039 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6164040 {B : Type'} (op : type1400 B) : (term431 B op) = (term832 B op).
Proof. exact (MK_COMB (@lem6164039) (@lem6164038 B op)). Qed.
Lemma lem6164041 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (op : type1400 B) : (term679 B y z x op) = (term833 B y z x op).
Proof. exact (MK_COMB (@lem6164040 B op) (@lem6164030 B y z x op)). Qed.
Lemma lem6164042 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) : (term681 B y z x) = (term834 B y z x).
Proof. exact (fun_ext (fun op : type1400 B => @lem6164041 B y z x op)). Qed.
Lemma lem6164043 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6164044 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) : (term683 B y z x) = (term835 B y z x).
Proof. exact (MK_COMB (@lem6164043 B) (@lem6164042 B y z x)). Qed.
Lemma lem6164045 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6164046 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) : (term736 B y z x) = (term836 B y z x).
Proof. exact (MK_COMB (@lem6164045) (@lem6164044 B y z x)). Qed.
Lemma lem6164047 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) : (term738 B y z x) = (term837 B y z x).
Proof. exact (MK_COMB (@lem6164046 B y z x) (@lem6163800 B)). Qed.
Lemma lem6164048 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term738 B y z x) : term837 B y z x.
Proof. exact (EQ_MP (@lem6164047 B y z x) (@lem6163548 B y z x h1)). Qed.
Lemma lem6164049 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6164050 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6164051 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6164056 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164057 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6164056 A B f x). Qed.
Lemma lem6164059 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (@I (A -> B) f x').
Proof. exact (@lem6164057 A B f x'). Qed.
Lemma lem6164064 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164065 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6164064 A B f x). Qed.
Lemma lem6164067 {A B : Type'} (g : A -> B) (x' : A) : (g x') = (@I (A -> B) g x').
Proof. exact (@lem6164065 A B g x'). Qed.
Lemma lem6164068 {A B : Type'} (op : type1400 B) (f : A -> B) (x' : A) : (term838 A B op f x') = (term839 A B op f x').
Proof. exact (MK_COMB (@lem6164051 B op) (@lem6164059 A B f x')). Qed.
Lemma lem6164069 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x' : A) : (term125 A B op f g x') = (term840 A B op f g x').
Proof. exact (MK_COMB (@lem6164068 A B op f x') (@lem6164067 A B g x')). Qed.
Lemma lem6164071 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164072 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem6164071 B (B -> B) f x). Qed.
Lemma lem6164073 {A B : Type'} (op : type1400 B) (f : A -> B) (x' : A) : (term839 A B op f x') = (term841 A B op f x').
Proof. exact (@lem6164072 B op (@I (A -> B) f x')). Qed.
Lemma lem6164074 {A B : Type'} (g : A -> B) (x' : A) : (@I (A -> B) g x') = (@I (A -> B) g x').
Proof. exact (eq_refl (@I (A -> B) g x')). Qed.
Lemma lem6164075 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x' : A) : (term840 A B op f g x') = (term842 A B op f g x').
Proof. exact (MK_COMB (@lem6164073 A B op f x') (@lem6164074 A B g x')). Qed.
Lemma lem6164077 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164078 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem6164077 B B f x). Qed.
Lemma lem6164079 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x' : A) : (term842 A B op f g x') = (term843 A B op f g x').
Proof. exact (@lem6164078 B (term841 A B op f x') (@I (A -> B) g x')). Qed.
Lemma lem6164080 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x' : A) : (term840 A B op f g x') = (term843 A B op f g x').
Proof. exact (TRANS (@lem6164075 A B op f g x') (@lem6164079 A B op f g x')). Qed.
Lemma lem6164081 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x' : A) : (term125 A B op f g x') = (term843 A B op f g x').
Proof. exact (TRANS (@lem6164069 A B op f g x') (@lem6164080 A B op f g x')). Qed.
Lemma lem6164086 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164087 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6164086 (type1400 B) B f x). Qed.
Lemma lem6164089 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem6164087 B (@neutral B) op). Qed.
Lemma lem6164090 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x' : A) : (term129 A B op f g x') = (term844 A B op f g x').
Proof. exact (MK_COMB (@lem6164050 B) (@lem6164081 A B op f g x')). Qed.
Lemma lem6164091 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) : ((term125 A B op f g x') = (@neutral B op)) = ((term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (MK_COMB (@lem6164090 A B op f g x') (@lem6164089 B op)). Qed.
Lemma lem6164092 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) : (term131 A B f g x' op) = (term845 A B f g x' op).
Proof. exact (MK_COMB (@lem6164049) (@lem6164091 A B f g x' op)). Qed.
Lemma lem6164093 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6164094 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6164099 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164100 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6164099 A B f x). Qed.
Lemma lem6164102 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (@I (A -> B) f x').
Proof. exact (@lem6164100 A B f x'). Qed.
Lemma lem6164107 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164108 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6164107 A B f x). Qed.
Lemma lem6164110 {A B : Type'} (g : A -> B) (x' : A) : (g x') = (@I (A -> B) g x').
Proof. exact (@lem6164108 A B g x'). Qed.
Lemma lem6164111 {A B : Type'} (op : type1400 B) (f : A -> B) (x' : A) : (term838 A B op f x') = (term839 A B op f x').
Proof. exact (MK_COMB (@lem6164094 B op) (@lem6164102 A B f x')). Qed.
Lemma lem6164112 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x' : A) : (term125 A B op f g x') = (term840 A B op f g x').
Proof. exact (MK_COMB (@lem6164111 A B op f x') (@lem6164110 A B g x')). Qed.
Lemma lem6164114 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164115 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem6164114 B (B -> B) f x). Qed.
Lemma lem6164116 {A B : Type'} (op : type1400 B) (f : A -> B) (x' : A) : (term839 A B op f x') = (term841 A B op f x').
Proof. exact (@lem6164115 B op (@I (A -> B) f x')). Qed.
Lemma lem6164117 {A B : Type'} (g : A -> B) (x' : A) : (@I (A -> B) g x') = (@I (A -> B) g x').
Proof. exact (eq_refl (@I (A -> B) g x')). Qed.
Lemma lem6164118 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x' : A) : (term840 A B op f g x') = (term842 A B op f g x').
Proof. exact (MK_COMB (@lem6164116 A B op f x') (@lem6164117 A B g x')). Qed.
Lemma lem6164120 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164121 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem6164120 B B f x). Qed.
Lemma lem6164122 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x' : A) : (term842 A B op f g x') = (term843 A B op f g x').
Proof. exact (@lem6164121 B (term841 A B op f x') (@I (A -> B) g x')). Qed.
Lemma lem6164123 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x' : A) : (term840 A B op f g x') = (term843 A B op f g x').
Proof. exact (TRANS (@lem6164118 A B op f g x') (@lem6164122 A B op f g x')). Qed.
Lemma lem6164124 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x' : A) : (term125 A B op f g x') = (term843 A B op f g x').
Proof. exact (TRANS (@lem6164112 A B op f g x') (@lem6164123 A B op f g x')). Qed.
Lemma lem6164129 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164130 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6164129 (type1400 B) B f x). Qed.
Lemma lem6164132 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem6164130 B (@neutral B) op). Qed.
Lemma lem6164133 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x' : A) : (term129 A B op f g x') = (term844 A B op f g x').
Proof. exact (MK_COMB (@lem6164093 B) (@lem6164124 A B op f g x')). Qed.
Lemma lem6164134 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) : ((term125 A B op f g x') = (@neutral B op)) = ((term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (MK_COMB (@lem6164133 A B op f g x') (@lem6164132 B op)). Qed.
Lemma lem6164135 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6164142 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164143 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6164142 A (type686 A) f x). Qed.
Lemma lem6164144 {A : Type'} (x' : A) : (@IN A x') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x').
Proof. exact (@lem6164143 A (@IN A) x'). Qed.
Lemma lem6164145 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6164146 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s).
Proof. exact (MK_COMB (@lem6164144 A x') (@lem6164145 A s)). Qed.
Lemma lem6164148 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164149 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6164148 (A -> Prop) Prop f x). Qed.
Lemma lem6164150 {A : Type'} (x' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s) = (term846 A x' s).
Proof. exact (@lem6164149 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x') s). Qed.
Lemma lem6164152 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (term846 A x' s).
Proof. exact (TRANS (@lem6164146 A x' s) (@lem6164150 A x' s)). Qed.
Lemma lem6164153 {A : Type'} (x' : A) (s : A -> Prop) : (term847 A x' s) = (term848 A x' s).
Proof. exact (MK_COMB (@lem6164135) (@lem6164152 A x' s)). Qed.
Lemma lem6164154 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6164155 {A : Type'} (x' : A) (s : A -> Prop) : (term312 A x' s) = (term849 A x' s).
Proof. exact (MK_COMB (@lem6164154) (@lem6164153 A x' s)). Qed.
Lemma lem6164156 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) : (term336 A B s f g x' op) = (term850 A B s f g x' op).
Proof. exact (MK_COMB (@lem6164155 A x' s) (@lem6164134 A B f g x' op)). Qed.
Lemma lem6164157 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6164158 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6164163 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164164 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6164163 A B f x). Qed.
Lemma lem6164166 {A B : Type'} (g : A -> B) (x' : A) : (g x') = (@I (A -> B) g x').
Proof. exact (@lem6164164 A B g x'). Qed.
Lemma lem6164171 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164172 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6164171 (type1400 B) B f x). Qed.
Lemma lem6164174 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem6164172 B (@neutral B) op). Qed.
Lemma lem6164175 {A B : Type'} (g : A -> B) (x' : A) : (term851 A B g x') = (term852 A B g x').
Proof. exact (MK_COMB (@lem6164158 B) (@lem6164166 A B g x')). Qed.
Lemma lem6164176 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) : ((g x') = (@neutral B op)) = ((@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (MK_COMB (@lem6164175 A B g x') (@lem6164174 B op)). Qed.
Lemma lem6164177 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) : (term315 A B g x' op) = (term853 A B g x' op).
Proof. exact (MK_COMB (@lem6164157) (@lem6164176 A B g x' op)). Qed.
Lemma lem6164184 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164185 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6164184 A (type686 A) f x). Qed.
Lemma lem6164186 {A : Type'} (x' : A) : (@IN A x') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x').
Proof. exact (@lem6164185 A (@IN A) x'). Qed.
Lemma lem6164187 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6164188 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s).
Proof. exact (MK_COMB (@lem6164186 A x') (@lem6164187 A s)). Qed.
Lemma lem6164190 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164191 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6164190 (A -> Prop) Prop f x). Qed.
Lemma lem6164192 {A : Type'} (x' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s) = (term846 A x' s).
Proof. exact (@lem6164191 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x') s). Qed.
Lemma lem6164194 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (term846 A x' s).
Proof. exact (TRANS (@lem6164188 A x' s) (@lem6164192 A x' s)). Qed.
Lemma lem6164195 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6164196 {A : Type'} (x' : A) (s : A -> Prop) : (term132 A x' s) = (term854 A x' s).
Proof. exact (MK_COMB (@lem6164195) (@lem6164194 A x' s)). Qed.
Lemma lem6164197 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) : (term168 A B s g x' op) = (term855 A B s g x' op).
Proof. exact (MK_COMB (@lem6164196 A x' s) (@lem6164177 A B g x' op)). Qed.
Lemma lem6164198 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6164199 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6164204 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164205 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6164204 A B f x). Qed.
Lemma lem6164207 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (@I (A -> B) f x').
Proof. exact (@lem6164205 A B f x'). Qed.
Lemma lem6164212 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164213 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6164212 (type1400 B) B f x). Qed.
Lemma lem6164215 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem6164213 B (@neutral B) op). Qed.
Lemma lem6164216 {A B : Type'} (f : A -> B) (x' : A) : (term851 A B f x') = (term852 A B f x').
Proof. exact (MK_COMB (@lem6164199 B) (@lem6164207 A B f x')). Qed.
Lemma lem6164217 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : ((f x') = (@neutral B op)) = ((@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (MK_COMB (@lem6164216 A B f x') (@lem6164215 B op)). Qed.
Lemma lem6164218 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : (term315 A B f x' op) = (term853 A B f x' op).
Proof. exact (MK_COMB (@lem6164198) (@lem6164217 A B f x' op)). Qed.
Lemma lem6164225 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164226 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6164225 A (type686 A) f x). Qed.
Lemma lem6164227 {A : Type'} (x' : A) : (@IN A x') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x').
Proof. exact (@lem6164226 A (@IN A) x'). Qed.
Lemma lem6164228 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6164229 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s).
Proof. exact (MK_COMB (@lem6164227 A x') (@lem6164228 A s)). Qed.
Lemma lem6164231 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164232 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6164231 (A -> Prop) Prop f x). Qed.
Lemma lem6164233 {A : Type'} (x' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s) = (term846 A x' s).
Proof. exact (@lem6164232 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x') s). Qed.
Lemma lem6164235 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (term846 A x' s).
Proof. exact (TRANS (@lem6164229 A x' s) (@lem6164233 A x' s)). Qed.
Lemma lem6164236 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6164237 {A : Type'} (x' : A) (s : A -> Prop) : (term132 A x' s) = (term854 A x' s).
Proof. exact (MK_COMB (@lem6164236) (@lem6164235 A x' s)). Qed.
Lemma lem6164238 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) : (term168 A B s f x' op) = (term855 A B s f x' op).
Proof. exact (MK_COMB (@lem6164237 A x' s) (@lem6164218 A B f x' op)). Qed.
Lemma lem6164239 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6164240 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) : (term183 A B s f x' op) = (term856 A B s f x' op).
Proof. exact (MK_COMB (@lem6164239) (@lem6164238 A B s f x' op)). Qed.
Lemma lem6164241 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) : (term184 A B f s g x' op) = (term857 A B f s g x' op).
Proof. exact (MK_COMB (@lem6164240 A B s f x' op) (@lem6164197 A B s g x' op)). Qed.
Lemma lem6164242 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6164243 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) : (term193 A B f s g x' op) = (term858 A B f s g x' op).
Proof. exact (MK_COMB (@lem6164242) (@lem6164241 A B f s g x' op)). Qed.
Lemma lem6164244 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) : (term337 A B s f g x' op) = (term859 A B s f g x' op).
Proof. exact (MK_COMB (@lem6164243 A B f s g x' op) (@lem6164156 A B s f g x' op)). Qed.
Lemma lem6164245 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6164246 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) : (term339 A B s f g x' op) = (term860 A B s f g x' op).
Proof. exact (MK_COMB (@lem6164245) (@lem6164244 A B s f g x' op)). Qed.
Lemma lem6164247 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) : (term341 A B s f g x' op) = (term861 A B s f g x' op).
Proof. exact (MK_COMB (@lem6164246 A B s f g x' op) (@lem6164092 A B f g x' op)). Qed.
Lemma lem6164248 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6164253 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164254 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6164253 A B f x). Qed.
Lemma lem6164256 {A B : Type'} (g : A -> B) (x' : A) : (g x') = (@I (A -> B) g x').
Proof. exact (@lem6164254 A B g x'). Qed.
Lemma lem6164261 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164262 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6164261 (type1400 B) B f x). Qed.
Lemma lem6164264 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem6164262 B (@neutral B) op). Qed.
Lemma lem6164265 {A B : Type'} (g : A -> B) (x' : A) : (term851 A B g x') = (term852 A B g x').
Proof. exact (MK_COMB (@lem6164248 B) (@lem6164256 A B g x')). Qed.
Lemma lem6164266 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) : ((g x') = (@neutral B op)) = ((@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (MK_COMB (@lem6164265 A B g x') (@lem6164264 B op)). Qed.
Lemma lem6164267 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6164274 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164275 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6164274 A (type686 A) f x). Qed.
Lemma lem6164276 {A : Type'} (x' : A) : (@IN A x') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x').
Proof. exact (@lem6164275 A (@IN A) x'). Qed.
Lemma lem6164277 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6164278 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s).
Proof. exact (MK_COMB (@lem6164276 A x') (@lem6164277 A s)). Qed.
Lemma lem6164280 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164281 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6164280 (A -> Prop) Prop f x). Qed.
Lemma lem6164282 {A : Type'} (x' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s) = (term846 A x' s).
Proof. exact (@lem6164281 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x') s). Qed.
Lemma lem6164284 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (term846 A x' s).
Proof. exact (TRANS (@lem6164278 A x' s) (@lem6164282 A x' s)). Qed.
Lemma lem6164285 {A : Type'} (x' : A) (s : A -> Prop) : (term847 A x' s) = (term848 A x' s).
Proof. exact (MK_COMB (@lem6164267) (@lem6164284 A x' s)). Qed.
Lemma lem6164286 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6164287 {A : Type'} (x' : A) (s : A -> Prop) : (term312 A x' s) = (term849 A x' s).
Proof. exact (MK_COMB (@lem6164286) (@lem6164285 A x' s)). Qed.
Lemma lem6164288 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) : (term314 A B s g x' op) = (term862 A B s g x' op).
Proof. exact (MK_COMB (@lem6164287 A x' s) (@lem6164266 A B g x' op)). Qed.
Lemma lem6164289 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6164294 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164295 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6164294 A B f x). Qed.
Lemma lem6164297 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (@I (A -> B) f x').
Proof. exact (@lem6164295 A B f x'). Qed.
Lemma lem6164302 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164303 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6164302 (type1400 B) B f x). Qed.
Lemma lem6164305 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem6164303 B (@neutral B) op). Qed.
Lemma lem6164306 {A B : Type'} (f : A -> B) (x' : A) : (term851 A B f x') = (term852 A B f x').
Proof. exact (MK_COMB (@lem6164289 B) (@lem6164297 A B f x')). Qed.
Lemma lem6164307 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : ((f x') = (@neutral B op)) = ((@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (MK_COMB (@lem6164306 A B f x') (@lem6164305 B op)). Qed.
Lemma lem6164308 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6164315 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164316 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6164315 A (type686 A) f x). Qed.
Lemma lem6164317 {A : Type'} (x' : A) : (@IN A x') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x').
Proof. exact (@lem6164316 A (@IN A) x'). Qed.
Lemma lem6164318 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6164319 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s).
Proof. exact (MK_COMB (@lem6164317 A x') (@lem6164318 A s)). Qed.
Lemma lem6164321 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164322 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6164321 (A -> Prop) Prop f x). Qed.
Lemma lem6164323 {A : Type'} (x' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s) = (term846 A x' s).
Proof. exact (@lem6164322 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x') s). Qed.
Lemma lem6164325 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (term846 A x' s).
Proof. exact (TRANS (@lem6164319 A x' s) (@lem6164323 A x' s)). Qed.
Lemma lem6164326 {A : Type'} (x' : A) (s : A -> Prop) : (term847 A x' s) = (term848 A x' s).
Proof. exact (MK_COMB (@lem6164308) (@lem6164325 A x' s)). Qed.
Lemma lem6164327 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6164328 {A : Type'} (x' : A) (s : A -> Prop) : (term312 A x' s) = (term849 A x' s).
Proof. exact (MK_COMB (@lem6164327) (@lem6164326 A x' s)). Qed.
Lemma lem6164329 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) : (term314 A B s f x' op) = (term862 A B s f x' op).
Proof. exact (MK_COMB (@lem6164328 A x' s) (@lem6164307 A B f x' op)). Qed.
Lemma lem6164330 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6164331 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) : (term317 A B s f x' op) = (term863 A B s f x' op).
Proof. exact (MK_COMB (@lem6164330) (@lem6164329 A B s f x' op)). Qed.
Lemma lem6164332 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) : (term319 A B f s g x' op) = (term864 A B f s g x' op).
Proof. exact (MK_COMB (@lem6164331 A B s f x' op) (@lem6164288 A B s g x' op)). Qed.
Lemma lem6164333 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6164334 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6164335 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6164340 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164341 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6164340 A B f x). Qed.
Lemma lem6164343 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (@I (A -> B) f x').
Proof. exact (@lem6164341 A B f x'). Qed.
Lemma lem6164348 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164349 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6164348 A B f x). Qed.
Lemma lem6164351 {A B : Type'} (g : A -> B) (x' : A) : (g x') = (@I (A -> B) g x').
Proof. exact (@lem6164349 A B g x'). Qed.
Lemma lem6164352 {A B : Type'} (op : type1400 B) (f : A -> B) (x' : A) : (term838 A B op f x') = (term839 A B op f x').
Proof. exact (MK_COMB (@lem6164335 B op) (@lem6164343 A B f x')). Qed.
Lemma lem6164353 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x' : A) : (term125 A B op f g x') = (term840 A B op f g x').
Proof. exact (MK_COMB (@lem6164352 A B op f x') (@lem6164351 A B g x')). Qed.
Lemma lem6164355 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164356 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem6164355 B (B -> B) f x). Qed.
Lemma lem6164357 {A B : Type'} (op : type1400 B) (f : A -> B) (x' : A) : (term839 A B op f x') = (term841 A B op f x').
Proof. exact (@lem6164356 B op (@I (A -> B) f x')). Qed.
Lemma lem6164358 {A B : Type'} (g : A -> B) (x' : A) : (@I (A -> B) g x') = (@I (A -> B) g x').
Proof. exact (eq_refl (@I (A -> B) g x')). Qed.
Lemma lem6164359 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x' : A) : (term840 A B op f g x') = (term842 A B op f g x').
Proof. exact (MK_COMB (@lem6164357 A B op f x') (@lem6164358 A B g x')). Qed.
Lemma lem6164361 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164362 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem6164361 B B f x). Qed.
Lemma lem6164363 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x' : A) : (term842 A B op f g x') = (term843 A B op f g x').
Proof. exact (@lem6164362 B (term841 A B op f x') (@I (A -> B) g x')). Qed.
Lemma lem6164364 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x' : A) : (term840 A B op f g x') = (term843 A B op f g x').
Proof. exact (TRANS (@lem6164359 A B op f g x') (@lem6164363 A B op f g x')). Qed.
Lemma lem6164365 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x' : A) : (term125 A B op f g x') = (term843 A B op f g x').
Proof. exact (TRANS (@lem6164353 A B op f g x') (@lem6164364 A B op f g x')). Qed.
Lemma lem6164370 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164371 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6164370 (type1400 B) B f x). Qed.
Lemma lem6164373 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem6164371 B (@neutral B) op). Qed.
Lemma lem6164374 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x' : A) : (term129 A B op f g x') = (term844 A B op f g x').
Proof. exact (MK_COMB (@lem6164334 B) (@lem6164365 A B op f g x')). Qed.
Lemma lem6164375 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) : ((term125 A B op f g x') = (@neutral B op)) = ((term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (MK_COMB (@lem6164374 A B op f g x') (@lem6164373 B op)). Qed.
Lemma lem6164376 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) : (term131 A B f g x' op) = (term845 A B f g x' op).
Proof. exact (MK_COMB (@lem6164333) (@lem6164375 A B f g x' op)). Qed.
Lemma lem6164383 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164384 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6164383 A (type686 A) f x). Qed.
Lemma lem6164385 {A : Type'} (x' : A) : (@IN A x') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x').
Proof. exact (@lem6164384 A (@IN A) x'). Qed.
Lemma lem6164386 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6164387 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s).
Proof. exact (MK_COMB (@lem6164385 A x') (@lem6164386 A s)). Qed.
Lemma lem6164389 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6164390 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6164389 (A -> Prop) Prop f x). Qed.
Lemma lem6164391 {A : Type'} (x' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s) = (term846 A x' s).
Proof. exact (@lem6164390 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x') s). Qed.
Lemma lem6164393 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (term846 A x' s).
Proof. exact (TRANS (@lem6164387 A x' s) (@lem6164391 A x' s)). Qed.
Lemma lem6164394 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6164395 {A : Type'} (x' : A) (s : A -> Prop) : (term132 A x' s) = (term854 A x' s).
Proof. exact (MK_COMB (@lem6164394) (@lem6164393 A x' s)). Qed.
Lemma lem6164396 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) : (term134 A B s f g x' op) = (term865 A B s f g x' op).
Proof. exact (MK_COMB (@lem6164395 A x' s) (@lem6164376 A B f g x' op)). Qed.
Lemma lem6164397 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6164398 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) : (term321 A B s f g x' op) = (term866 A B s f g x' op).
Proof. exact (MK_COMB (@lem6164397) (@lem6164396 A B s f g x' op)). Qed.
Lemma lem6164399 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) : (term323 A B f s g x' op) = (term867 A B f s g x' op).
Proof. exact (MK_COMB (@lem6164398 A B s f g x' op) (@lem6164332 A B f s g x' op)). Qed.
Lemma lem6164400 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6164401 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) : (term368 A B f s g x' op) = (term868 A B f s g x' op).
Proof. exact (MK_COMB (@lem6164400) (@lem6164399 A B f s g x' op)). Qed.
Lemma lem6164402 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) : (term370 A B s f g x' op) = (term869 A B s f g x' op).
Proof. exact (MK_COMB (@lem6164401 A B f s g x' op) (@lem6164247 A B s f g x' op)). Qed.
Lemma lem6164403 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term370 A B s f g x' op) : term869 A B s f g x' op.
Proof. exact (EQ_MP (@lem6164402 A B s f g x' op) (@lem6163549 A B s f g x' op h1)). Qed.
Lemma lem6164404 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term738 B y z x) : term789 B.
Proof. exact (proj2 (@lem6164048 B y z x h1)). Qed.
Lemma lem6164406 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term867 A B f s g x' op) : term867 A B f s g x' op.
Proof. exact (h1). Qed.
Lemma lem6164407 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term861 A B s f g x' op) : term861 A B s f g x' op.
Proof. exact (h1). Qed.
Lemma lem6164408 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term867 A B f s g x' op) : term864 A B f s g x' op.
Proof. exact (proj2 (@lem6164406 A B f s g x' op h1)). Qed.
Lemma lem6164409 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term867 A B f s g x' op) : term865 A B s f g x' op.
Proof. exact (proj1 (@lem6164406 A B f s g x' op h1)). Qed.
Lemma lem6164410 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term867 A B f s g x' op) : term862 A B s g x' op.
Proof. exact (proj2 (@lem6164408 A B f s g x' op h1)). Qed.
Lemma lem6164411 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term867 A B f s g x' op) : term862 A B s f x' op.
Proof. exact (proj1 (@lem6164408 A B f s g x' op h1)). Qed.
Lemma lem6164421 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term861 A B s f g x' op) : term859 A B s f g x' op.
Proof. exact (proj1 (@lem6164407 A B s f g x' op h1)). Qed.
Lemma lem6164422 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term861 A B s f g x' op) : term850 A B s f g x' op.
Proof. exact (proj2 (@lem6164421 A B s f g x' op h1)). Qed.
Lemma lem6164423 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term861 A B s f g x' op) : term857 A B f s g x' op.
Proof. exact (proj1 (@lem6164421 A B s f g x' op h1)). Qed.
Lemma lem6164426 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s f x' op) : term855 A B s f x' op.
Proof. exact (h1). Qed.
Lemma lem6164427 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s g x' op) : term855 A B s g x' op.
Proof. exact (h1). Qed.
Lemma lem6164769 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6164773 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6165105 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6165445 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6165484 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term441 A P Q) = (term440 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem6165485 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term441 B P Q) = (term440 B P Q).
Proof. exact (@lem6165484 B P Q). Qed.
Lemma lem6165486 {B : Type'} (op : type1400 B) : (term870 B op) = (term871 B op).
Proof. exact (@lem6165485 B (term772 B op) (term754 B op)). Qed.
Lemma lem6165487 {B : Type'} (op : type1400 B) (x : B) : (term872 B op x) = (term771 B op x).
Proof. exact (eq_refl (term872 B op x)). Qed.
Lemma lem6165488 {B : Type'} (op : type1400 B) : (term873 B op) = (term772 B op).
Proof. exact (fun_ext (fun x : B => @lem6165487 B op x)). Qed.
Lemma lem6165489 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6165490 {B : Type'} (op : type1400 B) : (term874 B op) = (term773 B op).
Proof. exact (MK_COMB (@lem6165489 B) (@lem6165488 B op)). Qed.
Lemma lem6165491 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6165492 {B : Type'} (op : type1400 B) : (term875 B op) = (term774 B op).
Proof. exact (MK_COMB (@lem6165491) (@lem6165490 B op)). Qed.
Lemma lem6165493 {B : Type'} (op : type1400 B) (x : B) : (term876 B op x) = ((term751 B op x) = x).
Proof. exact (eq_refl (term876 B op x)). Qed.
Lemma lem6165494 {B : Type'} (op : type1400 B) : (term877 B op) = (term754 B op).
Proof. exact (fun_ext (fun x : B => @lem6165493 B op x)). Qed.
Lemma lem6165495 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6165496 {B : Type'} (op : type1400 B) : (term878 B op) = (term755 B op).
Proof. exact (MK_COMB (@lem6165495 B) (@lem6165494 B op)). Qed.
Lemma lem6165497 {B : Type'} (op : type1400 B) : (term870 B op) = (term775 B op).
Proof. exact (MK_COMB (@lem6165492 B op) (@lem6165496 B op)). Qed.
Lemma lem6165498 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6165499 {B : Type'} (op : type1400 B) : (term879 B op) = (term880 B op).
Proof. exact (MK_COMB (@lem6165498) (@lem6165497 B op)). Qed.
Lemma lem6165500 {B : Type'} (op : type1400 B) (x : B) : (term872 B op x) = (term771 B op x).
Proof. exact (eq_refl (term872 B op x)). Qed.
Lemma lem6165501 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6165502 {B : Type'} (op : type1400 B) (x : B) : (term881 B op x) = (term882 B op x).
Proof. exact (MK_COMB (@lem6165501) (@lem6165500 B op x)). Qed.
Lemma lem6165503 {B : Type'} (op : type1400 B) (x : B) : (term876 B op x) = ((term751 B op x) = x).
Proof. exact (eq_refl (term876 B op x)). Qed.
Lemma lem6165504 {B : Type'} (op : type1400 B) (x : B) : (term883 B op x) = (term884 B op x).
Proof. exact (MK_COMB (@lem6165502 B op x) (@lem6165503 B op x)). Qed.
Lemma lem6165505 {B : Type'} (op : type1400 B) : (term885 B op) = (term886 B op).
Proof. exact (fun_ext (fun x : B => @lem6165504 B op x)). Qed.
Lemma lem6165506 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6165507 {B : Type'} (op : type1400 B) : (term871 B op) = (term887 B op).
Proof. exact (MK_COMB (@lem6165506 B) (@lem6165505 B op)). Qed.
Lemma lem6165508 {B : Type'} (op : type1400 B) : ((term870 B op) = (term871 B op)) = ((term775 B op) = (term887 B op)).
Proof. exact (MK_COMB (@lem6165499 B op) (@lem6165507 B op)). Qed.
Lemma lem6165509 {B : Type'} (op : type1400 B) : (term775 B op) = (term887 B op).
Proof. exact (EQ_MP (@lem6165508 B op) (@lem6165486 B op)). Qed.
Lemma lem6165511 {A : Type'} (P : A -> Prop) (Q : Prop) : (term888 A P Q) = (term889 A P Q).
Proof. exact (EQ_MP (@lem19025 A P Q) (@lem19024 A P Q)). Qed.
Lemma lem6165512 {B : Type'} (P : B -> Prop) (Q : Prop) : (term888 B P Q) = (term889 B P Q).
Proof. exact (@lem6165511 B P Q). Qed.
Lemma lem6165513 {B : Type'} (op : type1400 B) (x : B) : (term890 B op x) = (term891 B op x).
Proof. exact (@lem6165512 B (term770 B op x) ((term751 B op x) = x)). Qed.
Lemma lem6165514 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term892 B op x y) = (term769 B op x y).
Proof. exact (eq_refl (term892 B op x y)). Qed.
Lemma lem6165515 {B : Type'} (op : type1400 B) (x : B) : (term893 B op x) = (term770 B op x).
Proof. exact (fun_ext (fun y : B => @lem6165514 B op x y)). Qed.
Lemma lem6165516 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6165517 {B : Type'} (op : type1400 B) (x : B) : (term894 B op x) = (term771 B op x).
Proof. exact (MK_COMB (@lem6165516 B) (@lem6165515 B op x)). Qed.
Lemma lem6165518 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6165519 {B : Type'} (op : type1400 B) (x : B) : (term895 B op x) = (term882 B op x).
Proof. exact (MK_COMB (@lem6165518) (@lem6165517 B op x)). Qed.
Lemma lem6165520 {B : Type'} (op : type1400 B) (x : B) : ((term751 B op x) = x) = ((term751 B op x) = x).
Proof. exact (eq_refl ((term751 B op x) = x)). Qed.
Lemma lem6165521 {B : Type'} (op : type1400 B) (x : B) : (term890 B op x) = (term884 B op x).
Proof. exact (MK_COMB (@lem6165519 B op x) (@lem6165520 B op x)). Qed.
Lemma lem6165522 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6165523 {B : Type'} (op : type1400 B) (x : B) : (term896 B op x) = (term897 B op x).
Proof. exact (MK_COMB (@lem6165522) (@lem6165521 B op x)). Qed.
Lemma lem6165524 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term892 B op x y) = (term769 B op x y).
Proof. exact (eq_refl (term892 B op x y)). Qed.
Lemma lem6165525 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6165526 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term898 B op x y) = (term899 B op x y).
Proof. exact (MK_COMB (@lem6165525) (@lem6165524 B op x y)). Qed.
Lemma lem6165527 {B : Type'} (op : type1400 B) (x : B) : ((term751 B op x) = x) = ((term751 B op x) = x).
Proof. exact (eq_refl ((term751 B op x) = x)). Qed.
Lemma lem6165528 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term900 B y op x) = (term901 B y op x).
Proof. exact (MK_COMB (@lem6165526 B op x y) (@lem6165527 B op x)). Qed.
Lemma lem6165529 {B : Type'} (op : type1400 B) (x : B) : (term902 B op x) = (term903 B op x).
Proof. exact (fun_ext (fun y : B => @lem6165528 B y op x)). Qed.
Lemma lem6165530 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6165531 {B : Type'} (op : type1400 B) (x : B) : (term891 B op x) = (term904 B op x).
Proof. exact (MK_COMB (@lem6165530 B) (@lem6165529 B op x)). Qed.
Lemma lem6165532 {B : Type'} (op : type1400 B) (x : B) : ((term890 B op x) = (term891 B op x)) = ((term884 B op x) = (term904 B op x)).
Proof. exact (MK_COMB (@lem6165523 B op x) (@lem6165531 B op x)). Qed.
Lemma lem6165533 {B : Type'} (op : type1400 B) (x : B) : (term884 B op x) = (term904 B op x).
Proof. exact (EQ_MP (@lem6165532 B op x) (@lem6165513 B op x)). Qed.
Lemma lem6165535 {A : Type'} (P : A -> Prop) (Q : Prop) : (term888 A P Q) = (term889 A P Q).
Proof. exact (EQ_MP (@lem19025 A P Q) (@lem19024 A P Q)). Qed.
Lemma lem6165536 {B : Type'} (P : B -> Prop) (Q : Prop) : (term888 B P Q) = (term889 B P Q).
Proof. exact (@lem6165535 B P Q). Qed.
Lemma lem6165537 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term905 B y op x) = (term906 B y op x).
Proof. exact (@lem6165536 B (term768 B op x y) ((term751 B op x) = x)). Qed.
Lemma lem6165538 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term907 B op x y z) = ((term759 B x op y z) = (term765 B op x y z)).
Proof. exact (eq_refl (term907 B op x y z)). Qed.
Lemma lem6165539 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term908 B op x y) = (term768 B op x y).
Proof. exact (fun_ext (fun z : B => @lem6165538 B op x y z)). Qed.
Lemma lem6165540 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6165541 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term909 B op x y) = (term769 B op x y).
Proof. exact (MK_COMB (@lem6165540 B) (@lem6165539 B op x y)). Qed.
Lemma lem6165542 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6165543 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term910 B op x y) = (term899 B op x y).
Proof. exact (MK_COMB (@lem6165542) (@lem6165541 B op x y)). Qed.
Lemma lem6165544 {B : Type'} (op : type1400 B) (x : B) : ((term751 B op x) = x) = ((term751 B op x) = x).
Proof. exact (eq_refl ((term751 B op x) = x)). Qed.
Lemma lem6165545 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term905 B y op x) = (term901 B y op x).
Proof. exact (MK_COMB (@lem6165543 B op x y) (@lem6165544 B op x)). Qed.
Lemma lem6165546 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6165547 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term911 B y op x) = (term912 B y op x).
Proof. exact (MK_COMB (@lem6165546) (@lem6165545 B y op x)). Qed.
Lemma lem6165548 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term907 B op x y z) = ((term759 B x op y z) = (term765 B op x y z)).
Proof. exact (eq_refl (term907 B op x y z)). Qed.
Lemma lem6165549 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6165550 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term913 B op x y z) = (term914 B op x y z).
Proof. exact (MK_COMB (@lem6165549) (@lem6165548 B op x y z)). Qed.
Lemma lem6165551 {B : Type'} (op : type1400 B) (x : B) : ((term751 B op x) = x) = ((term751 B op x) = x).
Proof. exact (eq_refl ((term751 B op x) = x)). Qed.
Lemma lem6165552 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term915 B y z op x) = (term916 B y z op x).
Proof. exact (MK_COMB (@lem6165550 B op x y z) (@lem6165551 B op x)). Qed.
Lemma lem6165553 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term917 B y op x) = (term918 B y op x).
Proof. exact (fun_ext (fun z : B => @lem6165552 B y z op x)). Qed.
Lemma lem6165554 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6165555 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term906 B y op x) = (term919 B y op x).
Proof. exact (MK_COMB (@lem6165554 B) (@lem6165553 B y op x)). Qed.
Lemma lem6165556 {B : Type'} (y : B) (op : type1400 B) (x : B) : ((term905 B y op x) = (term906 B y op x)) = ((term901 B y op x) = (term919 B y op x)).
Proof. exact (MK_COMB (@lem6165547 B y op x) (@lem6165555 B y op x)). Qed.
Lemma lem6165557 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term901 B y op x) = (term919 B y op x).
Proof. exact (EQ_MP (@lem6165556 B y op x) (@lem6165537 B y op x)). Qed.
Lemma lem6165558 {B : Type'} (op : type1400 B) (x : B) : (term903 B op x) = (term920 B op x).
Proof. exact (fun_ext (fun y : B => @lem6165557 B y op x)). Qed.
Lemma lem6165559 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6165560 {B : Type'} (op : type1400 B) (x : B) : (term904 B op x) = (term921 B op x).
Proof. exact (MK_COMB (@lem6165559 B) (@lem6165558 B op x)). Qed.
Lemma lem6165561 {B : Type'} (op : type1400 B) (x : B) : (term884 B op x) = (term921 B op x).
Proof. exact (TRANS (@lem6165533 B op x) (@lem6165560 B op x)). Qed.
Lemma lem6165562 {B : Type'} (op : type1400 B) : (term886 B op) = (term922 B op).
Proof. exact (fun_ext (fun x : B => @lem6165561 B op x)). Qed.
Lemma lem6165563 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6165564 {B : Type'} (op : type1400 B) : (term887 B op) = (term923 B op).
Proof. exact (MK_COMB (@lem6165563 B) (@lem6165562 B op)). Qed.
Lemma lem6165565 {B : Type'} (op : type1400 B) : (term775 B op) = (term923 B op).
Proof. exact (TRANS (@lem6165509 B op) (@lem6165564 B op)). Qed.
Lemma lem6165566 {B : Type'} (op : type1400 B) : (term782 B op) = (term782 B op).
Proof. exact (eq_refl (term782 B op)). Qed.
Lemma lem6165567 {B : Type'} (op : type1400 B) : (term783 B op) = (term924 B op).
Proof. exact (MK_COMB (@lem6165566 B op) (@lem6165565 B op)). Qed.
Lemma lem6165569 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term441 A P Q) = (term440 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem6165570 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term441 B P Q) = (term440 B P Q).
Proof. exact (@lem6165569 B P Q). Qed.
Lemma lem6165571 {B : Type'} (op : type1400 B) : (term925 B op) = (term926 B op).
Proof. exact (@lem6165570 B (term780 B op) (term922 B op)). Qed.
Lemma lem6165572 {B : Type'} (op : type1400 B) (x : B) : (term927 B op x) = (term779 B op x).
Proof. exact (eq_refl (term927 B op x)). Qed.
Lemma lem6165573 {B : Type'} (op : type1400 B) : (term928 B op) = (term780 B op).
Proof. exact (fun_ext (fun x : B => @lem6165572 B op x)). Qed.
Lemma lem6165574 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6165575 {B : Type'} (op : type1400 B) : (term929 B op) = (term781 B op).
Proof. exact (MK_COMB (@lem6165574 B) (@lem6165573 B op)). Qed.
Lemma lem6165576 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6165577 {B : Type'} (op : type1400 B) : (term930 B op) = (term782 B op).
Proof. exact (MK_COMB (@lem6165576) (@lem6165575 B op)). Qed.
Lemma lem6165578 {B : Type'} (op : type1400 B) (x : B) : (term931 B op x) = (term921 B op x).
Proof. exact (eq_refl (term931 B op x)). Qed.
Lemma lem6165579 {B : Type'} (op : type1400 B) : (term932 B op) = (term922 B op).
Proof. exact (fun_ext (fun x : B => @lem6165578 B op x)). Qed.
Lemma lem6165580 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6165581 {B : Type'} (op : type1400 B) : (term933 B op) = (term923 B op).
Proof. exact (MK_COMB (@lem6165580 B) (@lem6165579 B op)). Qed.
Lemma lem6165582 {B : Type'} (op : type1400 B) : (term925 B op) = (term924 B op).
Proof. exact (MK_COMB (@lem6165577 B op) (@lem6165581 B op)). Qed.
Lemma lem6165583 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6165584 {B : Type'} (op : type1400 B) : (term934 B op) = (term935 B op).
Proof. exact (MK_COMB (@lem6165583) (@lem6165582 B op)). Qed.
Lemma lem6165585 {B : Type'} (op : type1400 B) (x : B) : (term927 B op x) = (term779 B op x).
Proof. exact (eq_refl (term927 B op x)). Qed.
Lemma lem6165586 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6165587 {B : Type'} (op : type1400 B) (x : B) : (term936 B op x) = (term937 B op x).
Proof. exact (MK_COMB (@lem6165586) (@lem6165585 B op x)). Qed.
Lemma lem6165588 {B : Type'} (op : type1400 B) (x : B) : (term931 B op x) = (term921 B op x).
Proof. exact (eq_refl (term931 B op x)). Qed.
Lemma lem6165589 {B : Type'} (op : type1400 B) (x : B) : (term938 B op x) = (term939 B op x).
Proof. exact (MK_COMB (@lem6165587 B op x) (@lem6165588 B op x)). Qed.
Lemma lem6165590 {B : Type'} (op : type1400 B) : (term940 B op) = (term941 B op).
Proof. exact (fun_ext (fun x : B => @lem6165589 B op x)). Qed.
Lemma lem6165591 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6165592 {B : Type'} (op : type1400 B) : (term926 B op) = (term942 B op).
Proof. exact (MK_COMB (@lem6165591 B) (@lem6165590 B op)). Qed.
Lemma lem6165593 {B : Type'} (op : type1400 B) : ((term925 B op) = (term926 B op)) = ((term924 B op) = (term942 B op)).
Proof. exact (MK_COMB (@lem6165584 B op) (@lem6165592 B op)). Qed.
Lemma lem6165594 {B : Type'} (op : type1400 B) : (term924 B op) = (term942 B op).
Proof. exact (EQ_MP (@lem6165593 B op) (@lem6165571 B op)). Qed.
Lemma lem6165596 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term441 A P Q) = (term440 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem6165597 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term441 B P Q) = (term440 B P Q).
Proof. exact (@lem6165596 B P Q). Qed.
Lemma lem6165598 {B : Type'} (op : type1400 B) (x : B) : (term943 B op x) = (term944 B op x).
Proof. exact (@lem6165597 B (term778 B op x) (term920 B op x)). Qed.
Lemma lem6165599 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term945 B op x y) = ((term756 B op x y) = (term756 B op y x)).
Proof. exact (eq_refl (term945 B op x y)). Qed.
Lemma lem6165600 {B : Type'} (op : type1400 B) (x : B) : (term946 B op x) = (term778 B op x).
Proof. exact (fun_ext (fun y : B => @lem6165599 B op y x)). Qed.
Lemma lem6165601 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6165602 {B : Type'} (op : type1400 B) (x : B) : (term947 B op x) = (term779 B op x).
Proof. exact (MK_COMB (@lem6165601 B) (@lem6165600 B op x)). Qed.
Lemma lem6165603 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6165604 {B : Type'} (op : type1400 B) (x : B) : (term948 B op x) = (term937 B op x).
Proof. exact (MK_COMB (@lem6165603) (@lem6165602 B op x)). Qed.
Lemma lem6165605 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term949 B op x y) = (term919 B y op x).
Proof. exact (eq_refl (term949 B op x y)). Qed.
Lemma lem6165606 {B : Type'} (op : type1400 B) (x : B) : (term950 B op x) = (term920 B op x).
Proof. exact (fun_ext (fun y : B => @lem6165605 B y op x)). Qed.
Lemma lem6165607 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6165608 {B : Type'} (op : type1400 B) (x : B) : (term951 B op x) = (term921 B op x).
Proof. exact (MK_COMB (@lem6165607 B) (@lem6165606 B op x)). Qed.
Lemma lem6165609 {B : Type'} (op : type1400 B) (x : B) : (term943 B op x) = (term939 B op x).
Proof. exact (MK_COMB (@lem6165604 B op x) (@lem6165608 B op x)). Qed.
Lemma lem6165610 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6165611 {B : Type'} (op : type1400 B) (x : B) : (term952 B op x) = (term953 B op x).
Proof. exact (MK_COMB (@lem6165610) (@lem6165609 B op x)). Qed.
Lemma lem6165612 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term945 B op x y) = ((term756 B op x y) = (term756 B op y x)).
Proof. exact (eq_refl (term945 B op x y)). Qed.
Lemma lem6165613 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6165614 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term954 B op x y) = (term955 B op y x).
Proof. exact (MK_COMB (@lem6165613) (@lem6165612 B op y x)). Qed.
Lemma lem6165615 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term949 B op x y) = (term919 B y op x).
Proof. exact (eq_refl (term949 B op x y)). Qed.
Lemma lem6165616 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term956 B op x y) = (term957 B y op x).
Proof. exact (MK_COMB (@lem6165614 B op y x) (@lem6165615 B y op x)). Qed.
Lemma lem6165617 {B : Type'} (op : type1400 B) (x : B) : (term958 B op x) = (term959 B op x).
Proof. exact (fun_ext (fun y : B => @lem6165616 B y op x)). Qed.
Lemma lem6165618 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6165619 {B : Type'} (op : type1400 B) (x : B) : (term944 B op x) = (term960 B op x).
Proof. exact (MK_COMB (@lem6165618 B) (@lem6165617 B op x)). Qed.
Lemma lem6165620 {B : Type'} (op : type1400 B) (x : B) : ((term943 B op x) = (term944 B op x)) = ((term939 B op x) = (term960 B op x)).
Proof. exact (MK_COMB (@lem6165611 B op x) (@lem6165619 B op x)). Qed.
Lemma lem6165621 {B : Type'} (op : type1400 B) (x : B) : (term939 B op x) = (term960 B op x).
Proof. exact (EQ_MP (@lem6165620 B op x) (@lem6165598 B op x)). Qed.
Lemma lem6165623 {A : Type'} (P : Prop) (Q : A -> Prop) : (term961 A P Q) = (term962 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem6165624 {B : Type'} (P : Prop) (Q : B -> Prop) : (term961 B P Q) = (term962 B P Q).
Proof. exact (@lem6165623 B P Q). Qed.
Lemma lem6165625 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term963 B y op x) = (term964 B y op x).
Proof. exact (@lem6165624 B ((term756 B op x y) = (term756 B op y x)) (term918 B y op x)). Qed.
Lemma lem6165626 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term965 B y op x z) = (term916 B y z op x).
Proof. exact (eq_refl (term965 B y op x z)). Qed.
Lemma lem6165627 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term966 B y op x) = (term918 B y op x).
Proof. exact (fun_ext (fun z : B => @lem6165626 B y z op x)). Qed.
Lemma lem6165628 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6165629 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term967 B y op x) = (term919 B y op x).
Proof. exact (MK_COMB (@lem6165628 B) (@lem6165627 B y op x)). Qed.
Lemma lem6165630 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term955 B op y x) = (term955 B op y x).
Proof. exact (eq_refl (term955 B op y x)). Qed.
Lemma lem6165631 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term963 B y op x) = (term957 B y op x).
Proof. exact (MK_COMB (@lem6165630 B op y x) (@lem6165629 B y op x)). Qed.
Lemma lem6165632 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6165633 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term968 B y op x) = (term969 B y op x).
Proof. exact (MK_COMB (@lem6165632) (@lem6165631 B y op x)). Qed.
Lemma lem6165634 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term965 B y op x z) = (term916 B y z op x).
Proof. exact (eq_refl (term965 B y op x z)). Qed.
Lemma lem6165635 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term955 B op y x) = (term955 B op y x).
Proof. exact (eq_refl (term955 B op y x)). Qed.
Lemma lem6165636 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term970 B y op x z) = (term971 B y z op x).
Proof. exact (MK_COMB (@lem6165635 B op y x) (@lem6165634 B y z op x)). Qed.
Lemma lem6165637 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term972 B y op x) = (term973 B y op x).
Proof. exact (fun_ext (fun z : B => @lem6165636 B y z op x)). Qed.
Lemma lem6165638 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6165639 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term964 B y op x) = (term974 B y op x).
Proof. exact (MK_COMB (@lem6165638 B) (@lem6165637 B y op x)). Qed.
Lemma lem6165640 {B : Type'} (y : B) (op : type1400 B) (x : B) : ((term963 B y op x) = (term964 B y op x)) = ((term957 B y op x) = (term974 B y op x)).
Proof. exact (MK_COMB (@lem6165633 B y op x) (@lem6165639 B y op x)). Qed.
Lemma lem6165641 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term957 B y op x) = (term974 B y op x).
Proof. exact (EQ_MP (@lem6165640 B y op x) (@lem6165625 B y op x)). Qed.
Lemma lem6165642 {B : Type'} (op : type1400 B) (x : B) : (term959 B op x) = (term975 B op x).
Proof. exact (fun_ext (fun y : B => @lem6165641 B y op x)). Qed.
Lemma lem6165643 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6165644 {B : Type'} (op : type1400 B) (x : B) : (term960 B op x) = (term976 B op x).
Proof. exact (MK_COMB (@lem6165643 B) (@lem6165642 B op x)). Qed.
Lemma lem6165645 {B : Type'} (op : type1400 B) (x : B) : (term939 B op x) = (term976 B op x).
Proof. exact (TRANS (@lem6165621 B op x) (@lem6165644 B op x)). Qed.
Lemma lem6165646 {B : Type'} (op : type1400 B) : (term941 B op) = (term977 B op).
Proof. exact (fun_ext (fun x : B => @lem6165645 B op x)). Qed.
Lemma lem6165647 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6165648 {B : Type'} (op : type1400 B) : (term942 B op) = (term978 B op).
Proof. exact (MK_COMB (@lem6165647 B) (@lem6165646 B op)). Qed.
Lemma lem6165649 {B : Type'} (op : type1400 B) : (term924 B op) = (term978 B op).
Proof. exact (TRANS (@lem6165594 B op) (@lem6165648 B op)). Qed.
Lemma lem6165650 {B : Type'} (op : type1400 B) : (term783 B op) = (term978 B op).
Proof. exact (TRANS (@lem6165567 B op) (@lem6165649 B op)). Qed.
Lemma lem6165651 {B : Type'} (op : type1400 B) : (term786 B op) = (term786 B op).
Proof. exact (eq_refl (term786 B op)). Qed.
Lemma lem6165652 {B : Type'} (op : type1400 B) : (term787 B op) = (term979 B op).
Proof. exact (MK_COMB (@lem6165651 B op) (@lem6165650 B op)). Qed.
Lemma lem6165654 {A : Type'} (P : Prop) (Q : A -> Prop) : (term980 A P Q) = (term981 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem6165655 {B : Type'} (P : Prop) (Q : B -> Prop) : (term980 B P Q) = (term981 B P Q).
Proof. exact (@lem6165654 B P Q). Qed.
Lemma lem6165656 {B : Type'} (op : type1400 B) : (term982 B op) = (term983 B op).
Proof. exact (@lem6165655 B (term785 B op) (term977 B op)). Qed.
Lemma lem6165657 {B : Type'} (op : type1400 B) (x : B) : (term984 B op x) = (term976 B op x).
Proof. exact (eq_refl (term984 B op x)). Qed.
Lemma lem6165658 {B : Type'} (op : type1400 B) : (term985 B op) = (term977 B op).
Proof. exact (fun_ext (fun x : B => @lem6165657 B op x)). Qed.
Lemma lem6165659 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6165660 {B : Type'} (op : type1400 B) : (term986 B op) = (term978 B op).
Proof. exact (MK_COMB (@lem6165659 B) (@lem6165658 B op)). Qed.
Lemma lem6165661 {B : Type'} (op : type1400 B) : (term786 B op) = (term786 B op).
Proof. exact (eq_refl (term786 B op)). Qed.
Lemma lem6165662 {B : Type'} (op : type1400 B) : (term982 B op) = (term979 B op).
Proof. exact (MK_COMB (@lem6165661 B op) (@lem6165660 B op)). Qed.
Lemma lem6165663 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6165664 {B : Type'} (op : type1400 B) : (term987 B op) = (term988 B op).
Proof. exact (MK_COMB (@lem6165663) (@lem6165662 B op)). Qed.
Lemma lem6165665 {B : Type'} (op : type1400 B) (x : B) : (term984 B op x) = (term976 B op x).
Proof. exact (eq_refl (term984 B op x)). Qed.
Lemma lem6165666 {B : Type'} (op : type1400 B) : (term786 B op) = (term786 B op).
Proof. exact (eq_refl (term786 B op)). Qed.
Lemma lem6165667 {B : Type'} (op : type1400 B) (x : B) : (term989 B op x) = (term990 B op x).
Proof. exact (MK_COMB (@lem6165666 B op) (@lem6165665 B op x)). Qed.
Lemma lem6165668 {B : Type'} (op : type1400 B) : (term991 B op) = (term992 B op).
Proof. exact (fun_ext (fun x : B => @lem6165667 B op x)). Qed.
Lemma lem6165669 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6165670 {B : Type'} (op : type1400 B) : (term983 B op) = (term993 B op).
Proof. exact (MK_COMB (@lem6165669 B) (@lem6165668 B op)). Qed.
Lemma lem6165671 {B : Type'} (op : type1400 B) : ((term982 B op) = (term983 B op)) = ((term979 B op) = (term993 B op)).
Proof. exact (MK_COMB (@lem6165664 B op) (@lem6165670 B op)). Qed.
Lemma lem6165672 {B : Type'} (op : type1400 B) : (term979 B op) = (term993 B op).
Proof. exact (EQ_MP (@lem6165671 B op) (@lem6165656 B op)). Qed.
Lemma lem6165674 {A : Type'} (P : Prop) (Q : A -> Prop) : (term980 A P Q) = (term981 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem6165675 {B : Type'} (P : Prop) (Q : B -> Prop) : (term980 B P Q) = (term981 B P Q).
Proof. exact (@lem6165674 B P Q). Qed.
Lemma lem6165676 {B : Type'} (op : type1400 B) (x : B) : (term994 B op x) = (term995 B op x).
Proof. exact (@lem6165675 B (term785 B op) (term975 B op x)). Qed.
Lemma lem6165677 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term996 B op x y) = (term974 B y op x).
Proof. exact (eq_refl (term996 B op x y)). Qed.
Lemma lem6165678 {B : Type'} (op : type1400 B) (x : B) : (term997 B op x) = (term975 B op x).
Proof. exact (fun_ext (fun y : B => @lem6165677 B y op x)). Qed.
Lemma lem6165679 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6165680 {B : Type'} (op : type1400 B) (x : B) : (term998 B op x) = (term976 B op x).
Proof. exact (MK_COMB (@lem6165679 B) (@lem6165678 B op x)). Qed.
Lemma lem6165681 {B : Type'} (op : type1400 B) : (term786 B op) = (term786 B op).
Proof. exact (eq_refl (term786 B op)). Qed.
Lemma lem6165682 {B : Type'} (op : type1400 B) (x : B) : (term994 B op x) = (term990 B op x).
Proof. exact (MK_COMB (@lem6165681 B op) (@lem6165680 B op x)). Qed.
Lemma lem6165683 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6165684 {B : Type'} (op : type1400 B) (x : B) : (term999 B op x) = (term1000 B op x).
Proof. exact (MK_COMB (@lem6165683) (@lem6165682 B op x)). Qed.
Lemma lem6165685 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term996 B op x y) = (term974 B y op x).
Proof. exact (eq_refl (term996 B op x y)). Qed.
Lemma lem6165686 {B : Type'} (op : type1400 B) : (term786 B op) = (term786 B op).
Proof. exact (eq_refl (term786 B op)). Qed.
Lemma lem6165687 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term1001 B op x y) = (term1002 B y op x).
Proof. exact (MK_COMB (@lem6165686 B op) (@lem6165685 B y op x)). Qed.
Lemma lem6165688 {B : Type'} (op : type1400 B) (x : B) : (term1003 B op x) = (term1004 B op x).
Proof. exact (fun_ext (fun y : B => @lem6165687 B y op x)). Qed.
Lemma lem6165689 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6165690 {B : Type'} (op : type1400 B) (x : B) : (term995 B op x) = (term1005 B op x).
Proof. exact (MK_COMB (@lem6165689 B) (@lem6165688 B op x)). Qed.
Lemma lem6165691 {B : Type'} (op : type1400 B) (x : B) : ((term994 B op x) = (term995 B op x)) = ((term990 B op x) = (term1005 B op x)).
Proof. exact (MK_COMB (@lem6165684 B op x) (@lem6165690 B op x)). Qed.
Lemma lem6165692 {B : Type'} (op : type1400 B) (x : B) : (term990 B op x) = (term1005 B op x).
Proof. exact (EQ_MP (@lem6165691 B op x) (@lem6165676 B op x)). Qed.
Lemma lem6165694 {A : Type'} (P : Prop) (Q : A -> Prop) : (term980 A P Q) = (term981 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem6165695 {B : Type'} (P : Prop) (Q : B -> Prop) : (term980 B P Q) = (term981 B P Q).
Proof. exact (@lem6165694 B P Q). Qed.
Lemma lem6165696 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term1006 B y op x) = (term1007 B y op x).
Proof. exact (@lem6165695 B (term785 B op) (term973 B y op x)). Qed.
Lemma lem6165697 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term1008 B y op x z) = (term971 B y z op x).
Proof. exact (eq_refl (term1008 B y op x z)). Qed.
Lemma lem6165698 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term1009 B y op x) = (term973 B y op x).
Proof. exact (fun_ext (fun z : B => @lem6165697 B y z op x)). Qed.
Lemma lem6165699 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6165700 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term1010 B y op x) = (term974 B y op x).
Proof. exact (MK_COMB (@lem6165699 B) (@lem6165698 B y op x)). Qed.
Lemma lem6165701 {B : Type'} (op : type1400 B) : (term786 B op) = (term786 B op).
Proof. exact (eq_refl (term786 B op)). Qed.
Lemma lem6165702 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term1006 B y op x) = (term1002 B y op x).
Proof. exact (MK_COMB (@lem6165701 B op) (@lem6165700 B y op x)). Qed.
Lemma lem6165703 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6165704 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term1011 B y op x) = (term1012 B y op x).
Proof. exact (MK_COMB (@lem6165703) (@lem6165702 B y op x)). Qed.
Lemma lem6165705 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term1008 B y op x z) = (term971 B y z op x).
Proof. exact (eq_refl (term1008 B y op x z)). Qed.
Lemma lem6165706 {B : Type'} (op : type1400 B) : (term786 B op) = (term786 B op).
Proof. exact (eq_refl (term786 B op)). Qed.
Lemma lem6165707 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term1013 B y op x z) = (term1014 B y z op x).
Proof. exact (MK_COMB (@lem6165706 B op) (@lem6165705 B y z op x)). Qed.
Lemma lem6165708 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term1015 B y op x) = (term1016 B y op x).
Proof. exact (fun_ext (fun z : B => @lem6165707 B y z op x)). Qed.
Lemma lem6165709 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6165710 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term1007 B y op x) = (term1017 B y op x).
Proof. exact (MK_COMB (@lem6165709 B) (@lem6165708 B y op x)). Qed.
Lemma lem6165711 {B : Type'} (y : B) (op : type1400 B) (x : B) : ((term1006 B y op x) = (term1007 B y op x)) = ((term1002 B y op x) = (term1017 B y op x)).
Proof. exact (MK_COMB (@lem6165704 B y op x) (@lem6165710 B y op x)). Qed.
Lemma lem6165712 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term1002 B y op x) = (term1017 B y op x).
Proof. exact (EQ_MP (@lem6165711 B y op x) (@lem6165696 B y op x)). Qed.
Lemma lem6165713 {B : Type'} (op : type1400 B) (x : B) : (term1004 B op x) = (term1018 B op x).
Proof. exact (fun_ext (fun y : B => @lem6165712 B y op x)). Qed.
Lemma lem6165714 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6165715 {B : Type'} (op : type1400 B) (x : B) : (term1005 B op x) = (term1019 B op x).
Proof. exact (MK_COMB (@lem6165714 B) (@lem6165713 B op x)). Qed.
Lemma lem6165716 {B : Type'} (op : type1400 B) (x : B) : (term990 B op x) = (term1019 B op x).
Proof. exact (TRANS (@lem6165692 B op x) (@lem6165715 B op x)). Qed.
Lemma lem6165717 {B : Type'} (op : type1400 B) : (term992 B op) = (term1020 B op).
Proof. exact (fun_ext (fun x : B => @lem6165716 B op x)). Qed.
Lemma lem6165718 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6165719 {B : Type'} (op : type1400 B) : (term993 B op) = (term1021 B op).
Proof. exact (MK_COMB (@lem6165718 B) (@lem6165717 B op)). Qed.
Lemma lem6165720 {B : Type'} (op : type1400 B) : (term979 B op) = (term1021 B op).
Proof. exact (TRANS (@lem6165672 B op) (@lem6165719 B op)). Qed.
Lemma lem6165721 {B : Type'} (op : type1400 B) : (term787 B op) = (term1021 B op).
Proof. exact (TRANS (@lem6165652 B op) (@lem6165720 B op)). Qed.
Lemma lem6165722 {B : Type'} : (term788 B) = (term1022 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6165721 B op)). Qed.
Lemma lem6165723 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6165724 {B : Type'} : (term789 B) = (term1023 B).
Proof. exact (MK_COMB (@lem6165723 B) (@lem6165722 B)). Qed.
Lemma lem6165738 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term1014 B y z op x) = (term1024 B y z op x).
Proof. exact (@lem19490 ((term756 B op x y) = (term756 B op y x)) (term785 B op) (term916 B y z op x)). Qed.
Lemma lem6165745 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term1025 B y z op x) = (term1026 B y z op x).
Proof. exact (@lem19490 ((term759 B x op y z) = (term765 B op x y z)) (term785 B op) ((term751 B op x) = x)). Qed.
Lemma lem6165748 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term1027 B op y x) = (term1027 B op y x).
Proof. exact (eq_refl (term1027 B op y x)). Qed.
Lemma lem6165749 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term1024 B y z op x) = (term1028 B y z op x).
Proof. exact (MK_COMB (@lem6165748 B op y x) (@lem6165745 B y z op x)). Qed.
Lemma lem6165751 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term1014 B y z op x) = (term1028 B y z op x).
Proof. exact (TRANS (@lem6165738 B y z op x) (@lem6165749 B y z op x)). Qed.
Lemma lem6165752 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term1016 B y op x) = (term1029 B y op x).
Proof. exact (fun_ext (fun z : B => @lem6165751 B y z op x)). Qed.
Lemma lem6165753 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6165754 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term1017 B y op x) = (term1030 B y op x).
Proof. exact (MK_COMB (@lem6165753 B) (@lem6165752 B y op x)). Qed.
Lemma lem6165755 {B : Type'} (op : type1400 B) (x : B) : (term1018 B op x) = (term1031 B op x).
Proof. exact (fun_ext (fun y : B => @lem6165754 B y op x)). Qed.
Lemma lem6165756 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6165757 {B : Type'} (op : type1400 B) (x : B) : (term1019 B op x) = (term1032 B op x).
Proof. exact (MK_COMB (@lem6165756 B) (@lem6165755 B op x)). Qed.
Lemma lem6165758 {B : Type'} (op : type1400 B) : (term1020 B op) = (term1033 B op).
Proof. exact (fun_ext (fun x : B => @lem6165757 B op x)). Qed.
Lemma lem6165759 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6165760 {B : Type'} (op : type1400 B) : (term1021 B op) = (term1034 B op).
Proof. exact (MK_COMB (@lem6165759 B) (@lem6165758 B op)). Qed.
Lemma lem6165761 {B : Type'} : (term1022 B) = (term1035 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6165760 B op)). Qed.
Lemma lem6165762 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6165763 {B : Type'} : (term1023 B) = (term1036 B).
Proof. exact (MK_COMB (@lem6165762 B) (@lem6165761 B)). Qed.
Lemma lem6165764 {B : Type'} : (term789 B) = (term1036 B).
Proof. exact (TRANS (@lem6165724 B) (@lem6165763 B)). Qed.
Lemma lem6165765 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term738 B y z x) : term1036 B.
Proof. exact (EQ_MP (@lem6165764 B) (@lem6164404 B y z x h1)). Qed.
Lemma lem6165777 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (h1). Qed.
Lemma lem6165781 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (h1). Qed.
Lemma lem6166109 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6166445 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6166781 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (h1). Qed.
Lemma lem6167117 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (h1). Qed.
Lemma lem6167174 {B : Type'} (_77702 : type1400 B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term738 B y z x) : term1037 B _77702.
Proof. exact (@lem6165765 B y z x h1 _77702). Qed.
Lemma lem6167175 {B : Type'} (_77702 : type1400 B) : (term1037 B _77702) = (term1034 B _77702).
Proof. exact (eq_refl (term1037 B _77702)). Qed.
Lemma lem6167176 {B : Type'} (_77702 : type1400 B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term738 B y z x) : term1034 B _77702.
Proof. exact (EQ_MP (@lem6167175 B _77702) (@lem6167174 B _77702 y z x h1)). Qed.
Lemma lem6167177 {B : Type'} (_77702 : type1400 B) (_77703 : B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term738 B y z x) : term1038 B _77702 _77703.
Proof. exact (@lem6167176 B _77702 y z x h1 _77703). Qed.
Lemma lem6167178 {B : Type'} (_77702 : type1400 B) (_77703 : B) : (term1038 B _77702 _77703) = (term1032 B _77702 _77703).
Proof. exact (eq_refl (term1038 B _77702 _77703)). Qed.
Lemma lem6167179 {B : Type'} (_77702 : type1400 B) (_77703 : B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term738 B y z x) : term1032 B _77702 _77703.
Proof. exact (EQ_MP (@lem6167178 B _77702 _77703) (@lem6167177 B _77702 _77703 y z x h1)). Qed.
Lemma lem6167180 {B : Type'} (_77702 : type1400 B) (_77703 : B) (_77704 : B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term738 B y z x) : term1039 B _77702 _77703 _77704.
Proof. exact (@lem6167179 B _77702 _77703 y z x h1 _77704). Qed.
Lemma lem6167181 {B : Type'} (_77704 : B) (_77702 : type1400 B) (_77703 : B) : (term1039 B _77702 _77703 _77704) = (term1030 B _77704 _77702 _77703).
Proof. exact (eq_refl (term1039 B _77702 _77703 _77704)). Qed.
Lemma lem6167182 {B : Type'} (_77704 : B) (_77702 : type1400 B) (_77703 : B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term738 B y z x) : term1030 B _77704 _77702 _77703.
Proof. exact (EQ_MP (@lem6167181 B _77704 _77702 _77703) (@lem6167180 B _77702 _77703 _77704 y z x h1)). Qed.
Lemma lem6167183 {B : Type'} (_77704 : B) (_77702 : type1400 B) (_77703 : B) (_77705 : B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term738 B y z x) : term1040 B _77704 _77702 _77703 _77705.
Proof. exact (@lem6167182 B _77704 _77702 _77703 y z x h1 _77705). Qed.
Lemma lem6167184 {B : Type'} (_77704 : B) (_77705 : B) (_77702 : type1400 B) (_77703 : B) : (term1040 B _77704 _77702 _77703 _77705) = (term1028 B _77704 _77705 _77702 _77703).
Proof. exact (eq_refl (term1040 B _77704 _77702 _77703 _77705)). Qed.
Lemma lem6167185 {B : Type'} (_77704 : B) (_77705 : B) (_77702 : type1400 B) (_77703 : B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term738 B y z x) : term1028 B _77704 _77705 _77702 _77703.
Proof. exact (EQ_MP (@lem6167184 B _77704 _77705 _77702 _77703) (@lem6167183 B _77704 _77702 _77703 _77705 y z x h1)). Qed.
Lemma lem6167258 {B : Type'} (_77704 : B) (_77705 : B) (_77702 : type1400 B) (_77703 : B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term738 B y z x) : term1026 B _77704 _77705 _77702 _77703.
Proof. exact (proj2 (@lem6167185 B _77704 _77705 _77702 _77703 y z x h1)). Qed.
Lemma lem6167303 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6167305 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6167349 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6167397 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6167439 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term867 A B f s g x' op) : term845 A B f g x' op.
Proof. exact (proj2 (@lem6164409 A B f s g x' op h1)). Qed.
Lemma lem6167441 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (h1). Qed.
Lemma lem6167443 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (h1). Qed.
Lemma lem6167461 {B : Type'} (_77702 : type1400 B) (_77703 : B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term738 B y z x) : term1041 B _77702 _77703.
Proof. exact (proj2 (@lem6167258 B (@el B) (@el B) _77702 _77703 y z x h1)). Qed.
Lemma lem6167485 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6167531 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6167575 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term861 A B s f g x' op) : term845 A B f g x' op.
Proof. exact (proj2 (@lem6164407 A B s f g x' op h1)). Qed.
Lemma lem6167577 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (h1). Qed.
Lemma lem6167621 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term861 A B s f g x' op) : term845 A B f g x' op.
Proof. exact (proj2 (@lem6164407 A B s f g x' op h1)). Qed.
Lemma lem6167623 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (h1). Qed.
Lemma lem6167831 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term867 A B f s g x' op) : term846 A x' s.
Proof. exact (proj1 (@lem6164409 A B f s g x' op h1)). Qed.
Lemma lem6167832 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term867 A B f s g x' op) : term1042 A x' s.
Proof. exact (fun h0 : term848 A x' s => @lem6167831 A B f s g x' op h1). Qed.
Lemma lem6167834 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6167835 {A : Type'} (x' : A) (s : A -> Prop) : (term1042 A x' s) = (term846 A x' s).
Proof. exact (@lem6167834 (term846 A x' s)). Qed.
Lemma lem6167836 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term867 A B f s g x' op) : term846 A x' s.
Proof. exact (EQ_MP (@lem6167835 A x' s) (@lem6167832 A B f s g x' op h1)). Qed.
Lemma lem6167839 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6167841 {A : Type'} (x' : A) (s : A -> Prop) : (term848 A x' s) = (term1044 A x' s).
Proof. exact (@lem6167839 (term846 A x' s)). Qed.
Lemma lem6167844 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term1044 A x' s.
Proof. exact (EQ_MP (@lem6167841 A x' s) (@lem6167303 A x' s h1)). Qed.
Lemma lem6167847 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : False.
Proof. exact (@lem6167844 A x' s h1 (@lem6167836 A B f s g x' op h2)). Qed.
Lemma lem6167848 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : term1045.
Proof. exact (fun h0 : ~ False => @lem6167847 A B f s g x' op h1 h2). Qed.
Lemma lem6167850 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6167851 : term1045 = False.
Proof. exact (@lem6167850 False). Qed.
Lemma lem6167852 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6167851) (@lem6167848 A B f s g x' op h1 h2)). Qed.
Lemma lem6168038 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term867 A B f s g x' op) : term846 A x' s.
Proof. exact (proj1 (@lem6164409 A B f s g x' op h1)). Qed.
Lemma lem6168039 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term867 A B f s g x' op) : term1042 A x' s.
Proof. exact (fun h0 : term848 A x' s => @lem6168038 A B f s g x' op h1). Qed.
Lemma lem6168041 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6168042 {A : Type'} (x' : A) (s : A -> Prop) : (term1042 A x' s) = (term846 A x' s).
Proof. exact (@lem6168041 (term846 A x' s)). Qed.
Lemma lem6168043 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term867 A B f s g x' op) : term846 A x' s.
Proof. exact (EQ_MP (@lem6168042 A x' s) (@lem6168039 A B f s g x' op h1)). Qed.
Lemma lem6168046 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6168048 {A : Type'} (x' : A) (s : A -> Prop) : (term848 A x' s) = (term1044 A x' s).
Proof. exact (@lem6168046 (term846 A x' s)). Qed.
Lemma lem6168051 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term1044 A x' s.
Proof. exact (EQ_MP (@lem6168048 A x' s) (@lem6167349 A x' s h1)). Qed.
Lemma lem6168054 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : False.
Proof. exact (@lem6168051 A x' s h1 (@lem6168043 A B f s g x' op h2)). Qed.
Lemma lem6168055 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : term1045.
Proof. exact (fun h0 : ~ False => @lem6168054 A B f s g x' op h1 h2). Qed.
Lemma lem6168057 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6168058 : term1045 = False.
Proof. exact (@lem6168057 False). Qed.
Lemma lem6168059 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6168058) (@lem6168055 A B f s g x' op h1 h2)). Qed.
Lemma lem6168245 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term867 A B f s g x' op) : term846 A x' s.
Proof. exact (proj1 (@lem6164409 A B f s g x' op h1)). Qed.
Lemma lem6168246 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term867 A B f s g x' op) : term1042 A x' s.
Proof. exact (fun h0 : term848 A x' s => @lem6168245 A B f s g x' op h1). Qed.
Lemma lem6168248 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6168249 {A : Type'} (x' : A) (s : A -> Prop) : (term1042 A x' s) = (term846 A x' s).
Proof. exact (@lem6168248 (term846 A x' s)). Qed.
Lemma lem6168250 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term867 A B f s g x' op) : term846 A x' s.
Proof. exact (EQ_MP (@lem6168249 A x' s) (@lem6168246 A B f s g x' op h1)). Qed.
Lemma lem6168253 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6168255 {A : Type'} (x' : A) (s : A -> Prop) : (term848 A x' s) = (term1044 A x' s).
Proof. exact (@lem6168253 (term846 A x' s)). Qed.
Lemma lem6168258 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term1044 A x' s.
Proof. exact (EQ_MP (@lem6168255 A x' s) (@lem6167397 A x' s h1)). Qed.
Lemma lem6168261 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : False.
Proof. exact (@lem6168258 A x' s h1 (@lem6168250 A B f s g x' op h2)). Qed.
Lemma lem6168262 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : term1045.
Proof. exact (fun h0 : ~ False => @lem6168261 A B f s g x' op h1 h2). Qed.
Lemma lem6168264 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6168265 : term1045 = False.
Proof. exact (@lem6168264 False). Qed.
Lemma lem6168266 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6168265) (@lem6168262 A B f s g x' op h1 h2)). Qed.
Lemma lem6168335 {B : Type'} : (@I (B -> B -> B)) = (@I (B -> B -> B)).
Proof. exact (eq_refl (@I (B -> B -> B))). Qed.
Lemma lem6168336 {B : Type'} (_77862 : type1400 B) (_77864 : type1400 B) (h1 : _77862 = _77864) : _77862 = _77864.
Proof. exact (h1). Qed.
Lemma lem6168337 {B : Type'} (_77863 : B) (_77865 : B) (h1 : _77863 = _77865) : _77863 = _77865.
Proof. exact (h1). Qed.
Lemma lem6168338 {B : Type'} (_77862 : type1400 B) (_77864 : type1400 B) (h1 : _77862 = _77864) : (@I (B -> B -> B) _77862) = (@I (B -> B -> B) _77864).
Proof. exact (MK_COMB (@lem6168335 B) (@lem6168336 B _77862 _77864 h1)). Qed.
Lemma lem6168339 {B : Type'} (_77863 : B) (_77865 : B) (_77862 : type1400 B) (_77864 : type1400 B) (h1 : _77863 = _77865) (h2 : _77862 = _77864) : (@I (B -> B -> B) _77862 _77863) = (@I (B -> B -> B) _77864 _77865).
Proof. exact (MK_COMB (@lem6168338 B _77862 _77864 h2) (@lem6168337 B _77863 _77865 h1)). Qed.
Lemma lem6168340 {B : Type'} (_77862 : type1400 B) (_77864 : type1400 B) (_77863 : B) (_77865 : B) (h1 : _77863 = _77865) : term1046 B _77862 _77863 _77864 _77865.
Proof. exact (fun h0 : _77862 = _77864 => @lem6168339 B _77863 _77865 _77862 _77864 h1 h0). Qed.
Lemma lem6168342 (a : Prop) (b : Prop) : (a -> b) = (term1047 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem6168343 {B : Type'} (_77862 : type1400 B) (_77863 : B) (_77864 : type1400 B) (_77865 : B) : (term1046 B _77862 _77863 _77864 _77865) = (term1048 B _77862 _77863 _77864 _77865).
Proof. exact (@lem6168342 (_77862 = _77864) ((@I (B -> B -> B) _77862 _77863) = (@I (B -> B -> B) _77864 _77865))). Qed.
Lemma lem6168344 {B : Type'} (_77862 : type1400 B) (_77864 : type1400 B) (_77863 : B) (_77865 : B) (h1 : _77863 = _77865) : term1048 B _77862 _77863 _77864 _77865.
Proof. exact (EQ_MP (@lem6168343 B _77862 _77863 _77864 _77865) (@lem6168340 B _77862 _77864 _77863 _77865 h1)). Qed.
Lemma lem6168345 {B : Type'} (_77862 : type1400 B) (_77863 : B) (_77864 : type1400 B) (_77865 : B) : term1049 B _77862 _77863 _77864 _77865.
Proof. exact (fun h0 : _77863 = _77865 => @lem6168344 B _77862 _77864 _77863 _77865 h0). Qed.
Lemma lem6168347 (a : Prop) (b : Prop) : (a -> b) = (term1047 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem6168348 {B : Type'} (_77862 : type1400 B) (_77863 : B) (_77864 : type1400 B) (_77865 : B) : (term1049 B _77862 _77863 _77864 _77865) = (term1050 B _77862 _77863 _77864 _77865).
Proof. exact (@lem6168347 (_77863 = _77865) (term1048 B _77862 _77863 _77864 _77865)). Qed.
Lemma lem6168349 {B : Type'} (_77862 : type1400 B) (_77863 : B) (_77864 : type1400 B) (_77865 : B) : term1050 B _77862 _77863 _77864 _77865.
Proof. exact (EQ_MP (@lem6168348 B _77862 _77863 _77864 _77865) (@lem6168345 B _77862 _77863 _77864 _77865)). Qed.
Lemma lem6168350 {B : Type'} : (@I (B -> B)) = (@I (B -> B)).
Proof. exact (eq_refl (@I (B -> B))). Qed.
Lemma lem6168351 {B : Type'} (_77866 : B -> B) (_77868 : B -> B) (h1 : _77866 = _77868) : _77866 = _77868.
Proof. exact (h1). Qed.
Lemma lem6168352 {B : Type'} (_77867 : B) (_77869 : B) (h1 : _77867 = _77869) : _77867 = _77869.
Proof. exact (h1). Qed.
Lemma lem6168353 {B : Type'} (_77866 : B -> B) (_77868 : B -> B) (h1 : _77866 = _77868) : (@I (B -> B) _77866) = (@I (B -> B) _77868).
Proof. exact (MK_COMB (@lem6168350 B) (@lem6168351 B _77866 _77868 h1)). Qed.
Lemma lem6168354 {B : Type'} (_77867 : B) (_77869 : B) (_77866 : B -> B) (_77868 : B -> B) (h1 : _77867 = _77869) (h2 : _77866 = _77868) : (@I (B -> B) _77866 _77867) = (@I (B -> B) _77868 _77869).
Proof. exact (MK_COMB (@lem6168353 B _77866 _77868 h2) (@lem6168352 B _77867 _77869 h1)). Qed.
Lemma lem6168355 {B : Type'} (_77866 : B -> B) (_77868 : B -> B) (_77867 : B) (_77869 : B) (h1 : _77867 = _77869) : term1051 B _77866 _77867 _77868 _77869.
Proof. exact (fun h0 : _77866 = _77868 => @lem6168354 B _77867 _77869 _77866 _77868 h1 h0). Qed.
Lemma lem6168357 (a : Prop) (b : Prop) : (a -> b) = (term1047 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem6168358 {B : Type'} (_77866 : B -> B) (_77867 : B) (_77868 : B -> B) (_77869 : B) : (term1051 B _77866 _77867 _77868 _77869) = (term1052 B _77866 _77867 _77868 _77869).
Proof. exact (@lem6168357 (_77866 = _77868) ((@I (B -> B) _77866 _77867) = (@I (B -> B) _77868 _77869))). Qed.
Lemma lem6168359 {B : Type'} (_77866 : B -> B) (_77868 : B -> B) (_77867 : B) (_77869 : B) (h1 : _77867 = _77869) : term1052 B _77866 _77867 _77868 _77869.
Proof. exact (EQ_MP (@lem6168358 B _77866 _77867 _77868 _77869) (@lem6168355 B _77866 _77868 _77867 _77869 h1)). Qed.
Lemma lem6168360 {B : Type'} (_77866 : B -> B) (_77867 : B) (_77868 : B -> B) (_77869 : B) : term1053 B _77866 _77867 _77868 _77869.
Proof. exact (fun h0 : _77867 = _77869 => @lem6168359 B _77866 _77868 _77867 _77869 h0). Qed.
Lemma lem6168362 (a : Prop) (b : Prop) : (a -> b) = (term1047 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem6168363 {B : Type'} (_77866 : B -> B) (_77867 : B) (_77868 : B -> B) (_77869 : B) : (term1053 B _77866 _77867 _77868 _77869) = (term1054 B _77866 _77867 _77868 _77869).
Proof. exact (@lem6168362 (_77867 = _77869) (term1052 B _77866 _77867 _77868 _77869)). Qed.
Lemma lem6168364 {B : Type'} (_77866 : B -> B) (_77867 : B) (_77868 : B -> B) (_77869 : B) : term1054 B _77866 _77867 _77868 _77869.
Proof. exact (EQ_MP (@lem6168363 B _77866 _77867 _77868 _77869) (@lem6168360 B _77866 _77867 _77868 _77869)). Qed.
Lemma lem6168438 {B : Type'} (x : B) (y : B) (z : B) : term1055 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem6168452 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (h1). Qed.
Lemma lem6168453 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : term1056 A B g x' op.
Proof. exact (fun h0 : term853 A B g x' op => @lem6168452 A B g x' op h1). Qed.
Lemma lem6168455 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6168456 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) : (term1056 A B g x' op) = ((@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (@lem6168455 ((@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op))). Qed.
Lemma lem6168457 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (EQ_MP (@lem6168456 A B g x' op) (@lem6168453 A B g x' op h1)). Qed.
Lemma lem6168459 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (h1). Qed.
Lemma lem6168460 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : term1056 A B f x' op.
Proof. exact (fun h0 : term853 A B f x' op => @lem6168459 A B f x' op h1). Qed.
Lemma lem6168462 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6168463 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : (term1056 A B f x' op) = ((@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (@lem6168462 ((@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op))). Qed.
Lemma lem6168464 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (EQ_MP (@lem6168463 A B f x' op) (@lem6168460 A B f x' op h1)). Qed.
Lemma lem6168466 {B : Type'} (x : type1400 B) : x = x.
Proof. exact (@lem21386 (type1400 B) x). Qed.
Lemma lem6168467 {B : Type'} (x : type1400 B) : x = x.
Proof. exact (@lem6168466 B x). Qed.
Lemma lem6168468 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (@lem6168467 B op). Qed.
Lemma lem6168469 {B : Type'} (op : type1400 B) : term1057 B op.
Proof. exact (fun h0 : term1058 B op => @lem6168468 B op). Qed.
Lemma lem6168471 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6168472 {B : Type'} (op : type1400 B) : (term1057 B op) = (op = op).
Proof. exact (@lem6168471 (op = op)). Qed.
Lemma lem6168473 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (EQ_MP (@lem6168472 B op) (@lem6168469 B op)). Qed.
Lemma lem6168491 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6168492 {B : Type'} (_77863 : B) (_77865 : B) (_77862 : type1400 B) (_77864 : type1400 B) : (term1048 B _77862 _77863 _77864 _77865) = (term1059 B _77863 _77865 _77862 _77864).
Proof. exact (@lem6168491 ((@I (B -> B -> B) _77862 _77863) = (@I (B -> B -> B) _77864 _77865)) (term1060 B _77862 _77864)). Qed.
Lemma lem6168502 {B : Type'} (_77863 : B) (_77865 : B) : (term1061 B _77863 _77865) = (term1061 B _77863 _77865).
Proof. exact (eq_refl (term1061 B _77863 _77865)). Qed.
Lemma lem6168503 {B : Type'} (_77863 : B) (_77865 : B) (_77862 : type1400 B) (_77864 : type1400 B) : (term1050 B _77862 _77863 _77864 _77865) = (term1062 B _77863 _77865 _77862 _77864).
Proof. exact (MK_COMB (@lem6168502 B _77863 _77865) (@lem6168492 B _77863 _77865 _77862 _77864)). Qed.
Lemma lem6168507 (q : Prop) (p : Prop) (r : Prop) : (term1063 p q r) = (term1063 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6168508 {B : Type'} (_77863 : B) (_77865 : B) (_77862 : type1400 B) (_77864 : type1400 B) : (term1062 B _77863 _77865 _77862 _77864) = (term1064 B _77863 _77865 _77862 _77864).
Proof. exact (@lem6168507 ((@I (B -> B -> B) _77862 _77863) = (@I (B -> B -> B) _77864 _77865)) (term1065 B _77863 _77865) (term1060 B _77862 _77864)). Qed.
Lemma lem6168530 {B : Type'} (_77863 : B) (_77865 : B) (_77862 : type1400 B) (_77864 : type1400 B) : (term1050 B _77862 _77863 _77864 _77865) = (term1064 B _77863 _77865 _77862 _77864).
Proof. exact (TRANS (@lem6168503 B _77863 _77865 _77862 _77864) (@lem6168508 B _77863 _77865 _77862 _77864)). Qed.
Lemma lem6168531 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6168532 {B : Type'} (_77863 : B) (_77865 : B) (_77862 : type1400 B) (_77864 : type1400 B) : (term1066 B _77862 _77863 _77864 _77865) = (term1067 B _77863 _77865 _77862 _77864).
Proof. exact (MK_COMB (@lem6168531) (@lem6168530 B _77863 _77865 _77862 _77864)). Qed.
Lemma lem6168554 {B : Type'} (_77863 : B) (_77865 : B) (_77862 : type1400 B) (_77864 : type1400 B) : (term1064 B _77863 _77865 _77862 _77864) = (term1064 B _77863 _77865 _77862 _77864).
Proof. exact (eq_refl (term1064 B _77863 _77865 _77862 _77864)). Qed.
Lemma lem6168555 {B : Type'} (_77863 : B) (_77865 : B) (_77862 : type1400 B) (_77864 : type1400 B) : ((term1050 B _77862 _77863 _77864 _77865) = (term1064 B _77863 _77865 _77862 _77864)) = ((term1064 B _77863 _77865 _77862 _77864) = (term1064 B _77863 _77865 _77862 _77864)).
Proof. exact (MK_COMB (@lem6168532 B _77863 _77865 _77862 _77864) (@lem6168554 B _77863 _77865 _77862 _77864)). Qed.
Lemma lem6168557 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6168558 (x : Prop) : (x = x) = True.
Proof. exact (@lem6168557 Prop x). Qed.
Lemma lem6168559 {B : Type'} (_77863 : B) (_77865 : B) (_77862 : type1400 B) (_77864 : type1400 B) : ((term1064 B _77863 _77865 _77862 _77864) = (term1064 B _77863 _77865 _77862 _77864)) = True.
Proof. exact (@lem6168558 (term1064 B _77863 _77865 _77862 _77864)). Qed.
Lemma lem6168560 {B : Type'} (_77863 : B) (_77865 : B) (_77862 : type1400 B) (_77864 : type1400 B) : ((term1050 B _77862 _77863 _77864 _77865) = (term1064 B _77863 _77865 _77862 _77864)) = True.
Proof. exact (TRANS (@lem6168555 B _77863 _77865 _77862 _77864) (@lem6168559 B _77863 _77865 _77862 _77864)). Qed.
Lemma lem6168561 {B : Type'} (_77863 : B) (_77865 : B) (_77862 : type1400 B) (_77864 : type1400 B) : True = ((term1050 B _77862 _77863 _77864 _77865) = (term1064 B _77863 _77865 _77862 _77864)).
Proof. exact (SYM (@lem6168560 B _77863 _77865 _77862 _77864)). Qed.
Lemma lem6168562 {B : Type'} (_77863 : B) (_77865 : B) (_77862 : type1400 B) (_77864 : type1400 B) : (term1050 B _77862 _77863 _77864 _77865) = (term1064 B _77863 _77865 _77862 _77864).
Proof. exact (EQ_MP (@lem6168561 B _77863 _77865 _77862 _77864) (@lem0)). Qed.
Lemma lem6168563 {B : Type'} (_77863 : B) (_77865 : B) (_77862 : type1400 B) (_77864 : type1400 B) : term1064 B _77863 _77865 _77862 _77864.
Proof. exact (EQ_MP (@lem6168562 B _77863 _77865 _77862 _77864) (@lem6168349 B _77862 _77863 _77864 _77865)). Qed.
Lemma lem6168565 (b : Prop) (a : Prop) : (a \/ b) = (term1068 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6168566 {B : Type'} (_77862 : type1400 B) (_77863 : B) (_77864 : type1400 B) (_77865 : B) : (term1064 B _77863 _77865 _77862 _77864) = (term1069 B _77862 _77863 _77864 _77865).
Proof. exact (@lem6168565 (term1070 B _77863 _77865 _77862 _77864) ((@I (B -> B -> B) _77862 _77863) = (@I (B -> B -> B) _77864 _77865))). Qed.
Lemma lem6168568 (a : Prop) (b : Prop) : (term1071 a b) = (term1072 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6168569 {B : Type'} (_77863 : B) (_77865 : B) (_77862 : type1400 B) (_77864 : type1400 B) : (term1073 B _77863 _77865 _77862 _77864) = (term1074 B _77863 _77865 _77862 _77864).
Proof. exact (@lem6168568 (term1065 B _77863 _77865) (term1060 B _77862 _77864)). Qed.
Lemma lem6168571 (a : Prop) : (term1075 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6168572 {B : Type'} (_77863 : B) (_77865 : B) : (term1076 B _77863 _77865) = (_77863 = _77865).
Proof. exact (@lem6168571 (_77863 = _77865)). Qed.
Lemma lem6168573 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6168574 {B : Type'} (_77863 : B) (_77865 : B) : (term1077 B _77863 _77865) = (term1078 B _77863 _77865).
Proof. exact (MK_COMB (@lem6168573) (@lem6168572 B _77863 _77865)). Qed.
Lemma lem6168576 (a : Prop) : (term1075 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6168577 {B : Type'} (_77862 : type1400 B) (_77864 : type1400 B) : (term1079 B _77862 _77864) = (_77862 = _77864).
Proof. exact (@lem6168576 (_77862 = _77864)). Qed.
Lemma lem6168578 {B : Type'} (_77863 : B) (_77865 : B) (_77862 : type1400 B) (_77864 : type1400 B) : (term1074 B _77863 _77865 _77862 _77864) = (term1080 B _77863 _77865 _77862 _77864).
Proof. exact (MK_COMB (@lem6168574 B _77863 _77865) (@lem6168577 B _77862 _77864)). Qed.
Lemma lem6168579 {B : Type'} (_77863 : B) (_77865 : B) (_77862 : type1400 B) (_77864 : type1400 B) : (term1073 B _77863 _77865 _77862 _77864) = (term1080 B _77863 _77865 _77862 _77864).
Proof. exact (TRANS (@lem6168569 B _77863 _77865 _77862 _77864) (@lem6168578 B _77863 _77865 _77862 _77864)). Qed.
Lemma lem6168580 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6168581 {B : Type'} (_77863 : B) (_77865 : B) (_77862 : type1400 B) (_77864 : type1400 B) : (term1081 B _77863 _77865 _77862 _77864) = (term1082 B _77863 _77865 _77862 _77864).
Proof. exact (MK_COMB (@lem6168580) (@lem6168579 B _77863 _77865 _77862 _77864)). Qed.
Lemma lem6168582 {B : Type'} (_77862 : type1400 B) (_77863 : B) (_77864 : type1400 B) (_77865 : B) : ((@I (B -> B -> B) _77862 _77863) = (@I (B -> B -> B) _77864 _77865)) = ((@I (B -> B -> B) _77862 _77863) = (@I (B -> B -> B) _77864 _77865)).
Proof. exact (eq_refl ((@I (B -> B -> B) _77862 _77863) = (@I (B -> B -> B) _77864 _77865))). Qed.
Lemma lem6168583 {B : Type'} (_77862 : type1400 B) (_77863 : B) (_77864 : type1400 B) (_77865 : B) : (term1069 B _77862 _77863 _77864 _77865) = (term1083 B _77862 _77863 _77864 _77865).
Proof. exact (MK_COMB (@lem6168581 B _77863 _77865 _77862 _77864) (@lem6168582 B _77862 _77863 _77864 _77865)). Qed.
Lemma lem6168584 {B : Type'} (_77862 : type1400 B) (_77863 : B) (_77864 : type1400 B) (_77865 : B) : (term1064 B _77863 _77865 _77862 _77864) = (term1083 B _77862 _77863 _77864 _77865).
Proof. exact (TRANS (@lem6168566 B _77862 _77863 _77864 _77865) (@lem6168583 B _77862 _77863 _77864 _77865)). Qed.
Lemma lem6168586 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : term1084 A B f x' op.
Proof. exact (conj (@lem6168464 A B f x' op h1) (@lem6168473 B op)). Qed.
Lemma lem6168588 {B : Type'} (_77862 : type1400 B) (_77863 : B) (_77864 : type1400 B) (_77865 : B) : term1083 B _77862 _77863 _77864 _77865.
Proof. exact (EQ_MP (@lem6168584 B _77862 _77863 _77864 _77865) (@lem6168563 B _77863 _77865 _77862 _77864)). Qed.
Lemma lem6168589 {B : Type'} (_77862 : type1400 B) (_77863 : B) (_77864 : type1400 B) (_77865 : B) : term1083 B _77862 _77863 _77864 _77865.
Proof. exact (@lem6168588 B _77862 _77863 _77864 _77865). Qed.
Lemma lem6168590 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : term1085 A B f x' op.
Proof. exact (@lem6168589 B op (@I (A -> B) f x') op (@I ((B -> B -> B) -> B) (@neutral B) op)). Qed.
Lemma lem6168593 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (term841 A B op f x') = (term749 B op).
Proof. exact (@lem6168590 A B f x' op (@lem6168586 A B f x' op h1)). Qed.
Lemma lem6168594 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : term1086 A B f x' op.
Proof. exact (fun h0 : term1087 A B f x' op => @lem6168593 A B f x' op h1). Qed.
Lemma lem6168596 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6168597 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : (term1086 A B f x' op) = ((term841 A B op f x') = (term749 B op)).
Proof. exact (@lem6168596 ((term841 A B op f x') = (term749 B op))). Qed.
Lemma lem6168598 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (term841 A B op f x') = (term749 B op).
Proof. exact (EQ_MP (@lem6168597 A B f x' op) (@lem6168594 A B f x' op h1)). Qed.
Lemma lem6168616 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6168617 {B : Type'} (_77867 : B) (_77869 : B) (_77866 : B -> B) (_77868 : B -> B) : (term1052 B _77866 _77867 _77868 _77869) = (term1088 B _77867 _77869 _77866 _77868).
Proof. exact (@lem6168616 ((@I (B -> B) _77866 _77867) = (@I (B -> B) _77868 _77869)) (term1089 B _77866 _77868)). Qed.
Lemma lem6168627 {B : Type'} (_77867 : B) (_77869 : B) : (term1061 B _77867 _77869) = (term1061 B _77867 _77869).
Proof. exact (eq_refl (term1061 B _77867 _77869)). Qed.
Lemma lem6168628 {B : Type'} (_77867 : B) (_77869 : B) (_77866 : B -> B) (_77868 : B -> B) : (term1054 B _77866 _77867 _77868 _77869) = (term1090 B _77867 _77869 _77866 _77868).
Proof. exact (MK_COMB (@lem6168627 B _77867 _77869) (@lem6168617 B _77867 _77869 _77866 _77868)). Qed.
Lemma lem6168632 (q : Prop) (p : Prop) (r : Prop) : (term1063 p q r) = (term1063 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6168633 {B : Type'} (_77867 : B) (_77869 : B) (_77866 : B -> B) (_77868 : B -> B) : (term1090 B _77867 _77869 _77866 _77868) = (term1091 B _77867 _77869 _77866 _77868).
Proof. exact (@lem6168632 ((@I (B -> B) _77866 _77867) = (@I (B -> B) _77868 _77869)) (term1065 B _77867 _77869) (term1089 B _77866 _77868)). Qed.
Lemma lem6168655 {B : Type'} (_77867 : B) (_77869 : B) (_77866 : B -> B) (_77868 : B -> B) : (term1054 B _77866 _77867 _77868 _77869) = (term1091 B _77867 _77869 _77866 _77868).
Proof. exact (TRANS (@lem6168628 B _77867 _77869 _77866 _77868) (@lem6168633 B _77867 _77869 _77866 _77868)). Qed.
Lemma lem6168656 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6168657 {B : Type'} (_77867 : B) (_77869 : B) (_77866 : B -> B) (_77868 : B -> B) : (term1092 B _77866 _77867 _77868 _77869) = (term1093 B _77867 _77869 _77866 _77868).
Proof. exact (MK_COMB (@lem6168656) (@lem6168655 B _77867 _77869 _77866 _77868)). Qed.
Lemma lem6168679 {B : Type'} (_77867 : B) (_77869 : B) (_77866 : B -> B) (_77868 : B -> B) : (term1091 B _77867 _77869 _77866 _77868) = (term1091 B _77867 _77869 _77866 _77868).
Proof. exact (eq_refl (term1091 B _77867 _77869 _77866 _77868)). Qed.
Lemma lem6168680 {B : Type'} (_77867 : B) (_77869 : B) (_77866 : B -> B) (_77868 : B -> B) : ((term1054 B _77866 _77867 _77868 _77869) = (term1091 B _77867 _77869 _77866 _77868)) = ((term1091 B _77867 _77869 _77866 _77868) = (term1091 B _77867 _77869 _77866 _77868)).
Proof. exact (MK_COMB (@lem6168657 B _77867 _77869 _77866 _77868) (@lem6168679 B _77867 _77869 _77866 _77868)). Qed.
Lemma lem6168682 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6168683 (x : Prop) : (x = x) = True.
Proof. exact (@lem6168682 Prop x). Qed.
Lemma lem6168684 {B : Type'} (_77867 : B) (_77869 : B) (_77866 : B -> B) (_77868 : B -> B) : ((term1091 B _77867 _77869 _77866 _77868) = (term1091 B _77867 _77869 _77866 _77868)) = True.
Proof. exact (@lem6168683 (term1091 B _77867 _77869 _77866 _77868)). Qed.
Lemma lem6168685 {B : Type'} (_77867 : B) (_77869 : B) (_77866 : B -> B) (_77868 : B -> B) : ((term1054 B _77866 _77867 _77868 _77869) = (term1091 B _77867 _77869 _77866 _77868)) = True.
Proof. exact (TRANS (@lem6168680 B _77867 _77869 _77866 _77868) (@lem6168684 B _77867 _77869 _77866 _77868)). Qed.
Lemma lem6168686 {B : Type'} (_77867 : B) (_77869 : B) (_77866 : B -> B) (_77868 : B -> B) : True = ((term1054 B _77866 _77867 _77868 _77869) = (term1091 B _77867 _77869 _77866 _77868)).
Proof. exact (SYM (@lem6168685 B _77867 _77869 _77866 _77868)). Qed.
Lemma lem6168687 {B : Type'} (_77867 : B) (_77869 : B) (_77866 : B -> B) (_77868 : B -> B) : (term1054 B _77866 _77867 _77868 _77869) = (term1091 B _77867 _77869 _77866 _77868).
Proof. exact (EQ_MP (@lem6168686 B _77867 _77869 _77866 _77868) (@lem0)). Qed.
Lemma lem6168688 {B : Type'} (_77867 : B) (_77869 : B) (_77866 : B -> B) (_77868 : B -> B) : term1091 B _77867 _77869 _77866 _77868.
Proof. exact (EQ_MP (@lem6168687 B _77867 _77869 _77866 _77868) (@lem6168364 B _77866 _77867 _77868 _77869)). Qed.
Lemma lem6168690 (b : Prop) (a : Prop) : (a \/ b) = (term1068 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6168691 {B : Type'} (_77866 : B -> B) (_77867 : B) (_77868 : B -> B) (_77869 : B) : (term1091 B _77867 _77869 _77866 _77868) = (term1094 B _77866 _77867 _77868 _77869).
Proof. exact (@lem6168690 (term1095 B _77867 _77869 _77866 _77868) ((@I (B -> B) _77866 _77867) = (@I (B -> B) _77868 _77869))). Qed.
Lemma lem6168693 (a : Prop) (b : Prop) : (term1071 a b) = (term1072 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6168694 {B : Type'} (_77867 : B) (_77869 : B) (_77866 : B -> B) (_77868 : B -> B) : (term1096 B _77867 _77869 _77866 _77868) = (term1097 B _77867 _77869 _77866 _77868).
Proof. exact (@lem6168693 (term1065 B _77867 _77869) (term1089 B _77866 _77868)). Qed.
Lemma lem6168696 (a : Prop) : (term1075 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6168697 {B : Type'} (_77867 : B) (_77869 : B) : (term1076 B _77867 _77869) = (_77867 = _77869).
Proof. exact (@lem6168696 (_77867 = _77869)). Qed.
Lemma lem6168698 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6168699 {B : Type'} (_77867 : B) (_77869 : B) : (term1077 B _77867 _77869) = (term1078 B _77867 _77869).
Proof. exact (MK_COMB (@lem6168698) (@lem6168697 B _77867 _77869)). Qed.
Lemma lem6168701 (a : Prop) : (term1075 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6168702 {B : Type'} (_77866 : B -> B) (_77868 : B -> B) : (term1098 B _77866 _77868) = (_77866 = _77868).
Proof. exact (@lem6168701 (_77866 = _77868)). Qed.
Lemma lem6168703 {B : Type'} (_77867 : B) (_77869 : B) (_77866 : B -> B) (_77868 : B -> B) : (term1097 B _77867 _77869 _77866 _77868) = (term1099 B _77867 _77869 _77866 _77868).
Proof. exact (MK_COMB (@lem6168699 B _77867 _77869) (@lem6168702 B _77866 _77868)). Qed.
Lemma lem6168704 {B : Type'} (_77867 : B) (_77869 : B) (_77866 : B -> B) (_77868 : B -> B) : (term1096 B _77867 _77869 _77866 _77868) = (term1099 B _77867 _77869 _77866 _77868).
Proof. exact (TRANS (@lem6168694 B _77867 _77869 _77866 _77868) (@lem6168703 B _77867 _77869 _77866 _77868)). Qed.
Lemma lem6168705 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6168706 {B : Type'} (_77867 : B) (_77869 : B) (_77866 : B -> B) (_77868 : B -> B) : (term1100 B _77867 _77869 _77866 _77868) = (term1101 B _77867 _77869 _77866 _77868).
Proof. exact (MK_COMB (@lem6168705) (@lem6168704 B _77867 _77869 _77866 _77868)). Qed.
Lemma lem6168707 {B : Type'} (_77866 : B -> B) (_77867 : B) (_77868 : B -> B) (_77869 : B) : ((@I (B -> B) _77866 _77867) = (@I (B -> B) _77868 _77869)) = ((@I (B -> B) _77866 _77867) = (@I (B -> B) _77868 _77869)).
Proof. exact (eq_refl ((@I (B -> B) _77866 _77867) = (@I (B -> B) _77868 _77869))). Qed.
Lemma lem6168708 {B : Type'} (_77866 : B -> B) (_77867 : B) (_77868 : B -> B) (_77869 : B) : (term1094 B _77866 _77867 _77868 _77869) = (term1102 B _77866 _77867 _77868 _77869).
Proof. exact (MK_COMB (@lem6168706 B _77867 _77869 _77866 _77868) (@lem6168707 B _77866 _77867 _77868 _77869)). Qed.
Lemma lem6168709 {B : Type'} (_77866 : B -> B) (_77867 : B) (_77868 : B -> B) (_77869 : B) : (term1091 B _77867 _77869 _77866 _77868) = (term1102 B _77866 _77867 _77868 _77869).
Proof. exact (TRANS (@lem6168691 B _77866 _77867 _77868 _77869) (@lem6168708 B _77866 _77867 _77868 _77869)). Qed.
Lemma lem6168711 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : term1103 A B g f x' op.
Proof. exact (conj (@lem6168457 A B g x' op h2) (@lem6168598 A B f x' op h1)). Qed.
Lemma lem6168713 {B : Type'} (_77866 : B -> B) (_77867 : B) (_77868 : B -> B) (_77869 : B) : term1102 B _77866 _77867 _77868 _77869.
Proof. exact (EQ_MP (@lem6168709 B _77866 _77867 _77868 _77869) (@lem6168688 B _77867 _77869 _77866 _77868)). Qed.
Lemma lem6168714 {B : Type'} (_77866 : B -> B) (_77867 : B) (_77868 : B -> B) (_77869 : B) : term1102 B _77866 _77867 _77868 _77869.
Proof. exact (@lem6168713 B _77866 _77867 _77868 _77869). Qed.
Lemma lem6168715 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) : term1104 A B f g x' op.
Proof. exact (@lem6168714 B (term841 A B op f x') (@I (A -> B) g x') (term749 B op) (@I ((B -> B -> B) -> B) (@neutral B) op)). Qed.
Lemma lem6168718 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (term843 A B op f g x') = (term1105 B op).
Proof. exact (@lem6168715 A B f g x' op (@lem6168711 A B f g x' op h1 h2)). Qed.
Lemma lem6168719 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : term1106 A B f g x' op.
Proof. exact (fun h0 : term1107 A B f g x' op => @lem6168718 A B f g x' op h1 h2). Qed.
Lemma lem6168721 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6168722 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) : (term1106 A B f g x' op) = ((term843 A B op f g x') = (term1105 B op)).
Proof. exact (@lem6168721 ((term843 A B op f g x') = (term1105 B op))). Qed.
Lemma lem6168723 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (term843 A B op f g x') = (term1105 B op).
Proof. exact (EQ_MP (@lem6168722 A B f g x' op) (@lem6168719 A B f g x' op h1 h2)). Qed.
Lemma lem6168725 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem6168726 {B : Type'} (x : B) : x = x.
Proof. exact (@lem6168725 B x). Qed.
Lemma lem6168727 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x' : A) : (term843 A B op f g x') = (term843 A B op f g x').
Proof. exact (@lem6168726 B (term843 A B op f g x')). Qed.
Lemma lem6168728 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x' : A) : term1108 A B op f g x'.
Proof. exact (fun h0 : term1109 A B op f g x' => @lem6168727 A B op f g x'). Qed.
Lemma lem6168730 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6168731 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x' : A) : (term1108 A B op f g x') = ((term843 A B op f g x') = (term843 A B op f g x')).
Proof. exact (@lem6168730 ((term843 A B op f g x') = (term843 A B op f g x'))). Qed.
Lemma lem6168732 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x' : A) : (term843 A B op f g x') = (term843 A B op f g x').
Proof. exact (EQ_MP (@lem6168731 A B op f g x') (@lem6168728 A B op f g x')). Qed.
Lemma lem6168750 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6168751 {B : Type'} (y : B) (x : B) (z : B) : (term1110 B x y z) = (term1111 B y x z).
Proof. exact (@lem6168750 (y = z) (term1065 B x z)). Qed.
Lemma lem6168761 {B : Type'} (x : B) (y : B) : (term1061 B x y) = (term1061 B x y).
Proof. exact (eq_refl (term1061 B x y)). Qed.
Lemma lem6168762 {B : Type'} (y : B) (x : B) (z : B) : (term1055 B x y z) = (term1112 B y x z).
Proof. exact (MK_COMB (@lem6168761 B x y) (@lem6168751 B y x z)). Qed.
Lemma lem6168766 (q : Prop) (p : Prop) (r : Prop) : (term1063 p q r) = (term1063 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6168767 {B : Type'} (y : B) (x : B) (z : B) : (term1112 B y x z) = (term1113 B y x z).
Proof. exact (@lem6168766 (y = z) (term1065 B x y) (term1065 B x z)). Qed.
Lemma lem6168789 {B : Type'} (y : B) (x : B) (z : B) : (term1055 B x y z) = (term1113 B y x z).
Proof. exact (TRANS (@lem6168762 B y x z) (@lem6168767 B y x z)). Qed.
Lemma lem6168790 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6168791 {B : Type'} (y : B) (x : B) (z : B) : (term1114 B x y z) = (term1115 B y x z).
Proof. exact (MK_COMB (@lem6168790) (@lem6168789 B y x z)). Qed.
Lemma lem6168813 {B : Type'} (y : B) (x : B) (z : B) : (term1113 B y x z) = (term1113 B y x z).
Proof. exact (eq_refl (term1113 B y x z)). Qed.
Lemma lem6168814 {B : Type'} (y : B) (x : B) (z : B) : ((term1055 B x y z) = (term1113 B y x z)) = ((term1113 B y x z) = (term1113 B y x z)).
Proof. exact (MK_COMB (@lem6168791 B y x z) (@lem6168813 B y x z)). Qed.
Lemma lem6168816 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6168817 (x : Prop) : (x = x) = True.
Proof. exact (@lem6168816 Prop x). Qed.
Lemma lem6168818 {B : Type'} (y : B) (x : B) (z : B) : ((term1113 B y x z) = (term1113 B y x z)) = True.
Proof. exact (@lem6168817 (term1113 B y x z)). Qed.
Lemma lem6168819 {B : Type'} (y : B) (x : B) (z : B) : ((term1055 B x y z) = (term1113 B y x z)) = True.
Proof. exact (TRANS (@lem6168814 B y x z) (@lem6168818 B y x z)). Qed.
Lemma lem6168820 {B : Type'} (y : B) (x : B) (z : B) : True = ((term1055 B x y z) = (term1113 B y x z)).
Proof. exact (SYM (@lem6168819 B y x z)). Qed.
Lemma lem6168821 {B : Type'} (y : B) (x : B) (z : B) : (term1055 B x y z) = (term1113 B y x z).
Proof. exact (EQ_MP (@lem6168820 B y x z) (@lem0)). Qed.
Lemma lem6168822 {B : Type'} (y : B) (x : B) (z : B) : term1113 B y x z.
Proof. exact (EQ_MP (@lem6168821 B y x z) (@lem6168438 B x y z)). Qed.
Lemma lem6168824 (b : Prop) (a : Prop) : (a \/ b) = (term1068 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6168825 {B : Type'} (x : B) (y : B) (z : B) : (term1113 B y x z) = (term1116 B x y z).
Proof. exact (@lem6168824 (term1117 B y x z) (y = z)). Qed.
Lemma lem6168827 (a : Prop) (b : Prop) : (term1071 a b) = (term1072 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6168828 {B : Type'} (y : B) (x : B) (z : B) : (term1118 B y x z) = (term1119 B y x z).
Proof. exact (@lem6168827 (term1065 B x y) (term1065 B x z)). Qed.
Lemma lem6168830 (a : Prop) : (term1075 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6168831 {B : Type'} (x : B) (y : B) : (term1076 B x y) = (x = y).
Proof. exact (@lem6168830 (x = y)). Qed.
Lemma lem6168832 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6168833 {B : Type'} (x : B) (y : B) : (term1077 B x y) = (term1078 B x y).
Proof. exact (MK_COMB (@lem6168832) (@lem6168831 B x y)). Qed.
Lemma lem6168835 (a : Prop) : (term1075 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6168836 {B : Type'} (x : B) (z : B) : (term1076 B x z) = (x = z).
Proof. exact (@lem6168835 (x = z)). Qed.
Lemma lem6168837 {B : Type'} (y : B) (x : B) (z : B) : (term1119 B y x z) = (term1120 B y x z).
Proof. exact (MK_COMB (@lem6168833 B x y) (@lem6168836 B x z)). Qed.
Lemma lem6168838 {B : Type'} (y : B) (x : B) (z : B) : (term1118 B y x z) = (term1120 B y x z).
Proof. exact (TRANS (@lem6168828 B y x z) (@lem6168837 B y x z)). Qed.
Lemma lem6168839 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6168840 {B : Type'} (y : B) (x : B) (z : B) : (term1121 B y x z) = (term1122 B y x z).
Proof. exact (MK_COMB (@lem6168839) (@lem6168838 B y x z)). Qed.
Lemma lem6168841 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem6168842 {B : Type'} (x : B) (y : B) (z : B) : (term1116 B x y z) = (term1123 B x y z).
Proof. exact (MK_COMB (@lem6168840 B y x z) (@lem6168841 B y z)). Qed.
Lemma lem6168843 {B : Type'} (x : B) (y : B) (z : B) : (term1113 B y x z) = (term1123 B x y z).
Proof. exact (TRANS (@lem6168825 B x y z) (@lem6168842 B x y z)). Qed.
Lemma lem6168845 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : term1124 A B op f g x'.
Proof. exact (conj (@lem6168723 A B f g x' op h1 h2) (@lem6168732 A B op f g x')). Qed.
Lemma lem6168847 {B : Type'} (x : B) (y : B) (z : B) : term1123 B x y z.
Proof. exact (EQ_MP (@lem6168843 B x y z) (@lem6168822 B y x z)). Qed.
Lemma lem6168848 {B : Type'} (x : B) (y : B) (z : B) : term1123 B x y z.
Proof. exact (@lem6168847 B x y z). Qed.
Lemma lem6168849 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x' : A) : term1125 A B op f g x'.
Proof. exact (@lem6168848 B (term843 A B op f g x') (term1105 B op) (term843 A B op f g x')). Qed.
Lemma lem6168852 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (term1105 B op) = (term843 A B op f g x').
Proof. exact (@lem6168849 A B op f g x' (@lem6168845 A B f g x' op h1 h2)). Qed.
Lemma lem6168853 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : term1126 A B op f g x'.
Proof. exact (fun h0 : term1127 A B op f g x' => @lem6168852 A B f g x' op h1 h2). Qed.
Lemma lem6168855 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6168856 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (x' : A) : (term1126 A B op f g x') = ((term1105 B op) = (term843 A B op f g x')).
Proof. exact (@lem6168855 ((term1105 B op) = (term843 A B op f g x'))). Qed.
Lemma lem6168857 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (term1105 B op) = (term843 A B op f g x').
Proof. exact (EQ_MP (@lem6168856 A B op f g x') (@lem6168853 A B f g x' op h1 h2)). Qed.
Lemma lem6168859 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @I ((B -> B -> B) -> Prop) (@monoidal B) op.
Proof. exact (EQ_MP (@lem6163557 B op) (@lem6162621 B op h1)). Qed.
Lemma lem6168860 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term1128 B op.
Proof. exact (fun h0 : term785 B op => @lem6168859 B op h1). Qed.
Lemma lem6168862 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6168863 {B : Type'} (op : type1400 B) : (term1128 B op) = (@I ((B -> B -> B) -> Prop) (@monoidal B) op).
Proof. exact (@lem6168862 (@I ((B -> B -> B) -> Prop) (@monoidal B) op)). Qed.
Lemma lem6168864 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @I ((B -> B -> B) -> Prop) (@monoidal B) op.
Proof. exact (EQ_MP (@lem6168863 B op) (@lem6168860 B op h1)). Qed.
Lemma lem6168870 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6168871 {B : Type'} (_77703 : B) (_77702 : type1400 B) : (term1041 B _77702 _77703) = (term1129 B _77703 _77702).
Proof. exact (@lem6168870 ((term751 B _77702 _77703) = _77703) (term785 B _77702)). Qed.
Lemma lem6168879 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6168880 {B : Type'} (_77703 : B) (_77702 : type1400 B) : (term1130 B _77702 _77703) = (term1131 B _77703 _77702).
Proof. exact (MK_COMB (@lem6168879) (@lem6168871 B _77703 _77702)). Qed.
Lemma lem6168888 {B : Type'} (_77703 : B) (_77702 : type1400 B) : (term1129 B _77703 _77702) = (term1129 B _77703 _77702).
Proof. exact (eq_refl (term1129 B _77703 _77702)). Qed.
Lemma lem6168889 {B : Type'} (_77703 : B) (_77702 : type1400 B) : ((term1041 B _77702 _77703) = (term1129 B _77703 _77702)) = ((term1129 B _77703 _77702) = (term1129 B _77703 _77702)).
Proof. exact (MK_COMB (@lem6168880 B _77703 _77702) (@lem6168888 B _77703 _77702)). Qed.
Lemma lem6168891 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6168892 (x : Prop) : (x = x) = True.
Proof. exact (@lem6168891 Prop x). Qed.
Lemma lem6168893 {B : Type'} (_77703 : B) (_77702 : type1400 B) : ((term1129 B _77703 _77702) = (term1129 B _77703 _77702)) = True.
Proof. exact (@lem6168892 (term1129 B _77703 _77702)). Qed.
Lemma lem6168894 {B : Type'} (_77703 : B) (_77702 : type1400 B) : ((term1041 B _77702 _77703) = (term1129 B _77703 _77702)) = True.
Proof. exact (TRANS (@lem6168889 B _77703 _77702) (@lem6168893 B _77703 _77702)). Qed.
Lemma lem6168895 {B : Type'} (_77703 : B) (_77702 : type1400 B) : True = ((term1041 B _77702 _77703) = (term1129 B _77703 _77702)).
Proof. exact (SYM (@lem6168894 B _77703 _77702)). Qed.
Lemma lem6168896 {B : Type'} (_77703 : B) (_77702 : type1400 B) : (term1041 B _77702 _77703) = (term1129 B _77703 _77702).
Proof. exact (EQ_MP (@lem6168895 B _77703 _77702) (@lem0)). Qed.
Lemma lem6168897 {B : Type'} (_77703 : B) (_77702 : type1400 B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term738 B y z x) : term1129 B _77703 _77702.
Proof. exact (EQ_MP (@lem6168896 B _77703 _77702) (@lem6167461 B _77702 _77703 y z x h1)). Qed.
Lemma lem6168899 (b : Prop) (a : Prop) : (a \/ b) = (term1068 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6168900 {B : Type'} (_77702 : type1400 B) (_77703 : B) : (term1129 B _77703 _77702) = (term1132 B _77702 _77703).
Proof. exact (@lem6168899 (term785 B _77702) ((term751 B _77702 _77703) = _77703)). Qed.
Lemma lem6168902 (a : Prop) : (term1075 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6168903 {B : Type'} (_77702 : type1400 B) : (term1133 B _77702) = (@I ((B -> B -> B) -> Prop) (@monoidal B) _77702).
Proof. exact (@lem6168902 (@I ((B -> B -> B) -> Prop) (@monoidal B) _77702)). Qed.
Lemma lem6168904 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6168905 {B : Type'} (_77702 : type1400 B) : (term1134 B _77702) = (term1135 B _77702).
Proof. exact (MK_COMB (@lem6168904) (@lem6168903 B _77702)). Qed.
Lemma lem6168906 {B : Type'} (_77702 : type1400 B) (_77703 : B) : ((term751 B _77702 _77703) = _77703) = ((term751 B _77702 _77703) = _77703).
Proof. exact (eq_refl ((term751 B _77702 _77703) = _77703)). Qed.
Lemma lem6168907 {B : Type'} (_77702 : type1400 B) (_77703 : B) : (term1132 B _77702 _77703) = (term1136 B _77702 _77703).
Proof. exact (MK_COMB (@lem6168905 B _77702) (@lem6168906 B _77702 _77703)). Qed.
Lemma lem6168908 {B : Type'} (_77702 : type1400 B) (_77703 : B) : (term1129 B _77703 _77702) = (term1136 B _77702 _77703).
Proof. exact (TRANS (@lem6168900 B _77702 _77703) (@lem6168907 B _77702 _77703)). Qed.
Lemma lem6168911 {B : Type'} (_77702 : type1400 B) (_77703 : B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term738 B y z x) : term1136 B _77702 _77703.
Proof. exact (EQ_MP (@lem6168908 B _77702 _77703) (@lem6168897 B _77703 _77702 y z x h1)). Qed.
Lemma lem6168912 {B : Type'} (_77702 : type1400 B) (_77703 : B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term738 B y z x) : term1136 B _77702 _77703.
Proof. exact (@lem6168911 B _77702 _77703 y z x h1). Qed.
Lemma lem6168913 {B : Type'} (op : type1400 B) (_77703 : B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term738 B y z x) : term1136 B op _77703.
Proof. exact (@lem6168912 B op _77703 y z x h1). Qed.
Lemma lem6168916 {B : Type'} (_77703 : B) (op : type1400 B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : @monoidal B op) (h2 : term738 B y z x) : (term751 B op _77703) = _77703.
Proof. exact (@lem6168913 B op _77703 y z x h2 (@lem6168864 B op h1)). Qed.
Lemma lem6168917 {B : Type'} (_77703 : B) (op : type1400 B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : @monoidal B op) (h2 : term738 B y z x) : (term751 B op _77703) = _77703.
Proof. exact (@lem6168916 B _77703 op y z x h1 h2). Qed.
Lemma lem6168918 {B : Type'} (op : type1400 B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : @monoidal B op) (h2 : term738 B y z x) : (term1105 B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem6168917 B (@I ((B -> B -> B) -> B) (@neutral B) op) op y z x h1 h2). Qed.
Lemma lem6168919 {B : Type'} (op : type1400 B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : @monoidal B op) (h2 : term738 B y z x) : term1137 B op.
Proof. exact (fun h0 : term1138 B op => @lem6168918 B op y z x h1 h2). Qed.
Lemma lem6168921 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6168922 {B : Type'} (op : type1400 B) : (term1137 B op) = ((term1105 B op) = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (@lem6168921 ((term1105 B op) = (@I ((B -> B -> B) -> B) (@neutral B) op))). Qed.
Lemma lem6168923 {B : Type'} (op : type1400 B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : @monoidal B op) (h2 : term738 B y z x) : (term1105 B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (EQ_MP (@lem6168922 B op) (@lem6168919 B op y z x h1 h2)). Qed.
Lemma lem6168924 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : @monoidal B op) (h2 : term738 B y z x) (h3 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) (h4 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : term1139 A B f g x' op.
Proof. exact (conj (@lem6168857 A B f g x' op h3 h4) (@lem6168923 B op y z x h1 h2)). Qed.
Lemma lem6168926 {B : Type'} (x : B) (y : B) (z : B) : term1123 B x y z.
Proof. exact (EQ_MP (@lem6168843 B x y z) (@lem6168822 B y x z)). Qed.
Lemma lem6168927 {B : Type'} (x : B) (y : B) (z : B) : term1123 B x y z.
Proof. exact (@lem6168926 B x y z). Qed.
Lemma lem6168928 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) : term1140 A B f g x' op.
Proof. exact (@lem6168927 B (term1105 B op) (term843 A B op f g x') (@I ((B -> B -> B) -> B) (@neutral B) op)). Qed.
Lemma lem6168931 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : @monoidal B op) (h2 : term738 B y z x) (h3 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) (h4 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem6168928 A B f g x' op (@lem6168924 A B y z x f g x' op h1 h2 h3 h4)). Qed.
Lemma lem6168932 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : @monoidal B op) (h2 : term738 B y z x) (h3 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) (h4 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : term1141 A B f g x' op.
Proof. exact (fun h0 : term845 A B f g x' op => @lem6168931 A B y z x f g x' op h1 h2 h3 h4). Qed.
Lemma lem6168934 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6168935 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) : (term1141 A B f g x' op) = ((term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (@lem6168934 ((term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op))). Qed.
Lemma lem6168936 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : @monoidal B op) (h2 : term738 B y z x) (h3 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) (h4 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (EQ_MP (@lem6168935 A B f g x' op) (@lem6168932 A B y z x f g x' op h1 h2 h3 h4)). Qed.
Lemma lem6168939 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6168941 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) : (term845 A B f g x' op) = (term1142 A B f g x' op).
Proof. exact (@lem6168939 ((term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op))). Qed.
Lemma lem6168944 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term867 A B f s g x' op) : term1142 A B f g x' op.
Proof. exact (EQ_MP (@lem6168941 A B f g x' op) (@lem6167439 A B f s g x' op h1)). Qed.
Lemma lem6168947 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : @monoidal B op) (h2 : term738 B y z x) (h3 : term867 A B f s g x' op) (h4 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) (h5 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (@lem6168944 A B f s g x' op h3 (@lem6168936 A B y z x f g x' op h1 h2 h4 h5)). Qed.
Lemma lem6168948 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : @monoidal B op) (h2 : term738 B y z x) (h3 : term867 A B f s g x' op) (h4 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) (h5 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : term1045.
Proof. exact (fun h0 : ~ False => @lem6168947 A B y z x s f g x' op h1 h2 h3 h4 h5). Qed.
Lemma lem6168950 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6168951 : term1045 = False.
Proof. exact (@lem6168950 False). Qed.
Lemma lem6168952 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : @monoidal B op) (h2 : term738 B y z x) (h3 : term867 A B f s g x' op) (h4 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) (h5 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6168951) (@lem6168948 A B y z x s f g x' op h1 h2 h3 h4 h5)). Qed.
Lemma lem6169138 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s f x' op) : term846 A x' s.
Proof. exact (proj1 (@lem6164426 A B s f x' op h1)). Qed.
Lemma lem6169139 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s f x' op) : term1042 A x' s.
Proof. exact (fun h0 : term848 A x' s => @lem6169138 A B s f x' op h1). Qed.
Lemma lem6169141 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6169142 {A : Type'} (x' : A) (s : A -> Prop) : (term1042 A x' s) = (term846 A x' s).
Proof. exact (@lem6169141 (term846 A x' s)). Qed.
Lemma lem6169143 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s f x' op) : term846 A x' s.
Proof. exact (EQ_MP (@lem6169142 A x' s) (@lem6169139 A B s f x' op h1)). Qed.
Lemma lem6169146 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6169148 {A : Type'} (x' : A) (s : A -> Prop) : (term848 A x' s) = (term1044 A x' s).
Proof. exact (@lem6169146 (term846 A x' s)). Qed.
Lemma lem6169151 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term1044 A x' s.
Proof. exact (EQ_MP (@lem6169148 A x' s) (@lem6167485 A x' s h1)). Qed.
Lemma lem6169154 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s f x' op) : False.
Proof. exact (@lem6169151 A x' s h1 (@lem6169143 A B s f x' op h2)). Qed.
Lemma lem6169155 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s f x' op) : term1045.
Proof. exact (fun h0 : ~ False => @lem6169154 A B s f x' op h1 h2). Qed.
Lemma lem6169157 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6169158 : term1045 = False.
Proof. exact (@lem6169157 False). Qed.
Lemma lem6169159 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s f x' op) : False.
Proof. exact (EQ_MP (@lem6169158) (@lem6169155 A B s f x' op h1 h2)). Qed.
Lemma lem6169345 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s g x' op) : term846 A x' s.
Proof. exact (proj1 (@lem6164427 A B s g x' op h1)). Qed.
Lemma lem6169346 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s g x' op) : term1042 A x' s.
Proof. exact (fun h0 : term848 A x' s => @lem6169345 A B s g x' op h1). Qed.
Lemma lem6169348 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6169349 {A : Type'} (x' : A) (s : A -> Prop) : (term1042 A x' s) = (term846 A x' s).
Proof. exact (@lem6169348 (term846 A x' s)). Qed.
Lemma lem6169350 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s g x' op) : term846 A x' s.
Proof. exact (EQ_MP (@lem6169349 A x' s) (@lem6169346 A B s g x' op h1)). Qed.
Lemma lem6169353 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6169355 {A : Type'} (x' : A) (s : A -> Prop) : (term848 A x' s) = (term1044 A x' s).
Proof. exact (@lem6169353 (term846 A x' s)). Qed.
Lemma lem6169358 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term1044 A x' s.
Proof. exact (EQ_MP (@lem6169355 A x' s) (@lem6167531 A x' s h1)). Qed.
Lemma lem6169361 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s g x' op) : False.
Proof. exact (@lem6169358 A x' s h1 (@lem6169350 A B s g x' op h2)). Qed.
Lemma lem6169362 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s g x' op) : term1045.
Proof. exact (fun h0 : ~ False => @lem6169361 A B s g x' op h1 h2). Qed.
Lemma lem6169364 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6169365 : term1045 = False.
Proof. exact (@lem6169364 False). Qed.
Lemma lem6169366 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s g x' op) : False.
Proof. exact (EQ_MP (@lem6169365) (@lem6169362 A B s g x' op h1 h2)). Qed.
Lemma lem6169552 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (h1). Qed.
Lemma lem6169553 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : term1141 A B f g x' op.
Proof. exact (fun h0 : term845 A B f g x' op => @lem6169552 A B f g x' op h1). Qed.
Lemma lem6169555 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6169556 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) : (term1141 A B f g x' op) = ((term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (@lem6169555 ((term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op))). Qed.
Lemma lem6169557 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (EQ_MP (@lem6169556 A B f g x' op) (@lem6169553 A B f g x' op h1)). Qed.
Lemma lem6169560 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6169562 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) : (term845 A B f g x' op) = (term1142 A B f g x' op).
Proof. exact (@lem6169560 ((term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op))). Qed.
Lemma lem6169565 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term861 A B s f g x' op) : term1142 A B f g x' op.
Proof. exact (EQ_MP (@lem6169562 A B f g x' op) (@lem6167575 A B s f g x' op h1)). Qed.
Lemma lem6169568 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term861 A B s f g x' op) (h2 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (@lem6169565 A B s f g x' op h1 (@lem6169557 A B f g x' op h2)). Qed.
Lemma lem6169569 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term861 A B s f g x' op) (h2 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : term1045.
Proof. exact (fun h0 : ~ False => @lem6169568 A B s f g x' op h1 h2). Qed.
Lemma lem6169571 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6169572 : term1045 = False.
Proof. exact (@lem6169571 False). Qed.
Lemma lem6169573 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term861 A B s f g x' op) (h2 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6169572) (@lem6169569 A B s f g x' op h1 h2)). Qed.
Lemma lem6169759 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (h1). Qed.
Lemma lem6169760 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : term1141 A B f g x' op.
Proof. exact (fun h0 : term845 A B f g x' op => @lem6169759 A B f g x' op h1). Qed.
Lemma lem6169762 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6169763 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) : (term1141 A B f g x' op) = ((term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (@lem6169762 ((term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op))). Qed.
Lemma lem6169764 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (EQ_MP (@lem6169763 A B f g x' op) (@lem6169760 A B f g x' op h1)). Qed.
Lemma lem6169767 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6169769 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) : (term845 A B f g x' op) = (term1142 A B f g x' op).
Proof. exact (@lem6169767 ((term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op))). Qed.
Lemma lem6169772 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term861 A B s f g x' op) : term1142 A B f g x' op.
Proof. exact (EQ_MP (@lem6169769 A B f g x' op) (@lem6167621 A B s f g x' op h1)). Qed.
Lemma lem6169775 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term861 A B s f g x' op) (h2 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (@lem6169772 A B s f g x' op h1 (@lem6169764 A B f g x' op h2)). Qed.
Lemma lem6169776 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term861 A B s f g x' op) (h2 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : term1045.
Proof. exact (fun h0 : ~ False => @lem6169775 A B s f g x' op h1 h2). Qed.
Lemma lem6169778 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6169779 : term1045 = False.
Proof. exact (@lem6169778 False). Qed.
Lemma lem6169780 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term861 A B s f g x' op) (h2 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6169779) (@lem6169776 A B s f g x' op h1 h2)). Qed.
Lemma lem6169781 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term861 A B s f g x' op) (h2 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : ((term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) = False.
Proof. exact (prop_ext (fun h3 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6169780 A B s f g x' op h1 h2) (fun h3 : False => @lem6167623 A B f g x' op h2)). Qed.
Lemma lem6169782 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term861 A B s f g x' op) (h2 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6169781 A B s f g x' op h1 h2) (@lem6167623 A B f g x' op h2)). Qed.
Lemma lem6169783 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term861 A B s f g x' op) (h2 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : ((term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) = False.
Proof. exact (prop_ext (fun h3 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6169573 A B s f g x' op h1 h2) (fun h3 : False => @lem6167577 A B f g x' op h2)). Qed.
Lemma lem6169784 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term861 A B s f g x' op) (h2 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6169783 A B s f g x' op h1 h2) (@lem6167577 A B f g x' op h2)). Qed.
Lemma lem6169785 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6169366 A B s g x' op h1 h2) (fun h3 : False => @lem6167531 A x' s h1)). Qed.
Lemma lem6169786 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s g x' op) : False.
Proof. exact (EQ_MP (@lem6169785 A B s g x' op h1 h2) (@lem6167531 A x' s h1)). Qed.
Lemma lem6169787 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s f x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6169159 A B s f x' op h1 h2) (fun h3 : False => @lem6167485 A x' s h1)). Qed.
Lemma lem6169788 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s f x' op) : False.
Proof. exact (EQ_MP (@lem6169787 A B s f x' op h1 h2) (@lem6167485 A x' s h1)). Qed.
Lemma lem6169789 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : @monoidal B op) (h2 : term738 B y z x) (h3 : term867 A B f s g x' op) (h4 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) (h5 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : ((@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) = False.
Proof. exact (prop_ext (fun h6 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6168952 A B y z x s f g x' op h1 h2 h3 h4 h5) (fun h6 : False => @lem6167443 A B f x' op h4)). Qed.
Lemma lem6169790 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : @monoidal B op) (h2 : term738 B y z x) (h3 : term867 A B f s g x' op) (h4 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) (h5 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6169789 A B y z x s f g x' op h1 h2 h3 h4 h5) (@lem6167443 A B f x' op h4)). Qed.
Lemma lem6169791 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : @monoidal B op) (h2 : term738 B y z x) (h3 : term867 A B f s g x' op) (h4 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) (h5 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : ((@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) = False.
Proof. exact (prop_ext (fun h6 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6169790 A B y z x s f g x' op h1 h2 h3 h4 h5) (fun h6 : False => @lem6167441 A B g x' op h5)). Qed.
Lemma lem6169792 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : @monoidal B op) (h2 : term738 B y z x) (h3 : term867 A B f s g x' op) (h4 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) (h5 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6169791 A B y z x s f g x' op h1 h2 h3 h4 h5) (@lem6167441 A B g x' op h5)). Qed.
Lemma lem6169793 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6168266 A B f s g x' op h1 h2) (fun h3 : False => @lem6167397 A x' s h1)). Qed.
Lemma lem6169794 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6169793 A B f s g x' op h1 h2) (@lem6167397 A x' s h1)). Qed.
Lemma lem6169795 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6168059 A B f s g x' op h1 h2) (fun h3 : False => @lem6167349 A x' s h1)). Qed.
Lemma lem6169796 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6169795 A B f s g x' op h1 h2) (@lem6167349 A x' s h1)). Qed.
Lemma lem6169797 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6167852 A B f s g x' op h1 h2) (fun h3 : False => @lem6167305 A x' s h1)). Qed.
Lemma lem6169798 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6169797 A B f s g x' op h1 h2) (@lem6167305 A x' s h1)). Qed.
Lemma lem6169799 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6169798 A B f s g x' op h1 h2) (fun h3 : False => @lem6167303 A x' s h1)). Qed.
Lemma lem6169800 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6169799 A B f s g x' op h1 h2) (@lem6167303 A x' s h1)). Qed.
Lemma lem6169801 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term861 A B s f g x' op) (h2 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : ((term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) = False.
Proof. exact (prop_ext (fun h3 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6169782 A B s f g x' op h1 h2) (fun h3 : False => @lem6167117 A B f g x' op h2)). Qed.
Lemma lem6169802 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term861 A B s f g x' op) (h2 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6169801 A B s f g x' op h1 h2) (@lem6167117 A B f g x' op h2)). Qed.
Lemma lem6169803 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term861 A B s f g x' op) (h2 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : ((term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) = False.
Proof. exact (prop_ext (fun h3 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6169784 A B s f g x' op h1 h2) (fun h3 : False => @lem6166781 A B f g x' op h2)). Qed.
Lemma lem6169804 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term861 A B s f g x' op) (h2 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6169803 A B s f g x' op h1 h2) (@lem6166781 A B f g x' op h2)). Qed.
Lemma lem6169805 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6169786 A B s g x' op h1 h2) (fun h3 : False => @lem6166445 A x' s h1)). Qed.
Lemma lem6169806 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s g x' op) : False.
Proof. exact (EQ_MP (@lem6169805 A B s g x' op h1 h2) (@lem6166445 A x' s h1)). Qed.
Lemma lem6169807 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s f x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6169788 A B s f x' op h1 h2) (fun h3 : False => @lem6166109 A x' s h1)). Qed.
Lemma lem6169808 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s f x' op) : False.
Proof. exact (EQ_MP (@lem6169807 A B s f x' op h1 h2) (@lem6166109 A x' s h1)). Qed.
Lemma lem6169809 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : @monoidal B op) (h2 : term738 B y z x) (h3 : term867 A B f s g x' op) (h4 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) (h5 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : ((@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) = False.
Proof. exact (prop_ext (fun h6 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6169792 A B y z x s f g x' op h1 h2 h3 h4 h5) (fun h6 : False => @lem6165781 A B f x' op h4)). Qed.
Lemma lem6169810 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : @monoidal B op) (h2 : term738 B y z x) (h3 : term867 A B f s g x' op) (h4 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) (h5 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6169809 A B y z x s f g x' op h1 h2 h3 h4 h5) (@lem6165781 A B f x' op h4)). Qed.
Lemma lem6169811 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : @monoidal B op) (h2 : term738 B y z x) (h3 : term867 A B f s g x' op) (h4 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) (h5 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : ((@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) = False.
Proof. exact (prop_ext (fun h6 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6169810 A B y z x s f g x' op h1 h2 h3 h4 h5) (fun h6 : False => @lem6165777 A B g x' op h5)). Qed.
Lemma lem6169812 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : @monoidal B op) (h2 : term738 B y z x) (h3 : term867 A B f s g x' op) (h4 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) (h5 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6169811 A B y z x s f g x' op h1 h2 h3 h4 h5) (@lem6165777 A B g x' op h5)). Qed.
Lemma lem6169813 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6169794 A B f s g x' op h1 h2) (fun h3 : False => @lem6165445 A x' s h1)). Qed.
Lemma lem6169814 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6169813 A B f s g x' op h1 h2) (@lem6165445 A x' s h1)). Qed.
Lemma lem6169815 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6169796 A B f s g x' op h1 h2) (fun h3 : False => @lem6165105 A x' s h1)). Qed.
Lemma lem6169816 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6169815 A B f s g x' op h1 h2) (@lem6165105 A x' s h1)). Qed.
Lemma lem6169817 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6169800 A B f s g x' op h1 h2) (fun h3 : False => @lem6164773 A x' s h1)). Qed.
Lemma lem6169818 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6169817 A B f s g x' op h1 h2) (@lem6164773 A x' s h1)). Qed.
Lemma lem6169819 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6169818 A B f s g x' op h1 h2) (fun h3 : False => @lem6164769 A x' s h1)). Qed.
Lemma lem6169820 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6169819 A B f s g x' op h1 h2) (@lem6164769 A x' s h1)). Qed.
Lemma lem6169821 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term861 A B s f g x' op) (h2 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : ((term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) = False.
Proof. exact (prop_ext (fun h3 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6169802 A B s f g x' op h1 h2) (fun h3 : False => @lem6167117 A B f g x' op h2)). Qed.
Lemma lem6169822 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term861 A B s f g x' op) (h2 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6169821 A B s f g x' op h1 h2) (@lem6167117 A B f g x' op h2)). Qed.
Lemma lem6169823 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term861 A B s f g x' op) (h2 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : ((term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) = False.
Proof. exact (prop_ext (fun h3 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6169804 A B s f g x' op h1 h2) (fun h3 : False => @lem6166781 A B f g x' op h2)). Qed.
Lemma lem6169824 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term861 A B s f g x' op) (h2 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6169823 A B s f g x' op h1 h2) (@lem6166781 A B f g x' op h2)). Qed.
Lemma lem6169825 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6169806 A B s g x' op h1 h2) (fun h3 : False => @lem6166445 A x' s h1)). Qed.
Lemma lem6169826 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s g x' op) : False.
Proof. exact (EQ_MP (@lem6169825 A B s g x' op h1 h2) (@lem6166445 A x' s h1)). Qed.
Lemma lem6169827 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s f x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6169808 A B s f x' op h1 h2) (fun h3 : False => @lem6166109 A x' s h1)). Qed.
Lemma lem6169828 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s f x' op) : False.
Proof. exact (EQ_MP (@lem6169827 A B s f x' op h1 h2) (@lem6166109 A x' s h1)). Qed.
Lemma lem6169829 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : @monoidal B op) (h2 : term738 B y z x) (h3 : term867 A B f s g x' op) (h4 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) (h5 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : ((@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) = False.
Proof. exact (prop_ext (fun h6 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6169812 A B y z x s f g x' op h1 h2 h3 h4 h5) (fun h6 : False => @lem6165781 A B f x' op h4)). Qed.
Lemma lem6169830 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : @monoidal B op) (h2 : term738 B y z x) (h3 : term867 A B f s g x' op) (h4 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) (h5 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6169829 A B y z x s f g x' op h1 h2 h3 h4 h5) (@lem6165781 A B f x' op h4)). Qed.
Lemma lem6169831 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : @monoidal B op) (h2 : term738 B y z x) (h3 : term867 A B f s g x' op) (h4 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) (h5 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : ((@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) = False.
Proof. exact (prop_ext (fun h6 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6169830 A B y z x s f g x' op h1 h2 h3 h4 h5) (fun h6 : False => @lem6165777 A B g x' op h5)). Qed.
Lemma lem6169832 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : @monoidal B op) (h2 : term738 B y z x) (h3 : term867 A B f s g x' op) (h4 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) (h5 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6169831 A B y z x s f g x' op h1 h2 h3 h4 h5) (@lem6165777 A B g x' op h5)). Qed.
Lemma lem6169833 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6169814 A B f s g x' op h1 h2) (fun h3 : False => @lem6165445 A x' s h1)). Qed.
Lemma lem6169834 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6169833 A B f s g x' op h1 h2) (@lem6165445 A x' s h1)). Qed.
Lemma lem6169835 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6169816 A B f s g x' op h1 h2) (fun h3 : False => @lem6165105 A x' s h1)). Qed.
Lemma lem6169836 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6169835 A B f s g x' op h1 h2) (@lem6165105 A x' s h1)). Qed.
Lemma lem6169837 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6169820 A B f s g x' op h1 h2) (fun h3 : False => @lem6164773 A x' s h1)). Qed.
Lemma lem6169838 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6169837 A B f s g x' op h1 h2) (@lem6164773 A x' s h1)). Qed.
Lemma lem6169839 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6169838 A B f s g x' op h1 h2) (fun h3 : False => @lem6164769 A x' s h1)). Qed.
Lemma lem6169840 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6169839 A B f s g x' op h1 h2) (@lem6164769 A x' s h1)). Qed.
Lemma lem6169841 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term861 A B s f g x' op) (h2 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (or_elim (@lem6164423 A B s f g x' op h1) (fun h0 : term855 A B s f x' op => @lem6169824 A B s f g x' op h1 h2) (fun h0 : term855 A B s g x' op => @lem6169822 A B s f g x' op h1 h2)). Qed.
Lemma lem6169842 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term861 A B s f g x' op) : False.
Proof. exact (or_elim (@lem6164423 A B s f g x' op h2) (fun h0 : term855 A B s f x' op => @lem6169828 A B s f x' op h1 h0) (fun h0 : term855 A B s g x' op => @lem6169826 A B s g x' op h1 h0)). Qed.
Lemma lem6169843 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term861 A B s f g x' op) : False.
Proof. exact (or_elim (@lem6164422 A B s f g x' op h1) (fun h0 : term848 A x' s => @lem6169842 A B s f g x' op h0 h1) (fun h0 : (term843 A B op f g x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6169841 A B s f g x' op h1 h0)). Qed.
Lemma lem6169844 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : @monoidal B op) (h2 : term738 B y z x) (h3 : term867 A B f s g x' op) (h4 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (or_elim (@lem6164411 A B f s g x' op h3) (fun h0 : term848 A x' s => @lem6169834 A B f s g x' op h0 h3) (fun h0 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6169832 A B y z x s f g x' op h1 h2 h3 h0 h4)). Qed.
Lemma lem6169845 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term867 A B f s g x' op) : False.
Proof. exact (or_elim (@lem6164411 A B f s g x' op h2) (fun h0 : term848 A x' s => @lem6169840 A B f s g x' op h1 h2) (fun h0 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6169836 A B f s g x' op h1 h2)). Qed.
Lemma lem6169846 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : @monoidal B op) (h2 : term738 B y z x) (h3 : term867 A B f s g x' op) : False.
Proof. exact (or_elim (@lem6164410 A B f s g x' op h3) (fun h0 : term848 A x' s => @lem6169845 A B f s g x' op h0 h3) (fun h0 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6169844 A B y z x f s g x' op h1 h2 h3 h0)). Qed.
Lemma lem6169847 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (op : type1400 B) (h1 : @monoidal B op) (h2 : term738 B y z x) (h3 : term370 A B s f g x' op) : False.
Proof. exact (or_elim (@lem6164403 A B s f g x' op h3) (fun h0 : term867 A B f s g x' op => @lem6169846 A B y z x f s g x' op h1 h2 h0) (fun h0 : term861 A B s f g x' op => @lem6169843 A B s f g x' op h0)). Qed.
Lemma lem6169848 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : @monoidal B op) (h2 : term256 A B s f g op) (h3 : term738 B y z x) : False.
Proof. exact (ex_elim (@lem6162849 A B s f g op h2) (fun x' : A => fun h0 : term372 A B s f g op x' => @lem6169847 A B y z x s f g x' op h1 h3 h0)). Qed.
Lemma lem6169849 {A B : Type'} (y : type402 B) (x : type402 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term741 B y x) (h2 : @monoidal B op) (h3 : term256 A B s f g op) : False.
Proof. exact (ex_elim (@lem6163547 B y x h1) (fun z : type402 B => fun h0 : term740 B y x z => @lem6169848 A B s f g op y z x h2 h3 h0)). Qed.
Lemma lem6169850 {A B : Type'} (x : type402 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term743 B x) (h2 : @monoidal B op) (h3 : term256 A B s f g op) : False.
Proof. exact (ex_elim (@lem6163546 B x h1) (fun y : type402 B => fun h0 : term742 B x y => @lem6169849 A B y x s f g op h0 h2 h3)). Qed.
Lemma lem6169851 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term257 B) (h2 : @monoidal B op) (h3 : term256 A B s f g op) : False.
Proof. exact (ex_elim (@lem6163545 B h1) (fun x : type402 B => fun h0 : term744 B x => @lem6169850 A B x s f g op h0 h2 h3)). Qed.
Lemma lem6169852 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term257 B) (h2 : @monoidal B op) (h3 : term256 A B s f g op) : (@monoidal B op) = False.
Proof. exact (prop_ext (fun h4 : @monoidal B op => @lem6169851 A B s f g op h1 h2 h3) (fun h4 : False => @lem6162621 B op h2)). Qed.
Lemma lem6169853 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term257 B) (h2 : @monoidal B op) (h3 : term256 A B s f g op) : False.
Proof. exact (EQ_MP (@lem6169852 A B s f g op h1 h2 h3) (@lem6162621 B op h2)). Qed.
Lemma lem6169854 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) (h2 : term256 A B s f g op) : term262 B.
Proof. exact (fun h0 : term257 B => @lem6169853 A B s f g op h0 h1 h2). Qed.
Lemma lem6169855 {B : Type'} : (term262 B) = (term263 B).
Proof. exact (@lem69 (term257 B)). Qed.
Lemma lem6169856 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) (h2 : term256 A B s f g op) : term263 B.
Proof. exact (EQ_MP (@lem6169855 B) (@lem6169854 A B s f g op h1 h2)). Qed.
Lemma lem6169857 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term266 A B s f g op.
Proof. exact (fun h0 : term256 A B s f g op => @lem6169856 A B s f g op h1 h0). Qed.
Lemma lem6169858 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term269 A B s f g op.
Proof. exact (fun h0 : term58 A B op g s => @lem6169857 A B s f g op h1). Qed.
Lemma lem6169859 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term271 A B s f g op.
Proof. exact (fun h0 : term58 A B op f s => @lem6169858 A B s f g op h1). Qed.
Lemma lem6169860 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : term273 A B s f g op.
Proof. exact (fun h0 : @monoidal B op => @lem6169859 A B s f g op h0). Qed.
Lemma lem6169865 {A B : Type'} (f : A -> B) (g : A -> B) (op : type1400 B) : term277 A B f g op.
Proof. exact (fun s : A -> Prop => @lem6169860 A B s f g op). Qed.
Lemma lem6169870 {A B : Type'} (g : A -> B) (op : type1400 B) : term281 A B g op.
Proof. exact (fun f : A -> B => @lem6169865 A B f g op). Qed.
Lemma lem6169875 {A B : Type'} (op : type1400 B) : term285 A B op.
Proof. exact (fun g : A -> B => @lem6169870 A B g op). Qed.
Lemma lem6169880 {A B : Type'} : term289 A B.
Proof. exact (fun op : type1400 B => @lem6169875 A B op). Qed.
Lemma lem6169881 {A B : Type'} : term288 A B.
Proof. exact (EQ_MP (@lem6162610 A B) (@lem6169880 A B)). Qed.
Lemma lem6169882 {A B : Type'} (op : type1400 B) : term1143 A B op.
Proof. exact (@lem6169881 A B op). Qed.
Lemma lem6169883 {A B : Type'} (op : type1400 B) : (term1143 A B op) = (term284 A B op).
Proof. exact (eq_refl (term1143 A B op)). Qed.
Lemma lem6169884 {A B : Type'} (op : type1400 B) : term284 A B op.
Proof. exact (EQ_MP (@lem6169883 A B op) (@lem6169882 A B op)). Qed.
Lemma lem6169885 {A B : Type'} (op : type1400 B) (g : A -> B) : term1144 A B op g.
Proof. exact (@lem6169884 A B op g). Qed.
Lemma lem6169886 {A B : Type'} (g : A -> B) (op : type1400 B) : (term1144 A B op g) = (term280 A B g op).
Proof. exact (eq_refl (term1144 A B op g)). Qed.
Lemma lem6169887 {A B : Type'} (g : A -> B) (op : type1400 B) : term280 A B g op.
Proof. exact (EQ_MP (@lem6169886 A B g op) (@lem6169885 A B op g)). Qed.
Lemma lem6169888 {A B : Type'} (g : A -> B) (op : type1400 B) (f : A -> B) : term1145 A B g op f.
Proof. exact (@lem6169887 A B g op f). Qed.
Lemma lem6169889 {A B : Type'} (f : A -> B) (g : A -> B) (op : type1400 B) : (term1145 A B g op f) = (term276 A B f g op).
Proof. exact (eq_refl (term1145 A B g op f)). Qed.
Lemma lem6169890 {A B : Type'} (f : A -> B) (g : A -> B) (op : type1400 B) : term276 A B f g op.
Proof. exact (EQ_MP (@lem6169889 A B f g op) (@lem6169888 A B g op f)). Qed.
Lemma lem6169891 {A B : Type'} (f : A -> B) (g : A -> B) (op : type1400 B) (s : A -> Prop) : term1146 A B f g op s.
Proof. exact (@lem6169890 A B f g op s). Qed.
Lemma lem6169892 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term1146 A B f g op s) = (term258 A B s f g op).
Proof. exact (eq_refl (term1146 A B f g op s)). Qed.
Lemma lem6169893 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : term258 A B s f g op.
Proof. exact (EQ_MP (@lem6169892 A B s f g op) (@lem6169891 A B f g op s)). Qed.
Lemma lem6169895 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : term258 A B s f g op.
Proof. exact (@lem6162219 A B s f g op (@lem6169893 A B s f g op)). Qed.
Lemma lem6169896 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term270 A B s f g op.
Proof. exact (@lem6169895 A B s f g op (@lem6160869 B op h1)). Qed.
Lemma lem6169897 {A B : Type'} (g : A -> B) (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : @monoidal B op) : term268 A B s f g op.
Proof. exact (@lem6169896 A B s f g op h2 (@lem6160872 A B op f s h1)). Qed.
Lemma lem6169898 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : term265 A B s f g op.
Proof. exact (@lem6169897 A B g f s op h1 h3 (@lem6160871 A B op g s h2)). Qed.
Lemma lem6169899 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) (h4 : term256 A B s f g op) : term262 B.
Proof. exact (@lem6169898 A B f g s op h1 h2 h3 (@lem6162200 A B s f g op h4)). Qed.
Lemma lem6169900 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) (h4 : term256 A B s f g op) : False.
Proof. exact (@lem6169899 A B s f g op h1 h2 h3 h4 (@lem6162201 B)). Qed.
Lemma lem6169901 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) (h4 : term256 A B s f g op) : (term256 A B s f g op) = False.
Proof. exact (prop_ext (fun h5 : term256 A B s f g op => @lem6169900 A B s f g op h1 h2 h3 h4) (fun h5 : False => @lem6162200 A B s f g op h4)). Qed.
Lemma lem6169902 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) (h4 : term256 A B s f g op) : False.
Proof. exact (EQ_MP (@lem6169901 A B s f g op h1 h2 h3 h4) (@lem6162200 A B s f g op h4)). Qed.
Lemma lem6169903 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : term255 A B s f g op.
Proof. exact (fun h0 : term256 A B s f g op => @lem6169902 A B s f g op h1 h2 h3 h0). Qed.
Lemma lem6169904 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : term207 A B s f g op.
Proof. exact (EQ_MP (@lem6162199 A B s f g op) (@lem6169903 A B f g s op h1 h2 h3)). Qed.
Lemma lem6169906 (p : Prop) : p = (term254 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6169907 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term232 A B g s f op) = (term1147 A B g s f op).
Proof. exact (@lem6169906 (term232 A B g s f op)). Qed.
Lemma lem6169908 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1147 A B g s f op) = (term232 A B g s f op).
Proof. exact (SYM (@lem6169907 A B g s f op)). Qed.
Lemma lem6169909 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term1148 A B g s f op) : term1148 A B g s f op.
Proof. exact (h1). Qed.
Lemma lem6169910 {B : Type'} : term257 B.
Proof. exact (@lem5712802 B). Qed.
Lemma lem6169915 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term1149 A B g s f op) : term1149 A B g s f op.
Proof. exact (h1). Qed.
Lemma lem6169916 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : term1150 A B g s f op.
Proof. exact (fun h0 : term1149 A B g s f op => @lem6169915 A B g s f op h0). Qed.
Lemma lem6169917 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term1150 A B g s f op) : term1150 A B g s f op.
Proof. exact (h1). Qed.
Lemma lem6169918 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term1149 A B g s f op) : term1149 A B g s f op.
Proof. exact (h1). Qed.
Lemma lem6169919 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term1149 A B g s f op) (h2 : term1150 A B g s f op) : term1149 A B g s f op.
Proof. exact (@lem6169917 A B g s f op h2 (@lem6169918 A B g s f op h1)). Qed.
Lemma lem6169920 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term1149 A B g s f op) : term1151 A B g s f op.
Proof. exact (fun h0 : term1150 A B g s f op => @lem6169919 A B g s f op h1 h0). Qed.
Lemma lem6169921 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term1150 A B g s f op) : term1150 A B g s f op.
Proof. exact (h1). Qed.
Lemma lem6169922 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term1149 A B g s f op) (h2 : term1150 A B g s f op) : term1149 A B g s f op.
Proof. exact (@lem6169920 A B g s f op h1 (@lem6169921 A B g s f op h2)). Qed.
Lemma lem6169923 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term1150 A B g s f op) : term1150 A B g s f op.
Proof. exact (fun h0 : term1149 A B g s f op => @lem6169922 A B g s f op h0 h1). Qed.
Lemma lem6169924 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : term1152 A B g s f op.
Proof. exact (fun h0 : term1150 A B g s f op => @lem6169923 A B g s f op h0). Qed.
Lemma lem6169927 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : term1150 A B g s f op.
Proof. exact (@lem6169924 A B g s f op (@lem6169916 A B g s f op)). Qed.
Lemma lem6169928 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : term1150 A B g s f op.
Proof. exact (@lem6169927 A B g s f op). Qed.
Lemma lem6169986 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6169987 {B : Type'} : (term262 B) = (term263 B).
Proof. exact (@lem6169986 (term257 B)). Qed.
Lemma lem6170020 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1153 A B g s f op) = (term1153 A B g s f op).
Proof. exact (eq_refl (term1153 A B g s f op)). Qed.
Lemma lem6170021 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1154 A B g s f op) = (term1155 A B g s f op).
Proof. exact (MK_COMB (@lem6170020 A B g s f op) (@lem6169987 B)). Qed.
Lemma lem6170024 {A B : Type'} (op : type1400 B) (g : A -> B) (s : A -> Prop) : (term267 A B op g s) = (term267 A B op g s).
Proof. exact (eq_refl (term267 A B op g s)). Qed.
Lemma lem6170025 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1156 A B g s f op) = (term1157 A B g s f op).
Proof. exact (MK_COMB (@lem6170024 A B op g s) (@lem6170021 A B g s f op)). Qed.
Lemma lem6170028 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term267 A B op f s) = (term267 A B op f s).
Proof. exact (eq_refl (term267 A B op f s)). Qed.
Lemma lem6170029 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1158 A B g s f op) = (term1159 A B g s f op).
Proof. exact (MK_COMB (@lem6170028 A B op f s) (@lem6170025 A B g s f op)). Qed.
Lemma lem6170032 {B : Type'} (op : type1400 B) : (term272 B op) = (term272 B op).
Proof. exact (eq_refl (term272 B op)). Qed.
Lemma lem6170033 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1149 A B g s f op) = (term1160 A B g s f op).
Proof. exact (MK_COMB (@lem6170032 B op) (@lem6170029 A B g s f op)). Qed.
Lemma lem6170036 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1161 A B s f op) = (term1162 A B s f op).
Proof. exact (fun_ext (fun g : A -> B => @lem6170033 A B g s f op)). Qed.
Lemma lem6170037 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem6170038 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1163 A B s f op) = (term1164 A B s f op).
Proof. exact (MK_COMB (@lem6170037 A B) (@lem6170036 A B s f op)). Qed.
Lemma lem6170043 {A B : Type'} (f : A -> B) (op : type1400 B) : (term1165 A B f op) = (term1166 A B f op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6170038 A B s f op)). Qed.
Lemma lem6170044 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6170045 {A B : Type'} (f : A -> B) (op : type1400 B) : (term1167 A B f op) = (term1168 A B f op).
Proof. exact (MK_COMB (@lem6170044 A) (@lem6170043 A B f op)). Qed.
Lemma lem6170050 {A B : Type'} (op : type1400 B) : (term1169 A B op) = (term1170 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem6170045 A B f op)). Qed.
Lemma lem6170051 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem6170052 {A B : Type'} (op : type1400 B) : (term1171 A B op) = (term1172 A B op).
Proof. exact (MK_COMB (@lem6170051 A B) (@lem6170050 A B op)). Qed.
Lemma lem6170057 {A B : Type'} : (term1173 A B) = (term1174 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6170052 A B op)). Qed.
Lemma lem6170058 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6170067 {A B : Type'} : (term1175 A B) = (term1176 A B).
Proof. exact (MK_COMB (@lem6170058 B) (@lem6170057 A B)). Qed.
Lemma lem6170068 {B : Type'} (op : type1400 B) (x : B) : ((term290 B op x) = x) = ((term290 B op x) = x).
Proof. exact (eq_refl ((term290 B op x) = x)). Qed.
Lemma lem6170069 {B : Type'} (op : type1400 B) : (term291 B op) = (term291 B op).
Proof. exact (fun_ext (fun x : B => @lem6170068 B op x)). Qed.
Lemma lem6170070 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6170071 {B : Type'} (op : type1400 B) : (term292 B op) = (term292 B op).
Proof. exact (MK_COMB (@lem6170070 B) (@lem6170069 B op)). Qed.
Lemma lem6170072 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : ((term293 B x op y z) = (term294 B op x y z)) = ((term293 B x op y z) = (term294 B op x y z)).
Proof. exact (eq_refl ((term293 B x op y z) = (term294 B op x y z))). Qed.
Lemma lem6170073 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term295 B op x y) = (term295 B op x y).
Proof. exact (fun_ext (fun z : B => @lem6170072 B op x y z)). Qed.
Lemma lem6170074 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6170075 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term296 B op x y) = (term296 B op x y).
Proof. exact (MK_COMB (@lem6170074 B) (@lem6170073 B op x y)). Qed.
Lemma lem6170076 {B : Type'} (op : type1400 B) (x : B) : (term297 B op x) = (term297 B op x).
Proof. exact (fun_ext (fun y : B => @lem6170075 B op x y)). Qed.
Lemma lem6170077 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6170078 {B : Type'} (op : type1400 B) (x : B) : (term298 B op x) = (term298 B op x).
Proof. exact (MK_COMB (@lem6170077 B) (@lem6170076 B op x)). Qed.
Lemma lem6170079 {B : Type'} (op : type1400 B) : (term299 B op) = (term299 B op).
Proof. exact (fun_ext (fun x : B => @lem6170078 B op x)). Qed.
Lemma lem6170080 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6170081 {B : Type'} (op : type1400 B) : (term300 B op) = (term300 B op).
Proof. exact (MK_COMB (@lem6170080 B) (@lem6170079 B op)). Qed.
Lemma lem6170082 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6170083 {B : Type'} (op : type1400 B) : (term301 B op) = (term301 B op).
Proof. exact (MK_COMB (@lem6170082) (@lem6170081 B op)). Qed.
Lemma lem6170084 {B : Type'} (op : type1400 B) : (term302 B op) = (term302 B op).
Proof. exact (MK_COMB (@lem6170083 B op) (@lem6170071 B op)). Qed.
Lemma lem6170085 {B : Type'} (op : type1400 B) (y : B) (x : B) : ((op x y) = (op y x)) = ((op x y) = (op y x)).
Proof. exact (eq_refl ((op x y) = (op y x))). Qed.
Lemma lem6170086 {B : Type'} (op : type1400 B) (x : B) : (term303 B op x) = (term303 B op x).
Proof. exact (fun_ext (fun y : B => @lem6170085 B op y x)). Qed.
Lemma lem6170087 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6170088 {B : Type'} (op : type1400 B) (x : B) : (term304 B op x) = (term304 B op x).
Proof. exact (MK_COMB (@lem6170087 B) (@lem6170086 B op x)). Qed.
Lemma lem6170089 {B : Type'} (op : type1400 B) : (term305 B op) = (term305 B op).
Proof. exact (fun_ext (fun x : B => @lem6170088 B op x)). Qed.
Lemma lem6170090 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6170091 {B : Type'} (op : type1400 B) : (term306 B op) = (term306 B op).
Proof. exact (MK_COMB (@lem6170090 B) (@lem6170089 B op)). Qed.
Lemma lem6170092 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6170093 {B : Type'} (op : type1400 B) : (term307 B op) = (term307 B op).
Proof. exact (MK_COMB (@lem6170092) (@lem6170091 B op)). Qed.
Lemma lem6170094 {B : Type'} (op : type1400 B) : (term308 B op) = (term308 B op).
Proof. exact (MK_COMB (@lem6170093 B op) (@lem6170084 B op)). Qed.
Lemma lem6170097 {B : Type'} (op : type1400 B) : (term309 B op) = (term309 B op).
Proof. exact (eq_refl (term309 B op)). Qed.
Lemma lem6170098 {B : Type'} (op : type1400 B) : ((@monoidal B op) = (term308 B op)) = ((@monoidal B op) = (term308 B op)).
Proof. exact (MK_COMB (@lem6170097 B op) (@lem6170094 B op)). Qed.
Lemma lem6170099 {B : Type'} : (term310 B) = (term310 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6170098 B op)). Qed.
Lemma lem6170100 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6170101 {B : Type'} : (term257 B) = (term257 B).
Proof. exact (MK_COMB (@lem6170100 B) (@lem6170099 B)). Qed.
Lemma lem6170102 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6170103 {B : Type'} : (term263 B) = (term263 B).
Proof. exact (MK_COMB (@lem6170102) (@lem6170101 B)). Qed.
Lemma lem6170136 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term226 A B g s f x op) = (term226 A B g s f x op).
Proof. exact (eq_refl (term226 A B g s f x op)). Qed.
Lemma lem6170137 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term228 A B g s f op) = (term228 A B g s f op).
Proof. exact (fun_ext (fun x : A => @lem6170136 A B g s f x op)). Qed.
Lemma lem6170138 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6170139 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term230 A B g s f op) = (term230 A B g s f op).
Proof. exact (MK_COMB (@lem6170138 A) (@lem6170137 A B g s f op)). Qed.
Lemma lem6170166 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term213 A B f s g x op) = (term213 A B f s g x op).
Proof. exact (eq_refl (term213 A B f s g x op)). Qed.
Lemma lem6170167 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term215 A B f s g op) = (term215 A B f s g op).
Proof. exact (fun_ext (fun x : A => @lem6170166 A B f s g x op)). Qed.
Lemma lem6170168 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6170169 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term216 A B f s g op) = (term216 A B f s g op).
Proof. exact (MK_COMB (@lem6170168 A) (@lem6170167 A B f s g op)). Qed.
Lemma lem6170170 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6170171 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term218 A B f s g op) = (term218 A B f s g op).
Proof. exact (MK_COMB (@lem6170170) (@lem6170169 A B f s g op)). Qed.
Lemma lem6170172 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term232 A B g s f op) = (term232 A B g s f op).
Proof. exact (MK_COMB (@lem6170171 A B f s g op) (@lem6170139 A B g s f op)). Qed.
Lemma lem6170173 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6170174 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1148 A B g s f op) = (term1148 A B g s f op).
Proof. exact (MK_COMB (@lem6170173) (@lem6170172 A B g s f op)). Qed.
Lemma lem6170175 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6170176 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1153 A B g s f op) = (term1153 A B g s f op).
Proof. exact (MK_COMB (@lem6170175) (@lem6170174 A B g s f op)). Qed.
Lemma lem6170177 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1155 A B g s f op) = (term1155 A B g s f op).
Proof. exact (MK_COMB (@lem6170176 A B g s f op) (@lem6170103 B)). Qed.
Lemma lem6170180 {A B : Type'} (op : type1400 B) (g : A -> B) (s : A -> Prop) : (term267 A B op g s) = (term267 A B op g s).
Proof. exact (eq_refl (term267 A B op g s)). Qed.
Lemma lem6170181 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1157 A B g s f op) = (term1157 A B g s f op).
Proof. exact (MK_COMB (@lem6170180 A B op g s) (@lem6170177 A B g s f op)). Qed.
Lemma lem6170184 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term267 A B op f s) = (term267 A B op f s).
Proof. exact (eq_refl (term267 A B op f s)). Qed.
Lemma lem6170185 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1159 A B g s f op) = (term1159 A B g s f op).
Proof. exact (MK_COMB (@lem6170184 A B op f s) (@lem6170181 A B g s f op)). Qed.
Lemma lem6170188 {B : Type'} (op : type1400 B) : (term272 B op) = (term272 B op).
Proof. exact (eq_refl (term272 B op)). Qed.
Lemma lem6170189 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1160 A B g s f op) = (term1160 A B g s f op).
Proof. exact (MK_COMB (@lem6170188 B op) (@lem6170185 A B g s f op)). Qed.
Lemma lem6170190 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1162 A B s f op) = (term1162 A B s f op).
Proof. exact (fun_ext (fun g : A -> B => @lem6170189 A B g s f op)). Qed.
Lemma lem6170191 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem6170192 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1164 A B s f op) = (term1164 A B s f op).
Proof. exact (MK_COMB (@lem6170191 A B) (@lem6170190 A B s f op)). Qed.
Lemma lem6170193 {A B : Type'} (f : A -> B) (op : type1400 B) : (term1166 A B f op) = (term1166 A B f op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6170192 A B s f op)). Qed.
Lemma lem6170194 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6170195 {A B : Type'} (f : A -> B) (op : type1400 B) : (term1168 A B f op) = (term1168 A B f op).
Proof. exact (MK_COMB (@lem6170194 A) (@lem6170193 A B f op)). Qed.
Lemma lem6170196 {A B : Type'} (op : type1400 B) : (term1170 A B op) = (term1170 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem6170195 A B f op)). Qed.
Lemma lem6170197 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem6170198 {A B : Type'} (op : type1400 B) : (term1172 A B op) = (term1172 A B op).
Proof. exact (MK_COMB (@lem6170197 A B) (@lem6170196 A B op)). Qed.
Lemma lem6170199 {A B : Type'} : (term1174 A B) = (term1174 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6170198 A B op)). Qed.
Lemma lem6170200 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6170201 {A B : Type'} : (term1176 A B) = (term1176 A B).
Proof. exact (MK_COMB (@lem6170200 B) (@lem6170199 A B)). Qed.
Lemma lem6170318 {A B : Type'} : (term1175 A B) = (term1176 A B).
Proof. exact (TRANS (@lem6170067 A B) (@lem6170201 A B)). Qed.
Lemma lem6170319 {A B : Type'} : (term1176 A B) = (term1175 A B).
Proof. exact (SYM (@lem6170318 A B)). Qed.
Lemma lem6170323 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term1148 A B g s f op) : term1148 A B g s f op.
Proof. exact (h1). Qed.
Lemma lem6170324 {B : Type'} (h1 : term257 B) : term257 B.
Proof. exact (h1). Qed.
Lemma lem6170351 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term311 A B f x op) = ((f x) = (@neutral B op)).
Proof. exact (@lem16933 ((f x) = (@neutral B op))). Qed.
Lemma lem6170353 {A : Type'} (x : A) (s : A -> Prop) : (term312 A x s) = (term312 A x s).
Proof. exact (eq_refl (term312 A x s)). Qed.
Lemma lem6170354 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term313 A B s f x op) = (term314 A B s f x op).
Proof. exact (MK_COMB (@lem6170353 A x s) (@lem6170351 A B f x op)). Qed.
Lemma lem6170355 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term220 A B s f x op) = (term313 A B s f x op).
Proof. exact (@lem17045 (@IN A x s) (term315 A B f x op)). Qed.
Lemma lem6170356 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term220 A B s f x op) = (term314 A B s f x op).
Proof. exact (TRANS (@lem6170355 A B s f x op) (@lem6170354 A B s f x op)). Qed.
Lemma lem6170360 {A B : Type'} (g : A -> B) (x : A) (op : type1400 B) : (term311 A B g x op) = ((g x) = (@neutral B op)).
Proof. exact (@lem16933 ((g x) = (@neutral B op))). Qed.
Lemma lem6170362 {A : Type'} (x : A) (s : A -> Prop) : (term312 A x s) = (term312 A x s).
Proof. exact (eq_refl (term312 A x s)). Qed.
Lemma lem6170363 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term313 A B s g x op) = (term314 A B s g x op).
Proof. exact (MK_COMB (@lem6170362 A x s) (@lem6170360 A B g x op)). Qed.
Lemma lem6170364 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term220 A B s g x op) = (term313 A B s g x op).
Proof. exact (@lem17045 (@IN A x s) (term315 A B g x op)). Qed.
Lemma lem6170365 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term220 A B s g x op) = (term314 A B s g x op).
Proof. exact (TRANS (@lem6170364 A B s g x op) (@lem6170363 A B s g x op)). Qed.
Lemma lem6170366 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6170367 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term316 A B s f x op) = (term317 A B s f x op).
Proof. exact (MK_COMB (@lem6170366) (@lem6170356 A B s f x op)). Qed.
Lemma lem6170368 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term318 A B f s g x op) = (term319 A B f s g x op).
Proof. exact (MK_COMB (@lem6170367 A B s f x op) (@lem6170365 A B s g x op)). Qed.
Lemma lem6170369 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term320 A B f s g x op) = (term318 A B f s g x op).
Proof. exact (@lem17160 (term168 A B s f x op) (term168 A B s g x op)). Qed.
Lemma lem6170370 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term320 A B f s g x op) = (term319 A B f s g x op).
Proof. exact (TRANS (@lem6170369 A B f s g x op) (@lem6170368 A B f s g x op)). Qed.
Lemma lem6170372 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term1177 A B s f x op) = (term1177 A B s f x op).
Proof. exact (eq_refl (term1177 A B s f x op)). Qed.
Lemma lem6170373 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term1178 A B f s g x op) = (term1179 A B f s g x op).
Proof. exact (MK_COMB (@lem6170372 A B s f x op) (@lem6170370 A B f s g x op)). Qed.
Lemma lem6170374 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term1180 A B f s g x op) = (term1178 A B f s g x op).
Proof. exact (@lem17362 (term168 A B s f x op) (term184 A B f s g x op)). Qed.
Lemma lem6170375 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term1180 A B f s g x op) = (term1179 A B f s g x op).
Proof. exact (TRANS (@lem6170374 A B f s g x op) (@lem6170373 A B f s g x op)). Qed.
Lemma lem6170376 {A : Type'} (P : A -> Prop) : (term325 A P) = (term326 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem6170377 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1181 A B f s g op) = (term1182 A B f s g op).
Proof. exact (@lem6170376 A (term215 A B f s g op)). Qed.
Lemma lem6170378 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term1183 A B f s g op x) = (term213 A B f s g x op).
Proof. exact (eq_refl (term1183 A B f s g op x)). Qed.
Lemma lem6170379 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6170380 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term1184 A B f s g op x) = (term1180 A B f s g x op).
Proof. exact (MK_COMB (@lem6170379) (@lem6170378 A B f s g x op)). Qed.
Lemma lem6170381 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term1184 A B f s g op x) = (term1179 A B f s g x op).
Proof. exact (TRANS (@lem6170380 A B f s g x op) (@lem6170375 A B f s g x op)). Qed.
Lemma lem6170382 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1185 A B f s g op) = (term1186 A B f s g op).
Proof. exact (fun_ext (fun x : A => @lem6170381 A B f s g x op)). Qed.
Lemma lem6170383 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6170384 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1182 A B f s g op) = (term1187 A B f s g op).
Proof. exact (MK_COMB (@lem6170383 A) (@lem6170382 A B f s g op)). Qed.
Lemma lem6170385 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1181 A B f s g op) = (term1187 A B f s g op).
Proof. exact (TRANS (@lem6170377 A B f s g op) (@lem6170384 A B f s g op)). Qed.
Lemma lem6170402 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term311 A B f x op) = ((f x) = (@neutral B op)).
Proof. exact (@lem16933 ((f x) = (@neutral B op))). Qed.
Lemma lem6170404 {A : Type'} (x : A) (s : A -> Prop) : (term312 A x s) = (term312 A x s).
Proof. exact (eq_refl (term312 A x s)). Qed.
Lemma lem6170405 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term313 A B s f x op) = (term314 A B s f x op).
Proof. exact (MK_COMB (@lem6170404 A x s) (@lem6170402 A B f x op)). Qed.
Lemma lem6170406 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term220 A B s f x op) = (term313 A B s f x op).
Proof. exact (@lem17045 (@IN A x s) (term315 A B f x op)). Qed.
Lemma lem6170407 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term220 A B s f x op) = (term314 A B s f x op).
Proof. exact (TRANS (@lem6170406 A B s f x op) (@lem6170405 A B s f x op)). Qed.
Lemma lem6170409 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term193 A B f s g x op) = (term193 A B f s g x op).
Proof. exact (eq_refl (term193 A B f s g x op)). Qed.
Lemma lem6170410 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term222 A B g s f x op) = (term1188 A B g s f x op).
Proof. exact (MK_COMB (@lem6170409 A B f s g x op) (@lem6170407 A B s f x op)). Qed.
Lemma lem6170411 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term315 A B f x op) = (term315 A B f x op).
Proof. exact (eq_refl (term315 A B f x op)). Qed.
Lemma lem6170412 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6170413 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term1189 A B g s f x op) = (term1190 A B g s f x op).
Proof. exact (MK_COMB (@lem6170412) (@lem6170410 A B g s f x op)). Qed.
Lemma lem6170414 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term1191 A B g s f x op) = (term1192 A B g s f x op).
Proof. exact (MK_COMB (@lem6170413 A B g s f x op) (@lem6170411 A B f x op)). Qed.
Lemma lem6170415 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term1193 A B g s f x op) = (term1191 A B g s f x op).
Proof. exact (@lem17362 (term222 A B g s f x op) ((f x) = (@neutral B op))). Qed.
Lemma lem6170416 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term1193 A B g s f x op) = (term1192 A B g s f x op).
Proof. exact (TRANS (@lem6170415 A B g s f x op) (@lem6170414 A B g s f x op)). Qed.
Lemma lem6170417 {A : Type'} (P : A -> Prop) : (term325 A P) = (term326 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem6170418 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1194 A B g s f op) = (term1195 A B g s f op).
Proof. exact (@lem6170417 A (term228 A B g s f op)). Qed.
Lemma lem6170419 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term1196 A B g s f op x) = (term226 A B g s f x op).
Proof. exact (eq_refl (term1196 A B g s f op x)). Qed.
Lemma lem6170420 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6170421 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term1197 A B g s f op x) = (term1193 A B g s f x op).
Proof. exact (MK_COMB (@lem6170420) (@lem6170419 A B g s f x op)). Qed.
Lemma lem6170422 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term1197 A B g s f op x) = (term1192 A B g s f x op).
Proof. exact (TRANS (@lem6170421 A B g s f x op) (@lem6170416 A B g s f x op)). Qed.
Lemma lem6170423 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1198 A B g s f op) = (term1199 A B g s f op).
Proof. exact (fun_ext (fun x : A => @lem6170422 A B g s f x op)). Qed.
Lemma lem6170424 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6170425 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1195 A B g s f op) = (term1200 A B g s f op).
Proof. exact (MK_COMB (@lem6170424 A) (@lem6170423 A B g s f op)). Qed.
Lemma lem6170426 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1194 A B g s f op) = (term1200 A B g s f op).
Proof. exact (TRANS (@lem6170418 A B g s f op) (@lem6170425 A B g s f op)). Qed.
Lemma lem6170427 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6170428 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1201 A B f s g op) = (term1202 A B f s g op).
Proof. exact (MK_COMB (@lem6170427) (@lem6170385 A B f s g op)). Qed.
Lemma lem6170429 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1203 A B g s f op) = (term1204 A B g s f op).
Proof. exact (MK_COMB (@lem6170428 A B f s g op) (@lem6170426 A B g s f op)). Qed.
Lemma lem6170430 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1148 A B g s f op) = (term1203 A B g s f op).
Proof. exact (@lem17045 (term216 A B f s g op) (term230 A B g s f op)). Qed.
Lemma lem6170431 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1148 A B g s f op) = (term1204 A B g s f op).
Proof. exact (TRANS (@lem6170430 A B g s f op) (@lem6170429 A B g s f op)). Qed.
Lemma lem6170530 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term354 A P Q) = (term355 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem6170531 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term354 A P Q) = (term355 A P Q).
Proof. exact (@lem6170530 A P Q). Qed.
Lemma lem6170532 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1205 A B g s f op) = (term1206 A B g s f op).
Proof. exact (@lem6170531 A (term1186 A B f s g op) (term1199 A B g s f op)). Qed.
Lemma lem6170533 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term1207 A B f s g op x) = (term1179 A B f s g x op).
Proof. exact (eq_refl (term1207 A B f s g op x)). Qed.
Lemma lem6170534 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1208 A B f s g op) = (term1186 A B f s g op).
Proof. exact (fun_ext (fun x : A => @lem6170533 A B f s g x op)). Qed.
Lemma lem6170535 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6170536 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1209 A B f s g op) = (term1187 A B f s g op).
Proof. exact (MK_COMB (@lem6170535 A) (@lem6170534 A B f s g op)). Qed.
Lemma lem6170537 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6170538 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1210 A B f s g op) = (term1202 A B f s g op).
Proof. exact (MK_COMB (@lem6170537) (@lem6170536 A B f s g op)). Qed.
Lemma lem6170539 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term1211 A B g s f op x) = (term1192 A B g s f x op).
Proof. exact (eq_refl (term1211 A B g s f op x)). Qed.
Lemma lem6170540 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1212 A B g s f op) = (term1199 A B g s f op).
Proof. exact (fun_ext (fun x : A => @lem6170539 A B g s f x op)). Qed.
Lemma lem6170541 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6170542 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1213 A B g s f op) = (term1200 A B g s f op).
Proof. exact (MK_COMB (@lem6170541 A) (@lem6170540 A B g s f op)). Qed.
Lemma lem6170543 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1205 A B g s f op) = (term1204 A B g s f op).
Proof. exact (MK_COMB (@lem6170538 A B f s g op) (@lem6170542 A B g s f op)). Qed.
Lemma lem6170544 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6170545 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1214 A B g s f op) = (term1215 A B g s f op).
Proof. exact (MK_COMB (@lem6170544) (@lem6170543 A B g s f op)). Qed.
Lemma lem6170546 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term1207 A B f s g op x) = (term1179 A B f s g x op).
Proof. exact (eq_refl (term1207 A B f s g op x)). Qed.
Lemma lem6170547 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6170548 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term1216 A B f s g op x) = (term1217 A B f s g x op).
Proof. exact (MK_COMB (@lem6170547) (@lem6170546 A B f s g x op)). Qed.
Lemma lem6170549 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term1211 A B g s f op x) = (term1192 A B g s f x op).
Proof. exact (eq_refl (term1211 A B g s f op x)). Qed.
Lemma lem6170550 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term1218 A B g s f op x) = (term1219 A B g s f x op).
Proof. exact (MK_COMB (@lem6170548 A B f s g x op) (@lem6170549 A B g s f x op)). Qed.
Lemma lem6170551 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1220 A B g s f op) = (term1221 A B g s f op).
Proof. exact (fun_ext (fun x : A => @lem6170550 A B g s f x op)). Qed.
Lemma lem6170552 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6170553 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1206 A B g s f op) = (term1222 A B g s f op).
Proof. exact (MK_COMB (@lem6170552 A) (@lem6170551 A B g s f op)). Qed.
Lemma lem6170554 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : ((term1205 A B g s f op) = (term1206 A B g s f op)) = ((term1204 A B g s f op) = (term1222 A B g s f op)).
Proof. exact (MK_COMB (@lem6170545 A B g s f op) (@lem6170553 A B g s f op)). Qed.
Lemma lem6170556 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1204 A B g s f op) = (term1222 A B g s f op).
Proof. exact (EQ_MP (@lem6170554 A B g s f op) (@lem6170532 A B g s f op)). Qed.
Lemma lem6170557 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1148 A B g s f op) = (term1222 A B g s f op).
Proof. exact (TRANS (@lem6170431 A B g s f op) (@lem6170556 A B g s f op)). Qed.
Lemma lem6170558 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term1148 A B g s f op) : term1222 A B g s f op.
Proof. exact (EQ_MP (@lem6170557 A B g s f op) (@lem6170323 A B g s f op h1)). Qed.
Lemma lem6170562 {B : Type'} (op : type1400 B) (y : B) (x : B) : ((op x y) = (op y x)) = ((op x y) = (op y x)).
Proof. exact (eq_refl ((op x y) = (op y x))). Qed.
Lemma lem6170563 {B : Type'} (P : B -> Prop) : (term325 B P) = (term326 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem6170564 {B : Type'} (op : type1400 B) (x : B) : (term374 B op x) = (term375 B op x).
Proof. exact (@lem6170563 B (term303 B op x)). Qed.
Lemma lem6170565 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term376 B op x y) = ((op x y) = (op y x)).
Proof. exact (eq_refl (term376 B op x y)). Qed.
Lemma lem6170566 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6170568 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term377 B op x y) = (term378 B op y x).
Proof. exact (MK_COMB (@lem6170566) (@lem6170565 B op y x)). Qed.
Lemma lem6170569 {B : Type'} (op : type1400 B) (x : B) : (term379 B op x) = (term380 B op x).
Proof. exact (fun_ext (fun y : B => @lem6170568 B op y x)). Qed.
Lemma lem6170570 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6170571 {B : Type'} (op : type1400 B) (x : B) : (term375 B op x) = (term381 B op x).
Proof. exact (MK_COMB (@lem6170570 B) (@lem6170569 B op x)). Qed.
Lemma lem6170572 {B : Type'} (op : type1400 B) (x : B) : (term374 B op x) = (term381 B op x).
Proof. exact (TRANS (@lem6170564 B op x) (@lem6170571 B op x)). Qed.
Lemma lem6170573 {B : Type'} (op : type1400 B) (x : B) : (term303 B op x) = (term303 B op x).
Proof. exact (fun_ext (fun y : B => @lem6170562 B op y x)). Qed.
Lemma lem6170574 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6170575 {B : Type'} (op : type1400 B) (x : B) : (term304 B op x) = (term304 B op x).
Proof. exact (MK_COMB (@lem6170574 B) (@lem6170573 B op x)). Qed.
Lemma lem6170576 {B : Type'} (P : B -> Prop) : (term325 B P) = (term326 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem6170577 {B : Type'} (op : type1400 B) : (term382 B op) = (term383 B op).
Proof. exact (@lem6170576 B (term305 B op)). Qed.
Lemma lem6170578 {B : Type'} (op : type1400 B) (x : B) : (term384 B op x) = (term304 B op x).
Proof. exact (eq_refl (term384 B op x)). Qed.
Lemma lem6170579 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6170580 {B : Type'} (op : type1400 B) (x : B) : (term385 B op x) = (term374 B op x).
Proof. exact (MK_COMB (@lem6170579) (@lem6170578 B op x)). Qed.
Lemma lem6170581 {B : Type'} (op : type1400 B) (x : B) : (term385 B op x) = (term381 B op x).
Proof. exact (TRANS (@lem6170580 B op x) (@lem6170572 B op x)). Qed.
Lemma lem6170582 {B : Type'} (op : type1400 B) : (term386 B op) = (term387 B op).
Proof. exact (fun_ext (fun x : B => @lem6170581 B op x)). Qed.
Lemma lem6170583 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6170584 {B : Type'} (op : type1400 B) : (term383 B op) = (term388 B op).
Proof. exact (MK_COMB (@lem6170583 B) (@lem6170582 B op)). Qed.
Lemma lem6170585 {B : Type'} (op : type1400 B) : (term382 B op) = (term388 B op).
Proof. exact (TRANS (@lem6170577 B op) (@lem6170584 B op)). Qed.
Lemma lem6170586 {B : Type'} (op : type1400 B) : (term305 B op) = (term305 B op).
Proof. exact (fun_ext (fun x : B => @lem6170575 B op x)). Qed.
Lemma lem6170587 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6170588 {B : Type'} (op : type1400 B) : (term306 B op) = (term306 B op).
Proof. exact (MK_COMB (@lem6170587 B) (@lem6170586 B op)). Qed.
Lemma lem6170590 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : ((term293 B x op y z) = (term294 B op x y z)) = ((term293 B x op y z) = (term294 B op x y z)).
Proof. exact (eq_refl ((term293 B x op y z) = (term294 B op x y z))). Qed.
Lemma lem6170591 {B : Type'} (P : B -> Prop) : (term325 B P) = (term326 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem6170592 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term389 B op x y) = (term390 B op x y).
Proof. exact (@lem6170591 B (term295 B op x y)). Qed.
Lemma lem6170593 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term391 B op x y z) = ((term293 B x op y z) = (term294 B op x y z)).
Proof. exact (eq_refl (term391 B op x y z)). Qed.
Lemma lem6170594 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6170596 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term392 B op x y z) = (term393 B op x y z).
Proof. exact (MK_COMB (@lem6170594) (@lem6170593 B op x y z)). Qed.
Lemma lem6170597 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term394 B op x y) = (term395 B op x y).
Proof. exact (fun_ext (fun z : B => @lem6170596 B op x y z)). Qed.
Lemma lem6170598 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6170599 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term390 B op x y) = (term396 B op x y).
Proof. exact (MK_COMB (@lem6170598 B) (@lem6170597 B op x y)). Qed.
Lemma lem6170600 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term389 B op x y) = (term396 B op x y).
Proof. exact (TRANS (@lem6170592 B op x y) (@lem6170599 B op x y)). Qed.
Lemma lem6170601 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term295 B op x y) = (term295 B op x y).
Proof. exact (fun_ext (fun z : B => @lem6170590 B op x y z)). Qed.
Lemma lem6170602 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6170603 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term296 B op x y) = (term296 B op x y).
Proof. exact (MK_COMB (@lem6170602 B) (@lem6170601 B op x y)). Qed.
Lemma lem6170604 {B : Type'} (P : B -> Prop) : (term325 B P) = (term326 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem6170605 {B : Type'} (op : type1400 B) (x : B) : (term397 B op x) = (term398 B op x).
Proof. exact (@lem6170604 B (term297 B op x)). Qed.
Lemma lem6170606 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term399 B op x y) = (term296 B op x y).
Proof. exact (eq_refl (term399 B op x y)). Qed.
Lemma lem6170607 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6170608 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term400 B op x y) = (term389 B op x y).
Proof. exact (MK_COMB (@lem6170607) (@lem6170606 B op x y)). Qed.
Lemma lem6170609 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term400 B op x y) = (term396 B op x y).
Proof. exact (TRANS (@lem6170608 B op x y) (@lem6170600 B op x y)). Qed.
Lemma lem6170610 {B : Type'} (op : type1400 B) (x : B) : (term401 B op x) = (term402 B op x).
Proof. exact (fun_ext (fun y : B => @lem6170609 B op x y)). Qed.
Lemma lem6170611 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6170612 {B : Type'} (op : type1400 B) (x : B) : (term398 B op x) = (term403 B op x).
Proof. exact (MK_COMB (@lem6170611 B) (@lem6170610 B op x)). Qed.
Lemma lem6170613 {B : Type'} (op : type1400 B) (x : B) : (term397 B op x) = (term403 B op x).
Proof. exact (TRANS (@lem6170605 B op x) (@lem6170612 B op x)). Qed.
Lemma lem6170614 {B : Type'} (op : type1400 B) (x : B) : (term297 B op x) = (term297 B op x).
Proof. exact (fun_ext (fun y : B => @lem6170603 B op x y)). Qed.
Lemma lem6170615 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6170616 {B : Type'} (op : type1400 B) (x : B) : (term298 B op x) = (term298 B op x).
Proof. exact (MK_COMB (@lem6170615 B) (@lem6170614 B op x)). Qed.
Lemma lem6170617 {B : Type'} (P : B -> Prop) : (term325 B P) = (term326 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem6170618 {B : Type'} (op : type1400 B) : (term404 B op) = (term405 B op).
Proof. exact (@lem6170617 B (term299 B op)). Qed.
Lemma lem6170619 {B : Type'} (op : type1400 B) (x : B) : (term406 B op x) = (term298 B op x).
Proof. exact (eq_refl (term406 B op x)). Qed.
Lemma lem6170620 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6170621 {B : Type'} (op : type1400 B) (x : B) : (term407 B op x) = (term397 B op x).
Proof. exact (MK_COMB (@lem6170620) (@lem6170619 B op x)). Qed.
Lemma lem6170622 {B : Type'} (op : type1400 B) (x : B) : (term407 B op x) = (term403 B op x).
Proof. exact (TRANS (@lem6170621 B op x) (@lem6170613 B op x)). Qed.
Lemma lem6170623 {B : Type'} (op : type1400 B) : (term408 B op) = (term409 B op).
Proof. exact (fun_ext (fun x : B => @lem6170622 B op x)). Qed.
Lemma lem6170624 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6170625 {B : Type'} (op : type1400 B) : (term405 B op) = (term410 B op).
Proof. exact (MK_COMB (@lem6170624 B) (@lem6170623 B op)). Qed.
Lemma lem6170626 {B : Type'} (op : type1400 B) : (term404 B op) = (term410 B op).
Proof. exact (TRANS (@lem6170618 B op) (@lem6170625 B op)). Qed.
Lemma lem6170627 {B : Type'} (op : type1400 B) : (term299 B op) = (term299 B op).
Proof. exact (fun_ext (fun x : B => @lem6170616 B op x)). Qed.
Lemma lem6170628 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6170629 {B : Type'} (op : type1400 B) : (term300 B op) = (term300 B op).
Proof. exact (MK_COMB (@lem6170628 B) (@lem6170627 B op)). Qed.
Lemma lem6170631 {B : Type'} (op : type1400 B) (x : B) : ((term290 B op x) = x) = ((term290 B op x) = x).
Proof. exact (eq_refl ((term290 B op x) = x)). Qed.
Lemma lem6170632 {B : Type'} (P : B -> Prop) : (term325 B P) = (term326 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem6170633 {B : Type'} (op : type1400 B) : (term411 B op) = (term412 B op).
Proof. exact (@lem6170632 B (term291 B op)). Qed.
Lemma lem6170634 {B : Type'} (op : type1400 B) (x : B) : (term413 B op x) = ((term290 B op x) = x).
Proof. exact (eq_refl (term413 B op x)). Qed.
Lemma lem6170635 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6170637 {B : Type'} (op : type1400 B) (x : B) : (term414 B op x) = (term415 B op x).
Proof. exact (MK_COMB (@lem6170635) (@lem6170634 B op x)). Qed.
Lemma lem6170638 {B : Type'} (op : type1400 B) : (term416 B op) = (term417 B op).
Proof. exact (fun_ext (fun x : B => @lem6170637 B op x)). Qed.
Lemma lem6170639 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6170640 {B : Type'} (op : type1400 B) : (term412 B op) = (term418 B op).
Proof. exact (MK_COMB (@lem6170639 B) (@lem6170638 B op)). Qed.
Lemma lem6170641 {B : Type'} (op : type1400 B) : (term411 B op) = (term418 B op).
Proof. exact (TRANS (@lem6170633 B op) (@lem6170640 B op)). Qed.
Lemma lem6170642 {B : Type'} (op : type1400 B) : (term291 B op) = (term291 B op).
Proof. exact (fun_ext (fun x : B => @lem6170631 B op x)). Qed.
Lemma lem6170643 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6170644 {B : Type'} (op : type1400 B) : (term292 B op) = (term292 B op).
Proof. exact (MK_COMB (@lem6170643 B) (@lem6170642 B op)). Qed.
Lemma lem6170645 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6170646 {B : Type'} (op : type1400 B) : (term419 B op) = (term420 B op).
Proof. exact (MK_COMB (@lem6170645) (@lem6170626 B op)). Qed.
Lemma lem6170647 {B : Type'} (op : type1400 B) : (term421 B op) = (term422 B op).
Proof. exact (MK_COMB (@lem6170646 B op) (@lem6170641 B op)). Qed.
Lemma lem6170648 {B : Type'} (op : type1400 B) : (term423 B op) = (term421 B op).
Proof. exact (@lem17045 (term300 B op) (term292 B op)). Qed.
Lemma lem6170649 {B : Type'} (op : type1400 B) : (term423 B op) = (term422 B op).
Proof. exact (TRANS (@lem6170648 B op) (@lem6170647 B op)). Qed.
Lemma lem6170650 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6170651 {B : Type'} (op : type1400 B) : (term301 B op) = (term301 B op).
Proof. exact (MK_COMB (@lem6170650) (@lem6170629 B op)). Qed.
Lemma lem6170652 {B : Type'} (op : type1400 B) : (term302 B op) = (term302 B op).
Proof. exact (MK_COMB (@lem6170651 B op) (@lem6170644 B op)). Qed.
Lemma lem6170653 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6170654 {B : Type'} (op : type1400 B) : (term424 B op) = (term425 B op).
Proof. exact (MK_COMB (@lem6170653) (@lem6170585 B op)). Qed.
Lemma lem6170655 {B : Type'} (op : type1400 B) : (term426 B op) = (term427 B op).
Proof. exact (MK_COMB (@lem6170654 B op) (@lem6170649 B op)). Qed.
Lemma lem6170656 {B : Type'} (op : type1400 B) : (term428 B op) = (term426 B op).
Proof. exact (@lem17045 (term306 B op) (term302 B op)). Qed.
Lemma lem6170657 {B : Type'} (op : type1400 B) : (term428 B op) = (term427 B op).
Proof. exact (TRANS (@lem6170656 B op) (@lem6170655 B op)). Qed.
Lemma lem6170658 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6170659 {B : Type'} (op : type1400 B) : (term307 B op) = (term307 B op).
Proof. exact (MK_COMB (@lem6170658) (@lem6170588 B op)). Qed.
Lemma lem6170660 {B : Type'} (op : type1400 B) : (term308 B op) = (term308 B op).
Proof. exact (MK_COMB (@lem6170659 B op) (@lem6170652 B op)). Qed.
Lemma lem6170662 {B : Type'} (op : type1400 B) : (term429 B op) = (term429 B op).
Proof. exact (eq_refl (term429 B op)). Qed.
Lemma lem6170663 {B : Type'} (op : type1400 B) : (term430 B op) = (term430 B op).
Proof. exact (MK_COMB (@lem6170662 B op) (@lem6170660 B op)). Qed.
Lemma lem6170665 {B : Type'} (op : type1400 B) : (term431 B op) = (term431 B op).
Proof. exact (eq_refl (term431 B op)). Qed.
Lemma lem6170666 {B : Type'} (op : type1400 B) : (term432 B op) = (term433 B op).
Proof. exact (MK_COMB (@lem6170665 B op) (@lem6170657 B op)). Qed.
Lemma lem6170667 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6170668 {B : Type'} (op : type1400 B) : (term434 B op) = (term435 B op).
Proof. exact (MK_COMB (@lem6170667) (@lem6170666 B op)). Qed.
Lemma lem6170669 {B : Type'} (op : type1400 B) : (term436 B op) = (term437 B op).
Proof. exact (MK_COMB (@lem6170668 B op) (@lem6170663 B op)). Qed.
Lemma lem6170670 {B : Type'} (op : type1400 B) : ((@monoidal B op) = (term308 B op)) = (term436 B op).
Proof. exact (@lem17784 (@monoidal B op) (term308 B op)). Qed.
Lemma lem6170671 {B : Type'} (op : type1400 B) : ((@monoidal B op) = (term308 B op)) = (term437 B op).
Proof. exact (TRANS (@lem6170670 B op) (@lem6170669 B op)). Qed.
Lemma lem6170672 {B : Type'} : (term310 B) = (term438 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6170671 B op)). Qed.
Lemma lem6170673 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6170674 {B : Type'} : (term257 B) = (term439 B).
Proof. exact (MK_COMB (@lem6170673 B) (@lem6170672 B)). Qed.
Lemma lem6170676 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term440 A P Q) = (term441 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6170677 {B : Type'} (P : type403 B) (Q : type403 B) : (term442 B P Q) = (term443 B P Q).
Proof. exact (@lem6170676 (type1400 B) P Q). Qed.
Lemma lem6170678 {B : Type'} : (term444 B) = (term445 B).
Proof. exact (@lem6170677 B (term446 B) (term447 B)). Qed.
Lemma lem6170679 {B : Type'} (op : type1400 B) : (term448 B op) = (term433 B op).
Proof. exact (eq_refl (term448 B op)). Qed.
Lemma lem6170680 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6170681 {B : Type'} (op : type1400 B) : (term449 B op) = (term435 B op).
Proof. exact (MK_COMB (@lem6170680) (@lem6170679 B op)). Qed.
Lemma lem6170682 {B : Type'} (op : type1400 B) : (term450 B op) = (term430 B op).
Proof. exact (eq_refl (term450 B op)). Qed.
Lemma lem6170683 {B : Type'} (op : type1400 B) : (term451 B op) = (term437 B op).
Proof. exact (MK_COMB (@lem6170681 B op) (@lem6170682 B op)). Qed.
Lemma lem6170684 {B : Type'} : (term452 B) = (term438 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6170683 B op)). Qed.
Lemma lem6170685 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6170686 {B : Type'} : (term444 B) = (term439 B).
Proof. exact (MK_COMB (@lem6170685 B) (@lem6170684 B)). Qed.
Lemma lem6170687 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6170688 {B : Type'} : (term453 B) = (term454 B).
Proof. exact (MK_COMB (@lem6170687) (@lem6170686 B)). Qed.
Lemma lem6170689 {B : Type'} (op : type1400 B) : (term448 B op) = (term433 B op).
Proof. exact (eq_refl (term448 B op)). Qed.
Lemma lem6170690 {B : Type'} : (term455 B) = (term446 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6170689 B op)). Qed.
Lemma lem6170691 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6170692 {B : Type'} : (term456 B) = (term457 B).
Proof. exact (MK_COMB (@lem6170691 B) (@lem6170690 B)). Qed.
Lemma lem6170693 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6170694 {B : Type'} : (term458 B) = (term459 B).
Proof. exact (MK_COMB (@lem6170693) (@lem6170692 B)). Qed.
Lemma lem6170695 {B : Type'} (op : type1400 B) : (term450 B op) = (term430 B op).
Proof. exact (eq_refl (term450 B op)). Qed.
Lemma lem6170696 {B : Type'} : (term460 B) = (term447 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6170695 B op)). Qed.
Lemma lem6170697 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6170698 {B : Type'} : (term461 B) = (term462 B).
Proof. exact (MK_COMB (@lem6170697 B) (@lem6170696 B)). Qed.
Lemma lem6170699 {B : Type'} : (term445 B) = (term463 B).
Proof. exact (MK_COMB (@lem6170694 B) (@lem6170698 B)). Qed.
Lemma lem6170700 {B : Type'} : ((term444 B) = (term445 B)) = ((term439 B) = (term463 B)).
Proof. exact (MK_COMB (@lem6170688 B) (@lem6170699 B)). Qed.
Lemma lem6170701 {B : Type'} : (term439 B) = (term463 B).
Proof. exact (EQ_MP (@lem6170700 B) (@lem6170678 B)). Qed.
Lemma lem6170827 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term354 A P Q) = (term355 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem6170828 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term354 B P Q) = (term355 B P Q).
Proof. exact (@lem6170827 B P Q). Qed.
Lemma lem6170829 {B : Type'} (op : type1400 B) : (term464 B op) = (term465 B op).
Proof. exact (@lem6170828 B (term409 B op) (term417 B op)). Qed.
Lemma lem6170830 {B : Type'} (op : type1400 B) (x : B) : (term466 B op x) = (term403 B op x).
Proof. exact (eq_refl (term466 B op x)). Qed.
Lemma lem6170831 {B : Type'} (op : type1400 B) : (term467 B op) = (term409 B op).
Proof. exact (fun_ext (fun x : B => @lem6170830 B op x)). Qed.
Lemma lem6170832 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6170833 {B : Type'} (op : type1400 B) : (term468 B op) = (term410 B op).
Proof. exact (MK_COMB (@lem6170832 B) (@lem6170831 B op)). Qed.
Lemma lem6170834 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6170835 {B : Type'} (op : type1400 B) : (term469 B op) = (term420 B op).
Proof. exact (MK_COMB (@lem6170834) (@lem6170833 B op)). Qed.
Lemma lem6170836 {B : Type'} (op : type1400 B) (x : B) : (term470 B op x) = (term415 B op x).
Proof. exact (eq_refl (term470 B op x)). Qed.
Lemma lem6170837 {B : Type'} (op : type1400 B) : (term471 B op) = (term417 B op).
Proof. exact (fun_ext (fun x : B => @lem6170836 B op x)). Qed.
Lemma lem6170838 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6170839 {B : Type'} (op : type1400 B) : (term472 B op) = (term418 B op).
Proof. exact (MK_COMB (@lem6170838 B) (@lem6170837 B op)). Qed.
Lemma lem6170840 {B : Type'} (op : type1400 B) : (term464 B op) = (term422 B op).
Proof. exact (MK_COMB (@lem6170835 B op) (@lem6170839 B op)). Qed.
Lemma lem6170841 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6170842 {B : Type'} (op : type1400 B) : (term473 B op) = (term474 B op).
Proof. exact (MK_COMB (@lem6170841) (@lem6170840 B op)). Qed.
Lemma lem6170843 {B : Type'} (op : type1400 B) (x : B) : (term466 B op x) = (term403 B op x).
Proof. exact (eq_refl (term466 B op x)). Qed.
Lemma lem6170844 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6170845 {B : Type'} (op : type1400 B) (x : B) : (term475 B op x) = (term476 B op x).
Proof. exact (MK_COMB (@lem6170844) (@lem6170843 B op x)). Qed.
Lemma lem6170846 {B : Type'} (op : type1400 B) (x : B) : (term470 B op x) = (term415 B op x).
Proof. exact (eq_refl (term470 B op x)). Qed.
Lemma lem6170847 {B : Type'} (op : type1400 B) (x : B) : (term477 B op x) = (term478 B op x).
Proof. exact (MK_COMB (@lem6170845 B op x) (@lem6170846 B op x)). Qed.
Lemma lem6170848 {B : Type'} (op : type1400 B) : (term479 B op) = (term480 B op).
Proof. exact (fun_ext (fun x : B => @lem6170847 B op x)). Qed.
Lemma lem6170849 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6170850 {B : Type'} (op : type1400 B) : (term465 B op) = (term481 B op).
Proof. exact (MK_COMB (@lem6170849 B) (@lem6170848 B op)). Qed.
Lemma lem6170851 {B : Type'} (op : type1400 B) : ((term464 B op) = (term465 B op)) = ((term422 B op) = (term481 B op)).
Proof. exact (MK_COMB (@lem6170842 B op) (@lem6170850 B op)). Qed.
Lemma lem6170852 {B : Type'} (op : type1400 B) : (term422 B op) = (term481 B op).
Proof. exact (EQ_MP (@lem6170851 B op) (@lem6170829 B op)). Qed.
Lemma lem6170854 {A : Type'} (P : A -> Prop) (Q : Prop) : (term482 A P Q) = (term483 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6170855 {B : Type'} (P : B -> Prop) (Q : Prop) : (term482 B P Q) = (term483 B P Q).
Proof. exact (@lem6170854 B P Q). Qed.
Lemma lem6170856 {B : Type'} (op : type1400 B) (x : B) : (term484 B op x) = (term485 B op x).
Proof. exact (@lem6170855 B (term402 B op x) (term415 B op x)). Qed.
Lemma lem6170857 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term486 B op x y) = (term396 B op x y).
Proof. exact (eq_refl (term486 B op x y)). Qed.
Lemma lem6170858 {B : Type'} (op : type1400 B) (x : B) : (term487 B op x) = (term402 B op x).
Proof. exact (fun_ext (fun y : B => @lem6170857 B op x y)). Qed.
Lemma lem6170859 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6170860 {B : Type'} (op : type1400 B) (x : B) : (term488 B op x) = (term403 B op x).
Proof. exact (MK_COMB (@lem6170859 B) (@lem6170858 B op x)). Qed.
Lemma lem6170861 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6170862 {B : Type'} (op : type1400 B) (x : B) : (term489 B op x) = (term476 B op x).
Proof. exact (MK_COMB (@lem6170861) (@lem6170860 B op x)). Qed.
Lemma lem6170863 {B : Type'} (op : type1400 B) (x : B) : (term415 B op x) = (term415 B op x).
Proof. exact (eq_refl (term415 B op x)). Qed.
Lemma lem6170864 {B : Type'} (op : type1400 B) (x : B) : (term484 B op x) = (term478 B op x).
Proof. exact (MK_COMB (@lem6170862 B op x) (@lem6170863 B op x)). Qed.
Lemma lem6170865 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6170866 {B : Type'} (op : type1400 B) (x : B) : (term490 B op x) = (term491 B op x).
Proof. exact (MK_COMB (@lem6170865) (@lem6170864 B op x)). Qed.
Lemma lem6170867 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term486 B op x y) = (term396 B op x y).
Proof. exact (eq_refl (term486 B op x y)). Qed.
Lemma lem6170868 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6170869 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term492 B op x y) = (term493 B op x y).
Proof. exact (MK_COMB (@lem6170868) (@lem6170867 B op x y)). Qed.
Lemma lem6170870 {B : Type'} (op : type1400 B) (x : B) : (term415 B op x) = (term415 B op x).
Proof. exact (eq_refl (term415 B op x)). Qed.
Lemma lem6170871 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term494 B y op x) = (term495 B y op x).
Proof. exact (MK_COMB (@lem6170869 B op x y) (@lem6170870 B op x)). Qed.
Lemma lem6170872 {B : Type'} (op : type1400 B) (x : B) : (term496 B op x) = (term497 B op x).
Proof. exact (fun_ext (fun y : B => @lem6170871 B y op x)). Qed.
Lemma lem6170873 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6170874 {B : Type'} (op : type1400 B) (x : B) : (term485 B op x) = (term498 B op x).
Proof. exact (MK_COMB (@lem6170873 B) (@lem6170872 B op x)). Qed.
Lemma lem6170875 {B : Type'} (op : type1400 B) (x : B) : ((term484 B op x) = (term485 B op x)) = ((term478 B op x) = (term498 B op x)).
Proof. exact (MK_COMB (@lem6170866 B op x) (@lem6170874 B op x)). Qed.
Lemma lem6170876 {B : Type'} (op : type1400 B) (x : B) : (term478 B op x) = (term498 B op x).
Proof. exact (EQ_MP (@lem6170875 B op x) (@lem6170856 B op x)). Qed.
Lemma lem6170878 {A : Type'} (P : A -> Prop) (Q : Prop) : (term482 A P Q) = (term483 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6170879 {B : Type'} (P : B -> Prop) (Q : Prop) : (term482 B P Q) = (term483 B P Q).
Proof. exact (@lem6170878 B P Q). Qed.
Lemma lem6170880 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term499 B y op x) = (term500 B y op x).
Proof. exact (@lem6170879 B (term395 B op x y) (term415 B op x)). Qed.
Lemma lem6170881 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term501 B op x y z) = (term393 B op x y z).
Proof. exact (eq_refl (term501 B op x y z)). Qed.
Lemma lem6170882 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term502 B op x y) = (term395 B op x y).
Proof. exact (fun_ext (fun z : B => @lem6170881 B op x y z)). Qed.
Lemma lem6170883 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6170884 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term503 B op x y) = (term396 B op x y).
Proof. exact (MK_COMB (@lem6170883 B) (@lem6170882 B op x y)). Qed.
Lemma lem6170885 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6170886 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term504 B op x y) = (term493 B op x y).
Proof. exact (MK_COMB (@lem6170885) (@lem6170884 B op x y)). Qed.
Lemma lem6170887 {B : Type'} (op : type1400 B) (x : B) : (term415 B op x) = (term415 B op x).
Proof. exact (eq_refl (term415 B op x)). Qed.
Lemma lem6170888 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term499 B y op x) = (term495 B y op x).
Proof. exact (MK_COMB (@lem6170886 B op x y) (@lem6170887 B op x)). Qed.
Lemma lem6170889 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6170890 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term505 B y op x) = (term506 B y op x).
Proof. exact (MK_COMB (@lem6170889) (@lem6170888 B y op x)). Qed.
Lemma lem6170891 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term501 B op x y z) = (term393 B op x y z).
Proof. exact (eq_refl (term501 B op x y z)). Qed.
Lemma lem6170892 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6170893 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term507 B op x y z) = (term508 B op x y z).
Proof. exact (MK_COMB (@lem6170892) (@lem6170891 B op x y z)). Qed.
Lemma lem6170894 {B : Type'} (op : type1400 B) (x : B) : (term415 B op x) = (term415 B op x).
Proof. exact (eq_refl (term415 B op x)). Qed.
Lemma lem6170895 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term509 B y z op x) = (term510 B y z op x).
Proof. exact (MK_COMB (@lem6170893 B op x y z) (@lem6170894 B op x)). Qed.
Lemma lem6170896 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term511 B y op x) = (term512 B y op x).
Proof. exact (fun_ext (fun z : B => @lem6170895 B y z op x)). Qed.
Lemma lem6170897 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6170898 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term500 B y op x) = (term513 B y op x).
Proof. exact (MK_COMB (@lem6170897 B) (@lem6170896 B y op x)). Qed.
Lemma lem6170899 {B : Type'} (y : B) (op : type1400 B) (x : B) : ((term499 B y op x) = (term500 B y op x)) = ((term495 B y op x) = (term513 B y op x)).
Proof. exact (MK_COMB (@lem6170890 B y op x) (@lem6170898 B y op x)). Qed.
Lemma lem6170900 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term495 B y op x) = (term513 B y op x).
Proof. exact (EQ_MP (@lem6170899 B y op x) (@lem6170880 B y op x)). Qed.
Lemma lem6170901 {B : Type'} (op : type1400 B) (x : B) : (term497 B op x) = (term514 B op x).
Proof. exact (fun_ext (fun y : B => @lem6170900 B y op x)). Qed.
Lemma lem6170902 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6170903 {B : Type'} (op : type1400 B) (x : B) : (term498 B op x) = (term515 B op x).
Proof. exact (MK_COMB (@lem6170902 B) (@lem6170901 B op x)). Qed.
Lemma lem6170904 {B : Type'} (op : type1400 B) (x : B) : (term478 B op x) = (term515 B op x).
Proof. exact (TRANS (@lem6170876 B op x) (@lem6170903 B op x)). Qed.
Lemma lem6170905 {B : Type'} (op : type1400 B) : (term480 B op) = (term516 B op).
Proof. exact (fun_ext (fun x : B => @lem6170904 B op x)). Qed.
Lemma lem6170906 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6170907 {B : Type'} (op : type1400 B) : (term481 B op) = (term517 B op).
Proof. exact (MK_COMB (@lem6170906 B) (@lem6170905 B op)). Qed.
Lemma lem6170908 {B : Type'} (op : type1400 B) : (term422 B op) = (term517 B op).
Proof. exact (TRANS (@lem6170852 B op) (@lem6170907 B op)). Qed.
Lemma lem6170909 {B : Type'} (op : type1400 B) : (term425 B op) = (term425 B op).
Proof. exact (eq_refl (term425 B op)). Qed.
Lemma lem6170910 {B : Type'} (op : type1400 B) : (term427 B op) = (term518 B op).
Proof. exact (MK_COMB (@lem6170909 B op) (@lem6170908 B op)). Qed.
Lemma lem6170912 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term354 A P Q) = (term355 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem6170913 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term354 B P Q) = (term355 B P Q).
Proof. exact (@lem6170912 B P Q). Qed.
Lemma lem6170914 {B : Type'} (op : type1400 B) : (term519 B op) = (term520 B op).
Proof. exact (@lem6170913 B (term387 B op) (term516 B op)). Qed.
Lemma lem6170915 {B : Type'} (op : type1400 B) (x : B) : (term521 B op x) = (term381 B op x).
Proof. exact (eq_refl (term521 B op x)). Qed.
Lemma lem6170916 {B : Type'} (op : type1400 B) : (term522 B op) = (term387 B op).
Proof. exact (fun_ext (fun x : B => @lem6170915 B op x)). Qed.
Lemma lem6170917 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6170918 {B : Type'} (op : type1400 B) : (term523 B op) = (term388 B op).
Proof. exact (MK_COMB (@lem6170917 B) (@lem6170916 B op)). Qed.
Lemma lem6170919 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6170920 {B : Type'} (op : type1400 B) : (term524 B op) = (term425 B op).
Proof. exact (MK_COMB (@lem6170919) (@lem6170918 B op)). Qed.
Lemma lem6170921 {B : Type'} (op : type1400 B) (x : B) : (term525 B op x) = (term515 B op x).
Proof. exact (eq_refl (term525 B op x)). Qed.
Lemma lem6170922 {B : Type'} (op : type1400 B) : (term526 B op) = (term516 B op).
Proof. exact (fun_ext (fun x : B => @lem6170921 B op x)). Qed.
Lemma lem6170923 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6170924 {B : Type'} (op : type1400 B) : (term527 B op) = (term517 B op).
Proof. exact (MK_COMB (@lem6170923 B) (@lem6170922 B op)). Qed.
Lemma lem6170925 {B : Type'} (op : type1400 B) : (term519 B op) = (term518 B op).
Proof. exact (MK_COMB (@lem6170920 B op) (@lem6170924 B op)). Qed.
Lemma lem6170926 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6170927 {B : Type'} (op : type1400 B) : (term528 B op) = (term529 B op).
Proof. exact (MK_COMB (@lem6170926) (@lem6170925 B op)). Qed.
Lemma lem6170928 {B : Type'} (op : type1400 B) (x : B) : (term521 B op x) = (term381 B op x).
Proof. exact (eq_refl (term521 B op x)). Qed.
Lemma lem6170929 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6170930 {B : Type'} (op : type1400 B) (x : B) : (term530 B op x) = (term531 B op x).
Proof. exact (MK_COMB (@lem6170929) (@lem6170928 B op x)). Qed.
Lemma lem6170931 {B : Type'} (op : type1400 B) (x : B) : (term525 B op x) = (term515 B op x).
Proof. exact (eq_refl (term525 B op x)). Qed.
Lemma lem6170932 {B : Type'} (op : type1400 B) (x : B) : (term532 B op x) = (term533 B op x).
Proof. exact (MK_COMB (@lem6170930 B op x) (@lem6170931 B op x)). Qed.
Lemma lem6170933 {B : Type'} (op : type1400 B) : (term534 B op) = (term535 B op).
Proof. exact (fun_ext (fun x : B => @lem6170932 B op x)). Qed.
Lemma lem6170934 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6170935 {B : Type'} (op : type1400 B) : (term520 B op) = (term536 B op).
Proof. exact (MK_COMB (@lem6170934 B) (@lem6170933 B op)). Qed.
Lemma lem6170936 {B : Type'} (op : type1400 B) : ((term519 B op) = (term520 B op)) = ((term518 B op) = (term536 B op)).
Proof. exact (MK_COMB (@lem6170927 B op) (@lem6170935 B op)). Qed.
Lemma lem6170937 {B : Type'} (op : type1400 B) : (term518 B op) = (term536 B op).
Proof. exact (EQ_MP (@lem6170936 B op) (@lem6170914 B op)). Qed.
Lemma lem6170939 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term354 A P Q) = (term355 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem6170940 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term354 B P Q) = (term355 B P Q).
Proof. exact (@lem6170939 B P Q). Qed.
Lemma lem6170941 {B : Type'} (op : type1400 B) (x : B) : (term537 B op x) = (term538 B op x).
Proof. exact (@lem6170940 B (term380 B op x) (term514 B op x)). Qed.
Lemma lem6170942 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term539 B op x y) = (term378 B op y x).
Proof. exact (eq_refl (term539 B op x y)). Qed.
Lemma lem6170943 {B : Type'} (op : type1400 B) (x : B) : (term540 B op x) = (term380 B op x).
Proof. exact (fun_ext (fun y : B => @lem6170942 B op y x)). Qed.
Lemma lem6170944 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6170945 {B : Type'} (op : type1400 B) (x : B) : (term541 B op x) = (term381 B op x).
Proof. exact (MK_COMB (@lem6170944 B) (@lem6170943 B op x)). Qed.
Lemma lem6170946 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6170947 {B : Type'} (op : type1400 B) (x : B) : (term542 B op x) = (term531 B op x).
Proof. exact (MK_COMB (@lem6170946) (@lem6170945 B op x)). Qed.
Lemma lem6170948 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term543 B op x y) = (term513 B y op x).
Proof. exact (eq_refl (term543 B op x y)). Qed.
Lemma lem6170949 {B : Type'} (op : type1400 B) (x : B) : (term544 B op x) = (term514 B op x).
Proof. exact (fun_ext (fun y : B => @lem6170948 B y op x)). Qed.
Lemma lem6170950 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6170951 {B : Type'} (op : type1400 B) (x : B) : (term545 B op x) = (term515 B op x).
Proof. exact (MK_COMB (@lem6170950 B) (@lem6170949 B op x)). Qed.
Lemma lem6170952 {B : Type'} (op : type1400 B) (x : B) : (term537 B op x) = (term533 B op x).
Proof. exact (MK_COMB (@lem6170947 B op x) (@lem6170951 B op x)). Qed.
Lemma lem6170953 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6170954 {B : Type'} (op : type1400 B) (x : B) : (term546 B op x) = (term547 B op x).
Proof. exact (MK_COMB (@lem6170953) (@lem6170952 B op x)). Qed.
Lemma lem6170955 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term539 B op x y) = (term378 B op y x).
Proof. exact (eq_refl (term539 B op x y)). Qed.
Lemma lem6170956 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6170957 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term548 B op x y) = (term549 B op y x).
Proof. exact (MK_COMB (@lem6170956) (@lem6170955 B op y x)). Qed.
Lemma lem6170958 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term543 B op x y) = (term513 B y op x).
Proof. exact (eq_refl (term543 B op x y)). Qed.
Lemma lem6170959 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term550 B op x y) = (term551 B y op x).
Proof. exact (MK_COMB (@lem6170957 B op y x) (@lem6170958 B y op x)). Qed.
Lemma lem6170960 {B : Type'} (op : type1400 B) (x : B) : (term552 B op x) = (term553 B op x).
Proof. exact (fun_ext (fun y : B => @lem6170959 B y op x)). Qed.
Lemma lem6170961 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6170962 {B : Type'} (op : type1400 B) (x : B) : (term538 B op x) = (term554 B op x).
Proof. exact (MK_COMB (@lem6170961 B) (@lem6170960 B op x)). Qed.
Lemma lem6170963 {B : Type'} (op : type1400 B) (x : B) : ((term537 B op x) = (term538 B op x)) = ((term533 B op x) = (term554 B op x)).
Proof. exact (MK_COMB (@lem6170954 B op x) (@lem6170962 B op x)). Qed.
Lemma lem6170964 {B : Type'} (op : type1400 B) (x : B) : (term533 B op x) = (term554 B op x).
Proof. exact (EQ_MP (@lem6170963 B op x) (@lem6170941 B op x)). Qed.
Lemma lem6170966 {A : Type'} (P : Prop) (Q : A -> Prop) : (term555 A P Q) = (term556 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6170967 {B : Type'} (P : Prop) (Q : B -> Prop) : (term555 B P Q) = (term556 B P Q).
Proof. exact (@lem6170966 B P Q). Qed.
Lemma lem6170968 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term557 B y op x) = (term558 B y op x).
Proof. exact (@lem6170967 B (term378 B op y x) (term512 B y op x)). Qed.
Lemma lem6170969 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term559 B y op x z) = (term510 B y z op x).
Proof. exact (eq_refl (term559 B y op x z)). Qed.
Lemma lem6170970 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term560 B y op x) = (term512 B y op x).
Proof. exact (fun_ext (fun z : B => @lem6170969 B y z op x)). Qed.
Lemma lem6170971 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6170972 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term561 B y op x) = (term513 B y op x).
Proof. exact (MK_COMB (@lem6170971 B) (@lem6170970 B y op x)). Qed.
Lemma lem6170973 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term549 B op y x) = (term549 B op y x).
Proof. exact (eq_refl (term549 B op y x)). Qed.
Lemma lem6170974 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term557 B y op x) = (term551 B y op x).
Proof. exact (MK_COMB (@lem6170973 B op y x) (@lem6170972 B y op x)). Qed.
Lemma lem6170975 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6170976 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term562 B y op x) = (term563 B y op x).
Proof. exact (MK_COMB (@lem6170975) (@lem6170974 B y op x)). Qed.
Lemma lem6170977 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term559 B y op x z) = (term510 B y z op x).
Proof. exact (eq_refl (term559 B y op x z)). Qed.
Lemma lem6170978 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term549 B op y x) = (term549 B op y x).
Proof. exact (eq_refl (term549 B op y x)). Qed.
Lemma lem6170979 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term564 B y op x z) = (term565 B y z op x).
Proof. exact (MK_COMB (@lem6170978 B op y x) (@lem6170977 B y z op x)). Qed.
Lemma lem6170980 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term566 B y op x) = (term567 B y op x).
Proof. exact (fun_ext (fun z : B => @lem6170979 B y z op x)). Qed.
Lemma lem6170981 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6170982 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term558 B y op x) = (term568 B y op x).
Proof. exact (MK_COMB (@lem6170981 B) (@lem6170980 B y op x)). Qed.
Lemma lem6170983 {B : Type'} (y : B) (op : type1400 B) (x : B) : ((term557 B y op x) = (term558 B y op x)) = ((term551 B y op x) = (term568 B y op x)).
Proof. exact (MK_COMB (@lem6170976 B y op x) (@lem6170982 B y op x)). Qed.
Lemma lem6170984 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term551 B y op x) = (term568 B y op x).
Proof. exact (EQ_MP (@lem6170983 B y op x) (@lem6170968 B y op x)). Qed.
Lemma lem6170985 {B : Type'} (op : type1400 B) (x : B) : (term553 B op x) = (term569 B op x).
Proof. exact (fun_ext (fun y : B => @lem6170984 B y op x)). Qed.
Lemma lem6170986 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6170987 {B : Type'} (op : type1400 B) (x : B) : (term554 B op x) = (term570 B op x).
Proof. exact (MK_COMB (@lem6170986 B) (@lem6170985 B op x)). Qed.
Lemma lem6170988 {B : Type'} (op : type1400 B) (x : B) : (term533 B op x) = (term570 B op x).
Proof. exact (TRANS (@lem6170964 B op x) (@lem6170987 B op x)). Qed.
Lemma lem6170989 {B : Type'} (op : type1400 B) : (term535 B op) = (term571 B op).
Proof. exact (fun_ext (fun x : B => @lem6170988 B op x)). Qed.
Lemma lem6170990 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6170991 {B : Type'} (op : type1400 B) : (term536 B op) = (term572 B op).
Proof. exact (MK_COMB (@lem6170990 B) (@lem6170989 B op)). Qed.
Lemma lem6170992 {B : Type'} (op : type1400 B) : (term518 B op) = (term572 B op).
Proof. exact (TRANS (@lem6170937 B op) (@lem6170991 B op)). Qed.
Lemma lem6170993 {B : Type'} (op : type1400 B) : (term427 B op) = (term572 B op).
Proof. exact (TRANS (@lem6170910 B op) (@lem6170992 B op)). Qed.
Lemma lem6170994 {B : Type'} (op : type1400 B) : (term431 B op) = (term431 B op).
Proof. exact (eq_refl (term431 B op)). Qed.
Lemma lem6170995 {B : Type'} (op : type1400 B) : (term433 B op) = (term573 B op).
Proof. exact (MK_COMB (@lem6170994 B op) (@lem6170993 B op)). Qed.
Lemma lem6170997 {A : Type'} (P : Prop) (Q : A -> Prop) : (term555 A P Q) = (term556 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6170998 {B : Type'} (P : Prop) (Q : B -> Prop) : (term555 B P Q) = (term556 B P Q).
Proof. exact (@lem6170997 B P Q). Qed.
Lemma lem6170999 {B : Type'} (op : type1400 B) : (term574 B op) = (term575 B op).
Proof. exact (@lem6170998 B (@monoidal B op) (term571 B op)). Qed.
Lemma lem6171000 {B : Type'} (op : type1400 B) (x : B) : (term576 B op x) = (term570 B op x).
Proof. exact (eq_refl (term576 B op x)). Qed.
Lemma lem6171001 {B : Type'} (op : type1400 B) : (term577 B op) = (term571 B op).
Proof. exact (fun_ext (fun x : B => @lem6171000 B op x)). Qed.
Lemma lem6171002 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6171003 {B : Type'} (op : type1400 B) : (term578 B op) = (term572 B op).
Proof. exact (MK_COMB (@lem6171002 B) (@lem6171001 B op)). Qed.
Lemma lem6171004 {B : Type'} (op : type1400 B) : (term431 B op) = (term431 B op).
Proof. exact (eq_refl (term431 B op)). Qed.
Lemma lem6171005 {B : Type'} (op : type1400 B) : (term574 B op) = (term573 B op).
Proof. exact (MK_COMB (@lem6171004 B op) (@lem6171003 B op)). Qed.
Lemma lem6171006 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6171007 {B : Type'} (op : type1400 B) : (term579 B op) = (term580 B op).
Proof. exact (MK_COMB (@lem6171006) (@lem6171005 B op)). Qed.
Lemma lem6171008 {B : Type'} (op : type1400 B) (x : B) : (term576 B op x) = (term570 B op x).
Proof. exact (eq_refl (term576 B op x)). Qed.
Lemma lem6171009 {B : Type'} (op : type1400 B) : (term431 B op) = (term431 B op).
Proof. exact (eq_refl (term431 B op)). Qed.
Lemma lem6171010 {B : Type'} (op : type1400 B) (x : B) : (term581 B op x) = (term582 B op x).
Proof. exact (MK_COMB (@lem6171009 B op) (@lem6171008 B op x)). Qed.
Lemma lem6171011 {B : Type'} (op : type1400 B) : (term583 B op) = (term584 B op).
Proof. exact (fun_ext (fun x : B => @lem6171010 B op x)). Qed.
Lemma lem6171012 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6171013 {B : Type'} (op : type1400 B) : (term575 B op) = (term585 B op).
Proof. exact (MK_COMB (@lem6171012 B) (@lem6171011 B op)). Qed.
Lemma lem6171014 {B : Type'} (op : type1400 B) : ((term574 B op) = (term575 B op)) = ((term573 B op) = (term585 B op)).
Proof. exact (MK_COMB (@lem6171007 B op) (@lem6171013 B op)). Qed.
Lemma lem6171015 {B : Type'} (op : type1400 B) : (term573 B op) = (term585 B op).
Proof. exact (EQ_MP (@lem6171014 B op) (@lem6170999 B op)). Qed.
Lemma lem6171017 {A : Type'} (P : Prop) (Q : A -> Prop) : (term555 A P Q) = (term556 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6171018 {B : Type'} (P : Prop) (Q : B -> Prop) : (term555 B P Q) = (term556 B P Q).
Proof. exact (@lem6171017 B P Q). Qed.
Lemma lem6171019 {B : Type'} (op : type1400 B) (x : B) : (term586 B op x) = (term587 B op x).
Proof. exact (@lem6171018 B (@monoidal B op) (term569 B op x)). Qed.
Lemma lem6171020 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term588 B op x y) = (term568 B y op x).
Proof. exact (eq_refl (term588 B op x y)). Qed.
Lemma lem6171021 {B : Type'} (op : type1400 B) (x : B) : (term589 B op x) = (term569 B op x).
Proof. exact (fun_ext (fun y : B => @lem6171020 B y op x)). Qed.
Lemma lem6171022 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6171023 {B : Type'} (op : type1400 B) (x : B) : (term590 B op x) = (term570 B op x).
Proof. exact (MK_COMB (@lem6171022 B) (@lem6171021 B op x)). Qed.
Lemma lem6171024 {B : Type'} (op : type1400 B) : (term431 B op) = (term431 B op).
Proof. exact (eq_refl (term431 B op)). Qed.
Lemma lem6171025 {B : Type'} (op : type1400 B) (x : B) : (term586 B op x) = (term582 B op x).
Proof. exact (MK_COMB (@lem6171024 B op) (@lem6171023 B op x)). Qed.
Lemma lem6171026 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6171027 {B : Type'} (op : type1400 B) (x : B) : (term591 B op x) = (term592 B op x).
Proof. exact (MK_COMB (@lem6171026) (@lem6171025 B op x)). Qed.
Lemma lem6171028 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term588 B op x y) = (term568 B y op x).
Proof. exact (eq_refl (term588 B op x y)). Qed.
Lemma lem6171029 {B : Type'} (op : type1400 B) : (term431 B op) = (term431 B op).
Proof. exact (eq_refl (term431 B op)). Qed.
Lemma lem6171030 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term593 B op x y) = (term594 B y op x).
Proof. exact (MK_COMB (@lem6171029 B op) (@lem6171028 B y op x)). Qed.
Lemma lem6171031 {B : Type'} (op : type1400 B) (x : B) : (term595 B op x) = (term596 B op x).
Proof. exact (fun_ext (fun y : B => @lem6171030 B y op x)). Qed.
Lemma lem6171032 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6171033 {B : Type'} (op : type1400 B) (x : B) : (term587 B op x) = (term597 B op x).
Proof. exact (MK_COMB (@lem6171032 B) (@lem6171031 B op x)). Qed.
Lemma lem6171034 {B : Type'} (op : type1400 B) (x : B) : ((term586 B op x) = (term587 B op x)) = ((term582 B op x) = (term597 B op x)).
Proof. exact (MK_COMB (@lem6171027 B op x) (@lem6171033 B op x)). Qed.
Lemma lem6171035 {B : Type'} (op : type1400 B) (x : B) : (term582 B op x) = (term597 B op x).
Proof. exact (EQ_MP (@lem6171034 B op x) (@lem6171019 B op x)). Qed.
Lemma lem6171037 {A : Type'} (P : Prop) (Q : A -> Prop) : (term555 A P Q) = (term556 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6171038 {B : Type'} (P : Prop) (Q : B -> Prop) : (term555 B P Q) = (term556 B P Q).
Proof. exact (@lem6171037 B P Q). Qed.
Lemma lem6171039 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term598 B y op x) = (term599 B y op x).
Proof. exact (@lem6171038 B (@monoidal B op) (term567 B y op x)). Qed.
Lemma lem6171040 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term600 B y op x z) = (term565 B y z op x).
Proof. exact (eq_refl (term600 B y op x z)). Qed.
Lemma lem6171041 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term601 B y op x) = (term567 B y op x).
Proof. exact (fun_ext (fun z : B => @lem6171040 B y z op x)). Qed.
Lemma lem6171042 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6171043 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term602 B y op x) = (term568 B y op x).
Proof. exact (MK_COMB (@lem6171042 B) (@lem6171041 B y op x)). Qed.
Lemma lem6171044 {B : Type'} (op : type1400 B) : (term431 B op) = (term431 B op).
Proof. exact (eq_refl (term431 B op)). Qed.
Lemma lem6171045 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term598 B y op x) = (term594 B y op x).
Proof. exact (MK_COMB (@lem6171044 B op) (@lem6171043 B y op x)). Qed.
Lemma lem6171046 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6171047 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term603 B y op x) = (term604 B y op x).
Proof. exact (MK_COMB (@lem6171046) (@lem6171045 B y op x)). Qed.
Lemma lem6171048 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term600 B y op x z) = (term565 B y z op x).
Proof. exact (eq_refl (term600 B y op x z)). Qed.
Lemma lem6171049 {B : Type'} (op : type1400 B) : (term431 B op) = (term431 B op).
Proof. exact (eq_refl (term431 B op)). Qed.
Lemma lem6171050 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term605 B y op x z) = (term606 B y z op x).
Proof. exact (MK_COMB (@lem6171049 B op) (@lem6171048 B y z op x)). Qed.
Lemma lem6171051 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term607 B y op x) = (term608 B y op x).
Proof. exact (fun_ext (fun z : B => @lem6171050 B y z op x)). Qed.
Lemma lem6171052 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6171053 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term599 B y op x) = (term609 B y op x).
Proof. exact (MK_COMB (@lem6171052 B) (@lem6171051 B y op x)). Qed.
Lemma lem6171054 {B : Type'} (y : B) (op : type1400 B) (x : B) : ((term598 B y op x) = (term599 B y op x)) = ((term594 B y op x) = (term609 B y op x)).
Proof. exact (MK_COMB (@lem6171047 B y op x) (@lem6171053 B y op x)). Qed.
Lemma lem6171055 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term594 B y op x) = (term609 B y op x).
Proof. exact (EQ_MP (@lem6171054 B y op x) (@lem6171039 B y op x)). Qed.
Lemma lem6171056 {B : Type'} (op : type1400 B) (x : B) : (term596 B op x) = (term610 B op x).
Proof. exact (fun_ext (fun y : B => @lem6171055 B y op x)). Qed.
Lemma lem6171057 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6171058 {B : Type'} (op : type1400 B) (x : B) : (term597 B op x) = (term611 B op x).
Proof. exact (MK_COMB (@lem6171057 B) (@lem6171056 B op x)). Qed.
Lemma lem6171059 {B : Type'} (op : type1400 B) (x : B) : (term582 B op x) = (term611 B op x).
Proof. exact (TRANS (@lem6171035 B op x) (@lem6171058 B op x)). Qed.
Lemma lem6171060 {B : Type'} (op : type1400 B) : (term584 B op) = (term612 B op).
Proof. exact (fun_ext (fun x : B => @lem6171059 B op x)). Qed.
Lemma lem6171061 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6171062 {B : Type'} (op : type1400 B) : (term585 B op) = (term613 B op).
Proof. exact (MK_COMB (@lem6171061 B) (@lem6171060 B op)). Qed.
Lemma lem6171063 {B : Type'} (op : type1400 B) : (term573 B op) = (term613 B op).
Proof. exact (TRANS (@lem6171015 B op) (@lem6171062 B op)). Qed.
Lemma lem6171064 {B : Type'} (op : type1400 B) : (term433 B op) = (term613 B op).
Proof. exact (TRANS (@lem6170995 B op) (@lem6171063 B op)). Qed.
Lemma lem6171065 {B : Type'} : (term446 B) = (term614 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6171064 B op)). Qed.
Lemma lem6171066 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6171067 {B : Type'} : (term457 B) = (term615 B).
Proof. exact (MK_COMB (@lem6171066 B) (@lem6171065 B)). Qed.
Lemma lem6171069 {A B : Type'} (P : type1413 A B) : (term616 A B P) = (term617 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6171070 {B : Type'} (P : type401 B) : (term618 B P) = (term619 B P).
Proof. exact (@lem6171069 (type1400 B) B P). Qed.
Lemma lem6171071 {B : Type'} : (term620 B) = (term621 B).
Proof. exact (@lem6171070 B (term622 B)). Qed.
Lemma lem6171072 {B : Type'} (op : type1400 B) : (term623 B op) = (term612 B op).
Proof. exact (eq_refl (term623 B op)). Qed.
Lemma lem6171073 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6171074 {B : Type'} (op : type1400 B) (x : B) : (term624 B op x) = (term625 B op x).
Proof. exact (MK_COMB (@lem6171072 B op) (@lem6171073 B x)). Qed.
Lemma lem6171075 {B : Type'} (op : type1400 B) (x : B) : (term625 B op x) = (term611 B op x).
Proof. exact (eq_refl (term625 B op x)). Qed.
Lemma lem6171076 {B : Type'} (op : type1400 B) (x : B) : (term624 B op x) = (term611 B op x).
Proof. exact (TRANS (@lem6171074 B op x) (@lem6171075 B op x)). Qed.
Lemma lem6171077 {B : Type'} (op : type1400 B) : (term626 B op) = (term612 B op).
Proof. exact (fun_ext (fun x : B => @lem6171076 B op x)). Qed.
Lemma lem6171078 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6171079 {B : Type'} (op : type1400 B) : (term627 B op) = (term613 B op).
Proof. exact (MK_COMB (@lem6171078 B) (@lem6171077 B op)). Qed.
Lemma lem6171080 {B : Type'} : (term628 B) = (term614 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6171079 B op)). Qed.
Lemma lem6171081 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6171082 {B : Type'} : (term620 B) = (term615 B).
Proof. exact (MK_COMB (@lem6171081 B) (@lem6171080 B)). Qed.
Lemma lem6171083 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6171084 {B : Type'} : (term629 B) = (term630 B).
Proof. exact (MK_COMB (@lem6171083) (@lem6171082 B)). Qed.
Lemma lem6171085 {B : Type'} (op : type1400 B) : (term623 B op) = (term612 B op).
Proof. exact (eq_refl (term623 B op)). Qed.
Lemma lem6171086 {B : Type'} (x : type402 B) (op : type1400 B) : (x op) = (x op).
Proof. exact (eq_refl (x op)). Qed.
Lemma lem6171087 {B : Type'} (x : type402 B) (op : type1400 B) : (term631 B x op) = (term632 B x op).
Proof. exact (MK_COMB (@lem6171085 B op) (@lem6171086 B x op)). Qed.
Lemma lem6171088 {B : Type'} (x : type402 B) (op : type1400 B) : (term632 B x op) = (term633 B x op).
Proof. exact (eq_refl (term632 B x op)). Qed.
Lemma lem6171089 {B : Type'} (x : type402 B) (op : type1400 B) : (term631 B x op) = (term633 B x op).
Proof. exact (TRANS (@lem6171087 B x op) (@lem6171088 B x op)). Qed.
Lemma lem6171090 {B : Type'} (x : type402 B) : (term634 B x) = (term635 B x).
Proof. exact (fun_ext (fun op : type1400 B => @lem6171089 B x op)). Qed.
Lemma lem6171091 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6171092 {B : Type'} (x : type402 B) : (term636 B x) = (term637 B x).
Proof. exact (MK_COMB (@lem6171091 B) (@lem6171090 B x)). Qed.
Lemma lem6171093 {B : Type'} : (term638 B) = (term639 B).
Proof. exact (fun_ext (fun x : type402 B => @lem6171092 B x)). Qed.
Lemma lem6171094 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6171095 {B : Type'} : (term621 B) = (term640 B).
Proof. exact (MK_COMB (@lem6171094 B) (@lem6171093 B)). Qed.
Lemma lem6171096 {B : Type'} : ((term620 B) = (term621 B)) = ((term615 B) = (term640 B)).
Proof. exact (MK_COMB (@lem6171084 B) (@lem6171095 B)). Qed.
Lemma lem6171097 {B : Type'} : (term615 B) = (term640 B).
Proof. exact (EQ_MP (@lem6171096 B) (@lem6171071 B)). Qed.
Lemma lem6171099 {A B : Type'} (P : type1413 A B) : (term616 A B P) = (term617 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6171100 {B : Type'} (P : type401 B) : (term618 B P) = (term619 B P).
Proof. exact (@lem6171099 (type1400 B) B P). Qed.
Lemma lem6171101 {B : Type'} (x : type402 B) : (term641 B x) = (term642 B x).
Proof. exact (@lem6171100 B (term643 B x)). Qed.
Lemma lem6171102 {B : Type'} (x : type402 B) (op : type1400 B) : (term644 B x op) = (term645 B x op).
Proof. exact (eq_refl (term644 B x op)). Qed.
Lemma lem6171103 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem6171104 {B : Type'} (x : type402 B) (op : type1400 B) (y : B) : (term646 B x op y) = (term647 B x op y).
Proof. exact (MK_COMB (@lem6171102 B x op) (@lem6171103 B y)). Qed.
Lemma lem6171105 {B : Type'} (y : B) (x : type402 B) (op : type1400 B) : (term647 B x op y) = (term648 B y x op).
Proof. exact (eq_refl (term647 B x op y)). Qed.
Lemma lem6171106 {B : Type'} (y : B) (x : type402 B) (op : type1400 B) : (term646 B x op y) = (term648 B y x op).
Proof. exact (TRANS (@lem6171104 B x op y) (@lem6171105 B y x op)). Qed.
Lemma lem6171107 {B : Type'} (x : type402 B) (op : type1400 B) : (term649 B x op) = (term645 B x op).
Proof. exact (fun_ext (fun y : B => @lem6171106 B y x op)). Qed.
Lemma lem6171108 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6171109 {B : Type'} (x : type402 B) (op : type1400 B) : (term650 B x op) = (term633 B x op).
Proof. exact (MK_COMB (@lem6171108 B) (@lem6171107 B x op)). Qed.
Lemma lem6171110 {B : Type'} (x : type402 B) : (term651 B x) = (term635 B x).
Proof. exact (fun_ext (fun op : type1400 B => @lem6171109 B x op)). Qed.
Lemma lem6171111 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6171112 {B : Type'} (x : type402 B) : (term641 B x) = (term637 B x).
Proof. exact (MK_COMB (@lem6171111 B) (@lem6171110 B x)). Qed.
Lemma lem6171113 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6171114 {B : Type'} (x : type402 B) : (term652 B x) = (term653 B x).
Proof. exact (MK_COMB (@lem6171113) (@lem6171112 B x)). Qed.
Lemma lem6171115 {B : Type'} (x : type402 B) (op : type1400 B) : (term644 B x op) = (term645 B x op).
Proof. exact (eq_refl (term644 B x op)). Qed.
Lemma lem6171116 {B : Type'} (y : type402 B) (op : type1400 B) : (y op) = (y op).
Proof. exact (eq_refl (y op)). Qed.
Lemma lem6171117 {B : Type'} (x : type402 B) (y : type402 B) (op : type1400 B) : (term654 B x y op) = (term655 B x y op).
Proof. exact (MK_COMB (@lem6171115 B x op) (@lem6171116 B y op)). Qed.
Lemma lem6171118 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term655 B x y op) = (term656 B y x op).
Proof. exact (eq_refl (term655 B x y op)). Qed.
Lemma lem6171119 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term654 B x y op) = (term656 B y x op).
Proof. exact (TRANS (@lem6171117 B x y op) (@lem6171118 B y x op)). Qed.
Lemma lem6171120 {B : Type'} (y : type402 B) (x : type402 B) : (term657 B x y) = (term658 B y x).
Proof. exact (fun_ext (fun op : type1400 B => @lem6171119 B y x op)). Qed.
Lemma lem6171121 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6171122 {B : Type'} (y : type402 B) (x : type402 B) : (term659 B x y) = (term660 B y x).
Proof. exact (MK_COMB (@lem6171121 B) (@lem6171120 B y x)). Qed.
Lemma lem6171123 {B : Type'} (x : type402 B) : (term661 B x) = (term662 B x).
Proof. exact (fun_ext (fun y : type402 B => @lem6171122 B y x)). Qed.
Lemma lem6171124 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6171125 {B : Type'} (x : type402 B) : (term642 B x) = (term663 B x).
Proof. exact (MK_COMB (@lem6171124 B) (@lem6171123 B x)). Qed.
Lemma lem6171126 {B : Type'} (x : type402 B) : ((term641 B x) = (term642 B x)) = ((term637 B x) = (term663 B x)).
Proof. exact (MK_COMB (@lem6171114 B x) (@lem6171125 B x)). Qed.
Lemma lem6171127 {B : Type'} (x : type402 B) : (term637 B x) = (term663 B x).
Proof. exact (EQ_MP (@lem6171126 B x) (@lem6171101 B x)). Qed.
Lemma lem6171129 {A B : Type'} (P : type1413 A B) : (term616 A B P) = (term617 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6171130 {B : Type'} (P : type401 B) : (term618 B P) = (term619 B P).
Proof. exact (@lem6171129 (type1400 B) B P). Qed.
Lemma lem6171131 {B : Type'} (y : type402 B) (x : type402 B) : (term664 B y x) = (term665 B y x).
Proof. exact (@lem6171130 B (term666 B y x)). Qed.
Lemma lem6171132 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term667 B y x op) = (term668 B y x op).
Proof. exact (eq_refl (term667 B y x op)). Qed.
Lemma lem6171133 {B : Type'} (z : B) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem6171134 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) (z : B) : (term669 B y x op z) = (term670 B y x op z).
Proof. exact (MK_COMB (@lem6171132 B y x op) (@lem6171133 B z)). Qed.
Lemma lem6171135 {B : Type'} (y : type402 B) (z : B) (x : type402 B) (op : type1400 B) : (term670 B y x op z) = (term671 B y z x op).
Proof. exact (eq_refl (term670 B y x op z)). Qed.
Lemma lem6171136 {B : Type'} (y : type402 B) (z : B) (x : type402 B) (op : type1400 B) : (term669 B y x op z) = (term671 B y z x op).
Proof. exact (TRANS (@lem6171134 B y x op z) (@lem6171135 B y z x op)). Qed.
Lemma lem6171137 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term672 B y x op) = (term668 B y x op).
Proof. exact (fun_ext (fun z : B => @lem6171136 B y z x op)). Qed.
Lemma lem6171138 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6171139 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term673 B y x op) = (term656 B y x op).
Proof. exact (MK_COMB (@lem6171138 B) (@lem6171137 B y x op)). Qed.
Lemma lem6171140 {B : Type'} (y : type402 B) (x : type402 B) : (term674 B y x) = (term658 B y x).
Proof. exact (fun_ext (fun op : type1400 B => @lem6171139 B y x op)). Qed.
Lemma lem6171141 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6171142 {B : Type'} (y : type402 B) (x : type402 B) : (term664 B y x) = (term660 B y x).
Proof. exact (MK_COMB (@lem6171141 B) (@lem6171140 B y x)). Qed.
Lemma lem6171143 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6171144 {B : Type'} (y : type402 B) (x : type402 B) : (term675 B y x) = (term676 B y x).
Proof. exact (MK_COMB (@lem6171143) (@lem6171142 B y x)). Qed.
Lemma lem6171145 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term667 B y x op) = (term668 B y x op).
Proof. exact (eq_refl (term667 B y x op)). Qed.
Lemma lem6171146 {B : Type'} (z : type402 B) (op : type1400 B) : (z op) = (z op).
Proof. exact (eq_refl (z op)). Qed.
Lemma lem6171147 {B : Type'} (y : type402 B) (x : type402 B) (z : type402 B) (op : type1400 B) : (term677 B y x z op) = (term678 B y x z op).
Proof. exact (MK_COMB (@lem6171145 B y x op) (@lem6171146 B z op)). Qed.
Lemma lem6171148 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (op : type1400 B) : (term678 B y x z op) = (term679 B y z x op).
Proof. exact (eq_refl (term678 B y x z op)). Qed.
Lemma lem6171149 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (op : type1400 B) : (term677 B y x z op) = (term679 B y z x op).
Proof. exact (TRANS (@lem6171147 B y x z op) (@lem6171148 B y z x op)). Qed.
Lemma lem6171150 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) : (term680 B y x z) = (term681 B y z x).
Proof. exact (fun_ext (fun op : type1400 B => @lem6171149 B y z x op)). Qed.
Lemma lem6171151 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6171152 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) : (term682 B y x z) = (term683 B y z x).
Proof. exact (MK_COMB (@lem6171151 B) (@lem6171150 B y z x)). Qed.
Lemma lem6171153 {B : Type'} (y : type402 B) (x : type402 B) : (term684 B y x) = (term685 B y x).
Proof. exact (fun_ext (fun z : type402 B => @lem6171152 B y z x)). Qed.
Lemma lem6171154 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6171155 {B : Type'} (y : type402 B) (x : type402 B) : (term665 B y x) = (term686 B y x).
Proof. exact (MK_COMB (@lem6171154 B) (@lem6171153 B y x)). Qed.
Lemma lem6171156 {B : Type'} (y : type402 B) (x : type402 B) : ((term664 B y x) = (term665 B y x)) = ((term660 B y x) = (term686 B y x)).
Proof. exact (MK_COMB (@lem6171144 B y x) (@lem6171155 B y x)). Qed.
Lemma lem6171157 {B : Type'} (y : type402 B) (x : type402 B) : (term660 B y x) = (term686 B y x).
Proof. exact (EQ_MP (@lem6171156 B y x) (@lem6171131 B y x)). Qed.
Lemma lem6171158 {B : Type'} (x : type402 B) : (term662 B x) = (term687 B x).
Proof. exact (fun_ext (fun y : type402 B => @lem6171157 B y x)). Qed.
Lemma lem6171159 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6171160 {B : Type'} (x : type402 B) : (term663 B x) = (term688 B x).
Proof. exact (MK_COMB (@lem6171159 B) (@lem6171158 B x)). Qed.
Lemma lem6171161 {B : Type'} (x : type402 B) : (term637 B x) = (term688 B x).
Proof. exact (TRANS (@lem6171127 B x) (@lem6171160 B x)). Qed.
Lemma lem6171162 {B : Type'} : (term639 B) = (term689 B).
Proof. exact (fun_ext (fun x : type402 B => @lem6171161 B x)). Qed.
Lemma lem6171163 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6171164 {B : Type'} : (term640 B) = (term690 B).
Proof. exact (MK_COMB (@lem6171163 B) (@lem6171162 B)). Qed.
Lemma lem6171165 {B : Type'} : (term615 B) = (term690 B).
Proof. exact (TRANS (@lem6171097 B) (@lem6171164 B)). Qed.
Lemma lem6171166 {B : Type'} : (term457 B) = (term690 B).
Proof. exact (TRANS (@lem6171067 B) (@lem6171165 B)). Qed.
Lemma lem6171167 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6171168 {B : Type'} : (term459 B) = (term691 B).
Proof. exact (MK_COMB (@lem6171167) (@lem6171166 B)). Qed.
Lemma lem6171169 {B : Type'} : (term462 B) = (term462 B).
Proof. exact (eq_refl (term462 B)). Qed.
Lemma lem6171170 {B : Type'} : (term463 B) = (term692 B).
Proof. exact (MK_COMB (@lem6171168 B) (@lem6171169 B)). Qed.
Lemma lem6171172 {A : Type'} (P : A -> Prop) (Q : Prop) : (term693 A P Q) = (term694 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6171173 {B : Type'} (P : type82 B) (Q : Prop) : (term695 B P Q) = (term696 B P Q).
Proof. exact (@lem6171172 (type402 B) P Q). Qed.
Lemma lem6171174 {B : Type'} : (term697 B) = (term698 B).
Proof. exact (@lem6171173 B (term689 B) (term462 B)). Qed.
Lemma lem6171175 {B : Type'} (x : type402 B) : (term699 B x) = (term688 B x).
Proof. exact (eq_refl (term699 B x)). Qed.
Lemma lem6171176 {B : Type'} : (term700 B) = (term689 B).
Proof. exact (fun_ext (fun x : type402 B => @lem6171175 B x)). Qed.
Lemma lem6171177 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6171178 {B : Type'} : (term701 B) = (term690 B).
Proof. exact (MK_COMB (@lem6171177 B) (@lem6171176 B)). Qed.
Lemma lem6171179 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6171180 {B : Type'} : (term702 B) = (term691 B).
Proof. exact (MK_COMB (@lem6171179) (@lem6171178 B)). Qed.
Lemma lem6171181 {B : Type'} : (term462 B) = (term462 B).
Proof. exact (eq_refl (term462 B)). Qed.
Lemma lem6171182 {B : Type'} : (term697 B) = (term692 B).
Proof. exact (MK_COMB (@lem6171180 B) (@lem6171181 B)). Qed.
Lemma lem6171183 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6171184 {B : Type'} : (term703 B) = (term704 B).
Proof. exact (MK_COMB (@lem6171183) (@lem6171182 B)). Qed.
Lemma lem6171185 {B : Type'} (x : type402 B) : (term699 B x) = (term688 B x).
Proof. exact (eq_refl (term699 B x)). Qed.
Lemma lem6171186 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6171187 {B : Type'} (x : type402 B) : (term705 B x) = (term706 B x).
Proof. exact (MK_COMB (@lem6171186) (@lem6171185 B x)). Qed.
Lemma lem6171188 {B : Type'} : (term462 B) = (term462 B).
Proof. exact (eq_refl (term462 B)). Qed.
Lemma lem6171189 {B : Type'} (x : type402 B) : (term707 B x) = (term708 B x).
Proof. exact (MK_COMB (@lem6171187 B x) (@lem6171188 B)). Qed.
Lemma lem6171190 {B : Type'} : (term709 B) = (term710 B).
Proof. exact (fun_ext (fun x : type402 B => @lem6171189 B x)). Qed.
Lemma lem6171191 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6171192 {B : Type'} : (term698 B) = (term711 B).
Proof. exact (MK_COMB (@lem6171191 B) (@lem6171190 B)). Qed.
Lemma lem6171193 {B : Type'} : ((term697 B) = (term698 B)) = ((term692 B) = (term711 B)).
Proof. exact (MK_COMB (@lem6171184 B) (@lem6171192 B)). Qed.
Lemma lem6171194 {B : Type'} : (term692 B) = (term711 B).
Proof. exact (EQ_MP (@lem6171193 B) (@lem6171174 B)). Qed.
Lemma lem6171196 {A : Type'} (P : A -> Prop) (Q : Prop) : (term693 A P Q) = (term694 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6171197 {B : Type'} (P : type82 B) (Q : Prop) : (term695 B P Q) = (term696 B P Q).
Proof. exact (@lem6171196 (type402 B) P Q). Qed.
Lemma lem6171198 {B : Type'} (x : type402 B) : (term712 B x) = (term713 B x).
Proof. exact (@lem6171197 B (term687 B x) (term462 B)). Qed.
Lemma lem6171199 {B : Type'} (y : type402 B) (x : type402 B) : (term714 B x y) = (term686 B y x).
Proof. exact (eq_refl (term714 B x y)). Qed.
Lemma lem6171200 {B : Type'} (x : type402 B) : (term715 B x) = (term687 B x).
Proof. exact (fun_ext (fun y : type402 B => @lem6171199 B y x)). Qed.
Lemma lem6171201 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6171202 {B : Type'} (x : type402 B) : (term716 B x) = (term688 B x).
Proof. exact (MK_COMB (@lem6171201 B) (@lem6171200 B x)). Qed.
Lemma lem6171203 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6171204 {B : Type'} (x : type402 B) : (term717 B x) = (term706 B x).
Proof. exact (MK_COMB (@lem6171203) (@lem6171202 B x)). Qed.
Lemma lem6171205 {B : Type'} : (term462 B) = (term462 B).
Proof. exact (eq_refl (term462 B)). Qed.
Lemma lem6171206 {B : Type'} (x : type402 B) : (term712 B x) = (term708 B x).
Proof. exact (MK_COMB (@lem6171204 B x) (@lem6171205 B)). Qed.
Lemma lem6171207 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6171208 {B : Type'} (x : type402 B) : (term718 B x) = (term719 B x).
Proof. exact (MK_COMB (@lem6171207) (@lem6171206 B x)). Qed.
Lemma lem6171209 {B : Type'} (y : type402 B) (x : type402 B) : (term714 B x y) = (term686 B y x).
Proof. exact (eq_refl (term714 B x y)). Qed.
Lemma lem6171210 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6171211 {B : Type'} (y : type402 B) (x : type402 B) : (term720 B x y) = (term721 B y x).
Proof. exact (MK_COMB (@lem6171210) (@lem6171209 B y x)). Qed.
Lemma lem6171212 {B : Type'} : (term462 B) = (term462 B).
Proof. exact (eq_refl (term462 B)). Qed.
Lemma lem6171213 {B : Type'} (y : type402 B) (x : type402 B) : (term722 B x y) = (term723 B y x).
Proof. exact (MK_COMB (@lem6171211 B y x) (@lem6171212 B)). Qed.
Lemma lem6171214 {B : Type'} (x : type402 B) : (term724 B x) = (term725 B x).
Proof. exact (fun_ext (fun y : type402 B => @lem6171213 B y x)). Qed.
Lemma lem6171215 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6171216 {B : Type'} (x : type402 B) : (term713 B x) = (term726 B x).
Proof. exact (MK_COMB (@lem6171215 B) (@lem6171214 B x)). Qed.
Lemma lem6171217 {B : Type'} (x : type402 B) : ((term712 B x) = (term713 B x)) = ((term708 B x) = (term726 B x)).
Proof. exact (MK_COMB (@lem6171208 B x) (@lem6171216 B x)). Qed.
Lemma lem6171218 {B : Type'} (x : type402 B) : (term708 B x) = (term726 B x).
Proof. exact (EQ_MP (@lem6171217 B x) (@lem6171198 B x)). Qed.
Lemma lem6171220 {A : Type'} (P : A -> Prop) (Q : Prop) : (term693 A P Q) = (term694 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6171221 {B : Type'} (P : type82 B) (Q : Prop) : (term695 B P Q) = (term696 B P Q).
Proof. exact (@lem6171220 (type402 B) P Q). Qed.
Lemma lem6171222 {B : Type'} (y : type402 B) (x : type402 B) : (term727 B y x) = (term728 B y x).
Proof. exact (@lem6171221 B (term685 B y x) (term462 B)). Qed.
Lemma lem6171223 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) : (term729 B y x z) = (term683 B y z x).
Proof. exact (eq_refl (term729 B y x z)). Qed.
Lemma lem6171224 {B : Type'} (y : type402 B) (x : type402 B) : (term730 B y x) = (term685 B y x).
Proof. exact (fun_ext (fun z : type402 B => @lem6171223 B y z x)). Qed.
Lemma lem6171225 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6171226 {B : Type'} (y : type402 B) (x : type402 B) : (term731 B y x) = (term686 B y x).
Proof. exact (MK_COMB (@lem6171225 B) (@lem6171224 B y x)). Qed.
Lemma lem6171227 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6171228 {B : Type'} (y : type402 B) (x : type402 B) : (term732 B y x) = (term721 B y x).
Proof. exact (MK_COMB (@lem6171227) (@lem6171226 B y x)). Qed.
Lemma lem6171229 {B : Type'} : (term462 B) = (term462 B).
Proof. exact (eq_refl (term462 B)). Qed.
Lemma lem6171230 {B : Type'} (y : type402 B) (x : type402 B) : (term727 B y x) = (term723 B y x).
Proof. exact (MK_COMB (@lem6171228 B y x) (@lem6171229 B)). Qed.
Lemma lem6171231 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6171232 {B : Type'} (y : type402 B) (x : type402 B) : (term733 B y x) = (term734 B y x).
Proof. exact (MK_COMB (@lem6171231) (@lem6171230 B y x)). Qed.
Lemma lem6171233 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) : (term729 B y x z) = (term683 B y z x).
Proof. exact (eq_refl (term729 B y x z)). Qed.
Lemma lem6171234 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6171235 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) : (term735 B y x z) = (term736 B y z x).
Proof. exact (MK_COMB (@lem6171234) (@lem6171233 B y z x)). Qed.
Lemma lem6171236 {B : Type'} : (term462 B) = (term462 B).
Proof. exact (eq_refl (term462 B)). Qed.
Lemma lem6171237 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) : (term737 B y x z) = (term738 B y z x).
Proof. exact (MK_COMB (@lem6171235 B y z x) (@lem6171236 B)). Qed.
Lemma lem6171238 {B : Type'} (y : type402 B) (x : type402 B) : (term739 B y x) = (term740 B y x).
Proof. exact (fun_ext (fun z : type402 B => @lem6171237 B y z x)). Qed.
Lemma lem6171239 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6171240 {B : Type'} (y : type402 B) (x : type402 B) : (term728 B y x) = (term741 B y x).
Proof. exact (MK_COMB (@lem6171239 B) (@lem6171238 B y x)). Qed.
Lemma lem6171241 {B : Type'} (y : type402 B) (x : type402 B) : ((term727 B y x) = (term728 B y x)) = ((term723 B y x) = (term741 B y x)).
Proof. exact (MK_COMB (@lem6171232 B y x) (@lem6171240 B y x)). Qed.
Lemma lem6171242 {B : Type'} (y : type402 B) (x : type402 B) : (term723 B y x) = (term741 B y x).
Proof. exact (EQ_MP (@lem6171241 B y x) (@lem6171222 B y x)). Qed.
Lemma lem6171243 {B : Type'} (x : type402 B) : (term725 B x) = (term742 B x).
Proof. exact (fun_ext (fun y : type402 B => @lem6171242 B y x)). Qed.
Lemma lem6171244 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6171245 {B : Type'} (x : type402 B) : (term726 B x) = (term743 B x).
Proof. exact (MK_COMB (@lem6171244 B) (@lem6171243 B x)). Qed.
Lemma lem6171246 {B : Type'} (x : type402 B) : (term708 B x) = (term743 B x).
Proof. exact (TRANS (@lem6171218 B x) (@lem6171245 B x)). Qed.
Lemma lem6171247 {B : Type'} : (term710 B) = (term744 B).
Proof. exact (fun_ext (fun x : type402 B => @lem6171246 B x)). Qed.
Lemma lem6171248 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6171249 {B : Type'} : (term711 B) = (term745 B).
Proof. exact (MK_COMB (@lem6171248 B) (@lem6171247 B)). Qed.
Lemma lem6171250 {B : Type'} : (term692 B) = (term745 B).
Proof. exact (TRANS (@lem6171194 B) (@lem6171249 B)). Qed.
Lemma lem6171251 {B : Type'} : (term463 B) = (term745 B).
Proof. exact (TRANS (@lem6171170 B) (@lem6171250 B)). Qed.
Lemma lem6171252 {B : Type'} : (term439 B) = (term745 B).
Proof. exact (TRANS (@lem6170701 B) (@lem6171251 B)). Qed.
Lemma lem6171253 {B : Type'} : (term257 B) = (term745 B).
Proof. exact (TRANS (@lem6170674 B) (@lem6171252 B)). Qed.
Lemma lem6171254 {B : Type'} (h1 : term257 B) : term745 B.
Proof. exact (EQ_MP (@lem6171253 B) (@lem6170324 B h1)). Qed.
Lemma lem6171255 {B : Type'} (x : type402 B) (h1 : term743 B x) : term743 B x.
Proof. exact (h1). Qed.
Lemma lem6171256 {B : Type'} (y : type402 B) (x : type402 B) (h1 : term741 B y x) : term741 B y x.
Proof. exact (h1). Qed.
Lemma lem6171258 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term1219 A B g s f x' op) : term1219 A B g s f x' op.
Proof. exact (h1). Qed.
Lemma lem6171758 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6171759 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6171764 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6171765 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6171764 A B f x). Qed.
Lemma lem6171767 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (@I (A -> B) f x').
Proof. exact (@lem6171765 A B f x'). Qed.
Lemma lem6171772 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6171773 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6171772 (type1400 B) B f x). Qed.
Lemma lem6171775 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem6171773 B (@neutral B) op). Qed.
Lemma lem6171776 {A B : Type'} (f : A -> B) (x' : A) : (term851 A B f x') = (term852 A B f x').
Proof. exact (MK_COMB (@lem6171759 B) (@lem6171767 A B f x')). Qed.
Lemma lem6171777 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : ((f x') = (@neutral B op)) = ((@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (MK_COMB (@lem6171776 A B f x') (@lem6171775 B op)). Qed.
Lemma lem6171778 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : (term315 A B f x' op) = (term853 A B f x' op).
Proof. exact (MK_COMB (@lem6171758) (@lem6171777 A B f x' op)). Qed.
Lemma lem6171779 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6171784 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6171785 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6171784 A B f x). Qed.
Lemma lem6171787 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (@I (A -> B) f x').
Proof. exact (@lem6171785 A B f x'). Qed.
Lemma lem6171792 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6171793 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6171792 (type1400 B) B f x). Qed.
Lemma lem6171795 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem6171793 B (@neutral B) op). Qed.
Lemma lem6171796 {A B : Type'} (f : A -> B) (x' : A) : (term851 A B f x') = (term852 A B f x').
Proof. exact (MK_COMB (@lem6171779 B) (@lem6171787 A B f x')). Qed.
Lemma lem6171797 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : ((f x') = (@neutral B op)) = ((@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (MK_COMB (@lem6171796 A B f x') (@lem6171795 B op)). Qed.
Lemma lem6171798 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6171805 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6171806 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6171805 A (type686 A) f x). Qed.
Lemma lem6171807 {A : Type'} (x' : A) : (@IN A x') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x').
Proof. exact (@lem6171806 A (@IN A) x'). Qed.
Lemma lem6171808 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6171809 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s).
Proof. exact (MK_COMB (@lem6171807 A x') (@lem6171808 A s)). Qed.
Lemma lem6171811 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6171812 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6171811 (A -> Prop) Prop f x). Qed.
Lemma lem6171813 {A : Type'} (x' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s) = (term846 A x' s).
Proof. exact (@lem6171812 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x') s). Qed.
Lemma lem6171815 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (term846 A x' s).
Proof. exact (TRANS (@lem6171809 A x' s) (@lem6171813 A x' s)). Qed.
Lemma lem6171816 {A : Type'} (x' : A) (s : A -> Prop) : (term847 A x' s) = (term848 A x' s).
Proof. exact (MK_COMB (@lem6171798) (@lem6171815 A x' s)). Qed.
Lemma lem6171817 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6171818 {A : Type'} (x' : A) (s : A -> Prop) : (term312 A x' s) = (term849 A x' s).
Proof. exact (MK_COMB (@lem6171817) (@lem6171816 A x' s)). Qed.
Lemma lem6171819 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) : (term314 A B s f x' op) = (term862 A B s f x' op).
Proof. exact (MK_COMB (@lem6171818 A x' s) (@lem6171797 A B f x' op)). Qed.
Lemma lem6171820 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6171821 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6171826 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6171827 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6171826 A B f x). Qed.
Lemma lem6171829 {A B : Type'} (g : A -> B) (x' : A) : (g x') = (@I (A -> B) g x').
Proof. exact (@lem6171827 A B g x'). Qed.
Lemma lem6171834 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6171835 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6171834 (type1400 B) B f x). Qed.
Lemma lem6171837 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem6171835 B (@neutral B) op). Qed.
Lemma lem6171838 {A B : Type'} (g : A -> B) (x' : A) : (term851 A B g x') = (term852 A B g x').
Proof. exact (MK_COMB (@lem6171821 B) (@lem6171829 A B g x')). Qed.
Lemma lem6171839 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) : ((g x') = (@neutral B op)) = ((@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (MK_COMB (@lem6171838 A B g x') (@lem6171837 B op)). Qed.
Lemma lem6171840 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) : (term315 A B g x' op) = (term853 A B g x' op).
Proof. exact (MK_COMB (@lem6171820) (@lem6171839 A B g x' op)). Qed.
Lemma lem6171847 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6171848 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6171847 A (type686 A) f x). Qed.
Lemma lem6171849 {A : Type'} (x' : A) : (@IN A x') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x').
Proof. exact (@lem6171848 A (@IN A) x'). Qed.
Lemma lem6171850 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6171851 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s).
Proof. exact (MK_COMB (@lem6171849 A x') (@lem6171850 A s)). Qed.
Lemma lem6171853 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6171854 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6171853 (A -> Prop) Prop f x). Qed.
Lemma lem6171855 {A : Type'} (x' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s) = (term846 A x' s).
Proof. exact (@lem6171854 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x') s). Qed.
Lemma lem6171857 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (term846 A x' s).
Proof. exact (TRANS (@lem6171851 A x' s) (@lem6171855 A x' s)). Qed.
Lemma lem6171858 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6171859 {A : Type'} (x' : A) (s : A -> Prop) : (term132 A x' s) = (term854 A x' s).
Proof. exact (MK_COMB (@lem6171858) (@lem6171857 A x' s)). Qed.
Lemma lem6171860 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) : (term168 A B s g x' op) = (term855 A B s g x' op).
Proof. exact (MK_COMB (@lem6171859 A x' s) (@lem6171840 A B g x' op)). Qed.
Lemma lem6171861 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6171862 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6171867 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6171868 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6171867 A B f x). Qed.
Lemma lem6171870 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (@I (A -> B) f x').
Proof. exact (@lem6171868 A B f x'). Qed.
Lemma lem6171875 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6171876 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6171875 (type1400 B) B f x). Qed.
Lemma lem6171878 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem6171876 B (@neutral B) op). Qed.
Lemma lem6171879 {A B : Type'} (f : A -> B) (x' : A) : (term851 A B f x') = (term852 A B f x').
Proof. exact (MK_COMB (@lem6171862 B) (@lem6171870 A B f x')). Qed.
Lemma lem6171880 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : ((f x') = (@neutral B op)) = ((@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (MK_COMB (@lem6171879 A B f x') (@lem6171878 B op)). Qed.
Lemma lem6171881 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : (term315 A B f x' op) = (term853 A B f x' op).
Proof. exact (MK_COMB (@lem6171861) (@lem6171880 A B f x' op)). Qed.
Lemma lem6171888 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6171889 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6171888 A (type686 A) f x). Qed.
Lemma lem6171890 {A : Type'} (x' : A) : (@IN A x') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x').
Proof. exact (@lem6171889 A (@IN A) x'). Qed.
Lemma lem6171891 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6171892 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s).
Proof. exact (MK_COMB (@lem6171890 A x') (@lem6171891 A s)). Qed.
Lemma lem6171894 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6171895 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6171894 (A -> Prop) Prop f x). Qed.
Lemma lem6171896 {A : Type'} (x' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s) = (term846 A x' s).
Proof. exact (@lem6171895 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x') s). Qed.
Lemma lem6171898 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (term846 A x' s).
Proof. exact (TRANS (@lem6171892 A x' s) (@lem6171896 A x' s)). Qed.
Lemma lem6171899 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6171900 {A : Type'} (x' : A) (s : A -> Prop) : (term132 A x' s) = (term854 A x' s).
Proof. exact (MK_COMB (@lem6171899) (@lem6171898 A x' s)). Qed.
Lemma lem6171901 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) : (term168 A B s f x' op) = (term855 A B s f x' op).
Proof. exact (MK_COMB (@lem6171900 A x' s) (@lem6171881 A B f x' op)). Qed.
Lemma lem6171902 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6171903 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) : (term183 A B s f x' op) = (term856 A B s f x' op).
Proof. exact (MK_COMB (@lem6171902) (@lem6171901 A B s f x' op)). Qed.
Lemma lem6171904 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) : (term184 A B f s g x' op) = (term857 A B f s g x' op).
Proof. exact (MK_COMB (@lem6171903 A B s f x' op) (@lem6171860 A B s g x' op)). Qed.
Lemma lem6171905 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6171906 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) : (term193 A B f s g x' op) = (term858 A B f s g x' op).
Proof. exact (MK_COMB (@lem6171905) (@lem6171904 A B f s g x' op)). Qed.
Lemma lem6171907 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) : (term1188 A B g s f x' op) = (term1223 A B g s f x' op).
Proof. exact (MK_COMB (@lem6171906 A B f s g x' op) (@lem6171819 A B s f x' op)). Qed.
Lemma lem6171908 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6171909 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) : (term1190 A B g s f x' op) = (term1224 A B g s f x' op).
Proof. exact (MK_COMB (@lem6171908) (@lem6171907 A B g s f x' op)). Qed.
Lemma lem6171910 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) : (term1192 A B g s f x' op) = (term1225 A B g s f x' op).
Proof. exact (MK_COMB (@lem6171909 A B g s f x' op) (@lem6171778 A B f x' op)). Qed.
Lemma lem6171911 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6171916 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6171917 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6171916 A B f x). Qed.
Lemma lem6171919 {A B : Type'} (g : A -> B) (x' : A) : (g x') = (@I (A -> B) g x').
Proof. exact (@lem6171917 A B g x'). Qed.
Lemma lem6171924 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6171925 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6171924 (type1400 B) B f x). Qed.
Lemma lem6171927 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem6171925 B (@neutral B) op). Qed.
Lemma lem6171928 {A B : Type'} (g : A -> B) (x' : A) : (term851 A B g x') = (term852 A B g x').
Proof. exact (MK_COMB (@lem6171911 B) (@lem6171919 A B g x')). Qed.
Lemma lem6171929 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) : ((g x') = (@neutral B op)) = ((@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (MK_COMB (@lem6171928 A B g x') (@lem6171927 B op)). Qed.
Lemma lem6171930 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6171937 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6171938 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6171937 A (type686 A) f x). Qed.
Lemma lem6171939 {A : Type'} (x' : A) : (@IN A x') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x').
Proof. exact (@lem6171938 A (@IN A) x'). Qed.
Lemma lem6171940 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6171941 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s).
Proof. exact (MK_COMB (@lem6171939 A x') (@lem6171940 A s)). Qed.
Lemma lem6171943 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6171944 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6171943 (A -> Prop) Prop f x). Qed.
Lemma lem6171945 {A : Type'} (x' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s) = (term846 A x' s).
Proof. exact (@lem6171944 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x') s). Qed.
Lemma lem6171947 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (term846 A x' s).
Proof. exact (TRANS (@lem6171941 A x' s) (@lem6171945 A x' s)). Qed.
Lemma lem6171948 {A : Type'} (x' : A) (s : A -> Prop) : (term847 A x' s) = (term848 A x' s).
Proof. exact (MK_COMB (@lem6171930) (@lem6171947 A x' s)). Qed.
Lemma lem6171949 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6171950 {A : Type'} (x' : A) (s : A -> Prop) : (term312 A x' s) = (term849 A x' s).
Proof. exact (MK_COMB (@lem6171949) (@lem6171948 A x' s)). Qed.
Lemma lem6171951 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) : (term314 A B s g x' op) = (term862 A B s g x' op).
Proof. exact (MK_COMB (@lem6171950 A x' s) (@lem6171929 A B g x' op)). Qed.
Lemma lem6171952 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6171957 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6171958 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6171957 A B f x). Qed.
Lemma lem6171960 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (@I (A -> B) f x').
Proof. exact (@lem6171958 A B f x'). Qed.
Lemma lem6171965 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6171966 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6171965 (type1400 B) B f x). Qed.
Lemma lem6171968 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem6171966 B (@neutral B) op). Qed.
Lemma lem6171969 {A B : Type'} (f : A -> B) (x' : A) : (term851 A B f x') = (term852 A B f x').
Proof. exact (MK_COMB (@lem6171952 B) (@lem6171960 A B f x')). Qed.
Lemma lem6171970 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : ((f x') = (@neutral B op)) = ((@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (MK_COMB (@lem6171969 A B f x') (@lem6171968 B op)). Qed.
Lemma lem6171971 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6171978 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6171979 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6171978 A (type686 A) f x). Qed.
Lemma lem6171980 {A : Type'} (x' : A) : (@IN A x') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x').
Proof. exact (@lem6171979 A (@IN A) x'). Qed.
Lemma lem6171981 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6171982 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s).
Proof. exact (MK_COMB (@lem6171980 A x') (@lem6171981 A s)). Qed.
Lemma lem6171984 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6171985 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6171984 (A -> Prop) Prop f x). Qed.
Lemma lem6171986 {A : Type'} (x' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s) = (term846 A x' s).
Proof. exact (@lem6171985 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x') s). Qed.
Lemma lem6171988 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (term846 A x' s).
Proof. exact (TRANS (@lem6171982 A x' s) (@lem6171986 A x' s)). Qed.
Lemma lem6171989 {A : Type'} (x' : A) (s : A -> Prop) : (term847 A x' s) = (term848 A x' s).
Proof. exact (MK_COMB (@lem6171971) (@lem6171988 A x' s)). Qed.
Lemma lem6171990 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6171991 {A : Type'} (x' : A) (s : A -> Prop) : (term312 A x' s) = (term849 A x' s).
Proof. exact (MK_COMB (@lem6171990) (@lem6171989 A x' s)). Qed.
Lemma lem6171992 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) : (term314 A B s f x' op) = (term862 A B s f x' op).
Proof. exact (MK_COMB (@lem6171991 A x' s) (@lem6171970 A B f x' op)). Qed.
Lemma lem6171993 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6171994 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) : (term317 A B s f x' op) = (term863 A B s f x' op).
Proof. exact (MK_COMB (@lem6171993) (@lem6171992 A B s f x' op)). Qed.
Lemma lem6171995 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) : (term319 A B f s g x' op) = (term864 A B f s g x' op).
Proof. exact (MK_COMB (@lem6171994 A B s f x' op) (@lem6171951 A B s g x' op)). Qed.
Lemma lem6171996 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6171997 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6172002 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6172003 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6172002 A B f x). Qed.
Lemma lem6172005 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (@I (A -> B) f x').
Proof. exact (@lem6172003 A B f x'). Qed.
Lemma lem6172010 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6172011 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6172010 (type1400 B) B f x). Qed.
Lemma lem6172013 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem6172011 B (@neutral B) op). Qed.
Lemma lem6172014 {A B : Type'} (f : A -> B) (x' : A) : (term851 A B f x') = (term852 A B f x').
Proof. exact (MK_COMB (@lem6171997 B) (@lem6172005 A B f x')). Qed.
Lemma lem6172015 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : ((f x') = (@neutral B op)) = ((@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (MK_COMB (@lem6172014 A B f x') (@lem6172013 B op)). Qed.
Lemma lem6172016 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : (term315 A B f x' op) = (term853 A B f x' op).
Proof. exact (MK_COMB (@lem6171996) (@lem6172015 A B f x' op)). Qed.
Lemma lem6172023 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6172024 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6172023 A (type686 A) f x). Qed.
Lemma lem6172025 {A : Type'} (x' : A) : (@IN A x') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x').
Proof. exact (@lem6172024 A (@IN A) x'). Qed.
Lemma lem6172026 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6172027 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s).
Proof. exact (MK_COMB (@lem6172025 A x') (@lem6172026 A s)). Qed.
Lemma lem6172029 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6172030 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6172029 (A -> Prop) Prop f x). Qed.
Lemma lem6172031 {A : Type'} (x' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s) = (term846 A x' s).
Proof. exact (@lem6172030 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x') s). Qed.
Lemma lem6172033 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (term846 A x' s).
Proof. exact (TRANS (@lem6172027 A x' s) (@lem6172031 A x' s)). Qed.
Lemma lem6172034 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6172035 {A : Type'} (x' : A) (s : A -> Prop) : (term132 A x' s) = (term854 A x' s).
Proof. exact (MK_COMB (@lem6172034) (@lem6172033 A x' s)). Qed.
Lemma lem6172036 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) : (term168 A B s f x' op) = (term855 A B s f x' op).
Proof. exact (MK_COMB (@lem6172035 A x' s) (@lem6172016 A B f x' op)). Qed.
Lemma lem6172037 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6172038 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) : (term1177 A B s f x' op) = (term1226 A B s f x' op).
Proof. exact (MK_COMB (@lem6172037) (@lem6172036 A B s f x' op)). Qed.
Lemma lem6172039 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) : (term1179 A B f s g x' op) = (term1227 A B f s g x' op).
Proof. exact (MK_COMB (@lem6172038 A B s f x' op) (@lem6171995 A B f s g x' op)). Qed.
Lemma lem6172040 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6172041 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) : (term1217 A B f s g x' op) = (term1228 A B f s g x' op).
Proof. exact (MK_COMB (@lem6172040) (@lem6172039 A B f s g x' op)). Qed.
Lemma lem6172042 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) : (term1219 A B g s f x' op) = (term1229 A B g s f x' op).
Proof. exact (MK_COMB (@lem6172041 A B f s g x' op) (@lem6171910 A B g s f x' op)). Qed.
Lemma lem6172043 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term1219 A B g s f x' op) : term1229 A B g s f x' op.
Proof. exact (EQ_MP (@lem6172042 A B g s f x' op) (@lem6171258 A B g s f x' op h1)). Qed.
Lemma lem6172046 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1227 A B f s g x' op) : term1227 A B f s g x' op.
Proof. exact (h1). Qed.
Lemma lem6172047 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term1225 A B g s f x' op) : term1225 A B g s f x' op.
Proof. exact (h1). Qed.
Lemma lem6172048 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1227 A B f s g x' op) : term864 A B f s g x' op.
Proof. exact (proj2 (@lem6172046 A B f s g x' op h1)). Qed.
Lemma lem6172049 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1227 A B f s g x' op) : term855 A B s f x' op.
Proof. exact (proj1 (@lem6172046 A B f s g x' op h1)). Qed.
Lemma lem6172050 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1227 A B f s g x' op) : term862 A B s g x' op.
Proof. exact (proj2 (@lem6172048 A B f s g x' op h1)). Qed.
Lemma lem6172051 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1227 A B f s g x' op) : term862 A B s f x' op.
Proof. exact (proj1 (@lem6172048 A B f s g x' op h1)). Qed.
Lemma lem6172061 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term1225 A B g s f x' op) : term1223 A B g s f x' op.
Proof. exact (proj1 (@lem6172047 A B g s f x' op h1)). Qed.
Lemma lem6172062 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term1225 A B g s f x' op) : term862 A B s f x' op.
Proof. exact (proj2 (@lem6172061 A B g s f x' op h1)). Qed.
Lemma lem6172063 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term1225 A B g s f x' op) : term857 A B f s g x' op.
Proof. exact (proj1 (@lem6172061 A B g s f x' op h1)). Qed.
Lemma lem6172066 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s f x' op) : term855 A B s f x' op.
Proof. exact (h1). Qed.
Lemma lem6172067 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s g x' op) : term855 A B s g x' op.
Proof. exact (h1). Qed.
Lemma lem6172072 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s f x' op) : term855 A B s f x' op.
Proof. exact (h1). Qed.
Lemma lem6172409 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6172413 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6172745 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6173085 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6173421 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (h1). Qed.
Lemma lem6173749 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6174085 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6174421 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (h1). Qed.
Lemma lem6174757 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (h1). Qed.
Lemma lem6174943 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6174945 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6174989 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6175037 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6175079 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1227 A B f s g x' op) : term853 A B f x' op.
Proof. exact (proj2 (@lem6172049 A B f s g x' op h1)). Qed.
Lemma lem6175083 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (h1). Qed.
Lemma lem6175125 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6175171 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6175217 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (h1). Qed.
Lemma lem6175221 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s f x' op) : term853 A B f x' op.
Proof. exact (proj2 (@lem6172072 A B s f x' op h1)). Qed.
Lemma lem6175261 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term1225 A B g s f x' op) : term853 A B f x' op.
Proof. exact (proj2 (@lem6172047 A B g s f x' op h1)). Qed.
Lemma lem6175263 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (h1). Qed.
Lemma lem6175471 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1227 A B f s g x' op) : term846 A x' s.
Proof. exact (proj1 (@lem6172049 A B f s g x' op h1)). Qed.
Lemma lem6175472 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1227 A B f s g x' op) : term1042 A x' s.
Proof. exact (fun h0 : term848 A x' s => @lem6175471 A B f s g x' op h1). Qed.
Lemma lem6175474 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6175475 {A : Type'} (x' : A) (s : A -> Prop) : (term1042 A x' s) = (term846 A x' s).
Proof. exact (@lem6175474 (term846 A x' s)). Qed.
Lemma lem6175476 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1227 A B f s g x' op) : term846 A x' s.
Proof. exact (EQ_MP (@lem6175475 A x' s) (@lem6175472 A B f s g x' op h1)). Qed.
Lemma lem6175479 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6175481 {A : Type'} (x' : A) (s : A -> Prop) : (term848 A x' s) = (term1044 A x' s).
Proof. exact (@lem6175479 (term846 A x' s)). Qed.
Lemma lem6175484 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term1044 A x' s.
Proof. exact (EQ_MP (@lem6175481 A x' s) (@lem6174943 A x' s h1)). Qed.
Lemma lem6175487 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : False.
Proof. exact (@lem6175484 A x' s h1 (@lem6175476 A B f s g x' op h2)). Qed.
Lemma lem6175488 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : term1045.
Proof. exact (fun h0 : ~ False => @lem6175487 A B f s g x' op h1 h2). Qed.
Lemma lem6175490 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6175491 : term1045 = False.
Proof. exact (@lem6175490 False). Qed.
Lemma lem6175492 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6175491) (@lem6175488 A B f s g x' op h1 h2)). Qed.
Lemma lem6175678 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1227 A B f s g x' op) : term846 A x' s.
Proof. exact (proj1 (@lem6172049 A B f s g x' op h1)). Qed.
Lemma lem6175679 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1227 A B f s g x' op) : term1042 A x' s.
Proof. exact (fun h0 : term848 A x' s => @lem6175678 A B f s g x' op h1). Qed.
Lemma lem6175681 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6175682 {A : Type'} (x' : A) (s : A -> Prop) : (term1042 A x' s) = (term846 A x' s).
Proof. exact (@lem6175681 (term846 A x' s)). Qed.
Lemma lem6175683 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1227 A B f s g x' op) : term846 A x' s.
Proof. exact (EQ_MP (@lem6175682 A x' s) (@lem6175679 A B f s g x' op h1)). Qed.
Lemma lem6175686 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6175688 {A : Type'} (x' : A) (s : A -> Prop) : (term848 A x' s) = (term1044 A x' s).
Proof. exact (@lem6175686 (term846 A x' s)). Qed.
Lemma lem6175691 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term1044 A x' s.
Proof. exact (EQ_MP (@lem6175688 A x' s) (@lem6174989 A x' s h1)). Qed.
Lemma lem6175694 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : False.
Proof. exact (@lem6175691 A x' s h1 (@lem6175683 A B f s g x' op h2)). Qed.
Lemma lem6175695 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : term1045.
Proof. exact (fun h0 : ~ False => @lem6175694 A B f s g x' op h1 h2). Qed.
Lemma lem6175697 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6175698 : term1045 = False.
Proof. exact (@lem6175697 False). Qed.
Lemma lem6175699 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6175698) (@lem6175695 A B f s g x' op h1 h2)). Qed.
Lemma lem6175885 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1227 A B f s g x' op) : term846 A x' s.
Proof. exact (proj1 (@lem6172049 A B f s g x' op h1)). Qed.
Lemma lem6175886 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1227 A B f s g x' op) : term1042 A x' s.
Proof. exact (fun h0 : term848 A x' s => @lem6175885 A B f s g x' op h1). Qed.
Lemma lem6175888 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6175889 {A : Type'} (x' : A) (s : A -> Prop) : (term1042 A x' s) = (term846 A x' s).
Proof. exact (@lem6175888 (term846 A x' s)). Qed.
Lemma lem6175890 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1227 A B f s g x' op) : term846 A x' s.
Proof. exact (EQ_MP (@lem6175889 A x' s) (@lem6175886 A B f s g x' op h1)). Qed.
Lemma lem6175893 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6175895 {A : Type'} (x' : A) (s : A -> Prop) : (term848 A x' s) = (term1044 A x' s).
Proof. exact (@lem6175893 (term846 A x' s)). Qed.
Lemma lem6175898 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term1044 A x' s.
Proof. exact (EQ_MP (@lem6175895 A x' s) (@lem6175037 A x' s h1)). Qed.
Lemma lem6175901 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : False.
Proof. exact (@lem6175898 A x' s h1 (@lem6175890 A B f s g x' op h2)). Qed.
Lemma lem6175902 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : term1045.
Proof. exact (fun h0 : ~ False => @lem6175901 A B f s g x' op h1 h2). Qed.
Lemma lem6175904 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6175905 : term1045 = False.
Proof. exact (@lem6175904 False). Qed.
Lemma lem6175906 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6175905) (@lem6175902 A B f s g x' op h1 h2)). Qed.
Lemma lem6176092 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (h1). Qed.
Lemma lem6176093 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : term1056 A B f x' op.
Proof. exact (fun h0 : term853 A B f x' op => @lem6176092 A B f x' op h1). Qed.
Lemma lem6176095 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6176096 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : (term1056 A B f x' op) = ((@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (@lem6176095 ((@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op))). Qed.
Lemma lem6176097 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (EQ_MP (@lem6176096 A B f x' op) (@lem6176093 A B f x' op h1)). Qed.
Lemma lem6176100 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6176102 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : (term853 A B f x' op) = (term1230 A B f x' op).
Proof. exact (@lem6176100 ((@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op))). Qed.
Lemma lem6176105 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1227 A B f s g x' op) : term1230 A B f x' op.
Proof. exact (EQ_MP (@lem6176102 A B f x' op) (@lem6175079 A B f s g x' op h1)). Qed.
Lemma lem6176108 {A B : Type'} (s : A -> Prop) (g : A -> B) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term1227 A B f s g x' op) (h2 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (@lem6176105 A B f s g x' op h1 (@lem6176097 A B f x' op h2)). Qed.
Lemma lem6176109 {A B : Type'} (s : A -> Prop) (g : A -> B) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term1227 A B f s g x' op) (h2 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : term1045.
Proof. exact (fun h0 : ~ False => @lem6176108 A B s g f x' op h1 h2). Qed.
Lemma lem6176111 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6176112 : term1045 = False.
Proof. exact (@lem6176111 False). Qed.
Lemma lem6176113 {A B : Type'} (s : A -> Prop) (g : A -> B) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term1227 A B f s g x' op) (h2 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6176112) (@lem6176109 A B s g f x' op h1 h2)). Qed.
Lemma lem6176299 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s f x' op) : term846 A x' s.
Proof. exact (proj1 (@lem6172066 A B s f x' op h1)). Qed.
Lemma lem6176300 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s f x' op) : term1042 A x' s.
Proof. exact (fun h0 : term848 A x' s => @lem6176299 A B s f x' op h1). Qed.
Lemma lem6176302 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6176303 {A : Type'} (x' : A) (s : A -> Prop) : (term1042 A x' s) = (term846 A x' s).
Proof. exact (@lem6176302 (term846 A x' s)). Qed.
Lemma lem6176304 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s f x' op) : term846 A x' s.
Proof. exact (EQ_MP (@lem6176303 A x' s) (@lem6176300 A B s f x' op h1)). Qed.
Lemma lem6176307 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6176309 {A : Type'} (x' : A) (s : A -> Prop) : (term848 A x' s) = (term1044 A x' s).
Proof. exact (@lem6176307 (term846 A x' s)). Qed.
Lemma lem6176312 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term1044 A x' s.
Proof. exact (EQ_MP (@lem6176309 A x' s) (@lem6175125 A x' s h1)). Qed.
Lemma lem6176315 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s f x' op) : False.
Proof. exact (@lem6176312 A x' s h1 (@lem6176304 A B s f x' op h2)). Qed.
Lemma lem6176316 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s f x' op) : term1045.
Proof. exact (fun h0 : ~ False => @lem6176315 A B s f x' op h1 h2). Qed.
Lemma lem6176318 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6176319 : term1045 = False.
Proof. exact (@lem6176318 False). Qed.
Lemma lem6176320 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s f x' op) : False.
Proof. exact (EQ_MP (@lem6176319) (@lem6176316 A B s f x' op h1 h2)). Qed.
Lemma lem6176506 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s g x' op) : term846 A x' s.
Proof. exact (proj1 (@lem6172067 A B s g x' op h1)). Qed.
Lemma lem6176507 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s g x' op) : term1042 A x' s.
Proof. exact (fun h0 : term848 A x' s => @lem6176506 A B s g x' op h1). Qed.
Lemma lem6176509 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6176510 {A : Type'} (x' : A) (s : A -> Prop) : (term1042 A x' s) = (term846 A x' s).
Proof. exact (@lem6176509 (term846 A x' s)). Qed.
Lemma lem6176511 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s g x' op) : term846 A x' s.
Proof. exact (EQ_MP (@lem6176510 A x' s) (@lem6176507 A B s g x' op h1)). Qed.
Lemma lem6176514 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6176516 {A : Type'} (x' : A) (s : A -> Prop) : (term848 A x' s) = (term1044 A x' s).
Proof. exact (@lem6176514 (term846 A x' s)). Qed.
Lemma lem6176519 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term1044 A x' s.
Proof. exact (EQ_MP (@lem6176516 A x' s) (@lem6175171 A x' s h1)). Qed.
Lemma lem6176522 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s g x' op) : False.
Proof. exact (@lem6176519 A x' s h1 (@lem6176511 A B s g x' op h2)). Qed.
Lemma lem6176523 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s g x' op) : term1045.
Proof. exact (fun h0 : ~ False => @lem6176522 A B s g x' op h1 h2). Qed.
Lemma lem6176525 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6176526 : term1045 = False.
Proof. exact (@lem6176525 False). Qed.
Lemma lem6176527 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s g x' op) : False.
Proof. exact (EQ_MP (@lem6176526) (@lem6176523 A B s g x' op h1 h2)). Qed.
Lemma lem6176713 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (h1). Qed.
Lemma lem6176714 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : term1056 A B f x' op.
Proof. exact (fun h0 : term853 A B f x' op => @lem6176713 A B f x' op h1). Qed.
Lemma lem6176716 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6176717 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : (term1056 A B f x' op) = ((@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (@lem6176716 ((@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op))). Qed.
Lemma lem6176718 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (EQ_MP (@lem6176717 A B f x' op) (@lem6176714 A B f x' op h1)). Qed.
Lemma lem6176721 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6176723 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : (term853 A B f x' op) = (term1230 A B f x' op).
Proof. exact (@lem6176721 ((@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op))). Qed.
Lemma lem6176726 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s f x' op) : term1230 A B f x' op.
Proof. exact (EQ_MP (@lem6176723 A B f x' op) (@lem6175221 A B s f x' op h1)). Qed.
Lemma lem6176729 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s f x' op) (h2 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (@lem6176726 A B s f x' op h1 (@lem6176718 A B f x' op h2)). Qed.
Lemma lem6176730 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s f x' op) (h2 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : term1045.
Proof. exact (fun h0 : ~ False => @lem6176729 A B s f x' op h1 h2). Qed.
Lemma lem6176732 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6176733 : term1045 = False.
Proof. exact (@lem6176732 False). Qed.
Lemma lem6176734 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s f x' op) (h2 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6176733) (@lem6176730 A B s f x' op h1 h2)). Qed.
Lemma lem6176920 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (h1). Qed.
Lemma lem6176921 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : term1056 A B f x' op.
Proof. exact (fun h0 : term853 A B f x' op => @lem6176920 A B f x' op h1). Qed.
Lemma lem6176923 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6176924 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : (term1056 A B f x' op) = ((@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (@lem6176923 ((@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op))). Qed.
Lemma lem6176925 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (EQ_MP (@lem6176924 A B f x' op) (@lem6176921 A B f x' op h1)). Qed.
Lemma lem6176928 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6176930 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : (term853 A B f x' op) = (term1230 A B f x' op).
Proof. exact (@lem6176928 ((@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op))). Qed.
Lemma lem6176933 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term1225 A B g s f x' op) : term1230 A B f x' op.
Proof. exact (EQ_MP (@lem6176930 A B f x' op) (@lem6175261 A B g s f x' op h1)). Qed.
Lemma lem6176936 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term1225 A B g s f x' op) (h2 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (@lem6176933 A B g s f x' op h1 (@lem6176925 A B f x' op h2)). Qed.
Lemma lem6176937 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term1225 A B g s f x' op) (h2 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : term1045.
Proof. exact (fun h0 : ~ False => @lem6176936 A B g s f x' op h1 h2). Qed.
Lemma lem6176939 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6176940 : term1045 = False.
Proof. exact (@lem6176939 False). Qed.
Lemma lem6176941 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term1225 A B g s f x' op) (h2 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6176940) (@lem6176937 A B g s f x' op h1 h2)). Qed.
Lemma lem6176942 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term1225 A B g s f x' op) (h2 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : ((@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) = False.
Proof. exact (prop_ext (fun h3 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6176941 A B g s f x' op h1 h2) (fun h3 : False => @lem6175263 A B f x' op h2)). Qed.
Lemma lem6176943 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term1225 A B g s f x' op) (h2 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6176942 A B g s f x' op h1 h2) (@lem6175263 A B f x' op h2)). Qed.
Lemma lem6176944 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s f x' op) (h2 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : ((@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) = False.
Proof. exact (prop_ext (fun h3 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6176734 A B s f x' op h1 h2) (fun h3 : False => @lem6175217 A B f x' op h2)). Qed.
Lemma lem6176945 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s f x' op) (h2 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6176944 A B s f x' op h1 h2) (@lem6175217 A B f x' op h2)). Qed.
Lemma lem6176946 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6176527 A B s g x' op h1 h2) (fun h3 : False => @lem6175171 A x' s h1)). Qed.
Lemma lem6176947 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s g x' op) : False.
Proof. exact (EQ_MP (@lem6176946 A B s g x' op h1 h2) (@lem6175171 A x' s h1)). Qed.
Lemma lem6176948 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s f x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6176320 A B s f x' op h1 h2) (fun h3 : False => @lem6175125 A x' s h1)). Qed.
Lemma lem6176949 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s f x' op) : False.
Proof. exact (EQ_MP (@lem6176948 A B s f x' op h1 h2) (@lem6175125 A x' s h1)). Qed.
Lemma lem6176950 {A B : Type'} (s : A -> Prop) (g : A -> B) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term1227 A B f s g x' op) (h2 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : ((@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) = False.
Proof. exact (prop_ext (fun h3 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6176113 A B s g f x' op h1 h2) (fun h3 : False => @lem6175083 A B f x' op h2)). Qed.
Lemma lem6176951 {A B : Type'} (s : A -> Prop) (g : A -> B) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term1227 A B f s g x' op) (h2 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6176950 A B s g f x' op h1 h2) (@lem6175083 A B f x' op h2)). Qed.
Lemma lem6176952 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6175906 A B f s g x' op h1 h2) (fun h3 : False => @lem6175037 A x' s h1)). Qed.
Lemma lem6176953 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6176952 A B f s g x' op h1 h2) (@lem6175037 A x' s h1)). Qed.
Lemma lem6176954 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6175699 A B f s g x' op h1 h2) (fun h3 : False => @lem6174989 A x' s h1)). Qed.
Lemma lem6176955 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6176954 A B f s g x' op h1 h2) (@lem6174989 A x' s h1)). Qed.
Lemma lem6176956 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6175492 A B f s g x' op h1 h2) (fun h3 : False => @lem6174945 A x' s h1)). Qed.
Lemma lem6176957 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6176956 A B f s g x' op h1 h2) (@lem6174945 A x' s h1)). Qed.
Lemma lem6176958 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6176957 A B f s g x' op h1 h2) (fun h3 : False => @lem6174943 A x' s h1)). Qed.
Lemma lem6176959 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6176958 A B f s g x' op h1 h2) (@lem6174943 A x' s h1)). Qed.
Lemma lem6176960 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term1225 A B g s f x' op) (h2 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : ((@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) = False.
Proof. exact (prop_ext (fun h3 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6176943 A B g s f x' op h1 h2) (fun h3 : False => @lem6174757 A B f x' op h2)). Qed.
Lemma lem6176961 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term1225 A B g s f x' op) (h2 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6176960 A B g s f x' op h1 h2) (@lem6174757 A B f x' op h2)). Qed.
Lemma lem6176962 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s f x' op) (h2 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : ((@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) = False.
Proof. exact (prop_ext (fun h3 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6176945 A B s f x' op h1 h2) (fun h3 : False => @lem6174421 A B f x' op h2)). Qed.
Lemma lem6176963 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s f x' op) (h2 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6176962 A B s f x' op h1 h2) (@lem6174421 A B f x' op h2)). Qed.
Lemma lem6176964 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6176947 A B s g x' op h1 h2) (fun h3 : False => @lem6174085 A x' s h1)). Qed.
Lemma lem6176965 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s g x' op) : False.
Proof. exact (EQ_MP (@lem6176964 A B s g x' op h1 h2) (@lem6174085 A x' s h1)). Qed.
Lemma lem6176966 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s f x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6176949 A B s f x' op h1 h2) (fun h3 : False => @lem6173749 A x' s h1)). Qed.
Lemma lem6176967 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s f x' op) : False.
Proof. exact (EQ_MP (@lem6176966 A B s f x' op h1 h2) (@lem6173749 A x' s h1)). Qed.
Lemma lem6176968 {A B : Type'} (s : A -> Prop) (g : A -> B) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term1227 A B f s g x' op) (h2 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : ((@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) = False.
Proof. exact (prop_ext (fun h3 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6176951 A B s g f x' op h1 h2) (fun h3 : False => @lem6173421 A B f x' op h2)). Qed.
Lemma lem6176969 {A B : Type'} (s : A -> Prop) (g : A -> B) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term1227 A B f s g x' op) (h2 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6176968 A B s g f x' op h1 h2) (@lem6173421 A B f x' op h2)). Qed.
Lemma lem6176970 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6176953 A B f s g x' op h1 h2) (fun h3 : False => @lem6173085 A x' s h1)). Qed.
Lemma lem6176971 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6176970 A B f s g x' op h1 h2) (@lem6173085 A x' s h1)). Qed.
Lemma lem6176972 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6176955 A B f s g x' op h1 h2) (fun h3 : False => @lem6172745 A x' s h1)). Qed.
Lemma lem6176973 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6176972 A B f s g x' op h1 h2) (@lem6172745 A x' s h1)). Qed.
Lemma lem6176974 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6176959 A B f s g x' op h1 h2) (fun h3 : False => @lem6172413 A x' s h1)). Qed.
Lemma lem6176975 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6176974 A B f s g x' op h1 h2) (@lem6172413 A x' s h1)). Qed.
Lemma lem6176976 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6176975 A B f s g x' op h1 h2) (fun h3 : False => @lem6172409 A x' s h1)). Qed.
Lemma lem6176977 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6176976 A B f s g x' op h1 h2) (@lem6172409 A x' s h1)). Qed.
Lemma lem6176978 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term1225 A B g s f x' op) (h2 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : ((@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) = False.
Proof. exact (prop_ext (fun h3 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6176961 A B g s f x' op h1 h2) (fun h3 : False => @lem6174757 A B f x' op h2)). Qed.
Lemma lem6176979 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term1225 A B g s f x' op) (h2 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6176978 A B g s f x' op h1 h2) (@lem6174757 A B f x' op h2)). Qed.
Lemma lem6176980 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s f x' op) (h2 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : ((@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) = False.
Proof. exact (prop_ext (fun h3 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6176963 A B s f x' op h1 h2) (fun h3 : False => @lem6174421 A B f x' op h2)). Qed.
Lemma lem6176981 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s f x' op) (h2 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6176980 A B s f x' op h1 h2) (@lem6174421 A B f x' op h2)). Qed.
Lemma lem6176982 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6176965 A B s g x' op h1 h2) (fun h3 : False => @lem6174085 A x' s h1)). Qed.
Lemma lem6176983 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s g x' op) : False.
Proof. exact (EQ_MP (@lem6176982 A B s g x' op h1 h2) (@lem6174085 A x' s h1)). Qed.
Lemma lem6176984 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s f x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6176967 A B s f x' op h1 h2) (fun h3 : False => @lem6173749 A x' s h1)). Qed.
Lemma lem6176985 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s f x' op) : False.
Proof. exact (EQ_MP (@lem6176984 A B s f x' op h1 h2) (@lem6173749 A x' s h1)). Qed.
Lemma lem6176986 {A B : Type'} (s : A -> Prop) (g : A -> B) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term1227 A B f s g x' op) (h2 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : ((@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) = False.
Proof. exact (prop_ext (fun h3 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6176969 A B s g f x' op h1 h2) (fun h3 : False => @lem6173421 A B f x' op h2)). Qed.
Lemma lem6176987 {A B : Type'} (s : A -> Prop) (g : A -> B) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term1227 A B f s g x' op) (h2 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6176986 A B s g f x' op h1 h2) (@lem6173421 A B f x' op h2)). Qed.
Lemma lem6176988 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6176971 A B f s g x' op h1 h2) (fun h3 : False => @lem6173085 A x' s h1)). Qed.
Lemma lem6176989 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6176988 A B f s g x' op h1 h2) (@lem6173085 A x' s h1)). Qed.
Lemma lem6176990 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6176973 A B f s g x' op h1 h2) (fun h3 : False => @lem6172745 A x' s h1)). Qed.
Lemma lem6176991 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6176990 A B f s g x' op h1 h2) (@lem6172745 A x' s h1)). Qed.
Lemma lem6176992 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6176977 A B f s g x' op h1 h2) (fun h3 : False => @lem6172413 A x' s h1)). Qed.
Lemma lem6176993 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6176992 A B f s g x' op h1 h2) (@lem6172413 A x' s h1)). Qed.
Lemma lem6176994 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6176993 A B f s g x' op h1 h2) (fun h3 : False => @lem6172409 A x' s h1)). Qed.
Lemma lem6176995 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6176994 A B f s g x' op h1 h2) (@lem6172409 A x' s h1)). Qed.
Lemma lem6176996 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term1225 A B g s f x' op) (h2 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (or_elim (@lem6172063 A B g s f x' op h1) (fun h0 : term855 A B s f x' op => @lem6176981 A B s f x' op h0 h2) (fun h0 : term855 A B s g x' op => @lem6176979 A B g s f x' op h1 h2)). Qed.
Lemma lem6176997 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1225 A B g s f x' op) : False.
Proof. exact (or_elim (@lem6172063 A B g s f x' op h2) (fun h0 : term855 A B s f x' op => @lem6176985 A B s f x' op h1 h0) (fun h0 : term855 A B s g x' op => @lem6176983 A B s g x' op h1 h0)). Qed.
Lemma lem6176998 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term1225 A B g s f x' op) : False.
Proof. exact (or_elim (@lem6172062 A B g s f x' op h1) (fun h0 : term848 A x' s => @lem6176997 A B g s f x' op h0 h1) (fun h0 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6176996 A B g s f x' op h1 h0)). Qed.
Lemma lem6176999 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1227 A B f s g x' op) : False.
Proof. exact (or_elim (@lem6172051 A B f s g x' op h1) (fun h0 : term848 A x' s => @lem6176989 A B f s g x' op h0 h1) (fun h0 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6176987 A B s g f x' op h1 h0)). Qed.
Lemma lem6177000 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1227 A B f s g x' op) : False.
Proof. exact (or_elim (@lem6172051 A B f s g x' op h2) (fun h0 : term848 A x' s => @lem6176995 A B f s g x' op h1 h2) (fun h0 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6176991 A B f s g x' op h1 h2)). Qed.
Lemma lem6177001 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1227 A B f s g x' op) : False.
Proof. exact (or_elim (@lem6172050 A B f s g x' op h1) (fun h0 : term848 A x' s => @lem6177000 A B f s g x' op h0 h1) (fun h0 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6176999 A B f s g x' op h1)). Qed.
Lemma lem6177002 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term1219 A B g s f x' op) : False.
Proof. exact (or_elim (@lem6172043 A B g s f x' op h1) (fun h0 : term1227 A B f s g x' op => @lem6177001 A B f s g x' op h0) (fun h0 : term1225 A B g s f x' op => @lem6176998 A B g s f x' op h0)). Qed.
Lemma lem6177003 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term1148 A B g s f op) : False.
Proof. exact (ex_elim (@lem6170558 A B g s f op h1) (fun x' : A => fun h0 : term1221 A B g s f op x' => @lem6177002 A B g s f x' op h0)). Qed.
Lemma lem6177004 {A B : Type'} (y : type402 B) (x : type402 B) (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term741 B y x) (h2 : term1148 A B g s f op) : False.
Proof. exact (ex_elim (@lem6171256 B y x h1) (fun z : type402 B => fun h0 : term740 B y x z => @lem6177003 A B g s f op h2)). Qed.
Lemma lem6177005 {A B : Type'} (x : type402 B) (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term743 B x) (h2 : term1148 A B g s f op) : False.
Proof. exact (ex_elim (@lem6171255 B x h1) (fun y : type402 B => fun h0 : term742 B x y => @lem6177004 A B y x g s f op h0 h2)). Qed.
Lemma lem6177006 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term257 B) (h2 : term1148 A B g s f op) : False.
Proof. exact (ex_elim (@lem6171254 B h1) (fun x : type402 B => fun h0 : term744 B x => @lem6177005 A B x g s f op h0 h2)). Qed.
Lemma lem6177007 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term1148 A B g s f op) : term262 B.
Proof. exact (fun h0 : term257 B => @lem6177006 A B g s f op h0 h1). Qed.
Lemma lem6177008 {B : Type'} : (term262 B) = (term263 B).
Proof. exact (@lem69 (term257 B)). Qed.
Lemma lem6177009 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term1148 A B g s f op) : term263 B.
Proof. exact (EQ_MP (@lem6177008 B) (@lem6177007 A B g s f op h1)). Qed.
Lemma lem6177010 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : term1155 A B g s f op.
Proof. exact (fun h0 : term1148 A B g s f op => @lem6177009 A B g s f op h0). Qed.
Lemma lem6177011 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : term1157 A B g s f op.
Proof. exact (fun h0 : term58 A B op g s => @lem6177010 A B g s f op). Qed.
Lemma lem6177012 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : term1159 A B g s f op.
Proof. exact (fun h0 : term58 A B op f s => @lem6177011 A B g s f op). Qed.
Lemma lem6177013 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : term1160 A B g s f op.
Proof. exact (fun h0 : @monoidal B op => @lem6177012 A B g s f op). Qed.
Lemma lem6177018 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term1164 A B s f op.
Proof. exact (fun g : A -> B => @lem6177013 A B g s f op). Qed.
Lemma lem6177023 {A B : Type'} (f : A -> B) (op : type1400 B) : term1168 A B f op.
Proof. exact (fun s : A -> Prop => @lem6177018 A B s f op). Qed.
Lemma lem6177028 {A B : Type'} (op : type1400 B) : term1172 A B op.
Proof. exact (fun f : A -> B => @lem6177023 A B f op). Qed.
Lemma lem6177033 {A B : Type'} : term1176 A B.
Proof. exact (fun op : type1400 B => @lem6177028 A B op). Qed.
Lemma lem6177034 {A B : Type'} : term1175 A B.
Proof. exact (EQ_MP (@lem6170319 A B) (@lem6177033 A B)). Qed.
Lemma lem6177035 {A B : Type'} (op : type1400 B) : term1231 A B op.
Proof. exact (@lem6177034 A B op). Qed.
Lemma lem6177036 {A B : Type'} (op : type1400 B) : (term1231 A B op) = (term1171 A B op).
Proof. exact (eq_refl (term1231 A B op)). Qed.
Lemma lem6177037 {A B : Type'} (op : type1400 B) : term1171 A B op.
Proof. exact (EQ_MP (@lem6177036 A B op) (@lem6177035 A B op)). Qed.
Lemma lem6177038 {A B : Type'} (op : type1400 B) (f : A -> B) : term1232 A B op f.
Proof. exact (@lem6177037 A B op f). Qed.
Lemma lem6177039 {A B : Type'} (f : A -> B) (op : type1400 B) : (term1232 A B op f) = (term1167 A B f op).
Proof. exact (eq_refl (term1232 A B op f)). Qed.
Lemma lem6177040 {A B : Type'} (f : A -> B) (op : type1400 B) : term1167 A B f op.
Proof. exact (EQ_MP (@lem6177039 A B f op) (@lem6177038 A B op f)). Qed.
Lemma lem6177041 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) : term1233 A B f op s.
Proof. exact (@lem6177040 A B f op s). Qed.
Lemma lem6177042 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1233 A B f op s) = (term1163 A B s f op).
Proof. exact (eq_refl (term1233 A B f op s)). Qed.
Lemma lem6177043 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term1163 A B s f op.
Proof. exact (EQ_MP (@lem6177042 A B s f op) (@lem6177041 A B f op s)). Qed.
Lemma lem6177044 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (g : A -> B) : term1234 A B s f op g.
Proof. exact (@lem6177043 A B s f op g). Qed.
Lemma lem6177045 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term1234 A B s f op g) = (term1149 A B g s f op).
Proof. exact (eq_refl (term1234 A B s f op g)). Qed.
Lemma lem6177046 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : term1149 A B g s f op.
Proof. exact (EQ_MP (@lem6177045 A B g s f op) (@lem6177044 A B s f op g)). Qed.
Lemma lem6177048 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : term1149 A B g s f op.
Proof. exact (@lem6169928 A B g s f op (@lem6177046 A B g s f op)). Qed.
Lemma lem6177049 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term1158 A B g s f op.
Proof. exact (@lem6177048 A B g s f op (@lem6160869 B op h1)). Qed.
Lemma lem6177050 {A B : Type'} (g : A -> B) (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : @monoidal B op) : term1156 A B g s f op.
Proof. exact (@lem6177049 A B g s f op h2 (@lem6160872 A B op f s h1)). Qed.
Lemma lem6177051 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : term1154 A B g s f op.
Proof. exact (@lem6177050 A B g f s op h1 h3 (@lem6160871 A B op g s h2)). Qed.
Lemma lem6177052 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) (h4 : term1148 A B g s f op) : term262 B.
Proof. exact (@lem6177051 A B f g s op h1 h2 h3 (@lem6169909 A B g s f op h4)). Qed.
Lemma lem6177053 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) (h4 : term1148 A B g s f op) : False.
Proof. exact (@lem6177052 A B g s f op h1 h2 h3 h4 (@lem6169910 B)). Qed.
Lemma lem6177054 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) (h4 : term1148 A B g s f op) : (term1148 A B g s f op) = False.
Proof. exact (prop_ext (fun h5 : term1148 A B g s f op => @lem6177053 A B g s f op h1 h2 h3 h4) (fun h5 : False => @lem6169909 A B g s f op h4)). Qed.
Lemma lem6177055 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) (h4 : term1148 A B g s f op) : False.
Proof. exact (EQ_MP (@lem6177054 A B g s f op h1 h2 h3 h4) (@lem6169909 A B g s f op h4)). Qed.
Lemma lem6177056 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : term1147 A B g s f op.
Proof. exact (fun h0 : term1148 A B g s f op => @lem6177055 A B g s f op h1 h2 h3 h0). Qed.
Lemma lem6177057 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : term232 A B g s f op.
Proof. exact (EQ_MP (@lem6169908 A B g s f op) (@lem6177056 A B f g s op h1 h2 h3)). Qed.
Lemma lem6177059 (p : Prop) : p = (term254 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6177060 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term253 A B f s g op) = (term1235 A B f s g op).
Proof. exact (@lem6177059 (term253 A B f s g op)). Qed.
Lemma lem6177061 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1235 A B f s g op) = (term253 A B f s g op).
Proof. exact (SYM (@lem6177060 A B f s g op)). Qed.
Lemma lem6177062 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : term1236 A B f s g op) : term1236 A B f s g op.
Proof. exact (h1). Qed.
Lemma lem6177063 {B : Type'} : term257 B.
Proof. exact (@lem5712802 B). Qed.
Lemma lem6177068 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : term1237 A B f s g op) : term1237 A B f s g op.
Proof. exact (h1). Qed.
Lemma lem6177069 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : term1238 A B f s g op.
Proof. exact (fun h0 : term1237 A B f s g op => @lem6177068 A B f s g op h0). Qed.
Lemma lem6177070 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : term1238 A B f s g op) : term1238 A B f s g op.
Proof. exact (h1). Qed.
Lemma lem6177071 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : term1237 A B f s g op) : term1237 A B f s g op.
Proof. exact (h1). Qed.
Lemma lem6177072 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : term1237 A B f s g op) (h2 : term1238 A B f s g op) : term1237 A B f s g op.
Proof. exact (@lem6177070 A B f s g op h2 (@lem6177071 A B f s g op h1)). Qed.
Lemma lem6177073 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : term1237 A B f s g op) : term1239 A B f s g op.
Proof. exact (fun h0 : term1238 A B f s g op => @lem6177072 A B f s g op h1 h0). Qed.
Lemma lem6177074 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : term1238 A B f s g op) : term1238 A B f s g op.
Proof. exact (h1). Qed.
Lemma lem6177075 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : term1237 A B f s g op) (h2 : term1238 A B f s g op) : term1237 A B f s g op.
Proof. exact (@lem6177073 A B f s g op h1 (@lem6177074 A B f s g op h2)). Qed.
Lemma lem6177076 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : term1238 A B f s g op) : term1238 A B f s g op.
Proof. exact (fun h0 : term1237 A B f s g op => @lem6177075 A B f s g op h0 h1). Qed.
Lemma lem6177077 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : term1240 A B f s g op.
Proof. exact (fun h0 : term1238 A B f s g op => @lem6177076 A B f s g op h0). Qed.
Lemma lem6177080 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : term1238 A B f s g op.
Proof. exact (@lem6177077 A B f s g op (@lem6177069 A B f s g op)). Qed.
Lemma lem6177081 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : term1238 A B f s g op.
Proof. exact (@lem6177080 A B f s g op). Qed.
Lemma lem6177139 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6177140 {B : Type'} : (term262 B) = (term263 B).
Proof. exact (@lem6177139 (term257 B)). Qed.
Lemma lem6177173 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1241 A B f s g op) = (term1241 A B f s g op).
Proof. exact (eq_refl (term1241 A B f s g op)). Qed.
Lemma lem6177174 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1242 A B f s g op) = (term1243 A B f s g op).
Proof. exact (MK_COMB (@lem6177173 A B f s g op) (@lem6177140 B)). Qed.
Lemma lem6177177 {A B : Type'} (op : type1400 B) (g : A -> B) (s : A -> Prop) : (term267 A B op g s) = (term267 A B op g s).
Proof. exact (eq_refl (term267 A B op g s)). Qed.
Lemma lem6177178 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1244 A B f s g op) = (term1245 A B f s g op).
Proof. exact (MK_COMB (@lem6177177 A B op g s) (@lem6177174 A B f s g op)). Qed.
Lemma lem6177181 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term267 A B op f s) = (term267 A B op f s).
Proof. exact (eq_refl (term267 A B op f s)). Qed.
Lemma lem6177182 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1246 A B f s g op) = (term1247 A B f s g op).
Proof. exact (MK_COMB (@lem6177181 A B op f s) (@lem6177178 A B f s g op)). Qed.
Lemma lem6177185 {B : Type'} (op : type1400 B) : (term272 B op) = (term272 B op).
Proof. exact (eq_refl (term272 B op)). Qed.
Lemma lem6177186 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1237 A B f s g op) = (term1248 A B f s g op).
Proof. exact (MK_COMB (@lem6177185 B op) (@lem6177182 A B f s g op)). Qed.
Lemma lem6177189 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1249 A B s g op) = (term1250 A B s g op).
Proof. exact (fun_ext (fun f : A -> B => @lem6177186 A B f s g op)). Qed.
Lemma lem6177190 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem6177191 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1251 A B s g op) = (term1252 A B s g op).
Proof. exact (MK_COMB (@lem6177190 A B) (@lem6177189 A B s g op)). Qed.
Lemma lem6177196 {A B : Type'} (g : A -> B) (op : type1400 B) : (term1253 A B g op) = (term1254 A B g op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6177191 A B s g op)). Qed.
Lemma lem6177197 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6177198 {A B : Type'} (g : A -> B) (op : type1400 B) : (term1255 A B g op) = (term1256 A B g op).
Proof. exact (MK_COMB (@lem6177197 A) (@lem6177196 A B g op)). Qed.
Lemma lem6177203 {A B : Type'} (op : type1400 B) : (term1257 A B op) = (term1258 A B op).
Proof. exact (fun_ext (fun g : A -> B => @lem6177198 A B g op)). Qed.
Lemma lem6177204 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem6177205 {A B : Type'} (op : type1400 B) : (term1259 A B op) = (term1260 A B op).
Proof. exact (MK_COMB (@lem6177204 A B) (@lem6177203 A B op)). Qed.
Lemma lem6177210 {A B : Type'} : (term1261 A B) = (term1262 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6177205 A B op)). Qed.
Lemma lem6177211 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6177220 {A B : Type'} : (term1263 A B) = (term1264 A B).
Proof. exact (MK_COMB (@lem6177211 B) (@lem6177210 A B)). Qed.
Lemma lem6177221 {B : Type'} (op : type1400 B) (x : B) : ((term290 B op x) = x) = ((term290 B op x) = x).
Proof. exact (eq_refl ((term290 B op x) = x)). Qed.
Lemma lem6177222 {B : Type'} (op : type1400 B) : (term291 B op) = (term291 B op).
Proof. exact (fun_ext (fun x : B => @lem6177221 B op x)). Qed.
Lemma lem6177223 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6177224 {B : Type'} (op : type1400 B) : (term292 B op) = (term292 B op).
Proof. exact (MK_COMB (@lem6177223 B) (@lem6177222 B op)). Qed.
Lemma lem6177225 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : ((term293 B x op y z) = (term294 B op x y z)) = ((term293 B x op y z) = (term294 B op x y z)).
Proof. exact (eq_refl ((term293 B x op y z) = (term294 B op x y z))). Qed.
Lemma lem6177226 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term295 B op x y) = (term295 B op x y).
Proof. exact (fun_ext (fun z : B => @lem6177225 B op x y z)). Qed.
Lemma lem6177227 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6177228 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term296 B op x y) = (term296 B op x y).
Proof. exact (MK_COMB (@lem6177227 B) (@lem6177226 B op x y)). Qed.
Lemma lem6177229 {B : Type'} (op : type1400 B) (x : B) : (term297 B op x) = (term297 B op x).
Proof. exact (fun_ext (fun y : B => @lem6177228 B op x y)). Qed.
Lemma lem6177230 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6177231 {B : Type'} (op : type1400 B) (x : B) : (term298 B op x) = (term298 B op x).
Proof. exact (MK_COMB (@lem6177230 B) (@lem6177229 B op x)). Qed.
Lemma lem6177232 {B : Type'} (op : type1400 B) : (term299 B op) = (term299 B op).
Proof. exact (fun_ext (fun x : B => @lem6177231 B op x)). Qed.
Lemma lem6177233 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6177234 {B : Type'} (op : type1400 B) : (term300 B op) = (term300 B op).
Proof. exact (MK_COMB (@lem6177233 B) (@lem6177232 B op)). Qed.
Lemma lem6177235 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6177236 {B : Type'} (op : type1400 B) : (term301 B op) = (term301 B op).
Proof. exact (MK_COMB (@lem6177235) (@lem6177234 B op)). Qed.
Lemma lem6177237 {B : Type'} (op : type1400 B) : (term302 B op) = (term302 B op).
Proof. exact (MK_COMB (@lem6177236 B op) (@lem6177224 B op)). Qed.
Lemma lem6177238 {B : Type'} (op : type1400 B) (y : B) (x : B) : ((op x y) = (op y x)) = ((op x y) = (op y x)).
Proof. exact (eq_refl ((op x y) = (op y x))). Qed.
Lemma lem6177239 {B : Type'} (op : type1400 B) (x : B) : (term303 B op x) = (term303 B op x).
Proof. exact (fun_ext (fun y : B => @lem6177238 B op y x)). Qed.
Lemma lem6177240 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6177241 {B : Type'} (op : type1400 B) (x : B) : (term304 B op x) = (term304 B op x).
Proof. exact (MK_COMB (@lem6177240 B) (@lem6177239 B op x)). Qed.
Lemma lem6177242 {B : Type'} (op : type1400 B) : (term305 B op) = (term305 B op).
Proof. exact (fun_ext (fun x : B => @lem6177241 B op x)). Qed.
Lemma lem6177243 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6177244 {B : Type'} (op : type1400 B) : (term306 B op) = (term306 B op).
Proof. exact (MK_COMB (@lem6177243 B) (@lem6177242 B op)). Qed.
Lemma lem6177245 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6177246 {B : Type'} (op : type1400 B) : (term307 B op) = (term307 B op).
Proof. exact (MK_COMB (@lem6177245) (@lem6177244 B op)). Qed.
Lemma lem6177247 {B : Type'} (op : type1400 B) : (term308 B op) = (term308 B op).
Proof. exact (MK_COMB (@lem6177246 B op) (@lem6177237 B op)). Qed.
Lemma lem6177250 {B : Type'} (op : type1400 B) : (term309 B op) = (term309 B op).
Proof. exact (eq_refl (term309 B op)). Qed.
Lemma lem6177251 {B : Type'} (op : type1400 B) : ((@monoidal B op) = (term308 B op)) = ((@monoidal B op) = (term308 B op)).
Proof. exact (MK_COMB (@lem6177250 B op) (@lem6177247 B op)). Qed.
Lemma lem6177252 {B : Type'} : (term310 B) = (term310 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6177251 B op)). Qed.
Lemma lem6177253 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6177254 {B : Type'} : (term257 B) = (term257 B).
Proof. exact (MK_COMB (@lem6177253 B) (@lem6177252 B)). Qed.
Lemma lem6177255 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6177256 {B : Type'} : (term263 B) = (term263 B).
Proof. exact (MK_COMB (@lem6177255) (@lem6177254 B)). Qed.
Lemma lem6177289 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term247 A B f s g x op) = (term247 A B f s g x op).
Proof. exact (eq_refl (term247 A B f s g x op)). Qed.
Lemma lem6177290 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term249 A B f s g op) = (term249 A B f s g op).
Proof. exact (fun_ext (fun x : A => @lem6177289 A B f s g x op)). Qed.
Lemma lem6177291 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6177292 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term251 A B f s g op) = (term251 A B f s g op).
Proof. exact (MK_COMB (@lem6177291 A) (@lem6177290 A B f s g op)). Qed.
Lemma lem6177319 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term236 A B f s g x op) = (term236 A B f s g x op).
Proof. exact (eq_refl (term236 A B f s g x op)). Qed.
Lemma lem6177320 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term238 A B f s g op) = (term238 A B f s g op).
Proof. exact (fun_ext (fun x : A => @lem6177319 A B f s g x op)). Qed.
Lemma lem6177321 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6177322 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term239 A B f s g op) = (term239 A B f s g op).
Proof. exact (MK_COMB (@lem6177321 A) (@lem6177320 A B f s g op)). Qed.
Lemma lem6177323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6177324 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term241 A B f s g op) = (term241 A B f s g op).
Proof. exact (MK_COMB (@lem6177323) (@lem6177322 A B f s g op)). Qed.
Lemma lem6177325 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term253 A B f s g op) = (term253 A B f s g op).
Proof. exact (MK_COMB (@lem6177324 A B f s g op) (@lem6177292 A B f s g op)). Qed.
Lemma lem6177326 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6177327 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1236 A B f s g op) = (term1236 A B f s g op).
Proof. exact (MK_COMB (@lem6177326) (@lem6177325 A B f s g op)). Qed.
Lemma lem6177328 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6177329 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1241 A B f s g op) = (term1241 A B f s g op).
Proof. exact (MK_COMB (@lem6177328) (@lem6177327 A B f s g op)). Qed.
Lemma lem6177330 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1243 A B f s g op) = (term1243 A B f s g op).
Proof. exact (MK_COMB (@lem6177329 A B f s g op) (@lem6177256 B)). Qed.
Lemma lem6177333 {A B : Type'} (op : type1400 B) (g : A -> B) (s : A -> Prop) : (term267 A B op g s) = (term267 A B op g s).
Proof. exact (eq_refl (term267 A B op g s)). Qed.
Lemma lem6177334 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1245 A B f s g op) = (term1245 A B f s g op).
Proof. exact (MK_COMB (@lem6177333 A B op g s) (@lem6177330 A B f s g op)). Qed.
Lemma lem6177337 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term267 A B op f s) = (term267 A B op f s).
Proof. exact (eq_refl (term267 A B op f s)). Qed.
Lemma lem6177338 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1247 A B f s g op) = (term1247 A B f s g op).
Proof. exact (MK_COMB (@lem6177337 A B op f s) (@lem6177334 A B f s g op)). Qed.
Lemma lem6177341 {B : Type'} (op : type1400 B) : (term272 B op) = (term272 B op).
Proof. exact (eq_refl (term272 B op)). Qed.
Lemma lem6177342 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1248 A B f s g op) = (term1248 A B f s g op).
Proof. exact (MK_COMB (@lem6177341 B op) (@lem6177338 A B f s g op)). Qed.
Lemma lem6177343 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1250 A B s g op) = (term1250 A B s g op).
Proof. exact (fun_ext (fun f : A -> B => @lem6177342 A B f s g op)). Qed.
Lemma lem6177344 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem6177345 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1252 A B s g op) = (term1252 A B s g op).
Proof. exact (MK_COMB (@lem6177344 A B) (@lem6177343 A B s g op)). Qed.
Lemma lem6177346 {A B : Type'} (g : A -> B) (op : type1400 B) : (term1254 A B g op) = (term1254 A B g op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6177345 A B s g op)). Qed.
Lemma lem6177347 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6177348 {A B : Type'} (g : A -> B) (op : type1400 B) : (term1256 A B g op) = (term1256 A B g op).
Proof. exact (MK_COMB (@lem6177347 A) (@lem6177346 A B g op)). Qed.
Lemma lem6177349 {A B : Type'} (op : type1400 B) : (term1258 A B op) = (term1258 A B op).
Proof. exact (fun_ext (fun g : A -> B => @lem6177348 A B g op)). Qed.
Lemma lem6177350 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem6177351 {A B : Type'} (op : type1400 B) : (term1260 A B op) = (term1260 A B op).
Proof. exact (MK_COMB (@lem6177350 A B) (@lem6177349 A B op)). Qed.
Lemma lem6177352 {A B : Type'} : (term1262 A B) = (term1262 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6177351 A B op)). Qed.
Lemma lem6177353 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6177354 {A B : Type'} : (term1264 A B) = (term1264 A B).
Proof. exact (MK_COMB (@lem6177353 B) (@lem6177352 A B)). Qed.
Lemma lem6177471 {A B : Type'} : (term1263 A B) = (term1264 A B).
Proof. exact (TRANS (@lem6177220 A B) (@lem6177354 A B)). Qed.
Lemma lem6177472 {A B : Type'} : (term1264 A B) = (term1263 A B).
Proof. exact (SYM (@lem6177471 A B)). Qed.
Lemma lem6177476 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : term1236 A B f s g op) : term1236 A B f s g op.
Proof. exact (h1). Qed.
Lemma lem6177477 {B : Type'} (h1 : term257 B) : term257 B.
Proof. exact (h1). Qed.
Lemma lem6177504 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term311 A B f x op) = ((f x) = (@neutral B op)).
Proof. exact (@lem16933 ((f x) = (@neutral B op))). Qed.
Lemma lem6177506 {A : Type'} (x : A) (s : A -> Prop) : (term312 A x s) = (term312 A x s).
Proof. exact (eq_refl (term312 A x s)). Qed.
Lemma lem6177507 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term313 A B s f x op) = (term314 A B s f x op).
Proof. exact (MK_COMB (@lem6177506 A x s) (@lem6177504 A B f x op)). Qed.
Lemma lem6177508 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term220 A B s f x op) = (term313 A B s f x op).
Proof. exact (@lem17045 (@IN A x s) (term315 A B f x op)). Qed.
Lemma lem6177509 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term220 A B s f x op) = (term314 A B s f x op).
Proof. exact (TRANS (@lem6177508 A B s f x op) (@lem6177507 A B s f x op)). Qed.
Lemma lem6177513 {A B : Type'} (g : A -> B) (x : A) (op : type1400 B) : (term311 A B g x op) = ((g x) = (@neutral B op)).
Proof. exact (@lem16933 ((g x) = (@neutral B op))). Qed.
Lemma lem6177515 {A : Type'} (x : A) (s : A -> Prop) : (term312 A x s) = (term312 A x s).
Proof. exact (eq_refl (term312 A x s)). Qed.
Lemma lem6177516 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term313 A B s g x op) = (term314 A B s g x op).
Proof. exact (MK_COMB (@lem6177515 A x s) (@lem6177513 A B g x op)). Qed.
Lemma lem6177517 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term220 A B s g x op) = (term313 A B s g x op).
Proof. exact (@lem17045 (@IN A x s) (term315 A B g x op)). Qed.
Lemma lem6177518 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term220 A B s g x op) = (term314 A B s g x op).
Proof. exact (TRANS (@lem6177517 A B s g x op) (@lem6177516 A B s g x op)). Qed.
Lemma lem6177519 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6177520 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term316 A B s f x op) = (term317 A B s f x op).
Proof. exact (MK_COMB (@lem6177519) (@lem6177509 A B s f x op)). Qed.
Lemma lem6177521 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term318 A B f s g x op) = (term319 A B f s g x op).
Proof. exact (MK_COMB (@lem6177520 A B s f x op) (@lem6177518 A B s g x op)). Qed.
Lemma lem6177522 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term320 A B f s g x op) = (term318 A B f s g x op).
Proof. exact (@lem17160 (term168 A B s f x op) (term168 A B s g x op)). Qed.
Lemma lem6177523 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term320 A B f s g x op) = (term319 A B f s g x op).
Proof. exact (TRANS (@lem6177522 A B f s g x op) (@lem6177521 A B f s g x op)). Qed.
Lemma lem6177525 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term1177 A B s g x op) = (term1177 A B s g x op).
Proof. exact (eq_refl (term1177 A B s g x op)). Qed.
Lemma lem6177526 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term1265 A B f s g x op) = (term1266 A B f s g x op).
Proof. exact (MK_COMB (@lem6177525 A B s g x op) (@lem6177523 A B f s g x op)). Qed.
Lemma lem6177527 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term1267 A B f s g x op) = (term1265 A B f s g x op).
Proof. exact (@lem17362 (term168 A B s g x op) (term184 A B f s g x op)). Qed.
Lemma lem6177528 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term1267 A B f s g x op) = (term1266 A B f s g x op).
Proof. exact (TRANS (@lem6177527 A B f s g x op) (@lem6177526 A B f s g x op)). Qed.
Lemma lem6177529 {A : Type'} (P : A -> Prop) : (term325 A P) = (term326 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem6177530 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1268 A B f s g op) = (term1269 A B f s g op).
Proof. exact (@lem6177529 A (term238 A B f s g op)). Qed.
Lemma lem6177531 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term1270 A B f s g op x) = (term236 A B f s g x op).
Proof. exact (eq_refl (term1270 A B f s g op x)). Qed.
Lemma lem6177532 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6177533 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term1271 A B f s g op x) = (term1267 A B f s g x op).
Proof. exact (MK_COMB (@lem6177532) (@lem6177531 A B f s g x op)). Qed.
Lemma lem6177534 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term1271 A B f s g op x) = (term1266 A B f s g x op).
Proof. exact (TRANS (@lem6177533 A B f s g x op) (@lem6177528 A B f s g x op)). Qed.
Lemma lem6177535 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1272 A B f s g op) = (term1273 A B f s g op).
Proof. exact (fun_ext (fun x : A => @lem6177534 A B f s g x op)). Qed.
Lemma lem6177536 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6177537 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1269 A B f s g op) = (term1274 A B f s g op).
Proof. exact (MK_COMB (@lem6177536 A) (@lem6177535 A B f s g op)). Qed.
Lemma lem6177538 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1268 A B f s g op) = (term1274 A B f s g op).
Proof. exact (TRANS (@lem6177530 A B f s g op) (@lem6177537 A B f s g op)). Qed.
Lemma lem6177555 {A B : Type'} (g : A -> B) (x : A) (op : type1400 B) : (term311 A B g x op) = ((g x) = (@neutral B op)).
Proof. exact (@lem16933 ((g x) = (@neutral B op))). Qed.
Lemma lem6177557 {A : Type'} (x : A) (s : A -> Prop) : (term312 A x s) = (term312 A x s).
Proof. exact (eq_refl (term312 A x s)). Qed.
Lemma lem6177558 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term313 A B s g x op) = (term314 A B s g x op).
Proof. exact (MK_COMB (@lem6177557 A x s) (@lem6177555 A B g x op)). Qed.
Lemma lem6177559 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term220 A B s g x op) = (term313 A B s g x op).
Proof. exact (@lem17045 (@IN A x s) (term315 A B g x op)). Qed.
Lemma lem6177560 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term220 A B s g x op) = (term314 A B s g x op).
Proof. exact (TRANS (@lem6177559 A B s g x op) (@lem6177558 A B s g x op)). Qed.
Lemma lem6177562 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term193 A B f s g x op) = (term193 A B f s g x op).
Proof. exact (eq_refl (term193 A B f s g x op)). Qed.
Lemma lem6177563 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term243 A B f s g x op) = (term1275 A B f s g x op).
Proof. exact (MK_COMB (@lem6177562 A B f s g x op) (@lem6177560 A B s g x op)). Qed.
Lemma lem6177564 {A B : Type'} (g : A -> B) (x : A) (op : type1400 B) : (term315 A B g x op) = (term315 A B g x op).
Proof. exact (eq_refl (term315 A B g x op)). Qed.
Lemma lem6177565 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6177566 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term1276 A B f s g x op) = (term1277 A B f s g x op).
Proof. exact (MK_COMB (@lem6177565) (@lem6177563 A B f s g x op)). Qed.
Lemma lem6177567 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term1278 A B f s g x op) = (term1279 A B f s g x op).
Proof. exact (MK_COMB (@lem6177566 A B f s g x op) (@lem6177564 A B g x op)). Qed.
Lemma lem6177568 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term1280 A B f s g x op) = (term1278 A B f s g x op).
Proof. exact (@lem17362 (term243 A B f s g x op) ((g x) = (@neutral B op))). Qed.
Lemma lem6177569 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term1280 A B f s g x op) = (term1279 A B f s g x op).
Proof. exact (TRANS (@lem6177568 A B f s g x op) (@lem6177567 A B f s g x op)). Qed.
Lemma lem6177570 {A : Type'} (P : A -> Prop) : (term325 A P) = (term326 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem6177571 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1281 A B f s g op) = (term1282 A B f s g op).
Proof. exact (@lem6177570 A (term249 A B f s g op)). Qed.
Lemma lem6177572 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term1283 A B f s g op x) = (term247 A B f s g x op).
Proof. exact (eq_refl (term1283 A B f s g op x)). Qed.
Lemma lem6177573 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6177574 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term1284 A B f s g op x) = (term1280 A B f s g x op).
Proof. exact (MK_COMB (@lem6177573) (@lem6177572 A B f s g x op)). Qed.
Lemma lem6177575 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term1284 A B f s g op x) = (term1279 A B f s g x op).
Proof. exact (TRANS (@lem6177574 A B f s g x op) (@lem6177569 A B f s g x op)). Qed.
Lemma lem6177576 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1285 A B f s g op) = (term1286 A B f s g op).
Proof. exact (fun_ext (fun x : A => @lem6177575 A B f s g x op)). Qed.
Lemma lem6177577 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6177578 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1282 A B f s g op) = (term1287 A B f s g op).
Proof. exact (MK_COMB (@lem6177577 A) (@lem6177576 A B f s g op)). Qed.
Lemma lem6177579 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1281 A B f s g op) = (term1287 A B f s g op).
Proof. exact (TRANS (@lem6177571 A B f s g op) (@lem6177578 A B f s g op)). Qed.
Lemma lem6177580 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6177581 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1288 A B f s g op) = (term1289 A B f s g op).
Proof. exact (MK_COMB (@lem6177580) (@lem6177538 A B f s g op)). Qed.
Lemma lem6177582 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1290 A B f s g op) = (term1291 A B f s g op).
Proof. exact (MK_COMB (@lem6177581 A B f s g op) (@lem6177579 A B f s g op)). Qed.
Lemma lem6177583 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1236 A B f s g op) = (term1290 A B f s g op).
Proof. exact (@lem17045 (term239 A B f s g op) (term251 A B f s g op)). Qed.
Lemma lem6177584 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1236 A B f s g op) = (term1291 A B f s g op).
Proof. exact (TRANS (@lem6177583 A B f s g op) (@lem6177582 A B f s g op)). Qed.
Lemma lem6177683 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term354 A P Q) = (term355 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem6177684 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term354 A P Q) = (term355 A P Q).
Proof. exact (@lem6177683 A P Q). Qed.
Lemma lem6177685 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1292 A B f s g op) = (term1293 A B f s g op).
Proof. exact (@lem6177684 A (term1273 A B f s g op) (term1286 A B f s g op)). Qed.
Lemma lem6177686 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term1294 A B f s g op x) = (term1266 A B f s g x op).
Proof. exact (eq_refl (term1294 A B f s g op x)). Qed.
Lemma lem6177687 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1295 A B f s g op) = (term1273 A B f s g op).
Proof. exact (fun_ext (fun x : A => @lem6177686 A B f s g x op)). Qed.
Lemma lem6177688 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6177689 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1296 A B f s g op) = (term1274 A B f s g op).
Proof. exact (MK_COMB (@lem6177688 A) (@lem6177687 A B f s g op)). Qed.
Lemma lem6177690 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6177691 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1297 A B f s g op) = (term1289 A B f s g op).
Proof. exact (MK_COMB (@lem6177690) (@lem6177689 A B f s g op)). Qed.
Lemma lem6177692 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term1298 A B f s g op x) = (term1279 A B f s g x op).
Proof. exact (eq_refl (term1298 A B f s g op x)). Qed.
Lemma lem6177693 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1299 A B f s g op) = (term1286 A B f s g op).
Proof. exact (fun_ext (fun x : A => @lem6177692 A B f s g x op)). Qed.
Lemma lem6177694 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6177695 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1300 A B f s g op) = (term1287 A B f s g op).
Proof. exact (MK_COMB (@lem6177694 A) (@lem6177693 A B f s g op)). Qed.
Lemma lem6177696 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1292 A B f s g op) = (term1291 A B f s g op).
Proof. exact (MK_COMB (@lem6177691 A B f s g op) (@lem6177695 A B f s g op)). Qed.
Lemma lem6177697 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6177698 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1301 A B f s g op) = (term1302 A B f s g op).
Proof. exact (MK_COMB (@lem6177697) (@lem6177696 A B f s g op)). Qed.
Lemma lem6177699 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term1294 A B f s g op x) = (term1266 A B f s g x op).
Proof. exact (eq_refl (term1294 A B f s g op x)). Qed.
Lemma lem6177700 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6177701 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term1303 A B f s g op x) = (term1304 A B f s g x op).
Proof. exact (MK_COMB (@lem6177700) (@lem6177699 A B f s g x op)). Qed.
Lemma lem6177702 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term1298 A B f s g op x) = (term1279 A B f s g x op).
Proof. exact (eq_refl (term1298 A B f s g op x)). Qed.
Lemma lem6177703 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term1305 A B f s g op x) = (term1306 A B f s g x op).
Proof. exact (MK_COMB (@lem6177701 A B f s g x op) (@lem6177702 A B f s g x op)). Qed.
Lemma lem6177704 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1307 A B f s g op) = (term1308 A B f s g op).
Proof. exact (fun_ext (fun x : A => @lem6177703 A B f s g x op)). Qed.
Lemma lem6177705 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6177706 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1293 A B f s g op) = (term1309 A B f s g op).
Proof. exact (MK_COMB (@lem6177705 A) (@lem6177704 A B f s g op)). Qed.
Lemma lem6177707 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : ((term1292 A B f s g op) = (term1293 A B f s g op)) = ((term1291 A B f s g op) = (term1309 A B f s g op)).
Proof. exact (MK_COMB (@lem6177698 A B f s g op) (@lem6177706 A B f s g op)). Qed.
Lemma lem6177709 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1291 A B f s g op) = (term1309 A B f s g op).
Proof. exact (EQ_MP (@lem6177707 A B f s g op) (@lem6177685 A B f s g op)). Qed.
Lemma lem6177710 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1236 A B f s g op) = (term1309 A B f s g op).
Proof. exact (TRANS (@lem6177584 A B f s g op) (@lem6177709 A B f s g op)). Qed.
Lemma lem6177711 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : term1236 A B f s g op) : term1309 A B f s g op.
Proof. exact (EQ_MP (@lem6177710 A B f s g op) (@lem6177476 A B f s g op h1)). Qed.
Lemma lem6177715 {B : Type'} (op : type1400 B) (y : B) (x : B) : ((op x y) = (op y x)) = ((op x y) = (op y x)).
Proof. exact (eq_refl ((op x y) = (op y x))). Qed.
Lemma lem6177716 {B : Type'} (P : B -> Prop) : (term325 B P) = (term326 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem6177717 {B : Type'} (op : type1400 B) (x : B) : (term374 B op x) = (term375 B op x).
Proof. exact (@lem6177716 B (term303 B op x)). Qed.
Lemma lem6177718 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term376 B op x y) = ((op x y) = (op y x)).
Proof. exact (eq_refl (term376 B op x y)). Qed.
Lemma lem6177719 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6177721 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term377 B op x y) = (term378 B op y x).
Proof. exact (MK_COMB (@lem6177719) (@lem6177718 B op y x)). Qed.
Lemma lem6177722 {B : Type'} (op : type1400 B) (x : B) : (term379 B op x) = (term380 B op x).
Proof. exact (fun_ext (fun y : B => @lem6177721 B op y x)). Qed.
Lemma lem6177723 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6177724 {B : Type'} (op : type1400 B) (x : B) : (term375 B op x) = (term381 B op x).
Proof. exact (MK_COMB (@lem6177723 B) (@lem6177722 B op x)). Qed.
Lemma lem6177725 {B : Type'} (op : type1400 B) (x : B) : (term374 B op x) = (term381 B op x).
Proof. exact (TRANS (@lem6177717 B op x) (@lem6177724 B op x)). Qed.
Lemma lem6177726 {B : Type'} (op : type1400 B) (x : B) : (term303 B op x) = (term303 B op x).
Proof. exact (fun_ext (fun y : B => @lem6177715 B op y x)). Qed.
Lemma lem6177727 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6177728 {B : Type'} (op : type1400 B) (x : B) : (term304 B op x) = (term304 B op x).
Proof. exact (MK_COMB (@lem6177727 B) (@lem6177726 B op x)). Qed.
Lemma lem6177729 {B : Type'} (P : B -> Prop) : (term325 B P) = (term326 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem6177730 {B : Type'} (op : type1400 B) : (term382 B op) = (term383 B op).
Proof. exact (@lem6177729 B (term305 B op)). Qed.
Lemma lem6177731 {B : Type'} (op : type1400 B) (x : B) : (term384 B op x) = (term304 B op x).
Proof. exact (eq_refl (term384 B op x)). Qed.
Lemma lem6177732 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6177733 {B : Type'} (op : type1400 B) (x : B) : (term385 B op x) = (term374 B op x).
Proof. exact (MK_COMB (@lem6177732) (@lem6177731 B op x)). Qed.
Lemma lem6177734 {B : Type'} (op : type1400 B) (x : B) : (term385 B op x) = (term381 B op x).
Proof. exact (TRANS (@lem6177733 B op x) (@lem6177725 B op x)). Qed.
Lemma lem6177735 {B : Type'} (op : type1400 B) : (term386 B op) = (term387 B op).
Proof. exact (fun_ext (fun x : B => @lem6177734 B op x)). Qed.
Lemma lem6177736 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6177737 {B : Type'} (op : type1400 B) : (term383 B op) = (term388 B op).
Proof. exact (MK_COMB (@lem6177736 B) (@lem6177735 B op)). Qed.
Lemma lem6177738 {B : Type'} (op : type1400 B) : (term382 B op) = (term388 B op).
Proof. exact (TRANS (@lem6177730 B op) (@lem6177737 B op)). Qed.
Lemma lem6177739 {B : Type'} (op : type1400 B) : (term305 B op) = (term305 B op).
Proof. exact (fun_ext (fun x : B => @lem6177728 B op x)). Qed.
Lemma lem6177740 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6177741 {B : Type'} (op : type1400 B) : (term306 B op) = (term306 B op).
Proof. exact (MK_COMB (@lem6177740 B) (@lem6177739 B op)). Qed.
Lemma lem6177743 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : ((term293 B x op y z) = (term294 B op x y z)) = ((term293 B x op y z) = (term294 B op x y z)).
Proof. exact (eq_refl ((term293 B x op y z) = (term294 B op x y z))). Qed.
Lemma lem6177744 {B : Type'} (P : B -> Prop) : (term325 B P) = (term326 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem6177745 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term389 B op x y) = (term390 B op x y).
Proof. exact (@lem6177744 B (term295 B op x y)). Qed.
Lemma lem6177746 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term391 B op x y z) = ((term293 B x op y z) = (term294 B op x y z)).
Proof. exact (eq_refl (term391 B op x y z)). Qed.
Lemma lem6177747 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6177749 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term392 B op x y z) = (term393 B op x y z).
Proof. exact (MK_COMB (@lem6177747) (@lem6177746 B op x y z)). Qed.
Lemma lem6177750 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term394 B op x y) = (term395 B op x y).
Proof. exact (fun_ext (fun z : B => @lem6177749 B op x y z)). Qed.
Lemma lem6177751 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6177752 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term390 B op x y) = (term396 B op x y).
Proof. exact (MK_COMB (@lem6177751 B) (@lem6177750 B op x y)). Qed.
Lemma lem6177753 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term389 B op x y) = (term396 B op x y).
Proof. exact (TRANS (@lem6177745 B op x y) (@lem6177752 B op x y)). Qed.
Lemma lem6177754 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term295 B op x y) = (term295 B op x y).
Proof. exact (fun_ext (fun z : B => @lem6177743 B op x y z)). Qed.
Lemma lem6177755 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6177756 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term296 B op x y) = (term296 B op x y).
Proof. exact (MK_COMB (@lem6177755 B) (@lem6177754 B op x y)). Qed.
Lemma lem6177757 {B : Type'} (P : B -> Prop) : (term325 B P) = (term326 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem6177758 {B : Type'} (op : type1400 B) (x : B) : (term397 B op x) = (term398 B op x).
Proof. exact (@lem6177757 B (term297 B op x)). Qed.
Lemma lem6177759 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term399 B op x y) = (term296 B op x y).
Proof. exact (eq_refl (term399 B op x y)). Qed.
Lemma lem6177760 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6177761 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term400 B op x y) = (term389 B op x y).
Proof. exact (MK_COMB (@lem6177760) (@lem6177759 B op x y)). Qed.
Lemma lem6177762 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term400 B op x y) = (term396 B op x y).
Proof. exact (TRANS (@lem6177761 B op x y) (@lem6177753 B op x y)). Qed.
Lemma lem6177763 {B : Type'} (op : type1400 B) (x : B) : (term401 B op x) = (term402 B op x).
Proof. exact (fun_ext (fun y : B => @lem6177762 B op x y)). Qed.
Lemma lem6177764 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6177765 {B : Type'} (op : type1400 B) (x : B) : (term398 B op x) = (term403 B op x).
Proof. exact (MK_COMB (@lem6177764 B) (@lem6177763 B op x)). Qed.
Lemma lem6177766 {B : Type'} (op : type1400 B) (x : B) : (term397 B op x) = (term403 B op x).
Proof. exact (TRANS (@lem6177758 B op x) (@lem6177765 B op x)). Qed.
Lemma lem6177767 {B : Type'} (op : type1400 B) (x : B) : (term297 B op x) = (term297 B op x).
Proof. exact (fun_ext (fun y : B => @lem6177756 B op x y)). Qed.
Lemma lem6177768 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6177769 {B : Type'} (op : type1400 B) (x : B) : (term298 B op x) = (term298 B op x).
Proof. exact (MK_COMB (@lem6177768 B) (@lem6177767 B op x)). Qed.
Lemma lem6177770 {B : Type'} (P : B -> Prop) : (term325 B P) = (term326 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem6177771 {B : Type'} (op : type1400 B) : (term404 B op) = (term405 B op).
Proof. exact (@lem6177770 B (term299 B op)). Qed.
Lemma lem6177772 {B : Type'} (op : type1400 B) (x : B) : (term406 B op x) = (term298 B op x).
Proof. exact (eq_refl (term406 B op x)). Qed.
Lemma lem6177773 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6177774 {B : Type'} (op : type1400 B) (x : B) : (term407 B op x) = (term397 B op x).
Proof. exact (MK_COMB (@lem6177773) (@lem6177772 B op x)). Qed.
Lemma lem6177775 {B : Type'} (op : type1400 B) (x : B) : (term407 B op x) = (term403 B op x).
Proof. exact (TRANS (@lem6177774 B op x) (@lem6177766 B op x)). Qed.
Lemma lem6177776 {B : Type'} (op : type1400 B) : (term408 B op) = (term409 B op).
Proof. exact (fun_ext (fun x : B => @lem6177775 B op x)). Qed.
Lemma lem6177777 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6177778 {B : Type'} (op : type1400 B) : (term405 B op) = (term410 B op).
Proof. exact (MK_COMB (@lem6177777 B) (@lem6177776 B op)). Qed.
Lemma lem6177779 {B : Type'} (op : type1400 B) : (term404 B op) = (term410 B op).
Proof. exact (TRANS (@lem6177771 B op) (@lem6177778 B op)). Qed.
Lemma lem6177780 {B : Type'} (op : type1400 B) : (term299 B op) = (term299 B op).
Proof. exact (fun_ext (fun x : B => @lem6177769 B op x)). Qed.
Lemma lem6177781 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6177782 {B : Type'} (op : type1400 B) : (term300 B op) = (term300 B op).
Proof. exact (MK_COMB (@lem6177781 B) (@lem6177780 B op)). Qed.
Lemma lem6177784 {B : Type'} (op : type1400 B) (x : B) : ((term290 B op x) = x) = ((term290 B op x) = x).
Proof. exact (eq_refl ((term290 B op x) = x)). Qed.
Lemma lem6177785 {B : Type'} (P : B -> Prop) : (term325 B P) = (term326 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem6177786 {B : Type'} (op : type1400 B) : (term411 B op) = (term412 B op).
Proof. exact (@lem6177785 B (term291 B op)). Qed.
Lemma lem6177787 {B : Type'} (op : type1400 B) (x : B) : (term413 B op x) = ((term290 B op x) = x).
Proof. exact (eq_refl (term413 B op x)). Qed.
Lemma lem6177788 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6177790 {B : Type'} (op : type1400 B) (x : B) : (term414 B op x) = (term415 B op x).
Proof. exact (MK_COMB (@lem6177788) (@lem6177787 B op x)). Qed.
Lemma lem6177791 {B : Type'} (op : type1400 B) : (term416 B op) = (term417 B op).
Proof. exact (fun_ext (fun x : B => @lem6177790 B op x)). Qed.
Lemma lem6177792 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6177793 {B : Type'} (op : type1400 B) : (term412 B op) = (term418 B op).
Proof. exact (MK_COMB (@lem6177792 B) (@lem6177791 B op)). Qed.
Lemma lem6177794 {B : Type'} (op : type1400 B) : (term411 B op) = (term418 B op).
Proof. exact (TRANS (@lem6177786 B op) (@lem6177793 B op)). Qed.
Lemma lem6177795 {B : Type'} (op : type1400 B) : (term291 B op) = (term291 B op).
Proof. exact (fun_ext (fun x : B => @lem6177784 B op x)). Qed.
Lemma lem6177796 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6177797 {B : Type'} (op : type1400 B) : (term292 B op) = (term292 B op).
Proof. exact (MK_COMB (@lem6177796 B) (@lem6177795 B op)). Qed.
Lemma lem6177798 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6177799 {B : Type'} (op : type1400 B) : (term419 B op) = (term420 B op).
Proof. exact (MK_COMB (@lem6177798) (@lem6177779 B op)). Qed.
Lemma lem6177800 {B : Type'} (op : type1400 B) : (term421 B op) = (term422 B op).
Proof. exact (MK_COMB (@lem6177799 B op) (@lem6177794 B op)). Qed.
Lemma lem6177801 {B : Type'} (op : type1400 B) : (term423 B op) = (term421 B op).
Proof. exact (@lem17045 (term300 B op) (term292 B op)). Qed.
Lemma lem6177802 {B : Type'} (op : type1400 B) : (term423 B op) = (term422 B op).
Proof. exact (TRANS (@lem6177801 B op) (@lem6177800 B op)). Qed.
Lemma lem6177803 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6177804 {B : Type'} (op : type1400 B) : (term301 B op) = (term301 B op).
Proof. exact (MK_COMB (@lem6177803) (@lem6177782 B op)). Qed.
Lemma lem6177805 {B : Type'} (op : type1400 B) : (term302 B op) = (term302 B op).
Proof. exact (MK_COMB (@lem6177804 B op) (@lem6177797 B op)). Qed.
Lemma lem6177806 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6177807 {B : Type'} (op : type1400 B) : (term424 B op) = (term425 B op).
Proof. exact (MK_COMB (@lem6177806) (@lem6177738 B op)). Qed.
Lemma lem6177808 {B : Type'} (op : type1400 B) : (term426 B op) = (term427 B op).
Proof. exact (MK_COMB (@lem6177807 B op) (@lem6177802 B op)). Qed.
Lemma lem6177809 {B : Type'} (op : type1400 B) : (term428 B op) = (term426 B op).
Proof. exact (@lem17045 (term306 B op) (term302 B op)). Qed.
Lemma lem6177810 {B : Type'} (op : type1400 B) : (term428 B op) = (term427 B op).
Proof. exact (TRANS (@lem6177809 B op) (@lem6177808 B op)). Qed.
Lemma lem6177811 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6177812 {B : Type'} (op : type1400 B) : (term307 B op) = (term307 B op).
Proof. exact (MK_COMB (@lem6177811) (@lem6177741 B op)). Qed.
Lemma lem6177813 {B : Type'} (op : type1400 B) : (term308 B op) = (term308 B op).
Proof. exact (MK_COMB (@lem6177812 B op) (@lem6177805 B op)). Qed.
Lemma lem6177815 {B : Type'} (op : type1400 B) : (term429 B op) = (term429 B op).
Proof. exact (eq_refl (term429 B op)). Qed.
Lemma lem6177816 {B : Type'} (op : type1400 B) : (term430 B op) = (term430 B op).
Proof. exact (MK_COMB (@lem6177815 B op) (@lem6177813 B op)). Qed.
Lemma lem6177818 {B : Type'} (op : type1400 B) : (term431 B op) = (term431 B op).
Proof. exact (eq_refl (term431 B op)). Qed.
Lemma lem6177819 {B : Type'} (op : type1400 B) : (term432 B op) = (term433 B op).
Proof. exact (MK_COMB (@lem6177818 B op) (@lem6177810 B op)). Qed.
Lemma lem6177820 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6177821 {B : Type'} (op : type1400 B) : (term434 B op) = (term435 B op).
Proof. exact (MK_COMB (@lem6177820) (@lem6177819 B op)). Qed.
Lemma lem6177822 {B : Type'} (op : type1400 B) : (term436 B op) = (term437 B op).
Proof. exact (MK_COMB (@lem6177821 B op) (@lem6177816 B op)). Qed.
Lemma lem6177823 {B : Type'} (op : type1400 B) : ((@monoidal B op) = (term308 B op)) = (term436 B op).
Proof. exact (@lem17784 (@monoidal B op) (term308 B op)). Qed.
Lemma lem6177824 {B : Type'} (op : type1400 B) : ((@monoidal B op) = (term308 B op)) = (term437 B op).
Proof. exact (TRANS (@lem6177823 B op) (@lem6177822 B op)). Qed.
Lemma lem6177825 {B : Type'} : (term310 B) = (term438 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6177824 B op)). Qed.
Lemma lem6177826 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6177827 {B : Type'} : (term257 B) = (term439 B).
Proof. exact (MK_COMB (@lem6177826 B) (@lem6177825 B)). Qed.
Lemma lem6177829 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term440 A P Q) = (term441 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6177830 {B : Type'} (P : type403 B) (Q : type403 B) : (term442 B P Q) = (term443 B P Q).
Proof. exact (@lem6177829 (type1400 B) P Q). Qed.
Lemma lem6177831 {B : Type'} : (term444 B) = (term445 B).
Proof. exact (@lem6177830 B (term446 B) (term447 B)). Qed.
Lemma lem6177832 {B : Type'} (op : type1400 B) : (term448 B op) = (term433 B op).
Proof. exact (eq_refl (term448 B op)). Qed.
Lemma lem6177833 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6177834 {B : Type'} (op : type1400 B) : (term449 B op) = (term435 B op).
Proof. exact (MK_COMB (@lem6177833) (@lem6177832 B op)). Qed.
Lemma lem6177835 {B : Type'} (op : type1400 B) : (term450 B op) = (term430 B op).
Proof. exact (eq_refl (term450 B op)). Qed.
Lemma lem6177836 {B : Type'} (op : type1400 B) : (term451 B op) = (term437 B op).
Proof. exact (MK_COMB (@lem6177834 B op) (@lem6177835 B op)). Qed.
Lemma lem6177837 {B : Type'} : (term452 B) = (term438 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6177836 B op)). Qed.
Lemma lem6177838 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6177839 {B : Type'} : (term444 B) = (term439 B).
Proof. exact (MK_COMB (@lem6177838 B) (@lem6177837 B)). Qed.
Lemma lem6177840 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6177841 {B : Type'} : (term453 B) = (term454 B).
Proof. exact (MK_COMB (@lem6177840) (@lem6177839 B)). Qed.
Lemma lem6177842 {B : Type'} (op : type1400 B) : (term448 B op) = (term433 B op).
Proof. exact (eq_refl (term448 B op)). Qed.
Lemma lem6177843 {B : Type'} : (term455 B) = (term446 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6177842 B op)). Qed.
Lemma lem6177844 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6177845 {B : Type'} : (term456 B) = (term457 B).
Proof. exact (MK_COMB (@lem6177844 B) (@lem6177843 B)). Qed.
Lemma lem6177846 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6177847 {B : Type'} : (term458 B) = (term459 B).
Proof. exact (MK_COMB (@lem6177846) (@lem6177845 B)). Qed.
Lemma lem6177848 {B : Type'} (op : type1400 B) : (term450 B op) = (term430 B op).
Proof. exact (eq_refl (term450 B op)). Qed.
Lemma lem6177849 {B : Type'} : (term460 B) = (term447 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6177848 B op)). Qed.
Lemma lem6177850 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6177851 {B : Type'} : (term461 B) = (term462 B).
Proof. exact (MK_COMB (@lem6177850 B) (@lem6177849 B)). Qed.
Lemma lem6177852 {B : Type'} : (term445 B) = (term463 B).
Proof. exact (MK_COMB (@lem6177847 B) (@lem6177851 B)). Qed.
Lemma lem6177853 {B : Type'} : ((term444 B) = (term445 B)) = ((term439 B) = (term463 B)).
Proof. exact (MK_COMB (@lem6177841 B) (@lem6177852 B)). Qed.
Lemma lem6177854 {B : Type'} : (term439 B) = (term463 B).
Proof. exact (EQ_MP (@lem6177853 B) (@lem6177831 B)). Qed.
Lemma lem6177980 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term354 A P Q) = (term355 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem6177981 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term354 B P Q) = (term355 B P Q).
Proof. exact (@lem6177980 B P Q). Qed.
Lemma lem6177982 {B : Type'} (op : type1400 B) : (term464 B op) = (term465 B op).
Proof. exact (@lem6177981 B (term409 B op) (term417 B op)). Qed.
Lemma lem6177983 {B : Type'} (op : type1400 B) (x : B) : (term466 B op x) = (term403 B op x).
Proof. exact (eq_refl (term466 B op x)). Qed.
Lemma lem6177984 {B : Type'} (op : type1400 B) : (term467 B op) = (term409 B op).
Proof. exact (fun_ext (fun x : B => @lem6177983 B op x)). Qed.
Lemma lem6177985 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6177986 {B : Type'} (op : type1400 B) : (term468 B op) = (term410 B op).
Proof. exact (MK_COMB (@lem6177985 B) (@lem6177984 B op)). Qed.
Lemma lem6177987 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6177988 {B : Type'} (op : type1400 B) : (term469 B op) = (term420 B op).
Proof. exact (MK_COMB (@lem6177987) (@lem6177986 B op)). Qed.
Lemma lem6177989 {B : Type'} (op : type1400 B) (x : B) : (term470 B op x) = (term415 B op x).
Proof. exact (eq_refl (term470 B op x)). Qed.
Lemma lem6177990 {B : Type'} (op : type1400 B) : (term471 B op) = (term417 B op).
Proof. exact (fun_ext (fun x : B => @lem6177989 B op x)). Qed.
Lemma lem6177991 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6177992 {B : Type'} (op : type1400 B) : (term472 B op) = (term418 B op).
Proof. exact (MK_COMB (@lem6177991 B) (@lem6177990 B op)). Qed.
Lemma lem6177993 {B : Type'} (op : type1400 B) : (term464 B op) = (term422 B op).
Proof. exact (MK_COMB (@lem6177988 B op) (@lem6177992 B op)). Qed.
Lemma lem6177994 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6177995 {B : Type'} (op : type1400 B) : (term473 B op) = (term474 B op).
Proof. exact (MK_COMB (@lem6177994) (@lem6177993 B op)). Qed.
Lemma lem6177996 {B : Type'} (op : type1400 B) (x : B) : (term466 B op x) = (term403 B op x).
Proof. exact (eq_refl (term466 B op x)). Qed.
Lemma lem6177997 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6177998 {B : Type'} (op : type1400 B) (x : B) : (term475 B op x) = (term476 B op x).
Proof. exact (MK_COMB (@lem6177997) (@lem6177996 B op x)). Qed.
Lemma lem6177999 {B : Type'} (op : type1400 B) (x : B) : (term470 B op x) = (term415 B op x).
Proof. exact (eq_refl (term470 B op x)). Qed.
Lemma lem6178000 {B : Type'} (op : type1400 B) (x : B) : (term477 B op x) = (term478 B op x).
Proof. exact (MK_COMB (@lem6177998 B op x) (@lem6177999 B op x)). Qed.
Lemma lem6178001 {B : Type'} (op : type1400 B) : (term479 B op) = (term480 B op).
Proof. exact (fun_ext (fun x : B => @lem6178000 B op x)). Qed.
Lemma lem6178002 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6178003 {B : Type'} (op : type1400 B) : (term465 B op) = (term481 B op).
Proof. exact (MK_COMB (@lem6178002 B) (@lem6178001 B op)). Qed.
Lemma lem6178004 {B : Type'} (op : type1400 B) : ((term464 B op) = (term465 B op)) = ((term422 B op) = (term481 B op)).
Proof. exact (MK_COMB (@lem6177995 B op) (@lem6178003 B op)). Qed.
Lemma lem6178005 {B : Type'} (op : type1400 B) : (term422 B op) = (term481 B op).
Proof. exact (EQ_MP (@lem6178004 B op) (@lem6177982 B op)). Qed.
Lemma lem6178007 {A : Type'} (P : A -> Prop) (Q : Prop) : (term482 A P Q) = (term483 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6178008 {B : Type'} (P : B -> Prop) (Q : Prop) : (term482 B P Q) = (term483 B P Q).
Proof. exact (@lem6178007 B P Q). Qed.
Lemma lem6178009 {B : Type'} (op : type1400 B) (x : B) : (term484 B op x) = (term485 B op x).
Proof. exact (@lem6178008 B (term402 B op x) (term415 B op x)). Qed.
Lemma lem6178010 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term486 B op x y) = (term396 B op x y).
Proof. exact (eq_refl (term486 B op x y)). Qed.
Lemma lem6178011 {B : Type'} (op : type1400 B) (x : B) : (term487 B op x) = (term402 B op x).
Proof. exact (fun_ext (fun y : B => @lem6178010 B op x y)). Qed.
Lemma lem6178012 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6178013 {B : Type'} (op : type1400 B) (x : B) : (term488 B op x) = (term403 B op x).
Proof. exact (MK_COMB (@lem6178012 B) (@lem6178011 B op x)). Qed.
Lemma lem6178014 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6178015 {B : Type'} (op : type1400 B) (x : B) : (term489 B op x) = (term476 B op x).
Proof. exact (MK_COMB (@lem6178014) (@lem6178013 B op x)). Qed.
Lemma lem6178016 {B : Type'} (op : type1400 B) (x : B) : (term415 B op x) = (term415 B op x).
Proof. exact (eq_refl (term415 B op x)). Qed.
Lemma lem6178017 {B : Type'} (op : type1400 B) (x : B) : (term484 B op x) = (term478 B op x).
Proof. exact (MK_COMB (@lem6178015 B op x) (@lem6178016 B op x)). Qed.
Lemma lem6178018 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6178019 {B : Type'} (op : type1400 B) (x : B) : (term490 B op x) = (term491 B op x).
Proof. exact (MK_COMB (@lem6178018) (@lem6178017 B op x)). Qed.
Lemma lem6178020 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term486 B op x y) = (term396 B op x y).
Proof. exact (eq_refl (term486 B op x y)). Qed.
Lemma lem6178021 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6178022 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term492 B op x y) = (term493 B op x y).
Proof. exact (MK_COMB (@lem6178021) (@lem6178020 B op x y)). Qed.
Lemma lem6178023 {B : Type'} (op : type1400 B) (x : B) : (term415 B op x) = (term415 B op x).
Proof. exact (eq_refl (term415 B op x)). Qed.
Lemma lem6178024 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term494 B y op x) = (term495 B y op x).
Proof. exact (MK_COMB (@lem6178022 B op x y) (@lem6178023 B op x)). Qed.
Lemma lem6178025 {B : Type'} (op : type1400 B) (x : B) : (term496 B op x) = (term497 B op x).
Proof. exact (fun_ext (fun y : B => @lem6178024 B y op x)). Qed.
Lemma lem6178026 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6178027 {B : Type'} (op : type1400 B) (x : B) : (term485 B op x) = (term498 B op x).
Proof. exact (MK_COMB (@lem6178026 B) (@lem6178025 B op x)). Qed.
Lemma lem6178028 {B : Type'} (op : type1400 B) (x : B) : ((term484 B op x) = (term485 B op x)) = ((term478 B op x) = (term498 B op x)).
Proof. exact (MK_COMB (@lem6178019 B op x) (@lem6178027 B op x)). Qed.
Lemma lem6178029 {B : Type'} (op : type1400 B) (x : B) : (term478 B op x) = (term498 B op x).
Proof. exact (EQ_MP (@lem6178028 B op x) (@lem6178009 B op x)). Qed.
Lemma lem6178031 {A : Type'} (P : A -> Prop) (Q : Prop) : (term482 A P Q) = (term483 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6178032 {B : Type'} (P : B -> Prop) (Q : Prop) : (term482 B P Q) = (term483 B P Q).
Proof. exact (@lem6178031 B P Q). Qed.
Lemma lem6178033 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term499 B y op x) = (term500 B y op x).
Proof. exact (@lem6178032 B (term395 B op x y) (term415 B op x)). Qed.
Lemma lem6178034 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term501 B op x y z) = (term393 B op x y z).
Proof. exact (eq_refl (term501 B op x y z)). Qed.
Lemma lem6178035 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term502 B op x y) = (term395 B op x y).
Proof. exact (fun_ext (fun z : B => @lem6178034 B op x y z)). Qed.
Lemma lem6178036 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6178037 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term503 B op x y) = (term396 B op x y).
Proof. exact (MK_COMB (@lem6178036 B) (@lem6178035 B op x y)). Qed.
Lemma lem6178038 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6178039 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term504 B op x y) = (term493 B op x y).
Proof. exact (MK_COMB (@lem6178038) (@lem6178037 B op x y)). Qed.
Lemma lem6178040 {B : Type'} (op : type1400 B) (x : B) : (term415 B op x) = (term415 B op x).
Proof. exact (eq_refl (term415 B op x)). Qed.
Lemma lem6178041 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term499 B y op x) = (term495 B y op x).
Proof. exact (MK_COMB (@lem6178039 B op x y) (@lem6178040 B op x)). Qed.
Lemma lem6178042 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6178043 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term505 B y op x) = (term506 B y op x).
Proof. exact (MK_COMB (@lem6178042) (@lem6178041 B y op x)). Qed.
Lemma lem6178044 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term501 B op x y z) = (term393 B op x y z).
Proof. exact (eq_refl (term501 B op x y z)). Qed.
Lemma lem6178045 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6178046 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term507 B op x y z) = (term508 B op x y z).
Proof. exact (MK_COMB (@lem6178045) (@lem6178044 B op x y z)). Qed.
Lemma lem6178047 {B : Type'} (op : type1400 B) (x : B) : (term415 B op x) = (term415 B op x).
Proof. exact (eq_refl (term415 B op x)). Qed.
Lemma lem6178048 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term509 B y z op x) = (term510 B y z op x).
Proof. exact (MK_COMB (@lem6178046 B op x y z) (@lem6178047 B op x)). Qed.
Lemma lem6178049 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term511 B y op x) = (term512 B y op x).
Proof. exact (fun_ext (fun z : B => @lem6178048 B y z op x)). Qed.
Lemma lem6178050 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6178051 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term500 B y op x) = (term513 B y op x).
Proof. exact (MK_COMB (@lem6178050 B) (@lem6178049 B y op x)). Qed.
Lemma lem6178052 {B : Type'} (y : B) (op : type1400 B) (x : B) : ((term499 B y op x) = (term500 B y op x)) = ((term495 B y op x) = (term513 B y op x)).
Proof. exact (MK_COMB (@lem6178043 B y op x) (@lem6178051 B y op x)). Qed.
Lemma lem6178053 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term495 B y op x) = (term513 B y op x).
Proof. exact (EQ_MP (@lem6178052 B y op x) (@lem6178033 B y op x)). Qed.
Lemma lem6178054 {B : Type'} (op : type1400 B) (x : B) : (term497 B op x) = (term514 B op x).
Proof. exact (fun_ext (fun y : B => @lem6178053 B y op x)). Qed.
Lemma lem6178055 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6178056 {B : Type'} (op : type1400 B) (x : B) : (term498 B op x) = (term515 B op x).
Proof. exact (MK_COMB (@lem6178055 B) (@lem6178054 B op x)). Qed.
Lemma lem6178057 {B : Type'} (op : type1400 B) (x : B) : (term478 B op x) = (term515 B op x).
Proof. exact (TRANS (@lem6178029 B op x) (@lem6178056 B op x)). Qed.
Lemma lem6178058 {B : Type'} (op : type1400 B) : (term480 B op) = (term516 B op).
Proof. exact (fun_ext (fun x : B => @lem6178057 B op x)). Qed.
Lemma lem6178059 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6178060 {B : Type'} (op : type1400 B) : (term481 B op) = (term517 B op).
Proof. exact (MK_COMB (@lem6178059 B) (@lem6178058 B op)). Qed.
Lemma lem6178061 {B : Type'} (op : type1400 B) : (term422 B op) = (term517 B op).
Proof. exact (TRANS (@lem6178005 B op) (@lem6178060 B op)). Qed.
Lemma lem6178062 {B : Type'} (op : type1400 B) : (term425 B op) = (term425 B op).
Proof. exact (eq_refl (term425 B op)). Qed.
Lemma lem6178063 {B : Type'} (op : type1400 B) : (term427 B op) = (term518 B op).
Proof. exact (MK_COMB (@lem6178062 B op) (@lem6178061 B op)). Qed.
Lemma lem6178065 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term354 A P Q) = (term355 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem6178066 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term354 B P Q) = (term355 B P Q).
Proof. exact (@lem6178065 B P Q). Qed.
Lemma lem6178067 {B : Type'} (op : type1400 B) : (term519 B op) = (term520 B op).
Proof. exact (@lem6178066 B (term387 B op) (term516 B op)). Qed.
Lemma lem6178068 {B : Type'} (op : type1400 B) (x : B) : (term521 B op x) = (term381 B op x).
Proof. exact (eq_refl (term521 B op x)). Qed.
Lemma lem6178069 {B : Type'} (op : type1400 B) : (term522 B op) = (term387 B op).
Proof. exact (fun_ext (fun x : B => @lem6178068 B op x)). Qed.
Lemma lem6178070 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6178071 {B : Type'} (op : type1400 B) : (term523 B op) = (term388 B op).
Proof. exact (MK_COMB (@lem6178070 B) (@lem6178069 B op)). Qed.
Lemma lem6178072 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6178073 {B : Type'} (op : type1400 B) : (term524 B op) = (term425 B op).
Proof. exact (MK_COMB (@lem6178072) (@lem6178071 B op)). Qed.
Lemma lem6178074 {B : Type'} (op : type1400 B) (x : B) : (term525 B op x) = (term515 B op x).
Proof. exact (eq_refl (term525 B op x)). Qed.
Lemma lem6178075 {B : Type'} (op : type1400 B) : (term526 B op) = (term516 B op).
Proof. exact (fun_ext (fun x : B => @lem6178074 B op x)). Qed.
Lemma lem6178076 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6178077 {B : Type'} (op : type1400 B) : (term527 B op) = (term517 B op).
Proof. exact (MK_COMB (@lem6178076 B) (@lem6178075 B op)). Qed.
Lemma lem6178078 {B : Type'} (op : type1400 B) : (term519 B op) = (term518 B op).
Proof. exact (MK_COMB (@lem6178073 B op) (@lem6178077 B op)). Qed.
Lemma lem6178079 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6178080 {B : Type'} (op : type1400 B) : (term528 B op) = (term529 B op).
Proof. exact (MK_COMB (@lem6178079) (@lem6178078 B op)). Qed.
Lemma lem6178081 {B : Type'} (op : type1400 B) (x : B) : (term521 B op x) = (term381 B op x).
Proof. exact (eq_refl (term521 B op x)). Qed.
Lemma lem6178082 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6178083 {B : Type'} (op : type1400 B) (x : B) : (term530 B op x) = (term531 B op x).
Proof. exact (MK_COMB (@lem6178082) (@lem6178081 B op x)). Qed.
Lemma lem6178084 {B : Type'} (op : type1400 B) (x : B) : (term525 B op x) = (term515 B op x).
Proof. exact (eq_refl (term525 B op x)). Qed.
Lemma lem6178085 {B : Type'} (op : type1400 B) (x : B) : (term532 B op x) = (term533 B op x).
Proof. exact (MK_COMB (@lem6178083 B op x) (@lem6178084 B op x)). Qed.
Lemma lem6178086 {B : Type'} (op : type1400 B) : (term534 B op) = (term535 B op).
Proof. exact (fun_ext (fun x : B => @lem6178085 B op x)). Qed.
Lemma lem6178087 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6178088 {B : Type'} (op : type1400 B) : (term520 B op) = (term536 B op).
Proof. exact (MK_COMB (@lem6178087 B) (@lem6178086 B op)). Qed.
Lemma lem6178089 {B : Type'} (op : type1400 B) : ((term519 B op) = (term520 B op)) = ((term518 B op) = (term536 B op)).
Proof. exact (MK_COMB (@lem6178080 B op) (@lem6178088 B op)). Qed.
Lemma lem6178090 {B : Type'} (op : type1400 B) : (term518 B op) = (term536 B op).
Proof. exact (EQ_MP (@lem6178089 B op) (@lem6178067 B op)). Qed.
Lemma lem6178092 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term354 A P Q) = (term355 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem6178093 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term354 B P Q) = (term355 B P Q).
Proof. exact (@lem6178092 B P Q). Qed.
Lemma lem6178094 {B : Type'} (op : type1400 B) (x : B) : (term537 B op x) = (term538 B op x).
Proof. exact (@lem6178093 B (term380 B op x) (term514 B op x)). Qed.
Lemma lem6178095 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term539 B op x y) = (term378 B op y x).
Proof. exact (eq_refl (term539 B op x y)). Qed.
Lemma lem6178096 {B : Type'} (op : type1400 B) (x : B) : (term540 B op x) = (term380 B op x).
Proof. exact (fun_ext (fun y : B => @lem6178095 B op y x)). Qed.
Lemma lem6178097 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6178098 {B : Type'} (op : type1400 B) (x : B) : (term541 B op x) = (term381 B op x).
Proof. exact (MK_COMB (@lem6178097 B) (@lem6178096 B op x)). Qed.
Lemma lem6178099 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6178100 {B : Type'} (op : type1400 B) (x : B) : (term542 B op x) = (term531 B op x).
Proof. exact (MK_COMB (@lem6178099) (@lem6178098 B op x)). Qed.
Lemma lem6178101 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term543 B op x y) = (term513 B y op x).
Proof. exact (eq_refl (term543 B op x y)). Qed.
Lemma lem6178102 {B : Type'} (op : type1400 B) (x : B) : (term544 B op x) = (term514 B op x).
Proof. exact (fun_ext (fun y : B => @lem6178101 B y op x)). Qed.
Lemma lem6178103 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6178104 {B : Type'} (op : type1400 B) (x : B) : (term545 B op x) = (term515 B op x).
Proof. exact (MK_COMB (@lem6178103 B) (@lem6178102 B op x)). Qed.
Lemma lem6178105 {B : Type'} (op : type1400 B) (x : B) : (term537 B op x) = (term533 B op x).
Proof. exact (MK_COMB (@lem6178100 B op x) (@lem6178104 B op x)). Qed.
Lemma lem6178106 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6178107 {B : Type'} (op : type1400 B) (x : B) : (term546 B op x) = (term547 B op x).
Proof. exact (MK_COMB (@lem6178106) (@lem6178105 B op x)). Qed.
Lemma lem6178108 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term539 B op x y) = (term378 B op y x).
Proof. exact (eq_refl (term539 B op x y)). Qed.
Lemma lem6178109 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6178110 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term548 B op x y) = (term549 B op y x).
Proof. exact (MK_COMB (@lem6178109) (@lem6178108 B op y x)). Qed.
Lemma lem6178111 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term543 B op x y) = (term513 B y op x).
Proof. exact (eq_refl (term543 B op x y)). Qed.
Lemma lem6178112 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term550 B op x y) = (term551 B y op x).
Proof. exact (MK_COMB (@lem6178110 B op y x) (@lem6178111 B y op x)). Qed.
Lemma lem6178113 {B : Type'} (op : type1400 B) (x : B) : (term552 B op x) = (term553 B op x).
Proof. exact (fun_ext (fun y : B => @lem6178112 B y op x)). Qed.
Lemma lem6178114 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6178115 {B : Type'} (op : type1400 B) (x : B) : (term538 B op x) = (term554 B op x).
Proof. exact (MK_COMB (@lem6178114 B) (@lem6178113 B op x)). Qed.
Lemma lem6178116 {B : Type'} (op : type1400 B) (x : B) : ((term537 B op x) = (term538 B op x)) = ((term533 B op x) = (term554 B op x)).
Proof. exact (MK_COMB (@lem6178107 B op x) (@lem6178115 B op x)). Qed.
Lemma lem6178117 {B : Type'} (op : type1400 B) (x : B) : (term533 B op x) = (term554 B op x).
Proof. exact (EQ_MP (@lem6178116 B op x) (@lem6178094 B op x)). Qed.
Lemma lem6178119 {A : Type'} (P : Prop) (Q : A -> Prop) : (term555 A P Q) = (term556 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6178120 {B : Type'} (P : Prop) (Q : B -> Prop) : (term555 B P Q) = (term556 B P Q).
Proof. exact (@lem6178119 B P Q). Qed.
Lemma lem6178121 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term557 B y op x) = (term558 B y op x).
Proof. exact (@lem6178120 B (term378 B op y x) (term512 B y op x)). Qed.
Lemma lem6178122 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term559 B y op x z) = (term510 B y z op x).
Proof. exact (eq_refl (term559 B y op x z)). Qed.
Lemma lem6178123 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term560 B y op x) = (term512 B y op x).
Proof. exact (fun_ext (fun z : B => @lem6178122 B y z op x)). Qed.
Lemma lem6178124 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6178125 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term561 B y op x) = (term513 B y op x).
Proof. exact (MK_COMB (@lem6178124 B) (@lem6178123 B y op x)). Qed.
Lemma lem6178126 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term549 B op y x) = (term549 B op y x).
Proof. exact (eq_refl (term549 B op y x)). Qed.
Lemma lem6178127 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term557 B y op x) = (term551 B y op x).
Proof. exact (MK_COMB (@lem6178126 B op y x) (@lem6178125 B y op x)). Qed.
Lemma lem6178128 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6178129 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term562 B y op x) = (term563 B y op x).
Proof. exact (MK_COMB (@lem6178128) (@lem6178127 B y op x)). Qed.
Lemma lem6178130 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term559 B y op x z) = (term510 B y z op x).
Proof. exact (eq_refl (term559 B y op x z)). Qed.
Lemma lem6178131 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term549 B op y x) = (term549 B op y x).
Proof. exact (eq_refl (term549 B op y x)). Qed.
Lemma lem6178132 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term564 B y op x z) = (term565 B y z op x).
Proof. exact (MK_COMB (@lem6178131 B op y x) (@lem6178130 B y z op x)). Qed.
Lemma lem6178133 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term566 B y op x) = (term567 B y op x).
Proof. exact (fun_ext (fun z : B => @lem6178132 B y z op x)). Qed.
Lemma lem6178134 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6178135 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term558 B y op x) = (term568 B y op x).
Proof. exact (MK_COMB (@lem6178134 B) (@lem6178133 B y op x)). Qed.
Lemma lem6178136 {B : Type'} (y : B) (op : type1400 B) (x : B) : ((term557 B y op x) = (term558 B y op x)) = ((term551 B y op x) = (term568 B y op x)).
Proof. exact (MK_COMB (@lem6178129 B y op x) (@lem6178135 B y op x)). Qed.
Lemma lem6178137 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term551 B y op x) = (term568 B y op x).
Proof. exact (EQ_MP (@lem6178136 B y op x) (@lem6178121 B y op x)). Qed.
Lemma lem6178138 {B : Type'} (op : type1400 B) (x : B) : (term553 B op x) = (term569 B op x).
Proof. exact (fun_ext (fun y : B => @lem6178137 B y op x)). Qed.
Lemma lem6178139 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6178140 {B : Type'} (op : type1400 B) (x : B) : (term554 B op x) = (term570 B op x).
Proof. exact (MK_COMB (@lem6178139 B) (@lem6178138 B op x)). Qed.
Lemma lem6178141 {B : Type'} (op : type1400 B) (x : B) : (term533 B op x) = (term570 B op x).
Proof. exact (TRANS (@lem6178117 B op x) (@lem6178140 B op x)). Qed.
Lemma lem6178142 {B : Type'} (op : type1400 B) : (term535 B op) = (term571 B op).
Proof. exact (fun_ext (fun x : B => @lem6178141 B op x)). Qed.
Lemma lem6178143 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6178144 {B : Type'} (op : type1400 B) : (term536 B op) = (term572 B op).
Proof. exact (MK_COMB (@lem6178143 B) (@lem6178142 B op)). Qed.
Lemma lem6178145 {B : Type'} (op : type1400 B) : (term518 B op) = (term572 B op).
Proof. exact (TRANS (@lem6178090 B op) (@lem6178144 B op)). Qed.
Lemma lem6178146 {B : Type'} (op : type1400 B) : (term427 B op) = (term572 B op).
Proof. exact (TRANS (@lem6178063 B op) (@lem6178145 B op)). Qed.
Lemma lem6178147 {B : Type'} (op : type1400 B) : (term431 B op) = (term431 B op).
Proof. exact (eq_refl (term431 B op)). Qed.
Lemma lem6178148 {B : Type'} (op : type1400 B) : (term433 B op) = (term573 B op).
Proof. exact (MK_COMB (@lem6178147 B op) (@lem6178146 B op)). Qed.
Lemma lem6178150 {A : Type'} (P : Prop) (Q : A -> Prop) : (term555 A P Q) = (term556 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6178151 {B : Type'} (P : Prop) (Q : B -> Prop) : (term555 B P Q) = (term556 B P Q).
Proof. exact (@lem6178150 B P Q). Qed.
Lemma lem6178152 {B : Type'} (op : type1400 B) : (term574 B op) = (term575 B op).
Proof. exact (@lem6178151 B (@monoidal B op) (term571 B op)). Qed.
Lemma lem6178153 {B : Type'} (op : type1400 B) (x : B) : (term576 B op x) = (term570 B op x).
Proof. exact (eq_refl (term576 B op x)). Qed.
Lemma lem6178154 {B : Type'} (op : type1400 B) : (term577 B op) = (term571 B op).
Proof. exact (fun_ext (fun x : B => @lem6178153 B op x)). Qed.
Lemma lem6178155 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6178156 {B : Type'} (op : type1400 B) : (term578 B op) = (term572 B op).
Proof. exact (MK_COMB (@lem6178155 B) (@lem6178154 B op)). Qed.
Lemma lem6178157 {B : Type'} (op : type1400 B) : (term431 B op) = (term431 B op).
Proof. exact (eq_refl (term431 B op)). Qed.
Lemma lem6178158 {B : Type'} (op : type1400 B) : (term574 B op) = (term573 B op).
Proof. exact (MK_COMB (@lem6178157 B op) (@lem6178156 B op)). Qed.
Lemma lem6178159 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6178160 {B : Type'} (op : type1400 B) : (term579 B op) = (term580 B op).
Proof. exact (MK_COMB (@lem6178159) (@lem6178158 B op)). Qed.
Lemma lem6178161 {B : Type'} (op : type1400 B) (x : B) : (term576 B op x) = (term570 B op x).
Proof. exact (eq_refl (term576 B op x)). Qed.
Lemma lem6178162 {B : Type'} (op : type1400 B) : (term431 B op) = (term431 B op).
Proof. exact (eq_refl (term431 B op)). Qed.
Lemma lem6178163 {B : Type'} (op : type1400 B) (x : B) : (term581 B op x) = (term582 B op x).
Proof. exact (MK_COMB (@lem6178162 B op) (@lem6178161 B op x)). Qed.
Lemma lem6178164 {B : Type'} (op : type1400 B) : (term583 B op) = (term584 B op).
Proof. exact (fun_ext (fun x : B => @lem6178163 B op x)). Qed.
Lemma lem6178165 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6178166 {B : Type'} (op : type1400 B) : (term575 B op) = (term585 B op).
Proof. exact (MK_COMB (@lem6178165 B) (@lem6178164 B op)). Qed.
Lemma lem6178167 {B : Type'} (op : type1400 B) : ((term574 B op) = (term575 B op)) = ((term573 B op) = (term585 B op)).
Proof. exact (MK_COMB (@lem6178160 B op) (@lem6178166 B op)). Qed.
Lemma lem6178168 {B : Type'} (op : type1400 B) : (term573 B op) = (term585 B op).
Proof. exact (EQ_MP (@lem6178167 B op) (@lem6178152 B op)). Qed.
Lemma lem6178170 {A : Type'} (P : Prop) (Q : A -> Prop) : (term555 A P Q) = (term556 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6178171 {B : Type'} (P : Prop) (Q : B -> Prop) : (term555 B P Q) = (term556 B P Q).
Proof. exact (@lem6178170 B P Q). Qed.
Lemma lem6178172 {B : Type'} (op : type1400 B) (x : B) : (term586 B op x) = (term587 B op x).
Proof. exact (@lem6178171 B (@monoidal B op) (term569 B op x)). Qed.
Lemma lem6178173 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term588 B op x y) = (term568 B y op x).
Proof. exact (eq_refl (term588 B op x y)). Qed.
Lemma lem6178174 {B : Type'} (op : type1400 B) (x : B) : (term589 B op x) = (term569 B op x).
Proof. exact (fun_ext (fun y : B => @lem6178173 B y op x)). Qed.
Lemma lem6178175 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6178176 {B : Type'} (op : type1400 B) (x : B) : (term590 B op x) = (term570 B op x).
Proof. exact (MK_COMB (@lem6178175 B) (@lem6178174 B op x)). Qed.
Lemma lem6178177 {B : Type'} (op : type1400 B) : (term431 B op) = (term431 B op).
Proof. exact (eq_refl (term431 B op)). Qed.
Lemma lem6178178 {B : Type'} (op : type1400 B) (x : B) : (term586 B op x) = (term582 B op x).
Proof. exact (MK_COMB (@lem6178177 B op) (@lem6178176 B op x)). Qed.
Lemma lem6178179 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6178180 {B : Type'} (op : type1400 B) (x : B) : (term591 B op x) = (term592 B op x).
Proof. exact (MK_COMB (@lem6178179) (@lem6178178 B op x)). Qed.
Lemma lem6178181 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term588 B op x y) = (term568 B y op x).
Proof. exact (eq_refl (term588 B op x y)). Qed.
Lemma lem6178182 {B : Type'} (op : type1400 B) : (term431 B op) = (term431 B op).
Proof. exact (eq_refl (term431 B op)). Qed.
Lemma lem6178183 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term593 B op x y) = (term594 B y op x).
Proof. exact (MK_COMB (@lem6178182 B op) (@lem6178181 B y op x)). Qed.
Lemma lem6178184 {B : Type'} (op : type1400 B) (x : B) : (term595 B op x) = (term596 B op x).
Proof. exact (fun_ext (fun y : B => @lem6178183 B y op x)). Qed.
Lemma lem6178185 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6178186 {B : Type'} (op : type1400 B) (x : B) : (term587 B op x) = (term597 B op x).
Proof. exact (MK_COMB (@lem6178185 B) (@lem6178184 B op x)). Qed.
Lemma lem6178187 {B : Type'} (op : type1400 B) (x : B) : ((term586 B op x) = (term587 B op x)) = ((term582 B op x) = (term597 B op x)).
Proof. exact (MK_COMB (@lem6178180 B op x) (@lem6178186 B op x)). Qed.
Lemma lem6178188 {B : Type'} (op : type1400 B) (x : B) : (term582 B op x) = (term597 B op x).
Proof. exact (EQ_MP (@lem6178187 B op x) (@lem6178172 B op x)). Qed.
Lemma lem6178190 {A : Type'} (P : Prop) (Q : A -> Prop) : (term555 A P Q) = (term556 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6178191 {B : Type'} (P : Prop) (Q : B -> Prop) : (term555 B P Q) = (term556 B P Q).
Proof. exact (@lem6178190 B P Q). Qed.
Lemma lem6178192 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term598 B y op x) = (term599 B y op x).
Proof. exact (@lem6178191 B (@monoidal B op) (term567 B y op x)). Qed.
Lemma lem6178193 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term600 B y op x z) = (term565 B y z op x).
Proof. exact (eq_refl (term600 B y op x z)). Qed.
Lemma lem6178194 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term601 B y op x) = (term567 B y op x).
Proof. exact (fun_ext (fun z : B => @lem6178193 B y z op x)). Qed.
Lemma lem6178195 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6178196 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term602 B y op x) = (term568 B y op x).
Proof. exact (MK_COMB (@lem6178195 B) (@lem6178194 B y op x)). Qed.
Lemma lem6178197 {B : Type'} (op : type1400 B) : (term431 B op) = (term431 B op).
Proof. exact (eq_refl (term431 B op)). Qed.
Lemma lem6178198 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term598 B y op x) = (term594 B y op x).
Proof. exact (MK_COMB (@lem6178197 B op) (@lem6178196 B y op x)). Qed.
Lemma lem6178199 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6178200 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term603 B y op x) = (term604 B y op x).
Proof. exact (MK_COMB (@lem6178199) (@lem6178198 B y op x)). Qed.
Lemma lem6178201 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term600 B y op x z) = (term565 B y z op x).
Proof. exact (eq_refl (term600 B y op x z)). Qed.
Lemma lem6178202 {B : Type'} (op : type1400 B) : (term431 B op) = (term431 B op).
Proof. exact (eq_refl (term431 B op)). Qed.
Lemma lem6178203 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term605 B y op x z) = (term606 B y z op x).
Proof. exact (MK_COMB (@lem6178202 B op) (@lem6178201 B y z op x)). Qed.
Lemma lem6178204 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term607 B y op x) = (term608 B y op x).
Proof. exact (fun_ext (fun z : B => @lem6178203 B y z op x)). Qed.
Lemma lem6178205 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6178206 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term599 B y op x) = (term609 B y op x).
Proof. exact (MK_COMB (@lem6178205 B) (@lem6178204 B y op x)). Qed.
Lemma lem6178207 {B : Type'} (y : B) (op : type1400 B) (x : B) : ((term598 B y op x) = (term599 B y op x)) = ((term594 B y op x) = (term609 B y op x)).
Proof. exact (MK_COMB (@lem6178200 B y op x) (@lem6178206 B y op x)). Qed.
Lemma lem6178208 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term594 B y op x) = (term609 B y op x).
Proof. exact (EQ_MP (@lem6178207 B y op x) (@lem6178192 B y op x)). Qed.
Lemma lem6178209 {B : Type'} (op : type1400 B) (x : B) : (term596 B op x) = (term610 B op x).
Proof. exact (fun_ext (fun y : B => @lem6178208 B y op x)). Qed.
Lemma lem6178210 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6178211 {B : Type'} (op : type1400 B) (x : B) : (term597 B op x) = (term611 B op x).
Proof. exact (MK_COMB (@lem6178210 B) (@lem6178209 B op x)). Qed.
Lemma lem6178212 {B : Type'} (op : type1400 B) (x : B) : (term582 B op x) = (term611 B op x).
Proof. exact (TRANS (@lem6178188 B op x) (@lem6178211 B op x)). Qed.
Lemma lem6178213 {B : Type'} (op : type1400 B) : (term584 B op) = (term612 B op).
Proof. exact (fun_ext (fun x : B => @lem6178212 B op x)). Qed.
Lemma lem6178214 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6178215 {B : Type'} (op : type1400 B) : (term585 B op) = (term613 B op).
Proof. exact (MK_COMB (@lem6178214 B) (@lem6178213 B op)). Qed.
Lemma lem6178216 {B : Type'} (op : type1400 B) : (term573 B op) = (term613 B op).
Proof. exact (TRANS (@lem6178168 B op) (@lem6178215 B op)). Qed.
Lemma lem6178217 {B : Type'} (op : type1400 B) : (term433 B op) = (term613 B op).
Proof. exact (TRANS (@lem6178148 B op) (@lem6178216 B op)). Qed.
Lemma lem6178218 {B : Type'} : (term446 B) = (term614 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6178217 B op)). Qed.
Lemma lem6178219 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6178220 {B : Type'} : (term457 B) = (term615 B).
Proof. exact (MK_COMB (@lem6178219 B) (@lem6178218 B)). Qed.
Lemma lem6178222 {A B : Type'} (P : type1413 A B) : (term616 A B P) = (term617 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6178223 {B : Type'} (P : type401 B) : (term618 B P) = (term619 B P).
Proof. exact (@lem6178222 (type1400 B) B P). Qed.
Lemma lem6178224 {B : Type'} : (term620 B) = (term621 B).
Proof. exact (@lem6178223 B (term622 B)). Qed.
Lemma lem6178225 {B : Type'} (op : type1400 B) : (term623 B op) = (term612 B op).
Proof. exact (eq_refl (term623 B op)). Qed.
Lemma lem6178226 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6178227 {B : Type'} (op : type1400 B) (x : B) : (term624 B op x) = (term625 B op x).
Proof. exact (MK_COMB (@lem6178225 B op) (@lem6178226 B x)). Qed.
Lemma lem6178228 {B : Type'} (op : type1400 B) (x : B) : (term625 B op x) = (term611 B op x).
Proof. exact (eq_refl (term625 B op x)). Qed.
Lemma lem6178229 {B : Type'} (op : type1400 B) (x : B) : (term624 B op x) = (term611 B op x).
Proof. exact (TRANS (@lem6178227 B op x) (@lem6178228 B op x)). Qed.
Lemma lem6178230 {B : Type'} (op : type1400 B) : (term626 B op) = (term612 B op).
Proof. exact (fun_ext (fun x : B => @lem6178229 B op x)). Qed.
Lemma lem6178231 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6178232 {B : Type'} (op : type1400 B) : (term627 B op) = (term613 B op).
Proof. exact (MK_COMB (@lem6178231 B) (@lem6178230 B op)). Qed.
Lemma lem6178233 {B : Type'} : (term628 B) = (term614 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6178232 B op)). Qed.
Lemma lem6178234 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6178235 {B : Type'} : (term620 B) = (term615 B).
Proof. exact (MK_COMB (@lem6178234 B) (@lem6178233 B)). Qed.
Lemma lem6178236 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6178237 {B : Type'} : (term629 B) = (term630 B).
Proof. exact (MK_COMB (@lem6178236) (@lem6178235 B)). Qed.
Lemma lem6178238 {B : Type'} (op : type1400 B) : (term623 B op) = (term612 B op).
Proof. exact (eq_refl (term623 B op)). Qed.
Lemma lem6178239 {B : Type'} (x : type402 B) (op : type1400 B) : (x op) = (x op).
Proof. exact (eq_refl (x op)). Qed.
Lemma lem6178240 {B : Type'} (x : type402 B) (op : type1400 B) : (term631 B x op) = (term632 B x op).
Proof. exact (MK_COMB (@lem6178238 B op) (@lem6178239 B x op)). Qed.
Lemma lem6178241 {B : Type'} (x : type402 B) (op : type1400 B) : (term632 B x op) = (term633 B x op).
Proof. exact (eq_refl (term632 B x op)). Qed.
Lemma lem6178242 {B : Type'} (x : type402 B) (op : type1400 B) : (term631 B x op) = (term633 B x op).
Proof. exact (TRANS (@lem6178240 B x op) (@lem6178241 B x op)). Qed.
Lemma lem6178243 {B : Type'} (x : type402 B) : (term634 B x) = (term635 B x).
Proof. exact (fun_ext (fun op : type1400 B => @lem6178242 B x op)). Qed.
Lemma lem6178244 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6178245 {B : Type'} (x : type402 B) : (term636 B x) = (term637 B x).
Proof. exact (MK_COMB (@lem6178244 B) (@lem6178243 B x)). Qed.
Lemma lem6178246 {B : Type'} : (term638 B) = (term639 B).
Proof. exact (fun_ext (fun x : type402 B => @lem6178245 B x)). Qed.
Lemma lem6178247 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6178248 {B : Type'} : (term621 B) = (term640 B).
Proof. exact (MK_COMB (@lem6178247 B) (@lem6178246 B)). Qed.
Lemma lem6178249 {B : Type'} : ((term620 B) = (term621 B)) = ((term615 B) = (term640 B)).
Proof. exact (MK_COMB (@lem6178237 B) (@lem6178248 B)). Qed.
Lemma lem6178250 {B : Type'} : (term615 B) = (term640 B).
Proof. exact (EQ_MP (@lem6178249 B) (@lem6178224 B)). Qed.
Lemma lem6178252 {A B : Type'} (P : type1413 A B) : (term616 A B P) = (term617 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6178253 {B : Type'} (P : type401 B) : (term618 B P) = (term619 B P).
Proof. exact (@lem6178252 (type1400 B) B P). Qed.
Lemma lem6178254 {B : Type'} (x : type402 B) : (term641 B x) = (term642 B x).
Proof. exact (@lem6178253 B (term643 B x)). Qed.
Lemma lem6178255 {B : Type'} (x : type402 B) (op : type1400 B) : (term644 B x op) = (term645 B x op).
Proof. exact (eq_refl (term644 B x op)). Qed.
Lemma lem6178256 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem6178257 {B : Type'} (x : type402 B) (op : type1400 B) (y : B) : (term646 B x op y) = (term647 B x op y).
Proof. exact (MK_COMB (@lem6178255 B x op) (@lem6178256 B y)). Qed.
Lemma lem6178258 {B : Type'} (y : B) (x : type402 B) (op : type1400 B) : (term647 B x op y) = (term648 B y x op).
Proof. exact (eq_refl (term647 B x op y)). Qed.
Lemma lem6178259 {B : Type'} (y : B) (x : type402 B) (op : type1400 B) : (term646 B x op y) = (term648 B y x op).
Proof. exact (TRANS (@lem6178257 B x op y) (@lem6178258 B y x op)). Qed.
Lemma lem6178260 {B : Type'} (x : type402 B) (op : type1400 B) : (term649 B x op) = (term645 B x op).
Proof. exact (fun_ext (fun y : B => @lem6178259 B y x op)). Qed.
Lemma lem6178261 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6178262 {B : Type'} (x : type402 B) (op : type1400 B) : (term650 B x op) = (term633 B x op).
Proof. exact (MK_COMB (@lem6178261 B) (@lem6178260 B x op)). Qed.
Lemma lem6178263 {B : Type'} (x : type402 B) : (term651 B x) = (term635 B x).
Proof. exact (fun_ext (fun op : type1400 B => @lem6178262 B x op)). Qed.
Lemma lem6178264 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6178265 {B : Type'} (x : type402 B) : (term641 B x) = (term637 B x).
Proof. exact (MK_COMB (@lem6178264 B) (@lem6178263 B x)). Qed.
Lemma lem6178266 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6178267 {B : Type'} (x : type402 B) : (term652 B x) = (term653 B x).
Proof. exact (MK_COMB (@lem6178266) (@lem6178265 B x)). Qed.
Lemma lem6178268 {B : Type'} (x : type402 B) (op : type1400 B) : (term644 B x op) = (term645 B x op).
Proof. exact (eq_refl (term644 B x op)). Qed.
Lemma lem6178269 {B : Type'} (y : type402 B) (op : type1400 B) : (y op) = (y op).
Proof. exact (eq_refl (y op)). Qed.
Lemma lem6178270 {B : Type'} (x : type402 B) (y : type402 B) (op : type1400 B) : (term654 B x y op) = (term655 B x y op).
Proof. exact (MK_COMB (@lem6178268 B x op) (@lem6178269 B y op)). Qed.
Lemma lem6178271 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term655 B x y op) = (term656 B y x op).
Proof. exact (eq_refl (term655 B x y op)). Qed.
Lemma lem6178272 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term654 B x y op) = (term656 B y x op).
Proof. exact (TRANS (@lem6178270 B x y op) (@lem6178271 B y x op)). Qed.
Lemma lem6178273 {B : Type'} (y : type402 B) (x : type402 B) : (term657 B x y) = (term658 B y x).
Proof. exact (fun_ext (fun op : type1400 B => @lem6178272 B y x op)). Qed.
Lemma lem6178274 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6178275 {B : Type'} (y : type402 B) (x : type402 B) : (term659 B x y) = (term660 B y x).
Proof. exact (MK_COMB (@lem6178274 B) (@lem6178273 B y x)). Qed.
Lemma lem6178276 {B : Type'} (x : type402 B) : (term661 B x) = (term662 B x).
Proof. exact (fun_ext (fun y : type402 B => @lem6178275 B y x)). Qed.
Lemma lem6178277 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6178278 {B : Type'} (x : type402 B) : (term642 B x) = (term663 B x).
Proof. exact (MK_COMB (@lem6178277 B) (@lem6178276 B x)). Qed.
Lemma lem6178279 {B : Type'} (x : type402 B) : ((term641 B x) = (term642 B x)) = ((term637 B x) = (term663 B x)).
Proof. exact (MK_COMB (@lem6178267 B x) (@lem6178278 B x)). Qed.
Lemma lem6178280 {B : Type'} (x : type402 B) : (term637 B x) = (term663 B x).
Proof. exact (EQ_MP (@lem6178279 B x) (@lem6178254 B x)). Qed.
Lemma lem6178282 {A B : Type'} (P : type1413 A B) : (term616 A B P) = (term617 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6178283 {B : Type'} (P : type401 B) : (term618 B P) = (term619 B P).
Proof. exact (@lem6178282 (type1400 B) B P). Qed.
Lemma lem6178284 {B : Type'} (y : type402 B) (x : type402 B) : (term664 B y x) = (term665 B y x).
Proof. exact (@lem6178283 B (term666 B y x)). Qed.
Lemma lem6178285 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term667 B y x op) = (term668 B y x op).
Proof. exact (eq_refl (term667 B y x op)). Qed.
Lemma lem6178286 {B : Type'} (z : B) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem6178287 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) (z : B) : (term669 B y x op z) = (term670 B y x op z).
Proof. exact (MK_COMB (@lem6178285 B y x op) (@lem6178286 B z)). Qed.
Lemma lem6178288 {B : Type'} (y : type402 B) (z : B) (x : type402 B) (op : type1400 B) : (term670 B y x op z) = (term671 B y z x op).
Proof. exact (eq_refl (term670 B y x op z)). Qed.
Lemma lem6178289 {B : Type'} (y : type402 B) (z : B) (x : type402 B) (op : type1400 B) : (term669 B y x op z) = (term671 B y z x op).
Proof. exact (TRANS (@lem6178287 B y x op z) (@lem6178288 B y z x op)). Qed.
Lemma lem6178290 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term672 B y x op) = (term668 B y x op).
Proof. exact (fun_ext (fun z : B => @lem6178289 B y z x op)). Qed.
Lemma lem6178291 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6178292 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term673 B y x op) = (term656 B y x op).
Proof. exact (MK_COMB (@lem6178291 B) (@lem6178290 B y x op)). Qed.
Lemma lem6178293 {B : Type'} (y : type402 B) (x : type402 B) : (term674 B y x) = (term658 B y x).
Proof. exact (fun_ext (fun op : type1400 B => @lem6178292 B y x op)). Qed.
Lemma lem6178294 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6178295 {B : Type'} (y : type402 B) (x : type402 B) : (term664 B y x) = (term660 B y x).
Proof. exact (MK_COMB (@lem6178294 B) (@lem6178293 B y x)). Qed.
Lemma lem6178296 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6178297 {B : Type'} (y : type402 B) (x : type402 B) : (term675 B y x) = (term676 B y x).
Proof. exact (MK_COMB (@lem6178296) (@lem6178295 B y x)). Qed.
Lemma lem6178298 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term667 B y x op) = (term668 B y x op).
Proof. exact (eq_refl (term667 B y x op)). Qed.
Lemma lem6178299 {B : Type'} (z : type402 B) (op : type1400 B) : (z op) = (z op).
Proof. exact (eq_refl (z op)). Qed.
Lemma lem6178300 {B : Type'} (y : type402 B) (x : type402 B) (z : type402 B) (op : type1400 B) : (term677 B y x z op) = (term678 B y x z op).
Proof. exact (MK_COMB (@lem6178298 B y x op) (@lem6178299 B z op)). Qed.
Lemma lem6178301 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (op : type1400 B) : (term678 B y x z op) = (term679 B y z x op).
Proof. exact (eq_refl (term678 B y x z op)). Qed.
Lemma lem6178302 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (op : type1400 B) : (term677 B y x z op) = (term679 B y z x op).
Proof. exact (TRANS (@lem6178300 B y x z op) (@lem6178301 B y z x op)). Qed.
Lemma lem6178303 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) : (term680 B y x z) = (term681 B y z x).
Proof. exact (fun_ext (fun op : type1400 B => @lem6178302 B y z x op)). Qed.
Lemma lem6178304 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6178305 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) : (term682 B y x z) = (term683 B y z x).
Proof. exact (MK_COMB (@lem6178304 B) (@lem6178303 B y z x)). Qed.
Lemma lem6178306 {B : Type'} (y : type402 B) (x : type402 B) : (term684 B y x) = (term685 B y x).
Proof. exact (fun_ext (fun z : type402 B => @lem6178305 B y z x)). Qed.
Lemma lem6178307 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6178308 {B : Type'} (y : type402 B) (x : type402 B) : (term665 B y x) = (term686 B y x).
Proof. exact (MK_COMB (@lem6178307 B) (@lem6178306 B y x)). Qed.
Lemma lem6178309 {B : Type'} (y : type402 B) (x : type402 B) : ((term664 B y x) = (term665 B y x)) = ((term660 B y x) = (term686 B y x)).
Proof. exact (MK_COMB (@lem6178297 B y x) (@lem6178308 B y x)). Qed.
Lemma lem6178310 {B : Type'} (y : type402 B) (x : type402 B) : (term660 B y x) = (term686 B y x).
Proof. exact (EQ_MP (@lem6178309 B y x) (@lem6178284 B y x)). Qed.
Lemma lem6178311 {B : Type'} (x : type402 B) : (term662 B x) = (term687 B x).
Proof. exact (fun_ext (fun y : type402 B => @lem6178310 B y x)). Qed.
Lemma lem6178312 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6178313 {B : Type'} (x : type402 B) : (term663 B x) = (term688 B x).
Proof. exact (MK_COMB (@lem6178312 B) (@lem6178311 B x)). Qed.
Lemma lem6178314 {B : Type'} (x : type402 B) : (term637 B x) = (term688 B x).
Proof. exact (TRANS (@lem6178280 B x) (@lem6178313 B x)). Qed.
Lemma lem6178315 {B : Type'} : (term639 B) = (term689 B).
Proof. exact (fun_ext (fun x : type402 B => @lem6178314 B x)). Qed.
Lemma lem6178316 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6178317 {B : Type'} : (term640 B) = (term690 B).
Proof. exact (MK_COMB (@lem6178316 B) (@lem6178315 B)). Qed.
Lemma lem6178318 {B : Type'} : (term615 B) = (term690 B).
Proof. exact (TRANS (@lem6178250 B) (@lem6178317 B)). Qed.
Lemma lem6178319 {B : Type'} : (term457 B) = (term690 B).
Proof. exact (TRANS (@lem6178220 B) (@lem6178318 B)). Qed.
Lemma lem6178320 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6178321 {B : Type'} : (term459 B) = (term691 B).
Proof. exact (MK_COMB (@lem6178320) (@lem6178319 B)). Qed.
Lemma lem6178322 {B : Type'} : (term462 B) = (term462 B).
Proof. exact (eq_refl (term462 B)). Qed.
Lemma lem6178323 {B : Type'} : (term463 B) = (term692 B).
Proof. exact (MK_COMB (@lem6178321 B) (@lem6178322 B)). Qed.
Lemma lem6178325 {A : Type'} (P : A -> Prop) (Q : Prop) : (term693 A P Q) = (term694 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6178326 {B : Type'} (P : type82 B) (Q : Prop) : (term695 B P Q) = (term696 B P Q).
Proof. exact (@lem6178325 (type402 B) P Q). Qed.
Lemma lem6178327 {B : Type'} : (term697 B) = (term698 B).
Proof. exact (@lem6178326 B (term689 B) (term462 B)). Qed.
Lemma lem6178328 {B : Type'} (x : type402 B) : (term699 B x) = (term688 B x).
Proof. exact (eq_refl (term699 B x)). Qed.
Lemma lem6178329 {B : Type'} : (term700 B) = (term689 B).
Proof. exact (fun_ext (fun x : type402 B => @lem6178328 B x)). Qed.
Lemma lem6178330 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6178331 {B : Type'} : (term701 B) = (term690 B).
Proof. exact (MK_COMB (@lem6178330 B) (@lem6178329 B)). Qed.
Lemma lem6178332 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6178333 {B : Type'} : (term702 B) = (term691 B).
Proof. exact (MK_COMB (@lem6178332) (@lem6178331 B)). Qed.
Lemma lem6178334 {B : Type'} : (term462 B) = (term462 B).
Proof. exact (eq_refl (term462 B)). Qed.
Lemma lem6178335 {B : Type'} : (term697 B) = (term692 B).
Proof. exact (MK_COMB (@lem6178333 B) (@lem6178334 B)). Qed.
Lemma lem6178336 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6178337 {B : Type'} : (term703 B) = (term704 B).
Proof. exact (MK_COMB (@lem6178336) (@lem6178335 B)). Qed.
Lemma lem6178338 {B : Type'} (x : type402 B) : (term699 B x) = (term688 B x).
Proof. exact (eq_refl (term699 B x)). Qed.
Lemma lem6178339 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6178340 {B : Type'} (x : type402 B) : (term705 B x) = (term706 B x).
Proof. exact (MK_COMB (@lem6178339) (@lem6178338 B x)). Qed.
Lemma lem6178341 {B : Type'} : (term462 B) = (term462 B).
Proof. exact (eq_refl (term462 B)). Qed.
Lemma lem6178342 {B : Type'} (x : type402 B) : (term707 B x) = (term708 B x).
Proof. exact (MK_COMB (@lem6178340 B x) (@lem6178341 B)). Qed.
Lemma lem6178343 {B : Type'} : (term709 B) = (term710 B).
Proof. exact (fun_ext (fun x : type402 B => @lem6178342 B x)). Qed.
Lemma lem6178344 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6178345 {B : Type'} : (term698 B) = (term711 B).
Proof. exact (MK_COMB (@lem6178344 B) (@lem6178343 B)). Qed.
Lemma lem6178346 {B : Type'} : ((term697 B) = (term698 B)) = ((term692 B) = (term711 B)).
Proof. exact (MK_COMB (@lem6178337 B) (@lem6178345 B)). Qed.
Lemma lem6178347 {B : Type'} : (term692 B) = (term711 B).
Proof. exact (EQ_MP (@lem6178346 B) (@lem6178327 B)). Qed.
Lemma lem6178349 {A : Type'} (P : A -> Prop) (Q : Prop) : (term693 A P Q) = (term694 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6178350 {B : Type'} (P : type82 B) (Q : Prop) : (term695 B P Q) = (term696 B P Q).
Proof. exact (@lem6178349 (type402 B) P Q). Qed.
Lemma lem6178351 {B : Type'} (x : type402 B) : (term712 B x) = (term713 B x).
Proof. exact (@lem6178350 B (term687 B x) (term462 B)). Qed.
Lemma lem6178352 {B : Type'} (y : type402 B) (x : type402 B) : (term714 B x y) = (term686 B y x).
Proof. exact (eq_refl (term714 B x y)). Qed.
Lemma lem6178353 {B : Type'} (x : type402 B) : (term715 B x) = (term687 B x).
Proof. exact (fun_ext (fun y : type402 B => @lem6178352 B y x)). Qed.
Lemma lem6178354 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6178355 {B : Type'} (x : type402 B) : (term716 B x) = (term688 B x).
Proof. exact (MK_COMB (@lem6178354 B) (@lem6178353 B x)). Qed.
Lemma lem6178356 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6178357 {B : Type'} (x : type402 B) : (term717 B x) = (term706 B x).
Proof. exact (MK_COMB (@lem6178356) (@lem6178355 B x)). Qed.
Lemma lem6178358 {B : Type'} : (term462 B) = (term462 B).
Proof. exact (eq_refl (term462 B)). Qed.
Lemma lem6178359 {B : Type'} (x : type402 B) : (term712 B x) = (term708 B x).
Proof. exact (MK_COMB (@lem6178357 B x) (@lem6178358 B)). Qed.
Lemma lem6178360 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6178361 {B : Type'} (x : type402 B) : (term718 B x) = (term719 B x).
Proof. exact (MK_COMB (@lem6178360) (@lem6178359 B x)). Qed.
Lemma lem6178362 {B : Type'} (y : type402 B) (x : type402 B) : (term714 B x y) = (term686 B y x).
Proof. exact (eq_refl (term714 B x y)). Qed.
Lemma lem6178363 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6178364 {B : Type'} (y : type402 B) (x : type402 B) : (term720 B x y) = (term721 B y x).
Proof. exact (MK_COMB (@lem6178363) (@lem6178362 B y x)). Qed.
Lemma lem6178365 {B : Type'} : (term462 B) = (term462 B).
Proof. exact (eq_refl (term462 B)). Qed.
Lemma lem6178366 {B : Type'} (y : type402 B) (x : type402 B) : (term722 B x y) = (term723 B y x).
Proof. exact (MK_COMB (@lem6178364 B y x) (@lem6178365 B)). Qed.
Lemma lem6178367 {B : Type'} (x : type402 B) : (term724 B x) = (term725 B x).
Proof. exact (fun_ext (fun y : type402 B => @lem6178366 B y x)). Qed.
Lemma lem6178368 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6178369 {B : Type'} (x : type402 B) : (term713 B x) = (term726 B x).
Proof. exact (MK_COMB (@lem6178368 B) (@lem6178367 B x)). Qed.
Lemma lem6178370 {B : Type'} (x : type402 B) : ((term712 B x) = (term713 B x)) = ((term708 B x) = (term726 B x)).
Proof. exact (MK_COMB (@lem6178361 B x) (@lem6178369 B x)). Qed.
Lemma lem6178371 {B : Type'} (x : type402 B) : (term708 B x) = (term726 B x).
Proof. exact (EQ_MP (@lem6178370 B x) (@lem6178351 B x)). Qed.
Lemma lem6178373 {A : Type'} (P : A -> Prop) (Q : Prop) : (term693 A P Q) = (term694 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6178374 {B : Type'} (P : type82 B) (Q : Prop) : (term695 B P Q) = (term696 B P Q).
Proof. exact (@lem6178373 (type402 B) P Q). Qed.
Lemma lem6178375 {B : Type'} (y : type402 B) (x : type402 B) : (term727 B y x) = (term728 B y x).
Proof. exact (@lem6178374 B (term685 B y x) (term462 B)). Qed.
Lemma lem6178376 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) : (term729 B y x z) = (term683 B y z x).
Proof. exact (eq_refl (term729 B y x z)). Qed.
Lemma lem6178377 {B : Type'} (y : type402 B) (x : type402 B) : (term730 B y x) = (term685 B y x).
Proof. exact (fun_ext (fun z : type402 B => @lem6178376 B y z x)). Qed.
Lemma lem6178378 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6178379 {B : Type'} (y : type402 B) (x : type402 B) : (term731 B y x) = (term686 B y x).
Proof. exact (MK_COMB (@lem6178378 B) (@lem6178377 B y x)). Qed.
Lemma lem6178380 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6178381 {B : Type'} (y : type402 B) (x : type402 B) : (term732 B y x) = (term721 B y x).
Proof. exact (MK_COMB (@lem6178380) (@lem6178379 B y x)). Qed.
Lemma lem6178382 {B : Type'} : (term462 B) = (term462 B).
Proof. exact (eq_refl (term462 B)). Qed.
Lemma lem6178383 {B : Type'} (y : type402 B) (x : type402 B) : (term727 B y x) = (term723 B y x).
Proof. exact (MK_COMB (@lem6178381 B y x) (@lem6178382 B)). Qed.
Lemma lem6178384 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6178385 {B : Type'} (y : type402 B) (x : type402 B) : (term733 B y x) = (term734 B y x).
Proof. exact (MK_COMB (@lem6178384) (@lem6178383 B y x)). Qed.
Lemma lem6178386 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) : (term729 B y x z) = (term683 B y z x).
Proof. exact (eq_refl (term729 B y x z)). Qed.
Lemma lem6178387 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6178388 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) : (term735 B y x z) = (term736 B y z x).
Proof. exact (MK_COMB (@lem6178387) (@lem6178386 B y z x)). Qed.
Lemma lem6178389 {B : Type'} : (term462 B) = (term462 B).
Proof. exact (eq_refl (term462 B)). Qed.
Lemma lem6178390 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) : (term737 B y x z) = (term738 B y z x).
Proof. exact (MK_COMB (@lem6178388 B y z x) (@lem6178389 B)). Qed.
Lemma lem6178391 {B : Type'} (y : type402 B) (x : type402 B) : (term739 B y x) = (term740 B y x).
Proof. exact (fun_ext (fun z : type402 B => @lem6178390 B y z x)). Qed.
Lemma lem6178392 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6178393 {B : Type'} (y : type402 B) (x : type402 B) : (term728 B y x) = (term741 B y x).
Proof. exact (MK_COMB (@lem6178392 B) (@lem6178391 B y x)). Qed.
Lemma lem6178394 {B : Type'} (y : type402 B) (x : type402 B) : ((term727 B y x) = (term728 B y x)) = ((term723 B y x) = (term741 B y x)).
Proof. exact (MK_COMB (@lem6178385 B y x) (@lem6178393 B y x)). Qed.
Lemma lem6178395 {B : Type'} (y : type402 B) (x : type402 B) : (term723 B y x) = (term741 B y x).
Proof. exact (EQ_MP (@lem6178394 B y x) (@lem6178375 B y x)). Qed.
Lemma lem6178396 {B : Type'} (x : type402 B) : (term725 B x) = (term742 B x).
Proof. exact (fun_ext (fun y : type402 B => @lem6178395 B y x)). Qed.
Lemma lem6178397 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6178398 {B : Type'} (x : type402 B) : (term726 B x) = (term743 B x).
Proof. exact (MK_COMB (@lem6178397 B) (@lem6178396 B x)). Qed.
Lemma lem6178399 {B : Type'} (x : type402 B) : (term708 B x) = (term743 B x).
Proof. exact (TRANS (@lem6178371 B x) (@lem6178398 B x)). Qed.
Lemma lem6178400 {B : Type'} : (term710 B) = (term744 B).
Proof. exact (fun_ext (fun x : type402 B => @lem6178399 B x)). Qed.
Lemma lem6178401 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem6178402 {B : Type'} : (term711 B) = (term745 B).
Proof. exact (MK_COMB (@lem6178401 B) (@lem6178400 B)). Qed.
Lemma lem6178403 {B : Type'} : (term692 B) = (term745 B).
Proof. exact (TRANS (@lem6178347 B) (@lem6178402 B)). Qed.
Lemma lem6178404 {B : Type'} : (term463 B) = (term745 B).
Proof. exact (TRANS (@lem6178323 B) (@lem6178403 B)). Qed.
Lemma lem6178405 {B : Type'} : (term439 B) = (term745 B).
Proof. exact (TRANS (@lem6177854 B) (@lem6178404 B)). Qed.
Lemma lem6178406 {B : Type'} : (term257 B) = (term745 B).
Proof. exact (TRANS (@lem6177827 B) (@lem6178405 B)). Qed.
Lemma lem6178407 {B : Type'} (h1 : term257 B) : term745 B.
Proof. exact (EQ_MP (@lem6178406 B) (@lem6177477 B h1)). Qed.
Lemma lem6178408 {B : Type'} (x : type402 B) (h1 : term743 B x) : term743 B x.
Proof. exact (h1). Qed.
Lemma lem6178409 {B : Type'} (y : type402 B) (x : type402 B) (h1 : term741 B y x) : term741 B y x.
Proof. exact (h1). Qed.
Lemma lem6178411 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1306 A B f s g x' op) : term1306 A B f s g x' op.
Proof. exact (h1). Qed.
Lemma lem6178911 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6178912 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6178917 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6178918 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6178917 A B f x). Qed.
Lemma lem6178920 {A B : Type'} (g : A -> B) (x' : A) : (g x') = (@I (A -> B) g x').
Proof. exact (@lem6178918 A B g x'). Qed.
Lemma lem6178925 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6178926 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6178925 (type1400 B) B f x). Qed.
Lemma lem6178928 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem6178926 B (@neutral B) op). Qed.
Lemma lem6178929 {A B : Type'} (g : A -> B) (x' : A) : (term851 A B g x') = (term852 A B g x').
Proof. exact (MK_COMB (@lem6178912 B) (@lem6178920 A B g x')). Qed.
Lemma lem6178930 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) : ((g x') = (@neutral B op)) = ((@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (MK_COMB (@lem6178929 A B g x') (@lem6178928 B op)). Qed.
Lemma lem6178931 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) : (term315 A B g x' op) = (term853 A B g x' op).
Proof. exact (MK_COMB (@lem6178911) (@lem6178930 A B g x' op)). Qed.
Lemma lem6178932 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6178937 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6178938 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6178937 A B f x). Qed.
Lemma lem6178940 {A B : Type'} (g : A -> B) (x' : A) : (g x') = (@I (A -> B) g x').
Proof. exact (@lem6178938 A B g x'). Qed.
Lemma lem6178945 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6178946 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6178945 (type1400 B) B f x). Qed.
Lemma lem6178948 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem6178946 B (@neutral B) op). Qed.
Lemma lem6178949 {A B : Type'} (g : A -> B) (x' : A) : (term851 A B g x') = (term852 A B g x').
Proof. exact (MK_COMB (@lem6178932 B) (@lem6178940 A B g x')). Qed.
Lemma lem6178950 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) : ((g x') = (@neutral B op)) = ((@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (MK_COMB (@lem6178949 A B g x') (@lem6178948 B op)). Qed.
Lemma lem6178951 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6178958 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6178959 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6178958 A (type686 A) f x). Qed.
Lemma lem6178960 {A : Type'} (x' : A) : (@IN A x') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x').
Proof. exact (@lem6178959 A (@IN A) x'). Qed.
Lemma lem6178961 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6178962 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s).
Proof. exact (MK_COMB (@lem6178960 A x') (@lem6178961 A s)). Qed.
Lemma lem6178964 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6178965 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6178964 (A -> Prop) Prop f x). Qed.
Lemma lem6178966 {A : Type'} (x' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s) = (term846 A x' s).
Proof. exact (@lem6178965 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x') s). Qed.
Lemma lem6178968 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (term846 A x' s).
Proof. exact (TRANS (@lem6178962 A x' s) (@lem6178966 A x' s)). Qed.
Lemma lem6178969 {A : Type'} (x' : A) (s : A -> Prop) : (term847 A x' s) = (term848 A x' s).
Proof. exact (MK_COMB (@lem6178951) (@lem6178968 A x' s)). Qed.
Lemma lem6178970 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6178971 {A : Type'} (x' : A) (s : A -> Prop) : (term312 A x' s) = (term849 A x' s).
Proof. exact (MK_COMB (@lem6178970) (@lem6178969 A x' s)). Qed.
Lemma lem6178972 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) : (term314 A B s g x' op) = (term862 A B s g x' op).
Proof. exact (MK_COMB (@lem6178971 A x' s) (@lem6178950 A B g x' op)). Qed.
Lemma lem6178973 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6178974 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6178979 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6178980 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6178979 A B f x). Qed.
Lemma lem6178982 {A B : Type'} (g : A -> B) (x' : A) : (g x') = (@I (A -> B) g x').
Proof. exact (@lem6178980 A B g x'). Qed.
Lemma lem6178987 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6178988 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6178987 (type1400 B) B f x). Qed.
Lemma lem6178990 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem6178988 B (@neutral B) op). Qed.
Lemma lem6178991 {A B : Type'} (g : A -> B) (x' : A) : (term851 A B g x') = (term852 A B g x').
Proof. exact (MK_COMB (@lem6178974 B) (@lem6178982 A B g x')). Qed.
Lemma lem6178992 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) : ((g x') = (@neutral B op)) = ((@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (MK_COMB (@lem6178991 A B g x') (@lem6178990 B op)). Qed.
Lemma lem6178993 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) : (term315 A B g x' op) = (term853 A B g x' op).
Proof. exact (MK_COMB (@lem6178973) (@lem6178992 A B g x' op)). Qed.
Lemma lem6179000 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6179001 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6179000 A (type686 A) f x). Qed.
Lemma lem6179002 {A : Type'} (x' : A) : (@IN A x') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x').
Proof. exact (@lem6179001 A (@IN A) x'). Qed.
Lemma lem6179003 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6179004 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s).
Proof. exact (MK_COMB (@lem6179002 A x') (@lem6179003 A s)). Qed.
Lemma lem6179006 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6179007 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6179006 (A -> Prop) Prop f x). Qed.
Lemma lem6179008 {A : Type'} (x' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s) = (term846 A x' s).
Proof. exact (@lem6179007 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x') s). Qed.
Lemma lem6179010 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (term846 A x' s).
Proof. exact (TRANS (@lem6179004 A x' s) (@lem6179008 A x' s)). Qed.
Lemma lem6179011 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6179012 {A : Type'} (x' : A) (s : A -> Prop) : (term132 A x' s) = (term854 A x' s).
Proof. exact (MK_COMB (@lem6179011) (@lem6179010 A x' s)). Qed.
Lemma lem6179013 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) : (term168 A B s g x' op) = (term855 A B s g x' op).
Proof. exact (MK_COMB (@lem6179012 A x' s) (@lem6178993 A B g x' op)). Qed.
Lemma lem6179014 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6179015 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6179020 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6179021 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6179020 A B f x). Qed.
Lemma lem6179023 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (@I (A -> B) f x').
Proof. exact (@lem6179021 A B f x'). Qed.
Lemma lem6179028 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6179029 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6179028 (type1400 B) B f x). Qed.
Lemma lem6179031 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem6179029 B (@neutral B) op). Qed.
Lemma lem6179032 {A B : Type'} (f : A -> B) (x' : A) : (term851 A B f x') = (term852 A B f x').
Proof. exact (MK_COMB (@lem6179015 B) (@lem6179023 A B f x')). Qed.
Lemma lem6179033 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : ((f x') = (@neutral B op)) = ((@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (MK_COMB (@lem6179032 A B f x') (@lem6179031 B op)). Qed.
Lemma lem6179034 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : (term315 A B f x' op) = (term853 A B f x' op).
Proof. exact (MK_COMB (@lem6179014) (@lem6179033 A B f x' op)). Qed.
Lemma lem6179041 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6179042 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6179041 A (type686 A) f x). Qed.
Lemma lem6179043 {A : Type'} (x' : A) : (@IN A x') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x').
Proof. exact (@lem6179042 A (@IN A) x'). Qed.
Lemma lem6179044 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6179045 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s).
Proof. exact (MK_COMB (@lem6179043 A x') (@lem6179044 A s)). Qed.
Lemma lem6179047 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6179048 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6179047 (A -> Prop) Prop f x). Qed.
Lemma lem6179049 {A : Type'} (x' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s) = (term846 A x' s).
Proof. exact (@lem6179048 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x') s). Qed.
Lemma lem6179051 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (term846 A x' s).
Proof. exact (TRANS (@lem6179045 A x' s) (@lem6179049 A x' s)). Qed.
Lemma lem6179052 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6179053 {A : Type'} (x' : A) (s : A -> Prop) : (term132 A x' s) = (term854 A x' s).
Proof. exact (MK_COMB (@lem6179052) (@lem6179051 A x' s)). Qed.
Lemma lem6179054 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) : (term168 A B s f x' op) = (term855 A B s f x' op).
Proof. exact (MK_COMB (@lem6179053 A x' s) (@lem6179034 A B f x' op)). Qed.
Lemma lem6179055 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6179056 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) : (term183 A B s f x' op) = (term856 A B s f x' op).
Proof. exact (MK_COMB (@lem6179055) (@lem6179054 A B s f x' op)). Qed.
Lemma lem6179057 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) : (term184 A B f s g x' op) = (term857 A B f s g x' op).
Proof. exact (MK_COMB (@lem6179056 A B s f x' op) (@lem6179013 A B s g x' op)). Qed.
Lemma lem6179058 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6179059 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) : (term193 A B f s g x' op) = (term858 A B f s g x' op).
Proof. exact (MK_COMB (@lem6179058) (@lem6179057 A B f s g x' op)). Qed.
Lemma lem6179060 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) : (term1275 A B f s g x' op) = (term1310 A B f s g x' op).
Proof. exact (MK_COMB (@lem6179059 A B f s g x' op) (@lem6178972 A B s g x' op)). Qed.
Lemma lem6179061 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6179062 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) : (term1277 A B f s g x' op) = (term1311 A B f s g x' op).
Proof. exact (MK_COMB (@lem6179061) (@lem6179060 A B f s g x' op)). Qed.
Lemma lem6179063 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) : (term1279 A B f s g x' op) = (term1312 A B f s g x' op).
Proof. exact (MK_COMB (@lem6179062 A B f s g x' op) (@lem6178931 A B g x' op)). Qed.
Lemma lem6179064 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6179069 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6179070 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6179069 A B f x). Qed.
Lemma lem6179072 {A B : Type'} (g : A -> B) (x' : A) : (g x') = (@I (A -> B) g x').
Proof. exact (@lem6179070 A B g x'). Qed.
Lemma lem6179077 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6179078 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6179077 (type1400 B) B f x). Qed.
Lemma lem6179080 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem6179078 B (@neutral B) op). Qed.
Lemma lem6179081 {A B : Type'} (g : A -> B) (x' : A) : (term851 A B g x') = (term852 A B g x').
Proof. exact (MK_COMB (@lem6179064 B) (@lem6179072 A B g x')). Qed.
Lemma lem6179082 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) : ((g x') = (@neutral B op)) = ((@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (MK_COMB (@lem6179081 A B g x') (@lem6179080 B op)). Qed.
Lemma lem6179083 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6179090 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6179091 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6179090 A (type686 A) f x). Qed.
Lemma lem6179092 {A : Type'} (x' : A) : (@IN A x') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x').
Proof. exact (@lem6179091 A (@IN A) x'). Qed.
Lemma lem6179093 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6179094 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s).
Proof. exact (MK_COMB (@lem6179092 A x') (@lem6179093 A s)). Qed.
Lemma lem6179096 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6179097 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6179096 (A -> Prop) Prop f x). Qed.
Lemma lem6179098 {A : Type'} (x' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s) = (term846 A x' s).
Proof. exact (@lem6179097 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x') s). Qed.
Lemma lem6179100 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (term846 A x' s).
Proof. exact (TRANS (@lem6179094 A x' s) (@lem6179098 A x' s)). Qed.
Lemma lem6179101 {A : Type'} (x' : A) (s : A -> Prop) : (term847 A x' s) = (term848 A x' s).
Proof. exact (MK_COMB (@lem6179083) (@lem6179100 A x' s)). Qed.
Lemma lem6179102 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6179103 {A : Type'} (x' : A) (s : A -> Prop) : (term312 A x' s) = (term849 A x' s).
Proof. exact (MK_COMB (@lem6179102) (@lem6179101 A x' s)). Qed.
Lemma lem6179104 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) : (term314 A B s g x' op) = (term862 A B s g x' op).
Proof. exact (MK_COMB (@lem6179103 A x' s) (@lem6179082 A B g x' op)). Qed.
Lemma lem6179105 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6179110 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6179111 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6179110 A B f x). Qed.
Lemma lem6179113 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (@I (A -> B) f x').
Proof. exact (@lem6179111 A B f x'). Qed.
Lemma lem6179118 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6179119 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6179118 (type1400 B) B f x). Qed.
Lemma lem6179121 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem6179119 B (@neutral B) op). Qed.
Lemma lem6179122 {A B : Type'} (f : A -> B) (x' : A) : (term851 A B f x') = (term852 A B f x').
Proof. exact (MK_COMB (@lem6179105 B) (@lem6179113 A B f x')). Qed.
Lemma lem6179123 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : ((f x') = (@neutral B op)) = ((@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (MK_COMB (@lem6179122 A B f x') (@lem6179121 B op)). Qed.
Lemma lem6179124 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6179131 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6179132 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6179131 A (type686 A) f x). Qed.
Lemma lem6179133 {A : Type'} (x' : A) : (@IN A x') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x').
Proof. exact (@lem6179132 A (@IN A) x'). Qed.
Lemma lem6179134 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6179135 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s).
Proof. exact (MK_COMB (@lem6179133 A x') (@lem6179134 A s)). Qed.
Lemma lem6179137 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6179138 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6179137 (A -> Prop) Prop f x). Qed.
Lemma lem6179139 {A : Type'} (x' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s) = (term846 A x' s).
Proof. exact (@lem6179138 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x') s). Qed.
Lemma lem6179141 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (term846 A x' s).
Proof. exact (TRANS (@lem6179135 A x' s) (@lem6179139 A x' s)). Qed.
Lemma lem6179142 {A : Type'} (x' : A) (s : A -> Prop) : (term847 A x' s) = (term848 A x' s).
Proof. exact (MK_COMB (@lem6179124) (@lem6179141 A x' s)). Qed.
Lemma lem6179143 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6179144 {A : Type'} (x' : A) (s : A -> Prop) : (term312 A x' s) = (term849 A x' s).
Proof. exact (MK_COMB (@lem6179143) (@lem6179142 A x' s)). Qed.
Lemma lem6179145 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) : (term314 A B s f x' op) = (term862 A B s f x' op).
Proof. exact (MK_COMB (@lem6179144 A x' s) (@lem6179123 A B f x' op)). Qed.
Lemma lem6179146 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6179147 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) : (term317 A B s f x' op) = (term863 A B s f x' op).
Proof. exact (MK_COMB (@lem6179146) (@lem6179145 A B s f x' op)). Qed.
Lemma lem6179148 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) : (term319 A B f s g x' op) = (term864 A B f s g x' op).
Proof. exact (MK_COMB (@lem6179147 A B s f x' op) (@lem6179104 A B s g x' op)). Qed.
Lemma lem6179149 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6179150 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6179155 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6179156 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6179155 A B f x). Qed.
Lemma lem6179158 {A B : Type'} (g : A -> B) (x' : A) : (g x') = (@I (A -> B) g x').
Proof. exact (@lem6179156 A B g x'). Qed.
Lemma lem6179163 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6179164 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem6179163 (type1400 B) B f x). Qed.
Lemma lem6179166 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem6179164 B (@neutral B) op). Qed.
Lemma lem6179167 {A B : Type'} (g : A -> B) (x' : A) : (term851 A B g x') = (term852 A B g x').
Proof. exact (MK_COMB (@lem6179150 B) (@lem6179158 A B g x')). Qed.
Lemma lem6179168 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) : ((g x') = (@neutral B op)) = ((@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (MK_COMB (@lem6179167 A B g x') (@lem6179166 B op)). Qed.
Lemma lem6179169 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) : (term315 A B g x' op) = (term853 A B g x' op).
Proof. exact (MK_COMB (@lem6179149) (@lem6179168 A B g x' op)). Qed.
Lemma lem6179176 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6179177 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6179176 A (type686 A) f x). Qed.
Lemma lem6179178 {A : Type'} (x' : A) : (@IN A x') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x').
Proof. exact (@lem6179177 A (@IN A) x'). Qed.
Lemma lem6179179 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6179180 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s).
Proof. exact (MK_COMB (@lem6179178 A x') (@lem6179179 A s)). Qed.
Lemma lem6179182 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6179183 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6179182 (A -> Prop) Prop f x). Qed.
Lemma lem6179184 {A : Type'} (x' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s) = (term846 A x' s).
Proof. exact (@lem6179183 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x') s). Qed.
Lemma lem6179186 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (term846 A x' s).
Proof. exact (TRANS (@lem6179180 A x' s) (@lem6179184 A x' s)). Qed.
Lemma lem6179187 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6179188 {A : Type'} (x' : A) (s : A -> Prop) : (term132 A x' s) = (term854 A x' s).
Proof. exact (MK_COMB (@lem6179187) (@lem6179186 A x' s)). Qed.
Lemma lem6179189 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) : (term168 A B s g x' op) = (term855 A B s g x' op).
Proof. exact (MK_COMB (@lem6179188 A x' s) (@lem6179169 A B g x' op)). Qed.
Lemma lem6179190 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6179191 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) : (term1177 A B s g x' op) = (term1226 A B s g x' op).
Proof. exact (MK_COMB (@lem6179190) (@lem6179189 A B s g x' op)). Qed.
Lemma lem6179192 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) : (term1266 A B f s g x' op) = (term1313 A B f s g x' op).
Proof. exact (MK_COMB (@lem6179191 A B s g x' op) (@lem6179148 A B f s g x' op)). Qed.
Lemma lem6179193 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6179194 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) : (term1304 A B f s g x' op) = (term1314 A B f s g x' op).
Proof. exact (MK_COMB (@lem6179193) (@lem6179192 A B f s g x' op)). Qed.
Lemma lem6179195 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) : (term1306 A B f s g x' op) = (term1315 A B f s g x' op).
Proof. exact (MK_COMB (@lem6179194 A B f s g x' op) (@lem6179063 A B f s g x' op)). Qed.
Lemma lem6179196 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1306 A B f s g x' op) : term1315 A B f s g x' op.
Proof. exact (EQ_MP (@lem6179195 A B f s g x' op) (@lem6178411 A B f s g x' op h1)). Qed.
Lemma lem6179199 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1313 A B f s g x' op) : term1313 A B f s g x' op.
Proof. exact (h1). Qed.
Lemma lem6179200 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1312 A B f s g x' op) : term1312 A B f s g x' op.
Proof. exact (h1). Qed.
Lemma lem6179201 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1313 A B f s g x' op) : term864 A B f s g x' op.
Proof. exact (proj2 (@lem6179199 A B f s g x' op h1)). Qed.
Lemma lem6179202 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1313 A B f s g x' op) : term855 A B s g x' op.
Proof. exact (proj1 (@lem6179199 A B f s g x' op h1)). Qed.
Lemma lem6179203 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1313 A B f s g x' op) : term862 A B s g x' op.
Proof. exact (proj2 (@lem6179201 A B f s g x' op h1)). Qed.
Lemma lem6179204 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1313 A B f s g x' op) : term862 A B s f x' op.
Proof. exact (proj1 (@lem6179201 A B f s g x' op h1)). Qed.
Lemma lem6179214 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1312 A B f s g x' op) : term1310 A B f s g x' op.
Proof. exact (proj1 (@lem6179200 A B f s g x' op h1)). Qed.
Lemma lem6179215 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1312 A B f s g x' op) : term862 A B s g x' op.
Proof. exact (proj2 (@lem6179214 A B f s g x' op h1)). Qed.
Lemma lem6179216 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1312 A B f s g x' op) : term857 A B f s g x' op.
Proof. exact (proj1 (@lem6179214 A B f s g x' op h1)). Qed.
Lemma lem6179219 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s f x' op) : term855 A B s f x' op.
Proof. exact (h1). Qed.
Lemma lem6179220 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s g x' op) : term855 A B s g x' op.
Proof. exact (h1). Qed.
Lemma lem6179226 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s g x' op) : term855 A B s g x' op.
Proof. exact (h1). Qed.
Lemma lem6179562 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6179566 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6179898 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6180238 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6180570 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (h1). Qed.
Lemma lem6180902 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6181238 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6181574 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (h1). Qed.
Lemma lem6181910 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (h1). Qed.
Lemma lem6182096 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6182098 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6182142 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6182190 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6182232 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1313 A B f s g x' op) : term853 A B g x' op.
Proof. exact (proj2 (@lem6179202 A B f s g x' op h1)). Qed.
Lemma lem6182234 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (h1). Qed.
Lemma lem6182278 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6182324 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term848 A x' s.
Proof. exact (h1). Qed.
Lemma lem6182368 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1312 A B f s g x' op) : term853 A B g x' op.
Proof. exact (proj2 (@lem6179200 A B f s g x' op h1)). Qed.
Lemma lem6182370 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (h1). Qed.
Lemma lem6182416 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (h1). Qed.
Lemma lem6182420 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s g x' op) : term853 A B g x' op.
Proof. exact (proj2 (@lem6179226 A B s g x' op h1)). Qed.
Lemma lem6182624 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1313 A B f s g x' op) : term846 A x' s.
Proof. exact (proj1 (@lem6179202 A B f s g x' op h1)). Qed.
Lemma lem6182625 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1313 A B f s g x' op) : term1042 A x' s.
Proof. exact (fun h0 : term848 A x' s => @lem6182624 A B f s g x' op h1). Qed.
Lemma lem6182627 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6182628 {A : Type'} (x' : A) (s : A -> Prop) : (term1042 A x' s) = (term846 A x' s).
Proof. exact (@lem6182627 (term846 A x' s)). Qed.
Lemma lem6182629 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1313 A B f s g x' op) : term846 A x' s.
Proof. exact (EQ_MP (@lem6182628 A x' s) (@lem6182625 A B f s g x' op h1)). Qed.
Lemma lem6182632 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6182634 {A : Type'} (x' : A) (s : A -> Prop) : (term848 A x' s) = (term1044 A x' s).
Proof. exact (@lem6182632 (term846 A x' s)). Qed.
Lemma lem6182637 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term1044 A x' s.
Proof. exact (EQ_MP (@lem6182634 A x' s) (@lem6182096 A x' s h1)). Qed.
Lemma lem6182640 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : False.
Proof. exact (@lem6182637 A x' s h1 (@lem6182629 A B f s g x' op h2)). Qed.
Lemma lem6182641 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : term1045.
Proof. exact (fun h0 : ~ False => @lem6182640 A B f s g x' op h1 h2). Qed.
Lemma lem6182643 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6182644 : term1045 = False.
Proof. exact (@lem6182643 False). Qed.
Lemma lem6182645 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6182644) (@lem6182641 A B f s g x' op h1 h2)). Qed.
Lemma lem6182831 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1313 A B f s g x' op) : term846 A x' s.
Proof. exact (proj1 (@lem6179202 A B f s g x' op h1)). Qed.
Lemma lem6182832 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1313 A B f s g x' op) : term1042 A x' s.
Proof. exact (fun h0 : term848 A x' s => @lem6182831 A B f s g x' op h1). Qed.
Lemma lem6182834 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6182835 {A : Type'} (x' : A) (s : A -> Prop) : (term1042 A x' s) = (term846 A x' s).
Proof. exact (@lem6182834 (term846 A x' s)). Qed.
Lemma lem6182836 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1313 A B f s g x' op) : term846 A x' s.
Proof. exact (EQ_MP (@lem6182835 A x' s) (@lem6182832 A B f s g x' op h1)). Qed.
Lemma lem6182839 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6182841 {A : Type'} (x' : A) (s : A -> Prop) : (term848 A x' s) = (term1044 A x' s).
Proof. exact (@lem6182839 (term846 A x' s)). Qed.
Lemma lem6182844 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term1044 A x' s.
Proof. exact (EQ_MP (@lem6182841 A x' s) (@lem6182142 A x' s h1)). Qed.
Lemma lem6182847 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : False.
Proof. exact (@lem6182844 A x' s h1 (@lem6182836 A B f s g x' op h2)). Qed.
Lemma lem6182848 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : term1045.
Proof. exact (fun h0 : ~ False => @lem6182847 A B f s g x' op h1 h2). Qed.
Lemma lem6182850 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6182851 : term1045 = False.
Proof. exact (@lem6182850 False). Qed.
Lemma lem6182852 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6182851) (@lem6182848 A B f s g x' op h1 h2)). Qed.
Lemma lem6183038 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1313 A B f s g x' op) : term846 A x' s.
Proof. exact (proj1 (@lem6179202 A B f s g x' op h1)). Qed.
Lemma lem6183039 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1313 A B f s g x' op) : term1042 A x' s.
Proof. exact (fun h0 : term848 A x' s => @lem6183038 A B f s g x' op h1). Qed.
Lemma lem6183041 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6183042 {A : Type'} (x' : A) (s : A -> Prop) : (term1042 A x' s) = (term846 A x' s).
Proof. exact (@lem6183041 (term846 A x' s)). Qed.
Lemma lem6183043 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1313 A B f s g x' op) : term846 A x' s.
Proof. exact (EQ_MP (@lem6183042 A x' s) (@lem6183039 A B f s g x' op h1)). Qed.
Lemma lem6183046 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6183048 {A : Type'} (x' : A) (s : A -> Prop) : (term848 A x' s) = (term1044 A x' s).
Proof. exact (@lem6183046 (term846 A x' s)). Qed.
Lemma lem6183051 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term1044 A x' s.
Proof. exact (EQ_MP (@lem6183048 A x' s) (@lem6182190 A x' s h1)). Qed.
Lemma lem6183054 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : False.
Proof. exact (@lem6183051 A x' s h1 (@lem6183043 A B f s g x' op h2)). Qed.
Lemma lem6183055 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : term1045.
Proof. exact (fun h0 : ~ False => @lem6183054 A B f s g x' op h1 h2). Qed.
Lemma lem6183057 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6183058 : term1045 = False.
Proof. exact (@lem6183057 False). Qed.
Lemma lem6183059 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6183058) (@lem6183055 A B f s g x' op h1 h2)). Qed.
Lemma lem6183245 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (h1). Qed.
Lemma lem6183246 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : term1056 A B g x' op.
Proof. exact (fun h0 : term853 A B g x' op => @lem6183245 A B g x' op h1). Qed.
Lemma lem6183248 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6183249 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) : (term1056 A B g x' op) = ((@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (@lem6183248 ((@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op))). Qed.
Lemma lem6183250 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (EQ_MP (@lem6183249 A B g x' op) (@lem6183246 A B g x' op h1)). Qed.
Lemma lem6183253 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6183255 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) : (term853 A B g x' op) = (term1230 A B g x' op).
Proof. exact (@lem6183253 ((@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op))). Qed.
Lemma lem6183258 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1313 A B f s g x' op) : term1230 A B g x' op.
Proof. exact (EQ_MP (@lem6183255 A B g x' op) (@lem6182232 A B f s g x' op h1)). Qed.
Lemma lem6183261 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1313 A B f s g x' op) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (@lem6183258 A B f s g x' op h1 (@lem6183250 A B g x' op h2)). Qed.
Lemma lem6183262 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1313 A B f s g x' op) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : term1045.
Proof. exact (fun h0 : ~ False => @lem6183261 A B f s g x' op h1 h2). Qed.
Lemma lem6183264 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6183265 : term1045 = False.
Proof. exact (@lem6183264 False). Qed.
Lemma lem6183266 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1313 A B f s g x' op) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6183265) (@lem6183262 A B f s g x' op h1 h2)). Qed.
Lemma lem6183452 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s f x' op) : term846 A x' s.
Proof. exact (proj1 (@lem6179219 A B s f x' op h1)). Qed.
Lemma lem6183453 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s f x' op) : term1042 A x' s.
Proof. exact (fun h0 : term848 A x' s => @lem6183452 A B s f x' op h1). Qed.
Lemma lem6183455 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6183456 {A : Type'} (x' : A) (s : A -> Prop) : (term1042 A x' s) = (term846 A x' s).
Proof. exact (@lem6183455 (term846 A x' s)). Qed.
Lemma lem6183457 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s f x' op) : term846 A x' s.
Proof. exact (EQ_MP (@lem6183456 A x' s) (@lem6183453 A B s f x' op h1)). Qed.
Lemma lem6183460 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6183462 {A : Type'} (x' : A) (s : A -> Prop) : (term848 A x' s) = (term1044 A x' s).
Proof. exact (@lem6183460 (term846 A x' s)). Qed.
Lemma lem6183465 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term1044 A x' s.
Proof. exact (EQ_MP (@lem6183462 A x' s) (@lem6182278 A x' s h1)). Qed.
Lemma lem6183468 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s f x' op) : False.
Proof. exact (@lem6183465 A x' s h1 (@lem6183457 A B s f x' op h2)). Qed.
Lemma lem6183469 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s f x' op) : term1045.
Proof. exact (fun h0 : ~ False => @lem6183468 A B s f x' op h1 h2). Qed.
Lemma lem6183471 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6183472 : term1045 = False.
Proof. exact (@lem6183471 False). Qed.
Lemma lem6183473 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s f x' op) : False.
Proof. exact (EQ_MP (@lem6183472) (@lem6183469 A B s f x' op h1 h2)). Qed.
Lemma lem6183659 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s g x' op) : term846 A x' s.
Proof. exact (proj1 (@lem6179220 A B s g x' op h1)). Qed.
Lemma lem6183660 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s g x' op) : term1042 A x' s.
Proof. exact (fun h0 : term848 A x' s => @lem6183659 A B s g x' op h1). Qed.
Lemma lem6183662 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6183663 {A : Type'} (x' : A) (s : A -> Prop) : (term1042 A x' s) = (term846 A x' s).
Proof. exact (@lem6183662 (term846 A x' s)). Qed.
Lemma lem6183664 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s g x' op) : term846 A x' s.
Proof. exact (EQ_MP (@lem6183663 A x' s) (@lem6183660 A B s g x' op h1)). Qed.
Lemma lem6183667 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6183669 {A : Type'} (x' : A) (s : A -> Prop) : (term848 A x' s) = (term1044 A x' s).
Proof. exact (@lem6183667 (term846 A x' s)). Qed.
Lemma lem6183672 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term848 A x' s) : term1044 A x' s.
Proof. exact (EQ_MP (@lem6183669 A x' s) (@lem6182324 A x' s h1)). Qed.
Lemma lem6183675 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s g x' op) : False.
Proof. exact (@lem6183672 A x' s h1 (@lem6183664 A B s g x' op h2)). Qed.
Lemma lem6183676 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s g x' op) : term1045.
Proof. exact (fun h0 : ~ False => @lem6183675 A B s g x' op h1 h2). Qed.
Lemma lem6183678 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6183679 : term1045 = False.
Proof. exact (@lem6183678 False). Qed.
Lemma lem6183680 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s g x' op) : False.
Proof. exact (EQ_MP (@lem6183679) (@lem6183676 A B s g x' op h1 h2)). Qed.
Lemma lem6183866 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (h1). Qed.
Lemma lem6183867 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : term1056 A B g x' op.
Proof. exact (fun h0 : term853 A B g x' op => @lem6183866 A B g x' op h1). Qed.
Lemma lem6183869 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6183870 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) : (term1056 A B g x' op) = ((@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (@lem6183869 ((@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op))). Qed.
Lemma lem6183871 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (EQ_MP (@lem6183870 A B g x' op) (@lem6183867 A B g x' op h1)). Qed.
Lemma lem6183874 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6183876 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) : (term853 A B g x' op) = (term1230 A B g x' op).
Proof. exact (@lem6183874 ((@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op))). Qed.
Lemma lem6183879 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1312 A B f s g x' op) : term1230 A B g x' op.
Proof. exact (EQ_MP (@lem6183876 A B g x' op) (@lem6182368 A B f s g x' op h1)). Qed.
Lemma lem6183882 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1312 A B f s g x' op) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (@lem6183879 A B f s g x' op h1 (@lem6183871 A B g x' op h2)). Qed.
Lemma lem6183883 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1312 A B f s g x' op) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : term1045.
Proof. exact (fun h0 : ~ False => @lem6183882 A B f s g x' op h1 h2). Qed.
Lemma lem6183885 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6183886 : term1045 = False.
Proof. exact (@lem6183885 False). Qed.
Lemma lem6183887 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1312 A B f s g x' op) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6183886) (@lem6183883 A B f s g x' op h1 h2)). Qed.
Lemma lem6184073 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (h1). Qed.
Lemma lem6184074 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : term1056 A B g x' op.
Proof. exact (fun h0 : term853 A B g x' op => @lem6184073 A B g x' op h1). Qed.
Lemma lem6184076 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6184077 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) : (term1056 A B g x' op) = ((@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (@lem6184076 ((@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op))). Qed.
Lemma lem6184078 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) (h1 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (EQ_MP (@lem6184077 A B g x' op) (@lem6184074 A B g x' op h1)). Qed.
Lemma lem6184081 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6184083 {A B : Type'} (g : A -> B) (x' : A) (op : type1400 B) : (term853 A B g x' op) = (term1230 A B g x' op).
Proof. exact (@lem6184081 ((@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op))). Qed.
Lemma lem6184086 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s g x' op) : term1230 A B g x' op.
Proof. exact (EQ_MP (@lem6184083 A B g x' op) (@lem6182420 A B s g x' op h1)). Qed.
Lemma lem6184089 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s g x' op) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (@lem6184086 A B s g x' op h1 (@lem6184078 A B g x' op h2)). Qed.
Lemma lem6184090 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s g x' op) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : term1045.
Proof. exact (fun h0 : ~ False => @lem6184089 A B s g x' op h1 h2). Qed.
Lemma lem6184092 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6184093 : term1045 = False.
Proof. exact (@lem6184092 False). Qed.
Lemma lem6184094 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s g x' op) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6184093) (@lem6184090 A B s g x' op h1 h2)). Qed.
Lemma lem6184095 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s g x' op) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : ((@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) = False.
Proof. exact (prop_ext (fun h3 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6184094 A B s g x' op h1 h2) (fun h3 : False => @lem6182416 A B g x' op h2)). Qed.
Lemma lem6184096 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s g x' op) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6184095 A B s g x' op h1 h2) (@lem6182416 A B g x' op h2)). Qed.
Lemma lem6184097 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1312 A B f s g x' op) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : ((@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) = False.
Proof. exact (prop_ext (fun h3 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6183887 A B f s g x' op h1 h2) (fun h3 : False => @lem6182370 A B g x' op h2)). Qed.
Lemma lem6184098 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1312 A B f s g x' op) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6184097 A B f s g x' op h1 h2) (@lem6182370 A B g x' op h2)). Qed.
Lemma lem6184099 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6183680 A B s g x' op h1 h2) (fun h3 : False => @lem6182324 A x' s h1)). Qed.
Lemma lem6184100 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s g x' op) : False.
Proof. exact (EQ_MP (@lem6184099 A B s g x' op h1 h2) (@lem6182324 A x' s h1)). Qed.
Lemma lem6184101 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s f x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6183473 A B s f x' op h1 h2) (fun h3 : False => @lem6182278 A x' s h1)). Qed.
Lemma lem6184102 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s f x' op) : False.
Proof. exact (EQ_MP (@lem6184101 A B s f x' op h1 h2) (@lem6182278 A x' s h1)). Qed.
Lemma lem6184103 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1313 A B f s g x' op) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : ((@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) = False.
Proof. exact (prop_ext (fun h3 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6183266 A B f s g x' op h1 h2) (fun h3 : False => @lem6182234 A B g x' op h2)). Qed.
Lemma lem6184104 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1313 A B f s g x' op) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6184103 A B f s g x' op h1 h2) (@lem6182234 A B g x' op h2)). Qed.
Lemma lem6184105 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6183059 A B f s g x' op h1 h2) (fun h3 : False => @lem6182190 A x' s h1)). Qed.
Lemma lem6184106 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6184105 A B f s g x' op h1 h2) (@lem6182190 A x' s h1)). Qed.
Lemma lem6184107 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6182852 A B f s g x' op h1 h2) (fun h3 : False => @lem6182142 A x' s h1)). Qed.
Lemma lem6184108 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6184107 A B f s g x' op h1 h2) (@lem6182142 A x' s h1)). Qed.
Lemma lem6184109 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6182645 A B f s g x' op h1 h2) (fun h3 : False => @lem6182098 A x' s h1)). Qed.
Lemma lem6184110 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6184109 A B f s g x' op h1 h2) (@lem6182098 A x' s h1)). Qed.
Lemma lem6184111 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6184110 A B f s g x' op h1 h2) (fun h3 : False => @lem6182096 A x' s h1)). Qed.
Lemma lem6184112 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6184111 A B f s g x' op h1 h2) (@lem6182096 A x' s h1)). Qed.
Lemma lem6184113 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s g x' op) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : ((@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) = False.
Proof. exact (prop_ext (fun h3 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6184096 A B s g x' op h1 h2) (fun h3 : False => @lem6181910 A B g x' op h2)). Qed.
Lemma lem6184114 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s g x' op) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6184113 A B s g x' op h1 h2) (@lem6181910 A B g x' op h2)). Qed.
Lemma lem6184115 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1312 A B f s g x' op) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : ((@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) = False.
Proof. exact (prop_ext (fun h3 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6184098 A B f s g x' op h1 h2) (fun h3 : False => @lem6181574 A B g x' op h2)). Qed.
Lemma lem6184116 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1312 A B f s g x' op) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6184115 A B f s g x' op h1 h2) (@lem6181574 A B g x' op h2)). Qed.
Lemma lem6184117 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6184100 A B s g x' op h1 h2) (fun h3 : False => @lem6181238 A x' s h1)). Qed.
Lemma lem6184118 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s g x' op) : False.
Proof. exact (EQ_MP (@lem6184117 A B s g x' op h1 h2) (@lem6181238 A x' s h1)). Qed.
Lemma lem6184119 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s f x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6184102 A B s f x' op h1 h2) (fun h3 : False => @lem6180902 A x' s h1)). Qed.
Lemma lem6184120 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s f x' op) : False.
Proof. exact (EQ_MP (@lem6184119 A B s f x' op h1 h2) (@lem6180902 A x' s h1)). Qed.
Lemma lem6184121 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1313 A B f s g x' op) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : ((@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) = False.
Proof. exact (prop_ext (fun h3 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6184104 A B f s g x' op h1 h2) (fun h3 : False => @lem6180570 A B g x' op h2)). Qed.
Lemma lem6184122 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1313 A B f s g x' op) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6184121 A B f s g x' op h1 h2) (@lem6180570 A B g x' op h2)). Qed.
Lemma lem6184123 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6184106 A B f s g x' op h1 h2) (fun h3 : False => @lem6180238 A x' s h1)). Qed.
Lemma lem6184124 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6184123 A B f s g x' op h1 h2) (@lem6180238 A x' s h1)). Qed.
Lemma lem6184125 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6184108 A B f s g x' op h1 h2) (fun h3 : False => @lem6179898 A x' s h1)). Qed.
Lemma lem6184126 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6184125 A B f s g x' op h1 h2) (@lem6179898 A x' s h1)). Qed.
Lemma lem6184127 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6184112 A B f s g x' op h1 h2) (fun h3 : False => @lem6179566 A x' s h1)). Qed.
Lemma lem6184128 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6184127 A B f s g x' op h1 h2) (@lem6179566 A x' s h1)). Qed.
Lemma lem6184129 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6184128 A B f s g x' op h1 h2) (fun h3 : False => @lem6179562 A x' s h1)). Qed.
Lemma lem6184130 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6184129 A B f s g x' op h1 h2) (@lem6179562 A x' s h1)). Qed.
Lemma lem6184131 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s g x' op) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : ((@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) = False.
Proof. exact (prop_ext (fun h3 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6184114 A B s g x' op h1 h2) (fun h3 : False => @lem6181910 A B g x' op h2)). Qed.
Lemma lem6184132 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term855 A B s g x' op) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6184131 A B s g x' op h1 h2) (@lem6181910 A B g x' op h2)). Qed.
Lemma lem6184133 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1312 A B f s g x' op) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : ((@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) = False.
Proof. exact (prop_ext (fun h3 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6184116 A B f s g x' op h1 h2) (fun h3 : False => @lem6181574 A B g x' op h2)). Qed.
Lemma lem6184134 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1312 A B f s g x' op) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6184133 A B f s g x' op h1 h2) (@lem6181574 A B g x' op h2)). Qed.
Lemma lem6184135 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6184118 A B s g x' op h1 h2) (fun h3 : False => @lem6181238 A x' s h1)). Qed.
Lemma lem6184136 {A B : Type'} (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s g x' op) : False.
Proof. exact (EQ_MP (@lem6184135 A B s g x' op h1 h2) (@lem6181238 A x' s h1)). Qed.
Lemma lem6184137 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s f x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6184120 A B s f x' op h1 h2) (fun h3 : False => @lem6180902 A x' s h1)). Qed.
Lemma lem6184138 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term855 A B s f x' op) : False.
Proof. exact (EQ_MP (@lem6184137 A B s f x' op h1 h2) (@lem6180902 A x' s h1)). Qed.
Lemma lem6184139 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1313 A B f s g x' op) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : ((@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) = False.
Proof. exact (prop_ext (fun h3 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6184122 A B f s g x' op h1 h2) (fun h3 : False => @lem6180570 A B g x' op h2)). Qed.
Lemma lem6184140 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1313 A B f s g x' op) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (EQ_MP (@lem6184139 A B f s g x' op h1 h2) (@lem6180570 A B g x' op h2)). Qed.
Lemma lem6184141 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6184124 A B f s g x' op h1 h2) (fun h3 : False => @lem6180238 A x' s h1)). Qed.
Lemma lem6184142 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6184141 A B f s g x' op h1 h2) (@lem6180238 A x' s h1)). Qed.
Lemma lem6184143 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6184126 A B f s g x' op h1 h2) (fun h3 : False => @lem6179898 A x' s h1)). Qed.
Lemma lem6184144 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6184143 A B f s g x' op h1 h2) (@lem6179898 A x' s h1)). Qed.
Lemma lem6184145 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6184130 A B f s g x' op h1 h2) (fun h3 : False => @lem6179566 A x' s h1)). Qed.
Lemma lem6184146 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6184145 A B f s g x' op h1 h2) (@lem6179566 A x' s h1)). Qed.
Lemma lem6184147 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : (term848 A x' s) = False.
Proof. exact (prop_ext (fun h3 : term848 A x' s => @lem6184146 A B f s g x' op h1 h2) (fun h3 : False => @lem6179562 A x' s h1)). Qed.
Lemma lem6184148 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : False.
Proof. exact (EQ_MP (@lem6184147 A B f s g x' op h1 h2) (@lem6179562 A x' s h1)). Qed.
Lemma lem6184149 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1312 A B f s g x' op) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (or_elim (@lem6179216 A B f s g x' op h1) (fun h0 : term855 A B s f x' op => @lem6184134 A B f s g x' op h1 h2) (fun h0 : term855 A B s g x' op => @lem6184132 A B s g x' op h0 h2)). Qed.
Lemma lem6184150 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1312 A B f s g x' op) : False.
Proof. exact (or_elim (@lem6179216 A B f s g x' op h2) (fun h0 : term855 A B s f x' op => @lem6184138 A B s f x' op h1 h0) (fun h0 : term855 A B s g x' op => @lem6184136 A B s g x' op h1 h0)). Qed.
Lemma lem6184151 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1312 A B f s g x' op) : False.
Proof. exact (or_elim (@lem6179215 A B f s g x' op h1) (fun h0 : term848 A x' s => @lem6184150 A B f s g x' op h0 h1) (fun h0 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6184149 A B f s g x' op h1 h0)). Qed.
Lemma lem6184152 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1313 A B f s g x' op) (h2 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op)) : False.
Proof. exact (or_elim (@lem6179204 A B f s g x' op h1) (fun h0 : term848 A x' s => @lem6184142 A B f s g x' op h0 h1) (fun h0 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6184140 A B f s g x' op h1 h2)). Qed.
Lemma lem6184153 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term848 A x' s) (h2 : term1313 A B f s g x' op) : False.
Proof. exact (or_elim (@lem6179204 A B f s g x' op h2) (fun h0 : term848 A x' s => @lem6184148 A B f s g x' op h1 h2) (fun h0 : (@I (A -> B) f x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6184144 A B f s g x' op h1 h2)). Qed.
Lemma lem6184154 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1313 A B f s g x' op) : False.
Proof. exact (or_elim (@lem6179203 A B f s g x' op h1) (fun h0 : term848 A x' s => @lem6184153 A B f s g x' op h0 h1) (fun h0 : (@I (A -> B) g x') = (@I ((B -> B -> B) -> B) (@neutral B) op) => @lem6184152 A B f s g x' op h1 h0)). Qed.
Lemma lem6184155 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x' : A) (op : type1400 B) (h1 : term1306 A B f s g x' op) : False.
Proof. exact (or_elim (@lem6179196 A B f s g x' op h1) (fun h0 : term1313 A B f s g x' op => @lem6184154 A B f s g x' op h0) (fun h0 : term1312 A B f s g x' op => @lem6184151 A B f s g x' op h0)). Qed.
Lemma lem6184156 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : term1236 A B f s g op) : False.
Proof. exact (ex_elim (@lem6177711 A B f s g op h1) (fun x' : A => fun h0 : term1308 A B f s g op x' => @lem6184155 A B f s g x' op h0)). Qed.
Lemma lem6184157 {A B : Type'} (y : type402 B) (x : type402 B) (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : term741 B y x) (h2 : term1236 A B f s g op) : False.
Proof. exact (ex_elim (@lem6178409 B y x h1) (fun z : type402 B => fun h0 : term740 B y x z => @lem6184156 A B f s g op h2)). Qed.
Lemma lem6184158 {A B : Type'} (x : type402 B) (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : term743 B x) (h2 : term1236 A B f s g op) : False.
Proof. exact (ex_elim (@lem6178408 B x h1) (fun y : type402 B => fun h0 : term742 B x y => @lem6184157 A B y x f s g op h0 h2)). Qed.
Lemma lem6184159 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : term257 B) (h2 : term1236 A B f s g op) : False.
Proof. exact (ex_elim (@lem6178407 B h1) (fun x : type402 B => fun h0 : term744 B x => @lem6184158 A B x f s g op h0 h2)). Qed.
Lemma lem6184160 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : term1236 A B f s g op) : term262 B.
Proof. exact (fun h0 : term257 B => @lem6184159 A B f s g op h0 h1). Qed.
Lemma lem6184161 {B : Type'} : (term262 B) = (term263 B).
Proof. exact (@lem69 (term257 B)). Qed.
Lemma lem6184162 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : term1236 A B f s g op) : term263 B.
Proof. exact (EQ_MP (@lem6184161 B) (@lem6184160 A B f s g op h1)). Qed.
Lemma lem6184163 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : term1243 A B f s g op.
Proof. exact (fun h0 : term1236 A B f s g op => @lem6184162 A B f s g op h0). Qed.
Lemma lem6184164 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : term1245 A B f s g op.
Proof. exact (fun h0 : term58 A B op g s => @lem6184163 A B f s g op). Qed.
Lemma lem6184165 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : term1247 A B f s g op.
Proof. exact (fun h0 : term58 A B op f s => @lem6184164 A B f s g op). Qed.
Lemma lem6184166 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : term1248 A B f s g op.
Proof. exact (fun h0 : @monoidal B op => @lem6184165 A B f s g op). Qed.
Lemma lem6184171 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) : term1252 A B s g op.
Proof. exact (fun f : A -> B => @lem6184166 A B f s g op). Qed.
Lemma lem6184176 {A B : Type'} (g : A -> B) (op : type1400 B) : term1256 A B g op.
Proof. exact (fun s : A -> Prop => @lem6184171 A B s g op). Qed.
Lemma lem6184181 {A B : Type'} (op : type1400 B) : term1260 A B op.
Proof. exact (fun g : A -> B => @lem6184176 A B g op). Qed.
Lemma lem6184186 {A B : Type'} : term1264 A B.
Proof. exact (fun op : type1400 B => @lem6184181 A B op). Qed.
Lemma lem6184187 {A B : Type'} : term1263 A B.
Proof. exact (EQ_MP (@lem6177472 A B) (@lem6184186 A B)). Qed.
Lemma lem6184188 {A B : Type'} (op : type1400 B) : term1316 A B op.
Proof. exact (@lem6184187 A B op). Qed.
Lemma lem6184189 {A B : Type'} (op : type1400 B) : (term1316 A B op) = (term1259 A B op).
Proof. exact (eq_refl (term1316 A B op)). Qed.
Lemma lem6184190 {A B : Type'} (op : type1400 B) : term1259 A B op.
Proof. exact (EQ_MP (@lem6184189 A B op) (@lem6184188 A B op)). Qed.
Lemma lem6184191 {A B : Type'} (op : type1400 B) (g : A -> B) : term1317 A B op g.
Proof. exact (@lem6184190 A B op g). Qed.
Lemma lem6184192 {A B : Type'} (g : A -> B) (op : type1400 B) : (term1317 A B op g) = (term1255 A B g op).
Proof. exact (eq_refl (term1317 A B op g)). Qed.
Lemma lem6184193 {A B : Type'} (g : A -> B) (op : type1400 B) : term1255 A B g op.
Proof. exact (EQ_MP (@lem6184192 A B g op) (@lem6184191 A B op g)). Qed.
Lemma lem6184194 {A B : Type'} (g : A -> B) (op : type1400 B) (s : A -> Prop) : term1318 A B g op s.
Proof. exact (@lem6184193 A B g op s). Qed.
Lemma lem6184195 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1318 A B g op s) = (term1251 A B s g op).
Proof. exact (eq_refl (term1318 A B g op s)). Qed.
Lemma lem6184196 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) : term1251 A B s g op.
Proof. exact (EQ_MP (@lem6184195 A B s g op) (@lem6184194 A B g op s)). Qed.
Lemma lem6184197 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) (f : A -> B) : term1319 A B s g op f.
Proof. exact (@lem6184196 A B s g op f). Qed.
Lemma lem6184198 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term1319 A B s g op f) = (term1237 A B f s g op).
Proof. exact (eq_refl (term1319 A B s g op f)). Qed.
Lemma lem6184199 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : term1237 A B f s g op.
Proof. exact (EQ_MP (@lem6184198 A B f s g op) (@lem6184197 A B s g op f)). Qed.
Lemma lem6184201 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : term1237 A B f s g op.
Proof. exact (@lem6177081 A B f s g op (@lem6184199 A B f s g op)). Qed.
Lemma lem6184202 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term1246 A B f s g op.
Proof. exact (@lem6184201 A B f s g op (@lem6160869 B op h1)). Qed.
Lemma lem6184203 {A B : Type'} (g : A -> B) (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : @monoidal B op) : term1244 A B f s g op.
Proof. exact (@lem6184202 A B f s g op h2 (@lem6160872 A B op f s h1)). Qed.
Lemma lem6184204 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : term1242 A B f s g op.
Proof. exact (@lem6184203 A B g f s op h1 h3 (@lem6160871 A B op g s h2)). Qed.
Lemma lem6184205 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) (h4 : term1236 A B f s g op) : term262 B.
Proof. exact (@lem6184204 A B f g s op h1 h2 h3 (@lem6177062 A B f s g op h4)). Qed.
Lemma lem6184206 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) (h4 : term1236 A B f s g op) : False.
Proof. exact (@lem6184205 A B f s g op h1 h2 h3 h4 (@lem6177063 B)). Qed.
Lemma lem6184207 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) (h4 : term1236 A B f s g op) : (term1236 A B f s g op) = False.
Proof. exact (prop_ext (fun h5 : term1236 A B f s g op => @lem6184206 A B f s g op h1 h2 h3 h4) (fun h5 : False => @lem6177062 A B f s g op h4)). Qed.
Lemma lem6184208 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) (h4 : term1236 A B f s g op) : False.
Proof. exact (EQ_MP (@lem6184207 A B f s g op h1 h2 h3 h4) (@lem6177062 A B f s g op h4)). Qed.
Lemma lem6184209 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : term1235 A B f s g op.
Proof. exact (fun h0 : term1236 A B f s g op => @lem6184208 A B f s g op h1 h2 h3 h0). Qed.
Lemma lem6184210 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : term253 A B f s g op.
Proof. exact (EQ_MP (@lem6177061 A B f s g op) (@lem6184209 A B f g s op h1 h2 h3)). Qed.
Lemma lem6184211 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : term252 A B f s g op.
Proof. exact (EQ_MP (@lem6162195 A B f s g op) (@lem6184210 A B f g s op h1 h2 h3)). Qed.
Lemma lem6184212 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : term231 A B g s f op.
Proof. exact (EQ_MP (@lem6161866 A B g s f op) (@lem6177057 A B f g s op h1 h2 h3)). Qed.
Lemma lem6184213 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : term206 A B s f g op.
Proof. exact (EQ_MP (@lem6161539 A B s f g op) (@lem6169904 A B f g s op h1 h2 h3)). Qed.
Lemma lem6184214 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : (term1320 A B f op s g) = (term59 A B op s g).
Proof. exact (@lem6161112 A B f s g op h3 (@lem6184211 A B f g s op h1 h2 h3)). Qed.
Lemma lem6184215 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : (term1321 A B op g s f) = (term59 A B op s f).
Proof. exact (@lem6161070 A B g s f op h3 (@lem6184212 A B f g s op h1 h2 h3)). Qed.
Lemma lem6184216 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : (term70 A B s op f g) = (term61 A B s op f g).
Proof. exact (@lem6161028 A B s f g op h3 (@lem6184213 A B f g s op h1 h2 h3)). Qed.
Lemma lem6184217 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : (term1322 A B op g s f) = (term66 A B op s f).
Proof. exact (MK_COMB (@lem6160986 B op) (@lem6184215 A B f g s op h1 h2 h3)). Qed.
Lemma lem6184218 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : (term96 A B f op s g) = (term68 A B f op s g).
Proof. exact (MK_COMB (@lem6184217 A B f g s op h1 h2 h3) (@lem6184214 A B f g s op h1 h2 h3)). Qed.
Lemma lem6184219 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : (term70 A B s op f g) = (term68 A B f op s g).
Proof. exact (EQ_MP (@lem6160985 A B f g s op h1 h2 h3) (@lem6184218 A B f g s op h1 h2 h3)). Qed.
Lemma lem6184220 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : (term61 A B s op f g) = (term70 A B s op f g).
Proof. exact (EQ_MP (@lem6160902 A B s op f g) (@lem6184216 A B f g s op h1 h2 h3)). Qed.
Lemma lem6184221 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : term1323 A B f op s g.
Proof. exact (conj (@lem6184220 A B f g s op h1 h2 h3) (@lem6184219 A B f g s op h1 h2 h3)). Qed.
Lemma lem6184222 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : term1324 A B f op s g.
Proof. exact (ex_intro (term1325 A B f op s g) (term70 A B s op f g) (@lem6184221 A B f g s op h1 h2 h3)). Qed.
Lemma lem6184223 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : (term61 A B s op f g) = (term68 A B f op s g).
Proof. exact (@lem6160896 A B f op s g (@lem6184222 A B f g s op h1 h2 h3)). Qed.
Lemma lem6184224 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : (term60 A B s op f g) = (term67 A B f op s g).
Proof. exact (EQ_MP (@lem6160892 A B f op s g) (@lem6184223 A B f g s op h1 h2 h3)). Qed.
Lemma lem6184225 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (s : A -> Prop) (h1 : term57 A B f op g s) : term58 A B op g s.
Proof. exact (proj2 (@lem6160870 A B f op g s h1)). Qed.
Lemma lem6184226 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (s : A -> Prop) (h1 : term57 A B f op g s) : term58 A B op f s.
Proof. exact (proj1 (@lem6160870 A B f op g s h1)). Qed.
Lemma lem6184227 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : (term58 A B op g s) = ((term60 A B s op f g) = (term67 A B f op s g)).
Proof. exact (prop_ext (fun h4 : term58 A B op g s => @lem6184224 A B f g s op h1 h2 h3) (fun h4 : (term60 A B s op f g) = (term67 A B f op s g) => @lem6160871 A B op g s h2)). Qed.
Lemma lem6184228 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : (term60 A B s op f g) = (term67 A B f op s g).
Proof. exact (EQ_MP (@lem6184227 A B f g s op h1 h2 h3) (@lem6160871 A B op g s h2)). Qed.
Lemma lem6184229 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : (term58 A B op f s) = ((term60 A B s op f g) = (term67 A B f op s g)).
Proof. exact (prop_ext (fun h4 : term58 A B op f s => @lem6184228 A B f g s op h1 h2 h3) (fun h4 : (term60 A B s op f g) = (term67 A B f op s g) => @lem6160872 A B op f s h1)). Qed.
Lemma lem6184230 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term58 A B op f s) (h2 : term58 A B op g s) (h3 : @monoidal B op) : (term60 A B s op f g) = (term67 A B f op s g).
Proof. exact (EQ_MP (@lem6184229 A B f g s op h1 h2 h3) (@lem6160872 A B op f s h1)). Qed.
Lemma lem6184231 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (s : A -> Prop) (h1 : term58 A B op f s) (h2 : @monoidal B op) (h3 : term57 A B f op g s) : (term58 A B op g s) = ((term60 A B s op f g) = (term67 A B f op s g)).
Proof. exact (prop_ext (fun h4 : term58 A B op g s => @lem6184230 A B f g s op h1 h4 h2) (fun h4 : (term60 A B s op f g) = (term67 A B f op s g) => @lem6184225 A B f op g s h3)). Qed.
Lemma lem6184232 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (s : A -> Prop) (h1 : term58 A B op f s) (h2 : @monoidal B op) (h3 : term57 A B f op g s) : (term60 A B s op f g) = (term67 A B f op s g).
Proof. exact (EQ_MP (@lem6184231 A B f op g s h1 h2 h3) (@lem6184225 A B f op g s h3)). Qed.
Lemma lem6184233 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term57 A B f op g s) : (term58 A B op f s) = ((term60 A B s op f g) = (term67 A B f op s g)).
Proof. exact (prop_ext (fun h3 : term58 A B op f s => @lem6184232 A B f op g s h3 h1 h2) (fun h3 : (term60 A B s op f g) = (term67 A B f op s g) => @lem6184226 A B f op g s h2)). Qed.
Lemma lem6184234 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term57 A B f op g s) : (term60 A B s op f g) = (term67 A B f op s g).
Proof. exact (EQ_MP (@lem6184233 A B f op g s h1 h2) (@lem6184226 A B f op g s h2)). Qed.
Lemma lem6184235 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term1326 A B f op s g.
Proof. exact (fun h0 : term57 A B f op g s => @lem6184234 A B f op g s h1 h0). Qed.
Lemma lem6184240 {A B : Type'} (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term1327 A B f op g.
Proof. exact (fun s : A -> Prop => @lem6184235 A B f s g op h1). Qed.
Lemma lem6184245 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term1328 A B f op.
Proof. exact (fun g : A -> B => @lem6184240 A B f g op h1). Qed.
Lemma lem6184250 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term1329 A B op.
Proof. exact (fun f : A -> B => @lem6184245 A B f op h1). Qed.
Lemma lem6184251 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = (term1329 A B op).
Proof. exact (prop_ext (fun h2 : @monoidal B op => @lem6184250 A B op h1) (fun h2 : term1329 A B op => @lem6160869 B op h1)). Qed.
Lemma lem6184252 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term1329 A B op.
Proof. exact (EQ_MP (@lem6184251 A B op h1) (@lem6160869 B op h1)). Qed.
Lemma lem6184253 {A B : Type'} (op : type1400 B) : term1330 A B op.
Proof. exact (fun h0 : @monoidal B op => @lem6184252 A B op h0). Qed.
Lemma lem6184258 {A B : Type'} : term1331 A B.
Proof. exact (fun op : type1400 B => @lem6184253 A B op). Qed.
