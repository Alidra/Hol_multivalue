Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_SUPERSET_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EXTENSION_spec.
Require Import ITERATE_SUPPORT_spec.
Require Import SUBSET_spec.
Require Import support_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm69_spec.
Lemma lem6013662 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem6013663 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem6013664 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem6013663 t1) (@lem6013662 t1)). Qed.
Lemma lem6013665 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem6013664 t1 t2). Qed.
Lemma lem6013666 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem6013667 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem6013666 t1 t2) (@lem6013665 t1 t2)). Qed.
Lemma lem6013668 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem6013667 t1 t2 t3). Qed.
Lemma lem6013669 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem6013670 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem6013669 t1 t2 t3) (@lem6013668 t1 t2 t3)). Qed.
Lemma lem6013671 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem6013670 t1 t2 t3)). Qed.
Lemma lem6013696 {_83095 : Type'} : term7 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem6013697 {_83095 : Type'} (p : _83095 -> Prop) : term8 _83095 p.
Proof. exact (@lem6013696 _83095 p). Qed.
Lemma lem6013698 {_83095 : Type'} (p : _83095 -> Prop) : (term8 _83095 p) = (term9 _83095 p).
Proof. exact (eq_refl (term8 _83095 p)). Qed.
Lemma lem6013699 {_83095 : Type'} (p : _83095 -> Prop) : term9 _83095 p.
Proof. exact (EQ_MP (@lem6013698 _83095 p) (@lem6013697 _83095 p)). Qed.
Lemma lem6013700 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term10 _83095 p x.
Proof. exact (@lem6013699 _83095 p x). Qed.
Lemma lem6013701 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term10 _83095 p x) = ((term11 _83095 x p) = (p x)).
Proof. exact (eq_refl (term10 _83095 p x)). Qed.
Lemma lem6013710 {A : Type'} (s : A -> Prop) : term12 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem6013711 {A : Type'} (s : A -> Prop) : (term12 A s) = (term13 A s).
Proof. exact (eq_refl (term12 A s)). Qed.
Lemma lem6013712 {A : Type'} (s : A -> Prop) : term13 A s.
Proof. exact (EQ_MP (@lem6013711 A s) (@lem6013710 A s)). Qed.
Lemma lem6013713 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term14 A s t.
Proof. exact (@lem6013712 A s t). Qed.
Lemma lem6013714 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term14 A s t) = ((s = t) = (term15 A s t)).
Proof. exact (eq_refl (term14 A s t)). Qed.
Lemma lem6013716 {A B : Type'} (s : A -> Prop) : term16 A B s.
Proof. exact (@lem5716761 A B s). Qed.
Lemma lem6013717 {A B : Type'} (s : A -> Prop) : (term16 A B s) = (term17 A B s).
Proof. exact (eq_refl (term16 A B s)). Qed.
Lemma lem6013718 {A B : Type'} (s : A -> Prop) : term17 A B s.
Proof. exact (EQ_MP (@lem6013717 A B s) (@lem6013716 A B s)). Qed.
Lemma lem6013719 {A B : Type'} (s : A -> Prop) (f : A -> B) : term18 A B s f.
Proof. exact (@lem6013718 A B s f). Qed.
Lemma lem6013720 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term18 A B s f) = (term19 A B s f).
Proof. exact (eq_refl (term18 A B s f)). Qed.
Lemma lem6013721 {A B : Type'} (s : A -> Prop) (f : A -> B) : term19 A B s f.
Proof. exact (EQ_MP (@lem6013720 A B s f) (@lem6013719 A B s f)). Qed.
Lemma lem6013722 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term20 A B s f op.
Proof. exact (@lem6013721 A B s f op). Qed.
Lemma lem6013723 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term20 A B s f op) = ((@support A B op f s) = (term21 A B s f op)).
Proof. exact (eq_refl (term20 A B s f op)). Qed.
Lemma lem6013728 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) (h1 : (term22 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f)) : (term22 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f).
Proof. exact (h1). Qed.
Lemma lem6013729 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) (h1 : (term22 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f)) : (@iterate _120296 _120308 op s f) = (term22 _120296 _120308 op s f).
Proof. exact (SYM (@lem6013728 _120296 _120308 op s f h1)). Qed.
Lemma lem6013730 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) (h1 : (@iterate _120296 _120308 op s f) = (term22 _120296 _120308 op s f)) : (@iterate _120296 _120308 op s f) = (term22 _120296 _120308 op s f).
Proof. exact (h1). Qed.
Lemma lem6013731 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) (h1 : (@iterate _120296 _120308 op s f) = (term22 _120296 _120308 op s f)) : (term22 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f).
Proof. exact (SYM (@lem6013730 _120296 _120308 op s f h1)). Qed.
Lemma lem6013732 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : ((term22 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f)) = ((@iterate _120296 _120308 op s f) = (term22 _120296 _120308 op s f)).
Proof. exact (prop_ext (fun h1 : (term22 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f) => @lem6013729 _120296 _120308 op s f h1) (fun h1 : (@iterate _120296 _120308 op s f) = (term22 _120296 _120308 op s f) => @lem6013731 _120296 _120308 op s f h1)). Qed.
Lemma lem6013733 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : (term23 _120296 _120308 op f) = (term24 _120296 _120308 op f).
Proof. exact (fun_ext (fun s : _120308 -> Prop => @lem6013732 _120296 _120308 op s f)). Qed.
Lemma lem6013734 {_120308 : Type'} : (@all (_120308 -> Prop)) = (@all (_120308 -> Prop)).
Proof. exact (eq_refl (@all (_120308 -> Prop))). Qed.
Lemma lem6013735 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : (term25 _120296 _120308 op f) = (term26 _120296 _120308 op f).
Proof. exact (MK_COMB (@lem6013734 _120308) (@lem6013733 _120296 _120308 op f)). Qed.
Lemma lem6013736 {_120296 _120308 : Type'} (op : type1400 _120296) : (term27 _120296 _120308 op) = (term28 _120296 _120308 op).
Proof. exact (fun_ext (fun f : _120308 -> _120296 => @lem6013735 _120296 _120308 op f)). Qed.
Lemma lem6013737 {_120296 _120308 : Type'} : (@all (_120308 -> _120296)) = (@all (_120308 -> _120296)).
Proof. exact (eq_refl (@all (_120308 -> _120296))). Qed.
Lemma lem6013738 {_120296 _120308 : Type'} (op : type1400 _120296) : (term29 _120296 _120308 op) = (term30 _120296 _120308 op).
Proof. exact (MK_COMB (@lem6013737 _120296 _120308) (@lem6013736 _120296 _120308 op)). Qed.
Lemma lem6013739 {_120296 _120308 : Type'} : (term31 _120296 _120308) = (term32 _120296 _120308).
Proof. exact (fun_ext (fun op : type1400 _120296 => @lem6013738 _120296 _120308 op)). Qed.
Lemma lem6013740 {_120296 : Type'} : (@all (_120296 -> _120296 -> _120296)) = (@all (_120296 -> _120296 -> _120296)).
Proof. exact (eq_refl (@all (_120296 -> _120296 -> _120296))). Qed.
Lemma lem6013741 {_120296 _120308 : Type'} : (term33 _120296 _120308) = (term34 _120296 _120308).
Proof. exact (MK_COMB (@lem6013740 _120296) (@lem6013739 _120296 _120308)). Qed.
Lemma lem6013742 {_120296 _120308 : Type'} : term34 _120296 _120308.
Proof. exact (EQ_MP (@lem6013741 _120296 _120308) (@lem5737860 _120296 _120308)). Qed.
Lemma lem6013743 {_120296 _120308 : Type'} (op : type1400 _120296) : term35 _120296 _120308 op.
Proof. exact (@lem6013742 _120296 _120308 op). Qed.
Lemma lem6013744 {_120296 _120308 : Type'} (op : type1400 _120296) : (term35 _120296 _120308 op) = (term30 _120296 _120308 op).
Proof. exact (eq_refl (term35 _120296 _120308 op)). Qed.
Lemma lem6013745 {_120296 _120308 : Type'} (op : type1400 _120296) : term30 _120296 _120308 op.
Proof. exact (EQ_MP (@lem6013744 _120296 _120308 op) (@lem6013743 _120296 _120308 op)). Qed.
Lemma lem6013746 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : term36 _120296 _120308 op f.
Proof. exact (@lem6013745 _120296 _120308 op f). Qed.
Lemma lem6013747 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : (term36 _120296 _120308 op f) = (term26 _120296 _120308 op f).
Proof. exact (eq_refl (term36 _120296 _120308 op f)). Qed.
Lemma lem6013748 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : term26 _120296 _120308 op f.
Proof. exact (EQ_MP (@lem6013747 _120296 _120308 op f) (@lem6013746 _120296 _120308 op f)). Qed.
Lemma lem6013749 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) (s : _120308 -> Prop) : term37 _120296 _120308 op f s.
Proof. exact (@lem6013748 _120296 _120308 op f s). Qed.
Lemma lem6013750 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : (term37 _120296 _120308 op f s) = ((@iterate _120296 _120308 op s f) = (term22 _120296 _120308 op s f)).
Proof. exact (eq_refl (term37 _120296 _120308 op f s)). Qed.
Lemma lem6013752 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem6013753 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term38 A B v u f op) : term38 A B v u f op.
Proof. exact (h1). Qed.
Lemma lem6013754 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term39 A B v u f op) : term39 A B v u f op.
Proof. exact (h1). Qed.
Lemma lem6013755 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @SUBSET A u v) : @SUBSET A u v.
Proof. exact (h1). Qed.
Lemma lem6013759 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : (@iterate _120296 _120308 op s f) = (term22 _120296 _120308 op s f).
Proof. exact (EQ_MP (@lem6013750 _120296 _120308 op s f) (@lem6013749 _120296 _120308 op f s)). Qed.
Lemma lem6013760 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (@iterate B A op s f) = (term40 A B op s f).
Proof. exact (@lem6013759 B A op s f). Qed.
Lemma lem6013761 {A B : Type'} (op : type1400 B) (v : A -> Prop) (f : A -> B) : (@iterate B A op v f) = (term40 A B op v f).
Proof. exact (@lem6013760 A B op v f). Qed.
Lemma lem6013762 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6013763 {A B : Type'} (op : type1400 B) (v : A -> Prop) (f : A -> B) : (term41 A B op v f) = (term42 A B op v f).
Proof. exact (MK_COMB (@lem6013762 B) (@lem6013761 A B op v f)). Qed.
Lemma lem6013765 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : (@iterate _120296 _120308 op s f) = (term22 _120296 _120308 op s f).
Proof. exact (EQ_MP (@lem6013750 _120296 _120308 op s f) (@lem6013749 _120296 _120308 op f s)). Qed.
Lemma lem6013766 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (@iterate B A op s f) = (term40 A B op s f).
Proof. exact (@lem6013765 B A op s f). Qed.
Lemma lem6013767 {A B : Type'} (op : type1400 B) (u : A -> Prop) (f : A -> B) : (@iterate B A op u f) = (term40 A B op u f).
Proof. exact (@lem6013766 A B op u f). Qed.
Lemma lem6013768 {A B : Type'} (v : A -> Prop) (op : type1400 B) (u : A -> Prop) (f : A -> B) : ((@iterate B A op v f) = (@iterate B A op u f)) = ((term40 A B op v f) = (term40 A B op u f)).
Proof. exact (MK_COMB (@lem6013763 A B op v f) (@lem6013767 A B op u f)). Qed.
Lemma lem6013769 {A B : Type'} (v : A -> Prop) (op : type1400 B) (u : A -> Prop) (f : A -> B) : ((term40 A B op v f) = (term40 A B op u f)) = ((@iterate B A op v f) = (@iterate B A op u f)).
Proof. exact (SYM (@lem6013768 A B v op u f)). Qed.
Lemma lem6013770 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6013771 {A B : Type'} (op : type1400 B) : (@iterate B A op) = (@iterate B A op).
Proof. exact (eq_refl (@iterate B A op)). Qed.
Lemma lem6013775 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term15 A s t).
Proof. exact (EQ_MP (@lem6013714 A s t) (@lem6013713 A s t)). Qed.
Lemma lem6013776 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term15 A s t).
Proof. exact (@lem6013775 A s t). Qed.
Lemma lem6013777 {A B : Type'} (v : A -> Prop) (op : type1400 B) (f : A -> B) (u : A -> Prop) : ((@support A B op f v) = (@support A B op f u)) = (term43 A B v op f u).
Proof. exact (@lem6013776 A (@support A B op f v) (@support A B op f u)). Qed.
Lemma lem6013787 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (EQ_MP (@lem6013723 A B s f op) (@lem6013722 A B s f op)). Qed.
Lemma lem6013788 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (@lem6013787 A B s f op). Qed.
Lemma lem6013789 {A B : Type'} (v : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f v) = (term21 A B v f op).
Proof. exact (@lem6013788 A B v f op). Qed.
Lemma lem6013800 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6013801 {A B : Type'} (x : A) (v : A -> Prop) (f : A -> B) (op : type1400 B) : (term44 A B x op f v) = (term45 A B x v f op).
Proof. exact (MK_COMB (@lem6013800 A x) (@lem6013789 A B v f op)). Qed.
Lemma lem6013803 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term11 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem6013701 _83095 p x) (@lem6013700 _83095 p x)). Qed.
Lemma lem6013804 {A : Type'} (p : A -> Prop) (x : A) : (term11 A x p) = (p x).
Proof. exact (@lem6013803 A p x). Qed.
Lemma lem6013805 {A B : Type'} (v : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term46 A B x v f op) = (term47 A B v f op x).
Proof. exact (@lem6013804 A (term48 A B v f op) x). Qed.
Lemma lem6013806 {A B : Type'} (v : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term47 A B v f op x) = (term49 A B v f x op).
Proof. exact (eq_refl (term47 A B v f op x)). Qed.
Lemma lem6013807 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem6013808 {A B : Type'} (GEN_PVAR_237 : A) (v : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term50 A B GEN_PVAR_237 v f op x) = (term51 A B GEN_PVAR_237 v f x op).
Proof. exact (MK_COMB (@lem6013807 A GEN_PVAR_237) (@lem6013806 A B v f x op)). Qed.
Lemma lem6013809 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6013810 {A B : Type'} (GEN_PVAR_237 : A) (v : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term52 A B GEN_PVAR_237 v f op x) = (term53 A B GEN_PVAR_237 v f op x).
Proof. exact (MK_COMB (@lem6013808 A B GEN_PVAR_237 v f x op) (@lem6013809 A x)). Qed.
Lemma lem6013811 {A B : Type'} (GEN_PVAR_237 : A) (v : A -> Prop) (f : A -> B) (op : type1400 B) : (term54 A B GEN_PVAR_237 v f op) = (term55 A B GEN_PVAR_237 v f op).
Proof. exact (fun_ext (fun x : A => @lem6013810 A B GEN_PVAR_237 v f op x)). Qed.
Lemma lem6013812 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6013813 {A B : Type'} (GEN_PVAR_237 : A) (v : A -> Prop) (f : A -> B) (op : type1400 B) : (term56 A B GEN_PVAR_237 v f op) = (term57 A B GEN_PVAR_237 v f op).
Proof. exact (MK_COMB (@lem6013812 A) (@lem6013811 A B GEN_PVAR_237 v f op)). Qed.
Lemma lem6013814 {A B : Type'} (v : A -> Prop) (f : A -> B) (op : type1400 B) : (term58 A B v f op) = (term59 A B v f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem6013813 A B GEN_PVAR_237 v f op)). Qed.
Lemma lem6013815 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6013816 {A B : Type'} (v : A -> Prop) (f : A -> B) (op : type1400 B) : (term60 A B v f op) = (term21 A B v f op).
Proof. exact (MK_COMB (@lem6013815 A) (@lem6013814 A B v f op)). Qed.
Lemma lem6013817 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6013818 {A B : Type'} (x : A) (v : A -> Prop) (f : A -> B) (op : type1400 B) : (term46 A B x v f op) = (term45 A B x v f op).
Proof. exact (MK_COMB (@lem6013817 A x) (@lem6013816 A B v f op)). Qed.
Lemma lem6013819 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6013820 {A B : Type'} (x : A) (v : A -> Prop) (f : A -> B) (op : type1400 B) : (term61 A B x v f op) = (term62 A B x v f op).
Proof. exact (MK_COMB (@lem6013819) (@lem6013818 A B x v f op)). Qed.
Lemma lem6013821 {A B : Type'} (v : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term47 A B v f op x) = (term49 A B v f x op).
Proof. exact (eq_refl (term47 A B v f op x)). Qed.
Lemma lem6013822 {A B : Type'} (v : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : ((term46 A B x v f op) = (term47 A B v f op x)) = ((term45 A B x v f op) = (term49 A B v f x op)).
Proof. exact (MK_COMB (@lem6013820 A B x v f op) (@lem6013821 A B v f x op)). Qed.
Lemma lem6013823 {A B : Type'} (v : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term45 A B x v f op) = (term49 A B v f x op).
Proof. exact (EQ_MP (@lem6013822 A B v f x op) (@lem6013805 A B v f op x)). Qed.
Lemma lem6013830 {A B : Type'} (v : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term44 A B x op f v) = (term49 A B v f x op).
Proof. exact (TRANS (@lem6013801 A B x v f op) (@lem6013823 A B v f x op)). Qed.
Lemma lem6013831 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6013832 {A B : Type'} (v : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term63 A B x op f v) = (term64 A B v f x op).
Proof. exact (MK_COMB (@lem6013831) (@lem6013830 A B v f x op)). Qed.
Lemma lem6013834 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (EQ_MP (@lem6013723 A B s f op) (@lem6013722 A B s f op)). Qed.
Lemma lem6013835 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term21 A B s f op).
Proof. exact (@lem6013834 A B s f op). Qed.
Lemma lem6013836 {A B : Type'} (u : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f u) = (term21 A B u f op).
Proof. exact (@lem6013835 A B u f op). Qed.
Lemma lem6013847 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6013848 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term44 A B x op f u) = (term45 A B x u f op).
Proof. exact (MK_COMB (@lem6013847 A x) (@lem6013836 A B u f op)). Qed.
Lemma lem6013850 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term11 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem6013701 _83095 p x) (@lem6013700 _83095 p x)). Qed.
Lemma lem6013851 {A : Type'} (p : A -> Prop) (x : A) : (term11 A x p) = (p x).
Proof. exact (@lem6013850 A p x). Qed.
Lemma lem6013852 {A B : Type'} (u : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term46 A B x u f op) = (term47 A B u f op x).
Proof. exact (@lem6013851 A (term48 A B u f op) x). Qed.
Lemma lem6013853 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term47 A B u f op x) = (term49 A B u f x op).
Proof. exact (eq_refl (term47 A B u f op x)). Qed.
Lemma lem6013854 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem6013855 {A B : Type'} (GEN_PVAR_237 : A) (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term50 A B GEN_PVAR_237 u f op x) = (term51 A B GEN_PVAR_237 u f x op).
Proof. exact (MK_COMB (@lem6013854 A GEN_PVAR_237) (@lem6013853 A B u f x op)). Qed.
Lemma lem6013856 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6013857 {A B : Type'} (GEN_PVAR_237 : A) (u : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term52 A B GEN_PVAR_237 u f op x) = (term53 A B GEN_PVAR_237 u f op x).
Proof. exact (MK_COMB (@lem6013855 A B GEN_PVAR_237 u f x op) (@lem6013856 A x)). Qed.
Lemma lem6013858 {A B : Type'} (GEN_PVAR_237 : A) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term54 A B GEN_PVAR_237 u f op) = (term55 A B GEN_PVAR_237 u f op).
Proof. exact (fun_ext (fun x : A => @lem6013857 A B GEN_PVAR_237 u f op x)). Qed.
Lemma lem6013859 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6013860 {A B : Type'} (GEN_PVAR_237 : A) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term56 A B GEN_PVAR_237 u f op) = (term57 A B GEN_PVAR_237 u f op).
Proof. exact (MK_COMB (@lem6013859 A) (@lem6013858 A B GEN_PVAR_237 u f op)). Qed.
Lemma lem6013861 {A B : Type'} (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term58 A B u f op) = (term59 A B u f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem6013860 A B GEN_PVAR_237 u f op)). Qed.
Lemma lem6013862 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6013863 {A B : Type'} (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term60 A B u f op) = (term21 A B u f op).
Proof. exact (MK_COMB (@lem6013862 A) (@lem6013861 A B u f op)). Qed.
Lemma lem6013864 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6013865 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term46 A B x u f op) = (term45 A B x u f op).
Proof. exact (MK_COMB (@lem6013864 A x) (@lem6013863 A B u f op)). Qed.
Lemma lem6013866 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6013867 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term61 A B x u f op) = (term62 A B x u f op).
Proof. exact (MK_COMB (@lem6013866) (@lem6013865 A B x u f op)). Qed.
Lemma lem6013868 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term47 A B u f op x) = (term49 A B u f x op).
Proof. exact (eq_refl (term47 A B u f op x)). Qed.
Lemma lem6013869 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : ((term46 A B x u f op) = (term47 A B u f op x)) = ((term45 A B x u f op) = (term49 A B u f x op)).
Proof. exact (MK_COMB (@lem6013867 A B x u f op) (@lem6013868 A B u f x op)). Qed.
Lemma lem6013870 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term45 A B x u f op) = (term49 A B u f x op).
Proof. exact (EQ_MP (@lem6013869 A B u f x op) (@lem6013852 A B u f op x)). Qed.
Lemma lem6013877 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term44 A B x op f u) = (term49 A B u f x op).
Proof. exact (TRANS (@lem6013848 A B x u f op) (@lem6013870 A B u f x op)). Qed.
Lemma lem6013878 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : ((term44 A B x op f v) = (term44 A B x op f u)) = ((term49 A B v f x op) = (term49 A B u f x op)).
Proof. exact (MK_COMB (@lem6013832 A B v f x op) (@lem6013877 A B u f x op)). Qed.
Lemma lem6013883 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term65 A B v op f u) = (term66 A B v u f op).
Proof. exact (fun_ext (fun x : A => @lem6013878 A B v u f x op)). Qed.
Lemma lem6013884 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6013885 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term43 A B v op f u) = (term67 A B v u f op).
Proof. exact (MK_COMB (@lem6013884 A) (@lem6013883 A B v u f op)). Qed.
Lemma lem6013890 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : ((@support A B op f v) = (@support A B op f u)) = (term67 A B v u f op).
Proof. exact (TRANS (@lem6013777 A B v op f u) (@lem6013885 A B v u f op)). Qed.
Lemma lem6013891 {A B : Type'} (v : A -> Prop) (op : type1400 B) (f : A -> B) (u : A -> Prop) : (term67 A B v u f op) = ((@support A B op f v) = (@support A B op f u)).
Proof. exact (SYM (@lem6013890 A B v u f op)). Qed.
Lemma lem6013893 (p : Prop) : p = (term68 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6013894 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term67 A B v u f op) = (term69 A B v u f op).
Proof. exact (@lem6013893 (term67 A B v u f op)). Qed.
Lemma lem6013895 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term69 A B v u f op) = (term67 A B v u f op).
Proof. exact (SYM (@lem6013894 A B v u f op)). Qed.
Lemma lem6013896 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term70 A B v u f op) : term70 A B v u f op.
Proof. exact (h1). Qed.
Lemma lem6013897 {A : Type'} : term71 A.
Proof. exact (@lem3194148 A). Qed.
Lemma lem6013901 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term72 A B v u f op) : term72 A B v u f op.
Proof. exact (h1). Qed.
Lemma lem6013902 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : term73 A B v u f op.
Proof. exact (fun h0 : term72 A B v u f op => @lem6013901 A B v u f op h0). Qed.
Lemma lem6013903 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term73 A B v u f op) : term73 A B v u f op.
Proof. exact (h1). Qed.
Lemma lem6013904 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term72 A B v u f op) : term72 A B v u f op.
Proof. exact (h1). Qed.
Lemma lem6013905 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term72 A B v u f op) (h2 : term73 A B v u f op) : term72 A B v u f op.
Proof. exact (@lem6013903 A B v u f op h2 (@lem6013904 A B v u f op h1)). Qed.
Lemma lem6013906 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term72 A B v u f op) : term74 A B v u f op.
Proof. exact (fun h0 : term73 A B v u f op => @lem6013905 A B v u f op h1 h0). Qed.
Lemma lem6013907 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term73 A B v u f op) : term73 A B v u f op.
Proof. exact (h1). Qed.
Lemma lem6013908 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term72 A B v u f op) (h2 : term73 A B v u f op) : term72 A B v u f op.
Proof. exact (@lem6013906 A B v u f op h1 (@lem6013907 A B v u f op h2)). Qed.
Lemma lem6013909 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term73 A B v u f op) : term73 A B v u f op.
Proof. exact (fun h0 : term72 A B v u f op => @lem6013908 A B v u f op h0 h1). Qed.
Lemma lem6013910 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : term75 A B v u f op.
Proof. exact (fun h0 : term73 A B v u f op => @lem6013909 A B v u f op h0). Qed.
Lemma lem6013913 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : term73 A B v u f op.
Proof. exact (@lem6013910 A B v u f op (@lem6013902 A B v u f op)). Qed.
Lemma lem6013914 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : term73 A B v u f op.
Proof. exact (@lem6013913 A B v u f op). Qed.
Lemma lem6013956 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6013957 {A : Type'} : (term76 A) = (term77 A).
Proof. exact (@lem6013956 (term71 A)). Qed.
Lemma lem6013972 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term78 A B v u f op) = (term78 A B v u f op).
Proof. exact (eq_refl (term78 A B v u f op)). Qed.
Lemma lem6013973 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term79 A B v u f op) = (term80 A B v u f op).
Proof. exact (MK_COMB (@lem6013972 A B v u f op) (@lem6013957 A)). Qed.
Lemma lem6013976 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term81 A B v u f op) = (term81 A B v u f op).
Proof. exact (eq_refl (term81 A B v u f op)). Qed.
Lemma lem6013977 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term82 A B v u f op) = (term83 A B v u f op).
Proof. exact (MK_COMB (@lem6013976 A B v u f op) (@lem6013973 A B v u f op)). Qed.
Lemma lem6013980 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term84 A u v) = (term84 A u v).
Proof. exact (eq_refl (term84 A u v)). Qed.
Lemma lem6013981 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term85 A B v u f op) = (term86 A B v u f op).
Proof. exact (MK_COMB (@lem6013980 A u v) (@lem6013977 A B v u f op)). Qed.
Lemma lem6013984 {B : Type'} (op : type1400 B) : (term87 B op) = (term87 B op).
Proof. exact (eq_refl (term87 B op)). Qed.
Lemma lem6013985 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term72 A B v u f op) = (term88 A B v u f op).
Proof. exact (MK_COMB (@lem6013984 B op) (@lem6013981 A B v u f op)). Qed.
Lemma lem6013988 {A B : Type'} (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term89 A B u f op) = (term90 A B u f op).
Proof. exact (fun_ext (fun v : A -> Prop => @lem6013985 A B v u f op)). Qed.
Lemma lem6013989 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6013990 {A B : Type'} (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term91 A B u f op) = (term92 A B u f op).
Proof. exact (MK_COMB (@lem6013989 A) (@lem6013988 A B u f op)). Qed.
Lemma lem6013995 {A B : Type'} (f : A -> B) (op : type1400 B) : (term93 A B f op) = (term94 A B f op).
Proof. exact (fun_ext (fun u : A -> Prop => @lem6013990 A B u f op)). Qed.
Lemma lem6013996 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6013997 {A B : Type'} (f : A -> B) (op : type1400 B) : (term95 A B f op) = (term96 A B f op).
Proof. exact (MK_COMB (@lem6013996 A) (@lem6013995 A B f op)). Qed.
Lemma lem6014002 {A B : Type'} (op : type1400 B) : (term97 A B op) = (term98 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem6013997 A B f op)). Qed.
Lemma lem6014003 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem6014004 {A B : Type'} (op : type1400 B) : (term99 A B op) = (term100 A B op).
Proof. exact (MK_COMB (@lem6014003 A B) (@lem6014002 A B op)). Qed.
Lemma lem6014009 {A B : Type'} : (term101 A B) = (term102 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6014004 A B op)). Qed.
Lemma lem6014010 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6014019 {A B : Type'} : (term103 A B) = (term104 A B).
Proof. exact (MK_COMB (@lem6014010 B) (@lem6014009 A B)). Qed.
Lemma lem6014024 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term105 A s x t) = (term105 A s x t).
Proof. exact (eq_refl (term105 A s x t)). Qed.
Lemma lem6014025 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term106 A s t) = (term106 A s t).
Proof. exact (fun_ext (fun x : A => @lem6014024 A s x t)). Qed.
Lemma lem6014026 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6014027 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term107 A s t) = (term107 A s t).
Proof. exact (MK_COMB (@lem6014026 A) (@lem6014025 A s t)). Qed.
Lemma lem6014030 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term108 A s t) = (term108 A s t).
Proof. exact (eq_refl (term108 A s t)). Qed.
Lemma lem6014031 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((@SUBSET A s t) = (term107 A s t)) = ((@SUBSET A s t) = (term107 A s t)).
Proof. exact (MK_COMB (@lem6014030 A s t) (@lem6014027 A s t)). Qed.
Lemma lem6014032 {A : Type'} (s : A -> Prop) : (term109 A s) = (term109 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6014031 A s t)). Qed.
Lemma lem6014033 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6014034 {A : Type'} (s : A -> Prop) : (term110 A s) = (term110 A s).
Proof. exact (MK_COMB (@lem6014033 A) (@lem6014032 A s)). Qed.
Lemma lem6014035 {A : Type'} : (term111 A) = (term111 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6014034 A s)). Qed.
Lemma lem6014036 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6014037 {A : Type'} : (term71 A) = (term71 A).
Proof. exact (MK_COMB (@lem6014036 A) (@lem6014035 A)). Qed.
Lemma lem6014038 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6014039 {A : Type'} : (term77 A) = (term77 A).
Proof. exact (MK_COMB (@lem6014038) (@lem6014037 A)). Qed.
Lemma lem6014056 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : ((term49 A B v f x op) = (term49 A B u f x op)) = ((term49 A B v f x op) = (term49 A B u f x op)).
Proof. exact (eq_refl ((term49 A B v f x op) = (term49 A B u f x op))). Qed.
Lemma lem6014057 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term66 A B v u f op) = (term66 A B v u f op).
Proof. exact (fun_ext (fun x : A => @lem6014056 A B v u f x op)). Qed.
Lemma lem6014058 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6014059 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term67 A B v u f op) = (term67 A B v u f op).
Proof. exact (MK_COMB (@lem6014058 A) (@lem6014057 A B v u f op)). Qed.
Lemma lem6014060 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6014061 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term70 A B v u f op) = (term70 A B v u f op).
Proof. exact (MK_COMB (@lem6014060) (@lem6014059 A B v u f op)). Qed.
Lemma lem6014062 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6014063 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term78 A B v u f op) = (term78 A B v u f op).
Proof. exact (MK_COMB (@lem6014062) (@lem6014061 A B v u f op)). Qed.
Lemma lem6014064 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term80 A B v u f op) = (term80 A B v u f op).
Proof. exact (MK_COMB (@lem6014063 A B v u f op) (@lem6014039 A)). Qed.
Lemma lem6014075 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term112 A B v u f x op) = (term112 A B v u f x op).
Proof. exact (eq_refl (term112 A B v u f x op)). Qed.
Lemma lem6014076 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term113 A B v u f op) = (term113 A B v u f op).
Proof. exact (fun_ext (fun x : A => @lem6014075 A B v u f x op)). Qed.
Lemma lem6014077 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6014078 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term39 A B v u f op) = (term39 A B v u f op).
Proof. exact (MK_COMB (@lem6014077 A) (@lem6014076 A B v u f op)). Qed.
Lemma lem6014079 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6014080 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term81 A B v u f op) = (term81 A B v u f op).
Proof. exact (MK_COMB (@lem6014079) (@lem6014078 A B v u f op)). Qed.
Lemma lem6014081 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term83 A B v u f op) = (term83 A B v u f op).
Proof. exact (MK_COMB (@lem6014080 A B v u f op) (@lem6014064 A B v u f op)). Qed.
Lemma lem6014084 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term84 A u v) = (term84 A u v).
Proof. exact (eq_refl (term84 A u v)). Qed.
Lemma lem6014085 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term86 A B v u f op) = (term86 A B v u f op).
Proof. exact (MK_COMB (@lem6014084 A u v) (@lem6014081 A B v u f op)). Qed.
Lemma lem6014088 {B : Type'} (op : type1400 B) : (term87 B op) = (term87 B op).
Proof. exact (eq_refl (term87 B op)). Qed.
Lemma lem6014089 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term88 A B v u f op) = (term88 A B v u f op).
Proof. exact (MK_COMB (@lem6014088 B op) (@lem6014085 A B v u f op)). Qed.
Lemma lem6014090 {A B : Type'} (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term90 A B u f op) = (term90 A B u f op).
Proof. exact (fun_ext (fun v : A -> Prop => @lem6014089 A B v u f op)). Qed.
Lemma lem6014091 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6014092 {A B : Type'} (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term92 A B u f op) = (term92 A B u f op).
Proof. exact (MK_COMB (@lem6014091 A) (@lem6014090 A B u f op)). Qed.
Lemma lem6014093 {A B : Type'} (f : A -> B) (op : type1400 B) : (term94 A B f op) = (term94 A B f op).
Proof. exact (fun_ext (fun u : A -> Prop => @lem6014092 A B u f op)). Qed.
Lemma lem6014094 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6014095 {A B : Type'} (f : A -> B) (op : type1400 B) : (term96 A B f op) = (term96 A B f op).
Proof. exact (MK_COMB (@lem6014094 A) (@lem6014093 A B f op)). Qed.
Lemma lem6014096 {A B : Type'} (op : type1400 B) : (term98 A B op) = (term98 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem6014095 A B f op)). Qed.
Lemma lem6014097 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem6014098 {A B : Type'} (op : type1400 B) : (term100 A B op) = (term100 A B op).
Proof. exact (MK_COMB (@lem6014097 A B) (@lem6014096 A B op)). Qed.
Lemma lem6014099 {A B : Type'} : (term102 A B) = (term102 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6014098 A B op)). Qed.
Lemma lem6014100 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6014101 {A B : Type'} : (term104 A B) = (term104 A B).
Proof. exact (MK_COMB (@lem6014100 B) (@lem6014099 A B)). Qed.
Lemma lem6014176 {A B : Type'} : (term103 A B) = (term104 A B).
Proof. exact (TRANS (@lem6014019 A B) (@lem6014101 A B)). Qed.
Lemma lem6014177 {A B : Type'} : (term104 A B) = (term103 A B).
Proof. exact (SYM (@lem6014176 A B)). Qed.
Lemma lem6014180 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term39 A B v u f op) : term39 A B v u f op.
Proof. exact (h1). Qed.
Lemma lem6014181 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term70 A B v u f op) : term70 A B v u f op.
Proof. exact (h1). Qed.
Lemma lem6014182 {A : Type'} (h1 : term71 A) : term71 A.
Proof. exact (h1). Qed.
Lemma lem6014194 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @SUBSET A u v) : @SUBSET A u v.
Proof. exact (h1). Qed.
Lemma lem6014198 {A : Type'} (x : A) (u : A -> Prop) : (term114 A x u) = (@IN A x u).
Proof. exact (@lem16933 (@IN A x u)). Qed.
Lemma lem6014200 {A : Type'} (x : A) (v : A -> Prop) : (term115 A x v) = (term115 A x v).
Proof. exact (eq_refl (term115 A x v)). Qed.
Lemma lem6014201 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) : (term116 A v x u) = (term117 A v x u).
Proof. exact (MK_COMB (@lem6014200 A x v) (@lem6014198 A x u)). Qed.
Lemma lem6014202 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) : (term118 A v x u) = (term116 A v x u).
Proof. exact (@lem17045 (@IN A x v) (term119 A x u)). Qed.
Lemma lem6014203 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) : (term118 A v x u) = (term117 A v x u).
Proof. exact (TRANS (@lem6014202 A v x u) (@lem6014201 A v x u)). Qed.
Lemma lem6014204 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : ((f x) = (@neutral B op)) = ((f x) = (@neutral B op)).
Proof. exact (eq_refl ((f x) = (@neutral B op))). Qed.
Lemma lem6014205 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6014206 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) : (term120 A v x u) = (term121 A v x u).
Proof. exact (MK_COMB (@lem6014205) (@lem6014203 A v x u)). Qed.
Lemma lem6014207 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term122 A B v u f x op) = (term123 A B v u f x op).
Proof. exact (MK_COMB (@lem6014206 A v x u) (@lem6014204 A B f x op)). Qed.
Lemma lem6014208 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term112 A B v u f x op) = (term122 A B v u f x op).
Proof. exact (@lem17265 (term124 A v x u) ((f x) = (@neutral B op))). Qed.
Lemma lem6014209 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term112 A B v u f x op) = (term123 A B v u f x op).
Proof. exact (TRANS (@lem6014208 A B v u f x op) (@lem6014207 A B v u f x op)). Qed.
Lemma lem6014210 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term113 A B v u f op) = (term125 A B v u f op).
Proof. exact (fun_ext (fun x : A => @lem6014209 A B v u f x op)). Qed.
Lemma lem6014211 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6014264 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term39 A B v u f op) = (term126 A B v u f op).
Proof. exact (MK_COMB (@lem6014211 A) (@lem6014210 A B v u f op)). Qed.
Lemma lem6014265 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term39 A B v u f op) : term126 A B v u f op.
Proof. exact (EQ_MP (@lem6014264 A B v u f op) (@lem6014180 A B v u f op h1)). Qed.
Lemma lem6014271 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term127 A B f x op) = ((f x) = (@neutral B op)).
Proof. exact (@lem16933 ((f x) = (@neutral B op))). Qed.
Lemma lem6014273 {A : Type'} (x : A) (v : A -> Prop) : (term115 A x v) = (term115 A x v).
Proof. exact (eq_refl (term115 A x v)). Qed.
Lemma lem6014274 {A B : Type'} (v : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term128 A B v f x op) = (term129 A B v f x op).
Proof. exact (MK_COMB (@lem6014273 A x v) (@lem6014271 A B f x op)). Qed.
Lemma lem6014275 {A B : Type'} (v : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term130 A B v f x op) = (term128 A B v f x op).
Proof. exact (@lem17045 (@IN A x v) (term131 A B f x op)). Qed.
Lemma lem6014276 {A B : Type'} (v : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term130 A B v f x op) = (term129 A B v f x op).
Proof. exact (TRANS (@lem6014275 A B v f x op) (@lem6014274 A B v f x op)). Qed.
Lemma lem6014285 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term127 A B f x op) = ((f x) = (@neutral B op)).
Proof. exact (@lem16933 ((f x) = (@neutral B op))). Qed.
Lemma lem6014287 {A : Type'} (x : A) (u : A -> Prop) : (term115 A x u) = (term115 A x u).
Proof. exact (eq_refl (term115 A x u)). Qed.
Lemma lem6014288 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term128 A B u f x op) = (term129 A B u f x op).
Proof. exact (MK_COMB (@lem6014287 A x u) (@lem6014285 A B f x op)). Qed.
Lemma lem6014289 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term130 A B u f x op) = (term128 A B u f x op).
Proof. exact (@lem17045 (@IN A x u) (term131 A B f x op)). Qed.
Lemma lem6014290 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term130 A B u f x op) = (term129 A B u f x op).
Proof. exact (TRANS (@lem6014289 A B u f x op) (@lem6014288 A B u f x op)). Qed.
Lemma lem6014293 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term49 A B u f x op) = (term49 A B u f x op).
Proof. exact (eq_refl (term49 A B u f x op)). Qed.
Lemma lem6014294 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6014295 {A B : Type'} (v : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term132 A B v f x op) = (term133 A B v f x op).
Proof. exact (MK_COMB (@lem6014294) (@lem6014276 A B v f x op)). Qed.
Lemma lem6014296 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term134 A B v u f x op) = (term135 A B v u f x op).
Proof. exact (MK_COMB (@lem6014295 A B v f x op) (@lem6014293 A B u f x op)). Qed.
Lemma lem6014298 {A B : Type'} (v : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term136 A B v f x op) = (term136 A B v f x op).
Proof. exact (eq_refl (term136 A B v f x op)). Qed.
Lemma lem6014299 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term137 A B v u f x op) = (term138 A B v u f x op).
Proof. exact (MK_COMB (@lem6014298 A B v f x op) (@lem6014290 A B u f x op)). Qed.
Lemma lem6014300 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6014301 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term139 A B v u f x op) = (term140 A B v u f x op).
Proof. exact (MK_COMB (@lem6014300) (@lem6014299 A B v u f x op)). Qed.
Lemma lem6014302 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term141 A B v u f x op) = (term142 A B v u f x op).
Proof. exact (MK_COMB (@lem6014301 A B v u f x op) (@lem6014296 A B v u f x op)). Qed.
Lemma lem6014303 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term143 A B v u f x op) = (term141 A B v u f x op).
Proof. exact (@lem17646 (term49 A B v f x op) (term49 A B u f x op)). Qed.
Lemma lem6014304 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term143 A B v u f x op) = (term142 A B v u f x op).
Proof. exact (TRANS (@lem6014303 A B v u f x op) (@lem6014302 A B v u f x op)). Qed.
Lemma lem6014305 {A : Type'} (P : A -> Prop) : (term144 A P) = (term145 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem6014306 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term70 A B v u f op) = (term146 A B v u f op).
Proof. exact (@lem6014305 A (term66 A B v u f op)). Qed.
Lemma lem6014307 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term147 A B v u f op x) = ((term49 A B v f x op) = (term49 A B u f x op)).
Proof. exact (eq_refl (term147 A B v u f op x)). Qed.
Lemma lem6014308 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6014309 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term148 A B v u f op x) = (term143 A B v u f x op).
Proof. exact (MK_COMB (@lem6014308) (@lem6014307 A B v u f x op)). Qed.
Lemma lem6014310 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term148 A B v u f op x) = (term142 A B v u f x op).
Proof. exact (TRANS (@lem6014309 A B v u f x op) (@lem6014304 A B v u f x op)). Qed.
Lemma lem6014311 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term149 A B v u f op) = (term150 A B v u f op).
Proof. exact (fun_ext (fun x : A => @lem6014310 A B v u f x op)). Qed.
Lemma lem6014312 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6014313 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term146 A B v u f op) = (term151 A B v u f op).
Proof. exact (MK_COMB (@lem6014312 A) (@lem6014311 A B v u f op)). Qed.
Lemma lem6014314 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term70 A B v u f op) = (term151 A B v u f op).
Proof. exact (TRANS (@lem6014306 A B v u f op) (@lem6014313 A B v u f op)). Qed.
Lemma lem6014316 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term152 A P Q) = (term153 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem6014317 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term152 A P Q) = (term153 A P Q).
Proof. exact (@lem6014316 A P Q). Qed.
Lemma lem6014318 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term154 A B v u f op) = (term155 A B v u f op).
Proof. exact (@lem6014317 A (term156 A B v u f op) (term157 A B v u f op)). Qed.
Lemma lem6014319 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term158 A B v u f op x) = (term138 A B v u f x op).
Proof. exact (eq_refl (term158 A B v u f op x)). Qed.
Lemma lem6014320 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6014321 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term159 A B v u f op x) = (term140 A B v u f x op).
Proof. exact (MK_COMB (@lem6014320) (@lem6014319 A B v u f x op)). Qed.
Lemma lem6014322 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term160 A B v u f op x) = (term135 A B v u f x op).
Proof. exact (eq_refl (term160 A B v u f op x)). Qed.
Lemma lem6014323 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term161 A B v u f op x) = (term142 A B v u f x op).
Proof. exact (MK_COMB (@lem6014321 A B v u f x op) (@lem6014322 A B v u f x op)). Qed.
Lemma lem6014324 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term162 A B v u f op) = (term150 A B v u f op).
Proof. exact (fun_ext (fun x : A => @lem6014323 A B v u f x op)). Qed.
Lemma lem6014325 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6014326 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term154 A B v u f op) = (term151 A B v u f op).
Proof. exact (MK_COMB (@lem6014325 A) (@lem6014324 A B v u f op)). Qed.
Lemma lem6014327 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6014328 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term163 A B v u f op) = (term164 A B v u f op).
Proof. exact (MK_COMB (@lem6014327) (@lem6014326 A B v u f op)). Qed.
Lemma lem6014329 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term158 A B v u f op x) = (term138 A B v u f x op).
Proof. exact (eq_refl (term158 A B v u f op x)). Qed.
Lemma lem6014330 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term165 A B v u f op) = (term156 A B v u f op).
Proof. exact (fun_ext (fun x : A => @lem6014329 A B v u f x op)). Qed.
Lemma lem6014331 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6014332 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term166 A B v u f op) = (term167 A B v u f op).
Proof. exact (MK_COMB (@lem6014331 A) (@lem6014330 A B v u f op)). Qed.
Lemma lem6014333 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6014334 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term168 A B v u f op) = (term169 A B v u f op).
Proof. exact (MK_COMB (@lem6014333) (@lem6014332 A B v u f op)). Qed.
Lemma lem6014335 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term160 A B v u f op x) = (term135 A B v u f x op).
Proof. exact (eq_refl (term160 A B v u f op x)). Qed.
Lemma lem6014336 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term170 A B v u f op) = (term157 A B v u f op).
Proof. exact (fun_ext (fun x : A => @lem6014335 A B v u f x op)). Qed.
Lemma lem6014337 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6014338 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term171 A B v u f op) = (term172 A B v u f op).
Proof. exact (MK_COMB (@lem6014337 A) (@lem6014336 A B v u f op)). Qed.
Lemma lem6014339 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term155 A B v u f op) = (term173 A B v u f op).
Proof. exact (MK_COMB (@lem6014334 A B v u f op) (@lem6014338 A B v u f op)). Qed.
Lemma lem6014340 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : ((term154 A B v u f op) = (term155 A B v u f op)) = ((term151 A B v u f op) = (term173 A B v u f op)).
Proof. exact (MK_COMB (@lem6014328 A B v u f op) (@lem6014339 A B v u f op)). Qed.
Lemma lem6014341 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term151 A B v u f op) = (term173 A B v u f op).
Proof. exact (EQ_MP (@lem6014340 A B v u f op) (@lem6014318 A B v u f op)). Qed.
Lemma lem6014439 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term153 A P Q) = (term152 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem6014440 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term153 A P Q) = (term152 A P Q).
Proof. exact (@lem6014439 A P Q). Qed.
Lemma lem6014441 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term155 A B v u f op) = (term154 A B v u f op).
Proof. exact (@lem6014440 A (term156 A B v u f op) (term157 A B v u f op)). Qed.
Lemma lem6014442 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term158 A B v u f op x) = (term138 A B v u f x op).
Proof. exact (eq_refl (term158 A B v u f op x)). Qed.
Lemma lem6014443 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term165 A B v u f op) = (term156 A B v u f op).
Proof. exact (fun_ext (fun x : A => @lem6014442 A B v u f x op)). Qed.
Lemma lem6014444 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6014445 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term166 A B v u f op) = (term167 A B v u f op).
Proof. exact (MK_COMB (@lem6014444 A) (@lem6014443 A B v u f op)). Qed.
Lemma lem6014446 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6014447 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term168 A B v u f op) = (term169 A B v u f op).
Proof. exact (MK_COMB (@lem6014446) (@lem6014445 A B v u f op)). Qed.
Lemma lem6014448 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term160 A B v u f op x) = (term135 A B v u f x op).
Proof. exact (eq_refl (term160 A B v u f op x)). Qed.
Lemma lem6014449 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term170 A B v u f op) = (term157 A B v u f op).
Proof. exact (fun_ext (fun x : A => @lem6014448 A B v u f x op)). Qed.
Lemma lem6014450 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6014451 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term171 A B v u f op) = (term172 A B v u f op).
Proof. exact (MK_COMB (@lem6014450 A) (@lem6014449 A B v u f op)). Qed.
Lemma lem6014452 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term155 A B v u f op) = (term173 A B v u f op).
Proof. exact (MK_COMB (@lem6014447 A B v u f op) (@lem6014451 A B v u f op)). Qed.
Lemma lem6014453 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6014454 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term174 A B v u f op) = (term175 A B v u f op).
Proof. exact (MK_COMB (@lem6014453) (@lem6014452 A B v u f op)). Qed.
Lemma lem6014455 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term158 A B v u f op x) = (term138 A B v u f x op).
Proof. exact (eq_refl (term158 A B v u f op x)). Qed.
Lemma lem6014456 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6014457 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term159 A B v u f op x) = (term140 A B v u f x op).
Proof. exact (MK_COMB (@lem6014456) (@lem6014455 A B v u f x op)). Qed.
Lemma lem6014458 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term160 A B v u f op x) = (term135 A B v u f x op).
Proof. exact (eq_refl (term160 A B v u f op x)). Qed.
Lemma lem6014459 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term161 A B v u f op x) = (term142 A B v u f x op).
Proof. exact (MK_COMB (@lem6014457 A B v u f x op) (@lem6014458 A B v u f x op)). Qed.
Lemma lem6014460 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term162 A B v u f op) = (term150 A B v u f op).
Proof. exact (fun_ext (fun x : A => @lem6014459 A B v u f x op)). Qed.
Lemma lem6014461 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6014462 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term154 A B v u f op) = (term151 A B v u f op).
Proof. exact (MK_COMB (@lem6014461 A) (@lem6014460 A B v u f op)). Qed.
Lemma lem6014463 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : ((term155 A B v u f op) = (term154 A B v u f op)) = ((term173 A B v u f op) = (term151 A B v u f op)).
Proof. exact (MK_COMB (@lem6014454 A B v u f op) (@lem6014462 A B v u f op)). Qed.
Lemma lem6014464 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term173 A B v u f op) = (term151 A B v u f op).
Proof. exact (EQ_MP (@lem6014463 A B v u f op) (@lem6014441 A B v u f op)). Qed.
Lemma lem6014465 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term151 A B v u f op) = (term151 A B v u f op).
Proof. exact (TRANS (@lem6014341 A B v u f op) (@lem6014464 A B v u f op)). Qed.
Lemma lem6014466 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term70 A B v u f op) = (term151 A B v u f op).
Proof. exact (TRANS (@lem6014314 A B v u f op) (@lem6014465 A B v u f op)). Qed.
Lemma lem6014467 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term70 A B v u f op) : term151 A B v u f op.
Proof. exact (EQ_MP (@lem6014466 A B v u f op) (@lem6014181 A B v u f op h1)). Qed.
Lemma lem6014478 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term176 A s x t) = (term124 A s x t).
Proof. exact (@lem17362 (@IN A x s) (@IN A x t)). Qed.
Lemma lem6014483 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term105 A s x t) = (term117 A s x t).
Proof. exact (@lem17265 (@IN A x s) (@IN A x t)). Qed.
Lemma lem6014484 {A : Type'} (P : A -> Prop) : (term144 A P) = (term145 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem6014485 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term177 A s t) = (term178 A s t).
Proof. exact (@lem6014484 A (term106 A s t)). Qed.
Lemma lem6014486 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term179 A s t x) = (term105 A s x t).
Proof. exact (eq_refl (term179 A s t x)). Qed.
Lemma lem6014487 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6014488 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term180 A s t x) = (term176 A s x t).
Proof. exact (MK_COMB (@lem6014487) (@lem6014486 A s x t)). Qed.
Lemma lem6014489 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term180 A s t x) = (term124 A s x t).
Proof. exact (TRANS (@lem6014488 A s x t) (@lem6014478 A s x t)). Qed.
Lemma lem6014490 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term181 A s t) = (term182 A s t).
Proof. exact (fun_ext (fun x : A => @lem6014489 A s x t)). Qed.
Lemma lem6014491 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6014492 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term178 A s t) = (term183 A s t).
Proof. exact (MK_COMB (@lem6014491 A) (@lem6014490 A s t)). Qed.
Lemma lem6014493 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term177 A s t) = (term183 A s t).
Proof. exact (TRANS (@lem6014485 A s t) (@lem6014492 A s t)). Qed.
Lemma lem6014494 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term106 A s t) = (term184 A s t).
Proof. exact (fun_ext (fun x : A => @lem6014483 A s x t)). Qed.
Lemma lem6014495 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6014496 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term107 A s t) = (term185 A s t).
Proof. exact (MK_COMB (@lem6014495 A) (@lem6014494 A s t)). Qed.
Lemma lem6014498 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term186 A s t) = (term186 A s t).
Proof. exact (eq_refl (term186 A s t)). Qed.
Lemma lem6014499 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term187 A s t) = (term188 A s t).
Proof. exact (MK_COMB (@lem6014498 A s t) (@lem6014496 A s t)). Qed.
Lemma lem6014501 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term189 A s t) = (term189 A s t).
Proof. exact (eq_refl (term189 A s t)). Qed.
Lemma lem6014502 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term190 A s t) = (term191 A s t).
Proof. exact (MK_COMB (@lem6014501 A s t) (@lem6014493 A s t)). Qed.
Lemma lem6014503 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6014504 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term192 A s t) = (term193 A s t).
Proof. exact (MK_COMB (@lem6014503) (@lem6014502 A s t)). Qed.
Lemma lem6014505 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term194 A s t) = (term195 A s t).
Proof. exact (MK_COMB (@lem6014504 A s t) (@lem6014499 A s t)). Qed.
Lemma lem6014506 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((@SUBSET A s t) = (term107 A s t)) = (term194 A s t).
Proof. exact (@lem17784 (@SUBSET A s t) (term107 A s t)). Qed.
Lemma lem6014507 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((@SUBSET A s t) = (term107 A s t)) = (term195 A s t).
Proof. exact (TRANS (@lem6014506 A s t) (@lem6014505 A s t)). Qed.
Lemma lem6014508 {A : Type'} (s : A -> Prop) : (term109 A s) = (term196 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6014507 A s t)). Qed.
Lemma lem6014509 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6014510 {A : Type'} (s : A -> Prop) : (term110 A s) = (term197 A s).
Proof. exact (MK_COMB (@lem6014509 A) (@lem6014508 A s)). Qed.
Lemma lem6014511 {A : Type'} : (term111 A) = (term198 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6014510 A s)). Qed.
Lemma lem6014512 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6014513 {A : Type'} : (term71 A) = (term199 A).
Proof. exact (MK_COMB (@lem6014512 A) (@lem6014511 A)). Qed.
Lemma lem6014519 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term200 A P Q) = (term201 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6014520 {A : Type'} (P : type686 A) (Q : type686 A) : (term202 A P Q) = (term203 A P Q).
Proof. exact (@lem6014519 (A -> Prop) P Q). Qed.
Lemma lem6014521 {A : Type'} (s : A -> Prop) : (term204 A s) = (term205 A s).
Proof. exact (@lem6014520 A (term206 A s) (term207 A s)). Qed.
Lemma lem6014522 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term208 A s t) = (term191 A s t).
Proof. exact (eq_refl (term208 A s t)). Qed.
Lemma lem6014523 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6014524 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term209 A s t) = (term193 A s t).
Proof. exact (MK_COMB (@lem6014523) (@lem6014522 A s t)). Qed.
Lemma lem6014525 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term210 A s t) = (term188 A s t).
Proof. exact (eq_refl (term210 A s t)). Qed.
Lemma lem6014526 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term211 A s t) = (term195 A s t).
Proof. exact (MK_COMB (@lem6014524 A s t) (@lem6014525 A s t)). Qed.
Lemma lem6014527 {A : Type'} (s : A -> Prop) : (term212 A s) = (term196 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6014526 A s t)). Qed.
Lemma lem6014528 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6014529 {A : Type'} (s : A -> Prop) : (term204 A s) = (term197 A s).
Proof. exact (MK_COMB (@lem6014528 A) (@lem6014527 A s)). Qed.
Lemma lem6014530 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6014531 {A : Type'} (s : A -> Prop) : (term213 A s) = (term214 A s).
Proof. exact (MK_COMB (@lem6014530) (@lem6014529 A s)). Qed.
Lemma lem6014532 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term208 A s t) = (term191 A s t).
Proof. exact (eq_refl (term208 A s t)). Qed.
Lemma lem6014533 {A : Type'} (s : A -> Prop) : (term215 A s) = (term206 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6014532 A s t)). Qed.
Lemma lem6014534 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6014535 {A : Type'} (s : A -> Prop) : (term216 A s) = (term217 A s).
Proof. exact (MK_COMB (@lem6014534 A) (@lem6014533 A s)). Qed.
Lemma lem6014536 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6014537 {A : Type'} (s : A -> Prop) : (term218 A s) = (term219 A s).
Proof. exact (MK_COMB (@lem6014536) (@lem6014535 A s)). Qed.
Lemma lem6014538 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term210 A s t) = (term188 A s t).
Proof. exact (eq_refl (term210 A s t)). Qed.
Lemma lem6014539 {A : Type'} (s : A -> Prop) : (term220 A s) = (term207 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6014538 A s t)). Qed.
Lemma lem6014540 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6014541 {A : Type'} (s : A -> Prop) : (term221 A s) = (term222 A s).
Proof. exact (MK_COMB (@lem6014540 A) (@lem6014539 A s)). Qed.
Lemma lem6014542 {A : Type'} (s : A -> Prop) : (term205 A s) = (term223 A s).
Proof. exact (MK_COMB (@lem6014537 A s) (@lem6014541 A s)). Qed.
Lemma lem6014543 {A : Type'} (s : A -> Prop) : ((term204 A s) = (term205 A s)) = ((term197 A s) = (term223 A s)).
Proof. exact (MK_COMB (@lem6014531 A s) (@lem6014542 A s)). Qed.
Lemma lem6014544 {A : Type'} (s : A -> Prop) : (term197 A s) = (term223 A s).
Proof. exact (EQ_MP (@lem6014543 A s) (@lem6014521 A s)). Qed.
Lemma lem6014737 {A : Type'} : (term198 A) = (term224 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6014544 A s)). Qed.
Lemma lem6014738 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6014739 {A : Type'} : (term199 A) = (term225 A).
Proof. exact (MK_COMB (@lem6014738 A) (@lem6014737 A)). Qed.
Lemma lem6014741 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term200 A P Q) = (term201 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6014742 {A : Type'} (P : type686 A) (Q : type686 A) : (term202 A P Q) = (term203 A P Q).
Proof. exact (@lem6014741 (A -> Prop) P Q). Qed.
Lemma lem6014743 {A : Type'} : (term226 A) = (term227 A).
Proof. exact (@lem6014742 A (term228 A) (term229 A)). Qed.
Lemma lem6014744 {A : Type'} (s : A -> Prop) : (term230 A s) = (term217 A s).
Proof. exact (eq_refl (term230 A s)). Qed.
Lemma lem6014745 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6014746 {A : Type'} (s : A -> Prop) : (term231 A s) = (term219 A s).
Proof. exact (MK_COMB (@lem6014745) (@lem6014744 A s)). Qed.
Lemma lem6014747 {A : Type'} (s : A -> Prop) : (term232 A s) = (term222 A s).
Proof. exact (eq_refl (term232 A s)). Qed.
Lemma lem6014748 {A : Type'} (s : A -> Prop) : (term233 A s) = (term223 A s).
Proof. exact (MK_COMB (@lem6014746 A s) (@lem6014747 A s)). Qed.
Lemma lem6014749 {A : Type'} : (term234 A) = (term224 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6014748 A s)). Qed.
Lemma lem6014750 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6014751 {A : Type'} : (term226 A) = (term225 A).
Proof. exact (MK_COMB (@lem6014750 A) (@lem6014749 A)). Qed.
Lemma lem6014752 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6014753 {A : Type'} : (term235 A) = (term236 A).
Proof. exact (MK_COMB (@lem6014752) (@lem6014751 A)). Qed.
Lemma lem6014754 {A : Type'} (s : A -> Prop) : (term230 A s) = (term217 A s).
Proof. exact (eq_refl (term230 A s)). Qed.
Lemma lem6014755 {A : Type'} : (term237 A) = (term228 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6014754 A s)). Qed.
Lemma lem6014756 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6014757 {A : Type'} : (term238 A) = (term239 A).
Proof. exact (MK_COMB (@lem6014756 A) (@lem6014755 A)). Qed.
Lemma lem6014758 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6014759 {A : Type'} : (term240 A) = (term241 A).
Proof. exact (MK_COMB (@lem6014758) (@lem6014757 A)). Qed.
Lemma lem6014760 {A : Type'} (s : A -> Prop) : (term232 A s) = (term222 A s).
Proof. exact (eq_refl (term232 A s)). Qed.
Lemma lem6014761 {A : Type'} : (term242 A) = (term229 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6014760 A s)). Qed.
Lemma lem6014762 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6014763 {A : Type'} : (term243 A) = (term244 A).
Proof. exact (MK_COMB (@lem6014762 A) (@lem6014761 A)). Qed.
Lemma lem6014764 {A : Type'} : (term227 A) = (term245 A).
Proof. exact (MK_COMB (@lem6014759 A) (@lem6014763 A)). Qed.
Lemma lem6014765 {A : Type'} : ((term226 A) = (term227 A)) = ((term225 A) = (term245 A)).
Proof. exact (MK_COMB (@lem6014753 A) (@lem6014764 A)). Qed.
Lemma lem6014766 {A : Type'} : (term225 A) = (term245 A).
Proof. exact (EQ_MP (@lem6014765 A) (@lem6014743 A)). Qed.
Lemma lem6014967 {A : Type'} : (term199 A) = (term245 A).
Proof. exact (TRANS (@lem6014739 A) (@lem6014766 A)). Qed.
Lemma lem6014969 {A : Type'} (P : Prop) (Q : A -> Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6014970 {A : Type'} (P : Prop) (Q : A -> Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (@lem6014969 A P Q). Qed.
Lemma lem6014971 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term248 A s t) = (term249 A s t).
Proof. exact (@lem6014970 A (@SUBSET A s t) (term182 A s t)). Qed.
Lemma lem6014972 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term250 A s t x) = (term124 A s x t).
Proof. exact (eq_refl (term250 A s t x)). Qed.
Lemma lem6014973 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term251 A s t) = (term182 A s t).
Proof. exact (fun_ext (fun x : A => @lem6014972 A s x t)). Qed.
Lemma lem6014974 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6014975 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term252 A s t) = (term183 A s t).
Proof. exact (MK_COMB (@lem6014974 A) (@lem6014973 A s t)). Qed.
Lemma lem6014976 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term189 A s t) = (term189 A s t).
Proof. exact (eq_refl (term189 A s t)). Qed.
Lemma lem6014977 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term248 A s t) = (term191 A s t).
Proof. exact (MK_COMB (@lem6014976 A s t) (@lem6014975 A s t)). Qed.
Lemma lem6014978 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6014979 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term253 A s t) = (term254 A s t).
Proof. exact (MK_COMB (@lem6014978) (@lem6014977 A s t)). Qed.
Lemma lem6014980 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term250 A s t x) = (term124 A s x t).
Proof. exact (eq_refl (term250 A s t x)). Qed.
Lemma lem6014981 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term189 A s t) = (term189 A s t).
Proof. exact (eq_refl (term189 A s t)). Qed.
Lemma lem6014982 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term255 A s t x) = (term256 A s x t).
Proof. exact (MK_COMB (@lem6014981 A s t) (@lem6014980 A s x t)). Qed.
Lemma lem6014983 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term257 A s t) = (term258 A s t).
Proof. exact (fun_ext (fun x : A => @lem6014982 A s x t)). Qed.
Lemma lem6014984 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6014985 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term249 A s t) = (term259 A s t).
Proof. exact (MK_COMB (@lem6014984 A) (@lem6014983 A s t)). Qed.
Lemma lem6014986 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term248 A s t) = (term249 A s t)) = ((term191 A s t) = (term259 A s t)).
Proof. exact (MK_COMB (@lem6014979 A s t) (@lem6014985 A s t)). Qed.
Lemma lem6014987 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term191 A s t) = (term259 A s t).
Proof. exact (EQ_MP (@lem6014986 A s t) (@lem6014971 A s t)). Qed.
Lemma lem6014988 {A : Type'} (s : A -> Prop) : (term206 A s) = (term260 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6014987 A s t)). Qed.
Lemma lem6014989 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6014990 {A : Type'} (s : A -> Prop) : (term217 A s) = (term261 A s).
Proof. exact (MK_COMB (@lem6014989 A) (@lem6014988 A s)). Qed.
Lemma lem6014992 {A B : Type'} (P : type1413 A B) : (term262 A B P) = (term263 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6014993 {A : Type'} (P : type672 A) : (term264 A P) = (term265 A P).
Proof. exact (@lem6014992 (A -> Prop) A P). Qed.
Lemma lem6014994 {A : Type'} (s : A -> Prop) : (term266 A s) = (term267 A s).
Proof. exact (@lem6014993 A (term268 A s)). Qed.
Lemma lem6014995 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term269 A s t) = (term258 A s t).
Proof. exact (eq_refl (term269 A s t)). Qed.
Lemma lem6014996 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6014997 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term270 A s t x) = (term271 A s t x).
Proof. exact (MK_COMB (@lem6014995 A s t) (@lem6014996 A x)). Qed.
Lemma lem6014998 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term271 A s t x) = (term256 A s x t).
Proof. exact (eq_refl (term271 A s t x)). Qed.
Lemma lem6014999 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term270 A s t x) = (term256 A s x t).
Proof. exact (TRANS (@lem6014997 A s t x) (@lem6014998 A s x t)). Qed.
Lemma lem6015000 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term272 A s t) = (term258 A s t).
Proof. exact (fun_ext (fun x : A => @lem6014999 A s x t)). Qed.
Lemma lem6015001 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6015002 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term273 A s t) = (term259 A s t).
Proof. exact (MK_COMB (@lem6015001 A) (@lem6015000 A s t)). Qed.
Lemma lem6015003 {A : Type'} (s : A -> Prop) : (term274 A s) = (term260 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6015002 A s t)). Qed.
Lemma lem6015004 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6015005 {A : Type'} (s : A -> Prop) : (term266 A s) = (term261 A s).
Proof. exact (MK_COMB (@lem6015004 A) (@lem6015003 A s)). Qed.
Lemma lem6015006 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6015007 {A : Type'} (s : A -> Prop) : (term275 A s) = (term276 A s).
Proof. exact (MK_COMB (@lem6015006) (@lem6015005 A s)). Qed.
Lemma lem6015008 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term269 A s t) = (term258 A s t).
Proof. exact (eq_refl (term269 A s t)). Qed.
Lemma lem6015009 {A : Type'} (x : type684 A) (t : A -> Prop) : (x t) = (x t).
Proof. exact (eq_refl (x t)). Qed.
Lemma lem6015010 {A : Type'} (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term277 A s x t) = (term278 A s x t).
Proof. exact (MK_COMB (@lem6015008 A s t) (@lem6015009 A x t)). Qed.
Lemma lem6015011 {A : Type'} (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term278 A s x t) = (term279 A s x t).
Proof. exact (eq_refl (term278 A s x t)). Qed.
Lemma lem6015012 {A : Type'} (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term277 A s x t) = (term279 A s x t).
Proof. exact (TRANS (@lem6015010 A s x t) (@lem6015011 A s x t)). Qed.
Lemma lem6015013 {A : Type'} (s : A -> Prop) (x : type684 A) : (term280 A s x) = (term281 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6015012 A s x t)). Qed.
Lemma lem6015014 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6015015 {A : Type'} (s : A -> Prop) (x : type684 A) : (term282 A s x) = (term283 A s x).
Proof. exact (MK_COMB (@lem6015014 A) (@lem6015013 A s x)). Qed.
Lemma lem6015016 {A : Type'} (s : A -> Prop) : (term284 A s) = (term285 A s).
Proof. exact (fun_ext (fun x : type684 A => @lem6015015 A s x)). Qed.
Lemma lem6015017 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem6015018 {A : Type'} (s : A -> Prop) : (term267 A s) = (term286 A s).
Proof. exact (MK_COMB (@lem6015017 A) (@lem6015016 A s)). Qed.
Lemma lem6015019 {A : Type'} (s : A -> Prop) : ((term266 A s) = (term267 A s)) = ((term261 A s) = (term286 A s)).
Proof. exact (MK_COMB (@lem6015007 A s) (@lem6015018 A s)). Qed.
Lemma lem6015020 {A : Type'} (s : A -> Prop) : (term261 A s) = (term286 A s).
Proof. exact (EQ_MP (@lem6015019 A s) (@lem6014994 A s)). Qed.
Lemma lem6015021 {A : Type'} (s : A -> Prop) : (term217 A s) = (term286 A s).
Proof. exact (TRANS (@lem6014990 A s) (@lem6015020 A s)). Qed.
Lemma lem6015022 {A : Type'} : (term228 A) = (term287 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6015021 A s)). Qed.
Lemma lem6015023 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6015024 {A : Type'} : (term239 A) = (term288 A).
Proof. exact (MK_COMB (@lem6015023 A) (@lem6015022 A)). Qed.
Lemma lem6015026 {A B : Type'} (P : type1413 A B) : (term262 A B P) = (term263 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6015027 {A : Type'} (P : type597 A) : (term289 A P) = (term290 A P).
Proof. exact (@lem6015026 (A -> Prop) (type684 A) P). Qed.
Lemma lem6015028 {A : Type'} : (term291 A) = (term292 A).
Proof. exact (@lem6015027 A (term293 A)). Qed.
Lemma lem6015029 {A : Type'} (s : A -> Prop) : (term294 A s) = (term285 A s).
Proof. exact (eq_refl (term294 A s)). Qed.
Lemma lem6015030 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6015031 {A : Type'} (s : A -> Prop) (x : type684 A) : (term295 A s x) = (term296 A s x).
Proof. exact (MK_COMB (@lem6015029 A s) (@lem6015030 A x)). Qed.
Lemma lem6015032 {A : Type'} (s : A -> Prop) (x : type684 A) : (term296 A s x) = (term283 A s x).
Proof. exact (eq_refl (term296 A s x)). Qed.
Lemma lem6015033 {A : Type'} (s : A -> Prop) (x : type684 A) : (term295 A s x) = (term283 A s x).
Proof. exact (TRANS (@lem6015031 A s x) (@lem6015032 A s x)). Qed.
Lemma lem6015034 {A : Type'} (s : A -> Prop) : (term297 A s) = (term285 A s).
Proof. exact (fun_ext (fun x : type684 A => @lem6015033 A s x)). Qed.
Lemma lem6015035 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem6015036 {A : Type'} (s : A -> Prop) : (term298 A s) = (term286 A s).
Proof. exact (MK_COMB (@lem6015035 A) (@lem6015034 A s)). Qed.
Lemma lem6015037 {A : Type'} : (term299 A) = (term287 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6015036 A s)). Qed.
Lemma lem6015038 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6015039 {A : Type'} : (term291 A) = (term288 A).
Proof. exact (MK_COMB (@lem6015038 A) (@lem6015037 A)). Qed.
Lemma lem6015040 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6015041 {A : Type'} : (term300 A) = (term301 A).
Proof. exact (MK_COMB (@lem6015040) (@lem6015039 A)). Qed.
Lemma lem6015042 {A : Type'} (s : A -> Prop) : (term294 A s) = (term285 A s).
Proof. exact (eq_refl (term294 A s)). Qed.
Lemma lem6015043 {A : Type'} (x : type638 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem6015044 {A : Type'} (x : type638 A) (s : A -> Prop) : (term302 A x s) = (term303 A x s).
Proof. exact (MK_COMB (@lem6015042 A s) (@lem6015043 A x s)). Qed.
Lemma lem6015045 {A : Type'} (x : type638 A) (s : A -> Prop) : (term303 A x s) = (term304 A x s).
Proof. exact (eq_refl (term303 A x s)). Qed.
Lemma lem6015046 {A : Type'} (x : type638 A) (s : A -> Prop) : (term302 A x s) = (term304 A x s).
Proof. exact (TRANS (@lem6015044 A x s) (@lem6015045 A x s)). Qed.
Lemma lem6015047 {A : Type'} (x : type638 A) : (term305 A x) = (term306 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6015046 A x s)). Qed.
Lemma lem6015048 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6015049 {A : Type'} (x : type638 A) : (term307 A x) = (term308 A x).
Proof. exact (MK_COMB (@lem6015048 A) (@lem6015047 A x)). Qed.
Lemma lem6015050 {A : Type'} : (term309 A) = (term310 A).
Proof. exact (fun_ext (fun x : type638 A => @lem6015049 A x)). Qed.
Lemma lem6015051 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem6015052 {A : Type'} : (term292 A) = (term311 A).
Proof. exact (MK_COMB (@lem6015051 A) (@lem6015050 A)). Qed.
Lemma lem6015053 {A : Type'} : ((term291 A) = (term292 A)) = ((term288 A) = (term311 A)).
Proof. exact (MK_COMB (@lem6015041 A) (@lem6015052 A)). Qed.
Lemma lem6015054 {A : Type'} : (term288 A) = (term311 A).
Proof. exact (EQ_MP (@lem6015053 A) (@lem6015028 A)). Qed.
Lemma lem6015055 {A : Type'} : (term239 A) = (term311 A).
Proof. exact (TRANS (@lem6015024 A) (@lem6015054 A)). Qed.
Lemma lem6015056 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6015057 {A : Type'} : (term241 A) = (term312 A).
Proof. exact (MK_COMB (@lem6015056) (@lem6015055 A)). Qed.
Lemma lem6015058 {A : Type'} : (term244 A) = (term244 A).
Proof. exact (eq_refl (term244 A)). Qed.
Lemma lem6015059 {A : Type'} : (term245 A) = (term313 A).
Proof. exact (MK_COMB (@lem6015057 A) (@lem6015058 A)). Qed.
Lemma lem6015061 {A : Type'} (P : A -> Prop) (Q : Prop) : (term314 A P Q) = (term315 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6015062 {A : Type'} (P : type139 A) (Q : Prop) : (term316 A P Q) = (term317 A P Q).
Proof. exact (@lem6015061 (type638 A) P Q). Qed.
Lemma lem6015063 {A : Type'} : (term318 A) = (term319 A).
Proof. exact (@lem6015062 A (term310 A) (term244 A)). Qed.
Lemma lem6015064 {A : Type'} (x : type638 A) : (term320 A x) = (term308 A x).
Proof. exact (eq_refl (term320 A x)). Qed.
Lemma lem6015065 {A : Type'} : (term321 A) = (term310 A).
Proof. exact (fun_ext (fun x : type638 A => @lem6015064 A x)). Qed.
Lemma lem6015066 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem6015067 {A : Type'} : (term322 A) = (term311 A).
Proof. exact (MK_COMB (@lem6015066 A) (@lem6015065 A)). Qed.
Lemma lem6015068 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6015069 {A : Type'} : (term323 A) = (term312 A).
Proof. exact (MK_COMB (@lem6015068) (@lem6015067 A)). Qed.
Lemma lem6015070 {A : Type'} : (term244 A) = (term244 A).
Proof. exact (eq_refl (term244 A)). Qed.
Lemma lem6015071 {A : Type'} : (term318 A) = (term313 A).
Proof. exact (MK_COMB (@lem6015069 A) (@lem6015070 A)). Qed.
Lemma lem6015072 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6015073 {A : Type'} : (term324 A) = (term325 A).
Proof. exact (MK_COMB (@lem6015072) (@lem6015071 A)). Qed.
Lemma lem6015074 {A : Type'} (x : type638 A) : (term320 A x) = (term308 A x).
Proof. exact (eq_refl (term320 A x)). Qed.
Lemma lem6015075 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6015076 {A : Type'} (x : type638 A) : (term326 A x) = (term327 A x).
Proof. exact (MK_COMB (@lem6015075) (@lem6015074 A x)). Qed.
Lemma lem6015077 {A : Type'} : (term244 A) = (term244 A).
Proof. exact (eq_refl (term244 A)). Qed.
Lemma lem6015078 {A : Type'} (x : type638 A) : (term328 A x) = (term329 A x).
Proof. exact (MK_COMB (@lem6015076 A x) (@lem6015077 A)). Qed.
Lemma lem6015079 {A : Type'} : (term330 A) = (term331 A).
Proof. exact (fun_ext (fun x : type638 A => @lem6015078 A x)). Qed.
Lemma lem6015080 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem6015081 {A : Type'} : (term319 A) = (term332 A).
Proof. exact (MK_COMB (@lem6015080 A) (@lem6015079 A)). Qed.
Lemma lem6015082 {A : Type'} : ((term318 A) = (term319 A)) = ((term313 A) = (term332 A)).
Proof. exact (MK_COMB (@lem6015073 A) (@lem6015081 A)). Qed.
Lemma lem6015083 {A : Type'} : (term313 A) = (term332 A).
Proof. exact (EQ_MP (@lem6015082 A) (@lem6015063 A)). Qed.
Lemma lem6015084 {A : Type'} : (term245 A) = (term332 A).
Proof. exact (TRANS (@lem6015059 A) (@lem6015083 A)). Qed.
Lemma lem6015085 {A : Type'} : (term199 A) = (term332 A).
Proof. exact (TRANS (@lem6014967 A) (@lem6015084 A)). Qed.
Lemma lem6015086 {A : Type'} : (term71 A) = (term332 A).
Proof. exact (TRANS (@lem6014513 A) (@lem6015085 A)). Qed.
Lemma lem6015087 {A : Type'} (h1 : term71 A) : term332 A.
Proof. exact (EQ_MP (@lem6015086 A) (@lem6014182 A h1)). Qed.
Lemma lem6015088 {A : Type'} (x : type638 A) (h1 : term329 A x) : term329 A x.
Proof. exact (h1). Qed.
Lemma lem6015099 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @SUBSET A u v) : @SUBSET A u v.
Proof. exact (h1). Qed.
Lemma lem6015126 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term123 A B v u f x op) = (term123 A B v u f x op).
Proof. exact (eq_refl (term123 A B v u f x op)). Qed.
Lemma lem6015127 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term125 A B v u f op) = (term125 A B v u f op).
Proof. exact (fun_ext (fun x : A => @lem6015126 A B v u f x op)). Qed.
Lemma lem6015128 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6015129 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term126 A B v u f op) = (term126 A B v u f op).
Proof. exact (MK_COMB (@lem6015128 A) (@lem6015127 A B v u f op)). Qed.
Lemma lem6015130 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term39 A B v u f op) : term126 A B v u f op.
Proof. exact (EQ_MP (@lem6015129 A B v u f op) (@lem6014265 A B v u f op h1)). Qed.
Lemma lem6015145 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term117 A s x t) = (term117 A s x t).
Proof. exact (eq_refl (term117 A s x t)). Qed.
Lemma lem6015146 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term184 A s t) = (term184 A s t).
Proof. exact (fun_ext (fun x : A => @lem6015145 A s x t)). Qed.
Lemma lem6015147 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6015148 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term185 A s t) = (term185 A s t).
Proof. exact (MK_COMB (@lem6015147 A) (@lem6015146 A s t)). Qed.
Lemma lem6015157 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term186 A s t) = (term186 A s t).
Proof. exact (eq_refl (term186 A s t)). Qed.
Lemma lem6015158 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term188 A s t) = (term188 A s t).
Proof. exact (MK_COMB (@lem6015157 A s t) (@lem6015148 A s t)). Qed.
Lemma lem6015159 {A : Type'} (s : A -> Prop) : (term207 A s) = (term207 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6015158 A s t)). Qed.
Lemma lem6015160 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6015161 {A : Type'} (s : A -> Prop) : (term222 A s) = (term222 A s).
Proof. exact (MK_COMB (@lem6015160 A) (@lem6015159 A s)). Qed.
Lemma lem6015162 {A : Type'} : (term229 A) = (term229 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6015161 A s)). Qed.
Lemma lem6015163 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6015164 {A : Type'} : (term244 A) = (term244 A).
Proof. exact (MK_COMB (@lem6015163 A) (@lem6015162 A)). Qed.
Lemma lem6015195 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (term333 A x s t) = (term333 A x s t).
Proof. exact (eq_refl (term333 A x s t)). Qed.
Lemma lem6015196 {A : Type'} (x : type638 A) (s : A -> Prop) : (term334 A x s) = (term334 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6015195 A x s t)). Qed.
Lemma lem6015197 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6015198 {A : Type'} (x : type638 A) (s : A -> Prop) : (term304 A x s) = (term304 A x s).
Proof. exact (MK_COMB (@lem6015197 A) (@lem6015196 A x s)). Qed.
Lemma lem6015199 {A : Type'} (x : type638 A) : (term306 A x) = (term306 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6015198 A x s)). Qed.
Lemma lem6015200 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6015201 {A : Type'} (x : type638 A) : (term308 A x) = (term308 A x).
Proof. exact (MK_COMB (@lem6015200 A) (@lem6015199 A x)). Qed.
Lemma lem6015202 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6015203 {A : Type'} (x : type638 A) : (term327 A x) = (term327 A x).
Proof. exact (MK_COMB (@lem6015202) (@lem6015201 A x)). Qed.
Lemma lem6015204 {A : Type'} (x : type638 A) : (term329 A x) = (term329 A x).
Proof. exact (MK_COMB (@lem6015203 A x) (@lem6015164 A)). Qed.
Lemma lem6015205 {A : Type'} (x : type638 A) (h1 : term329 A x) : term329 A x.
Proof. exact (EQ_MP (@lem6015204 A x) (@lem6015088 A x h1)). Qed.
Lemma lem6015291 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term142 A B v u f x' op) : term142 A B v u f x' op.
Proof. exact (h1). Qed.
Lemma lem6015292 {A : Type'} (x : type638 A) (h1 : term329 A x) : term244 A.
Proof. exact (proj2 (@lem6015205 A x h1)). Qed.
Lemma lem6015294 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term138 A B v u f x' op) : term138 A B v u f x' op.
Proof. exact (h1). Qed.
Lemma lem6015295 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term135 A B v u f x' op) : term135 A B v u f x' op.
Proof. exact (h1). Qed.
Lemma lem6015296 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term138 A B v u f x' op) : term129 A B u f x' op.
Proof. exact (proj2 (@lem6015294 A B v u f x' op h1)). Qed.
Lemma lem6015297 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term138 A B v u f x' op) : term49 A B v f x' op.
Proof. exact (proj1 (@lem6015294 A B v u f x' op h1)). Qed.
Lemma lem6015302 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term135 A B v u f x' op) : term49 A B u f x' op.
Proof. exact (proj2 (@lem6015295 A B v u f x' op h1)). Qed.
Lemma lem6015303 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term135 A B v u f x' op) : term129 A B v f x' op.
Proof. exact (proj1 (@lem6015295 A B v u f x' op h1)). Qed.
Lemma lem6015329 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term123 A B v u f x op) = (term123 A B v u f x op).
Proof. exact (eq_refl (term123 A B v u f x op)). Qed.
Lemma lem6015330 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term125 A B v u f op) = (term125 A B v u f op).
Proof. exact (fun_ext (fun x : A => @lem6015329 A B v u f x op)). Qed.
Lemma lem6015331 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6015333 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term126 A B v u f op) = (term126 A B v u f op).
Proof. exact (MK_COMB (@lem6015331 A) (@lem6015330 A B v u f op)). Qed.
Lemma lem6015334 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term39 A B v u f op) : term126 A B v u f op.
Proof. exact (EQ_MP (@lem6015333 A B v u f op) (@lem6015130 A B v u f op h1)). Qed.
Lemma lem6015422 {A : Type'} (x' : A) (u : A -> Prop) (h1 : term119 A x' u) : term119 A x' u.
Proof. exact (h1). Qed.
Lemma lem6015537 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (f x') = (@neutral B op)) : (f x') = (@neutral B op).
Proof. exact (h1). Qed.
Lemma lem6015545 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @SUBSET A u v) : @SUBSET A u v.
Proof. exact (h1). Qed.
Lemma lem6015592 {A : Type'} (P : Prop) (Q : A -> Prop) : (term335 A P Q) = (term336 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem6015593 {A : Type'} (P : Prop) (Q : A -> Prop) : (term335 A P Q) = (term336 A P Q).
Proof. exact (@lem6015592 A P Q). Qed.
Lemma lem6015594 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term337 A s t) = (term338 A s t).
Proof. exact (@lem6015593 A (term339 A s t) (term184 A s t)). Qed.
Lemma lem6015595 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term340 A s t x) = (term117 A s x t).
Proof. exact (eq_refl (term340 A s t x)). Qed.
Lemma lem6015596 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term341 A s t) = (term184 A s t).
Proof. exact (fun_ext (fun x : A => @lem6015595 A s x t)). Qed.
Lemma lem6015597 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6015598 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term342 A s t) = (term185 A s t).
Proof. exact (MK_COMB (@lem6015597 A) (@lem6015596 A s t)). Qed.
Lemma lem6015599 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term186 A s t) = (term186 A s t).
Proof. exact (eq_refl (term186 A s t)). Qed.
Lemma lem6015600 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term337 A s t) = (term188 A s t).
Proof. exact (MK_COMB (@lem6015599 A s t) (@lem6015598 A s t)). Qed.
Lemma lem6015601 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6015602 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term343 A s t) = (term344 A s t).
Proof. exact (MK_COMB (@lem6015601) (@lem6015600 A s t)). Qed.
Lemma lem6015603 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term340 A s t x) = (term117 A s x t).
Proof. exact (eq_refl (term340 A s t x)). Qed.
Lemma lem6015604 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term186 A s t) = (term186 A s t).
Proof. exact (eq_refl (term186 A s t)). Qed.
Lemma lem6015605 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term345 A s t x) = (term346 A s x t).
Proof. exact (MK_COMB (@lem6015604 A s t) (@lem6015603 A s x t)). Qed.
Lemma lem6015606 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term347 A s t) = (term348 A s t).
Proof. exact (fun_ext (fun x : A => @lem6015605 A s x t)). Qed.
Lemma lem6015607 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6015608 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term338 A s t) = (term349 A s t).
Proof. exact (MK_COMB (@lem6015607 A) (@lem6015606 A s t)). Qed.
Lemma lem6015609 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term337 A s t) = (term338 A s t)) = ((term188 A s t) = (term349 A s t)).
Proof. exact (MK_COMB (@lem6015602 A s t) (@lem6015608 A s t)). Qed.
Lemma lem6015610 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term188 A s t) = (term349 A s t).
Proof. exact (EQ_MP (@lem6015609 A s t) (@lem6015594 A s t)). Qed.
Lemma lem6015611 {A : Type'} (s : A -> Prop) : (term207 A s) = (term350 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6015610 A s t)). Qed.
Lemma lem6015612 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6015613 {A : Type'} (s : A -> Prop) : (term222 A s) = (term351 A s).
Proof. exact (MK_COMB (@lem6015612 A) (@lem6015611 A s)). Qed.
Lemma lem6015614 {A : Type'} : (term229 A) = (term352 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6015613 A s)). Qed.
Lemma lem6015615 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6015616 {A : Type'} : (term244 A) = (term353 A).
Proof. exact (MK_COMB (@lem6015615 A) (@lem6015614 A)). Qed.
Lemma lem6015629 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term346 A s x t) = (term346 A s x t).
Proof. exact (eq_refl (term346 A s x t)). Qed.
Lemma lem6015630 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term348 A s t) = (term348 A s t).
Proof. exact (fun_ext (fun x : A => @lem6015629 A s x t)). Qed.
Lemma lem6015631 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6015632 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term349 A s t) = (term349 A s t).
Proof. exact (MK_COMB (@lem6015631 A) (@lem6015630 A s t)). Qed.
Lemma lem6015633 {A : Type'} (s : A -> Prop) : (term350 A s) = (term350 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6015632 A s t)). Qed.
Lemma lem6015634 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6015635 {A : Type'} (s : A -> Prop) : (term351 A s) = (term351 A s).
Proof. exact (MK_COMB (@lem6015634 A) (@lem6015633 A s)). Qed.
Lemma lem6015636 {A : Type'} : (term352 A) = (term352 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6015635 A s)). Qed.
Lemma lem6015637 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6015638 {A : Type'} : (term353 A) = (term353 A).
Proof. exact (MK_COMB (@lem6015637 A) (@lem6015636 A)). Qed.
Lemma lem6015639 {A : Type'} : (term244 A) = (term353 A).
Proof. exact (TRANS (@lem6015616 A) (@lem6015638 A)). Qed.
Lemma lem6015640 {A : Type'} (x : type638 A) (h1 : term329 A x) : term353 A.
Proof. exact (EQ_MP (@lem6015639 A) (@lem6015292 A x h1)). Qed.
Lemma lem6015652 {A : Type'} (x' : A) (v : A -> Prop) (h1 : term119 A x' v) : term119 A x' v.
Proof. exact (h1). Qed.
Lemma lem6015767 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (f x') = (@neutral B op)) : (f x') = (@neutral B op).
Proof. exact (h1). Qed.
Lemma lem6015768 {A B : Type'} (_76643 : A) (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term39 A B v u f op) : term354 A B v u f op _76643.
Proof. exact (@lem6015334 A B v u f op h1 _76643). Qed.
Lemma lem6015769 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (_76643 : A) (op : type1400 B) : (term354 A B v u f op _76643) = (term123 A B v u f _76643 op).
Proof. exact (eq_refl (term354 A B v u f op _76643)). Qed.
Lemma lem6015770 {A B : Type'} (_76643 : A) (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term39 A B v u f op) : term123 A B v u f _76643 op.
Proof. exact (EQ_MP (@lem6015769 A B v u f _76643 op) (@lem6015768 A B _76643 v u f op h1)). Qed.
Lemma lem6015813 {A : Type'} (_76658 : A -> Prop) (x : type638 A) (h1 : term329 A x) : term355 A _76658.
Proof. exact (@lem6015640 A x h1 _76658). Qed.
Lemma lem6015814 {A : Type'} (_76658 : A -> Prop) : (term355 A _76658) = (term351 A _76658).
Proof. exact (eq_refl (term355 A _76658)). Qed.
Lemma lem6015815 {A : Type'} (_76658 : A -> Prop) (x : type638 A) (h1 : term329 A x) : term351 A _76658.
Proof. exact (EQ_MP (@lem6015814 A _76658) (@lem6015813 A _76658 x h1)). Qed.
Lemma lem6015816 {A : Type'} (_76658 : A -> Prop) (_76659 : A -> Prop) (x : type638 A) (h1 : term329 A x) : term356 A _76658 _76659.
Proof. exact (@lem6015815 A _76658 x h1 _76659). Qed.
Lemma lem6015817 {A : Type'} (_76658 : A -> Prop) (_76659 : A -> Prop) : (term356 A _76658 _76659) = (term349 A _76658 _76659).
Proof. exact (eq_refl (term356 A _76658 _76659)). Qed.
Lemma lem6015818 {A : Type'} (_76658 : A -> Prop) (_76659 : A -> Prop) (x : type638 A) (h1 : term329 A x) : term349 A _76658 _76659.
Proof. exact (EQ_MP (@lem6015817 A _76658 _76659) (@lem6015816 A _76658 _76659 x h1)). Qed.
Lemma lem6015819 {A : Type'} (_76658 : A -> Prop) (_76659 : A -> Prop) (_76660 : A) (x : type638 A) (h1 : term329 A x) : term357 A _76658 _76659 _76660.
Proof. exact (@lem6015818 A _76658 _76659 x h1 _76660). Qed.
Lemma lem6015820 {A : Type'} (_76658 : A -> Prop) (_76660 : A) (_76659 : A -> Prop) : (term357 A _76658 _76659 _76660) = (term346 A _76658 _76660 _76659).
Proof. exact (eq_refl (term357 A _76658 _76659 _76660)). Qed.
Lemma lem6015862 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (_76643 : A) (op : type1400 B) : (term123 A B v u f _76643 op) = (term358 A B v u f _76643 op).
Proof. exact (@lem6013671 (term119 A _76643 v) (@IN A _76643 u) ((f _76643) = (@neutral B op))). Qed.
Lemma lem6015863 {A B : Type'} (_76643 : A) (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term39 A B v u f op) : term358 A B v u f _76643 op.
Proof. exact (EQ_MP (@lem6015862 A B v u f _76643 op) (@lem6015770 A B _76643 v u f op h1)). Qed.
Lemma lem6015879 {A : Type'} (x' : A) (u : A -> Prop) (h1 : term119 A x' u) : term119 A x' u.
Proof. exact (h1). Qed.
Lemma lem6015921 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term138 A B v u f x' op) : term131 A B f x' op.
Proof. exact (proj2 (@lem6015297 A B v u f x' op h1)). Qed.
Lemma lem6015923 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (f x') = (@neutral B op)) : (f x') = (@neutral B op).
Proof. exact (h1). Qed.
Lemma lem6015939 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @SUBSET A u v) : @SUBSET A u v.
Proof. exact (h1). Qed.
Lemma lem6015961 {A : Type'} (_76658 : A -> Prop) (_76660 : A) (_76659 : A -> Prop) (x : type638 A) (h1 : term329 A x) : term346 A _76658 _76660 _76659.
Proof. exact (EQ_MP (@lem6015820 A _76658 _76660 _76659) (@lem6015819 A _76658 _76659 _76660 x h1)). Qed.
Lemma lem6015967 {A : Type'} (x' : A) (v : A -> Prop) (h1 : term119 A x' v) : term119 A x' v.
Proof. exact (h1). Qed.
Lemma lem6016009 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term135 A B v u f x' op) : term131 A B f x' op.
Proof. exact (proj2 (@lem6015302 A B v u f x' op h1)). Qed.
Lemma lem6016011 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (f x') = (@neutral B op)) : (f x') = (@neutral B op).
Proof. exact (h1). Qed.
Lemma lem6016114 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term138 A B v u f x' op) : @IN A x' v.
Proof. exact (proj1 (@lem6015297 A B v u f x' op h1)). Qed.
Lemma lem6016115 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term138 A B v u f x' op) : term359 A x' v.
Proof. exact (fun h0 : term119 A x' v => @lem6016114 A B v u f x' op h1). Qed.
Lemma lem6016117 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6016118 {A : Type'} (x' : A) (v : A -> Prop) : (term359 A x' v) = (@IN A x' v).
Proof. exact (@lem6016117 (@IN A x' v)). Qed.
Lemma lem6016119 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term138 A B v u f x' op) : @IN A x' v.
Proof. exact (EQ_MP (@lem6016118 A x' v) (@lem6016115 A B v u f x' op h1)). Qed.
Lemma lem6016121 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term138 A B v u f x' op) : term131 A B f x' op.
Proof. exact (proj2 (@lem6015297 A B v u f x' op h1)). Qed.
Lemma lem6016122 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term138 A B v u f x' op) : term361 A B f x' op.
Proof. exact (fun h0 : (f x') = (@neutral B op) => @lem6016121 A B v u f x' op h1). Qed.
Lemma lem6016124 (p : Prop) : (term362 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6016125 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : (term361 A B f x' op) = (term131 A B f x' op).
Proof. exact (@lem6016124 ((f x') = (@neutral B op))). Qed.
Lemma lem6016126 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term138 A B v u f x' op) : term131 A B f x' op.
Proof. exact (EQ_MP (@lem6016125 A B f x' op) (@lem6016122 A B v u f x' op h1)). Qed.
Lemma lem6016132 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6016133 {A B : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> B) (_76643 : A) (op : type1400 B) : (term358 A B v u f _76643 op) = (term363 A B u v f _76643 op).
Proof. exact (@lem6016132 (@IN A _76643 u) (term119 A _76643 v) ((f _76643) = (@neutral B op))). Qed.
Lemma lem6016147 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6016148 {A B : Type'} (f : A -> B) (op : type1400 B) (_76643 : A) (v : A -> Prop) : (term129 A B v f _76643 op) = (term364 A B f op _76643 v).
Proof. exact (@lem6016147 ((f _76643) = (@neutral B op)) (term119 A _76643 v)). Qed.
Lemma lem6016156 {A : Type'} (_76643 : A) (u : A -> Prop) : (term365 A _76643 u) = (term365 A _76643 u).
Proof. exact (eq_refl (term365 A _76643 u)). Qed.
Lemma lem6016157 {A B : Type'} (u : A -> Prop) (f : A -> B) (op : type1400 B) (_76643 : A) (v : A -> Prop) : (term363 A B u v f _76643 op) = (term366 A B u f op _76643 v).
Proof. exact (MK_COMB (@lem6016156 A _76643 u) (@lem6016148 A B f op _76643 v)). Qed.
Lemma lem6016161 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6016162 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (_76643 : A) (v : A -> Prop) : (term366 A B u f op _76643 v) = (term367 A B f op u _76643 v).
Proof. exact (@lem6016161 ((f _76643) = (@neutral B op)) (@IN A _76643 u) (term119 A _76643 v)). Qed.
Lemma lem6016180 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (_76643 : A) (v : A -> Prop) : (term363 A B u v f _76643 op) = (term367 A B f op u _76643 v).
Proof. exact (TRANS (@lem6016157 A B u f op _76643 v) (@lem6016162 A B f op u _76643 v)). Qed.
Lemma lem6016181 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (_76643 : A) (v : A -> Prop) : (term358 A B v u f _76643 op) = (term367 A B f op u _76643 v).
Proof. exact (TRANS (@lem6016133 A B u v f _76643 op) (@lem6016180 A B f op u _76643 v)). Qed.
Lemma lem6016182 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6016183 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (_76643 : A) (v : A -> Prop) : (term368 A B v u f _76643 op) = (term369 A B f op u _76643 v).
Proof. exact (MK_COMB (@lem6016182) (@lem6016181 A B f op u _76643 v)). Qed.
Lemma lem6016197 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6016198 {A B : Type'} (f : A -> B) (op : type1400 B) (_76643 : A) (v : A -> Prop) : (term129 A B v f _76643 op) = (term364 A B f op _76643 v).
Proof. exact (@lem6016197 ((f _76643) = (@neutral B op)) (term119 A _76643 v)). Qed.
Lemma lem6016206 {A : Type'} (_76643 : A) (u : A -> Prop) : (term365 A _76643 u) = (term365 A _76643 u).
Proof. exact (eq_refl (term365 A _76643 u)). Qed.
Lemma lem6016207 {A B : Type'} (u : A -> Prop) (f : A -> B) (op : type1400 B) (_76643 : A) (v : A -> Prop) : (term363 A B u v f _76643 op) = (term366 A B u f op _76643 v).
Proof. exact (MK_COMB (@lem6016206 A _76643 u) (@lem6016198 A B f op _76643 v)). Qed.
Lemma lem6016211 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6016212 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (_76643 : A) (v : A -> Prop) : (term366 A B u f op _76643 v) = (term367 A B f op u _76643 v).
Proof. exact (@lem6016211 ((f _76643) = (@neutral B op)) (@IN A _76643 u) (term119 A _76643 v)). Qed.
Lemma lem6016230 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (_76643 : A) (v : A -> Prop) : (term363 A B u v f _76643 op) = (term367 A B f op u _76643 v).
Proof. exact (TRANS (@lem6016207 A B u f op _76643 v) (@lem6016212 A B f op u _76643 v)). Qed.
Lemma lem6016231 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (_76643 : A) (v : A -> Prop) : ((term358 A B v u f _76643 op) = (term363 A B u v f _76643 op)) = ((term367 A B f op u _76643 v) = (term367 A B f op u _76643 v)).
Proof. exact (MK_COMB (@lem6016183 A B f op u _76643 v) (@lem6016230 A B f op u _76643 v)). Qed.
Lemma lem6016233 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6016234 (x : Prop) : (x = x) = True.
Proof. exact (@lem6016233 Prop x). Qed.
Lemma lem6016235 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (_76643 : A) (v : A -> Prop) : ((term367 A B f op u _76643 v) = (term367 A B f op u _76643 v)) = True.
Proof. exact (@lem6016234 (term367 A B f op u _76643 v)). Qed.
Lemma lem6016236 {A B : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> B) (_76643 : A) (op : type1400 B) : ((term358 A B v u f _76643 op) = (term363 A B u v f _76643 op)) = True.
Proof. exact (TRANS (@lem6016231 A B f op u _76643 v) (@lem6016235 A B f op u _76643 v)). Qed.
Lemma lem6016237 {A B : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> B) (_76643 : A) (op : type1400 B) : True = ((term358 A B v u f _76643 op) = (term363 A B u v f _76643 op)).
Proof. exact (SYM (@lem6016236 A B u v f _76643 op)). Qed.
Lemma lem6016238 {A B : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> B) (_76643 : A) (op : type1400 B) : (term358 A B v u f _76643 op) = (term363 A B u v f _76643 op).
Proof. exact (EQ_MP (@lem6016237 A B u v f _76643 op) (@lem0)). Qed.
Lemma lem6016239 {A B : Type'} (_76643 : A) (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term39 A B v u f op) : term363 A B u v f _76643 op.
Proof. exact (EQ_MP (@lem6016238 A B u v f _76643 op) (@lem6015863 A B _76643 v u f op h1)). Qed.
Lemma lem6016241 (b : Prop) (a : Prop) : (a \/ b) = (term370 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6016242 {A B : Type'} (v : A -> Prop) (f : A -> B) (op : type1400 B) (_76643 : A) (u : A -> Prop) : (term363 A B u v f _76643 op) = (term371 A B v f op _76643 u).
Proof. exact (@lem6016241 (term129 A B v f _76643 op) (@IN A _76643 u)). Qed.
Lemma lem6016244 (a : Prop) (b : Prop) : (term372 a b) = (term373 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6016245 {A B : Type'} (v : A -> Prop) (f : A -> B) (_76643 : A) (op : type1400 B) : (term374 A B v f _76643 op) = (term375 A B v f _76643 op).
Proof. exact (@lem6016244 (term119 A _76643 v) ((f _76643) = (@neutral B op))). Qed.
Lemma lem6016247 (a : Prop) : (term376 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6016248 {A : Type'} (_76643 : A) (v : A -> Prop) : (term114 A _76643 v) = (@IN A _76643 v).
Proof. exact (@lem6016247 (@IN A _76643 v)). Qed.
Lemma lem6016249 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6016250 {A : Type'} (_76643 : A) (v : A -> Prop) : (term377 A _76643 v) = (term378 A _76643 v).
Proof. exact (MK_COMB (@lem6016249) (@lem6016248 A _76643 v)). Qed.
Lemma lem6016251 {A B : Type'} (f : A -> B) (_76643 : A) (op : type1400 B) : (term131 A B f _76643 op) = (term131 A B f _76643 op).
Proof. exact (eq_refl (term131 A B f _76643 op)). Qed.
Lemma lem6016252 {A B : Type'} (v : A -> Prop) (f : A -> B) (_76643 : A) (op : type1400 B) : (term375 A B v f _76643 op) = (term49 A B v f _76643 op).
Proof. exact (MK_COMB (@lem6016250 A _76643 v) (@lem6016251 A B f _76643 op)). Qed.
Lemma lem6016253 {A B : Type'} (v : A -> Prop) (f : A -> B) (_76643 : A) (op : type1400 B) : (term374 A B v f _76643 op) = (term49 A B v f _76643 op).
Proof. exact (TRANS (@lem6016245 A B v f _76643 op) (@lem6016252 A B v f _76643 op)). Qed.
Lemma lem6016254 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6016255 {A B : Type'} (v : A -> Prop) (f : A -> B) (_76643 : A) (op : type1400 B) : (term379 A B v f _76643 op) = (term380 A B v f _76643 op).
Proof. exact (MK_COMB (@lem6016254) (@lem6016253 A B v f _76643 op)). Qed.
Lemma lem6016256 {A : Type'} (_76643 : A) (u : A -> Prop) : (@IN A _76643 u) = (@IN A _76643 u).
Proof. exact (eq_refl (@IN A _76643 u)). Qed.
Lemma lem6016257 {A B : Type'} (v : A -> Prop) (f : A -> B) (op : type1400 B) (_76643 : A) (u : A -> Prop) : (term371 A B v f op _76643 u) = (term381 A B v f op _76643 u).
Proof. exact (MK_COMB (@lem6016255 A B v f _76643 op) (@lem6016256 A _76643 u)). Qed.
Lemma lem6016258 {A B : Type'} (v : A -> Prop) (f : A -> B) (op : type1400 B) (_76643 : A) (u : A -> Prop) : (term363 A B u v f _76643 op) = (term381 A B v f op _76643 u).
Proof. exact (TRANS (@lem6016242 A B v f op _76643 u) (@lem6016257 A B v f op _76643 u)). Qed.
Lemma lem6016260 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term138 A B v u f x' op) : term49 A B v f x' op.
Proof. exact (conj (@lem6016119 A B v u f x' op h1) (@lem6016126 A B v u f x' op h1)). Qed.
Lemma lem6016262 {A B : Type'} (_76643 : A) (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term39 A B v u f op) : term381 A B v f op _76643 u.
Proof. exact (EQ_MP (@lem6016258 A B v f op _76643 u) (@lem6016239 A B _76643 v u f op h1)). Qed.
Lemma lem6016263 {A B : Type'} (_76643 : A) (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term39 A B v u f op) : term381 A B v f op _76643 u.
Proof. exact (@lem6016262 A B _76643 v u f op h1). Qed.
Lemma lem6016264 {A B : Type'} (x' : A) (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term39 A B v u f op) : term381 A B v f op x' u.
Proof. exact (@lem6016263 A B x' v u f op h1). Qed.
Lemma lem6016267 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term39 A B v u f op) (h2 : term138 A B v u f x' op) : @IN A x' u.
Proof. exact (@lem6016264 A B x' v u f op h1 (@lem6016260 A B v u f x' op h2)). Qed.
Lemma lem6016268 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term39 A B v u f op) (h2 : term138 A B v u f x' op) : term359 A x' u.
Proof. exact (fun h0 : term119 A x' u => @lem6016267 A B v u f x' op h1 h2). Qed.
Lemma lem6016270 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6016271 {A : Type'} (x' : A) (u : A -> Prop) : (term359 A x' u) = (@IN A x' u).
Proof. exact (@lem6016270 (@IN A x' u)). Qed.
Lemma lem6016272 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term39 A B v u f op) (h2 : term138 A B v u f x' op) : @IN A x' u.
Proof. exact (EQ_MP (@lem6016271 A x' u) (@lem6016268 A B v u f x' op h1 h2)). Qed.
Lemma lem6016275 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6016277 {A : Type'} (x' : A) (u : A -> Prop) : (term119 A x' u) = (term382 A x' u).
Proof. exact (@lem6016275 (@IN A x' u)). Qed.
Lemma lem6016280 {A : Type'} (x' : A) (u : A -> Prop) (h1 : term119 A x' u) : term382 A x' u.
Proof. exact (EQ_MP (@lem6016277 A x' u) (@lem6015879 A x' u h1)). Qed.
Lemma lem6016283 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term39 A B v u f op) (h2 : term119 A x' u) (h3 : term138 A B v u f x' op) : False.
Proof. exact (@lem6016280 A x' u h2 (@lem6016272 A B v u f x' op h1 h3)). Qed.
Lemma lem6016284 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term39 A B v u f op) (h2 : term119 A x' u) (h3 : term138 A B v u f x' op) : term383.
Proof. exact (fun h0 : ~ False => @lem6016283 A B v u f x' op h1 h2 h3). Qed.
Lemma lem6016286 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6016287 : term383 = False.
Proof. exact (@lem6016286 False). Qed.
Lemma lem6016288 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term39 A B v u f op) (h2 : term119 A x' u) (h3 : term138 A B v u f x' op) : False.
Proof. exact (EQ_MP (@lem6016287) (@lem6016284 A B v u f x' op h1 h2 h3)). Qed.
Lemma lem6016379 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (f x') = (@neutral B op)) : (f x') = (@neutral B op).
Proof. exact (h1). Qed.
Lemma lem6016380 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (f x') = (@neutral B op)) : term384 A B f x' op.
Proof. exact (fun h0 : term131 A B f x' op => @lem6016379 A B f x' op h1). Qed.
Lemma lem6016382 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6016383 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : (term384 A B f x' op) = ((f x') = (@neutral B op)).
Proof. exact (@lem6016382 ((f x') = (@neutral B op))). Qed.
Lemma lem6016384 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (f x') = (@neutral B op)) : (f x') = (@neutral B op).
Proof. exact (EQ_MP (@lem6016383 A B f x' op) (@lem6016380 A B f x' op h1)). Qed.
Lemma lem6016387 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6016389 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : (term131 A B f x' op) = (term385 A B f x' op).
Proof. exact (@lem6016387 ((f x') = (@neutral B op))). Qed.
Lemma lem6016392 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term138 A B v u f x' op) : term385 A B f x' op.
Proof. exact (EQ_MP (@lem6016389 A B f x' op) (@lem6015921 A B v u f x' op h1)). Qed.
Lemma lem6016395 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term138 A B v u f x' op) (h2 : (f x') = (@neutral B op)) : False.
Proof. exact (@lem6016392 A B v u f x' op h1 (@lem6016384 A B f x' op h2)). Qed.
Lemma lem6016396 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term138 A B v u f x' op) (h2 : (f x') = (@neutral B op)) : term383.
Proof. exact (fun h0 : ~ False => @lem6016395 A B v u f x' op h1 h2). Qed.
Lemma lem6016398 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6016399 : term383 = False.
Proof. exact (@lem6016398 False). Qed.
Lemma lem6016400 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term138 A B v u f x' op) (h2 : (f x') = (@neutral B op)) : False.
Proof. exact (EQ_MP (@lem6016399) (@lem6016396 A B v u f x' op h1 h2)). Qed.
Lemma lem6016491 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @SUBSET A u v) : @SUBSET A u v.
Proof. exact (h1). Qed.
Lemma lem6016492 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @SUBSET A u v) : term386 A u v.
Proof. exact (fun h0 : term339 A u v => @lem6016491 A u v h1). Qed.
Lemma lem6016494 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6016495 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term386 A u v) = (@SUBSET A u v).
Proof. exact (@lem6016494 (@SUBSET A u v)). Qed.
Lemma lem6016496 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @SUBSET A u v) : @SUBSET A u v.
Proof. exact (EQ_MP (@lem6016495 A u v) (@lem6016492 A u v h1)). Qed.
Lemma lem6016498 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term135 A B v u f x' op) : @IN A x' u.
Proof. exact (proj1 (@lem6015302 A B v u f x' op h1)). Qed.
Lemma lem6016499 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term135 A B v u f x' op) : term359 A x' u.
Proof. exact (fun h0 : term119 A x' u => @lem6016498 A B v u f x' op h1). Qed.
Lemma lem6016501 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6016502 {A : Type'} (x' : A) (u : A -> Prop) : (term359 A x' u) = (@IN A x' u).
Proof. exact (@lem6016501 (@IN A x' u)). Qed.
Lemma lem6016503 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term135 A B v u f x' op) : @IN A x' u.
Proof. exact (EQ_MP (@lem6016502 A x' u) (@lem6016499 A B v u f x' op h1)). Qed.
Lemma lem6016509 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6016510 {A : Type'} (_76658 : A -> Prop) (_76660 : A) (_76659 : A -> Prop) : (term346 A _76658 _76660 _76659) = (term387 A _76658 _76660 _76659).
Proof. exact (@lem6016509 (term119 A _76660 _76658) (term339 A _76658 _76659) (@IN A _76660 _76659)). Qed.
Lemma lem6016524 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6016525 {A : Type'} (_76660 : A) (_76658 : A -> Prop) (_76659 : A -> Prop) : (term388 A _76658 _76660 _76659) = (term389 A _76660 _76658 _76659).
Proof. exact (@lem6016524 (@IN A _76660 _76659) (term339 A _76658 _76659)). Qed.
Lemma lem6016531 {A : Type'} (_76660 : A) (_76658 : A -> Prop) : (term115 A _76660 _76658) = (term115 A _76660 _76658).
Proof. exact (eq_refl (term115 A _76660 _76658)). Qed.
Lemma lem6016532 {A : Type'} (_76660 : A) (_76658 : A -> Prop) (_76659 : A -> Prop) : (term387 A _76658 _76660 _76659) = (term390 A _76660 _76658 _76659).
Proof. exact (MK_COMB (@lem6016531 A _76660 _76658) (@lem6016525 A _76660 _76658 _76659)). Qed.
Lemma lem6016536 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6016537 {A : Type'} (_76660 : A) (_76658 : A -> Prop) (_76659 : A -> Prop) : (term390 A _76660 _76658 _76659) = (term391 A _76660 _76658 _76659).
Proof. exact (@lem6016536 (@IN A _76660 _76659) (term119 A _76660 _76658) (term339 A _76658 _76659)). Qed.
Lemma lem6016553 {A : Type'} (_76660 : A) (_76658 : A -> Prop) (_76659 : A -> Prop) : (term387 A _76658 _76660 _76659) = (term391 A _76660 _76658 _76659).
Proof. exact (TRANS (@lem6016532 A _76660 _76658 _76659) (@lem6016537 A _76660 _76658 _76659)). Qed.
Lemma lem6016554 {A : Type'} (_76660 : A) (_76658 : A -> Prop) (_76659 : A -> Prop) : (term346 A _76658 _76660 _76659) = (term391 A _76660 _76658 _76659).
Proof. exact (TRANS (@lem6016510 A _76658 _76660 _76659) (@lem6016553 A _76660 _76658 _76659)). Qed.
Lemma lem6016555 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6016556 {A : Type'} (_76660 : A) (_76658 : A -> Prop) (_76659 : A -> Prop) : (term392 A _76658 _76660 _76659) = (term393 A _76660 _76658 _76659).
Proof. exact (MK_COMB (@lem6016555) (@lem6016554 A _76660 _76658 _76659)). Qed.
Lemma lem6016570 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6016571 {A : Type'} (_76660 : A) (_76658 : A -> Prop) (_76659 : A -> Prop) : (term394 A _76659 _76660 _76658) = (term395 A _76660 _76658 _76659).
Proof. exact (@lem6016570 (term119 A _76660 _76658) (term339 A _76658 _76659)). Qed.
Lemma lem6016577 {A : Type'} (_76660 : A) (_76659 : A -> Prop) : (term365 A _76660 _76659) = (term365 A _76660 _76659).
Proof. exact (eq_refl (term365 A _76660 _76659)). Qed.
Lemma lem6016578 {A : Type'} (_76660 : A) (_76658 : A -> Prop) (_76659 : A -> Prop) : (term396 A _76659 _76660 _76658) = (term391 A _76660 _76658 _76659).
Proof. exact (MK_COMB (@lem6016577 A _76660 _76659) (@lem6016571 A _76660 _76658 _76659)). Qed.
Lemma lem6016589 {A : Type'} (_76660 : A) (_76658 : A -> Prop) (_76659 : A -> Prop) : ((term346 A _76658 _76660 _76659) = (term396 A _76659 _76660 _76658)) = ((term391 A _76660 _76658 _76659) = (term391 A _76660 _76658 _76659)).
Proof. exact (MK_COMB (@lem6016556 A _76660 _76658 _76659) (@lem6016578 A _76660 _76658 _76659)). Qed.
Lemma lem6016591 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6016592 (x : Prop) : (x = x) = True.
Proof. exact (@lem6016591 Prop x). Qed.
Lemma lem6016593 {A : Type'} (_76660 : A) (_76658 : A -> Prop) (_76659 : A -> Prop) : ((term391 A _76660 _76658 _76659) = (term391 A _76660 _76658 _76659)) = True.
Proof. exact (@lem6016592 (term391 A _76660 _76658 _76659)). Qed.
Lemma lem6016594 {A : Type'} (_76659 : A -> Prop) (_76660 : A) (_76658 : A -> Prop) : ((term346 A _76658 _76660 _76659) = (term396 A _76659 _76660 _76658)) = True.
Proof. exact (TRANS (@lem6016589 A _76660 _76658 _76659) (@lem6016593 A _76660 _76658 _76659)). Qed.
Lemma lem6016595 {A : Type'} (_76659 : A -> Prop) (_76660 : A) (_76658 : A -> Prop) : True = ((term346 A _76658 _76660 _76659) = (term396 A _76659 _76660 _76658)).
Proof. exact (SYM (@lem6016594 A _76659 _76660 _76658)). Qed.
Lemma lem6016596 {A : Type'} (_76659 : A -> Prop) (_76660 : A) (_76658 : A -> Prop) : (term346 A _76658 _76660 _76659) = (term396 A _76659 _76660 _76658).
Proof. exact (EQ_MP (@lem6016595 A _76659 _76660 _76658) (@lem0)). Qed.
Lemma lem6016597 {A : Type'} (_76659 : A -> Prop) (_76660 : A) (_76658 : A -> Prop) (x : type638 A) (h1 : term329 A x) : term396 A _76659 _76660 _76658.
Proof. exact (EQ_MP (@lem6016596 A _76659 _76660 _76658) (@lem6015961 A _76658 _76660 _76659 x h1)). Qed.
Lemma lem6016599 (b : Prop) (a : Prop) : (a \/ b) = (term370 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6016600 {A : Type'} (_76658 : A -> Prop) (_76660 : A) (_76659 : A -> Prop) : (term396 A _76659 _76660 _76658) = (term397 A _76658 _76660 _76659).
Proof. exact (@lem6016599 (term394 A _76659 _76660 _76658) (@IN A _76660 _76659)). Qed.
Lemma lem6016602 (a : Prop) (b : Prop) : (term372 a b) = (term373 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6016603 {A : Type'} (_76659 : A -> Prop) (_76660 : A) (_76658 : A -> Prop) : (term398 A _76659 _76660 _76658) = (term399 A _76659 _76660 _76658).
Proof. exact (@lem6016602 (term339 A _76658 _76659) (term119 A _76660 _76658)). Qed.
Lemma lem6016605 (a : Prop) : (term376 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6016606 {A : Type'} (_76658 : A -> Prop) (_76659 : A -> Prop) : (term400 A _76658 _76659) = (@SUBSET A _76658 _76659).
Proof. exact (@lem6016605 (@SUBSET A _76658 _76659)). Qed.
Lemma lem6016607 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6016608 {A : Type'} (_76658 : A -> Prop) (_76659 : A -> Prop) : (term401 A _76658 _76659) = (term402 A _76658 _76659).
Proof. exact (MK_COMB (@lem6016607) (@lem6016606 A _76658 _76659)). Qed.
Lemma lem6016610 (a : Prop) : (term376 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6016611 {A : Type'} (_76660 : A) (_76658 : A -> Prop) : (term114 A _76660 _76658) = (@IN A _76660 _76658).
Proof. exact (@lem6016610 (@IN A _76660 _76658)). Qed.
Lemma lem6016612 {A : Type'} (_76659 : A -> Prop) (_76660 : A) (_76658 : A -> Prop) : (term399 A _76659 _76660 _76658) = (term403 A _76659 _76660 _76658).
Proof. exact (MK_COMB (@lem6016608 A _76658 _76659) (@lem6016611 A _76660 _76658)). Qed.
Lemma lem6016613 {A : Type'} (_76659 : A -> Prop) (_76660 : A) (_76658 : A -> Prop) : (term398 A _76659 _76660 _76658) = (term403 A _76659 _76660 _76658).
Proof. exact (TRANS (@lem6016603 A _76659 _76660 _76658) (@lem6016612 A _76659 _76660 _76658)). Qed.
Lemma lem6016614 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6016615 {A : Type'} (_76659 : A -> Prop) (_76660 : A) (_76658 : A -> Prop) : (term404 A _76659 _76660 _76658) = (term405 A _76659 _76660 _76658).
Proof. exact (MK_COMB (@lem6016614) (@lem6016613 A _76659 _76660 _76658)). Qed.
Lemma lem6016616 {A : Type'} (_76660 : A) (_76659 : A -> Prop) : (@IN A _76660 _76659) = (@IN A _76660 _76659).
Proof. exact (eq_refl (@IN A _76660 _76659)). Qed.
Lemma lem6016617 {A : Type'} (_76658 : A -> Prop) (_76660 : A) (_76659 : A -> Prop) : (term397 A _76658 _76660 _76659) = (term406 A _76658 _76660 _76659).
Proof. exact (MK_COMB (@lem6016615 A _76659 _76660 _76658) (@lem6016616 A _76660 _76659)). Qed.
Lemma lem6016618 {A : Type'} (_76658 : A -> Prop) (_76660 : A) (_76659 : A -> Prop) : (term396 A _76659 _76660 _76658) = (term406 A _76658 _76660 _76659).
Proof. exact (TRANS (@lem6016600 A _76658 _76660 _76659) (@lem6016617 A _76658 _76660 _76659)). Qed.
Lemma lem6016620 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term135 A B v u f x' op) (h2 : @SUBSET A u v) : term403 A v x' u.
Proof. exact (conj (@lem6016496 A u v h2) (@lem6016503 A B v u f x' op h1)). Qed.
Lemma lem6016622 {A : Type'} (_76658 : A -> Prop) (_76660 : A) (_76659 : A -> Prop) (x : type638 A) (h1 : term329 A x) : term406 A _76658 _76660 _76659.
Proof. exact (EQ_MP (@lem6016618 A _76658 _76660 _76659) (@lem6016597 A _76659 _76660 _76658 x h1)). Qed.
Lemma lem6016623 {A : Type'} (_76658 : A -> Prop) (_76660 : A) (_76659 : A -> Prop) (x : type638 A) (h1 : term329 A x) : term406 A _76658 _76660 _76659.
Proof. exact (@lem6016622 A _76658 _76660 _76659 x h1). Qed.
Lemma lem6016624 {A : Type'} (u : A -> Prop) (x' : A) (v : A -> Prop) (x : type638 A) (h1 : term329 A x) : term406 A u x' v.
Proof. exact (@lem6016623 A u x' v x h1). Qed.
Lemma lem6016627 {A B : Type'} (x : type638 A) (f : A -> B) (x' : A) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term329 A x) (h2 : term135 A B v u f x' op) (h3 : @SUBSET A u v) : @IN A x' v.
Proof. exact (@lem6016624 A u x' v x h1 (@lem6016620 A B f x' op u v h2 h3)). Qed.
Lemma lem6016628 {A B : Type'} (x : type638 A) (f : A -> B) (x' : A) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term329 A x) (h2 : term135 A B v u f x' op) (h3 : @SUBSET A u v) : term359 A x' v.
Proof. exact (fun h0 : term119 A x' v => @lem6016627 A B x f x' op u v h1 h2 h3). Qed.
Lemma lem6016630 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6016631 {A : Type'} (x' : A) (v : A -> Prop) : (term359 A x' v) = (@IN A x' v).
Proof. exact (@lem6016630 (@IN A x' v)). Qed.
Lemma lem6016632 {A B : Type'} (x : type638 A) (f : A -> B) (x' : A) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term329 A x) (h2 : term135 A B v u f x' op) (h3 : @SUBSET A u v) : @IN A x' v.
Proof. exact (EQ_MP (@lem6016631 A x' v) (@lem6016628 A B x f x' op u v h1 h2 h3)). Qed.
Lemma lem6016635 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6016637 {A : Type'} (x' : A) (v : A -> Prop) : (term119 A x' v) = (term382 A x' v).
Proof. exact (@lem6016635 (@IN A x' v)). Qed.
Lemma lem6016640 {A : Type'} (x' : A) (v : A -> Prop) (h1 : term119 A x' v) : term382 A x' v.
Proof. exact (EQ_MP (@lem6016637 A x' v) (@lem6015967 A x' v h1)). Qed.
Lemma lem6016643 {A B : Type'} (x : type638 A) (f : A -> B) (x' : A) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term119 A x' v) (h2 : term329 A x) (h3 : term135 A B v u f x' op) (h4 : @SUBSET A u v) : False.
Proof. exact (@lem6016640 A x' v h1 (@lem6016632 A B x f x' op u v h2 h3 h4)). Qed.
Lemma lem6016644 {A B : Type'} (x : type638 A) (f : A -> B) (x' : A) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term119 A x' v) (h2 : term329 A x) (h3 : term135 A B v u f x' op) (h4 : @SUBSET A u v) : term383.
Proof. exact (fun h0 : ~ False => @lem6016643 A B x f x' op u v h1 h2 h3 h4). Qed.
Lemma lem6016646 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6016647 : term383 = False.
Proof. exact (@lem6016646 False). Qed.
Lemma lem6016648 {A B : Type'} (x : type638 A) (f : A -> B) (x' : A) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term119 A x' v) (h2 : term329 A x) (h3 : term135 A B v u f x' op) (h4 : @SUBSET A u v) : False.
Proof. exact (EQ_MP (@lem6016647) (@lem6016644 A B x f x' op u v h1 h2 h3 h4)). Qed.
Lemma lem6016739 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (f x') = (@neutral B op)) : (f x') = (@neutral B op).
Proof. exact (h1). Qed.
Lemma lem6016740 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (f x') = (@neutral B op)) : term384 A B f x' op.
Proof. exact (fun h0 : term131 A B f x' op => @lem6016739 A B f x' op h1). Qed.
Lemma lem6016742 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6016743 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : (term384 A B f x' op) = ((f x') = (@neutral B op)).
Proof. exact (@lem6016742 ((f x') = (@neutral B op))). Qed.
Lemma lem6016744 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) (h1 : (f x') = (@neutral B op)) : (f x') = (@neutral B op).
Proof. exact (EQ_MP (@lem6016743 A B f x' op) (@lem6016740 A B f x' op h1)). Qed.
Lemma lem6016747 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6016749 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : (term131 A B f x' op) = (term385 A B f x' op).
Proof. exact (@lem6016747 ((f x') = (@neutral B op))). Qed.
Lemma lem6016752 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term135 A B v u f x' op) : term385 A B f x' op.
Proof. exact (EQ_MP (@lem6016749 A B f x' op) (@lem6016009 A B v u f x' op h1)). Qed.
Lemma lem6016755 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term135 A B v u f x' op) (h2 : (f x') = (@neutral B op)) : False.
Proof. exact (@lem6016752 A B v u f x' op h1 (@lem6016744 A B f x' op h2)). Qed.
Lemma lem6016756 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term135 A B v u f x' op) (h2 : (f x') = (@neutral B op)) : term383.
Proof. exact (fun h0 : ~ False => @lem6016755 A B v u f x' op h1 h2). Qed.
Lemma lem6016758 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6016759 : term383 = False.
Proof. exact (@lem6016758 False). Qed.
Lemma lem6016760 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term135 A B v u f x' op) (h2 : (f x') = (@neutral B op)) : False.
Proof. exact (EQ_MP (@lem6016759) (@lem6016756 A B v u f x' op h1 h2)). Qed.
Lemma lem6016761 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term135 A B v u f x' op) (h2 : (f x') = (@neutral B op)) : ((f x') = (@neutral B op)) = False.
Proof. exact (prop_ext (fun h3 : (f x') = (@neutral B op) => @lem6016760 A B v u f x' op h1 h2) (fun h3 : False => @lem6016011 A B f x' op h2)). Qed.
Lemma lem6016762 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term135 A B v u f x' op) (h2 : (f x') = (@neutral B op)) : False.
Proof. exact (EQ_MP (@lem6016761 A B v u f x' op h1 h2) (@lem6016011 A B f x' op h2)). Qed.
Lemma lem6016763 {A B : Type'} (x : type638 A) (f : A -> B) (x' : A) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term119 A x' v) (h2 : term329 A x) (h3 : term135 A B v u f x' op) (h4 : @SUBSET A u v) : (term119 A x' v) = False.
Proof. exact (prop_ext (fun h5 : term119 A x' v => @lem6016648 A B x f x' op u v h1 h2 h3 h4) (fun h5 : False => @lem6015967 A x' v h1)). Qed.
Lemma lem6016764 {A B : Type'} (x : type638 A) (f : A -> B) (x' : A) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term119 A x' v) (h2 : term329 A x) (h3 : term135 A B v u f x' op) (h4 : @SUBSET A u v) : False.
Proof. exact (EQ_MP (@lem6016763 A B x f x' op u v h1 h2 h3 h4) (@lem6015967 A x' v h1)). Qed.
Lemma lem6016765 {A B : Type'} (x : type638 A) (f : A -> B) (x' : A) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term119 A x' v) (h2 : term329 A x) (h3 : term135 A B v u f x' op) (h4 : @SUBSET A u v) : (@SUBSET A u v) = False.
Proof. exact (prop_ext (fun h5 : @SUBSET A u v => @lem6016764 A B x f x' op u v h1 h2 h3 h4) (fun h5 : False => @lem6015939 A u v h4)). Qed.
Lemma lem6016766 {A B : Type'} (x : type638 A) (f : A -> B) (x' : A) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term119 A x' v) (h2 : term329 A x) (h3 : term135 A B v u f x' op) (h4 : @SUBSET A u v) : False.
Proof. exact (EQ_MP (@lem6016765 A B x f x' op u v h1 h2 h3 h4) (@lem6015939 A u v h4)). Qed.
Lemma lem6016767 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term138 A B v u f x' op) (h2 : (f x') = (@neutral B op)) : ((f x') = (@neutral B op)) = False.
Proof. exact (prop_ext (fun h3 : (f x') = (@neutral B op) => @lem6016400 A B v u f x' op h1 h2) (fun h3 : False => @lem6015923 A B f x' op h2)). Qed.
Lemma lem6016768 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term138 A B v u f x' op) (h2 : (f x') = (@neutral B op)) : False.
Proof. exact (EQ_MP (@lem6016767 A B v u f x' op h1 h2) (@lem6015923 A B f x' op h2)). Qed.
Lemma lem6016769 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term39 A B v u f op) (h2 : term119 A x' u) (h3 : term138 A B v u f x' op) : (term119 A x' u) = False.
Proof. exact (prop_ext (fun h4 : term119 A x' u => @lem6016288 A B v u f x' op h1 h2 h3) (fun h4 : False => @lem6015879 A x' u h2)). Qed.
Lemma lem6016770 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term39 A B v u f op) (h2 : term119 A x' u) (h3 : term138 A B v u f x' op) : False.
Proof. exact (EQ_MP (@lem6016769 A B v u f x' op h1 h2 h3) (@lem6015879 A x' u h2)). Qed.
Lemma lem6016771 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term135 A B v u f x' op) (h2 : (f x') = (@neutral B op)) : ((f x') = (@neutral B op)) = False.
Proof. exact (prop_ext (fun h3 : (f x') = (@neutral B op) => @lem6016762 A B v u f x' op h1 h2) (fun h3 : False => @lem6015767 A B f x' op h2)). Qed.
Lemma lem6016772 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term135 A B v u f x' op) (h2 : (f x') = (@neutral B op)) : False.
Proof. exact (EQ_MP (@lem6016771 A B v u f x' op h1 h2) (@lem6015767 A B f x' op h2)). Qed.
Lemma lem6016773 {A B : Type'} (x : type638 A) (f : A -> B) (x' : A) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term119 A x' v) (h2 : term329 A x) (h3 : term135 A B v u f x' op) (h4 : @SUBSET A u v) : (term119 A x' v) = False.
Proof. exact (prop_ext (fun h5 : term119 A x' v => @lem6016766 A B x f x' op u v h1 h2 h3 h4) (fun h5 : False => @lem6015652 A x' v h1)). Qed.
Lemma lem6016774 {A B : Type'} (x : type638 A) (f : A -> B) (x' : A) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term119 A x' v) (h2 : term329 A x) (h3 : term135 A B v u f x' op) (h4 : @SUBSET A u v) : False.
Proof. exact (EQ_MP (@lem6016773 A B x f x' op u v h1 h2 h3 h4) (@lem6015652 A x' v h1)). Qed.
Lemma lem6016775 {A B : Type'} (x : type638 A) (f : A -> B) (x' : A) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term119 A x' v) (h2 : term329 A x) (h3 : term135 A B v u f x' op) (h4 : @SUBSET A u v) : (@SUBSET A u v) = False.
Proof. exact (prop_ext (fun h5 : @SUBSET A u v => @lem6016774 A B x f x' op u v h1 h2 h3 h4) (fun h5 : False => @lem6015545 A u v h4)). Qed.
Lemma lem6016776 {A B : Type'} (x : type638 A) (f : A -> B) (x' : A) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term119 A x' v) (h2 : term329 A x) (h3 : term135 A B v u f x' op) (h4 : @SUBSET A u v) : False.
Proof. exact (EQ_MP (@lem6016775 A B x f x' op u v h1 h2 h3 h4) (@lem6015545 A u v h4)). Qed.
Lemma lem6016777 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term138 A B v u f x' op) (h2 : (f x') = (@neutral B op)) : ((f x') = (@neutral B op)) = False.
Proof. exact (prop_ext (fun h3 : (f x') = (@neutral B op) => @lem6016768 A B v u f x' op h1 h2) (fun h3 : False => @lem6015537 A B f x' op h2)). Qed.
Lemma lem6016778 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term138 A B v u f x' op) (h2 : (f x') = (@neutral B op)) : False.
Proof. exact (EQ_MP (@lem6016777 A B v u f x' op h1 h2) (@lem6015537 A B f x' op h2)). Qed.
Lemma lem6016779 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term39 A B v u f op) (h2 : term119 A x' u) (h3 : term138 A B v u f x' op) : (term119 A x' u) = False.
Proof. exact (prop_ext (fun h4 : term119 A x' u => @lem6016770 A B v u f x' op h1 h2 h3) (fun h4 : False => @lem6015422 A x' u h2)). Qed.
Lemma lem6016780 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term39 A B v u f op) (h2 : term119 A x' u) (h3 : term138 A B v u f x' op) : False.
Proof. exact (EQ_MP (@lem6016779 A B v u f x' op h1 h2 h3) (@lem6015422 A x' u h2)). Qed.
Lemma lem6016781 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term135 A B v u f x' op) (h2 : (f x') = (@neutral B op)) : ((f x') = (@neutral B op)) = False.
Proof. exact (prop_ext (fun h3 : (f x') = (@neutral B op) => @lem6016772 A B v u f x' op h1 h2) (fun h3 : False => @lem6015767 A B f x' op h2)). Qed.
Lemma lem6016782 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term135 A B v u f x' op) (h2 : (f x') = (@neutral B op)) : False.
Proof. exact (EQ_MP (@lem6016781 A B v u f x' op h1 h2) (@lem6015767 A B f x' op h2)). Qed.
Lemma lem6016783 {A B : Type'} (x : type638 A) (f : A -> B) (x' : A) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term119 A x' v) (h2 : term329 A x) (h3 : term135 A B v u f x' op) (h4 : @SUBSET A u v) : (term119 A x' v) = False.
Proof. exact (prop_ext (fun h5 : term119 A x' v => @lem6016776 A B x f x' op u v h1 h2 h3 h4) (fun h5 : False => @lem6015652 A x' v h1)). Qed.
Lemma lem6016784 {A B : Type'} (x : type638 A) (f : A -> B) (x' : A) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term119 A x' v) (h2 : term329 A x) (h3 : term135 A B v u f x' op) (h4 : @SUBSET A u v) : False.
Proof. exact (EQ_MP (@lem6016783 A B x f x' op u v h1 h2 h3 h4) (@lem6015652 A x' v h1)). Qed.
Lemma lem6016785 {A B : Type'} (x : type638 A) (f : A -> B) (x' : A) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term119 A x' v) (h2 : term329 A x) (h3 : term135 A B v u f x' op) (h4 : @SUBSET A u v) : (@SUBSET A u v) = False.
Proof. exact (prop_ext (fun h5 : @SUBSET A u v => @lem6016784 A B x f x' op u v h1 h2 h3 h4) (fun h5 : False => @lem6015545 A u v h4)). Qed.
Lemma lem6016786 {A B : Type'} (x : type638 A) (f : A -> B) (x' : A) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term119 A x' v) (h2 : term329 A x) (h3 : term135 A B v u f x' op) (h4 : @SUBSET A u v) : False.
Proof. exact (EQ_MP (@lem6016785 A B x f x' op u v h1 h2 h3 h4) (@lem6015545 A u v h4)). Qed.
Lemma lem6016787 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term138 A B v u f x' op) (h2 : (f x') = (@neutral B op)) : ((f x') = (@neutral B op)) = False.
Proof. exact (prop_ext (fun h3 : (f x') = (@neutral B op) => @lem6016778 A B v u f x' op h1 h2) (fun h3 : False => @lem6015537 A B f x' op h2)). Qed.
Lemma lem6016788 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term138 A B v u f x' op) (h2 : (f x') = (@neutral B op)) : False.
Proof. exact (EQ_MP (@lem6016787 A B v u f x' op h1 h2) (@lem6015537 A B f x' op h2)). Qed.
Lemma lem6016789 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term39 A B v u f op) (h2 : term119 A x' u) (h3 : term138 A B v u f x' op) : (term119 A x' u) = False.
Proof. exact (prop_ext (fun h4 : term119 A x' u => @lem6016780 A B v u f x' op h1 h2 h3) (fun h4 : False => @lem6015422 A x' u h2)). Qed.
Lemma lem6016790 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term39 A B v u f op) (h2 : term119 A x' u) (h3 : term138 A B v u f x' op) : False.
Proof. exact (EQ_MP (@lem6016789 A B v u f x' op h1 h2 h3) (@lem6015422 A x' u h2)). Qed.
Lemma lem6016791 {A B : Type'} (x : type638 A) (f : A -> B) (x' : A) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term329 A x) (h2 : term135 A B v u f x' op) (h3 : @SUBSET A u v) : False.
Proof. exact (or_elim (@lem6015303 A B v u f x' op h2) (fun h0 : term119 A x' v => @lem6016786 A B x f x' op u v h0 h1 h2 h3) (fun h0 : (f x') = (@neutral B op) => @lem6016782 A B v u f x' op h2 h0)). Qed.
Lemma lem6016792 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term39 A B v u f op) (h2 : term138 A B v u f x' op) : False.
Proof. exact (or_elim (@lem6015296 A B v u f x' op h2) (fun h0 : term119 A x' u => @lem6016790 A B v u f x' op h1 h0 h2) (fun h0 : (f x') = (@neutral B op) => @lem6016788 A B v u f x' op h2 h0)). Qed.
Lemma lem6016793 {A B : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term39 A B v u f op) (h2 : term329 A x) (h3 : @SUBSET A u v) (h4 : term142 A B v u f x' op) : False.
Proof. exact (or_elim (@lem6015291 A B v u f x' op h4) (fun h0 : term138 A B v u f x' op => @lem6016792 A B v u f x' op h1 h0) (fun h0 : term135 A B v u f x' op => @lem6016791 A B x f x' op u v h2 h0 h3)). Qed.
Lemma lem6016794 {A B : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term39 A B v u f op) (h2 : term329 A x) (h3 : @SUBSET A u v) (h4 : term142 A B v u f x' op) : (term142 A B v u f x' op) = False.
Proof. exact (prop_ext (fun h5 : term142 A B v u f x' op => @lem6016793 A B x v u f x' op h1 h2 h3 h4) (fun h5 : False => @lem6015291 A B v u f x' op h4)). Qed.
Lemma lem6016795 {A B : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term39 A B v u f op) (h2 : term329 A x) (h3 : @SUBSET A u v) (h4 : term142 A B v u f x' op) : False.
Proof. exact (EQ_MP (@lem6016794 A B x v u f x' op h1 h2 h3 h4) (@lem6015291 A B v u f x' op h4)). Qed.
Lemma lem6016796 {A B : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term39 A B v u f op) (h2 : term329 A x) (h3 : @SUBSET A u v) (h4 : term142 A B v u f x' op) : (term329 A x) = False.
Proof. exact (prop_ext (fun h5 : term329 A x => @lem6016795 A B x v u f x' op h1 h2 h3 h4) (fun h5 : False => @lem6015205 A x h2)). Qed.
Lemma lem6016797 {A B : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term39 A B v u f op) (h2 : term329 A x) (h3 : @SUBSET A u v) (h4 : term142 A B v u f x' op) : False.
Proof. exact (EQ_MP (@lem6016796 A B x v u f x' op h1 h2 h3 h4) (@lem6015205 A x h2)). Qed.
Lemma lem6016798 {A B : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term39 A B v u f op) (h2 : term329 A x) (h3 : @SUBSET A u v) (h4 : term142 A B v u f x' op) : (@SUBSET A u v) = False.
Proof. exact (prop_ext (fun h5 : @SUBSET A u v => @lem6016797 A B x v u f x' op h1 h2 h3 h4) (fun h5 : False => @lem6015099 A u v h3)). Qed.
Lemma lem6016799 {A B : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) (f : A -> B) (x' : A) (op : type1400 B) (h1 : term39 A B v u f op) (h2 : term329 A x) (h3 : @SUBSET A u v) (h4 : term142 A B v u f x' op) : False.
Proof. exact (EQ_MP (@lem6016798 A B x v u f x' op h1 h2 h3 h4) (@lem6015099 A u v h3)). Qed.
Lemma lem6016800 {A B : Type'} (f : A -> B) (op : type1400 B) (x : type638 A) (u : A -> Prop) (v : A -> Prop) (h1 : term39 A B v u f op) (h2 : term70 A B v u f op) (h3 : term329 A x) (h4 : @SUBSET A u v) : False.
Proof. exact (ex_elim (@lem6014467 A B v u f op h2) (fun x' : A => fun h0 : term150 A B v u f op x' => @lem6016799 A B x v u f x' op h1 h3 h4 h0)). Qed.
Lemma lem6016801 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term39 A B v u f op) (h2 : term71 A) (h3 : term70 A B v u f op) (h4 : @SUBSET A u v) : False.
Proof. exact (ex_elim (@lem6015087 A h2) (fun x : type638 A => fun h0 : term331 A x => @lem6016800 A B f op x u v h1 h3 h0 h4)). Qed.
Lemma lem6016802 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term39 A B v u f op) (h2 : term71 A) (h3 : term70 A B v u f op) (h4 : @SUBSET A u v) : (@SUBSET A u v) = False.
Proof. exact (prop_ext (fun h5 : @SUBSET A u v => @lem6016801 A B f op u v h1 h2 h3 h4) (fun h5 : False => @lem6014194 A u v h4)). Qed.
Lemma lem6016803 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term39 A B v u f op) (h2 : term71 A) (h3 : term70 A B v u f op) (h4 : @SUBSET A u v) : False.
Proof. exact (EQ_MP (@lem6016802 A B f op u v h1 h2 h3 h4) (@lem6014194 A u v h4)). Qed.
Lemma lem6016804 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term39 A B v u f op) (h2 : term70 A B v u f op) (h3 : @SUBSET A u v) : term76 A.
Proof. exact (fun h0 : term71 A => @lem6016803 A B f op u v h1 h0 h2 h3). Qed.
Lemma lem6016805 {A : Type'} : (term76 A) = (term77 A).
Proof. exact (@lem69 (term71 A)). Qed.
Lemma lem6016806 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term39 A B v u f op) (h2 : term70 A B v u f op) (h3 : @SUBSET A u v) : term77 A.
Proof. exact (EQ_MP (@lem6016805 A) (@lem6016804 A B f op u v h1 h2 h3)). Qed.
Lemma lem6016807 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term39 A B v u f op) (h2 : @SUBSET A u v) : term80 A B v u f op.
Proof. exact (fun h0 : term70 A B v u f op => @lem6016806 A B f op u v h1 h0 h2). Qed.
Lemma lem6016808 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : @SUBSET A u v) : term83 A B v u f op.
Proof. exact (fun h0 : term39 A B v u f op => @lem6016807 A B f op u v h0 h1). Qed.
Lemma lem6016809 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : term86 A B v u f op.
Proof. exact (fun h0 : @SUBSET A u v => @lem6016808 A B f op u v h0). Qed.
Lemma lem6016810 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : term88 A B v u f op.
Proof. exact (fun h0 : @monoidal B op => @lem6016809 A B v u f op). Qed.
Lemma lem6016815 {A B : Type'} (u : A -> Prop) (f : A -> B) (op : type1400 B) : term92 A B u f op.
Proof. exact (fun v : A -> Prop => @lem6016810 A B v u f op). Qed.
Lemma lem6016820 {A B : Type'} (f : A -> B) (op : type1400 B) : term96 A B f op.
Proof. exact (fun u : A -> Prop => @lem6016815 A B u f op). Qed.
Lemma lem6016825 {A B : Type'} (op : type1400 B) : term100 A B op.
Proof. exact (fun f : A -> B => @lem6016820 A B f op). Qed.
Lemma lem6016830 {A B : Type'} : term104 A B.
Proof. exact (fun op : type1400 B => @lem6016825 A B op). Qed.
Lemma lem6016831 {A B : Type'} : term103 A B.
Proof. exact (EQ_MP (@lem6014177 A B) (@lem6016830 A B)). Qed.
Lemma lem6016832 {A B : Type'} (op : type1400 B) : term407 A B op.
Proof. exact (@lem6016831 A B op). Qed.
Lemma lem6016833 {A B : Type'} (op : type1400 B) : (term407 A B op) = (term99 A B op).
Proof. exact (eq_refl (term407 A B op)). Qed.
Lemma lem6016834 {A B : Type'} (op : type1400 B) : term99 A B op.
Proof. exact (EQ_MP (@lem6016833 A B op) (@lem6016832 A B op)). Qed.
Lemma lem6016835 {A B : Type'} (op : type1400 B) (f : A -> B) : term408 A B op f.
Proof. exact (@lem6016834 A B op f). Qed.
Lemma lem6016836 {A B : Type'} (f : A -> B) (op : type1400 B) : (term408 A B op f) = (term95 A B f op).
Proof. exact (eq_refl (term408 A B op f)). Qed.
Lemma lem6016837 {A B : Type'} (f : A -> B) (op : type1400 B) : term95 A B f op.
Proof. exact (EQ_MP (@lem6016836 A B f op) (@lem6016835 A B op f)). Qed.
Lemma lem6016838 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) : term409 A B f op u.
Proof. exact (@lem6016837 A B f op u). Qed.
Lemma lem6016839 {A B : Type'} (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term409 A B f op u) = (term91 A B u f op).
Proof. exact (eq_refl (term409 A B f op u)). Qed.
Lemma lem6016840 {A B : Type'} (u : A -> Prop) (f : A -> B) (op : type1400 B) : term91 A B u f op.
Proof. exact (EQ_MP (@lem6016839 A B u f op) (@lem6016838 A B f op u)). Qed.
Lemma lem6016841 {A B : Type'} (u : A -> Prop) (f : A -> B) (op : type1400 B) (v : A -> Prop) : term410 A B u f op v.
Proof. exact (@lem6016840 A B u f op v). Qed.
Lemma lem6016842 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : (term410 A B u f op v) = (term72 A B v u f op).
Proof. exact (eq_refl (term410 A B u f op v)). Qed.
Lemma lem6016843 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : term72 A B v u f op.
Proof. exact (EQ_MP (@lem6016842 A B v u f op) (@lem6016841 A B u f op v)). Qed.
Lemma lem6016845 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) : term72 A B v u f op.
Proof. exact (@lem6013914 A B v u f op (@lem6016843 A B v u f op)). Qed.
Lemma lem6016846 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term85 A B v u f op.
Proof. exact (@lem6016845 A B v u f op (@lem6013752 B op h1)). Qed.
Lemma lem6016847 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : @monoidal B op) (h2 : @SUBSET A u v) : term82 A B v u f op.
Proof. exact (@lem6016846 A B v u f op h1 (@lem6013755 A u v h2)). Qed.
Lemma lem6016848 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term39 A B v u f op) (h2 : @monoidal B op) (h3 : @SUBSET A u v) : term79 A B v u f op.
Proof. exact (@lem6016847 A B f op u v h2 h3 (@lem6013754 A B v u f op h1)). Qed.
Lemma lem6016849 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term39 A B v u f op) (h2 : @monoidal B op) (h3 : term70 A B v u f op) (h4 : @SUBSET A u v) : term76 A.
Proof. exact (@lem6016848 A B f op u v h1 h2 h4 (@lem6013896 A B v u f op h3)). Qed.
Lemma lem6016850 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term39 A B v u f op) (h2 : @monoidal B op) (h3 : term70 A B v u f op) (h4 : @SUBSET A u v) : False.
Proof. exact (@lem6016849 A B f op u v h1 h2 h3 h4 (@lem6013897 A)). Qed.
Lemma lem6016851 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term39 A B v u f op) (h2 : @monoidal B op) (h3 : term70 A B v u f op) (h4 : @SUBSET A u v) : (term70 A B v u f op) = False.
Proof. exact (prop_ext (fun h5 : term70 A B v u f op => @lem6016850 A B f op u v h1 h2 h3 h4) (fun h5 : False => @lem6013896 A B v u f op h3)). Qed.
Lemma lem6016852 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term39 A B v u f op) (h2 : @monoidal B op) (h3 : term70 A B v u f op) (h4 : @SUBSET A u v) : False.
Proof. exact (EQ_MP (@lem6016851 A B f op u v h1 h2 h3 h4) (@lem6013896 A B v u f op h3)). Qed.
Lemma lem6016853 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term39 A B v u f op) (h2 : @monoidal B op) (h3 : @SUBSET A u v) : term69 A B v u f op.
Proof. exact (fun h0 : term70 A B v u f op => @lem6016852 A B f op u v h1 h2 h0 h3). Qed.
Lemma lem6016854 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term39 A B v u f op) (h2 : @monoidal B op) (h3 : @SUBSET A u v) : term67 A B v u f op.
Proof. exact (EQ_MP (@lem6013895 A B v u f op) (@lem6016853 A B f op u v h1 h2 h3)). Qed.
Lemma lem6016855 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term39 A B v u f op) (h2 : @monoidal B op) (h3 : @SUBSET A u v) : (@support A B op f v) = (@support A B op f u).
Proof. exact (EQ_MP (@lem6013891 A B v op f u) (@lem6016854 A B f op u v h1 h2 h3)). Qed.
Lemma lem6016856 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term39 A B v u f op) (h2 : @monoidal B op) (h3 : @SUBSET A u v) : (term411 A B op f v) = (term411 A B op f u).
Proof. exact (MK_COMB (@lem6013771 A B op) (@lem6016855 A B f op u v h1 h2 h3)). Qed.
Lemma lem6016857 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term39 A B v u f op) (h2 : @monoidal B op) (h3 : @SUBSET A u v) : (term40 A B op v f) = (term40 A B op u f).
Proof. exact (MK_COMB (@lem6016856 A B f op u v h1 h2 h3) (@lem6013770 A B f)). Qed.
Lemma lem6016858 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term39 A B v u f op) (h2 : @monoidal B op) (h3 : @SUBSET A u v) : (@iterate B A op v f) = (@iterate B A op u f).
Proof. exact (EQ_MP (@lem6013769 A B v op u f) (@lem6016857 A B f op u v h1 h2 h3)). Qed.
Lemma lem6016859 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term38 A B v u f op) : term39 A B v u f op.
Proof. exact (proj2 (@lem6013753 A B v u f op h1)). Qed.
Lemma lem6016860 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term38 A B v u f op) : @SUBSET A u v.
Proof. exact (proj1 (@lem6013753 A B v u f op h1)). Qed.
Lemma lem6016861 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term39 A B v u f op) (h2 : @monoidal B op) (h3 : @SUBSET A u v) : (term39 A B v u f op) = ((@iterate B A op v f) = (@iterate B A op u f)).
Proof. exact (prop_ext (fun h4 : term39 A B v u f op => @lem6016858 A B f op u v h1 h2 h3) (fun h4 : (@iterate B A op v f) = (@iterate B A op u f) => @lem6013754 A B v u f op h1)). Qed.
Lemma lem6016862 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term39 A B v u f op) (h2 : @monoidal B op) (h3 : @SUBSET A u v) : (@iterate B A op v f) = (@iterate B A op u f).
Proof. exact (EQ_MP (@lem6016861 A B f op u v h1 h2 h3) (@lem6013754 A B v u f op h1)). Qed.
Lemma lem6016863 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term39 A B v u f op) (h2 : @monoidal B op) (h3 : @SUBSET A u v) : (@SUBSET A u v) = ((@iterate B A op v f) = (@iterate B A op u f)).
Proof. exact (prop_ext (fun h4 : @SUBSET A u v => @lem6016862 A B f op u v h1 h2 h3) (fun h4 : (@iterate B A op v f) = (@iterate B A op u f) => @lem6013755 A u v h3)). Qed.
Lemma lem6016864 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : term39 A B v u f op) (h2 : @monoidal B op) (h3 : @SUBSET A u v) : (@iterate B A op v f) = (@iterate B A op u f).
Proof. exact (EQ_MP (@lem6016863 A B f op u v h1 h2 h3) (@lem6013755 A u v h3)). Qed.
Lemma lem6016865 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : @monoidal B op) (h2 : term38 A B v u f op) (h3 : @SUBSET A u v) : (term39 A B v u f op) = ((@iterate B A op v f) = (@iterate B A op u f)).
Proof. exact (prop_ext (fun h4 : term39 A B v u f op => @lem6016864 A B f op u v h4 h1 h3) (fun h4 : (@iterate B A op v f) = (@iterate B A op u f) => @lem6016859 A B v u f op h2)). Qed.
Lemma lem6016866 {A B : Type'} (f : A -> B) (op : type1400 B) (u : A -> Prop) (v : A -> Prop) (h1 : @monoidal B op) (h2 : term38 A B v u f op) (h3 : @SUBSET A u v) : (@iterate B A op v f) = (@iterate B A op u f).
Proof. exact (EQ_MP (@lem6016865 A B f op u v h1 h2 h3) (@lem6016859 A B v u f op h2)). Qed.
Lemma lem6016867 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) (h2 : term38 A B v u f op) : (@SUBSET A u v) = ((@iterate B A op v f) = (@iterate B A op u f)).
Proof. exact (prop_ext (fun h3 : @SUBSET A u v => @lem6016866 A B f op u v h1 h2 h3) (fun h3 : (@iterate B A op v f) = (@iterate B A op u f) => @lem6016860 A B v u f op h2)). Qed.
Lemma lem6016868 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) (h2 : term38 A B v u f op) : (@iterate B A op v f) = (@iterate B A op u f).
Proof. exact (EQ_MP (@lem6016867 A B v u f op h1 h2) (@lem6016860 A B v u f op h2)). Qed.
Lemma lem6016869 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term412 A B v op u f.
Proof. exact (fun h0 : term38 A B v u f op => @lem6016868 A B v u f op h1 h0). Qed.
Lemma lem6016874 {A B : Type'} (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term413 A B op u f.
Proof. exact (fun v : A -> Prop => @lem6016869 A B v u f op h1). Qed.
Lemma lem6016879 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term414 A B op f.
Proof. exact (fun u : A -> Prop => @lem6016874 A B u f op h1). Qed.
Lemma lem6016884 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term415 A B op.
Proof. exact (fun f : A -> B => @lem6016879 A B f op h1). Qed.
Lemma lem6016885 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = (term415 A B op).
Proof. exact (prop_ext (fun h2 : @monoidal B op => @lem6016884 A B op h1) (fun h2 : term415 A B op => @lem6013752 B op h1)). Qed.
Lemma lem6016886 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term415 A B op.
Proof. exact (EQ_MP (@lem6016885 A B op h1) (@lem6013752 B op h1)). Qed.
Lemma lem6016887 {A B : Type'} (op : type1400 B) : term416 A B op.
Proof. exact (fun h0 : @monoidal B op => @lem6016886 A B op h0). Qed.
Lemma lem6016892 {A B : Type'} : term417 A B.
Proof. exact (fun op : type1400 B => @lem6016887 A B op). Qed.
