Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_UNPAIR_FUN_THM_term_abbrevs.
Require Import ETA_AX_spec.
Require Import FORALL_PAIR_FUN_THM_spec.
Require Import o_DEF_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm48213_spec.
Require Import thm48214_spec.
Require Import thm48219_spec.
Require Import thm48220_spec.
Lemma lem54787 {A B : Type'} (t : A -> B) : term0 A B t.
Proof. exact (@lem9121 A B t). Qed.
Lemma lem54788 {A B : Type'} (t : A -> B) : (term0 A B t) = ((term1 A B t) = t).
Proof. exact (eq_refl (term0 A B t)). Qed.
Lemma lem54789 {A B : Type'} (t : A -> B) : (term1 A B t) = t.
Proof. exact (EQ_MP (@lem54788 A B t) (@lem54787 A B t)). Qed.
Lemma lem54790 {A B C : Type'} (f : B -> C) : term2 A B C f.
Proof. exact (@lem15397 A B C f). Qed.
Lemma lem54791 {A B C : Type'} (f : B -> C) : (term2 A B C f) = (term3 A B C f).
Proof. exact (eq_refl (term2 A B C f)). Qed.
Lemma lem54792 {A B C : Type'} (f : B -> C) : term3 A B C f.
Proof. exact (EQ_MP (@lem54791 A B C f) (@lem54790 A B C f)). Qed.
Lemma lem54793 {A B C : Type'} (f : B -> C) (g : A -> B) : term4 A B C f g.
Proof. exact (@lem54792 A B C f g). Qed.
Lemma lem54794 {A B C : Type'} (f : B -> C) (g : A -> B) : (term4 A B C f g) = ((@o A B C f g) = (term5 A B C f g)).
Proof. exact (eq_refl (term4 A B C f g)). Qed.
Lemma lem54796 {A B C : Type'} (P : type478 A B C) : term6 A B C P.
Proof. exact (@lem54241 A B C P). Qed.
Lemma lem54797 {A B C : Type'} (P : type478 A B C) : (term6 A B C P) = ((term7 A B C P) = (term8 A B C P)).
Proof. exact (eq_refl (term6 A B C P)). Qed.
Lemma lem54819 {_5621 _5631 : Type'} (t : type572 _5621 _5631) : (term9 _5621 _5631 t) = t.
Proof. exact (@lem54789 (_5621 -> _5631) Prop t). Qed.
Lemma lem54820 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) (f : _5621 -> _5630) : (term10 _5621 _5630 _5631 P f) = (P f).
Proof. exact (@lem54819 _5621 _5631 (P f)). Qed.
Lemma lem54821 {_5621 _5631 : Type'} : (@all (_5621 -> _5631)) = (@all (_5621 -> _5631)).
Proof. exact (eq_refl (@all (_5621 -> _5631))). Qed.
Lemma lem54822 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) (f : _5621 -> _5630) : (term11 _5621 _5630 _5631 P f) = (term12 _5621 _5630 _5631 P f).
Proof. exact (MK_COMB (@lem54821 _5621 _5631) (@lem54820 _5621 _5630 _5631 P f)). Qed.
Lemma lem54823 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) : (term13 _5621 _5630 _5631 P) = (term14 _5621 _5630 _5631 P).
Proof. exact (fun_ext (fun f : _5621 -> _5630 => @lem54822 _5621 _5630 _5631 P f)). Qed.
Lemma lem54824 {_5621 _5630 : Type'} : (@all (_5621 -> _5630)) = (@all (_5621 -> _5630)).
Proof. exact (eq_refl (@all (_5621 -> _5630))). Qed.
Lemma lem54825 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) : (term15 _5621 _5630 _5631 P) = (term16 _5621 _5630 _5631 P).
Proof. exact (MK_COMB (@lem54824 _5621 _5630) (@lem54823 _5621 _5630 _5631 P)). Qed.
Lemma lem54832 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem54833 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) : (term17 _5621 _5630 _5631 P) = (term18 _5621 _5630 _5631 P).
Proof. exact (MK_COMB (@lem54832) (@lem54825 _5621 _5630 _5631 P)). Qed.
Lemma lem54839 {A B C : Type'} (P : type478 A B C) : (term7 A B C P) = (term8 A B C P).
Proof. exact (EQ_MP (@lem54797 A B C P) (@lem54796 A B C P)). Qed.
Lemma lem54840 {_5621 _5630 _5631 : Type'} (P : type478 _5621 _5630 _5631) : (term7 _5621 _5630 _5631 P) = (term8 _5621 _5630 _5631 P).
Proof. exact (@lem54839 _5621 _5630 _5631 P). Qed.
Lemma lem54841 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) : (term19 _5621 _5630 _5631 P) = (term20 _5621 _5630 _5631 P).
Proof. exact (@lem54840 _5621 _5630 _5631 (term21 _5621 _5630 _5631 P)). Qed.
Lemma lem54842 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) (h : type1430 _5621 _5630 _5631) : (term22 _5621 _5630 _5631 P h) = (term23 _5621 _5630 _5631 P h).
Proof. exact (eq_refl (term22 _5621 _5630 _5631 P h)). Qed.
Lemma lem54843 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) : (term24 _5621 _5630 _5631 P) = (term21 _5621 _5630 _5631 P).
Proof. exact (fun_ext (fun h : type1430 _5621 _5630 _5631 => @lem54842 _5621 _5630 _5631 P h)). Qed.
Lemma lem54844 {_5621 _5630 _5631 : Type'} : (@all (_5621 -> prod _5630 _5631)) = (@all (_5621 -> prod _5630 _5631)).
Proof. exact (eq_refl (@all (_5621 -> prod _5630 _5631))). Qed.
Lemma lem54845 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) : (term19 _5621 _5630 _5631 P) = (term25 _5621 _5630 _5631 P).
Proof. exact (MK_COMB (@lem54844 _5621 _5630 _5631) (@lem54843 _5621 _5630 _5631 P)). Qed.
Lemma lem54846 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem54847 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) : (term26 _5621 _5630 _5631 P) = (term27 _5621 _5630 _5631 P).
Proof. exact (MK_COMB (@lem54846) (@lem54845 _5621 _5630 _5631 P)). Qed.
Lemma lem54848 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) (g : _5621 -> _5630) (h : _5621 -> _5631) : (term28 _5621 _5630 _5631 P g h) = (term29 _5621 _5630 _5631 P g h).
Proof. exact (eq_refl (term28 _5621 _5630 _5631 P g h)). Qed.
Lemma lem54849 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) (g : _5621 -> _5630) : (term30 _5621 _5630 _5631 P g) = (term31 _5621 _5630 _5631 P g).
Proof. exact (fun_ext (fun h : _5621 -> _5631 => @lem54848 _5621 _5630 _5631 P g h)). Qed.
Lemma lem54850 {_5621 _5631 : Type'} : (@all (_5621 -> _5631)) = (@all (_5621 -> _5631)).
Proof. exact (eq_refl (@all (_5621 -> _5631))). Qed.
Lemma lem54851 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) (g : _5621 -> _5630) : (term32 _5621 _5630 _5631 P g) = (term33 _5621 _5630 _5631 P g).
Proof. exact (MK_COMB (@lem54850 _5621 _5631) (@lem54849 _5621 _5630 _5631 P g)). Qed.
Lemma lem54852 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) : (term34 _5621 _5630 _5631 P) = (term35 _5621 _5630 _5631 P).
Proof. exact (fun_ext (fun g : _5621 -> _5630 => @lem54851 _5621 _5630 _5631 P g)). Qed.
Lemma lem54853 {_5621 _5630 : Type'} : (@all (_5621 -> _5630)) = (@all (_5621 -> _5630)).
Proof. exact (eq_refl (@all (_5621 -> _5630))). Qed.
Lemma lem54854 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) : (term20 _5621 _5630 _5631 P) = (term36 _5621 _5630 _5631 P).
Proof. exact (MK_COMB (@lem54853 _5621 _5630) (@lem54852 _5621 _5630 _5631 P)). Qed.
Lemma lem54855 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) : ((term19 _5621 _5630 _5631 P) = (term20 _5621 _5630 _5631 P)) = ((term25 _5621 _5630 _5631 P) = (term36 _5621 _5630 _5631 P)).
Proof. exact (MK_COMB (@lem54847 _5621 _5630 _5631 P) (@lem54854 _5621 _5630 _5631 P)). Qed.
Lemma lem54856 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) : (term25 _5621 _5630 _5631 P) = (term36 _5621 _5630 _5631 P).
Proof. exact (EQ_MP (@lem54855 _5621 _5630 _5631 P) (@lem54841 _5621 _5630 _5631 P)). Qed.
Lemma lem54870 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term5 A B C f g).
Proof. exact (EQ_MP (@lem54794 A B C f g) (@lem54793 A B C f g)). Qed.
Lemma lem54871 {_5621 _5630 _5631 : Type'} (f : type1207 _5630 _5631) (g : type1430 _5621 _5630 _5631) : (@o _5621 (prod _5630 _5631) _5630 f g) = (term37 _5621 _5630 _5631 f g).
Proof. exact (@lem54870 _5621 (prod _5630 _5631) _5630 f g). Qed.
Lemma lem54872 {_5621 _5630 _5631 : Type'} (g : _5621 -> _5630) (h : _5621 -> _5631) : (term38 _5621 _5630 _5631 g h) = (term39 _5621 _5630 _5631 g h).
Proof. exact (@lem54871 _5621 _5630 _5631 (@fst _5630 _5631) (term40 _5621 _5630 _5631 g h)). Qed.
Lemma lem54874 {A B : Type'} (f : A -> B) (y : A) : (term41 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem54875 {_5621 _5630 _5631 : Type'} (f : type1430 _5621 _5630 _5631) (y : _5621) : (term42 _5621 _5630 _5631 f y) = (f y).
Proof. exact (@lem54874 _5621 (prod _5630 _5631) f y). Qed.
Lemma lem54876 {_5621 _5630 _5631 : Type'} (g : _5621 -> _5630) (h : _5621 -> _5631) (x : _5621) : (term43 _5621 _5630 _5631 g h x) = (term44 _5621 _5630 _5631 g h x).
Proof. exact (@lem54875 _5621 _5630 _5631 (term40 _5621 _5630 _5631 g h) x). Qed.
Lemma lem54877 {_5621 _5630 _5631 : Type'} (g : _5621 -> _5630) (h : _5621 -> _5631) (a : _5621) : (term44 _5621 _5630 _5631 g h a) = (term45 _5621 _5630 _5631 g h a).
Proof. exact (eq_refl (term44 _5621 _5630 _5631 g h a)). Qed.
Lemma lem54878 {_5621 _5630 _5631 : Type'} (g : _5621 -> _5630) (h : _5621 -> _5631) : (term46 _5621 _5630 _5631 g h) = (term40 _5621 _5630 _5631 g h).
Proof. exact (fun_ext (fun a : _5621 => @lem54877 _5621 _5630 _5631 g h a)). Qed.
Lemma lem54879 {_5621 : Type'} (x : _5621) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem54880 {_5621 _5630 _5631 : Type'} (g : _5621 -> _5630) (h : _5621 -> _5631) (x : _5621) : (term43 _5621 _5630 _5631 g h x) = (term44 _5621 _5630 _5631 g h x).
Proof. exact (MK_COMB (@lem54878 _5621 _5630 _5631 g h) (@lem54879 _5621 x)). Qed.
Lemma lem54881 {_5630 _5631 : Type'} : (@eq (prod _5630 _5631)) = (@eq (prod _5630 _5631)).
Proof. exact (eq_refl (@eq (prod _5630 _5631))). Qed.
Lemma lem54882 {_5621 _5630 _5631 : Type'} (g : _5621 -> _5630) (h : _5621 -> _5631) (x : _5621) : (term47 _5621 _5630 _5631 g h x) = (term48 _5621 _5630 _5631 g h x).
Proof. exact (MK_COMB (@lem54881 _5630 _5631) (@lem54880 _5621 _5630 _5631 g h x)). Qed.
Lemma lem54883 {_5621 _5630 _5631 : Type'} (g : _5621 -> _5630) (h : _5621 -> _5631) (x : _5621) : (term44 _5621 _5630 _5631 g h x) = (term45 _5621 _5630 _5631 g h x).
Proof. exact (eq_refl (term44 _5621 _5630 _5631 g h x)). Qed.
Lemma lem54884 {_5621 _5630 _5631 : Type'} (g : _5621 -> _5630) (h : _5621 -> _5631) (x : _5621) : ((term43 _5621 _5630 _5631 g h x) = (term44 _5621 _5630 _5631 g h x)) = ((term44 _5621 _5630 _5631 g h x) = (term45 _5621 _5630 _5631 g h x)).
Proof. exact (MK_COMB (@lem54882 _5621 _5630 _5631 g h x) (@lem54883 _5621 _5630 _5631 g h x)). Qed.
Lemma lem54885 {_5621 _5630 _5631 : Type'} (g : _5621 -> _5630) (h : _5621 -> _5631) (x : _5621) : (term44 _5621 _5630 _5631 g h x) = (term45 _5621 _5630 _5631 g h x).
Proof. exact (EQ_MP (@lem54884 _5621 _5630 _5631 g h x) (@lem54876 _5621 _5630 _5631 g h x)). Qed.
Lemma lem54886 {_5630 _5631 : Type'} : (@fst _5630 _5631) = (@fst _5630 _5631).
Proof. exact (eq_refl (@fst _5630 _5631)). Qed.
Lemma lem54887 {_5621 _5630 _5631 : Type'} (g : _5621 -> _5630) (h : _5621 -> _5631) (x : _5621) : (term49 _5621 _5630 _5631 g h x) = (term50 _5621 _5630 _5631 g h x).
Proof. exact (MK_COMB (@lem54886 _5630 _5631) (@lem54885 _5621 _5630 _5631 g h x)). Qed.
Lemma lem54889 {A B : Type'} (y : B) (x : A) : (term51 A B x y) = x.
Proof. exact (EQ_MP (@lem48220 A B y x) (@lem48219 A B x y)). Qed.
Lemma lem54890 {_5630 _5631 : Type'} (y : _5631) (x : _5630) : (term51 _5630 _5631 x y) = x.
Proof. exact (@lem54889 _5630 _5631 y x). Qed.
Lemma lem54891 {_5621 _5630 _5631 : Type'} (h : _5621 -> _5631) (g : _5621 -> _5630) (x : _5621) : (term50 _5621 _5630 _5631 g h x) = (g x).
Proof. exact (@lem54890 _5630 _5631 (h x) (g x)). Qed.
Lemma lem54892 {_5621 _5630 _5631 : Type'} (h : _5621 -> _5631) (g : _5621 -> _5630) (x : _5621) : (term49 _5621 _5630 _5631 g h x) = (g x).
Proof. exact (TRANS (@lem54887 _5621 _5630 _5631 g h x) (@lem54891 _5621 _5630 _5631 h g x)). Qed.
Lemma lem54893 {_5621 _5630 _5631 : Type'} (h : _5621 -> _5631) (g : _5621 -> _5630) : (term39 _5621 _5630 _5631 g h) = (term1 _5621 _5630 g).
Proof. exact (fun_ext (fun x : _5621 => @lem54892 _5621 _5630 _5631 h g x)). Qed.
Lemma lem54894 {_5621 _5630 : Type'} (t : _5621 -> _5630) : (term1 _5621 _5630 t) = t.
Proof. exact (@lem54789 _5621 _5630 t). Qed.
Lemma lem54895 {_5621 _5630 : Type'} (g : _5621 -> _5630) : (term1 _5621 _5630 g) = g.
Proof. exact (@lem54894 _5621 _5630 g). Qed.
Lemma lem54896 {_5621 _5630 _5631 : Type'} (h : _5621 -> _5631) (g : _5621 -> _5630) : (term39 _5621 _5630 _5631 g h) = g.
Proof. exact (TRANS (@lem54893 _5621 _5630 _5631 h g) (@lem54895 _5621 _5630 g)). Qed.
Lemma lem54897 {_5621 _5630 _5631 : Type'} (h : _5621 -> _5631) (g : _5621 -> _5630) : (term38 _5621 _5630 _5631 g h) = g.
Proof. exact (TRANS (@lem54872 _5621 _5630 _5631 g h) (@lem54896 _5621 _5630 _5631 h g)). Qed.
Lemma lem54898 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem54899 {_5621 _5630 _5631 : Type'} (h : _5621 -> _5631) (P : type524 _5621 _5630 _5631) (g : _5621 -> _5630) : (term52 _5621 _5630 _5631 P g h) = (P g).
Proof. exact (MK_COMB (@lem54898 _5621 _5630 _5631 P) (@lem54897 _5621 _5630 _5631 h g)). Qed.
Lemma lem54901 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term5 A B C f g).
Proof. exact (EQ_MP (@lem54794 A B C f g) (@lem54793 A B C f g)). Qed.
Lemma lem54902 {_5621 _5630 _5631 : Type'} (f : type1208 _5630 _5631) (g : type1430 _5621 _5630 _5631) : (@o _5621 (prod _5630 _5631) _5631 f g) = (term53 _5621 _5630 _5631 f g).
Proof. exact (@lem54901 _5621 (prod _5630 _5631) _5631 f g). Qed.
Lemma lem54903 {_5621 _5630 _5631 : Type'} (g : _5621 -> _5630) (h : _5621 -> _5631) : (term54 _5621 _5630 _5631 g h) = (term55 _5621 _5630 _5631 g h).
Proof. exact (@lem54902 _5621 _5630 _5631 (@snd _5630 _5631) (term40 _5621 _5630 _5631 g h)). Qed.
Lemma lem54905 {A B : Type'} (f : A -> B) (y : A) : (term41 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem54906 {_5621 _5630 _5631 : Type'} (f : type1430 _5621 _5630 _5631) (y : _5621) : (term42 _5621 _5630 _5631 f y) = (f y).
Proof. exact (@lem54905 _5621 (prod _5630 _5631) f y). Qed.
Lemma lem54907 {_5621 _5630 _5631 : Type'} (g : _5621 -> _5630) (h : _5621 -> _5631) (x : _5621) : (term43 _5621 _5630 _5631 g h x) = (term44 _5621 _5630 _5631 g h x).
Proof. exact (@lem54906 _5621 _5630 _5631 (term40 _5621 _5630 _5631 g h) x). Qed.
Lemma lem54908 {_5621 _5630 _5631 : Type'} (g : _5621 -> _5630) (h : _5621 -> _5631) (a : _5621) : (term44 _5621 _5630 _5631 g h a) = (term45 _5621 _5630 _5631 g h a).
Proof. exact (eq_refl (term44 _5621 _5630 _5631 g h a)). Qed.
Lemma lem54909 {_5621 _5630 _5631 : Type'} (g : _5621 -> _5630) (h : _5621 -> _5631) : (term46 _5621 _5630 _5631 g h) = (term40 _5621 _5630 _5631 g h).
Proof. exact (fun_ext (fun a : _5621 => @lem54908 _5621 _5630 _5631 g h a)). Qed.
Lemma lem54910 {_5621 : Type'} (x : _5621) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem54911 {_5621 _5630 _5631 : Type'} (g : _5621 -> _5630) (h : _5621 -> _5631) (x : _5621) : (term43 _5621 _5630 _5631 g h x) = (term44 _5621 _5630 _5631 g h x).
Proof. exact (MK_COMB (@lem54909 _5621 _5630 _5631 g h) (@lem54910 _5621 x)). Qed.
Lemma lem54912 {_5630 _5631 : Type'} : (@eq (prod _5630 _5631)) = (@eq (prod _5630 _5631)).
Proof. exact (eq_refl (@eq (prod _5630 _5631))). Qed.
Lemma lem54913 {_5621 _5630 _5631 : Type'} (g : _5621 -> _5630) (h : _5621 -> _5631) (x : _5621) : (term47 _5621 _5630 _5631 g h x) = (term48 _5621 _5630 _5631 g h x).
Proof. exact (MK_COMB (@lem54912 _5630 _5631) (@lem54911 _5621 _5630 _5631 g h x)). Qed.
Lemma lem54914 {_5621 _5630 _5631 : Type'} (g : _5621 -> _5630) (h : _5621 -> _5631) (x : _5621) : (term44 _5621 _5630 _5631 g h x) = (term45 _5621 _5630 _5631 g h x).
Proof. exact (eq_refl (term44 _5621 _5630 _5631 g h x)). Qed.
Lemma lem54915 {_5621 _5630 _5631 : Type'} (g : _5621 -> _5630) (h : _5621 -> _5631) (x : _5621) : ((term43 _5621 _5630 _5631 g h x) = (term44 _5621 _5630 _5631 g h x)) = ((term44 _5621 _5630 _5631 g h x) = (term45 _5621 _5630 _5631 g h x)).
Proof. exact (MK_COMB (@lem54913 _5621 _5630 _5631 g h x) (@lem54914 _5621 _5630 _5631 g h x)). Qed.
Lemma lem54916 {_5621 _5630 _5631 : Type'} (g : _5621 -> _5630) (h : _5621 -> _5631) (x : _5621) : (term44 _5621 _5630 _5631 g h x) = (term45 _5621 _5630 _5631 g h x).
Proof. exact (EQ_MP (@lem54915 _5621 _5630 _5631 g h x) (@lem54907 _5621 _5630 _5631 g h x)). Qed.
Lemma lem54917 {_5630 _5631 : Type'} : (@snd _5630 _5631) = (@snd _5630 _5631).
Proof. exact (eq_refl (@snd _5630 _5631)). Qed.
Lemma lem54918 {_5621 _5630 _5631 : Type'} (g : _5621 -> _5630) (h : _5621 -> _5631) (x : _5621) : (term56 _5621 _5630 _5631 g h x) = (term57 _5621 _5630 _5631 g h x).
Proof. exact (MK_COMB (@lem54917 _5630 _5631) (@lem54916 _5621 _5630 _5631 g h x)). Qed.
Lemma lem54920 {A B : Type'} (x : A) (y : B) : (term58 A B x y) = y.
Proof. exact (EQ_MP (@lem48214 A B x y) (@lem48213 A B x y)). Qed.
Lemma lem54921 {_5630 _5631 : Type'} (x : _5630) (y : _5631) : (term58 _5630 _5631 x y) = y.
Proof. exact (@lem54920 _5630 _5631 x y). Qed.
Lemma lem54922 {_5621 _5630 _5631 : Type'} (g : _5621 -> _5630) (h : _5621 -> _5631) (x : _5621) : (term57 _5621 _5630 _5631 g h x) = (h x).
Proof. exact (@lem54921 _5630 _5631 (g x) (h x)). Qed.
Lemma lem54923 {_5621 _5630 _5631 : Type'} (g : _5621 -> _5630) (h : _5621 -> _5631) (x : _5621) : (term56 _5621 _5630 _5631 g h x) = (h x).
Proof. exact (TRANS (@lem54918 _5621 _5630 _5631 g h x) (@lem54922 _5621 _5630 _5631 g h x)). Qed.
Lemma lem54924 {_5621 _5630 _5631 : Type'} (g : _5621 -> _5630) (h : _5621 -> _5631) : (term55 _5621 _5630 _5631 g h) = (term1 _5621 _5631 h).
Proof. exact (fun_ext (fun x : _5621 => @lem54923 _5621 _5630 _5631 g h x)). Qed.
Lemma lem54925 {_5621 _5631 : Type'} (t : _5621 -> _5631) : (term1 _5621 _5631 t) = t.
Proof. exact (@lem54789 _5621 _5631 t). Qed.
Lemma lem54926 {_5621 _5631 : Type'} (h : _5621 -> _5631) : (term1 _5621 _5631 h) = h.
Proof. exact (@lem54925 _5621 _5631 h). Qed.
Lemma lem54927 {_5621 _5630 _5631 : Type'} (g : _5621 -> _5630) (h : _5621 -> _5631) : (term55 _5621 _5630 _5631 g h) = h.
Proof. exact (TRANS (@lem54924 _5621 _5630 _5631 g h) (@lem54926 _5621 _5631 h)). Qed.
Lemma lem54928 {_5621 _5630 _5631 : Type'} (g : _5621 -> _5630) (h : _5621 -> _5631) : (term54 _5621 _5630 _5631 g h) = h.
Proof. exact (TRANS (@lem54903 _5621 _5630 _5631 g h) (@lem54927 _5621 _5630 _5631 g h)). Qed.
Lemma lem54929 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) (g : _5621 -> _5630) (h : _5621 -> _5631) : (term29 _5621 _5630 _5631 P g h) = (P g h).
Proof. exact (MK_COMB (@lem54899 _5621 _5630 _5631 h P g) (@lem54928 _5621 _5630 _5631 g h)). Qed.
Lemma lem54930 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) (g : _5621 -> _5630) : (term31 _5621 _5630 _5631 P g) = (term10 _5621 _5630 _5631 P g).
Proof. exact (fun_ext (fun h : _5621 -> _5631 => @lem54929 _5621 _5630 _5631 P g h)). Qed.
Lemma lem54931 {_5621 _5631 : Type'} (t : type572 _5621 _5631) : (term9 _5621 _5631 t) = t.
Proof. exact (@lem54789 (_5621 -> _5631) Prop t). Qed.
Lemma lem54932 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) (g : _5621 -> _5630) : (term10 _5621 _5630 _5631 P g) = (P g).
Proof. exact (@lem54931 _5621 _5631 (P g)). Qed.
Lemma lem54933 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) (g : _5621 -> _5630) : (term31 _5621 _5630 _5631 P g) = (P g).
Proof. exact (TRANS (@lem54930 _5621 _5630 _5631 P g) (@lem54932 _5621 _5630 _5631 P g)). Qed.
Lemma lem54934 {_5621 _5631 : Type'} : (@all (_5621 -> _5631)) = (@all (_5621 -> _5631)).
Proof. exact (eq_refl (@all (_5621 -> _5631))). Qed.
Lemma lem54935 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) (g : _5621 -> _5630) : (term33 _5621 _5630 _5631 P g) = (term12 _5621 _5630 _5631 P g).
Proof. exact (MK_COMB (@lem54934 _5621 _5631) (@lem54933 _5621 _5630 _5631 P g)). Qed.
Lemma lem54936 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) : (term35 _5621 _5630 _5631 P) = (term14 _5621 _5630 _5631 P).
Proof. exact (fun_ext (fun g : _5621 -> _5630 => @lem54935 _5621 _5630 _5631 P g)). Qed.
Lemma lem54937 {_5621 _5630 : Type'} : (@all (_5621 -> _5630)) = (@all (_5621 -> _5630)).
Proof. exact (eq_refl (@all (_5621 -> _5630))). Qed.
Lemma lem54938 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) : (term36 _5621 _5630 _5631 P) = (term16 _5621 _5630 _5631 P).
Proof. exact (MK_COMB (@lem54937 _5621 _5630) (@lem54936 _5621 _5630 _5631 P)). Qed.
Lemma lem54945 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) : (term25 _5621 _5630 _5631 P) = (term16 _5621 _5630 _5631 P).
Proof. exact (TRANS (@lem54856 _5621 _5630 _5631 P) (@lem54938 _5621 _5630 _5631 P)). Qed.
Lemma lem54946 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) : ((term15 _5621 _5630 _5631 P) = (term25 _5621 _5630 _5631 P)) = ((term16 _5621 _5630 _5631 P) = (term16 _5621 _5630 _5631 P)).
Proof. exact (MK_COMB (@lem54833 _5621 _5630 _5631 P) (@lem54945 _5621 _5630 _5631 P)). Qed.
Lemma lem54948 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem54949 (x : Prop) : (x = x) = True.
Proof. exact (@lem54948 Prop x). Qed.
Lemma lem54950 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) : ((term16 _5621 _5630 _5631 P) = (term16 _5621 _5630 _5631 P)) = True.
Proof. exact (@lem54949 (term16 _5621 _5630 _5631 P)). Qed.
Lemma lem54953 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) : (term59 _5621 _5630 _5631 P) = (term59 _5621 _5630 _5631 P).
Proof. exact (eq_refl (term59 _5621 _5630 _5631 P)). Qed.
Lemma lem54954 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) : (term59 _5621 _5630 _5631 P) = (((term16 _5621 _5630 _5631 P) = (term16 _5621 _5630 _5631 P)) = True).
Proof. exact (eq_refl (term59 _5621 _5630 _5631 P)). Qed.
Lemma lem54955 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) : (term60 _5621 _5630 _5631 P) = (term60 _5621 _5630 _5631 P).
Proof. exact (eq_refl (term60 _5621 _5630 _5631 P)). Qed.
Lemma lem54956 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) : ((term59 _5621 _5630 _5631 P) = (term59 _5621 _5630 _5631 P)) = ((term59 _5621 _5630 _5631 P) = (((term16 _5621 _5630 _5631 P) = (term16 _5621 _5630 _5631 P)) = True)).
Proof. exact (MK_COMB (@lem54955 _5621 _5630 _5631 P) (@lem54954 _5621 _5630 _5631 P)). Qed.
Lemma lem54957 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) : (term59 _5621 _5630 _5631 P) = (((term16 _5621 _5630 _5631 P) = (term16 _5621 _5630 _5631 P)) = True).
Proof. exact (eq_refl (term59 _5621 _5630 _5631 P)). Qed.
Lemma lem54958 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem54959 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) : (term60 _5621 _5630 _5631 P) = (term61 _5621 _5630 _5631 P).
Proof. exact (MK_COMB (@lem54958) (@lem54957 _5621 _5630 _5631 P)). Qed.
Lemma lem54960 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) : (((term16 _5621 _5630 _5631 P) = (term16 _5621 _5630 _5631 P)) = True) = (((term16 _5621 _5630 _5631 P) = (term16 _5621 _5630 _5631 P)) = True).
Proof. exact (eq_refl (((term16 _5621 _5630 _5631 P) = (term16 _5621 _5630 _5631 P)) = True)). Qed.
Lemma lem54961 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) : ((term59 _5621 _5630 _5631 P) = (((term16 _5621 _5630 _5631 P) = (term16 _5621 _5630 _5631 P)) = True)) = ((((term16 _5621 _5630 _5631 P) = (term16 _5621 _5630 _5631 P)) = True) = (((term16 _5621 _5630 _5631 P) = (term16 _5621 _5630 _5631 P)) = True)).
Proof. exact (MK_COMB (@lem54959 _5621 _5630 _5631 P) (@lem54960 _5621 _5630 _5631 P)). Qed.
Lemma lem54962 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) : ((term59 _5621 _5630 _5631 P) = (term59 _5621 _5630 _5631 P)) = ((((term16 _5621 _5630 _5631 P) = (term16 _5621 _5630 _5631 P)) = True) = (((term16 _5621 _5630 _5631 P) = (term16 _5621 _5630 _5631 P)) = True)).
Proof. exact (TRANS (@lem54956 _5621 _5630 _5631 P) (@lem54961 _5621 _5630 _5631 P)). Qed.
Lemma lem54963 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) : (((term16 _5621 _5630 _5631 P) = (term16 _5621 _5630 _5631 P)) = True) = (((term16 _5621 _5630 _5631 P) = (term16 _5621 _5630 _5631 P)) = True).
Proof. exact (EQ_MP (@lem54962 _5621 _5630 _5631 P) (@lem54953 _5621 _5630 _5631 P)). Qed.
Lemma lem54964 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) : ((term16 _5621 _5630 _5631 P) = (term16 _5621 _5630 _5631 P)) = True.
Proof. exact (EQ_MP (@lem54963 _5621 _5630 _5631 P) (@lem54950 _5621 _5630 _5631 P)). Qed.
Lemma lem54965 {_5621 _5630 _5631 : Type'} (P : type524 _5621 _5630 _5631) : ((term15 _5621 _5630 _5631 P) = (term25 _5621 _5630 _5631 P)) = True.
Proof. exact (TRANS (@lem54946 _5621 _5630 _5631 P) (@lem54964 _5621 _5630 _5631 P)). Qed.
Lemma lem54966 {_5621 _5630 _5631 : Type'} : (term62 _5621 _5630 _5631) = (term63 _5621 _5630 _5631).
Proof. exact (fun_ext (fun P : type524 _5621 _5630 _5631 => @lem54965 _5621 _5630 _5631 P)). Qed.
Lemma lem54967 {_5621 _5630 _5631 : Type'} : (@all ((_5621 -> _5630) -> (_5621 -> _5631) -> Prop)) = (@all ((_5621 -> _5630) -> (_5621 -> _5631) -> Prop)).
Proof. exact (eq_refl (@all ((_5621 -> _5630) -> (_5621 -> _5631) -> Prop))). Qed.
Lemma lem54968 {_5621 _5630 _5631 : Type'} : (term64 _5621 _5630 _5631) = (term65 _5621 _5630 _5631).
Proof. exact (MK_COMB (@lem54967 _5621 _5630 _5631) (@lem54966 _5621 _5630 _5631)). Qed.
Lemma lem54970 {A : Type'} (t : Prop) : (term66 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem54971 {_5621 _5630 _5631 : Type'} (t : Prop) : (term67 _5621 _5630 _5631 t) = t.
Proof. exact (@lem54970 (type524 _5621 _5630 _5631) t). Qed.
Lemma lem54972 {_5621 _5630 _5631 : Type'} : (term65 _5621 _5630 _5631) = True.
Proof. exact (@lem54971 _5621 _5630 _5631 True). Qed.
Lemma lem54973 {_5621 _5630 _5631 : Type'} : (term64 _5621 _5630 _5631) = True.
Proof. exact (TRANS (@lem54968 _5621 _5630 _5631) (@lem54972 _5621 _5630 _5631)). Qed.
Lemma lem54974 {_5621 _5630 _5631 : Type'} : True = (term64 _5621 _5630 _5631).
Proof. exact (SYM (@lem54973 _5621 _5630 _5631)). Qed.
Lemma lem54977 {_5621 _5630 _5631 : Type'} : term64 _5621 _5630 _5631.
Proof. exact (EQ_MP (@lem54974 _5621 _5630 _5631) (@lem0)). Qed.
