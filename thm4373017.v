Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4373017_term_abbrevs.
Require Import EXTENSION_spec.
Require Import FORALL_PAIR_THM_spec.
Require Import IN_CROSS_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm3464405_spec.
Require Import thm3464408_spec.
Lemma lem4372728 {_103718 _103721 : Type'} (x : _103718) : term0 _103718 _103721 x.
Proof. exact (@lem4325365 _103718 _103721 x). Qed.
Lemma lem4372729 {_103718 _103721 : Type'} (x : _103718) : (term0 _103718 _103721 x) = (term1 _103718 _103721 x).
Proof. exact (eq_refl (term0 _103718 _103721 x)). Qed.
Lemma lem4372730 {_103718 _103721 : Type'} (x : _103718) : term1 _103718 _103721 x.
Proof. exact (EQ_MP (@lem4372729 _103718 _103721 x) (@lem4372728 _103718 _103721 x)). Qed.
Lemma lem4372731 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term2 _103718 _103721 x y.
Proof. exact (@lem4372730 _103718 _103721 x y). Qed.
Lemma lem4372732 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : (term2 _103718 _103721 x y) = (term3 _103718 _103721 x y).
Proof. exact (eq_refl (term2 _103718 _103721 x y)). Qed.
Lemma lem4372733 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term3 _103718 _103721 x y.
Proof. exact (EQ_MP (@lem4372732 _103718 _103721 x y) (@lem4372731 _103718 _103721 x y)). Qed.
Lemma lem4372734 {_103718 _103721 : Type'} (x : _103718) (y : _103721) (s : _103718 -> Prop) : term4 _103718 _103721 x y s.
Proof. exact (@lem4372733 _103718 _103721 x y s). Qed.
Lemma lem4372735 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : (term4 _103718 _103721 x y s) = (term5 _103718 _103721 x s y).
Proof. exact (eq_refl (term4 _103718 _103721 x y s)). Qed.
Lemma lem4372736 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : term5 _103718 _103721 x s y.
Proof. exact (EQ_MP (@lem4372735 _103718 _103721 x s y) (@lem4372734 _103718 _103721 x y s)). Qed.
Lemma lem4372737 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : term6 _103718 _103721 x s y t.
Proof. exact (@lem4372736 _103718 _103721 x s y t). Qed.
Lemma lem4372738 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term6 _103718 _103721 x s y t) = ((term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t)).
Proof. exact (eq_refl (term6 _103718 _103721 x s y t)). Qed.
Lemma lem4372764 {_83095 : Type'} : term9 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4372765 {_83095 : Type'} (p : _83095 -> Prop) : term10 _83095 p.
Proof. exact (@lem4372764 _83095 p). Qed.
Lemma lem4372766 {_83095 : Type'} (p : _83095 -> Prop) : (term10 _83095 p) = (term11 _83095 p).
Proof. exact (eq_refl (term10 _83095 p)). Qed.
Lemma lem4372767 {_83095 : Type'} (p : _83095 -> Prop) : term11 _83095 p.
Proof. exact (EQ_MP (@lem4372766 _83095 p) (@lem4372765 _83095 p)). Qed.
Lemma lem4372768 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term12 _83095 p x.
Proof. exact (@lem4372767 _83095 p x). Qed.
Lemma lem4372769 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term12 _83095 p x) = ((term13 _83095 x p) = (p x)).
Proof. exact (eq_refl (term12 _83095 p x)). Qed.
Lemma lem4372778 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term14 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem4372779 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term14 _5106 _5107 P) = ((term15 _5106 _5107 P) = (term16 _5106 _5107 P)).
Proof. exact (eq_refl (term14 _5106 _5107 P)). Qed.
Lemma lem4372781 {A : Type'} (s : A -> Prop) : term17 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4372782 {A : Type'} (s : A -> Prop) : (term17 A s) = (term18 A s).
Proof. exact (eq_refl (term17 A s)). Qed.
Lemma lem4372783 {A : Type'} (s : A -> Prop) : term18 A s.
Proof. exact (EQ_MP (@lem4372782 A s) (@lem4372781 A s)). Qed.
Lemma lem4372784 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term19 A s t.
Proof. exact (@lem4372783 A s t). Qed.
Lemma lem4372785 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term19 A s t) = ((s = t) = (term20 A s t)).
Proof. exact (eq_refl (term19 A s t)). Qed.
Lemma lem4372802 {_89711 _89725 : Type'} : term21 _89711 _89725.
Proof. exact (EQ_MP (@lem3464408 _89711 _89725) (@lem3464405 _89711 _89725)). Qed.
Lemma lem4372803 {_89711 _89725 : Type'} (P : _89725 -> Prop) : term22 _89711 _89725 P.
Proof. exact (@lem4372802 _89711 _89725 P). Qed.
Lemma lem4372804 {_89711 _89725 : Type'} (P : _89725 -> Prop) : (term22 _89711 _89725 P) = (term23 _89711 _89725 P).
Proof. exact (eq_refl (term22 _89711 _89725 P)). Qed.
Lemma lem4372805 {_89711 _89725 : Type'} (P : _89725 -> Prop) : term23 _89711 _89725 P.
Proof. exact (EQ_MP (@lem4372804 _89711 _89725 P) (@lem4372803 _89711 _89725 P)). Qed.
Lemma lem4372806 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : term24 _89711 _89725 P f.
Proof. exact (@lem4372805 _89711 _89725 P f). Qed.
Lemma lem4372807 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term24 _89711 _89725 P f) = ((term25 _89711 _89725 P f) = (term26 _89711 _89725 P f)).
Proof. exact (eq_refl (term24 _89711 _89725 P f)). Qed.
Lemma lem4372825 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term20 A s t).
Proof. exact (EQ_MP (@lem4372785 A s t) (@lem4372784 A s t)). Qed.
Lemma lem4372826 {_104907 _104908 : Type'} (s : type1210 _104907 _104908) (t : type1210 _104907 _104908) : (s = t) = (term27 _104907 _104908 s t).
Proof. exact (@lem4372825 (prod _104907 _104908) s t). Qed.
Lemma lem4372827 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : ((term28 _104907 _104908 f g) = (term29 _104907 _104908 f)) = (term30 _104907 _104908 g f).
Proof. exact (@lem4372826 _104907 _104908 (term28 _104907 _104908 f g) (term29 _104907 _104908 f)). Qed.
Lemma lem4372833 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term15 _5106 _5107 P) = (term16 _5106 _5107 P).
Proof. exact (EQ_MP (@lem4372779 _5106 _5107 P) (@lem4372778 _5106 _5107 P)). Qed.
Lemma lem4372834 {_104907 _104908 : Type'} (P : type1210 _104907 _104908) : (term31 _104907 _104908 P) = (term32 _104907 _104908 P).
Proof. exact (@lem4372833 _104908 _104907 P). Qed.
Lemma lem4372835 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : (term33 _104907 _104908 g f) = (term34 _104907 _104908 g f).
Proof. exact (@lem4372834 _104907 _104908 (term35 _104907 _104908 g f)). Qed.
Lemma lem4372836 {_104907 _104908 : Type'} (g : type686 _104908) (x : prod _104907 _104908) (f : type686 _104907) : (term36 _104907 _104908 g f x) = ((term37 _104907 _104908 x f g) = (term38 _104907 _104908 x f)).
Proof. exact (eq_refl (term36 _104907 _104908 g f x)). Qed.
Lemma lem4372837 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : (term39 _104907 _104908 g f) = (term35 _104907 _104908 g f).
Proof. exact (fun_ext (fun x : prod _104907 _104908 => @lem4372836 _104907 _104908 g x f)). Qed.
Lemma lem4372838 {_104907 _104908 : Type'} : (@all (prod _104907 _104908)) = (@all (prod _104907 _104908)).
Proof. exact (eq_refl (@all (prod _104907 _104908))). Qed.
Lemma lem4372839 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : (term33 _104907 _104908 g f) = (term30 _104907 _104908 g f).
Proof. exact (MK_COMB (@lem4372838 _104907 _104908) (@lem4372837 _104907 _104908 g f)). Qed.
Lemma lem4372840 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4372841 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : (term40 _104907 _104908 g f) = (term41 _104907 _104908 g f).
Proof. exact (MK_COMB (@lem4372840) (@lem4372839 _104907 _104908 g f)). Qed.
Lemma lem4372842 {_104907 _104908 : Type'} (g : type686 _104908) (p1 : _104907) (p2 : _104908) (f : type686 _104907) : (term42 _104907 _104908 g f p1 p2) = ((term43 _104907 _104908 p1 p2 f g) = (term44 _104907 _104908 p1 p2 f)).
Proof. exact (eq_refl (term42 _104907 _104908 g f p1 p2)). Qed.
Lemma lem4372843 {_104907 _104908 : Type'} (g : type686 _104908) (p1 : _104907) (f : type686 _104907) : (term45 _104907 _104908 g f p1) = (term46 _104907 _104908 g p1 f).
Proof. exact (fun_ext (fun p2 : _104908 => @lem4372842 _104907 _104908 g p1 p2 f)). Qed.
Lemma lem4372844 {_104908 : Type'} : (@all _104908) = (@all _104908).
Proof. exact (eq_refl (@all _104908)). Qed.
Lemma lem4372845 {_104907 _104908 : Type'} (g : type686 _104908) (p1 : _104907) (f : type686 _104907) : (term47 _104907 _104908 g f p1) = (term48 _104907 _104908 g p1 f).
Proof. exact (MK_COMB (@lem4372844 _104908) (@lem4372843 _104907 _104908 g p1 f)). Qed.
Lemma lem4372846 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : (term49 _104907 _104908 g f) = (term50 _104907 _104908 g f).
Proof. exact (fun_ext (fun p1 : _104907 => @lem4372845 _104907 _104908 g p1 f)). Qed.
Lemma lem4372847 {_104907 : Type'} : (@all _104907) = (@all _104907).
Proof. exact (eq_refl (@all _104907)). Qed.
Lemma lem4372848 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : (term34 _104907 _104908 g f) = (term51 _104907 _104908 g f).
Proof. exact (MK_COMB (@lem4372847 _104907) (@lem4372846 _104907 _104908 g f)). Qed.
Lemma lem4372849 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : ((term33 _104907 _104908 g f) = (term34 _104907 _104908 g f)) = ((term30 _104907 _104908 g f) = (term51 _104907 _104908 g f)).
Proof. exact (MK_COMB (@lem4372841 _104907 _104908 g f) (@lem4372848 _104907 _104908 g f)). Qed.
Lemma lem4372850 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : (term30 _104907 _104908 g f) = (term51 _104907 _104908 g f).
Proof. exact (EQ_MP (@lem4372849 _104907 _104908 g f) (@lem4372835 _104907 _104908 g f)). Qed.
Lemma lem4372857 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : ((term28 _104907 _104908 f g) = (term29 _104907 _104908 f)) = (term51 _104907 _104908 g f).
Proof. exact (TRANS (@lem4372827 _104907 _104908 g f) (@lem4372850 _104907 _104908 g f)). Qed.
Lemma lem4372869 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4372738 _103718 _103721 x s y t) (@lem4372737 _103718 _103721 x s y t)). Qed.
Lemma lem4372870 {_104907 _104908 : Type'} (x : _104907) (s : _104907 -> Prop) (y : _104908) (t : _104908 -> Prop) : (term7 _104907 _104908 x y s t) = (term8 _104907 _104908 x s y t).
Proof. exact (@lem4372869 _104907 _104908 x s y t). Qed.
Lemma lem4372871 {_104907 _104908 : Type'} (p1 : _104907) (f : type686 _104907) (p2 : _104908) (g : type686 _104908) : (term43 _104907 _104908 p1 p2 f g) = (term52 _104907 _104908 p1 f p2 g).
Proof. exact (@lem4372870 _104907 _104908 p1 (@INTERS _104907 f) p2 (@INTERS _104908 g)). Qed.
Lemma lem4372875 {_104908 : Type'} (g : type686 _104908) (h1 : g = (@EMPTY (_104908 -> Prop))) : g = (@EMPTY (_104908 -> Prop)).
Proof. exact (h1). Qed.
Lemma lem4372876 {_104908 : Type'} : (@INTERS _104908) = (@INTERS _104908).
Proof. exact (eq_refl (@INTERS _104908)). Qed.
Lemma lem4372877 {_104908 : Type'} (g : type686 _104908) (h1 : g = (@EMPTY (_104908 -> Prop))) : (@INTERS _104908 g) = (@INTERS _104908 (@EMPTY (_104908 -> Prop))).
Proof. exact (MK_COMB (@lem4372876 _104908) (@lem4372875 _104908 g h1)). Qed.
Lemma lem4372878 {_104908 : Type'} (p2 : _104908) : (@IN _104908 p2) = (@IN _104908 p2).
Proof. exact (eq_refl (@IN _104908 p2)). Qed.
Lemma lem4372879 {_104908 : Type'} (p2 : _104908) (g : type686 _104908) (h1 : g = (@EMPTY (_104908 -> Prop))) : (term53 _104908 p2 g) = (term54 _104908 p2).
Proof. exact (MK_COMB (@lem4372878 _104908 p2) (@lem4372877 _104908 g h1)). Qed.
Lemma lem4372880 {_104907 : Type'} (p1 : _104907) (f : type686 _104907) : (term55 _104907 p1 f) = (term55 _104907 p1 f).
Proof. exact (eq_refl (term55 _104907 p1 f)). Qed.
Lemma lem4372881 {_104907 _104908 : Type'} (p1 : _104907) (f : type686 _104907) (p2 : _104908) (g : type686 _104908) (h1 : g = (@EMPTY (_104908 -> Prop))) : (term52 _104907 _104908 p1 f p2 g) = (term56 _104907 _104908 p1 f p2).
Proof. exact (MK_COMB (@lem4372880 _104907 p1 f) (@lem4372879 _104908 p2 g h1)). Qed.
Lemma lem4372884 {_104907 _104908 : Type'} (p1 : _104907) (f : type686 _104907) (p2 : _104908) (g : type686 _104908) (h1 : g = (@EMPTY (_104908 -> Prop))) : (term43 _104907 _104908 p1 p2 f g) = (term56 _104907 _104908 p1 f p2).
Proof. exact (TRANS (@lem4372871 _104907 _104908 p1 f p2 g) (@lem4372881 _104907 _104908 p1 f p2 g h1)). Qed.
Lemma lem4372885 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4372886 {_104907 _104908 : Type'} (p1 : _104907) (f : type686 _104907) (p2 : _104908) (g : type686 _104908) (h1 : g = (@EMPTY (_104908 -> Prop))) : (term57 _104907 _104908 p1 p2 f g) = (term58 _104907 _104908 p1 f p2).
Proof. exact (MK_COMB (@lem4372885) (@lem4372884 _104907 _104908 p1 f p2 g h1)). Qed.
Lemma lem4372888 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term25 _89711 _89725 P f) = (term26 _89711 _89725 P f).
Proof. exact (EQ_MP (@lem4372807 _89711 _89725 P f) (@lem4372806 _89711 _89725 P f)). Qed.
Lemma lem4372889 {_104907 _104908 : Type'} (P : type686 _104907) (f : type664 _104907 _104908) : (term59 _104907 _104908 P f) = (term60 _104907 _104908 P f).
Proof. exact (@lem4372888 (prod _104907 _104908) (_104907 -> Prop) P f). Qed.
Lemma lem4372890 {_104907 _104908 : Type'} (f : type686 _104907) : (term61 _104907 _104908 f) = (term62 _104907 _104908 f).
Proof. exact (@lem4372889 _104907 _104908 (term63 _104907 f) (term64 _104907 _104908)). Qed.
Lemma lem4372891 {_104907 : Type'} (s : _104907 -> Prop) (f : type686 _104907) : (term65 _104907 f s) = (@IN (_104907 -> Prop) s f).
Proof. exact (eq_refl (term65 _104907 f s)). Qed.
Lemma lem4372892 {_104907 _104908 : Type'} (GEN_PVAR_135 : type1210 _104907 _104908) : (@SETSPEC ((prod _104907 _104908) -> Prop) GEN_PVAR_135) = (@SETSPEC ((prod _104907 _104908) -> Prop) GEN_PVAR_135).
Proof. exact (eq_refl (@SETSPEC ((prod _104907 _104908) -> Prop) GEN_PVAR_135)). Qed.
Lemma lem4372893 {_104907 _104908 : Type'} (GEN_PVAR_135 : type1210 _104907 _104908) (s : _104907 -> Prop) (f : type686 _104907) : (term66 _104907 _104908 GEN_PVAR_135 f s) = (term67 _104907 _104908 GEN_PVAR_135 s f).
Proof. exact (MK_COMB (@lem4372892 _104907 _104908 GEN_PVAR_135) (@lem4372891 _104907 s f)). Qed.
Lemma lem4372894 {_104907 _104908 : Type'} (s : _104907 -> Prop) : (term68 _104907 _104908 s) = (@CROSS _104908 _104907 s (@UNIV _104908)).
Proof. exact (eq_refl (term68 _104907 _104908 s)). Qed.
Lemma lem4372895 {_104907 _104908 : Type'} (GEN_PVAR_135 : type1210 _104907 _104908) (f : type686 _104907) (s : _104907 -> Prop) : (term69 _104907 _104908 GEN_PVAR_135 f s) = (term70 _104907 _104908 GEN_PVAR_135 f s).
Proof. exact (MK_COMB (@lem4372893 _104907 _104908 GEN_PVAR_135 s f) (@lem4372894 _104907 _104908 s)). Qed.
Lemma lem4372896 {_104907 _104908 : Type'} (GEN_PVAR_135 : type1210 _104907 _104908) (f : type686 _104907) : (term71 _104907 _104908 GEN_PVAR_135 f) = (term72 _104907 _104908 GEN_PVAR_135 f).
Proof. exact (fun_ext (fun s : _104907 -> Prop => @lem4372895 _104907 _104908 GEN_PVAR_135 f s)). Qed.
Lemma lem4372897 {_104907 : Type'} : (@ex (_104907 -> Prop)) = (@ex (_104907 -> Prop)).
Proof. exact (eq_refl (@ex (_104907 -> Prop))). Qed.
Lemma lem4372898 {_104907 _104908 : Type'} (GEN_PVAR_135 : type1210 _104907 _104908) (f : type686 _104907) : (term73 _104907 _104908 GEN_PVAR_135 f) = (term74 _104907 _104908 GEN_PVAR_135 f).
Proof. exact (MK_COMB (@lem4372897 _104907) (@lem4372896 _104907 _104908 GEN_PVAR_135 f)). Qed.
Lemma lem4372899 {_104907 _104908 : Type'} (f : type686 _104907) : (term75 _104907 _104908 f) = (term76 _104907 _104908 f).
Proof. exact (fun_ext (fun GEN_PVAR_135 : type1210 _104907 _104908 => @lem4372898 _104907 _104908 GEN_PVAR_135 f)). Qed.
Lemma lem4372900 {_104907 _104908 : Type'} : (@GSPEC ((prod _104907 _104908) -> Prop)) = (@GSPEC ((prod _104907 _104908) -> Prop)).
Proof. exact (eq_refl (@GSPEC ((prod _104907 _104908) -> Prop))). Qed.
Lemma lem4372901 {_104907 _104908 : Type'} (f : type686 _104907) : (term77 _104907 _104908 f) = (term78 _104907 _104908 f).
Proof. exact (MK_COMB (@lem4372900 _104907 _104908) (@lem4372899 _104907 _104908 f)). Qed.
Lemma lem4372902 {_104907 _104908 : Type'} : (@INTERS (prod _104907 _104908)) = (@INTERS (prod _104907 _104908)).
Proof. exact (eq_refl (@INTERS (prod _104907 _104908))). Qed.
Lemma lem4372903 {_104907 _104908 : Type'} (f : type686 _104907) : (term61 _104907 _104908 f) = (term29 _104907 _104908 f).
Proof. exact (MK_COMB (@lem4372902 _104907 _104908) (@lem4372901 _104907 _104908 f)). Qed.
Lemma lem4372904 {_104907 _104908 : Type'} : (@eq ((prod _104907 _104908) -> Prop)) = (@eq ((prod _104907 _104908) -> Prop)).
Proof. exact (eq_refl (@eq ((prod _104907 _104908) -> Prop))). Qed.
Lemma lem4372905 {_104907 _104908 : Type'} (f : type686 _104907) : (term79 _104907 _104908 f) = (term80 _104907 _104908 f).
Proof. exact (MK_COMB (@lem4372904 _104907 _104908) (@lem4372903 _104907 _104908 f)). Qed.
Lemma lem4372906 {_104907 : Type'} (s : _104907 -> Prop) (f : type686 _104907) : (term65 _104907 f s) = (@IN (_104907 -> Prop) s f).
Proof. exact (eq_refl (term65 _104907 f s)). Qed.
Lemma lem4372907 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4372908 {_104907 : Type'} (s : _104907 -> Prop) (f : type686 _104907) : (term81 _104907 f s) = (term82 _104907 s f).
Proof. exact (MK_COMB (@lem4372907) (@lem4372906 _104907 s f)). Qed.
Lemma lem4372909 {_104907 _104908 : Type'} (s : _104907 -> Prop) : (term68 _104907 _104908 s) = (@CROSS _104908 _104907 s (@UNIV _104908)).
Proof. exact (eq_refl (term68 _104907 _104908 s)). Qed.
Lemma lem4372910 {_104907 _104908 : Type'} (a : prod _104907 _104908) : (@IN (prod _104907 _104908) a) = (@IN (prod _104907 _104908) a).
Proof. exact (eq_refl (@IN (prod _104907 _104908) a)). Qed.
Lemma lem4372911 {_104907 _104908 : Type'} (a : prod _104907 _104908) (s : _104907 -> Prop) : (term83 _104907 _104908 a s) = (term84 _104907 _104908 a s).
Proof. exact (MK_COMB (@lem4372910 _104907 _104908 a) (@lem4372909 _104907 _104908 s)). Qed.
Lemma lem4372912 {_104907 _104908 : Type'} (f : type686 _104907) (a : prod _104907 _104908) (s : _104907 -> Prop) : (term85 _104907 _104908 f a s) = (term86 _104907 _104908 f a s).
Proof. exact (MK_COMB (@lem4372908 _104907 s f) (@lem4372911 _104907 _104908 a s)). Qed.
Lemma lem4372913 {_104907 _104908 : Type'} (f : type686 _104907) (a : prod _104907 _104908) : (term87 _104907 _104908 f a) = (term88 _104907 _104908 f a).
Proof. exact (fun_ext (fun s : _104907 -> Prop => @lem4372912 _104907 _104908 f a s)). Qed.
Lemma lem4372914 {_104907 : Type'} : (@all (_104907 -> Prop)) = (@all (_104907 -> Prop)).
Proof. exact (eq_refl (@all (_104907 -> Prop))). Qed.
Lemma lem4372915 {_104907 _104908 : Type'} (f : type686 _104907) (a : prod _104907 _104908) : (term89 _104907 _104908 f a) = (term90 _104907 _104908 f a).
Proof. exact (MK_COMB (@lem4372914 _104907) (@lem4372913 _104907 _104908 f a)). Qed.
Lemma lem4372916 {_104907 _104908 : Type'} (GEN_PVAR_56 : prod _104907 _104908) : (@SETSPEC (prod _104907 _104908) GEN_PVAR_56) = (@SETSPEC (prod _104907 _104908) GEN_PVAR_56).
Proof. exact (eq_refl (@SETSPEC (prod _104907 _104908) GEN_PVAR_56)). Qed.
Lemma lem4372917 {_104907 _104908 : Type'} (GEN_PVAR_56 : prod _104907 _104908) (f : type686 _104907) (a : prod _104907 _104908) : (term91 _104907 _104908 GEN_PVAR_56 f a) = (term92 _104907 _104908 GEN_PVAR_56 f a).
Proof. exact (MK_COMB (@lem4372916 _104907 _104908 GEN_PVAR_56) (@lem4372915 _104907 _104908 f a)). Qed.
Lemma lem4372918 {_104907 _104908 : Type'} (a : prod _104907 _104908) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4372919 {_104907 _104908 : Type'} (GEN_PVAR_56 : prod _104907 _104908) (f : type686 _104907) (a : prod _104907 _104908) : (term93 _104907 _104908 GEN_PVAR_56 f a) = (term94 _104907 _104908 GEN_PVAR_56 f a).
Proof. exact (MK_COMB (@lem4372917 _104907 _104908 GEN_PVAR_56 f a) (@lem4372918 _104907 _104908 a)). Qed.
Lemma lem4372920 {_104907 _104908 : Type'} (GEN_PVAR_56 : prod _104907 _104908) (f : type686 _104907) : (term95 _104907 _104908 GEN_PVAR_56 f) = (term96 _104907 _104908 GEN_PVAR_56 f).
Proof. exact (fun_ext (fun a : prod _104907 _104908 => @lem4372919 _104907 _104908 GEN_PVAR_56 f a)). Qed.
Lemma lem4372921 {_104907 _104908 : Type'} : (@ex (prod _104907 _104908)) = (@ex (prod _104907 _104908)).
Proof. exact (eq_refl (@ex (prod _104907 _104908))). Qed.
Lemma lem4372922 {_104907 _104908 : Type'} (GEN_PVAR_56 : prod _104907 _104908) (f : type686 _104907) : (term97 _104907 _104908 GEN_PVAR_56 f) = (term98 _104907 _104908 GEN_PVAR_56 f).
Proof. exact (MK_COMB (@lem4372921 _104907 _104908) (@lem4372920 _104907 _104908 GEN_PVAR_56 f)). Qed.
Lemma lem4372923 {_104907 _104908 : Type'} (f : type686 _104907) : (term99 _104907 _104908 f) = (term100 _104907 _104908 f).
Proof. exact (fun_ext (fun GEN_PVAR_56 : prod _104907 _104908 => @lem4372922 _104907 _104908 GEN_PVAR_56 f)). Qed.
Lemma lem4372924 {_104907 _104908 : Type'} : (@GSPEC (prod _104907 _104908)) = (@GSPEC (prod _104907 _104908)).
Proof. exact (eq_refl (@GSPEC (prod _104907 _104908))). Qed.
Lemma lem4372925 {_104907 _104908 : Type'} (f : type686 _104907) : (term62 _104907 _104908 f) = (term101 _104907 _104908 f).
Proof. exact (MK_COMB (@lem4372924 _104907 _104908) (@lem4372923 _104907 _104908 f)). Qed.
Lemma lem4372926 {_104907 _104908 : Type'} (f : type686 _104907) : ((term61 _104907 _104908 f) = (term62 _104907 _104908 f)) = ((term29 _104907 _104908 f) = (term101 _104907 _104908 f)).
Proof. exact (MK_COMB (@lem4372905 _104907 _104908 f) (@lem4372925 _104907 _104908 f)). Qed.
Lemma lem4372927 {_104907 _104908 : Type'} (f : type686 _104907) : (term29 _104907 _104908 f) = (term101 _104907 _104908 f).
Proof. exact (EQ_MP (@lem4372926 _104907 _104908 f) (@lem4372890 _104907 _104908 f)). Qed.
Lemma lem4372940 {_104907 _104908 : Type'} (p1 : _104907) (p2 : _104908) : (term102 _104907 _104908 p1 p2) = (term102 _104907 _104908 p1 p2).
Proof. exact (eq_refl (term102 _104907 _104908 p1 p2)). Qed.
Lemma lem4372941 {_104907 _104908 : Type'} (p1 : _104907) (p2 : _104908) (f : type686 _104907) : (term44 _104907 _104908 p1 p2 f) = (term103 _104907 _104908 p1 p2 f).
Proof. exact (MK_COMB (@lem4372940 _104907 _104908 p1 p2) (@lem4372927 _104907 _104908 f)). Qed.
Lemma lem4372943 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term13 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4372769 _83095 p x) (@lem4372768 _83095 p x)). Qed.
Lemma lem4372944 {_104907 _104908 : Type'} (p : type1210 _104907 _104908) (x : prod _104907 _104908) : (term104 _104907 _104908 x p) = (p x).
Proof. exact (@lem4372943 (prod _104907 _104908) p x). Qed.
Lemma lem4372945 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (p2 : _104908) : (term105 _104907 _104908 p1 p2 f) = (term106 _104907 _104908 f p1 p2).
Proof. exact (@lem4372944 _104907 _104908 (term107 _104907 _104908 f) (@pair _104907 _104908 p1 p2)). Qed.
Lemma lem4372946 {_104907 _104908 : Type'} (f : type686 _104907) (a : prod _104907 _104908) : (term108 _104907 _104908 f a) = (term90 _104907 _104908 f a).
Proof. exact (eq_refl (term108 _104907 _104908 f a)). Qed.
Lemma lem4372947 {_104907 _104908 : Type'} (GEN_PVAR_56 : prod _104907 _104908) : (@SETSPEC (prod _104907 _104908) GEN_PVAR_56) = (@SETSPEC (prod _104907 _104908) GEN_PVAR_56).
Proof. exact (eq_refl (@SETSPEC (prod _104907 _104908) GEN_PVAR_56)). Qed.
Lemma lem4372948 {_104907 _104908 : Type'} (GEN_PVAR_56 : prod _104907 _104908) (f : type686 _104907) (a : prod _104907 _104908) : (term109 _104907 _104908 GEN_PVAR_56 f a) = (term92 _104907 _104908 GEN_PVAR_56 f a).
Proof. exact (MK_COMB (@lem4372947 _104907 _104908 GEN_PVAR_56) (@lem4372946 _104907 _104908 f a)). Qed.
Lemma lem4372949 {_104907 _104908 : Type'} (a : prod _104907 _104908) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4372950 {_104907 _104908 : Type'} (GEN_PVAR_56 : prod _104907 _104908) (f : type686 _104907) (a : prod _104907 _104908) : (term110 _104907 _104908 GEN_PVAR_56 f a) = (term94 _104907 _104908 GEN_PVAR_56 f a).
Proof. exact (MK_COMB (@lem4372948 _104907 _104908 GEN_PVAR_56 f a) (@lem4372949 _104907 _104908 a)). Qed.
Lemma lem4372951 {_104907 _104908 : Type'} (GEN_PVAR_56 : prod _104907 _104908) (f : type686 _104907) : (term111 _104907 _104908 GEN_PVAR_56 f) = (term96 _104907 _104908 GEN_PVAR_56 f).
Proof. exact (fun_ext (fun a : prod _104907 _104908 => @lem4372950 _104907 _104908 GEN_PVAR_56 f a)). Qed.
Lemma lem4372952 {_104907 _104908 : Type'} : (@ex (prod _104907 _104908)) = (@ex (prod _104907 _104908)).
Proof. exact (eq_refl (@ex (prod _104907 _104908))). Qed.
Lemma lem4372953 {_104907 _104908 : Type'} (GEN_PVAR_56 : prod _104907 _104908) (f : type686 _104907) : (term112 _104907 _104908 GEN_PVAR_56 f) = (term98 _104907 _104908 GEN_PVAR_56 f).
Proof. exact (MK_COMB (@lem4372952 _104907 _104908) (@lem4372951 _104907 _104908 GEN_PVAR_56 f)). Qed.
Lemma lem4372954 {_104907 _104908 : Type'} (f : type686 _104907) : (term113 _104907 _104908 f) = (term100 _104907 _104908 f).
Proof. exact (fun_ext (fun GEN_PVAR_56 : prod _104907 _104908 => @lem4372953 _104907 _104908 GEN_PVAR_56 f)). Qed.
Lemma lem4372955 {_104907 _104908 : Type'} : (@GSPEC (prod _104907 _104908)) = (@GSPEC (prod _104907 _104908)).
Proof. exact (eq_refl (@GSPEC (prod _104907 _104908))). Qed.
Lemma lem4372956 {_104907 _104908 : Type'} (f : type686 _104907) : (term114 _104907 _104908 f) = (term101 _104907 _104908 f).
Proof. exact (MK_COMB (@lem4372955 _104907 _104908) (@lem4372954 _104907 _104908 f)). Qed.
Lemma lem4372957 {_104907 _104908 : Type'} (p1 : _104907) (p2 : _104908) : (term102 _104907 _104908 p1 p2) = (term102 _104907 _104908 p1 p2).
Proof. exact (eq_refl (term102 _104907 _104908 p1 p2)). Qed.
Lemma lem4372958 {_104907 _104908 : Type'} (p1 : _104907) (p2 : _104908) (f : type686 _104907) : (term105 _104907 _104908 p1 p2 f) = (term103 _104907 _104908 p1 p2 f).
Proof. exact (MK_COMB (@lem4372957 _104907 _104908 p1 p2) (@lem4372956 _104907 _104908 f)). Qed.
Lemma lem4372959 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4372960 {_104907 _104908 : Type'} (p1 : _104907) (p2 : _104908) (f : type686 _104907) : (term115 _104907 _104908 p1 p2 f) = (term116 _104907 _104908 p1 p2 f).
Proof. exact (MK_COMB (@lem4372959) (@lem4372958 _104907 _104908 p1 p2 f)). Qed.
Lemma lem4372961 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (p2 : _104908) : (term106 _104907 _104908 f p1 p2) = (term117 _104907 _104908 f p1 p2).
Proof. exact (eq_refl (term106 _104907 _104908 f p1 p2)). Qed.
Lemma lem4372962 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (p2 : _104908) : ((term105 _104907 _104908 p1 p2 f) = (term106 _104907 _104908 f p1 p2)) = ((term103 _104907 _104908 p1 p2 f) = (term117 _104907 _104908 f p1 p2)).
Proof. exact (MK_COMB (@lem4372960 _104907 _104908 p1 p2 f) (@lem4372961 _104907 _104908 f p1 p2)). Qed.
Lemma lem4372963 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (p2 : _104908) : (term103 _104907 _104908 p1 p2 f) = (term117 _104907 _104908 f p1 p2).
Proof. exact (EQ_MP (@lem4372962 _104907 _104908 f p1 p2) (@lem4372945 _104907 _104908 f p1 p2)). Qed.
Lemma lem4372973 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4372738 _103718 _103721 x s y t) (@lem4372737 _103718 _103721 x s y t)). Qed.
Lemma lem4372974 {_104907 _104908 : Type'} (x : _104907) (s : _104907 -> Prop) (y : _104908) (t : _104908 -> Prop) : (term7 _104907 _104908 x y s t) = (term8 _104907 _104908 x s y t).
Proof. exact (@lem4372973 _104907 _104908 x s y t). Qed.
Lemma lem4372975 {_104907 _104908 : Type'} (p1 : _104907) (s : _104907 -> Prop) (p2 : _104908) : (term118 _104907 _104908 p1 p2 s) = (term119 _104907 _104908 p1 s p2).
Proof. exact (@lem4372974 _104907 _104908 p1 s p2 (@UNIV _104908)). Qed.
Lemma lem4372978 {_104907 : Type'} (s : _104907 -> Prop) (f : type686 _104907) : (term82 _104907 s f) = (term82 _104907 s f).
Proof. exact (eq_refl (term82 _104907 s f)). Qed.
Lemma lem4372979 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (s : _104907 -> Prop) (p2 : _104908) : (term120 _104907 _104908 f p1 p2 s) = (term121 _104907 _104908 f p1 s p2).
Proof. exact (MK_COMB (@lem4372978 _104907 s f) (@lem4372975 _104907 _104908 p1 s p2)). Qed.
Lemma lem4372982 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (p2 : _104908) : (term122 _104907 _104908 f p1 p2) = (term123 _104907 _104908 f p1 p2).
Proof. exact (fun_ext (fun s : _104907 -> Prop => @lem4372979 _104907 _104908 f p1 s p2)). Qed.
Lemma lem4372983 {_104907 : Type'} : (@all (_104907 -> Prop)) = (@all (_104907 -> Prop)).
Proof. exact (eq_refl (@all (_104907 -> Prop))). Qed.
Lemma lem4372984 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (p2 : _104908) : (term117 _104907 _104908 f p1 p2) = (term124 _104907 _104908 f p1 p2).
Proof. exact (MK_COMB (@lem4372983 _104907) (@lem4372982 _104907 _104908 f p1 p2)). Qed.
Lemma lem4372991 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (p2 : _104908) : (term103 _104907 _104908 p1 p2 f) = (term124 _104907 _104908 f p1 p2).
Proof. exact (TRANS (@lem4372963 _104907 _104908 f p1 p2) (@lem4372984 _104907 _104908 f p1 p2)). Qed.
Lemma lem4372992 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (p2 : _104908) : (term44 _104907 _104908 p1 p2 f) = (term124 _104907 _104908 f p1 p2).
Proof. exact (TRANS (@lem4372941 _104907 _104908 p1 p2 f) (@lem4372991 _104907 _104908 f p1 p2)). Qed.
Lemma lem4372993 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (p2 : _104908) (g : type686 _104908) (h1 : g = (@EMPTY (_104908 -> Prop))) : ((term43 _104907 _104908 p1 p2 f g) = (term44 _104907 _104908 p1 p2 f)) = ((term56 _104907 _104908 p1 f p2) = (term124 _104907 _104908 f p1 p2)).
Proof. exact (MK_COMB (@lem4372886 _104907 _104908 p1 f p2 g h1) (@lem4372992 _104907 _104908 f p1 p2)). Qed.
Lemma lem4372998 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) (h1 : g = (@EMPTY (_104908 -> Prop))) : (term46 _104907 _104908 g p1 f) = (term125 _104907 _104908 f p1).
Proof. exact (fun_ext (fun p2 : _104908 => @lem4372993 _104907 _104908 f p1 p2 g h1)). Qed.
Lemma lem4372999 {_104908 : Type'} : (@all _104908) = (@all _104908).
Proof. exact (eq_refl (@all _104908)). Qed.
Lemma lem4373000 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) (h1 : g = (@EMPTY (_104908 -> Prop))) : (term48 _104907 _104908 g p1 f) = (term126 _104907 _104908 f p1).
Proof. exact (MK_COMB (@lem4372999 _104908) (@lem4372998 _104907 _104908 f p1 g h1)). Qed.
Lemma lem4373007 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (h1 : g = (@EMPTY (_104908 -> Prop))) : (term50 _104907 _104908 g f) = (term127 _104907 _104908 f).
Proof. exact (fun_ext (fun p1 : _104907 => @lem4373000 _104907 _104908 f p1 g h1)). Qed.
Lemma lem4373008 {_104907 : Type'} : (@all _104907) = (@all _104907).
Proof. exact (eq_refl (@all _104907)). Qed.
Lemma lem4373009 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (h1 : g = (@EMPTY (_104908 -> Prop))) : (term51 _104907 _104908 g f) = (term128 _104907 _104908 f).
Proof. exact (MK_COMB (@lem4373008 _104907) (@lem4373007 _104907 _104908 f g h1)). Qed.
Lemma lem4373016 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (h1 : g = (@EMPTY (_104908 -> Prop))) : ((term28 _104907 _104908 f g) = (term29 _104907 _104908 f)) = (term128 _104907 _104908 f).
Proof. exact (TRANS (@lem4372857 _104907 _104908 g f) (@lem4373009 _104907 _104908 f g h1)). Qed.
Lemma lem4373017 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (h1 : g = (@EMPTY (_104908 -> Prop))) : (term128 _104907 _104908 f) = ((term28 _104907 _104908 f g) = (term29 _104907 _104908 f)).
Proof. exact (SYM (@lem4373016 _104907 _104908 f g h1)). Qed.
