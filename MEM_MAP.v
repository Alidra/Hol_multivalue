Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MEM_MAP_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1097797_spec.
Require Import thm1103191_spec.
Require Import thm1103192_spec.
Require Import thm1103200_spec.
Require Import thm1103201_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm18394_spec.
Require Import thm1844_spec.
Require Import thm1857_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19699_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Lemma lem1145814 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1145815 {_26981 : Type'} (P : type1143 _26981) : term0 _26981 P.
Proof. exact (@lem1145814 _26981 P). Qed.
Lemma lem1145816 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : term1 _26978 _26981 y f.
Proof. exact (@lem1145815 _26981 (term2 _26978 _26981 y f)). Qed.
Lemma lem1145817 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : (term3 _26978 _26981 y f) = ((term4 _26978 _26981 y f) = (term5 _26978 _26981 y f)).
Proof. exact (eq_refl (term3 _26978 _26981 y f)). Qed.
Lemma lem1145818 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1145819 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : (term6 _26978 _26981 y f) = (term7 _26978 _26981 y f).
Proof. exact (MK_COMB (@lem1145818) (@lem1145817 _26978 _26981 y f)). Qed.
Lemma lem1145820 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term8 _26978 _26981 y f t) = ((term9 _26978 _26981 y f t) = (term10 _26978 _26981 t y f)).
Proof. exact (eq_refl (term8 _26978 _26981 y f t)). Qed.
Lemma lem1145821 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1145822 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term11 _26978 _26981 y f t) = (term12 _26978 _26981 t y f).
Proof. exact (MK_COMB (@lem1145821) (@lem1145820 _26978 _26981 t y f)). Qed.
Lemma lem1145823 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term13 _26978 _26981 y f h t) = ((term14 _26978 _26981 y f h t) = (term15 _26978 _26981 h t y f)).
Proof. exact (eq_refl (term13 _26978 _26981 y f h t)). Qed.
Lemma lem1145824 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term16 _26978 _26981 y f h t) = (term17 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1145822 _26978 _26981 t y f) (@lem1145823 _26978 _26981 h t y f)). Qed.
Lemma lem1145825 {_26978 _26981 : Type'} (h : _26981) (y : _26978) (f : _26981 -> _26978) : (term18 _26978 _26981 y f h) = (term19 _26978 _26981 h y f).
Proof. exact (fun_ext (fun t : list _26981 => @lem1145824 _26978 _26981 h t y f)). Qed.
Lemma lem1145826 {_26981 : Type'} : (@all (list _26981)) = (@all (list _26981)).
Proof. exact (eq_refl (@all (list _26981))). Qed.
Lemma lem1145827 {_26978 _26981 : Type'} (h : _26981) (y : _26978) (f : _26981 -> _26978) : (term20 _26978 _26981 y f h) = (term21 _26978 _26981 h y f).
Proof. exact (MK_COMB (@lem1145826 _26981) (@lem1145825 _26978 _26981 h y f)). Qed.
Lemma lem1145828 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : (term22 _26978 _26981 y f) = (term23 _26978 _26981 y f).
Proof. exact (fun_ext (fun h : _26981 => @lem1145827 _26978 _26981 h y f)). Qed.
Lemma lem1145829 {_26981 : Type'} : (@all _26981) = (@all _26981).
Proof. exact (eq_refl (@all _26981)). Qed.
Lemma lem1145830 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : (term24 _26978 _26981 y f) = (term25 _26978 _26981 y f).
Proof. exact (MK_COMB (@lem1145829 _26981) (@lem1145828 _26978 _26981 y f)). Qed.
Lemma lem1145831 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : (term26 _26978 _26981 y f) = (term27 _26978 _26981 y f).
Proof. exact (MK_COMB (@lem1145819 _26978 _26981 y f) (@lem1145830 _26978 _26981 y f)). Qed.
Lemma lem1145832 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1145833 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : (term28 _26978 _26981 y f) = (term29 _26978 _26981 y f).
Proof. exact (MK_COMB (@lem1145832) (@lem1145831 _26978 _26981 y f)). Qed.
Lemma lem1145834 {_26978 _26981 : Type'} (l : list _26981) (y : _26978) (f : _26981 -> _26978) : (term8 _26978 _26981 y f l) = ((term9 _26978 _26981 y f l) = (term10 _26978 _26981 l y f)).
Proof. exact (eq_refl (term8 _26978 _26981 y f l)). Qed.
Lemma lem1145835 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : (term30 _26978 _26981 y f) = (term2 _26978 _26981 y f).
Proof. exact (fun_ext (fun l : list _26981 => @lem1145834 _26978 _26981 l y f)). Qed.
Lemma lem1145836 {_26981 : Type'} : (@all (list _26981)) = (@all (list _26981)).
Proof. exact (eq_refl (@all (list _26981))). Qed.
Lemma lem1145837 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : (term31 _26978 _26981 y f) = (term32 _26978 _26981 y f).
Proof. exact (MK_COMB (@lem1145836 _26981) (@lem1145835 _26978 _26981 y f)). Qed.
Lemma lem1145838 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : (term1 _26978 _26981 y f) = (term33 _26978 _26981 y f).
Proof. exact (MK_COMB (@lem1145833 _26978 _26981 y f) (@lem1145837 _26978 _26981 y f)). Qed.
Lemma lem1145839 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : term33 _26978 _26981 y f.
Proof. exact (EQ_MP (@lem1145838 _26978 _26981 y f) (@lem1145816 _26978 _26981 y f)). Qed.
Lemma lem1145851 {A B : Type'} : term34 A B.
Proof. exact (proj1 (@lem1097797 A B)). Qed.
Lemma lem1145852 {A B : Type'} (f : A -> B) : term35 A B f.
Proof. exact (@lem1145851 A B f). Qed.
Lemma lem1145853 {A B : Type'} (f : A -> B) : (term35 A B f) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl (term35 A B f)). Qed.
Lemma lem1145860 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1145853 A B f) (@lem1145852 A B f)). Qed.
Lemma lem1145861 {_26978 _26981 : Type'} (f : _26981 -> _26978) : (@List.map _26981 _26978 f (@nil _26981)) = (@nil _26978).
Proof. exact (@lem1145860 _26981 _26978 f). Qed.
Lemma lem1145862 {_26978 : Type'} (y : _26978) : (@List.In _26978 y) = (@List.In _26978 y).
Proof. exact (eq_refl (@List.In _26978 y)). Qed.
Lemma lem1145863 {_26978 _26981 : Type'} (f : _26981 -> _26978) (y : _26978) : (term4 _26978 _26981 y f) = (@List.In _26978 y (@nil _26978)).
Proof. exact (MK_COMB (@lem1145862 _26978 y) (@lem1145861 _26978 _26981 f)). Qed.
Lemma lem1145865 {_25376 : Type'} (x : _25376) : (@List.In _25376 x (@nil _25376)) = False.
Proof. exact (EQ_MP (@lem1103192 _25376 x) (@lem1103191 _25376 x)). Qed.
Lemma lem1145866 {_26978 : Type'} (x : _26978) : (@List.In _26978 x (@nil _26978)) = False.
Proof. exact (@lem1145865 _26978 x). Qed.
Lemma lem1145867 {_26978 : Type'} (y : _26978) : (@List.In _26978 y (@nil _26978)) = False.
Proof. exact (@lem1145866 _26978 y). Qed.
Lemma lem1145868 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : (term4 _26978 _26981 y f) = False.
Proof. exact (TRANS (@lem1145863 _26978 _26981 f y) (@lem1145867 _26978 y)). Qed.
Lemma lem1145869 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1145870 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : (term36 _26978 _26981 y f) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1145869) (@lem1145868 _26978 _26981 y f)). Qed.
Lemma lem1145878 {_25376 : Type'} (x : _25376) : (@List.In _25376 x (@nil _25376)) = False.
Proof. exact (EQ_MP (@lem1103192 _25376 x) (@lem1103191 _25376 x)). Qed.
Lemma lem1145879 {_26981 : Type'} (x : _26981) : (@List.In _26981 x (@nil _26981)) = False.
Proof. exact (@lem1145878 _26981 x). Qed.
Lemma lem1145880 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1145881 {_26981 : Type'} (x : _26981) : (term37 _26981 x) = (and False).
Proof. exact (MK_COMB (@lem1145880) (@lem1145879 _26981 x)). Qed.
Lemma lem1145884 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) (x : _26981) : (y = (f x)) = (y = (f x)).
Proof. exact (eq_refl (y = (f x))). Qed.
Lemma lem1145885 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term38 _26978 _26981 y f x) = (term39 _26978 _26981 y f x).
Proof. exact (MK_COMB (@lem1145881 _26981 x) (@lem1145884 _26978 _26981 y f x)). Qed.
Lemma lem1145887 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1145888 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term39 _26978 _26981 y f x) = False.
Proof. exact (@lem1145887 (y = (f x))). Qed.
Lemma lem1145889 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term38 _26978 _26981 y f x) = False.
Proof. exact (TRANS (@lem1145885 _26978 _26981 y f x) (@lem1145888 _26978 _26981 y f x)). Qed.
Lemma lem1145890 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : (term40 _26978 _26981 y f) = (term41 _26981).
Proof. exact (fun_ext (fun x : _26981 => @lem1145889 _26978 _26981 y f x)). Qed.
Lemma lem1145891 {_26981 : Type'} : (@ex _26981) = (@ex _26981).
Proof. exact (eq_refl (@ex _26981)). Qed.
Lemma lem1145892 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : (term5 _26978 _26981 y f) = (term42 _26981).
Proof. exact (MK_COMB (@lem1145891 _26981) (@lem1145890 _26978 _26981 y f)). Qed.
Lemma lem1145894 {A : Type'} (t : Prop) : (term43 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem1145895 {_26981 : Type'} (t : Prop) : (term43 _26981 t) = t.
Proof. exact (@lem1145894 _26981 t). Qed.
Lemma lem1145896 {_26981 : Type'} : (term42 _26981) = False.
Proof. exact (@lem1145895 _26981 False). Qed.
Lemma lem1145897 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : (term5 _26978 _26981 y f) = False.
Proof. exact (TRANS (@lem1145892 _26978 _26981 y f) (@lem1145896 _26981)). Qed.
Lemma lem1145898 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : ((term4 _26978 _26981 y f) = (term5 _26978 _26981 y f)) = (False = False).
Proof. exact (MK_COMB (@lem1145870 _26978 _26981 y f) (@lem1145897 _26978 _26981 y f)). Qed.
Lemma lem1145900 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1145901 : (False = False) = (~ False).
Proof. exact (@lem1145900 False). Qed.
Lemma lem1145903 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1145904 : (False = False) = True.
Proof. exact (TRANS (@lem1145901) (@lem1145903)). Qed.
Lemma lem1145905 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : ((term4 _26978 _26981 y f) = (term5 _26978 _26981 y f)) = True.
Proof. exact (TRANS (@lem1145898 _26978 _26981 y f) (@lem1145904)). Qed.
Lemma lem1145906 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : True = ((term4 _26978 _26981 y f) = (term5 _26978 _26981 y f)).
Proof. exact (SYM (@lem1145905 _26978 _26981 y f)). Qed.
Lemma lem1145907 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : (term4 _26978 _26981 y f) = (term5 _26978 _26981 y f).
Proof. exact (EQ_MP (@lem1145906 _26978 _26981 y f) (@lem0)). Qed.
Lemma lem1145908 {A B : Type'} : term44 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem1145909 {A B : Type'} (f : A -> B) : term45 A B f.
Proof. exact (@lem1145908 A B f). Qed.
Lemma lem1145910 {A B : Type'} (f : A -> B) : (term45 A B f) = (term46 A B f).
Proof. exact (eq_refl (term45 A B f)). Qed.
Lemma lem1145911 {A B : Type'} (f : A -> B) : term46 A B f.
Proof. exact (EQ_MP (@lem1145910 A B f) (@lem1145909 A B f)). Qed.
Lemma lem1145912 {A B : Type'} (f : A -> B) (h : A) : term47 A B f h.
Proof. exact (@lem1145911 A B f h). Qed.
Lemma lem1145913 {A B : Type'} (h : A) (f : A -> B) : (term47 A B f h) = (term48 A B h f).
Proof. exact (eq_refl (term47 A B f h)). Qed.
Lemma lem1145914 {A B : Type'} (h : A) (f : A -> B) : term48 A B h f.
Proof. exact (EQ_MP (@lem1145913 A B h f) (@lem1145912 A B f h)). Qed.
Lemma lem1145915 {A B : Type'} (h : A) (f : A -> B) (t : list A) : term49 A B h f t.
Proof. exact (@lem1145914 A B h f t). Qed.
Lemma lem1145916 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term49 A B h f t) = ((term50 A B f h t) = (term51 A B h f t)).
Proof. exact (eq_refl (term49 A B h f t)). Qed.
Lemma lem1145927 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term50 A B f h t) = (term51 A B h f t).
Proof. exact (EQ_MP (@lem1145916 A B h f t) (@lem1145915 A B h f t)). Qed.
Lemma lem1145928 {_26978 _26981 : Type'} (h : _26981) (f : _26981 -> _26978) (t : list _26981) : (term52 _26978 _26981 f h t) = (term53 _26978 _26981 h f t).
Proof. exact (@lem1145927 _26981 _26978 h f t). Qed.
Lemma lem1145929 {_26978 : Type'} (y : _26978) : (@List.In _26978 y) = (@List.In _26978 y).
Proof. exact (eq_refl (@List.In _26978 y)). Qed.
Lemma lem1145930 {_26978 _26981 : Type'} (y : _26978) (h : _26981) (f : _26981 -> _26978) (t : list _26981) : (term14 _26978 _26981 y f h t) = (term54 _26978 _26981 y h f t).
Proof. exact (MK_COMB (@lem1145929 _26978 y) (@lem1145928 _26978 _26981 h f t)). Qed.
Lemma lem1145932 {_25376 : Type'} (h : _25376) (x : _25376) (t : list _25376) : (term55 _25376 x h t) = (term56 _25376 h x t).
Proof. exact (EQ_MP (@lem1103201 _25376 h x t) (@lem1103200 _25376 h x t)). Qed.
Lemma lem1145933 {_26978 : Type'} (h : _26978) (x : _26978) (t : list _26978) : (term55 _26978 x h t) = (term56 _26978 h x t).
Proof. exact (@lem1145932 _26978 h x t). Qed.
Lemma lem1145934 {_26978 _26981 : Type'} (h : _26981) (y : _26978) (f : _26981 -> _26978) (t : list _26981) : (term54 _26978 _26981 y h f t) = (term57 _26978 _26981 h y f t).
Proof. exact (@lem1145933 _26978 (f h) y (@List.map _26981 _26978 f t)). Qed.
Lemma lem1145940 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : (term9 _26978 _26981 y f t) = (term10 _26978 _26981 t y f)) : (term9 _26978 _26981 y f t) = (term10 _26978 _26981 t y f).
Proof. exact (h1). Qed.
Lemma lem1145949 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) (h : _26981) : (term58 _26978 _26981 y f h) = (term58 _26978 _26981 y f h).
Proof. exact (eq_refl (term58 _26978 _26981 y f h)). Qed.
Lemma lem1145950 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : (term9 _26978 _26981 y f t) = (term10 _26978 _26981 t y f)) : (term57 _26978 _26981 h y f t) = (term59 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1145949 _26978 _26981 y f h) (@lem1145940 _26978 _26981 t y f h1)). Qed.
Lemma lem1145953 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : (term9 _26978 _26981 y f t) = (term10 _26978 _26981 t y f)) : (term54 _26978 _26981 y h f t) = (term59 _26978 _26981 h t y f).
Proof. exact (TRANS (@lem1145934 _26978 _26981 h y f t) (@lem1145950 _26978 _26981 h t y f h1)). Qed.
Lemma lem1145954 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : (term9 _26978 _26981 y f t) = (term10 _26978 _26981 t y f)) : (term14 _26978 _26981 y f h t) = (term59 _26978 _26981 h t y f).
Proof. exact (TRANS (@lem1145930 _26978 _26981 y h f t) (@lem1145953 _26978 _26981 h t y f h1)). Qed.
Lemma lem1145955 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1145956 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : (term9 _26978 _26981 y f t) = (term10 _26978 _26981 t y f)) : (term60 _26978 _26981 y f h t) = (term61 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1145955) (@lem1145954 _26978 _26981 h t y f h1)). Qed.
Lemma lem1145964 {_25376 : Type'} (h : _25376) (x : _25376) (t : list _25376) : (term55 _25376 x h t) = (term56 _25376 h x t).
Proof. exact (EQ_MP (@lem1103201 _25376 h x t) (@lem1103200 _25376 h x t)). Qed.
Lemma lem1145965 {_26981 : Type'} (h : _26981) (x : _26981) (t : list _26981) : (term55 _26981 x h t) = (term56 _26981 h x t).
Proof. exact (@lem1145964 _26981 h x t). Qed.
Lemma lem1145970 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1145971 {_26981 : Type'} (h : _26981) (x : _26981) (t : list _26981) : (term62 _26981 x h t) = (term63 _26981 h x t).
Proof. exact (MK_COMB (@lem1145970) (@lem1145965 _26981 h x t)). Qed.
Lemma lem1145974 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) (x : _26981) : (y = (f x)) = (y = (f x)).
Proof. exact (eq_refl (y = (f x))). Qed.
Lemma lem1145975 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term64 _26978 _26981 h t y f x) = (term65 _26978 _26981 h t y f x).
Proof. exact (MK_COMB (@lem1145971 _26981 h x t) (@lem1145974 _26978 _26981 y f x)). Qed.
Lemma lem1145978 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term66 _26978 _26981 h t y f) = (term67 _26978 _26981 h t y f).
Proof. exact (fun_ext (fun x : _26981 => @lem1145975 _26978 _26981 h t y f x)). Qed.
Lemma lem1145979 {_26981 : Type'} : (@ex _26981) = (@ex _26981).
Proof. exact (eq_refl (@ex _26981)). Qed.
Lemma lem1145980 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term15 _26978 _26981 h t y f) = (term68 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1145979 _26981) (@lem1145978 _26978 _26981 h t y f)). Qed.
Lemma lem1145985 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : (term9 _26978 _26981 y f t) = (term10 _26978 _26981 t y f)) : ((term14 _26978 _26981 y f h t) = (term15 _26978 _26981 h t y f)) = ((term59 _26978 _26981 h t y f) = (term68 _26978 _26981 h t y f)).
Proof. exact (MK_COMB (@lem1145956 _26978 _26981 h t y f h1) (@lem1145980 _26978 _26981 h t y f)). Qed.
Lemma lem1145988 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : (term9 _26978 _26981 y f t) = (term10 _26978 _26981 t y f)) : ((term59 _26978 _26981 h t y f) = (term68 _26978 _26981 h t y f)) = ((term14 _26978 _26981 y f h t) = (term15 _26978 _26981 h t y f)).
Proof. exact (SYM (@lem1145985 _26978 _26981 h t y f h1)). Qed.
Lemma lem1145990 (p : Prop) : p = (term69 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1145991 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : ((term59 _26978 _26981 h t y f) = (term68 _26978 _26981 h t y f)) = (term70 _26978 _26981 h t y f).
Proof. exact (@lem1145990 ((term59 _26978 _26981 h t y f) = (term68 _26978 _26981 h t y f))). Qed.
Lemma lem1145992 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term70 _26978 _26981 h t y f) = ((term59 _26978 _26981 h t y f) = (term68 _26978 _26981 h t y f)).
Proof. exact (SYM (@lem1145991 _26978 _26981 h t y f)). Qed.
Lemma lem1145993 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term71 _26978 _26981 h t y f) : term71 _26978 _26981 h t y f.
Proof. exact (h1). Qed.
Lemma lem1145996 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term70 _26978 _26981 h t y f) : term70 _26978 _26981 h t y f.
Proof. exact (h1). Qed.
Lemma lem1145997 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : term72 _26978 _26981 h t y f.
Proof. exact (fun h0 : term70 _26978 _26981 h t y f => @lem1145996 _26978 _26981 h t y f h0). Qed.
Lemma lem1145998 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term72 _26978 _26981 h t y f) : term72 _26978 _26981 h t y f.
Proof. exact (h1). Qed.
Lemma lem1145999 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term70 _26978 _26981 h t y f) : term70 _26978 _26981 h t y f.
Proof. exact (h1). Qed.
Lemma lem1146000 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term70 _26978 _26981 h t y f) (h2 : term72 _26978 _26981 h t y f) : term70 _26978 _26981 h t y f.
Proof. exact (@lem1145998 _26978 _26981 h t y f h2 (@lem1145999 _26978 _26981 h t y f h1)). Qed.
Lemma lem1146001 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term70 _26978 _26981 h t y f) : term73 _26978 _26981 h t y f.
Proof. exact (fun h0 : term72 _26978 _26981 h t y f => @lem1146000 _26978 _26981 h t y f h1 h0). Qed.
Lemma lem1146002 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term72 _26978 _26981 h t y f) : term72 _26978 _26981 h t y f.
Proof. exact (h1). Qed.
Lemma lem1146003 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term70 _26978 _26981 h t y f) (h2 : term72 _26978 _26981 h t y f) : term70 _26978 _26981 h t y f.
Proof. exact (@lem1146001 _26978 _26981 h t y f h1 (@lem1146002 _26978 _26981 h t y f h2)). Qed.
Lemma lem1146004 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term72 _26978 _26981 h t y f) : term72 _26978 _26981 h t y f.
Proof. exact (fun h0 : term70 _26978 _26981 h t y f => @lem1146003 _26978 _26981 h t y f h0 h1). Qed.
Lemma lem1146005 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : term74 _26978 _26981 h t y f.
Proof. exact (fun h0 : term72 _26978 _26981 h t y f => @lem1146004 _26978 _26981 h t y f h0). Qed.
Lemma lem1146008 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : term72 _26978 _26981 h t y f.
Proof. exact (@lem1146005 _26978 _26981 h t y f (@lem1145997 _26978 _26981 h t y f)). Qed.
Lemma lem1146009 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : term72 _26978 _26981 h t y f.
Proof. exact (@lem1146008 _26978 _26981 h t y f). Qed.
Lemma lem1146027 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1146028 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term70 _26978 _26981 h t y f) = (term75 _26978 _26981 h t y f).
Proof. exact (@lem1146027 (term71 _26978 _26981 h t y f)). Qed.
Lemma lem1146030 (t : Prop) : (term76 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1146031 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term75 _26978 _26981 h t y f) = ((term59 _26978 _26981 h t y f) = (term68 _26978 _26981 h t y f)).
Proof. exact (@lem1146030 ((term59 _26978 _26981 h t y f) = (term68 _26978 _26981 h t y f))). Qed.
Lemma lem1146032 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term70 _26978 _26981 h t y f) = ((term59 _26978 _26981 h t y f) = (term68 _26978 _26981 h t y f)).
Proof. exact (TRANS (@lem1146028 _26978 _26981 h t y f) (@lem1146031 _26978 _26981 h t y f)). Qed.
Lemma lem1146137 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term77 _26978 _26981 t y f) = (term78 _26978 _26981 t y f).
Proof. exact (fun_ext (fun h : _26981 => @lem1146032 _26978 _26981 h t y f)). Qed.
Lemma lem1146138 {_26981 : Type'} : (@all _26981) = (@all _26981).
Proof. exact (eq_refl (@all _26981)). Qed.
Lemma lem1146139 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term79 _26978 _26981 t y f) = (term80 _26978 _26981 t y f).
Proof. exact (MK_COMB (@lem1146138 _26981) (@lem1146137 _26978 _26981 t y f)). Qed.
Lemma lem1146144 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : (term81 _26978 _26981 y f) = (term82 _26978 _26981 y f).
Proof. exact (fun_ext (fun t : list _26981 => @lem1146139 _26978 _26981 t y f)). Qed.
Lemma lem1146145 {_26981 : Type'} : (@all (list _26981)) = (@all (list _26981)).
Proof. exact (eq_refl (@all (list _26981))). Qed.
Lemma lem1146146 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : (term83 _26978 _26981 y f) = (term84 _26978 _26981 y f).
Proof. exact (MK_COMB (@lem1146145 _26981) (@lem1146144 _26978 _26981 y f)). Qed.
Lemma lem1146151 {_26978 _26981 : Type'} (f : _26981 -> _26978) : (term85 _26978 _26981 f) = (term86 _26978 _26981 f).
Proof. exact (fun_ext (fun y : _26978 => @lem1146146 _26978 _26981 y f)). Qed.
Lemma lem1146152 {_26978 : Type'} : (@all _26978) = (@all _26978).
Proof. exact (eq_refl (@all _26978)). Qed.
Lemma lem1146153 {_26978 _26981 : Type'} (f : _26981 -> _26978) : (term87 _26978 _26981 f) = (term88 _26978 _26981 f).
Proof. exact (MK_COMB (@lem1146152 _26978) (@lem1146151 _26978 _26981 f)). Qed.
Lemma lem1146158 {_26978 _26981 : Type'} : (term89 _26978 _26981) = (term90 _26978 _26981).
Proof. exact (fun_ext (fun f : _26981 -> _26978 => @lem1146153 _26978 _26981 f)). Qed.
Lemma lem1146159 {_26978 _26981 : Type'} : (@all (_26981 -> _26978)) = (@all (_26981 -> _26978)).
Proof. exact (eq_refl (@all (_26981 -> _26978))). Qed.
Lemma lem1146168 {_26978 _26981 : Type'} : (term91 _26978 _26981) = (term92 _26978 _26981).
Proof. exact (MK_COMB (@lem1146159 _26978 _26981) (@lem1146158 _26978 _26981)). Qed.
Lemma lem1146177 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term65 _26978 _26981 h t y f x) = (term65 _26978 _26981 h t y f x).
Proof. exact (eq_refl (term65 _26978 _26981 h t y f x)). Qed.
Lemma lem1146178 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term67 _26978 _26981 h t y f) = (term67 _26978 _26981 h t y f).
Proof. exact (fun_ext (fun x : _26981 => @lem1146177 _26978 _26981 h t y f x)). Qed.
Lemma lem1146179 {_26981 : Type'} : (@ex _26981) = (@ex _26981).
Proof. exact (eq_refl (@ex _26981)). Qed.
Lemma lem1146180 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term68 _26978 _26981 h t y f) = (term68 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146179 _26981) (@lem1146178 _26978 _26981 h t y f)). Qed.
Lemma lem1146185 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term93 _26978 _26981 t y f x) = (term93 _26978 _26981 t y f x).
Proof. exact (eq_refl (term93 _26978 _26981 t y f x)). Qed.
Lemma lem1146186 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term94 _26978 _26981 t y f) = (term94 _26978 _26981 t y f).
Proof. exact (fun_ext (fun x : _26981 => @lem1146185 _26978 _26981 t y f x)). Qed.
Lemma lem1146187 {_26981 : Type'} : (@ex _26981) = (@ex _26981).
Proof. exact (eq_refl (@ex _26981)). Qed.
Lemma lem1146188 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term10 _26978 _26981 t y f) = (term10 _26978 _26981 t y f).
Proof. exact (MK_COMB (@lem1146187 _26981) (@lem1146186 _26978 _26981 t y f)). Qed.
Lemma lem1146191 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) (h : _26981) : (term58 _26978 _26981 y f h) = (term58 _26978 _26981 y f h).
Proof. exact (eq_refl (term58 _26978 _26981 y f h)). Qed.
Lemma lem1146192 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term59 _26978 _26981 h t y f) = (term59 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146191 _26978 _26981 y f h) (@lem1146188 _26978 _26981 t y f)). Qed.
Lemma lem1146193 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1146194 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term61 _26978 _26981 h t y f) = (term61 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146193) (@lem1146192 _26978 _26981 h t y f)). Qed.
Lemma lem1146195 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : ((term59 _26978 _26981 h t y f) = (term68 _26978 _26981 h t y f)) = ((term59 _26978 _26981 h t y f) = (term68 _26978 _26981 h t y f)).
Proof. exact (MK_COMB (@lem1146194 _26978 _26981 h t y f) (@lem1146180 _26978 _26981 h t y f)). Qed.
Lemma lem1146196 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term78 _26978 _26981 t y f) = (term78 _26978 _26981 t y f).
Proof. exact (fun_ext (fun h : _26981 => @lem1146195 _26978 _26981 h t y f)). Qed.
Lemma lem1146197 {_26981 : Type'} : (@all _26981) = (@all _26981).
Proof. exact (eq_refl (@all _26981)). Qed.
Lemma lem1146198 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term80 _26978 _26981 t y f) = (term80 _26978 _26981 t y f).
Proof. exact (MK_COMB (@lem1146197 _26981) (@lem1146196 _26978 _26981 t y f)). Qed.
Lemma lem1146199 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : (term82 _26978 _26981 y f) = (term82 _26978 _26981 y f).
Proof. exact (fun_ext (fun t : list _26981 => @lem1146198 _26978 _26981 t y f)). Qed.
Lemma lem1146200 {_26981 : Type'} : (@all (list _26981)) = (@all (list _26981)).
Proof. exact (eq_refl (@all (list _26981))). Qed.
Lemma lem1146201 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : (term84 _26978 _26981 y f) = (term84 _26978 _26981 y f).
Proof. exact (MK_COMB (@lem1146200 _26981) (@lem1146199 _26978 _26981 y f)). Qed.
Lemma lem1146202 {_26978 _26981 : Type'} (f : _26981 -> _26978) : (term86 _26978 _26981 f) = (term86 _26978 _26981 f).
Proof. exact (fun_ext (fun y : _26978 => @lem1146201 _26978 _26981 y f)). Qed.
Lemma lem1146203 {_26978 : Type'} : (@all _26978) = (@all _26978).
Proof. exact (eq_refl (@all _26978)). Qed.
Lemma lem1146204 {_26978 _26981 : Type'} (f : _26981 -> _26978) : (term88 _26978 _26981 f) = (term88 _26978 _26981 f).
Proof. exact (MK_COMB (@lem1146203 _26978) (@lem1146202 _26978 _26981 f)). Qed.
Lemma lem1146205 {_26978 _26981 : Type'} : (term90 _26978 _26981) = (term90 _26978 _26981).
Proof. exact (fun_ext (fun f : _26981 -> _26978 => @lem1146204 _26978 _26981 f)). Qed.
Lemma lem1146206 {_26978 _26981 : Type'} : (@all (_26981 -> _26978)) = (@all (_26981 -> _26978)).
Proof. exact (eq_refl (@all (_26981 -> _26978))). Qed.
Lemma lem1146207 {_26978 _26981 : Type'} : (term92 _26978 _26981) = (term92 _26978 _26981).
Proof. exact (MK_COMB (@lem1146206 _26978 _26981) (@lem1146205 _26978 _26981)). Qed.
Lemma lem1146254 {_26978 _26981 : Type'} : (term91 _26978 _26981) = (term92 _26978 _26981).
Proof. exact (TRANS (@lem1146168 _26978 _26981) (@lem1146207 _26978 _26981)). Qed.
Lemma lem1146255 {_26978 _26981 : Type'} : (term92 _26978 _26981) = (term91 _26978 _26981).
Proof. exact (SYM (@lem1146254 _26978 _26981)). Qed.
Lemma lem1146257 (p : Prop) : p = (term69 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1146258 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : ((term59 _26978 _26981 h t y f) = (term68 _26978 _26981 h t y f)) = (term70 _26978 _26981 h t y f).
Proof. exact (@lem1146257 ((term59 _26978 _26981 h t y f) = (term68 _26978 _26981 h t y f))). Qed.
Lemma lem1146259 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term70 _26978 _26981 h t y f) = ((term59 _26978 _26981 h t y f) = (term68 _26978 _26981 h t y f)).
Proof. exact (SYM (@lem1146258 _26978 _26981 h t y f)). Qed.
Lemma lem1146260 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term71 _26978 _26981 h t y f) : term71 _26978 _26981 h t y f.
Proof. exact (h1). Qed.
Lemma lem1146271 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term95 _26978 _26981 t y f x) = (term96 _26978 _26981 t y f x).
Proof. exact (@lem17045 (@List.In _26981 x t) (y = (f x))). Qed.
Lemma lem1146274 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term93 _26978 _26981 t y f x) = (term93 _26978 _26981 t y f x).
Proof. exact (eq_refl (term93 _26978 _26981 t y f x)). Qed.
Lemma lem1146275 {_26981 : Type'} (P : _26981 -> Prop) : (term97 _26981 P) = (term98 _26981 P).
Proof. exact (@lem18394 _26981 P). Qed.
Lemma lem1146276 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term99 _26978 _26981 t y f) = (term100 _26978 _26981 t y f).
Proof. exact (@lem1146275 _26981 (term94 _26978 _26981 t y f)). Qed.
Lemma lem1146277 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term101 _26978 _26981 t y f x) = (term93 _26978 _26981 t y f x).
Proof. exact (eq_refl (term101 _26978 _26981 t y f x)). Qed.
Lemma lem1146278 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1146279 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term102 _26978 _26981 t y f x) = (term95 _26978 _26981 t y f x).
Proof. exact (MK_COMB (@lem1146278) (@lem1146277 _26978 _26981 t y f x)). Qed.
Lemma lem1146280 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term102 _26978 _26981 t y f x) = (term96 _26978 _26981 t y f x).
Proof. exact (TRANS (@lem1146279 _26978 _26981 t y f x) (@lem1146271 _26978 _26981 t y f x)). Qed.
Lemma lem1146281 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term103 _26978 _26981 t y f) = (term104 _26978 _26981 t y f).
Proof. exact (fun_ext (fun x : _26981 => @lem1146280 _26978 _26981 t y f x)). Qed.
Lemma lem1146282 {_26981 : Type'} : (@all _26981) = (@all _26981).
Proof. exact (eq_refl (@all _26981)). Qed.
Lemma lem1146283 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term100 _26978 _26981 t y f) = (term105 _26978 _26981 t y f).
Proof. exact (MK_COMB (@lem1146282 _26981) (@lem1146281 _26978 _26981 t y f)). Qed.
Lemma lem1146284 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term99 _26978 _26981 t y f) = (term105 _26978 _26981 t y f).
Proof. exact (TRANS (@lem1146276 _26978 _26981 t y f) (@lem1146283 _26978 _26981 t y f)). Qed.
Lemma lem1146285 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term94 _26978 _26981 t y f) = (term94 _26978 _26981 t y f).
Proof. exact (fun_ext (fun x : _26981 => @lem1146274 _26978 _26981 t y f x)). Qed.
Lemma lem1146286 {_26981 : Type'} : (@ex _26981) = (@ex _26981).
Proof. exact (eq_refl (@ex _26981)). Qed.
Lemma lem1146287 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term10 _26978 _26981 t y f) = (term10 _26978 _26981 t y f).
Proof. exact (MK_COMB (@lem1146286 _26981) (@lem1146285 _26978 _26981 t y f)). Qed.
Lemma lem1146289 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) (h : _26981) : (term106 _26978 _26981 y f h) = (term106 _26978 _26981 y f h).
Proof. exact (eq_refl (term106 _26978 _26981 y f h)). Qed.
Lemma lem1146290 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term107 _26978 _26981 h t y f) = (term108 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146289 _26978 _26981 y f h) (@lem1146284 _26978 _26981 t y f)). Qed.
Lemma lem1146291 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term109 _26978 _26981 h t y f) = (term107 _26978 _26981 h t y f).
Proof. exact (@lem17160 (y = (f h)) (term10 _26978 _26981 t y f)). Qed.
Lemma lem1146292 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term109 _26978 _26981 h t y f) = (term108 _26978 _26981 h t y f).
Proof. exact (TRANS (@lem1146291 _26978 _26981 h t y f) (@lem1146290 _26978 _26981 h t y f)). Qed.
Lemma lem1146294 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) (h : _26981) : (term58 _26978 _26981 y f h) = (term58 _26978 _26981 y f h).
Proof. exact (eq_refl (term58 _26978 _26981 y f h)). Qed.
Lemma lem1146295 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term59 _26978 _26981 h t y f) = (term59 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146294 _26978 _26981 y f h) (@lem1146287 _26978 _26981 t y f)). Qed.
Lemma lem1146304 {_26981 : Type'} (h : _26981) (x : _26981) (t : list _26981) : (term110 _26981 h x t) = (term111 _26981 h x t).
Proof. exact (@lem17160 (x = h) (@List.In _26981 x t)). Qed.
Lemma lem1146308 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term112 _26978 _26981 y f x) = (term112 _26978 _26981 y f x).
Proof. exact (eq_refl (term112 _26978 _26981 y f x)). Qed.
Lemma lem1146310 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1146311 {_26981 : Type'} (h : _26981) (x : _26981) (t : list _26981) : (term113 _26981 h x t) = (term114 _26981 h x t).
Proof. exact (MK_COMB (@lem1146310) (@lem1146304 _26981 h x t)). Qed.
Lemma lem1146312 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term115 _26978 _26981 h t y f x) = (term116 _26978 _26981 h t y f x).
Proof. exact (MK_COMB (@lem1146311 _26981 h x t) (@lem1146308 _26978 _26981 y f x)). Qed.
Lemma lem1146313 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term117 _26978 _26981 h t y f x) = (term115 _26978 _26981 h t y f x).
Proof. exact (@lem17045 (term56 _26981 h x t) (y = (f x))). Qed.
Lemma lem1146314 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term117 _26978 _26981 h t y f x) = (term116 _26978 _26981 h t y f x).
Proof. exact (TRANS (@lem1146313 _26978 _26981 h t y f x) (@lem1146312 _26978 _26981 h t y f x)). Qed.
Lemma lem1146317 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term65 _26978 _26981 h t y f x) = (term65 _26978 _26981 h t y f x).
Proof. exact (eq_refl (term65 _26978 _26981 h t y f x)). Qed.
Lemma lem1146318 {_26981 : Type'} (P : _26981 -> Prop) : (term97 _26981 P) = (term98 _26981 P).
Proof. exact (@lem18394 _26981 P). Qed.
Lemma lem1146319 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term118 _26978 _26981 h t y f) = (term119 _26978 _26981 h t y f).
Proof. exact (@lem1146318 _26981 (term67 _26978 _26981 h t y f)). Qed.
Lemma lem1146320 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term120 _26978 _26981 h t y f x) = (term65 _26978 _26981 h t y f x).
Proof. exact (eq_refl (term120 _26978 _26981 h t y f x)). Qed.
Lemma lem1146321 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1146322 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term121 _26978 _26981 h t y f x) = (term117 _26978 _26981 h t y f x).
Proof. exact (MK_COMB (@lem1146321) (@lem1146320 _26978 _26981 h t y f x)). Qed.
Lemma lem1146323 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term121 _26978 _26981 h t y f x) = (term116 _26978 _26981 h t y f x).
Proof. exact (TRANS (@lem1146322 _26978 _26981 h t y f x) (@lem1146314 _26978 _26981 h t y f x)). Qed.
Lemma lem1146324 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term122 _26978 _26981 h t y f) = (term123 _26978 _26981 h t y f).
Proof. exact (fun_ext (fun x : _26981 => @lem1146323 _26978 _26981 h t y f x)). Qed.
Lemma lem1146325 {_26981 : Type'} : (@all _26981) = (@all _26981).
Proof. exact (eq_refl (@all _26981)). Qed.
Lemma lem1146326 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term119 _26978 _26981 h t y f) = (term124 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146325 _26981) (@lem1146324 _26978 _26981 h t y f)). Qed.
Lemma lem1146327 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term118 _26978 _26981 h t y f) = (term124 _26978 _26981 h t y f).
Proof. exact (TRANS (@lem1146319 _26978 _26981 h t y f) (@lem1146326 _26978 _26981 h t y f)). Qed.
Lemma lem1146328 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term67 _26978 _26981 h t y f) = (term67 _26978 _26981 h t y f).
Proof. exact (fun_ext (fun x : _26981 => @lem1146317 _26978 _26981 h t y f x)). Qed.
Lemma lem1146329 {_26981 : Type'} : (@ex _26981) = (@ex _26981).
Proof. exact (eq_refl (@ex _26981)). Qed.
Lemma lem1146330 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term68 _26978 _26981 h t y f) = (term68 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146329 _26981) (@lem1146328 _26978 _26981 h t y f)). Qed.
Lemma lem1146331 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1146332 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term125 _26978 _26981 h t y f) = (term126 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146331) (@lem1146292 _26978 _26981 h t y f)). Qed.
Lemma lem1146333 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term127 _26978 _26981 h t y f) = (term128 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146332 _26978 _26981 h t y f) (@lem1146330 _26978 _26981 h t y f)). Qed.
Lemma lem1146334 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1146335 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term129 _26978 _26981 h t y f) = (term129 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146334) (@lem1146295 _26978 _26981 h t y f)). Qed.
Lemma lem1146336 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term130 _26978 _26981 h t y f) = (term131 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146335 _26978 _26981 h t y f) (@lem1146327 _26978 _26981 h t y f)). Qed.
Lemma lem1146337 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1146338 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term132 _26978 _26981 h t y f) = (term133 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146337) (@lem1146336 _26978 _26981 h t y f)). Qed.
Lemma lem1146339 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term134 _26978 _26981 h t y f) = (term135 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146338 _26978 _26981 h t y f) (@lem1146333 _26978 _26981 h t y f)). Qed.
Lemma lem1146340 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term71 _26978 _26981 h t y f) = (term134 _26978 _26981 h t y f).
Proof. exact (@lem17646 (term59 _26978 _26981 h t y f) (term68 _26978 _26981 h t y f)). Qed.
Lemma lem1146341 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term71 _26978 _26981 h t y f) = (term135 _26978 _26981 h t y f).
Proof. exact (TRANS (@lem1146340 _26978 _26981 h t y f) (@lem1146339 _26978 _26981 h t y f)). Qed.
Lemma lem1146536 {A : Type'} (P : Prop) (Q : A -> Prop) : (term136 A P Q) = (term137 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1146537 {_26981 : Type'} (P : Prop) (Q : _26981 -> Prop) : (term136 _26981 P Q) = (term137 _26981 P Q).
Proof. exact (@lem1146536 _26981 P Q). Qed.
Lemma lem1146538 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term138 _26978 _26981 h t y f) = (term139 _26978 _26981 h t y f).
Proof. exact (@lem1146537 _26981 (y = (f h)) (term94 _26978 _26981 t y f)). Qed.
Lemma lem1146539 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term101 _26978 _26981 t y f x) = (term93 _26978 _26981 t y f x).
Proof. exact (eq_refl (term101 _26978 _26981 t y f x)). Qed.
Lemma lem1146540 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term140 _26978 _26981 t y f) = (term94 _26978 _26981 t y f).
Proof. exact (fun_ext (fun x : _26981 => @lem1146539 _26978 _26981 t y f x)). Qed.
Lemma lem1146541 {_26981 : Type'} : (@ex _26981) = (@ex _26981).
Proof. exact (eq_refl (@ex _26981)). Qed.
Lemma lem1146542 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term141 _26978 _26981 t y f) = (term10 _26978 _26981 t y f).
Proof. exact (MK_COMB (@lem1146541 _26981) (@lem1146540 _26978 _26981 t y f)). Qed.
Lemma lem1146543 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) (h : _26981) : (term58 _26978 _26981 y f h) = (term58 _26978 _26981 y f h).
Proof. exact (eq_refl (term58 _26978 _26981 y f h)). Qed.
Lemma lem1146544 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term138 _26978 _26981 h t y f) = (term59 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146543 _26978 _26981 y f h) (@lem1146542 _26978 _26981 t y f)). Qed.
Lemma lem1146545 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1146546 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term142 _26978 _26981 h t y f) = (term61 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146545) (@lem1146544 _26978 _26981 h t y f)). Qed.
Lemma lem1146547 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term101 _26978 _26981 t y f x) = (term93 _26978 _26981 t y f x).
Proof. exact (eq_refl (term101 _26978 _26981 t y f x)). Qed.
Lemma lem1146548 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) (h : _26981) : (term58 _26978 _26981 y f h) = (term58 _26978 _26981 y f h).
Proof. exact (eq_refl (term58 _26978 _26981 y f h)). Qed.
Lemma lem1146549 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term143 _26978 _26981 h t y f x) = (term144 _26978 _26981 h t y f x).
Proof. exact (MK_COMB (@lem1146548 _26978 _26981 y f h) (@lem1146547 _26978 _26981 t y f x)). Qed.
Lemma lem1146550 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term145 _26978 _26981 h t y f) = (term146 _26978 _26981 h t y f).
Proof. exact (fun_ext (fun x : _26981 => @lem1146549 _26978 _26981 h t y f x)). Qed.
Lemma lem1146551 {_26981 : Type'} : (@ex _26981) = (@ex _26981).
Proof. exact (eq_refl (@ex _26981)). Qed.
Lemma lem1146552 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term139 _26978 _26981 h t y f) = (term147 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146551 _26981) (@lem1146550 _26978 _26981 h t y f)). Qed.
Lemma lem1146553 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : ((term138 _26978 _26981 h t y f) = (term139 _26978 _26981 h t y f)) = ((term59 _26978 _26981 h t y f) = (term147 _26978 _26981 h t y f)).
Proof. exact (MK_COMB (@lem1146546 _26978 _26981 h t y f) (@lem1146552 _26978 _26981 h t y f)). Qed.
Lemma lem1146554 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term59 _26978 _26981 h t y f) = (term147 _26978 _26981 h t y f).
Proof. exact (EQ_MP (@lem1146553 _26978 _26981 h t y f) (@lem1146538 _26978 _26981 h t y f)). Qed.
Lemma lem1146555 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1146556 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term129 _26978 _26981 h t y f) = (term148 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146555) (@lem1146554 _26978 _26981 h t y f)). Qed.
Lemma lem1146557 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term124 _26978 _26981 h t y f) = (term124 _26978 _26981 h t y f).
Proof. exact (eq_refl (term124 _26978 _26981 h t y f)). Qed.
Lemma lem1146558 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term131 _26978 _26981 h t y f) = (term149 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146556 _26978 _26981 h t y f) (@lem1146557 _26978 _26981 h t y f)). Qed.
Lemma lem1146560 {A : Type'} (P : A -> Prop) (Q : Prop) : (term150 A P Q) = (term151 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1146561 {_26981 : Type'} (P : _26981 -> Prop) (Q : Prop) : (term150 _26981 P Q) = (term151 _26981 P Q).
Proof. exact (@lem1146560 _26981 P Q). Qed.
Lemma lem1146562 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term152 _26978 _26981 h t y f) = (term153 _26978 _26981 h t y f).
Proof. exact (@lem1146561 _26981 (term146 _26978 _26981 h t y f) (term124 _26978 _26981 h t y f)). Qed.
Lemma lem1146563 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term154 _26978 _26981 h t y f x) = (term144 _26978 _26981 h t y f x).
Proof. exact (eq_refl (term154 _26978 _26981 h t y f x)). Qed.
Lemma lem1146564 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term155 _26978 _26981 h t y f) = (term146 _26978 _26981 h t y f).
Proof. exact (fun_ext (fun x : _26981 => @lem1146563 _26978 _26981 h t y f x)). Qed.
Lemma lem1146565 {_26981 : Type'} : (@ex _26981) = (@ex _26981).
Proof. exact (eq_refl (@ex _26981)). Qed.
Lemma lem1146566 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term156 _26978 _26981 h t y f) = (term147 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146565 _26981) (@lem1146564 _26978 _26981 h t y f)). Qed.
Lemma lem1146567 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1146568 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term157 _26978 _26981 h t y f) = (term148 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146567) (@lem1146566 _26978 _26981 h t y f)). Qed.
Lemma lem1146569 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term124 _26978 _26981 h t y f) = (term124 _26978 _26981 h t y f).
Proof. exact (eq_refl (term124 _26978 _26981 h t y f)). Qed.
Lemma lem1146570 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term152 _26978 _26981 h t y f) = (term149 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146568 _26978 _26981 h t y f) (@lem1146569 _26978 _26981 h t y f)). Qed.
Lemma lem1146571 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1146572 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term158 _26978 _26981 h t y f) = (term159 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146571) (@lem1146570 _26978 _26981 h t y f)). Qed.
Lemma lem1146573 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term154 _26978 _26981 h t y f x) = (term144 _26978 _26981 h t y f x).
Proof. exact (eq_refl (term154 _26978 _26981 h t y f x)). Qed.
Lemma lem1146574 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1146575 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term160 _26978 _26981 h t y f x) = (term161 _26978 _26981 h t y f x).
Proof. exact (MK_COMB (@lem1146574) (@lem1146573 _26978 _26981 h t y f x)). Qed.
Lemma lem1146576 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term124 _26978 _26981 h t y f) = (term124 _26978 _26981 h t y f).
Proof. exact (eq_refl (term124 _26978 _26981 h t y f)). Qed.
Lemma lem1146577 {_26978 _26981 : Type'} (x : _26981) (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term162 _26978 _26981 x h t y f) = (term163 _26978 _26981 x h t y f).
Proof. exact (MK_COMB (@lem1146575 _26978 _26981 h t y f x) (@lem1146576 _26978 _26981 h t y f)). Qed.
Lemma lem1146578 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term164 _26978 _26981 h t y f) = (term165 _26978 _26981 h t y f).
Proof. exact (fun_ext (fun x : _26981 => @lem1146577 _26978 _26981 x h t y f)). Qed.
Lemma lem1146579 {_26981 : Type'} : (@ex _26981) = (@ex _26981).
Proof. exact (eq_refl (@ex _26981)). Qed.
Lemma lem1146580 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term153 _26978 _26981 h t y f) = (term166 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146579 _26981) (@lem1146578 _26978 _26981 h t y f)). Qed.
Lemma lem1146581 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : ((term152 _26978 _26981 h t y f) = (term153 _26978 _26981 h t y f)) = ((term149 _26978 _26981 h t y f) = (term166 _26978 _26981 h t y f)).
Proof. exact (MK_COMB (@lem1146572 _26978 _26981 h t y f) (@lem1146580 _26978 _26981 h t y f)). Qed.
Lemma lem1146582 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term149 _26978 _26981 h t y f) = (term166 _26978 _26981 h t y f).
Proof. exact (EQ_MP (@lem1146581 _26978 _26981 h t y f) (@lem1146562 _26978 _26981 h t y f)). Qed.
Lemma lem1146583 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term131 _26978 _26981 h t y f) = (term166 _26978 _26981 h t y f).
Proof. exact (TRANS (@lem1146558 _26978 _26981 h t y f) (@lem1146582 _26978 _26981 h t y f)). Qed.
Lemma lem1146584 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1146585 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term133 _26978 _26981 h t y f) = (term167 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146584) (@lem1146583 _26978 _26981 h t y f)). Qed.
Lemma lem1146587 {A : Type'} (P : Prop) (Q : A -> Prop) : (term168 A P Q) = (term169 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1146588 {_26981 : Type'} (P : Prop) (Q : _26981 -> Prop) : (term168 _26981 P Q) = (term169 _26981 P Q).
Proof. exact (@lem1146587 _26981 P Q). Qed.
Lemma lem1146589 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term170 _26978 _26981 h t y f) = (term171 _26978 _26981 h t y f).
Proof. exact (@lem1146588 _26981 (term108 _26978 _26981 h t y f) (term67 _26978 _26981 h t y f)). Qed.
Lemma lem1146590 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term120 _26978 _26981 h t y f x) = (term65 _26978 _26981 h t y f x).
Proof. exact (eq_refl (term120 _26978 _26981 h t y f x)). Qed.
Lemma lem1146591 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term172 _26978 _26981 h t y f) = (term67 _26978 _26981 h t y f).
Proof. exact (fun_ext (fun x : _26981 => @lem1146590 _26978 _26981 h t y f x)). Qed.
Lemma lem1146592 {_26981 : Type'} : (@ex _26981) = (@ex _26981).
Proof. exact (eq_refl (@ex _26981)). Qed.
Lemma lem1146593 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term173 _26978 _26981 h t y f) = (term68 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146592 _26981) (@lem1146591 _26978 _26981 h t y f)). Qed.
Lemma lem1146594 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term126 _26978 _26981 h t y f) = (term126 _26978 _26981 h t y f).
Proof. exact (eq_refl (term126 _26978 _26981 h t y f)). Qed.
Lemma lem1146595 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term170 _26978 _26981 h t y f) = (term128 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146594 _26978 _26981 h t y f) (@lem1146593 _26978 _26981 h t y f)). Qed.
Lemma lem1146596 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1146597 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term174 _26978 _26981 h t y f) = (term175 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146596) (@lem1146595 _26978 _26981 h t y f)). Qed.
Lemma lem1146598 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term120 _26978 _26981 h t y f x) = (term65 _26978 _26981 h t y f x).
Proof. exact (eq_refl (term120 _26978 _26981 h t y f x)). Qed.
Lemma lem1146599 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term126 _26978 _26981 h t y f) = (term126 _26978 _26981 h t y f).
Proof. exact (eq_refl (term126 _26978 _26981 h t y f)). Qed.
Lemma lem1146600 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term176 _26978 _26981 h t y f x) = (term177 _26978 _26981 h t y f x).
Proof. exact (MK_COMB (@lem1146599 _26978 _26981 h t y f) (@lem1146598 _26978 _26981 h t y f x)). Qed.
Lemma lem1146601 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term178 _26978 _26981 h t y f) = (term179 _26978 _26981 h t y f).
Proof. exact (fun_ext (fun x : _26981 => @lem1146600 _26978 _26981 h t y f x)). Qed.
Lemma lem1146602 {_26981 : Type'} : (@ex _26981) = (@ex _26981).
Proof. exact (eq_refl (@ex _26981)). Qed.
Lemma lem1146603 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term171 _26978 _26981 h t y f) = (term180 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146602 _26981) (@lem1146601 _26978 _26981 h t y f)). Qed.
Lemma lem1146604 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : ((term170 _26978 _26981 h t y f) = (term171 _26978 _26981 h t y f)) = ((term128 _26978 _26981 h t y f) = (term180 _26978 _26981 h t y f)).
Proof. exact (MK_COMB (@lem1146597 _26978 _26981 h t y f) (@lem1146603 _26978 _26981 h t y f)). Qed.
Lemma lem1146605 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term128 _26978 _26981 h t y f) = (term180 _26978 _26981 h t y f).
Proof. exact (EQ_MP (@lem1146604 _26978 _26981 h t y f) (@lem1146589 _26978 _26981 h t y f)). Qed.
Lemma lem1146606 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term135 _26978 _26981 h t y f) = (term181 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146585 _26978 _26981 h t y f) (@lem1146605 _26978 _26981 h t y f)). Qed.
Lemma lem1146608 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term182 A P Q) = (term183 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1146609 {_26981 : Type'} (P : _26981 -> Prop) (Q : _26981 -> Prop) : (term182 _26981 P Q) = (term183 _26981 P Q).
Proof. exact (@lem1146608 _26981 P Q). Qed.
Lemma lem1146610 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term184 _26978 _26981 h t y f) = (term185 _26978 _26981 h t y f).
Proof. exact (@lem1146609 _26981 (term165 _26978 _26981 h t y f) (term179 _26978 _26981 h t y f)). Qed.
Lemma lem1146611 {_26978 _26981 : Type'} (x : _26981) (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term186 _26978 _26981 h t y f x) = (term163 _26978 _26981 x h t y f).
Proof. exact (eq_refl (term186 _26978 _26981 h t y f x)). Qed.
Lemma lem1146612 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term187 _26978 _26981 h t y f) = (term165 _26978 _26981 h t y f).
Proof. exact (fun_ext (fun x : _26981 => @lem1146611 _26978 _26981 x h t y f)). Qed.
Lemma lem1146613 {_26981 : Type'} : (@ex _26981) = (@ex _26981).
Proof. exact (eq_refl (@ex _26981)). Qed.
Lemma lem1146614 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term188 _26978 _26981 h t y f) = (term166 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146613 _26981) (@lem1146612 _26978 _26981 h t y f)). Qed.
Lemma lem1146615 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1146616 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term189 _26978 _26981 h t y f) = (term167 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146615) (@lem1146614 _26978 _26981 h t y f)). Qed.
Lemma lem1146617 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term190 _26978 _26981 h t y f x) = (term177 _26978 _26981 h t y f x).
Proof. exact (eq_refl (term190 _26978 _26981 h t y f x)). Qed.
Lemma lem1146618 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term191 _26978 _26981 h t y f) = (term179 _26978 _26981 h t y f).
Proof. exact (fun_ext (fun x : _26981 => @lem1146617 _26978 _26981 h t y f x)). Qed.
Lemma lem1146619 {_26981 : Type'} : (@ex _26981) = (@ex _26981).
Proof. exact (eq_refl (@ex _26981)). Qed.
Lemma lem1146620 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term192 _26978 _26981 h t y f) = (term180 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146619 _26981) (@lem1146618 _26978 _26981 h t y f)). Qed.
Lemma lem1146621 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term184 _26978 _26981 h t y f) = (term181 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146616 _26978 _26981 h t y f) (@lem1146620 _26978 _26981 h t y f)). Qed.
Lemma lem1146622 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1146623 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term193 _26978 _26981 h t y f) = (term194 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146622) (@lem1146621 _26978 _26981 h t y f)). Qed.
Lemma lem1146624 {_26978 _26981 : Type'} (x : _26981) (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term186 _26978 _26981 h t y f x) = (term163 _26978 _26981 x h t y f).
Proof. exact (eq_refl (term186 _26978 _26981 h t y f x)). Qed.
Lemma lem1146625 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1146626 {_26978 _26981 : Type'} (x : _26981) (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term195 _26978 _26981 h t y f x) = (term196 _26978 _26981 x h t y f).
Proof. exact (MK_COMB (@lem1146625) (@lem1146624 _26978 _26981 x h t y f)). Qed.
Lemma lem1146627 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term190 _26978 _26981 h t y f x) = (term177 _26978 _26981 h t y f x).
Proof. exact (eq_refl (term190 _26978 _26981 h t y f x)). Qed.
Lemma lem1146628 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term197 _26978 _26981 h t y f x) = (term198 _26978 _26981 h t y f x).
Proof. exact (MK_COMB (@lem1146626 _26978 _26981 x h t y f) (@lem1146627 _26978 _26981 h t y f x)). Qed.
Lemma lem1146629 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term199 _26978 _26981 h t y f) = (term200 _26978 _26981 h t y f).
Proof. exact (fun_ext (fun x : _26981 => @lem1146628 _26978 _26981 h t y f x)). Qed.
Lemma lem1146630 {_26981 : Type'} : (@ex _26981) = (@ex _26981).
Proof. exact (eq_refl (@ex _26981)). Qed.
Lemma lem1146631 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term185 _26978 _26981 h t y f) = (term201 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146630 _26981) (@lem1146629 _26978 _26981 h t y f)). Qed.
Lemma lem1146632 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : ((term184 _26978 _26981 h t y f) = (term185 _26978 _26981 h t y f)) = ((term181 _26978 _26981 h t y f) = (term201 _26978 _26981 h t y f)).
Proof. exact (MK_COMB (@lem1146623 _26978 _26981 h t y f) (@lem1146631 _26978 _26981 h t y f)). Qed.
Lemma lem1146633 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term181 _26978 _26981 h t y f) = (term201 _26978 _26981 h t y f).
Proof. exact (EQ_MP (@lem1146632 _26978 _26981 h t y f) (@lem1146610 _26978 _26981 h t y f)). Qed.
Lemma lem1146635 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term135 _26978 _26981 h t y f) = (term201 _26978 _26981 h t y f).
Proof. exact (TRANS (@lem1146606 _26978 _26981 h t y f) (@lem1146633 _26978 _26981 h t y f)). Qed.
Lemma lem1146636 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term71 _26978 _26981 h t y f) = (term201 _26978 _26981 h t y f).
Proof. exact (TRANS (@lem1146341 _26978 _26981 h t y f) (@lem1146635 _26978 _26981 h t y f)). Qed.
Lemma lem1146637 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term71 _26978 _26981 h t y f) : term201 _26978 _26981 h t y f.
Proof. exact (EQ_MP (@lem1146636 _26978 _26981 h t y f) (@lem1146260 _26978 _26981 h t y f h1)). Qed.
Lemma lem1146638 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h1 : term198 _26978 _26981 h t y f x) : term198 _26978 _26981 h t y f x.
Proof. exact (h1). Qed.
Lemma lem1146661 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term65 _26978 _26981 h t y f x) = (term65 _26978 _26981 h t y f x).
Proof. exact (eq_refl (term65 _26978 _26981 h t y f x)). Qed.
Lemma lem1146680 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term96 _26978 _26981 t y f x) = (term96 _26978 _26981 t y f x).
Proof. exact (eq_refl (term96 _26978 _26981 t y f x)). Qed.
Lemma lem1146681 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term104 _26978 _26981 t y f) = (term104 _26978 _26981 t y f).
Proof. exact (fun_ext (fun x : _26981 => @lem1146680 _26978 _26981 t y f x)). Qed.
Lemma lem1146682 {_26981 : Type'} : (@all _26981) = (@all _26981).
Proof. exact (eq_refl (@all _26981)). Qed.
Lemma lem1146683 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term105 _26978 _26981 t y f) = (term105 _26978 _26981 t y f).
Proof. exact (MK_COMB (@lem1146682 _26981) (@lem1146681 _26978 _26981 t y f)). Qed.
Lemma lem1146694 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) (h : _26981) : (term106 _26978 _26981 y f h) = (term106 _26978 _26981 y f h).
Proof. exact (eq_refl (term106 _26978 _26981 y f h)). Qed.
Lemma lem1146695 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term108 _26978 _26981 h t y f) = (term108 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146694 _26978 _26981 y f h) (@lem1146683 _26978 _26981 t y f)). Qed.
Lemma lem1146696 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1146697 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term126 _26978 _26981 h t y f) = (term126 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146696) (@lem1146695 _26978 _26981 h t y f)). Qed.
Lemma lem1146698 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term177 _26978 _26981 h t y f x) = (term177 _26978 _26981 h t y f x).
Proof. exact (MK_COMB (@lem1146697 _26978 _26981 h t y f) (@lem1146661 _26978 _26981 h t y f x)). Qed.
Lemma lem1146727 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term116 _26978 _26981 h t y f x) = (term116 _26978 _26981 h t y f x).
Proof. exact (eq_refl (term116 _26978 _26981 h t y f x)). Qed.
Lemma lem1146728 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term123 _26978 _26981 h t y f) = (term123 _26978 _26981 h t y f).
Proof. exact (fun_ext (fun x : _26981 => @lem1146727 _26978 _26981 h t y f x)). Qed.
Lemma lem1146729 {_26981 : Type'} : (@all _26981) = (@all _26981).
Proof. exact (eq_refl (@all _26981)). Qed.
Lemma lem1146730 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term124 _26978 _26981 h t y f) = (term124 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146729 _26981) (@lem1146728 _26978 _26981 h t y f)). Qed.
Lemma lem1146757 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term161 _26978 _26981 h t y f x) = (term161 _26978 _26981 h t y f x).
Proof. exact (eq_refl (term161 _26978 _26981 h t y f x)). Qed.
Lemma lem1146758 {_26978 _26981 : Type'} (x : _26981) (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term163 _26978 _26981 x h t y f) = (term163 _26978 _26981 x h t y f).
Proof. exact (MK_COMB (@lem1146757 _26978 _26981 h t y f x) (@lem1146730 _26978 _26981 h t y f)). Qed.
Lemma lem1146759 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1146760 {_26978 _26981 : Type'} (x : _26981) (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term196 _26978 _26981 x h t y f) = (term196 _26978 _26981 x h t y f).
Proof. exact (MK_COMB (@lem1146759) (@lem1146758 _26978 _26981 x h t y f)). Qed.
Lemma lem1146761 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term198 _26978 _26981 h t y f x) = (term198 _26978 _26981 h t y f x).
Proof. exact (MK_COMB (@lem1146760 _26978 _26981 x h t y f) (@lem1146698 _26978 _26981 h t y f x)). Qed.
Lemma lem1146762 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h1 : term198 _26978 _26981 h t y f x) : term198 _26978 _26981 h t y f x.
Proof. exact (EQ_MP (@lem1146761 _26978 _26981 h t y f x) (@lem1146638 _26978 _26981 h t y f x h1)). Qed.
Lemma lem1146763 {_26978 _26981 : Type'} (x : _26981) (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term163 _26978 _26981 x h t y f) : term163 _26978 _26981 x h t y f.
Proof. exact (h1). Qed.
Lemma lem1146764 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h1 : term177 _26978 _26981 h t y f x) : term177 _26978 _26981 h t y f x.
Proof. exact (h1). Qed.
Lemma lem1146765 {_26978 _26981 : Type'} (x : _26981) (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term163 _26978 _26981 x h t y f) : term124 _26978 _26981 h t y f.
Proof. exact (proj2 (@lem1146763 _26978 _26981 x h t y f h1)). Qed.
Lemma lem1146766 {_26978 _26981 : Type'} (x : _26981) (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term163 _26978 _26981 x h t y f) : term144 _26978 _26981 h t y f x.
Proof. exact (proj1 (@lem1146763 _26978 _26981 x h t y f h1)). Qed.
Lemma lem1146768 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h1 : term93 _26978 _26981 t y f x) : term93 _26978 _26981 t y f x.
Proof. exact (h1). Qed.
Lemma lem1146771 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h1 : term177 _26978 _26981 h t y f x) : term65 _26978 _26981 h t y f x.
Proof. exact (proj2 (@lem1146764 _26978 _26981 h t y f x h1)). Qed.
Lemma lem1146772 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h1 : term177 _26978 _26981 h t y f x) : term108 _26978 _26981 h t y f.
Proof. exact (proj1 (@lem1146764 _26978 _26981 h t y f x h1)). Qed.
Lemma lem1146774 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h1 : term177 _26978 _26981 h t y f x) : term56 _26981 h x t.
Proof. exact (proj1 (@lem1146771 _26978 _26981 h t y f x h1)). Qed.
Lemma lem1146775 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h1 : term177 _26978 _26981 h t y f x) : term105 _26978 _26981 t y f.
Proof. exact (proj2 (@lem1146772 _26978 _26981 h t y f x h1)). Qed.
Lemma lem1146796 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term116 _26978 _26981 h t y f x) = (term202 _26978 _26981 h t y f x).
Proof. exact (@lem19699 (term203 _26981 x h) (term204 _26981 x t) (term112 _26978 _26981 y f x)). Qed.
Lemma lem1146797 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term123 _26978 _26981 h t y f) = (term205 _26978 _26981 h t y f).
Proof. exact (fun_ext (fun x : _26981 => @lem1146796 _26978 _26981 h t y f x)). Qed.
Lemma lem1146798 {_26981 : Type'} : (@all _26981) = (@all _26981).
Proof. exact (eq_refl (@all _26981)). Qed.
Lemma lem1146800 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term124 _26978 _26981 h t y f) = (term206 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146798 _26981) (@lem1146797 _26978 _26981 h t y f)). Qed.
Lemma lem1146801 {_26978 _26981 : Type'} (x : _26981) (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term163 _26978 _26981 x h t y f) : term206 _26978 _26981 h t y f.
Proof. exact (EQ_MP (@lem1146800 _26978 _26981 h t y f) (@lem1146765 _26978 _26981 x h t y f h1)). Qed.
Lemma lem1146805 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) (h : _26981) (h1 : y = (f h)) : y = (f h).
Proof. exact (h1). Qed.
Lemma lem1146823 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term116 _26978 _26981 h t y f x) = (term202 _26978 _26981 h t y f x).
Proof. exact (@lem19699 (term203 _26981 x h) (term204 _26981 x t) (term112 _26978 _26981 y f x)). Qed.
Lemma lem1146824 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term123 _26978 _26981 h t y f) = (term205 _26978 _26981 h t y f).
Proof. exact (fun_ext (fun x : _26981 => @lem1146823 _26978 _26981 h t y f x)). Qed.
Lemma lem1146825 {_26981 : Type'} : (@all _26981) = (@all _26981).
Proof. exact (eq_refl (@all _26981)). Qed.
Lemma lem1146827 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term124 _26978 _26981 h t y f) = (term206 _26978 _26981 h t y f).
Proof. exact (MK_COMB (@lem1146825 _26981) (@lem1146824 _26978 _26981 h t y f)). Qed.
Lemma lem1146828 {_26978 _26981 : Type'} (x : _26981) (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term163 _26978 _26981 x h t y f) : term206 _26978 _26981 h t y f.
Proof. exact (EQ_MP (@lem1146827 _26978 _26981 h t y f) (@lem1146765 _26978 _26981 x h t y f h1)). Qed.
Lemma lem1146861 {_26981 : Type'} (x : _26981) (h : _26981) (h1 : x = h) : x = h.
Proof. exact (h1). Qed.
Lemma lem1146877 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term96 _26978 _26981 t y f x) = (term96 _26978 _26981 t y f x).
Proof. exact (eq_refl (term96 _26978 _26981 t y f x)). Qed.
Lemma lem1146878 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term104 _26978 _26981 t y f) = (term104 _26978 _26981 t y f).
Proof. exact (fun_ext (fun x : _26981 => @lem1146877 _26978 _26981 t y f x)). Qed.
Lemma lem1146879 {_26981 : Type'} : (@all _26981) = (@all _26981).
Proof. exact (eq_refl (@all _26981)). Qed.
Lemma lem1146881 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term105 _26978 _26981 t y f) = (term105 _26978 _26981 t y f).
Proof. exact (MK_COMB (@lem1146879 _26981) (@lem1146878 _26978 _26981 t y f)). Qed.
Lemma lem1146882 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h1 : term177 _26978 _26981 h t y f x) : term105 _26978 _26981 t y f.
Proof. exact (EQ_MP (@lem1146881 _26978 _26981 t y f) (@lem1146775 _26978 _26981 h t y f x h1)). Qed.
Lemma lem1146886 {_26981 : Type'} (x : _26981) (t : list _26981) (h1 : @List.In _26981 x t) : @List.In _26981 x t.
Proof. exact (h1). Qed.
Lemma lem1146887 {_26978 _26981 : Type'} (_18963 : _26981) (x : _26981) (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term163 _26978 _26981 x h t y f) : term207 _26978 _26981 h t y f _18963.
Proof. exact (@lem1146801 _26978 _26981 x h t y f h1 _18963). Qed.
Lemma lem1146888 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (_18963 : _26981) : (term207 _26978 _26981 h t y f _18963) = (term202 _26978 _26981 h t y f _18963).
Proof. exact (eq_refl (term207 _26978 _26981 h t y f _18963)). Qed.
Lemma lem1146889 {_26978 _26981 : Type'} (_18963 : _26981) (x : _26981) (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term163 _26978 _26981 x h t y f) : term202 _26978 _26981 h t y f _18963.
Proof. exact (EQ_MP (@lem1146888 _26978 _26981 h t y f _18963) (@lem1146887 _26978 _26981 _18963 x h t y f h1)). Qed.
Lemma lem1146890 {_26978 _26981 : Type'} (_18964 : _26981) (x : _26981) (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term163 _26978 _26981 x h t y f) : term207 _26978 _26981 h t y f _18964.
Proof. exact (@lem1146828 _26978 _26981 x h t y f h1 _18964). Qed.
Lemma lem1146891 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (_18964 : _26981) : (term207 _26978 _26981 h t y f _18964) = (term202 _26978 _26981 h t y f _18964).
Proof. exact (eq_refl (term207 _26978 _26981 h t y f _18964)). Qed.
Lemma lem1146892 {_26978 _26981 : Type'} (_18964 : _26981) (x : _26981) (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term163 _26978 _26981 x h t y f) : term202 _26978 _26981 h t y f _18964.
Proof. exact (EQ_MP (@lem1146891 _26978 _26981 h t y f _18964) (@lem1146890 _26978 _26981 _18964 x h t y f h1)). Qed.
Lemma lem1146896 {_26978 _26981 : Type'} (_18966 : _26981) (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h1 : term177 _26978 _26981 h t y f x) : term208 _26978 _26981 t y f _18966.
Proof. exact (@lem1146882 _26978 _26981 h t y f x h1 _18966). Qed.
Lemma lem1146897 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (_18966 : _26981) : (term208 _26978 _26981 t y f _18966) = (term96 _26978 _26981 t y f _18966).
Proof. exact (eq_refl (term208 _26978 _26981 t y f _18966)). Qed.
Lemma lem1146904 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) (h : _26981) (h1 : y = (f h)) : y = (f h).
Proof. exact (h1). Qed.
Lemma lem1146910 {_26978 _26981 : Type'} (_18963 : _26981) (x : _26981) (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term163 _26978 _26981 x h t y f) : term209 _26978 _26981 h y f _18963.
Proof. exact (proj1 (@lem1146889 _26978 _26981 _18963 x h t y f h1)). Qed.
Lemma lem1146920 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h1 : term93 _26978 _26981 t y f x) : y = (f x).
Proof. exact (proj2 (@lem1146768 _26978 _26981 t y f x h1)). Qed.
Lemma lem1146932 {_26978 _26981 : Type'} (_18964 : _26981) (x : _26981) (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term163 _26978 _26981 x h t y f) : term96 _26978 _26981 t y f _18964.
Proof. exact (proj2 (@lem1146892 _26978 _26981 _18964 x h t y f h1)). Qed.
Lemma lem1146934 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h1 : term177 _26978 _26981 h t y f x) : y = (f x).
Proof. exact (proj2 (@lem1146771 _26978 _26981 h t y f x h1)). Qed.
Lemma lem1146944 {_26981 : Type'} (x : _26981) (h : _26981) (h1 : x = h) : x = h.
Proof. exact (h1). Qed.
Lemma lem1146946 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h1 : term177 _26978 _26981 h t y f x) : y = (f x).
Proof. exact (proj2 (@lem1146771 _26978 _26981 h t y f x h1)). Qed.
Lemma lem1146954 {_26978 _26981 : Type'} (_18966 : _26981) (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h1 : term177 _26978 _26981 h t y f x) : term96 _26978 _26981 t y f _18966.
Proof. exact (EQ_MP (@lem1146897 _26978 _26981 t y f _18966) (@lem1146896 _26978 _26981 _18966 h t y f x h1)). Qed.
Lemma lem1146956 {_26981 : Type'} (x : _26981) (t : list _26981) (h1 : @List.In _26981 x t) : @List.In _26981 x t.
Proof. exact (h1). Qed.
Lemma lem1146971 {_26978 _26981 : Type'} (h : _26981) (f : _26981 -> _26978) (_18963 : _26981) : (term210 _26978 _26981 h f _18963) = (term210 _26978 _26981 h f _18963).
Proof. exact (eq_refl (term210 _26978 _26981 h f _18963)). Qed.
Lemma lem1146972 {_26978 _26981 : Type'} (_18963 : _26981) (y : _26978) (f : _26981 -> _26978) (h : _26981) (h1 : y = (f h)) : (term211 _26978 _26981 h f _18963 y) = (term212 _26978 _26981 _18963 f h).
Proof. exact (MK_COMB (@lem1146971 _26978 _26981 h f _18963) (@lem1146904 _26978 _26981 y f h h1)). Qed.
Lemma lem1146973 {_26978 _26981 : Type'} (h : _26981) (f : _26981 -> _26978) (_18963 : _26981) : (term212 _26978 _26981 _18963 f h) = (term213 _26978 _26981 h f _18963).
Proof. exact (eq_refl (term212 _26978 _26981 _18963 f h)). Qed.
Lemma lem1146974 {_26978 _26981 : Type'} (h : _26981) (f : _26981 -> _26978) (_18963 : _26981) (y : _26978) : (term214 _26978 _26981 h f _18963 y) = (term214 _26978 _26981 h f _18963 y).
Proof. exact (eq_refl (term214 _26978 _26981 h f _18963 y)). Qed.
Lemma lem1146975 {_26978 _26981 : Type'} (y : _26978) (h : _26981) (f : _26981 -> _26978) (_18963 : _26981) : ((term211 _26978 _26981 h f _18963 y) = (term212 _26978 _26981 _18963 f h)) = ((term211 _26978 _26981 h f _18963 y) = (term213 _26978 _26981 h f _18963)).
Proof. exact (MK_COMB (@lem1146974 _26978 _26981 h f _18963 y) (@lem1146973 _26978 _26981 h f _18963)). Qed.
Lemma lem1146976 {_26978 _26981 : Type'} (h : _26981) (y : _26978) (f : _26981 -> _26978) (_18963 : _26981) : (term211 _26978 _26981 h f _18963 y) = (term209 _26978 _26981 h y f _18963).
Proof. exact (eq_refl (term211 _26978 _26981 h f _18963 y)). Qed.
Lemma lem1146977 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1146978 {_26978 _26981 : Type'} (h : _26981) (y : _26978) (f : _26981 -> _26978) (_18963 : _26981) : (term214 _26978 _26981 h f _18963 y) = (term215 _26978 _26981 h y f _18963).
Proof. exact (MK_COMB (@lem1146977) (@lem1146976 _26978 _26981 h y f _18963)). Qed.
Lemma lem1146979 {_26978 _26981 : Type'} (h : _26981) (f : _26981 -> _26978) (_18963 : _26981) : (term213 _26978 _26981 h f _18963) = (term213 _26978 _26981 h f _18963).
Proof. exact (eq_refl (term213 _26978 _26981 h f _18963)). Qed.
Lemma lem1146980 {_26978 _26981 : Type'} (y : _26978) (h : _26981) (f : _26981 -> _26978) (_18963 : _26981) : ((term211 _26978 _26981 h f _18963 y) = (term213 _26978 _26981 h f _18963)) = ((term209 _26978 _26981 h y f _18963) = (term213 _26978 _26981 h f _18963)).
Proof. exact (MK_COMB (@lem1146978 _26978 _26981 h y f _18963) (@lem1146979 _26978 _26981 h f _18963)). Qed.
Lemma lem1146981 {_26978 _26981 : Type'} (y : _26978) (h : _26981) (f : _26981 -> _26978) (_18963 : _26981) : ((term211 _26978 _26981 h f _18963 y) = (term212 _26978 _26981 _18963 f h)) = ((term209 _26978 _26981 h y f _18963) = (term213 _26978 _26981 h f _18963)).
Proof. exact (TRANS (@lem1146975 _26978 _26981 y h f _18963) (@lem1146980 _26978 _26981 y h f _18963)). Qed.
Lemma lem1146982 {_26978 _26981 : Type'} (_18963 : _26981) (y : _26978) (f : _26981 -> _26978) (h : _26981) (h1 : y = (f h)) : (term209 _26978 _26981 h y f _18963) = (term213 _26978 _26981 h f _18963).
Proof. exact (EQ_MP (@lem1146981 _26978 _26981 y h f _18963) (@lem1146972 _26978 _26981 _18963 y f h h1)). Qed.
Lemma lem1146983 {_26978 _26981 : Type'} (_18963 : _26981) (x : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h : _26981) (h1 : term163 _26978 _26981 x h t y f) (h2 : y = (f h)) : term213 _26978 _26981 h f _18963.
Proof. exact (EQ_MP (@lem1146982 _26978 _26981 _18963 y f h h2) (@lem1146910 _26978 _26981 _18963 x h t y f h1)). Qed.
Lemma lem1147038 {_26978 _26981 : Type'} (t : list _26981) (f : _26981 -> _26978) (_18964 : _26981) : (term216 _26978 _26981 t f _18964) = (term216 _26978 _26981 t f _18964).
Proof. exact (eq_refl (term216 _26978 _26981 t f _18964)). Qed.
Lemma lem1147039 {_26978 _26981 : Type'} (_18964 : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h1 : term93 _26978 _26981 t y f x) : (term217 _26978 _26981 t f _18964 y) = (term218 _26978 _26981 t _18964 f x).
Proof. exact (MK_COMB (@lem1147038 _26978 _26981 t f _18964) (@lem1146920 _26978 _26981 t y f x h1)). Qed.
Lemma lem1147040 {_26978 _26981 : Type'} (t : list _26981) (x : _26981) (f : _26981 -> _26978) (_18964 : _26981) : (term218 _26978 _26981 t _18964 f x) = (term219 _26978 _26981 t x f _18964).
Proof. exact (eq_refl (term218 _26978 _26981 t _18964 f x)). Qed.
Lemma lem1147041 {_26978 _26981 : Type'} (t : list _26981) (f : _26981 -> _26978) (_18964 : _26981) (y : _26978) : (term220 _26978 _26981 t f _18964 y) = (term220 _26978 _26981 t f _18964 y).
Proof. exact (eq_refl (term220 _26978 _26981 t f _18964 y)). Qed.
Lemma lem1147042 {_26978 _26981 : Type'} (y : _26978) (t : list _26981) (x : _26981) (f : _26981 -> _26978) (_18964 : _26981) : ((term217 _26978 _26981 t f _18964 y) = (term218 _26978 _26981 t _18964 f x)) = ((term217 _26978 _26981 t f _18964 y) = (term219 _26978 _26981 t x f _18964)).
Proof. exact (MK_COMB (@lem1147041 _26978 _26981 t f _18964 y) (@lem1147040 _26978 _26981 t x f _18964)). Qed.
Lemma lem1147043 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (_18964 : _26981) : (term217 _26978 _26981 t f _18964 y) = (term96 _26978 _26981 t y f _18964).
Proof. exact (eq_refl (term217 _26978 _26981 t f _18964 y)). Qed.
Lemma lem1147044 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1147045 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (_18964 : _26981) : (term220 _26978 _26981 t f _18964 y) = (term221 _26978 _26981 t y f _18964).
Proof. exact (MK_COMB (@lem1147044) (@lem1147043 _26978 _26981 t y f _18964)). Qed.
Lemma lem1147046 {_26978 _26981 : Type'} (t : list _26981) (x : _26981) (f : _26981 -> _26978) (_18964 : _26981) : (term219 _26978 _26981 t x f _18964) = (term219 _26978 _26981 t x f _18964).
Proof. exact (eq_refl (term219 _26978 _26981 t x f _18964)). Qed.
Lemma lem1147047 {_26978 _26981 : Type'} (y : _26978) (t : list _26981) (x : _26981) (f : _26981 -> _26978) (_18964 : _26981) : ((term217 _26978 _26981 t f _18964 y) = (term219 _26978 _26981 t x f _18964)) = ((term96 _26978 _26981 t y f _18964) = (term219 _26978 _26981 t x f _18964)).
Proof. exact (MK_COMB (@lem1147045 _26978 _26981 t y f _18964) (@lem1147046 _26978 _26981 t x f _18964)). Qed.
Lemma lem1147048 {_26978 _26981 : Type'} (y : _26978) (t : list _26981) (x : _26981) (f : _26981 -> _26978) (_18964 : _26981) : ((term217 _26978 _26981 t f _18964 y) = (term218 _26978 _26981 t _18964 f x)) = ((term96 _26978 _26981 t y f _18964) = (term219 _26978 _26981 t x f _18964)).
Proof. exact (TRANS (@lem1147042 _26978 _26981 y t x f _18964) (@lem1147047 _26978 _26981 y t x f _18964)). Qed.
Lemma lem1147049 {_26978 _26981 : Type'} (_18964 : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h1 : term93 _26978 _26981 t y f x) : (term96 _26978 _26981 t y f _18964) = (term219 _26978 _26981 t x f _18964).
Proof. exact (EQ_MP (@lem1147048 _26978 _26981 y t x f _18964) (@lem1147039 _26978 _26981 _18964 t y f x h1)). Qed.
Lemma lem1147050 {_26978 _26981 : Type'} (_18964 : _26981) (x : _26981) (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term93 _26978 _26981 t y f x) (h2 : term163 _26978 _26981 x h t y f) : term219 _26978 _26981 t x f _18964.
Proof. exact (EQ_MP (@lem1147049 _26978 _26981 _18964 t y f x h1) (@lem1146932 _26978 _26981 _18964 x h t y f h2)). Qed.
Lemma lem1147065 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : (term222 _26978 _26981 y f) = (term222 _26978 _26981 y f).
Proof. exact (eq_refl (term222 _26978 _26981 y f)). Qed.
Lemma lem1147066 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) (x : _26981) (h : _26981) (h1 : x = h) : (term223 _26978 _26981 y f x) = (term223 _26978 _26981 y f h).
Proof. exact (MK_COMB (@lem1147065 _26978 _26981 y f) (@lem1146944 _26981 x h h1)). Qed.
Lemma lem1147067 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) (h : _26981) : (term223 _26978 _26981 y f h) = (y = (f h)).
Proof. exact (eq_refl (term223 _26978 _26981 y f h)). Qed.
Lemma lem1147068 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term224 _26978 _26981 y f x) = (term224 _26978 _26981 y f x).
Proof. exact (eq_refl (term224 _26978 _26981 y f x)). Qed.
Lemma lem1147069 {_26978 _26981 : Type'} (x : _26981) (y : _26978) (f : _26981 -> _26978) (h : _26981) : ((term223 _26978 _26981 y f x) = (term223 _26978 _26981 y f h)) = ((term223 _26978 _26981 y f x) = (y = (f h))).
Proof. exact (MK_COMB (@lem1147068 _26978 _26981 y f x) (@lem1147067 _26978 _26981 y f h)). Qed.
Lemma lem1147070 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term223 _26978 _26981 y f x) = (y = (f x)).
Proof. exact (eq_refl (term223 _26978 _26981 y f x)). Qed.
Lemma lem1147071 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1147072 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) (x : _26981) : (term224 _26978 _26981 y f x) = (term225 _26978 _26981 y f x).
Proof. exact (MK_COMB (@lem1147071) (@lem1147070 _26978 _26981 y f x)). Qed.
Lemma lem1147073 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) (h : _26981) : (y = (f h)) = (y = (f h)).
Proof. exact (eq_refl (y = (f h))). Qed.
Lemma lem1147074 {_26978 _26981 : Type'} (x : _26981) (y : _26978) (f : _26981 -> _26978) (h : _26981) : ((term223 _26978 _26981 y f x) = (y = (f h))) = ((y = (f x)) = (y = (f h))).
Proof. exact (MK_COMB (@lem1147072 _26978 _26981 y f x) (@lem1147073 _26978 _26981 y f h)). Qed.
Lemma lem1147075 {_26978 _26981 : Type'} (x : _26981) (y : _26978) (f : _26981 -> _26978) (h : _26981) : ((term223 _26978 _26981 y f x) = (term223 _26978 _26981 y f h)) = ((y = (f x)) = (y = (f h))).
Proof. exact (TRANS (@lem1147069 _26978 _26981 x y f h) (@lem1147074 _26978 _26981 x y f h)). Qed.
Lemma lem1147076 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) (x : _26981) (h : _26981) (h1 : x = h) : (y = (f x)) = (y = (f h)).
Proof. exact (EQ_MP (@lem1147075 _26978 _26981 x y f h) (@lem1147066 _26978 _26981 y f x h h1)). Qed.
Lemma lem1147077 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h : _26981) (h1 : term177 _26978 _26981 h t y f x) (h2 : x = h) : y = (f h).
Proof. exact (EQ_MP (@lem1147076 _26978 _26981 y f x h h2) (@lem1146934 _26978 _26981 h t y f x h1)). Qed.
Lemma lem1147091 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h1 : term177 _26978 _26981 h t y f x) : term112 _26978 _26981 y f h.
Proof. exact (proj1 (@lem1146772 _26978 _26981 h t y f x h1)). Qed.
Lemma lem1147120 {_26978 _26981 : Type'} (f : _26981 -> _26978) (h : _26981) : (term226 _26978 _26981 f h) = (term226 _26978 _26981 f h).
Proof. exact (eq_refl (term226 _26978 _26981 f h)). Qed.
Lemma lem1147121 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h : _26981) (h1 : term177 _26978 _26981 h t y f x) (h2 : x = h) : (term227 _26978 _26981 f h y) = (term228 _26978 _26981 f h).
Proof. exact (MK_COMB (@lem1147120 _26978 _26981 f h) (@lem1147077 _26978 _26981 t y f x h h1 h2)). Qed.
Lemma lem1147122 {_26978 _26981 : Type'} (f : _26981 -> _26978) (h : _26981) : (term228 _26978 _26981 f h) = (term229 _26978 _26981 f h).
Proof. exact (eq_refl (term228 _26978 _26981 f h)). Qed.
Lemma lem1147123 {_26978 _26981 : Type'} (f : _26981 -> _26978) (h : _26981) (y : _26978) : (term230 _26978 _26981 f h y) = (term230 _26978 _26981 f h y).
Proof. exact (eq_refl (term230 _26978 _26981 f h y)). Qed.
Lemma lem1147124 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) (h : _26981) : ((term227 _26978 _26981 f h y) = (term228 _26978 _26981 f h)) = ((term227 _26978 _26981 f h y) = (term229 _26978 _26981 f h)).
Proof. exact (MK_COMB (@lem1147123 _26978 _26981 f h y) (@lem1147122 _26978 _26981 f h)). Qed.
Lemma lem1147125 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) (h : _26981) : (term227 _26978 _26981 f h y) = (term112 _26978 _26981 y f h).
Proof. exact (eq_refl (term227 _26978 _26981 f h y)). Qed.
Lemma lem1147126 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1147127 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) (h : _26981) : (term230 _26978 _26981 f h y) = (term231 _26978 _26981 y f h).
Proof. exact (MK_COMB (@lem1147126) (@lem1147125 _26978 _26981 y f h)). Qed.
Lemma lem1147128 {_26978 _26981 : Type'} (f : _26981 -> _26978) (h : _26981) : (term229 _26978 _26981 f h) = (term229 _26978 _26981 f h).
Proof. exact (eq_refl (term229 _26978 _26981 f h)). Qed.
Lemma lem1147129 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) (h : _26981) : ((term227 _26978 _26981 f h y) = (term229 _26978 _26981 f h)) = ((term112 _26978 _26981 y f h) = (term229 _26978 _26981 f h)).
Proof. exact (MK_COMB (@lem1147127 _26978 _26981 y f h) (@lem1147128 _26978 _26981 f h)). Qed.
Lemma lem1147130 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) (h : _26981) : ((term227 _26978 _26981 f h y) = (term228 _26978 _26981 f h)) = ((term112 _26978 _26981 y f h) = (term229 _26978 _26981 f h)).
Proof. exact (TRANS (@lem1147124 _26978 _26981 y f h) (@lem1147129 _26978 _26981 y f h)). Qed.
Lemma lem1147131 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h : _26981) (h1 : term177 _26978 _26981 h t y f x) (h2 : x = h) : (term112 _26978 _26981 y f h) = (term229 _26978 _26981 f h).
Proof. exact (EQ_MP (@lem1147130 _26978 _26981 y f h) (@lem1147121 _26978 _26981 t y f x h h1 h2)). Qed.
Lemma lem1147132 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h : _26981) (h1 : term177 _26978 _26981 h t y f x) (h2 : x = h) : term229 _26978 _26981 f h.
Proof. exact (EQ_MP (@lem1147131 _26978 _26981 t y f x h h1 h2) (@lem1147091 _26978 _26981 h t y f x h1)). Qed.
Lemma lem1147173 {_26978 _26981 : Type'} (t : list _26981) (f : _26981 -> _26978) (_18966 : _26981) : (term216 _26978 _26981 t f _18966) = (term216 _26978 _26981 t f _18966).
Proof. exact (eq_refl (term216 _26978 _26981 t f _18966)). Qed.
Lemma lem1147174 {_26978 _26981 : Type'} (_18966 : _26981) (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h1 : term177 _26978 _26981 h t y f x) : (term217 _26978 _26981 t f _18966 y) = (term218 _26978 _26981 t _18966 f x).
Proof. exact (MK_COMB (@lem1147173 _26978 _26981 t f _18966) (@lem1146946 _26978 _26981 h t y f x h1)). Qed.
Lemma lem1147175 {_26978 _26981 : Type'} (t : list _26981) (x : _26981) (f : _26981 -> _26978) (_18966 : _26981) : (term218 _26978 _26981 t _18966 f x) = (term219 _26978 _26981 t x f _18966).
Proof. exact (eq_refl (term218 _26978 _26981 t _18966 f x)). Qed.
Lemma lem1147176 {_26978 _26981 : Type'} (t : list _26981) (f : _26981 -> _26978) (_18966 : _26981) (y : _26978) : (term220 _26978 _26981 t f _18966 y) = (term220 _26978 _26981 t f _18966 y).
Proof. exact (eq_refl (term220 _26978 _26981 t f _18966 y)). Qed.
Lemma lem1147177 {_26978 _26981 : Type'} (y : _26978) (t : list _26981) (x : _26981) (f : _26981 -> _26978) (_18966 : _26981) : ((term217 _26978 _26981 t f _18966 y) = (term218 _26978 _26981 t _18966 f x)) = ((term217 _26978 _26981 t f _18966 y) = (term219 _26978 _26981 t x f _18966)).
Proof. exact (MK_COMB (@lem1147176 _26978 _26981 t f _18966 y) (@lem1147175 _26978 _26981 t x f _18966)). Qed.
Lemma lem1147178 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (_18966 : _26981) : (term217 _26978 _26981 t f _18966 y) = (term96 _26978 _26981 t y f _18966).
Proof. exact (eq_refl (term217 _26978 _26981 t f _18966 y)). Qed.
Lemma lem1147179 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1147180 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (_18966 : _26981) : (term220 _26978 _26981 t f _18966 y) = (term221 _26978 _26981 t y f _18966).
Proof. exact (MK_COMB (@lem1147179) (@lem1147178 _26978 _26981 t y f _18966)). Qed.
Lemma lem1147181 {_26978 _26981 : Type'} (t : list _26981) (x : _26981) (f : _26981 -> _26978) (_18966 : _26981) : (term219 _26978 _26981 t x f _18966) = (term219 _26978 _26981 t x f _18966).
Proof. exact (eq_refl (term219 _26978 _26981 t x f _18966)). Qed.
Lemma lem1147182 {_26978 _26981 : Type'} (y : _26978) (t : list _26981) (x : _26981) (f : _26981 -> _26978) (_18966 : _26981) : ((term217 _26978 _26981 t f _18966 y) = (term219 _26978 _26981 t x f _18966)) = ((term96 _26978 _26981 t y f _18966) = (term219 _26978 _26981 t x f _18966)).
Proof. exact (MK_COMB (@lem1147180 _26978 _26981 t y f _18966) (@lem1147181 _26978 _26981 t x f _18966)). Qed.
Lemma lem1147183 {_26978 _26981 : Type'} (y : _26978) (t : list _26981) (x : _26981) (f : _26981 -> _26978) (_18966 : _26981) : ((term217 _26978 _26981 t f _18966 y) = (term218 _26978 _26981 t _18966 f x)) = ((term96 _26978 _26981 t y f _18966) = (term219 _26978 _26981 t x f _18966)).
Proof. exact (TRANS (@lem1147177 _26978 _26981 y t x f _18966) (@lem1147182 _26978 _26981 y t x f _18966)). Qed.
Lemma lem1147184 {_26978 _26981 : Type'} (_18966 : _26981) (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h1 : term177 _26978 _26981 h t y f x) : (term96 _26978 _26981 t y f _18966) = (term219 _26978 _26981 t x f _18966).
Proof. exact (EQ_MP (@lem1147183 _26978 _26981 y t x f _18966) (@lem1147174 _26978 _26981 _18966 h t y f x h1)). Qed.
Lemma lem1147185 {_26978 _26981 : Type'} (_18966 : _26981) (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h1 : term177 _26978 _26981 h t y f x) : term219 _26978 _26981 t x f _18966.
Proof. exact (EQ_MP (@lem1147184 _26978 _26981 _18966 h t y f x h1) (@lem1146954 _26978 _26981 _18966 h t y f x h1)). Qed.
Lemma lem1147199 {_26981 : Type'} (x : _26981) (t : list _26981) (h1 : @List.In _26981 x t) : @List.In _26981 x t.
Proof. exact (h1). Qed.
Lemma lem1147234 {_26981 : Type'} (x : _26981) : x = x.
Proof. exact (@lem21386 _26981 x). Qed.
Lemma lem1147235 {_26981 : Type'} (x : _26981) : x = x.
Proof. exact (@lem1147234 _26981 x). Qed.
Lemma lem1147236 {_26981 : Type'} (h : _26981) : h = h.
Proof. exact (@lem1147235 _26981 h). Qed.
Lemma lem1147237 {_26981 : Type'} (h : _26981) : term232 _26981 h.
Proof. exact (fun h0 : term233 _26981 h => @lem1147236 _26981 h). Qed.
Lemma lem1147239 (p : Prop) : (term234 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1147240 {_26981 : Type'} (h : _26981) : (term232 _26981 h) = (h = h).
Proof. exact (@lem1147239 (h = h)). Qed.
Lemma lem1147241 {_26981 : Type'} (h : _26981) : h = h.
Proof. exact (EQ_MP (@lem1147240 _26981 h) (@lem1147237 _26981 h)). Qed.
Lemma lem1147243 {_26978 : Type'} (x : _26978) : x = x.
Proof. exact (@lem21386 _26978 x). Qed.
Lemma lem1147244 {_26978 : Type'} (x : _26978) : x = x.
Proof. exact (@lem1147243 _26978 x). Qed.
Lemma lem1147245 {_26978 _26981 : Type'} (f : _26981 -> _26978) (h : _26981) : (f h) = (f h).
Proof. exact (@lem1147244 _26978 (f h)). Qed.
Lemma lem1147246 {_26978 _26981 : Type'} (f : _26981 -> _26978) (h : _26981) : term235 _26978 _26981 f h.
Proof. exact (fun h0 : term229 _26978 _26981 f h => @lem1147245 _26978 _26981 f h). Qed.
Lemma lem1147248 (p : Prop) : (term234 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1147249 {_26978 _26981 : Type'} (f : _26981 -> _26978) (h : _26981) : (term235 _26978 _26981 f h) = ((f h) = (f h)).
Proof. exact (@lem1147248 ((f h) = (f h))). Qed.
Lemma lem1147250 {_26978 _26981 : Type'} (f : _26981 -> _26978) (h : _26981) : (f h) = (f h).
Proof. exact (EQ_MP (@lem1147249 _26978 _26981 f h) (@lem1147246 _26978 _26981 f h)). Qed.
Lemma lem1147252 (a : Prop) (b : Prop) : (term236 a b) = (term237 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem1147253 {_26978 _26981 : Type'} (h : _26981) (f : _26981 -> _26978) (_18963 : _26981) : (term213 _26978 _26981 h f _18963) = (term238 _26978 _26981 h f _18963).
Proof. exact (@lem1147252 (_18963 = h) ((f h) = (f _18963))). Qed.
Lemma lem1147255 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1147256 {_26978 _26981 : Type'} (h : _26981) (f : _26981 -> _26978) (_18963 : _26981) : (term238 _26978 _26981 h f _18963) = (term239 _26978 _26981 h f _18963).
Proof. exact (@lem1147255 (term240 _26978 _26981 h f _18963)). Qed.
Lemma lem1147257 {_26978 _26981 : Type'} (h : _26981) (f : _26981 -> _26978) (_18963 : _26981) : (term213 _26978 _26981 h f _18963) = (term239 _26978 _26981 h f _18963).
Proof. exact (TRANS (@lem1147253 _26978 _26981 h f _18963) (@lem1147256 _26978 _26981 h f _18963)). Qed.
Lemma lem1147259 {_26978 _26981 : Type'} (f : _26981 -> _26978) (h : _26981) : term241 _26978 _26981 f h.
Proof. exact (conj (@lem1147241 _26981 h) (@lem1147250 _26978 _26981 f h)). Qed.
Lemma lem1147261 {_26978 _26981 : Type'} (_18963 : _26981) (x : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h : _26981) (h1 : term163 _26978 _26981 x h t y f) (h2 : y = (f h)) : term239 _26978 _26981 h f _18963.
Proof. exact (EQ_MP (@lem1147257 _26978 _26981 h f _18963) (@lem1146983 _26978 _26981 _18963 x t y f h h1 h2)). Qed.
Lemma lem1147262 {_26978 _26981 : Type'} (_18963 : _26981) (x : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h : _26981) (h1 : term163 _26978 _26981 x h t y f) (h2 : y = (f h)) : term239 _26978 _26981 h f _18963.
Proof. exact (@lem1147261 _26978 _26981 _18963 x t y f h h1 h2). Qed.
Lemma lem1147263 {_26978 _26981 : Type'} (x : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h : _26981) (h1 : term163 _26978 _26981 x h t y f) (h2 : y = (f h)) : term242 _26978 _26981 f h.
Proof. exact (@lem1147262 _26978 _26981 h x t y f h h1 h2). Qed.
Lemma lem1147266 {_26978 _26981 : Type'} (x : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h : _26981) (h1 : term163 _26978 _26981 x h t y f) (h2 : y = (f h)) : False.
Proof. exact (@lem1147263 _26978 _26981 x t y f h h1 h2 (@lem1147259 _26978 _26981 f h)). Qed.
Lemma lem1147267 {_26978 _26981 : Type'} (x : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h : _26981) (h1 : term163 _26978 _26981 x h t y f) (h2 : y = (f h)) : term243.
Proof. exact (fun h0 : ~ False => @lem1147266 _26978 _26981 x t y f h h1 h2). Qed.
Lemma lem1147269 (p : Prop) : (term234 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1147270 : term243 = False.
Proof. exact (@lem1147269 False). Qed.
Lemma lem1147306 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h1 : term93 _26978 _26981 t y f x) : @List.In _26981 x t.
Proof. exact (proj1 (@lem1146768 _26978 _26981 t y f x h1)). Qed.
Lemma lem1147307 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h1 : term93 _26978 _26981 t y f x) : term244 _26981 x t.
Proof. exact (fun h0 : term204 _26981 x t => @lem1147306 _26978 _26981 t y f x h1). Qed.
Lemma lem1147309 (p : Prop) : (term234 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1147310 {_26981 : Type'} (x : _26981) (t : list _26981) : (term244 _26981 x t) = (@List.In _26981 x t).
Proof. exact (@lem1147309 (@List.In _26981 x t)). Qed.
Lemma lem1147311 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h1 : term93 _26978 _26981 t y f x) : @List.In _26981 x t.
Proof. exact (EQ_MP (@lem1147310 _26981 x t) (@lem1147307 _26978 _26981 t y f x h1)). Qed.
Lemma lem1147313 {_26978 : Type'} (x : _26978) : x = x.
Proof. exact (@lem21386 _26978 x). Qed.
Lemma lem1147314 {_26978 : Type'} (x : _26978) : x = x.
Proof. exact (@lem1147313 _26978 x). Qed.
Lemma lem1147315 {_26978 _26981 : Type'} (f : _26981 -> _26978) (x : _26981) : (f x) = (f x).
Proof. exact (@lem1147314 _26978 (f x)). Qed.
Lemma lem1147316 {_26978 _26981 : Type'} (f : _26981 -> _26978) (x : _26981) : term235 _26978 _26981 f x.
Proof. exact (fun h0 : term229 _26978 _26981 f x => @lem1147315 _26978 _26981 f x). Qed.
Lemma lem1147318 (p : Prop) : (term234 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1147319 {_26978 _26981 : Type'} (f : _26981 -> _26978) (x : _26981) : (term235 _26978 _26981 f x) = ((f x) = (f x)).
Proof. exact (@lem1147318 ((f x) = (f x))). Qed.
Lemma lem1147320 {_26978 _26981 : Type'} (f : _26981 -> _26978) (x : _26981) : (f x) = (f x).
Proof. exact (EQ_MP (@lem1147319 _26978 _26981 f x) (@lem1147316 _26978 _26981 f x)). Qed.
Lemma lem1147322 (a : Prop) (b : Prop) : (term236 a b) = (term237 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem1147323 {_26978 _26981 : Type'} (t : list _26981) (x : _26981) (f : _26981 -> _26978) (_18964 : _26981) : (term219 _26978 _26981 t x f _18964) = (term245 _26978 _26981 t x f _18964).
Proof. exact (@lem1147322 (@List.In _26981 _18964 t) ((f x) = (f _18964))). Qed.
Lemma lem1147325 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1147326 {_26978 _26981 : Type'} (t : list _26981) (x : _26981) (f : _26981 -> _26978) (_18964 : _26981) : (term245 _26978 _26981 t x f _18964) = (term246 _26978 _26981 t x f _18964).
Proof. exact (@lem1147325 (term247 _26978 _26981 t x f _18964)). Qed.
Lemma lem1147327 {_26978 _26981 : Type'} (t : list _26981) (x : _26981) (f : _26981 -> _26978) (_18964 : _26981) : (term219 _26978 _26981 t x f _18964) = (term246 _26978 _26981 t x f _18964).
Proof. exact (TRANS (@lem1147323 _26978 _26981 t x f _18964) (@lem1147326 _26978 _26981 t x f _18964)). Qed.
Lemma lem1147329 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h1 : term93 _26978 _26981 t y f x) : term248 _26978 _26981 t f x.
Proof. exact (conj (@lem1147311 _26978 _26981 t y f x h1) (@lem1147320 _26978 _26981 f x)). Qed.
Lemma lem1147331 {_26978 _26981 : Type'} (_18964 : _26981) (x : _26981) (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term93 _26978 _26981 t y f x) (h2 : term163 _26978 _26981 x h t y f) : term246 _26978 _26981 t x f _18964.
Proof. exact (EQ_MP (@lem1147327 _26978 _26981 t x f _18964) (@lem1147050 _26978 _26981 _18964 x h t y f h1 h2)). Qed.
Lemma lem1147332 {_26978 _26981 : Type'} (_18964 : _26981) (x : _26981) (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term93 _26978 _26981 t y f x) (h2 : term163 _26978 _26981 x h t y f) : term246 _26978 _26981 t x f _18964.
Proof. exact (@lem1147331 _26978 _26981 _18964 x h t y f h1 h2). Qed.
Lemma lem1147333 {_26978 _26981 : Type'} (x : _26981) (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term93 _26978 _26981 t y f x) (h2 : term163 _26978 _26981 x h t y f) : term249 _26978 _26981 t f x.
Proof. exact (@lem1147332 _26978 _26981 x x h t y f h1 h2). Qed.
Lemma lem1147336 {_26978 _26981 : Type'} (x : _26981) (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term93 _26978 _26981 t y f x) (h2 : term163 _26978 _26981 x h t y f) : False.
Proof. exact (@lem1147333 _26978 _26981 x h t y f h1 h2 (@lem1147329 _26978 _26981 t y f x h1)). Qed.
Lemma lem1147337 {_26978 _26981 : Type'} (x : _26981) (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term93 _26978 _26981 t y f x) (h2 : term163 _26978 _26981 x h t y f) : term243.
Proof. exact (fun h0 : ~ False => @lem1147336 _26978 _26981 x h t y f h1 h2). Qed.
Lemma lem1147339 (p : Prop) : (term234 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1147340 : term243 = False.
Proof. exact (@lem1147339 False). Qed.
Lemma lem1147376 {_26978 : Type'} (x : _26978) : x = x.
Proof. exact (@lem21386 _26978 x). Qed.
Lemma lem1147377 {_26978 : Type'} (x : _26978) : x = x.
Proof. exact (@lem1147376 _26978 x). Qed.
Lemma lem1147378 {_26978 _26981 : Type'} (f : _26981 -> _26978) (h : _26981) : (f h) = (f h).
Proof. exact (@lem1147377 _26978 (f h)). Qed.
Lemma lem1147379 {_26978 _26981 : Type'} (f : _26981 -> _26978) (h : _26981) : term235 _26978 _26981 f h.
Proof. exact (fun h0 : term229 _26978 _26981 f h => @lem1147378 _26978 _26981 f h). Qed.
Lemma lem1147381 (p : Prop) : (term234 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1147382 {_26978 _26981 : Type'} (f : _26981 -> _26978) (h : _26981) : (term235 _26978 _26981 f h) = ((f h) = (f h)).
Proof. exact (@lem1147381 ((f h) = (f h))). Qed.
Lemma lem1147383 {_26978 _26981 : Type'} (f : _26981 -> _26978) (h : _26981) : (f h) = (f h).
Proof. exact (EQ_MP (@lem1147382 _26978 _26981 f h) (@lem1147379 _26978 _26981 f h)). Qed.
Lemma lem1147386 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1147388 {_26978 _26981 : Type'} (f : _26981 -> _26978) (h : _26981) : (term229 _26978 _26981 f h) = (term250 _26978 _26981 f h).
Proof. exact (@lem1147386 ((f h) = (f h))). Qed.
Lemma lem1147391 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h : _26981) (h1 : term177 _26978 _26981 h t y f x) (h2 : x = h) : term250 _26978 _26981 f h.
Proof. exact (EQ_MP (@lem1147388 _26978 _26981 f h) (@lem1147132 _26978 _26981 t y f x h h1 h2)). Qed.
Lemma lem1147394 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h : _26981) (h1 : term177 _26978 _26981 h t y f x) (h2 : x = h) : False.
Proof. exact (@lem1147391 _26978 _26981 t y f x h h1 h2 (@lem1147383 _26978 _26981 f h)). Qed.
Lemma lem1147395 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h : _26981) (h1 : term177 _26978 _26981 h t y f x) (h2 : x = h) : term243.
Proof. exact (fun h0 : ~ False => @lem1147394 _26978 _26981 t y f x h h1 h2). Qed.
Lemma lem1147397 (p : Prop) : (term234 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1147398 : term243 = False.
Proof. exact (@lem1147397 False). Qed.
Lemma lem1147434 {_26981 : Type'} (x : _26981) (t : list _26981) (h1 : @List.In _26981 x t) : @List.In _26981 x t.
Proof. exact (h1). Qed.
Lemma lem1147435 {_26981 : Type'} (x : _26981) (t : list _26981) (h1 : @List.In _26981 x t) : term244 _26981 x t.
Proof. exact (fun h0 : term204 _26981 x t => @lem1147434 _26981 x t h1). Qed.
Lemma lem1147437 (p : Prop) : (term234 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1147438 {_26981 : Type'} (x : _26981) (t : list _26981) : (term244 _26981 x t) = (@List.In _26981 x t).
Proof. exact (@lem1147437 (@List.In _26981 x t)). Qed.
Lemma lem1147439 {_26981 : Type'} (x : _26981) (t : list _26981) (h1 : @List.In _26981 x t) : @List.In _26981 x t.
Proof. exact (EQ_MP (@lem1147438 _26981 x t) (@lem1147435 _26981 x t h1)). Qed.
Lemma lem1147441 {_26978 : Type'} (x : _26978) : x = x.
Proof. exact (@lem21386 _26978 x). Qed.
Lemma lem1147442 {_26978 : Type'} (x : _26978) : x = x.
Proof. exact (@lem1147441 _26978 x). Qed.
Lemma lem1147443 {_26978 _26981 : Type'} (f : _26981 -> _26978) (x : _26981) : (f x) = (f x).
Proof. exact (@lem1147442 _26978 (f x)). Qed.
Lemma lem1147444 {_26978 _26981 : Type'} (f : _26981 -> _26978) (x : _26981) : term235 _26978 _26981 f x.
Proof. exact (fun h0 : term229 _26978 _26981 f x => @lem1147443 _26978 _26981 f x). Qed.
Lemma lem1147446 (p : Prop) : (term234 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1147447 {_26978 _26981 : Type'} (f : _26981 -> _26978) (x : _26981) : (term235 _26978 _26981 f x) = ((f x) = (f x)).
Proof. exact (@lem1147446 ((f x) = (f x))). Qed.
Lemma lem1147448 {_26978 _26981 : Type'} (f : _26981 -> _26978) (x : _26981) : (f x) = (f x).
Proof. exact (EQ_MP (@lem1147447 _26978 _26981 f x) (@lem1147444 _26978 _26981 f x)). Qed.
Lemma lem1147450 (a : Prop) (b : Prop) : (term236 a b) = (term237 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem1147451 {_26978 _26981 : Type'} (t : list _26981) (x : _26981) (f : _26981 -> _26978) (_18966 : _26981) : (term219 _26978 _26981 t x f _18966) = (term245 _26978 _26981 t x f _18966).
Proof. exact (@lem1147450 (@List.In _26981 _18966 t) ((f x) = (f _18966))). Qed.
Lemma lem1147453 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1147454 {_26978 _26981 : Type'} (t : list _26981) (x : _26981) (f : _26981 -> _26978) (_18966 : _26981) : (term245 _26978 _26981 t x f _18966) = (term246 _26978 _26981 t x f _18966).
Proof. exact (@lem1147453 (term247 _26978 _26981 t x f _18966)). Qed.
Lemma lem1147455 {_26978 _26981 : Type'} (t : list _26981) (x : _26981) (f : _26981 -> _26978) (_18966 : _26981) : (term219 _26978 _26981 t x f _18966) = (term246 _26978 _26981 t x f _18966).
Proof. exact (TRANS (@lem1147451 _26978 _26981 t x f _18966) (@lem1147454 _26978 _26981 t x f _18966)). Qed.
Lemma lem1147457 {_26978 _26981 : Type'} (f : _26981 -> _26978) (x : _26981) (t : list _26981) (h1 : @List.In _26981 x t) : term248 _26978 _26981 t f x.
Proof. exact (conj (@lem1147439 _26981 x t h1) (@lem1147448 _26978 _26981 f x)). Qed.
Lemma lem1147459 {_26978 _26981 : Type'} (_18966 : _26981) (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h1 : term177 _26978 _26981 h t y f x) : term246 _26978 _26981 t x f _18966.
Proof. exact (EQ_MP (@lem1147455 _26978 _26981 t x f _18966) (@lem1147185 _26978 _26981 _18966 h t y f x h1)). Qed.
Lemma lem1147460 {_26978 _26981 : Type'} (_18966 : _26981) (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h1 : term177 _26978 _26981 h t y f x) : term246 _26978 _26981 t x f _18966.
Proof. exact (@lem1147459 _26978 _26981 _18966 h t y f x h1). Qed.
Lemma lem1147461 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h1 : term177 _26978 _26981 h t y f x) : term249 _26978 _26981 t f x.
Proof. exact (@lem1147460 _26978 _26981 x h t y f x h1). Qed.
Lemma lem1147464 {_26978 _26981 : Type'} (h : _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (t : list _26981) (h1 : term177 _26978 _26981 h t y f x) (h2 : @List.In _26981 x t) : False.
Proof. exact (@lem1147461 _26978 _26981 h t y f x h1 (@lem1147457 _26978 _26981 f x t h2)). Qed.
Lemma lem1147465 {_26978 _26981 : Type'} (h : _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (t : list _26981) (h1 : term177 _26978 _26981 h t y f x) (h2 : @List.In _26981 x t) : term243.
Proof. exact (fun h0 : ~ False => @lem1147464 _26978 _26981 h y f x t h1 h2). Qed.
Lemma lem1147467 (p : Prop) : (term234 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1147468 : term243 = False.
Proof. exact (@lem1147467 False). Qed.
Lemma lem1147469 {_26978 _26981 : Type'} (h : _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (t : list _26981) (h1 : term177 _26978 _26981 h t y f x) (h2 : @List.In _26981 x t) : False.
Proof. exact (EQ_MP (@lem1147468) (@lem1147465 _26978 _26981 h y f x t h1 h2)). Qed.
Lemma lem1147470 {_26978 _26981 : Type'} (h : _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (t : list _26981) (h1 : term177 _26978 _26981 h t y f x) (h2 : @List.In _26981 x t) : (@List.In _26981 x t) = False.
Proof. exact (prop_ext (fun h3 : @List.In _26981 x t => @lem1147469 _26978 _26981 h y f x t h1 h2) (fun h3 : False => @lem1147199 _26981 x t h2)). Qed.
Lemma lem1147472 {_26978 _26981 : Type'} (h : _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (t : list _26981) (h1 : term177 _26978 _26981 h t y f x) (h2 : @List.In _26981 x t) : False.
Proof. exact (EQ_MP (@lem1147470 _26978 _26981 h y f x t h1 h2) (@lem1147199 _26981 x t h2)). Qed.
Lemma lem1147474 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h : _26981) (h1 : term177 _26978 _26981 h t y f x) (h2 : x = h) : False.
Proof. exact (EQ_MP (@lem1147398) (@lem1147395 _26978 _26981 t y f x h h1 h2)). Qed.
Lemma lem1147475 {_26978 _26981 : Type'} (x : _26981) (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term93 _26978 _26981 t y f x) (h2 : term163 _26978 _26981 x h t y f) : False.
Proof. exact (EQ_MP (@lem1147340) (@lem1147337 _26978 _26981 x h t y f h1 h2)). Qed.
Lemma lem1147476 {_26978 _26981 : Type'} (x : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h : _26981) (h1 : term163 _26978 _26981 x h t y f) (h2 : y = (f h)) : False.
Proof. exact (EQ_MP (@lem1147270) (@lem1147267 _26978 _26981 x t y f h h1 h2)). Qed.
Lemma lem1147477 {_26978 _26981 : Type'} (h : _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (t : list _26981) (h1 : term177 _26978 _26981 h t y f x) (h2 : @List.In _26981 x t) : (@List.In _26981 x t) = False.
Proof. exact (prop_ext (fun h3 : @List.In _26981 x t => @lem1147472 _26978 _26981 h y f x t h1 h2) (fun h3 : False => @lem1146956 _26981 x t h2)). Qed.
Lemma lem1147478 {_26978 _26981 : Type'} (h : _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (t : list _26981) (h1 : term177 _26978 _26981 h t y f x) (h2 : @List.In _26981 x t) : False.
Proof. exact (EQ_MP (@lem1147477 _26978 _26981 h y f x t h1 h2) (@lem1146956 _26981 x t h2)). Qed.
Lemma lem1147479 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h : _26981) (h1 : term177 _26978 _26981 h t y f x) (h2 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h3 : x = h => @lem1147474 _26978 _26981 t y f x h h1 h2) (fun h3 : False => @lem1146944 _26981 x h h2)). Qed.
Lemma lem1147480 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h : _26981) (h1 : term177 _26978 _26981 h t y f x) (h2 : x = h) : False.
Proof. exact (EQ_MP (@lem1147479 _26978 _26981 t y f x h h1 h2) (@lem1146944 _26981 x h h2)). Qed.
Lemma lem1147481 {_26978 _26981 : Type'} (x : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h : _26981) (h1 : term163 _26978 _26981 x h t y f) (h2 : y = (f h)) : (y = (f h)) = False.
Proof. exact (prop_ext (fun h3 : y = (f h) => @lem1147476 _26978 _26981 x t y f h h1 h2) (fun h3 : False => @lem1146904 _26978 _26981 y f h h2)). Qed.
Lemma lem1147482 {_26978 _26981 : Type'} (x : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h : _26981) (h1 : term163 _26978 _26981 x h t y f) (h2 : y = (f h)) : False.
Proof. exact (EQ_MP (@lem1147481 _26978 _26981 x t y f h h1 h2) (@lem1146904 _26978 _26981 y f h h2)). Qed.
Lemma lem1147483 {_26978 _26981 : Type'} (h : _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (t : list _26981) (h1 : term177 _26978 _26981 h t y f x) (h2 : @List.In _26981 x t) : (@List.In _26981 x t) = False.
Proof. exact (prop_ext (fun h3 : @List.In _26981 x t => @lem1147478 _26978 _26981 h y f x t h1 h2) (fun h3 : False => @lem1146886 _26981 x t h2)). Qed.
Lemma lem1147484 {_26978 _26981 : Type'} (h : _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (t : list _26981) (h1 : term177 _26978 _26981 h t y f x) (h2 : @List.In _26981 x t) : False.
Proof. exact (EQ_MP (@lem1147483 _26978 _26981 h y f x t h1 h2) (@lem1146886 _26981 x t h2)). Qed.
Lemma lem1147485 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h : _26981) (h1 : term177 _26978 _26981 h t y f x) (h2 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h3 : x = h => @lem1147480 _26978 _26981 t y f x h h1 h2) (fun h3 : False => @lem1146861 _26981 x h h2)). Qed.
Lemma lem1147486 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h : _26981) (h1 : term177 _26978 _26981 h t y f x) (h2 : x = h) : False.
Proof. exact (EQ_MP (@lem1147485 _26978 _26981 t y f x h h1 h2) (@lem1146861 _26981 x h h2)). Qed.
Lemma lem1147487 {_26978 _26981 : Type'} (x : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h : _26981) (h1 : term163 _26978 _26981 x h t y f) (h2 : y = (f h)) : (y = (f h)) = False.
Proof. exact (prop_ext (fun h3 : y = (f h) => @lem1147482 _26978 _26981 x t y f h h1 h2) (fun h3 : False => @lem1146805 _26978 _26981 y f h h2)). Qed.
Lemma lem1147488 {_26978 _26981 : Type'} (x : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h : _26981) (h1 : term163 _26978 _26981 x h t y f) (h2 : y = (f h)) : False.
Proof. exact (EQ_MP (@lem1147487 _26978 _26981 x t y f h h1 h2) (@lem1146805 _26978 _26981 y f h h2)). Qed.
Lemma lem1147489 {_26978 _26981 : Type'} (h : _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (t : list _26981) (h1 : term177 _26978 _26981 h t y f x) (h2 : @List.In _26981 x t) : (@List.In _26981 x t) = False.
Proof. exact (prop_ext (fun h3 : @List.In _26981 x t => @lem1147484 _26978 _26981 h y f x t h1 h2) (fun h3 : False => @lem1146886 _26981 x t h2)). Qed.
Lemma lem1147490 {_26978 _26981 : Type'} (h : _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (t : list _26981) (h1 : term177 _26978 _26981 h t y f x) (h2 : @List.In _26981 x t) : False.
Proof. exact (EQ_MP (@lem1147489 _26978 _26981 h y f x t h1 h2) (@lem1146886 _26981 x t h2)). Qed.
Lemma lem1147491 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h : _26981) (h1 : term177 _26978 _26981 h t y f x) (h2 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h3 : x = h => @lem1147486 _26978 _26981 t y f x h h1 h2) (fun h3 : False => @lem1146861 _26981 x h h2)). Qed.
Lemma lem1147492 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h : _26981) (h1 : term177 _26978 _26981 h t y f x) (h2 : x = h) : False.
Proof. exact (EQ_MP (@lem1147491 _26978 _26981 t y f x h h1 h2) (@lem1146861 _26981 x h h2)). Qed.
Lemma lem1147493 {_26978 _26981 : Type'} (x : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h : _26981) (h1 : term163 _26978 _26981 x h t y f) (h2 : y = (f h)) : (y = (f h)) = False.
Proof. exact (prop_ext (fun h3 : y = (f h) => @lem1147488 _26978 _26981 x t y f h h1 h2) (fun h3 : False => @lem1146805 _26978 _26981 y f h h2)). Qed.
Lemma lem1147494 {_26978 _26981 : Type'} (x : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h : _26981) (h1 : term163 _26978 _26981 x h t y f) (h2 : y = (f h)) : False.
Proof. exact (EQ_MP (@lem1147493 _26978 _26981 x t y f h h1 h2) (@lem1146805 _26978 _26981 y f h h2)). Qed.
Lemma lem1147495 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h1 : term177 _26978 _26981 h t y f x) : False.
Proof. exact (or_elim (@lem1146774 _26978 _26981 h t y f x h1) (fun h0 : x = h => @lem1147492 _26978 _26981 t y f x h h1 h0) (fun h0 : @List.In _26981 x t => @lem1147490 _26978 _26981 h y f x t h1 h0)). Qed.
Lemma lem1147496 {_26978 _26981 : Type'} (x : _26981) (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term163 _26978 _26981 x h t y f) : False.
Proof. exact (or_elim (@lem1146766 _26978 _26981 x h t y f h1) (fun h0 : y = (f h) => @lem1147494 _26978 _26981 x t y f h h1 h0) (fun h0 : term93 _26978 _26981 t y f x => @lem1147475 _26978 _26981 x h t y f h0 h1)). Qed.
Lemma lem1147497 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h1 : term198 _26978 _26981 h t y f x) : False.
Proof. exact (or_elim (@lem1146762 _26978 _26981 h t y f x h1) (fun h0 : term163 _26978 _26981 x h t y f => @lem1147496 _26978 _26981 x h t y f h0) (fun h0 : term177 _26978 _26981 h t y f x => @lem1147495 _26978 _26981 h t y f x h0)). Qed.
Lemma lem1147498 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h1 : term198 _26978 _26981 h t y f x) : (term198 _26978 _26981 h t y f x) = False.
Proof. exact (prop_ext (fun h2 : term198 _26978 _26981 h t y f x => @lem1147497 _26978 _26981 h t y f x h1) (fun h2 : False => @lem1146762 _26978 _26981 h t y f x h1)). Qed.
Lemma lem1147499 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (x : _26981) (h1 : term198 _26978 _26981 h t y f x) : False.
Proof. exact (EQ_MP (@lem1147498 _26978 _26981 h t y f x h1) (@lem1146762 _26978 _26981 h t y f x h1)). Qed.
Lemma lem1147500 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term71 _26978 _26981 h t y f) : False.
Proof. exact (ex_elim (@lem1146637 _26978 _26981 h t y f h1) (fun x : _26981 => fun h0 : term200 _26978 _26981 h t y f x => @lem1147499 _26978 _26981 h t y f x h0)). Qed.
Lemma lem1147501 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term71 _26978 _26981 h t y f) : (term71 _26978 _26981 h t y f) = False.
Proof. exact (prop_ext (fun h2 : term71 _26978 _26981 h t y f => @lem1147500 _26978 _26981 h t y f h1) (fun h2 : False => @lem1146260 _26978 _26981 h t y f h1)). Qed.
Lemma lem1147502 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term71 _26978 _26981 h t y f) : False.
Proof. exact (EQ_MP (@lem1147501 _26978 _26981 h t y f h1) (@lem1146260 _26978 _26981 h t y f h1)). Qed.
Lemma lem1147503 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : term70 _26978 _26981 h t y f.
Proof. exact (fun h0 : term71 _26978 _26981 h t y f => @lem1147502 _26978 _26981 h t y f h0). Qed.
Lemma lem1147504 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term59 _26978 _26981 h t y f) = (term68 _26978 _26981 h t y f).
Proof. exact (EQ_MP (@lem1146259 _26978 _26981 h t y f) (@lem1147503 _26978 _26981 h t y f)). Qed.
Lemma lem1147509 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) : term80 _26978 _26981 t y f.
Proof. exact (fun h : _26981 => @lem1147504 _26978 _26981 h t y f). Qed.
Lemma lem1147514 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : term84 _26978 _26981 y f.
Proof. exact (fun t : list _26981 => @lem1147509 _26978 _26981 t y f). Qed.
Lemma lem1147519 {_26978 _26981 : Type'} (f : _26981 -> _26978) : term88 _26978 _26981 f.
Proof. exact (fun y : _26978 => @lem1147514 _26978 _26981 y f). Qed.
Lemma lem1147524 {_26978 _26981 : Type'} : term92 _26978 _26981.
Proof. exact (fun f : _26981 -> _26978 => @lem1147519 _26978 _26981 f). Qed.
Lemma lem1147525 {_26978 _26981 : Type'} : term91 _26978 _26981.
Proof. exact (EQ_MP (@lem1146255 _26978 _26981) (@lem1147524 _26978 _26981)). Qed.
Lemma lem1147526 {_26978 _26981 : Type'} (f : _26981 -> _26978) : term251 _26978 _26981 f.
Proof. exact (@lem1147525 _26978 _26981 f). Qed.
Lemma lem1147527 {_26978 _26981 : Type'} (f : _26981 -> _26978) : (term251 _26978 _26981 f) = (term87 _26978 _26981 f).
Proof. exact (eq_refl (term251 _26978 _26981 f)). Qed.
Lemma lem1147528 {_26978 _26981 : Type'} (f : _26981 -> _26978) : term87 _26978 _26981 f.
Proof. exact (EQ_MP (@lem1147527 _26978 _26981 f) (@lem1147526 _26978 _26981 f)). Qed.
Lemma lem1147529 {_26978 _26981 : Type'} (f : _26981 -> _26978) (y : _26978) : term252 _26978 _26981 f y.
Proof. exact (@lem1147528 _26978 _26981 f y). Qed.
Lemma lem1147530 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : (term252 _26978 _26981 f y) = (term83 _26978 _26981 y f).
Proof. exact (eq_refl (term252 _26978 _26981 f y)). Qed.
Lemma lem1147531 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : term83 _26978 _26981 y f.
Proof. exact (EQ_MP (@lem1147530 _26978 _26981 y f) (@lem1147529 _26978 _26981 f y)). Qed.
Lemma lem1147532 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) (t : list _26981) : term253 _26978 _26981 y f t.
Proof. exact (@lem1147531 _26978 _26981 y f t). Qed.
Lemma lem1147533 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term253 _26978 _26981 y f t) = (term79 _26978 _26981 t y f).
Proof. exact (eq_refl (term253 _26978 _26981 y f t)). Qed.
Lemma lem1147534 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) : term79 _26978 _26981 t y f.
Proof. exact (EQ_MP (@lem1147533 _26978 _26981 t y f) (@lem1147532 _26978 _26981 y f t)). Qed.
Lemma lem1147535 {_26978 _26981 : Type'} (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h : _26981) : term254 _26978 _26981 t y f h.
Proof. exact (@lem1147534 _26978 _26981 t y f h). Qed.
Lemma lem1147536 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term254 _26978 _26981 t y f h) = (term70 _26978 _26981 h t y f).
Proof. exact (eq_refl (term254 _26978 _26981 t y f h)). Qed.
Lemma lem1147537 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : term70 _26978 _26981 h t y f.
Proof. exact (EQ_MP (@lem1147536 _26978 _26981 h t y f) (@lem1147535 _26978 _26981 t y f h)). Qed.
Lemma lem1147539 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : term70 _26978 _26981 h t y f.
Proof. exact (@lem1146009 _26978 _26981 h t y f (@lem1147537 _26978 _26981 h t y f)). Qed.
Lemma lem1147540 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term71 _26978 _26981 h t y f) : False.
Proof. exact (@lem1147539 _26978 _26981 h t y f (@lem1145993 _26978 _26981 h t y f h1)). Qed.
Lemma lem1147541 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term71 _26978 _26981 h t y f) : (term71 _26978 _26981 h t y f) = False.
Proof. exact (prop_ext (fun h2 : term71 _26978 _26981 h t y f => @lem1147540 _26978 _26981 h t y f h1) (fun h2 : False => @lem1145993 _26978 _26981 h t y f h1)). Qed.
Lemma lem1147542 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : term71 _26978 _26981 h t y f) : False.
Proof. exact (EQ_MP (@lem1147541 _26978 _26981 h t y f h1) (@lem1145993 _26978 _26981 h t y f h1)). Qed.
Lemma lem1147543 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : term70 _26978 _26981 h t y f.
Proof. exact (fun h0 : term71 _26978 _26981 h t y f => @lem1147542 _26978 _26981 h t y f h0). Qed.
Lemma lem1147544 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : (term59 _26978 _26981 h t y f) = (term68 _26978 _26981 h t y f).
Proof. exact (EQ_MP (@lem1145992 _26978 _26981 h t y f) (@lem1147543 _26978 _26981 h t y f)). Qed.
Lemma lem1147545 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) (h1 : (term9 _26978 _26981 y f t) = (term10 _26978 _26981 t y f)) : (term14 _26978 _26981 y f h t) = (term15 _26978 _26981 h t y f).
Proof. exact (EQ_MP (@lem1145988 _26978 _26981 h t y f h1) (@lem1147544 _26978 _26981 h t y f)). Qed.
Lemma lem1147546 {_26978 _26981 : Type'} (h : _26981) (t : list _26981) (y : _26978) (f : _26981 -> _26978) : term17 _26978 _26981 h t y f.
Proof. exact (fun h0 : (term9 _26978 _26981 y f t) = (term10 _26978 _26981 t y f) => @lem1147545 _26978 _26981 h t y f h0). Qed.
Lemma lem1147551 {_26978 _26981 : Type'} (h : _26981) (y : _26978) (f : _26981 -> _26978) : term21 _26978 _26981 h y f.
Proof. exact (fun t : list _26981 => @lem1147546 _26978 _26981 h t y f). Qed.
Lemma lem1147556 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : term25 _26978 _26981 y f.
Proof. exact (fun h : _26981 => @lem1147551 _26978 _26981 h y f). Qed.
Lemma lem1147557 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : term27 _26978 _26981 y f.
Proof. exact (conj (@lem1145907 _26978 _26981 y f) (@lem1147556 _26978 _26981 y f)). Qed.
Lemma lem1147558 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : term32 _26978 _26981 y f.
Proof. exact (@lem1145839 _26978 _26981 y f (@lem1147557 _26978 _26981 y f)). Qed.
Lemma lem1147563 {_26978 _26981 : Type'} (f : _26981 -> _26978) : term255 _26978 _26981 f.
Proof. exact (fun y : _26978 => @lem1147558 _26978 _26981 y f). Qed.
Lemma lem1147568 {_26978 _26981 : Type'} : term256 _26978 _26981.
Proof. exact (fun f : _26981 -> _26978 => @lem1147563 _26978 _26981 f). Qed.
