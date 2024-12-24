Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MAP2_term_abbrevs.
Require Import thm0_spec.
Require Import thm1094865_spec.
Require Import thm1094866_spec.
Require Import thm1095388_spec.
Require Import thm1095389_spec.
Require Import thm1105052_spec.
Require Import thm1105053_spec.
Require Import thm1105064_spec.
Require Import thm1105065_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1105075 {_25498 _25501 _25508 : Type'} (f : type1475 _25498 _25501 _25508) (l : list _25508) : (@MAP2 _25498 _25501 _25508 f (@nil _25501) l) = (@nil _25498).
Proof. exact (EQ_MP (@lem1105053 _25498 _25501 _25508 f l) (@lem1105052 _25498 _25501 _25508 f l)). Qed.
Lemma lem1105076 {_25542 _25543 _25549 : Type'} (f : type1469 _25542 _25543 _25549) (l : list _25542) : (@MAP2 _25549 _25543 _25542 f (@nil _25543) l) = (@nil _25549).
Proof. exact (@lem1105075 _25549 _25543 _25542 f l). Qed.
Lemma lem1105077 {_25542 _25543 _25549 : Type'} (f : type1469 _25542 _25543 _25549) : (@MAP2 _25549 _25543 _25542 f (@nil _25543) (@nil _25542)) = (@nil _25549).
Proof. exact (@lem1105076 _25542 _25543 _25549 f (@nil _25542)). Qed.
Lemma lem1105078 {_25549 : Type'} : (@eq (list _25549)) = (@eq (list _25549)).
Proof. exact (eq_refl (@eq (list _25549))). Qed.
Lemma lem1105079 {_25542 _25543 _25549 : Type'} (f : type1469 _25542 _25543 _25549) : (term0 _25542 _25543 _25549 f) = (@eq (list _25549) (@nil _25549)).
Proof. exact (MK_COMB (@lem1105078 _25549) (@lem1105077 _25542 _25543 _25549 f)). Qed.
Lemma lem1105080 {_25549 : Type'} : (@nil _25549) = (@nil _25549).
Proof. exact (eq_refl (@nil _25549)). Qed.
Lemma lem1105081 {_25542 _25543 _25549 : Type'} (f : type1469 _25542 _25543 _25549) : ((@MAP2 _25549 _25543 _25542 f (@nil _25543) (@nil _25542)) = (@nil _25549)) = ((@nil _25549) = (@nil _25549)).
Proof. exact (MK_COMB (@lem1105079 _25542 _25543 _25549 f) (@lem1105080 _25549)). Qed.
Lemma lem1105083 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1105084 {_25549 : Type'} (x : list _25549) : (x = x) = True.
Proof. exact (@lem1105083 (list _25549) x). Qed.
Lemma lem1105085 {_25549 : Type'} : ((@nil _25549) = (@nil _25549)) = True.
Proof. exact (@lem1105084 _25549 (@nil _25549)). Qed.
Lemma lem1105086 {_25542 _25543 _25549 : Type'} (f : type1469 _25542 _25543 _25549) : ((@MAP2 _25549 _25543 _25542 f (@nil _25543) (@nil _25542)) = (@nil _25549)) = True.
Proof. exact (TRANS (@lem1105081 _25542 _25543 _25549 f) (@lem1105085 _25549)). Qed.
Lemma lem1105087 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1105088 {_25542 _25543 _25549 : Type'} (f : type1469 _25542 _25543 _25549) : (term1 _25542 _25543 _25549 f) = (and True).
Proof. exact (MK_COMB (@lem1105087) (@lem1105086 _25542 _25543 _25549 f)). Qed.
Lemma lem1105092 {_25498 _25501 _25508 : Type'} (h1' : _25501) (f : type1475 _25498 _25501 _25508) (t1 : list _25501) (l : list _25508) : (term2 _25498 _25501 _25508 f h1' t1 l) = (term3 _25498 _25501 _25508 h1' f t1 l).
Proof. exact (EQ_MP (@lem1105065 _25498 _25501 _25508 h1' f t1 l) (@lem1105064 _25498 _25501 _25508 h1' f t1 l)). Qed.
Lemma lem1105093 {_25542 _25543 _25549 : Type'} (h1' : _25543) (f : type1469 _25542 _25543 _25549) (t1 : list _25543) (l : list _25542) : (term4 _25542 _25543 _25549 f h1' t1 l) = (term5 _25542 _25543 _25549 h1' f t1 l).
Proof. exact (@lem1105092 _25549 _25543 _25542 h1' f t1 l). Qed.
Lemma lem1105094 {_25542 _25543 _25549 : Type'} (h1' : _25543) (f : type1469 _25542 _25543 _25549) (t1 : list _25543) (h2' : _25542) (t2 : list _25542) : (term6 _25542 _25543 _25549 f h1' t1 h2' t2) = (term7 _25542 _25543 _25549 h1' f t1 h2' t2).
Proof. exact (@lem1105093 _25542 _25543 _25549 h1' f t1 (@cons _25542 h2' t2)). Qed.
Lemma lem1105096 {A : Type'} (t : list A) (h : A) : (term8 A h t) = h.
Proof. exact (EQ_MP (@lem1094866 A t h) (@lem1094865 A t h)). Qed.
Lemma lem1105097 {_25542 : Type'} (t : list _25542) (h : _25542) : (term8 _25542 h t) = h.
Proof. exact (@lem1105096 _25542 t h). Qed.
Lemma lem1105098 {_25542 : Type'} (t2 : list _25542) (h2' : _25542) : (term8 _25542 h2' t2) = h2'.
Proof. exact (@lem1105097 _25542 t2 h2'). Qed.
Lemma lem1105099 {_25542 _25543 _25549 : Type'} (f : type1469 _25542 _25543 _25549) (h1' : _25543) : (f h1') = (f h1').
Proof. exact (eq_refl (f h1')). Qed.
Lemma lem1105100 {_25542 _25543 _25549 : Type'} (t2 : list _25542) (f : type1469 _25542 _25543 _25549) (h1' : _25543) (h2' : _25542) : (term9 _25542 _25543 _25549 f h1' h2' t2) = (f h1' h2').
Proof. exact (MK_COMB (@lem1105099 _25542 _25543 _25549 f h1') (@lem1105098 _25542 t2 h2')). Qed.
Lemma lem1105101 {_25549 : Type'} : (@cons _25549) = (@cons _25549).
Proof. exact (eq_refl (@cons _25549)). Qed.
Lemma lem1105102 {_25542 _25543 _25549 : Type'} (t2 : list _25542) (f : type1469 _25542 _25543 _25549) (h1' : _25543) (h2' : _25542) : (term10 _25542 _25543 _25549 f h1' h2' t2) = (term11 _25542 _25543 _25549 f h1' h2').
Proof. exact (MK_COMB (@lem1105101 _25549) (@lem1105100 _25542 _25543 _25549 t2 f h1' h2')). Qed.
Lemma lem1105104 {A : Type'} (h : A) (t : list A) : (term12 A h t) = t.
Proof. exact (EQ_MP (@lem1095389 A h t) (@lem1095388 A h t)). Qed.
Lemma lem1105105 {_25542 : Type'} (h : _25542) (t : list _25542) : (term12 _25542 h t) = t.
Proof. exact (@lem1105104 _25542 h t). Qed.
Lemma lem1105106 {_25542 : Type'} (h2' : _25542) (t2 : list _25542) : (term12 _25542 h2' t2) = t2.
Proof. exact (@lem1105105 _25542 h2' t2). Qed.
Lemma lem1105107 {_25542 _25543 _25549 : Type'} (f : type1469 _25542 _25543 _25549) (t1 : list _25543) : (@MAP2 _25549 _25543 _25542 f t1) = (@MAP2 _25549 _25543 _25542 f t1).
Proof. exact (eq_refl (@MAP2 _25549 _25543 _25542 f t1)). Qed.
Lemma lem1105108 {_25542 _25543 _25549 : Type'} (h2' : _25542) (f : type1469 _25542 _25543 _25549) (t1 : list _25543) (t2 : list _25542) : (term13 _25542 _25543 _25549 f t1 h2' t2) = (@MAP2 _25549 _25543 _25542 f t1 t2).
Proof. exact (MK_COMB (@lem1105107 _25542 _25543 _25549 f t1) (@lem1105106 _25542 h2' t2)). Qed.
Lemma lem1105109 {_25542 _25543 _25549 : Type'} (h1' : _25543) (h2' : _25542) (f : type1469 _25542 _25543 _25549) (t1 : list _25543) (t2 : list _25542) : (term7 _25542 _25543 _25549 h1' f t1 h2' t2) = (term14 _25542 _25543 _25549 h1' h2' f t1 t2).
Proof. exact (MK_COMB (@lem1105102 _25542 _25543 _25549 t2 f h1' h2') (@lem1105108 _25542 _25543 _25549 h2' f t1 t2)). Qed.
Lemma lem1105110 {_25542 _25543 _25549 : Type'} (h1' : _25543) (h2' : _25542) (f : type1469 _25542 _25543 _25549) (t1 : list _25543) (t2 : list _25542) : (term6 _25542 _25543 _25549 f h1' t1 h2' t2) = (term14 _25542 _25543 _25549 h1' h2' f t1 t2).
Proof. exact (TRANS (@lem1105094 _25542 _25543 _25549 h1' f t1 h2' t2) (@lem1105109 _25542 _25543 _25549 h1' h2' f t1 t2)). Qed.
Lemma lem1105111 {_25549 : Type'} : (@eq (list _25549)) = (@eq (list _25549)).
Proof. exact (eq_refl (@eq (list _25549))). Qed.
Lemma lem1105112 {_25542 _25543 _25549 : Type'} (h1' : _25543) (h2' : _25542) (f : type1469 _25542 _25543 _25549) (t1 : list _25543) (t2 : list _25542) : (term15 _25542 _25543 _25549 f h1' t1 h2' t2) = (term16 _25542 _25543 _25549 h1' h2' f t1 t2).
Proof. exact (MK_COMB (@lem1105111 _25549) (@lem1105110 _25542 _25543 _25549 h1' h2' f t1 t2)). Qed.
Lemma lem1105113 {_25542 _25543 _25549 : Type'} (h1' : _25543) (h2' : _25542) (f : type1469 _25542 _25543 _25549) (t1 : list _25543) (t2 : list _25542) : (term14 _25542 _25543 _25549 h1' h2' f t1 t2) = (term14 _25542 _25543 _25549 h1' h2' f t1 t2).
Proof. exact (eq_refl (term14 _25542 _25543 _25549 h1' h2' f t1 t2)). Qed.
Lemma lem1105114 {_25542 _25543 _25549 : Type'} (h1' : _25543) (h2' : _25542) (f : type1469 _25542 _25543 _25549) (t1 : list _25543) (t2 : list _25542) : ((term6 _25542 _25543 _25549 f h1' t1 h2' t2) = (term14 _25542 _25543 _25549 h1' h2' f t1 t2)) = ((term14 _25542 _25543 _25549 h1' h2' f t1 t2) = (term14 _25542 _25543 _25549 h1' h2' f t1 t2)).
Proof. exact (MK_COMB (@lem1105112 _25542 _25543 _25549 h1' h2' f t1 t2) (@lem1105113 _25542 _25543 _25549 h1' h2' f t1 t2)). Qed.
Lemma lem1105116 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1105117 {_25549 : Type'} (x : list _25549) : (x = x) = True.
Proof. exact (@lem1105116 (list _25549) x). Qed.
Lemma lem1105118 {_25542 _25543 _25549 : Type'} (h1' : _25543) (h2' : _25542) (f : type1469 _25542 _25543 _25549) (t1 : list _25543) (t2 : list _25542) : ((term14 _25542 _25543 _25549 h1' h2' f t1 t2) = (term14 _25542 _25543 _25549 h1' h2' f t1 t2)) = True.
Proof. exact (@lem1105117 _25549 (term14 _25542 _25543 _25549 h1' h2' f t1 t2)). Qed.
Lemma lem1105119 {_25542 _25543 _25549 : Type'} (h1' : _25543) (h2' : _25542) (f : type1469 _25542 _25543 _25549) (t1 : list _25543) (t2 : list _25542) : ((term6 _25542 _25543 _25549 f h1' t1 h2' t2) = (term14 _25542 _25543 _25549 h1' h2' f t1 t2)) = True.
Proof. exact (TRANS (@lem1105114 _25542 _25543 _25549 h1' h2' f t1 t2) (@lem1105118 _25542 _25543 _25549 h1' h2' f t1 t2)). Qed.
Lemma lem1105120 {_25542 _25543 _25549 : Type'} (h1' : _25543) (h2' : _25542) (f : type1469 _25542 _25543 _25549) (t1 : list _25543) (t2 : list _25542) : (term17 _25542 _25543 _25549 h1' h2' f t1 t2) = (True /\ True).
Proof. exact (MK_COMB (@lem1105088 _25542 _25543 _25549 f) (@lem1105119 _25542 _25543 _25549 h1' h2' f t1 t2)). Qed.
Lemma lem1105122 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1105123 : (True /\ True) = True.
Proof. exact (@lem1105122 True). Qed.
Lemma lem1105124 {_25542 _25543 _25549 : Type'} (h1' : _25543) (h2' : _25542) (f : type1469 _25542 _25543 _25549) (t1 : list _25543) (t2 : list _25542) : (term17 _25542 _25543 _25549 h1' h2' f t1 t2) = True.
Proof. exact (TRANS (@lem1105120 _25542 _25543 _25549 h1' h2' f t1 t2) (@lem1105123)). Qed.
Lemma lem1105125 {_25542 _25543 _25549 : Type'} (h1' : _25543) (h2' : _25542) (f : type1469 _25542 _25543 _25549) (t1 : list _25543) (t2 : list _25542) : True = (term17 _25542 _25543 _25549 h1' h2' f t1 t2).
Proof. exact (SYM (@lem1105124 _25542 _25543 _25549 h1' h2' f t1 t2)). Qed.
Lemma lem1105126 {_25542 _25543 _25549 : Type'} (h1' : _25543) (h2' : _25542) (f : type1469 _25542 _25543 _25549) (t1 : list _25543) (t2 : list _25542) : term17 _25542 _25543 _25549 h1' h2' f t1 t2.
Proof. exact (EQ_MP (@lem1105125 _25542 _25543 _25549 h1' h2' f t1 t2) (@lem0)). Qed.
