Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ZIP_term_abbrevs.
Require Import thm0_spec.
Require Import thm1094865_spec.
Require Import thm1094866_spec.
Require Import thm1095388_spec.
Require Import thm1095389_spec.
Require Import thm1108937_spec.
Require Import thm1108938_spec.
Require Import thm1108946_spec.
Require Import thm1108947_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1108957 {_25719 _25727 : Type'} (l2 : list _25727) : (@ZIP _25719 _25727 (@nil _25719) l2) = (@nil (prod _25719 _25727)).
Proof. exact (EQ_MP (@lem1108938 _25719 _25727 l2) (@lem1108937 _25719 _25727 l2)). Qed.
Lemma lem1108958 {_25738 _25739 : Type'} (l2 : list _25739) : (@ZIP _25738 _25739 (@nil _25738) l2) = (@nil (prod _25738 _25739)).
Proof. exact (@lem1108957 _25738 _25739 l2). Qed.
Lemma lem1108959 {_25738 _25739 : Type'} : (@ZIP _25738 _25739 (@nil _25738) (@nil _25739)) = (@nil (prod _25738 _25739)).
Proof. exact (@lem1108958 _25738 _25739 (@nil _25739)). Qed.
Lemma lem1108960 {_25738 _25739 : Type'} : (@eq (list (prod _25738 _25739))) = (@eq (list (prod _25738 _25739))).
Proof. exact (eq_refl (@eq (list (prod _25738 _25739)))). Qed.
Lemma lem1108961 {_25738 _25739 : Type'} : (term0 _25738 _25739) = (@eq (list (prod _25738 _25739)) (@nil (prod _25738 _25739))).
Proof. exact (MK_COMB (@lem1108960 _25738 _25739) (@lem1108959 _25738 _25739)). Qed.
Lemma lem1108962 {_25738 _25739 : Type'} : (@nil (prod _25738 _25739)) = (@nil (prod _25738 _25739)).
Proof. exact (eq_refl (@nil (prod _25738 _25739))). Qed.
Lemma lem1108963 {_25738 _25739 : Type'} : ((@ZIP _25738 _25739 (@nil _25738) (@nil _25739)) = (@nil (prod _25738 _25739))) = ((@nil (prod _25738 _25739)) = (@nil (prod _25738 _25739))).
Proof. exact (MK_COMB (@lem1108961 _25738 _25739) (@lem1108962 _25738 _25739)). Qed.
Lemma lem1108965 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1108966 {_25738 _25739 : Type'} (x : type1640 _25738 _25739) : (x = x) = True.
Proof. exact (@lem1108965 (type1640 _25738 _25739) x). Qed.
Lemma lem1108967 {_25738 _25739 : Type'} : ((@nil (prod _25738 _25739)) = (@nil (prod _25738 _25739))) = True.
Proof. exact (@lem1108966 _25738 _25739 (@nil (prod _25738 _25739))). Qed.
Lemma lem1108968 {_25738 _25739 : Type'} : ((@ZIP _25738 _25739 (@nil _25738) (@nil _25739)) = (@nil (prod _25738 _25739))) = True.
Proof. exact (TRANS (@lem1108963 _25738 _25739) (@lem1108967 _25738 _25739)). Qed.
Lemma lem1108969 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1108970 {_25738 _25739 : Type'} : (term1 _25738 _25739) = (and True).
Proof. exact (MK_COMB (@lem1108969) (@lem1108968 _25738 _25739)). Qed.
Lemma lem1108974 {_25719 _25727 : Type'} (h1' : _25719) (t1 : list _25719) (l2 : list _25727) : (term2 _25719 _25727 h1' t1 l2) = (term3 _25719 _25727 h1' t1 l2).
Proof. exact (EQ_MP (@lem1108947 _25719 _25727 h1' t1 l2) (@lem1108946 _25719 _25727 h1' t1 l2)). Qed.
Lemma lem1108975 {_25763 _25764 : Type'} (h1' : _25763) (t1 : list _25763) (l2 : list _25764) : (term2 _25763 _25764 h1' t1 l2) = (term3 _25763 _25764 h1' t1 l2).
Proof. exact (@lem1108974 _25763 _25764 h1' t1 l2). Qed.
Lemma lem1108976 {_25763 _25764 : Type'} (h1' : _25763) (t1 : list _25763) (h2' : _25764) (t2 : list _25764) : (term4 _25763 _25764 h1' t1 h2' t2) = (term5 _25763 _25764 h1' t1 h2' t2).
Proof. exact (@lem1108975 _25763 _25764 h1' t1 (@cons _25764 h2' t2)). Qed.
Lemma lem1108978 {A : Type'} (t : list A) (h : A) : (term6 A h t) = h.
Proof. exact (EQ_MP (@lem1094866 A t h) (@lem1094865 A t h)). Qed.
Lemma lem1108979 {_25764 : Type'} (t : list _25764) (h : _25764) : (term6 _25764 h t) = h.
Proof. exact (@lem1108978 _25764 t h). Qed.
Lemma lem1108980 {_25764 : Type'} (t2 : list _25764) (h2' : _25764) : (term6 _25764 h2' t2) = h2'.
Proof. exact (@lem1108979 _25764 t2 h2'). Qed.
Lemma lem1108981 {_25763 _25764 : Type'} (h1' : _25763) : (@pair _25763 _25764 h1') = (@pair _25763 _25764 h1').
Proof. exact (eq_refl (@pair _25763 _25764 h1')). Qed.
Lemma lem1108982 {_25763 _25764 : Type'} (t2 : list _25764) (h1' : _25763) (h2' : _25764) : (term7 _25763 _25764 h1' h2' t2) = (@pair _25763 _25764 h1' h2').
Proof. exact (MK_COMB (@lem1108981 _25763 _25764 h1') (@lem1108980 _25764 t2 h2')). Qed.
Lemma lem1108983 {_25763 _25764 : Type'} : (@cons (prod _25763 _25764)) = (@cons (prod _25763 _25764)).
Proof. exact (eq_refl (@cons (prod _25763 _25764))). Qed.
Lemma lem1108984 {_25763 _25764 : Type'} (t2 : list _25764) (h1' : _25763) (h2' : _25764) : (term8 _25763 _25764 h1' h2' t2) = (term9 _25763 _25764 h1' h2').
Proof. exact (MK_COMB (@lem1108983 _25763 _25764) (@lem1108982 _25763 _25764 t2 h1' h2')). Qed.
Lemma lem1108986 {A : Type'} (h : A) (t : list A) : (term10 A h t) = t.
Proof. exact (EQ_MP (@lem1095389 A h t) (@lem1095388 A h t)). Qed.
Lemma lem1108987 {_25764 : Type'} (h : _25764) (t : list _25764) : (term10 _25764 h t) = t.
Proof. exact (@lem1108986 _25764 h t). Qed.
Lemma lem1108988 {_25764 : Type'} (h2' : _25764) (t2 : list _25764) : (term10 _25764 h2' t2) = t2.
Proof. exact (@lem1108987 _25764 h2' t2). Qed.
Lemma lem1108989 {_25763 _25764 : Type'} (t1 : list _25763) : (@ZIP _25763 _25764 t1) = (@ZIP _25763 _25764 t1).
Proof. exact (eq_refl (@ZIP _25763 _25764 t1)). Qed.
Lemma lem1108990 {_25763 _25764 : Type'} (h2' : _25764) (t1 : list _25763) (t2 : list _25764) : (term11 _25763 _25764 t1 h2' t2) = (@ZIP _25763 _25764 t1 t2).
Proof. exact (MK_COMB (@lem1108989 _25763 _25764 t1) (@lem1108988 _25764 h2' t2)). Qed.
Lemma lem1108991 {_25763 _25764 : Type'} (h1' : _25763) (h2' : _25764) (t1 : list _25763) (t2 : list _25764) : (term5 _25763 _25764 h1' t1 h2' t2) = (term12 _25763 _25764 h1' h2' t1 t2).
Proof. exact (MK_COMB (@lem1108984 _25763 _25764 t2 h1' h2') (@lem1108990 _25763 _25764 h2' t1 t2)). Qed.
Lemma lem1108992 {_25763 _25764 : Type'} (h1' : _25763) (h2' : _25764) (t1 : list _25763) (t2 : list _25764) : (term4 _25763 _25764 h1' t1 h2' t2) = (term12 _25763 _25764 h1' h2' t1 t2).
Proof. exact (TRANS (@lem1108976 _25763 _25764 h1' t1 h2' t2) (@lem1108991 _25763 _25764 h1' h2' t1 t2)). Qed.
Lemma lem1108993 {_25763 _25764 : Type'} : (@eq (list (prod _25763 _25764))) = (@eq (list (prod _25763 _25764))).
Proof. exact (eq_refl (@eq (list (prod _25763 _25764)))). Qed.
Lemma lem1108994 {_25763 _25764 : Type'} (h1' : _25763) (h2' : _25764) (t1 : list _25763) (t2 : list _25764) : (term13 _25763 _25764 h1' t1 h2' t2) = (term14 _25763 _25764 h1' h2' t1 t2).
Proof. exact (MK_COMB (@lem1108993 _25763 _25764) (@lem1108992 _25763 _25764 h1' h2' t1 t2)). Qed.
Lemma lem1108995 {_25763 _25764 : Type'} (h1' : _25763) (h2' : _25764) (t1 : list _25763) (t2 : list _25764) : (term12 _25763 _25764 h1' h2' t1 t2) = (term12 _25763 _25764 h1' h2' t1 t2).
Proof. exact (eq_refl (term12 _25763 _25764 h1' h2' t1 t2)). Qed.
Lemma lem1108996 {_25763 _25764 : Type'} (h1' : _25763) (h2' : _25764) (t1 : list _25763) (t2 : list _25764) : ((term4 _25763 _25764 h1' t1 h2' t2) = (term12 _25763 _25764 h1' h2' t1 t2)) = ((term12 _25763 _25764 h1' h2' t1 t2) = (term12 _25763 _25764 h1' h2' t1 t2)).
Proof. exact (MK_COMB (@lem1108994 _25763 _25764 h1' h2' t1 t2) (@lem1108995 _25763 _25764 h1' h2' t1 t2)). Qed.
Lemma lem1108998 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1108999 {_25763 _25764 : Type'} (x : type1640 _25763 _25764) : (x = x) = True.
Proof. exact (@lem1108998 (type1640 _25763 _25764) x). Qed.
Lemma lem1109000 {_25763 _25764 : Type'} (h1' : _25763) (h2' : _25764) (t1 : list _25763) (t2 : list _25764) : ((term12 _25763 _25764 h1' h2' t1 t2) = (term12 _25763 _25764 h1' h2' t1 t2)) = True.
Proof. exact (@lem1108999 _25763 _25764 (term12 _25763 _25764 h1' h2' t1 t2)). Qed.
Lemma lem1109001 {_25763 _25764 : Type'} (h1' : _25763) (h2' : _25764) (t1 : list _25763) (t2 : list _25764) : ((term4 _25763 _25764 h1' t1 h2' t2) = (term12 _25763 _25764 h1' h2' t1 t2)) = True.
Proof. exact (TRANS (@lem1108996 _25763 _25764 h1' h2' t1 t2) (@lem1109000 _25763 _25764 h1' h2' t1 t2)). Qed.
Lemma lem1109002 {_25738 _25739 _25763 _25764 : Type'} (h1' : _25763) (h2' : _25764) (t1 : list _25763) (t2 : list _25764) : (term15 _25738 _25739 _25763 _25764 h1' h2' t1 t2) = (True /\ True).
Proof. exact (MK_COMB (@lem1108970 _25738 _25739) (@lem1109001 _25763 _25764 h1' h2' t1 t2)). Qed.
Lemma lem1109004 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1109005 : (True /\ True) = True.
Proof. exact (@lem1109004 True). Qed.
Lemma lem1109006 {_25738 _25739 _25763 _25764 : Type'} (h1' : _25763) (h2' : _25764) (t1 : list _25763) (t2 : list _25764) : (term15 _25738 _25739 _25763 _25764 h1' h2' t1 t2) = True.
Proof. exact (TRANS (@lem1109002 _25738 _25739 _25763 _25764 h1' h2' t1 t2) (@lem1109005)). Qed.
Lemma lem1109007 {_25738 _25739 _25763 _25764 : Type'} (h1' : _25763) (h2' : _25764) (t1 : list _25763) (t2 : list _25764) : True = (term15 _25738 _25739 _25763 _25764 h1' h2' t1 t2).
Proof. exact (SYM (@lem1109006 _25738 _25739 _25763 _25764 h1' h2' t1 t2)). Qed.
Lemma lem1109008 {_25738 _25739 _25763 _25764 : Type'} (h1' : _25763) (h2' : _25764) (t1 : list _25763) (t2 : list _25764) : term15 _25738 _25739 _25763 _25764 h1' h2' t1 t2.
Proof. exact (EQ_MP (@lem1109007 _25738 _25739 _25763 _25764 h1' h2' t1 t2) (@lem0)). Qed.
