Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ALL_MAP_term_abbrevs.
Require Import o_THM_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1097797_spec.
Require Import thm1100834_spec.
Require Import thm1100835_spec.
Require Import thm1100843_spec.
Require Import thm1100844_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1123623 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1123624 {_26411 : Type'} (P : type1143 _26411) : term0 _26411 P.
Proof. exact (@lem1123623 _26411 P). Qed.
Lemma lem1123625 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) : term1 _26411 _26412 P f.
Proof. exact (@lem1123624 _26411 (term2 _26411 _26412 P f)). Qed.
Lemma lem1123626 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) : (term3 _26411 _26412 P f) = ((term4 _26411 _26412 P f) = (term5 _26411 _26412 P f)).
Proof. exact (eq_refl (term3 _26411 _26412 P f)). Qed.
Lemma lem1123627 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1123628 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) : (term6 _26411 _26412 P f) = (term7 _26411 _26412 P f).
Proof. exact (MK_COMB (@lem1123627) (@lem1123626 _26411 _26412 P f)). Qed.
Lemma lem1123629 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) (t : list _26411) : (term8 _26411 _26412 P f t) = ((term9 _26411 _26412 P f t) = (term10 _26411 _26412 P f t)).
Proof. exact (eq_refl (term8 _26411 _26412 P f t)). Qed.
Lemma lem1123630 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1123631 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) (t : list _26411) : (term11 _26411 _26412 P f t) = (term12 _26411 _26412 P f t).
Proof. exact (MK_COMB (@lem1123630) (@lem1123629 _26411 _26412 P f t)). Qed.
Lemma lem1123632 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) (h : _26411) (t : list _26411) : (term13 _26411 _26412 P f h t) = ((term14 _26411 _26412 P f h t) = (term15 _26411 _26412 P f h t)).
Proof. exact (eq_refl (term13 _26411 _26412 P f h t)). Qed.
Lemma lem1123633 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) (h : _26411) (t : list _26411) : (term16 _26411 _26412 P f h t) = (term17 _26411 _26412 P f h t).
Proof. exact (MK_COMB (@lem1123631 _26411 _26412 P f t) (@lem1123632 _26411 _26412 P f h t)). Qed.
Lemma lem1123634 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) (h : _26411) : (term18 _26411 _26412 P f h) = (term19 _26411 _26412 P f h).
Proof. exact (fun_ext (fun t : list _26411 => @lem1123633 _26411 _26412 P f h t)). Qed.
Lemma lem1123635 {_26411 : Type'} : (@all (list _26411)) = (@all (list _26411)).
Proof. exact (eq_refl (@all (list _26411))). Qed.
Lemma lem1123636 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) (h : _26411) : (term20 _26411 _26412 P f h) = (term21 _26411 _26412 P f h).
Proof. exact (MK_COMB (@lem1123635 _26411) (@lem1123634 _26411 _26412 P f h)). Qed.
Lemma lem1123637 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) : (term22 _26411 _26412 P f) = (term23 _26411 _26412 P f).
Proof. exact (fun_ext (fun h : _26411 => @lem1123636 _26411 _26412 P f h)). Qed.
Lemma lem1123638 {_26411 : Type'} : (@all _26411) = (@all _26411).
Proof. exact (eq_refl (@all _26411)). Qed.
Lemma lem1123639 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) : (term24 _26411 _26412 P f) = (term25 _26411 _26412 P f).
Proof. exact (MK_COMB (@lem1123638 _26411) (@lem1123637 _26411 _26412 P f)). Qed.
Lemma lem1123640 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) : (term26 _26411 _26412 P f) = (term27 _26411 _26412 P f).
Proof. exact (MK_COMB (@lem1123628 _26411 _26412 P f) (@lem1123639 _26411 _26412 P f)). Qed.
Lemma lem1123641 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1123642 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) : (term28 _26411 _26412 P f) = (term29 _26411 _26412 P f).
Proof. exact (MK_COMB (@lem1123641) (@lem1123640 _26411 _26412 P f)). Qed.
Lemma lem1123643 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) (l : list _26411) : (term8 _26411 _26412 P f l) = ((term9 _26411 _26412 P f l) = (term10 _26411 _26412 P f l)).
Proof. exact (eq_refl (term8 _26411 _26412 P f l)). Qed.
Lemma lem1123644 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) : (term30 _26411 _26412 P f) = (term2 _26411 _26412 P f).
Proof. exact (fun_ext (fun l : list _26411 => @lem1123643 _26411 _26412 P f l)). Qed.
Lemma lem1123645 {_26411 : Type'} : (@all (list _26411)) = (@all (list _26411)).
Proof. exact (eq_refl (@all (list _26411))). Qed.
Lemma lem1123646 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) : (term31 _26411 _26412 P f) = (term32 _26411 _26412 P f).
Proof. exact (MK_COMB (@lem1123645 _26411) (@lem1123644 _26411 _26412 P f)). Qed.
Lemma lem1123647 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) : (term1 _26411 _26412 P f) = (term33 _26411 _26412 P f).
Proof. exact (MK_COMB (@lem1123642 _26411 _26412 P f) (@lem1123646 _26411 _26412 P f)). Qed.
Lemma lem1123648 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) : term33 _26411 _26412 P f.
Proof. exact (EQ_MP (@lem1123647 _26411 _26412 P f) (@lem1123625 _26411 _26412 P f)). Qed.
Lemma lem1123669 {A B : Type'} : term34 A B.
Proof. exact (proj1 (@lem1097797 A B)). Qed.
Lemma lem1123670 {A B : Type'} (f : A -> B) : term35 A B f.
Proof. exact (@lem1123669 A B f). Qed.
Lemma lem1123671 {A B : Type'} (f : A -> B) : (term35 A B f) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl (term35 A B f)). Qed.
Lemma lem1123678 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1123671 A B f) (@lem1123670 A B f)). Qed.
Lemma lem1123679 {_26411 _26412 : Type'} (f : _26411 -> _26412) : (@List.map _26411 _26412 f (@nil _26411)) = (@nil _26412).
Proof. exact (@lem1123678 _26411 _26412 f). Qed.
Lemma lem1123680 {_26412 : Type'} (P : _26412 -> Prop) : (@List.Forall _26412 P) = (@List.Forall _26412 P).
Proof. exact (eq_refl (@List.Forall _26412 P)). Qed.
Lemma lem1123681 {_26411 _26412 : Type'} (f : _26411 -> _26412) (P : _26412 -> Prop) : (term4 _26411 _26412 P f) = (@List.Forall _26412 P (@nil _26412)).
Proof. exact (MK_COMB (@lem1123680 _26412 P) (@lem1123679 _26411 _26412 f)). Qed.
Lemma lem1123683 {_25307 : Type'} (P : _25307 -> Prop) : (@List.Forall _25307 P (@nil _25307)) = True.
Proof. exact (EQ_MP (@lem1100835 _25307 P) (@lem1100834 _25307 P)). Qed.
Lemma lem1123684 {_26412 : Type'} (P : _26412 -> Prop) : (@List.Forall _26412 P (@nil _26412)) = True.
Proof. exact (@lem1123683 _26412 P). Qed.
Lemma lem1123685 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) : (term4 _26411 _26412 P f) = True.
Proof. exact (TRANS (@lem1123681 _26411 _26412 f P) (@lem1123684 _26412 P)). Qed.
Lemma lem1123686 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1123687 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) : (term36 _26411 _26412 P f) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1123686) (@lem1123685 _26411 _26412 P f)). Qed.
Lemma lem1123689 {_25307 : Type'} (P : _25307 -> Prop) : (@List.Forall _25307 P (@nil _25307)) = True.
Proof. exact (EQ_MP (@lem1100835 _25307 P) (@lem1100834 _25307 P)). Qed.
Lemma lem1123690 {_26411 : Type'} (P : _26411 -> Prop) : (@List.Forall _26411 P (@nil _26411)) = True.
Proof. exact (@lem1123689 _26411 P). Qed.
Lemma lem1123691 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) : (term5 _26411 _26412 P f) = True.
Proof. exact (@lem1123690 _26411 (@o _26411 _26412 Prop P f)). Qed.
Lemma lem1123692 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) : ((term4 _26411 _26412 P f) = (term5 _26411 _26412 P f)) = (True = True).
Proof. exact (MK_COMB (@lem1123687 _26411 _26412 P f) (@lem1123691 _26411 _26412 P f)). Qed.
Lemma lem1123694 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1123695 : (True = True) = True.
Proof. exact (@lem1123694 True). Qed.
Lemma lem1123696 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) : ((term4 _26411 _26412 P f) = (term5 _26411 _26412 P f)) = True.
Proof. exact (TRANS (@lem1123692 _26411 _26412 P f) (@lem1123695)). Qed.
Lemma lem1123697 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) : True = ((term4 _26411 _26412 P f) = (term5 _26411 _26412 P f)).
Proof. exact (SYM (@lem1123696 _26411 _26412 P f)). Qed.
Lemma lem1123698 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) : (term4 _26411 _26412 P f) = (term5 _26411 _26412 P f).
Proof. exact (EQ_MP (@lem1123697 _26411 _26412 P f) (@lem0)). Qed.
Lemma lem1123699 {A B C : Type'} (f : B -> C) : term37 A B C f.
Proof. exact (@lem15456 A B C f). Qed.
Lemma lem1123700 {A B C : Type'} (f : B -> C) : (term37 A B C f) = (term38 A B C f).
Proof. exact (eq_refl (term37 A B C f)). Qed.
Lemma lem1123701 {A B C : Type'} (f : B -> C) : term38 A B C f.
Proof. exact (EQ_MP (@lem1123700 A B C f) (@lem1123699 A B C f)). Qed.
Lemma lem1123702 {A B C : Type'} (f : B -> C) (g : A -> B) : term39 A B C f g.
Proof. exact (@lem1123701 A B C f g). Qed.
Lemma lem1123703 {A B C : Type'} (f : B -> C) (g : A -> B) : (term39 A B C f g) = (term40 A B C f g).
Proof. exact (eq_refl (term39 A B C f g)). Qed.
Lemma lem1123704 {A B C : Type'} (f : B -> C) (g : A -> B) : term40 A B C f g.
Proof. exact (EQ_MP (@lem1123703 A B C f g) (@lem1123702 A B C f g)). Qed.
Lemma lem1123705 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : term41 A B C f g x.
Proof. exact (@lem1123704 A B C f g x). Qed.
Lemma lem1123706 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (term41 A B C f g x) = ((@o A B C f g x) = (term42 A B C f g x)).
Proof. exact (eq_refl (term41 A B C f g x)). Qed.
Lemma lem1123708 {A B : Type'} : term43 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem1123709 {A B : Type'} (f : A -> B) : term44 A B f.
Proof. exact (@lem1123708 A B f). Qed.
Lemma lem1123710 {A B : Type'} (f : A -> B) : (term44 A B f) = (term45 A B f).
Proof. exact (eq_refl (term44 A B f)). Qed.
Lemma lem1123711 {A B : Type'} (f : A -> B) : term45 A B f.
Proof. exact (EQ_MP (@lem1123710 A B f) (@lem1123709 A B f)). Qed.
Lemma lem1123712 {A B : Type'} (f : A -> B) (h : A) : term46 A B f h.
Proof. exact (@lem1123711 A B f h). Qed.
Lemma lem1123713 {A B : Type'} (h : A) (f : A -> B) : (term46 A B f h) = (term47 A B h f).
Proof. exact (eq_refl (term46 A B f h)). Qed.
Lemma lem1123714 {A B : Type'} (h : A) (f : A -> B) : term47 A B h f.
Proof. exact (EQ_MP (@lem1123713 A B h f) (@lem1123712 A B f h)). Qed.
Lemma lem1123715 {A B : Type'} (h : A) (f : A -> B) (t : list A) : term48 A B h f t.
Proof. exact (@lem1123714 A B h f t). Qed.
Lemma lem1123716 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term48 A B h f t) = ((term49 A B f h t) = (term50 A B h f t)).
Proof. exact (eq_refl (term48 A B h f t)). Qed.
Lemma lem1123727 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term49 A B f h t) = (term50 A B h f t).
Proof. exact (EQ_MP (@lem1123716 A B h f t) (@lem1123715 A B h f t)). Qed.
Lemma lem1123728 {_26411 _26412 : Type'} (h : _26411) (f : _26411 -> _26412) (t : list _26411) : (term49 _26411 _26412 f h t) = (term50 _26411 _26412 h f t).
Proof. exact (@lem1123727 _26411 _26412 h f t). Qed.
Lemma lem1123729 {_26412 : Type'} (P : _26412 -> Prop) : (@List.Forall _26412 P) = (@List.Forall _26412 P).
Proof. exact (eq_refl (@List.Forall _26412 P)). Qed.
Lemma lem1123730 {_26411 _26412 : Type'} (P : _26412 -> Prop) (h : _26411) (f : _26411 -> _26412) (t : list _26411) : (term14 _26411 _26412 P f h t) = (term51 _26411 _26412 P h f t).
Proof. exact (MK_COMB (@lem1123729 _26412 P) (@lem1123728 _26411 _26412 h f t)). Qed.
Lemma lem1123732 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term52 _25307 P h t) = (term53 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1123733 {_26412 : Type'} (h : _26412) (P : _26412 -> Prop) (t : list _26412) : (term52 _26412 P h t) = (term53 _26412 h P t).
Proof. exact (@lem1123732 _26412 h P t). Qed.
Lemma lem1123734 {_26411 _26412 : Type'} (h : _26411) (P : _26412 -> Prop) (f : _26411 -> _26412) (t : list _26411) : (term51 _26411 _26412 P h f t) = (term54 _26411 _26412 h P f t).
Proof. exact (@lem1123733 _26412 (f h) P (@List.map _26411 _26412 f t)). Qed.
Lemma lem1123738 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) (t : list _26411) (h1 : (term9 _26411 _26412 P f t) = (term10 _26411 _26412 P f t)) : (term9 _26411 _26412 P f t) = (term10 _26411 _26412 P f t).
Proof. exact (h1). Qed.
Lemma lem1123739 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) (h : _26411) : (term55 _26411 _26412 P f h) = (term55 _26411 _26412 P f h).
Proof. exact (eq_refl (term55 _26411 _26412 P f h)). Qed.
Lemma lem1123740 {_26411 _26412 : Type'} (h : _26411) (P : _26412 -> Prop) (f : _26411 -> _26412) (t : list _26411) (h1 : (term9 _26411 _26412 P f t) = (term10 _26411 _26412 P f t)) : (term54 _26411 _26412 h P f t) = (term56 _26411 _26412 h P f t).
Proof. exact (MK_COMB (@lem1123739 _26411 _26412 P f h) (@lem1123738 _26411 _26412 P f t h1)). Qed.
Lemma lem1123743 {_26411 _26412 : Type'} (h : _26411) (P : _26412 -> Prop) (f : _26411 -> _26412) (t : list _26411) (h1 : (term9 _26411 _26412 P f t) = (term10 _26411 _26412 P f t)) : (term51 _26411 _26412 P h f t) = (term56 _26411 _26412 h P f t).
Proof. exact (TRANS (@lem1123734 _26411 _26412 h P f t) (@lem1123740 _26411 _26412 h P f t h1)). Qed.
Lemma lem1123744 {_26411 _26412 : Type'} (h : _26411) (P : _26412 -> Prop) (f : _26411 -> _26412) (t : list _26411) (h1 : (term9 _26411 _26412 P f t) = (term10 _26411 _26412 P f t)) : (term14 _26411 _26412 P f h t) = (term56 _26411 _26412 h P f t).
Proof. exact (TRANS (@lem1123730 _26411 _26412 P h f t) (@lem1123743 _26411 _26412 h P f t h1)). Qed.
Lemma lem1123745 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1123746 {_26411 _26412 : Type'} (h : _26411) (P : _26412 -> Prop) (f : _26411 -> _26412) (t : list _26411) (h1 : (term9 _26411 _26412 P f t) = (term10 _26411 _26412 P f t)) : (term57 _26411 _26412 P f h t) = (term58 _26411 _26412 h P f t).
Proof. exact (MK_COMB (@lem1123745) (@lem1123744 _26411 _26412 h P f t h1)). Qed.
Lemma lem1123748 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term52 _25307 P h t) = (term53 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1123749 {_26411 : Type'} (h : _26411) (P : _26411 -> Prop) (t : list _26411) : (term52 _26411 P h t) = (term53 _26411 h P t).
Proof. exact (@lem1123748 _26411 h P t). Qed.
Lemma lem1123750 {_26411 _26412 : Type'} (h : _26411) (P : _26412 -> Prop) (f : _26411 -> _26412) (t : list _26411) : (term15 _26411 _26412 P f h t) = (term59 _26411 _26412 h P f t).
Proof. exact (@lem1123749 _26411 h (@o _26411 _26412 Prop P f) t). Qed.
Lemma lem1123754 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (@o A B C f g x) = (term42 A B C f g x).
Proof. exact (EQ_MP (@lem1123706 A B C f g x) (@lem1123705 A B C f g x)). Qed.
Lemma lem1123755 {_26411 _26412 : Type'} (f : _26412 -> Prop) (g : _26411 -> _26412) (x : _26411) : (@o _26411 _26412 Prop f g x) = (term60 _26411 _26412 f g x).
Proof. exact (@lem1123754 _26411 _26412 Prop f g x). Qed.
Lemma lem1123756 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) (h : _26411) : (@o _26411 _26412 Prop P f h) = (term60 _26411 _26412 P f h).
Proof. exact (@lem1123755 _26411 _26412 P f h). Qed.
Lemma lem1123757 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1123758 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) (h : _26411) : (term61 _26411 _26412 P f h) = (term55 _26411 _26412 P f h).
Proof. exact (MK_COMB (@lem1123757) (@lem1123756 _26411 _26412 P f h)). Qed.
Lemma lem1123759 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) (t : list _26411) : (term10 _26411 _26412 P f t) = (term10 _26411 _26412 P f t).
Proof. exact (eq_refl (term10 _26411 _26412 P f t)). Qed.
Lemma lem1123760 {_26411 _26412 : Type'} (h : _26411) (P : _26412 -> Prop) (f : _26411 -> _26412) (t : list _26411) : (term59 _26411 _26412 h P f t) = (term56 _26411 _26412 h P f t).
Proof. exact (MK_COMB (@lem1123758 _26411 _26412 P f h) (@lem1123759 _26411 _26412 P f t)). Qed.
Lemma lem1123763 {_26411 _26412 : Type'} (h : _26411) (P : _26412 -> Prop) (f : _26411 -> _26412) (t : list _26411) : (term15 _26411 _26412 P f h t) = (term56 _26411 _26412 h P f t).
Proof. exact (TRANS (@lem1123750 _26411 _26412 h P f t) (@lem1123760 _26411 _26412 h P f t)). Qed.
Lemma lem1123764 {_26411 _26412 : Type'} (h : _26411) (P : _26412 -> Prop) (f : _26411 -> _26412) (t : list _26411) (h1 : (term9 _26411 _26412 P f t) = (term10 _26411 _26412 P f t)) : ((term14 _26411 _26412 P f h t) = (term15 _26411 _26412 P f h t)) = ((term56 _26411 _26412 h P f t) = (term56 _26411 _26412 h P f t)).
Proof. exact (MK_COMB (@lem1123746 _26411 _26412 h P f t h1) (@lem1123763 _26411 _26412 h P f t)). Qed.
Lemma lem1123766 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1123767 (x : Prop) : (x = x) = True.
Proof. exact (@lem1123766 Prop x). Qed.
Lemma lem1123768 {_26411 _26412 : Type'} (h : _26411) (P : _26412 -> Prop) (f : _26411 -> _26412) (t : list _26411) : ((term56 _26411 _26412 h P f t) = (term56 _26411 _26412 h P f t)) = True.
Proof. exact (@lem1123767 (term56 _26411 _26412 h P f t)). Qed.
Lemma lem1123769 {_26411 _26412 : Type'} (h : _26411) (P : _26412 -> Prop) (f : _26411 -> _26412) (t : list _26411) (h1 : (term9 _26411 _26412 P f t) = (term10 _26411 _26412 P f t)) : ((term14 _26411 _26412 P f h t) = (term15 _26411 _26412 P f h t)) = True.
Proof. exact (TRANS (@lem1123764 _26411 _26412 h P f t h1) (@lem1123768 _26411 _26412 h P f t)). Qed.
Lemma lem1123770 {_26411 _26412 : Type'} (h : _26411) (P : _26412 -> Prop) (f : _26411 -> _26412) (t : list _26411) (h1 : (term9 _26411 _26412 P f t) = (term10 _26411 _26412 P f t)) : True = ((term14 _26411 _26412 P f h t) = (term15 _26411 _26412 P f h t)).
Proof. exact (SYM (@lem1123769 _26411 _26412 h P f t h1)). Qed.
Lemma lem1123771 {_26411 _26412 : Type'} (h : _26411) (P : _26412 -> Prop) (f : _26411 -> _26412) (t : list _26411) (h1 : (term9 _26411 _26412 P f t) = (term10 _26411 _26412 P f t)) : (term14 _26411 _26412 P f h t) = (term15 _26411 _26412 P f h t).
Proof. exact (EQ_MP (@lem1123770 _26411 _26412 h P f t h1) (@lem0)). Qed.
Lemma lem1123772 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) (h : _26411) (t : list _26411) : term17 _26411 _26412 P f h t.
Proof. exact (fun h0 : (term9 _26411 _26412 P f t) = (term10 _26411 _26412 P f t) => @lem1123771 _26411 _26412 h P f t h0). Qed.
Lemma lem1123777 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) (h : _26411) : term21 _26411 _26412 P f h.
Proof. exact (fun t : list _26411 => @lem1123772 _26411 _26412 P f h t). Qed.
Lemma lem1123782 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) : term25 _26411 _26412 P f.
Proof. exact (fun h : _26411 => @lem1123777 _26411 _26412 P f h). Qed.
Lemma lem1123783 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) : term27 _26411 _26412 P f.
Proof. exact (conj (@lem1123698 _26411 _26412 P f) (@lem1123782 _26411 _26412 P f)). Qed.
Lemma lem1123784 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) : term32 _26411 _26412 P f.
Proof. exact (@lem1123648 _26411 _26412 P f (@lem1123783 _26411 _26412 P f)). Qed.
Lemma lem1123789 {_26411 _26412 : Type'} (P : _26412 -> Prop) : term62 _26411 _26412 P.
Proof. exact (fun f : _26411 -> _26412 => @lem1123784 _26411 _26412 P f). Qed.
Lemma lem1123794 {_26411 _26412 : Type'} : term63 _26411 _26412.
Proof. exact (fun P : _26412 -> Prop => @lem1123789 _26411 _26412 P). Qed.
