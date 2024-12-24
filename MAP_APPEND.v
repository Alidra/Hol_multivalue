Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MAP_APPEND_term_abbrevs.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1095962_spec.
Require Import thm1097797_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1116560 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1116561 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (@lem1116560 A P). Qed.
Lemma lem1116562 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (@lem1116561 A (term2 A B f)). Qed.
Lemma lem1116563 {A B : Type'} (f : A -> B) : (term3 A B f) = (term4 A B f).
Proof. exact (eq_refl (term3 A B f)). Qed.
Lemma lem1116564 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1116565 {A B : Type'} (f : A -> B) : (term5 A B f) = (term6 A B f).
Proof. exact (MK_COMB (@lem1116564) (@lem1116563 A B f)). Qed.
Lemma lem1116566 {A B : Type'} (t : list A) (f : A -> B) : (term7 A B f t) = (term8 A B t f).
Proof. exact (eq_refl (term7 A B f t)). Qed.
Lemma lem1116567 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1116568 {A B : Type'} (t : list A) (f : A -> B) : (term9 A B f t) = (term10 A B t f).
Proof. exact (MK_COMB (@lem1116567) (@lem1116566 A B t f)). Qed.
Lemma lem1116569 {A B : Type'} (h : A) (t : list A) (f : A -> B) : (term11 A B f h t) = (term12 A B h t f).
Proof. exact (eq_refl (term11 A B f h t)). Qed.
Lemma lem1116570 {A B : Type'} (h : A) (t : list A) (f : A -> B) : (term13 A B f h t) = (term14 A B h t f).
Proof. exact (MK_COMB (@lem1116568 A B t f) (@lem1116569 A B h t f)). Qed.
Lemma lem1116571 {A B : Type'} (h : A) (f : A -> B) : (term15 A B f h) = (term16 A B h f).
Proof. exact (fun_ext (fun t : list A => @lem1116570 A B h t f)). Qed.
Lemma lem1116572 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1116573 {A B : Type'} (h : A) (f : A -> B) : (term17 A B f h) = (term18 A B h f).
Proof. exact (MK_COMB (@lem1116572 A) (@lem1116571 A B h f)). Qed.
Lemma lem1116574 {A B : Type'} (f : A -> B) : (term19 A B f) = (term20 A B f).
Proof. exact (fun_ext (fun h : A => @lem1116573 A B h f)). Qed.
Lemma lem1116575 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1116576 {A B : Type'} (f : A -> B) : (term21 A B f) = (term22 A B f).
Proof. exact (MK_COMB (@lem1116575 A) (@lem1116574 A B f)). Qed.
Lemma lem1116577 {A B : Type'} (f : A -> B) : (term23 A B f) = (term24 A B f).
Proof. exact (MK_COMB (@lem1116565 A B f) (@lem1116576 A B f)). Qed.
Lemma lem1116578 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1116579 {A B : Type'} (f : A -> B) : (term25 A B f) = (term26 A B f).
Proof. exact (MK_COMB (@lem1116578) (@lem1116577 A B f)). Qed.
Lemma lem1116580 {A B : Type'} (l1 : list A) (f : A -> B) : (term7 A B f l1) = (term8 A B l1 f).
Proof. exact (eq_refl (term7 A B f l1)). Qed.
Lemma lem1116581 {A B : Type'} (f : A -> B) : (term27 A B f) = (term2 A B f).
Proof. exact (fun_ext (fun l1 : list A => @lem1116580 A B l1 f)). Qed.
Lemma lem1116582 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1116583 {A B : Type'} (f : A -> B) : (term28 A B f) = (term29 A B f).
Proof. exact (MK_COMB (@lem1116582 A) (@lem1116581 A B f)). Qed.
Lemma lem1116584 {A B : Type'} (f : A -> B) : (term1 A B f) = (term30 A B f).
Proof. exact (MK_COMB (@lem1116579 A B f) (@lem1116583 A B f)). Qed.
Lemma lem1116585 {A B : Type'} (f : A -> B) : term30 A B f.
Proof. exact (EQ_MP (@lem1116584 A B f) (@lem1116562 A B f)). Qed.
Lemma lem1116586 {A B : Type'} (t : list A) (f : A -> B) (h1 : term8 A B t f) : term8 A B t f.
Proof. exact (h1). Qed.
Lemma lem1116597 {A : Type'} : term31 A.
Proof. exact (proj1 (@lem1095962 A)). Qed.
Lemma lem1116598 {A : Type'} (l : list A) : term32 A l.
Proof. exact (@lem1116597 A l). Qed.
Lemma lem1116599 {A : Type'} (l : list A) : (term32 A l) = ((@List.app A (@nil A) l) = l).
Proof. exact (eq_refl (term32 A l)). Qed.
Lemma lem1116611 {A B : Type'} : term33 A B.
Proof. exact (proj1 (@lem1097797 A B)). Qed.
Lemma lem1116612 {A B : Type'} (f : A -> B) : term34 A B f.
Proof. exact (@lem1116611 A B f). Qed.
Lemma lem1116613 {A B : Type'} (f : A -> B) : (term34 A B f) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl (term34 A B f)). Qed.
Lemma lem1116622 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (EQ_MP (@lem1116599 A l) (@lem1116598 A l)). Qed.
Lemma lem1116623 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (@lem1116622 A l). Qed.
Lemma lem1116624 {A : Type'} (l2 : list A) : (@List.app A (@nil A) l2) = l2.
Proof. exact (@lem1116623 A l2). Qed.
Lemma lem1116625 {A B : Type'} (f : A -> B) : (@List.map A B f) = (@List.map A B f).
Proof. exact (eq_refl (@List.map A B f)). Qed.
Lemma lem1116626 {A B : Type'} (f : A -> B) (l2 : list A) : (term35 A B f l2) = (@List.map A B f l2).
Proof. exact (MK_COMB (@lem1116625 A B f) (@lem1116624 A l2)). Qed.
Lemma lem1116627 {B : Type'} : (@eq (list B)) = (@eq (list B)).
Proof. exact (eq_refl (@eq (list B))). Qed.
Lemma lem1116628 {A B : Type'} (f : A -> B) (l2 : list A) : (term36 A B f l2) = (term37 A B f l2).
Proof. exact (MK_COMB (@lem1116627 B) (@lem1116626 A B f l2)). Qed.
Lemma lem1116630 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1116613 A B f) (@lem1116612 A B f)). Qed.
Lemma lem1116631 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (@lem1116630 A B f). Qed.
Lemma lem1116632 {B : Type'} : (@List.app B) = (@List.app B).
Proof. exact (eq_refl (@List.app B)). Qed.
Lemma lem1116633 {A B : Type'} (f : A -> B) : (term38 A B f) = (@List.app B (@nil B)).
Proof. exact (MK_COMB (@lem1116632 B) (@lem1116631 A B f)). Qed.
Lemma lem1116634 {A B : Type'} (f : A -> B) (l2 : list A) : (@List.map A B f l2) = (@List.map A B f l2).
Proof. exact (eq_refl (@List.map A B f l2)). Qed.
Lemma lem1116635 {A B : Type'} (f : A -> B) (l2 : list A) : (term39 A B f l2) = (term40 A B f l2).
Proof. exact (MK_COMB (@lem1116633 A B f) (@lem1116634 A B f l2)). Qed.
Lemma lem1116637 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (EQ_MP (@lem1116599 A l) (@lem1116598 A l)). Qed.
Lemma lem1116638 {B : Type'} (l : list B) : (@List.app B (@nil B) l) = l.
Proof. exact (@lem1116637 B l). Qed.
Lemma lem1116639 {A B : Type'} (f : A -> B) (l2 : list A) : (term40 A B f l2) = (@List.map A B f l2).
Proof. exact (@lem1116638 B (@List.map A B f l2)). Qed.
Lemma lem1116640 {A B : Type'} (f : A -> B) (l2 : list A) : (term39 A B f l2) = (@List.map A B f l2).
Proof. exact (TRANS (@lem1116635 A B f l2) (@lem1116639 A B f l2)). Qed.
Lemma lem1116641 {A B : Type'} (f : A -> B) (l2 : list A) : ((term35 A B f l2) = (term39 A B f l2)) = ((@List.map A B f l2) = (@List.map A B f l2)).
Proof. exact (MK_COMB (@lem1116628 A B f l2) (@lem1116640 A B f l2)). Qed.
Lemma lem1116643 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1116644 {B : Type'} (x : list B) : (x = x) = True.
Proof. exact (@lem1116643 (list B) x). Qed.
Lemma lem1116645 {A B : Type'} (f : A -> B) (l2 : list A) : ((@List.map A B f l2) = (@List.map A B f l2)) = True.
Proof. exact (@lem1116644 B (@List.map A B f l2)). Qed.
Lemma lem1116646 {A B : Type'} (f : A -> B) (l2 : list A) : ((term35 A B f l2) = (term39 A B f l2)) = True.
Proof. exact (TRANS (@lem1116641 A B f l2) (@lem1116645 A B f l2)). Qed.
Lemma lem1116647 {A B : Type'} (f : A -> B) : (term41 A B f) = (term42 A).
Proof. exact (fun_ext (fun l2 : list A => @lem1116646 A B f l2)). Qed.
Lemma lem1116648 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1116649 {A B : Type'} (f : A -> B) : (term4 A B f) = (term43 A).
Proof. exact (MK_COMB (@lem1116648 A) (@lem1116647 A B f)). Qed.
Lemma lem1116651 {A : Type'} (t : Prop) : (term44 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1116652 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (@lem1116651 (list A) t). Qed.
Lemma lem1116653 {A : Type'} : (term43 A) = True.
Proof. exact (@lem1116652 A True). Qed.
Lemma lem1116654 {A B : Type'} (f : A -> B) : (term4 A B f) = True.
Proof. exact (TRANS (@lem1116649 A B f) (@lem1116653 A)). Qed.
Lemma lem1116655 {A B : Type'} (f : A -> B) : True = (term4 A B f).
Proof. exact (SYM (@lem1116654 A B f)). Qed.
Lemma lem1116656 {A B : Type'} (f : A -> B) : term4 A B f.
Proof. exact (EQ_MP (@lem1116655 A B f) (@lem0)). Qed.
Lemma lem1116657 {A : Type'} : term46 A.
Proof. exact (proj2 (@lem1095962 A)). Qed.
Lemma lem1116658 {A : Type'} (h : A) : term47 A h.
Proof. exact (@lem1116657 A h). Qed.
Lemma lem1116659 {A : Type'} (h : A) : (term47 A h) = (term48 A h).
Proof. exact (eq_refl (term47 A h)). Qed.
Lemma lem1116660 {A : Type'} (h : A) : term48 A h.
Proof. exact (EQ_MP (@lem1116659 A h) (@lem1116658 A h)). Qed.
Lemma lem1116661 {A : Type'} (h : A) (t : list A) : term49 A h t.
Proof. exact (@lem1116660 A h t). Qed.
Lemma lem1116662 {A : Type'} (h : A) (t : list A) : (term49 A h t) = (term50 A h t).
Proof. exact (eq_refl (term49 A h t)). Qed.
Lemma lem1116663 {A : Type'} (h : A) (t : list A) : term50 A h t.
Proof. exact (EQ_MP (@lem1116662 A h t) (@lem1116661 A h t)). Qed.
Lemma lem1116664 {A : Type'} (h : A) (t : list A) (l : list A) : term51 A h t l.
Proof. exact (@lem1116663 A h t l). Qed.
Lemma lem1116665 {A : Type'} (h : A) (t : list A) (l : list A) : (term51 A h t l) = ((term52 A h t l) = (term53 A h t l)).
Proof. exact (eq_refl (term51 A h t l)). Qed.
Lemma lem1116671 {A B : Type'} : term54 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem1116672 {A B : Type'} (f : A -> B) : term55 A B f.
Proof. exact (@lem1116671 A B f). Qed.
Lemma lem1116673 {A B : Type'} (f : A -> B) : (term55 A B f) = (term56 A B f).
Proof. exact (eq_refl (term55 A B f)). Qed.
Lemma lem1116674 {A B : Type'} (f : A -> B) : term56 A B f.
Proof. exact (EQ_MP (@lem1116673 A B f) (@lem1116672 A B f)). Qed.
Lemma lem1116675 {A B : Type'} (f : A -> B) (h : A) : term57 A B f h.
Proof. exact (@lem1116674 A B f h). Qed.
Lemma lem1116676 {A B : Type'} (h : A) (f : A -> B) : (term57 A B f h) = (term58 A B h f).
Proof. exact (eq_refl (term57 A B f h)). Qed.
Lemma lem1116677 {A B : Type'} (h : A) (f : A -> B) : term58 A B h f.
Proof. exact (EQ_MP (@lem1116676 A B h f) (@lem1116675 A B f h)). Qed.
Lemma lem1116678 {A B : Type'} (h : A) (f : A -> B) (t : list A) : term59 A B h f t.
Proof. exact (@lem1116677 A B h f t). Qed.
Lemma lem1116679 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term59 A B h f t) = ((term60 A B f h t) = (term61 A B h f t)).
Proof. exact (eq_refl (term59 A B h f t)). Qed.
Lemma lem1116685 {A B : Type'} (l2 : list A) (t : list A) (f : A -> B) (h1 : term8 A B t f) : term62 A B t f l2.
Proof. exact (@lem1116586 A B t f h1 l2). Qed.
Lemma lem1116686 {A B : Type'} (t : list A) (f : A -> B) (l2 : list A) : (term62 A B t f l2) = ((term63 A B f t l2) = (term64 A B t f l2)).
Proof. exact (eq_refl (term62 A B t f l2)). Qed.
Lemma lem1116695 {A : Type'} (h : A) (t : list A) (l : list A) : (term52 A h t l) = (term53 A h t l).
Proof. exact (EQ_MP (@lem1116665 A h t l) (@lem1116664 A h t l)). Qed.
Lemma lem1116696 {A : Type'} (h : A) (t : list A) (l : list A) : (term52 A h t l) = (term53 A h t l).
Proof. exact (@lem1116695 A h t l). Qed.
Lemma lem1116697 {A : Type'} (h : A) (t : list A) (l2 : list A) : (term52 A h t l2) = (term53 A h t l2).
Proof. exact (@lem1116696 A h t l2). Qed.
Lemma lem1116698 {A B : Type'} (f : A -> B) : (@List.map A B f) = (@List.map A B f).
Proof. exact (eq_refl (@List.map A B f)). Qed.
Lemma lem1116699 {A B : Type'} (f : A -> B) (h : A) (t : list A) (l2 : list A) : (term65 A B f h t l2) = (term66 A B f h t l2).
Proof. exact (MK_COMB (@lem1116698 A B f) (@lem1116697 A h t l2)). Qed.
Lemma lem1116701 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term60 A B f h t) = (term61 A B h f t).
Proof. exact (EQ_MP (@lem1116679 A B h f t) (@lem1116678 A B h f t)). Qed.
Lemma lem1116702 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term60 A B f h t) = (term61 A B h f t).
Proof. exact (@lem1116701 A B h f t). Qed.
Lemma lem1116703 {A B : Type'} (h : A) (f : A -> B) (t : list A) (l2 : list A) : (term66 A B f h t l2) = (term67 A B h f t l2).
Proof. exact (@lem1116702 A B h f (@List.app A t l2)). Qed.
Lemma lem1116705 {A B : Type'} (l2 : list A) (t : list A) (f : A -> B) (h1 : term8 A B t f) : (term63 A B f t l2) = (term64 A B t f l2).
Proof. exact (EQ_MP (@lem1116686 A B t f l2) (@lem1116685 A B l2 t f h1)). Qed.
Lemma lem1116706 {A B : Type'} (l2 : list A) (t : list A) (f : A -> B) (h1 : term8 A B t f) : (term63 A B f t l2) = (term64 A B t f l2).
Proof. exact (@lem1116705 A B l2 t f h1). Qed.
Lemma lem1116707 {A B : Type'} (f : A -> B) (h : A) : (term68 A B f h) = (term68 A B f h).
Proof. exact (eq_refl (term68 A B f h)). Qed.
Lemma lem1116708 {A B : Type'} (h : A) (l2 : list A) (t : list A) (f : A -> B) (h1 : term8 A B t f) : (term67 A B h f t l2) = (term69 A B h t f l2).
Proof. exact (MK_COMB (@lem1116707 A B f h) (@lem1116706 A B l2 t f h1)). Qed.
Lemma lem1116709 {A B : Type'} (h : A) (l2 : list A) (t : list A) (f : A -> B) (h1 : term8 A B t f) : (term66 A B f h t l2) = (term69 A B h t f l2).
Proof. exact (TRANS (@lem1116703 A B h f t l2) (@lem1116708 A B h l2 t f h1)). Qed.
Lemma lem1116710 {A B : Type'} (h : A) (l2 : list A) (t : list A) (f : A -> B) (h1 : term8 A B t f) : (term65 A B f h t l2) = (term69 A B h t f l2).
Proof. exact (TRANS (@lem1116699 A B f h t l2) (@lem1116709 A B h l2 t f h1)). Qed.
Lemma lem1116711 {B : Type'} : (@eq (list B)) = (@eq (list B)).
Proof. exact (eq_refl (@eq (list B))). Qed.
Lemma lem1116712 {A B : Type'} (h : A) (l2 : list A) (t : list A) (f : A -> B) (h1 : term8 A B t f) : (term70 A B f h t l2) = (term71 A B h t f l2).
Proof. exact (MK_COMB (@lem1116711 B) (@lem1116710 A B h l2 t f h1)). Qed.
Lemma lem1116714 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term60 A B f h t) = (term61 A B h f t).
Proof. exact (EQ_MP (@lem1116679 A B h f t) (@lem1116678 A B h f t)). Qed.
Lemma lem1116715 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term60 A B f h t) = (term61 A B h f t).
Proof. exact (@lem1116714 A B h f t). Qed.
Lemma lem1116716 {B : Type'} : (@List.app B) = (@List.app B).
Proof. exact (eq_refl (@List.app B)). Qed.
Lemma lem1116717 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term72 A B f h t) = (term73 A B h f t).
Proof. exact (MK_COMB (@lem1116716 B) (@lem1116715 A B h f t)). Qed.
Lemma lem1116718 {A B : Type'} (f : A -> B) (l2 : list A) : (@List.map A B f l2) = (@List.map A B f l2).
Proof. exact (eq_refl (@List.map A B f l2)). Qed.
Lemma lem1116719 {A B : Type'} (h : A) (t : list A) (f : A -> B) (l2 : list A) : (term74 A B h t f l2) = (term75 A B h t f l2).
Proof. exact (MK_COMB (@lem1116717 A B h f t) (@lem1116718 A B f l2)). Qed.
Lemma lem1116721 {A : Type'} (h : A) (t : list A) (l : list A) : (term52 A h t l) = (term53 A h t l).
Proof. exact (EQ_MP (@lem1116665 A h t l) (@lem1116664 A h t l)). Qed.
Lemma lem1116722 {B : Type'} (h : B) (t : list B) (l : list B) : (term52 B h t l) = (term53 B h t l).
Proof. exact (@lem1116721 B h t l). Qed.
Lemma lem1116723 {A B : Type'} (h : A) (t : list A) (f : A -> B) (l2 : list A) : (term75 A B h t f l2) = (term69 A B h t f l2).
Proof. exact (@lem1116722 B (f h) (@List.map A B f t) (@List.map A B f l2)). Qed.
Lemma lem1116724 {A B : Type'} (h : A) (t : list A) (f : A -> B) (l2 : list A) : (term74 A B h t f l2) = (term69 A B h t f l2).
Proof. exact (TRANS (@lem1116719 A B h t f l2) (@lem1116723 A B h t f l2)). Qed.
Lemma lem1116725 {A B : Type'} (h : A) (l2 : list A) (t : list A) (f : A -> B) (h1 : term8 A B t f) : ((term65 A B f h t l2) = (term74 A B h t f l2)) = ((term69 A B h t f l2) = (term69 A B h t f l2)).
Proof. exact (MK_COMB (@lem1116712 A B h l2 t f h1) (@lem1116724 A B h t f l2)). Qed.
Lemma lem1116727 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1116728 {B : Type'} (x : list B) : (x = x) = True.
Proof. exact (@lem1116727 (list B) x). Qed.
Lemma lem1116729 {A B : Type'} (h : A) (t : list A) (f : A -> B) (l2 : list A) : ((term69 A B h t f l2) = (term69 A B h t f l2)) = True.
Proof. exact (@lem1116728 B (term69 A B h t f l2)). Qed.
Lemma lem1116730 {A B : Type'} (h : A) (l2 : list A) (t : list A) (f : A -> B) (h1 : term8 A B t f) : ((term65 A B f h t l2) = (term74 A B h t f l2)) = True.
Proof. exact (TRANS (@lem1116725 A B h l2 t f h1) (@lem1116729 A B h t f l2)). Qed.
Lemma lem1116731 {A B : Type'} (h : A) (t : list A) (f : A -> B) (h1 : term8 A B t f) : (term76 A B h t f) = (term42 A).
Proof. exact (fun_ext (fun l2 : list A => @lem1116730 A B h l2 t f h1)). Qed.
Lemma lem1116732 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1116733 {A B : Type'} (h : A) (t : list A) (f : A -> B) (h1 : term8 A B t f) : (term12 A B h t f) = (term43 A).
Proof. exact (MK_COMB (@lem1116732 A) (@lem1116731 A B h t f h1)). Qed.
Lemma lem1116735 {A : Type'} (t : Prop) : (term44 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1116736 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (@lem1116735 (list A) t). Qed.
Lemma lem1116737 {A : Type'} : (term43 A) = True.
Proof. exact (@lem1116736 A True). Qed.
Lemma lem1116738 {A B : Type'} (h : A) (t : list A) (f : A -> B) (h1 : term8 A B t f) : (term12 A B h t f) = True.
Proof. exact (TRANS (@lem1116733 A B h t f h1) (@lem1116737 A)). Qed.
Lemma lem1116739 {A B : Type'} (h : A) (t : list A) (f : A -> B) (h1 : term8 A B t f) : True = (term12 A B h t f).
Proof. exact (SYM (@lem1116738 A B h t f h1)). Qed.
Lemma lem1116740 {A B : Type'} (h : A) (t : list A) (f : A -> B) (h1 : term8 A B t f) : term12 A B h t f.
Proof. exact (EQ_MP (@lem1116739 A B h t f h1) (@lem0)). Qed.
Lemma lem1116741 {A B : Type'} (h : A) (t : list A) (f : A -> B) : term14 A B h t f.
Proof. exact (fun h0 : term8 A B t f => @lem1116740 A B h t f h0). Qed.
Lemma lem1116746 {A B : Type'} (h : A) (f : A -> B) : term18 A B h f.
Proof. exact (fun t : list A => @lem1116741 A B h t f). Qed.
Lemma lem1116751 {A B : Type'} (f : A -> B) : term22 A B f.
Proof. exact (fun h : A => @lem1116746 A B h f). Qed.
Lemma lem1116752 {A B : Type'} (f : A -> B) : term24 A B f.
Proof. exact (conj (@lem1116656 A B f) (@lem1116751 A B f)). Qed.
Lemma lem1116753 {A B : Type'} (f : A -> B) : term29 A B f.
Proof. exact (@lem1116585 A B f (@lem1116752 A B f)). Qed.
Lemma lem1116758 {A B : Type'} : term77 A B.
Proof. exact (fun f : A -> B => @lem1116753 A B f). Qed.
