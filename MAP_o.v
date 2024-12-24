Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MAP_o_term_abbrevs.
Require Import o_THM_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1097797_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1118495 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1118496 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (@lem1118495 A P). Qed.
Lemma lem1118497 {A B C : Type'} (g : B -> C) (f : A -> B) : term1 A B C g f.
Proof. exact (@lem1118496 A (term2 A B C g f)). Qed.
Lemma lem1118498 {A B C : Type'} (g : B -> C) (f : A -> B) : (term3 A B C g f) = ((term4 A B C g f) = (term5 A B C g f)).
Proof. exact (eq_refl (term3 A B C g f)). Qed.
Lemma lem1118499 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1118500 {A B C : Type'} (g : B -> C) (f : A -> B) : (term6 A B C g f) = (term7 A B C g f).
Proof. exact (MK_COMB (@lem1118499) (@lem1118498 A B C g f)). Qed.
Lemma lem1118501 {A B C : Type'} (g : B -> C) (f : A -> B) (t : list A) : (term8 A B C g f t) = ((term9 A B C g f t) = (term10 A B C g f t)).
Proof. exact (eq_refl (term8 A B C g f t)). Qed.
Lemma lem1118502 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1118503 {A B C : Type'} (g : B -> C) (f : A -> B) (t : list A) : (term11 A B C g f t) = (term12 A B C g f t).
Proof. exact (MK_COMB (@lem1118502) (@lem1118501 A B C g f t)). Qed.
Lemma lem1118504 {A B C : Type'} (g : B -> C) (f : A -> B) (h : A) (t : list A) : (term13 A B C g f h t) = ((term14 A B C g f h t) = (term15 A B C g f h t)).
Proof. exact (eq_refl (term13 A B C g f h t)). Qed.
Lemma lem1118505 {A B C : Type'} (g : B -> C) (f : A -> B) (h : A) (t : list A) : (term16 A B C g f h t) = (term17 A B C g f h t).
Proof. exact (MK_COMB (@lem1118503 A B C g f t) (@lem1118504 A B C g f h t)). Qed.
Lemma lem1118506 {A B C : Type'} (g : B -> C) (f : A -> B) (h : A) : (term18 A B C g f h) = (term19 A B C g f h).
Proof. exact (fun_ext (fun t : list A => @lem1118505 A B C g f h t)). Qed.
Lemma lem1118507 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1118508 {A B C : Type'} (g : B -> C) (f : A -> B) (h : A) : (term20 A B C g f h) = (term21 A B C g f h).
Proof. exact (MK_COMB (@lem1118507 A) (@lem1118506 A B C g f h)). Qed.
Lemma lem1118509 {A B C : Type'} (g : B -> C) (f : A -> B) : (term22 A B C g f) = (term23 A B C g f).
Proof. exact (fun_ext (fun h : A => @lem1118508 A B C g f h)). Qed.
Lemma lem1118510 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1118511 {A B C : Type'} (g : B -> C) (f : A -> B) : (term24 A B C g f) = (term25 A B C g f).
Proof. exact (MK_COMB (@lem1118510 A) (@lem1118509 A B C g f)). Qed.
Lemma lem1118512 {A B C : Type'} (g : B -> C) (f : A -> B) : (term26 A B C g f) = (term27 A B C g f).
Proof. exact (MK_COMB (@lem1118500 A B C g f) (@lem1118511 A B C g f)). Qed.
Lemma lem1118513 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1118514 {A B C : Type'} (g : B -> C) (f : A -> B) : (term28 A B C g f) = (term29 A B C g f).
Proof. exact (MK_COMB (@lem1118513) (@lem1118512 A B C g f)). Qed.
Lemma lem1118515 {A B C : Type'} (g : B -> C) (f : A -> B) (l : list A) : (term8 A B C g f l) = ((term9 A B C g f l) = (term10 A B C g f l)).
Proof. exact (eq_refl (term8 A B C g f l)). Qed.
Lemma lem1118516 {A B C : Type'} (g : B -> C) (f : A -> B) : (term30 A B C g f) = (term2 A B C g f).
Proof. exact (fun_ext (fun l : list A => @lem1118515 A B C g f l)). Qed.
Lemma lem1118517 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1118518 {A B C : Type'} (g : B -> C) (f : A -> B) : (term31 A B C g f) = (term32 A B C g f).
Proof. exact (MK_COMB (@lem1118517 A) (@lem1118516 A B C g f)). Qed.
Lemma lem1118519 {A B C : Type'} (g : B -> C) (f : A -> B) : (term1 A B C g f) = (term33 A B C g f).
Proof. exact (MK_COMB (@lem1118514 A B C g f) (@lem1118518 A B C g f)). Qed.
Lemma lem1118520 {A B C : Type'} (g : B -> C) (f : A -> B) : term33 A B C g f.
Proof. exact (EQ_MP (@lem1118519 A B C g f) (@lem1118497 A B C g f)). Qed.
Lemma lem1118541 {A B : Type'} : term34 A B.
Proof. exact (proj1 (@lem1097797 A B)). Qed.
Lemma lem1118542 {A B : Type'} (f : A -> B) : term35 A B f.
Proof. exact (@lem1118541 A B f). Qed.
Lemma lem1118543 {A B : Type'} (f : A -> B) : (term35 A B f) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl (term35 A B f)). Qed.
Lemma lem1118548 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1118543 A B f) (@lem1118542 A B f)). Qed.
Lemma lem1118549 {A C : Type'} (f : A -> C) : (@List.map A C f (@nil A)) = (@nil C).
Proof. exact (@lem1118548 A C f). Qed.
Lemma lem1118550 {A B C : Type'} (g : B -> C) (f : A -> B) : (term4 A B C g f) = (@nil C).
Proof. exact (@lem1118549 A C (@o A B C g f)). Qed.
Lemma lem1118551 {C : Type'} : (@eq (list C)) = (@eq (list C)).
Proof. exact (eq_refl (@eq (list C))). Qed.
Lemma lem1118552 {A B C : Type'} (g : B -> C) (f : A -> B) : (term36 A B C g f) = (@eq (list C) (@nil C)).
Proof. exact (MK_COMB (@lem1118551 C) (@lem1118550 A B C g f)). Qed.
Lemma lem1118554 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1118543 A B f) (@lem1118542 A B f)). Qed.
Lemma lem1118555 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (@lem1118554 A B f). Qed.
Lemma lem1118556 {B C : Type'} (g : B -> C) : (@List.map B C g) = (@List.map B C g).
Proof. exact (eq_refl (@List.map B C g)). Qed.
Lemma lem1118557 {A B C : Type'} (f : A -> B) (g : B -> C) : (term5 A B C g f) = (@List.map B C g (@nil B)).
Proof. exact (MK_COMB (@lem1118556 B C g) (@lem1118555 A B f)). Qed.
Lemma lem1118559 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1118543 A B f) (@lem1118542 A B f)). Qed.
Lemma lem1118560 {B C : Type'} (f : B -> C) : (@List.map B C f (@nil B)) = (@nil C).
Proof. exact (@lem1118559 B C f). Qed.
Lemma lem1118561 {B C : Type'} (g : B -> C) : (@List.map B C g (@nil B)) = (@nil C).
Proof. exact (@lem1118560 B C g). Qed.
Lemma lem1118562 {A B C : Type'} (g : B -> C) (f : A -> B) : (term5 A B C g f) = (@nil C).
Proof. exact (TRANS (@lem1118557 A B C f g) (@lem1118561 B C g)). Qed.
Lemma lem1118563 {A B C : Type'} (g : B -> C) (f : A -> B) : ((term4 A B C g f) = (term5 A B C g f)) = ((@nil C) = (@nil C)).
Proof. exact (MK_COMB (@lem1118552 A B C g f) (@lem1118562 A B C g f)). Qed.
Lemma lem1118565 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1118566 {C : Type'} (x : list C) : (x = x) = True.
Proof. exact (@lem1118565 (list C) x). Qed.
Lemma lem1118567 {C : Type'} : ((@nil C) = (@nil C)) = True.
Proof. exact (@lem1118566 C (@nil C)). Qed.
Lemma lem1118568 {A B C : Type'} (g : B -> C) (f : A -> B) : ((term4 A B C g f) = (term5 A B C g f)) = True.
Proof. exact (TRANS (@lem1118563 A B C g f) (@lem1118567 C)). Qed.
Lemma lem1118569 {A B C : Type'} (g : B -> C) (f : A -> B) : True = ((term4 A B C g f) = (term5 A B C g f)).
Proof. exact (SYM (@lem1118568 A B C g f)). Qed.
Lemma lem1118570 {A B C : Type'} (g : B -> C) (f : A -> B) : (term4 A B C g f) = (term5 A B C g f).
Proof. exact (EQ_MP (@lem1118569 A B C g f) (@lem0)). Qed.
Lemma lem1118571 {A B C : Type'} (f : B -> C) : term37 A B C f.
Proof. exact (@lem15456 A B C f). Qed.
Lemma lem1118572 {A B C : Type'} (f : B -> C) : (term37 A B C f) = (term38 A B C f).
Proof. exact (eq_refl (term37 A B C f)). Qed.
Lemma lem1118573 {A B C : Type'} (f : B -> C) : term38 A B C f.
Proof. exact (EQ_MP (@lem1118572 A B C f) (@lem1118571 A B C f)). Qed.
Lemma lem1118574 {A B C : Type'} (f : B -> C) (g : A -> B) : term39 A B C f g.
Proof. exact (@lem1118573 A B C f g). Qed.
Lemma lem1118575 {A B C : Type'} (f : B -> C) (g : A -> B) : (term39 A B C f g) = (term40 A B C f g).
Proof. exact (eq_refl (term39 A B C f g)). Qed.
Lemma lem1118576 {A B C : Type'} (f : B -> C) (g : A -> B) : term40 A B C f g.
Proof. exact (EQ_MP (@lem1118575 A B C f g) (@lem1118574 A B C f g)). Qed.
Lemma lem1118577 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : term41 A B C f g x.
Proof. exact (@lem1118576 A B C f g x). Qed.
Lemma lem1118578 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (term41 A B C f g x) = ((@o A B C f g x) = (term42 A B C f g x)).
Proof. exact (eq_refl (term41 A B C f g x)). Qed.
Lemma lem1118580 {A B : Type'} : term43 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem1118581 {A B : Type'} (f : A -> B) : term44 A B f.
Proof. exact (@lem1118580 A B f). Qed.
Lemma lem1118582 {A B : Type'} (f : A -> B) : (term44 A B f) = (term45 A B f).
Proof. exact (eq_refl (term44 A B f)). Qed.
Lemma lem1118583 {A B : Type'} (f : A -> B) : term45 A B f.
Proof. exact (EQ_MP (@lem1118582 A B f) (@lem1118581 A B f)). Qed.
Lemma lem1118584 {A B : Type'} (f : A -> B) (h : A) : term46 A B f h.
Proof. exact (@lem1118583 A B f h). Qed.
Lemma lem1118585 {A B : Type'} (h : A) (f : A -> B) : (term46 A B f h) = (term47 A B h f).
Proof. exact (eq_refl (term46 A B f h)). Qed.
Lemma lem1118586 {A B : Type'} (h : A) (f : A -> B) : term47 A B h f.
Proof. exact (EQ_MP (@lem1118585 A B h f) (@lem1118584 A B f h)). Qed.
Lemma lem1118587 {A B : Type'} (h : A) (f : A -> B) (t : list A) : term48 A B h f t.
Proof. exact (@lem1118586 A B h f t). Qed.
Lemma lem1118588 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term48 A B h f t) = ((term49 A B f h t) = (term50 A B h f t)).
Proof. exact (eq_refl (term48 A B h f t)). Qed.
Lemma lem1118597 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term49 A B f h t) = (term50 A B h f t).
Proof. exact (EQ_MP (@lem1118588 A B h f t) (@lem1118587 A B h f t)). Qed.
Lemma lem1118598 {A C : Type'} (h : A) (f : A -> C) (t : list A) : (term49 A C f h t) = (term50 A C h f t).
Proof. exact (@lem1118597 A C h f t). Qed.
Lemma lem1118599 {A B C : Type'} (h : A) (g : B -> C) (f : A -> B) (t : list A) : (term14 A B C g f h t) = (term51 A B C h g f t).
Proof. exact (@lem1118598 A C h (@o A B C g f) t). Qed.
Lemma lem1118601 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (@o A B C f g x) = (term42 A B C f g x).
Proof. exact (EQ_MP (@lem1118578 A B C f g x) (@lem1118577 A B C f g x)). Qed.
Lemma lem1118602 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (@o A B C f g x) = (term42 A B C f g x).
Proof. exact (@lem1118601 A B C f g x). Qed.
Lemma lem1118603 {A B C : Type'} (g : B -> C) (f : A -> B) (h : A) : (@o A B C g f h) = (term42 A B C g f h).
Proof. exact (@lem1118602 A B C g f h). Qed.
Lemma lem1118604 {C : Type'} : (@cons C) = (@cons C).
Proof. exact (eq_refl (@cons C)). Qed.
Lemma lem1118605 {A B C : Type'} (g : B -> C) (f : A -> B) (h : A) : (term52 A B C g f h) = (term53 A B C g f h).
Proof. exact (MK_COMB (@lem1118604 C) (@lem1118603 A B C g f h)). Qed.
Lemma lem1118607 {A B C : Type'} (g : B -> C) (f : A -> B) (t : list A) (h1 : (term9 A B C g f t) = (term10 A B C g f t)) : (term9 A B C g f t) = (term10 A B C g f t).
Proof. exact (h1). Qed.
Lemma lem1118608 {A B C : Type'} (h : A) (g : B -> C) (f : A -> B) (t : list A) (h1 : (term9 A B C g f t) = (term10 A B C g f t)) : (term51 A B C h g f t) = (term54 A B C h g f t).
Proof. exact (MK_COMB (@lem1118605 A B C g f h) (@lem1118607 A B C g f t h1)). Qed.
Lemma lem1118609 {A B C : Type'} (h : A) (g : B -> C) (f : A -> B) (t : list A) (h1 : (term9 A B C g f t) = (term10 A B C g f t)) : (term14 A B C g f h t) = (term54 A B C h g f t).
Proof. exact (TRANS (@lem1118599 A B C h g f t) (@lem1118608 A B C h g f t h1)). Qed.
Lemma lem1118610 {C : Type'} : (@eq (list C)) = (@eq (list C)).
Proof. exact (eq_refl (@eq (list C))). Qed.
Lemma lem1118611 {A B C : Type'} (h : A) (g : B -> C) (f : A -> B) (t : list A) (h1 : (term9 A B C g f t) = (term10 A B C g f t)) : (term55 A B C g f h t) = (term56 A B C h g f t).
Proof. exact (MK_COMB (@lem1118610 C) (@lem1118609 A B C h g f t h1)). Qed.
Lemma lem1118613 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term49 A B f h t) = (term50 A B h f t).
Proof. exact (EQ_MP (@lem1118588 A B h f t) (@lem1118587 A B h f t)). Qed.
Lemma lem1118614 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term49 A B f h t) = (term50 A B h f t).
Proof. exact (@lem1118613 A B h f t). Qed.
Lemma lem1118615 {B C : Type'} (g : B -> C) : (@List.map B C g) = (@List.map B C g).
Proof. exact (eq_refl (@List.map B C g)). Qed.
Lemma lem1118616 {A B C : Type'} (g : B -> C) (h : A) (f : A -> B) (t : list A) : (term15 A B C g f h t) = (term57 A B C g h f t).
Proof. exact (MK_COMB (@lem1118615 B C g) (@lem1118614 A B h f t)). Qed.
Lemma lem1118618 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term49 A B f h t) = (term50 A B h f t).
Proof. exact (EQ_MP (@lem1118588 A B h f t) (@lem1118587 A B h f t)). Qed.
Lemma lem1118619 {B C : Type'} (h : B) (f : B -> C) (t : list B) : (term49 B C f h t) = (term50 B C h f t).
Proof. exact (@lem1118618 B C h f t). Qed.
Lemma lem1118620 {A B C : Type'} (h : A) (g : B -> C) (f : A -> B) (t : list A) : (term57 A B C g h f t) = (term54 A B C h g f t).
Proof. exact (@lem1118619 B C (f h) g (@List.map A B f t)). Qed.
Lemma lem1118621 {A B C : Type'} (h : A) (g : B -> C) (f : A -> B) (t : list A) : (term15 A B C g f h t) = (term54 A B C h g f t).
Proof. exact (TRANS (@lem1118616 A B C g h f t) (@lem1118620 A B C h g f t)). Qed.
Lemma lem1118622 {A B C : Type'} (h : A) (g : B -> C) (f : A -> B) (t : list A) (h1 : (term9 A B C g f t) = (term10 A B C g f t)) : ((term14 A B C g f h t) = (term15 A B C g f h t)) = ((term54 A B C h g f t) = (term54 A B C h g f t)).
Proof. exact (MK_COMB (@lem1118611 A B C h g f t h1) (@lem1118621 A B C h g f t)). Qed.
Lemma lem1118624 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1118625 {C : Type'} (x : list C) : (x = x) = True.
Proof. exact (@lem1118624 (list C) x). Qed.
Lemma lem1118626 {A B C : Type'} (h : A) (g : B -> C) (f : A -> B) (t : list A) : ((term54 A B C h g f t) = (term54 A B C h g f t)) = True.
Proof. exact (@lem1118625 C (term54 A B C h g f t)). Qed.
Lemma lem1118627 {A B C : Type'} (h : A) (g : B -> C) (f : A -> B) (t : list A) (h1 : (term9 A B C g f t) = (term10 A B C g f t)) : ((term14 A B C g f h t) = (term15 A B C g f h t)) = True.
Proof. exact (TRANS (@lem1118622 A B C h g f t h1) (@lem1118626 A B C h g f t)). Qed.
Lemma lem1118628 {A B C : Type'} (h : A) (g : B -> C) (f : A -> B) (t : list A) (h1 : (term9 A B C g f t) = (term10 A B C g f t)) : True = ((term14 A B C g f h t) = (term15 A B C g f h t)).
Proof. exact (SYM (@lem1118627 A B C h g f t h1)). Qed.
Lemma lem1118629 {A B C : Type'} (h : A) (g : B -> C) (f : A -> B) (t : list A) (h1 : (term9 A B C g f t) = (term10 A B C g f t)) : (term14 A B C g f h t) = (term15 A B C g f h t).
Proof. exact (EQ_MP (@lem1118628 A B C h g f t h1) (@lem0)). Qed.
Lemma lem1118630 {A B C : Type'} (g : B -> C) (f : A -> B) (h : A) (t : list A) : term17 A B C g f h t.
Proof. exact (fun h0 : (term9 A B C g f t) = (term10 A B C g f t) => @lem1118629 A B C h g f t h0). Qed.
Lemma lem1118635 {A B C : Type'} (g : B -> C) (f : A -> B) (h : A) : term21 A B C g f h.
Proof. exact (fun t : list A => @lem1118630 A B C g f h t). Qed.
Lemma lem1118640 {A B C : Type'} (g : B -> C) (f : A -> B) : term25 A B C g f.
Proof. exact (fun h : A => @lem1118635 A B C g f h). Qed.
Lemma lem1118641 {A B C : Type'} (g : B -> C) (f : A -> B) : term27 A B C g f.
Proof. exact (conj (@lem1118570 A B C g f) (@lem1118640 A B C g f)). Qed.
Lemma lem1118642 {A B C : Type'} (g : B -> C) (f : A -> B) : term32 A B C g f.
Proof. exact (@lem1118520 A B C g f (@lem1118641 A B C g f)). Qed.
Lemma lem1118647 {A B C : Type'} (f : A -> B) : term58 A B C f.
Proof. exact (fun g : B -> C => @lem1118642 A B C g f). Qed.
Lemma lem1118652 {A B C : Type'} : term59 A B C.
Proof. exact (fun f : A -> B => @lem1118647 A B C f). Qed.
