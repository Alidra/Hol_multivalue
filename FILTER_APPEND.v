Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FILTER_APPEND_term_abbrevs.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1095962_spec.
Require Import thm1106562_spec.
Require Import thm1106563_spec.
Require Import thm1106571_spec.
Require Import thm1106572_spec.
Require Import thm12653_spec.
Require Import thm13473_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem1147570 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1147571 {_27012 : Type'} (P : type1143 _27012) : term0 _27012 P.
Proof. exact (@lem1147570 _27012 P). Qed.
Lemma lem1147572 {_27012 : Type'} (P : _27012 -> Prop) : term1 _27012 P.
Proof. exact (@lem1147571 _27012 (term2 _27012 P)). Qed.
Lemma lem1147573 {_27012 : Type'} (P : _27012 -> Prop) : (term3 _27012 P) = (term4 _27012 P).
Proof. exact (eq_refl (term3 _27012 P)). Qed.
Lemma lem1147574 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1147575 {_27012 : Type'} (P : _27012 -> Prop) : (term5 _27012 P) = (term6 _27012 P).
Proof. exact (MK_COMB (@lem1147574) (@lem1147573 _27012 P)). Qed.
Lemma lem1147576 {_27012 : Type'} (t : list _27012) (P : _27012 -> Prop) : (term7 _27012 P t) = (term8 _27012 t P).
Proof. exact (eq_refl (term7 _27012 P t)). Qed.
Lemma lem1147577 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1147578 {_27012 : Type'} (t : list _27012) (P : _27012 -> Prop) : (term9 _27012 P t) = (term10 _27012 t P).
Proof. exact (MK_COMB (@lem1147577) (@lem1147576 _27012 t P)). Qed.
Lemma lem1147579 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) : (term11 _27012 P h t) = (term12 _27012 h t P).
Proof. exact (eq_refl (term11 _27012 P h t)). Qed.
Lemma lem1147580 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) : (term13 _27012 P h t) = (term14 _27012 h t P).
Proof. exact (MK_COMB (@lem1147578 _27012 t P) (@lem1147579 _27012 h t P)). Qed.
Lemma lem1147581 {_27012 : Type'} (h : _27012) (P : _27012 -> Prop) : (term15 _27012 P h) = (term16 _27012 h P).
Proof. exact (fun_ext (fun t : list _27012 => @lem1147580 _27012 h t P)). Qed.
Lemma lem1147582 {_27012 : Type'} : (@all (list _27012)) = (@all (list _27012)).
Proof. exact (eq_refl (@all (list _27012))). Qed.
Lemma lem1147583 {_27012 : Type'} (h : _27012) (P : _27012 -> Prop) : (term17 _27012 P h) = (term18 _27012 h P).
Proof. exact (MK_COMB (@lem1147582 _27012) (@lem1147581 _27012 h P)). Qed.
Lemma lem1147584 {_27012 : Type'} (P : _27012 -> Prop) : (term19 _27012 P) = (term20 _27012 P).
Proof. exact (fun_ext (fun h : _27012 => @lem1147583 _27012 h P)). Qed.
Lemma lem1147585 {_27012 : Type'} : (@all _27012) = (@all _27012).
Proof. exact (eq_refl (@all _27012)). Qed.
Lemma lem1147586 {_27012 : Type'} (P : _27012 -> Prop) : (term21 _27012 P) = (term22 _27012 P).
Proof. exact (MK_COMB (@lem1147585 _27012) (@lem1147584 _27012 P)). Qed.
Lemma lem1147587 {_27012 : Type'} (P : _27012 -> Prop) : (term23 _27012 P) = (term24 _27012 P).
Proof. exact (MK_COMB (@lem1147575 _27012 P) (@lem1147586 _27012 P)). Qed.
Lemma lem1147588 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1147589 {_27012 : Type'} (P : _27012 -> Prop) : (term25 _27012 P) = (term26 _27012 P).
Proof. exact (MK_COMB (@lem1147588) (@lem1147587 _27012 P)). Qed.
Lemma lem1147590 {_27012 : Type'} (l1 : list _27012) (P : _27012 -> Prop) : (term7 _27012 P l1) = (term8 _27012 l1 P).
Proof. exact (eq_refl (term7 _27012 P l1)). Qed.
Lemma lem1147591 {_27012 : Type'} (P : _27012 -> Prop) : (term27 _27012 P) = (term2 _27012 P).
Proof. exact (fun_ext (fun l1 : list _27012 => @lem1147590 _27012 l1 P)). Qed.
Lemma lem1147592 {_27012 : Type'} : (@all (list _27012)) = (@all (list _27012)).
Proof. exact (eq_refl (@all (list _27012))). Qed.
Lemma lem1147593 {_27012 : Type'} (P : _27012 -> Prop) : (term28 _27012 P) = (term29 _27012 P).
Proof. exact (MK_COMB (@lem1147592 _27012) (@lem1147591 _27012 P)). Qed.
Lemma lem1147594 {_27012 : Type'} (P : _27012 -> Prop) : (term1 _27012 P) = (term30 _27012 P).
Proof. exact (MK_COMB (@lem1147589 _27012 P) (@lem1147593 _27012 P)). Qed.
Lemma lem1147595 {_27012 : Type'} (P : _27012 -> Prop) : term30 _27012 P.
Proof. exact (EQ_MP (@lem1147594 _27012 P) (@lem1147572 _27012 P)). Qed.
Lemma lem1147596 {_27012 : Type'} (t : list _27012) (P : _27012 -> Prop) (h1 : term8 _27012 t P) : term8 _27012 t P.
Proof. exact (h1). Qed.
Lemma lem1147607 {A : Type'} : term31 A.
Proof. exact (proj1 (@lem1095962 A)). Qed.
Lemma lem1147608 {A : Type'} (l : list A) : term32 A l.
Proof. exact (@lem1147607 A l). Qed.
Lemma lem1147609 {A : Type'} (l : list A) : (term32 A l) = ((@List.app A (@nil A) l) = l).
Proof. exact (eq_refl (term32 A l)). Qed.
Lemma lem1147620 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (EQ_MP (@lem1147609 A l) (@lem1147608 A l)). Qed.
Lemma lem1147621 {_27012 : Type'} (l : list _27012) : (@List.app _27012 (@nil _27012) l) = l.
Proof. exact (@lem1147620 _27012 l). Qed.
Lemma lem1147622 {_27012 : Type'} (l2 : list _27012) : (@List.app _27012 (@nil _27012) l2) = l2.
Proof. exact (@lem1147621 _27012 l2). Qed.
Lemma lem1147623 {_27012 : Type'} (P : _27012 -> Prop) : (@FILTER _27012 P) = (@FILTER _27012 P).
Proof. exact (eq_refl (@FILTER _27012 P)). Qed.
Lemma lem1147624 {_27012 : Type'} (P : _27012 -> Prop) (l2 : list _27012) : (term33 _27012 P l2) = (@FILTER _27012 P l2).
Proof. exact (MK_COMB (@lem1147623 _27012 P) (@lem1147622 _27012 l2)). Qed.
Lemma lem1147625 {_27012 : Type'} : (@eq (list _27012)) = (@eq (list _27012)).
Proof. exact (eq_refl (@eq (list _27012))). Qed.
Lemma lem1147626 {_27012 : Type'} (P : _27012 -> Prop) (l2 : list _27012) : (term34 _27012 P l2) = (term35 _27012 P l2).
Proof. exact (MK_COMB (@lem1147625 _27012) (@lem1147624 _27012 P l2)). Qed.
Lemma lem1147628 {_25594 : Type'} (P : _25594 -> Prop) : (@FILTER _25594 P (@nil _25594)) = (@nil _25594).
Proof. exact (EQ_MP (@lem1106563 _25594 P) (@lem1106562 _25594 P)). Qed.
Lemma lem1147629 {_27012 : Type'} (P : _27012 -> Prop) : (@FILTER _27012 P (@nil _27012)) = (@nil _27012).
Proof. exact (@lem1147628 _27012 P). Qed.
Lemma lem1147630 {_27012 : Type'} : (@List.app _27012) = (@List.app _27012).
Proof. exact (eq_refl (@List.app _27012)). Qed.
Lemma lem1147631 {_27012 : Type'} (P : _27012 -> Prop) : (term36 _27012 P) = (@List.app _27012 (@nil _27012)).
Proof. exact (MK_COMB (@lem1147630 _27012) (@lem1147629 _27012 P)). Qed.
Lemma lem1147632 {_27012 : Type'} (P : _27012 -> Prop) (l2 : list _27012) : (@FILTER _27012 P l2) = (@FILTER _27012 P l2).
Proof. exact (eq_refl (@FILTER _27012 P l2)). Qed.
Lemma lem1147633 {_27012 : Type'} (P : _27012 -> Prop) (l2 : list _27012) : (term37 _27012 P l2) = (term38 _27012 P l2).
Proof. exact (MK_COMB (@lem1147631 _27012 P) (@lem1147632 _27012 P l2)). Qed.
Lemma lem1147635 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (EQ_MP (@lem1147609 A l) (@lem1147608 A l)). Qed.
Lemma lem1147636 {_27012 : Type'} (l : list _27012) : (@List.app _27012 (@nil _27012) l) = l.
Proof. exact (@lem1147635 _27012 l). Qed.
Lemma lem1147637 {_27012 : Type'} (P : _27012 -> Prop) (l2 : list _27012) : (term38 _27012 P l2) = (@FILTER _27012 P l2).
Proof. exact (@lem1147636 _27012 (@FILTER _27012 P l2)). Qed.
Lemma lem1147638 {_27012 : Type'} (P : _27012 -> Prop) (l2 : list _27012) : (term37 _27012 P l2) = (@FILTER _27012 P l2).
Proof. exact (TRANS (@lem1147633 _27012 P l2) (@lem1147637 _27012 P l2)). Qed.
Lemma lem1147639 {_27012 : Type'} (P : _27012 -> Prop) (l2 : list _27012) : ((term33 _27012 P l2) = (term37 _27012 P l2)) = ((@FILTER _27012 P l2) = (@FILTER _27012 P l2)).
Proof. exact (MK_COMB (@lem1147626 _27012 P l2) (@lem1147638 _27012 P l2)). Qed.
Lemma lem1147641 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1147642 {_27012 : Type'} (x : list _27012) : (x = x) = True.
Proof. exact (@lem1147641 (list _27012) x). Qed.
Lemma lem1147643 {_27012 : Type'} (P : _27012 -> Prop) (l2 : list _27012) : ((@FILTER _27012 P l2) = (@FILTER _27012 P l2)) = True.
Proof. exact (@lem1147642 _27012 (@FILTER _27012 P l2)). Qed.
Lemma lem1147644 {_27012 : Type'} (P : _27012 -> Prop) (l2 : list _27012) : ((term33 _27012 P l2) = (term37 _27012 P l2)) = True.
Proof. exact (TRANS (@lem1147639 _27012 P l2) (@lem1147643 _27012 P l2)). Qed.
Lemma lem1147645 {_27012 : Type'} (P : _27012 -> Prop) : (term39 _27012 P) = (term40 _27012).
Proof. exact (fun_ext (fun l2 : list _27012 => @lem1147644 _27012 P l2)). Qed.
Lemma lem1147646 {_27012 : Type'} : (@all (list _27012)) = (@all (list _27012)).
Proof. exact (eq_refl (@all (list _27012))). Qed.
Lemma lem1147647 {_27012 : Type'} (P : _27012 -> Prop) : (term4 _27012 P) = (term41 _27012).
Proof. exact (MK_COMB (@lem1147646 _27012) (@lem1147645 _27012 P)). Qed.
Lemma lem1147649 {A : Type'} (t : Prop) : (term42 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1147650 {_27012 : Type'} (t : Prop) : (term43 _27012 t) = t.
Proof. exact (@lem1147649 (list _27012) t). Qed.
Lemma lem1147651 {_27012 : Type'} : (term41 _27012) = True.
Proof. exact (@lem1147650 _27012 True). Qed.
Lemma lem1147652 {_27012 : Type'} (P : _27012 -> Prop) : (term4 _27012 P) = True.
Proof. exact (TRANS (@lem1147647 _27012 P) (@lem1147651 _27012)). Qed.
Lemma lem1147653 {_27012 : Type'} (P : _27012 -> Prop) : True = (term4 _27012 P).
Proof. exact (SYM (@lem1147652 _27012 P)). Qed.
Lemma lem1147654 {_27012 : Type'} (P : _27012 -> Prop) : term4 _27012 P.
Proof. exact (EQ_MP (@lem1147653 _27012 P) (@lem0)). Qed.
Lemma lem1147655 {A : Type'} : term44 A.
Proof. exact (proj2 (@lem1095962 A)). Qed.
Lemma lem1147656 {A : Type'} (h : A) : term45 A h.
Proof. exact (@lem1147655 A h). Qed.
Lemma lem1147657 {A : Type'} (h : A) : (term45 A h) = (term46 A h).
Proof. exact (eq_refl (term45 A h)). Qed.
Lemma lem1147658 {A : Type'} (h : A) : term46 A h.
Proof. exact (EQ_MP (@lem1147657 A h) (@lem1147656 A h)). Qed.
Lemma lem1147659 {A : Type'} (h : A) (t : list A) : term47 A h t.
Proof. exact (@lem1147658 A h t). Qed.
Lemma lem1147660 {A : Type'} (h : A) (t : list A) : (term47 A h t) = (term48 A h t).
Proof. exact (eq_refl (term47 A h t)). Qed.
Lemma lem1147661 {A : Type'} (h : A) (t : list A) : term48 A h t.
Proof. exact (EQ_MP (@lem1147660 A h t) (@lem1147659 A h t)). Qed.
Lemma lem1147662 {A : Type'} (h : A) (t : list A) (l : list A) : term49 A h t l.
Proof. exact (@lem1147661 A h t l). Qed.
Lemma lem1147663 {A : Type'} (h : A) (t : list A) (l : list A) : (term49 A h t l) = ((term50 A h t l) = (term51 A h t l)).
Proof. exact (eq_refl (term49 A h t l)). Qed.
Lemma lem1147671 {_27012 : Type'} (l2 : list _27012) (t : list _27012) (P : _27012 -> Prop) (h1 : term8 _27012 t P) : term52 _27012 t P l2.
Proof. exact (@lem1147596 _27012 t P h1 l2). Qed.
Lemma lem1147672 {_27012 : Type'} (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : (term52 _27012 t P l2) = ((term53 _27012 P t l2) = (term54 _27012 t P l2)).
Proof. exact (eq_refl (term52 _27012 t P l2)). Qed.
Lemma lem1147681 {A : Type'} (h : A) (t : list A) (l : list A) : (term50 A h t l) = (term51 A h t l).
Proof. exact (EQ_MP (@lem1147663 A h t l) (@lem1147662 A h t l)). Qed.
Lemma lem1147682 {_27012 : Type'} (h : _27012) (t : list _27012) (l : list _27012) : (term50 _27012 h t l) = (term51 _27012 h t l).
Proof. exact (@lem1147681 _27012 h t l). Qed.
Lemma lem1147683 {_27012 : Type'} (h : _27012) (t : list _27012) (l2 : list _27012) : (term50 _27012 h t l2) = (term51 _27012 h t l2).
Proof. exact (@lem1147682 _27012 h t l2). Qed.
Lemma lem1147684 {_27012 : Type'} (P : _27012 -> Prop) : (@FILTER _27012 P) = (@FILTER _27012 P).
Proof. exact (eq_refl (@FILTER _27012 P)). Qed.
Lemma lem1147685 {_27012 : Type'} (P : _27012 -> Prop) (h : _27012) (t : list _27012) (l2 : list _27012) : (term55 _27012 P h t l2) = (term56 _27012 P h t l2).
Proof. exact (MK_COMB (@lem1147684 _27012 P) (@lem1147683 _27012 h t l2)). Qed.
Lemma lem1147687 {_25594 : Type'} (h : _25594) (P : _25594 -> Prop) (t : list _25594) : (term57 _25594 P h t) = (term58 _25594 h P t).
Proof. exact (EQ_MP (@lem1106572 _25594 h P t) (@lem1106571 _25594 h P t)). Qed.
Lemma lem1147688 {_27012 : Type'} (h : _27012) (P : _27012 -> Prop) (t : list _27012) : (term57 _27012 P h t) = (term58 _27012 h P t).
Proof. exact (@lem1147687 _27012 h P t). Qed.
Lemma lem1147689 {_27012 : Type'} (h : _27012) (P : _27012 -> Prop) (t : list _27012) (l2 : list _27012) : (term56 _27012 P h t l2) = (term59 _27012 h P t l2).
Proof. exact (@lem1147688 _27012 h P (@List.app _27012 t l2)). Qed.
Lemma lem1147691 {_27012 : Type'} (l2 : list _27012) (t : list _27012) (P : _27012 -> Prop) (h1 : term8 _27012 t P) : (term53 _27012 P t l2) = (term54 _27012 t P l2).
Proof. exact (EQ_MP (@lem1147672 _27012 t P l2) (@lem1147671 _27012 l2 t P h1)). Qed.
Lemma lem1147692 {_27012 : Type'} (l2 : list _27012) (t : list _27012) (P : _27012 -> Prop) (h1 : term8 _27012 t P) : (term53 _27012 P t l2) = (term54 _27012 t P l2).
Proof. exact (@lem1147691 _27012 l2 t P h1). Qed.
Lemma lem1147693 {_27012 : Type'} (h : _27012) : (@cons _27012 h) = (@cons _27012 h).
Proof. exact (eq_refl (@cons _27012 h)). Qed.
Lemma lem1147694 {_27012 : Type'} (h : _27012) (l2 : list _27012) (t : list _27012) (P : _27012 -> Prop) (h1 : term8 _27012 t P) : (term60 _27012 h P t l2) = (term61 _27012 h t P l2).
Proof. exact (MK_COMB (@lem1147693 _27012 h) (@lem1147692 _27012 l2 t P h1)). Qed.
Lemma lem1147695 {_27012 : Type'} (P : _27012 -> Prop) (h : _27012) : (term62 _27012 P h) = (term62 _27012 P h).
Proof. exact (eq_refl (term62 _27012 P h)). Qed.
Lemma lem1147696 {_27012 : Type'} (h : _27012) (l2 : list _27012) (t : list _27012) (P : _27012 -> Prop) (h1 : term8 _27012 t P) : (term63 _27012 h P t l2) = (term64 _27012 h t P l2).
Proof. exact (MK_COMB (@lem1147695 _27012 P h) (@lem1147694 _27012 h l2 t P h1)). Qed.
Lemma lem1147698 {_27012 : Type'} (l2 : list _27012) (t : list _27012) (P : _27012 -> Prop) (h1 : term8 _27012 t P) : (term53 _27012 P t l2) = (term54 _27012 t P l2).
Proof. exact (EQ_MP (@lem1147672 _27012 t P l2) (@lem1147671 _27012 l2 t P h1)). Qed.
Lemma lem1147699 {_27012 : Type'} (l2 : list _27012) (t : list _27012) (P : _27012 -> Prop) (h1 : term8 _27012 t P) : (term53 _27012 P t l2) = (term54 _27012 t P l2).
Proof. exact (@lem1147698 _27012 l2 t P h1). Qed.
Lemma lem1147700 {_27012 : Type'} (h : _27012) (l2 : list _27012) (t : list _27012) (P : _27012 -> Prop) (h1 : term8 _27012 t P) : (term59 _27012 h P t l2) = (term65 _27012 h t P l2).
Proof. exact (MK_COMB (@lem1147696 _27012 h l2 t P h1) (@lem1147699 _27012 l2 t P h1)). Qed.
Lemma lem1147701 {_27012 : Type'} (h : _27012) (l2 : list _27012) (t : list _27012) (P : _27012 -> Prop) (h1 : term8 _27012 t P) : (term56 _27012 P h t l2) = (term65 _27012 h t P l2).
Proof. exact (TRANS (@lem1147689 _27012 h P t l2) (@lem1147700 _27012 h l2 t P h1)). Qed.
Lemma lem1147702 {_27012 : Type'} (h : _27012) (l2 : list _27012) (t : list _27012) (P : _27012 -> Prop) (h1 : term8 _27012 t P) : (term55 _27012 P h t l2) = (term65 _27012 h t P l2).
Proof. exact (TRANS (@lem1147685 _27012 P h t l2) (@lem1147701 _27012 h l2 t P h1)). Qed.
Lemma lem1147703 {_27012 : Type'} : (@eq (list _27012)) = (@eq (list _27012)).
Proof. exact (eq_refl (@eq (list _27012))). Qed.
Lemma lem1147704 {_27012 : Type'} (h : _27012) (l2 : list _27012) (t : list _27012) (P : _27012 -> Prop) (h1 : term8 _27012 t P) : (term66 _27012 P h t l2) = (term67 _27012 h t P l2).
Proof. exact (MK_COMB (@lem1147703 _27012) (@lem1147702 _27012 h l2 t P h1)). Qed.
Lemma lem1147706 {_25594 : Type'} (h : _25594) (P : _25594 -> Prop) (t : list _25594) : (term57 _25594 P h t) = (term58 _25594 h P t).
Proof. exact (EQ_MP (@lem1106572 _25594 h P t) (@lem1106571 _25594 h P t)). Qed.
Lemma lem1147707 {_27012 : Type'} (h : _27012) (P : _27012 -> Prop) (t : list _27012) : (term57 _27012 P h t) = (term58 _27012 h P t).
Proof. exact (@lem1147706 _27012 h P t). Qed.
Lemma lem1147708 {_27012 : Type'} : (@List.app _27012) = (@List.app _27012).
Proof. exact (eq_refl (@List.app _27012)). Qed.
Lemma lem1147709 {_27012 : Type'} (h : _27012) (P : _27012 -> Prop) (t : list _27012) : (term68 _27012 P h t) = (term69 _27012 h P t).
Proof. exact (MK_COMB (@lem1147708 _27012) (@lem1147707 _27012 h P t)). Qed.
Lemma lem1147710 {_27012 : Type'} (P : _27012 -> Prop) (l2 : list _27012) : (@FILTER _27012 P l2) = (@FILTER _27012 P l2).
Proof. exact (eq_refl (@FILTER _27012 P l2)). Qed.
Lemma lem1147711 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : (term70 _27012 h t P l2) = (term71 _27012 h t P l2).
Proof. exact (MK_COMB (@lem1147709 _27012 h P t) (@lem1147710 _27012 P l2)). Qed.
Lemma lem1147712 {_27012 : Type'} (h : _27012) (l2 : list _27012) (t : list _27012) (P : _27012 -> Prop) (h1 : term8 _27012 t P) : ((term55 _27012 P h t l2) = (term70 _27012 h t P l2)) = ((term65 _27012 h t P l2) = (term71 _27012 h t P l2)).
Proof. exact (MK_COMB (@lem1147704 _27012 h l2 t P h1) (@lem1147711 _27012 h t P l2)). Qed.
Lemma lem1147715 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (h1 : term8 _27012 t P) : (term72 _27012 h t P) = (term73 _27012 h t P).
Proof. exact (fun_ext (fun l2 : list _27012 => @lem1147712 _27012 h l2 t P h1)). Qed.
Lemma lem1147716 {_27012 : Type'} : (@all (list _27012)) = (@all (list _27012)).
Proof. exact (eq_refl (@all (list _27012))). Qed.
Lemma lem1147717 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (h1 : term8 _27012 t P) : (term12 _27012 h t P) = (term74 _27012 h t P).
Proof. exact (MK_COMB (@lem1147716 _27012) (@lem1147715 _27012 h t P h1)). Qed.
Lemma lem1147722 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (h1 : term8 _27012 t P) : (term74 _27012 h t P) = (term12 _27012 h t P).
Proof. exact (SYM (@lem1147717 _27012 h t P h1)). Qed.
Lemma lem1147723 {_27012 : Type'} (_474 : list _27012) (_475 : Prop) (_476 : type1143 _27012) (_477 : list _27012) : (term75 _27012 _476 _475 _474 _477) = (term76 _27012 _474 _475 _476 _477).
Proof. exact (@lem13473 (list _27012) _474 _475 _476 _477). Qed.
Lemma lem1147724 {_27012 : Type'} (_474 : list _27012) (_475 : Prop) (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) (_477 : list _27012) : (term77 _27012 h t P l2 _475 _474 _477) = (term78 _27012 _474 _475 h t P l2 _477).
Proof. exact (@lem1147723 _27012 _474 _475 (term79 _27012 h t P l2) _477). Qed.
Lemma lem1147725 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : (term80 _27012 h t P l2) = (term81 _27012 h t P l2).
Proof. exact (@lem1147724 _27012 (term61 _27012 h t P l2) (P h) h t P l2 (term54 _27012 t P l2)). Qed.
Lemma lem1147726 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : (term82 _27012 h t P l2) = ((term54 _27012 t P l2) = (term71 _27012 h t P l2)).
Proof. exact (eq_refl (term82 _27012 h t P l2)). Qed.
Lemma lem1147727 {_27012 : Type'} (P : _27012 -> Prop) (h : _27012) : (term83 _27012 P h) = (term83 _27012 P h).
Proof. exact (eq_refl (term83 _27012 P h)). Qed.
Lemma lem1147728 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : (term84 _27012 h t P l2) = (term85 _27012 h t P l2).
Proof. exact (MK_COMB (@lem1147727 _27012 P h) (@lem1147726 _27012 h t P l2)). Qed.
Lemma lem1147729 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : (term86 _27012 h t P l2) = ((term61 _27012 h t P l2) = (term71 _27012 h t P l2)).
Proof. exact (eq_refl (term86 _27012 h t P l2)). Qed.
Lemma lem1147730 {_27012 : Type'} (P : _27012 -> Prop) (h : _27012) : (term87 _27012 P h) = (term87 _27012 P h).
Proof. exact (eq_refl (term87 _27012 P h)). Qed.
Lemma lem1147731 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : (term88 _27012 h t P l2) = (term89 _27012 h t P l2).
Proof. exact (MK_COMB (@lem1147730 _27012 P h) (@lem1147729 _27012 h t P l2)). Qed.
Lemma lem1147732 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1147733 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : (term90 _27012 h t P l2) = (term91 _27012 h t P l2).
Proof. exact (MK_COMB (@lem1147732) (@lem1147731 _27012 h t P l2)). Qed.
Lemma lem1147734 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : (term81 _27012 h t P l2) = (term92 _27012 h t P l2).
Proof. exact (MK_COMB (@lem1147733 _27012 h t P l2) (@lem1147728 _27012 h t P l2)). Qed.
Lemma lem1147735 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : (term80 _27012 h t P l2) = ((term65 _27012 h t P l2) = (term71 _27012 h t P l2)).
Proof. exact (eq_refl (term80 _27012 h t P l2)). Qed.
Lemma lem1147736 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1147737 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : (term93 _27012 h t P l2) = (term94 _27012 h t P l2).
Proof. exact (MK_COMB (@lem1147736) (@lem1147735 _27012 h t P l2)). Qed.
Lemma lem1147738 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : ((term80 _27012 h t P l2) = (term81 _27012 h t P l2)) = (((term65 _27012 h t P l2) = (term71 _27012 h t P l2)) = (term92 _27012 h t P l2)).
Proof. exact (MK_COMB (@lem1147737 _27012 h t P l2) (@lem1147734 _27012 h t P l2)). Qed.
Lemma lem1147739 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : ((term65 _27012 h t P l2) = (term71 _27012 h t P l2)) = (term92 _27012 h t P l2).
Proof. exact (EQ_MP (@lem1147738 _27012 h t P l2) (@lem1147725 _27012 h t P l2)). Qed.
Lemma lem1147740 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : (term92 _27012 h t P l2) = ((term65 _27012 h t P l2) = (term71 _27012 h t P l2)).
Proof. exact (SYM (@lem1147739 _27012 h t P l2)). Qed.
Lemma lem1147741 {_27012 : Type'} (P : _27012 -> Prop) (h : _27012) (h1 : P h) : P h.
Proof. exact (h1). Qed.
Lemma lem1147742 {_27012 : Type'} (P : _27012 -> Prop) (h : _27012) : (P h) = ((P h) = True).
Proof. exact (@lem7 (P h)). Qed.
Lemma lem1147743 {_27012 : Type'} (P : _27012 -> Prop) (h : _27012) (h1 : P h) : (P h) = True.
Proof. exact (EQ_MP (@lem1147742 _27012 P h) (@lem1147741 _27012 P h h1)). Qed.
Lemma lem1147744 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : (term95 _27012 h t P l2) = (term95 _27012 h t P l2).
Proof. exact (eq_refl (term95 _27012 h t P l2)). Qed.
Lemma lem1147745 {_27012 : Type'} (t : list _27012) (l2 : list _27012) (P : _27012 -> Prop) (h : _27012) (h1 : P h) : (term96 _27012 t l2 P h) = (term97 _27012 h t P l2).
Proof. exact (MK_COMB (@lem1147744 _27012 h t P l2) (@lem1147743 _27012 P h h1)). Qed.
Lemma lem1147746 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : (term97 _27012 h t P l2) = ((term61 _27012 h t P l2) = (term98 _27012 h t P l2)).
Proof. exact (eq_refl (term97 _27012 h t P l2)). Qed.
Lemma lem1147747 {_27012 : Type'} (t : list _27012) (l2 : list _27012) (P : _27012 -> Prop) (h : _27012) : (term99 _27012 t l2 P h) = (term99 _27012 t l2 P h).
Proof. exact (eq_refl (term99 _27012 t l2 P h)). Qed.
Lemma lem1147748 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : ((term96 _27012 t l2 P h) = (term97 _27012 h t P l2)) = ((term96 _27012 t l2 P h) = ((term61 _27012 h t P l2) = (term98 _27012 h t P l2))).
Proof. exact (MK_COMB (@lem1147747 _27012 t l2 P h) (@lem1147746 _27012 h t P l2)). Qed.
Lemma lem1147749 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : (term96 _27012 t l2 P h) = ((term61 _27012 h t P l2) = (term71 _27012 h t P l2)).
Proof. exact (eq_refl (term96 _27012 t l2 P h)). Qed.
Lemma lem1147750 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1147751 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : (term99 _27012 t l2 P h) = (term100 _27012 h t P l2).
Proof. exact (MK_COMB (@lem1147750) (@lem1147749 _27012 h t P l2)). Qed.
Lemma lem1147752 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : ((term61 _27012 h t P l2) = (term98 _27012 h t P l2)) = ((term61 _27012 h t P l2) = (term98 _27012 h t P l2)).
Proof. exact (eq_refl ((term61 _27012 h t P l2) = (term98 _27012 h t P l2))). Qed.
Lemma lem1147753 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : ((term96 _27012 t l2 P h) = ((term61 _27012 h t P l2) = (term98 _27012 h t P l2))) = (((term61 _27012 h t P l2) = (term71 _27012 h t P l2)) = ((term61 _27012 h t P l2) = (term98 _27012 h t P l2))).
Proof. exact (MK_COMB (@lem1147751 _27012 h t P l2) (@lem1147752 _27012 h t P l2)). Qed.
Lemma lem1147754 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : ((term96 _27012 t l2 P h) = (term97 _27012 h t P l2)) = (((term61 _27012 h t P l2) = (term71 _27012 h t P l2)) = ((term61 _27012 h t P l2) = (term98 _27012 h t P l2))).
Proof. exact (TRANS (@lem1147748 _27012 h t P l2) (@lem1147753 _27012 h t P l2)). Qed.
Lemma lem1147755 {_27012 : Type'} (t : list _27012) (l2 : list _27012) (P : _27012 -> Prop) (h : _27012) (h1 : P h) : ((term61 _27012 h t P l2) = (term71 _27012 h t P l2)) = ((term61 _27012 h t P l2) = (term98 _27012 h t P l2)).
Proof. exact (EQ_MP (@lem1147754 _27012 h t P l2) (@lem1147745 _27012 t l2 P h h1)). Qed.
Lemma lem1147756 {_27012 : Type'} (t : list _27012) (l2 : list _27012) (P : _27012 -> Prop) (h : _27012) (h1 : P h) : ((term61 _27012 h t P l2) = (term98 _27012 h t P l2)) = ((term61 _27012 h t P l2) = (term71 _27012 h t P l2)).
Proof. exact (SYM (@lem1147755 _27012 t l2 P h h1)). Qed.
Lemma lem1147757 {_27012 : Type'} (P : _27012 -> Prop) (h : _27012) (h1 : term101 _27012 P h) : term101 _27012 P h.
Proof. exact (h1). Qed.
Lemma lem1147758 {_27012 : Type'} (P : _27012 -> Prop) (h : _27012) : term102 _27012 P h.
Proof. exact (@lem82 (P h)). Qed.
Lemma lem1147759 {_27012 : Type'} (P : _27012 -> Prop) (h : _27012) (h1 : term101 _27012 P h) : (P h) = False.
Proof. exact (@lem1147758 _27012 P h (@lem1147757 _27012 P h h1)). Qed.
Lemma lem1147760 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : (term103 _27012 h t P l2) = (term103 _27012 h t P l2).
Proof. exact (eq_refl (term103 _27012 h t P l2)). Qed.
Lemma lem1147761 {_27012 : Type'} (t : list _27012) (l2 : list _27012) (P : _27012 -> Prop) (h : _27012) (h1 : term101 _27012 P h) : (term104 _27012 t l2 P h) = (term105 _27012 h t P l2).
Proof. exact (MK_COMB (@lem1147760 _27012 h t P l2) (@lem1147759 _27012 P h h1)). Qed.
Lemma lem1147762 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : (term105 _27012 h t P l2) = ((term54 _27012 t P l2) = (term106 _27012 h t P l2)).
Proof. exact (eq_refl (term105 _27012 h t P l2)). Qed.
Lemma lem1147763 {_27012 : Type'} (t : list _27012) (l2 : list _27012) (P : _27012 -> Prop) (h : _27012) : (term107 _27012 t l2 P h) = (term107 _27012 t l2 P h).
Proof. exact (eq_refl (term107 _27012 t l2 P h)). Qed.
Lemma lem1147764 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : ((term104 _27012 t l2 P h) = (term105 _27012 h t P l2)) = ((term104 _27012 t l2 P h) = ((term54 _27012 t P l2) = (term106 _27012 h t P l2))).
Proof. exact (MK_COMB (@lem1147763 _27012 t l2 P h) (@lem1147762 _27012 h t P l2)). Qed.
Lemma lem1147765 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : (term104 _27012 t l2 P h) = ((term54 _27012 t P l2) = (term71 _27012 h t P l2)).
Proof. exact (eq_refl (term104 _27012 t l2 P h)). Qed.
Lemma lem1147766 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1147767 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : (term107 _27012 t l2 P h) = (term108 _27012 h t P l2).
Proof. exact (MK_COMB (@lem1147766) (@lem1147765 _27012 h t P l2)). Qed.
Lemma lem1147768 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : ((term54 _27012 t P l2) = (term106 _27012 h t P l2)) = ((term54 _27012 t P l2) = (term106 _27012 h t P l2)).
Proof. exact (eq_refl ((term54 _27012 t P l2) = (term106 _27012 h t P l2))). Qed.
Lemma lem1147769 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : ((term104 _27012 t l2 P h) = ((term54 _27012 t P l2) = (term106 _27012 h t P l2))) = (((term54 _27012 t P l2) = (term71 _27012 h t P l2)) = ((term54 _27012 t P l2) = (term106 _27012 h t P l2))).
Proof. exact (MK_COMB (@lem1147767 _27012 h t P l2) (@lem1147768 _27012 h t P l2)). Qed.
Lemma lem1147770 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : ((term104 _27012 t l2 P h) = (term105 _27012 h t P l2)) = (((term54 _27012 t P l2) = (term71 _27012 h t P l2)) = ((term54 _27012 t P l2) = (term106 _27012 h t P l2))).
Proof. exact (TRANS (@lem1147764 _27012 h t P l2) (@lem1147769 _27012 h t P l2)). Qed.
Lemma lem1147771 {_27012 : Type'} (t : list _27012) (l2 : list _27012) (P : _27012 -> Prop) (h : _27012) (h1 : term101 _27012 P h) : ((term54 _27012 t P l2) = (term71 _27012 h t P l2)) = ((term54 _27012 t P l2) = (term106 _27012 h t P l2)).
Proof. exact (EQ_MP (@lem1147770 _27012 h t P l2) (@lem1147761 _27012 t l2 P h h1)). Qed.
Lemma lem1147772 {_27012 : Type'} (t : list _27012) (l2 : list _27012) (P : _27012 -> Prop) (h : _27012) (h1 : term101 _27012 P h) : ((term54 _27012 t P l2) = (term106 _27012 h t P l2)) = ((term54 _27012 t P l2) = (term71 _27012 h t P l2)).
Proof. exact (SYM (@lem1147771 _27012 t l2 P h h1)). Qed.
Lemma lem1147773 {A : Type'} : term44 A.
Proof. exact (proj2 (@lem1095962 A)). Qed.
Lemma lem1147774 {A : Type'} (h : A) : term45 A h.
Proof. exact (@lem1147773 A h). Qed.
Lemma lem1147775 {A : Type'} (h : A) : (term45 A h) = (term46 A h).
Proof. exact (eq_refl (term45 A h)). Qed.
Lemma lem1147776 {A : Type'} (h : A) : term46 A h.
Proof. exact (EQ_MP (@lem1147775 A h) (@lem1147774 A h)). Qed.
Lemma lem1147777 {A : Type'} (h : A) (t : list A) : term47 A h t.
Proof. exact (@lem1147776 A h t). Qed.
Lemma lem1147778 {A : Type'} (h : A) (t : list A) : (term47 A h t) = (term48 A h t).
Proof. exact (eq_refl (term47 A h t)). Qed.
Lemma lem1147779 {A : Type'} (h : A) (t : list A) : term48 A h t.
Proof. exact (EQ_MP (@lem1147778 A h t) (@lem1147777 A h t)). Qed.
Lemma lem1147780 {A : Type'} (h : A) (t : list A) (l : list A) : term49 A h t l.
Proof. exact (@lem1147779 A h t l). Qed.
Lemma lem1147781 {A : Type'} (h : A) (t : list A) (l : list A) : (term49 A h t l) = ((term50 A h t l) = (term51 A h t l)).
Proof. exact (eq_refl (term49 A h t l)). Qed.
Lemma lem1147795 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1147796 {_27012 : Type'} (t2 : list _27012) (t1 : list _27012) : (@COND (list _27012) True t1 t2) = t1.
Proof. exact (@lem1147795 (list _27012) t2 t1). Qed.
Lemma lem1147797 {_27012 : Type'} (h : _27012) (P : _27012 -> Prop) (t : list _27012) : (term109 _27012 h P t) = (term110 _27012 h P t).
Proof. exact (@lem1147796 _27012 (@FILTER _27012 P t) (term110 _27012 h P t)). Qed.
Lemma lem1147798 {_27012 : Type'} : (@List.app _27012) = (@List.app _27012).
Proof. exact (eq_refl (@List.app _27012)). Qed.
Lemma lem1147799 {_27012 : Type'} (h : _27012) (P : _27012 -> Prop) (t : list _27012) : (term111 _27012 h P t) = (term112 _27012 h P t).
Proof. exact (MK_COMB (@lem1147798 _27012) (@lem1147797 _27012 h P t)). Qed.
Lemma lem1147800 {_27012 : Type'} (P : _27012 -> Prop) (l2 : list _27012) : (@FILTER _27012 P l2) = (@FILTER _27012 P l2).
Proof. exact (eq_refl (@FILTER _27012 P l2)). Qed.
Lemma lem1147801 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : (term98 _27012 h t P l2) = (term113 _27012 h t P l2).
Proof. exact (MK_COMB (@lem1147799 _27012 h P t) (@lem1147800 _27012 P l2)). Qed.
Lemma lem1147803 {A : Type'} (h : A) (t : list A) (l : list A) : (term50 A h t l) = (term51 A h t l).
Proof. exact (EQ_MP (@lem1147781 A h t l) (@lem1147780 A h t l)). Qed.
Lemma lem1147804 {_27012 : Type'} (h : _27012) (t : list _27012) (l : list _27012) : (term50 _27012 h t l) = (term51 _27012 h t l).
Proof. exact (@lem1147803 _27012 h t l). Qed.
Lemma lem1147805 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : (term113 _27012 h t P l2) = (term61 _27012 h t P l2).
Proof. exact (@lem1147804 _27012 h (@FILTER _27012 P t) (@FILTER _27012 P l2)). Qed.
Lemma lem1147806 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : (term98 _27012 h t P l2) = (term61 _27012 h t P l2).
Proof. exact (TRANS (@lem1147801 _27012 h t P l2) (@lem1147805 _27012 h t P l2)). Qed.
Lemma lem1147807 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : (term114 _27012 h t P l2) = (term114 _27012 h t P l2).
Proof. exact (eq_refl (term114 _27012 h t P l2)). Qed.
Lemma lem1147808 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : ((term61 _27012 h t P l2) = (term98 _27012 h t P l2)) = ((term61 _27012 h t P l2) = (term61 _27012 h t P l2)).
Proof. exact (MK_COMB (@lem1147807 _27012 h t P l2) (@lem1147806 _27012 h t P l2)). Qed.
Lemma lem1147810 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1147811 {_27012 : Type'} (x : list _27012) : (x = x) = True.
Proof. exact (@lem1147810 (list _27012) x). Qed.
Lemma lem1147812 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : ((term61 _27012 h t P l2) = (term61 _27012 h t P l2)) = True.
Proof. exact (@lem1147811 _27012 (term61 _27012 h t P l2)). Qed.
Lemma lem1147813 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : ((term61 _27012 h t P l2) = (term98 _27012 h t P l2)) = True.
Proof. exact (TRANS (@lem1147808 _27012 h t P l2) (@lem1147812 _27012 h t P l2)). Qed.
Lemma lem1147814 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : True = ((term61 _27012 h t P l2) = (term98 _27012 h t P l2)).
Proof. exact (SYM (@lem1147813 _27012 h t P l2)). Qed.
Lemma lem1147815 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : (term61 _27012 h t P l2) = (term98 _27012 h t P l2).
Proof. exact (EQ_MP (@lem1147814 _27012 h t P l2) (@lem0)). Qed.
Lemma lem1147838 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1147839 {_27012 : Type'} (t1 : list _27012) (t2 : list _27012) : (@COND (list _27012) False t1 t2) = t2.
Proof. exact (@lem1147838 (list _27012) t1 t2). Qed.
Lemma lem1147840 {_27012 : Type'} (h : _27012) (P : _27012 -> Prop) (t : list _27012) : (term115 _27012 h P t) = (@FILTER _27012 P t).
Proof. exact (@lem1147839 _27012 (term110 _27012 h P t) (@FILTER _27012 P t)). Qed.
Lemma lem1147841 {_27012 : Type'} : (@List.app _27012) = (@List.app _27012).
Proof. exact (eq_refl (@List.app _27012)). Qed.
Lemma lem1147842 {_27012 : Type'} (h : _27012) (P : _27012 -> Prop) (t : list _27012) : (term116 _27012 h P t) = (term117 _27012 P t).
Proof. exact (MK_COMB (@lem1147841 _27012) (@lem1147840 _27012 h P t)). Qed.
Lemma lem1147843 {_27012 : Type'} (P : _27012 -> Prop) (l2 : list _27012) : (@FILTER _27012 P l2) = (@FILTER _27012 P l2).
Proof. exact (eq_refl (@FILTER _27012 P l2)). Qed.
Lemma lem1147844 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : (term106 _27012 h t P l2) = (term54 _27012 t P l2).
Proof. exact (MK_COMB (@lem1147842 _27012 h P t) (@lem1147843 _27012 P l2)). Qed.
Lemma lem1147845 {_27012 : Type'} (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : (term118 _27012 t P l2) = (term118 _27012 t P l2).
Proof. exact (eq_refl (term118 _27012 t P l2)). Qed.
Lemma lem1147846 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : ((term54 _27012 t P l2) = (term106 _27012 h t P l2)) = ((term54 _27012 t P l2) = (term54 _27012 t P l2)).
Proof. exact (MK_COMB (@lem1147845 _27012 t P l2) (@lem1147844 _27012 h t P l2)). Qed.
Lemma lem1147848 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1147849 {_27012 : Type'} (x : list _27012) : (x = x) = True.
Proof. exact (@lem1147848 (list _27012) x). Qed.
Lemma lem1147850 {_27012 : Type'} (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : ((term54 _27012 t P l2) = (term54 _27012 t P l2)) = True.
Proof. exact (@lem1147849 _27012 (term54 _27012 t P l2)). Qed.
Lemma lem1147851 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : ((term54 _27012 t P l2) = (term106 _27012 h t P l2)) = True.
Proof. exact (TRANS (@lem1147846 _27012 h t P l2) (@lem1147850 _27012 t P l2)). Qed.
Lemma lem1147852 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : True = ((term54 _27012 t P l2) = (term106 _27012 h t P l2)).
Proof. exact (SYM (@lem1147851 _27012 h t P l2)). Qed.
Lemma lem1147853 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : (term54 _27012 t P l2) = (term106 _27012 h t P l2).
Proof. exact (EQ_MP (@lem1147852 _27012 h t P l2) (@lem0)). Qed.
Lemma lem1147854 {_27012 : Type'} (t : list _27012) (l2 : list _27012) (P : _27012 -> Prop) (h : _27012) (h1 : term101 _27012 P h) : (term54 _27012 t P l2) = (term71 _27012 h t P l2).
Proof. exact (EQ_MP (@lem1147772 _27012 t l2 P h h1) (@lem1147853 _27012 h t P l2)). Qed.
Lemma lem1147855 {_27012 : Type'} (t : list _27012) (l2 : list _27012) (P : _27012 -> Prop) (h : _27012) (h1 : term101 _27012 P h) : (term101 _27012 P h) = ((term54 _27012 t P l2) = (term71 _27012 h t P l2)).
Proof. exact (prop_ext (fun h2 : term101 _27012 P h => @lem1147854 _27012 t l2 P h h1) (fun h2 : (term54 _27012 t P l2) = (term71 _27012 h t P l2) => @lem1147757 _27012 P h h1)). Qed.
Lemma lem1147856 {_27012 : Type'} (t : list _27012) (l2 : list _27012) (P : _27012 -> Prop) (h : _27012) (h1 : term101 _27012 P h) : (term54 _27012 t P l2) = (term71 _27012 h t P l2).
Proof. exact (EQ_MP (@lem1147855 _27012 t l2 P h h1) (@lem1147757 _27012 P h h1)). Qed.
Lemma lem1147857 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : term85 _27012 h t P l2.
Proof. exact (fun h0 : term101 _27012 P h => @lem1147856 _27012 t l2 P h h0). Qed.
Lemma lem1147858 {_27012 : Type'} (t : list _27012) (l2 : list _27012) (P : _27012 -> Prop) (h : _27012) (h1 : P h) : (term61 _27012 h t P l2) = (term71 _27012 h t P l2).
Proof. exact (EQ_MP (@lem1147756 _27012 t l2 P h h1) (@lem1147815 _27012 h t P l2)). Qed.
Lemma lem1147859 {_27012 : Type'} (t : list _27012) (l2 : list _27012) (P : _27012 -> Prop) (h : _27012) (h1 : P h) : (P h) = ((term61 _27012 h t P l2) = (term71 _27012 h t P l2)).
Proof. exact (prop_ext (fun h2 : P h => @lem1147858 _27012 t l2 P h h1) (fun h2 : (term61 _27012 h t P l2) = (term71 _27012 h t P l2) => @lem1147741 _27012 P h h1)). Qed.
Lemma lem1147860 {_27012 : Type'} (t : list _27012) (l2 : list _27012) (P : _27012 -> Prop) (h : _27012) (h1 : P h) : (term61 _27012 h t P l2) = (term71 _27012 h t P l2).
Proof. exact (EQ_MP (@lem1147859 _27012 t l2 P h h1) (@lem1147741 _27012 P h h1)). Qed.
Lemma lem1147861 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : term89 _27012 h t P l2.
Proof. exact (fun h0 : P h => @lem1147860 _27012 t l2 P h h0). Qed.
Lemma lem1147862 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : term92 _27012 h t P l2.
Proof. exact (conj (@lem1147861 _27012 h t P l2) (@lem1147857 _27012 h t P l2)). Qed.
Lemma lem1147863 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (l2 : list _27012) : (term65 _27012 h t P l2) = (term71 _27012 h t P l2).
Proof. exact (EQ_MP (@lem1147740 _27012 h t P l2) (@lem1147862 _27012 h t P l2)). Qed.
Lemma lem1147868 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) : term74 _27012 h t P.
Proof. exact (fun l2 : list _27012 => @lem1147863 _27012 h t P l2). Qed.
Lemma lem1147869 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) (h1 : term8 _27012 t P) : term12 _27012 h t P.
Proof. exact (EQ_MP (@lem1147722 _27012 h t P h1) (@lem1147868 _27012 h t P)). Qed.
Lemma lem1147870 {_27012 : Type'} (h : _27012) (t : list _27012) (P : _27012 -> Prop) : term14 _27012 h t P.
Proof. exact (fun h0 : term8 _27012 t P => @lem1147869 _27012 h t P h0). Qed.
Lemma lem1147875 {_27012 : Type'} (h : _27012) (P : _27012 -> Prop) : term18 _27012 h P.
Proof. exact (fun t : list _27012 => @lem1147870 _27012 h t P). Qed.
Lemma lem1147880 {_27012 : Type'} (P : _27012 -> Prop) : term22 _27012 P.
Proof. exact (fun h : _27012 => @lem1147875 _27012 h P). Qed.
Lemma lem1147881 {_27012 : Type'} (P : _27012 -> Prop) : term24 _27012 P.
Proof. exact (conj (@lem1147654 _27012 P) (@lem1147880 _27012 P)). Qed.
Lemma lem1147882 {_27012 : Type'} (P : _27012 -> Prop) : term29 _27012 P.
Proof. exact (@lem1147595 _27012 P (@lem1147881 _27012 P)). Qed.
Lemma lem1147887 {_27012 : Type'} : term119 _27012.
Proof. exact (fun P : _27012 -> Prop => @lem1147882 _27012 P). Qed.
