Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import APPEND_NIL_term_abbrevs.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1095962_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1111626 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1111627 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (@lem1111626 A P). Qed.
Lemma lem1111628 {A : Type'} : term1 A.
Proof. exact (@lem1111627 A (term2 A)). Qed.
Lemma lem1111629 {A : Type'} : (term3 A) = ((@List.app A (@nil A) (@nil A)) = (@nil A)).
Proof. exact (eq_refl (term3 A)). Qed.
Lemma lem1111630 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1111631 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (MK_COMB (@lem1111630) (@lem1111629 A)). Qed.
Lemma lem1111632 {A : Type'} (t : list A) : (term6 A t) = ((@List.app A t (@nil A)) = t).
Proof. exact (eq_refl (term6 A t)). Qed.
Lemma lem1111633 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1111634 {A : Type'} (t : list A) : (term7 A t) = (term8 A t).
Proof. exact (MK_COMB (@lem1111633) (@lem1111632 A t)). Qed.
Lemma lem1111635 {A : Type'} (h : A) (t : list A) : (term9 A h t) = ((term10 A h t) = (@cons A h t)).
Proof. exact (eq_refl (term9 A h t)). Qed.
Lemma lem1111636 {A : Type'} (h : A) (t : list A) : (term11 A h t) = (term12 A h t).
Proof. exact (MK_COMB (@lem1111634 A t) (@lem1111635 A h t)). Qed.
Lemma lem1111637 {A : Type'} (h : A) : (term13 A h) = (term14 A h).
Proof. exact (fun_ext (fun t : list A => @lem1111636 A h t)). Qed.
Lemma lem1111638 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1111639 {A : Type'} (h : A) : (term15 A h) = (term16 A h).
Proof. exact (MK_COMB (@lem1111638 A) (@lem1111637 A h)). Qed.
Lemma lem1111640 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (fun_ext (fun h : A => @lem1111639 A h)). Qed.
Lemma lem1111641 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1111642 {A : Type'} : (term19 A) = (term20 A).
Proof. exact (MK_COMB (@lem1111641 A) (@lem1111640 A)). Qed.
Lemma lem1111643 {A : Type'} : (term21 A) = (term22 A).
Proof. exact (MK_COMB (@lem1111631 A) (@lem1111642 A)). Qed.
Lemma lem1111644 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1111645 {A : Type'} : (term23 A) = (term24 A).
Proof. exact (MK_COMB (@lem1111644) (@lem1111643 A)). Qed.
Lemma lem1111646 {A : Type'} (l : list A) : (term6 A l) = ((@List.app A l (@nil A)) = l).
Proof. exact (eq_refl (term6 A l)). Qed.
Lemma lem1111647 {A : Type'} : (term25 A) = (term2 A).
Proof. exact (fun_ext (fun l : list A => @lem1111646 A l)). Qed.
Lemma lem1111648 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1111649 {A : Type'} : (term26 A) = (term27 A).
Proof. exact (MK_COMB (@lem1111648 A) (@lem1111647 A)). Qed.
Lemma lem1111650 {A : Type'} : (term1 A) = (term28 A).
Proof. exact (MK_COMB (@lem1111645 A) (@lem1111649 A)). Qed.
Lemma lem1111651 {A : Type'} : term28 A.
Proof. exact (EQ_MP (@lem1111650 A) (@lem1111628 A)). Qed.
Lemma lem1111663 {A : Type'} : term29 A.
Proof. exact (proj1 (@lem1095962 A)). Qed.
Lemma lem1111664 {A : Type'} (l : list A) : term30 A l.
Proof. exact (@lem1111663 A l). Qed.
Lemma lem1111665 {A : Type'} (l : list A) : (term30 A l) = ((@List.app A (@nil A) l) = l).
Proof. exact (eq_refl (term30 A l)). Qed.
Lemma lem1111670 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (EQ_MP (@lem1111665 A l) (@lem1111664 A l)). Qed.
Lemma lem1111671 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (@lem1111670 A l). Qed.
Lemma lem1111672 {A : Type'} : (@List.app A (@nil A) (@nil A)) = (@nil A).
Proof. exact (@lem1111671 A (@nil A)). Qed.
Lemma lem1111673 {A : Type'} : (@eq (list A)) = (@eq (list A)).
Proof. exact (eq_refl (@eq (list A))). Qed.
Lemma lem1111674 {A : Type'} : (term31 A) = (@eq (list A) (@nil A)).
Proof. exact (MK_COMB (@lem1111673 A) (@lem1111672 A)). Qed.
Lemma lem1111675 {A : Type'} : (@nil A) = (@nil A).
Proof. exact (eq_refl (@nil A)). Qed.
Lemma lem1111676 {A : Type'} : ((@List.app A (@nil A) (@nil A)) = (@nil A)) = ((@nil A) = (@nil A)).
Proof. exact (MK_COMB (@lem1111674 A) (@lem1111675 A)). Qed.
Lemma lem1111678 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1111679 {A : Type'} (x : list A) : (x = x) = True.
Proof. exact (@lem1111678 (list A) x). Qed.
Lemma lem1111680 {A : Type'} : ((@nil A) = (@nil A)) = True.
Proof. exact (@lem1111679 A (@nil A)). Qed.
Lemma lem1111681 {A : Type'} : ((@List.app A (@nil A) (@nil A)) = (@nil A)) = True.
Proof. exact (TRANS (@lem1111676 A) (@lem1111680 A)). Qed.
Lemma lem1111682 {A : Type'} : True = ((@List.app A (@nil A) (@nil A)) = (@nil A)).
Proof. exact (SYM (@lem1111681 A)). Qed.
Lemma lem1111683 {A : Type'} : (@List.app A (@nil A) (@nil A)) = (@nil A).
Proof. exact (EQ_MP (@lem1111682 A) (@lem0)). Qed.
Lemma lem1111684 {A : Type'} : term32 A.
Proof. exact (proj2 (@lem1095962 A)). Qed.
Lemma lem1111685 {A : Type'} (h : A) : term33 A h.
Proof. exact (@lem1111684 A h). Qed.
Lemma lem1111686 {A : Type'} (h : A) : (term33 A h) = (term34 A h).
Proof. exact (eq_refl (term33 A h)). Qed.
Lemma lem1111687 {A : Type'} (h : A) : term34 A h.
Proof. exact (EQ_MP (@lem1111686 A h) (@lem1111685 A h)). Qed.
Lemma lem1111688 {A : Type'} (h : A) (t : list A) : term35 A h t.
Proof. exact (@lem1111687 A h t). Qed.
Lemma lem1111689 {A : Type'} (h : A) (t : list A) : (term35 A h t) = (term36 A h t).
Proof. exact (eq_refl (term35 A h t)). Qed.
Lemma lem1111690 {A : Type'} (h : A) (t : list A) : term36 A h t.
Proof. exact (EQ_MP (@lem1111689 A h t) (@lem1111688 A h t)). Qed.
Lemma lem1111691 {A : Type'} (h : A) (t : list A) (l : list A) : term37 A h t l.
Proof. exact (@lem1111690 A h t l). Qed.
Lemma lem1111692 {A : Type'} (h : A) (t : list A) (l : list A) : (term37 A h t l) = ((term38 A h t l) = (term39 A h t l)).
Proof. exact (eq_refl (term37 A h t l)). Qed.
Lemma lem1111701 {A : Type'} (h : A) (t : list A) (l : list A) : (term38 A h t l) = (term39 A h t l).
Proof. exact (EQ_MP (@lem1111692 A h t l) (@lem1111691 A h t l)). Qed.
Lemma lem1111702 {A : Type'} (h : A) (t : list A) (l : list A) : (term38 A h t l) = (term39 A h t l).
Proof. exact (@lem1111701 A h t l). Qed.
Lemma lem1111703 {A : Type'} (h : A) (t : list A) : (term10 A h t) = (term40 A h t).
Proof. exact (@lem1111702 A h t (@nil A)). Qed.
Lemma lem1111705 {A : Type'} (t : list A) (h1 : (@List.app A t (@nil A)) = t) : (@List.app A t (@nil A)) = t.
Proof. exact (h1). Qed.
Lemma lem1111706 {A : Type'} (h : A) : (@cons A h) = (@cons A h).
Proof. exact (eq_refl (@cons A h)). Qed.
Lemma lem1111707 {A : Type'} (h : A) (t : list A) (h1 : (@List.app A t (@nil A)) = t) : (term40 A h t) = (@cons A h t).
Proof. exact (MK_COMB (@lem1111706 A h) (@lem1111705 A t h1)). Qed.
Lemma lem1111708 {A : Type'} (h : A) (t : list A) (h1 : (@List.app A t (@nil A)) = t) : (term10 A h t) = (@cons A h t).
Proof. exact (TRANS (@lem1111703 A h t) (@lem1111707 A h t h1)). Qed.
Lemma lem1111709 {A : Type'} : (@eq (list A)) = (@eq (list A)).
Proof. exact (eq_refl (@eq (list A))). Qed.
Lemma lem1111710 {A : Type'} (h : A) (t : list A) (h1 : (@List.app A t (@nil A)) = t) : (term41 A h t) = (term42 A h t).
Proof. exact (MK_COMB (@lem1111709 A) (@lem1111708 A h t h1)). Qed.
Lemma lem1111711 {A : Type'} (h : A) (t : list A) : (@cons A h t) = (@cons A h t).
Proof. exact (eq_refl (@cons A h t)). Qed.
Lemma lem1111712 {A : Type'} (h : A) (t : list A) (h1 : (@List.app A t (@nil A)) = t) : ((term10 A h t) = (@cons A h t)) = ((@cons A h t) = (@cons A h t)).
Proof. exact (MK_COMB (@lem1111710 A h t h1) (@lem1111711 A h t)). Qed.
Lemma lem1111714 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1111715 {A : Type'} (x : list A) : (x = x) = True.
Proof. exact (@lem1111714 (list A) x). Qed.
Lemma lem1111716 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@cons A h t)) = True.
Proof. exact (@lem1111715 A (@cons A h t)). Qed.
Lemma lem1111717 {A : Type'} (h : A) (t : list A) (h1 : (@List.app A t (@nil A)) = t) : ((term10 A h t) = (@cons A h t)) = True.
Proof. exact (TRANS (@lem1111712 A h t h1) (@lem1111716 A h t)). Qed.
Lemma lem1111718 {A : Type'} (h : A) (t : list A) (h1 : (@List.app A t (@nil A)) = t) : True = ((term10 A h t) = (@cons A h t)).
Proof. exact (SYM (@lem1111717 A h t h1)). Qed.
Lemma lem1111719 {A : Type'} (h : A) (t : list A) (h1 : (@List.app A t (@nil A)) = t) : (term10 A h t) = (@cons A h t).
Proof. exact (EQ_MP (@lem1111718 A h t h1) (@lem0)). Qed.
Lemma lem1111720 {A : Type'} (h : A) (t : list A) : term12 A h t.
Proof. exact (fun h0 : (@List.app A t (@nil A)) = t => @lem1111719 A h t h0). Qed.
Lemma lem1111725 {A : Type'} (h : A) : term16 A h.
Proof. exact (fun t : list A => @lem1111720 A h t). Qed.
Lemma lem1111730 {A : Type'} : term20 A.
Proof. exact (fun h : A => @lem1111725 A h). Qed.
Lemma lem1111731 {A : Type'} : term22 A.
Proof. exact (conj (@lem1111683 A) (@lem1111730 A)). Qed.
Lemma lem1111732 {A : Type'} : term27 A.
Proof. exact (@lem1111651 A (@lem1111731 A)). Qed.
