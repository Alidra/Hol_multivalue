Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1106843_term_abbrevs.
Require Import BETA_THM_spec.
Require Import SKOLEM_THM_spec.
Require Import list_RECURSION_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem1106638 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem421 A B f). Qed.
Lemma lem1106639 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem1106640 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem1106639 A B f) (@lem1106638 A B f)). Qed.
Lemma lem1106641 {A B : Type'} (f : A -> B) (y : A) : term2 A B f y.
Proof. exact (@lem1106640 A B f y). Qed.
Lemma lem1106642 {A B : Type'} (f : A -> B) (y : A) : (term2 A B f y) = ((term3 A B f y) = (f y)).
Proof. exact (eq_refl (term2 A B f y)). Qed.
Lemma lem1106645 {_25617 _25623 : Type'} (ASSOC' : type1457 _25617 _25623) (_18025 : type1124 _25617 _25623) (h1 : ASSOC' = (term4 _25617 _25623 _18025)) : ASSOC' = (term4 _25617 _25623 _18025).
Proof. exact (h1). Qed.
Lemma lem1106646 {_25623 : Type'} (a : _25623) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1106647 {_25617 _25623 : Type'} (a : _25623) (ASSOC' : type1457 _25617 _25623) (_18025 : type1124 _25617 _25623) (h1 : ASSOC' = (term4 _25617 _25623 _18025)) : (ASSOC' a) = (term5 _25617 _25623 _18025 a).
Proof. exact (MK_COMB (@lem1106645 _25617 _25623 ASSOC' _18025 h1) (@lem1106646 _25623 a)). Qed.
Lemma lem1106649 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1106642 A B f y) (@lem1106641 A B f y)). Qed.
Lemma lem1106650 {_25617 _25623 : Type'} (f : type1457 _25617 _25623) (y : _25623) : (term6 _25617 _25623 f y) = (f y).
Proof. exact (@lem1106649 _25623 (type1125 _25617 _25623) f y). Qed.
Lemma lem1106651 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (a : _25623) : (term7 _25617 _25623 _18025 a) = (term5 _25617 _25623 _18025 a).
Proof. exact (@lem1106650 _25617 _25623 (term4 _25617 _25623 _18025) a). Qed.
Lemma lem1106652 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (_18023 : _25623) : (term5 _25617 _25623 _18025 _18023) = (term8 _25617 _25623 _18025 _18023).
Proof. exact (eq_refl (term5 _25617 _25623 _18025 _18023)). Qed.
Lemma lem1106653 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) : (term9 _25617 _25623 _18025) = (term4 _25617 _25623 _18025).
Proof. exact (fun_ext (fun _18023 : _25623 => @lem1106652 _25617 _25623 _18025 _18023)). Qed.
Lemma lem1106654 {_25623 : Type'} (a : _25623) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1106655 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (a : _25623) : (term7 _25617 _25623 _18025 a) = (term5 _25617 _25623 _18025 a).
Proof. exact (MK_COMB (@lem1106653 _25617 _25623 _18025) (@lem1106654 _25623 a)). Qed.
Lemma lem1106656 {_25617 _25623 : Type'} : (@eq ((list (prod _25623 _25617)) -> _25617)) = (@eq ((list (prod _25623 _25617)) -> _25617)).
Proof. exact (eq_refl (@eq ((list (prod _25623 _25617)) -> _25617))). Qed.
Lemma lem1106657 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (a : _25623) : (term10 _25617 _25623 _18025 a) = (term11 _25617 _25623 _18025 a).
Proof. exact (MK_COMB (@lem1106656 _25617 _25623) (@lem1106655 _25617 _25623 _18025 a)). Qed.
Lemma lem1106658 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (a : _25623) : (term5 _25617 _25623 _18025 a) = (term8 _25617 _25623 _18025 a).
Proof. exact (eq_refl (term5 _25617 _25623 _18025 a)). Qed.
Lemma lem1106659 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (a : _25623) : ((term7 _25617 _25623 _18025 a) = (term5 _25617 _25623 _18025 a)) = ((term5 _25617 _25623 _18025 a) = (term8 _25617 _25623 _18025 a)).
Proof. exact (MK_COMB (@lem1106657 _25617 _25623 _18025 a) (@lem1106658 _25617 _25623 _18025 a)). Qed.
Lemma lem1106660 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (a : _25623) : (term5 _25617 _25623 _18025 a) = (term8 _25617 _25623 _18025 a).
Proof. exact (EQ_MP (@lem1106659 _25617 _25623 _18025 a) (@lem1106651 _25617 _25623 _18025 a)). Qed.
Lemma lem1106661 {_25617 _25623 : Type'} (a : _25623) (ASSOC' : type1457 _25617 _25623) (_18025 : type1124 _25617 _25623) (h1 : ASSOC' = (term4 _25617 _25623 _18025)) : (ASSOC' a) = (term8 _25617 _25623 _18025 a).
Proof. exact (TRANS (@lem1106647 _25617 _25623 a ASSOC' _18025 h1) (@lem1106660 _25617 _25623 _18025 a)). Qed.
Lemma lem1106662 {_25617 _25623 : Type'} (h : prod _25623 _25617) (t : type1641 _25617 _25623) : (@cons (prod _25623 _25617) h t) = (@cons (prod _25623 _25617) h t).
Proof. exact (eq_refl (@cons (prod _25623 _25617) h t)). Qed.
Lemma lem1106663 {_25617 _25623 : Type'} (a : _25623) (h : prod _25623 _25617) (t : type1641 _25617 _25623) (ASSOC' : type1457 _25617 _25623) (_18025 : type1124 _25617 _25623) (h1 : ASSOC' = (term4 _25617 _25623 _18025)) : (term12 _25617 _25623 ASSOC' a h t) = (term13 _25617 _25623 _18025 a h t).
Proof. exact (MK_COMB (@lem1106661 _25617 _25623 a ASSOC' _18025 h1) (@lem1106662 _25617 _25623 h t)). Qed.
Lemma lem1106665 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1106642 A B f y) (@lem1106641 A B f y)). Qed.
Lemma lem1106666 {_25617 _25623 : Type'} (f : type1125 _25617 _25623) (y : type1641 _25617 _25623) : (term14 _25617 _25623 f y) = (f y).
Proof. exact (@lem1106665 (type1641 _25617 _25623) _25617 f y). Qed.
Lemma lem1106667 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (a : _25623) (h : prod _25623 _25617) (t : type1641 _25617 _25623) : (term15 _25617 _25623 _18025 a h t) = (term13 _25617 _25623 _18025 a h t).
Proof. exact (@lem1106666 _25617 _25623 (term8 _25617 _25623 _18025 a) (@cons (prod _25623 _25617) h t)). Qed.
Lemma lem1106668 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (_18024 : type1641 _25617 _25623) (a : _25623) : (term16 _25617 _25623 _18025 a _18024) = (_18025 _18024 a).
Proof. exact (eq_refl (term16 _25617 _25623 _18025 a _18024)). Qed.
Lemma lem1106669 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (a : _25623) : (term17 _25617 _25623 _18025 a) = (term8 _25617 _25623 _18025 a).
Proof. exact (fun_ext (fun _18024 : type1641 _25617 _25623 => @lem1106668 _25617 _25623 _18025 _18024 a)). Qed.
Lemma lem1106670 {_25617 _25623 : Type'} (h : prod _25623 _25617) (t : type1641 _25617 _25623) : (@cons (prod _25623 _25617) h t) = (@cons (prod _25623 _25617) h t).
Proof. exact (eq_refl (@cons (prod _25623 _25617) h t)). Qed.
Lemma lem1106671 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (a : _25623) (h : prod _25623 _25617) (t : type1641 _25617 _25623) : (term15 _25617 _25623 _18025 a h t) = (term13 _25617 _25623 _18025 a h t).
Proof. exact (MK_COMB (@lem1106669 _25617 _25623 _18025 a) (@lem1106670 _25617 _25623 h t)). Qed.
Lemma lem1106672 {_25617 : Type'} : (@eq _25617) = (@eq _25617).
Proof. exact (eq_refl (@eq _25617)). Qed.
Lemma lem1106673 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (a : _25623) (h : prod _25623 _25617) (t : type1641 _25617 _25623) : (term18 _25617 _25623 _18025 a h t) = (term19 _25617 _25623 _18025 a h t).
Proof. exact (MK_COMB (@lem1106672 _25617) (@lem1106671 _25617 _25623 _18025 a h t)). Qed.
Lemma lem1106674 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (h : prod _25623 _25617) (t : type1641 _25617 _25623) (a : _25623) : (term13 _25617 _25623 _18025 a h t) = (term20 _25617 _25623 _18025 h t a).
Proof. exact (eq_refl (term13 _25617 _25623 _18025 a h t)). Qed.
Lemma lem1106675 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (h : prod _25623 _25617) (t : type1641 _25617 _25623) (a : _25623) : ((term15 _25617 _25623 _18025 a h t) = (term13 _25617 _25623 _18025 a h t)) = ((term13 _25617 _25623 _18025 a h t) = (term20 _25617 _25623 _18025 h t a)).
Proof. exact (MK_COMB (@lem1106673 _25617 _25623 _18025 a h t) (@lem1106674 _25617 _25623 _18025 h t a)). Qed.
Lemma lem1106676 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (h : prod _25623 _25617) (t : type1641 _25617 _25623) (a : _25623) : (term13 _25617 _25623 _18025 a h t) = (term20 _25617 _25623 _18025 h t a).
Proof. exact (EQ_MP (@lem1106675 _25617 _25623 _18025 h t a) (@lem1106667 _25617 _25623 _18025 a h t)). Qed.
Lemma lem1106677 {_25617 _25623 : Type'} (h : prod _25623 _25617) (t : type1641 _25617 _25623) (a : _25623) (ASSOC' : type1457 _25617 _25623) (_18025 : type1124 _25617 _25623) (h1 : ASSOC' = (term4 _25617 _25623 _18025)) : (term12 _25617 _25623 ASSOC' a h t) = (term20 _25617 _25623 _18025 h t a).
Proof. exact (TRANS (@lem1106663 _25617 _25623 a h t ASSOC' _18025 h1) (@lem1106676 _25617 _25623 _18025 h t a)). Qed.
Lemma lem1106678 {_25617 : Type'} : (@eq _25617) = (@eq _25617).
Proof. exact (eq_refl (@eq _25617)). Qed.
Lemma lem1106679 {_25617 _25623 : Type'} (h : prod _25623 _25617) (t : type1641 _25617 _25623) (a : _25623) (ASSOC' : type1457 _25617 _25623) (_18025 : type1124 _25617 _25623) (h1 : ASSOC' = (term4 _25617 _25623 _18025)) : (term21 _25617 _25623 ASSOC' a h t) = (term22 _25617 _25623 _18025 h t a).
Proof. exact (MK_COMB (@lem1106678 _25617) (@lem1106677 _25617 _25623 h t a ASSOC' _18025 h1)). Qed.
Lemma lem1106681 {_25617 _25623 : Type'} (ASSOC' : type1457 _25617 _25623) (_18025 : type1124 _25617 _25623) (h1 : ASSOC' = (term4 _25617 _25623 _18025)) : ASSOC' = (term4 _25617 _25623 _18025).
Proof. exact (h1). Qed.
Lemma lem1106682 {_25623 : Type'} (a : _25623) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1106683 {_25617 _25623 : Type'} (a : _25623) (ASSOC' : type1457 _25617 _25623) (_18025 : type1124 _25617 _25623) (h1 : ASSOC' = (term4 _25617 _25623 _18025)) : (ASSOC' a) = (term5 _25617 _25623 _18025 a).
Proof. exact (MK_COMB (@lem1106681 _25617 _25623 ASSOC' _18025 h1) (@lem1106682 _25623 a)). Qed.
Lemma lem1106685 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1106642 A B f y) (@lem1106641 A B f y)). Qed.
Lemma lem1106686 {_25617 _25623 : Type'} (f : type1457 _25617 _25623) (y : _25623) : (term6 _25617 _25623 f y) = (f y).
Proof. exact (@lem1106685 _25623 (type1125 _25617 _25623) f y). Qed.
Lemma lem1106687 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (a : _25623) : (term7 _25617 _25623 _18025 a) = (term5 _25617 _25623 _18025 a).
Proof. exact (@lem1106686 _25617 _25623 (term4 _25617 _25623 _18025) a). Qed.
Lemma lem1106688 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (_18023 : _25623) : (term5 _25617 _25623 _18025 _18023) = (term8 _25617 _25623 _18025 _18023).
Proof. exact (eq_refl (term5 _25617 _25623 _18025 _18023)). Qed.
Lemma lem1106689 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) : (term9 _25617 _25623 _18025) = (term4 _25617 _25623 _18025).
Proof. exact (fun_ext (fun _18023 : _25623 => @lem1106688 _25617 _25623 _18025 _18023)). Qed.
Lemma lem1106690 {_25623 : Type'} (a : _25623) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1106691 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (a : _25623) : (term7 _25617 _25623 _18025 a) = (term5 _25617 _25623 _18025 a).
Proof. exact (MK_COMB (@lem1106689 _25617 _25623 _18025) (@lem1106690 _25623 a)). Qed.
Lemma lem1106692 {_25617 _25623 : Type'} : (@eq ((list (prod _25623 _25617)) -> _25617)) = (@eq ((list (prod _25623 _25617)) -> _25617)).
Proof. exact (eq_refl (@eq ((list (prod _25623 _25617)) -> _25617))). Qed.
Lemma lem1106693 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (a : _25623) : (term10 _25617 _25623 _18025 a) = (term11 _25617 _25623 _18025 a).
Proof. exact (MK_COMB (@lem1106692 _25617 _25623) (@lem1106691 _25617 _25623 _18025 a)). Qed.
Lemma lem1106694 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (a : _25623) : (term5 _25617 _25623 _18025 a) = (term8 _25617 _25623 _18025 a).
Proof. exact (eq_refl (term5 _25617 _25623 _18025 a)). Qed.
Lemma lem1106695 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (a : _25623) : ((term7 _25617 _25623 _18025 a) = (term5 _25617 _25623 _18025 a)) = ((term5 _25617 _25623 _18025 a) = (term8 _25617 _25623 _18025 a)).
Proof. exact (MK_COMB (@lem1106693 _25617 _25623 _18025 a) (@lem1106694 _25617 _25623 _18025 a)). Qed.
Lemma lem1106696 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (a : _25623) : (term5 _25617 _25623 _18025 a) = (term8 _25617 _25623 _18025 a).
Proof. exact (EQ_MP (@lem1106695 _25617 _25623 _18025 a) (@lem1106687 _25617 _25623 _18025 a)). Qed.
Lemma lem1106697 {_25617 _25623 : Type'} (a : _25623) (ASSOC' : type1457 _25617 _25623) (_18025 : type1124 _25617 _25623) (h1 : ASSOC' = (term4 _25617 _25623 _18025)) : (ASSOC' a) = (term8 _25617 _25623 _18025 a).
Proof. exact (TRANS (@lem1106683 _25617 _25623 a ASSOC' _18025 h1) (@lem1106696 _25617 _25623 _18025 a)). Qed.
Lemma lem1106698 {_25617 _25623 : Type'} (t : type1641 _25617 _25623) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1106699 {_25617 _25623 : Type'} (a : _25623) (t : type1641 _25617 _25623) (ASSOC' : type1457 _25617 _25623) (_18025 : type1124 _25617 _25623) (h1 : ASSOC' = (term4 _25617 _25623 _18025)) : (ASSOC' a t) = (term16 _25617 _25623 _18025 a t).
Proof. exact (MK_COMB (@lem1106697 _25617 _25623 a ASSOC' _18025 h1) (@lem1106698 _25617 _25623 t)). Qed.
Lemma lem1106701 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1106642 A B f y) (@lem1106641 A B f y)). Qed.
Lemma lem1106702 {_25617 _25623 : Type'} (f : type1125 _25617 _25623) (y : type1641 _25617 _25623) : (term14 _25617 _25623 f y) = (f y).
Proof. exact (@lem1106701 (type1641 _25617 _25623) _25617 f y). Qed.
Lemma lem1106703 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (a : _25623) (t : type1641 _25617 _25623) : (term23 _25617 _25623 _18025 a t) = (term16 _25617 _25623 _18025 a t).
Proof. exact (@lem1106702 _25617 _25623 (term8 _25617 _25623 _18025 a) t). Qed.
Lemma lem1106704 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (_18024 : type1641 _25617 _25623) (a : _25623) : (term16 _25617 _25623 _18025 a _18024) = (_18025 _18024 a).
Proof. exact (eq_refl (term16 _25617 _25623 _18025 a _18024)). Qed.
Lemma lem1106705 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (a : _25623) : (term17 _25617 _25623 _18025 a) = (term8 _25617 _25623 _18025 a).
Proof. exact (fun_ext (fun _18024 : type1641 _25617 _25623 => @lem1106704 _25617 _25623 _18025 _18024 a)). Qed.
Lemma lem1106706 {_25617 _25623 : Type'} (t : type1641 _25617 _25623) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1106707 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (a : _25623) (t : type1641 _25617 _25623) : (term23 _25617 _25623 _18025 a t) = (term16 _25617 _25623 _18025 a t).
Proof. exact (MK_COMB (@lem1106705 _25617 _25623 _18025 a) (@lem1106706 _25617 _25623 t)). Qed.
Lemma lem1106708 {_25617 : Type'} : (@eq _25617) = (@eq _25617).
Proof. exact (eq_refl (@eq _25617)). Qed.
Lemma lem1106709 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (a : _25623) (t : type1641 _25617 _25623) : (term24 _25617 _25623 _18025 a t) = (term25 _25617 _25623 _18025 a t).
Proof. exact (MK_COMB (@lem1106708 _25617) (@lem1106707 _25617 _25623 _18025 a t)). Qed.
Lemma lem1106710 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (t : type1641 _25617 _25623) (a : _25623) : (term16 _25617 _25623 _18025 a t) = (_18025 t a).
Proof. exact (eq_refl (term16 _25617 _25623 _18025 a t)). Qed.
Lemma lem1106711 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (t : type1641 _25617 _25623) (a : _25623) : ((term23 _25617 _25623 _18025 a t) = (term16 _25617 _25623 _18025 a t)) = ((term16 _25617 _25623 _18025 a t) = (_18025 t a)).
Proof. exact (MK_COMB (@lem1106709 _25617 _25623 _18025 a t) (@lem1106710 _25617 _25623 _18025 t a)). Qed.
Lemma lem1106712 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (t : type1641 _25617 _25623) (a : _25623) : (term16 _25617 _25623 _18025 a t) = (_18025 t a).
Proof. exact (EQ_MP (@lem1106711 _25617 _25623 _18025 t a) (@lem1106703 _25617 _25623 _18025 a t)). Qed.
Lemma lem1106713 {_25617 _25623 : Type'} (t : type1641 _25617 _25623) (a : _25623) (ASSOC' : type1457 _25617 _25623) (_18025 : type1124 _25617 _25623) (h1 : ASSOC' = (term4 _25617 _25623 _18025)) : (ASSOC' a t) = (_18025 t a).
Proof. exact (TRANS (@lem1106699 _25617 _25623 a t ASSOC' _18025 h1) (@lem1106712 _25617 _25623 _18025 t a)). Qed.
Lemma lem1106714 {_25617 _25623 : Type'} (a : _25623) (h : prod _25623 _25617) : (term26 _25617 _25623 a h) = (term26 _25617 _25623 a h).
Proof. exact (eq_refl (term26 _25617 _25623 a h)). Qed.
Lemma lem1106715 {_25617 _25623 : Type'} (h : prod _25623 _25617) (t : type1641 _25617 _25623) (a : _25623) (ASSOC' : type1457 _25617 _25623) (_18025 : type1124 _25617 _25623) (h1 : ASSOC' = (term4 _25617 _25623 _18025)) : (term27 _25617 _25623 h ASSOC' a t) = (term28 _25617 _25623 h _18025 t a).
Proof. exact (MK_COMB (@lem1106714 _25617 _25623 a h) (@lem1106713 _25617 _25623 t a ASSOC' _18025 h1)). Qed.
Lemma lem1106716 {_25617 _25623 : Type'} (h : prod _25623 _25617) (t : type1641 _25617 _25623) (a : _25623) (ASSOC' : type1457 _25617 _25623) (_18025 : type1124 _25617 _25623) (h1 : ASSOC' = (term4 _25617 _25623 _18025)) : ((term12 _25617 _25623 ASSOC' a h t) = (term27 _25617 _25623 h ASSOC' a t)) = ((term20 _25617 _25623 _18025 h t a) = (term28 _25617 _25623 h _18025 t a)).
Proof. exact (MK_COMB (@lem1106679 _25617 _25623 h t a ASSOC' _18025 h1) (@lem1106715 _25617 _25623 h t a ASSOC' _18025 h1)). Qed.
Lemma lem1106717 {_25617 _25623 : Type'} (h : prod _25623 _25617) (a : _25623) (ASSOC' : type1457 _25617 _25623) (_18025 : type1124 _25617 _25623) (h1 : ASSOC' = (term4 _25617 _25623 _18025)) : (term29 _25617 _25623 h ASSOC' a) = (term30 _25617 _25623 h _18025 a).
Proof. exact (fun_ext (fun t : type1641 _25617 _25623 => @lem1106716 _25617 _25623 h t a ASSOC' _18025 h1)). Qed.
Lemma lem1106718 {_25617 _25623 : Type'} : (@all (list (prod _25623 _25617))) = (@all (list (prod _25623 _25617))).
Proof. exact (eq_refl (@all (list (prod _25623 _25617)))). Qed.
Lemma lem1106719 {_25617 _25623 : Type'} (h : prod _25623 _25617) (a : _25623) (ASSOC' : type1457 _25617 _25623) (_18025 : type1124 _25617 _25623) (h1 : ASSOC' = (term4 _25617 _25623 _18025)) : (term31 _25617 _25623 h ASSOC' a) = (term32 _25617 _25623 h _18025 a).
Proof. exact (MK_COMB (@lem1106718 _25617 _25623) (@lem1106717 _25617 _25623 h a ASSOC' _18025 h1)). Qed.
Lemma lem1106720 {_25617 _25623 : Type'} (h : prod _25623 _25617) (ASSOC' : type1457 _25617 _25623) (_18025 : type1124 _25617 _25623) (h1 : ASSOC' = (term4 _25617 _25623 _18025)) : (term33 _25617 _25623 h ASSOC') = (term34 _25617 _25623 h _18025).
Proof. exact (fun_ext (fun a : _25623 => @lem1106719 _25617 _25623 h a ASSOC' _18025 h1)). Qed.
Lemma lem1106721 {_25623 : Type'} : (@all _25623) = (@all _25623).
Proof. exact (eq_refl (@all _25623)). Qed.
Lemma lem1106722 {_25617 _25623 : Type'} (h : prod _25623 _25617) (ASSOC' : type1457 _25617 _25623) (_18025 : type1124 _25617 _25623) (h1 : ASSOC' = (term4 _25617 _25623 _18025)) : (term35 _25617 _25623 h ASSOC') = (term36 _25617 _25623 h _18025).
Proof. exact (MK_COMB (@lem1106721 _25623) (@lem1106720 _25617 _25623 h ASSOC' _18025 h1)). Qed.
Lemma lem1106723 {_25617 _25623 : Type'} (ASSOC' : type1457 _25617 _25623) (_18025 : type1124 _25617 _25623) (h1 : ASSOC' = (term4 _25617 _25623 _18025)) : (term37 _25617 _25623 ASSOC') = (term38 _25617 _25623 _18025).
Proof. exact (fun_ext (fun h : prod _25623 _25617 => @lem1106722 _25617 _25623 h ASSOC' _18025 h1)). Qed.
Lemma lem1106724 {_25617 _25623 : Type'} : (@all (prod _25623 _25617)) = (@all (prod _25623 _25617)).
Proof. exact (eq_refl (@all (prod _25623 _25617))). Qed.
Lemma lem1106725 {_25617 _25623 : Type'} (ASSOC' : type1457 _25617 _25623) (_18025 : type1124 _25617 _25623) (h1 : ASSOC' = (term4 _25617 _25623 _18025)) : (term39 _25617 _25623 ASSOC') = (term40 _25617 _25623 _18025).
Proof. exact (MK_COMB (@lem1106724 _25617 _25623) (@lem1106723 _25617 _25623 ASSOC' _18025 h1)). Qed.
Lemma lem1106726 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (h1 : term41 _25617 _25623 _18025) : term41 _25617 _25623 _18025.
Proof. exact (h1). Qed.
Lemma lem1106727 {_25617 _25623 : Type'} (h : prod _25623 _25617) (_18025 : type1124 _25617 _25623) (h1 : term41 _25617 _25623 _18025) : term42 _25617 _25623 _18025 h.
Proof. exact (@lem1106726 _25617 _25623 _18025 h1 h). Qed.
Lemma lem1106728 {_25617 _25623 : Type'} (h : prod _25623 _25617) (_18025 : type1124 _25617 _25623) : (term42 _25617 _25623 _18025 h) = (term43 _25617 _25623 h _18025).
Proof. exact (eq_refl (term42 _25617 _25623 _18025 h)). Qed.
Lemma lem1106729 {_25617 _25623 : Type'} (h : prod _25623 _25617) (_18025 : type1124 _25617 _25623) (h1 : term41 _25617 _25623 _18025) : term43 _25617 _25623 h _18025.
Proof. exact (EQ_MP (@lem1106728 _25617 _25623 h _18025) (@lem1106727 _25617 _25623 h _18025 h1)). Qed.
Lemma lem1106730 {_25617 _25623 : Type'} (h : prod _25623 _25617) (t : type1641 _25617 _25623) (_18025 : type1124 _25617 _25623) (h1 : term41 _25617 _25623 _18025) : term44 _25617 _25623 h _18025 t.
Proof. exact (@lem1106729 _25617 _25623 h _18025 h1 t). Qed.
Lemma lem1106731 {_25617 _25623 : Type'} (h : prod _25623 _25617) (_18025 : type1124 _25617 _25623) (t : type1641 _25617 _25623) : (term44 _25617 _25623 h _18025 t) = ((term45 _25617 _25623 _18025 h t) = (term46 _25617 _25623 h _18025 t)).
Proof. exact (eq_refl (term44 _25617 _25623 h _18025 t)). Qed.
Lemma lem1106732 {_25617 _25623 : Type'} (h : prod _25623 _25617) (t : type1641 _25617 _25623) (_18025 : type1124 _25617 _25623) (h1 : term41 _25617 _25623 _18025) : (term45 _25617 _25623 _18025 h t) = (term46 _25617 _25623 h _18025 t).
Proof. exact (EQ_MP (@lem1106731 _25617 _25623 h _18025 t) (@lem1106730 _25617 _25623 h t _18025 h1)). Qed.
Lemma lem1106733 {_25623 : Type'} (a : _25623) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1106734 {_25617 _25623 : Type'} (h : prod _25623 _25617) (t : type1641 _25617 _25623) (a : _25623) (_18025 : type1124 _25617 _25623) (h1 : term41 _25617 _25623 _18025) : (term20 _25617 _25623 _18025 h t a) = (term47 _25617 _25623 h _18025 t a).
Proof. exact (MK_COMB (@lem1106732 _25617 _25623 h t _18025 h1) (@lem1106733 _25623 a)). Qed.
Lemma lem1106735 {_25617 _25623 : Type'} (h : prod _25623 _25617) (_18025 : type1124 _25617 _25623) (t : type1641 _25617 _25623) (a : _25623) : (term47 _25617 _25623 h _18025 t a) = (term28 _25617 _25623 h _18025 t a).
Proof. exact (eq_refl (term47 _25617 _25623 h _18025 t a)). Qed.
Lemma lem1106736 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (h : prod _25623 _25617) (t : type1641 _25617 _25623) (a : _25623) : (term22 _25617 _25623 _18025 h t a) = (term22 _25617 _25623 _18025 h t a).
Proof. exact (eq_refl (term22 _25617 _25623 _18025 h t a)). Qed.
Lemma lem1106737 {_25617 _25623 : Type'} (h : prod _25623 _25617) (_18025 : type1124 _25617 _25623) (t : type1641 _25617 _25623) (a : _25623) : ((term20 _25617 _25623 _18025 h t a) = (term47 _25617 _25623 h _18025 t a)) = ((term20 _25617 _25623 _18025 h t a) = (term28 _25617 _25623 h _18025 t a)).
Proof. exact (MK_COMB (@lem1106736 _25617 _25623 _18025 h t a) (@lem1106735 _25617 _25623 h _18025 t a)). Qed.
Lemma lem1106738 {_25617 _25623 : Type'} (h : prod _25623 _25617) (t : type1641 _25617 _25623) (a : _25623) (_18025 : type1124 _25617 _25623) (h1 : term41 _25617 _25623 _18025) : (term20 _25617 _25623 _18025 h t a) = (term28 _25617 _25623 h _18025 t a).
Proof. exact (EQ_MP (@lem1106737 _25617 _25623 h _18025 t a) (@lem1106734 _25617 _25623 h t a _18025 h1)). Qed.
Lemma lem1106739 {_25617 _25623 : Type'} (h : prod _25623 _25617) (a : _25623) (_18025 : type1124 _25617 _25623) (h1 : term41 _25617 _25623 _18025) : term32 _25617 _25623 h _18025 a.
Proof. exact (fun t : type1641 _25617 _25623 => @lem1106738 _25617 _25623 h t a _18025 h1). Qed.
Lemma lem1106740 {_25617 _25623 : Type'} (h : prod _25623 _25617) (_18025 : type1124 _25617 _25623) (h1 : term41 _25617 _25623 _18025) : term36 _25617 _25623 h _18025.
Proof. exact (fun a : _25623 => @lem1106739 _25617 _25623 h a _18025 h1). Qed.
Lemma lem1106741 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (h1 : term41 _25617 _25623 _18025) : term40 _25617 _25623 _18025.
Proof. exact (fun h : prod _25623 _25617 => @lem1106740 _25617 _25623 h _18025 h1). Qed.
Lemma lem1106742 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (h1 : term41 _25617 _25623 _18025) : term41 _25617 _25623 _18025.
Proof. exact (h1). Qed.
Lemma lem1106743 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (h1 : term41 _25617 _25623 _18025) : (term41 _25617 _25623 _18025) = (term40 _25617 _25623 _18025).
Proof. exact (prop_ext (fun h2 : term41 _25617 _25623 _18025 => @lem1106741 _25617 _25623 _18025 h1) (fun h2 : term40 _25617 _25623 _18025 => @lem1106742 _25617 _25623 _18025 h1)). Qed.
Lemma lem1106744 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (h1 : term41 _25617 _25623 _18025) : term40 _25617 _25623 _18025.
Proof. exact (EQ_MP (@lem1106743 _25617 _25623 _18025 h1) (@lem1106742 _25617 _25623 _18025 h1)). Qed.
Lemma lem1106745 {A Z : Type'} (NIL' : Z) : term48 A Z NIL'.
Proof. exact (@lem1072128 A Z NIL'). Qed.
Lemma lem1106746 {A Z : Type'} (NIL' : Z) : (term48 A Z NIL') = (term49 A Z NIL').
Proof. exact (eq_refl (term48 A Z NIL')). Qed.
Lemma lem1106747 {A Z : Type'} (NIL' : Z) : term49 A Z NIL'.
Proof. exact (EQ_MP (@lem1106746 A Z NIL') (@lem1106745 A Z NIL')). Qed.
Lemma lem1106748 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term50 A Z NIL' CONS'.
Proof. exact (@lem1106747 A Z NIL' CONS'). Qed.
Lemma lem1106749 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : (term50 A Z NIL' CONS') = (term51 A Z NIL' CONS').
Proof. exact (eq_refl (term50 A Z NIL' CONS')). Qed.
Lemma lem1106750 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term51 A Z NIL' CONS'.
Proof. exact (EQ_MP (@lem1106749 A Z NIL' CONS') (@lem1106748 A Z NIL' CONS')). Qed.
Lemma lem1106751 {_25617 _25623 : Type'} (NIL' : _25623 -> _25617) (CONS' : type1220 _25617 _25623) : term52 _25617 _25623 NIL' CONS'.
Proof. exact (@lem1106750 (prod _25623 _25617) (_25623 -> _25617) NIL' CONS'). Qed.
Lemma lem1106752 {_25617 _25623 : Type'} (NIL' : _25623 -> _25617) : term53 _25617 _25623 NIL'.
Proof. exact (@lem1106751 _25617 _25623 NIL' (term54 _25617 _25623)). Qed.
Lemma lem1106753 {_25617 _25623 : Type'} (a0 : prod _25623 _25617) : (term55 _25617 _25623 a0) = (term56 _25617 _25623 a0).
Proof. exact (eq_refl (term55 _25617 _25623 a0)). Qed.
Lemma lem1106754 {_25617 _25623 : Type'} (a1 : type1641 _25617 _25623) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem1106755 {_25617 _25623 : Type'} (a0 : prod _25623 _25617) (a1 : type1641 _25617 _25623) : (term57 _25617 _25623 a0 a1) = (term58 _25617 _25623 a0 a1).
Proof. exact (MK_COMB (@lem1106753 _25617 _25623 a0) (@lem1106754 _25617 _25623 a1)). Qed.
Lemma lem1106756 {_25617 _25623 : Type'} (a1 : type1641 _25617 _25623) (a0 : prod _25623 _25617) : (term58 _25617 _25623 a0 a1) = (term59 _25617 _25623 a0).
Proof. exact (eq_refl (term58 _25617 _25623 a0 a1)). Qed.
Lemma lem1106757 {_25617 _25623 : Type'} (a1 : type1641 _25617 _25623) (a0 : prod _25623 _25617) : (term57 _25617 _25623 a0 a1) = (term59 _25617 _25623 a0).
Proof. exact (TRANS (@lem1106755 _25617 _25623 a0 a1) (@lem1106756 _25617 _25623 a1 a0)). Qed.
Lemma lem1106758 {_25617 _25623 : Type'} (fn : type1124 _25617 _25623) (a1 : type1641 _25617 _25623) : (fn a1) = (fn a1).
Proof. exact (eq_refl (fn a1)). Qed.
Lemma lem1106759 {_25617 _25623 : Type'} (a0 : prod _25623 _25617) (fn : type1124 _25617 _25623) (a1 : type1641 _25617 _25623) : (term60 _25617 _25623 a0 fn a1) = (term61 _25617 _25623 a0 fn a1).
Proof. exact (MK_COMB (@lem1106757 _25617 _25623 a1 a0) (@lem1106758 _25617 _25623 fn a1)). Qed.
Lemma lem1106760 {_25617 _25623 : Type'} (a0 : prod _25623 _25617) (fn : type1124 _25617 _25623) (a1 : type1641 _25617 _25623) : (term61 _25617 _25623 a0 fn a1) = (term46 _25617 _25623 a0 fn a1).
Proof. exact (eq_refl (term61 _25617 _25623 a0 fn a1)). Qed.
Lemma lem1106761 {_25617 _25623 : Type'} (a0 : prod _25623 _25617) (fn : type1124 _25617 _25623) (a1 : type1641 _25617 _25623) : (term60 _25617 _25623 a0 fn a1) = (term46 _25617 _25623 a0 fn a1).
Proof. exact (TRANS (@lem1106759 _25617 _25623 a0 fn a1) (@lem1106760 _25617 _25623 a0 fn a1)). Qed.
Lemma lem1106762 {_25617 _25623 : Type'} (fn : type1124 _25617 _25623) (a0 : prod _25623 _25617) (a1 : type1641 _25617 _25623) : (term62 _25617 _25623 fn a0 a1) = (term62 _25617 _25623 fn a0 a1).
Proof. exact (eq_refl (term62 _25617 _25623 fn a0 a1)). Qed.
Lemma lem1106763 {_25617 _25623 : Type'} (a0 : prod _25623 _25617) (fn : type1124 _25617 _25623) (a1 : type1641 _25617 _25623) : ((term45 _25617 _25623 fn a0 a1) = (term60 _25617 _25623 a0 fn a1)) = ((term45 _25617 _25623 fn a0 a1) = (term46 _25617 _25623 a0 fn a1)).
Proof. exact (MK_COMB (@lem1106762 _25617 _25623 fn a0 a1) (@lem1106761 _25617 _25623 a0 fn a1)). Qed.
Lemma lem1106764 {_25617 _25623 : Type'} (a0 : prod _25623 _25617) (fn : type1124 _25617 _25623) : (term63 _25617 _25623 a0 fn) = (term64 _25617 _25623 a0 fn).
Proof. exact (fun_ext (fun a1 : type1641 _25617 _25623 => @lem1106763 _25617 _25623 a0 fn a1)). Qed.
Lemma lem1106765 {_25617 _25623 : Type'} : (@all (list (prod _25623 _25617))) = (@all (list (prod _25623 _25617))).
Proof. exact (eq_refl (@all (list (prod _25623 _25617)))). Qed.
Lemma lem1106766 {_25617 _25623 : Type'} (a0 : prod _25623 _25617) (fn : type1124 _25617 _25623) : (term65 _25617 _25623 a0 fn) = (term43 _25617 _25623 a0 fn).
Proof. exact (MK_COMB (@lem1106765 _25617 _25623) (@lem1106764 _25617 _25623 a0 fn)). Qed.
Lemma lem1106767 {_25617 _25623 : Type'} (fn : type1124 _25617 _25623) : (term66 _25617 _25623 fn) = (term67 _25617 _25623 fn).
Proof. exact (fun_ext (fun a0 : prod _25623 _25617 => @lem1106766 _25617 _25623 a0 fn)). Qed.
Lemma lem1106768 {_25617 _25623 : Type'} : (@all (prod _25623 _25617)) = (@all (prod _25623 _25617)).
Proof. exact (eq_refl (@all (prod _25623 _25617))). Qed.
Lemma lem1106769 {_25617 _25623 : Type'} (fn : type1124 _25617 _25623) : (term68 _25617 _25623 fn) = (term41 _25617 _25623 fn).
Proof. exact (MK_COMB (@lem1106768 _25617 _25623) (@lem1106767 _25617 _25623 fn)). Qed.
Lemma lem1106770 {_25617 _25623 : Type'} (fn : type1124 _25617 _25623) (NIL' : _25623 -> _25617) : (term69 _25617 _25623 fn NIL') = (term69 _25617 _25623 fn NIL').
Proof. exact (eq_refl (term69 _25617 _25623 fn NIL')). Qed.
Lemma lem1106771 {_25617 _25623 : Type'} (NIL' : _25623 -> _25617) (fn : type1124 _25617 _25623) : (term70 _25617 _25623 NIL' fn) = (term71 _25617 _25623 NIL' fn).
Proof. exact (MK_COMB (@lem1106770 _25617 _25623 fn NIL') (@lem1106769 _25617 _25623 fn)). Qed.
Lemma lem1106772 {_25617 _25623 : Type'} (NIL' : _25623 -> _25617) : (term72 _25617 _25623 NIL') = (term73 _25617 _25623 NIL').
Proof. exact (fun_ext (fun fn : type1124 _25617 _25623 => @lem1106771 _25617 _25623 NIL' fn)). Qed.
Lemma lem1106773 {_25617 _25623 : Type'} : (@ex ((list (prod _25623 _25617)) -> _25623 -> _25617)) = (@ex ((list (prod _25623 _25617)) -> _25623 -> _25617)).
Proof. exact (eq_refl (@ex ((list (prod _25623 _25617)) -> _25623 -> _25617))). Qed.
Lemma lem1106774 {_25617 _25623 : Type'} (NIL' : _25623 -> _25617) : (term53 _25617 _25623 NIL') = (term74 _25617 _25623 NIL').
Proof. exact (MK_COMB (@lem1106773 _25617 _25623) (@lem1106772 _25617 _25623 NIL')). Qed.
Lemma lem1106775 {_25617 _25623 : Type'} (NIL' : _25623 -> _25617) : term74 _25617 _25623 NIL'.
Proof. exact (EQ_MP (@lem1106774 _25617 _25623 NIL') (@lem1106752 _25617 _25623 NIL')). Qed.
Lemma lem1106776 {_25617 _25623 : Type'} (NIL' : _25623 -> _25617) (_18025 : type1124 _25617 _25623) (h1 : term71 _25617 _25623 NIL' _18025) : term71 _25617 _25623 NIL' _18025.
Proof. exact (h1). Qed.
Lemma lem1106777 {_25617 _25623 : Type'} (NIL' : _25623 -> _25617) (_18025 : type1124 _25617 _25623) (h1 : term71 _25617 _25623 NIL' _18025) : term41 _25617 _25623 _18025.
Proof. exact (proj2 (@lem1106776 _25617 _25623 NIL' _18025 h1)). Qed.
Lemma lem1106779 {_25617 _25623 : Type'} (NIL' : _25623 -> _25617) (_18025 : type1124 _25617 _25623) (h1 : term71 _25617 _25623 NIL' _18025) : term75 _25617 _25623.
Proof. exact (ex_intro (term76 _25617 _25623) _18025 (@lem1106777 _25617 _25623 NIL' _18025 h1)). Qed.
Lemma lem1106780 {_25617 _25623 : Type'} (NIL' : _25623 -> _25617) (h1 : term74 _25617 _25623 NIL') : term74 _25617 _25623 NIL'.
Proof. exact (h1). Qed.
Lemma lem1106781 {_25617 _25623 : Type'} (NIL' : _25623 -> _25617) (h1 : term74 _25617 _25623 NIL') : term75 _25617 _25623.
Proof. exact (ex_elim (@lem1106780 _25617 _25623 NIL' h1) (fun _18025 : type1124 _25617 _25623 => fun h0 : term73 _25617 _25623 NIL' _18025 => @lem1106779 _25617 _25623 NIL' _18025 h0)). Qed.
Lemma lem1106782 {_25617 _25623 : Type'} (NIL' : _25623 -> _25617) : (term74 _25617 _25623 NIL') = (term75 _25617 _25623).
Proof. exact (prop_ext (fun h1 : term74 _25617 _25623 NIL' => @lem1106781 _25617 _25623 NIL' h1) (fun h1 : term75 _25617 _25623 => @lem1106775 _25617 _25623 NIL')). Qed.
Lemma lem1106783 {_25617 _25623 : Type'} : term75 _25617 _25623.
Proof. exact (EQ_MP (@lem1106782 _25617 _25623 (@el (_25623 -> _25617))) (@lem1106775 _25617 _25623 (@el (_25623 -> _25617)))). Qed.
Lemma lem1106784 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (h1 : term41 _25617 _25623 _18025) : term77 _25617 _25623.
Proof. exact (ex_intro (term78 _25617 _25623) _18025 (@lem1106744 _25617 _25623 _18025 h1)). Qed.
Lemma lem1106785 {_25617 _25623 : Type'} (h1 : term75 _25617 _25623) : term75 _25617 _25623.
Proof. exact (h1). Qed.
Lemma lem1106786 {_25617 _25623 : Type'} (h1 : term75 _25617 _25623) : term77 _25617 _25623.
Proof. exact (ex_elim (@lem1106785 _25617 _25623 h1) (fun _18025 : type1124 _25617 _25623 => fun h0 : term76 _25617 _25623 _18025 => @lem1106784 _25617 _25623 _18025 h0)). Qed.
Lemma lem1106787 {_25617 _25623 : Type'} : (term75 _25617 _25623) = (term77 _25617 _25623).
Proof. exact (prop_ext (fun h1 : term75 _25617 _25623 => @lem1106786 _25617 _25623 h1) (fun h1 : term77 _25617 _25623 => @lem1106783 _25617 _25623)). Qed.
Lemma lem1106788 {_25617 _25623 : Type'} : term77 _25617 _25623.
Proof. exact (EQ_MP (@lem1106787 _25617 _25623) (@lem1106783 _25617 _25623)). Qed.
Lemma lem1106789 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (h1 : term40 _25617 _25623 _18025) : term40 _25617 _25623 _18025.
Proof. exact (h1). Qed.
Lemma lem1106790 {_25617 _25623 : Type'} (ASSOC' : type1457 _25617 _25623) (_18025 : type1124 _25617 _25623) (h1 : ASSOC' = (term4 _25617 _25623 _18025)) : (term40 _25617 _25623 _18025) = (term39 _25617 _25623 ASSOC').
Proof. exact (SYM (@lem1106725 _25617 _25623 ASSOC' _18025 h1)). Qed.
Lemma lem1106791 {_25617 _25623 : Type'} (ASSOC' : type1457 _25617 _25623) (_18025 : type1124 _25617 _25623) (h1 : term40 _25617 _25623 _18025) (h2 : ASSOC' = (term4 _25617 _25623 _18025)) : term39 _25617 _25623 ASSOC'.
Proof. exact (EQ_MP (@lem1106790 _25617 _25623 ASSOC' _18025 h2) (@lem1106789 _25617 _25623 _18025 h1)). Qed.
Lemma lem1106792 {_25617 _25623 : Type'} (ASSOC' : type1457 _25617 _25623) (_18025 : type1124 _25617 _25623) (h1 : term40 _25617 _25623 _18025) (h2 : ASSOC' = (term4 _25617 _25623 _18025)) : term79 _25617 _25623.
Proof. exact (ex_intro (term80 _25617 _25623) ASSOC' (@lem1106791 _25617 _25623 ASSOC' _18025 h1 h2)). Qed.
Lemma lem1106793 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) : (term4 _25617 _25623 _18025) = (term4 _25617 _25623 _18025).
Proof. exact (eq_refl (term4 _25617 _25623 _18025)). Qed.
Lemma lem1106794 {_25617 _25623 : Type'} (ASSOC' : type1457 _25617 _25623) (_18025 : type1124 _25617 _25623) (h1 : term40 _25617 _25623 _18025) : term81 _25617 _25623 ASSOC' _18025.
Proof. exact (fun h0 : ASSOC' = (term4 _25617 _25623 _18025) => @lem1106792 _25617 _25623 ASSOC' _18025 h1 h0). Qed.
Lemma lem1106795 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (h1 : term40 _25617 _25623 _18025) : term82 _25617 _25623 _18025.
Proof. exact (@lem1106794 _25617 _25623 (term4 _25617 _25623 _18025) _18025 h1). Qed.
Lemma lem1106796 {_25617 _25623 : Type'} (_18025 : type1124 _25617 _25623) (h1 : term40 _25617 _25623 _18025) : term79 _25617 _25623.
Proof. exact (@lem1106795 _25617 _25623 _18025 h1 (@lem1106793 _25617 _25623 _18025)). Qed.
Lemma lem1106797 {_25617 _25623 : Type'} (h1 : term77 _25617 _25623) : term77 _25617 _25623.
Proof. exact (h1). Qed.
Lemma lem1106798 {_25617 _25623 : Type'} (h1 : term77 _25617 _25623) : term79 _25617 _25623.
Proof. exact (ex_elim (@lem1106797 _25617 _25623 h1) (fun _18025 : type1124 _25617 _25623 => fun h0 : term78 _25617 _25623 _18025 => @lem1106796 _25617 _25623 _18025 h0)). Qed.
Lemma lem1106799 {_25617 _25623 : Type'} : (term77 _25617 _25623) = (term79 _25617 _25623).
Proof. exact (prop_ext (fun h1 : term77 _25617 _25623 => @lem1106798 _25617 _25623 h1) (fun h1 : term79 _25617 _25623 => @lem1106788 _25617 _25623)). Qed.
Lemma lem1106800 {_25617 _25623 : Type'} : term79 _25617 _25623.
Proof. exact (EQ_MP (@lem1106799 _25617 _25623) (@lem1106788 _25617 _25623)). Qed.
Lemma lem1106801 {_25617 _25623 : Type'} : term83 _25617 _25623.
Proof. exact (fun _18029 : type1672 => @lem1106800 _25617 _25623). Qed.
Lemma lem1106802 {A B : Type'} (P : type1413 A B) : term84 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1106803 {A B : Type'} (P : type1413 A B) : (term84 A B P) = ((term85 A B P) = (term86 A B P)).
Proof. exact (eq_refl (term84 A B P)). Qed.
Lemma lem1106806 {A B : Type'} (P : type1413 A B) : (term85 A B P) = (term86 A B P).
Proof. exact (EQ_MP (@lem1106803 A B P) (@lem1106802 A B P)). Qed.
Lemma lem1106807 {_25617 _25623 : Type'} (P : type1274 _25617 _25623) : (term87 _25617 _25623 P) = (term88 _25617 _25623 P).
Proof. exact (@lem1106806 type1672 (type1457 _25617 _25623) P). Qed.
Lemma lem1106808 {_25617 _25623 : Type'} : (term89 _25617 _25623) = (term90 _25617 _25623).
Proof. exact (@lem1106807 _25617 _25623 (term91 _25617 _25623)). Qed.
Lemma lem1106809 {_25617 _25623 : Type'} (_18029 : type1672) : (term92 _25617 _25623 _18029) = (term80 _25617 _25623).
Proof. exact (eq_refl (term92 _25617 _25623 _18029)). Qed.
Lemma lem1106810 {_25617 _25623 : Type'} (ASSOC' : type1457 _25617 _25623) : ASSOC' = ASSOC'.
Proof. exact (eq_refl ASSOC'). Qed.
Lemma lem1106811 {_25617 _25623 : Type'} (_18029 : type1672) (ASSOC' : type1457 _25617 _25623) : (term93 _25617 _25623 _18029 ASSOC') = (term94 _25617 _25623 ASSOC').
Proof. exact (MK_COMB (@lem1106809 _25617 _25623 _18029) (@lem1106810 _25617 _25623 ASSOC')). Qed.
Lemma lem1106812 {_25617 _25623 : Type'} (ASSOC' : type1457 _25617 _25623) : (term94 _25617 _25623 ASSOC') = (term39 _25617 _25623 ASSOC').
Proof. exact (eq_refl (term94 _25617 _25623 ASSOC')). Qed.
Lemma lem1106813 {_25617 _25623 : Type'} (_18029 : type1672) (ASSOC' : type1457 _25617 _25623) : (term93 _25617 _25623 _18029 ASSOC') = (term39 _25617 _25623 ASSOC').
Proof. exact (TRANS (@lem1106811 _25617 _25623 _18029 ASSOC') (@lem1106812 _25617 _25623 ASSOC')). Qed.
Lemma lem1106814 {_25617 _25623 : Type'} (_18029 : type1672) : (term95 _25617 _25623 _18029) = (term80 _25617 _25623).
Proof. exact (fun_ext (fun ASSOC' : type1457 _25617 _25623 => @lem1106813 _25617 _25623 _18029 ASSOC')). Qed.
Lemma lem1106815 {_25617 _25623 : Type'} : (@ex (_25623 -> (list (prod _25623 _25617)) -> _25617)) = (@ex (_25623 -> (list (prod _25623 _25617)) -> _25617)).
Proof. exact (eq_refl (@ex (_25623 -> (list (prod _25623 _25617)) -> _25617))). Qed.
Lemma lem1106816 {_25617 _25623 : Type'} (_18029 : type1672) : (term96 _25617 _25623 _18029) = (term79 _25617 _25623).
Proof. exact (MK_COMB (@lem1106815 _25617 _25623) (@lem1106814 _25617 _25623 _18029)). Qed.
Lemma lem1106817 {_25617 _25623 : Type'} : (term97 _25617 _25623) = (term98 _25617 _25623).
Proof. exact (fun_ext (fun _18029 : type1672 => @lem1106816 _25617 _25623 _18029)). Qed.
Lemma lem1106818 : (@all (prod nat (prod nat (prod nat (prod nat nat))))) = (@all (prod nat (prod nat (prod nat (prod nat nat))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat nat)))))). Qed.
Lemma lem1106819 {_25617 _25623 : Type'} : (term89 _25617 _25623) = (term83 _25617 _25623).
Proof. exact (MK_COMB (@lem1106818) (@lem1106817 _25617 _25623)). Qed.
Lemma lem1106820 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1106821 {_25617 _25623 : Type'} : (term99 _25617 _25623) = (term100 _25617 _25623).
Proof. exact (MK_COMB (@lem1106820) (@lem1106819 _25617 _25623)). Qed.
Lemma lem1106822 {_25617 _25623 : Type'} (_18029 : type1672) : (term92 _25617 _25623 _18029) = (term80 _25617 _25623).
Proof. exact (eq_refl (term92 _25617 _25623 _18029)). Qed.
Lemma lem1106823 {_25617 _25623 : Type'} (ASSOC' : type1276 _25617 _25623) (_18029 : type1672) : (ASSOC' _18029) = (ASSOC' _18029).
Proof. exact (eq_refl (ASSOC' _18029)). Qed.
Lemma lem1106824 {_25617 _25623 : Type'} (ASSOC' : type1276 _25617 _25623) (_18029 : type1672) : (term101 _25617 _25623 ASSOC' _18029) = (term102 _25617 _25623 ASSOC' _18029).
Proof. exact (MK_COMB (@lem1106822 _25617 _25623 _18029) (@lem1106823 _25617 _25623 ASSOC' _18029)). Qed.
Lemma lem1106825 {_25617 _25623 : Type'} (ASSOC' : type1276 _25617 _25623) (_18029 : type1672) : (term102 _25617 _25623 ASSOC' _18029) = (term103 _25617 _25623 ASSOC' _18029).
Proof. exact (eq_refl (term102 _25617 _25623 ASSOC' _18029)). Qed.
Lemma lem1106826 {_25617 _25623 : Type'} (ASSOC' : type1276 _25617 _25623) (_18029 : type1672) : (term101 _25617 _25623 ASSOC' _18029) = (term103 _25617 _25623 ASSOC' _18029).
Proof. exact (TRANS (@lem1106824 _25617 _25623 ASSOC' _18029) (@lem1106825 _25617 _25623 ASSOC' _18029)). Qed.
Lemma lem1106827 {_25617 _25623 : Type'} (ASSOC' : type1276 _25617 _25623) : (term104 _25617 _25623 ASSOC') = (term105 _25617 _25623 ASSOC').
Proof. exact (fun_ext (fun _18029 : type1672 => @lem1106826 _25617 _25623 ASSOC' _18029)). Qed.
Lemma lem1106828 : (@all (prod nat (prod nat (prod nat (prod nat nat))))) = (@all (prod nat (prod nat (prod nat (prod nat nat))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat nat)))))). Qed.
Lemma lem1106829 {_25617 _25623 : Type'} (ASSOC' : type1276 _25617 _25623) : (term106 _25617 _25623 ASSOC') = (term107 _25617 _25623 ASSOC').
Proof. exact (MK_COMB (@lem1106828) (@lem1106827 _25617 _25623 ASSOC')). Qed.
Lemma lem1106830 {_25617 _25623 : Type'} : (term108 _25617 _25623) = (term109 _25617 _25623).
Proof. exact (fun_ext (fun ASSOC' : type1276 _25617 _25623 => @lem1106829 _25617 _25623 ASSOC')). Qed.
Lemma lem1106831 {_25617 _25623 : Type'} : (@ex ((prod nat (prod nat (prod nat (prod nat nat)))) -> _25623 -> (list (prod _25623 _25617)) -> _25617)) = (@ex ((prod nat (prod nat (prod nat (prod nat nat)))) -> _25623 -> (list (prod _25623 _25617)) -> _25617)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat (prod nat (prod nat nat)))) -> _25623 -> (list (prod _25623 _25617)) -> _25617))). Qed.
Lemma lem1106832 {_25617 _25623 : Type'} : (term90 _25617 _25623) = (term110 _25617 _25623).
Proof. exact (MK_COMB (@lem1106831 _25617 _25623) (@lem1106830 _25617 _25623)). Qed.
Lemma lem1106833 {_25617 _25623 : Type'} : ((term89 _25617 _25623) = (term90 _25617 _25623)) = ((term83 _25617 _25623) = (term110 _25617 _25623)).
Proof. exact (MK_COMB (@lem1106821 _25617 _25623) (@lem1106832 _25617 _25623)). Qed.
Lemma lem1106834 {_25617 _25623 : Type'} : (term83 _25617 _25623) = (term110 _25617 _25623).
Proof. exact (EQ_MP (@lem1106833 _25617 _25623) (@lem1106808 _25617 _25623)). Qed.
Lemma lem1106835 {_25617 _25623 : Type'} : term110 _25617 _25623.
Proof. exact (EQ_MP (@lem1106834 _25617 _25623) (@lem1106801 _25617 _25623)). Qed.
Lemma lem1106837 {A : Type'} : (@ex A) = (term111 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem1106838 {_25617 _25623 : Type'} : (@ex ((prod nat (prod nat (prod nat (prod nat nat)))) -> _25623 -> (list (prod _25623 _25617)) -> _25617)) = (term112 _25617 _25623).
Proof. exact (@lem1106837 (type1276 _25617 _25623)). Qed.
Lemma lem1106839 {_25617 _25623 : Type'} : (term109 _25617 _25623) = (term109 _25617 _25623).
Proof. exact (eq_refl (term109 _25617 _25623)). Qed.
Lemma lem1106840 {_25617 _25623 : Type'} : (term110 _25617 _25623) = (term113 _25617 _25623).
Proof. exact (MK_COMB (@lem1106838 _25617 _25623) (@lem1106839 _25617 _25623)). Qed.
Lemma lem1106841 {_25617 _25623 : Type'} : (term113 _25617 _25623) = (term114 _25617 _25623).
Proof. exact (eq_refl (term113 _25617 _25623)). Qed.
Lemma lem1106842 {_25617 _25623 : Type'} : (term110 _25617 _25623) = (term114 _25617 _25623).
Proof. exact (TRANS (@lem1106840 _25617 _25623) (@lem1106841 _25617 _25623)). Qed.
Lemma lem1106843 {_25617 _25623 : Type'} : term114 _25617 _25623.
Proof. exact (EQ_MP (@lem1106842 _25617 _25623) (@lem1106835 _25617 _25623)). Qed.
