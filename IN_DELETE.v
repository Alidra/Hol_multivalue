Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IN_DELETE_term_abbrevs.
Require Import DELETE_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Lemma lem3205666 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3193179 A s). Qed.
Lemma lem3205667 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem3205668 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem3205667 A s) (@lem3205666 A s)). Qed.
Lemma lem3205669 {A : Type'} (s : A -> Prop) (x : A) : term2 A s x.
Proof. exact (@lem3205668 A s x). Qed.
Lemma lem3205670 {A : Type'} (s : A -> Prop) (x : A) : (term2 A s x) = ((@DELETE A s x) = (term3 A s x)).
Proof. exact (eq_refl (term2 A s x)). Qed.
Lemma lem3205696 {_83095 : Type'} : term4 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem3205697 {_83095 : Type'} (p : _83095 -> Prop) : term5 _83095 p.
Proof. exact (@lem3205696 _83095 p). Qed.
Lemma lem3205698 {_83095 : Type'} (p : _83095 -> Prop) : (term5 _83095 p) = (term6 _83095 p).
Proof. exact (eq_refl (term5 _83095 p)). Qed.
Lemma lem3205699 {_83095 : Type'} (p : _83095 -> Prop) : term6 _83095 p.
Proof. exact (EQ_MP (@lem3205698 _83095 p) (@lem3205697 _83095 p)). Qed.
Lemma lem3205700 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term7 _83095 p x.
Proof. exact (@lem3205699 _83095 p x). Qed.
Lemma lem3205701 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term7 _83095 p x) = ((term8 _83095 x p) = (p x)).
Proof. exact (eq_refl (term7 _83095 p x)). Qed.
Lemma lem3205725 {A : Type'} (s : A -> Prop) (x : A) : (@DELETE A s x) = (term3 A s x).
Proof. exact (EQ_MP (@lem3205670 A s x) (@lem3205669 A s x)). Qed.
Lemma lem3205726 {A : Type'} (s : A -> Prop) (x : A) : (@DELETE A s x) = (term3 A s x).
Proof. exact (@lem3205725 A s x). Qed.
Lemma lem3205727 {A : Type'} (s : A -> Prop) (y : A) : (@DELETE A s y) = (term3 A s y).
Proof. exact (@lem3205726 A s y). Qed.
Lemma lem3205736 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3205737 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term9 A x s y) = (term10 A x s y).
Proof. exact (MK_COMB (@lem3205736 A x) (@lem3205727 A s y)). Qed.
Lemma lem3205739 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term8 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3205701 _83095 p x) (@lem3205700 _83095 p x)). Qed.
Lemma lem3205740 {A : Type'} (p : A -> Prop) (x : A) : (term8 A x p) = (p x).
Proof. exact (@lem3205739 A p x). Qed.
Lemma lem3205741 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term11 A x s y) = (term12 A s y x).
Proof. exact (@lem3205740 A (term13 A s y) x). Qed.
Lemma lem3205742 {A : Type'} (s : A -> Prop) (y' : A) (y : A) : (term12 A s y y') = (term14 A s y' y).
Proof. exact (eq_refl (term12 A s y y')). Qed.
Lemma lem3205743 {A : Type'} (GEN_PVAR_6 : A) : (@SETSPEC A GEN_PVAR_6) = (@SETSPEC A GEN_PVAR_6).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_6)). Qed.
Lemma lem3205744 {A : Type'} (GEN_PVAR_6 : A) (s : A -> Prop) (y' : A) (y : A) : (term15 A GEN_PVAR_6 s y y') = (term16 A GEN_PVAR_6 s y' y).
Proof. exact (MK_COMB (@lem3205743 A GEN_PVAR_6) (@lem3205742 A s y' y)). Qed.
Lemma lem3205745 {A : Type'} (y' : A) : y' = y'.
Proof. exact (eq_refl y'). Qed.
Lemma lem3205746 {A : Type'} (GEN_PVAR_6 : A) (s : A -> Prop) (y : A) (y' : A) : (term17 A GEN_PVAR_6 s y y') = (term18 A GEN_PVAR_6 s y y').
Proof. exact (MK_COMB (@lem3205744 A GEN_PVAR_6 s y' y) (@lem3205745 A y')). Qed.
Lemma lem3205747 {A : Type'} (GEN_PVAR_6 : A) (s : A -> Prop) (y : A) : (term19 A GEN_PVAR_6 s y) = (term20 A GEN_PVAR_6 s y).
Proof. exact (fun_ext (fun y' : A => @lem3205746 A GEN_PVAR_6 s y y')). Qed.
Lemma lem3205748 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3205749 {A : Type'} (GEN_PVAR_6 : A) (s : A -> Prop) (y : A) : (term21 A GEN_PVAR_6 s y) = (term22 A GEN_PVAR_6 s y).
Proof. exact (MK_COMB (@lem3205748 A) (@lem3205747 A GEN_PVAR_6 s y)). Qed.
Lemma lem3205750 {A : Type'} (s : A -> Prop) (y : A) : (term23 A s y) = (term24 A s y).
Proof. exact (fun_ext (fun GEN_PVAR_6 : A => @lem3205749 A GEN_PVAR_6 s y)). Qed.
Lemma lem3205751 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3205752 {A : Type'} (s : A -> Prop) (y : A) : (term25 A s y) = (term3 A s y).
Proof. exact (MK_COMB (@lem3205751 A) (@lem3205750 A s y)). Qed.
Lemma lem3205753 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3205754 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term11 A x s y) = (term10 A x s y).
Proof. exact (MK_COMB (@lem3205753 A x) (@lem3205752 A s y)). Qed.
Lemma lem3205755 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3205756 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term26 A x s y) = (term27 A x s y).
Proof. exact (MK_COMB (@lem3205755) (@lem3205754 A x s y)). Qed.
Lemma lem3205757 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term12 A s y x) = (term14 A s x y).
Proof. exact (eq_refl (term12 A s y x)). Qed.
Lemma lem3205758 {A : Type'} (s : A -> Prop) (x : A) (y : A) : ((term11 A x s y) = (term12 A s y x)) = ((term10 A x s y) = (term14 A s x y)).
Proof. exact (MK_COMB (@lem3205756 A x s y) (@lem3205757 A s x y)). Qed.
Lemma lem3205759 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term10 A x s y) = (term14 A s x y).
Proof. exact (EQ_MP (@lem3205758 A s x y) (@lem3205741 A s y x)). Qed.
Lemma lem3205764 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term9 A x s y) = (term14 A s x y).
Proof. exact (TRANS (@lem3205737 A x s y) (@lem3205759 A s x y)). Qed.
Lemma lem3205765 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3205766 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term28 A x s y) = (term29 A s x y).
Proof. exact (MK_COMB (@lem3205765) (@lem3205764 A s x y)). Qed.
Lemma lem3205771 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term14 A s x y) = (term14 A s x y).
Proof. exact (eq_refl (term14 A s x y)). Qed.
Lemma lem3205772 {A : Type'} (s : A -> Prop) (x : A) (y : A) : ((term9 A x s y) = (term14 A s x y)) = ((term14 A s x y) = (term14 A s x y)).
Proof. exact (MK_COMB (@lem3205766 A s x y) (@lem3205771 A s x y)). Qed.
Lemma lem3205774 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3205775 (x : Prop) : (x = x) = True.
Proof. exact (@lem3205774 Prop x). Qed.
Lemma lem3205776 {A : Type'} (s : A -> Prop) (x : A) (y : A) : ((term14 A s x y) = (term14 A s x y)) = True.
Proof. exact (@lem3205775 (term14 A s x y)). Qed.
Lemma lem3205777 {A : Type'} (s : A -> Prop) (x : A) (y : A) : ((term9 A x s y) = (term14 A s x y)) = True.
Proof. exact (TRANS (@lem3205772 A s x y) (@lem3205776 A s x y)). Qed.
Lemma lem3205778 {A : Type'} (s : A -> Prop) (x : A) : (term30 A s x) = (term31 A).
Proof. exact (fun_ext (fun y : A => @lem3205777 A s x y)). Qed.
Lemma lem3205779 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3205780 {A : Type'} (s : A -> Prop) (x : A) : (term32 A s x) = (term33 A).
Proof. exact (MK_COMB (@lem3205779 A) (@lem3205778 A s x)). Qed.
Lemma lem3205782 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3205783 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (@lem3205782 A t). Qed.
Lemma lem3205784 {A : Type'} : (term33 A) = True.
Proof. exact (@lem3205783 A True). Qed.
Lemma lem3205785 {A : Type'} (s : A -> Prop) (x : A) : (term32 A s x) = True.
Proof. exact (TRANS (@lem3205780 A s x) (@lem3205784 A)). Qed.
Lemma lem3205786 {A : Type'} (s : A -> Prop) : (term35 A s) = (term31 A).
Proof. exact (fun_ext (fun x : A => @lem3205785 A s x)). Qed.
Lemma lem3205787 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3205788 {A : Type'} (s : A -> Prop) : (term36 A s) = (term33 A).
Proof. exact (MK_COMB (@lem3205787 A) (@lem3205786 A s)). Qed.
Lemma lem3205790 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3205791 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (@lem3205790 A t). Qed.
Lemma lem3205792 {A : Type'} : (term33 A) = True.
Proof. exact (@lem3205791 A True). Qed.
Lemma lem3205793 {A : Type'} (s : A -> Prop) : (term36 A s) = True.
Proof. exact (TRANS (@lem3205788 A s) (@lem3205792 A)). Qed.
Lemma lem3205794 {A : Type'} : (term37 A) = (term38 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3205793 A s)). Qed.
Lemma lem3205795 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3205796 {A : Type'} : (term39 A) = (term40 A).
Proof. exact (MK_COMB (@lem3205795 A) (@lem3205794 A)). Qed.
Lemma lem3205798 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3205799 {A : Type'} (t : Prop) : (term41 A t) = t.
Proof. exact (@lem3205798 (A -> Prop) t). Qed.
Lemma lem3205800 {A : Type'} : (term40 A) = True.
Proof. exact (@lem3205799 A True). Qed.
Lemma lem3205801 {A : Type'} : (term39 A) = True.
Proof. exact (TRANS (@lem3205796 A) (@lem3205800 A)). Qed.
Lemma lem3205802 {A : Type'} : True = (term39 A).
Proof. exact (SYM (@lem3205801 A)). Qed.
Lemma lem3205803 {A : Type'} : term39 A.
Proof. exact (EQ_MP (@lem3205802 A) (@lem0)). Qed.
