Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CROSS_EQ_EMPTY_term_abbrevs.
Require Import EXTENSION_spec.
Require Import FORALL_PAIR_THM_spec.
Require Import IN_CROSS_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm1857_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18940_spec.
Require Import thm18941_spec.
Require Import thm18946_spec.
Require Import thm18947_spec.
Require Import thm18958_spec.
Require Import thm18959_spec.
Require Import thm18964_spec.
Require Import thm18965_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm82_spec.
Lemma lem4325710 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem4325711 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem4325712 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem4325711 A x) (@lem4325710 A x)). Qed.
Lemma lem4325713 {A : Type'} (x : A) : term2 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem4325715 {_103718 _103721 : Type'} (x : _103718) : term3 _103718 _103721 x.
Proof. exact (@lem4325365 _103718 _103721 x). Qed.
Lemma lem4325716 {_103718 _103721 : Type'} (x : _103718) : (term3 _103718 _103721 x) = (term4 _103718 _103721 x).
Proof. exact (eq_refl (term3 _103718 _103721 x)). Qed.
Lemma lem4325717 {_103718 _103721 : Type'} (x : _103718) : term4 _103718 _103721 x.
Proof. exact (EQ_MP (@lem4325716 _103718 _103721 x) (@lem4325715 _103718 _103721 x)). Qed.
Lemma lem4325718 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term5 _103718 _103721 x y.
Proof. exact (@lem4325717 _103718 _103721 x y). Qed.
Lemma lem4325719 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : (term5 _103718 _103721 x y) = (term6 _103718 _103721 x y).
Proof. exact (eq_refl (term5 _103718 _103721 x y)). Qed.
Lemma lem4325720 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term6 _103718 _103721 x y.
Proof. exact (EQ_MP (@lem4325719 _103718 _103721 x y) (@lem4325718 _103718 _103721 x y)). Qed.
Lemma lem4325721 {_103718 _103721 : Type'} (x : _103718) (y : _103721) (s : _103718 -> Prop) : term7 _103718 _103721 x y s.
Proof. exact (@lem4325720 _103718 _103721 x y s). Qed.
Lemma lem4325722 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : (term7 _103718 _103721 x y s) = (term8 _103718 _103721 x s y).
Proof. exact (eq_refl (term7 _103718 _103721 x y s)). Qed.
Lemma lem4325723 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : term8 _103718 _103721 x s y.
Proof. exact (EQ_MP (@lem4325722 _103718 _103721 x s y) (@lem4325721 _103718 _103721 x y s)). Qed.
Lemma lem4325724 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : term9 _103718 _103721 x s y t.
Proof. exact (@lem4325723 _103718 _103721 x s y t). Qed.
Lemma lem4325725 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term9 _103718 _103721 x s y t) = ((term10 _103718 _103721 x y s t) = (term11 _103718 _103721 x s y t)).
Proof. exact (eq_refl (term9 _103718 _103721 x s y t)). Qed.
Lemma lem4325727 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term12 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem4325728 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term12 _5106 _5107 P) = ((term13 _5106 _5107 P) = (term14 _5106 _5107 P)).
Proof. exact (eq_refl (term12 _5106 _5107 P)). Qed.
Lemma lem4325730 {A : Type'} (s : A -> Prop) : term15 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4325731 {A : Type'} (s : A -> Prop) : (term15 A s) = (term16 A s).
Proof. exact (eq_refl (term15 A s)). Qed.
Lemma lem4325732 {A : Type'} (s : A -> Prop) : term16 A s.
Proof. exact (EQ_MP (@lem4325731 A s) (@lem4325730 A s)). Qed.
Lemma lem4325733 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term17 A s t.
Proof. exact (@lem4325732 A s t). Qed.
Lemma lem4325734 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term17 A s t) = ((s = t) = (term18 A s t)).
Proof. exact (eq_refl (term17 A s t)). Qed.
Lemma lem4325755 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term18 A s t).
Proof. exact (EQ_MP (@lem4325734 A s t) (@lem4325733 A s t)). Qed.
Lemma lem4325756 {_103840 _103844 : Type'} (s : type1210 _103840 _103844) (t : type1210 _103840 _103844) : (s = t) = (term19 _103840 _103844 s t).
Proof. exact (@lem4325755 (prod _103840 _103844) s t). Qed.
Lemma lem4325757 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : ((@CROSS _103844 _103840 s t) = (@EMPTY (prod _103840 _103844))) = (term20 _103840 _103844 s t).
Proof. exact (@lem4325756 _103840 _103844 (@CROSS _103844 _103840 s t) (@EMPTY (prod _103840 _103844))). Qed.
Lemma lem4325763 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term13 _5106 _5107 P) = (term14 _5106 _5107 P).
Proof. exact (EQ_MP (@lem4325728 _5106 _5107 P) (@lem4325727 _5106 _5107 P)). Qed.
Lemma lem4325764 {_103840 _103844 : Type'} (P : type1210 _103840 _103844) : (term21 _103840 _103844 P) = (term22 _103840 _103844 P).
Proof. exact (@lem4325763 _103844 _103840 P). Qed.
Lemma lem4325765 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term23 _103840 _103844 s t) = (term24 _103840 _103844 s t).
Proof. exact (@lem4325764 _103840 _103844 (term25 _103840 _103844 s t)). Qed.
Lemma lem4325766 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) (x : prod _103840 _103844) : (term26 _103840 _103844 s t x) = ((term27 _103840 _103844 x s t) = (@IN (prod _103840 _103844) x (@EMPTY (prod _103840 _103844)))).
Proof. exact (eq_refl (term26 _103840 _103844 s t x)). Qed.
Lemma lem4325767 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term28 _103840 _103844 s t) = (term25 _103840 _103844 s t).
Proof. exact (fun_ext (fun x : prod _103840 _103844 => @lem4325766 _103840 _103844 s t x)). Qed.
Lemma lem4325768 {_103840 _103844 : Type'} : (@all (prod _103840 _103844)) = (@all (prod _103840 _103844)).
Proof. exact (eq_refl (@all (prod _103840 _103844))). Qed.
Lemma lem4325769 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term23 _103840 _103844 s t) = (term20 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4325768 _103840 _103844) (@lem4325767 _103840 _103844 s t)). Qed.
Lemma lem4325770 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4325771 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term29 _103840 _103844 s t) = (term30 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4325770) (@lem4325769 _103840 _103844 s t)). Qed.
Lemma lem4325772 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) (p1 : _103840) (p2 : _103844) : (term31 _103840 _103844 s t p1 p2) = ((term10 _103840 _103844 p1 p2 s t) = (term32 _103840 _103844 p1 p2)).
Proof. exact (eq_refl (term31 _103840 _103844 s t p1 p2)). Qed.
Lemma lem4325773 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) (p1 : _103840) : (term33 _103840 _103844 s t p1) = (term34 _103840 _103844 s t p1).
Proof. exact (fun_ext (fun p2 : _103844 => @lem4325772 _103840 _103844 s t p1 p2)). Qed.
Lemma lem4325774 {_103844 : Type'} : (@all _103844) = (@all _103844).
Proof. exact (eq_refl (@all _103844)). Qed.
Lemma lem4325775 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) (p1 : _103840) : (term35 _103840 _103844 s t p1) = (term36 _103840 _103844 s t p1).
Proof. exact (MK_COMB (@lem4325774 _103844) (@lem4325773 _103840 _103844 s t p1)). Qed.
Lemma lem4325776 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term37 _103840 _103844 s t) = (term38 _103840 _103844 s t).
Proof. exact (fun_ext (fun p1 : _103840 => @lem4325775 _103840 _103844 s t p1)). Qed.
Lemma lem4325777 {_103840 : Type'} : (@all _103840) = (@all _103840).
Proof. exact (eq_refl (@all _103840)). Qed.
Lemma lem4325778 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term24 _103840 _103844 s t) = (term39 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4325777 _103840) (@lem4325776 _103840 _103844 s t)). Qed.
Lemma lem4325779 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : ((term23 _103840 _103844 s t) = (term24 _103840 _103844 s t)) = ((term20 _103840 _103844 s t) = (term39 _103840 _103844 s t)).
Proof. exact (MK_COMB (@lem4325771 _103840 _103844 s t) (@lem4325778 _103840 _103844 s t)). Qed.
Lemma lem4325780 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term20 _103840 _103844 s t) = (term39 _103840 _103844 s t).
Proof. exact (EQ_MP (@lem4325779 _103840 _103844 s t) (@lem4325765 _103840 _103844 s t)). Qed.
Lemma lem4325787 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : ((@CROSS _103844 _103840 s t) = (@EMPTY (prod _103840 _103844))) = (term39 _103840 _103844 s t).
Proof. exact (TRANS (@lem4325757 _103840 _103844 s t) (@lem4325780 _103840 _103844 s t)). Qed.
Lemma lem4325799 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term10 _103718 _103721 x y s t) = (term11 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4325725 _103718 _103721 x s y t) (@lem4325724 _103718 _103721 x s y t)). Qed.
Lemma lem4325800 {_103840 _103844 : Type'} (x : _103840) (s : _103840 -> Prop) (y : _103844) (t : _103844 -> Prop) : (term10 _103840 _103844 x y s t) = (term11 _103840 _103844 x s y t).
Proof. exact (@lem4325799 _103840 _103844 x s y t). Qed.
Lemma lem4325801 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) : (term10 _103840 _103844 p1 p2 s t) = (term11 _103840 _103844 p1 s p2 t).
Proof. exact (@lem4325800 _103840 _103844 p1 s p2 t). Qed.
Lemma lem4325804 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4325805 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) : (term40 _103840 _103844 p1 p2 s t) = (term41 _103840 _103844 p1 s p2 t).
Proof. exact (MK_COMB (@lem4325804) (@lem4325801 _103840 _103844 p1 s p2 t)). Qed.
Lemma lem4325807 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4325713 A x (@lem4325712 A x)). Qed.
Lemma lem4325808 {_103840 _103844 : Type'} (x : prod _103840 _103844) : (@IN (prod _103840 _103844) x (@EMPTY (prod _103840 _103844))) = False.
Proof. exact (@lem4325807 (prod _103840 _103844) x). Qed.
Lemma lem4325809 {_103840 _103844 : Type'} (p1 : _103840) (p2 : _103844) : (term32 _103840 _103844 p1 p2) = False.
Proof. exact (@lem4325808 _103840 _103844 (@pair _103840 _103844 p1 p2)). Qed.
Lemma lem4325810 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) : ((term10 _103840 _103844 p1 p2 s t) = (term32 _103840 _103844 p1 p2)) = ((term11 _103840 _103844 p1 s p2 t) = False).
Proof. exact (MK_COMB (@lem4325805 _103840 _103844 p1 s p2 t) (@lem4325809 _103840 _103844 p1 p2)). Qed.
Lemma lem4325812 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4325813 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) : ((term11 _103840 _103844 p1 s p2 t) = False) = (term42 _103840 _103844 p1 s p2 t).
Proof. exact (@lem4325812 (term11 _103840 _103844 p1 s p2 t)). Qed.
Lemma lem4325816 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) : ((term10 _103840 _103844 p1 p2 s t) = (term32 _103840 _103844 p1 p2)) = (term42 _103840 _103844 p1 s p2 t).
Proof. exact (TRANS (@lem4325810 _103840 _103844 p1 s p2 t) (@lem4325813 _103840 _103844 p1 s p2 t)). Qed.
Lemma lem4325817 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term34 _103840 _103844 s t p1) = (term43 _103840 _103844 p1 s t).
Proof. exact (fun_ext (fun p2 : _103844 => @lem4325816 _103840 _103844 p1 s p2 t)). Qed.
Lemma lem4325818 {_103844 : Type'} : (@all _103844) = (@all _103844).
Proof. exact (eq_refl (@all _103844)). Qed.
Lemma lem4325819 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term36 _103840 _103844 s t p1) = (term44 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4325818 _103844) (@lem4325817 _103840 _103844 p1 s t)). Qed.
Lemma lem4325826 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term38 _103840 _103844 s t) = (term45 _103840 _103844 s t).
Proof. exact (fun_ext (fun p1 : _103840 => @lem4325819 _103840 _103844 p1 s t)). Qed.
Lemma lem4325827 {_103840 : Type'} : (@all _103840) = (@all _103840).
Proof. exact (eq_refl (@all _103840)). Qed.
Lemma lem4325828 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term39 _103840 _103844 s t) = (term46 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4325827 _103840) (@lem4325826 _103840 _103844 s t)). Qed.
Lemma lem4325835 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : ((@CROSS _103844 _103840 s t) = (@EMPTY (prod _103840 _103844))) = (term46 _103840 _103844 s t).
Proof. exact (TRANS (@lem4325787 _103840 _103844 s t) (@lem4325828 _103840 _103844 s t)). Qed.
Lemma lem4325836 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4325837 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term47 _103840 _103844 s t) = (term48 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4325836) (@lem4325835 _103840 _103844 s t)). Qed.
Lemma lem4325843 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term18 A s t).
Proof. exact (EQ_MP (@lem4325734 A s t) (@lem4325733 A s t)). Qed.
Lemma lem4325844 {_103840 : Type'} (s : _103840 -> Prop) (t : _103840 -> Prop) : (s = t) = (term18 _103840 s t).
Proof. exact (@lem4325843 _103840 s t). Qed.
Lemma lem4325845 {_103840 : Type'} (s : _103840 -> Prop) : (s = (@EMPTY _103840)) = (term49 _103840 s).
Proof. exact (@lem4325844 _103840 s (@EMPTY _103840)). Qed.
Lemma lem4325857 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4325713 A x (@lem4325712 A x)). Qed.
Lemma lem4325858 {_103840 : Type'} (x : _103840) : (@IN _103840 x (@EMPTY _103840)) = False.
Proof. exact (@lem4325857 _103840 x). Qed.
Lemma lem4325859 {_103840 : Type'} (x : _103840) (s : _103840 -> Prop) : (term50 _103840 x s) = (term50 _103840 x s).
Proof. exact (eq_refl (term50 _103840 x s)). Qed.
Lemma lem4325860 {_103840 : Type'} (x : _103840) (s : _103840 -> Prop) : ((@IN _103840 x s) = (@IN _103840 x (@EMPTY _103840))) = ((@IN _103840 x s) = False).
Proof. exact (MK_COMB (@lem4325859 _103840 x s) (@lem4325858 _103840 x)). Qed.
Lemma lem4325862 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4325863 {_103840 : Type'} (x : _103840) (s : _103840 -> Prop) : ((@IN _103840 x s) = False) = (term51 _103840 x s).
Proof. exact (@lem4325862 (@IN _103840 x s)). Qed.
Lemma lem4325864 {_103840 : Type'} (x : _103840) (s : _103840 -> Prop) : ((@IN _103840 x s) = (@IN _103840 x (@EMPTY _103840))) = (term51 _103840 x s).
Proof. exact (TRANS (@lem4325860 _103840 x s) (@lem4325863 _103840 x s)). Qed.
Lemma lem4325865 {_103840 : Type'} (s : _103840 -> Prop) : (term52 _103840 s) = (term53 _103840 s).
Proof. exact (fun_ext (fun x : _103840 => @lem4325864 _103840 x s)). Qed.
Lemma lem4325866 {_103840 : Type'} : (@all _103840) = (@all _103840).
Proof. exact (eq_refl (@all _103840)). Qed.
Lemma lem4325867 {_103840 : Type'} (s : _103840 -> Prop) : (term49 _103840 s) = (term54 _103840 s).
Proof. exact (MK_COMB (@lem4325866 _103840) (@lem4325865 _103840 s)). Qed.
Lemma lem4325874 {_103840 : Type'} (s : _103840 -> Prop) : (s = (@EMPTY _103840)) = (term54 _103840 s).
Proof. exact (TRANS (@lem4325845 _103840 s) (@lem4325867 _103840 s)). Qed.
Lemma lem4325875 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4325876 {_103840 : Type'} (s : _103840 -> Prop) : (term55 _103840 s) = (term56 _103840 s).
Proof. exact (MK_COMB (@lem4325875) (@lem4325874 _103840 s)). Qed.
Lemma lem4325880 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term18 A s t).
Proof. exact (EQ_MP (@lem4325734 A s t) (@lem4325733 A s t)). Qed.
Lemma lem4325881 {_103844 : Type'} (s : _103844 -> Prop) (t : _103844 -> Prop) : (s = t) = (term18 _103844 s t).
Proof. exact (@lem4325880 _103844 s t). Qed.
Lemma lem4325882 {_103844 : Type'} (t : _103844 -> Prop) : (t = (@EMPTY _103844)) = (term49 _103844 t).
Proof. exact (@lem4325881 _103844 t (@EMPTY _103844)). Qed.
Lemma lem4325894 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4325713 A x (@lem4325712 A x)). Qed.
Lemma lem4325895 {_103844 : Type'} (x : _103844) : (@IN _103844 x (@EMPTY _103844)) = False.
Proof. exact (@lem4325894 _103844 x). Qed.
Lemma lem4325896 {_103844 : Type'} (x : _103844) (t : _103844 -> Prop) : (term50 _103844 x t) = (term50 _103844 x t).
Proof. exact (eq_refl (term50 _103844 x t)). Qed.
Lemma lem4325897 {_103844 : Type'} (x : _103844) (t : _103844 -> Prop) : ((@IN _103844 x t) = (@IN _103844 x (@EMPTY _103844))) = ((@IN _103844 x t) = False).
Proof. exact (MK_COMB (@lem4325896 _103844 x t) (@lem4325895 _103844 x)). Qed.
Lemma lem4325899 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4325900 {_103844 : Type'} (x : _103844) (t : _103844 -> Prop) : ((@IN _103844 x t) = False) = (term51 _103844 x t).
Proof. exact (@lem4325899 (@IN _103844 x t)). Qed.
Lemma lem4325901 {_103844 : Type'} (x : _103844) (t : _103844 -> Prop) : ((@IN _103844 x t) = (@IN _103844 x (@EMPTY _103844))) = (term51 _103844 x t).
Proof. exact (TRANS (@lem4325897 _103844 x t) (@lem4325900 _103844 x t)). Qed.
Lemma lem4325902 {_103844 : Type'} (t : _103844 -> Prop) : (term52 _103844 t) = (term53 _103844 t).
Proof. exact (fun_ext (fun x : _103844 => @lem4325901 _103844 x t)). Qed.
Lemma lem4325903 {_103844 : Type'} : (@all _103844) = (@all _103844).
Proof. exact (eq_refl (@all _103844)). Qed.
Lemma lem4325904 {_103844 : Type'} (t : _103844 -> Prop) : (term49 _103844 t) = (term54 _103844 t).
Proof. exact (MK_COMB (@lem4325903 _103844) (@lem4325902 _103844 t)). Qed.
Lemma lem4325911 {_103844 : Type'} (t : _103844 -> Prop) : (t = (@EMPTY _103844)) = (term54 _103844 t).
Proof. exact (TRANS (@lem4325882 _103844 t) (@lem4325904 _103844 t)). Qed.
Lemma lem4325912 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term57 _103840 _103844 s t) = (term58 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4325876 _103840 s) (@lem4325911 _103844 t)). Qed.
Lemma lem4325915 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (((@CROSS _103844 _103840 s t) = (@EMPTY (prod _103840 _103844))) = (term57 _103840 _103844 s t)) = ((term46 _103840 _103844 s t) = (term58 _103840 _103844 s t)).
Proof. exact (MK_COMB (@lem4325837 _103840 _103844 s t) (@lem4325912 _103840 _103844 s t)). Qed.
Lemma lem4325920 {_103840 _103844 : Type'} (s : _103840 -> Prop) : (term59 _103840 _103844 s) = (term60 _103840 _103844 s).
Proof. exact (fun_ext (fun t : _103844 -> Prop => @lem4325915 _103840 _103844 s t)). Qed.
Lemma lem4325921 {_103844 : Type'} : (@all (_103844 -> Prop)) = (@all (_103844 -> Prop)).
Proof. exact (eq_refl (@all (_103844 -> Prop))). Qed.
Lemma lem4325922 {_103840 _103844 : Type'} (s : _103840 -> Prop) : (term61 _103840 _103844 s) = (term62 _103840 _103844 s).
Proof. exact (MK_COMB (@lem4325921 _103844) (@lem4325920 _103840 _103844 s)). Qed.
Lemma lem4325929 {_103840 _103844 : Type'} : (term63 _103840 _103844) = (term64 _103840 _103844).
Proof. exact (fun_ext (fun s : _103840 -> Prop => @lem4325922 _103840 _103844 s)). Qed.
Lemma lem4325930 {_103840 : Type'} : (@all (_103840 -> Prop)) = (@all (_103840 -> Prop)).
Proof. exact (eq_refl (@all (_103840 -> Prop))). Qed.
Lemma lem4325931 {_103840 _103844 : Type'} : (term65 _103840 _103844) = (term66 _103840 _103844).
Proof. exact (MK_COMB (@lem4325930 _103840) (@lem4325929 _103840 _103844)). Qed.
Lemma lem4325938 {_103840 _103844 : Type'} : (term66 _103840 _103844) = (term65 _103840 _103844).
Proof. exact (SYM (@lem4325931 _103840 _103844)). Qed.
Lemma lem4325940 (p : Prop) : p = (term67 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4325941 {_103840 _103844 : Type'} : (term66 _103840 _103844) = (term68 _103840 _103844).
Proof. exact (@lem4325940 (term66 _103840 _103844)). Qed.
Lemma lem4325942 {_103840 _103844 : Type'} : (term68 _103840 _103844) = (term66 _103840 _103844).
Proof. exact (SYM (@lem4325941 _103840 _103844)). Qed.
Lemma lem4325943 {_103840 _103844 : Type'} (h1 : term69 _103840 _103844) : term69 _103840 _103844.
Proof. exact (h1). Qed.
Lemma lem4325946 {_103840 _103844 : Type'} (h1 : term68 _103840 _103844) : term68 _103840 _103844.
Proof. exact (h1). Qed.
Lemma lem4325947 {_103840 _103844 : Type'} : term70 _103840 _103844.
Proof. exact (fun h0 : term68 _103840 _103844 => @lem4325946 _103840 _103844 h0). Qed.
Lemma lem4325948 {_103840 _103844 : Type'} (h1 : term70 _103840 _103844) : term70 _103840 _103844.
Proof. exact (h1). Qed.
Lemma lem4325949 {_103840 _103844 : Type'} (h1 : term68 _103840 _103844) : term68 _103840 _103844.
Proof. exact (h1). Qed.
Lemma lem4325950 {_103840 _103844 : Type'} (h1 : term68 _103840 _103844) (h2 : term70 _103840 _103844) : term68 _103840 _103844.
Proof. exact (@lem4325948 _103840 _103844 h2 (@lem4325949 _103840 _103844 h1)). Qed.
Lemma lem4325951 {_103840 _103844 : Type'} (h1 : term68 _103840 _103844) : term71 _103840 _103844.
Proof. exact (fun h0 : term70 _103840 _103844 => @lem4325950 _103840 _103844 h1 h0). Qed.
Lemma lem4325952 {_103840 _103844 : Type'} (h1 : term70 _103840 _103844) : term70 _103840 _103844.
Proof. exact (h1). Qed.
Lemma lem4325953 {_103840 _103844 : Type'} (h1 : term68 _103840 _103844) (h2 : term70 _103840 _103844) : term68 _103840 _103844.
Proof. exact (@lem4325951 _103840 _103844 h1 (@lem4325952 _103840 _103844 h2)). Qed.
Lemma lem4325954 {_103840 _103844 : Type'} (h1 : term70 _103840 _103844) : term70 _103840 _103844.
Proof. exact (fun h0 : term68 _103840 _103844 => @lem4325953 _103840 _103844 h0 h1). Qed.
Lemma lem4325955 {_103840 _103844 : Type'} : term72 _103840 _103844.
Proof. exact (fun h0 : term70 _103840 _103844 => @lem4325954 _103840 _103844 h0). Qed.
Lemma lem4325958 {_103840 _103844 : Type'} : term70 _103840 _103844.
Proof. exact (@lem4325955 _103840 _103844 (@lem4325947 _103840 _103844)). Qed.
Lemma lem4325959 {_103840 _103844 : Type'} : term70 _103840 _103844.
Proof. exact (@lem4325958 _103840 _103844). Qed.
Lemma lem4325961 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4325962 {_103840 _103844 : Type'} : (term68 _103840 _103844) = (term73 _103840 _103844).
Proof. exact (@lem4325961 (term69 _103840 _103844)). Qed.
Lemma lem4325964 (t : Prop) : (term74 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4325965 {_103840 _103844 : Type'} : (term73 _103840 _103844) = (term66 _103840 _103844).
Proof. exact (@lem4325964 (term66 _103840 _103844)). Qed.
Lemma lem4325998 {_103840 _103844 : Type'} : (term68 _103840 _103844) = (term66 _103840 _103844).
Proof. exact (TRANS (@lem4325962 _103840 _103844) (@lem4325965 _103840 _103844)). Qed.
Lemma lem4326001 {_103844 : Type'} (x : _103844) (t : _103844 -> Prop) : (term51 _103844 x t) = (term51 _103844 x t).
Proof. exact (eq_refl (term51 _103844 x t)). Qed.
Lemma lem4326002 {_103844 : Type'} (t : _103844 -> Prop) : (term53 _103844 t) = (term53 _103844 t).
Proof. exact (fun_ext (fun x : _103844 => @lem4326001 _103844 x t)). Qed.
Lemma lem4326003 {_103844 : Type'} : (@all _103844) = (@all _103844).
Proof. exact (eq_refl (@all _103844)). Qed.
Lemma lem4326004 {_103844 : Type'} (t : _103844 -> Prop) : (term54 _103844 t) = (term54 _103844 t).
Proof. exact (MK_COMB (@lem4326003 _103844) (@lem4326002 _103844 t)). Qed.
Lemma lem4326007 {_103840 : Type'} (x : _103840) (s : _103840 -> Prop) : (term51 _103840 x s) = (term51 _103840 x s).
Proof. exact (eq_refl (term51 _103840 x s)). Qed.
Lemma lem4326008 {_103840 : Type'} (s : _103840 -> Prop) : (term53 _103840 s) = (term53 _103840 s).
Proof. exact (fun_ext (fun x : _103840 => @lem4326007 _103840 x s)). Qed.
Lemma lem4326009 {_103840 : Type'} : (@all _103840) = (@all _103840).
Proof. exact (eq_refl (@all _103840)). Qed.
Lemma lem4326010 {_103840 : Type'} (s : _103840 -> Prop) : (term54 _103840 s) = (term54 _103840 s).
Proof. exact (MK_COMB (@lem4326009 _103840) (@lem4326008 _103840 s)). Qed.
Lemma lem4326011 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4326012 {_103840 : Type'} (s : _103840 -> Prop) : (term56 _103840 s) = (term56 _103840 s).
Proof. exact (MK_COMB (@lem4326011) (@lem4326010 _103840 s)). Qed.
Lemma lem4326013 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term58 _103840 _103844 s t) = (term58 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326012 _103840 s) (@lem4326004 _103844 t)). Qed.
Lemma lem4326020 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) : (term42 _103840 _103844 p1 s p2 t) = (term42 _103840 _103844 p1 s p2 t).
Proof. exact (eq_refl (term42 _103840 _103844 p1 s p2 t)). Qed.
Lemma lem4326021 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term43 _103840 _103844 p1 s t) = (term43 _103840 _103844 p1 s t).
Proof. exact (fun_ext (fun p2 : _103844 => @lem4326020 _103840 _103844 p1 s p2 t)). Qed.
Lemma lem4326022 {_103844 : Type'} : (@all _103844) = (@all _103844).
Proof. exact (eq_refl (@all _103844)). Qed.
Lemma lem4326023 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term44 _103840 _103844 p1 s t) = (term44 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4326022 _103844) (@lem4326021 _103840 _103844 p1 s t)). Qed.
Lemma lem4326024 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term45 _103840 _103844 s t) = (term45 _103840 _103844 s t).
Proof. exact (fun_ext (fun p1 : _103840 => @lem4326023 _103840 _103844 p1 s t)). Qed.
Lemma lem4326025 {_103840 : Type'} : (@all _103840) = (@all _103840).
Proof. exact (eq_refl (@all _103840)). Qed.
Lemma lem4326026 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term46 _103840 _103844 s t) = (term46 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326025 _103840) (@lem4326024 _103840 _103844 s t)). Qed.
Lemma lem4326027 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4326028 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term48 _103840 _103844 s t) = (term48 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326027) (@lem4326026 _103840 _103844 s t)). Qed.
Lemma lem4326029 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : ((term46 _103840 _103844 s t) = (term58 _103840 _103844 s t)) = ((term46 _103840 _103844 s t) = (term58 _103840 _103844 s t)).
Proof. exact (MK_COMB (@lem4326028 _103840 _103844 s t) (@lem4326013 _103840 _103844 s t)). Qed.
Lemma lem4326030 {_103840 _103844 : Type'} (s : _103840 -> Prop) : (term60 _103840 _103844 s) = (term60 _103840 _103844 s).
Proof. exact (fun_ext (fun t : _103844 -> Prop => @lem4326029 _103840 _103844 s t)). Qed.
Lemma lem4326031 {_103844 : Type'} : (@all (_103844 -> Prop)) = (@all (_103844 -> Prop)).
Proof. exact (eq_refl (@all (_103844 -> Prop))). Qed.
Lemma lem4326032 {_103840 _103844 : Type'} (s : _103840 -> Prop) : (term62 _103840 _103844 s) = (term62 _103840 _103844 s).
Proof. exact (MK_COMB (@lem4326031 _103844) (@lem4326030 _103840 _103844 s)). Qed.
Lemma lem4326033 {_103840 _103844 : Type'} : (term64 _103840 _103844) = (term64 _103840 _103844).
Proof. exact (fun_ext (fun s : _103840 -> Prop => @lem4326032 _103840 _103844 s)). Qed.
Lemma lem4326034 {_103840 : Type'} : (@all (_103840 -> Prop)) = (@all (_103840 -> Prop)).
Proof. exact (eq_refl (@all (_103840 -> Prop))). Qed.
Lemma lem4326035 {_103840 _103844 : Type'} : (term66 _103840 _103844) = (term66 _103840 _103844).
Proof. exact (MK_COMB (@lem4326034 _103840) (@lem4326033 _103840 _103844)). Qed.
Lemma lem4326078 {_103840 _103844 : Type'} : (term68 _103840 _103844) = (term66 _103840 _103844).
Proof. exact (TRANS (@lem4325998 _103840 _103844) (@lem4326035 _103840 _103844)). Qed.
Lemma lem4326079 {_103840 _103844 : Type'} : (term66 _103840 _103844) = (term68 _103840 _103844).
Proof. exact (SYM (@lem4326078 _103840 _103844)). Qed.
Lemma lem4326081 (p : Prop) : p = (term67 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4326082 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : ((term46 _103840 _103844 s t) = (term58 _103840 _103844 s t)) = (term75 _103840 _103844 s t).
Proof. exact (@lem4326081 ((term46 _103840 _103844 s t) = (term58 _103840 _103844 s t))). Qed.
Lemma lem4326083 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term75 _103840 _103844 s t) = ((term46 _103840 _103844 s t) = (term58 _103840 _103844 s t)).
Proof. exact (SYM (@lem4326082 _103840 _103844 s t)). Qed.
Lemma lem4326084 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) (h1 : term76 _103840 _103844 s t) : term76 _103840 _103844 s t.
Proof. exact (h1). Qed.
Lemma lem4326093 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) : (term42 _103840 _103844 p1 s p2 t) = (term77 _103840 _103844 p1 s p2 t).
Proof. exact (@lem17045 (@IN _103840 p1 s) (@IN _103844 p2 t)). Qed.
Lemma lem4326098 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) : (term78 _103840 _103844 p1 s p2 t) = (term11 _103840 _103844 p1 s p2 t).
Proof. exact (@lem16933 (term11 _103840 _103844 p1 s p2 t)). Qed.
Lemma lem4326099 {_103844 : Type'} (P : _103844 -> Prop) : (term79 _103844 P) = (term80 _103844 P).
Proof. exact (@lem18392 _103844 P). Qed.
Lemma lem4326100 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term81 _103840 _103844 p1 s t) = (term82 _103840 _103844 p1 s t).
Proof. exact (@lem4326099 _103844 (term43 _103840 _103844 p1 s t)). Qed.
Lemma lem4326101 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) : (term83 _103840 _103844 p1 s t p2) = (term42 _103840 _103844 p1 s p2 t).
Proof. exact (eq_refl (term83 _103840 _103844 p1 s t p2)). Qed.
Lemma lem4326102 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4326103 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) : (term84 _103840 _103844 p1 s t p2) = (term78 _103840 _103844 p1 s p2 t).
Proof. exact (MK_COMB (@lem4326102) (@lem4326101 _103840 _103844 p1 s p2 t)). Qed.
Lemma lem4326104 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) : (term84 _103840 _103844 p1 s t p2) = (term11 _103840 _103844 p1 s p2 t).
Proof. exact (TRANS (@lem4326103 _103840 _103844 p1 s p2 t) (@lem4326098 _103840 _103844 p1 s p2 t)). Qed.
Lemma lem4326105 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term85 _103840 _103844 p1 s t) = (term86 _103840 _103844 p1 s t).
Proof. exact (fun_ext (fun p2 : _103844 => @lem4326104 _103840 _103844 p1 s p2 t)). Qed.
Lemma lem4326106 {_103844 : Type'} : (@ex _103844) = (@ex _103844).
Proof. exact (eq_refl (@ex _103844)). Qed.
Lemma lem4326107 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term82 _103840 _103844 p1 s t) = (term87 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4326106 _103844) (@lem4326105 _103840 _103844 p1 s t)). Qed.
Lemma lem4326108 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term81 _103840 _103844 p1 s t) = (term87 _103840 _103844 p1 s t).
Proof. exact (TRANS (@lem4326100 _103840 _103844 p1 s t) (@lem4326107 _103840 _103844 p1 s t)). Qed.
Lemma lem4326109 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term43 _103840 _103844 p1 s t) = (term88 _103840 _103844 p1 s t).
Proof. exact (fun_ext (fun p2 : _103844 => @lem4326093 _103840 _103844 p1 s p2 t)). Qed.
Lemma lem4326110 {_103844 : Type'} : (@all _103844) = (@all _103844).
Proof. exact (eq_refl (@all _103844)). Qed.
Lemma lem4326111 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term44 _103840 _103844 p1 s t) = (term89 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4326110 _103844) (@lem4326109 _103840 _103844 p1 s t)). Qed.
Lemma lem4326112 {_103840 : Type'} (P : _103840 -> Prop) : (term79 _103840 P) = (term80 _103840 P).
Proof. exact (@lem18392 _103840 P). Qed.
Lemma lem4326113 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term90 _103840 _103844 s t) = (term91 _103840 _103844 s t).
Proof. exact (@lem4326112 _103840 (term45 _103840 _103844 s t)). Qed.
Lemma lem4326114 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term92 _103840 _103844 s t p1) = (term44 _103840 _103844 p1 s t).
Proof. exact (eq_refl (term92 _103840 _103844 s t p1)). Qed.
Lemma lem4326115 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4326116 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term93 _103840 _103844 s t p1) = (term81 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4326115) (@lem4326114 _103840 _103844 p1 s t)). Qed.
Lemma lem4326117 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term93 _103840 _103844 s t p1) = (term87 _103840 _103844 p1 s t).
Proof. exact (TRANS (@lem4326116 _103840 _103844 p1 s t) (@lem4326108 _103840 _103844 p1 s t)). Qed.
Lemma lem4326118 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term94 _103840 _103844 s t) = (term95 _103840 _103844 s t).
Proof. exact (fun_ext (fun p1 : _103840 => @lem4326117 _103840 _103844 p1 s t)). Qed.
Lemma lem4326119 {_103840 : Type'} : (@ex _103840) = (@ex _103840).
Proof. exact (eq_refl (@ex _103840)). Qed.
Lemma lem4326120 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term91 _103840 _103844 s t) = (term96 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326119 _103840) (@lem4326118 _103840 _103844 s t)). Qed.
Lemma lem4326121 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term90 _103840 _103844 s t) = (term96 _103840 _103844 s t).
Proof. exact (TRANS (@lem4326113 _103840 _103844 s t) (@lem4326120 _103840 _103844 s t)). Qed.
Lemma lem4326122 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term45 _103840 _103844 s t) = (term97 _103840 _103844 s t).
Proof. exact (fun_ext (fun p1 : _103840 => @lem4326111 _103840 _103844 p1 s t)). Qed.
Lemma lem4326123 {_103840 : Type'} : (@all _103840) = (@all _103840).
Proof. exact (eq_refl (@all _103840)). Qed.
Lemma lem4326124 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term46 _103840 _103844 s t) = (term98 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326123 _103840) (@lem4326122 _103840 _103844 s t)). Qed.
Lemma lem4326125 {_103840 : Type'} (x : _103840) (s : _103840 -> Prop) : (term51 _103840 x s) = (term51 _103840 x s).
Proof. exact (eq_refl (term51 _103840 x s)). Qed.
Lemma lem4326128 {_103840 : Type'} (x : _103840) (s : _103840 -> Prop) : (term99 _103840 x s) = (@IN _103840 x s).
Proof. exact (@lem16933 (@IN _103840 x s)). Qed.
Lemma lem4326129 {_103840 : Type'} (P : _103840 -> Prop) : (term79 _103840 P) = (term80 _103840 P).
Proof. exact (@lem18392 _103840 P). Qed.
Lemma lem4326130 {_103840 : Type'} (s : _103840 -> Prop) : (term100 _103840 s) = (term101 _103840 s).
Proof. exact (@lem4326129 _103840 (term53 _103840 s)). Qed.
Lemma lem4326131 {_103840 : Type'} (x : _103840) (s : _103840 -> Prop) : (term102 _103840 s x) = (term51 _103840 x s).
Proof. exact (eq_refl (term102 _103840 s x)). Qed.
Lemma lem4326132 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4326133 {_103840 : Type'} (x : _103840) (s : _103840 -> Prop) : (term103 _103840 s x) = (term99 _103840 x s).
Proof. exact (MK_COMB (@lem4326132) (@lem4326131 _103840 x s)). Qed.
Lemma lem4326134 {_103840 : Type'} (x : _103840) (s : _103840 -> Prop) : (term103 _103840 s x) = (@IN _103840 x s).
Proof. exact (TRANS (@lem4326133 _103840 x s) (@lem4326128 _103840 x s)). Qed.
Lemma lem4326135 {_103840 : Type'} (s : _103840 -> Prop) : (term104 _103840 s) = (term105 _103840 s).
Proof. exact (fun_ext (fun x : _103840 => @lem4326134 _103840 x s)). Qed.
Lemma lem4326136 {_103840 : Type'} : (@ex _103840) = (@ex _103840).
Proof. exact (eq_refl (@ex _103840)). Qed.
Lemma lem4326137 {_103840 : Type'} (s : _103840 -> Prop) : (term101 _103840 s) = (term106 _103840 s).
Proof. exact (MK_COMB (@lem4326136 _103840) (@lem4326135 _103840 s)). Qed.
Lemma lem4326138 {_103840 : Type'} (s : _103840 -> Prop) : (term100 _103840 s) = (term106 _103840 s).
Proof. exact (TRANS (@lem4326130 _103840 s) (@lem4326137 _103840 s)). Qed.
Lemma lem4326139 {_103840 : Type'} (s : _103840 -> Prop) : (term53 _103840 s) = (term53 _103840 s).
Proof. exact (fun_ext (fun x : _103840 => @lem4326125 _103840 x s)). Qed.
Lemma lem4326140 {_103840 : Type'} : (@all _103840) = (@all _103840).
Proof. exact (eq_refl (@all _103840)). Qed.
Lemma lem4326141 {_103840 : Type'} (s : _103840 -> Prop) : (term54 _103840 s) = (term54 _103840 s).
Proof. exact (MK_COMB (@lem4326140 _103840) (@lem4326139 _103840 s)). Qed.
Lemma lem4326142 {_103844 : Type'} (x : _103844) (t : _103844 -> Prop) : (term51 _103844 x t) = (term51 _103844 x t).
Proof. exact (eq_refl (term51 _103844 x t)). Qed.
Lemma lem4326145 {_103844 : Type'} (x : _103844) (t : _103844 -> Prop) : (term99 _103844 x t) = (@IN _103844 x t).
Proof. exact (@lem16933 (@IN _103844 x t)). Qed.
Lemma lem4326146 {_103844 : Type'} (P : _103844 -> Prop) : (term79 _103844 P) = (term80 _103844 P).
Proof. exact (@lem18392 _103844 P). Qed.
Lemma lem4326147 {_103844 : Type'} (t : _103844 -> Prop) : (term100 _103844 t) = (term101 _103844 t).
Proof. exact (@lem4326146 _103844 (term53 _103844 t)). Qed.
Lemma lem4326148 {_103844 : Type'} (x : _103844) (t : _103844 -> Prop) : (term102 _103844 t x) = (term51 _103844 x t).
Proof. exact (eq_refl (term102 _103844 t x)). Qed.
Lemma lem4326149 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4326150 {_103844 : Type'} (x : _103844) (t : _103844 -> Prop) : (term103 _103844 t x) = (term99 _103844 x t).
Proof. exact (MK_COMB (@lem4326149) (@lem4326148 _103844 x t)). Qed.
Lemma lem4326151 {_103844 : Type'} (x : _103844) (t : _103844 -> Prop) : (term103 _103844 t x) = (@IN _103844 x t).
Proof. exact (TRANS (@lem4326150 _103844 x t) (@lem4326145 _103844 x t)). Qed.
Lemma lem4326152 {_103844 : Type'} (t : _103844 -> Prop) : (term104 _103844 t) = (term105 _103844 t).
Proof. exact (fun_ext (fun x : _103844 => @lem4326151 _103844 x t)). Qed.
Lemma lem4326153 {_103844 : Type'} : (@ex _103844) = (@ex _103844).
Proof. exact (eq_refl (@ex _103844)). Qed.
Lemma lem4326154 {_103844 : Type'} (t : _103844 -> Prop) : (term101 _103844 t) = (term106 _103844 t).
Proof. exact (MK_COMB (@lem4326153 _103844) (@lem4326152 _103844 t)). Qed.
Lemma lem4326155 {_103844 : Type'} (t : _103844 -> Prop) : (term100 _103844 t) = (term106 _103844 t).
Proof. exact (TRANS (@lem4326147 _103844 t) (@lem4326154 _103844 t)). Qed.
Lemma lem4326156 {_103844 : Type'} (t : _103844 -> Prop) : (term53 _103844 t) = (term53 _103844 t).
Proof. exact (fun_ext (fun x : _103844 => @lem4326142 _103844 x t)). Qed.
Lemma lem4326157 {_103844 : Type'} : (@all _103844) = (@all _103844).
Proof. exact (eq_refl (@all _103844)). Qed.
Lemma lem4326158 {_103844 : Type'} (t : _103844 -> Prop) : (term54 _103844 t) = (term54 _103844 t).
Proof. exact (MK_COMB (@lem4326157 _103844) (@lem4326156 _103844 t)). Qed.
Lemma lem4326159 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4326160 {_103840 : Type'} (s : _103840 -> Prop) : (term107 _103840 s) = (term108 _103840 s).
Proof. exact (MK_COMB (@lem4326159) (@lem4326138 _103840 s)). Qed.
Lemma lem4326161 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term109 _103840 _103844 s t) = (term110 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326160 _103840 s) (@lem4326155 _103844 t)). Qed.
Lemma lem4326162 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term111 _103840 _103844 s t) = (term109 _103840 _103844 s t).
Proof. exact (@lem17160 (term54 _103840 s) (term54 _103844 t)). Qed.
Lemma lem4326163 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term111 _103840 _103844 s t) = (term110 _103840 _103844 s t).
Proof. exact (TRANS (@lem4326162 _103840 _103844 s t) (@lem4326161 _103840 _103844 s t)). Qed.
Lemma lem4326164 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4326165 {_103840 : Type'} (s : _103840 -> Prop) : (term56 _103840 s) = (term56 _103840 s).
Proof. exact (MK_COMB (@lem4326164) (@lem4326141 _103840 s)). Qed.
Lemma lem4326166 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term58 _103840 _103844 s t) = (term58 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326165 _103840 s) (@lem4326158 _103844 t)). Qed.
Lemma lem4326167 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4326168 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term112 _103840 _103844 s t) = (term113 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326167) (@lem4326121 _103840 _103844 s t)). Qed.
Lemma lem4326169 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term114 _103840 _103844 s t) = (term115 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326168 _103840 _103844 s t) (@lem4326166 _103840 _103844 s t)). Qed.
Lemma lem4326170 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4326171 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term116 _103840 _103844 s t) = (term117 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326170) (@lem4326124 _103840 _103844 s t)). Qed.
Lemma lem4326172 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term118 _103840 _103844 s t) = (term119 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326171 _103840 _103844 s t) (@lem4326163 _103840 _103844 s t)). Qed.
Lemma lem4326173 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4326174 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term120 _103840 _103844 s t) = (term121 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326173) (@lem4326172 _103840 _103844 s t)). Qed.
Lemma lem4326175 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term122 _103840 _103844 s t) = (term123 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326174 _103840 _103844 s t) (@lem4326169 _103840 _103844 s t)). Qed.
Lemma lem4326176 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term76 _103840 _103844 s t) = (term122 _103840 _103844 s t).
Proof. exact (@lem17646 (term46 _103840 _103844 s t) (term58 _103840 _103844 s t)). Qed.
Lemma lem4326177 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term76 _103840 _103844 s t) = (term123 _103840 _103844 s t).
Proof. exact (TRANS (@lem4326176 _103840 _103844 s t) (@lem4326175 _103840 _103844 s t)). Qed.
Lemma lem4326183 {A : Type'} (P : Prop) (Q : A -> Prop) : (term124 A P Q) = (term125 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem4326184 {_103844 : Type'} (P : Prop) (Q : _103844 -> Prop) : (term124 _103844 P Q) = (term125 _103844 P Q).
Proof. exact (@lem4326183 _103844 P Q). Qed.
Lemma lem4326185 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term126 _103840 _103844 p1 s t) = (term127 _103840 _103844 p1 s t).
Proof. exact (@lem4326184 _103844 (term51 _103840 p1 s) (term53 _103844 t)). Qed.
Lemma lem4326186 {_103844 : Type'} (p2 : _103844) (t : _103844 -> Prop) : (term102 _103844 t p2) = (term51 _103844 p2 t).
Proof. exact (eq_refl (term102 _103844 t p2)). Qed.
Lemma lem4326187 {_103840 : Type'} (p1 : _103840) (s : _103840 -> Prop) : (term128 _103840 p1 s) = (term128 _103840 p1 s).
Proof. exact (eq_refl (term128 _103840 p1 s)). Qed.
Lemma lem4326188 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) : (term129 _103840 _103844 p1 s t p2) = (term77 _103840 _103844 p1 s p2 t).
Proof. exact (MK_COMB (@lem4326187 _103840 p1 s) (@lem4326186 _103844 p2 t)). Qed.
Lemma lem4326189 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term130 _103840 _103844 p1 s t) = (term88 _103840 _103844 p1 s t).
Proof. exact (fun_ext (fun p2 : _103844 => @lem4326188 _103840 _103844 p1 s p2 t)). Qed.
Lemma lem4326190 {_103844 : Type'} : (@all _103844) = (@all _103844).
Proof. exact (eq_refl (@all _103844)). Qed.
Lemma lem4326191 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term126 _103840 _103844 p1 s t) = (term89 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4326190 _103844) (@lem4326189 _103840 _103844 p1 s t)). Qed.
Lemma lem4326192 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4326193 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term131 _103840 _103844 p1 s t) = (term132 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4326192) (@lem4326191 _103840 _103844 p1 s t)). Qed.
Lemma lem4326194 {_103844 : Type'} (p2 : _103844) (t : _103844 -> Prop) : (term102 _103844 t p2) = (term51 _103844 p2 t).
Proof. exact (eq_refl (term102 _103844 t p2)). Qed.
Lemma lem4326195 {_103844 : Type'} (t : _103844 -> Prop) : (term133 _103844 t) = (term53 _103844 t).
Proof. exact (fun_ext (fun p2 : _103844 => @lem4326194 _103844 p2 t)). Qed.
Lemma lem4326196 {_103844 : Type'} : (@all _103844) = (@all _103844).
Proof. exact (eq_refl (@all _103844)). Qed.
Lemma lem4326197 {_103844 : Type'} (t : _103844 -> Prop) : (term134 _103844 t) = (term54 _103844 t).
Proof. exact (MK_COMB (@lem4326196 _103844) (@lem4326195 _103844 t)). Qed.
Lemma lem4326198 {_103840 : Type'} (p1 : _103840) (s : _103840 -> Prop) : (term128 _103840 p1 s) = (term128 _103840 p1 s).
Proof. exact (eq_refl (term128 _103840 p1 s)). Qed.
Lemma lem4326199 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term127 _103840 _103844 p1 s t) = (term135 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4326198 _103840 p1 s) (@lem4326197 _103844 t)). Qed.
Lemma lem4326200 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : ((term126 _103840 _103844 p1 s t) = (term127 _103840 _103844 p1 s t)) = ((term89 _103840 _103844 p1 s t) = (term135 _103840 _103844 p1 s t)).
Proof. exact (MK_COMB (@lem4326193 _103840 _103844 p1 s t) (@lem4326199 _103840 _103844 p1 s t)). Qed.
Lemma lem4326201 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term89 _103840 _103844 p1 s t) = (term135 _103840 _103844 p1 s t).
Proof. exact (EQ_MP (@lem4326200 _103840 _103844 p1 s t) (@lem4326185 _103840 _103844 p1 s t)). Qed.
Lemma lem4326206 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term97 _103840 _103844 s t) = (term136 _103840 _103844 s t).
Proof. exact (fun_ext (fun p1 : _103840 => @lem4326201 _103840 _103844 p1 s t)). Qed.
Lemma lem4326207 {_103840 : Type'} : (@all _103840) = (@all _103840).
Proof. exact (eq_refl (@all _103840)). Qed.
Lemma lem4326208 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term98 _103840 _103844 s t) = (term137 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326207 _103840) (@lem4326206 _103840 _103844 s t)). Qed.
Lemma lem4326230 {A : Type'} (P : A -> Prop) (Q : Prop) : (term138 A P Q) = (term139 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem4326231 {_103840 : Type'} (P : _103840 -> Prop) (Q : Prop) : (term138 _103840 P Q) = (term139 _103840 P Q).
Proof. exact (@lem4326230 _103840 P Q). Qed.
Lemma lem4326232 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term140 _103840 _103844 s t) = (term141 _103840 _103844 s t).
Proof. exact (@lem4326231 _103840 (term53 _103840 s) (term54 _103844 t)). Qed.
Lemma lem4326233 {_103840 : Type'} (p1 : _103840) (s : _103840 -> Prop) : (term102 _103840 s p1) = (term51 _103840 p1 s).
Proof. exact (eq_refl (term102 _103840 s p1)). Qed.
Lemma lem4326234 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4326235 {_103840 : Type'} (p1 : _103840) (s : _103840 -> Prop) : (term142 _103840 s p1) = (term128 _103840 p1 s).
Proof. exact (MK_COMB (@lem4326234) (@lem4326233 _103840 p1 s)). Qed.
Lemma lem4326236 {_103844 : Type'} (t : _103844 -> Prop) : (term54 _103844 t) = (term54 _103844 t).
Proof. exact (eq_refl (term54 _103844 t)). Qed.
Lemma lem4326237 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term143 _103840 _103844 s p1 t) = (term135 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4326235 _103840 p1 s) (@lem4326236 _103844 t)). Qed.
Lemma lem4326238 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term144 _103840 _103844 s t) = (term136 _103840 _103844 s t).
Proof. exact (fun_ext (fun p1 : _103840 => @lem4326237 _103840 _103844 p1 s t)). Qed.
Lemma lem4326239 {_103840 : Type'} : (@all _103840) = (@all _103840).
Proof. exact (eq_refl (@all _103840)). Qed.
Lemma lem4326240 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term140 _103840 _103844 s t) = (term137 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326239 _103840) (@lem4326238 _103840 _103844 s t)). Qed.
Lemma lem4326241 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4326242 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term145 _103840 _103844 s t) = (term146 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326241) (@lem4326240 _103840 _103844 s t)). Qed.
Lemma lem4326243 {_103840 : Type'} (p1 : _103840) (s : _103840 -> Prop) : (term102 _103840 s p1) = (term51 _103840 p1 s).
Proof. exact (eq_refl (term102 _103840 s p1)). Qed.
Lemma lem4326244 {_103840 : Type'} (s : _103840 -> Prop) : (term133 _103840 s) = (term53 _103840 s).
Proof. exact (fun_ext (fun p1 : _103840 => @lem4326243 _103840 p1 s)). Qed.
Lemma lem4326245 {_103840 : Type'} : (@all _103840) = (@all _103840).
Proof. exact (eq_refl (@all _103840)). Qed.
Lemma lem4326246 {_103840 : Type'} (s : _103840 -> Prop) : (term134 _103840 s) = (term54 _103840 s).
Proof. exact (MK_COMB (@lem4326245 _103840) (@lem4326244 _103840 s)). Qed.
Lemma lem4326247 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4326248 {_103840 : Type'} (s : _103840 -> Prop) : (term147 _103840 s) = (term56 _103840 s).
Proof. exact (MK_COMB (@lem4326247) (@lem4326246 _103840 s)). Qed.
Lemma lem4326249 {_103844 : Type'} (t : _103844 -> Prop) : (term54 _103844 t) = (term54 _103844 t).
Proof. exact (eq_refl (term54 _103844 t)). Qed.
Lemma lem4326250 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term141 _103840 _103844 s t) = (term58 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326248 _103840 s) (@lem4326249 _103844 t)). Qed.
Lemma lem4326251 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : ((term140 _103840 _103844 s t) = (term141 _103840 _103844 s t)) = ((term137 _103840 _103844 s t) = (term58 _103840 _103844 s t)).
Proof. exact (MK_COMB (@lem4326242 _103840 _103844 s t) (@lem4326250 _103840 _103844 s t)). Qed.
Lemma lem4326252 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term137 _103840 _103844 s t) = (term58 _103840 _103844 s t).
Proof. exact (EQ_MP (@lem4326251 _103840 _103844 s t) (@lem4326232 _103840 _103844 s t)). Qed.
Lemma lem4326261 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term98 _103840 _103844 s t) = (term58 _103840 _103844 s t).
Proof. exact (TRANS (@lem4326208 _103840 _103844 s t) (@lem4326252 _103840 _103844 s t)). Qed.
Lemma lem4326262 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4326263 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term117 _103840 _103844 s t) = (term148 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326262) (@lem4326261 _103840 _103844 s t)). Qed.
Lemma lem4326272 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term110 _103840 _103844 s t) = (term110 _103840 _103844 s t).
Proof. exact (eq_refl (term110 _103840 _103844 s t)). Qed.
Lemma lem4326273 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term119 _103840 _103844 s t) = (term149 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326263 _103840 _103844 s t) (@lem4326272 _103840 _103844 s t)). Qed.
Lemma lem4326274 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4326275 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term121 _103840 _103844 s t) = (term150 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326274) (@lem4326273 _103840 _103844 s t)). Qed.
Lemma lem4326281 {A : Type'} (P : Prop) (Q : A -> Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem4326282 {_103844 : Type'} (P : Prop) (Q : _103844 -> Prop) : (term151 _103844 P Q) = (term152 _103844 P Q).
Proof. exact (@lem4326281 _103844 P Q). Qed.
Lemma lem4326283 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term153 _103840 _103844 p1 s t) = (term154 _103840 _103844 p1 s t).
Proof. exact (@lem4326282 _103844 (@IN _103840 p1 s) (term105 _103844 t)). Qed.
Lemma lem4326284 {_103844 : Type'} (p2 : _103844) (t : _103844 -> Prop) : (term155 _103844 t p2) = (@IN _103844 p2 t).
Proof. exact (eq_refl (term155 _103844 t p2)). Qed.
Lemma lem4326285 {_103840 : Type'} (p1 : _103840) (s : _103840 -> Prop) : (term156 _103840 p1 s) = (term156 _103840 p1 s).
Proof. exact (eq_refl (term156 _103840 p1 s)). Qed.
Lemma lem4326286 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) : (term157 _103840 _103844 p1 s t p2) = (term11 _103840 _103844 p1 s p2 t).
Proof. exact (MK_COMB (@lem4326285 _103840 p1 s) (@lem4326284 _103844 p2 t)). Qed.
Lemma lem4326287 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term158 _103840 _103844 p1 s t) = (term86 _103840 _103844 p1 s t).
Proof. exact (fun_ext (fun p2 : _103844 => @lem4326286 _103840 _103844 p1 s p2 t)). Qed.
Lemma lem4326288 {_103844 : Type'} : (@ex _103844) = (@ex _103844).
Proof. exact (eq_refl (@ex _103844)). Qed.
Lemma lem4326289 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term153 _103840 _103844 p1 s t) = (term87 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4326288 _103844) (@lem4326287 _103840 _103844 p1 s t)). Qed.
Lemma lem4326290 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4326291 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term159 _103840 _103844 p1 s t) = (term160 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4326290) (@lem4326289 _103840 _103844 p1 s t)). Qed.
Lemma lem4326292 {_103844 : Type'} (p2 : _103844) (t : _103844 -> Prop) : (term155 _103844 t p2) = (@IN _103844 p2 t).
Proof. exact (eq_refl (term155 _103844 t p2)). Qed.
Lemma lem4326293 {_103844 : Type'} (t : _103844 -> Prop) : (term161 _103844 t) = (term105 _103844 t).
Proof. exact (fun_ext (fun p2 : _103844 => @lem4326292 _103844 p2 t)). Qed.
Lemma lem4326294 {_103844 : Type'} : (@ex _103844) = (@ex _103844).
Proof. exact (eq_refl (@ex _103844)). Qed.
Lemma lem4326295 {_103844 : Type'} (t : _103844 -> Prop) : (term162 _103844 t) = (term106 _103844 t).
Proof. exact (MK_COMB (@lem4326294 _103844) (@lem4326293 _103844 t)). Qed.
Lemma lem4326296 {_103840 : Type'} (p1 : _103840) (s : _103840 -> Prop) : (term156 _103840 p1 s) = (term156 _103840 p1 s).
Proof. exact (eq_refl (term156 _103840 p1 s)). Qed.
Lemma lem4326297 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term154 _103840 _103844 p1 s t) = (term163 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4326296 _103840 p1 s) (@lem4326295 _103844 t)). Qed.
Lemma lem4326298 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : ((term153 _103840 _103844 p1 s t) = (term154 _103840 _103844 p1 s t)) = ((term87 _103840 _103844 p1 s t) = (term163 _103840 _103844 p1 s t)).
Proof. exact (MK_COMB (@lem4326291 _103840 _103844 p1 s t) (@lem4326297 _103840 _103844 p1 s t)). Qed.
Lemma lem4326299 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term87 _103840 _103844 p1 s t) = (term163 _103840 _103844 p1 s t).
Proof. exact (EQ_MP (@lem4326298 _103840 _103844 p1 s t) (@lem4326283 _103840 _103844 p1 s t)). Qed.
Lemma lem4326304 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term95 _103840 _103844 s t) = (term164 _103840 _103844 s t).
Proof. exact (fun_ext (fun p1 : _103840 => @lem4326299 _103840 _103844 p1 s t)). Qed.
Lemma lem4326305 {_103840 : Type'} : (@ex _103840) = (@ex _103840).
Proof. exact (eq_refl (@ex _103840)). Qed.
Lemma lem4326306 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term96 _103840 _103844 s t) = (term165 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326305 _103840) (@lem4326304 _103840 _103844 s t)). Qed.
Lemma lem4326328 {A : Type'} (P : A -> Prop) (Q : Prop) : (term166 A P Q) = (term167 A P Q).
Proof. exact (EQ_MP (@lem18965 A P Q) (@lem18964 A P Q)). Qed.
Lemma lem4326329 {_103840 : Type'} (P : _103840 -> Prop) (Q : Prop) : (term166 _103840 P Q) = (term167 _103840 P Q).
Proof. exact (@lem4326328 _103840 P Q). Qed.
Lemma lem4326330 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term168 _103840 _103844 s t) = (term169 _103840 _103844 s t).
Proof. exact (@lem4326329 _103840 (term105 _103840 s) (term106 _103844 t)). Qed.
Lemma lem4326331 {_103840 : Type'} (p1 : _103840) (s : _103840 -> Prop) : (term155 _103840 s p1) = (@IN _103840 p1 s).
Proof. exact (eq_refl (term155 _103840 s p1)). Qed.
Lemma lem4326332 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4326333 {_103840 : Type'} (p1 : _103840) (s : _103840 -> Prop) : (term170 _103840 s p1) = (term156 _103840 p1 s).
Proof. exact (MK_COMB (@lem4326332) (@lem4326331 _103840 p1 s)). Qed.
Lemma lem4326334 {_103844 : Type'} (t : _103844 -> Prop) : (term106 _103844 t) = (term106 _103844 t).
Proof. exact (eq_refl (term106 _103844 t)). Qed.
Lemma lem4326335 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term171 _103840 _103844 s p1 t) = (term163 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4326333 _103840 p1 s) (@lem4326334 _103844 t)). Qed.
Lemma lem4326336 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term172 _103840 _103844 s t) = (term164 _103840 _103844 s t).
Proof. exact (fun_ext (fun p1 : _103840 => @lem4326335 _103840 _103844 p1 s t)). Qed.
Lemma lem4326337 {_103840 : Type'} : (@ex _103840) = (@ex _103840).
Proof. exact (eq_refl (@ex _103840)). Qed.
Lemma lem4326338 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term168 _103840 _103844 s t) = (term165 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326337 _103840) (@lem4326336 _103840 _103844 s t)). Qed.
Lemma lem4326339 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4326340 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term173 _103840 _103844 s t) = (term174 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326339) (@lem4326338 _103840 _103844 s t)). Qed.
Lemma lem4326341 {_103840 : Type'} (p1 : _103840) (s : _103840 -> Prop) : (term155 _103840 s p1) = (@IN _103840 p1 s).
Proof. exact (eq_refl (term155 _103840 s p1)). Qed.
Lemma lem4326342 {_103840 : Type'} (s : _103840 -> Prop) : (term161 _103840 s) = (term105 _103840 s).
Proof. exact (fun_ext (fun p1 : _103840 => @lem4326341 _103840 p1 s)). Qed.
Lemma lem4326343 {_103840 : Type'} : (@ex _103840) = (@ex _103840).
Proof. exact (eq_refl (@ex _103840)). Qed.
Lemma lem4326344 {_103840 : Type'} (s : _103840 -> Prop) : (term162 _103840 s) = (term106 _103840 s).
Proof. exact (MK_COMB (@lem4326343 _103840) (@lem4326342 _103840 s)). Qed.
Lemma lem4326345 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4326346 {_103840 : Type'} (s : _103840 -> Prop) : (term175 _103840 s) = (term108 _103840 s).
Proof. exact (MK_COMB (@lem4326345) (@lem4326344 _103840 s)). Qed.
Lemma lem4326347 {_103844 : Type'} (t : _103844 -> Prop) : (term106 _103844 t) = (term106 _103844 t).
Proof. exact (eq_refl (term106 _103844 t)). Qed.
Lemma lem4326348 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term169 _103840 _103844 s t) = (term110 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326346 _103840 s) (@lem4326347 _103844 t)). Qed.
Lemma lem4326349 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : ((term168 _103840 _103844 s t) = (term169 _103840 _103844 s t)) = ((term165 _103840 _103844 s t) = (term110 _103840 _103844 s t)).
Proof. exact (MK_COMB (@lem4326340 _103840 _103844 s t) (@lem4326348 _103840 _103844 s t)). Qed.
Lemma lem4326350 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term165 _103840 _103844 s t) = (term110 _103840 _103844 s t).
Proof. exact (EQ_MP (@lem4326349 _103840 _103844 s t) (@lem4326330 _103840 _103844 s t)). Qed.
Lemma lem4326359 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term96 _103840 _103844 s t) = (term110 _103840 _103844 s t).
Proof. exact (TRANS (@lem4326306 _103840 _103844 s t) (@lem4326350 _103840 _103844 s t)). Qed.
Lemma lem4326360 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4326361 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term113 _103840 _103844 s t) = (term176 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326360) (@lem4326359 _103840 _103844 s t)). Qed.
Lemma lem4326370 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term58 _103840 _103844 s t) = (term58 _103840 _103844 s t).
Proof. exact (eq_refl (term58 _103840 _103844 s t)). Qed.
Lemma lem4326371 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term115 _103840 _103844 s t) = (term177 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326361 _103840 _103844 s t) (@lem4326370 _103840 _103844 s t)). Qed.
Lemma lem4326372 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term123 _103840 _103844 s t) = (term178 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326275 _103840 _103844 s t) (@lem4326371 _103840 _103844 s t)). Qed.
Lemma lem4326374 {A : Type'} (P : A -> Prop) (Q : Prop) : (term167 A P Q) = (term166 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4326375 {_103840 : Type'} (P : _103840 -> Prop) (Q : Prop) : (term167 _103840 P Q) = (term166 _103840 P Q).
Proof. exact (@lem4326374 _103840 P Q). Qed.
Lemma lem4326376 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term169 _103840 _103844 s t) = (term168 _103840 _103844 s t).
Proof. exact (@lem4326375 _103840 (term105 _103840 s) (term106 _103844 t)). Qed.
Lemma lem4326377 {_103840 : Type'} (x : _103840) (s : _103840 -> Prop) : (term155 _103840 s x) = (@IN _103840 x s).
Proof. exact (eq_refl (term155 _103840 s x)). Qed.
Lemma lem4326378 {_103840 : Type'} (s : _103840 -> Prop) : (term161 _103840 s) = (term105 _103840 s).
Proof. exact (fun_ext (fun x : _103840 => @lem4326377 _103840 x s)). Qed.
Lemma lem4326379 {_103840 : Type'} : (@ex _103840) = (@ex _103840).
Proof. exact (eq_refl (@ex _103840)). Qed.
Lemma lem4326380 {_103840 : Type'} (s : _103840 -> Prop) : (term162 _103840 s) = (term106 _103840 s).
Proof. exact (MK_COMB (@lem4326379 _103840) (@lem4326378 _103840 s)). Qed.
Lemma lem4326381 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4326382 {_103840 : Type'} (s : _103840 -> Prop) : (term175 _103840 s) = (term108 _103840 s).
Proof. exact (MK_COMB (@lem4326381) (@lem4326380 _103840 s)). Qed.
Lemma lem4326383 {_103844 : Type'} (t : _103844 -> Prop) : (term106 _103844 t) = (term106 _103844 t).
Proof. exact (eq_refl (term106 _103844 t)). Qed.
Lemma lem4326384 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term169 _103840 _103844 s t) = (term110 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326382 _103840 s) (@lem4326383 _103844 t)). Qed.
Lemma lem4326385 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4326386 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term179 _103840 _103844 s t) = (term180 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326385) (@lem4326384 _103840 _103844 s t)). Qed.
Lemma lem4326387 {_103840 : Type'} (x : _103840) (s : _103840 -> Prop) : (term155 _103840 s x) = (@IN _103840 x s).
Proof. exact (eq_refl (term155 _103840 s x)). Qed.
Lemma lem4326388 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4326389 {_103840 : Type'} (x : _103840) (s : _103840 -> Prop) : (term170 _103840 s x) = (term156 _103840 x s).
Proof. exact (MK_COMB (@lem4326388) (@lem4326387 _103840 x s)). Qed.
Lemma lem4326390 {_103844 : Type'} (t : _103844 -> Prop) : (term106 _103844 t) = (term106 _103844 t).
Proof. exact (eq_refl (term106 _103844 t)). Qed.
Lemma lem4326391 {_103840 _103844 : Type'} (x : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term171 _103840 _103844 s x t) = (term163 _103840 _103844 x s t).
Proof. exact (MK_COMB (@lem4326389 _103840 x s) (@lem4326390 _103844 t)). Qed.
Lemma lem4326392 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term172 _103840 _103844 s t) = (term164 _103840 _103844 s t).
Proof. exact (fun_ext (fun x : _103840 => @lem4326391 _103840 _103844 x s t)). Qed.
Lemma lem4326393 {_103840 : Type'} : (@ex _103840) = (@ex _103840).
Proof. exact (eq_refl (@ex _103840)). Qed.
Lemma lem4326394 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term168 _103840 _103844 s t) = (term165 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326393 _103840) (@lem4326392 _103840 _103844 s t)). Qed.
Lemma lem4326395 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : ((term169 _103840 _103844 s t) = (term168 _103840 _103844 s t)) = ((term110 _103840 _103844 s t) = (term165 _103840 _103844 s t)).
Proof. exact (MK_COMB (@lem4326386 _103840 _103844 s t) (@lem4326394 _103840 _103844 s t)). Qed.
Lemma lem4326396 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term110 _103840 _103844 s t) = (term165 _103840 _103844 s t).
Proof. exact (EQ_MP (@lem4326395 _103840 _103844 s t) (@lem4326376 _103840 _103844 s t)). Qed.
Lemma lem4326398 {A : Type'} (P : Prop) (Q : A -> Prop) : (term152 A P Q) = (term151 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4326399 {_103844 : Type'} (P : Prop) (Q : _103844 -> Prop) : (term152 _103844 P Q) = (term151 _103844 P Q).
Proof. exact (@lem4326398 _103844 P Q). Qed.
Lemma lem4326400 {_103840 _103844 : Type'} (x : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term154 _103840 _103844 x s t) = (term153 _103840 _103844 x s t).
Proof. exact (@lem4326399 _103844 (@IN _103840 x s) (term105 _103844 t)). Qed.
Lemma lem4326401 {_103844 : Type'} (x : _103844) (t : _103844 -> Prop) : (term155 _103844 t x) = (@IN _103844 x t).
Proof. exact (eq_refl (term155 _103844 t x)). Qed.
Lemma lem4326402 {_103844 : Type'} (t : _103844 -> Prop) : (term161 _103844 t) = (term105 _103844 t).
Proof. exact (fun_ext (fun x : _103844 => @lem4326401 _103844 x t)). Qed.
Lemma lem4326403 {_103844 : Type'} : (@ex _103844) = (@ex _103844).
Proof. exact (eq_refl (@ex _103844)). Qed.
Lemma lem4326404 {_103844 : Type'} (t : _103844 -> Prop) : (term162 _103844 t) = (term106 _103844 t).
Proof. exact (MK_COMB (@lem4326403 _103844) (@lem4326402 _103844 t)). Qed.
Lemma lem4326405 {_103840 : Type'} (x : _103840) (s : _103840 -> Prop) : (term156 _103840 x s) = (term156 _103840 x s).
Proof. exact (eq_refl (term156 _103840 x s)). Qed.
Lemma lem4326406 {_103840 _103844 : Type'} (x : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term154 _103840 _103844 x s t) = (term163 _103840 _103844 x s t).
Proof. exact (MK_COMB (@lem4326405 _103840 x s) (@lem4326404 _103844 t)). Qed.
Lemma lem4326407 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4326408 {_103840 _103844 : Type'} (x : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term181 _103840 _103844 x s t) = (term182 _103840 _103844 x s t).
Proof. exact (MK_COMB (@lem4326407) (@lem4326406 _103840 _103844 x s t)). Qed.
Lemma lem4326409 {_103844 : Type'} (x : _103844) (t : _103844 -> Prop) : (term155 _103844 t x) = (@IN _103844 x t).
Proof. exact (eq_refl (term155 _103844 t x)). Qed.
Lemma lem4326410 {_103840 : Type'} (x : _103840) (s : _103840 -> Prop) : (term156 _103840 x s) = (term156 _103840 x s).
Proof. exact (eq_refl (term156 _103840 x s)). Qed.
Lemma lem4326411 {_103840 _103844 : Type'} (x : _103840) (s : _103840 -> Prop) (x' : _103844) (t : _103844 -> Prop) : (term157 _103840 _103844 x s t x') = (term11 _103840 _103844 x s x' t).
Proof. exact (MK_COMB (@lem4326410 _103840 x s) (@lem4326409 _103844 x' t)). Qed.
Lemma lem4326412 {_103840 _103844 : Type'} (x : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term158 _103840 _103844 x s t) = (term86 _103840 _103844 x s t).
Proof. exact (fun_ext (fun x' : _103844 => @lem4326411 _103840 _103844 x s x' t)). Qed.
Lemma lem4326413 {_103844 : Type'} : (@ex _103844) = (@ex _103844).
Proof. exact (eq_refl (@ex _103844)). Qed.
Lemma lem4326414 {_103840 _103844 : Type'} (x : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term153 _103840 _103844 x s t) = (term87 _103840 _103844 x s t).
Proof. exact (MK_COMB (@lem4326413 _103844) (@lem4326412 _103840 _103844 x s t)). Qed.
Lemma lem4326415 {_103840 _103844 : Type'} (x : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : ((term154 _103840 _103844 x s t) = (term153 _103840 _103844 x s t)) = ((term163 _103840 _103844 x s t) = (term87 _103840 _103844 x s t)).
Proof. exact (MK_COMB (@lem4326408 _103840 _103844 x s t) (@lem4326414 _103840 _103844 x s t)). Qed.
Lemma lem4326416 {_103840 _103844 : Type'} (x : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term163 _103840 _103844 x s t) = (term87 _103840 _103844 x s t).
Proof. exact (EQ_MP (@lem4326415 _103840 _103844 x s t) (@lem4326400 _103840 _103844 x s t)). Qed.
Lemma lem4326417 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term164 _103840 _103844 s t) = (term95 _103840 _103844 s t).
Proof. exact (fun_ext (fun x : _103840 => @lem4326416 _103840 _103844 x s t)). Qed.
Lemma lem4326418 {_103840 : Type'} : (@ex _103840) = (@ex _103840).
Proof. exact (eq_refl (@ex _103840)). Qed.
Lemma lem4326419 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term165 _103840 _103844 s t) = (term96 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326418 _103840) (@lem4326417 _103840 _103844 s t)). Qed.
Lemma lem4326420 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term110 _103840 _103844 s t) = (term96 _103840 _103844 s t).
Proof. exact (TRANS (@lem4326396 _103840 _103844 s t) (@lem4326419 _103840 _103844 s t)). Qed.
Lemma lem4326421 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term148 _103840 _103844 s t) = (term148 _103840 _103844 s t).
Proof. exact (eq_refl (term148 _103840 _103844 s t)). Qed.
Lemma lem4326422 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term149 _103840 _103844 s t) = (term183 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326421 _103840 _103844 s t) (@lem4326420 _103840 _103844 s t)). Qed.
Lemma lem4326424 {A : Type'} (P : Prop) (Q : A -> Prop) : (term152 A P Q) = (term151 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4326425 {_103840 : Type'} (P : Prop) (Q : _103840 -> Prop) : (term152 _103840 P Q) = (term151 _103840 P Q).
Proof. exact (@lem4326424 _103840 P Q). Qed.
Lemma lem4326426 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term184 _103840 _103844 s t) = (term185 _103840 _103844 s t).
Proof. exact (@lem4326425 _103840 (term58 _103840 _103844 s t) (term95 _103840 _103844 s t)). Qed.
Lemma lem4326427 {_103840 _103844 : Type'} (x : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term186 _103840 _103844 s t x) = (term87 _103840 _103844 x s t).
Proof. exact (eq_refl (term186 _103840 _103844 s t x)). Qed.
Lemma lem4326428 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term187 _103840 _103844 s t) = (term95 _103840 _103844 s t).
Proof. exact (fun_ext (fun x : _103840 => @lem4326427 _103840 _103844 x s t)). Qed.
Lemma lem4326429 {_103840 : Type'} : (@ex _103840) = (@ex _103840).
Proof. exact (eq_refl (@ex _103840)). Qed.
Lemma lem4326430 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term188 _103840 _103844 s t) = (term96 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326429 _103840) (@lem4326428 _103840 _103844 s t)). Qed.
Lemma lem4326431 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term148 _103840 _103844 s t) = (term148 _103840 _103844 s t).
Proof. exact (eq_refl (term148 _103840 _103844 s t)). Qed.
Lemma lem4326432 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term184 _103840 _103844 s t) = (term183 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326431 _103840 _103844 s t) (@lem4326430 _103840 _103844 s t)). Qed.
Lemma lem4326433 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4326434 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term189 _103840 _103844 s t) = (term190 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326433) (@lem4326432 _103840 _103844 s t)). Qed.
Lemma lem4326435 {_103840 _103844 : Type'} (x : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term186 _103840 _103844 s t x) = (term87 _103840 _103844 x s t).
Proof. exact (eq_refl (term186 _103840 _103844 s t x)). Qed.
Lemma lem4326436 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term148 _103840 _103844 s t) = (term148 _103840 _103844 s t).
Proof. exact (eq_refl (term148 _103840 _103844 s t)). Qed.
Lemma lem4326437 {_103840 _103844 : Type'} (x : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term191 _103840 _103844 s t x) = (term192 _103840 _103844 x s t).
Proof. exact (MK_COMB (@lem4326436 _103840 _103844 s t) (@lem4326435 _103840 _103844 x s t)). Qed.
Lemma lem4326438 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term193 _103840 _103844 s t) = (term194 _103840 _103844 s t).
Proof. exact (fun_ext (fun x : _103840 => @lem4326437 _103840 _103844 x s t)). Qed.
Lemma lem4326439 {_103840 : Type'} : (@ex _103840) = (@ex _103840).
Proof. exact (eq_refl (@ex _103840)). Qed.
Lemma lem4326440 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term185 _103840 _103844 s t) = (term195 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326439 _103840) (@lem4326438 _103840 _103844 s t)). Qed.
Lemma lem4326441 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : ((term184 _103840 _103844 s t) = (term185 _103840 _103844 s t)) = ((term183 _103840 _103844 s t) = (term195 _103840 _103844 s t)).
Proof. exact (MK_COMB (@lem4326434 _103840 _103844 s t) (@lem4326440 _103840 _103844 s t)). Qed.
Lemma lem4326442 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term183 _103840 _103844 s t) = (term195 _103840 _103844 s t).
Proof. exact (EQ_MP (@lem4326441 _103840 _103844 s t) (@lem4326426 _103840 _103844 s t)). Qed.
Lemma lem4326444 {A : Type'} (P : Prop) (Q : A -> Prop) : (term152 A P Q) = (term151 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4326445 {_103844 : Type'} (P : Prop) (Q : _103844 -> Prop) : (term152 _103844 P Q) = (term151 _103844 P Q).
Proof. exact (@lem4326444 _103844 P Q). Qed.
Lemma lem4326446 {_103840 _103844 : Type'} (x : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term196 _103840 _103844 x s t) = (term197 _103840 _103844 x s t).
Proof. exact (@lem4326445 _103844 (term58 _103840 _103844 s t) (term86 _103840 _103844 x s t)). Qed.
Lemma lem4326447 {_103840 _103844 : Type'} (x : _103840) (s : _103840 -> Prop) (x' : _103844) (t : _103844 -> Prop) : (term198 _103840 _103844 x s t x') = (term11 _103840 _103844 x s x' t).
Proof. exact (eq_refl (term198 _103840 _103844 x s t x')). Qed.
Lemma lem4326448 {_103840 _103844 : Type'} (x : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term199 _103840 _103844 x s t) = (term86 _103840 _103844 x s t).
Proof. exact (fun_ext (fun x' : _103844 => @lem4326447 _103840 _103844 x s x' t)). Qed.
Lemma lem4326449 {_103844 : Type'} : (@ex _103844) = (@ex _103844).
Proof. exact (eq_refl (@ex _103844)). Qed.
Lemma lem4326450 {_103840 _103844 : Type'} (x : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term200 _103840 _103844 x s t) = (term87 _103840 _103844 x s t).
Proof. exact (MK_COMB (@lem4326449 _103844) (@lem4326448 _103840 _103844 x s t)). Qed.
Lemma lem4326451 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term148 _103840 _103844 s t) = (term148 _103840 _103844 s t).
Proof. exact (eq_refl (term148 _103840 _103844 s t)). Qed.
Lemma lem4326452 {_103840 _103844 : Type'} (x : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term196 _103840 _103844 x s t) = (term192 _103840 _103844 x s t).
Proof. exact (MK_COMB (@lem4326451 _103840 _103844 s t) (@lem4326450 _103840 _103844 x s t)). Qed.
Lemma lem4326453 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4326454 {_103840 _103844 : Type'} (x : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term201 _103840 _103844 x s t) = (term202 _103840 _103844 x s t).
Proof. exact (MK_COMB (@lem4326453) (@lem4326452 _103840 _103844 x s t)). Qed.
Lemma lem4326455 {_103840 _103844 : Type'} (x : _103840) (s : _103840 -> Prop) (x' : _103844) (t : _103844 -> Prop) : (term198 _103840 _103844 x s t x') = (term11 _103840 _103844 x s x' t).
Proof. exact (eq_refl (term198 _103840 _103844 x s t x')). Qed.
Lemma lem4326456 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term148 _103840 _103844 s t) = (term148 _103840 _103844 s t).
Proof. exact (eq_refl (term148 _103840 _103844 s t)). Qed.
Lemma lem4326457 {_103840 _103844 : Type'} (x : _103840) (s : _103840 -> Prop) (x' : _103844) (t : _103844 -> Prop) : (term203 _103840 _103844 x s t x') = (term204 _103840 _103844 x s x' t).
Proof. exact (MK_COMB (@lem4326456 _103840 _103844 s t) (@lem4326455 _103840 _103844 x s x' t)). Qed.
Lemma lem4326458 {_103840 _103844 : Type'} (x : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term205 _103840 _103844 x s t) = (term206 _103840 _103844 x s t).
Proof. exact (fun_ext (fun x' : _103844 => @lem4326457 _103840 _103844 x s x' t)). Qed.
Lemma lem4326459 {_103844 : Type'} : (@ex _103844) = (@ex _103844).
Proof. exact (eq_refl (@ex _103844)). Qed.
Lemma lem4326460 {_103840 _103844 : Type'} (x : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term197 _103840 _103844 x s t) = (term207 _103840 _103844 x s t).
Proof. exact (MK_COMB (@lem4326459 _103844) (@lem4326458 _103840 _103844 x s t)). Qed.
Lemma lem4326461 {_103840 _103844 : Type'} (x : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : ((term196 _103840 _103844 x s t) = (term197 _103840 _103844 x s t)) = ((term192 _103840 _103844 x s t) = (term207 _103840 _103844 x s t)).
Proof. exact (MK_COMB (@lem4326454 _103840 _103844 x s t) (@lem4326460 _103840 _103844 x s t)). Qed.
Lemma lem4326462 {_103840 _103844 : Type'} (x : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term192 _103840 _103844 x s t) = (term207 _103840 _103844 x s t).
Proof. exact (EQ_MP (@lem4326461 _103840 _103844 x s t) (@lem4326446 _103840 _103844 x s t)). Qed.
Lemma lem4326463 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term194 _103840 _103844 s t) = (term208 _103840 _103844 s t).
Proof. exact (fun_ext (fun x : _103840 => @lem4326462 _103840 _103844 x s t)). Qed.
Lemma lem4326464 {_103840 : Type'} : (@ex _103840) = (@ex _103840).
Proof. exact (eq_refl (@ex _103840)). Qed.
Lemma lem4326465 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term195 _103840 _103844 s t) = (term209 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326464 _103840) (@lem4326463 _103840 _103844 s t)). Qed.
Lemma lem4326466 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term183 _103840 _103844 s t) = (term209 _103840 _103844 s t).
Proof. exact (TRANS (@lem4326442 _103840 _103844 s t) (@lem4326465 _103840 _103844 s t)). Qed.
Lemma lem4326467 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term149 _103840 _103844 s t) = (term209 _103840 _103844 s t).
Proof. exact (TRANS (@lem4326422 _103840 _103844 s t) (@lem4326466 _103840 _103844 s t)). Qed.
Lemma lem4326468 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4326469 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term150 _103840 _103844 s t) = (term210 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326468) (@lem4326467 _103840 _103844 s t)). Qed.
Lemma lem4326471 {A : Type'} (P : A -> Prop) (Q : Prop) : (term167 A P Q) = (term166 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4326472 {_103840 : Type'} (P : _103840 -> Prop) (Q : Prop) : (term167 _103840 P Q) = (term166 _103840 P Q).
Proof. exact (@lem4326471 _103840 P Q). Qed.
Lemma lem4326473 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term169 _103840 _103844 s t) = (term168 _103840 _103844 s t).
Proof. exact (@lem4326472 _103840 (term105 _103840 s) (term106 _103844 t)). Qed.
Lemma lem4326474 {_103840 : Type'} (p1 : _103840) (s : _103840 -> Prop) : (term155 _103840 s p1) = (@IN _103840 p1 s).
Proof. exact (eq_refl (term155 _103840 s p1)). Qed.
Lemma lem4326475 {_103840 : Type'} (s : _103840 -> Prop) : (term161 _103840 s) = (term105 _103840 s).
Proof. exact (fun_ext (fun p1 : _103840 => @lem4326474 _103840 p1 s)). Qed.
Lemma lem4326476 {_103840 : Type'} : (@ex _103840) = (@ex _103840).
Proof. exact (eq_refl (@ex _103840)). Qed.
Lemma lem4326477 {_103840 : Type'} (s : _103840 -> Prop) : (term162 _103840 s) = (term106 _103840 s).
Proof. exact (MK_COMB (@lem4326476 _103840) (@lem4326475 _103840 s)). Qed.
Lemma lem4326478 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4326479 {_103840 : Type'} (s : _103840 -> Prop) : (term175 _103840 s) = (term108 _103840 s).
Proof. exact (MK_COMB (@lem4326478) (@lem4326477 _103840 s)). Qed.
Lemma lem4326480 {_103844 : Type'} (t : _103844 -> Prop) : (term106 _103844 t) = (term106 _103844 t).
Proof. exact (eq_refl (term106 _103844 t)). Qed.
Lemma lem4326481 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term169 _103840 _103844 s t) = (term110 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326479 _103840 s) (@lem4326480 _103844 t)). Qed.
Lemma lem4326482 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4326483 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term179 _103840 _103844 s t) = (term180 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326482) (@lem4326481 _103840 _103844 s t)). Qed.
Lemma lem4326484 {_103840 : Type'} (p1 : _103840) (s : _103840 -> Prop) : (term155 _103840 s p1) = (@IN _103840 p1 s).
Proof. exact (eq_refl (term155 _103840 s p1)). Qed.
Lemma lem4326485 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4326486 {_103840 : Type'} (p1 : _103840) (s : _103840 -> Prop) : (term170 _103840 s p1) = (term156 _103840 p1 s).
Proof. exact (MK_COMB (@lem4326485) (@lem4326484 _103840 p1 s)). Qed.
Lemma lem4326487 {_103844 : Type'} (t : _103844 -> Prop) : (term106 _103844 t) = (term106 _103844 t).
Proof. exact (eq_refl (term106 _103844 t)). Qed.
Lemma lem4326488 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term171 _103840 _103844 s p1 t) = (term163 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4326486 _103840 p1 s) (@lem4326487 _103844 t)). Qed.
Lemma lem4326489 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term172 _103840 _103844 s t) = (term164 _103840 _103844 s t).
Proof. exact (fun_ext (fun p1 : _103840 => @lem4326488 _103840 _103844 p1 s t)). Qed.
Lemma lem4326490 {_103840 : Type'} : (@ex _103840) = (@ex _103840).
Proof. exact (eq_refl (@ex _103840)). Qed.
Lemma lem4326491 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term168 _103840 _103844 s t) = (term165 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326490 _103840) (@lem4326489 _103840 _103844 s t)). Qed.
Lemma lem4326492 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : ((term169 _103840 _103844 s t) = (term168 _103840 _103844 s t)) = ((term110 _103840 _103844 s t) = (term165 _103840 _103844 s t)).
Proof. exact (MK_COMB (@lem4326483 _103840 _103844 s t) (@lem4326491 _103840 _103844 s t)). Qed.
Lemma lem4326493 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term110 _103840 _103844 s t) = (term165 _103840 _103844 s t).
Proof. exact (EQ_MP (@lem4326492 _103840 _103844 s t) (@lem4326473 _103840 _103844 s t)). Qed.
Lemma lem4326495 {A : Type'} (P : Prop) (Q : A -> Prop) : (term152 A P Q) = (term151 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4326496 {_103844 : Type'} (P : Prop) (Q : _103844 -> Prop) : (term152 _103844 P Q) = (term151 _103844 P Q).
Proof. exact (@lem4326495 _103844 P Q). Qed.
Lemma lem4326497 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term154 _103840 _103844 p1 s t) = (term153 _103840 _103844 p1 s t).
Proof. exact (@lem4326496 _103844 (@IN _103840 p1 s) (term105 _103844 t)). Qed.
Lemma lem4326498 {_103844 : Type'} (p2 : _103844) (t : _103844 -> Prop) : (term155 _103844 t p2) = (@IN _103844 p2 t).
Proof. exact (eq_refl (term155 _103844 t p2)). Qed.
Lemma lem4326499 {_103844 : Type'} (t : _103844 -> Prop) : (term161 _103844 t) = (term105 _103844 t).
Proof. exact (fun_ext (fun p2 : _103844 => @lem4326498 _103844 p2 t)). Qed.
Lemma lem4326500 {_103844 : Type'} : (@ex _103844) = (@ex _103844).
Proof. exact (eq_refl (@ex _103844)). Qed.
Lemma lem4326501 {_103844 : Type'} (t : _103844 -> Prop) : (term162 _103844 t) = (term106 _103844 t).
Proof. exact (MK_COMB (@lem4326500 _103844) (@lem4326499 _103844 t)). Qed.
Lemma lem4326502 {_103840 : Type'} (p1 : _103840) (s : _103840 -> Prop) : (term156 _103840 p1 s) = (term156 _103840 p1 s).
Proof. exact (eq_refl (term156 _103840 p1 s)). Qed.
Lemma lem4326503 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term154 _103840 _103844 p1 s t) = (term163 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4326502 _103840 p1 s) (@lem4326501 _103844 t)). Qed.
Lemma lem4326504 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4326505 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term181 _103840 _103844 p1 s t) = (term182 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4326504) (@lem4326503 _103840 _103844 p1 s t)). Qed.
Lemma lem4326506 {_103844 : Type'} (p2 : _103844) (t : _103844 -> Prop) : (term155 _103844 t p2) = (@IN _103844 p2 t).
Proof. exact (eq_refl (term155 _103844 t p2)). Qed.
Lemma lem4326507 {_103840 : Type'} (p1 : _103840) (s : _103840 -> Prop) : (term156 _103840 p1 s) = (term156 _103840 p1 s).
Proof. exact (eq_refl (term156 _103840 p1 s)). Qed.
Lemma lem4326508 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) : (term157 _103840 _103844 p1 s t p2) = (term11 _103840 _103844 p1 s p2 t).
Proof. exact (MK_COMB (@lem4326507 _103840 p1 s) (@lem4326506 _103844 p2 t)). Qed.
Lemma lem4326509 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term158 _103840 _103844 p1 s t) = (term86 _103840 _103844 p1 s t).
Proof. exact (fun_ext (fun p2 : _103844 => @lem4326508 _103840 _103844 p1 s p2 t)). Qed.
Lemma lem4326510 {_103844 : Type'} : (@ex _103844) = (@ex _103844).
Proof. exact (eq_refl (@ex _103844)). Qed.
Lemma lem4326511 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term153 _103840 _103844 p1 s t) = (term87 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4326510 _103844) (@lem4326509 _103840 _103844 p1 s t)). Qed.
Lemma lem4326512 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : ((term154 _103840 _103844 p1 s t) = (term153 _103840 _103844 p1 s t)) = ((term163 _103840 _103844 p1 s t) = (term87 _103840 _103844 p1 s t)).
Proof. exact (MK_COMB (@lem4326505 _103840 _103844 p1 s t) (@lem4326511 _103840 _103844 p1 s t)). Qed.
Lemma lem4326513 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term163 _103840 _103844 p1 s t) = (term87 _103840 _103844 p1 s t).
Proof. exact (EQ_MP (@lem4326512 _103840 _103844 p1 s t) (@lem4326497 _103840 _103844 p1 s t)). Qed.
Lemma lem4326514 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term164 _103840 _103844 s t) = (term95 _103840 _103844 s t).
Proof. exact (fun_ext (fun p1 : _103840 => @lem4326513 _103840 _103844 p1 s t)). Qed.
Lemma lem4326515 {_103840 : Type'} : (@ex _103840) = (@ex _103840).
Proof. exact (eq_refl (@ex _103840)). Qed.
Lemma lem4326516 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term165 _103840 _103844 s t) = (term96 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326515 _103840) (@lem4326514 _103840 _103844 s t)). Qed.
Lemma lem4326517 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term110 _103840 _103844 s t) = (term96 _103840 _103844 s t).
Proof. exact (TRANS (@lem4326493 _103840 _103844 s t) (@lem4326516 _103840 _103844 s t)). Qed.
Lemma lem4326518 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4326519 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term176 _103840 _103844 s t) = (term113 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326518) (@lem4326517 _103840 _103844 s t)). Qed.
Lemma lem4326520 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term58 _103840 _103844 s t) = (term58 _103840 _103844 s t).
Proof. exact (eq_refl (term58 _103840 _103844 s t)). Qed.
Lemma lem4326521 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term177 _103840 _103844 s t) = (term115 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326519 _103840 _103844 s t) (@lem4326520 _103840 _103844 s t)). Qed.
Lemma lem4326523 {A : Type'} (P : A -> Prop) (Q : Prop) : (term167 A P Q) = (term166 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4326524 {_103840 : Type'} (P : _103840 -> Prop) (Q : Prop) : (term167 _103840 P Q) = (term166 _103840 P Q).
Proof. exact (@lem4326523 _103840 P Q). Qed.
Lemma lem4326525 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term211 _103840 _103844 s t) = (term212 _103840 _103844 s t).
Proof. exact (@lem4326524 _103840 (term95 _103840 _103844 s t) (term58 _103840 _103844 s t)). Qed.
Lemma lem4326526 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term186 _103840 _103844 s t p1) = (term87 _103840 _103844 p1 s t).
Proof. exact (eq_refl (term186 _103840 _103844 s t p1)). Qed.
Lemma lem4326527 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term187 _103840 _103844 s t) = (term95 _103840 _103844 s t).
Proof. exact (fun_ext (fun p1 : _103840 => @lem4326526 _103840 _103844 p1 s t)). Qed.
Lemma lem4326528 {_103840 : Type'} : (@ex _103840) = (@ex _103840).
Proof. exact (eq_refl (@ex _103840)). Qed.
Lemma lem4326529 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term188 _103840 _103844 s t) = (term96 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326528 _103840) (@lem4326527 _103840 _103844 s t)). Qed.
Lemma lem4326530 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4326531 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term213 _103840 _103844 s t) = (term113 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326530) (@lem4326529 _103840 _103844 s t)). Qed.
Lemma lem4326532 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term58 _103840 _103844 s t) = (term58 _103840 _103844 s t).
Proof. exact (eq_refl (term58 _103840 _103844 s t)). Qed.
Lemma lem4326533 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term211 _103840 _103844 s t) = (term115 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326531 _103840 _103844 s t) (@lem4326532 _103840 _103844 s t)). Qed.
Lemma lem4326534 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4326535 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term214 _103840 _103844 s t) = (term215 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326534) (@lem4326533 _103840 _103844 s t)). Qed.
Lemma lem4326536 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term186 _103840 _103844 s t p1) = (term87 _103840 _103844 p1 s t).
Proof. exact (eq_refl (term186 _103840 _103844 s t p1)). Qed.
Lemma lem4326537 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4326538 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term216 _103840 _103844 s t p1) = (term217 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4326537) (@lem4326536 _103840 _103844 p1 s t)). Qed.
Lemma lem4326539 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term58 _103840 _103844 s t) = (term58 _103840 _103844 s t).
Proof. exact (eq_refl (term58 _103840 _103844 s t)). Qed.
Lemma lem4326540 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term218 _103840 _103844 p1 s t) = (term219 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4326538 _103840 _103844 p1 s t) (@lem4326539 _103840 _103844 s t)). Qed.
Lemma lem4326541 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term220 _103840 _103844 s t) = (term221 _103840 _103844 s t).
Proof. exact (fun_ext (fun p1 : _103840 => @lem4326540 _103840 _103844 p1 s t)). Qed.
Lemma lem4326542 {_103840 : Type'} : (@ex _103840) = (@ex _103840).
Proof. exact (eq_refl (@ex _103840)). Qed.
Lemma lem4326543 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term212 _103840 _103844 s t) = (term222 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326542 _103840) (@lem4326541 _103840 _103844 s t)). Qed.
Lemma lem4326544 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : ((term211 _103840 _103844 s t) = (term212 _103840 _103844 s t)) = ((term115 _103840 _103844 s t) = (term222 _103840 _103844 s t)).
Proof. exact (MK_COMB (@lem4326535 _103840 _103844 s t) (@lem4326543 _103840 _103844 s t)). Qed.
Lemma lem4326545 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term115 _103840 _103844 s t) = (term222 _103840 _103844 s t).
Proof. exact (EQ_MP (@lem4326544 _103840 _103844 s t) (@lem4326525 _103840 _103844 s t)). Qed.
Lemma lem4326547 {A : Type'} (P : A -> Prop) (Q : Prop) : (term167 A P Q) = (term166 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4326548 {_103844 : Type'} (P : _103844 -> Prop) (Q : Prop) : (term167 _103844 P Q) = (term166 _103844 P Q).
Proof. exact (@lem4326547 _103844 P Q). Qed.
Lemma lem4326549 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term223 _103840 _103844 p1 s t) = (term224 _103840 _103844 p1 s t).
Proof. exact (@lem4326548 _103844 (term86 _103840 _103844 p1 s t) (term58 _103840 _103844 s t)). Qed.
Lemma lem4326550 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) : (term198 _103840 _103844 p1 s t p2) = (term11 _103840 _103844 p1 s p2 t).
Proof. exact (eq_refl (term198 _103840 _103844 p1 s t p2)). Qed.
Lemma lem4326551 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term199 _103840 _103844 p1 s t) = (term86 _103840 _103844 p1 s t).
Proof. exact (fun_ext (fun p2 : _103844 => @lem4326550 _103840 _103844 p1 s p2 t)). Qed.
Lemma lem4326552 {_103844 : Type'} : (@ex _103844) = (@ex _103844).
Proof. exact (eq_refl (@ex _103844)). Qed.
Lemma lem4326553 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term200 _103840 _103844 p1 s t) = (term87 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4326552 _103844) (@lem4326551 _103840 _103844 p1 s t)). Qed.
Lemma lem4326554 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4326555 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term225 _103840 _103844 p1 s t) = (term217 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4326554) (@lem4326553 _103840 _103844 p1 s t)). Qed.
Lemma lem4326556 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term58 _103840 _103844 s t) = (term58 _103840 _103844 s t).
Proof. exact (eq_refl (term58 _103840 _103844 s t)). Qed.
Lemma lem4326557 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term223 _103840 _103844 p1 s t) = (term219 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4326555 _103840 _103844 p1 s t) (@lem4326556 _103840 _103844 s t)). Qed.
Lemma lem4326558 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4326559 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term226 _103840 _103844 p1 s t) = (term227 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4326558) (@lem4326557 _103840 _103844 p1 s t)). Qed.
Lemma lem4326560 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) : (term198 _103840 _103844 p1 s t p2) = (term11 _103840 _103844 p1 s p2 t).
Proof. exact (eq_refl (term198 _103840 _103844 p1 s t p2)). Qed.
Lemma lem4326561 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4326562 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) : (term228 _103840 _103844 p1 s t p2) = (term229 _103840 _103844 p1 s p2 t).
Proof. exact (MK_COMB (@lem4326561) (@lem4326560 _103840 _103844 p1 s p2 t)). Qed.
Lemma lem4326563 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term58 _103840 _103844 s t) = (term58 _103840 _103844 s t).
Proof. exact (eq_refl (term58 _103840 _103844 s t)). Qed.
Lemma lem4326564 {_103840 _103844 : Type'} (p1 : _103840) (p2 : _103844) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term230 _103840 _103844 p1 p2 s t) = (term231 _103840 _103844 p1 p2 s t).
Proof. exact (MK_COMB (@lem4326562 _103840 _103844 p1 s p2 t) (@lem4326563 _103840 _103844 s t)). Qed.
Lemma lem4326565 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term232 _103840 _103844 p1 s t) = (term233 _103840 _103844 p1 s t).
Proof. exact (fun_ext (fun p2 : _103844 => @lem4326564 _103840 _103844 p1 p2 s t)). Qed.
Lemma lem4326566 {_103844 : Type'} : (@ex _103844) = (@ex _103844).
Proof. exact (eq_refl (@ex _103844)). Qed.
Lemma lem4326567 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term224 _103840 _103844 p1 s t) = (term234 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4326566 _103844) (@lem4326565 _103840 _103844 p1 s t)). Qed.
Lemma lem4326568 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : ((term223 _103840 _103844 p1 s t) = (term224 _103840 _103844 p1 s t)) = ((term219 _103840 _103844 p1 s t) = (term234 _103840 _103844 p1 s t)).
Proof. exact (MK_COMB (@lem4326559 _103840 _103844 p1 s t) (@lem4326567 _103840 _103844 p1 s t)). Qed.
Lemma lem4326569 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term219 _103840 _103844 p1 s t) = (term234 _103840 _103844 p1 s t).
Proof. exact (EQ_MP (@lem4326568 _103840 _103844 p1 s t) (@lem4326549 _103840 _103844 p1 s t)). Qed.
Lemma lem4326570 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term221 _103840 _103844 s t) = (term235 _103840 _103844 s t).
Proof. exact (fun_ext (fun p1 : _103840 => @lem4326569 _103840 _103844 p1 s t)). Qed.
Lemma lem4326571 {_103840 : Type'} : (@ex _103840) = (@ex _103840).
Proof. exact (eq_refl (@ex _103840)). Qed.
Lemma lem4326572 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term222 _103840 _103844 s t) = (term236 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326571 _103840) (@lem4326570 _103840 _103844 s t)). Qed.
Lemma lem4326573 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term115 _103840 _103844 s t) = (term236 _103840 _103844 s t).
Proof. exact (TRANS (@lem4326545 _103840 _103844 s t) (@lem4326572 _103840 _103844 s t)). Qed.
Lemma lem4326574 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term177 _103840 _103844 s t) = (term236 _103840 _103844 s t).
Proof. exact (TRANS (@lem4326521 _103840 _103844 s t) (@lem4326573 _103840 _103844 s t)). Qed.
Lemma lem4326575 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term178 _103840 _103844 s t) = (term237 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326469 _103840 _103844 s t) (@lem4326574 _103840 _103844 s t)). Qed.
Lemma lem4326577 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term238 A P Q) = (term239 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4326578 {_103840 : Type'} (P : _103840 -> Prop) (Q : _103840 -> Prop) : (term238 _103840 P Q) = (term239 _103840 P Q).
Proof. exact (@lem4326577 _103840 P Q). Qed.
Lemma lem4326579 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term240 _103840 _103844 s t) = (term241 _103840 _103844 s t).
Proof. exact (@lem4326578 _103840 (term208 _103840 _103844 s t) (term235 _103840 _103844 s t)). Qed.
Lemma lem4326580 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term242 _103840 _103844 s t p1) = (term207 _103840 _103844 p1 s t).
Proof. exact (eq_refl (term242 _103840 _103844 s t p1)). Qed.
Lemma lem4326581 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term243 _103840 _103844 s t) = (term208 _103840 _103844 s t).
Proof. exact (fun_ext (fun p1 : _103840 => @lem4326580 _103840 _103844 p1 s t)). Qed.
Lemma lem4326582 {_103840 : Type'} : (@ex _103840) = (@ex _103840).
Proof. exact (eq_refl (@ex _103840)). Qed.
Lemma lem4326583 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term244 _103840 _103844 s t) = (term209 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326582 _103840) (@lem4326581 _103840 _103844 s t)). Qed.
Lemma lem4326584 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4326585 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term245 _103840 _103844 s t) = (term210 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326584) (@lem4326583 _103840 _103844 s t)). Qed.
Lemma lem4326586 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term246 _103840 _103844 s t p1) = (term234 _103840 _103844 p1 s t).
Proof. exact (eq_refl (term246 _103840 _103844 s t p1)). Qed.
Lemma lem4326587 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term247 _103840 _103844 s t) = (term235 _103840 _103844 s t).
Proof. exact (fun_ext (fun p1 : _103840 => @lem4326586 _103840 _103844 p1 s t)). Qed.
Lemma lem4326588 {_103840 : Type'} : (@ex _103840) = (@ex _103840).
Proof. exact (eq_refl (@ex _103840)). Qed.
Lemma lem4326589 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term248 _103840 _103844 s t) = (term236 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326588 _103840) (@lem4326587 _103840 _103844 s t)). Qed.
Lemma lem4326590 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term240 _103840 _103844 s t) = (term237 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326585 _103840 _103844 s t) (@lem4326589 _103840 _103844 s t)). Qed.
Lemma lem4326591 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4326592 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term249 _103840 _103844 s t) = (term250 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326591) (@lem4326590 _103840 _103844 s t)). Qed.
Lemma lem4326593 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term242 _103840 _103844 s t p1) = (term207 _103840 _103844 p1 s t).
Proof. exact (eq_refl (term242 _103840 _103844 s t p1)). Qed.
Lemma lem4326594 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4326595 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term251 _103840 _103844 s t p1) = (term252 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4326594) (@lem4326593 _103840 _103844 p1 s t)). Qed.
Lemma lem4326596 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term246 _103840 _103844 s t p1) = (term234 _103840 _103844 p1 s t).
Proof. exact (eq_refl (term246 _103840 _103844 s t p1)). Qed.
Lemma lem4326597 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term253 _103840 _103844 s t p1) = (term254 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4326595 _103840 _103844 p1 s t) (@lem4326596 _103840 _103844 p1 s t)). Qed.
Lemma lem4326598 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term255 _103840 _103844 s t) = (term256 _103840 _103844 s t).
Proof. exact (fun_ext (fun p1 : _103840 => @lem4326597 _103840 _103844 p1 s t)). Qed.
Lemma lem4326599 {_103840 : Type'} : (@ex _103840) = (@ex _103840).
Proof. exact (eq_refl (@ex _103840)). Qed.
Lemma lem4326600 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term241 _103840 _103844 s t) = (term257 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326599 _103840) (@lem4326598 _103840 _103844 s t)). Qed.
Lemma lem4326601 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : ((term240 _103840 _103844 s t) = (term241 _103840 _103844 s t)) = ((term237 _103840 _103844 s t) = (term257 _103840 _103844 s t)).
Proof. exact (MK_COMB (@lem4326592 _103840 _103844 s t) (@lem4326600 _103840 _103844 s t)). Qed.
Lemma lem4326602 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term237 _103840 _103844 s t) = (term257 _103840 _103844 s t).
Proof. exact (EQ_MP (@lem4326601 _103840 _103844 s t) (@lem4326579 _103840 _103844 s t)). Qed.
Lemma lem4326605 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term258 _103840 _103844 s t) = (term258 _103840 _103844 s t).
Proof. exact (eq_refl (term258 _103840 _103844 s t)). Qed.
Lemma lem4326606 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term258 _103840 _103844 s t) = ((term237 _103840 _103844 s t) = (term257 _103840 _103844 s t)).
Proof. exact (eq_refl (term258 _103840 _103844 s t)). Qed.
Lemma lem4326607 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term259 _103840 _103844 s t) = (term259 _103840 _103844 s t).
Proof. exact (eq_refl (term259 _103840 _103844 s t)). Qed.
Lemma lem4326608 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : ((term258 _103840 _103844 s t) = (term258 _103840 _103844 s t)) = ((term258 _103840 _103844 s t) = ((term237 _103840 _103844 s t) = (term257 _103840 _103844 s t))).
Proof. exact (MK_COMB (@lem4326607 _103840 _103844 s t) (@lem4326606 _103840 _103844 s t)). Qed.
Lemma lem4326609 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term258 _103840 _103844 s t) = ((term237 _103840 _103844 s t) = (term257 _103840 _103844 s t)).
Proof. exact (eq_refl (term258 _103840 _103844 s t)). Qed.
Lemma lem4326610 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4326611 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term259 _103840 _103844 s t) = (term260 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326610) (@lem4326609 _103840 _103844 s t)). Qed.
Lemma lem4326612 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : ((term237 _103840 _103844 s t) = (term257 _103840 _103844 s t)) = ((term237 _103840 _103844 s t) = (term257 _103840 _103844 s t)).
Proof. exact (eq_refl ((term237 _103840 _103844 s t) = (term257 _103840 _103844 s t))). Qed.
Lemma lem4326613 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : ((term258 _103840 _103844 s t) = ((term237 _103840 _103844 s t) = (term257 _103840 _103844 s t))) = (((term237 _103840 _103844 s t) = (term257 _103840 _103844 s t)) = ((term237 _103840 _103844 s t) = (term257 _103840 _103844 s t))).
Proof. exact (MK_COMB (@lem4326611 _103840 _103844 s t) (@lem4326612 _103840 _103844 s t)). Qed.
Lemma lem4326614 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : ((term258 _103840 _103844 s t) = (term258 _103840 _103844 s t)) = (((term237 _103840 _103844 s t) = (term257 _103840 _103844 s t)) = ((term237 _103840 _103844 s t) = (term257 _103840 _103844 s t))).
Proof. exact (TRANS (@lem4326608 _103840 _103844 s t) (@lem4326613 _103840 _103844 s t)). Qed.
Lemma lem4326615 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : ((term237 _103840 _103844 s t) = (term257 _103840 _103844 s t)) = ((term237 _103840 _103844 s t) = (term257 _103840 _103844 s t)).
Proof. exact (EQ_MP (@lem4326614 _103840 _103844 s t) (@lem4326605 _103840 _103844 s t)). Qed.
Lemma lem4326616 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term237 _103840 _103844 s t) = (term257 _103840 _103844 s t).
Proof. exact (EQ_MP (@lem4326615 _103840 _103844 s t) (@lem4326602 _103840 _103844 s t)). Qed.
Lemma lem4326618 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term238 A P Q) = (term239 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4326619 {_103844 : Type'} (P : _103844 -> Prop) (Q : _103844 -> Prop) : (term238 _103844 P Q) = (term239 _103844 P Q).
Proof. exact (@lem4326618 _103844 P Q). Qed.
Lemma lem4326620 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term261 _103840 _103844 p1 s t) = (term262 _103840 _103844 p1 s t).
Proof. exact (@lem4326619 _103844 (term206 _103840 _103844 p1 s t) (term233 _103840 _103844 p1 s t)). Qed.
Lemma lem4326621 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) : (term263 _103840 _103844 p1 s t p2) = (term204 _103840 _103844 p1 s p2 t).
Proof. exact (eq_refl (term263 _103840 _103844 p1 s t p2)). Qed.
Lemma lem4326622 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term264 _103840 _103844 p1 s t) = (term206 _103840 _103844 p1 s t).
Proof. exact (fun_ext (fun p2 : _103844 => @lem4326621 _103840 _103844 p1 s p2 t)). Qed.
Lemma lem4326623 {_103844 : Type'} : (@ex _103844) = (@ex _103844).
Proof. exact (eq_refl (@ex _103844)). Qed.
Lemma lem4326624 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term265 _103840 _103844 p1 s t) = (term207 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4326623 _103844) (@lem4326622 _103840 _103844 p1 s t)). Qed.
Lemma lem4326625 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4326626 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term266 _103840 _103844 p1 s t) = (term252 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4326625) (@lem4326624 _103840 _103844 p1 s t)). Qed.
Lemma lem4326627 {_103840 _103844 : Type'} (p1 : _103840) (p2 : _103844) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term267 _103840 _103844 p1 s t p2) = (term231 _103840 _103844 p1 p2 s t).
Proof. exact (eq_refl (term267 _103840 _103844 p1 s t p2)). Qed.
Lemma lem4326628 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term268 _103840 _103844 p1 s t) = (term233 _103840 _103844 p1 s t).
Proof. exact (fun_ext (fun p2 : _103844 => @lem4326627 _103840 _103844 p1 p2 s t)). Qed.
Lemma lem4326629 {_103844 : Type'} : (@ex _103844) = (@ex _103844).
Proof. exact (eq_refl (@ex _103844)). Qed.
Lemma lem4326630 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term269 _103840 _103844 p1 s t) = (term234 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4326629 _103844) (@lem4326628 _103840 _103844 p1 s t)). Qed.
Lemma lem4326631 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term261 _103840 _103844 p1 s t) = (term254 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4326626 _103840 _103844 p1 s t) (@lem4326630 _103840 _103844 p1 s t)). Qed.
Lemma lem4326632 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4326633 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term270 _103840 _103844 p1 s t) = (term271 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4326632) (@lem4326631 _103840 _103844 p1 s t)). Qed.
Lemma lem4326634 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) : (term263 _103840 _103844 p1 s t p2) = (term204 _103840 _103844 p1 s p2 t).
Proof. exact (eq_refl (term263 _103840 _103844 p1 s t p2)). Qed.
Lemma lem4326635 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4326636 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) : (term272 _103840 _103844 p1 s t p2) = (term273 _103840 _103844 p1 s p2 t).
Proof. exact (MK_COMB (@lem4326635) (@lem4326634 _103840 _103844 p1 s p2 t)). Qed.
Lemma lem4326637 {_103840 _103844 : Type'} (p1 : _103840) (p2 : _103844) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term267 _103840 _103844 p1 s t p2) = (term231 _103840 _103844 p1 p2 s t).
Proof. exact (eq_refl (term267 _103840 _103844 p1 s t p2)). Qed.
Lemma lem4326638 {_103840 _103844 : Type'} (p1 : _103840) (p2 : _103844) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term274 _103840 _103844 p1 s t p2) = (term275 _103840 _103844 p1 p2 s t).
Proof. exact (MK_COMB (@lem4326636 _103840 _103844 p1 s p2 t) (@lem4326637 _103840 _103844 p1 p2 s t)). Qed.
Lemma lem4326639 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term276 _103840 _103844 p1 s t) = (term277 _103840 _103844 p1 s t).
Proof. exact (fun_ext (fun p2 : _103844 => @lem4326638 _103840 _103844 p1 p2 s t)). Qed.
Lemma lem4326640 {_103844 : Type'} : (@ex _103844) = (@ex _103844).
Proof. exact (eq_refl (@ex _103844)). Qed.
Lemma lem4326641 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term262 _103840 _103844 p1 s t) = (term278 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4326640 _103844) (@lem4326639 _103840 _103844 p1 s t)). Qed.
Lemma lem4326642 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : ((term261 _103840 _103844 p1 s t) = (term262 _103840 _103844 p1 s t)) = ((term254 _103840 _103844 p1 s t) = (term278 _103840 _103844 p1 s t)).
Proof. exact (MK_COMB (@lem4326633 _103840 _103844 p1 s t) (@lem4326641 _103840 _103844 p1 s t)). Qed.
Lemma lem4326643 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term254 _103840 _103844 p1 s t) = (term278 _103840 _103844 p1 s t).
Proof. exact (EQ_MP (@lem4326642 _103840 _103844 p1 s t) (@lem4326620 _103840 _103844 p1 s t)). Qed.
Lemma lem4326646 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term279 _103840 _103844 p1 s t) = (term279 _103840 _103844 p1 s t).
Proof. exact (eq_refl (term279 _103840 _103844 p1 s t)). Qed.
Lemma lem4326647 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term279 _103840 _103844 p1 s t) = ((term254 _103840 _103844 p1 s t) = (term278 _103840 _103844 p1 s t)).
Proof. exact (eq_refl (term279 _103840 _103844 p1 s t)). Qed.
Lemma lem4326648 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term280 _103840 _103844 p1 s t) = (term280 _103840 _103844 p1 s t).
Proof. exact (eq_refl (term280 _103840 _103844 p1 s t)). Qed.
Lemma lem4326649 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : ((term279 _103840 _103844 p1 s t) = (term279 _103840 _103844 p1 s t)) = ((term279 _103840 _103844 p1 s t) = ((term254 _103840 _103844 p1 s t) = (term278 _103840 _103844 p1 s t))).
Proof. exact (MK_COMB (@lem4326648 _103840 _103844 p1 s t) (@lem4326647 _103840 _103844 p1 s t)). Qed.
Lemma lem4326650 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term279 _103840 _103844 p1 s t) = ((term254 _103840 _103844 p1 s t) = (term278 _103840 _103844 p1 s t)).
Proof. exact (eq_refl (term279 _103840 _103844 p1 s t)). Qed.
Lemma lem4326651 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4326652 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term280 _103840 _103844 p1 s t) = (term281 _103840 _103844 p1 s t).
Proof. exact (MK_COMB (@lem4326651) (@lem4326650 _103840 _103844 p1 s t)). Qed.
Lemma lem4326653 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : ((term254 _103840 _103844 p1 s t) = (term278 _103840 _103844 p1 s t)) = ((term254 _103840 _103844 p1 s t) = (term278 _103840 _103844 p1 s t)).
Proof. exact (eq_refl ((term254 _103840 _103844 p1 s t) = (term278 _103840 _103844 p1 s t))). Qed.
Lemma lem4326654 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : ((term279 _103840 _103844 p1 s t) = ((term254 _103840 _103844 p1 s t) = (term278 _103840 _103844 p1 s t))) = (((term254 _103840 _103844 p1 s t) = (term278 _103840 _103844 p1 s t)) = ((term254 _103840 _103844 p1 s t) = (term278 _103840 _103844 p1 s t))).
Proof. exact (MK_COMB (@lem4326652 _103840 _103844 p1 s t) (@lem4326653 _103840 _103844 p1 s t)). Qed.
Lemma lem4326655 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : ((term279 _103840 _103844 p1 s t) = (term279 _103840 _103844 p1 s t)) = (((term254 _103840 _103844 p1 s t) = (term278 _103840 _103844 p1 s t)) = ((term254 _103840 _103844 p1 s t) = (term278 _103840 _103844 p1 s t))).
Proof. exact (TRANS (@lem4326649 _103840 _103844 p1 s t) (@lem4326654 _103840 _103844 p1 s t)). Qed.
Lemma lem4326656 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : ((term254 _103840 _103844 p1 s t) = (term278 _103840 _103844 p1 s t)) = ((term254 _103840 _103844 p1 s t) = (term278 _103840 _103844 p1 s t)).
Proof. exact (EQ_MP (@lem4326655 _103840 _103844 p1 s t) (@lem4326646 _103840 _103844 p1 s t)). Qed.
Lemma lem4326657 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term254 _103840 _103844 p1 s t) = (term278 _103840 _103844 p1 s t).
Proof. exact (EQ_MP (@lem4326656 _103840 _103844 p1 s t) (@lem4326643 _103840 _103844 p1 s t)). Qed.
Lemma lem4326658 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term256 _103840 _103844 s t) = (term282 _103840 _103844 s t).
Proof. exact (fun_ext (fun p1 : _103840 => @lem4326657 _103840 _103844 p1 s t)). Qed.
Lemma lem4326659 {_103840 : Type'} : (@ex _103840) = (@ex _103840).
Proof. exact (eq_refl (@ex _103840)). Qed.
Lemma lem4326660 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term257 _103840 _103844 s t) = (term283 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326659 _103840) (@lem4326658 _103840 _103844 s t)). Qed.
Lemma lem4326661 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term237 _103840 _103844 s t) = (term283 _103840 _103844 s t).
Proof. exact (TRANS (@lem4326616 _103840 _103844 s t) (@lem4326660 _103840 _103844 s t)). Qed.
Lemma lem4326662 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term178 _103840 _103844 s t) = (term283 _103840 _103844 s t).
Proof. exact (TRANS (@lem4326575 _103840 _103844 s t) (@lem4326661 _103840 _103844 s t)). Qed.
Lemma lem4326663 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term123 _103840 _103844 s t) = (term283 _103840 _103844 s t).
Proof. exact (TRANS (@lem4326372 _103840 _103844 s t) (@lem4326662 _103840 _103844 s t)). Qed.
Lemma lem4326664 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term76 _103840 _103844 s t) = (term283 _103840 _103844 s t).
Proof. exact (TRANS (@lem4326177 _103840 _103844 s t) (@lem4326663 _103840 _103844 s t)). Qed.
Lemma lem4326665 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) (h1 : term76 _103840 _103844 s t) : term283 _103840 _103844 s t.
Proof. exact (EQ_MP (@lem4326664 _103840 _103844 s t) (@lem4326084 _103840 _103844 s t h1)). Qed.
Lemma lem4326666 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) (h1 : term278 _103840 _103844 p1 s t) : term278 _103840 _103844 p1 s t.
Proof. exact (h1). Qed.
Lemma lem4326667 {_103840 _103844 : Type'} (p1 : _103840) (p2 : _103844) (s : _103840 -> Prop) (t : _103844 -> Prop) (h1 : term275 _103840 _103844 p1 p2 s t) : term275 _103840 _103844 p1 p2 s t.
Proof. exact (h1). Qed.
Lemma lem4326674 {_103844 : Type'} (x : _103844) (t : _103844 -> Prop) : (term51 _103844 x t) = (term51 _103844 x t).
Proof. exact (eq_refl (term51 _103844 x t)). Qed.
Lemma lem4326675 {_103844 : Type'} (t : _103844 -> Prop) : (term53 _103844 t) = (term53 _103844 t).
Proof. exact (fun_ext (fun x : _103844 => @lem4326674 _103844 x t)). Qed.
Lemma lem4326676 {_103844 : Type'} : (@all _103844) = (@all _103844).
Proof. exact (eq_refl (@all _103844)). Qed.
Lemma lem4326677 {_103844 : Type'} (t : _103844 -> Prop) : (term54 _103844 t) = (term54 _103844 t).
Proof. exact (MK_COMB (@lem4326676 _103844) (@lem4326675 _103844 t)). Qed.
Lemma lem4326684 {_103840 : Type'} (x : _103840) (s : _103840 -> Prop) : (term51 _103840 x s) = (term51 _103840 x s).
Proof. exact (eq_refl (term51 _103840 x s)). Qed.
Lemma lem4326685 {_103840 : Type'} (s : _103840 -> Prop) : (term53 _103840 s) = (term53 _103840 s).
Proof. exact (fun_ext (fun x : _103840 => @lem4326684 _103840 x s)). Qed.
Lemma lem4326686 {_103840 : Type'} : (@all _103840) = (@all _103840).
Proof. exact (eq_refl (@all _103840)). Qed.
Lemma lem4326687 {_103840 : Type'} (s : _103840 -> Prop) : (term54 _103840 s) = (term54 _103840 s).
Proof. exact (MK_COMB (@lem4326686 _103840) (@lem4326685 _103840 s)). Qed.
Lemma lem4326688 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4326689 {_103840 : Type'} (s : _103840 -> Prop) : (term56 _103840 s) = (term56 _103840 s).
Proof. exact (MK_COMB (@lem4326688) (@lem4326687 _103840 s)). Qed.
Lemma lem4326690 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term58 _103840 _103844 s t) = (term58 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326689 _103840 s) (@lem4326677 _103844 t)). Qed.
Lemma lem4326705 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) : (term229 _103840 _103844 p1 s p2 t) = (term229 _103840 _103844 p1 s p2 t).
Proof. exact (eq_refl (term229 _103840 _103844 p1 s p2 t)). Qed.
Lemma lem4326706 {_103840 _103844 : Type'} (p1 : _103840) (p2 : _103844) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term231 _103840 _103844 p1 p2 s t) = (term231 _103840 _103844 p1 p2 s t).
Proof. exact (MK_COMB (@lem4326705 _103840 _103844 p1 s p2 t) (@lem4326690 _103840 _103844 s t)). Qed.
Lemma lem4326719 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) : (term11 _103840 _103844 p1 s p2 t) = (term11 _103840 _103844 p1 s p2 t).
Proof. exact (eq_refl (term11 _103840 _103844 p1 s p2 t)). Qed.
Lemma lem4326726 {_103844 : Type'} (p2 : _103844) (t : _103844 -> Prop) : (term51 _103844 p2 t) = (term51 _103844 p2 t).
Proof. exact (eq_refl (term51 _103844 p2 t)). Qed.
Lemma lem4326727 {_103844 : Type'} (t : _103844 -> Prop) : (term53 _103844 t) = (term53 _103844 t).
Proof. exact (fun_ext (fun p2 : _103844 => @lem4326726 _103844 p2 t)). Qed.
Lemma lem4326728 {_103844 : Type'} : (@all _103844) = (@all _103844).
Proof. exact (eq_refl (@all _103844)). Qed.
Lemma lem4326729 {_103844 : Type'} (t : _103844 -> Prop) : (term54 _103844 t) = (term54 _103844 t).
Proof. exact (MK_COMB (@lem4326728 _103844) (@lem4326727 _103844 t)). Qed.
Lemma lem4326736 {_103840 : Type'} (p1 : _103840) (s : _103840 -> Prop) : (term51 _103840 p1 s) = (term51 _103840 p1 s).
Proof. exact (eq_refl (term51 _103840 p1 s)). Qed.
Lemma lem4326737 {_103840 : Type'} (s : _103840 -> Prop) : (term53 _103840 s) = (term53 _103840 s).
Proof. exact (fun_ext (fun p1 : _103840 => @lem4326736 _103840 p1 s)). Qed.
Lemma lem4326738 {_103840 : Type'} : (@all _103840) = (@all _103840).
Proof. exact (eq_refl (@all _103840)). Qed.
Lemma lem4326739 {_103840 : Type'} (s : _103840 -> Prop) : (term54 _103840 s) = (term54 _103840 s).
Proof. exact (MK_COMB (@lem4326738 _103840) (@lem4326737 _103840 s)). Qed.
Lemma lem4326740 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4326741 {_103840 : Type'} (s : _103840 -> Prop) : (term56 _103840 s) = (term56 _103840 s).
Proof. exact (MK_COMB (@lem4326740) (@lem4326739 _103840 s)). Qed.
Lemma lem4326742 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term58 _103840 _103844 s t) = (term58 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326741 _103840 s) (@lem4326729 _103844 t)). Qed.
Lemma lem4326743 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4326744 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term148 _103840 _103844 s t) = (term148 _103840 _103844 s t).
Proof. exact (MK_COMB (@lem4326743) (@lem4326742 _103840 _103844 s t)). Qed.
Lemma lem4326745 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) : (term204 _103840 _103844 p1 s p2 t) = (term204 _103840 _103844 p1 s p2 t).
Proof. exact (MK_COMB (@lem4326744 _103840 _103844 s t) (@lem4326719 _103840 _103844 p1 s p2 t)). Qed.
Lemma lem4326746 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4326747 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) : (term273 _103840 _103844 p1 s p2 t) = (term273 _103840 _103844 p1 s p2 t).
Proof. exact (MK_COMB (@lem4326746) (@lem4326745 _103840 _103844 p1 s p2 t)). Qed.
Lemma lem4326748 {_103840 _103844 : Type'} (p1 : _103840) (p2 : _103844) (s : _103840 -> Prop) (t : _103844 -> Prop) : (term275 _103840 _103844 p1 p2 s t) = (term275 _103840 _103844 p1 p2 s t).
Proof. exact (MK_COMB (@lem4326747 _103840 _103844 p1 s p2 t) (@lem4326706 _103840 _103844 p1 p2 s t)). Qed.
Lemma lem4326749 {_103840 _103844 : Type'} (p1 : _103840) (p2 : _103844) (s : _103840 -> Prop) (t : _103844 -> Prop) (h1 : term275 _103840 _103844 p1 p2 s t) : term275 _103840 _103844 p1 p2 s t.
Proof. exact (EQ_MP (@lem4326748 _103840 _103844 p1 p2 s t) (@lem4326667 _103840 _103844 p1 p2 s t h1)). Qed.
Lemma lem4326750 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) (h1 : term204 _103840 _103844 p1 s p2 t) : term204 _103840 _103844 p1 s p2 t.
Proof. exact (h1). Qed.
Lemma lem4326751 {_103840 _103844 : Type'} (p1 : _103840) (p2 : _103844) (s : _103840 -> Prop) (t : _103844 -> Prop) (h1 : term231 _103840 _103844 p1 p2 s t) : term231 _103840 _103844 p1 p2 s t.
Proof. exact (h1). Qed.
Lemma lem4326752 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) (h1 : term204 _103840 _103844 p1 s p2 t) : term11 _103840 _103844 p1 s p2 t.
Proof. exact (proj2 (@lem4326750 _103840 _103844 p1 s p2 t h1)). Qed.
Lemma lem4326753 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) (h1 : term204 _103840 _103844 p1 s p2 t) : term58 _103840 _103844 s t.
Proof. exact (proj1 (@lem4326750 _103840 _103844 p1 s p2 t h1)). Qed.
Lemma lem4326756 {_103840 : Type'} (s : _103840 -> Prop) (h1 : term54 _103840 s) : term54 _103840 s.
Proof. exact (h1). Qed.
Lemma lem4326757 {_103844 : Type'} (t : _103844 -> Prop) (h1 : term54 _103844 t) : term54 _103844 t.
Proof. exact (h1). Qed.
Lemma lem4326758 {_103840 _103844 : Type'} (p1 : _103840) (p2 : _103844) (s : _103840 -> Prop) (t : _103844 -> Prop) (h1 : term231 _103840 _103844 p1 p2 s t) : term58 _103840 _103844 s t.
Proof. exact (proj2 (@lem4326751 _103840 _103844 p1 p2 s t h1)). Qed.
Lemma lem4326759 {_103840 _103844 : Type'} (p1 : _103840) (p2 : _103844) (s : _103840 -> Prop) (t : _103844 -> Prop) (h1 : term231 _103840 _103844 p1 p2 s t) : term11 _103840 _103844 p1 s p2 t.
Proof. exact (proj1 (@lem4326751 _103840 _103844 p1 p2 s t h1)). Qed.
Lemma lem4326762 {_103840 : Type'} (s : _103840 -> Prop) (h1 : term54 _103840 s) : term54 _103840 s.
Proof. exact (h1). Qed.
Lemma lem4326763 {_103844 : Type'} (t : _103844 -> Prop) (h1 : term54 _103844 t) : term54 _103844 t.
Proof. exact (h1). Qed.
Lemma lem4326773 {_103840 : Type'} (p1 : _103840) (s : _103840 -> Prop) : (term51 _103840 p1 s) = (term51 _103840 p1 s).
Proof. exact (eq_refl (term51 _103840 p1 s)). Qed.
Lemma lem4326774 {_103840 : Type'} (s : _103840 -> Prop) : (term53 _103840 s) = (term53 _103840 s).
Proof. exact (fun_ext (fun p1 : _103840 => @lem4326773 _103840 p1 s)). Qed.
Lemma lem4326775 {_103840 : Type'} : (@all _103840) = (@all _103840).
Proof. exact (eq_refl (@all _103840)). Qed.
Lemma lem4326777 {_103840 : Type'} (s : _103840 -> Prop) : (term54 _103840 s) = (term54 _103840 s).
Proof. exact (MK_COMB (@lem4326775 _103840) (@lem4326774 _103840 s)). Qed.
Lemma lem4326778 {_103840 : Type'} (s : _103840 -> Prop) (h1 : term54 _103840 s) : term54 _103840 s.
Proof. exact (EQ_MP (@lem4326777 _103840 s) (@lem4326756 _103840 s h1)). Qed.
Lemma lem4326788 {_103844 : Type'} (p2 : _103844) (t : _103844 -> Prop) : (term51 _103844 p2 t) = (term51 _103844 p2 t).
Proof. exact (eq_refl (term51 _103844 p2 t)). Qed.
Lemma lem4326789 {_103844 : Type'} (t : _103844 -> Prop) : (term53 _103844 t) = (term53 _103844 t).
Proof. exact (fun_ext (fun p2 : _103844 => @lem4326788 _103844 p2 t)). Qed.
Lemma lem4326790 {_103844 : Type'} : (@all _103844) = (@all _103844).
Proof. exact (eq_refl (@all _103844)). Qed.
Lemma lem4326792 {_103844 : Type'} (t : _103844 -> Prop) : (term54 _103844 t) = (term54 _103844 t).
Proof. exact (MK_COMB (@lem4326790 _103844) (@lem4326789 _103844 t)). Qed.
Lemma lem4326793 {_103844 : Type'} (t : _103844 -> Prop) (h1 : term54 _103844 t) : term54 _103844 t.
Proof. exact (EQ_MP (@lem4326792 _103844 t) (@lem4326757 _103844 t h1)). Qed.
Lemma lem4326803 {_103840 : Type'} (x : _103840) (s : _103840 -> Prop) : (term51 _103840 x s) = (term51 _103840 x s).
Proof. exact (eq_refl (term51 _103840 x s)). Qed.
Lemma lem4326804 {_103840 : Type'} (s : _103840 -> Prop) : (term53 _103840 s) = (term53 _103840 s).
Proof. exact (fun_ext (fun x : _103840 => @lem4326803 _103840 x s)). Qed.
Lemma lem4326805 {_103840 : Type'} : (@all _103840) = (@all _103840).
Proof. exact (eq_refl (@all _103840)). Qed.
Lemma lem4326807 {_103840 : Type'} (s : _103840 -> Prop) : (term54 _103840 s) = (term54 _103840 s).
Proof. exact (MK_COMB (@lem4326805 _103840) (@lem4326804 _103840 s)). Qed.
Lemma lem4326808 {_103840 : Type'} (s : _103840 -> Prop) (h1 : term54 _103840 s) : term54 _103840 s.
Proof. exact (EQ_MP (@lem4326807 _103840 s) (@lem4326762 _103840 s h1)). Qed.
Lemma lem4326818 {_103844 : Type'} (x : _103844) (t : _103844 -> Prop) : (term51 _103844 x t) = (term51 _103844 x t).
Proof. exact (eq_refl (term51 _103844 x t)). Qed.
Lemma lem4326819 {_103844 : Type'} (t : _103844 -> Prop) : (term53 _103844 t) = (term53 _103844 t).
Proof. exact (fun_ext (fun x : _103844 => @lem4326818 _103844 x t)). Qed.
Lemma lem4326820 {_103844 : Type'} : (@all _103844) = (@all _103844).
Proof. exact (eq_refl (@all _103844)). Qed.
Lemma lem4326822 {_103844 : Type'} (t : _103844 -> Prop) : (term54 _103844 t) = (term54 _103844 t).
Proof. exact (MK_COMB (@lem4326820 _103844) (@lem4326819 _103844 t)). Qed.
Lemma lem4326823 {_103844 : Type'} (t : _103844 -> Prop) (h1 : term54 _103844 t) : term54 _103844 t.
Proof. exact (EQ_MP (@lem4326822 _103844 t) (@lem4326763 _103844 t h1)). Qed.
Lemma lem4326824 {_103840 : Type'} (_49290 : _103840) (s : _103840 -> Prop) (h1 : term54 _103840 s) : term102 _103840 s _49290.
Proof. exact (@lem4326778 _103840 s h1 _49290). Qed.
Lemma lem4326825 {_103840 : Type'} (_49290 : _103840) (s : _103840 -> Prop) : (term102 _103840 s _49290) = (term51 _103840 _49290 s).
Proof. exact (eq_refl (term102 _103840 s _49290)). Qed.
Lemma lem4326827 {_103844 : Type'} (_49291 : _103844) (t : _103844 -> Prop) (h1 : term54 _103844 t) : term102 _103844 t _49291.
Proof. exact (@lem4326793 _103844 t h1 _49291). Qed.
Lemma lem4326828 {_103844 : Type'} (_49291 : _103844) (t : _103844 -> Prop) : (term102 _103844 t _49291) = (term51 _103844 _49291 t).
Proof. exact (eq_refl (term102 _103844 t _49291)). Qed.
Lemma lem4326830 {_103840 : Type'} (_49292 : _103840) (s : _103840 -> Prop) (h1 : term54 _103840 s) : term102 _103840 s _49292.
Proof. exact (@lem4326808 _103840 s h1 _49292). Qed.
Lemma lem4326831 {_103840 : Type'} (_49292 : _103840) (s : _103840 -> Prop) : (term102 _103840 s _49292) = (term51 _103840 _49292 s).
Proof. exact (eq_refl (term102 _103840 s _49292)). Qed.
Lemma lem4326833 {_103844 : Type'} (_49293 : _103844) (t : _103844 -> Prop) (h1 : term54 _103844 t) : term102 _103844 t _49293.
Proof. exact (@lem4326823 _103844 t h1 _49293). Qed.
Lemma lem4326834 {_103844 : Type'} (_49293 : _103844) (t : _103844 -> Prop) : (term102 _103844 t _49293) = (term51 _103844 _49293 t).
Proof. exact (eq_refl (term102 _103844 t _49293)). Qed.
Lemma lem4326841 {_103840 : Type'} (_49290 : _103840) (s : _103840 -> Prop) (h1 : term54 _103840 s) : term51 _103840 _49290 s.
Proof. exact (EQ_MP (@lem4326825 _103840 _49290 s) (@lem4326824 _103840 _49290 s h1)). Qed.
Lemma lem4326847 {_103844 : Type'} (_49291 : _103844) (t : _103844 -> Prop) (h1 : term54 _103844 t) : term51 _103844 _49291 t.
Proof. exact (EQ_MP (@lem4326828 _103844 _49291 t) (@lem4326827 _103844 _49291 t h1)). Qed.
Lemma lem4326853 {_103840 : Type'} (_49292 : _103840) (s : _103840 -> Prop) (h1 : term54 _103840 s) : term51 _103840 _49292 s.
Proof. exact (EQ_MP (@lem4326831 _103840 _49292 s) (@lem4326830 _103840 _49292 s h1)). Qed.
Lemma lem4326859 {_103844 : Type'} (_49293 : _103844) (t : _103844 -> Prop) (h1 : term54 _103844 t) : term51 _103844 _49293 t.
Proof. exact (EQ_MP (@lem4326834 _103844 _49293 t) (@lem4326833 _103844 _49293 t h1)). Qed.
Lemma lem4326861 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) (h1 : term204 _103840 _103844 p1 s p2 t) : @IN _103840 p1 s.
Proof. exact (proj1 (@lem4326752 _103840 _103844 p1 s p2 t h1)). Qed.
Lemma lem4326862 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) (h1 : term204 _103840 _103844 p1 s p2 t) : term284 _103840 p1 s.
Proof. exact (fun h0 : term51 _103840 p1 s => @lem4326861 _103840 _103844 p1 s p2 t h1). Qed.
Lemma lem4326864 (p : Prop) : (term285 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4326865 {_103840 : Type'} (p1 : _103840) (s : _103840 -> Prop) : (term284 _103840 p1 s) = (@IN _103840 p1 s).
Proof. exact (@lem4326864 (@IN _103840 p1 s)). Qed.
Lemma lem4326866 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) (h1 : term204 _103840 _103844 p1 s p2 t) : @IN _103840 p1 s.
Proof. exact (EQ_MP (@lem4326865 _103840 p1 s) (@lem4326862 _103840 _103844 p1 s p2 t h1)). Qed.
Lemma lem4326869 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4326871 {_103840 : Type'} (_49290 : _103840) (s : _103840 -> Prop) : (term51 _103840 _49290 s) = (term286 _103840 _49290 s).
Proof. exact (@lem4326869 (@IN _103840 _49290 s)). Qed.
Lemma lem4326874 {_103840 : Type'} (_49290 : _103840) (s : _103840 -> Prop) (h1 : term54 _103840 s) : term286 _103840 _49290 s.
Proof. exact (EQ_MP (@lem4326871 _103840 _49290 s) (@lem4326841 _103840 _49290 s h1)). Qed.
Lemma lem4326875 {_103840 : Type'} (_49290 : _103840) (s : _103840 -> Prop) (h1 : term54 _103840 s) : term286 _103840 _49290 s.
Proof. exact (@lem4326874 _103840 _49290 s h1). Qed.
Lemma lem4326876 {_103840 : Type'} (p1 : _103840) (s : _103840 -> Prop) (h1 : term54 _103840 s) : term286 _103840 p1 s.
Proof. exact (@lem4326875 _103840 p1 s h1). Qed.
Lemma lem4326879 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) (h1 : term54 _103840 s) (h2 : term204 _103840 _103844 p1 s p2 t) : False.
Proof. exact (@lem4326876 _103840 p1 s h1 (@lem4326866 _103840 _103844 p1 s p2 t h2)). Qed.
Lemma lem4326880 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) (h1 : term54 _103840 s) (h2 : term204 _103840 _103844 p1 s p2 t) : term287.
Proof. exact (fun h0 : ~ False => @lem4326879 _103840 _103844 p1 s p2 t h1 h2). Qed.
Lemma lem4326882 (p : Prop) : (term285 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4326883 : term287 = False.
Proof. exact (@lem4326882 False). Qed.
Lemma lem4326884 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) (h1 : term54 _103840 s) (h2 : term204 _103840 _103844 p1 s p2 t) : False.
Proof. exact (EQ_MP (@lem4326883) (@lem4326880 _103840 _103844 p1 s p2 t h1 h2)). Qed.
Lemma lem4326886 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) (h1 : term204 _103840 _103844 p1 s p2 t) : @IN _103844 p2 t.
Proof. exact (proj2 (@lem4326752 _103840 _103844 p1 s p2 t h1)). Qed.
Lemma lem4326887 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) (h1 : term204 _103840 _103844 p1 s p2 t) : term284 _103844 p2 t.
Proof. exact (fun h0 : term51 _103844 p2 t => @lem4326886 _103840 _103844 p1 s p2 t h1). Qed.
Lemma lem4326889 (p : Prop) : (term285 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4326890 {_103844 : Type'} (p2 : _103844) (t : _103844 -> Prop) : (term284 _103844 p2 t) = (@IN _103844 p2 t).
Proof. exact (@lem4326889 (@IN _103844 p2 t)). Qed.
Lemma lem4326891 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) (h1 : term204 _103840 _103844 p1 s p2 t) : @IN _103844 p2 t.
Proof. exact (EQ_MP (@lem4326890 _103844 p2 t) (@lem4326887 _103840 _103844 p1 s p2 t h1)). Qed.
Lemma lem4326894 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4326896 {_103844 : Type'} (_49291 : _103844) (t : _103844 -> Prop) : (term51 _103844 _49291 t) = (term286 _103844 _49291 t).
Proof. exact (@lem4326894 (@IN _103844 _49291 t)). Qed.
Lemma lem4326899 {_103844 : Type'} (_49291 : _103844) (t : _103844 -> Prop) (h1 : term54 _103844 t) : term286 _103844 _49291 t.
Proof. exact (EQ_MP (@lem4326896 _103844 _49291 t) (@lem4326847 _103844 _49291 t h1)). Qed.
Lemma lem4326900 {_103844 : Type'} (_49291 : _103844) (t : _103844 -> Prop) (h1 : term54 _103844 t) : term286 _103844 _49291 t.
Proof. exact (@lem4326899 _103844 _49291 t h1). Qed.
Lemma lem4326901 {_103844 : Type'} (p2 : _103844) (t : _103844 -> Prop) (h1 : term54 _103844 t) : term286 _103844 p2 t.
Proof. exact (@lem4326900 _103844 p2 t h1). Qed.
Lemma lem4326904 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) (h1 : term54 _103844 t) (h2 : term204 _103840 _103844 p1 s p2 t) : False.
Proof. exact (@lem4326901 _103844 p2 t h1 (@lem4326891 _103840 _103844 p1 s p2 t h2)). Qed.
Lemma lem4326905 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) (h1 : term54 _103844 t) (h2 : term204 _103840 _103844 p1 s p2 t) : term287.
Proof. exact (fun h0 : ~ False => @lem4326904 _103840 _103844 p1 s p2 t h1 h2). Qed.
Lemma lem4326907 (p : Prop) : (term285 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4326908 : term287 = False.
Proof. exact (@lem4326907 False). Qed.
Lemma lem4326909 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) (h1 : term54 _103844 t) (h2 : term204 _103840 _103844 p1 s p2 t) : False.
Proof. exact (EQ_MP (@lem4326908) (@lem4326905 _103840 _103844 p1 s p2 t h1 h2)). Qed.
Lemma lem4326911 {_103840 _103844 : Type'} (p1 : _103840) (p2 : _103844) (s : _103840 -> Prop) (t : _103844 -> Prop) (h1 : term231 _103840 _103844 p1 p2 s t) : @IN _103840 p1 s.
Proof. exact (proj1 (@lem4326759 _103840 _103844 p1 p2 s t h1)). Qed.
Lemma lem4326912 {_103840 _103844 : Type'} (p1 : _103840) (p2 : _103844) (s : _103840 -> Prop) (t : _103844 -> Prop) (h1 : term231 _103840 _103844 p1 p2 s t) : term284 _103840 p1 s.
Proof. exact (fun h0 : term51 _103840 p1 s => @lem4326911 _103840 _103844 p1 p2 s t h1). Qed.
Lemma lem4326914 (p : Prop) : (term285 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4326915 {_103840 : Type'} (p1 : _103840) (s : _103840 -> Prop) : (term284 _103840 p1 s) = (@IN _103840 p1 s).
Proof. exact (@lem4326914 (@IN _103840 p1 s)). Qed.
Lemma lem4326916 {_103840 _103844 : Type'} (p1 : _103840) (p2 : _103844) (s : _103840 -> Prop) (t : _103844 -> Prop) (h1 : term231 _103840 _103844 p1 p2 s t) : @IN _103840 p1 s.
Proof. exact (EQ_MP (@lem4326915 _103840 p1 s) (@lem4326912 _103840 _103844 p1 p2 s t h1)). Qed.
Lemma lem4326919 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4326921 {_103840 : Type'} (_49292 : _103840) (s : _103840 -> Prop) : (term51 _103840 _49292 s) = (term286 _103840 _49292 s).
Proof. exact (@lem4326919 (@IN _103840 _49292 s)). Qed.
Lemma lem4326924 {_103840 : Type'} (_49292 : _103840) (s : _103840 -> Prop) (h1 : term54 _103840 s) : term286 _103840 _49292 s.
Proof. exact (EQ_MP (@lem4326921 _103840 _49292 s) (@lem4326853 _103840 _49292 s h1)). Qed.
Lemma lem4326925 {_103840 : Type'} (_49292 : _103840) (s : _103840 -> Prop) (h1 : term54 _103840 s) : term286 _103840 _49292 s.
Proof. exact (@lem4326924 _103840 _49292 s h1). Qed.
Lemma lem4326926 {_103840 : Type'} (p1 : _103840) (s : _103840 -> Prop) (h1 : term54 _103840 s) : term286 _103840 p1 s.
Proof. exact (@lem4326925 _103840 p1 s h1). Qed.
Lemma lem4326929 {_103840 _103844 : Type'} (p1 : _103840) (p2 : _103844) (s : _103840 -> Prop) (t : _103844 -> Prop) (h1 : term54 _103840 s) (h2 : term231 _103840 _103844 p1 p2 s t) : False.
Proof. exact (@lem4326926 _103840 p1 s h1 (@lem4326916 _103840 _103844 p1 p2 s t h2)). Qed.
Lemma lem4326930 {_103840 _103844 : Type'} (p1 : _103840) (p2 : _103844) (s : _103840 -> Prop) (t : _103844 -> Prop) (h1 : term54 _103840 s) (h2 : term231 _103840 _103844 p1 p2 s t) : term287.
Proof. exact (fun h0 : ~ False => @lem4326929 _103840 _103844 p1 p2 s t h1 h2). Qed.
Lemma lem4326932 (p : Prop) : (term285 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4326933 : term287 = False.
Proof. exact (@lem4326932 False). Qed.
Lemma lem4326934 {_103840 _103844 : Type'} (p1 : _103840) (p2 : _103844) (s : _103840 -> Prop) (t : _103844 -> Prop) (h1 : term54 _103840 s) (h2 : term231 _103840 _103844 p1 p2 s t) : False.
Proof. exact (EQ_MP (@lem4326933) (@lem4326930 _103840 _103844 p1 p2 s t h1 h2)). Qed.
Lemma lem4326936 {_103840 _103844 : Type'} (p1 : _103840) (p2 : _103844) (s : _103840 -> Prop) (t : _103844 -> Prop) (h1 : term231 _103840 _103844 p1 p2 s t) : @IN _103844 p2 t.
Proof. exact (proj2 (@lem4326759 _103840 _103844 p1 p2 s t h1)). Qed.
Lemma lem4326937 {_103840 _103844 : Type'} (p1 : _103840) (p2 : _103844) (s : _103840 -> Prop) (t : _103844 -> Prop) (h1 : term231 _103840 _103844 p1 p2 s t) : term284 _103844 p2 t.
Proof. exact (fun h0 : term51 _103844 p2 t => @lem4326936 _103840 _103844 p1 p2 s t h1). Qed.
Lemma lem4326939 (p : Prop) : (term285 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4326940 {_103844 : Type'} (p2 : _103844) (t : _103844 -> Prop) : (term284 _103844 p2 t) = (@IN _103844 p2 t).
Proof. exact (@lem4326939 (@IN _103844 p2 t)). Qed.
Lemma lem4326941 {_103840 _103844 : Type'} (p1 : _103840) (p2 : _103844) (s : _103840 -> Prop) (t : _103844 -> Prop) (h1 : term231 _103840 _103844 p1 p2 s t) : @IN _103844 p2 t.
Proof. exact (EQ_MP (@lem4326940 _103844 p2 t) (@lem4326937 _103840 _103844 p1 p2 s t h1)). Qed.
Lemma lem4326944 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4326946 {_103844 : Type'} (_49293 : _103844) (t : _103844 -> Prop) : (term51 _103844 _49293 t) = (term286 _103844 _49293 t).
Proof. exact (@lem4326944 (@IN _103844 _49293 t)). Qed.
Lemma lem4326949 {_103844 : Type'} (_49293 : _103844) (t : _103844 -> Prop) (h1 : term54 _103844 t) : term286 _103844 _49293 t.
Proof. exact (EQ_MP (@lem4326946 _103844 _49293 t) (@lem4326859 _103844 _49293 t h1)). Qed.
Lemma lem4326950 {_103844 : Type'} (_49293 : _103844) (t : _103844 -> Prop) (h1 : term54 _103844 t) : term286 _103844 _49293 t.
Proof. exact (@lem4326949 _103844 _49293 t h1). Qed.
Lemma lem4326951 {_103844 : Type'} (p2 : _103844) (t : _103844 -> Prop) (h1 : term54 _103844 t) : term286 _103844 p2 t.
Proof. exact (@lem4326950 _103844 p2 t h1). Qed.
Lemma lem4326954 {_103840 _103844 : Type'} (p1 : _103840) (p2 : _103844) (s : _103840 -> Prop) (t : _103844 -> Prop) (h1 : term54 _103844 t) (h2 : term231 _103840 _103844 p1 p2 s t) : False.
Proof. exact (@lem4326951 _103844 p2 t h1 (@lem4326941 _103840 _103844 p1 p2 s t h2)). Qed.
Lemma lem4326955 {_103840 _103844 : Type'} (p1 : _103840) (p2 : _103844) (s : _103840 -> Prop) (t : _103844 -> Prop) (h1 : term54 _103844 t) (h2 : term231 _103840 _103844 p1 p2 s t) : term287.
Proof. exact (fun h0 : ~ False => @lem4326954 _103840 _103844 p1 p2 s t h1 h2). Qed.
Lemma lem4326957 (p : Prop) : (term285 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4326958 : term287 = False.
Proof. exact (@lem4326957 False). Qed.
Lemma lem4326959 {_103840 _103844 : Type'} (p1 : _103840) (p2 : _103844) (s : _103840 -> Prop) (t : _103844 -> Prop) (h1 : term54 _103844 t) (h2 : term231 _103840 _103844 p1 p2 s t) : False.
Proof. exact (EQ_MP (@lem4326958) (@lem4326955 _103840 _103844 p1 p2 s t h1 h2)). Qed.
Lemma lem4326960 {_103840 _103844 : Type'} (p1 : _103840) (p2 : _103844) (s : _103840 -> Prop) (t : _103844 -> Prop) (h1 : term54 _103844 t) (h2 : term231 _103840 _103844 p1 p2 s t) : (term54 _103844 t) = False.
Proof. exact (prop_ext (fun h3 : term54 _103844 t => @lem4326959 _103840 _103844 p1 p2 s t h1 h2) (fun h3 : False => @lem4326823 _103844 t h1)). Qed.
Lemma lem4326961 {_103840 _103844 : Type'} (p1 : _103840) (p2 : _103844) (s : _103840 -> Prop) (t : _103844 -> Prop) (h1 : term54 _103844 t) (h2 : term231 _103840 _103844 p1 p2 s t) : False.
Proof. exact (EQ_MP (@lem4326960 _103840 _103844 p1 p2 s t h1 h2) (@lem4326823 _103844 t h1)). Qed.
Lemma lem4326962 {_103840 _103844 : Type'} (p1 : _103840) (p2 : _103844) (s : _103840 -> Prop) (t : _103844 -> Prop) (h1 : term54 _103840 s) (h2 : term231 _103840 _103844 p1 p2 s t) : (term54 _103840 s) = False.
Proof. exact (prop_ext (fun h3 : term54 _103840 s => @lem4326934 _103840 _103844 p1 p2 s t h1 h2) (fun h3 : False => @lem4326808 _103840 s h1)). Qed.
Lemma lem4326963 {_103840 _103844 : Type'} (p1 : _103840) (p2 : _103844) (s : _103840 -> Prop) (t : _103844 -> Prop) (h1 : term54 _103840 s) (h2 : term231 _103840 _103844 p1 p2 s t) : False.
Proof. exact (EQ_MP (@lem4326962 _103840 _103844 p1 p2 s t h1 h2) (@lem4326808 _103840 s h1)). Qed.
Lemma lem4326964 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) (h1 : term54 _103844 t) (h2 : term204 _103840 _103844 p1 s p2 t) : (term54 _103844 t) = False.
Proof. exact (prop_ext (fun h3 : term54 _103844 t => @lem4326909 _103840 _103844 p1 s p2 t h1 h2) (fun h3 : False => @lem4326793 _103844 t h1)). Qed.
Lemma lem4326965 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) (h1 : term54 _103844 t) (h2 : term204 _103840 _103844 p1 s p2 t) : False.
Proof. exact (EQ_MP (@lem4326964 _103840 _103844 p1 s p2 t h1 h2) (@lem4326793 _103844 t h1)). Qed.
Lemma lem4326966 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) (h1 : term54 _103840 s) (h2 : term204 _103840 _103844 p1 s p2 t) : (term54 _103840 s) = False.
Proof. exact (prop_ext (fun h3 : term54 _103840 s => @lem4326884 _103840 _103844 p1 s p2 t h1 h2) (fun h3 : False => @lem4326778 _103840 s h1)). Qed.
Lemma lem4326967 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) (h1 : term54 _103840 s) (h2 : term204 _103840 _103844 p1 s p2 t) : False.
Proof. exact (EQ_MP (@lem4326966 _103840 _103844 p1 s p2 t h1 h2) (@lem4326778 _103840 s h1)). Qed.
Lemma lem4326968 {_103840 _103844 : Type'} (p1 : _103840) (p2 : _103844) (s : _103840 -> Prop) (t : _103844 -> Prop) (h1 : term231 _103840 _103844 p1 p2 s t) : False.
Proof. exact (or_elim (@lem4326758 _103840 _103844 p1 p2 s t h1) (fun h0 : term54 _103840 s => @lem4326963 _103840 _103844 p1 p2 s t h0 h1) (fun h0 : term54 _103844 t => @lem4326961 _103840 _103844 p1 p2 s t h0 h1)). Qed.
Lemma lem4326969 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (p2 : _103844) (t : _103844 -> Prop) (h1 : term204 _103840 _103844 p1 s p2 t) : False.
Proof. exact (or_elim (@lem4326753 _103840 _103844 p1 s p2 t h1) (fun h0 : term54 _103840 s => @lem4326967 _103840 _103844 p1 s p2 t h0 h1) (fun h0 : term54 _103844 t => @lem4326965 _103840 _103844 p1 s p2 t h0 h1)). Qed.
Lemma lem4326970 {_103840 _103844 : Type'} (p1 : _103840) (p2 : _103844) (s : _103840 -> Prop) (t : _103844 -> Prop) (h1 : term275 _103840 _103844 p1 p2 s t) : False.
Proof. exact (or_elim (@lem4326749 _103840 _103844 p1 p2 s t h1) (fun h0 : term204 _103840 _103844 p1 s p2 t => @lem4326969 _103840 _103844 p1 s p2 t h0) (fun h0 : term231 _103840 _103844 p1 p2 s t => @lem4326968 _103840 _103844 p1 p2 s t h0)). Qed.
Lemma lem4326971 {_103840 _103844 : Type'} (p1 : _103840) (p2 : _103844) (s : _103840 -> Prop) (t : _103844 -> Prop) (h1 : term275 _103840 _103844 p1 p2 s t) : (term275 _103840 _103844 p1 p2 s t) = False.
Proof. exact (prop_ext (fun h2 : term275 _103840 _103844 p1 p2 s t => @lem4326970 _103840 _103844 p1 p2 s t h1) (fun h2 : False => @lem4326749 _103840 _103844 p1 p2 s t h1)). Qed.
Lemma lem4326972 {_103840 _103844 : Type'} (p1 : _103840) (p2 : _103844) (s : _103840 -> Prop) (t : _103844 -> Prop) (h1 : term275 _103840 _103844 p1 p2 s t) : False.
Proof. exact (EQ_MP (@lem4326971 _103840 _103844 p1 p2 s t h1) (@lem4326749 _103840 _103844 p1 p2 s t h1)). Qed.
Lemma lem4326973 {_103840 _103844 : Type'} (p1 : _103840) (s : _103840 -> Prop) (t : _103844 -> Prop) (h1 : term278 _103840 _103844 p1 s t) : False.
Proof. exact (ex_elim (@lem4326666 _103840 _103844 p1 s t h1) (fun p2 : _103844 => fun h0 : term277 _103840 _103844 p1 s t p2 => @lem4326972 _103840 _103844 p1 p2 s t h0)). Qed.
Lemma lem4326974 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) (h1 : term76 _103840 _103844 s t) : False.
Proof. exact (ex_elim (@lem4326665 _103840 _103844 s t h1) (fun p1 : _103840 => fun h0 : term282 _103840 _103844 s t p1 => @lem4326973 _103840 _103844 p1 s t h0)). Qed.
Lemma lem4326975 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) (h1 : term76 _103840 _103844 s t) : (term76 _103840 _103844 s t) = False.
Proof. exact (prop_ext (fun h2 : term76 _103840 _103844 s t => @lem4326974 _103840 _103844 s t h1) (fun h2 : False => @lem4326084 _103840 _103844 s t h1)). Qed.
Lemma lem4326976 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) (h1 : term76 _103840 _103844 s t) : False.
Proof. exact (EQ_MP (@lem4326975 _103840 _103844 s t h1) (@lem4326084 _103840 _103844 s t h1)). Qed.
Lemma lem4326977 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : term75 _103840 _103844 s t.
Proof. exact (fun h0 : term76 _103840 _103844 s t => @lem4326976 _103840 _103844 s t h0). Qed.
Lemma lem4326978 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term46 _103840 _103844 s t) = (term58 _103840 _103844 s t).
Proof. exact (EQ_MP (@lem4326083 _103840 _103844 s t) (@lem4326977 _103840 _103844 s t)). Qed.
Lemma lem4326983 {_103840 _103844 : Type'} (s : _103840 -> Prop) : term62 _103840 _103844 s.
Proof. exact (fun t : _103844 -> Prop => @lem4326978 _103840 _103844 s t). Qed.
Lemma lem4326988 {_103840 _103844 : Type'} : term66 _103840 _103844.
Proof. exact (fun s : _103840 -> Prop => @lem4326983 _103840 _103844 s). Qed.
Lemma lem4326989 {_103840 _103844 : Type'} : term68 _103840 _103844.
Proof. exact (EQ_MP (@lem4326079 _103840 _103844) (@lem4326988 _103840 _103844)). Qed.
Lemma lem4326991 {_103840 _103844 : Type'} : term68 _103840 _103844.
Proof. exact (@lem4325959 _103840 _103844 (@lem4326989 _103840 _103844)). Qed.
Lemma lem4326992 {_103840 _103844 : Type'} (h1 : term69 _103840 _103844) : False.
Proof. exact (@lem4326991 _103840 _103844 (@lem4325943 _103840 _103844 h1)). Qed.
Lemma lem4326993 {_103840 _103844 : Type'} (h1 : term69 _103840 _103844) : (term69 _103840 _103844) = False.
Proof. exact (prop_ext (fun h2 : term69 _103840 _103844 => @lem4326992 _103840 _103844 h1) (fun h2 : False => @lem4325943 _103840 _103844 h1)). Qed.
Lemma lem4326994 {_103840 _103844 : Type'} (h1 : term69 _103840 _103844) : False.
Proof. exact (EQ_MP (@lem4326993 _103840 _103844 h1) (@lem4325943 _103840 _103844 h1)). Qed.
Lemma lem4326995 {_103840 _103844 : Type'} : term68 _103840 _103844.
Proof. exact (fun h0 : term69 _103840 _103844 => @lem4326994 _103840 _103844 h0). Qed.
Lemma lem4326996 {_103840 _103844 : Type'} : term66 _103840 _103844.
Proof. exact (EQ_MP (@lem4325942 _103840 _103844) (@lem4326995 _103840 _103844)). Qed.
Lemma lem4326997 {_103840 _103844 : Type'} : term65 _103840 _103844.
Proof. exact (EQ_MP (@lem4325938 _103840 _103844) (@lem4326996 _103840 _103844)). Qed.
