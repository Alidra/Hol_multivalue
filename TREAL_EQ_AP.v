Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_EQ_AP_term_abbrevs.
Require Import TREAL_EQ_REFL_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem1326779 (x : prod hreal hreal) : term0 x.
Proof. exact (@lem1326193 x). Qed.
Lemma lem1326780 (x : prod hreal hreal) : (term0 x) = (treal_eq x x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1326781 (x : prod hreal hreal) : treal_eq x x.
Proof. exact (EQ_MP (@lem1326780 x) (@lem1326779 x)). Qed.
Lemma lem1326782 (x : prod hreal hreal) : (treal_eq x x) = ((treal_eq x x) = True).
Proof. exact (@lem7 (treal_eq x x)). Qed.
Lemma lem1326797 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term1 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1326798 (p : Prop) (q : Prop) (p' : Prop) : term2 p q p'.
Proof. exact (fun q' : Prop => @lem1326797 p q p' q'). Qed.
Lemma lem1326799 (p : Prop) (q : Prop) : term3 p q.
Proof. exact (fun p' : Prop => @lem1326798 p q p'). Qed.
Lemma lem1326800 (x : prod hreal hreal) (y : prod hreal hreal) : term4 x y.
Proof. exact (@lem1326799 (x = y) (treal_eq x y)). Qed.
Lemma lem1326801 (x : prod hreal hreal) (y : prod hreal hreal) (p' : Prop) : term5 x y p'.
Proof. exact (@lem1326800 x y p'). Qed.
Lemma lem1326802 (x : prod hreal hreal) (y : prod hreal hreal) (p' : Prop) : (term5 x y p') = (term6 x y p').
Proof. exact (eq_refl (term5 x y p')). Qed.
Lemma lem1326803 (x : prod hreal hreal) (y : prod hreal hreal) (p' : Prop) : term6 x y p'.
Proof. exact (EQ_MP (@lem1326802 x y p') (@lem1326801 x y p')). Qed.
Lemma lem1326804 (x : prod hreal hreal) (y : prod hreal hreal) (p' : Prop) (q' : Prop) : term7 x y p' q'.
Proof. exact (@lem1326803 x y p' q'). Qed.
Lemma lem1326805 (x : prod hreal hreal) (y : prod hreal hreal) (p' : Prop) (q' : Prop) : (term7 x y p' q') = (term8 x y p' q').
Proof. exact (eq_refl (term7 x y p' q')). Qed.
Lemma lem1326806 (x : prod hreal hreal) (y : prod hreal hreal) (p' : Prop) (q' : Prop) : term8 x y p' q'.
Proof. exact (EQ_MP (@lem1326805 x y p' q') (@lem1326804 x y p' q')). Qed.
Lemma lem1326809 (x : prod hreal hreal) (y : prod hreal hreal) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1326810 (x : prod hreal hreal) (y : prod hreal hreal) (q' : Prop) : term9 x y q'.
Proof. exact (@lem1326806 x y (x = y) q'). Qed.
Lemma lem1326811 (x : prod hreal hreal) (y : prod hreal hreal) (q' : Prop) : term10 x y q'.
Proof. exact (@lem1326810 x y q' (@lem1326809 x y)). Qed.
Lemma lem1326816 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1326817 : treal_eq = treal_eq.
Proof. exact (eq_refl treal_eq). Qed.
Lemma lem1326818 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : x = y) : (treal_eq x) = (treal_eq y).
Proof. exact (MK_COMB (@lem1326817) (@lem1326816 x y h1)). Qed.
Lemma lem1326819 (y : prod hreal hreal) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1326820 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : x = y) : (treal_eq x y) = (treal_eq y y).
Proof. exact (MK_COMB (@lem1326818 x y h1) (@lem1326819 y)). Qed.
Lemma lem1326822 (x : prod hreal hreal) : (treal_eq x x) = True.
Proof. exact (EQ_MP (@lem1326782 x) (@lem1326781 x)). Qed.
Lemma lem1326823 (y : prod hreal hreal) : (treal_eq y y) = True.
Proof. exact (@lem1326822 y). Qed.
Lemma lem1326824 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : x = y) : (treal_eq x y) = True.
Proof. exact (TRANS (@lem1326820 x y h1) (@lem1326823 y)). Qed.
Lemma lem1326825 (x : prod hreal hreal) (y : prod hreal hreal) : term11 x y.
Proof. exact (fun h0 : x = y => @lem1326824 x y h0). Qed.
Lemma lem1326826 (x : prod hreal hreal) (y : prod hreal hreal) : term12 x y.
Proof. exact (@lem1326811 x y True). Qed.
Lemma lem1326827 (x : prod hreal hreal) (y : prod hreal hreal) : (term13 x y) = (term14 x y).
Proof. exact (@lem1326826 x y (@lem1326825 x y)). Qed.
Lemma lem1326831 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1326832 (x : prod hreal hreal) (y : prod hreal hreal) : (term14 x y) = True.
Proof. exact (@lem1326831 (x = y)). Qed.
Lemma lem1326833 (x : prod hreal hreal) (y : prod hreal hreal) : (term13 x y) = True.
Proof. exact (TRANS (@lem1326827 x y) (@lem1326832 x y)). Qed.
Lemma lem1326834 (x : prod hreal hreal) : (term15 x) = term16.
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1326833 x y)). Qed.
Lemma lem1326835 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1326836 (x : prod hreal hreal) : (term17 x) = term18.
Proof. exact (MK_COMB (@lem1326835) (@lem1326834 x)). Qed.
Lemma lem1326838 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1326839 (t : Prop) : (term20 t) = t.
Proof. exact (@lem1326838 (prod hreal hreal) t). Qed.
Lemma lem1326840 : term18 = True.
Proof. exact (@lem1326839 True). Qed.
Lemma lem1326841 (x : prod hreal hreal) : (term17 x) = True.
Proof. exact (TRANS (@lem1326836 x) (@lem1326840)). Qed.
Lemma lem1326842 : term21 = term16.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1326841 x)). Qed.
Lemma lem1326843 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1326844 : term22 = term18.
Proof. exact (MK_COMB (@lem1326843) (@lem1326842)). Qed.
Lemma lem1326846 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1326847 (t : Prop) : (term20 t) = t.
Proof. exact (@lem1326846 (prod hreal hreal) t). Qed.
Lemma lem1326848 : term18 = True.
Proof. exact (@lem1326847 True). Qed.
Lemma lem1326849 : term22 = True.
Proof. exact (TRANS (@lem1326844) (@lem1326848)). Qed.
Lemma lem1326850 : True = term22.
Proof. exact (SYM (@lem1326849)). Qed.
Lemma lem1326851 : term22.
Proof. exact (EQ_MP (@lem1326850) (@lem0)). Qed.
