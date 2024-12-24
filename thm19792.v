Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm19792_term_abbrevs.
Require Import FUN_EQ_THM_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem19733 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem19734 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem19735 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem19734 A B f) (@lem19733 A B f)). Qed.
Lemma lem19736 {A B : Type'} (f : A -> B) (g : A -> B) : term2 A B f g.
Proof. exact (@lem19735 A B f g). Qed.
Lemma lem19737 {A B : Type'} (f : A -> B) (g : A -> B) : (term2 A B f g) = ((f = g) = (term3 A B f g)).
Proof. exact (eq_refl (term2 A B f g)). Qed.
Lemma lem19746 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term3 A B f g).
Proof. exact (EQ_MP (@lem19737 A B f g) (@lem19736 A B f g)). Qed.
Lemma lem19747 {_3571 _3575 : Type'} (f : _3575 -> _3571) (g : _3575 -> _3571) : (f = g) = (term4 _3571 _3575 f g).
Proof. exact (@lem19746 _3575 _3571 f g). Qed.
Lemma lem19748 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term5 _3571 _3575 t)) = (term6 _3571 _3575 s t).
Proof. exact (@lem19747 _3571 _3575 s (term5 _3571 _3575 t)). Qed.
Lemma lem19758 {A B : Type'} (f : A -> B) (y : A) : (term7 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem19759 {_3571 _3575 : Type'} (f : _3575 -> _3571) (y : _3575) : (term8 _3571 _3575 f y) = (f y).
Proof. exact (@lem19758 _3575 _3571 f y). Qed.
Lemma lem19760 {_3571 _3575 : Type'} (t : _3575 -> _3571) (x : _3575) : (term8 _3571 _3575 t x) = (t x).
Proof. exact (@lem19759 _3571 _3575 t x). Qed.
Lemma lem19761 {_3571 _3575 : Type'} (s : _3575 -> _3571) (x : _3575) : (term9 _3571 _3575 s x) = (term9 _3571 _3575 s x).
Proof. exact (eq_refl (term9 _3571 _3575 s x)). Qed.
Lemma lem19762 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) (x : _3575) : ((s x) = (term8 _3571 _3575 t x)) = ((s x) = (t x)).
Proof. exact (MK_COMB (@lem19761 _3571 _3575 s x) (@lem19760 _3571 _3575 t x)). Qed.
Lemma lem19767 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (term10 _3571 _3575 s t) = (term11 _3571 _3575 s t).
Proof. exact (fun_ext (fun x : _3575 => @lem19762 _3571 _3575 s t x)). Qed.
Lemma lem19768 {_3575 : Type'} : (@all _3575) = (@all _3575).
Proof. exact (eq_refl (@all _3575)). Qed.
Lemma lem19769 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (term6 _3571 _3575 s t) = (term4 _3571 _3575 s t).
Proof. exact (MK_COMB (@lem19768 _3575) (@lem19767 _3571 _3575 s t)). Qed.
Lemma lem19774 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term5 _3571 _3575 t)) = (term4 _3571 _3575 s t).
Proof. exact (TRANS (@lem19748 _3571 _3575 s t) (@lem19769 _3571 _3575 s t)). Qed.
Lemma lem19775 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem19776 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (term12 _3571 _3575 s t) = (term13 _3571 _3575 s t).
Proof. exact (MK_COMB (@lem19775) (@lem19774 _3571 _3575 s t)). Qed.
Lemma lem19785 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (term4 _3571 _3575 s t) = (term4 _3571 _3575 s t).
Proof. exact (eq_refl (term4 _3571 _3575 s t)). Qed.
Lemma lem19786 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : ((s = (term5 _3571 _3575 t)) = (term4 _3571 _3575 s t)) = ((term4 _3571 _3575 s t) = (term4 _3571 _3575 s t)).
Proof. exact (MK_COMB (@lem19776 _3571 _3575 s t) (@lem19785 _3571 _3575 s t)). Qed.
Lemma lem19788 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem19789 (x : Prop) : (x = x) = True.
Proof. exact (@lem19788 Prop x). Qed.
Lemma lem19790 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : ((term4 _3571 _3575 s t) = (term4 _3571 _3575 s t)) = True.
Proof. exact (@lem19789 (term4 _3571 _3575 s t)). Qed.
Lemma lem19791 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : ((s = (term5 _3571 _3575 t)) = (term4 _3571 _3575 s t)) = True.
Proof. exact (TRANS (@lem19786 _3571 _3575 s t) (@lem19790 _3571 _3575 s t)). Qed.
Lemma lem19792 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : True = ((s = (term5 _3571 _3575 t)) = (term4 _3571 _3575 s t)).
Proof. exact (SYM (@lem19791 _3571 _3575 s t)). Qed.
