Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import dest_int_rep_term_abbrevs.
Require Import is_int_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm2267740_spec.
Require Import thm2267741_spec.
Require Import thm2267744_spec.
Require Import thm2267745_spec.
Lemma lem2267747 (x : real) (h1 : (integer x) = (term0 x)) : (integer x) = (term0 x).
Proof. exact (h1). Qed.
Lemma lem2267748 (x : real) (h1 : (integer x) = (term0 x)) : (term0 x) = (integer x).
Proof. exact (SYM (@lem2267747 x h1)). Qed.
Lemma lem2267749 (x : real) (h1 : (term0 x) = (integer x)) : (term0 x) = (integer x).
Proof. exact (h1). Qed.
Lemma lem2267750 (x : real) (h1 : (term0 x) = (integer x)) : (integer x) = (term0 x).
Proof. exact (SYM (@lem2267749 x h1)). Qed.
Lemma lem2267751 (x : real) : ((integer x) = (term0 x)) = ((term0 x) = (integer x)).
Proof. exact (prop_ext (fun h1 : (integer x) = (term0 x) => @lem2267748 x h1) (fun h1 : (term0 x) = (integer x) => @lem2267750 x h1)). Qed.
Lemma lem2267758 (x : real) : (term0 x) = (integer x).
Proof. exact (EQ_MP (@lem2267751 x) (@lem2267614 x)). Qed.
Lemma lem2267759 (i : int) : (term1 i) = (term2 i).
Proof. exact (@lem2267758 (real_of_int i)). Qed.
Lemma lem2267761 (r : real) : (integer r) = ((term3 r) = r).
Proof. exact (EQ_MP (@lem2267741 r) (@lem2267740 r)). Qed.
Lemma lem2267762 (i : int) : (term2 i) = ((term4 i) = (real_of_int i)).
Proof. exact (@lem2267761 (real_of_int i)). Qed.
Lemma lem2267765 (i : int) : (term1 i) = ((term4 i) = (real_of_int i)).
Proof. exact (TRANS (@lem2267759 i) (@lem2267762 i)). Qed.
Lemma lem2267767 (a : int) : (term5 a) = a.
Proof. exact (EQ_MP (@lem2267745 a) (@lem2267744 a)). Qed.
Lemma lem2267768 (i : int) : (term5 i) = i.
Proof. exact (@lem2267767 i). Qed.
Lemma lem2267769 : real_of_int = real_of_int.
Proof. exact (eq_refl real_of_int). Qed.
Lemma lem2267770 (i : int) : (term4 i) = (real_of_int i).
Proof. exact (MK_COMB (@lem2267769) (@lem2267768 i)). Qed.
Lemma lem2267771 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2267772 (i : int) : (term6 i) = (term7 i).
Proof. exact (MK_COMB (@lem2267771) (@lem2267770 i)). Qed.
Lemma lem2267773 (i : int) : (real_of_int i) = (real_of_int i).
Proof. exact (eq_refl (real_of_int i)). Qed.
Lemma lem2267774 (i : int) : ((term4 i) = (real_of_int i)) = ((real_of_int i) = (real_of_int i)).
Proof. exact (MK_COMB (@lem2267772 i) (@lem2267773 i)). Qed.
Lemma lem2267776 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2267777 (x : real) : (x = x) = True.
Proof. exact (@lem2267776 real x). Qed.
Lemma lem2267778 (i : int) : ((real_of_int i) = (real_of_int i)) = True.
Proof. exact (@lem2267777 (real_of_int i)). Qed.
Lemma lem2267779 (i : int) : ((term4 i) = (real_of_int i)) = True.
Proof. exact (TRANS (@lem2267774 i) (@lem2267778 i)). Qed.
Lemma lem2267780 (i : int) : (term1 i) = True.
Proof. exact (TRANS (@lem2267765 i) (@lem2267779 i)). Qed.
Lemma lem2267781 : term8 = term9.
Proof. exact (fun_ext (fun i : int => @lem2267780 i)). Qed.
Lemma lem2267782 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2267783 : term10 = term11.
Proof. exact (MK_COMB (@lem2267782) (@lem2267781)). Qed.
Lemma lem2267785 {A : Type'} (t : Prop) : (term12 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2267786 (t : Prop) : (term13 t) = t.
Proof. exact (@lem2267785 int t). Qed.
Lemma lem2267787 : term11 = True.
Proof. exact (@lem2267786 True). Qed.
Lemma lem2267788 : term10 = True.
Proof. exact (TRANS (@lem2267783) (@lem2267787)). Qed.
Lemma lem2267789 : True = term10.
Proof. exact (SYM (@lem2267788)). Qed.
Lemma lem2267790 : term10.
Proof. exact (EQ_MP (@lem2267789) (@lem0)). Qed.
