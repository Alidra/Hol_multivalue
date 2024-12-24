Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IN_UNIV_term_abbrevs.
Require Import IN_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm3187402_spec.
Require Import thm3187416_spec.
Lemma lem3204776 {A : Type'} (P : A -> Prop) : term0 A P.
Proof. exact (@lem3181151 A P). Qed.
Lemma lem3204777 {A : Type'} (P : A -> Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem3204778 {A : Type'} (P : A -> Prop) : term1 A P.
Proof. exact (EQ_MP (@lem3204777 A P) (@lem3204776 A P)). Qed.
Lemma lem3204779 {A : Type'} (P : A -> Prop) (x : A) : term2 A P x.
Proof. exact (@lem3204778 A P x). Qed.
Lemma lem3204780 {A : Type'} (P : A -> Prop) (x : A) : (term2 A P x) = ((@IN A x P) = (P x)).
Proof. exact (eq_refl (term2 A P x)). Qed.
Lemma lem3204787 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3204780 A P x) (@lem3204779 A P x)). Qed.
Lemma lem3204788 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3204787 A P x). Qed.
Lemma lem3204789 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = (@UNIV A x).
Proof. exact (@lem3204788 A (@UNIV A) x). Qed.
Lemma lem3204791 {A : Type'} : (@UNIV A) = (term3 A).
Proof. exact (TRANS (@lem3187402 A) (@lem3187416 A)). Qed.
Lemma lem3204792 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3204793 {A : Type'} (x : A) : (@UNIV A x) = (term4 A x).
Proof. exact (MK_COMB (@lem3204791 A) (@lem3204792 A x)). Qed.
Lemma lem3204795 {A B : Type'} (f : A -> B) (y : A) : (term5 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3204796 {A : Type'} (f : A -> Prop) (y : A) : (term6 A f y) = (f y).
Proof. exact (@lem3204795 A Prop f y). Qed.
Lemma lem3204797 {A : Type'} (x : A) : (term7 A x) = (term4 A x).
Proof. exact (@lem3204796 A (term3 A) x). Qed.
Lemma lem3204798 {A : Type'} (x : A) : (term4 A x) = True.
Proof. exact (eq_refl (term4 A x)). Qed.
Lemma lem3204799 {A : Type'} : (term8 A) = (term3 A).
Proof. exact (fun_ext (fun x : A => @lem3204798 A x)). Qed.
Lemma lem3204800 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3204801 {A : Type'} (x : A) : (term7 A x) = (term4 A x).
Proof. exact (MK_COMB (@lem3204799 A) (@lem3204800 A x)). Qed.
Lemma lem3204802 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3204803 {A : Type'} (x : A) : (term9 A x) = (term10 A x).
Proof. exact (MK_COMB (@lem3204802) (@lem3204801 A x)). Qed.
Lemma lem3204804 {A : Type'} (x : A) : (term4 A x) = True.
Proof. exact (eq_refl (term4 A x)). Qed.
Lemma lem3204805 {A : Type'} (x : A) : ((term7 A x) = (term4 A x)) = ((term4 A x) = True).
Proof. exact (MK_COMB (@lem3204803 A x) (@lem3204804 A x)). Qed.
Lemma lem3204806 {A : Type'} (x : A) : (term4 A x) = True.
Proof. exact (EQ_MP (@lem3204805 A x) (@lem3204797 A x)). Qed.
Lemma lem3204807 {A : Type'} (x : A) : (@UNIV A x) = True.
Proof. exact (TRANS (@lem3204793 A x) (@lem3204806 A x)). Qed.
Lemma lem3204808 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (TRANS (@lem3204789 A x) (@lem3204807 A x)). Qed.
Lemma lem3204809 {A : Type'} : (term11 A) = (term3 A).
Proof. exact (fun_ext (fun x : A => @lem3204808 A x)). Qed.
Lemma lem3204810 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3204811 {A : Type'} : (term12 A) = (term13 A).
Proof. exact (MK_COMB (@lem3204810 A) (@lem3204809 A)). Qed.
Lemma lem3204813 {A : Type'} (t : Prop) : (term14 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3204814 {A : Type'} (t : Prop) : (term14 A t) = t.
Proof. exact (@lem3204813 A t). Qed.
Lemma lem3204815 {A : Type'} : (term13 A) = True.
Proof. exact (@lem3204814 A True). Qed.
Lemma lem3204816 {A : Type'} : (term12 A) = True.
Proof. exact (TRANS (@lem3204811 A) (@lem3204815 A)). Qed.
Lemma lem3204817 {A : Type'} : True = (term12 A).
Proof. exact (SYM (@lem3204816 A)). Qed.
Lemma lem3204818 {A : Type'} : term12 A.
Proof. exact (EQ_MP (@lem3204817 A) (@lem0)). Qed.
