Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNION_IDEMPOT_term_abbrevs.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1834_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3232765 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3232766 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3232765 A s t). Qed.
Lemma lem3232767 {A : Type'} (s : A -> Prop) : ((@UNION A s s) = s) = (term1 A s).
Proof. exact (@lem3232766 A (@UNION A s s) s). Qed.
Lemma lem3232776 {A : Type'} : (term2 A) = (term3 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3232767 A s)). Qed.
Lemma lem3232777 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3232778 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (MK_COMB (@lem3232777 A) (@lem3232776 A)). Qed.
Lemma lem3232783 {A : Type'} : (term5 A) = (term4 A).
Proof. exact (SYM (@lem3232778 A)). Qed.
Lemma lem3232795 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term6 A x s t) = (term7 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3232796 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term6 A x s t) = (term7 A s x t).
Proof. exact (@lem3232795 A s x t). Qed.
Lemma lem3232797 {A : Type'} (x : A) (s : A -> Prop) : (term8 A x s) = (term9 A x s).
Proof. exact (@lem3232796 A s x s). Qed.
Lemma lem3232799 (t : Prop) : (t \/ t) = t.
Proof. exact (proj2 (@lem1834 t)). Qed.
Lemma lem3232800 {A : Type'} (x : A) (s : A -> Prop) : (term9 A x s) = (@IN A x s).
Proof. exact (@lem3232799 (@IN A x s)). Qed.
Lemma lem3232802 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3232803 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3232802 A P x). Qed.
Lemma lem3232804 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3232803 A s x). Qed.
Lemma lem3232805 {A : Type'} (s : A -> Prop) (x : A) : (term9 A x s) = (s x).
Proof. exact (TRANS (@lem3232800 A x s) (@lem3232804 A s x)). Qed.
Lemma lem3232806 {A : Type'} (s : A -> Prop) (x : A) : (term8 A x s) = (s x).
Proof. exact (TRANS (@lem3232797 A x s) (@lem3232805 A s x)). Qed.
Lemma lem3232807 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3232808 {A : Type'} (s : A -> Prop) (x : A) : (term10 A x s) = (term11 A s x).
Proof. exact (MK_COMB (@lem3232807) (@lem3232806 A s x)). Qed.
Lemma lem3232810 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3232811 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3232810 A P x). Qed.
Lemma lem3232812 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3232811 A s x). Qed.
Lemma lem3232813 {A : Type'} (s : A -> Prop) (x : A) : ((term8 A x s) = (@IN A x s)) = ((s x) = (s x)).
Proof. exact (MK_COMB (@lem3232808 A s x) (@lem3232812 A s x)). Qed.
Lemma lem3232815 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3232816 (x : Prop) : (x = x) = True.
Proof. exact (@lem3232815 Prop x). Qed.
Lemma lem3232817 {A : Type'} (s : A -> Prop) (x : A) : ((s x) = (s x)) = True.
Proof. exact (@lem3232816 (s x)). Qed.
Lemma lem3232818 {A : Type'} (x : A) (s : A -> Prop) : ((term8 A x s) = (@IN A x s)) = True.
Proof. exact (TRANS (@lem3232813 A s x) (@lem3232817 A s x)). Qed.
Lemma lem3232819 {A : Type'} (s : A -> Prop) : (term12 A s) = (term13 A).
Proof. exact (fun_ext (fun x : A => @lem3232818 A x s)). Qed.
Lemma lem3232820 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3232821 {A : Type'} (s : A -> Prop) : (term1 A s) = (term14 A).
Proof. exact (MK_COMB (@lem3232820 A) (@lem3232819 A s)). Qed.
Lemma lem3232823 {A : Type'} (t : Prop) : (term15 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3232824 {A : Type'} (t : Prop) : (term15 A t) = t.
Proof. exact (@lem3232823 A t). Qed.
Lemma lem3232825 {A : Type'} : (term14 A) = True.
Proof. exact (@lem3232824 A True). Qed.
Lemma lem3232826 {A : Type'} (s : A -> Prop) : (term1 A s) = True.
Proof. exact (TRANS (@lem3232821 A s) (@lem3232825 A)). Qed.
Lemma lem3232827 {A : Type'} : (term3 A) = (term16 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3232826 A s)). Qed.
Lemma lem3232828 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3232829 {A : Type'} : (term5 A) = (term17 A).
Proof. exact (MK_COMB (@lem3232828 A) (@lem3232827 A)). Qed.
Lemma lem3232831 {A : Type'} (t : Prop) : (term15 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3232832 {A : Type'} (t : Prop) : (term18 A t) = t.
Proof. exact (@lem3232831 (A -> Prop) t). Qed.
Lemma lem3232833 {A : Type'} : (term17 A) = True.
Proof. exact (@lem3232832 A True). Qed.
Lemma lem3232834 {A : Type'} : (term5 A) = True.
Proof. exact (TRANS (@lem3232829 A) (@lem3232833 A)). Qed.
Lemma lem3232835 {A : Type'} : True = (term5 A).
Proof. exact (SYM (@lem3232834 A)). Qed.
Lemma lem3232836 {A : Type'} : term5 A.
Proof. exact (EQ_MP (@lem3232835 A) (@lem0)). Qed.
Lemma lem3232837 {A : Type'} : term4 A.
Proof. exact (EQ_MP (@lem3232783 A) (@lem3232836 A)). Qed.
