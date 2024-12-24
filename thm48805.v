Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm48805_term_abbrevs.
Require Import GEQ_DEF_spec.
Lemma lem48790 {A : Type'} (a : A) (b : A) (h1 : (@GEQ A a b) = (a = b)) : (@GEQ A a b) = (a = b).
Proof. exact (h1). Qed.
Lemma lem48791 {A : Type'} (a : A) (b : A) (h1 : (@GEQ A a b) = (a = b)) : (a = b) = (@GEQ A a b).
Proof. exact (SYM (@lem48790 A a b h1)). Qed.
Lemma lem48792 {A : Type'} (a : A) (b : A) (h1 : (a = b) = (@GEQ A a b)) : (a = b) = (@GEQ A a b).
Proof. exact (h1). Qed.
Lemma lem48793 {A : Type'} (a : A) (b : A) (h1 : (a = b) = (@GEQ A a b)) : (@GEQ A a b) = (a = b).
Proof. exact (SYM (@lem48792 A a b h1)). Qed.
Lemma lem48794 {A : Type'} (a : A) (b : A) : ((@GEQ A a b) = (a = b)) = ((a = b) = (@GEQ A a b)).
Proof. exact (prop_ext (fun h1 : (@GEQ A a b) = (a = b) => @lem48791 A a b h1) (fun h1 : (a = b) = (@GEQ A a b) => @lem48793 A a b h1)). Qed.
Lemma lem48795 {A : Type'} (a : A) : (term0 A a) = (term1 A a).
Proof. exact (fun_ext (fun b : A => @lem48794 A a b)). Qed.
Lemma lem48796 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem48797 {A : Type'} (a : A) : (term2 A a) = (term3 A a).
Proof. exact (MK_COMB (@lem48796 A) (@lem48795 A a)). Qed.
Lemma lem48798 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (fun_ext (fun a : A => @lem48797 A a)). Qed.
Lemma lem48799 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem48800 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (MK_COMB (@lem48799 A) (@lem48798 A)). Qed.
Lemma lem48801 {A : Type'} : term7 A.
Proof. exact (EQ_MP (@lem48800 A) (@lem44156 A)). Qed.
Lemma lem48802 {A : Type'} (a : A) : term8 A a.
Proof. exact (@lem48801 A a). Qed.
Lemma lem48803 {A : Type'} (a : A) : (term8 A a) = (term3 A a).
Proof. exact (eq_refl (term8 A a)). Qed.
Lemma lem48804 {A : Type'} (a : A) : term3 A a.
Proof. exact (EQ_MP (@lem48803 A a) (@lem48802 A a)). Qed.
Lemma lem48805 {A : Type'} (a : A) (b : A) : term9 A a b.
Proof. exact (@lem48804 A a b). Qed.
