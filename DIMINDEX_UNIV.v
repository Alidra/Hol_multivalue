Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIMINDEX_UNIV_term_abbrevs.
Require Import dimindex_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem7594655 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem7590231 A s). Qed.
Lemma lem7594656 {A : Type'} (s : A -> Prop) : (term0 A s) = ((@dimindex A s) = (term1 A)).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem7594665 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (term1 A).
Proof. exact (EQ_MP (@lem7594656 A s) (@lem7594655 A s)). Qed.
Lemma lem7594666 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (term1 A).
Proof. exact (@lem7594665 A s). Qed.
Lemma lem7594667 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7594668 {A : Type'} (s : A -> Prop) : (term2 A s) = (term3 A).
Proof. exact (MK_COMB (@lem7594667) (@lem7594666 A s)). Qed.
Lemma lem7594670 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (term1 A).
Proof. exact (EQ_MP (@lem7594656 A s) (@lem7594655 A s)). Qed.
Lemma lem7594671 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (term1 A).
Proof. exact (@lem7594670 A s). Qed.
Lemma lem7594672 {A : Type'} : (@dimindex A (@UNIV A)) = (term1 A).
Proof. exact (@lem7594671 A (@UNIV A)). Qed.
Lemma lem7594673 {A : Type'} (s : A -> Prop) : ((@dimindex A s) = (@dimindex A (@UNIV A))) = ((term1 A) = (term1 A)).
Proof. exact (MK_COMB (@lem7594668 A s) (@lem7594672 A)). Qed.
Lemma lem7594675 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7594676 (x : nat) : (x = x) = True.
Proof. exact (@lem7594675 nat x). Qed.
Lemma lem7594677 {A : Type'} : ((term1 A) = (term1 A)) = True.
Proof. exact (@lem7594676 (term1 A)). Qed.
Lemma lem7594678 {A : Type'} (s : A -> Prop) : ((@dimindex A s) = (@dimindex A (@UNIV A))) = True.
Proof. exact (TRANS (@lem7594673 A s) (@lem7594677 A)). Qed.
Lemma lem7594679 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7594678 A s)). Qed.
Lemma lem7594680 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7594681 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (MK_COMB (@lem7594680 A) (@lem7594679 A)). Qed.
Lemma lem7594683 {A : Type'} (t : Prop) : (term8 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7594684 {A : Type'} (t : Prop) : (term9 A t) = t.
Proof. exact (@lem7594683 (A -> Prop) t). Qed.
Lemma lem7594685 {A : Type'} : (term7 A) = True.
Proof. exact (@lem7594684 A True). Qed.
Lemma lem7594686 {A : Type'} : (term6 A) = True.
Proof. exact (TRANS (@lem7594681 A) (@lem7594685 A)). Qed.
Lemma lem7594687 {A : Type'} : True = (term6 A).
Proof. exact (SYM (@lem7594686 A)). Qed.
Lemma lem7594688 {A : Type'} : term6 A.
Proof. exact (EQ_MP (@lem7594687 A) (@lem0)). Qed.
