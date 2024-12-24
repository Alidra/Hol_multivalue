Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SWAP_EXISTS_THM_term_abbrevs.
Require Import thm32_spec.
Lemma lem4817 {A B : Type'} (P : type1413 A B) (h1 : term0 A B P) : term0 A B P.
Proof. exact (h1). Qed.
Lemma lem4818 {A B : Type'} (P : type1413 A B) (x : A) (h1 : term1 A B P x) : term1 A B P x.
Proof. exact (h1). Qed.
Lemma lem4819 {A B : Type'} (P : type1413 A B) (x : A) (y : B) (h1 : P x y) : P x y.
Proof. exact (h1). Qed.
Lemma lem4820 {A B : Type'} (P : type1413 A B) (x : A) (y : B) (h1 : P x y) : P x y.
Proof. exact (@lem4819 A B P x y h1). Qed.
Lemma lem4821 {A B : Type'} (P : type1413 A B) (x : A) (y : B) (h1 : P x y) : term2 A B P y.
Proof. exact (ex_intro (term3 A B P y) x (@lem4820 A B P x y h1)). Qed.
Lemma lem4822 {A B : Type'} (P : type1413 A B) (x : A) (y : B) (h1 : P x y) : term4 A B P.
Proof. exact (ex_intro (term5 A B P) y (@lem4821 A B P x y h1)). Qed.
Lemma lem4823 {A B : Type'} (P : type1413 A B) (x : A) (h1 : term1 A B P x) : term1 A B P x.
Proof. exact (@lem4818 A B P x h1). Qed.
Lemma lem4824 {A B : Type'} (P : type1413 A B) (x : A) (h1 : term1 A B P x) : term4 A B P.
Proof. exact (ex_elim (@lem4823 A B P x h1) (fun y : B => fun h0 : term6 A B P x y => @lem4822 A B P x y h0)). Qed.
Lemma lem4825 {A B : Type'} (P : type1413 A B) (h1 : term0 A B P) : term0 A B P.
Proof. exact (@lem4817 A B P h1). Qed.
Lemma lem4826 {A B : Type'} (P : type1413 A B) (h1 : term0 A B P) : term4 A B P.
Proof. exact (ex_elim (@lem4825 A B P h1) (fun x : A => fun h0 : term7 A B P x => @lem4824 A B P x h0)). Qed.
Lemma lem4827 {A B : Type'} (P : type1413 A B) : term8 A B P.
Proof. exact (fun h0 : term0 A B P => @lem4826 A B P h0). Qed.
Lemma lem4828 {A B : Type'} (P : type1413 A B) (h1 : term4 A B P) : term4 A B P.
Proof. exact (h1). Qed.
Lemma lem4829 {A B : Type'} (P : type1413 A B) (y : B) (h1 : term2 A B P y) : term2 A B P y.
Proof. exact (h1). Qed.
Lemma lem4830 {A B : Type'} (P : type1413 A B) (x : A) (y : B) (h1 : P x y) : P x y.
Proof. exact (h1). Qed.
Lemma lem4831 {A B : Type'} (P : type1413 A B) (x : A) (y : B) (h1 : P x y) : P x y.
Proof. exact (@lem4830 A B P x y h1). Qed.
Lemma lem4832 {A B : Type'} (P : type1413 A B) (x : A) (y : B) (h1 : P x y) : term1 A B P x.
Proof. exact (ex_intro (term6 A B P x) y (@lem4831 A B P x y h1)). Qed.
Lemma lem4833 {A B : Type'} (P : type1413 A B) (x : A) (y : B) (h1 : P x y) : term0 A B P.
Proof. exact (ex_intro (term7 A B P) x (@lem4832 A B P x y h1)). Qed.
Lemma lem4834 {A B : Type'} (P : type1413 A B) (y : B) (h1 : term2 A B P y) : term2 A B P y.
Proof. exact (@lem4829 A B P y h1). Qed.
Lemma lem4835 {A B : Type'} (P : type1413 A B) (y : B) (h1 : term2 A B P y) : term0 A B P.
Proof. exact (ex_elim (@lem4834 A B P y h1) (fun x : A => fun h0 : term3 A B P y x => @lem4833 A B P x y h0)). Qed.
Lemma lem4836 {A B : Type'} (P : type1413 A B) (h1 : term4 A B P) : term4 A B P.
Proof. exact (@lem4828 A B P h1). Qed.
Lemma lem4837 {A B : Type'} (P : type1413 A B) (h1 : term4 A B P) : term0 A B P.
Proof. exact (ex_elim (@lem4836 A B P h1) (fun y : B => fun h0 : term5 A B P y => @lem4835 A B P y h0)). Qed.
Lemma lem4838 {A B : Type'} (P : type1413 A B) : term9 A B P.
Proof. exact (fun h0 : term4 A B P => @lem4837 A B P h0). Qed.
Lemma lem4839 {A B : Type'} (P : type1413 A B) : term8 A B P.
Proof. exact (@lem4827 A B P). Qed.
Lemma lem4840 {A B : Type'} (P : type1413 A B) : term10 A B P.
Proof. exact (conj (@lem4839 A B P) (@lem4838 A B P)). Qed.
Lemma lem4841 {A B : Type'} (P : type1413 A B) : (term10 A B P) = ((term0 A B P) = (term4 A B P)).
Proof. exact (@lem32 (term0 A B P) (term4 A B P)). Qed.
Lemma lem4842 {A B : Type'} (P : type1413 A B) : (term0 A B P) = (term4 A B P).
Proof. exact (EQ_MP (@lem4841 A B P) (@lem4840 A B P)). Qed.
Lemma lem4847 {A B : Type'} : term11 A B.
Proof. exact (fun P : type1413 A B => @lem4842 A B P). Qed.
Lemma lem4848 {A B : Type'} : term11 A B.
Proof. exact (@lem4847 A B). Qed.
