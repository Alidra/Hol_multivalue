Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SWAP_FORALL_THM_term_abbrevs.
Require Import thm32_spec.
Lemma lem4725 {A B : Type'} (P : type1413 A B) (h1 : term0 A B P) : term0 A B P.
Proof. exact (h1). Qed.
Lemma lem4726 {A B : Type'} (_48 : A) (P : type1413 A B) (h1 : term0 A B P) : term1 A B P _48.
Proof. exact (@lem4725 A B P h1 _48). Qed.
Lemma lem4727 {A B : Type'} (P : type1413 A B) (_48 : A) : (term1 A B P _48) = (term2 A B P _48).
Proof. exact (eq_refl (term1 A B P _48)). Qed.
Lemma lem4728 {A B : Type'} (_48 : A) (P : type1413 A B) (h1 : term0 A B P) : term2 A B P _48.
Proof. exact (EQ_MP (@lem4727 A B P _48) (@lem4726 A B _48 P h1)). Qed.
Lemma lem4729 {A B : Type'} (_48 : A) (_49 : B) (P : type1413 A B) (h1 : term0 A B P) : term3 A B P _48 _49.
Proof. exact (@lem4728 A B _48 P h1 _49). Qed.
Lemma lem4730 {A B : Type'} (P : type1413 A B) (_48 : A) (_49 : B) : (term3 A B P _48 _49) = (P _48 _49).
Proof. exact (eq_refl (term3 A B P _48 _49)). Qed.
Lemma lem4731 {A B : Type'} (_48 : A) (_49 : B) (P : type1413 A B) (h1 : term0 A B P) : P _48 _49.
Proof. exact (EQ_MP (@lem4730 A B P _48 _49) (@lem4729 A B _48 _49 P h1)). Qed.
Lemma lem4732 {A B : Type'} (x : A) (y : B) (P : type1413 A B) (h1 : term0 A B P) : P x y.
Proof. exact (@lem4731 A B x y P h1). Qed.
Lemma lem4740 {A B : Type'} (P : type1413 A B) (h1 : term0 A B P) : term0 A B P.
Proof. exact (@lem4725 A B P h1). Qed.
Lemma lem4741 {A B : Type'} (x : A) (y : B) (P : type1413 A B) (h1 : term0 A B P) : (term0 A B P) = (P x y).
Proof. exact (prop_ext (fun h2 : term0 A B P => @lem4732 A B x y P h1) (fun h2 : P x y => @lem4740 A B P h1)). Qed.
Lemma lem4742 {A B : Type'} (x : A) (y : B) (P : type1413 A B) (h1 : term0 A B P) : P x y.
Proof. exact (EQ_MP (@lem4741 A B x y P h1) (@lem4740 A B P h1)). Qed.
Lemma lem4747 {A B : Type'} (y : B) (P : type1413 A B) (h1 : term0 A B P) : term4 A B P y.
Proof. exact (fun x : A => @lem4742 A B x y P h1). Qed.
Lemma lem4752 {A B : Type'} (P : type1413 A B) (h1 : term0 A B P) : term5 A B P.
Proof. exact (fun y : B => @lem4747 A B y P h1). Qed.
Lemma lem4753 {A B : Type'} (P : type1413 A B) : term6 A B P.
Proof. exact (fun h0 : term0 A B P => @lem4752 A B P h0). Qed.
Lemma lem4754 {A B : Type'} (P : type1413 A B) (h1 : term5 A B P) : term5 A B P.
Proof. exact (h1). Qed.
Lemma lem4755 {A B : Type'} (_52 : B) (P : type1413 A B) (h1 : term5 A B P) : term7 A B P _52.
Proof. exact (@lem4754 A B P h1 _52). Qed.
Lemma lem4756 {A B : Type'} (P : type1413 A B) (_52 : B) : (term7 A B P _52) = (term4 A B P _52).
Proof. exact (eq_refl (term7 A B P _52)). Qed.
Lemma lem4757 {A B : Type'} (_52 : B) (P : type1413 A B) (h1 : term5 A B P) : term4 A B P _52.
Proof. exact (EQ_MP (@lem4756 A B P _52) (@lem4755 A B _52 P h1)). Qed.
Lemma lem4758 {A B : Type'} (_52 : B) (_53 : A) (P : type1413 A B) (h1 : term5 A B P) : term8 A B P _52 _53.
Proof. exact (@lem4757 A B _52 P h1 _53). Qed.
Lemma lem4759 {A B : Type'} (P : type1413 A B) (_53 : A) (_52 : B) : (term8 A B P _52 _53) = (P _53 _52).
Proof. exact (eq_refl (term8 A B P _52 _53)). Qed.
Lemma lem4760 {A B : Type'} (_53 : A) (_52 : B) (P : type1413 A B) (h1 : term5 A B P) : P _53 _52.
Proof. exact (EQ_MP (@lem4759 A B P _53 _52) (@lem4758 A B _52 _53 P h1)). Qed.
Lemma lem4761 {A B : Type'} (x : A) (y : B) (P : type1413 A B) (h1 : term5 A B P) : P x y.
Proof. exact (@lem4760 A B x y P h1). Qed.
Lemma lem4769 {A B : Type'} (P : type1413 A B) (h1 : term5 A B P) : term5 A B P.
Proof. exact (@lem4754 A B P h1). Qed.
Lemma lem4770 {A B : Type'} (x : A) (y : B) (P : type1413 A B) (h1 : term5 A B P) : (term5 A B P) = (P x y).
Proof. exact (prop_ext (fun h2 : term5 A B P => @lem4761 A B x y P h1) (fun h2 : P x y => @lem4769 A B P h1)). Qed.
Lemma lem4771 {A B : Type'} (x : A) (y : B) (P : type1413 A B) (h1 : term5 A B P) : P x y.
Proof. exact (EQ_MP (@lem4770 A B x y P h1) (@lem4769 A B P h1)). Qed.
Lemma lem4776 {A B : Type'} (x : A) (P : type1413 A B) (h1 : term5 A B P) : term2 A B P x.
Proof. exact (fun y : B => @lem4771 A B x y P h1). Qed.
Lemma lem4781 {A B : Type'} (P : type1413 A B) (h1 : term5 A B P) : term0 A B P.
Proof. exact (fun x : A => @lem4776 A B x P h1). Qed.
Lemma lem4782 {A B : Type'} (P : type1413 A B) : term9 A B P.
Proof. exact (fun h0 : term5 A B P => @lem4781 A B P h0). Qed.
Lemma lem4783 {A B : Type'} (P : type1413 A B) : term6 A B P.
Proof. exact (@lem4753 A B P). Qed.
Lemma lem4784 {A B : Type'} (P : type1413 A B) : term10 A B P.
Proof. exact (conj (@lem4783 A B P) (@lem4782 A B P)). Qed.
Lemma lem4785 {A B : Type'} (P : type1413 A B) : (term10 A B P) = ((term0 A B P) = (term5 A B P)).
Proof. exact (@lem32 (term0 A B P) (term5 A B P)). Qed.
Lemma lem4786 {A B : Type'} (P : type1413 A B) : (term0 A B P) = (term5 A B P).
Proof. exact (EQ_MP (@lem4785 A B P) (@lem4784 A B P)). Qed.
Lemma lem4791 {A B : Type'} : term11 A B.
Proof. exact (fun P : type1413 A B => @lem4786 A B P). Qed.
Lemma lem4792 {A B : Type'} : term11 A B.
Proof. exact (@lem4791 A B). Qed.
