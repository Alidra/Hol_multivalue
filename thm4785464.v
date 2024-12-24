Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4785464_term_abbrevs.
Require Import thm4784335_spec.
Require Import thm4785419_spec.
Lemma lem4785420 {A : Type'} : (term0 A) = (term1 A).
Proof. exact (eq_refl (term0 A)). Qed.
Lemma lem4785421 {A : Type'} : term1 A.
Proof. exact (EQ_MP (@lem4785420 A) (@lem4784335 A)). Qed.
Lemma lem4785422 {A : Type'} : term2 A.
Proof. exact (@lem4785421 A term3). Qed.
Lemma lem4785423 {A : Type'} : (term2 A) = (term4 A).
Proof. exact (eq_refl (term2 A)). Qed.
Lemma lem4785424 {A : Type'} : term4 A.
Proof. exact (EQ_MP (@lem4785423 A) (@lem4785422 A)). Qed.
Lemma lem4785425 {A : Type'} (h1 : (@set_of_list A) = (term5 A)) : (@set_of_list A) = (term5 A).
Proof. exact (h1). Qed.
Lemma lem4785426 {A : Type'} (h1 : (@set_of_list A) = (term5 A)) : (term5 A) = (@set_of_list A).
Proof. exact (SYM (@lem4785425 A h1)). Qed.
Lemma lem4785427 {A : Type'} (h1 : (term5 A) = (@set_of_list A)) : (term5 A) = (@set_of_list A).
Proof. exact (h1). Qed.
Lemma lem4785428 {A : Type'} (h1 : (term5 A) = (@set_of_list A)) : (@set_of_list A) = (term5 A).
Proof. exact (SYM (@lem4785427 A h1)). Qed.
Lemma lem4785429 {A : Type'} : ((@set_of_list A) = (term5 A)) = ((term5 A) = (@set_of_list A)).
Proof. exact (prop_ext (fun h1 : (@set_of_list A) = (term5 A) => @lem4785426 A h1) (fun h1 : (term5 A) = (@set_of_list A) => @lem4785428 A h1)). Qed.
Lemma lem4785432 {A : Type'} : (term5 A) = (@set_of_list A).
Proof. exact (EQ_MP (@lem4785429 A) (@lem4785419 A)). Qed.
Lemma lem4785433 {A : Type'} : (term5 A) = (@set_of_list A).
Proof. exact (@lem4785432 A). Qed.
Lemma lem4785434 {A : Type'} : (@nil A) = (@nil A).
Proof. exact (eq_refl (@nil A)). Qed.
Lemma lem4785435 {A : Type'} : (term6 A) = (@set_of_list A (@nil A)).
Proof. exact (MK_COMB (@lem4785433 A) (@lem4785434 A)). Qed.
Lemma lem4785436 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4785437 {A : Type'} : (term7 A) = (term8 A).
Proof. exact (MK_COMB (@lem4785436 A) (@lem4785435 A)). Qed.
Lemma lem4785438 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (eq_refl (@EMPTY A)). Qed.
Lemma lem4785439 {A : Type'} : ((term6 A) = (@EMPTY A)) = ((@set_of_list A (@nil A)) = (@EMPTY A)).
Proof. exact (MK_COMB (@lem4785437 A) (@lem4785438 A)). Qed.
Lemma lem4785440 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4785441 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (MK_COMB (@lem4785440) (@lem4785439 A)). Qed.
Lemma lem4785443 {A : Type'} : (term5 A) = (@set_of_list A).
Proof. exact (EQ_MP (@lem4785429 A) (@lem4785419 A)). Qed.
Lemma lem4785444 {A : Type'} : (term5 A) = (@set_of_list A).
Proof. exact (@lem4785443 A). Qed.
Lemma lem4785445 {A : Type'} (h : A) (t : list A) : (@cons A h t) = (@cons A h t).
Proof. exact (eq_refl (@cons A h t)). Qed.
Lemma lem4785446 {A : Type'} (h : A) (t : list A) : (term11 A h t) = (term12 A h t).
Proof. exact (MK_COMB (@lem4785444 A) (@lem4785445 A h t)). Qed.
Lemma lem4785447 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4785448 {A : Type'} (h : A) (t : list A) : (term13 A h t) = (term14 A h t).
Proof. exact (MK_COMB (@lem4785447 A) (@lem4785446 A h t)). Qed.
Lemma lem4785450 {A : Type'} : (term5 A) = (@set_of_list A).
Proof. exact (EQ_MP (@lem4785429 A) (@lem4785419 A)). Qed.
Lemma lem4785451 {A : Type'} : (term5 A) = (@set_of_list A).
Proof. exact (@lem4785450 A). Qed.
Lemma lem4785452 {A : Type'} (t : list A) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4785453 {A : Type'} (t : list A) : (term15 A t) = (@set_of_list A t).
Proof. exact (MK_COMB (@lem4785451 A) (@lem4785452 A t)). Qed.
Lemma lem4785454 {A : Type'} (h : A) : (@INSERT A h) = (@INSERT A h).
Proof. exact (eq_refl (@INSERT A h)). Qed.
Lemma lem4785455 {A : Type'} (h : A) (t : list A) : (term16 A h t) = (term17 A h t).
Proof. exact (MK_COMB (@lem4785454 A h) (@lem4785453 A t)). Qed.
Lemma lem4785456 {A : Type'} (h : A) (t : list A) : ((term11 A h t) = (term16 A h t)) = ((term12 A h t) = (term17 A h t)).
Proof. exact (MK_COMB (@lem4785448 A h t) (@lem4785455 A h t)). Qed.
Lemma lem4785457 {A : Type'} (h : A) : (term18 A h) = (term19 A h).
Proof. exact (fun_ext (fun t : list A => @lem4785456 A h t)). Qed.
Lemma lem4785458 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem4785459 {A : Type'} (h : A) : (term20 A h) = (term21 A h).
Proof. exact (MK_COMB (@lem4785458 A) (@lem4785457 A h)). Qed.
Lemma lem4785460 {A : Type'} : (term22 A) = (term23 A).
Proof. exact (fun_ext (fun h : A => @lem4785459 A h)). Qed.
Lemma lem4785461 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4785462 {A : Type'} : (term24 A) = (term25 A).
Proof. exact (MK_COMB (@lem4785461 A) (@lem4785460 A)). Qed.
Lemma lem4785463 {A : Type'} : (term4 A) = (term26 A).
Proof. exact (MK_COMB (@lem4785441 A) (@lem4785462 A)). Qed.
Lemma lem4785464 {A : Type'} : term26 A.
Proof. exact (EQ_MP (@lem4785463 A) (@lem4785424 A)). Qed.
