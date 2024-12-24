Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_UNION_OF_EMPTY_term_abbrevs.
Require Import FINITE_EMPTY_spec.
Require Import UNION_OF_EMPTY_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem4876620 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = ((@FINITE _92140 (@EMPTY _92140)) = True).
Proof. exact (@lem7 (@FINITE _92140 (@EMPTY _92140))). Qed.
Lemma lem4876622 {A : Type'} (P : type180 A) : term0 A P.
Proof. exact (@lem4851738 A P). Qed.
Lemma lem4876623 {A : Type'} (P : type180 A) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem4876624 {A : Type'} (P : type180 A) : term1 A P.
Proof. exact (EQ_MP (@lem4876623 A P) (@lem4876622 A P)). Qed.
Lemma lem4876625 {A : Type'} (P : type180 A) (Q : type686 A) : term2 A P Q.
Proof. exact (@lem4876624 A P Q). Qed.
Lemma lem4876626 {A : Type'} (P : type180 A) (Q : type686 A) : (term2 A P Q) = (term3 A P Q).
Proof. exact (eq_refl (term2 A P Q)). Qed.
Lemma lem4876627 {A : Type'} (P : type180 A) (Q : type686 A) : term3 A P Q.
Proof. exact (EQ_MP (@lem4876626 A P Q) (@lem4876625 A P Q)). Qed.
Lemma lem4876628 {A : Type'} (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : P (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem4876629 {A : Type'} (Q : type686 A) (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : @UNION_OF A P Q (@EMPTY A).
Proof. exact (@lem4876627 A P Q (@lem4876628 A P h1)). Qed.
Lemma lem4876630 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q (@EMPTY A)) = ((@UNION_OF A P Q (@EMPTY A)) = True).
Proof. exact (@lem7 (@UNION_OF A P Q (@EMPTY A))). Qed.
Lemma lem4876631 {A : Type'} (Q : type686 A) (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : (@UNION_OF A P Q (@EMPTY A)) = True.
Proof. exact (EQ_MP (@lem4876630 A P Q) (@lem4876629 A Q P h1)). Qed.
Lemma lem4876642 {A : Type'} (P : type180 A) (Q : type686 A) : term4 A P Q.
Proof. exact (fun h0 : P (@EMPTY (A -> Prop)) => @lem4876631 A Q P h0). Qed.
Lemma lem4876643 {A : Type'} (P : type180 A) (Q : type686 A) : term4 A P Q.
Proof. exact (@lem4876642 A P Q). Qed.
Lemma lem4876644 {A : Type'} (P : type686 A) : term5 A P.
Proof. exact (@lem4876643 A (@FINITE (A -> Prop)) P). Qed.
Lemma lem4876646 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem4876620 _92140) (@lem3596285 _92140)). Qed.
Lemma lem4876647 {A : Type'} : (@FINITE (A -> Prop) (@EMPTY (A -> Prop))) = True.
Proof. exact (@lem4876646 (A -> Prop)). Qed.
Lemma lem4876648 {A : Type'} : True = (@FINITE (A -> Prop) (@EMPTY (A -> Prop))).
Proof. exact (SYM (@lem4876647 A)). Qed.
Lemma lem4876649 {A : Type'} : @FINITE (A -> Prop) (@EMPTY (A -> Prop)).
Proof. exact (EQ_MP (@lem4876648 A) (@lem0)). Qed.
Lemma lem4876650 {A : Type'} (P : type686 A) : (@UNION_OF A (@FINITE (A -> Prop)) P (@EMPTY A)) = True.
Proof. exact (@lem4876644 A P (@lem4876649 A)). Qed.
Lemma lem4876651 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4876650 A P)). Qed.
Lemma lem4876652 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4876653 {A : Type'} : (term8 A) = (term9 A).
Proof. exact (MK_COMB (@lem4876652 A) (@lem4876651 A)). Qed.
Lemma lem4876655 {A : Type'} (t : Prop) : (term10 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4876656 {A : Type'} (t : Prop) : (term11 A t) = t.
Proof. exact (@lem4876655 (type686 A) t). Qed.
Lemma lem4876657 {A : Type'} : (term9 A) = True.
Proof. exact (@lem4876656 A True). Qed.
Lemma lem4876658 {A : Type'} : (term8 A) = True.
Proof. exact (TRANS (@lem4876653 A) (@lem4876657 A)). Qed.
Lemma lem4876659 {A : Type'} : True = (term8 A).
Proof. exact (SYM (@lem4876658 A)). Qed.
Lemma lem4876660 {A : Type'} : term8 A.
Proof. exact (EQ_MP (@lem4876659 A) (@lem0)). Qed.
