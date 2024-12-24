Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IN_REST_term_abbrevs.
Require Import IN_DELETE_spec.
Require Import REST_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem3206071 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3205803 A s). Qed.
Lemma lem3206072 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem3206073 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem3206072 A s) (@lem3206071 A s)). Qed.
Lemma lem3206074 {A : Type'} (s : A -> Prop) (x : A) : term2 A s x.
Proof. exact (@lem3206073 A s x). Qed.
Lemma lem3206075 {A : Type'} (s : A -> Prop) (x : A) : (term2 A s x) = (term3 A s x).
Proof. exact (eq_refl (term2 A s x)). Qed.
Lemma lem3206076 {A : Type'} (s : A -> Prop) (x : A) : term3 A s x.
Proof. exact (EQ_MP (@lem3206075 A s x) (@lem3206074 A s x)). Qed.
Lemma lem3206077 {A : Type'} (s : A -> Prop) (x : A) (y : A) : term4 A s x y.
Proof. exact (@lem3206076 A s x y). Qed.
Lemma lem3206078 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term4 A s x y) = ((term5 A x s y) = (term6 A s x y)).
Proof. exact (eq_refl (term4 A s x y)). Qed.
Lemma lem3206080 {A : Type'} (s : A -> Prop) : term7 A s.
Proof. exact (@lem3204727 A s). Qed.
Lemma lem3206081 {A : Type'} (s : A -> Prop) : (term7 A s) = ((@REST A s) = (term8 A s)).
Proof. exact (eq_refl (term7 A s)). Qed.
Lemma lem3206094 {A : Type'} (s : A -> Prop) : (@REST A s) = (term8 A s).
Proof. exact (EQ_MP (@lem3206081 A s) (@lem3206080 A s)). Qed.
Lemma lem3206095 {A : Type'} (s : A -> Prop) : (@REST A s) = (term8 A s).
Proof. exact (@lem3206094 A s). Qed.
Lemma lem3206096 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3206097 {A : Type'} (x : A) (s : A -> Prop) : (term9 A x s) = (term10 A x s).
Proof. exact (MK_COMB (@lem3206096 A x) (@lem3206095 A s)). Qed.
Lemma lem3206099 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term5 A x s y) = (term6 A s x y).
Proof. exact (EQ_MP (@lem3206078 A s x y) (@lem3206077 A s x y)). Qed.
Lemma lem3206100 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term5 A x s y) = (term6 A s x y).
Proof. exact (@lem3206099 A s x y). Qed.
Lemma lem3206101 {A : Type'} (x : A) (s : A -> Prop) : (term10 A x s) = (term11 A x s).
Proof. exact (@lem3206100 A s x (@CHOICE A s)). Qed.
Lemma lem3206106 {A : Type'} (x : A) (s : A -> Prop) : (term9 A x s) = (term11 A x s).
Proof. exact (TRANS (@lem3206097 A x s) (@lem3206101 A x s)). Qed.
Lemma lem3206107 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3206108 {A : Type'} (x : A) (s : A -> Prop) : (term12 A x s) = (term13 A x s).
Proof. exact (MK_COMB (@lem3206107) (@lem3206106 A x s)). Qed.
Lemma lem3206113 {A : Type'} (x : A) (s : A -> Prop) : (term11 A x s) = (term11 A x s).
Proof. exact (eq_refl (term11 A x s)). Qed.
Lemma lem3206114 {A : Type'} (x : A) (s : A -> Prop) : ((term9 A x s) = (term11 A x s)) = ((term11 A x s) = (term11 A x s)).
Proof. exact (MK_COMB (@lem3206108 A x s) (@lem3206113 A x s)). Qed.
Lemma lem3206116 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3206117 (x : Prop) : (x = x) = True.
Proof. exact (@lem3206116 Prop x). Qed.
Lemma lem3206118 {A : Type'} (x : A) (s : A -> Prop) : ((term11 A x s) = (term11 A x s)) = True.
Proof. exact (@lem3206117 (term11 A x s)). Qed.
Lemma lem3206119 {A : Type'} (x : A) (s : A -> Prop) : ((term9 A x s) = (term11 A x s)) = True.
Proof. exact (TRANS (@lem3206114 A x s) (@lem3206118 A x s)). Qed.
Lemma lem3206120 {A : Type'} (x : A) : (term14 A x) = (term15 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3206119 A x s)). Qed.
Lemma lem3206121 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3206122 {A : Type'} (x : A) : (term16 A x) = (term17 A).
Proof. exact (MK_COMB (@lem3206121 A) (@lem3206120 A x)). Qed.
Lemma lem3206124 {A : Type'} (t : Prop) : (term18 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3206125 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (@lem3206124 (A -> Prop) t). Qed.
Lemma lem3206126 {A : Type'} : (term17 A) = True.
Proof. exact (@lem3206125 A True). Qed.
Lemma lem3206127 {A : Type'} (x : A) : (term16 A x) = True.
Proof. exact (TRANS (@lem3206122 A x) (@lem3206126 A)). Qed.
Lemma lem3206128 {A : Type'} : (term20 A) = (term21 A).
Proof. exact (fun_ext (fun x : A => @lem3206127 A x)). Qed.
Lemma lem3206129 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3206130 {A : Type'} : (term22 A) = (term23 A).
Proof. exact (MK_COMB (@lem3206129 A) (@lem3206128 A)). Qed.
Lemma lem3206132 {A : Type'} (t : Prop) : (term18 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3206133 {A : Type'} (t : Prop) : (term18 A t) = t.
Proof. exact (@lem3206132 A t). Qed.
Lemma lem3206134 {A : Type'} : (term23 A) = True.
Proof. exact (@lem3206133 A True). Qed.
Lemma lem3206135 {A : Type'} : (term22 A) = True.
Proof. exact (TRANS (@lem3206130 A) (@lem3206134 A)). Qed.
Lemma lem3206136 {A : Type'} : True = (term22 A).
Proof. exact (SYM (@lem3206135 A)). Qed.
Lemma lem3206137 {A : Type'} : term22 A.
Proof. exact (EQ_MP (@lem3206136 A) (@lem0)). Qed.
