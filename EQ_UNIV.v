Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EQ_UNIV_term_abbrevs.
Require Import thm0_spec.
Require Import thm1856_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211724_spec.
Require Import thm3211725_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3216517 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3216518 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3216517 A s t). Qed.
Lemma lem3216519 {A : Type'} (s : A -> Prop) : (s = (@UNIV A)) = (term1 A s).
Proof. exact (@lem3216518 A s (@UNIV A)). Qed.
Lemma lem3216528 {A : Type'} (s : A -> Prop) : (term2 A s) = (term2 A s).
Proof. exact (eq_refl (term2 A s)). Qed.
Lemma lem3216529 {A : Type'} (s : A -> Prop) : ((term3 A s) = (s = (@UNIV A))) = ((term3 A s) = (term1 A s)).
Proof. exact (MK_COMB (@lem3216528 A s) (@lem3216519 A s)). Qed.
Lemma lem3216534 {A : Type'} (s : A -> Prop) : ((term3 A s) = (term1 A s)) = ((term3 A s) = (s = (@UNIV A))).
Proof. exact (SYM (@lem3216529 A s)). Qed.
Lemma lem3216542 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3216543 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3216542 A P x). Qed.
Lemma lem3216544 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3216543 A s x). Qed.
Lemma lem3216545 {A : Type'} (s : A -> Prop) : (term4 A s) = (term5 A s).
Proof. exact (fun_ext (fun x : A => @lem3216544 A s x)). Qed.
Lemma lem3216546 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3216547 {A : Type'} (s : A -> Prop) : (term3 A s) = (term6 A s).
Proof. exact (MK_COMB (@lem3216546 A) (@lem3216545 A s)). Qed.
Lemma lem3216552 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3216553 {A : Type'} (s : A -> Prop) : (term2 A s) = (term7 A s).
Proof. exact (MK_COMB (@lem3216552) (@lem3216547 A s)). Qed.
Lemma lem3216561 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3216562 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3216561 A P x). Qed.
Lemma lem3216563 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3216562 A s x). Qed.
Lemma lem3216564 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3216565 {A : Type'} (s : A -> Prop) (x : A) : (term8 A x s) = (term9 A s x).
Proof. exact (MK_COMB (@lem3216564) (@lem3216563 A s x)). Qed.
Lemma lem3216567 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem3216568 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3216567 A x). Qed.
Lemma lem3216569 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x (@UNIV A))) = ((s x) = True).
Proof. exact (MK_COMB (@lem3216565 A s x) (@lem3216568 A x)). Qed.
Lemma lem3216571 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem3216572 {A : Type'} (s : A -> Prop) (x : A) : ((s x) = True) = (s x).
Proof. exact (@lem3216571 (s x)). Qed.
Lemma lem3216573 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x (@UNIV A))) = (s x).
Proof. exact (TRANS (@lem3216569 A s x) (@lem3216572 A s x)). Qed.
Lemma lem3216574 {A : Type'} (s : A -> Prop) : (term10 A s) = (term5 A s).
Proof. exact (fun_ext (fun x : A => @lem3216573 A s x)). Qed.
Lemma lem3216575 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3216576 {A : Type'} (s : A -> Prop) : (term1 A s) = (term6 A s).
Proof. exact (MK_COMB (@lem3216575 A) (@lem3216574 A s)). Qed.
Lemma lem3216581 {A : Type'} (s : A -> Prop) : ((term3 A s) = (term1 A s)) = ((term6 A s) = (term6 A s)).
Proof. exact (MK_COMB (@lem3216553 A s) (@lem3216576 A s)). Qed.
Lemma lem3216583 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3216584 (x : Prop) : (x = x) = True.
Proof. exact (@lem3216583 Prop x). Qed.
Lemma lem3216585 {A : Type'} (s : A -> Prop) : ((term6 A s) = (term6 A s)) = True.
Proof. exact (@lem3216584 (term6 A s)). Qed.
Lemma lem3216586 {A : Type'} (s : A -> Prop) : ((term3 A s) = (term1 A s)) = True.
Proof. exact (TRANS (@lem3216581 A s) (@lem3216585 A s)). Qed.
Lemma lem3216587 {A : Type'} (s : A -> Prop) : True = ((term3 A s) = (term1 A s)).
Proof. exact (SYM (@lem3216586 A s)). Qed.
Lemma lem3216588 {A : Type'} (s : A -> Prop) : (term3 A s) = (term1 A s).
Proof. exact (EQ_MP (@lem3216587 A s) (@lem0)). Qed.
Lemma lem3216589 {A : Type'} (s : A -> Prop) : (term3 A s) = (s = (@UNIV A)).
Proof. exact (EQ_MP (@lem3216534 A s) (@lem3216588 A s)). Qed.
