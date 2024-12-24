Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SURJ_term_abbrevs.
Lemma lem3201540 {A B : Type'} : (@SURJ A B) = (term0 A B).
Proof. exact (@SURJ_def A B). Qed.
Lemma lem3201541 {A B : Type'} (_32892 : A -> B) : _32892 = _32892.
Proof. exact (eq_refl _32892). Qed.
Lemma lem3201542 {A B : Type'} (_32892 : A -> B) : (@SURJ A B _32892) = (term1 A B _32892).
Proof. exact (MK_COMB (@lem3201540 A B) (@lem3201541 A B _32892)). Qed.
Lemma lem3201543 {A B : Type'} (_32892 : A -> B) : (term1 A B _32892) = (term2 A B _32892).
Proof. exact (eq_refl (term1 A B _32892)). Qed.
Lemma lem3201544 {A B : Type'} (_32892 : A -> B) : (@SURJ A B _32892) = (term2 A B _32892).
Proof. exact (TRANS (@lem3201542 A B _32892) (@lem3201543 A B _32892)). Qed.
Lemma lem3201545 {A : Type'} (_32893 : A -> Prop) : _32893 = _32893.
Proof. exact (eq_refl _32893). Qed.
Lemma lem3201546 {A B : Type'} (_32892 : A -> B) (_32893 : A -> Prop) : (@SURJ A B _32892 _32893) = (term3 A B _32892 _32893).
Proof. exact (MK_COMB (@lem3201544 A B _32892) (@lem3201545 A _32893)). Qed.
Lemma lem3201547 {A B : Type'} (_32893 : A -> Prop) (_32892 : A -> B) : (term3 A B _32892 _32893) = (term4 A B _32893 _32892).
Proof. exact (eq_refl (term3 A B _32892 _32893)). Qed.
Lemma lem3201548 {A B : Type'} (_32893 : A -> Prop) (_32892 : A -> B) : (@SURJ A B _32892 _32893) = (term4 A B _32893 _32892).
Proof. exact (TRANS (@lem3201546 A B _32892 _32893) (@lem3201547 A B _32893 _32892)). Qed.
Lemma lem3201549 {B : Type'} (_32894 : B -> Prop) : _32894 = _32894.
Proof. exact (eq_refl _32894). Qed.
Lemma lem3201550 {A B : Type'} (_32893 : A -> Prop) (_32892 : A -> B) (_32894 : B -> Prop) : (@SURJ A B _32892 _32893 _32894) = (term5 A B _32893 _32892 _32894).
Proof. exact (MK_COMB (@lem3201548 A B _32893 _32892) (@lem3201549 B _32894)). Qed.
Lemma lem3201551 {A B : Type'} (_32894 : B -> Prop) (_32893 : A -> Prop) (_32892 : A -> B) : (term5 A B _32893 _32892 _32894) = (term6 A B _32894 _32893 _32892).
Proof. exact (eq_refl (term5 A B _32893 _32892 _32894)). Qed.
Lemma lem3201552 {A B : Type'} (_32894 : B -> Prop) (_32893 : A -> Prop) (_32892 : A -> B) : (@SURJ A B _32892 _32893 _32894) = (term6 A B _32894 _32893 _32892).
Proof. exact (TRANS (@lem3201550 A B _32893 _32892 _32894) (@lem3201551 A B _32894 _32893 _32892)). Qed.
Lemma lem3201553 {A B : Type'} (_32893 : A -> Prop) (_32892 : A -> B) : term7 A B _32893 _32892.
Proof. exact (fun _32894 : B -> Prop => @lem3201552 A B _32894 _32893 _32892). Qed.
Lemma lem3201554 {A B : Type'} (_32892 : A -> B) : term8 A B _32892.
Proof. exact (fun _32893 : A -> Prop => @lem3201553 A B _32893 _32892). Qed.
Lemma lem3201555 {A B : Type'} : term9 A B.
Proof. exact (fun _32892 : A -> B => @lem3201554 A B _32892). Qed.
Lemma lem3201556 {A B : Type'} (_32892 : A -> B) : term10 A B _32892.
Proof. exact (@lem3201555 A B _32892). Qed.
Lemma lem3201557 {A B : Type'} (_32892 : A -> B) : (term10 A B _32892) = (term8 A B _32892).
Proof. exact (eq_refl (term10 A B _32892)). Qed.
Lemma lem3201558 {A B : Type'} (_32892 : A -> B) : term8 A B _32892.
Proof. exact (EQ_MP (@lem3201557 A B _32892) (@lem3201556 A B _32892)). Qed.
Lemma lem3201559 {A B : Type'} (_32892 : A -> B) (_32893 : A -> Prop) : term11 A B _32892 _32893.
Proof. exact (@lem3201558 A B _32892 _32893). Qed.
Lemma lem3201560 {A B : Type'} (_32893 : A -> Prop) (_32892 : A -> B) : (term11 A B _32892 _32893) = (term7 A B _32893 _32892).
Proof. exact (eq_refl (term11 A B _32892 _32893)). Qed.
Lemma lem3201561 {A B : Type'} (_32893 : A -> Prop) (_32892 : A -> B) : term7 A B _32893 _32892.
Proof. exact (EQ_MP (@lem3201560 A B _32893 _32892) (@lem3201559 A B _32892 _32893)). Qed.
Lemma lem3201562 {A B : Type'} (_32893 : A -> Prop) (_32892 : A -> B) (_32894 : B -> Prop) : term12 A B _32893 _32892 _32894.
Proof. exact (@lem3201561 A B _32893 _32892 _32894). Qed.
Lemma lem3201563 {A B : Type'} (_32894 : B -> Prop) (_32893 : A -> Prop) (_32892 : A -> B) : (term12 A B _32893 _32892 _32894) = ((@SURJ A B _32892 _32893 _32894) = (term6 A B _32894 _32893 _32892)).
Proof. exact (eq_refl (term12 A B _32893 _32892 _32894)). Qed.
Lemma lem3201564 {A B : Type'} (_32894 : B -> Prop) (_32893 : A -> Prop) (_32892 : A -> B) : (@SURJ A B _32892 _32893 _32894) = (term6 A B _32894 _32893 _32892).
Proof. exact (EQ_MP (@lem3201563 A B _32894 _32893 _32892) (@lem3201562 A B _32893 _32892 _32894)). Qed.
Lemma lem3201620 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (@SURJ A B f s t) = (term6 A B t s f).
Proof. exact (@lem3201564 A B t s f). Qed.
Lemma lem3201621 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term13 A B t s.
Proof. exact (fun f : A -> B => @lem3201620 A B t s f). Qed.
Lemma lem3201622 {A B : Type'} (t : B -> Prop) : term14 A B t.
Proof. exact (fun s : A -> Prop => @lem3201621 A B t s). Qed.
Lemma lem3201623 {A B : Type'} : term15 A B.
Proof. exact (fun t : B -> Prop => @lem3201622 A B t). Qed.
