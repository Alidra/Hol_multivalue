Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import cong_term_abbrevs.
Lemma lem2427736 {A : Type'} : (@eq2 A) = (term0 A).
Proof. exact (@eq2_def A). Qed.
Lemma lem2427737 {A : Type'} (_29475 : A) : _29475 = _29475.
Proof. exact (eq_refl _29475). Qed.
Lemma lem2427738 {A : Type'} (_29475 : A) : (@eq2 A _29475) = (term1 A _29475).
Proof. exact (MK_COMB (@lem2427736 A) (@lem2427737 A _29475)). Qed.
Lemma lem2427739 {A : Type'} (_29475 : A) : (term1 A _29475) = (term2 A _29475).
Proof. exact (eq_refl (term1 A _29475)). Qed.
Lemma lem2427740 {A : Type'} (_29475 : A) : (@eq2 A _29475) = (term2 A _29475).
Proof. exact (TRANS (@lem2427738 A _29475) (@lem2427739 A _29475)). Qed.
Lemma lem2427741 {A : Type'} (_29476 : A) : _29476 = _29476.
Proof. exact (eq_refl _29476). Qed.
Lemma lem2427742 {A : Type'} (_29475 : A) (_29476 : A) : (@eq2 A _29475 _29476) = (term3 A _29475 _29476).
Proof. exact (MK_COMB (@lem2427740 A _29475) (@lem2427741 A _29476)). Qed.
Lemma lem2427743 {A : Type'} (_29475 : A) (_29476 : A) : (term3 A _29475 _29476) = (term4 A _29475 _29476).
Proof. exact (eq_refl (term3 A _29475 _29476)). Qed.
Lemma lem2427744 {A : Type'} (_29475 : A) (_29476 : A) : (@eq2 A _29475 _29476) = (term4 A _29475 _29476).
Proof. exact (TRANS (@lem2427742 A _29475 _29476) (@lem2427743 A _29475 _29476)). Qed.
Lemma lem2427745 {A : Type'} (_29477 : type1402 A) : _29477 = _29477.
Proof. exact (eq_refl _29477). Qed.
Lemma lem2427746 {A : Type'} (_29475 : A) (_29476 : A) (_29477 : type1402 A) : (@eq2 A _29475 _29476 _29477) = (term5 A _29475 _29476 _29477).
Proof. exact (MK_COMB (@lem2427744 A _29475 _29476) (@lem2427745 A _29477)). Qed.
Lemma lem2427747 {A : Type'} (_29477 : type1402 A) (_29475 : A) (_29476 : A) : (term5 A _29475 _29476 _29477) = (_29477 _29475 _29476).
Proof. exact (eq_refl (term5 A _29475 _29476 _29477)). Qed.
Lemma lem2427748 {A : Type'} (_29477 : type1402 A) (_29475 : A) (_29476 : A) : (@eq2 A _29475 _29476 _29477) = (_29477 _29475 _29476).
Proof. exact (TRANS (@lem2427746 A _29475 _29476 _29477) (@lem2427747 A _29477 _29475 _29476)). Qed.
Lemma lem2427749 {A : Type'} (_29475 : A) (_29476 : A) : term6 A _29475 _29476.
Proof. exact (fun _29477 : type1402 A => @lem2427748 A _29477 _29475 _29476). Qed.
Lemma lem2427750 {A : Type'} (_29475 : A) : term7 A _29475.
Proof. exact (fun _29476 : A => @lem2427749 A _29475 _29476). Qed.
Lemma lem2427751 {A : Type'} : term8 A.
Proof. exact (fun _29475 : A => @lem2427750 A _29475). Qed.
Lemma lem2427752 {A : Type'} (_29475 : A) : term9 A _29475.
Proof. exact (@lem2427751 A _29475). Qed.
Lemma lem2427753 {A : Type'} (_29475 : A) : (term9 A _29475) = (term7 A _29475).
Proof. exact (eq_refl (term9 A _29475)). Qed.
Lemma lem2427754 {A : Type'} (_29475 : A) : term7 A _29475.
Proof. exact (EQ_MP (@lem2427753 A _29475) (@lem2427752 A _29475)). Qed.
Lemma lem2427755 {A : Type'} (_29475 : A) (_29476 : A) : term10 A _29475 _29476.
Proof. exact (@lem2427754 A _29475 _29476). Qed.
Lemma lem2427756 {A : Type'} (_29475 : A) (_29476 : A) : (term10 A _29475 _29476) = (term6 A _29475 _29476).
Proof. exact (eq_refl (term10 A _29475 _29476)). Qed.
Lemma lem2427757 {A : Type'} (_29475 : A) (_29476 : A) : term6 A _29475 _29476.
Proof. exact (EQ_MP (@lem2427756 A _29475 _29476) (@lem2427755 A _29475 _29476)). Qed.
Lemma lem2427758 {A : Type'} (_29475 : A) (_29476 : A) (_29477 : type1402 A) : term11 A _29475 _29476 _29477.
Proof. exact (@lem2427757 A _29475 _29476 _29477). Qed.
Lemma lem2427759 {A : Type'} (_29477 : type1402 A) (_29475 : A) (_29476 : A) : (term11 A _29475 _29476 _29477) = ((@eq2 A _29475 _29476 _29477) = (_29477 _29475 _29476)).
Proof. exact (eq_refl (term11 A _29475 _29476 _29477)). Qed.
Lemma lem2427760 {A : Type'} (_29477 : type1402 A) (_29475 : A) (_29476 : A) : (@eq2 A _29475 _29476 _29477) = (_29477 _29475 _29476).
Proof. exact (EQ_MP (@lem2427759 A _29477 _29475 _29476) (@lem2427758 A _29475 _29476 _29477)). Qed.
Lemma lem2427816 {A : Type'} (rel : type1402 A) (x : A) (y : A) : (@eq2 A x y rel) = (rel x y).
Proof. exact (@lem2427760 A rel x y). Qed.
Lemma lem2427817 {A : Type'} (rel : type1402 A) (x : A) : term12 A rel x.
Proof. exact (fun y : A => @lem2427816 A rel x y). Qed.
Lemma lem2427818 {A : Type'} (rel : type1402 A) : term13 A rel.
Proof. exact (fun x : A => @lem2427817 A rel x). Qed.
Lemma lem2427819 {A : Type'} : term14 A.
Proof. exact (fun rel : type1402 A => @lem2427818 A rel). Qed.
