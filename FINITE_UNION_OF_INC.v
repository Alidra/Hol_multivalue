Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_UNION_OF_INC_term_abbrevs.
Require Import FINITE_SING_spec.
Require Import UNION_OF_INC_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem4876702 {_92373 : Type'} (a : _92373) : term0 _92373 a.
Proof. exact (@lem3608356 _92373 a). Qed.
Lemma lem4876703 {_92373 : Type'} (a : _92373) : (term0 _92373 a) = (term1 _92373 a).
Proof. exact (eq_refl (term0 _92373 a)). Qed.
Lemma lem4876704 {_92373 : Type'} (a : _92373) : term1 _92373 a.
Proof. exact (EQ_MP (@lem4876703 _92373 a) (@lem4876702 _92373 a)). Qed.
Lemma lem4876705 {_92373 : Type'} (a : _92373) : (term1 _92373 a) = ((term1 _92373 a) = True).
Proof. exact (@lem7 (term1 _92373 a)). Qed.
Lemma lem4876707 {A : Type'} (P : type180 A) : term2 A P.
Proof. exact (@lem4842424 A P). Qed.
Lemma lem4876708 {A : Type'} (P : type180 A) : (term2 A P) = (term3 A P).
Proof. exact (eq_refl (term2 A P)). Qed.
Lemma lem4876709 {A : Type'} (P : type180 A) : term3 A P.
Proof. exact (EQ_MP (@lem4876708 A P) (@lem4876707 A P)). Qed.
Lemma lem4876710 {A : Type'} (P : type180 A) (Q : type686 A) : term4 A P Q.
Proof. exact (@lem4876709 A P Q). Qed.
Lemma lem4876711 {A : Type'} (P : type180 A) (Q : type686 A) : (term4 A P Q) = (term5 A P Q).
Proof. exact (eq_refl (term4 A P Q)). Qed.
Lemma lem4876712 {A : Type'} (P : type180 A) (Q : type686 A) : term5 A P Q.
Proof. exact (EQ_MP (@lem4876711 A P Q) (@lem4876710 A P Q)). Qed.
Lemma lem4876713 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : term6 A P Q s.
Proof. exact (@lem4876712 A P Q s). Qed.
Lemma lem4876714 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term6 A P Q s) = (term7 A P Q s).
Proof. exact (eq_refl (term6 A P Q s)). Qed.
Lemma lem4876715 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : term7 A P Q s.
Proof. exact (EQ_MP (@lem4876714 A P Q s) (@lem4876713 A P Q s)). Qed.
Lemma lem4876716 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term8 A P Q s) : term8 A P Q s.
Proof. exact (h1). Qed.
Lemma lem4876717 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term8 A P Q s) : @UNION_OF A P Q s.
Proof. exact (@lem4876715 A P Q s (@lem4876716 A P Q s h1)). Qed.
Lemma lem4876718 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (@UNION_OF A P Q s) = ((@UNION_OF A P Q s) = True).
Proof. exact (@lem7 (@UNION_OF A P Q s)). Qed.
Lemma lem4876719 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term8 A P Q s) : (@UNION_OF A P Q s) = True.
Proof. exact (EQ_MP (@lem4876718 A P Q s) (@lem4876717 A P Q s h1)). Qed.
Lemma lem4876736 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term9 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4876737 (p : Prop) (q : Prop) (p' : Prop) : term10 p q p'.
Proof. exact (fun q' : Prop => @lem4876736 p q p' q'). Qed.
Lemma lem4876738 (p : Prop) (q : Prop) : term11 p q.
Proof. exact (fun p' : Prop => @lem4876737 p q p'). Qed.
Lemma lem4876739 {A : Type'} (P : type686 A) (s : A -> Prop) : term12 A P s.
Proof. exact (@lem4876738 (P s) (@UNION_OF A (@FINITE (A -> Prop)) P s)). Qed.
Lemma lem4876740 {A : Type'} (P : type686 A) (s : A -> Prop) (p' : Prop) : term13 A P s p'.
Proof. exact (@lem4876739 A P s p'). Qed.
Lemma lem4876741 {A : Type'} (P : type686 A) (s : A -> Prop) (p' : Prop) : (term13 A P s p') = (term14 A P s p').
Proof. exact (eq_refl (term13 A P s p')). Qed.
Lemma lem4876742 {A : Type'} (P : type686 A) (s : A -> Prop) (p' : Prop) : term14 A P s p'.
Proof. exact (EQ_MP (@lem4876741 A P s p') (@lem4876740 A P s p')). Qed.
Lemma lem4876743 {A : Type'} (P : type686 A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term15 A P s p' q'.
Proof. exact (@lem4876742 A P s p' q'). Qed.
Lemma lem4876744 {A : Type'} (P : type686 A) (s : A -> Prop) (p' : Prop) (q' : Prop) : (term15 A P s p' q') = (term16 A P s p' q').
Proof. exact (eq_refl (term15 A P s p' q')). Qed.
Lemma lem4876745 {A : Type'} (P : type686 A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term16 A P s p' q'.
Proof. exact (EQ_MP (@lem4876744 A P s p' q') (@lem4876743 A P s p' q')). Qed.
Lemma lem4876746 {A : Type'} (P : type686 A) (s : A -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem4876747 {A : Type'} (P : type686 A) (s : A -> Prop) (q' : Prop) : term17 A P s q'.
Proof. exact (@lem4876745 A P s (P s) q'). Qed.
Lemma lem4876748 {A : Type'} (P : type686 A) (s : A -> Prop) (q' : Prop) : term18 A P s q'.
Proof. exact (@lem4876747 A P s q' (@lem4876746 A P s)). Qed.
Lemma lem4876749 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : P s.
Proof. exact (h1). Qed.
Lemma lem4876750 {A : Type'} (P : type686 A) (s : A -> Prop) : (P s) = ((P s) = True).
Proof. exact (@lem7 (P s)). Qed.
Lemma lem4876753 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : term19 A P Q s.
Proof. exact (fun h0 : term8 A P Q s => @lem4876719 A P Q s h0). Qed.
Lemma lem4876754 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : term19 A P Q s.
Proof. exact (@lem4876753 A P Q s). Qed.
Lemma lem4876755 {A : Type'} (P : type686 A) (s : A -> Prop) : term20 A P s.
Proof. exact (@lem4876754 A (@FINITE (A -> Prop)) P s). Qed.
Lemma lem4876759 {_92373 : Type'} (a : _92373) : (term1 _92373 a) = True.
Proof. exact (EQ_MP (@lem4876705 _92373 a) (@lem4876704 _92373 a)). Qed.
Lemma lem4876760 {A : Type'} (a : A -> Prop) : (term21 A a) = True.
Proof. exact (@lem4876759 (A -> Prop) a). Qed.
Lemma lem4876761 {A : Type'} (s : A -> Prop) : (term21 A s) = True.
Proof. exact (@lem4876760 A s). Qed.
Lemma lem4876762 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4876763 {A : Type'} (s : A -> Prop) : (term22 A s) = (and True).
Proof. exact (MK_COMB (@lem4876762) (@lem4876761 A s)). Qed.
Lemma lem4876765 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : (P s) = True.
Proof. exact (EQ_MP (@lem4876750 A P s) (@lem4876749 A P s h1)). Qed.
Lemma lem4876766 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : (term23 A P s) = (True /\ True).
Proof. exact (MK_COMB (@lem4876763 A s) (@lem4876765 A P s h1)). Qed.
Lemma lem4876768 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4876769 : (True /\ True) = True.
Proof. exact (@lem4876768 True). Qed.
Lemma lem4876770 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : (term23 A P s) = True.
Proof. exact (TRANS (@lem4876766 A P s h1) (@lem4876769)). Qed.
Lemma lem4876771 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : True = (term23 A P s).
Proof. exact (SYM (@lem4876770 A P s h1)). Qed.
Lemma lem4876772 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : term23 A P s.
Proof. exact (EQ_MP (@lem4876771 A P s h1) (@lem0)). Qed.
Lemma lem4876773 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : (@UNION_OF A (@FINITE (A -> Prop)) P s) = True.
Proof. exact (@lem4876755 A P s (@lem4876772 A P s h1)). Qed.
Lemma lem4876774 {A : Type'} (P : type686 A) (s : A -> Prop) : term24 A P s.
Proof. exact (fun h0 : P s => @lem4876773 A P s h0). Qed.
Lemma lem4876775 {A : Type'} (P : type686 A) (s : A -> Prop) : term25 A P s.
Proof. exact (@lem4876748 A P s True). Qed.
Lemma lem4876776 {A : Type'} (P : type686 A) (s : A -> Prop) : (term26 A P s) = (term27 A P s).
Proof. exact (@lem4876775 A P s (@lem4876774 A P s)). Qed.
Lemma lem4876778 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4876779 {A : Type'} (P : type686 A) (s : A -> Prop) : (term27 A P s) = True.
Proof. exact (@lem4876778 (P s)). Qed.
Lemma lem4876780 {A : Type'} (P : type686 A) (s : A -> Prop) : (term26 A P s) = True.
Proof. exact (TRANS (@lem4876776 A P s) (@lem4876779 A P s)). Qed.
Lemma lem4876781 {A : Type'} (P : type686 A) : (term28 A P) = (term29 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4876780 A P s)). Qed.
Lemma lem4876782 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4876783 {A : Type'} (P : type686 A) : (term30 A P) = (term31 A).
Proof. exact (MK_COMB (@lem4876782 A) (@lem4876781 A P)). Qed.
Lemma lem4876785 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4876786 {A : Type'} (t : Prop) : (term33 A t) = t.
Proof. exact (@lem4876785 (A -> Prop) t). Qed.
Lemma lem4876787 {A : Type'} : (term31 A) = True.
Proof. exact (@lem4876786 A True). Qed.
Lemma lem4876788 {A : Type'} (P : type686 A) : (term30 A P) = True.
Proof. exact (TRANS (@lem4876783 A P) (@lem4876787 A)). Qed.
Lemma lem4876789 {A : Type'} : (term34 A) = (term35 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4876788 A P)). Qed.
Lemma lem4876790 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4876791 {A : Type'} : (term36 A) = (term37 A).
Proof. exact (MK_COMB (@lem4876790 A) (@lem4876789 A)). Qed.
Lemma lem4876793 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4876794 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (@lem4876793 (type686 A) t). Qed.
Lemma lem4876795 {A : Type'} : (term37 A) = True.
Proof. exact (@lem4876794 A True). Qed.
Lemma lem4876796 {A : Type'} : (term36 A) = True.
Proof. exact (TRANS (@lem4876791 A) (@lem4876795 A)). Qed.
Lemma lem4876797 {A : Type'} : True = (term36 A).
Proof. exact (SYM (@lem4876796 A)). Qed.
Lemma lem4876798 {A : Type'} : term36 A.
Proof. exact (EQ_MP (@lem4876797 A) (@lem0)). Qed.
