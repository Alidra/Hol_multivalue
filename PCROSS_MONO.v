Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PCROSS_MONO_term_abbrevs.
Require Import SUBSET_PCROSS_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1832_spec.
Require Import thm1842_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem8010704 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) : term0 _142062 _142063 _142064 s.
Proof. exact (@lem8010703 _142062 _142063 _142064 s). Qed.
Lemma lem8010705 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) : (term0 _142062 _142063 _142064 s) = (term1 _142062 _142063 _142064 s).
Proof. exact (eq_refl (term0 _142062 _142063 _142064 s)). Qed.
Lemma lem8010706 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) : term1 _142062 _142063 _142064 s.
Proof. exact (EQ_MP (@lem8010705 _142062 _142063 _142064 s) (@lem8010704 _142062 _142063 _142064 s)). Qed.
Lemma lem8010707 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) : term2 _142062 _142063 _142064 s t.
Proof. exact (@lem8010706 _142062 _142063 _142064 s t). Qed.
Lemma lem8010708 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) : (term2 _142062 _142063 _142064 s t) = (term3 _142062 _142063 _142064 s t).
Proof. exact (eq_refl (term2 _142062 _142063 _142064 s t)). Qed.
Lemma lem8010709 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) : term3 _142062 _142063 _142064 s t.
Proof. exact (EQ_MP (@lem8010708 _142062 _142063 _142064 s t) (@lem8010707 _142062 _142063 _142064 s t)). Qed.
Lemma lem8010710 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) : term4 _142062 _142063 _142064 s t s'.
Proof. exact (@lem8010709 _142062 _142063 _142064 s t s'). Qed.
Lemma lem8010711 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) : (term4 _142062 _142063 _142064 s t s') = (term5 _142062 _142063 _142064 s s' t).
Proof. exact (eq_refl (term4 _142062 _142063 _142064 s t s')). Qed.
Lemma lem8010712 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) : term5 _142062 _142063 _142064 s s' t.
Proof. exact (EQ_MP (@lem8010711 _142062 _142063 _142064 s s' t) (@lem8010710 _142062 _142063 _142064 s t s')). Qed.
Lemma lem8010713 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : term6 _142062 _142063 _142064 s s' t t'.
Proof. exact (@lem8010712 _142062 _142063 _142064 s s' t t'). Qed.
Lemma lem8010714 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term6 _142062 _142063 _142064 s s' t t') = ((term7 _142062 _142063 _142064 s t s' t') = (term8 _142062 _142063 _142064 s s' t t')).
Proof. exact (eq_refl (term6 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8010735 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term9 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem8010736 (p : Prop) (q : Prop) (p' : Prop) : term10 p q p'.
Proof. exact (fun q' : Prop => @lem8010735 p q p' q'). Qed.
Lemma lem8010737 (p : Prop) (q : Prop) : term11 p q.
Proof. exact (fun p' : Prop => @lem8010736 p q p'). Qed.
Lemma lem8010738 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (t : type24 _142122 _142124) (s' : type24 _142122 _142123) (t' : type24 _142122 _142124) : term12 _142122 _142123 _142124 s t s' t'.
Proof. exact (@lem8010737 (term13 _142122 _142123 _142124 s s' t t') (term7 _142122 _142123 _142124 s t s' t')). Qed.
Lemma lem8010739 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (t : type24 _142122 _142124) (s' : type24 _142122 _142123) (t' : type24 _142122 _142124) (p' : Prop) : term14 _142122 _142123 _142124 s t s' t' p'.
Proof. exact (@lem8010738 _142122 _142123 _142124 s t s' t' p'). Qed.
Lemma lem8010740 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (t : type24 _142122 _142124) (s' : type24 _142122 _142123) (t' : type24 _142122 _142124) (p' : Prop) : (term14 _142122 _142123 _142124 s t s' t' p') = (term15 _142122 _142123 _142124 s t s' t' p').
Proof. exact (eq_refl (term14 _142122 _142123 _142124 s t s' t' p')). Qed.
Lemma lem8010741 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (t : type24 _142122 _142124) (s' : type24 _142122 _142123) (t' : type24 _142122 _142124) (p' : Prop) : term15 _142122 _142123 _142124 s t s' t' p'.
Proof. exact (EQ_MP (@lem8010740 _142122 _142123 _142124 s t s' t' p') (@lem8010739 _142122 _142123 _142124 s t s' t' p')). Qed.
Lemma lem8010742 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (t : type24 _142122 _142124) (s' : type24 _142122 _142123) (t' : type24 _142122 _142124) (p' : Prop) (q' : Prop) : term16 _142122 _142123 _142124 s t s' t' p' q'.
Proof. exact (@lem8010741 _142122 _142123 _142124 s t s' t' p' q'). Qed.
Lemma lem8010743 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (t : type24 _142122 _142124) (s' : type24 _142122 _142123) (t' : type24 _142122 _142124) (p' : Prop) (q' : Prop) : (term16 _142122 _142123 _142124 s t s' t' p' q') = (term17 _142122 _142123 _142124 s t s' t' p' q').
Proof. exact (eq_refl (term16 _142122 _142123 _142124 s t s' t' p' q')). Qed.
Lemma lem8010744 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (t : type24 _142122 _142124) (s' : type24 _142122 _142123) (t' : type24 _142122 _142124) (p' : Prop) (q' : Prop) : term17 _142122 _142123 _142124 s t s' t' p' q'.
Proof. exact (EQ_MP (@lem8010743 _142122 _142123 _142124 s t s' t' p' q') (@lem8010742 _142122 _142123 _142124 s t s' t' p' q')). Qed.
Lemma lem8010747 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (s' : type24 _142122 _142123) (t : type24 _142122 _142124) (t' : type24 _142122 _142124) : (term13 _142122 _142123 _142124 s s' t t') = (term13 _142122 _142123 _142124 s s' t t').
Proof. exact (eq_refl (term13 _142122 _142123 _142124 s s' t t')). Qed.
Lemma lem8010748 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (s' : type24 _142122 _142123) (t : type24 _142122 _142124) (t' : type24 _142122 _142124) (q' : Prop) : term18 _142122 _142123 _142124 s s' t t' q'.
Proof. exact (@lem8010744 _142122 _142123 _142124 s t s' t' (term13 _142122 _142123 _142124 s s' t t') q'). Qed.
Lemma lem8010749 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (s' : type24 _142122 _142123) (t : type24 _142122 _142124) (t' : type24 _142122 _142124) (q' : Prop) : term19 _142122 _142123 _142124 s s' t t' q'.
Proof. exact (@lem8010748 _142122 _142123 _142124 s s' t t' q' (@lem8010747 _142122 _142123 _142124 s s' t t')). Qed.
Lemma lem8010750 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (s' : type24 _142122 _142123) (t : type24 _142122 _142124) (t' : type24 _142122 _142124) (h1 : term13 _142122 _142123 _142124 s s' t t') : term13 _142122 _142123 _142124 s s' t t'.
Proof. exact (h1). Qed.
Lemma lem8010751 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (s' : type24 _142122 _142123) (t : type24 _142122 _142124) (t' : type24 _142122 _142124) (h1 : term13 _142122 _142123 _142124 s s' t t') : @SUBSET (cart _142122 _142124) t t'.
Proof. exact (proj2 (@lem8010750 _142122 _142123 _142124 s s' t t' h1)). Qed.
Lemma lem8010752 {_142122 _142124 : Type'} (t : type24 _142122 _142124) (t' : type24 _142122 _142124) : (@SUBSET (cart _142122 _142124) t t') = ((@SUBSET (cart _142122 _142124) t t') = True).
Proof. exact (@lem7 (@SUBSET (cart _142122 _142124) t t')). Qed.
Lemma lem8010754 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (s' : type24 _142122 _142123) (t : type24 _142122 _142124) (t' : type24 _142122 _142124) (h1 : term13 _142122 _142123 _142124 s s' t t') : @SUBSET (cart _142122 _142123) s s'.
Proof. exact (proj1 (@lem8010750 _142122 _142123 _142124 s s' t t' h1)). Qed.
Lemma lem8010755 {_142122 _142123 : Type'} (s : type24 _142122 _142123) (s' : type24 _142122 _142123) : (@SUBSET (cart _142122 _142123) s s') = ((@SUBSET (cart _142122 _142123) s s') = True).
Proof. exact (@lem7 (@SUBSET (cart _142122 _142123) s s')). Qed.
Lemma lem8010758 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term7 _142062 _142063 _142064 s t s' t') = (term8 _142062 _142063 _142064 s s' t t').
Proof. exact (EQ_MP (@lem8010714 _142062 _142063 _142064 s s' t t') (@lem8010713 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8010759 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (s' : type24 _142122 _142123) (t : type24 _142122 _142124) (t' : type24 _142122 _142124) : (term7 _142122 _142123 _142124 s t s' t') = (term8 _142122 _142123 _142124 s s' t t').
Proof. exact (@lem8010758 _142122 _142123 _142124 s s' t t'). Qed.
Lemma lem8010771 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (s' : type24 _142122 _142123) (t : type24 _142122 _142124) (t' : type24 _142122 _142124) (h1 : term13 _142122 _142123 _142124 s s' t t') : (@SUBSET (cart _142122 _142123) s s') = True.
Proof. exact (EQ_MP (@lem8010755 _142122 _142123 s s') (@lem8010754 _142122 _142123 _142124 s s' t t' h1)). Qed.
Lemma lem8010772 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8010773 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (s' : type24 _142122 _142123) (t : type24 _142122 _142124) (t' : type24 _142122 _142124) (h1 : term13 _142122 _142123 _142124 s s' t t') : (term20 _142122 _142123 s s') = (and True).
Proof. exact (MK_COMB (@lem8010772) (@lem8010771 _142122 _142123 _142124 s s' t t' h1)). Qed.
Lemma lem8010775 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (s' : type24 _142122 _142123) (t : type24 _142122 _142124) (t' : type24 _142122 _142124) (h1 : term13 _142122 _142123 _142124 s s' t t') : (@SUBSET (cart _142122 _142124) t t') = True.
Proof. exact (EQ_MP (@lem8010752 _142122 _142124 t t') (@lem8010751 _142122 _142123 _142124 s s' t t' h1)). Qed.
Lemma lem8010776 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (s' : type24 _142122 _142123) (t : type24 _142122 _142124) (t' : type24 _142122 _142124) (h1 : term13 _142122 _142123 _142124 s s' t t') : (term13 _142122 _142123 _142124 s s' t t') = (True /\ True).
Proof. exact (MK_COMB (@lem8010773 _142122 _142123 _142124 s s' t t' h1) (@lem8010775 _142122 _142123 _142124 s s' t t' h1)). Qed.
Lemma lem8010778 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8010779 : (True /\ True) = True.
Proof. exact (@lem8010778 True). Qed.
Lemma lem8010780 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (s' : type24 _142122 _142123) (t : type24 _142122 _142124) (t' : type24 _142122 _142124) (h1 : term13 _142122 _142123 _142124 s s' t t') : (term13 _142122 _142123 _142124 s s' t t') = True.
Proof. exact (TRANS (@lem8010776 _142122 _142123 _142124 s s' t t' h1) (@lem8010779)). Qed.
Lemma lem8010781 {_142122 _142124 : Type'} (t : type24 _142122 _142124) : (term21 _142122 _142124 t) = (term21 _142122 _142124 t).
Proof. exact (eq_refl (term21 _142122 _142124 t)). Qed.
Lemma lem8010782 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (s' : type24 _142122 _142123) (t : type24 _142122 _142124) (t' : type24 _142122 _142124) (h1 : term13 _142122 _142123 _142124 s s' t t') : (term22 _142122 _142123 _142124 s s' t t') = (term23 _142122 _142124 t).
Proof. exact (MK_COMB (@lem8010781 _142122 _142124 t) (@lem8010780 _142122 _142123 _142124 s s' t t' h1)). Qed.
Lemma lem8010784 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem8010785 {_142122 _142124 : Type'} (t : type24 _142122 _142124) : (term23 _142122 _142124 t) = True.
Proof. exact (@lem8010784 (t = (@EMPTY (cart _142122 _142124)))). Qed.
Lemma lem8010786 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (s' : type24 _142122 _142123) (t : type24 _142122 _142124) (t' : type24 _142122 _142124) (h1 : term13 _142122 _142123 _142124 s s' t t') : (term22 _142122 _142123 _142124 s s' t t') = True.
Proof. exact (TRANS (@lem8010782 _142122 _142123 _142124 s s' t t' h1) (@lem8010785 _142122 _142124 t)). Qed.
Lemma lem8010787 {_142122 _142123 : Type'} (s : type24 _142122 _142123) : (term21 _142122 _142123 s) = (term21 _142122 _142123 s).
Proof. exact (eq_refl (term21 _142122 _142123 s)). Qed.
Lemma lem8010788 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (s' : type24 _142122 _142123) (t : type24 _142122 _142124) (t' : type24 _142122 _142124) (h1 : term13 _142122 _142123 _142124 s s' t t') : (term8 _142122 _142123 _142124 s s' t t') = (term23 _142122 _142123 s).
Proof. exact (MK_COMB (@lem8010787 _142122 _142123 s) (@lem8010786 _142122 _142123 _142124 s s' t t' h1)). Qed.
Lemma lem8010790 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem8010791 {_142122 _142123 : Type'} (s : type24 _142122 _142123) : (term23 _142122 _142123 s) = True.
Proof. exact (@lem8010790 (s = (@EMPTY (cart _142122 _142123)))). Qed.
Lemma lem8010792 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (s' : type24 _142122 _142123) (t : type24 _142122 _142124) (t' : type24 _142122 _142124) (h1 : term13 _142122 _142123 _142124 s s' t t') : (term8 _142122 _142123 _142124 s s' t t') = True.
Proof. exact (TRANS (@lem8010788 _142122 _142123 _142124 s s' t t' h1) (@lem8010791 _142122 _142123 s)). Qed.
Lemma lem8010793 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (s' : type24 _142122 _142123) (t : type24 _142122 _142124) (t' : type24 _142122 _142124) (h1 : term13 _142122 _142123 _142124 s s' t t') : (term7 _142122 _142123 _142124 s t s' t') = True.
Proof. exact (TRANS (@lem8010759 _142122 _142123 _142124 s s' t t') (@lem8010792 _142122 _142123 _142124 s s' t t' h1)). Qed.
Lemma lem8010794 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (t : type24 _142122 _142124) (s' : type24 _142122 _142123) (t' : type24 _142122 _142124) : term24 _142122 _142123 _142124 s t s' t'.
Proof. exact (fun h0 : term13 _142122 _142123 _142124 s s' t t' => @lem8010793 _142122 _142123 _142124 s s' t t' h0). Qed.
Lemma lem8010795 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (s' : type24 _142122 _142123) (t : type24 _142122 _142124) (t' : type24 _142122 _142124) : term25 _142122 _142123 _142124 s s' t t'.
Proof. exact (@lem8010749 _142122 _142123 _142124 s s' t t' True). Qed.
Lemma lem8010796 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (s' : type24 _142122 _142123) (t : type24 _142122 _142124) (t' : type24 _142122 _142124) : (term26 _142122 _142123 _142124 s t s' t') = (term27 _142122 _142123 _142124 s s' t t').
Proof. exact (@lem8010795 _142122 _142123 _142124 s s' t t' (@lem8010794 _142122 _142123 _142124 s t s' t')). Qed.
Lemma lem8010798 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem8010799 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (s' : type24 _142122 _142123) (t : type24 _142122 _142124) (t' : type24 _142122 _142124) : (term27 _142122 _142123 _142124 s s' t t') = True.
Proof. exact (@lem8010798 (term13 _142122 _142123 _142124 s s' t t')). Qed.
Lemma lem8010800 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (t : type24 _142122 _142124) (s' : type24 _142122 _142123) (t' : type24 _142122 _142124) : (term26 _142122 _142123 _142124 s t s' t') = True.
Proof. exact (TRANS (@lem8010796 _142122 _142123 _142124 s s' t t') (@lem8010799 _142122 _142123 _142124 s s' t t')). Qed.
Lemma lem8010801 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (t : type24 _142122 _142124) (s' : type24 _142122 _142123) : (term28 _142122 _142123 _142124 s t s') = (term29 _142122 _142124).
Proof. exact (fun_ext (fun t' : type24 _142122 _142124 => @lem8010800 _142122 _142123 _142124 s t s' t')). Qed.
Lemma lem8010802 {_142122 _142124 : Type'} : (@all ((cart _142122 _142124) -> Prop)) = (@all ((cart _142122 _142124) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142122 _142124) -> Prop))). Qed.
Lemma lem8010803 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (t : type24 _142122 _142124) (s' : type24 _142122 _142123) : (term30 _142122 _142123 _142124 s t s') = (term31 _142122 _142124).
Proof. exact (MK_COMB (@lem8010802 _142122 _142124) (@lem8010801 _142122 _142123 _142124 s t s')). Qed.
Lemma lem8010805 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8010806 {_142122 _142124 : Type'} (t : Prop) : (term33 _142122 _142124 t) = t.
Proof. exact (@lem8010805 (type24 _142122 _142124) t). Qed.
Lemma lem8010807 {_142122 _142124 : Type'} : (term31 _142122 _142124) = True.
Proof. exact (@lem8010806 _142122 _142124 True). Qed.
Lemma lem8010808 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (t : type24 _142122 _142124) (s' : type24 _142122 _142123) : (term30 _142122 _142123 _142124 s t s') = True.
Proof. exact (TRANS (@lem8010803 _142122 _142123 _142124 s t s') (@lem8010807 _142122 _142124)). Qed.
Lemma lem8010809 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (t : type24 _142122 _142124) : (term34 _142122 _142123 _142124 s t) = (term29 _142122 _142123).
Proof. exact (fun_ext (fun s' : type24 _142122 _142123 => @lem8010808 _142122 _142123 _142124 s t s')). Qed.
Lemma lem8010810 {_142122 _142123 : Type'} : (@all ((cart _142122 _142123) -> Prop)) = (@all ((cart _142122 _142123) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142122 _142123) -> Prop))). Qed.
Lemma lem8010811 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (t : type24 _142122 _142124) : (term35 _142122 _142123 _142124 s t) = (term31 _142122 _142123).
Proof. exact (MK_COMB (@lem8010810 _142122 _142123) (@lem8010809 _142122 _142123 _142124 s t)). Qed.
Lemma lem8010813 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8010814 {_142122 _142123 : Type'} (t : Prop) : (term33 _142122 _142123 t) = t.
Proof. exact (@lem8010813 (type24 _142122 _142123) t). Qed.
Lemma lem8010815 {_142122 _142123 : Type'} : (term31 _142122 _142123) = True.
Proof. exact (@lem8010814 _142122 _142123 True). Qed.
Lemma lem8010816 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) (t : type24 _142122 _142124) : (term35 _142122 _142123 _142124 s t) = True.
Proof. exact (TRANS (@lem8010811 _142122 _142123 _142124 s t) (@lem8010815 _142122 _142123)). Qed.
Lemma lem8010817 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) : (term36 _142122 _142123 _142124 s) = (term29 _142122 _142124).
Proof. exact (fun_ext (fun t : type24 _142122 _142124 => @lem8010816 _142122 _142123 _142124 s t)). Qed.
Lemma lem8010818 {_142122 _142124 : Type'} : (@all ((cart _142122 _142124) -> Prop)) = (@all ((cart _142122 _142124) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142122 _142124) -> Prop))). Qed.
Lemma lem8010819 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) : (term37 _142122 _142123 _142124 s) = (term31 _142122 _142124).
Proof. exact (MK_COMB (@lem8010818 _142122 _142124) (@lem8010817 _142122 _142123 _142124 s)). Qed.
Lemma lem8010821 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8010822 {_142122 _142124 : Type'} (t : Prop) : (term33 _142122 _142124 t) = t.
Proof. exact (@lem8010821 (type24 _142122 _142124) t). Qed.
Lemma lem8010823 {_142122 _142124 : Type'} : (term31 _142122 _142124) = True.
Proof. exact (@lem8010822 _142122 _142124 True). Qed.
Lemma lem8010824 {_142122 _142123 _142124 : Type'} (s : type24 _142122 _142123) : (term37 _142122 _142123 _142124 s) = True.
Proof. exact (TRANS (@lem8010819 _142122 _142123 _142124 s) (@lem8010823 _142122 _142124)). Qed.
Lemma lem8010825 {_142122 _142123 _142124 : Type'} : (term38 _142122 _142123 _142124) = (term29 _142122 _142123).
Proof. exact (fun_ext (fun s : type24 _142122 _142123 => @lem8010824 _142122 _142123 _142124 s)). Qed.
Lemma lem8010826 {_142122 _142123 : Type'} : (@all ((cart _142122 _142123) -> Prop)) = (@all ((cart _142122 _142123) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142122 _142123) -> Prop))). Qed.
Lemma lem8010827 {_142122 _142123 _142124 : Type'} : (term39 _142122 _142123 _142124) = (term31 _142122 _142123).
Proof. exact (MK_COMB (@lem8010826 _142122 _142123) (@lem8010825 _142122 _142123 _142124)). Qed.
Lemma lem8010829 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8010830 {_142122 _142123 : Type'} (t : Prop) : (term33 _142122 _142123 t) = t.
Proof. exact (@lem8010829 (type24 _142122 _142123) t). Qed.
Lemma lem8010831 {_142122 _142123 : Type'} : (term31 _142122 _142123) = True.
Proof. exact (@lem8010830 _142122 _142123 True). Qed.
Lemma lem8010832 {_142122 _142123 _142124 : Type'} : (term39 _142122 _142123 _142124) = True.
Proof. exact (TRANS (@lem8010827 _142122 _142123 _142124) (@lem8010831 _142122 _142123)). Qed.
Lemma lem8010833 {_142122 _142123 _142124 : Type'} : True = (term39 _142122 _142123 _142124).
Proof. exact (SYM (@lem8010832 _142122 _142123 _142124)). Qed.
Lemma lem8010834 {_142122 _142123 _142124 : Type'} : term39 _142122 _142123 _142124.
Proof. exact (EQ_MP (@lem8010833 _142122 _142123 _142124) (@lem0)). Qed.
