Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ADMISSIBLE_COMB_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import admissible_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm4211_spec.
Lemma lem8101085 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem8101086 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem8101087 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem8101086 t1) (@lem8101085 t1)). Qed.
Lemma lem8101088 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem8101087 t1 t2). Qed.
Lemma lem8101089 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem8101090 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem8101089 t1 t2) (@lem8101088 t1 t2)). Qed.
Lemma lem8101091 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem8101090 t1 t2 t3). Qed.
Lemma lem8101092 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem8101093 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem8101092 t1 t2 t3) (@lem8101091 t1 t2 t3)). Qed.
Lemma lem8101094 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem8101093 t1 t2 t3)). Qed.
Lemma lem8101095 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : term7 _143449 _143452 _143456 _143457 _143462 p.
Proof. exact (@lem8093231 _143449 _143452 _143456 _143457 _143462 p). Qed.
Lemma lem8101096 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : (term7 _143449 _143452 _143456 _143457 _143462 p) = (term8 _143449 _143452 _143456 _143457 _143462 p).
Proof. exact (eq_refl (term7 _143449 _143452 _143456 _143457 _143462 p)). Qed.
Lemma lem8101097 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : term8 _143449 _143452 _143456 _143457 _143462 p.
Proof. exact (EQ_MP (@lem8101096 _143449 _143452 _143456 _143457 _143462 p) (@lem8101095 _143449 _143452 _143456 _143457 _143462 p)). Qed.
Lemma lem8101098 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : term9 _143449 _143452 _143456 _143457 _143462 p lt2.
Proof. exact (@lem8101097 _143449 _143452 _143456 _143457 _143462 p lt2). Qed.
Lemma lem8101099 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : (term9 _143449 _143452 _143456 _143457 _143462 p lt2) = (term10 _143449 _143452 _143456 _143457 _143462 p lt2).
Proof. exact (eq_refl (term9 _143449 _143452 _143456 _143457 _143462 p lt2)). Qed.
Lemma lem8101100 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : term10 _143449 _143452 _143456 _143457 _143462 p lt2.
Proof. exact (EQ_MP (@lem8101099 _143449 _143452 _143456 _143457 _143462 p lt2) (@lem8101098 _143449 _143452 _143456 _143457 _143462 p lt2)). Qed.
Lemma lem8101101 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : term11 _143449 _143452 _143456 _143457 _143462 p lt2 s.
Proof. exact (@lem8101100 _143449 _143452 _143456 _143457 _143462 p lt2 s). Qed.
Lemma lem8101102 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : (term11 _143449 _143452 _143456 _143457 _143462 p lt2 s) = (term12 _143449 _143452 _143456 _143457 _143462 p lt2 s).
Proof. exact (eq_refl (term11 _143449 _143452 _143456 _143457 _143462 p lt2 s)). Qed.
Lemma lem8101103 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : term12 _143449 _143452 _143456 _143457 _143462 p lt2 s.
Proof. exact (EQ_MP (@lem8101102 _143449 _143452 _143456 _143457 _143462 p lt2 s) (@lem8101101 _143449 _143452 _143456 _143457 _143462 p lt2 s)). Qed.
Lemma lem8101104 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : term13 _143449 _143452 _143456 _143457 _143462 p lt2 s t.
Proof. exact (@lem8101103 _143449 _143452 _143456 _143457 _143462 p lt2 s t). Qed.
Lemma lem8101105 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (term13 _143449 _143452 _143456 _143457 _143462 p lt2 s t) = ((@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term14 _143449 _143452 _143456 _143457 _143462 p lt2 s t)).
Proof. exact (eq_refl (term13 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8101130 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term15 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem8101131 (p : Prop) (q : Prop) (p' : Prop) : term16 p q p'.
Proof. exact (fun q' : Prop => @lem8101130 p q p' q'). Qed.
Lemma lem8101132 (p : Prop) (q : Prop) : term17 p q.
Proof. exact (fun p' : Prop => @lem8101131 p q p'). Qed.
Lemma lem8101133 {A B C D P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (g : type565 A B C D P) (y : type564 A B C P) : term18 A B C D P lt2 p s g y.
Proof. exact (@lem8101132 (term19 A B C D P g lt2 p s y) (term20 A B C D P lt2 p s g y)). Qed.
Lemma lem8101134 {A B C D P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (g : type565 A B C D P) (y : type564 A B C P) (p' : Prop) : term21 A B C D P lt2 p s g y p'.
Proof. exact (@lem8101133 A B C D P lt2 p s g y p'). Qed.
Lemma lem8101135 {A B C D P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (g : type565 A B C D P) (y : type564 A B C P) (p' : Prop) : (term21 A B C D P lt2 p s g y p') = (term22 A B C D P lt2 p s g y p').
Proof. exact (eq_refl (term21 A B C D P lt2 p s g y p')). Qed.
Lemma lem8101136 {A B C D P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (g : type565 A B C D P) (y : type564 A B C P) (p' : Prop) : term22 A B C D P lt2 p s g y p'.
Proof. exact (EQ_MP (@lem8101135 A B C D P lt2 p s g y p') (@lem8101134 A B C D P lt2 p s g y p')). Qed.
Lemma lem8101137 {A B C D P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (g : type565 A B C D P) (y : type564 A B C P) (p' : Prop) (q' : Prop) : term23 A B C D P lt2 p s g y p' q'.
Proof. exact (@lem8101136 A B C D P lt2 p s g y p' q'). Qed.
Lemma lem8101138 {A B C D P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (g : type565 A B C D P) (y : type564 A B C P) (p' : Prop) (q' : Prop) : (term23 A B C D P lt2 p s g y p' q') = (term24 A B C D P lt2 p s g y p' q').
Proof. exact (eq_refl (term23 A B C D P lt2 p s g y p' q')). Qed.
Lemma lem8101139 {A B C D P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (g : type565 A B C D P) (y : type564 A B C P) (p' : Prop) (q' : Prop) : term24 A B C D P lt2 p s g y p' q'.
Proof. exact (EQ_MP (@lem8101138 A B C D P lt2 p s g y p' q') (@lem8101137 A B C D P lt2 p s g y p' q')). Qed.
Lemma lem8101143 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term14 _143449 _143452 _143456 _143457 _143462 p lt2 s t).
Proof. exact (EQ_MP (@lem8101105 _143449 _143452 _143456 _143457 _143462 p lt2 s t) (@lem8101104 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8101144 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type565 A B C D P) : (@admissible A B A (C -> D) P lt2 p s t) = (term25 A B C D P p lt2 s t).
Proof. exact (@lem8101143 A B A (C -> D) P p lt2 s t). Qed.
Lemma lem8101145 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) : (@admissible A B A (C -> D) P lt2 p s g) = (term25 A B C D P p lt2 s g).
Proof. exact (@lem8101144 A B C D P p lt2 s g). Qed.
Lemma lem8101271 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8101272 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) : (term26 A B C D P lt2 p s g) = (term27 A B C D P p lt2 s g).
Proof. exact (MK_COMB (@lem8101271) (@lem8101145 A B C D P p lt2 s g)). Qed.
Lemma lem8101399 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term14 _143449 _143452 _143456 _143457 _143462 p lt2 s t).
Proof. exact (EQ_MP (@lem8101105 _143449 _143452 _143456 _143457 _143462 p lt2 s t) (@lem8101104 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8101400 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type564 A B C P) : (@admissible A B A C P lt2 p s t) = (term28 A B C P p lt2 s t).
Proof. exact (@lem8101399 A B A C P p lt2 s t). Qed.
Lemma lem8101401 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (@admissible A B A C P lt2 p s y) = (term28 A B C P p lt2 s y).
Proof. exact (@lem8101400 A B C P p lt2 s y). Qed.
Lemma lem8101527 {A B C D P : Type'} (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term19 A B C D P g lt2 p s y) = (term29 A B C D P g p lt2 s y).
Proof. exact (MK_COMB (@lem8101272 A B C D P p lt2 s g) (@lem8101401 A B C P p lt2 s y)). Qed.
Lemma lem8101780 {A B C D P : Type'} (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) (q' : Prop) : term30 A B C D P g p lt2 s y q'.
Proof. exact (@lem8101139 A B C D P lt2 p s g y (term29 A B C D P g p lt2 s y) q'). Qed.
Lemma lem8101781 {A B C D P : Type'} (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) (q' : Prop) : term31 A B C D P g p lt2 s y q'.
Proof. exact (@lem8101780 A B C D P g p lt2 s y q' (@lem8101527 A B C D P g p lt2 s y)). Qed.
Lemma lem8101818 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term14 _143449 _143452 _143456 _143457 _143462 p lt2 s t).
Proof. exact (EQ_MP (@lem8101105 _143449 _143452 _143456 _143457 _143462 p lt2 s t) (@lem8101104 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8101819 {A B D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type564 A B D P) : (@admissible A B A D P lt2 p s t) = (term28 A B D P p lt2 s t).
Proof. exact (@lem8101818 A B A D P p lt2 s t). Qed.
Lemma lem8101820 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) (y : type564 A B C P) : (term20 A B C D P lt2 p s g y) = (term32 A B C D P p lt2 s g y).
Proof. exact (@lem8101819 A B D P p lt2 s (term33 A B C D P g y)). Qed.
Lemma lem8101836 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term15 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem8101837 (p : Prop) (q : Prop) (p' : Prop) : term16 p q p'.
Proof. exact (fun q' : Prop => @lem8101836 p q p' q'). Qed.
Lemma lem8101838 (p : Prop) (q : Prop) : term17 p q.
Proof. exact (fun p' : Prop => @lem8101837 p q p'). Qed.
Lemma lem8101839 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : term34 A B C D P p lt2 s f g y g' a.
Proof. exact (@lem8101838 (term35 A B P p lt2 s a f g') ((term36 A B C D P g y f a) = (term36 A B C D P g y g' a))). Qed.
Lemma lem8101840 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) (p' : Prop) : term37 A B C D P p lt2 s f g y g' a p'.
Proof. exact (@lem8101839 A B C D P p lt2 s f g y g' a p'). Qed.
Lemma lem8101841 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) (p' : Prop) : (term37 A B C D P p lt2 s f g y g' a p') = (term38 A B C D P p lt2 s f g y g' a p').
Proof. exact (eq_refl (term37 A B C D P p lt2 s f g y g' a p')). Qed.
Lemma lem8101842 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) (p' : Prop) : term38 A B C D P p lt2 s f g y g' a p'.
Proof. exact (EQ_MP (@lem8101841 A B C D P p lt2 s f g y g' a p') (@lem8101840 A B C D P p lt2 s f g y g' a p')). Qed.
Lemma lem8101843 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) (p' : Prop) (q' : Prop) : term39 A B C D P p lt2 s f g y g' a p' q'.
Proof. exact (@lem8101842 A B C D P p lt2 s f g y g' a p' q'). Qed.
Lemma lem8101844 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) (p' : Prop) (q' : Prop) : (term39 A B C D P p lt2 s f g y g' a p' q') = (term40 A B C D P p lt2 s f g y g' a p' q').
Proof. exact (eq_refl (term39 A B C D P p lt2 s f g y g' a p' q')). Qed.
Lemma lem8101845 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) (p' : Prop) (q' : Prop) : term40 A B C D P p lt2 s f g y g' a p' q'.
Proof. exact (EQ_MP (@lem8101844 A B C D P p lt2 s f g y g' a p' q') (@lem8101843 A B C D P p lt2 s f g y g' a p' q')). Qed.
Lemma lem8101881 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term35 A B P p lt2 s a f g) = (term35 A B P p lt2 s a f g).
Proof. exact (eq_refl (term35 A B P p lt2 s a f g)). Qed.
Lemma lem8101882 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (q' : Prop) : term41 A B C D P g y p lt2 s a f g' q'.
Proof. exact (@lem8101845 A B C D P p lt2 s f g y g' a (term35 A B P p lt2 s a f g') q'). Qed.
Lemma lem8101883 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (q' : Prop) : term42 A B C D P g y p lt2 s a f g' q'.
Proof. exact (@lem8101882 A B C D P g y p lt2 s a f g' q' (@lem8101881 A B P p lt2 s a f g')). Qed.
Lemma lem8101906 {A B : Type'} (f : A -> B) (y : A) : (term43 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8101907 {A B D P : Type'} (f : type564 A B D P) (y : A -> B) : (term44 A B D P f y) = (f y).
Proof. exact (@lem8101906 (A -> B) (P -> D) f y). Qed.
Lemma lem8101908 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (f : A -> B) : (term45 A B C D P g y f) = (term46 A B C D P g y f).
Proof. exact (@lem8101907 A B D P (term33 A B C D P g y) f). Qed.
Lemma lem8101909 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (f : A -> B) : (term46 A B C D P g y f) = (term47 A B C D P g y f).
Proof. exact (eq_refl (term46 A B C D P g y f)). Qed.
Lemma lem8101910 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) : (term48 A B C D P g y) = (term33 A B C D P g y).
Proof. exact (fun_ext (fun f : A -> B => @lem8101909 A B C D P g y f)). Qed.
Lemma lem8101911 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8101912 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (f : A -> B) : (term45 A B C D P g y f) = (term46 A B C D P g y f).
Proof. exact (MK_COMB (@lem8101910 A B C D P g y) (@lem8101911 A B f)). Qed.
Lemma lem8101913 {D P : Type'} : (@eq (P -> D)) = (@eq (P -> D)).
Proof. exact (eq_refl (@eq (P -> D))). Qed.
Lemma lem8101914 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (f : A -> B) : (term49 A B C D P g y f) = (term50 A B C D P g y f).
Proof. exact (MK_COMB (@lem8101913 D P) (@lem8101912 A B C D P g y f)). Qed.
Lemma lem8101915 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (f : A -> B) : (term46 A B C D P g y f) = (term47 A B C D P g y f).
Proof. exact (eq_refl (term46 A B C D P g y f)). Qed.
Lemma lem8101916 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (f : A -> B) : ((term45 A B C D P g y f) = (term46 A B C D P g y f)) = ((term46 A B C D P g y f) = (term47 A B C D P g y f)).
Proof. exact (MK_COMB (@lem8101914 A B C D P g y f) (@lem8101915 A B C D P g y f)). Qed.
Lemma lem8101917 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (f : A -> B) : (term46 A B C D P g y f) = (term47 A B C D P g y f).
Proof. exact (EQ_MP (@lem8101916 A B C D P g y f) (@lem8101908 A B C D P g y f)). Qed.
Lemma lem8101926 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8101927 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (f : A -> B) (a : P) : (term36 A B C D P g y f a) = (term51 A B C D P g y f a).
Proof. exact (MK_COMB (@lem8101917 A B C D P g y f) (@lem8101926 P a)). Qed.
Lemma lem8101929 {A B : Type'} (f : A -> B) (y : A) : (term43 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8101930 {D P : Type'} (f : P -> D) (y : P) : (term52 D P f y) = (f y).
Proof. exact (@lem8101929 P D f y). Qed.
Lemma lem8101931 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (f : A -> B) (a : P) : (term53 A B C D P g y f a) = (term51 A B C D P g y f a).
Proof. exact (@lem8101930 D P (term47 A B C D P g y f) a). Qed.
Lemma lem8101932 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (f : A -> B) (x : P) : (term51 A B C D P g y f x) = (term54 A B C D P g y f x).
Proof. exact (eq_refl (term51 A B C D P g y f x)). Qed.
Lemma lem8101933 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (f : A -> B) : (term55 A B C D P g y f) = (term47 A B C D P g y f).
Proof. exact (fun_ext (fun x : P => @lem8101932 A B C D P g y f x)). Qed.
Lemma lem8101934 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8101935 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (f : A -> B) (a : P) : (term53 A B C D P g y f a) = (term51 A B C D P g y f a).
Proof. exact (MK_COMB (@lem8101933 A B C D P g y f) (@lem8101934 P a)). Qed.
Lemma lem8101936 {D : Type'} : (@eq D) = (@eq D).
Proof. exact (eq_refl (@eq D)). Qed.
Lemma lem8101937 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (f : A -> B) (a : P) : (term56 A B C D P g y f a) = (term57 A B C D P g y f a).
Proof. exact (MK_COMB (@lem8101936 D) (@lem8101935 A B C D P g y f a)). Qed.
Lemma lem8101938 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (f : A -> B) (a : P) : (term51 A B C D P g y f a) = (term54 A B C D P g y f a).
Proof. exact (eq_refl (term51 A B C D P g y f a)). Qed.
Lemma lem8101939 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (f : A -> B) (a : P) : ((term53 A B C D P g y f a) = (term51 A B C D P g y f a)) = ((term51 A B C D P g y f a) = (term54 A B C D P g y f a)).
Proof. exact (MK_COMB (@lem8101937 A B C D P g y f a) (@lem8101938 A B C D P g y f a)). Qed.
Lemma lem8101940 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (f : A -> B) (a : P) : (term51 A B C D P g y f a) = (term54 A B C D P g y f a).
Proof. exact (EQ_MP (@lem8101939 A B C D P g y f a) (@lem8101931 A B C D P g y f a)). Qed.
Lemma lem8101947 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (f : A -> B) (a : P) : (term36 A B C D P g y f a) = (term54 A B C D P g y f a).
Proof. exact (TRANS (@lem8101927 A B C D P g y f a) (@lem8101940 A B C D P g y f a)). Qed.
Lemma lem8101948 {D : Type'} : (@eq D) = (@eq D).
Proof. exact (eq_refl (@eq D)). Qed.
Lemma lem8101949 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (f : A -> B) (a : P) : (term58 A B C D P g y f a) = (term59 A B C D P g y f a).
Proof. exact (MK_COMB (@lem8101948 D) (@lem8101947 A B C D P g y f a)). Qed.
Lemma lem8101957 {A B : Type'} (f : A -> B) (y : A) : (term43 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8101958 {A B D P : Type'} (f : type564 A B D P) (y : A -> B) : (term44 A B D P f y) = (f y).
Proof. exact (@lem8101957 (A -> B) (P -> D) f y). Qed.
Lemma lem8101959 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) : (term45 A B C D P g y g') = (term46 A B C D P g y g').
Proof. exact (@lem8101958 A B D P (term33 A B C D P g y) g'). Qed.
Lemma lem8101960 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (f : A -> B) : (term46 A B C D P g y f) = (term47 A B C D P g y f).
Proof. exact (eq_refl (term46 A B C D P g y f)). Qed.
Lemma lem8101961 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) : (term48 A B C D P g y) = (term33 A B C D P g y).
Proof. exact (fun_ext (fun f : A -> B => @lem8101960 A B C D P g y f)). Qed.
Lemma lem8101962 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8101963 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) : (term45 A B C D P g y g') = (term46 A B C D P g y g').
Proof. exact (MK_COMB (@lem8101961 A B C D P g y) (@lem8101962 A B g')). Qed.
Lemma lem8101964 {D P : Type'} : (@eq (P -> D)) = (@eq (P -> D)).
Proof. exact (eq_refl (@eq (P -> D))). Qed.
Lemma lem8101965 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) : (term49 A B C D P g y g') = (term50 A B C D P g y g').
Proof. exact (MK_COMB (@lem8101964 D P) (@lem8101963 A B C D P g y g')). Qed.
Lemma lem8101966 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) : (term46 A B C D P g y g') = (term47 A B C D P g y g').
Proof. exact (eq_refl (term46 A B C D P g y g')). Qed.
Lemma lem8101967 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) : ((term45 A B C D P g y g') = (term46 A B C D P g y g')) = ((term46 A B C D P g y g') = (term47 A B C D P g y g')).
Proof. exact (MK_COMB (@lem8101965 A B C D P g y g') (@lem8101966 A B C D P g y g')). Qed.
Lemma lem8101968 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) : (term46 A B C D P g y g') = (term47 A B C D P g y g').
Proof. exact (EQ_MP (@lem8101967 A B C D P g y g') (@lem8101959 A B C D P g y g')). Qed.
Lemma lem8101977 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8101978 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term36 A B C D P g y g' a) = (term51 A B C D P g y g' a).
Proof. exact (MK_COMB (@lem8101968 A B C D P g y g') (@lem8101977 P a)). Qed.
Lemma lem8101980 {A B : Type'} (f : A -> B) (y : A) : (term43 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8101981 {D P : Type'} (f : P -> D) (y : P) : (term52 D P f y) = (f y).
Proof. exact (@lem8101980 P D f y). Qed.
Lemma lem8101982 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term53 A B C D P g y g' a) = (term51 A B C D P g y g' a).
Proof. exact (@lem8101981 D P (term47 A B C D P g y g') a). Qed.
Lemma lem8101983 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (x : P) : (term51 A B C D P g y g' x) = (term54 A B C D P g y g' x).
Proof. exact (eq_refl (term51 A B C D P g y g' x)). Qed.
Lemma lem8101984 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) : (term55 A B C D P g y g') = (term47 A B C D P g y g').
Proof. exact (fun_ext (fun x : P => @lem8101983 A B C D P g y g' x)). Qed.
Lemma lem8101985 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8101986 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term53 A B C D P g y g' a) = (term51 A B C D P g y g' a).
Proof. exact (MK_COMB (@lem8101984 A B C D P g y g') (@lem8101985 P a)). Qed.
Lemma lem8101987 {D : Type'} : (@eq D) = (@eq D).
Proof. exact (eq_refl (@eq D)). Qed.
Lemma lem8101988 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term56 A B C D P g y g' a) = (term57 A B C D P g y g' a).
Proof. exact (MK_COMB (@lem8101987 D) (@lem8101986 A B C D P g y g' a)). Qed.
Lemma lem8101989 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term51 A B C D P g y g' a) = (term54 A B C D P g y g' a).
Proof. exact (eq_refl (term51 A B C D P g y g' a)). Qed.
Lemma lem8101990 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : ((term53 A B C D P g y g' a) = (term51 A B C D P g y g' a)) = ((term51 A B C D P g y g' a) = (term54 A B C D P g y g' a)).
Proof. exact (MK_COMB (@lem8101988 A B C D P g y g' a) (@lem8101989 A B C D P g y g' a)). Qed.
Lemma lem8101991 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term51 A B C D P g y g' a) = (term54 A B C D P g y g' a).
Proof. exact (EQ_MP (@lem8101990 A B C D P g y g' a) (@lem8101982 A B C D P g y g' a)). Qed.
Lemma lem8102000 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term36 A B C D P g y g' a) = (term54 A B C D P g y g' a).
Proof. exact (TRANS (@lem8101978 A B C D P g y g' a) (@lem8101991 A B C D P g y g' a)). Qed.
Lemma lem8102001 {A B C D P : Type'} (f : A -> B) (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : ((term36 A B C D P g y f a) = (term36 A B C D P g y g' a)) = ((term54 A B C D P g y f a) = (term54 A B C D P g y g' a)).
Proof. exact (MK_COMB (@lem8101949 A B C D P g y f a) (@lem8102000 A B C D P g y g' a)). Qed.
Lemma lem8102018 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : term60 A B C D P p lt2 s f g y g' a.
Proof. exact (fun h0 : term35 A B P p lt2 s a f g' => @lem8102001 A B C D P f g y g' a). Qed.
Lemma lem8102019 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : term61 A B C D P p lt2 s f g y g' a.
Proof. exact (@lem8101883 A B C D P g y p lt2 s a f g' ((term54 A B C D P g y f a) = (term54 A B C D P g y g' a))). Qed.
Lemma lem8102020 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term62 A B C D P p lt2 s f g y g' a) = (term63 A B C D P p lt2 s f g y g' a).
Proof. exact (@lem8102019 A B C D P p lt2 s f g y g' a (@lem8102018 A B C D P p lt2 s f g y g' a)). Qed.
Lemma lem8102162 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) : (term64 A B C D P p lt2 s f g y g') = (term65 A B C D P p lt2 s f g y g').
Proof. exact (fun_ext (fun a : P => @lem8102020 A B C D P p lt2 s f g y g' a)). Qed.
Lemma lem8102304 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8102305 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) : (term66 A B C D P p lt2 s f g y g') = (term67 A B C D P p lt2 s f g y g').
Proof. exact (MK_COMB (@lem8102304 P) (@lem8102162 A B C D P p lt2 s f g y g')). Qed.
Lemma lem8102451 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (y : type564 A B C P) : (term68 A B C D P p lt2 s f g y) = (term69 A B C D P p lt2 s f g y).
Proof. exact (fun_ext (fun g' : A -> B => @lem8102305 A B C D P p lt2 s f g y g')). Qed.
Lemma lem8102597 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8102598 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (y : type564 A B C P) : (term70 A B C D P p lt2 s f g y) = (term71 A B C D P p lt2 s f g y).
Proof. exact (MK_COMB (@lem8102597 A B) (@lem8102451 A B C D P p lt2 s f g y)). Qed.
Lemma lem8102748 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) (y : type564 A B C P) : (term72 A B C D P p lt2 s g y) = (term73 A B C D P p lt2 s g y).
Proof. exact (fun_ext (fun f : A -> B => @lem8102598 A B C D P p lt2 s f g y)). Qed.
Lemma lem8102898 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8102899 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) (y : type564 A B C P) : (term32 A B C D P p lt2 s g y) = (term74 A B C D P p lt2 s g y).
Proof. exact (MK_COMB (@lem8102898 A B) (@lem8102748 A B C D P p lt2 s g y)). Qed.
Lemma lem8103053 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) (y : type564 A B C P) : (term20 A B C D P lt2 p s g y) = (term74 A B C D P p lt2 s g y).
Proof. exact (TRANS (@lem8101820 A B C D P p lt2 s g y) (@lem8102899 A B C D P p lt2 s g y)). Qed.
Lemma lem8103054 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) (y : type564 A B C P) : term75 A B C D P p lt2 s g y.
Proof. exact (fun h0 : term29 A B C D P g p lt2 s y => @lem8103053 A B C D P p lt2 s g y). Qed.
Lemma lem8103055 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) (y : type564 A B C P) : term76 A B C D P p lt2 s g y.
Proof. exact (@lem8101781 A B C D P g p lt2 s y (term74 A B C D P p lt2 s g y)). Qed.
Lemma lem8103056 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) (y : type564 A B C P) : (term77 A B C D P lt2 p s g y) = (term78 A B C D P p lt2 s g y).
Proof. exact (@lem8103055 A B C D P p lt2 s g y (@lem8103054 A B C D P p lt2 s g y)). Qed.
Lemma lem8103894 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) : (term79 A B C D P lt2 p s g) = (term80 A B C D P p lt2 s g).
Proof. exact (fun_ext (fun y : type564 A B C P => @lem8103056 A B C D P p lt2 s g y)). Qed.
Lemma lem8104732 {A B C P : Type'} : (@all ((A -> B) -> P -> C)) = (@all ((A -> B) -> P -> C)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> C))). Qed.
Lemma lem8104733 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) : (term81 A B C D P lt2 p s g) = (term82 A B C D P p lt2 s g).
Proof. exact (MK_COMB (@lem8104732 A B C P) (@lem8103894 A B C D P p lt2 s g)). Qed.
Lemma lem8105575 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) : (term83 A B C D P lt2 p s) = (term84 A B C D P p lt2 s).
Proof. exact (fun_ext (fun g : type565 A B C D P => @lem8104733 A B C D P p lt2 s g)). Qed.
Lemma lem8106417 {A B C D P : Type'} : (@all ((A -> B) -> P -> C -> D)) = (@all ((A -> B) -> P -> C -> D)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> C -> D))). Qed.
Lemma lem8106418 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) : (term85 A B C D P lt2 p s) = (term86 A B C D P p lt2 s).
Proof. exact (MK_COMB (@lem8106417 A B C D P) (@lem8105575 A B C D P p lt2 s)). Qed.
Lemma lem8107264 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) : (term87 A B C D P lt2 p) = (term88 A B C D P p lt2).
Proof. exact (fun_ext (fun s : P -> A => @lem8106418 A B C D P p lt2 s)). Qed.
Lemma lem8108110 {A P : Type'} : (@all (P -> A)) = (@all (P -> A)).
Proof. exact (eq_refl (@all (P -> A))). Qed.
Lemma lem8108111 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) : (term89 A B C D P lt2 p) = (term90 A B C D P p lt2).
Proof. exact (MK_COMB (@lem8108110 A P) (@lem8107264 A B C D P p lt2)). Qed.
Lemma lem8108961 {A B C D P : Type'} (lt2 : type1402 A) : (term91 A B C D P lt2) = (term92 A B C D P lt2).
Proof. exact (fun_ext (fun p : type560 A B P => @lem8108111 A B C D P p lt2)). Qed.
Lemma lem8109811 {A B P : Type'} : (@all ((A -> B) -> P -> Prop)) = (@all ((A -> B) -> P -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> Prop))). Qed.
Lemma lem8109812 {A B C D P : Type'} (lt2 : type1402 A) : (term93 A B C D P lt2) = (term94 A B C D P lt2).
Proof. exact (MK_COMB (@lem8109811 A B P) (@lem8108961 A B C D P lt2)). Qed.
Lemma lem8110666 {A B C D P : Type'} : (term95 A B C D P) = (term96 A B C D P).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem8109812 A B C D P lt2)). Qed.
Lemma lem8111520 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem8111521 {A B C D P : Type'} : (term97 A B C D P) = (term98 A B C D P).
Proof. exact (MK_COMB (@lem8111520 A) (@lem8110666 A B C D P)). Qed.
Lemma lem8112379 {A B C D P : Type'} : (term98 A B C D P) = (term97 A B C D P).
Proof. exact (SYM (@lem8111521 A B C D P)). Qed.
Lemma lem8112381 (p : Prop) : p = (term99 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8112382 {A B C D P : Type'} : (term98 A B C D P) = (term100 A B C D P).
Proof. exact (@lem8112381 (term98 A B C D P)). Qed.
Lemma lem8112383 {A B C D P : Type'} : (term100 A B C D P) = (term98 A B C D P).
Proof. exact (SYM (@lem8112382 A B C D P)). Qed.
Lemma lem8112384 {A B C D P : Type'} (h1 : term101 A B C D P) : term101 A B C D P.
Proof. exact (h1). Qed.
Lemma lem8112387 {A B C D P : Type'} (h1 : term100 A B C D P) : term100 A B C D P.
Proof. exact (h1). Qed.
Lemma lem8112388 {A B C D P : Type'} : term102 A B C D P.
Proof. exact (fun h0 : term100 A B C D P => @lem8112387 A B C D P h0). Qed.
Lemma lem8112389 {A B C D P : Type'} (h1 : term102 A B C D P) : term102 A B C D P.
Proof. exact (h1). Qed.
Lemma lem8112390 {A B C D P : Type'} (h1 : term100 A B C D P) : term100 A B C D P.
Proof. exact (h1). Qed.
Lemma lem8112391 {A B C D P : Type'} (h1 : term100 A B C D P) (h2 : term102 A B C D P) : term100 A B C D P.
Proof. exact (@lem8112389 A B C D P h2 (@lem8112390 A B C D P h1)). Qed.
Lemma lem8112392 {A B C D P : Type'} (h1 : term100 A B C D P) : term103 A B C D P.
Proof. exact (fun h0 : term102 A B C D P => @lem8112391 A B C D P h1 h0). Qed.
Lemma lem8112393 {A B C D P : Type'} (h1 : term102 A B C D P) : term102 A B C D P.
Proof. exact (h1). Qed.
Lemma lem8112394 {A B C D P : Type'} (h1 : term100 A B C D P) (h2 : term102 A B C D P) : term100 A B C D P.
Proof. exact (@lem8112392 A B C D P h1 (@lem8112393 A B C D P h2)). Qed.
Lemma lem8112395 {A B C D P : Type'} (h1 : term102 A B C D P) : term102 A B C D P.
Proof. exact (fun h0 : term100 A B C D P => @lem8112394 A B C D P h0 h1). Qed.
Lemma lem8112396 {A B C D P : Type'} : term104 A B C D P.
Proof. exact (fun h0 : term102 A B C D P => @lem8112395 A B C D P h0). Qed.
Lemma lem8112399 {A B C D P : Type'} : term102 A B C D P.
Proof. exact (@lem8112396 A B C D P (@lem8112388 A B C D P)). Qed.
Lemma lem8112400 {A B C D P : Type'} : term102 A B C D P.
Proof. exact (@lem8112399 A B C D P). Qed.
Lemma lem8112402 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem8112403 {A B C D P : Type'} : (term100 A B C D P) = (term105 A B C D P).
Proof. exact (@lem8112402 (term101 A B C D P)). Qed.
Lemma lem8112405 (t : Prop) : (term106 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem8112406 {A B C D P : Type'} : (term105 A B C D P) = (term98 A B C D P).
Proof. exact (@lem8112405 (term98 A B C D P)). Qed.
Lemma lem8112507 {A B C D P : Type'} : (term100 A B C D P) = (term98 A B C D P).
Proof. exact (TRANS (@lem8112403 A B C D P) (@lem8112406 A B C D P)). Qed.
Lemma lem8112508 {A B C D P : Type'} (f : A -> B) (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : ((term54 A B C D P g y f a) = (term54 A B C D P g y g' a)) = ((term54 A B C D P g y f a) = (term54 A B C D P g y g' a)).
Proof. exact (eq_refl ((term54 A B C D P g y f a) = (term54 A B C D P g y g' a))). Qed.
Lemma lem8112513 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term107 A B P lt2 s a f g z) = (term107 A B P lt2 s a f g z).
Proof. exact (eq_refl (term107 A B P lt2 s a f g z)). Qed.
Lemma lem8112514 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term108 A B P lt2 s a f g) = (term108 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8112513 A B P lt2 s a f g z)). Qed.
Lemma lem8112515 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8112516 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term109 A B P lt2 s a f g) = (term109 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8112515 A) (@lem8112514 A B P lt2 s a f g)). Qed.
Lemma lem8112519 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term110 A B P p g a) = (term110 A B P p g a).
Proof. exact (eq_refl (term110 A B P p g a)). Qed.
Lemma lem8112520 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term111 A B P p lt2 s a f g) = (term111 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8112519 A B P p g a) (@lem8112516 A B P lt2 s a f g)). Qed.
Lemma lem8112523 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term110 A B P p f a) = (term110 A B P p f a).
Proof. exact (eq_refl (term110 A B P p f a)). Qed.
Lemma lem8112524 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term35 A B P p lt2 s a f g) = (term35 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8112523 A B P p f a) (@lem8112520 A B P p lt2 s a f g)). Qed.
Lemma lem8112525 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8112526 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term112 A B P p lt2 s a f g) = (term112 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8112525) (@lem8112524 A B P p lt2 s a f g)). Qed.
Lemma lem8112527 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term63 A B C D P p lt2 s f g y g' a) = (term63 A B C D P p lt2 s f g y g' a).
Proof. exact (MK_COMB (@lem8112526 A B P p lt2 s a f g') (@lem8112508 A B C D P f g y g' a)). Qed.
Lemma lem8112528 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) : (term65 A B C D P p lt2 s f g y g') = (term65 A B C D P p lt2 s f g y g').
Proof. exact (fun_ext (fun a : P => @lem8112527 A B C D P p lt2 s f g y g' a)). Qed.
Lemma lem8112529 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8112530 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) : (term67 A B C D P p lt2 s f g y g') = (term67 A B C D P p lt2 s f g y g').
Proof. exact (MK_COMB (@lem8112529 P) (@lem8112528 A B C D P p lt2 s f g y g')). Qed.
Lemma lem8112531 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (y : type564 A B C P) : (term69 A B C D P p lt2 s f g y) = (term69 A B C D P p lt2 s f g y).
Proof. exact (fun_ext (fun g' : A -> B => @lem8112530 A B C D P p lt2 s f g y g')). Qed.
Lemma lem8112532 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8112533 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (y : type564 A B C P) : (term71 A B C D P p lt2 s f g y) = (term71 A B C D P p lt2 s f g y).
Proof. exact (MK_COMB (@lem8112532 A B) (@lem8112531 A B C D P p lt2 s f g y)). Qed.
Lemma lem8112534 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) (y : type564 A B C P) : (term73 A B C D P p lt2 s g y) = (term73 A B C D P p lt2 s g y).
Proof. exact (fun_ext (fun f : A -> B => @lem8112533 A B C D P p lt2 s f g y)). Qed.
Lemma lem8112535 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8112536 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) (y : type564 A B C P) : (term74 A B C D P p lt2 s g y) = (term74 A B C D P p lt2 s g y).
Proof. exact (MK_COMB (@lem8112535 A B) (@lem8112534 A B C D P p lt2 s g y)). Qed.
Lemma lem8112537 {A B C P : Type'} (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : ((y f a) = (y g a)) = ((y f a) = (y g a)).
Proof. exact (eq_refl ((y f a) = (y g a))). Qed.
Lemma lem8112542 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term107 A B P lt2 s a f g z) = (term107 A B P lt2 s a f g z).
Proof. exact (eq_refl (term107 A B P lt2 s a f g z)). Qed.
Lemma lem8112543 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term108 A B P lt2 s a f g) = (term108 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8112542 A B P lt2 s a f g z)). Qed.
Lemma lem8112544 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8112545 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term109 A B P lt2 s a f g) = (term109 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8112544 A) (@lem8112543 A B P lt2 s a f g)). Qed.
Lemma lem8112548 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term110 A B P p g a) = (term110 A B P p g a).
Proof. exact (eq_refl (term110 A B P p g a)). Qed.
Lemma lem8112549 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term111 A B P p lt2 s a f g) = (term111 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8112548 A B P p g a) (@lem8112545 A B P lt2 s a f g)). Qed.
Lemma lem8112552 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term110 A B P p f a) = (term110 A B P p f a).
Proof. exact (eq_refl (term110 A B P p f a)). Qed.
Lemma lem8112553 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term35 A B P p lt2 s a f g) = (term35 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8112552 A B P p f a) (@lem8112549 A B P p lt2 s a f g)). Qed.
Lemma lem8112554 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8112555 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term112 A B P p lt2 s a f g) = (term112 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8112554) (@lem8112553 A B P p lt2 s a f g)). Qed.
Lemma lem8112556 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term113 A B C P p lt2 s f y g a) = (term113 A B C P p lt2 s f y g a).
Proof. exact (MK_COMB (@lem8112555 A B P p lt2 s a f g) (@lem8112537 A B C P f y g a)). Qed.
Lemma lem8112557 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term114 A B C P p lt2 s f y g) = (term114 A B C P p lt2 s f y g).
Proof. exact (fun_ext (fun a : P => @lem8112556 A B C P p lt2 s f y g a)). Qed.
Lemma lem8112558 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8112559 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term115 A B C P p lt2 s f y g) = (term115 A B C P p lt2 s f y g).
Proof. exact (MK_COMB (@lem8112558 P) (@lem8112557 A B C P p lt2 s f y g)). Qed.
Lemma lem8112560 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term116 A B C P p lt2 s f y) = (term116 A B C P p lt2 s f y).
Proof. exact (fun_ext (fun g : A -> B => @lem8112559 A B C P p lt2 s f y g)). Qed.
Lemma lem8112561 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8112562 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term117 A B C P p lt2 s f y) = (term117 A B C P p lt2 s f y).
Proof. exact (MK_COMB (@lem8112561 A B) (@lem8112560 A B C P p lt2 s f y)). Qed.
Lemma lem8112563 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term118 A B C P p lt2 s y) = (term118 A B C P p lt2 s y).
Proof. exact (fun_ext (fun f : A -> B => @lem8112562 A B C P p lt2 s f y)). Qed.
Lemma lem8112564 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8112565 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term28 A B C P p lt2 s y) = (term28 A B C P p lt2 s y).
Proof. exact (MK_COMB (@lem8112564 A B) (@lem8112563 A B C P p lt2 s y)). Qed.
Lemma lem8112566 {A B C D P : Type'} (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : ((g f a) = (g g' a)) = ((g f a) = (g g' a)).
Proof. exact (eq_refl ((g f a) = (g g' a))). Qed.
Lemma lem8112571 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term107 A B P lt2 s a f g z) = (term107 A B P lt2 s a f g z).
Proof. exact (eq_refl (term107 A B P lt2 s a f g z)). Qed.
Lemma lem8112572 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term108 A B P lt2 s a f g) = (term108 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8112571 A B P lt2 s a f g z)). Qed.
Lemma lem8112573 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8112574 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term109 A B P lt2 s a f g) = (term109 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8112573 A) (@lem8112572 A B P lt2 s a f g)). Qed.
Lemma lem8112577 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term110 A B P p g a) = (term110 A B P p g a).
Proof. exact (eq_refl (term110 A B P p g a)). Qed.
Lemma lem8112578 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term111 A B P p lt2 s a f g) = (term111 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8112577 A B P p g a) (@lem8112574 A B P lt2 s a f g)). Qed.
Lemma lem8112581 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term110 A B P p f a) = (term110 A B P p f a).
Proof. exact (eq_refl (term110 A B P p f a)). Qed.
Lemma lem8112582 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term35 A B P p lt2 s a f g) = (term35 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8112581 A B P p f a) (@lem8112578 A B P p lt2 s a f g)). Qed.
Lemma lem8112583 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8112584 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term112 A B P p lt2 s a f g) = (term112 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8112583) (@lem8112582 A B P p lt2 s a f g)). Qed.
Lemma lem8112585 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : (term119 A B C D P p lt2 s f g g' a) = (term119 A B C D P p lt2 s f g g' a).
Proof. exact (MK_COMB (@lem8112584 A B P p lt2 s a f g') (@lem8112566 A B C D P f g g' a)). Qed.
Lemma lem8112586 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) : (term120 A B C D P p lt2 s f g g') = (term120 A B C D P p lt2 s f g g').
Proof. exact (fun_ext (fun a : P => @lem8112585 A B C D P p lt2 s f g g' a)). Qed.
Lemma lem8112587 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8112588 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) : (term121 A B C D P p lt2 s f g g') = (term121 A B C D P p lt2 s f g g').
Proof. exact (MK_COMB (@lem8112587 P) (@lem8112586 A B C D P p lt2 s f g g')). Qed.
Lemma lem8112589 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) : (term122 A B C D P p lt2 s f g) = (term122 A B C D P p lt2 s f g).
Proof. exact (fun_ext (fun g' : A -> B => @lem8112588 A B C D P p lt2 s f g g')). Qed.
Lemma lem8112590 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8112591 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) : (term123 A B C D P p lt2 s f g) = (term123 A B C D P p lt2 s f g).
Proof. exact (MK_COMB (@lem8112590 A B) (@lem8112589 A B C D P p lt2 s f g)). Qed.
Lemma lem8112592 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) : (term124 A B C D P p lt2 s g) = (term124 A B C D P p lt2 s g).
Proof. exact (fun_ext (fun f : A -> B => @lem8112591 A B C D P p lt2 s f g)). Qed.
Lemma lem8112593 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8112594 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) : (term25 A B C D P p lt2 s g) = (term25 A B C D P p lt2 s g).
Proof. exact (MK_COMB (@lem8112593 A B) (@lem8112592 A B C D P p lt2 s g)). Qed.
Lemma lem8112595 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8112596 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) : (term27 A B C D P p lt2 s g) = (term27 A B C D P p lt2 s g).
Proof. exact (MK_COMB (@lem8112595) (@lem8112594 A B C D P p lt2 s g)). Qed.
Lemma lem8112597 {A B C D P : Type'} (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term29 A B C D P g p lt2 s y) = (term29 A B C D P g p lt2 s y).
Proof. exact (MK_COMB (@lem8112596 A B C D P p lt2 s g) (@lem8112565 A B C P p lt2 s y)). Qed.
Lemma lem8112598 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8112599 {A B C D P : Type'} (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term125 A B C D P g p lt2 s y) = (term125 A B C D P g p lt2 s y).
Proof. exact (MK_COMB (@lem8112598) (@lem8112597 A B C D P g p lt2 s y)). Qed.
Lemma lem8112600 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) (y : type564 A B C P) : (term78 A B C D P p lt2 s g y) = (term78 A B C D P p lt2 s g y).
Proof. exact (MK_COMB (@lem8112599 A B C D P g p lt2 s y) (@lem8112536 A B C D P p lt2 s g y)). Qed.
Lemma lem8112601 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) : (term80 A B C D P p lt2 s g) = (term80 A B C D P p lt2 s g).
Proof. exact (fun_ext (fun y : type564 A B C P => @lem8112600 A B C D P p lt2 s g y)). Qed.
Lemma lem8112602 {A B C P : Type'} : (@all ((A -> B) -> P -> C)) = (@all ((A -> B) -> P -> C)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> C))). Qed.
Lemma lem8112603 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) : (term82 A B C D P p lt2 s g) = (term82 A B C D P p lt2 s g).
Proof. exact (MK_COMB (@lem8112602 A B C P) (@lem8112601 A B C D P p lt2 s g)). Qed.
Lemma lem8112604 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) : (term84 A B C D P p lt2 s) = (term84 A B C D P p lt2 s).
Proof. exact (fun_ext (fun g : type565 A B C D P => @lem8112603 A B C D P p lt2 s g)). Qed.
Lemma lem8112605 {A B C D P : Type'} : (@all ((A -> B) -> P -> C -> D)) = (@all ((A -> B) -> P -> C -> D)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> C -> D))). Qed.
Lemma lem8112606 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) : (term86 A B C D P p lt2 s) = (term86 A B C D P p lt2 s).
Proof. exact (MK_COMB (@lem8112605 A B C D P) (@lem8112604 A B C D P p lt2 s)). Qed.
Lemma lem8112607 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) : (term88 A B C D P p lt2) = (term88 A B C D P p lt2).
Proof. exact (fun_ext (fun s : P -> A => @lem8112606 A B C D P p lt2 s)). Qed.
Lemma lem8112608 {A P : Type'} : (@all (P -> A)) = (@all (P -> A)).
Proof. exact (eq_refl (@all (P -> A))). Qed.
Lemma lem8112609 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) : (term90 A B C D P p lt2) = (term90 A B C D P p lt2).
Proof. exact (MK_COMB (@lem8112608 A P) (@lem8112607 A B C D P p lt2)). Qed.
Lemma lem8112610 {A B C D P : Type'} (lt2 : type1402 A) : (term92 A B C D P lt2) = (term92 A B C D P lt2).
Proof. exact (fun_ext (fun p : type560 A B P => @lem8112609 A B C D P p lt2)). Qed.
Lemma lem8112611 {A B P : Type'} : (@all ((A -> B) -> P -> Prop)) = (@all ((A -> B) -> P -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> Prop))). Qed.
Lemma lem8112612 {A B C D P : Type'} (lt2 : type1402 A) : (term94 A B C D P lt2) = (term94 A B C D P lt2).
Proof. exact (MK_COMB (@lem8112611 A B P) (@lem8112610 A B C D P lt2)). Qed.
Lemma lem8112613 {A B C D P : Type'} : (term96 A B C D P) = (term96 A B C D P).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem8112612 A B C D P lt2)). Qed.
Lemma lem8112614 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem8112615 {A B C D P : Type'} : (term98 A B C D P) = (term98 A B C D P).
Proof. exact (MK_COMB (@lem8112614 A) (@lem8112613 A B C D P)). Qed.
Lemma lem8112748 {A B C D P : Type'} : (term100 A B C D P) = (term98 A B C D P).
Proof. exact (TRANS (@lem8112507 A B C D P) (@lem8112615 A B C D P)). Qed.
Lemma lem8112749 {A B C D P : Type'} : (term98 A B C D P) = (term100 A B C D P).
Proof. exact (SYM (@lem8112748 A B C D P)). Qed.
Lemma lem8112750 {A B C D P : Type'} (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) (h1 : term29 A B C D P g p lt2 s y) : term29 A B C D P g p lt2 s y.
Proof. exact (h1). Qed.
Lemma lem8112751 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term35 A B P p lt2 s a f g'.
Proof. exact (h1). Qed.
Lemma lem8112753 (p : Prop) : p = (term99 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8112754 {A B C D P : Type'} (f : A -> B) (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : ((term54 A B C D P g y f a) = (term54 A B C D P g y g' a)) = (term126 A B C D P f g y g' a).
Proof. exact (@lem8112753 ((term54 A B C D P g y f a) = (term54 A B C D P g y g' a))). Qed.
Lemma lem8112755 {A B C D P : Type'} (f : A -> B) (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term126 A B C D P f g y g' a) = ((term54 A B C D P g y f a) = (term54 A B C D P g y g' a)).
Proof. exact (SYM (@lem8112754 A B C D P f g y g' a)). Qed.
Lemma lem8112756 {A B C D P : Type'} (f : A -> B) (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) (h1 : term127 A B C D P f g y g' a) : term127 A B C D P f g y g' a.
Proof. exact (h1). Qed.
Lemma lem8112765 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term128 A B P lt2 s a f g z) = (term129 A B P lt2 s a f g z).
Proof. exact (@lem17362 (term130 A P lt2 z s a) ((f z) = (g z))). Qed.
Lemma lem8112766 {A : Type'} (P : A -> Prop) : (term131 A P) = (term132 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem8112767 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term133 A B P lt2 s a f g) = (term134 A B P lt2 s a f g).
Proof. exact (@lem8112766 A (term108 A B P lt2 s a f g)). Qed.
Lemma lem8112768 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term135 A B P lt2 s a f g z) = (term107 A B P lt2 s a f g z).
Proof. exact (eq_refl (term135 A B P lt2 s a f g z)). Qed.
Lemma lem8112769 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8112770 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term136 A B P lt2 s a f g z) = (term128 A B P lt2 s a f g z).
Proof. exact (MK_COMB (@lem8112769) (@lem8112768 A B P lt2 s a f g z)). Qed.
Lemma lem8112771 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term136 A B P lt2 s a f g z) = (term129 A B P lt2 s a f g z).
Proof. exact (TRANS (@lem8112770 A B P lt2 s a f g z) (@lem8112765 A B P lt2 s a f g z)). Qed.
Lemma lem8112772 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term137 A B P lt2 s a f g) = (term138 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8112771 A B P lt2 s a f g z)). Qed.
Lemma lem8112773 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8112774 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term134 A B P lt2 s a f g) = (term139 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8112773 A) (@lem8112772 A B P lt2 s a f g)). Qed.
Lemma lem8112775 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term133 A B P lt2 s a f g) = (term139 A B P lt2 s a f g).
Proof. exact (TRANS (@lem8112767 A B P lt2 s a f g) (@lem8112774 A B P lt2 s a f g)). Qed.
Lemma lem8112777 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term140 A B P p g a) = (term140 A B P p g a).
Proof. exact (eq_refl (term140 A B P p g a)). Qed.
Lemma lem8112778 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term141 A B P p lt2 s a f g) = (term142 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8112777 A B P p g a) (@lem8112775 A B P lt2 s a f g)). Qed.
Lemma lem8112779 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term143 A B P p lt2 s a f g) = (term141 A B P p lt2 s a f g).
Proof. exact (@lem17045 (p g a) (term109 A B P lt2 s a f g)). Qed.
Lemma lem8112780 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term143 A B P p lt2 s a f g) = (term142 A B P p lt2 s a f g).
Proof. exact (TRANS (@lem8112779 A B P p lt2 s a f g) (@lem8112778 A B P p lt2 s a f g)). Qed.
Lemma lem8112782 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term140 A B P p f a) = (term140 A B P p f a).
Proof. exact (eq_refl (term140 A B P p f a)). Qed.
Lemma lem8112783 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term144 A B P p lt2 s a f g) = (term145 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8112782 A B P p f a) (@lem8112780 A B P p lt2 s a f g)). Qed.
Lemma lem8112784 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term146 A B P p lt2 s a f g) = (term144 A B P p lt2 s a f g).
Proof. exact (@lem17045 (p f a) (term111 A B P p lt2 s a f g)). Qed.
Lemma lem8112785 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term146 A B P p lt2 s a f g) = (term145 A B P p lt2 s a f g).
Proof. exact (TRANS (@lem8112784 A B P p lt2 s a f g) (@lem8112783 A B P p lt2 s a f g)). Qed.
Lemma lem8112786 {A B C D P : Type'} (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : ((g f a) = (g g' a)) = ((g f a) = (g g' a)).
Proof. exact (eq_refl ((g f a) = (g g' a))). Qed.
Lemma lem8112787 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8112788 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term147 A B P p lt2 s a f g) = (term148 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8112787) (@lem8112785 A B P p lt2 s a f g)). Qed.
Lemma lem8112789 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : (term149 A B C D P p lt2 s f g g' a) = (term150 A B C D P p lt2 s f g g' a).
Proof. exact (MK_COMB (@lem8112788 A B P p lt2 s a f g') (@lem8112786 A B C D P f g g' a)). Qed.
Lemma lem8112790 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : (term119 A B C D P p lt2 s f g g' a) = (term149 A B C D P p lt2 s f g g' a).
Proof. exact (@lem17265 (term35 A B P p lt2 s a f g') ((g f a) = (g g' a))). Qed.
Lemma lem8112791 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : (term119 A B C D P p lt2 s f g g' a) = (term150 A B C D P p lt2 s f g g' a).
Proof. exact (TRANS (@lem8112790 A B C D P p lt2 s f g g' a) (@lem8112789 A B C D P p lt2 s f g g' a)). Qed.
Lemma lem8112792 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) : (term120 A B C D P p lt2 s f g g') = (term151 A B C D P p lt2 s f g g').
Proof. exact (fun_ext (fun a : P => @lem8112791 A B C D P p lt2 s f g g' a)). Qed.
Lemma lem8112793 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8112794 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) : (term121 A B C D P p lt2 s f g g') = (term152 A B C D P p lt2 s f g g').
Proof. exact (MK_COMB (@lem8112793 P) (@lem8112792 A B C D P p lt2 s f g g')). Qed.
Lemma lem8112795 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) : (term122 A B C D P p lt2 s f g) = (term153 A B C D P p lt2 s f g).
Proof. exact (fun_ext (fun g' : A -> B => @lem8112794 A B C D P p lt2 s f g g')). Qed.
Lemma lem8112796 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8112797 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) : (term123 A B C D P p lt2 s f g) = (term154 A B C D P p lt2 s f g).
Proof. exact (MK_COMB (@lem8112796 A B) (@lem8112795 A B C D P p lt2 s f g)). Qed.
Lemma lem8112798 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) : (term124 A B C D P p lt2 s g) = (term155 A B C D P p lt2 s g).
Proof. exact (fun_ext (fun f : A -> B => @lem8112797 A B C D P p lt2 s f g)). Qed.
Lemma lem8112799 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8112800 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) : (term25 A B C D P p lt2 s g) = (term156 A B C D P p lt2 s g).
Proof. exact (MK_COMB (@lem8112799 A B) (@lem8112798 A B C D P p lt2 s g)). Qed.
Lemma lem8112809 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term128 A B P lt2 s a f g z) = (term129 A B P lt2 s a f g z).
Proof. exact (@lem17362 (term130 A P lt2 z s a) ((f z) = (g z))). Qed.
Lemma lem8112810 {A : Type'} (P : A -> Prop) : (term131 A P) = (term132 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem8112811 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term133 A B P lt2 s a f g) = (term134 A B P lt2 s a f g).
Proof. exact (@lem8112810 A (term108 A B P lt2 s a f g)). Qed.
Lemma lem8112812 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term135 A B P lt2 s a f g z) = (term107 A B P lt2 s a f g z).
Proof. exact (eq_refl (term135 A B P lt2 s a f g z)). Qed.
Lemma lem8112813 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8112814 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term136 A B P lt2 s a f g z) = (term128 A B P lt2 s a f g z).
Proof. exact (MK_COMB (@lem8112813) (@lem8112812 A B P lt2 s a f g z)). Qed.
Lemma lem8112815 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term136 A B P lt2 s a f g z) = (term129 A B P lt2 s a f g z).
Proof. exact (TRANS (@lem8112814 A B P lt2 s a f g z) (@lem8112809 A B P lt2 s a f g z)). Qed.
Lemma lem8112816 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term137 A B P lt2 s a f g) = (term138 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8112815 A B P lt2 s a f g z)). Qed.
Lemma lem8112817 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8112818 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term134 A B P lt2 s a f g) = (term139 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8112817 A) (@lem8112816 A B P lt2 s a f g)). Qed.
Lemma lem8112819 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term133 A B P lt2 s a f g) = (term139 A B P lt2 s a f g).
Proof. exact (TRANS (@lem8112811 A B P lt2 s a f g) (@lem8112818 A B P lt2 s a f g)). Qed.
Lemma lem8112821 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term140 A B P p g a) = (term140 A B P p g a).
Proof. exact (eq_refl (term140 A B P p g a)). Qed.
Lemma lem8112822 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term141 A B P p lt2 s a f g) = (term142 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8112821 A B P p g a) (@lem8112819 A B P lt2 s a f g)). Qed.
Lemma lem8112823 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term143 A B P p lt2 s a f g) = (term141 A B P p lt2 s a f g).
Proof. exact (@lem17045 (p g a) (term109 A B P lt2 s a f g)). Qed.
Lemma lem8112824 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term143 A B P p lt2 s a f g) = (term142 A B P p lt2 s a f g).
Proof. exact (TRANS (@lem8112823 A B P p lt2 s a f g) (@lem8112822 A B P p lt2 s a f g)). Qed.
Lemma lem8112826 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term140 A B P p f a) = (term140 A B P p f a).
Proof. exact (eq_refl (term140 A B P p f a)). Qed.
Lemma lem8112827 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term144 A B P p lt2 s a f g) = (term145 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8112826 A B P p f a) (@lem8112824 A B P p lt2 s a f g)). Qed.
Lemma lem8112828 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term146 A B P p lt2 s a f g) = (term144 A B P p lt2 s a f g).
Proof. exact (@lem17045 (p f a) (term111 A B P p lt2 s a f g)). Qed.
Lemma lem8112829 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term146 A B P p lt2 s a f g) = (term145 A B P p lt2 s a f g).
Proof. exact (TRANS (@lem8112828 A B P p lt2 s a f g) (@lem8112827 A B P p lt2 s a f g)). Qed.
Lemma lem8112830 {A B C P : Type'} (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : ((y f a) = (y g a)) = ((y f a) = (y g a)).
Proof. exact (eq_refl ((y f a) = (y g a))). Qed.
Lemma lem8112831 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8112832 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term147 A B P p lt2 s a f g) = (term148 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8112831) (@lem8112829 A B P p lt2 s a f g)). Qed.
Lemma lem8112833 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term157 A B C P p lt2 s f y g a) = (term158 A B C P p lt2 s f y g a).
Proof. exact (MK_COMB (@lem8112832 A B P p lt2 s a f g) (@lem8112830 A B C P f y g a)). Qed.
Lemma lem8112834 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term113 A B C P p lt2 s f y g a) = (term157 A B C P p lt2 s f y g a).
Proof. exact (@lem17265 (term35 A B P p lt2 s a f g) ((y f a) = (y g a))). Qed.
Lemma lem8112835 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term113 A B C P p lt2 s f y g a) = (term158 A B C P p lt2 s f y g a).
Proof. exact (TRANS (@lem8112834 A B C P p lt2 s f y g a) (@lem8112833 A B C P p lt2 s f y g a)). Qed.
Lemma lem8112836 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term114 A B C P p lt2 s f y g) = (term159 A B C P p lt2 s f y g).
Proof. exact (fun_ext (fun a : P => @lem8112835 A B C P p lt2 s f y g a)). Qed.
Lemma lem8112837 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8112838 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term115 A B C P p lt2 s f y g) = (term160 A B C P p lt2 s f y g).
Proof. exact (MK_COMB (@lem8112837 P) (@lem8112836 A B C P p lt2 s f y g)). Qed.
Lemma lem8112839 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term116 A B C P p lt2 s f y) = (term161 A B C P p lt2 s f y).
Proof. exact (fun_ext (fun g : A -> B => @lem8112838 A B C P p lt2 s f y g)). Qed.
Lemma lem8112840 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8112841 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term117 A B C P p lt2 s f y) = (term162 A B C P p lt2 s f y).
Proof. exact (MK_COMB (@lem8112840 A B) (@lem8112839 A B C P p lt2 s f y)). Qed.
Lemma lem8112842 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term118 A B C P p lt2 s y) = (term163 A B C P p lt2 s y).
Proof. exact (fun_ext (fun f : A -> B => @lem8112841 A B C P p lt2 s f y)). Qed.
Lemma lem8112843 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8112844 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term28 A B C P p lt2 s y) = (term164 A B C P p lt2 s y).
Proof. exact (MK_COMB (@lem8112843 A B) (@lem8112842 A B C P p lt2 s y)). Qed.
Lemma lem8112845 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8112846 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) : (term27 A B C D P p lt2 s g) = (term165 A B C D P p lt2 s g).
Proof. exact (MK_COMB (@lem8112845) (@lem8112800 A B C D P p lt2 s g)). Qed.
Lemma lem8112847 {A B C D P : Type'} (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term29 A B C D P g p lt2 s y) = (term166 A B C D P g p lt2 s y).
Proof. exact (MK_COMB (@lem8112846 A B C D P p lt2 s g) (@lem8112844 A B C P p lt2 s y)). Qed.
Lemma lem8113058 {A : Type'} (P : Prop) (Q : A -> Prop) : (term167 A P Q) = (term168 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem8113059 {A : Type'} (P : Prop) (Q : A -> Prop) : (term167 A P Q) = (term168 A P Q).
Proof. exact (@lem8113058 A P Q). Qed.
Lemma lem8113060 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term169 A B P p lt2 s a f g) = (term170 A B P p lt2 s a f g).
Proof. exact (@lem8113059 A (term171 A B P p g a) (term138 A B P lt2 s a f g)). Qed.
Lemma lem8113061 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term172 A B P lt2 s a f g z) = (term129 A B P lt2 s a f g z).
Proof. exact (eq_refl (term172 A B P lt2 s a f g z)). Qed.
Lemma lem8113062 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term173 A B P lt2 s a f g) = (term138 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8113061 A B P lt2 s a f g z)). Qed.
Lemma lem8113063 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8113064 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term174 A B P lt2 s a f g) = (term139 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8113063 A) (@lem8113062 A B P lt2 s a f g)). Qed.
Lemma lem8113065 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term140 A B P p g a) = (term140 A B P p g a).
Proof. exact (eq_refl (term140 A B P p g a)). Qed.
Lemma lem8113066 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term169 A B P p lt2 s a f g) = (term142 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8113065 A B P p g a) (@lem8113064 A B P lt2 s a f g)). Qed.
Lemma lem8113067 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8113068 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term175 A B P p lt2 s a f g) = (term176 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8113067) (@lem8113066 A B P p lt2 s a f g)). Qed.
Lemma lem8113069 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term172 A B P lt2 s a f g z) = (term129 A B P lt2 s a f g z).
Proof. exact (eq_refl (term172 A B P lt2 s a f g z)). Qed.
Lemma lem8113070 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term140 A B P p g a) = (term140 A B P p g a).
Proof. exact (eq_refl (term140 A B P p g a)). Qed.
Lemma lem8113071 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term177 A B P p lt2 s a f g z) = (term178 A B P p lt2 s a f g z).
Proof. exact (MK_COMB (@lem8113070 A B P p g a) (@lem8113069 A B P lt2 s a f g z)). Qed.
Lemma lem8113072 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term179 A B P p lt2 s a f g) = (term180 A B P p lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8113071 A B P p lt2 s a f g z)). Qed.
Lemma lem8113073 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8113074 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term170 A B P p lt2 s a f g) = (term181 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8113073 A) (@lem8113072 A B P p lt2 s a f g)). Qed.
Lemma lem8113075 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : ((term169 A B P p lt2 s a f g) = (term170 A B P p lt2 s a f g)) = ((term142 A B P p lt2 s a f g) = (term181 A B P p lt2 s a f g)).
Proof. exact (MK_COMB (@lem8113068 A B P p lt2 s a f g) (@lem8113074 A B P p lt2 s a f g)). Qed.
Lemma lem8113076 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term142 A B P p lt2 s a f g) = (term181 A B P p lt2 s a f g).
Proof. exact (EQ_MP (@lem8113075 A B P p lt2 s a f g) (@lem8113060 A B P p lt2 s a f g)). Qed.
Lemma lem8113077 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term140 A B P p f a) = (term140 A B P p f a).
Proof. exact (eq_refl (term140 A B P p f a)). Qed.
Lemma lem8113078 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term145 A B P p lt2 s a f g) = (term182 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8113077 A B P p f a) (@lem8113076 A B P p lt2 s a f g)). Qed.
Lemma lem8113080 {A : Type'} (P : Prop) (Q : A -> Prop) : (term167 A P Q) = (term168 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem8113081 {A : Type'} (P : Prop) (Q : A -> Prop) : (term167 A P Q) = (term168 A P Q).
Proof. exact (@lem8113080 A P Q). Qed.
Lemma lem8113082 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term183 A B P p lt2 s a f g) = (term184 A B P p lt2 s a f g).
Proof. exact (@lem8113081 A (term171 A B P p f a) (term180 A B P p lt2 s a f g)). Qed.
Lemma lem8113083 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term185 A B P p lt2 s a f g z) = (term178 A B P p lt2 s a f g z).
Proof. exact (eq_refl (term185 A B P p lt2 s a f g z)). Qed.
Lemma lem8113084 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term186 A B P p lt2 s a f g) = (term180 A B P p lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8113083 A B P p lt2 s a f g z)). Qed.
Lemma lem8113085 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8113086 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term187 A B P p lt2 s a f g) = (term181 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8113085 A) (@lem8113084 A B P p lt2 s a f g)). Qed.
Lemma lem8113087 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term140 A B P p f a) = (term140 A B P p f a).
Proof. exact (eq_refl (term140 A B P p f a)). Qed.
Lemma lem8113088 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term183 A B P p lt2 s a f g) = (term182 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8113087 A B P p f a) (@lem8113086 A B P p lt2 s a f g)). Qed.
Lemma lem8113089 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8113090 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term188 A B P p lt2 s a f g) = (term189 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8113089) (@lem8113088 A B P p lt2 s a f g)). Qed.
Lemma lem8113091 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term185 A B P p lt2 s a f g z) = (term178 A B P p lt2 s a f g z).
Proof. exact (eq_refl (term185 A B P p lt2 s a f g z)). Qed.
Lemma lem8113092 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term140 A B P p f a) = (term140 A B P p f a).
Proof. exact (eq_refl (term140 A B P p f a)). Qed.
Lemma lem8113093 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term190 A B P p lt2 s a f g z) = (term191 A B P p lt2 s a f g z).
Proof. exact (MK_COMB (@lem8113092 A B P p f a) (@lem8113091 A B P p lt2 s a f g z)). Qed.
Lemma lem8113094 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term192 A B P p lt2 s a f g) = (term193 A B P p lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8113093 A B P p lt2 s a f g z)). Qed.
Lemma lem8113095 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8113096 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term184 A B P p lt2 s a f g) = (term194 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8113095 A) (@lem8113094 A B P p lt2 s a f g)). Qed.
Lemma lem8113097 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : ((term183 A B P p lt2 s a f g) = (term184 A B P p lt2 s a f g)) = ((term182 A B P p lt2 s a f g) = (term194 A B P p lt2 s a f g)).
Proof. exact (MK_COMB (@lem8113090 A B P p lt2 s a f g) (@lem8113096 A B P p lt2 s a f g)). Qed.
Lemma lem8113098 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term182 A B P p lt2 s a f g) = (term194 A B P p lt2 s a f g).
Proof. exact (EQ_MP (@lem8113097 A B P p lt2 s a f g) (@lem8113082 A B P p lt2 s a f g)). Qed.
Lemma lem8113099 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term145 A B P p lt2 s a f g) = (term194 A B P p lt2 s a f g).
Proof. exact (TRANS (@lem8113078 A B P p lt2 s a f g) (@lem8113098 A B P p lt2 s a f g)). Qed.
Lemma lem8113100 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8113101 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term148 A B P p lt2 s a f g) = (term195 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8113100) (@lem8113099 A B P p lt2 s a f g)). Qed.
Lemma lem8113102 {A B C D P : Type'} (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : ((g f a) = (g g' a)) = ((g f a) = (g g' a)).
Proof. exact (eq_refl ((g f a) = (g g' a))). Qed.
Lemma lem8113103 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : (term150 A B C D P p lt2 s f g g' a) = (term196 A B C D P p lt2 s f g g' a).
Proof. exact (MK_COMB (@lem8113101 A B P p lt2 s a f g') (@lem8113102 A B C D P f g g' a)). Qed.
Lemma lem8113105 {A : Type'} (P : A -> Prop) (Q : Prop) : (term197 A P Q) = (term198 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem8113106 {A : Type'} (P : A -> Prop) (Q : Prop) : (term197 A P Q) = (term198 A P Q).
Proof. exact (@lem8113105 A P Q). Qed.
Lemma lem8113107 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : (term199 A B C D P p lt2 s f g g' a) = (term200 A B C D P p lt2 s f g g' a).
Proof. exact (@lem8113106 A (term193 A B P p lt2 s a f g') ((g f a) = (g g' a))). Qed.
Lemma lem8113108 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term201 A B P p lt2 s a f g z) = (term191 A B P p lt2 s a f g z).
Proof. exact (eq_refl (term201 A B P p lt2 s a f g z)). Qed.
Lemma lem8113109 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term202 A B P p lt2 s a f g) = (term193 A B P p lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8113108 A B P p lt2 s a f g z)). Qed.
Lemma lem8113110 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8113111 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term203 A B P p lt2 s a f g) = (term194 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8113110 A) (@lem8113109 A B P p lt2 s a f g)). Qed.
Lemma lem8113112 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8113113 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term204 A B P p lt2 s a f g) = (term195 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8113112) (@lem8113111 A B P p lt2 s a f g)). Qed.
Lemma lem8113114 {A B C D P : Type'} (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : ((g f a) = (g g' a)) = ((g f a) = (g g' a)).
Proof. exact (eq_refl ((g f a) = (g g' a))). Qed.
Lemma lem8113115 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : (term199 A B C D P p lt2 s f g g' a) = (term196 A B C D P p lt2 s f g g' a).
Proof. exact (MK_COMB (@lem8113113 A B P p lt2 s a f g') (@lem8113114 A B C D P f g g' a)). Qed.
Lemma lem8113116 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8113117 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : (term205 A B C D P p lt2 s f g g' a) = (term206 A B C D P p lt2 s f g g' a).
Proof. exact (MK_COMB (@lem8113116) (@lem8113115 A B C D P p lt2 s f g g' a)). Qed.
Lemma lem8113118 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term201 A B P p lt2 s a f g z) = (term191 A B P p lt2 s a f g z).
Proof. exact (eq_refl (term201 A B P p lt2 s a f g z)). Qed.
Lemma lem8113119 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8113120 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term207 A B P p lt2 s a f g z) = (term208 A B P p lt2 s a f g z).
Proof. exact (MK_COMB (@lem8113119) (@lem8113118 A B P p lt2 s a f g z)). Qed.
Lemma lem8113121 {A B C D P : Type'} (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : ((g f a) = (g g' a)) = ((g f a) = (g g' a)).
Proof. exact (eq_refl ((g f a) = (g g' a))). Qed.
Lemma lem8113122 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : (term209 A B C D P p lt2 s z f g g' a) = (term210 A B C D P p lt2 s z f g g' a).
Proof. exact (MK_COMB (@lem8113120 A B P p lt2 s a f g' z) (@lem8113121 A B C D P f g g' a)). Qed.
Lemma lem8113123 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : (term211 A B C D P p lt2 s f g g' a) = (term212 A B C D P p lt2 s f g g' a).
Proof. exact (fun_ext (fun z : A => @lem8113122 A B C D P p lt2 s z f g g' a)). Qed.
Lemma lem8113124 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8113125 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : (term200 A B C D P p lt2 s f g g' a) = (term213 A B C D P p lt2 s f g g' a).
Proof. exact (MK_COMB (@lem8113124 A) (@lem8113123 A B C D P p lt2 s f g g' a)). Qed.
Lemma lem8113126 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : ((term199 A B C D P p lt2 s f g g' a) = (term200 A B C D P p lt2 s f g g' a)) = ((term196 A B C D P p lt2 s f g g' a) = (term213 A B C D P p lt2 s f g g' a)).
Proof. exact (MK_COMB (@lem8113117 A B C D P p lt2 s f g g' a) (@lem8113125 A B C D P p lt2 s f g g' a)). Qed.
Lemma lem8113127 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : (term196 A B C D P p lt2 s f g g' a) = (term213 A B C D P p lt2 s f g g' a).
Proof. exact (EQ_MP (@lem8113126 A B C D P p lt2 s f g g' a) (@lem8113107 A B C D P p lt2 s f g g' a)). Qed.
Lemma lem8113128 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : (term150 A B C D P p lt2 s f g g' a) = (term213 A B C D P p lt2 s f g g' a).
Proof. exact (TRANS (@lem8113103 A B C D P p lt2 s f g g' a) (@lem8113127 A B C D P p lt2 s f g g' a)). Qed.
Lemma lem8113129 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) : (term151 A B C D P p lt2 s f g g') = (term214 A B C D P p lt2 s f g g').
Proof. exact (fun_ext (fun a : P => @lem8113128 A B C D P p lt2 s f g g' a)). Qed.
Lemma lem8113130 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8113131 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) : (term152 A B C D P p lt2 s f g g') = (term215 A B C D P p lt2 s f g g').
Proof. exact (MK_COMB (@lem8113130 P) (@lem8113129 A B C D P p lt2 s f g g')). Qed.
Lemma lem8113133 {A B : Type'} (P : type1413 A B) : (term216 A B P) = (term217 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8113134 {A P : Type'} (P' : type1470 A P) : (term218 A P P') = (term219 A P P').
Proof. exact (@lem8113133 P A P'). Qed.
Lemma lem8113135 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) : (term220 A B C D P p lt2 s f g g') = (term221 A B C D P p lt2 s f g g').
Proof. exact (@lem8113134 A P (term222 A B C D P p lt2 s f g g')). Qed.
Lemma lem8113136 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : (term223 A B C D P p lt2 s f g g' a) = (term212 A B C D P p lt2 s f g g' a).
Proof. exact (eq_refl (term223 A B C D P p lt2 s f g g' a)). Qed.
Lemma lem8113137 {A : Type'} (z : A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8113138 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) (z : A) : (term224 A B C D P p lt2 s f g g' a z) = (term225 A B C D P p lt2 s f g g' a z).
Proof. exact (MK_COMB (@lem8113136 A B C D P p lt2 s f g g' a) (@lem8113137 A z)). Qed.
Lemma lem8113139 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : (term225 A B C D P p lt2 s f g g' a z) = (term210 A B C D P p lt2 s z f g g' a).
Proof. exact (eq_refl (term225 A B C D P p lt2 s f g g' a z)). Qed.
Lemma lem8113140 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : (term224 A B C D P p lt2 s f g g' a z) = (term210 A B C D P p lt2 s z f g g' a).
Proof. exact (TRANS (@lem8113138 A B C D P p lt2 s f g g' a z) (@lem8113139 A B C D P p lt2 s z f g g' a)). Qed.
Lemma lem8113141 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : (term226 A B C D P p lt2 s f g g' a) = (term212 A B C D P p lt2 s f g g' a).
Proof. exact (fun_ext (fun z : A => @lem8113140 A B C D P p lt2 s z f g g' a)). Qed.
Lemma lem8113142 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8113143 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : (term227 A B C D P p lt2 s f g g' a) = (term213 A B C D P p lt2 s f g g' a).
Proof. exact (MK_COMB (@lem8113142 A) (@lem8113141 A B C D P p lt2 s f g g' a)). Qed.
Lemma lem8113144 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) : (term228 A B C D P p lt2 s f g g') = (term214 A B C D P p lt2 s f g g').
Proof. exact (fun_ext (fun a : P => @lem8113143 A B C D P p lt2 s f g g' a)). Qed.
Lemma lem8113145 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8113146 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) : (term220 A B C D P p lt2 s f g g') = (term215 A B C D P p lt2 s f g g').
Proof. exact (MK_COMB (@lem8113145 P) (@lem8113144 A B C D P p lt2 s f g g')). Qed.
Lemma lem8113147 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8113148 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) : (term229 A B C D P p lt2 s f g g') = (term230 A B C D P p lt2 s f g g').
Proof. exact (MK_COMB (@lem8113147) (@lem8113146 A B C D P p lt2 s f g g')). Qed.
Lemma lem8113149 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : (term223 A B C D P p lt2 s f g g' a) = (term212 A B C D P p lt2 s f g g' a).
Proof. exact (eq_refl (term223 A B C D P p lt2 s f g g' a)). Qed.
Lemma lem8113150 {A P : Type'} (z : P -> A) (a : P) : (z a) = (z a).
Proof. exact (eq_refl (z a)). Qed.
Lemma lem8113151 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (z : P -> A) (a : P) : (term231 A B C D P p lt2 s f g g' z a) = (term232 A B C D P p lt2 s f g g' z a).
Proof. exact (MK_COMB (@lem8113149 A B C D P p lt2 s f g g' a) (@lem8113150 A P z a)). Qed.
Lemma lem8113152 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : (term232 A B C D P p lt2 s f g g' z a) = (term233 A B C D P p lt2 s z f g g' a).
Proof. exact (eq_refl (term232 A B C D P p lt2 s f g g' z a)). Qed.
Lemma lem8113153 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : (term231 A B C D P p lt2 s f g g' z a) = (term233 A B C D P p lt2 s z f g g' a).
Proof. exact (TRANS (@lem8113151 A B C D P p lt2 s f g g' z a) (@lem8113152 A B C D P p lt2 s z f g g' a)). Qed.
Lemma lem8113154 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) : (term234 A B C D P p lt2 s f g g' z) = (term235 A B C D P p lt2 s z f g g').
Proof. exact (fun_ext (fun a : P => @lem8113153 A B C D P p lt2 s z f g g' a)). Qed.
Lemma lem8113155 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8113156 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) : (term236 A B C D P p lt2 s f g g' z) = (term237 A B C D P p lt2 s z f g g').
Proof. exact (MK_COMB (@lem8113155 P) (@lem8113154 A B C D P p lt2 s z f g g')). Qed.
Lemma lem8113157 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) : (term238 A B C D P p lt2 s f g g') = (term239 A B C D P p lt2 s f g g').
Proof. exact (fun_ext (fun z : P -> A => @lem8113156 A B C D P p lt2 s z f g g')). Qed.
Lemma lem8113158 {A P : Type'} : (@ex (P -> A)) = (@ex (P -> A)).
Proof. exact (eq_refl (@ex (P -> A))). Qed.
Lemma lem8113159 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) : (term221 A B C D P p lt2 s f g g') = (term240 A B C D P p lt2 s f g g').
Proof. exact (MK_COMB (@lem8113158 A P) (@lem8113157 A B C D P p lt2 s f g g')). Qed.
Lemma lem8113160 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) : ((term220 A B C D P p lt2 s f g g') = (term221 A B C D P p lt2 s f g g')) = ((term215 A B C D P p lt2 s f g g') = (term240 A B C D P p lt2 s f g g')).
Proof. exact (MK_COMB (@lem8113148 A B C D P p lt2 s f g g') (@lem8113159 A B C D P p lt2 s f g g')). Qed.
Lemma lem8113161 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) : (term215 A B C D P p lt2 s f g g') = (term240 A B C D P p lt2 s f g g').
Proof. exact (EQ_MP (@lem8113160 A B C D P p lt2 s f g g') (@lem8113135 A B C D P p lt2 s f g g')). Qed.
Lemma lem8113162 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) : (term152 A B C D P p lt2 s f g g') = (term240 A B C D P p lt2 s f g g').
Proof. exact (TRANS (@lem8113131 A B C D P p lt2 s f g g') (@lem8113161 A B C D P p lt2 s f g g')). Qed.
Lemma lem8113163 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) : (term153 A B C D P p lt2 s f g) = (term241 A B C D P p lt2 s f g).
Proof. exact (fun_ext (fun g' : A -> B => @lem8113162 A B C D P p lt2 s f g g')). Qed.
Lemma lem8113164 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8113165 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) : (term154 A B C D P p lt2 s f g) = (term242 A B C D P p lt2 s f g).
Proof. exact (MK_COMB (@lem8113164 A B) (@lem8113163 A B C D P p lt2 s f g)). Qed.
Lemma lem8113167 {A B : Type'} (P : type1413 A B) : (term216 A B P) = (term217 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8113168 {A B P : Type'} (P' : type537 A B P) : (term243 A B P P') = (term244 A B P P').
Proof. exact (@lem8113167 (A -> B) (P -> A) P'). Qed.
Lemma lem8113169 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) : (term245 A B C D P p lt2 s f g) = (term246 A B C D P p lt2 s f g).
Proof. exact (@lem8113168 A B P (term247 A B C D P p lt2 s f g)). Qed.
Lemma lem8113170 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) : (term248 A B C D P p lt2 s f g g') = (term239 A B C D P p lt2 s f g g').
Proof. exact (eq_refl (term248 A B C D P p lt2 s f g g')). Qed.
Lemma lem8113171 {A P : Type'} (z : P -> A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8113172 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (z : P -> A) : (term249 A B C D P p lt2 s f g g' z) = (term250 A B C D P p lt2 s f g g' z).
Proof. exact (MK_COMB (@lem8113170 A B C D P p lt2 s f g g') (@lem8113171 A P z)). Qed.
Lemma lem8113173 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) : (term250 A B C D P p lt2 s f g g' z) = (term237 A B C D P p lt2 s z f g g').
Proof. exact (eq_refl (term250 A B C D P p lt2 s f g g' z)). Qed.
Lemma lem8113174 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) : (term249 A B C D P p lt2 s f g g' z) = (term237 A B C D P p lt2 s z f g g').
Proof. exact (TRANS (@lem8113172 A B C D P p lt2 s f g g' z) (@lem8113173 A B C D P p lt2 s z f g g')). Qed.
Lemma lem8113175 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) : (term251 A B C D P p lt2 s f g g') = (term239 A B C D P p lt2 s f g g').
Proof. exact (fun_ext (fun z : P -> A => @lem8113174 A B C D P p lt2 s z f g g')). Qed.
Lemma lem8113176 {A P : Type'} : (@ex (P -> A)) = (@ex (P -> A)).
Proof. exact (eq_refl (@ex (P -> A))). Qed.
Lemma lem8113177 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) : (term252 A B C D P p lt2 s f g g') = (term240 A B C D P p lt2 s f g g').
Proof. exact (MK_COMB (@lem8113176 A P) (@lem8113175 A B C D P p lt2 s f g g')). Qed.
Lemma lem8113178 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) : (term253 A B C D P p lt2 s f g) = (term241 A B C D P p lt2 s f g).
Proof. exact (fun_ext (fun g' : A -> B => @lem8113177 A B C D P p lt2 s f g g')). Qed.
Lemma lem8113179 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8113180 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) : (term245 A B C D P p lt2 s f g) = (term242 A B C D P p lt2 s f g).
Proof. exact (MK_COMB (@lem8113179 A B) (@lem8113178 A B C D P p lt2 s f g)). Qed.
Lemma lem8113181 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8113182 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) : (term254 A B C D P p lt2 s f g) = (term255 A B C D P p lt2 s f g).
Proof. exact (MK_COMB (@lem8113181) (@lem8113180 A B C D P p lt2 s f g)). Qed.
Lemma lem8113183 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) : (term248 A B C D P p lt2 s f g g') = (term239 A B C D P p lt2 s f g g').
Proof. exact (eq_refl (term248 A B C D P p lt2 s f g g')). Qed.
Lemma lem8113184 {A B P : Type'} (z : type557 A B P) (g : A -> B) : (z g) = (z g).
Proof. exact (eq_refl (z g)). Qed.
Lemma lem8113185 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (z : type557 A B P) (g' : A -> B) : (term256 A B C D P p lt2 s f g z g') = (term257 A B C D P p lt2 s f g z g').
Proof. exact (MK_COMB (@lem8113183 A B C D P p lt2 s f g g') (@lem8113184 A B P z g')). Qed.
Lemma lem8113186 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) : (term257 A B C D P p lt2 s f g z g') = (term258 A B C D P p lt2 s z f g g').
Proof. exact (eq_refl (term257 A B C D P p lt2 s f g z g')). Qed.
Lemma lem8113187 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) : (term256 A B C D P p lt2 s f g z g') = (term258 A B C D P p lt2 s z f g g').
Proof. exact (TRANS (@lem8113185 A B C D P p lt2 s f g z g') (@lem8113186 A B C D P p lt2 s z f g g')). Qed.
Lemma lem8113188 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (g : type565 A B C D P) : (term259 A B C D P p lt2 s f g z) = (term260 A B C D P p lt2 s z f g).
Proof. exact (fun_ext (fun g' : A -> B => @lem8113187 A B C D P p lt2 s z f g g')). Qed.
Lemma lem8113189 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8113190 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (g : type565 A B C D P) : (term261 A B C D P p lt2 s f g z) = (term262 A B C D P p lt2 s z f g).
Proof. exact (MK_COMB (@lem8113189 A B) (@lem8113188 A B C D P p lt2 s z f g)). Qed.
Lemma lem8113191 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) : (term263 A B C D P p lt2 s f g) = (term264 A B C D P p lt2 s f g).
Proof. exact (fun_ext (fun z : type557 A B P => @lem8113190 A B C D P p lt2 s z f g)). Qed.
Lemma lem8113192 {A B P : Type'} : (@ex ((A -> B) -> P -> A)) = (@ex ((A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> P -> A))). Qed.
Lemma lem8113193 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) : (term246 A B C D P p lt2 s f g) = (term265 A B C D P p lt2 s f g).
Proof. exact (MK_COMB (@lem8113192 A B P) (@lem8113191 A B C D P p lt2 s f g)). Qed.
Lemma lem8113194 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) : ((term245 A B C D P p lt2 s f g) = (term246 A B C D P p lt2 s f g)) = ((term242 A B C D P p lt2 s f g) = (term265 A B C D P p lt2 s f g)).
Proof. exact (MK_COMB (@lem8113182 A B C D P p lt2 s f g) (@lem8113193 A B C D P p lt2 s f g)). Qed.
Lemma lem8113195 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) : (term242 A B C D P p lt2 s f g) = (term265 A B C D P p lt2 s f g).
Proof. exact (EQ_MP (@lem8113194 A B C D P p lt2 s f g) (@lem8113169 A B C D P p lt2 s f g)). Qed.
Lemma lem8113196 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) : (term154 A B C D P p lt2 s f g) = (term265 A B C D P p lt2 s f g).
Proof. exact (TRANS (@lem8113165 A B C D P p lt2 s f g) (@lem8113195 A B C D P p lt2 s f g)). Qed.
Lemma lem8113197 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) : (term155 A B C D P p lt2 s g) = (term266 A B C D P p lt2 s g).
Proof. exact (fun_ext (fun f : A -> B => @lem8113196 A B C D P p lt2 s f g)). Qed.
Lemma lem8113198 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8113199 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) : (term156 A B C D P p lt2 s g) = (term267 A B C D P p lt2 s g).
Proof. exact (MK_COMB (@lem8113198 A B) (@lem8113197 A B C D P p lt2 s g)). Qed.
Lemma lem8113201 {A B : Type'} (P : type1413 A B) : (term216 A B P) = (term217 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8113202 {A B P : Type'} (P' : type495 A B P) : (term268 A B P P') = (term269 A B P P').
Proof. exact (@lem8113201 (A -> B) (type557 A B P) P'). Qed.
Lemma lem8113203 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) : (term270 A B C D P p lt2 s g) = (term271 A B C D P p lt2 s g).
Proof. exact (@lem8113202 A B P (term272 A B C D P p lt2 s g)). Qed.
Lemma lem8113204 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) : (term273 A B C D P p lt2 s g f) = (term264 A B C D P p lt2 s f g).
Proof. exact (eq_refl (term273 A B C D P p lt2 s g f)). Qed.
Lemma lem8113205 {A B P : Type'} (z : type557 A B P) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8113206 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) (z : type557 A B P) : (term274 A B C D P p lt2 s g f z) = (term275 A B C D P p lt2 s f g z).
Proof. exact (MK_COMB (@lem8113204 A B C D P p lt2 s f g) (@lem8113205 A B P z)). Qed.
Lemma lem8113207 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (g : type565 A B C D P) : (term275 A B C D P p lt2 s f g z) = (term262 A B C D P p lt2 s z f g).
Proof. exact (eq_refl (term275 A B C D P p lt2 s f g z)). Qed.
Lemma lem8113208 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (g : type565 A B C D P) : (term274 A B C D P p lt2 s g f z) = (term262 A B C D P p lt2 s z f g).
Proof. exact (TRANS (@lem8113206 A B C D P p lt2 s f g z) (@lem8113207 A B C D P p lt2 s z f g)). Qed.
Lemma lem8113209 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) : (term276 A B C D P p lt2 s g f) = (term264 A B C D P p lt2 s f g).
Proof. exact (fun_ext (fun z : type557 A B P => @lem8113208 A B C D P p lt2 s z f g)). Qed.
Lemma lem8113210 {A B P : Type'} : (@ex ((A -> B) -> P -> A)) = (@ex ((A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> P -> A))). Qed.
Lemma lem8113211 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) : (term277 A B C D P p lt2 s g f) = (term265 A B C D P p lt2 s f g).
Proof. exact (MK_COMB (@lem8113210 A B P) (@lem8113209 A B C D P p lt2 s f g)). Qed.
Lemma lem8113212 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) : (term278 A B C D P p lt2 s g) = (term266 A B C D P p lt2 s g).
Proof. exact (fun_ext (fun f : A -> B => @lem8113211 A B C D P p lt2 s f g)). Qed.
Lemma lem8113213 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8113214 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) : (term270 A B C D P p lt2 s g) = (term267 A B C D P p lt2 s g).
Proof. exact (MK_COMB (@lem8113213 A B) (@lem8113212 A B C D P p lt2 s g)). Qed.
Lemma lem8113215 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8113216 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) : (term279 A B C D P p lt2 s g) = (term280 A B C D P p lt2 s g).
Proof. exact (MK_COMB (@lem8113215) (@lem8113214 A B C D P p lt2 s g)). Qed.
Lemma lem8113217 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type565 A B C D P) : (term273 A B C D P p lt2 s g f) = (term264 A B C D P p lt2 s f g).
Proof. exact (eq_refl (term273 A B C D P p lt2 s g f)). Qed.
Lemma lem8113218 {A B P : Type'} (z : type518 A B P) (f : A -> B) : (z f) = (z f).
Proof. exact (eq_refl (z f)). Qed.
Lemma lem8113219 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) (z : type518 A B P) (f : A -> B) : (term281 A B C D P p lt2 s g z f) = (term282 A B C D P p lt2 s g z f).
Proof. exact (MK_COMB (@lem8113217 A B C D P p lt2 s f g) (@lem8113218 A B P z f)). Qed.
Lemma lem8113220 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (g : type565 A B C D P) : (term282 A B C D P p lt2 s g z f) = (term283 A B C D P p lt2 s z f g).
Proof. exact (eq_refl (term282 A B C D P p lt2 s g z f)). Qed.
Lemma lem8113221 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (g : type565 A B C D P) : (term281 A B C D P p lt2 s g z f) = (term283 A B C D P p lt2 s z f g).
Proof. exact (TRANS (@lem8113219 A B C D P p lt2 s g z f) (@lem8113220 A B C D P p lt2 s z f g)). Qed.
Lemma lem8113222 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (g : type565 A B C D P) : (term284 A B C D P p lt2 s g z) = (term285 A B C D P p lt2 s z g).
Proof. exact (fun_ext (fun f : A -> B => @lem8113221 A B C D P p lt2 s z f g)). Qed.
Lemma lem8113223 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8113224 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (g : type565 A B C D P) : (term286 A B C D P p lt2 s g z) = (term287 A B C D P p lt2 s z g).
Proof. exact (MK_COMB (@lem8113223 A B) (@lem8113222 A B C D P p lt2 s z g)). Qed.
Lemma lem8113225 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) : (term288 A B C D P p lt2 s g) = (term289 A B C D P p lt2 s g).
Proof. exact (fun_ext (fun z : type518 A B P => @lem8113224 A B C D P p lt2 s z g)). Qed.
Lemma lem8113226 {A B P : Type'} : (@ex ((A -> B) -> (A -> B) -> P -> A)) = (@ex ((A -> B) -> (A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> P -> A))). Qed.
Lemma lem8113227 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) : (term271 A B C D P p lt2 s g) = (term290 A B C D P p lt2 s g).
Proof. exact (MK_COMB (@lem8113226 A B P) (@lem8113225 A B C D P p lt2 s g)). Qed.
Lemma lem8113228 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) : ((term270 A B C D P p lt2 s g) = (term271 A B C D P p lt2 s g)) = ((term267 A B C D P p lt2 s g) = (term290 A B C D P p lt2 s g)).
Proof. exact (MK_COMB (@lem8113216 A B C D P p lt2 s g) (@lem8113227 A B C D P p lt2 s g)). Qed.
Lemma lem8113229 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) : (term267 A B C D P p lt2 s g) = (term290 A B C D P p lt2 s g).
Proof. exact (EQ_MP (@lem8113228 A B C D P p lt2 s g) (@lem8113203 A B C D P p lt2 s g)). Qed.
Lemma lem8113230 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) : (term156 A B C D P p lt2 s g) = (term290 A B C D P p lt2 s g).
Proof. exact (TRANS (@lem8113199 A B C D P p lt2 s g) (@lem8113229 A B C D P p lt2 s g)). Qed.
Lemma lem8113231 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8113232 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) : (term165 A B C D P p lt2 s g) = (term291 A B C D P p lt2 s g).
Proof. exact (MK_COMB (@lem8113231) (@lem8113230 A B C D P p lt2 s g)). Qed.
Lemma lem8113234 {A : Type'} (P : Prop) (Q : A -> Prop) : (term167 A P Q) = (term168 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem8113235 {A : Type'} (P : Prop) (Q : A -> Prop) : (term167 A P Q) = (term168 A P Q).
Proof. exact (@lem8113234 A P Q). Qed.
Lemma lem8113236 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term169 A B P p lt2 s a f g) = (term170 A B P p lt2 s a f g).
Proof. exact (@lem8113235 A (term171 A B P p g a) (term138 A B P lt2 s a f g)). Qed.
Lemma lem8113237 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term172 A B P lt2 s a f g z) = (term129 A B P lt2 s a f g z).
Proof. exact (eq_refl (term172 A B P lt2 s a f g z)). Qed.
Lemma lem8113238 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term173 A B P lt2 s a f g) = (term138 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8113237 A B P lt2 s a f g z)). Qed.
Lemma lem8113239 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8113240 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term174 A B P lt2 s a f g) = (term139 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8113239 A) (@lem8113238 A B P lt2 s a f g)). Qed.
Lemma lem8113241 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term140 A B P p g a) = (term140 A B P p g a).
Proof. exact (eq_refl (term140 A B P p g a)). Qed.
Lemma lem8113242 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term169 A B P p lt2 s a f g) = (term142 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8113241 A B P p g a) (@lem8113240 A B P lt2 s a f g)). Qed.
Lemma lem8113243 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8113244 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term175 A B P p lt2 s a f g) = (term176 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8113243) (@lem8113242 A B P p lt2 s a f g)). Qed.
Lemma lem8113245 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term172 A B P lt2 s a f g z) = (term129 A B P lt2 s a f g z).
Proof. exact (eq_refl (term172 A B P lt2 s a f g z)). Qed.
Lemma lem8113246 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term140 A B P p g a) = (term140 A B P p g a).
Proof. exact (eq_refl (term140 A B P p g a)). Qed.
Lemma lem8113247 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term177 A B P p lt2 s a f g z) = (term178 A B P p lt2 s a f g z).
Proof. exact (MK_COMB (@lem8113246 A B P p g a) (@lem8113245 A B P lt2 s a f g z)). Qed.
Lemma lem8113248 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term179 A B P p lt2 s a f g) = (term180 A B P p lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8113247 A B P p lt2 s a f g z)). Qed.
Lemma lem8113249 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8113250 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term170 A B P p lt2 s a f g) = (term181 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8113249 A) (@lem8113248 A B P p lt2 s a f g)). Qed.
Lemma lem8113251 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : ((term169 A B P p lt2 s a f g) = (term170 A B P p lt2 s a f g)) = ((term142 A B P p lt2 s a f g) = (term181 A B P p lt2 s a f g)).
Proof. exact (MK_COMB (@lem8113244 A B P p lt2 s a f g) (@lem8113250 A B P p lt2 s a f g)). Qed.
Lemma lem8113252 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term142 A B P p lt2 s a f g) = (term181 A B P p lt2 s a f g).
Proof. exact (EQ_MP (@lem8113251 A B P p lt2 s a f g) (@lem8113236 A B P p lt2 s a f g)). Qed.
Lemma lem8113253 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term140 A B P p f a) = (term140 A B P p f a).
Proof. exact (eq_refl (term140 A B P p f a)). Qed.
Lemma lem8113254 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term145 A B P p lt2 s a f g) = (term182 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8113253 A B P p f a) (@lem8113252 A B P p lt2 s a f g)). Qed.
Lemma lem8113256 {A : Type'} (P : Prop) (Q : A -> Prop) : (term167 A P Q) = (term168 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem8113257 {A : Type'} (P : Prop) (Q : A -> Prop) : (term167 A P Q) = (term168 A P Q).
Proof. exact (@lem8113256 A P Q). Qed.
Lemma lem8113258 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term183 A B P p lt2 s a f g) = (term184 A B P p lt2 s a f g).
Proof. exact (@lem8113257 A (term171 A B P p f a) (term180 A B P p lt2 s a f g)). Qed.
Lemma lem8113259 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term185 A B P p lt2 s a f g z) = (term178 A B P p lt2 s a f g z).
Proof. exact (eq_refl (term185 A B P p lt2 s a f g z)). Qed.
Lemma lem8113260 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term186 A B P p lt2 s a f g) = (term180 A B P p lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8113259 A B P p lt2 s a f g z)). Qed.
Lemma lem8113261 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8113262 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term187 A B P p lt2 s a f g) = (term181 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8113261 A) (@lem8113260 A B P p lt2 s a f g)). Qed.
Lemma lem8113263 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term140 A B P p f a) = (term140 A B P p f a).
Proof. exact (eq_refl (term140 A B P p f a)). Qed.
Lemma lem8113264 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term183 A B P p lt2 s a f g) = (term182 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8113263 A B P p f a) (@lem8113262 A B P p lt2 s a f g)). Qed.
Lemma lem8113265 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8113266 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term188 A B P p lt2 s a f g) = (term189 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8113265) (@lem8113264 A B P p lt2 s a f g)). Qed.
Lemma lem8113267 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term185 A B P p lt2 s a f g z) = (term178 A B P p lt2 s a f g z).
Proof. exact (eq_refl (term185 A B P p lt2 s a f g z)). Qed.
Lemma lem8113268 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term140 A B P p f a) = (term140 A B P p f a).
Proof. exact (eq_refl (term140 A B P p f a)). Qed.
Lemma lem8113269 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term190 A B P p lt2 s a f g z) = (term191 A B P p lt2 s a f g z).
Proof. exact (MK_COMB (@lem8113268 A B P p f a) (@lem8113267 A B P p lt2 s a f g z)). Qed.
Lemma lem8113270 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term192 A B P p lt2 s a f g) = (term193 A B P p lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8113269 A B P p lt2 s a f g z)). Qed.
Lemma lem8113271 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8113272 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term184 A B P p lt2 s a f g) = (term194 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8113271 A) (@lem8113270 A B P p lt2 s a f g)). Qed.
Lemma lem8113273 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : ((term183 A B P p lt2 s a f g) = (term184 A B P p lt2 s a f g)) = ((term182 A B P p lt2 s a f g) = (term194 A B P p lt2 s a f g)).
Proof. exact (MK_COMB (@lem8113266 A B P p lt2 s a f g) (@lem8113272 A B P p lt2 s a f g)). Qed.
Lemma lem8113274 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term182 A B P p lt2 s a f g) = (term194 A B P p lt2 s a f g).
Proof. exact (EQ_MP (@lem8113273 A B P p lt2 s a f g) (@lem8113258 A B P p lt2 s a f g)). Qed.
Lemma lem8113275 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term145 A B P p lt2 s a f g) = (term194 A B P p lt2 s a f g).
Proof. exact (TRANS (@lem8113254 A B P p lt2 s a f g) (@lem8113274 A B P p lt2 s a f g)). Qed.
Lemma lem8113276 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8113277 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term148 A B P p lt2 s a f g) = (term195 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8113276) (@lem8113275 A B P p lt2 s a f g)). Qed.
Lemma lem8113278 {A B C P : Type'} (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : ((y f a) = (y g a)) = ((y f a) = (y g a)).
Proof. exact (eq_refl ((y f a) = (y g a))). Qed.
Lemma lem8113279 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term158 A B C P p lt2 s f y g a) = (term292 A B C P p lt2 s f y g a).
Proof. exact (MK_COMB (@lem8113277 A B P p lt2 s a f g) (@lem8113278 A B C P f y g a)). Qed.
Lemma lem8113281 {A : Type'} (P : A -> Prop) (Q : Prop) : (term197 A P Q) = (term198 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem8113282 {A : Type'} (P : A -> Prop) (Q : Prop) : (term197 A P Q) = (term198 A P Q).
Proof. exact (@lem8113281 A P Q). Qed.
Lemma lem8113283 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term293 A B C P p lt2 s f y g a) = (term294 A B C P p lt2 s f y g a).
Proof. exact (@lem8113282 A (term193 A B P p lt2 s a f g) ((y f a) = (y g a))). Qed.
Lemma lem8113284 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term201 A B P p lt2 s a f g z) = (term191 A B P p lt2 s a f g z).
Proof. exact (eq_refl (term201 A B P p lt2 s a f g z)). Qed.
Lemma lem8113285 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term202 A B P p lt2 s a f g) = (term193 A B P p lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8113284 A B P p lt2 s a f g z)). Qed.
Lemma lem8113286 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8113287 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term203 A B P p lt2 s a f g) = (term194 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8113286 A) (@lem8113285 A B P p lt2 s a f g)). Qed.
Lemma lem8113288 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8113289 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term204 A B P p lt2 s a f g) = (term195 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8113288) (@lem8113287 A B P p lt2 s a f g)). Qed.
Lemma lem8113290 {A B C P : Type'} (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : ((y f a) = (y g a)) = ((y f a) = (y g a)).
Proof. exact (eq_refl ((y f a) = (y g a))). Qed.
Lemma lem8113291 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term293 A B C P p lt2 s f y g a) = (term292 A B C P p lt2 s f y g a).
Proof. exact (MK_COMB (@lem8113289 A B P p lt2 s a f g) (@lem8113290 A B C P f y g a)). Qed.
Lemma lem8113292 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8113293 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term295 A B C P p lt2 s f y g a) = (term296 A B C P p lt2 s f y g a).
Proof. exact (MK_COMB (@lem8113292) (@lem8113291 A B C P p lt2 s f y g a)). Qed.
Lemma lem8113294 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term201 A B P p lt2 s a f g z) = (term191 A B P p lt2 s a f g z).
Proof. exact (eq_refl (term201 A B P p lt2 s a f g z)). Qed.
Lemma lem8113295 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8113296 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term207 A B P p lt2 s a f g z) = (term208 A B P p lt2 s a f g z).
Proof. exact (MK_COMB (@lem8113295) (@lem8113294 A B P p lt2 s a f g z)). Qed.
Lemma lem8113297 {A B C P : Type'} (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : ((y f a) = (y g a)) = ((y f a) = (y g a)).
Proof. exact (eq_refl ((y f a) = (y g a))). Qed.
Lemma lem8113298 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term297 A B C P p lt2 s z f y g a) = (term298 A B C P p lt2 s z f y g a).
Proof. exact (MK_COMB (@lem8113296 A B P p lt2 s a f g z) (@lem8113297 A B C P f y g a)). Qed.
Lemma lem8113299 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term299 A B C P p lt2 s f y g a) = (term300 A B C P p lt2 s f y g a).
Proof. exact (fun_ext (fun z : A => @lem8113298 A B C P p lt2 s z f y g a)). Qed.
Lemma lem8113300 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8113301 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term294 A B C P p lt2 s f y g a) = (term301 A B C P p lt2 s f y g a).
Proof. exact (MK_COMB (@lem8113300 A) (@lem8113299 A B C P p lt2 s f y g a)). Qed.
Lemma lem8113302 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : ((term293 A B C P p lt2 s f y g a) = (term294 A B C P p lt2 s f y g a)) = ((term292 A B C P p lt2 s f y g a) = (term301 A B C P p lt2 s f y g a)).
Proof. exact (MK_COMB (@lem8113293 A B C P p lt2 s f y g a) (@lem8113301 A B C P p lt2 s f y g a)). Qed.
Lemma lem8113303 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term292 A B C P p lt2 s f y g a) = (term301 A B C P p lt2 s f y g a).
Proof. exact (EQ_MP (@lem8113302 A B C P p lt2 s f y g a) (@lem8113283 A B C P p lt2 s f y g a)). Qed.
Lemma lem8113304 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term158 A B C P p lt2 s f y g a) = (term301 A B C P p lt2 s f y g a).
Proof. exact (TRANS (@lem8113279 A B C P p lt2 s f y g a) (@lem8113303 A B C P p lt2 s f y g a)). Qed.
Lemma lem8113305 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term159 A B C P p lt2 s f y g) = (term302 A B C P p lt2 s f y g).
Proof. exact (fun_ext (fun a : P => @lem8113304 A B C P p lt2 s f y g a)). Qed.
Lemma lem8113306 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8113307 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term160 A B C P p lt2 s f y g) = (term303 A B C P p lt2 s f y g).
Proof. exact (MK_COMB (@lem8113306 P) (@lem8113305 A B C P p lt2 s f y g)). Qed.
Lemma lem8113309 {A B : Type'} (P : type1413 A B) : (term216 A B P) = (term217 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8113310 {A P : Type'} (P' : type1470 A P) : (term218 A P P') = (term219 A P P').
Proof. exact (@lem8113309 P A P'). Qed.
Lemma lem8113311 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term304 A B C P p lt2 s f y g) = (term305 A B C P p lt2 s f y g).
Proof. exact (@lem8113310 A P (term306 A B C P p lt2 s f y g)). Qed.
Lemma lem8113312 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term307 A B C P p lt2 s f y g a) = (term300 A B C P p lt2 s f y g a).
Proof. exact (eq_refl (term307 A B C P p lt2 s f y g a)). Qed.
Lemma lem8113313 {A : Type'} (z : A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8113314 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) (z : A) : (term308 A B C P p lt2 s f y g a z) = (term309 A B C P p lt2 s f y g a z).
Proof. exact (MK_COMB (@lem8113312 A B C P p lt2 s f y g a) (@lem8113313 A z)). Qed.
Lemma lem8113315 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term309 A B C P p lt2 s f y g a z) = (term298 A B C P p lt2 s z f y g a).
Proof. exact (eq_refl (term309 A B C P p lt2 s f y g a z)). Qed.
Lemma lem8113316 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term308 A B C P p lt2 s f y g a z) = (term298 A B C P p lt2 s z f y g a).
Proof. exact (TRANS (@lem8113314 A B C P p lt2 s f y g a z) (@lem8113315 A B C P p lt2 s z f y g a)). Qed.
Lemma lem8113317 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term310 A B C P p lt2 s f y g a) = (term300 A B C P p lt2 s f y g a).
Proof. exact (fun_ext (fun z : A => @lem8113316 A B C P p lt2 s z f y g a)). Qed.
Lemma lem8113318 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8113319 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term311 A B C P p lt2 s f y g a) = (term301 A B C P p lt2 s f y g a).
Proof. exact (MK_COMB (@lem8113318 A) (@lem8113317 A B C P p lt2 s f y g a)). Qed.
Lemma lem8113320 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term312 A B C P p lt2 s f y g) = (term302 A B C P p lt2 s f y g).
Proof. exact (fun_ext (fun a : P => @lem8113319 A B C P p lt2 s f y g a)). Qed.
Lemma lem8113321 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8113322 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term304 A B C P p lt2 s f y g) = (term303 A B C P p lt2 s f y g).
Proof. exact (MK_COMB (@lem8113321 P) (@lem8113320 A B C P p lt2 s f y g)). Qed.
Lemma lem8113323 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8113324 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term313 A B C P p lt2 s f y g) = (term314 A B C P p lt2 s f y g).
Proof. exact (MK_COMB (@lem8113323) (@lem8113322 A B C P p lt2 s f y g)). Qed.
Lemma lem8113325 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term307 A B C P p lt2 s f y g a) = (term300 A B C P p lt2 s f y g a).
Proof. exact (eq_refl (term307 A B C P p lt2 s f y g a)). Qed.
Lemma lem8113326 {A P : Type'} (z : P -> A) (a : P) : (z a) = (z a).
Proof. exact (eq_refl (z a)). Qed.
Lemma lem8113327 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (z : P -> A) (a : P) : (term315 A B C P p lt2 s f y g z a) = (term316 A B C P p lt2 s f y g z a).
Proof. exact (MK_COMB (@lem8113325 A B C P p lt2 s f y g a) (@lem8113326 A P z a)). Qed.
Lemma lem8113328 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term316 A B C P p lt2 s f y g z a) = (term317 A B C P p lt2 s z f y g a).
Proof. exact (eq_refl (term316 A B C P p lt2 s f y g z a)). Qed.
Lemma lem8113329 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term315 A B C P p lt2 s f y g z a) = (term317 A B C P p lt2 s z f y g a).
Proof. exact (TRANS (@lem8113327 A B C P p lt2 s f y g z a) (@lem8113328 A B C P p lt2 s z f y g a)). Qed.
Lemma lem8113330 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term318 A B C P p lt2 s f y g z) = (term319 A B C P p lt2 s z f y g).
Proof. exact (fun_ext (fun a : P => @lem8113329 A B C P p lt2 s z f y g a)). Qed.
Lemma lem8113331 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8113332 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term320 A B C P p lt2 s f y g z) = (term321 A B C P p lt2 s z f y g).
Proof. exact (MK_COMB (@lem8113331 P) (@lem8113330 A B C P p lt2 s z f y g)). Qed.
Lemma lem8113333 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term322 A B C P p lt2 s f y g) = (term323 A B C P p lt2 s f y g).
Proof. exact (fun_ext (fun z : P -> A => @lem8113332 A B C P p lt2 s z f y g)). Qed.
Lemma lem8113334 {A P : Type'} : (@ex (P -> A)) = (@ex (P -> A)).
Proof. exact (eq_refl (@ex (P -> A))). Qed.
Lemma lem8113335 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term305 A B C P p lt2 s f y g) = (term324 A B C P p lt2 s f y g).
Proof. exact (MK_COMB (@lem8113334 A P) (@lem8113333 A B C P p lt2 s f y g)). Qed.
Lemma lem8113336 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : ((term304 A B C P p lt2 s f y g) = (term305 A B C P p lt2 s f y g)) = ((term303 A B C P p lt2 s f y g) = (term324 A B C P p lt2 s f y g)).
Proof. exact (MK_COMB (@lem8113324 A B C P p lt2 s f y g) (@lem8113335 A B C P p lt2 s f y g)). Qed.
Lemma lem8113337 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term303 A B C P p lt2 s f y g) = (term324 A B C P p lt2 s f y g).
Proof. exact (EQ_MP (@lem8113336 A B C P p lt2 s f y g) (@lem8113311 A B C P p lt2 s f y g)). Qed.
Lemma lem8113338 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term160 A B C P p lt2 s f y g) = (term324 A B C P p lt2 s f y g).
Proof. exact (TRANS (@lem8113307 A B C P p lt2 s f y g) (@lem8113337 A B C P p lt2 s f y g)). Qed.
Lemma lem8113339 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term161 A B C P p lt2 s f y) = (term325 A B C P p lt2 s f y).
Proof. exact (fun_ext (fun g : A -> B => @lem8113338 A B C P p lt2 s f y g)). Qed.
Lemma lem8113340 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8113341 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term162 A B C P p lt2 s f y) = (term326 A B C P p lt2 s f y).
Proof. exact (MK_COMB (@lem8113340 A B) (@lem8113339 A B C P p lt2 s f y)). Qed.
Lemma lem8113343 {A B : Type'} (P : type1413 A B) : (term216 A B P) = (term217 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8113344 {A B P : Type'} (P' : type537 A B P) : (term243 A B P P') = (term244 A B P P').
Proof. exact (@lem8113343 (A -> B) (P -> A) P'). Qed.
Lemma lem8113345 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term327 A B C P p lt2 s f y) = (term328 A B C P p lt2 s f y).
Proof. exact (@lem8113344 A B P (term329 A B C P p lt2 s f y)). Qed.
Lemma lem8113346 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term330 A B C P p lt2 s f y g) = (term323 A B C P p lt2 s f y g).
Proof. exact (eq_refl (term330 A B C P p lt2 s f y g)). Qed.
Lemma lem8113347 {A P : Type'} (z : P -> A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8113348 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (z : P -> A) : (term331 A B C P p lt2 s f y g z) = (term332 A B C P p lt2 s f y g z).
Proof. exact (MK_COMB (@lem8113346 A B C P p lt2 s f y g) (@lem8113347 A P z)). Qed.
Lemma lem8113349 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term332 A B C P p lt2 s f y g z) = (term321 A B C P p lt2 s z f y g).
Proof. exact (eq_refl (term332 A B C P p lt2 s f y g z)). Qed.
Lemma lem8113350 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term331 A B C P p lt2 s f y g z) = (term321 A B C P p lt2 s z f y g).
Proof. exact (TRANS (@lem8113348 A B C P p lt2 s f y g z) (@lem8113349 A B C P p lt2 s z f y g)). Qed.
Lemma lem8113351 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term333 A B C P p lt2 s f y g) = (term323 A B C P p lt2 s f y g).
Proof. exact (fun_ext (fun z : P -> A => @lem8113350 A B C P p lt2 s z f y g)). Qed.
Lemma lem8113352 {A P : Type'} : (@ex (P -> A)) = (@ex (P -> A)).
Proof. exact (eq_refl (@ex (P -> A))). Qed.
Lemma lem8113353 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term334 A B C P p lt2 s f y g) = (term324 A B C P p lt2 s f y g).
Proof. exact (MK_COMB (@lem8113352 A P) (@lem8113351 A B C P p lt2 s f y g)). Qed.
Lemma lem8113354 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term335 A B C P p lt2 s f y) = (term325 A B C P p lt2 s f y).
Proof. exact (fun_ext (fun g : A -> B => @lem8113353 A B C P p lt2 s f y g)). Qed.
Lemma lem8113355 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8113356 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term327 A B C P p lt2 s f y) = (term326 A B C P p lt2 s f y).
Proof. exact (MK_COMB (@lem8113355 A B) (@lem8113354 A B C P p lt2 s f y)). Qed.
Lemma lem8113357 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8113358 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term336 A B C P p lt2 s f y) = (term337 A B C P p lt2 s f y).
Proof. exact (MK_COMB (@lem8113357) (@lem8113356 A B C P p lt2 s f y)). Qed.
Lemma lem8113359 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term330 A B C P p lt2 s f y g) = (term323 A B C P p lt2 s f y g).
Proof. exact (eq_refl (term330 A B C P p lt2 s f y g)). Qed.
Lemma lem8113360 {A B P : Type'} (z : type557 A B P) (g : A -> B) : (z g) = (z g).
Proof. exact (eq_refl (z g)). Qed.
Lemma lem8113361 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (z : type557 A B P) (g : A -> B) : (term338 A B C P p lt2 s f y z g) = (term339 A B C P p lt2 s f y z g).
Proof. exact (MK_COMB (@lem8113359 A B C P p lt2 s f y g) (@lem8113360 A B P z g)). Qed.
Lemma lem8113362 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term339 A B C P p lt2 s f y z g) = (term340 A B C P p lt2 s z f y g).
Proof. exact (eq_refl (term339 A B C P p lt2 s f y z g)). Qed.
Lemma lem8113363 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term338 A B C P p lt2 s f y z g) = (term340 A B C P p lt2 s z f y g).
Proof. exact (TRANS (@lem8113361 A B C P p lt2 s f y z g) (@lem8113362 A B C P p lt2 s z f y g)). Qed.
Lemma lem8113364 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (y : type564 A B C P) : (term341 A B C P p lt2 s f y z) = (term342 A B C P p lt2 s z f y).
Proof. exact (fun_ext (fun g : A -> B => @lem8113363 A B C P p lt2 s z f y g)). Qed.
Lemma lem8113365 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8113366 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (y : type564 A B C P) : (term343 A B C P p lt2 s f y z) = (term344 A B C P p lt2 s z f y).
Proof. exact (MK_COMB (@lem8113365 A B) (@lem8113364 A B C P p lt2 s z f y)). Qed.
Lemma lem8113367 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term345 A B C P p lt2 s f y) = (term346 A B C P p lt2 s f y).
Proof. exact (fun_ext (fun z : type557 A B P => @lem8113366 A B C P p lt2 s z f y)). Qed.
Lemma lem8113368 {A B P : Type'} : (@ex ((A -> B) -> P -> A)) = (@ex ((A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> P -> A))). Qed.
Lemma lem8113369 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term328 A B C P p lt2 s f y) = (term347 A B C P p lt2 s f y).
Proof. exact (MK_COMB (@lem8113368 A B P) (@lem8113367 A B C P p lt2 s f y)). Qed.
Lemma lem8113370 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : ((term327 A B C P p lt2 s f y) = (term328 A B C P p lt2 s f y)) = ((term326 A B C P p lt2 s f y) = (term347 A B C P p lt2 s f y)).
Proof. exact (MK_COMB (@lem8113358 A B C P p lt2 s f y) (@lem8113369 A B C P p lt2 s f y)). Qed.
Lemma lem8113371 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term326 A B C P p lt2 s f y) = (term347 A B C P p lt2 s f y).
Proof. exact (EQ_MP (@lem8113370 A B C P p lt2 s f y) (@lem8113345 A B C P p lt2 s f y)). Qed.
Lemma lem8113372 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term162 A B C P p lt2 s f y) = (term347 A B C P p lt2 s f y).
Proof. exact (TRANS (@lem8113341 A B C P p lt2 s f y) (@lem8113371 A B C P p lt2 s f y)). Qed.
Lemma lem8113373 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term163 A B C P p lt2 s y) = (term348 A B C P p lt2 s y).
Proof. exact (fun_ext (fun f : A -> B => @lem8113372 A B C P p lt2 s f y)). Qed.
Lemma lem8113374 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8113375 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term164 A B C P p lt2 s y) = (term349 A B C P p lt2 s y).
Proof. exact (MK_COMB (@lem8113374 A B) (@lem8113373 A B C P p lt2 s y)). Qed.
Lemma lem8113377 {A B : Type'} (P : type1413 A B) : (term216 A B P) = (term217 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8113378 {A B P : Type'} (P' : type495 A B P) : (term268 A B P P') = (term269 A B P P').
Proof. exact (@lem8113377 (A -> B) (type557 A B P) P'). Qed.
Lemma lem8113379 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term350 A B C P p lt2 s y) = (term351 A B C P p lt2 s y).
Proof. exact (@lem8113378 A B P (term352 A B C P p lt2 s y)). Qed.
Lemma lem8113380 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term353 A B C P p lt2 s y f) = (term346 A B C P p lt2 s f y).
Proof. exact (eq_refl (term353 A B C P p lt2 s y f)). Qed.
Lemma lem8113381 {A B P : Type'} (z : type557 A B P) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8113382 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (z : type557 A B P) : (term354 A B C P p lt2 s y f z) = (term355 A B C P p lt2 s f y z).
Proof. exact (MK_COMB (@lem8113380 A B C P p lt2 s f y) (@lem8113381 A B P z)). Qed.
Lemma lem8113383 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (y : type564 A B C P) : (term355 A B C P p lt2 s f y z) = (term344 A B C P p lt2 s z f y).
Proof. exact (eq_refl (term355 A B C P p lt2 s f y z)). Qed.
Lemma lem8113384 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (y : type564 A B C P) : (term354 A B C P p lt2 s y f z) = (term344 A B C P p lt2 s z f y).
Proof. exact (TRANS (@lem8113382 A B C P p lt2 s f y z) (@lem8113383 A B C P p lt2 s z f y)). Qed.
Lemma lem8113385 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term356 A B C P p lt2 s y f) = (term346 A B C P p lt2 s f y).
Proof. exact (fun_ext (fun z : type557 A B P => @lem8113384 A B C P p lt2 s z f y)). Qed.
Lemma lem8113386 {A B P : Type'} : (@ex ((A -> B) -> P -> A)) = (@ex ((A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> P -> A))). Qed.
Lemma lem8113387 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term357 A B C P p lt2 s y f) = (term347 A B C P p lt2 s f y).
Proof. exact (MK_COMB (@lem8113386 A B P) (@lem8113385 A B C P p lt2 s f y)). Qed.
Lemma lem8113388 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term358 A B C P p lt2 s y) = (term348 A B C P p lt2 s y).
Proof. exact (fun_ext (fun f : A -> B => @lem8113387 A B C P p lt2 s f y)). Qed.
Lemma lem8113389 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8113390 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term350 A B C P p lt2 s y) = (term349 A B C P p lt2 s y).
Proof. exact (MK_COMB (@lem8113389 A B) (@lem8113388 A B C P p lt2 s y)). Qed.
Lemma lem8113391 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8113392 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term359 A B C P p lt2 s y) = (term360 A B C P p lt2 s y).
Proof. exact (MK_COMB (@lem8113391) (@lem8113390 A B C P p lt2 s y)). Qed.
Lemma lem8113393 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term353 A B C P p lt2 s y f) = (term346 A B C P p lt2 s f y).
Proof. exact (eq_refl (term353 A B C P p lt2 s y f)). Qed.
Lemma lem8113394 {A B P : Type'} (z : type518 A B P) (f : A -> B) : (z f) = (z f).
Proof. exact (eq_refl (z f)). Qed.
Lemma lem8113395 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) (z : type518 A B P) (f : A -> B) : (term361 A B C P p lt2 s y z f) = (term362 A B C P p lt2 s y z f).
Proof. exact (MK_COMB (@lem8113393 A B C P p lt2 s f y) (@lem8113394 A B P z f)). Qed.
Lemma lem8113396 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (y : type564 A B C P) : (term362 A B C P p lt2 s y z f) = (term363 A B C P p lt2 s z f y).
Proof. exact (eq_refl (term362 A B C P p lt2 s y z f)). Qed.
Lemma lem8113397 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (y : type564 A B C P) : (term361 A B C P p lt2 s y z f) = (term363 A B C P p lt2 s z f y).
Proof. exact (TRANS (@lem8113395 A B C P p lt2 s y z f) (@lem8113396 A B C P p lt2 s z f y)). Qed.
Lemma lem8113398 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (y : type564 A B C P) : (term364 A B C P p lt2 s y z) = (term365 A B C P p lt2 s z y).
Proof. exact (fun_ext (fun f : A -> B => @lem8113397 A B C P p lt2 s z f y)). Qed.
Lemma lem8113399 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8113400 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (y : type564 A B C P) : (term366 A B C P p lt2 s y z) = (term367 A B C P p lt2 s z y).
Proof. exact (MK_COMB (@lem8113399 A B) (@lem8113398 A B C P p lt2 s z y)). Qed.
Lemma lem8113401 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term368 A B C P p lt2 s y) = (term369 A B C P p lt2 s y).
Proof. exact (fun_ext (fun z : type518 A B P => @lem8113400 A B C P p lt2 s z y)). Qed.
Lemma lem8113402 {A B P : Type'} : (@ex ((A -> B) -> (A -> B) -> P -> A)) = (@ex ((A -> B) -> (A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> P -> A))). Qed.
Lemma lem8113403 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term351 A B C P p lt2 s y) = (term370 A B C P p lt2 s y).
Proof. exact (MK_COMB (@lem8113402 A B P) (@lem8113401 A B C P p lt2 s y)). Qed.
Lemma lem8113404 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : ((term350 A B C P p lt2 s y) = (term351 A B C P p lt2 s y)) = ((term349 A B C P p lt2 s y) = (term370 A B C P p lt2 s y)).
Proof. exact (MK_COMB (@lem8113392 A B C P p lt2 s y) (@lem8113403 A B C P p lt2 s y)). Qed.
Lemma lem8113405 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term349 A B C P p lt2 s y) = (term370 A B C P p lt2 s y).
Proof. exact (EQ_MP (@lem8113404 A B C P p lt2 s y) (@lem8113379 A B C P p lt2 s y)). Qed.
Lemma lem8113406 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term164 A B C P p lt2 s y) = (term370 A B C P p lt2 s y).
Proof. exact (TRANS (@lem8113375 A B C P p lt2 s y) (@lem8113405 A B C P p lt2 s y)). Qed.
Lemma lem8113407 {A B C D P : Type'} (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term166 A B C D P g p lt2 s y) = (term371 A B C D P g p lt2 s y).
Proof. exact (MK_COMB (@lem8113232 A B C D P p lt2 s g) (@lem8113406 A B C P p lt2 s y)). Qed.
Lemma lem8113409 {A : Type'} (P : A -> Prop) (Q : Prop) : (term372 A P Q) = (term373 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem8113410 {A B P : Type'} (P' : type96 A B P) (Q : Prop) : (term374 A B P P' Q) = (term375 A B P P' Q).
Proof. exact (@lem8113409 (type518 A B P) P' Q). Qed.
Lemma lem8113411 {A B C D P : Type'} (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term376 A B C D P g p lt2 s y) = (term377 A B C D P g p lt2 s y).
Proof. exact (@lem8113410 A B P (term289 A B C D P p lt2 s g) (term370 A B C P p lt2 s y)). Qed.
Lemma lem8113412 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (g : type565 A B C D P) : (term378 A B C D P p lt2 s g z) = (term287 A B C D P p lt2 s z g).
Proof. exact (eq_refl (term378 A B C D P p lt2 s g z)). Qed.
Lemma lem8113413 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) : (term379 A B C D P p lt2 s g) = (term289 A B C D P p lt2 s g).
Proof. exact (fun_ext (fun z : type518 A B P => @lem8113412 A B C D P p lt2 s z g)). Qed.
Lemma lem8113414 {A B P : Type'} : (@ex ((A -> B) -> (A -> B) -> P -> A)) = (@ex ((A -> B) -> (A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> P -> A))). Qed.
Lemma lem8113415 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) : (term380 A B C D P p lt2 s g) = (term290 A B C D P p lt2 s g).
Proof. exact (MK_COMB (@lem8113414 A B P) (@lem8113413 A B C D P p lt2 s g)). Qed.
Lemma lem8113416 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8113417 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) : (term381 A B C D P p lt2 s g) = (term291 A B C D P p lt2 s g).
Proof. exact (MK_COMB (@lem8113416) (@lem8113415 A B C D P p lt2 s g)). Qed.
Lemma lem8113418 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term370 A B C P p lt2 s y) = (term370 A B C P p lt2 s y).
Proof. exact (eq_refl (term370 A B C P p lt2 s y)). Qed.
Lemma lem8113419 {A B C D P : Type'} (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term376 A B C D P g p lt2 s y) = (term371 A B C D P g p lt2 s y).
Proof. exact (MK_COMB (@lem8113417 A B C D P p lt2 s g) (@lem8113418 A B C P p lt2 s y)). Qed.
Lemma lem8113420 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8113421 {A B C D P : Type'} (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term382 A B C D P g p lt2 s y) = (term383 A B C D P g p lt2 s y).
Proof. exact (MK_COMB (@lem8113420) (@lem8113419 A B C D P g p lt2 s y)). Qed.
Lemma lem8113422 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (g : type565 A B C D P) : (term378 A B C D P p lt2 s g z) = (term287 A B C D P p lt2 s z g).
Proof. exact (eq_refl (term378 A B C D P p lt2 s g z)). Qed.
Lemma lem8113423 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8113424 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (g : type565 A B C D P) : (term384 A B C D P p lt2 s g z) = (term385 A B C D P p lt2 s z g).
Proof. exact (MK_COMB (@lem8113423) (@lem8113422 A B C D P p lt2 s z g)). Qed.
Lemma lem8113425 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term370 A B C P p lt2 s y) = (term370 A B C P p lt2 s y).
Proof. exact (eq_refl (term370 A B C P p lt2 s y)). Qed.
Lemma lem8113426 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term386 A B C D P g z p lt2 s y) = (term387 A B C D P z g p lt2 s y).
Proof. exact (MK_COMB (@lem8113424 A B C D P p lt2 s z g) (@lem8113425 A B C P p lt2 s y)). Qed.
Lemma lem8113427 {A B C D P : Type'} (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term388 A B C D P g p lt2 s y) = (term389 A B C D P g p lt2 s y).
Proof. exact (fun_ext (fun z : type518 A B P => @lem8113426 A B C D P z g p lt2 s y)). Qed.
Lemma lem8113428 {A B P : Type'} : (@ex ((A -> B) -> (A -> B) -> P -> A)) = (@ex ((A -> B) -> (A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> P -> A))). Qed.
Lemma lem8113429 {A B C D P : Type'} (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term377 A B C D P g p lt2 s y) = (term390 A B C D P g p lt2 s y).
Proof. exact (MK_COMB (@lem8113428 A B P) (@lem8113427 A B C D P g p lt2 s y)). Qed.
Lemma lem8113430 {A B C D P : Type'} (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : ((term376 A B C D P g p lt2 s y) = (term377 A B C D P g p lt2 s y)) = ((term371 A B C D P g p lt2 s y) = (term390 A B C D P g p lt2 s y)).
Proof. exact (MK_COMB (@lem8113421 A B C D P g p lt2 s y) (@lem8113429 A B C D P g p lt2 s y)). Qed.
Lemma lem8113431 {A B C D P : Type'} (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term371 A B C D P g p lt2 s y) = (term390 A B C D P g p lt2 s y).
Proof. exact (EQ_MP (@lem8113430 A B C D P g p lt2 s y) (@lem8113411 A B C D P g p lt2 s y)). Qed.
Lemma lem8113433 {A : Type'} (P : Prop) (Q : A -> Prop) : (term391 A P Q) = (term392 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8113434 {A B P : Type'} (P' : Prop) (Q : type96 A B P) : (term393 A B P P' Q) = (term394 A B P P' Q).
Proof. exact (@lem8113433 (type518 A B P) P' Q). Qed.
Lemma lem8113435 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term395 A B C D P z g p lt2 s y) = (term396 A B C D P z g p lt2 s y).
Proof. exact (@lem8113434 A B P (term287 A B C D P p lt2 s z g) (term369 A B C P p lt2 s y)). Qed.
Lemma lem8113436 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (y : type564 A B C P) : (term397 A B C P p lt2 s y z) = (term367 A B C P p lt2 s z y).
Proof. exact (eq_refl (term397 A B C P p lt2 s y z)). Qed.
Lemma lem8113437 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term398 A B C P p lt2 s y) = (term369 A B C P p lt2 s y).
Proof. exact (fun_ext (fun z : type518 A B P => @lem8113436 A B C P p lt2 s z y)). Qed.
Lemma lem8113438 {A B P : Type'} : (@ex ((A -> B) -> (A -> B) -> P -> A)) = (@ex ((A -> B) -> (A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> P -> A))). Qed.
Lemma lem8113439 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term399 A B C P p lt2 s y) = (term370 A B C P p lt2 s y).
Proof. exact (MK_COMB (@lem8113438 A B P) (@lem8113437 A B C P p lt2 s y)). Qed.
Lemma lem8113440 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (g : type565 A B C D P) : (term385 A B C D P p lt2 s z g) = (term385 A B C D P p lt2 s z g).
Proof. exact (eq_refl (term385 A B C D P p lt2 s z g)). Qed.
Lemma lem8113441 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term395 A B C D P z g p lt2 s y) = (term387 A B C D P z g p lt2 s y).
Proof. exact (MK_COMB (@lem8113440 A B C D P p lt2 s z g) (@lem8113439 A B C P p lt2 s y)). Qed.
Lemma lem8113442 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8113443 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term400 A B C D P z g p lt2 s y) = (term401 A B C D P z g p lt2 s y).
Proof. exact (MK_COMB (@lem8113442) (@lem8113441 A B C D P z g p lt2 s y)). Qed.
Lemma lem8113444 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) : (term397 A B C P p lt2 s y z') = (term367 A B C P p lt2 s z' y).
Proof. exact (eq_refl (term397 A B C P p lt2 s y z')). Qed.
Lemma lem8113445 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (g : type565 A B C D P) : (term385 A B C D P p lt2 s z g) = (term385 A B C D P p lt2 s z g).
Proof. exact (eq_refl (term385 A B C D P p lt2 s z g)). Qed.
Lemma lem8113446 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) : (term402 A B C D P z g p lt2 s y z') = (term403 A B C D P z g p lt2 s z' y).
Proof. exact (MK_COMB (@lem8113445 A B C D P p lt2 s z g) (@lem8113444 A B C P p lt2 s z' y)). Qed.
Lemma lem8113447 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term404 A B C D P z g p lt2 s y) = (term405 A B C D P z g p lt2 s y).
Proof. exact (fun_ext (fun z' : type518 A B P => @lem8113446 A B C D P z g p lt2 s z' y)). Qed.
Lemma lem8113448 {A B P : Type'} : (@ex ((A -> B) -> (A -> B) -> P -> A)) = (@ex ((A -> B) -> (A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> P -> A))). Qed.
Lemma lem8113449 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term396 A B C D P z g p lt2 s y) = (term406 A B C D P z g p lt2 s y).
Proof. exact (MK_COMB (@lem8113448 A B P) (@lem8113447 A B C D P z g p lt2 s y)). Qed.
Lemma lem8113450 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : ((term395 A B C D P z g p lt2 s y) = (term396 A B C D P z g p lt2 s y)) = ((term387 A B C D P z g p lt2 s y) = (term406 A B C D P z g p lt2 s y)).
Proof. exact (MK_COMB (@lem8113443 A B C D P z g p lt2 s y) (@lem8113449 A B C D P z g p lt2 s y)). Qed.
Lemma lem8113451 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term387 A B C D P z g p lt2 s y) = (term406 A B C D P z g p lt2 s y).
Proof. exact (EQ_MP (@lem8113450 A B C D P z g p lt2 s y) (@lem8113435 A B C D P z g p lt2 s y)). Qed.
Lemma lem8113452 {A B C D P : Type'} (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term389 A B C D P g p lt2 s y) = (term407 A B C D P g p lt2 s y).
Proof. exact (fun_ext (fun z : type518 A B P => @lem8113451 A B C D P z g p lt2 s y)). Qed.
Lemma lem8113453 {A B P : Type'} : (@ex ((A -> B) -> (A -> B) -> P -> A)) = (@ex ((A -> B) -> (A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> P -> A))). Qed.
Lemma lem8113454 {A B C D P : Type'} (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term390 A B C D P g p lt2 s y) = (term408 A B C D P g p lt2 s y).
Proof. exact (MK_COMB (@lem8113453 A B P) (@lem8113452 A B C D P g p lt2 s y)). Qed.
Lemma lem8113455 {A B C D P : Type'} (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term371 A B C D P g p lt2 s y) = (term408 A B C D P g p lt2 s y).
Proof. exact (TRANS (@lem8113431 A B C D P g p lt2 s y) (@lem8113454 A B C D P g p lt2 s y)). Qed.
Lemma lem8113457 {A B C D P : Type'} (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term166 A B C D P g p lt2 s y) = (term408 A B C D P g p lt2 s y).
Proof. exact (TRANS (@lem8113407 A B C D P g p lt2 s y) (@lem8113455 A B C D P g p lt2 s y)). Qed.
Lemma lem8113458 {A B C D P : Type'} (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term29 A B C D P g p lt2 s y) = (term408 A B C D P g p lt2 s y).
Proof. exact (TRANS (@lem8112847 A B C D P g p lt2 s y) (@lem8113457 A B C D P g p lt2 s y)). Qed.
Lemma lem8113459 {A B C D P : Type'} (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) (h1 : term29 A B C D P g p lt2 s y) : term408 A B C D P g p lt2 s y.
Proof. exact (EQ_MP (@lem8113458 A B C D P g p lt2 s y) (@lem8112750 A B C D P g p lt2 s y h1)). Qed.
Lemma lem8113468 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (z : A) : (term107 A B P lt2 s a f g' z) = (term409 A B P lt2 s a f g' z).
Proof. exact (@lem17265 (term130 A P lt2 z s a) ((f z) = (g' z))). Qed.
Lemma lem8113469 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) : (term108 A B P lt2 s a f g') = (term410 A B P lt2 s a f g').
Proof. exact (fun_ext (fun z : A => @lem8113468 A B P lt2 s a f g' z)). Qed.
Lemma lem8113470 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8113471 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) : (term109 A B P lt2 s a f g') = (term411 A B P lt2 s a f g').
Proof. exact (MK_COMB (@lem8113470 A) (@lem8113469 A B P lt2 s a f g')). Qed.
Lemma lem8113473 {A B P : Type'} (p : type560 A B P) (g' : A -> B) (a : P) : (term110 A B P p g' a) = (term110 A B P p g' a).
Proof. exact (eq_refl (term110 A B P p g' a)). Qed.
Lemma lem8113474 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) : (term111 A B P p lt2 s a f g') = (term412 A B P p lt2 s a f g').
Proof. exact (MK_COMB (@lem8113473 A B P p g' a) (@lem8113471 A B P lt2 s a f g')). Qed.
Lemma lem8113476 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term110 A B P p f a) = (term110 A B P p f a).
Proof. exact (eq_refl (term110 A B P p f a)). Qed.
Lemma lem8113529 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) : (term35 A B P p lt2 s a f g') = (term413 A B P p lt2 s a f g').
Proof. exact (MK_COMB (@lem8113476 A B P p f a) (@lem8113474 A B P p lt2 s a f g')). Qed.
Lemma lem8113530 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term413 A B P p lt2 s a f g'.
Proof. exact (EQ_MP (@lem8113529 A B P p lt2 s a f g') (@lem8112751 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8113536 {A B C D P : Type'} (f : A -> B) (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) (h1 : term127 A B C D P f g y g' a) : term127 A B C D P f g y g' a.
Proof. exact (h1). Qed.
Lemma lem8113537 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) (h1 : term406 A B C D P z g p lt2 s y) : term406 A B C D P z g p lt2 s y.
Proof. exact (h1). Qed.
Lemma lem8113538 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term403 A B C D P z g p lt2 s z' y.
Proof. exact (h1). Qed.
Lemma lem8113539 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8113544 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113545 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8113544 A B f x). Qed.
Lemma lem8113547 {A B : Type'} (f : A -> B) (z : A) : (f z) = (@I (A -> B) f z).
Proof. exact (@lem8113545 A B f z). Qed.
Lemma lem8113552 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113553 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8113552 A B f x). Qed.
Lemma lem8113555 {A B : Type'} (g' : A -> B) (z : A) : (g' z) = (@I (A -> B) g' z).
Proof. exact (@lem8113553 A B g' z). Qed.
Lemma lem8113556 {A B : Type'} (f : A -> B) (z : A) : (term414 A B f z) = (term415 A B f z).
Proof. exact (MK_COMB (@lem8113539 B) (@lem8113547 A B f z)). Qed.
Lemma lem8113557 {A B : Type'} (f : A -> B) (g' : A -> B) (z : A) : ((f z) = (g' z)) = ((@I (A -> B) f z) = (@I (A -> B) g' z)).
Proof. exact (MK_COMB (@lem8113556 A B f z) (@lem8113555 A B g' z)). Qed.
Lemma lem8113558 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8113565 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113566 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8113565 P A f x). Qed.
Lemma lem8113568 {A P : Type'} (s : P -> A) (a : P) : (s a) = (@I (P -> A) s a).
Proof. exact (@lem8113566 A P s a). Qed.
Lemma lem8113569 {A : Type'} (lt2 : type1402 A) (z : A) : (lt2 z) = (lt2 z).
Proof. exact (eq_refl (lt2 z)). Qed.
Lemma lem8113570 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term130 A P lt2 z s a) = (term416 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8113569 A lt2 z) (@lem8113568 A P s a)). Qed.
Lemma lem8113572 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113573 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem8113572 A (A -> Prop) f x). Qed.
Lemma lem8113574 {A : Type'} (lt2 : type1402 A) (z : A) : (lt2 z) = (@I (A -> A -> Prop) lt2 z).
Proof. exact (@lem8113573 A lt2 z). Qed.
Lemma lem8113575 {A P : Type'} (s : P -> A) (a : P) : (@I (P -> A) s a) = (@I (P -> A) s a).
Proof. exact (eq_refl (@I (P -> A) s a)). Qed.
Lemma lem8113576 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term416 A P lt2 z s a) = (term417 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8113574 A lt2 z) (@lem8113575 A P s a)). Qed.
Lemma lem8113578 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113579 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem8113578 A Prop f x). Qed.
Lemma lem8113580 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term417 A P lt2 z s a) = (term418 A P lt2 z s a).
Proof. exact (@lem8113579 A (@I (A -> A -> Prop) lt2 z) (@I (P -> A) s a)). Qed.
Lemma lem8113581 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term416 A P lt2 z s a) = (term418 A P lt2 z s a).
Proof. exact (TRANS (@lem8113576 A P lt2 z s a) (@lem8113580 A P lt2 z s a)). Qed.
Lemma lem8113582 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term130 A P lt2 z s a) = (term418 A P lt2 z s a).
Proof. exact (TRANS (@lem8113570 A P lt2 z s a) (@lem8113581 A P lt2 z s a)). Qed.
Lemma lem8113583 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term419 A P lt2 z s a) = (term420 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8113558) (@lem8113582 A P lt2 z s a)). Qed.
Lemma lem8113584 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8113585 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term421 A P lt2 z s a) = (term422 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8113584) (@lem8113583 A P lt2 z s a)). Qed.
Lemma lem8113586 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (z : A) : (term409 A B P lt2 s a f g' z) = (term423 A B P lt2 s a f g' z).
Proof. exact (MK_COMB (@lem8113585 A P lt2 z s a) (@lem8113557 A B f g' z)). Qed.
Lemma lem8113587 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) : (term410 A B P lt2 s a f g') = (term424 A B P lt2 s a f g').
Proof. exact (fun_ext (fun z : A => @lem8113586 A B P lt2 s a f g' z)). Qed.
Lemma lem8113588 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8113589 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) : (term411 A B P lt2 s a f g') = (term425 A B P lt2 s a f g').
Proof. exact (MK_COMB (@lem8113588 A) (@lem8113587 A B P lt2 s a f g')). Qed.
Lemma lem8113596 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113597 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8113596 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8113598 {A B P : Type'} (p : type560 A B P) (g' : A -> B) : (p g') = (@I ((A -> B) -> P -> Prop) p g').
Proof. exact (@lem8113597 A B P p g'). Qed.
Lemma lem8113599 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8113600 {A B P : Type'} (p : type560 A B P) (g' : A -> B) (a : P) : (p g' a) = (@I ((A -> B) -> P -> Prop) p g' a).
Proof. exact (MK_COMB (@lem8113598 A B P p g') (@lem8113599 P a)). Qed.
Lemma lem8113602 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113603 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8113602 P Prop f x). Qed.
Lemma lem8113604 {A B P : Type'} (p : type560 A B P) (g' : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p g' a) = (term426 A B P p g' a).
Proof. exact (@lem8113603 P (@I ((A -> B) -> P -> Prop) p g') a). Qed.
Lemma lem8113606 {A B P : Type'} (p : type560 A B P) (g' : A -> B) (a : P) : (p g' a) = (term426 A B P p g' a).
Proof. exact (TRANS (@lem8113600 A B P p g' a) (@lem8113604 A B P p g' a)). Qed.
Lemma lem8113607 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8113608 {A B P : Type'} (p : type560 A B P) (g' : A -> B) (a : P) : (term110 A B P p g' a) = (term427 A B P p g' a).
Proof. exact (MK_COMB (@lem8113607) (@lem8113606 A B P p g' a)). Qed.
Lemma lem8113609 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) : (term412 A B P p lt2 s a f g') = (term428 A B P p lt2 s a f g').
Proof. exact (MK_COMB (@lem8113608 A B P p g' a) (@lem8113589 A B P lt2 s a f g')). Qed.
Lemma lem8113616 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113617 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8113616 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8113618 {A B P : Type'} (p : type560 A B P) (f : A -> B) : (p f) = (@I ((A -> B) -> P -> Prop) p f).
Proof. exact (@lem8113617 A B P p f). Qed.
Lemma lem8113619 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8113620 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (@I ((A -> B) -> P -> Prop) p f a).
Proof. exact (MK_COMB (@lem8113618 A B P p f) (@lem8113619 P a)). Qed.
Lemma lem8113622 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113623 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8113622 P Prop f x). Qed.
Lemma lem8113624 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p f a) = (term426 A B P p f a).
Proof. exact (@lem8113623 P (@I ((A -> B) -> P -> Prop) p f) a). Qed.
Lemma lem8113626 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (term426 A B P p f a).
Proof. exact (TRANS (@lem8113620 A B P p f a) (@lem8113624 A B P p f a)). Qed.
Lemma lem8113627 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8113628 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term110 A B P p f a) = (term427 A B P p f a).
Proof. exact (MK_COMB (@lem8113627) (@lem8113626 A B P p f a)). Qed.
Lemma lem8113629 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) : (term413 A B P p lt2 s a f g') = (term429 A B P p lt2 s a f g').
Proof. exact (MK_COMB (@lem8113628 A B P p f a) (@lem8113609 A B P p lt2 s a f g')). Qed.
Lemma lem8113630 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term429 A B P p lt2 s a f g'.
Proof. exact (EQ_MP (@lem8113629 A B P p lt2 s a f g') (@lem8113530 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8113631 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8113632 {D : Type'} : (@eq D) = (@eq D).
Proof. exact (eq_refl (@eq D)). Qed.
Lemma lem8113642 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113643 {A B C P : Type'} (f : type564 A B C P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> C) f x).
Proof. exact (@lem8113642 (A -> B) (P -> C) f x). Qed.
Lemma lem8113644 {A B C P : Type'} (y : type564 A B C P) (f : A -> B) : (y f) = (@I ((A -> B) -> P -> C) y f).
Proof. exact (@lem8113643 A B C P y f). Qed.
Lemma lem8113645 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8113646 {A B C P : Type'} (y : type564 A B C P) (f : A -> B) (a : P) : (y f a) = (@I ((A -> B) -> P -> C) y f a).
Proof. exact (MK_COMB (@lem8113644 A B C P y f) (@lem8113645 P a)). Qed.
Lemma lem8113648 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113649 {C P : Type'} (f : P -> C) (x : P) : (f x) = (@I (P -> C) f x).
Proof. exact (@lem8113648 P C f x). Qed.
Lemma lem8113650 {A B C P : Type'} (y : type564 A B C P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> C) y f a) = (term430 A B C P y f a).
Proof. exact (@lem8113649 C P (@I ((A -> B) -> P -> C) y f) a). Qed.
Lemma lem8113652 {A B C P : Type'} (y : type564 A B C P) (f : A -> B) (a : P) : (y f a) = (term430 A B C P y f a).
Proof. exact (TRANS (@lem8113646 A B C P y f a) (@lem8113650 A B C P y f a)). Qed.
Lemma lem8113654 {A B C D P : Type'} (g : type565 A B C D P) (f : A -> B) (a : P) : (g f a) = (g f a).
Proof. exact (eq_refl (g f a)). Qed.
Lemma lem8113655 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (f : A -> B) (a : P) : (term54 A B C D P g y f a) = (term431 A B C D P g y f a).
Proof. exact (MK_COMB (@lem8113654 A B C D P g f a) (@lem8113652 A B C P y f a)). Qed.
Lemma lem8113657 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113658 {A B C D P : Type'} (f : type565 A B C D P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> C -> D) f x).
Proof. exact (@lem8113657 (A -> B) (type1514 C D P) f x). Qed.
Lemma lem8113659 {A B C D P : Type'} (g : type565 A B C D P) (f : A -> B) : (g f) = (@I ((A -> B) -> P -> C -> D) g f).
Proof. exact (@lem8113658 A B C D P g f). Qed.
Lemma lem8113660 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8113661 {A B C D P : Type'} (g : type565 A B C D P) (f : A -> B) (a : P) : (g f a) = (@I ((A -> B) -> P -> C -> D) g f a).
Proof. exact (MK_COMB (@lem8113659 A B C D P g f) (@lem8113660 P a)). Qed.
Lemma lem8113663 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113664 {C D P : Type'} (f : type1514 C D P) (x : P) : (f x) = (@I (P -> C -> D) f x).
Proof. exact (@lem8113663 P (C -> D) f x). Qed.
Lemma lem8113665 {A B C D P : Type'} (g : type565 A B C D P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> C -> D) g f a) = (term432 A B C D P g f a).
Proof. exact (@lem8113664 C D P (@I ((A -> B) -> P -> C -> D) g f) a). Qed.
Lemma lem8113666 {A B C D P : Type'} (g : type565 A B C D P) (f : A -> B) (a : P) : (g f a) = (term432 A B C D P g f a).
Proof. exact (TRANS (@lem8113661 A B C D P g f a) (@lem8113665 A B C D P g f a)). Qed.
Lemma lem8113667 {A B C P : Type'} (y : type564 A B C P) (f : A -> B) (a : P) : (term430 A B C P y f a) = (term430 A B C P y f a).
Proof. exact (eq_refl (term430 A B C P y f a)). Qed.
Lemma lem8113668 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (f : A -> B) (a : P) : (term431 A B C D P g y f a) = (term433 A B C D P g y f a).
Proof. exact (MK_COMB (@lem8113666 A B C D P g f a) (@lem8113667 A B C P y f a)). Qed.
Lemma lem8113670 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113671 {C D : Type'} (f : C -> D) (x : C) : (f x) = (@I (C -> D) f x).
Proof. exact (@lem8113670 C D f x). Qed.
Lemma lem8113672 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (f : A -> B) (a : P) : (term433 A B C D P g y f a) = (term434 A B C D P g y f a).
Proof. exact (@lem8113671 C D (term432 A B C D P g f a) (term430 A B C P y f a)). Qed.
Lemma lem8113673 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (f : A -> B) (a : P) : (term431 A B C D P g y f a) = (term434 A B C D P g y f a).
Proof. exact (TRANS (@lem8113668 A B C D P g y f a) (@lem8113672 A B C D P g y f a)). Qed.
Lemma lem8113674 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (f : A -> B) (a : P) : (term54 A B C D P g y f a) = (term434 A B C D P g y f a).
Proof. exact (TRANS (@lem8113655 A B C D P g y f a) (@lem8113673 A B C D P g y f a)). Qed.
Lemma lem8113684 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113685 {A B C P : Type'} (f : type564 A B C P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> C) f x).
Proof. exact (@lem8113684 (A -> B) (P -> C) f x). Qed.
Lemma lem8113686 {A B C P : Type'} (y : type564 A B C P) (g' : A -> B) : (y g') = (@I ((A -> B) -> P -> C) y g').
Proof. exact (@lem8113685 A B C P y g'). Qed.
Lemma lem8113687 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8113688 {A B C P : Type'} (y : type564 A B C P) (g' : A -> B) (a : P) : (y g' a) = (@I ((A -> B) -> P -> C) y g' a).
Proof. exact (MK_COMB (@lem8113686 A B C P y g') (@lem8113687 P a)). Qed.
Lemma lem8113690 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113691 {C P : Type'} (f : P -> C) (x : P) : (f x) = (@I (P -> C) f x).
Proof. exact (@lem8113690 P C f x). Qed.
Lemma lem8113692 {A B C P : Type'} (y : type564 A B C P) (g' : A -> B) (a : P) : (@I ((A -> B) -> P -> C) y g' a) = (term430 A B C P y g' a).
Proof. exact (@lem8113691 C P (@I ((A -> B) -> P -> C) y g') a). Qed.
Lemma lem8113694 {A B C P : Type'} (y : type564 A B C P) (g' : A -> B) (a : P) : (y g' a) = (term430 A B C P y g' a).
Proof. exact (TRANS (@lem8113688 A B C P y g' a) (@lem8113692 A B C P y g' a)). Qed.
Lemma lem8113696 {A B C D P : Type'} (g : type565 A B C D P) (g' : A -> B) (a : P) : (g g' a) = (g g' a).
Proof. exact (eq_refl (g g' a)). Qed.
Lemma lem8113697 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term54 A B C D P g y g' a) = (term431 A B C D P g y g' a).
Proof. exact (MK_COMB (@lem8113696 A B C D P g g' a) (@lem8113694 A B C P y g' a)). Qed.
Lemma lem8113699 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113700 {A B C D P : Type'} (f : type565 A B C D P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> C -> D) f x).
Proof. exact (@lem8113699 (A -> B) (type1514 C D P) f x). Qed.
Lemma lem8113701 {A B C D P : Type'} (g : type565 A B C D P) (g' : A -> B) : (g g') = (@I ((A -> B) -> P -> C -> D) g g').
Proof. exact (@lem8113700 A B C D P g g'). Qed.
Lemma lem8113702 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8113703 {A B C D P : Type'} (g : type565 A B C D P) (g' : A -> B) (a : P) : (g g' a) = (@I ((A -> B) -> P -> C -> D) g g' a).
Proof. exact (MK_COMB (@lem8113701 A B C D P g g') (@lem8113702 P a)). Qed.
Lemma lem8113705 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113706 {C D P : Type'} (f : type1514 C D P) (x : P) : (f x) = (@I (P -> C -> D) f x).
Proof. exact (@lem8113705 P (C -> D) f x). Qed.
Lemma lem8113707 {A B C D P : Type'} (g : type565 A B C D P) (g' : A -> B) (a : P) : (@I ((A -> B) -> P -> C -> D) g g' a) = (term432 A B C D P g g' a).
Proof. exact (@lem8113706 C D P (@I ((A -> B) -> P -> C -> D) g g') a). Qed.
Lemma lem8113708 {A B C D P : Type'} (g : type565 A B C D P) (g' : A -> B) (a : P) : (g g' a) = (term432 A B C D P g g' a).
Proof. exact (TRANS (@lem8113703 A B C D P g g' a) (@lem8113707 A B C D P g g' a)). Qed.
Lemma lem8113709 {A B C P : Type'} (y : type564 A B C P) (g' : A -> B) (a : P) : (term430 A B C P y g' a) = (term430 A B C P y g' a).
Proof. exact (eq_refl (term430 A B C P y g' a)). Qed.
Lemma lem8113710 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term431 A B C D P g y g' a) = (term433 A B C D P g y g' a).
Proof. exact (MK_COMB (@lem8113708 A B C D P g g' a) (@lem8113709 A B C P y g' a)). Qed.
Lemma lem8113712 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113713 {C D : Type'} (f : C -> D) (x : C) : (f x) = (@I (C -> D) f x).
Proof. exact (@lem8113712 C D f x). Qed.
Lemma lem8113714 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term433 A B C D P g y g' a) = (term434 A B C D P g y g' a).
Proof. exact (@lem8113713 C D (term432 A B C D P g g' a) (term430 A B C P y g' a)). Qed.
Lemma lem8113715 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term431 A B C D P g y g' a) = (term434 A B C D P g y g' a).
Proof. exact (TRANS (@lem8113710 A B C D P g y g' a) (@lem8113714 A B C D P g y g' a)). Qed.
Lemma lem8113716 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term54 A B C D P g y g' a) = (term434 A B C D P g y g' a).
Proof. exact (TRANS (@lem8113697 A B C D P g y g' a) (@lem8113715 A B C D P g y g' a)). Qed.
Lemma lem8113717 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (f : A -> B) (a : P) : (term59 A B C D P g y f a) = (term435 A B C D P g y f a).
Proof. exact (MK_COMB (@lem8113632 D) (@lem8113674 A B C D P g y f a)). Qed.
Lemma lem8113718 {A B C D P : Type'} (f : A -> B) (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : ((term54 A B C D P g y f a) = (term54 A B C D P g y g' a)) = ((term434 A B C D P g y f a) = (term434 A B C D P g y g' a)).
Proof. exact (MK_COMB (@lem8113717 A B C D P g y f a) (@lem8113716 A B C D P g y g' a)). Qed.
Lemma lem8113719 {A B C D P : Type'} (f : A -> B) (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term127 A B C D P f g y g' a) = (term436 A B C D P f g y g' a).
Proof. exact (MK_COMB (@lem8113631) (@lem8113718 A B C D P f g y g' a)). Qed.
Lemma lem8113721 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem8113728 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113729 {A B C P : Type'} (f : type564 A B C P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> C) f x).
Proof. exact (@lem8113728 (A -> B) (P -> C) f x). Qed.
Lemma lem8113730 {A B C P : Type'} (y : type564 A B C P) (f : A -> B) : (y f) = (@I ((A -> B) -> P -> C) y f).
Proof. exact (@lem8113729 A B C P y f). Qed.
Lemma lem8113731 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8113732 {A B C P : Type'} (y : type564 A B C P) (f : A -> B) (a : P) : (y f a) = (@I ((A -> B) -> P -> C) y f a).
Proof. exact (MK_COMB (@lem8113730 A B C P y f) (@lem8113731 P a)). Qed.
Lemma lem8113734 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113735 {C P : Type'} (f : P -> C) (x : P) : (f x) = (@I (P -> C) f x).
Proof. exact (@lem8113734 P C f x). Qed.
Lemma lem8113736 {A B C P : Type'} (y : type564 A B C P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> C) y f a) = (term430 A B C P y f a).
Proof. exact (@lem8113735 C P (@I ((A -> B) -> P -> C) y f) a). Qed.
Lemma lem8113738 {A B C P : Type'} (y : type564 A B C P) (f : A -> B) (a : P) : (y f a) = (term430 A B C P y f a).
Proof. exact (TRANS (@lem8113732 A B C P y f a) (@lem8113736 A B C P y f a)). Qed.
Lemma lem8113745 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113746 {A B C P : Type'} (f : type564 A B C P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> C) f x).
Proof. exact (@lem8113745 (A -> B) (P -> C) f x). Qed.
Lemma lem8113747 {A B C P : Type'} (y : type564 A B C P) (g : A -> B) : (y g) = (@I ((A -> B) -> P -> C) y g).
Proof. exact (@lem8113746 A B C P y g). Qed.
Lemma lem8113748 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8113749 {A B C P : Type'} (y : type564 A B C P) (g : A -> B) (a : P) : (y g a) = (@I ((A -> B) -> P -> C) y g a).
Proof. exact (MK_COMB (@lem8113747 A B C P y g) (@lem8113748 P a)). Qed.
Lemma lem8113751 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113752 {C P : Type'} (f : P -> C) (x : P) : (f x) = (@I (P -> C) f x).
Proof. exact (@lem8113751 P C f x). Qed.
Lemma lem8113753 {A B C P : Type'} (y : type564 A B C P) (g : A -> B) (a : P) : (@I ((A -> B) -> P -> C) y g a) = (term430 A B C P y g a).
Proof. exact (@lem8113752 C P (@I ((A -> B) -> P -> C) y g) a). Qed.
Lemma lem8113755 {A B C P : Type'} (y : type564 A B C P) (g : A -> B) (a : P) : (y g a) = (term430 A B C P y g a).
Proof. exact (TRANS (@lem8113749 A B C P y g a) (@lem8113753 A B C P y g a)). Qed.
Lemma lem8113756 {A B C P : Type'} (y : type564 A B C P) (f : A -> B) (a : P) : (term437 A B C P y f a) = (term438 A B C P y f a).
Proof. exact (MK_COMB (@lem8113721 C) (@lem8113738 A B C P y f a)). Qed.
Lemma lem8113757 {A B C P : Type'} (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : ((y f a) = (y g a)) = ((term430 A B C P y f a) = (term430 A B C P y g a)).
Proof. exact (MK_COMB (@lem8113756 A B C P y f a) (@lem8113755 A B C P y g a)). Qed.
Lemma lem8113758 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8113759 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8113760 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8113769 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113770 {A B P : Type'} (f : type518 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> P -> A) f x).
Proof. exact (@lem8113769 (A -> B) (type557 A B P) f x). Qed.
Lemma lem8113771 {A B P : Type'} (z' : type518 A B P) (f : A -> B) : (z' f) = (@I ((A -> B) -> (A -> B) -> P -> A) z' f).
Proof. exact (@lem8113770 A B P z' f). Qed.
Lemma lem8113772 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8113773 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (z' f g) = (@I ((A -> B) -> (A -> B) -> P -> A) z' f g).
Proof. exact (MK_COMB (@lem8113771 A B P z' f) (@lem8113772 A B g)). Qed.
Lemma lem8113775 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113776 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8113775 (A -> B) (P -> A) f x). Qed.
Lemma lem8113777 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> P -> A) z' f g) = (term439 A B P z' f g).
Proof. exact (@lem8113776 A B P (@I ((A -> B) -> (A -> B) -> P -> A) z' f) g). Qed.
Lemma lem8113778 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (z' f g) = (term439 A B P z' f g).
Proof. exact (TRANS (@lem8113773 A B P z' f g) (@lem8113777 A B P z' f g)). Qed.
Lemma lem8113779 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8113780 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z' f g a) = (term440 A B P z' f g a).
Proof. exact (MK_COMB (@lem8113778 A B P z' f g) (@lem8113779 P a)). Qed.
Lemma lem8113782 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113783 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8113782 P A f x). Qed.
Lemma lem8113784 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term440 A B P z' f g a) = (term441 A B P z' f g a).
Proof. exact (@lem8113783 A P (term439 A B P z' f g) a). Qed.
Lemma lem8113786 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z' f g a) = (term441 A B P z' f g a).
Proof. exact (TRANS (@lem8113780 A B P z' f g a) (@lem8113784 A B P z' f g a)). Qed.
Lemma lem8113787 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term442 A B P z' f g a) = (term443 A B P z' f g a).
Proof. exact (MK_COMB (@lem8113760 A B f) (@lem8113786 A B P z' f g a)). Qed.
Lemma lem8113789 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113790 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8113789 A B f x). Qed.
Lemma lem8113791 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term443 A B P z' f g a) = (term444 A B P z' f g a).
Proof. exact (@lem8113790 A B f (term441 A B P z' f g a)). Qed.
Lemma lem8113792 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term442 A B P z' f g a) = (term444 A B P z' f g a).
Proof. exact (TRANS (@lem8113787 A B P z' f g a) (@lem8113791 A B P z' f g a)). Qed.
Lemma lem8113793 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8113802 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113803 {A B P : Type'} (f : type518 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> P -> A) f x).
Proof. exact (@lem8113802 (A -> B) (type557 A B P) f x). Qed.
Lemma lem8113804 {A B P : Type'} (z' : type518 A B P) (f : A -> B) : (z' f) = (@I ((A -> B) -> (A -> B) -> P -> A) z' f).
Proof. exact (@lem8113803 A B P z' f). Qed.
Lemma lem8113805 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8113806 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (z' f g) = (@I ((A -> B) -> (A -> B) -> P -> A) z' f g).
Proof. exact (MK_COMB (@lem8113804 A B P z' f) (@lem8113805 A B g)). Qed.
Lemma lem8113808 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113809 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8113808 (A -> B) (P -> A) f x). Qed.
Lemma lem8113810 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> P -> A) z' f g) = (term439 A B P z' f g).
Proof. exact (@lem8113809 A B P (@I ((A -> B) -> (A -> B) -> P -> A) z' f) g). Qed.
Lemma lem8113811 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (z' f g) = (term439 A B P z' f g).
Proof. exact (TRANS (@lem8113806 A B P z' f g) (@lem8113810 A B P z' f g)). Qed.
Lemma lem8113812 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8113813 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z' f g a) = (term440 A B P z' f g a).
Proof. exact (MK_COMB (@lem8113811 A B P z' f g) (@lem8113812 P a)). Qed.
Lemma lem8113815 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113816 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8113815 P A f x). Qed.
Lemma lem8113817 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term440 A B P z' f g a) = (term441 A B P z' f g a).
Proof. exact (@lem8113816 A P (term439 A B P z' f g) a). Qed.
Lemma lem8113819 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z' f g a) = (term441 A B P z' f g a).
Proof. exact (TRANS (@lem8113813 A B P z' f g a) (@lem8113817 A B P z' f g a)). Qed.
Lemma lem8113820 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term445 A B P z' f g a) = (term446 A B P z' f g a).
Proof. exact (MK_COMB (@lem8113793 A B g) (@lem8113819 A B P z' f g a)). Qed.
Lemma lem8113822 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113823 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8113822 A B f x). Qed.
Lemma lem8113824 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term446 A B P z' f g a) = (term447 A B P z' f g a).
Proof. exact (@lem8113823 A B g (term441 A B P z' f g a)). Qed.
Lemma lem8113825 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term445 A B P z' f g a) = (term447 A B P z' f g a).
Proof. exact (TRANS (@lem8113820 A B P z' f g a) (@lem8113824 A B P z' f g a)). Qed.
Lemma lem8113826 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term448 A B P z' f g a) = (term449 A B P z' f g a).
Proof. exact (MK_COMB (@lem8113759 B) (@lem8113792 A B P z' f g a)). Qed.
Lemma lem8113827 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : ((term442 A B P z' f g a) = (term445 A B P z' f g a)) = ((term444 A B P z' f g a) = (term447 A B P z' f g a)).
Proof. exact (MK_COMB (@lem8113826 A B P z' f g a) (@lem8113825 A B P z' f g a)). Qed.
Lemma lem8113828 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term450 A B P z' f g a) = (term451 A B P z' f g a).
Proof. exact (MK_COMB (@lem8113758) (@lem8113827 A B P z' f g a)). Qed.
Lemma lem8113829 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem8113838 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113839 {A B P : Type'} (f : type518 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> P -> A) f x).
Proof. exact (@lem8113838 (A -> B) (type557 A B P) f x). Qed.
Lemma lem8113840 {A B P : Type'} (z' : type518 A B P) (f : A -> B) : (z' f) = (@I ((A -> B) -> (A -> B) -> P -> A) z' f).
Proof. exact (@lem8113839 A B P z' f). Qed.
Lemma lem8113841 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8113842 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (z' f g) = (@I ((A -> B) -> (A -> B) -> P -> A) z' f g).
Proof. exact (MK_COMB (@lem8113840 A B P z' f) (@lem8113841 A B g)). Qed.
Lemma lem8113844 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113845 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8113844 (A -> B) (P -> A) f x). Qed.
Lemma lem8113846 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> P -> A) z' f g) = (term439 A B P z' f g).
Proof. exact (@lem8113845 A B P (@I ((A -> B) -> (A -> B) -> P -> A) z' f) g). Qed.
Lemma lem8113847 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (z' f g) = (term439 A B P z' f g).
Proof. exact (TRANS (@lem8113842 A B P z' f g) (@lem8113846 A B P z' f g)). Qed.
Lemma lem8113848 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8113849 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z' f g a) = (term440 A B P z' f g a).
Proof. exact (MK_COMB (@lem8113847 A B P z' f g) (@lem8113848 P a)). Qed.
Lemma lem8113851 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113852 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8113851 P A f x). Qed.
Lemma lem8113853 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term440 A B P z' f g a) = (term441 A B P z' f g a).
Proof. exact (@lem8113852 A P (term439 A B P z' f g) a). Qed.
Lemma lem8113855 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z' f g a) = (term441 A B P z' f g a).
Proof. exact (TRANS (@lem8113849 A B P z' f g a) (@lem8113853 A B P z' f g a)). Qed.
Lemma lem8113860 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113861 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8113860 P A f x). Qed.
Lemma lem8113863 {A P : Type'} (s : P -> A) (a : P) : (s a) = (@I (P -> A) s a).
Proof. exact (@lem8113861 A P s a). Qed.
Lemma lem8113864 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term452 A B P lt2 z' f g a) = (term453 A B P lt2 z' f g a).
Proof. exact (MK_COMB (@lem8113829 A lt2) (@lem8113855 A B P z' f g a)). Qed.
Lemma lem8113865 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term454 A B P lt2 z' f g s a) = (term455 A B P lt2 z' f g s a).
Proof. exact (MK_COMB (@lem8113864 A B P lt2 z' f g a) (@lem8113863 A P s a)). Qed.
Lemma lem8113867 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113868 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem8113867 A (A -> Prop) f x). Qed.
Lemma lem8113869 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term453 A B P lt2 z' f g a) = (term456 A B P lt2 z' f g a).
Proof. exact (@lem8113868 A lt2 (term441 A B P z' f g a)). Qed.
Lemma lem8113870 {A P : Type'} (s : P -> A) (a : P) : (@I (P -> A) s a) = (@I (P -> A) s a).
Proof. exact (eq_refl (@I (P -> A) s a)). Qed.
Lemma lem8113871 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term455 A B P lt2 z' f g s a) = (term457 A B P lt2 z' f g s a).
Proof. exact (MK_COMB (@lem8113869 A B P lt2 z' f g a) (@lem8113870 A P s a)). Qed.
Lemma lem8113873 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113874 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem8113873 A Prop f x). Qed.
Lemma lem8113875 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term457 A B P lt2 z' f g s a) = (term458 A B P lt2 z' f g s a).
Proof. exact (@lem8113874 A (term456 A B P lt2 z' f g a) (@I (P -> A) s a)). Qed.
Lemma lem8113876 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term455 A B P lt2 z' f g s a) = (term458 A B P lt2 z' f g s a).
Proof. exact (TRANS (@lem8113871 A B P lt2 z' f g s a) (@lem8113875 A B P lt2 z' f g s a)). Qed.
Lemma lem8113877 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term454 A B P lt2 z' f g s a) = (term458 A B P lt2 z' f g s a).
Proof. exact (TRANS (@lem8113865 A B P lt2 z' f g s a) (@lem8113876 A B P lt2 z' f g s a)). Qed.
Lemma lem8113878 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8113879 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term459 A B P lt2 z' f g s a) = (term460 A B P lt2 z' f g s a).
Proof. exact (MK_COMB (@lem8113878) (@lem8113877 A B P lt2 z' f g s a)). Qed.
Lemma lem8113880 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term461 A B P lt2 s z' f g a) = (term462 A B P lt2 s z' f g a).
Proof. exact (MK_COMB (@lem8113879 A B P lt2 z' f g s a) (@lem8113828 A B P z' f g a)). Qed.
Lemma lem8113881 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8113888 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113889 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8113888 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8113890 {A B P : Type'} (p : type560 A B P) (g : A -> B) : (p g) = (@I ((A -> B) -> P -> Prop) p g).
Proof. exact (@lem8113889 A B P p g). Qed.
Lemma lem8113891 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8113892 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (@I ((A -> B) -> P -> Prop) p g a).
Proof. exact (MK_COMB (@lem8113890 A B P p g) (@lem8113891 P a)). Qed.
Lemma lem8113894 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113895 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8113894 P Prop f x). Qed.
Lemma lem8113896 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p g a) = (term426 A B P p g a).
Proof. exact (@lem8113895 P (@I ((A -> B) -> P -> Prop) p g) a). Qed.
Lemma lem8113898 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (term426 A B P p g a).
Proof. exact (TRANS (@lem8113892 A B P p g a) (@lem8113896 A B P p g a)). Qed.
Lemma lem8113899 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term171 A B P p g a) = (term463 A B P p g a).
Proof. exact (MK_COMB (@lem8113881) (@lem8113898 A B P p g a)). Qed.
Lemma lem8113900 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8113901 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term140 A B P p g a) = (term464 A B P p g a).
Proof. exact (MK_COMB (@lem8113900) (@lem8113899 A B P p g a)). Qed.
Lemma lem8113902 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term465 A B P p lt2 s z' f g a) = (term466 A B P p lt2 s z' f g a).
Proof. exact (MK_COMB (@lem8113901 A B P p g a) (@lem8113880 A B P lt2 s z' f g a)). Qed.
Lemma lem8113903 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8113910 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113911 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8113910 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8113912 {A B P : Type'} (p : type560 A B P) (f : A -> B) : (p f) = (@I ((A -> B) -> P -> Prop) p f).
Proof. exact (@lem8113911 A B P p f). Qed.
Lemma lem8113913 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8113914 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (@I ((A -> B) -> P -> Prop) p f a).
Proof. exact (MK_COMB (@lem8113912 A B P p f) (@lem8113913 P a)). Qed.
Lemma lem8113916 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113917 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8113916 P Prop f x). Qed.
Lemma lem8113918 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p f a) = (term426 A B P p f a).
Proof. exact (@lem8113917 P (@I ((A -> B) -> P -> Prop) p f) a). Qed.
Lemma lem8113920 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (term426 A B P p f a).
Proof. exact (TRANS (@lem8113914 A B P p f a) (@lem8113918 A B P p f a)). Qed.
Lemma lem8113921 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term171 A B P p f a) = (term463 A B P p f a).
Proof. exact (MK_COMB (@lem8113903) (@lem8113920 A B P p f a)). Qed.
Lemma lem8113922 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8113923 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term140 A B P p f a) = (term464 A B P p f a).
Proof. exact (MK_COMB (@lem8113922) (@lem8113921 A B P p f a)). Qed.
Lemma lem8113924 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term467 A B P p lt2 s z' f g a) = (term468 A B P p lt2 s z' f g a).
Proof. exact (MK_COMB (@lem8113923 A B P p f a) (@lem8113902 A B P p lt2 s z' f g a)). Qed.
Lemma lem8113925 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8113926 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term469 A B P p lt2 s z' f g a) = (term470 A B P p lt2 s z' f g a).
Proof. exact (MK_COMB (@lem8113925) (@lem8113924 A B P p lt2 s z' f g a)). Qed.
Lemma lem8113927 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term471 A B C P p lt2 s z' f y g a) = (term472 A B C P p lt2 s z' f y g a).
Proof. exact (MK_COMB (@lem8113926 A B P p lt2 s z' f g a) (@lem8113757 A B C P f y g a)). Qed.
Lemma lem8113928 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term473 A B C P p lt2 s z' f y g) = (term474 A B C P p lt2 s z' f y g).
Proof. exact (fun_ext (fun a : P => @lem8113927 A B C P p lt2 s z' f y g a)). Qed.
Lemma lem8113929 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8113930 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term475 A B C P p lt2 s z' f y g) = (term476 A B C P p lt2 s z' f y g).
Proof. exact (MK_COMB (@lem8113929 P) (@lem8113928 A B C P p lt2 s z' f y g)). Qed.
Lemma lem8113931 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (f : A -> B) (y : type564 A B C P) : (term477 A B C P p lt2 s z' f y) = (term478 A B C P p lt2 s z' f y).
Proof. exact (fun_ext (fun g : A -> B => @lem8113930 A B C P p lt2 s z' f y g)). Qed.
Lemma lem8113932 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8113933 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (f : A -> B) (y : type564 A B C P) : (term363 A B C P p lt2 s z' f y) = (term479 A B C P p lt2 s z' f y).
Proof. exact (MK_COMB (@lem8113932 A B) (@lem8113931 A B C P p lt2 s z' f y)). Qed.
Lemma lem8113934 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) : (term365 A B C P p lt2 s z' y) = (term480 A B C P p lt2 s z' y).
Proof. exact (fun_ext (fun f : A -> B => @lem8113933 A B C P p lt2 s z' f y)). Qed.
Lemma lem8113935 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8113936 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) : (term367 A B C P p lt2 s z' y) = (term481 A B C P p lt2 s z' y).
Proof. exact (MK_COMB (@lem8113935 A B) (@lem8113934 A B C P p lt2 s z' y)). Qed.
Lemma lem8113937 {C D : Type'} : (@eq (C -> D)) = (@eq (C -> D)).
Proof. exact (eq_refl (@eq (C -> D))). Qed.
Lemma lem8113944 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113945 {A B C D P : Type'} (f : type565 A B C D P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> C -> D) f x).
Proof. exact (@lem8113944 (A -> B) (type1514 C D P) f x). Qed.
Lemma lem8113946 {A B C D P : Type'} (g : type565 A B C D P) (f : A -> B) : (g f) = (@I ((A -> B) -> P -> C -> D) g f).
Proof. exact (@lem8113945 A B C D P g f). Qed.
Lemma lem8113947 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8113948 {A B C D P : Type'} (g : type565 A B C D P) (f : A -> B) (a : P) : (g f a) = (@I ((A -> B) -> P -> C -> D) g f a).
Proof. exact (MK_COMB (@lem8113946 A B C D P g f) (@lem8113947 P a)). Qed.
Lemma lem8113950 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113951 {C D P : Type'} (f : type1514 C D P) (x : P) : (f x) = (@I (P -> C -> D) f x).
Proof. exact (@lem8113950 P (C -> D) f x). Qed.
Lemma lem8113952 {A B C D P : Type'} (g : type565 A B C D P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> C -> D) g f a) = (term432 A B C D P g f a).
Proof. exact (@lem8113951 C D P (@I ((A -> B) -> P -> C -> D) g f) a). Qed.
Lemma lem8113954 {A B C D P : Type'} (g : type565 A B C D P) (f : A -> B) (a : P) : (g f a) = (term432 A B C D P g f a).
Proof. exact (TRANS (@lem8113948 A B C D P g f a) (@lem8113952 A B C D P g f a)). Qed.
Lemma lem8113961 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113962 {A B C D P : Type'} (f : type565 A B C D P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> C -> D) f x).
Proof. exact (@lem8113961 (A -> B) (type1514 C D P) f x). Qed.
Lemma lem8113963 {A B C D P : Type'} (g : type565 A B C D P) (g' : A -> B) : (g g') = (@I ((A -> B) -> P -> C -> D) g g').
Proof. exact (@lem8113962 A B C D P g g'). Qed.
Lemma lem8113964 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8113965 {A B C D P : Type'} (g : type565 A B C D P) (g' : A -> B) (a : P) : (g g' a) = (@I ((A -> B) -> P -> C -> D) g g' a).
Proof. exact (MK_COMB (@lem8113963 A B C D P g g') (@lem8113964 P a)). Qed.
Lemma lem8113967 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113968 {C D P : Type'} (f : type1514 C D P) (x : P) : (f x) = (@I (P -> C -> D) f x).
Proof. exact (@lem8113967 P (C -> D) f x). Qed.
Lemma lem8113969 {A B C D P : Type'} (g : type565 A B C D P) (g' : A -> B) (a : P) : (@I ((A -> B) -> P -> C -> D) g g' a) = (term432 A B C D P g g' a).
Proof. exact (@lem8113968 C D P (@I ((A -> B) -> P -> C -> D) g g') a). Qed.
Lemma lem8113971 {A B C D P : Type'} (g : type565 A B C D P) (g' : A -> B) (a : P) : (g g' a) = (term432 A B C D P g g' a).
Proof. exact (TRANS (@lem8113965 A B C D P g g' a) (@lem8113969 A B C D P g g' a)). Qed.
Lemma lem8113972 {A B C D P : Type'} (g : type565 A B C D P) (f : A -> B) (a : P) : (term482 A B C D P g f a) = (term483 A B C D P g f a).
Proof. exact (MK_COMB (@lem8113937 C D) (@lem8113954 A B C D P g f a)). Qed.
Lemma lem8113973 {A B C D P : Type'} (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : ((g f a) = (g g' a)) = ((term432 A B C D P g f a) = (term432 A B C D P g g' a)).
Proof. exact (MK_COMB (@lem8113972 A B C D P g f a) (@lem8113971 A B C D P g g' a)). Qed.
Lemma lem8113974 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8113975 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8113976 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8113985 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113986 {A B P : Type'} (f : type518 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> P -> A) f x).
Proof. exact (@lem8113985 (A -> B) (type557 A B P) f x). Qed.
Lemma lem8113987 {A B P : Type'} (z : type518 A B P) (f : A -> B) : (z f) = (@I ((A -> B) -> (A -> B) -> P -> A) z f).
Proof. exact (@lem8113986 A B P z f). Qed.
Lemma lem8113988 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8113989 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (@I ((A -> B) -> (A -> B) -> P -> A) z f g).
Proof. exact (MK_COMB (@lem8113987 A B P z f) (@lem8113988 A B g)). Qed.
Lemma lem8113991 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113992 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8113991 (A -> B) (P -> A) f x). Qed.
Lemma lem8113993 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> P -> A) z f g) = (term439 A B P z f g).
Proof. exact (@lem8113992 A B P (@I ((A -> B) -> (A -> B) -> P -> A) z f) g). Qed.
Lemma lem8113994 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (term439 A B P z f g).
Proof. exact (TRANS (@lem8113989 A B P z f g) (@lem8113993 A B P z f g)). Qed.
Lemma lem8113995 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8113996 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term440 A B P z f g a).
Proof. exact (MK_COMB (@lem8113994 A B P z f g) (@lem8113995 P a)). Qed.
Lemma lem8113998 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8113999 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8113998 P A f x). Qed.
Lemma lem8114000 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term440 A B P z f g a) = (term441 A B P z f g a).
Proof. exact (@lem8113999 A P (term439 A B P z f g) a). Qed.
Lemma lem8114002 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term441 A B P z f g a).
Proof. exact (TRANS (@lem8113996 A B P z f g a) (@lem8114000 A B P z f g a)). Qed.
Lemma lem8114003 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term442 A B P z f g a) = (term443 A B P z f g a).
Proof. exact (MK_COMB (@lem8113976 A B f) (@lem8114002 A B P z f g a)). Qed.
Lemma lem8114005 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8114006 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8114005 A B f x). Qed.
Lemma lem8114007 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term443 A B P z f g a) = (term444 A B P z f g a).
Proof. exact (@lem8114006 A B f (term441 A B P z f g a)). Qed.
Lemma lem8114008 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term442 A B P z f g a) = (term444 A B P z f g a).
Proof. exact (TRANS (@lem8114003 A B P z f g a) (@lem8114007 A B P z f g a)). Qed.
Lemma lem8114009 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8114018 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8114019 {A B P : Type'} (f : type518 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> P -> A) f x).
Proof. exact (@lem8114018 (A -> B) (type557 A B P) f x). Qed.
Lemma lem8114020 {A B P : Type'} (z : type518 A B P) (f : A -> B) : (z f) = (@I ((A -> B) -> (A -> B) -> P -> A) z f).
Proof. exact (@lem8114019 A B P z f). Qed.
Lemma lem8114021 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8114022 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (@I ((A -> B) -> (A -> B) -> P -> A) z f g).
Proof. exact (MK_COMB (@lem8114020 A B P z f) (@lem8114021 A B g)). Qed.
Lemma lem8114024 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8114025 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8114024 (A -> B) (P -> A) f x). Qed.
Lemma lem8114026 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> P -> A) z f g) = (term439 A B P z f g).
Proof. exact (@lem8114025 A B P (@I ((A -> B) -> (A -> B) -> P -> A) z f) g). Qed.
Lemma lem8114027 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (term439 A B P z f g).
Proof. exact (TRANS (@lem8114022 A B P z f g) (@lem8114026 A B P z f g)). Qed.
Lemma lem8114028 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8114029 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term440 A B P z f g a).
Proof. exact (MK_COMB (@lem8114027 A B P z f g) (@lem8114028 P a)). Qed.
Lemma lem8114031 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8114032 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8114031 P A f x). Qed.
Lemma lem8114033 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term440 A B P z f g a) = (term441 A B P z f g a).
Proof. exact (@lem8114032 A P (term439 A B P z f g) a). Qed.
Lemma lem8114035 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term441 A B P z f g a).
Proof. exact (TRANS (@lem8114029 A B P z f g a) (@lem8114033 A B P z f g a)). Qed.
Lemma lem8114036 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term445 A B P z f g a) = (term446 A B P z f g a).
Proof. exact (MK_COMB (@lem8114009 A B g) (@lem8114035 A B P z f g a)). Qed.
Lemma lem8114038 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8114039 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8114038 A B f x). Qed.
Lemma lem8114040 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term446 A B P z f g a) = (term447 A B P z f g a).
Proof. exact (@lem8114039 A B g (term441 A B P z f g a)). Qed.
Lemma lem8114041 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term445 A B P z f g a) = (term447 A B P z f g a).
Proof. exact (TRANS (@lem8114036 A B P z f g a) (@lem8114040 A B P z f g a)). Qed.
Lemma lem8114042 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term448 A B P z f g a) = (term449 A B P z f g a).
Proof. exact (MK_COMB (@lem8113975 B) (@lem8114008 A B P z f g a)). Qed.
Lemma lem8114043 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : ((term442 A B P z f g a) = (term445 A B P z f g a)) = ((term444 A B P z f g a) = (term447 A B P z f g a)).
Proof. exact (MK_COMB (@lem8114042 A B P z f g a) (@lem8114041 A B P z f g a)). Qed.
Lemma lem8114044 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term450 A B P z f g a) = (term451 A B P z f g a).
Proof. exact (MK_COMB (@lem8113974) (@lem8114043 A B P z f g a)). Qed.
Lemma lem8114045 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem8114054 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8114055 {A B P : Type'} (f : type518 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> P -> A) f x).
Proof. exact (@lem8114054 (A -> B) (type557 A B P) f x). Qed.
Lemma lem8114056 {A B P : Type'} (z : type518 A B P) (f : A -> B) : (z f) = (@I ((A -> B) -> (A -> B) -> P -> A) z f).
Proof. exact (@lem8114055 A B P z f). Qed.
Lemma lem8114057 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8114058 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (@I ((A -> B) -> (A -> B) -> P -> A) z f g).
Proof. exact (MK_COMB (@lem8114056 A B P z f) (@lem8114057 A B g)). Qed.
Lemma lem8114060 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8114061 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8114060 (A -> B) (P -> A) f x). Qed.
Lemma lem8114062 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> P -> A) z f g) = (term439 A B P z f g).
Proof. exact (@lem8114061 A B P (@I ((A -> B) -> (A -> B) -> P -> A) z f) g). Qed.
Lemma lem8114063 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (term439 A B P z f g).
Proof. exact (TRANS (@lem8114058 A B P z f g) (@lem8114062 A B P z f g)). Qed.
Lemma lem8114064 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8114065 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term440 A B P z f g a).
Proof. exact (MK_COMB (@lem8114063 A B P z f g) (@lem8114064 P a)). Qed.
Lemma lem8114067 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8114068 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8114067 P A f x). Qed.
Lemma lem8114069 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term440 A B P z f g a) = (term441 A B P z f g a).
Proof. exact (@lem8114068 A P (term439 A B P z f g) a). Qed.
Lemma lem8114071 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term441 A B P z f g a).
Proof. exact (TRANS (@lem8114065 A B P z f g a) (@lem8114069 A B P z f g a)). Qed.
Lemma lem8114076 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8114077 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8114076 P A f x). Qed.
Lemma lem8114079 {A P : Type'} (s : P -> A) (a : P) : (s a) = (@I (P -> A) s a).
Proof. exact (@lem8114077 A P s a). Qed.
Lemma lem8114080 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term452 A B P lt2 z f g a) = (term453 A B P lt2 z f g a).
Proof. exact (MK_COMB (@lem8114045 A lt2) (@lem8114071 A B P z f g a)). Qed.
Lemma lem8114081 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term454 A B P lt2 z f g s a) = (term455 A B P lt2 z f g s a).
Proof. exact (MK_COMB (@lem8114080 A B P lt2 z f g a) (@lem8114079 A P s a)). Qed.
Lemma lem8114083 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8114084 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem8114083 A (A -> Prop) f x). Qed.
Lemma lem8114085 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term453 A B P lt2 z f g a) = (term456 A B P lt2 z f g a).
Proof. exact (@lem8114084 A lt2 (term441 A B P z f g a)). Qed.
Lemma lem8114086 {A P : Type'} (s : P -> A) (a : P) : (@I (P -> A) s a) = (@I (P -> A) s a).
Proof. exact (eq_refl (@I (P -> A) s a)). Qed.
Lemma lem8114087 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term455 A B P lt2 z f g s a) = (term457 A B P lt2 z f g s a).
Proof. exact (MK_COMB (@lem8114085 A B P lt2 z f g a) (@lem8114086 A P s a)). Qed.
Lemma lem8114089 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8114090 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem8114089 A Prop f x). Qed.
Lemma lem8114091 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term457 A B P lt2 z f g s a) = (term458 A B P lt2 z f g s a).
Proof. exact (@lem8114090 A (term456 A B P lt2 z f g a) (@I (P -> A) s a)). Qed.
Lemma lem8114092 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term455 A B P lt2 z f g s a) = (term458 A B P lt2 z f g s a).
Proof. exact (TRANS (@lem8114087 A B P lt2 z f g s a) (@lem8114091 A B P lt2 z f g s a)). Qed.
Lemma lem8114093 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term454 A B P lt2 z f g s a) = (term458 A B P lt2 z f g s a).
Proof. exact (TRANS (@lem8114081 A B P lt2 z f g s a) (@lem8114092 A B P lt2 z f g s a)). Qed.
Lemma lem8114094 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8114095 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term459 A B P lt2 z f g s a) = (term460 A B P lt2 z f g s a).
Proof. exact (MK_COMB (@lem8114094) (@lem8114093 A B P lt2 z f g s a)). Qed.
Lemma lem8114096 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term461 A B P lt2 s z f g a) = (term462 A B P lt2 s z f g a).
Proof. exact (MK_COMB (@lem8114095 A B P lt2 z f g s a) (@lem8114044 A B P z f g a)). Qed.
Lemma lem8114097 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8114104 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8114105 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8114104 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8114106 {A B P : Type'} (p : type560 A B P) (g : A -> B) : (p g) = (@I ((A -> B) -> P -> Prop) p g).
Proof. exact (@lem8114105 A B P p g). Qed.
Lemma lem8114107 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8114108 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (@I ((A -> B) -> P -> Prop) p g a).
Proof. exact (MK_COMB (@lem8114106 A B P p g) (@lem8114107 P a)). Qed.
Lemma lem8114110 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8114111 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8114110 P Prop f x). Qed.
Lemma lem8114112 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p g a) = (term426 A B P p g a).
Proof. exact (@lem8114111 P (@I ((A -> B) -> P -> Prop) p g) a). Qed.
Lemma lem8114114 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (term426 A B P p g a).
Proof. exact (TRANS (@lem8114108 A B P p g a) (@lem8114112 A B P p g a)). Qed.
Lemma lem8114115 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term171 A B P p g a) = (term463 A B P p g a).
Proof. exact (MK_COMB (@lem8114097) (@lem8114114 A B P p g a)). Qed.
Lemma lem8114116 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8114117 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term140 A B P p g a) = (term464 A B P p g a).
Proof. exact (MK_COMB (@lem8114116) (@lem8114115 A B P p g a)). Qed.
Lemma lem8114118 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term465 A B P p lt2 s z f g a) = (term466 A B P p lt2 s z f g a).
Proof. exact (MK_COMB (@lem8114117 A B P p g a) (@lem8114096 A B P lt2 s z f g a)). Qed.
Lemma lem8114119 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8114126 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8114127 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8114126 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8114128 {A B P : Type'} (p : type560 A B P) (f : A -> B) : (p f) = (@I ((A -> B) -> P -> Prop) p f).
Proof. exact (@lem8114127 A B P p f). Qed.
Lemma lem8114129 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8114130 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (@I ((A -> B) -> P -> Prop) p f a).
Proof. exact (MK_COMB (@lem8114128 A B P p f) (@lem8114129 P a)). Qed.
Lemma lem8114132 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8114133 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8114132 P Prop f x). Qed.
Lemma lem8114134 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p f a) = (term426 A B P p f a).
Proof. exact (@lem8114133 P (@I ((A -> B) -> P -> Prop) p f) a). Qed.
Lemma lem8114136 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (term426 A B P p f a).
Proof. exact (TRANS (@lem8114130 A B P p f a) (@lem8114134 A B P p f a)). Qed.
Lemma lem8114137 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term171 A B P p f a) = (term463 A B P p f a).
Proof. exact (MK_COMB (@lem8114119) (@lem8114136 A B P p f a)). Qed.
Lemma lem8114138 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8114139 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term140 A B P p f a) = (term464 A B P p f a).
Proof. exact (MK_COMB (@lem8114138) (@lem8114137 A B P p f a)). Qed.
Lemma lem8114140 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term467 A B P p lt2 s z f g a) = (term468 A B P p lt2 s z f g a).
Proof. exact (MK_COMB (@lem8114139 A B P p f a) (@lem8114118 A B P p lt2 s z f g a)). Qed.
Lemma lem8114141 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8114142 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term469 A B P p lt2 s z f g a) = (term470 A B P p lt2 s z f g a).
Proof. exact (MK_COMB (@lem8114141) (@lem8114140 A B P p lt2 s z f g a)). Qed.
Lemma lem8114143 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : (term484 A B C D P p lt2 s z f g g' a) = (term485 A B C D P p lt2 s z f g g' a).
Proof. exact (MK_COMB (@lem8114142 A B P p lt2 s z f g' a) (@lem8113973 A B C D P f g g' a)). Qed.
Lemma lem8114144 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) : (term486 A B C D P p lt2 s z f g g') = (term487 A B C D P p lt2 s z f g g').
Proof. exact (fun_ext (fun a : P => @lem8114143 A B C D P p lt2 s z f g g' a)). Qed.
Lemma lem8114145 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8114146 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) : (term488 A B C D P p lt2 s z f g g') = (term489 A B C D P p lt2 s z f g g').
Proof. exact (MK_COMB (@lem8114145 P) (@lem8114144 A B C D P p lt2 s z f g g')). Qed.
Lemma lem8114147 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (g : type565 A B C D P) : (term490 A B C D P p lt2 s z f g) = (term491 A B C D P p lt2 s z f g).
Proof. exact (fun_ext (fun g' : A -> B => @lem8114146 A B C D P p lt2 s z f g g')). Qed.
Lemma lem8114148 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8114149 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (g : type565 A B C D P) : (term283 A B C D P p lt2 s z f g) = (term492 A B C D P p lt2 s z f g).
Proof. exact (MK_COMB (@lem8114148 A B) (@lem8114147 A B C D P p lt2 s z f g)). Qed.
Lemma lem8114150 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (g : type565 A B C D P) : (term285 A B C D P p lt2 s z g) = (term493 A B C D P p lt2 s z g).
Proof. exact (fun_ext (fun f : A -> B => @lem8114149 A B C D P p lt2 s z f g)). Qed.
Lemma lem8114151 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8114152 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (g : type565 A B C D P) : (term287 A B C D P p lt2 s z g) = (term494 A B C D P p lt2 s z g).
Proof. exact (MK_COMB (@lem8114151 A B) (@lem8114150 A B C D P p lt2 s z g)). Qed.
Lemma lem8114153 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8114154 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (g : type565 A B C D P) : (term385 A B C D P p lt2 s z g) = (term495 A B C D P p lt2 s z g).
Proof. exact (MK_COMB (@lem8114153) (@lem8114152 A B C D P p lt2 s z g)). Qed.
Lemma lem8114155 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) : (term403 A B C D P z g p lt2 s z' y) = (term496 A B C D P z g p lt2 s z' y).
Proof. exact (MK_COMB (@lem8114154 A B C D P p lt2 s z g) (@lem8113936 A B C P p lt2 s z' y)). Qed.
Lemma lem8114156 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term496 A B C D P z g p lt2 s z' y.
Proof. exact (EQ_MP (@lem8114155 A B C D P z g p lt2 s z' y) (@lem8113538 A B C D P z g p lt2 s z' y h1)). Qed.
Lemma lem8114157 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term481 A B C P p lt2 s z' y.
Proof. exact (proj2 (@lem8114156 A B C D P z g p lt2 s z' y h1)). Qed.
Lemma lem8114158 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term494 A B C D P p lt2 s z g.
Proof. exact (proj1 (@lem8114156 A B C D P z g p lt2 s z' y h1)). Qed.
Lemma lem8114159 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term428 A B P p lt2 s a f g'.
Proof. exact (proj2 (@lem8113630 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8114161 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term425 A B P lt2 s a f g'.
Proof. exact (proj2 (@lem8114159 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8114168 {A B C D P : Type'} (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : ((term432 A B C D P g f a) = (term432 A B C D P g g' a)) = ((term432 A B C D P g f a) = (term432 A B C D P g g' a)).
Proof. exact (eq_refl ((term432 A B C D P g f a) = (term432 A B C D P g g' a))). Qed.
Lemma lem8114185 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term466 A B P p lt2 s z f g a) = (term497 A B P lt2 s p z f g a).
Proof. exact (@lem19490 (term458 A B P lt2 z f g s a) (term463 A B P p g a) (term451 A B P z f g a)). Qed.
Lemma lem8114188 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term464 A B P p f a) = (term464 A B P p f a).
Proof. exact (eq_refl (term464 A B P p f a)). Qed.
Lemma lem8114189 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term468 A B P p lt2 s z f g a) = (term498 A B P lt2 s p z f g a).
Proof. exact (MK_COMB (@lem8114188 A B P p f a) (@lem8114185 A B P lt2 s p z f g a)). Qed.
Lemma lem8114196 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term498 A B P lt2 s p z f g a) = (term499 A B P lt2 s p z f g a).
Proof. exact (@lem19490 (term500 A B P p lt2 z f g s a) (term463 A B P p f a) (term501 A B P p z f g a)). Qed.
Lemma lem8114197 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term468 A B P p lt2 s z f g a) = (term499 A B P lt2 s p z f g a).
Proof. exact (TRANS (@lem8114189 A B P lt2 s p z f g a) (@lem8114196 A B P lt2 s p z f g a)). Qed.
Lemma lem8114198 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8114199 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term470 A B P p lt2 s z f g a) = (term502 A B P lt2 s p z f g a).
Proof. exact (MK_COMB (@lem8114198) (@lem8114197 A B P lt2 s p z f g a)). Qed.
Lemma lem8114200 {A B C D P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : (term485 A B C D P p lt2 s z f g g' a) = (term503 A B C D P lt2 s p z f g g' a).
Proof. exact (MK_COMB (@lem8114199 A B P lt2 s p z f g' a) (@lem8114168 A B C D P f g g' a)). Qed.
Lemma lem8114207 {A B C D P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : (term503 A B C D P lt2 s p z f g g' a) = (term504 A B C D P lt2 s p z f g g' a).
Proof. exact (@lem19699 (term505 A B P p lt2 z f g' s a) (term506 A B P p z f g' a) ((term432 A B C D P g f a) = (term432 A B C D P g g' a))). Qed.
Lemma lem8114208 {A B C D P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : (term485 A B C D P p lt2 s z f g g' a) = (term504 A B C D P lt2 s p z f g g' a).
Proof. exact (TRANS (@lem8114200 A B C D P lt2 s p z f g g' a) (@lem8114207 A B C D P lt2 s p z f g g' a)). Qed.
Lemma lem8114209 {A B C D P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) : (term487 A B C D P p lt2 s z f g g') = (term507 A B C D P lt2 s p z f g g').
Proof. exact (fun_ext (fun a : P => @lem8114208 A B C D P lt2 s p z f g g' a)). Qed.
Lemma lem8114210 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8114211 {A B C D P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (g : type565 A B C D P) (g' : A -> B) : (term489 A B C D P p lt2 s z f g g') = (term508 A B C D P lt2 s p z f g g').
Proof. exact (MK_COMB (@lem8114210 P) (@lem8114209 A B C D P lt2 s p z f g g')). Qed.
Lemma lem8114212 {A B C D P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (g : type565 A B C D P) : (term491 A B C D P p lt2 s z f g) = (term509 A B C D P lt2 s p z f g).
Proof. exact (fun_ext (fun g' : A -> B => @lem8114211 A B C D P lt2 s p z f g g')). Qed.
Lemma lem8114213 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8114214 {A B C D P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (g : type565 A B C D P) : (term492 A B C D P p lt2 s z f g) = (term510 A B C D P lt2 s p z f g).
Proof. exact (MK_COMB (@lem8114213 A B) (@lem8114212 A B C D P lt2 s p z f g)). Qed.
Lemma lem8114215 {A B C D P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (g : type565 A B C D P) : (term493 A B C D P p lt2 s z g) = (term511 A B C D P lt2 s p z g).
Proof. exact (fun_ext (fun f : A -> B => @lem8114214 A B C D P lt2 s p z f g)). Qed.
Lemma lem8114216 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8114218 {A B C D P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (g : type565 A B C D P) : (term494 A B C D P p lt2 s z g) = (term512 A B C D P lt2 s p z g).
Proof. exact (MK_COMB (@lem8114216 A B) (@lem8114215 A B C D P lt2 s p z g)). Qed.
Lemma lem8114219 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term512 A B C D P lt2 s p z g.
Proof. exact (EQ_MP (@lem8114218 A B C D P lt2 s p z g) (@lem8114158 A B C D P z g p lt2 s z' y h1)). Qed.
Lemma lem8114221 {A B C P : Type'} (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : ((term430 A B C P y f a) = (term430 A B C P y g a)) = ((term430 A B C P y f a) = (term430 A B C P y g a)).
Proof. exact (eq_refl ((term430 A B C P y f a) = (term430 A B C P y g a))). Qed.
Lemma lem8114238 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term466 A B P p lt2 s z' f g a) = (term497 A B P lt2 s p z' f g a).
Proof. exact (@lem19490 (term458 A B P lt2 z' f g s a) (term463 A B P p g a) (term451 A B P z' f g a)). Qed.
Lemma lem8114241 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term464 A B P p f a) = (term464 A B P p f a).
Proof. exact (eq_refl (term464 A B P p f a)). Qed.
Lemma lem8114242 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term468 A B P p lt2 s z' f g a) = (term498 A B P lt2 s p z' f g a).
Proof. exact (MK_COMB (@lem8114241 A B P p f a) (@lem8114238 A B P lt2 s p z' f g a)). Qed.
Lemma lem8114249 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term498 A B P lt2 s p z' f g a) = (term499 A B P lt2 s p z' f g a).
Proof. exact (@lem19490 (term500 A B P p lt2 z' f g s a) (term463 A B P p f a) (term501 A B P p z' f g a)). Qed.
Lemma lem8114250 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term468 A B P p lt2 s z' f g a) = (term499 A B P lt2 s p z' f g a).
Proof. exact (TRANS (@lem8114242 A B P lt2 s p z' f g a) (@lem8114249 A B P lt2 s p z' f g a)). Qed.
Lemma lem8114251 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8114252 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term470 A B P p lt2 s z' f g a) = (term502 A B P lt2 s p z' f g a).
Proof. exact (MK_COMB (@lem8114251) (@lem8114250 A B P lt2 s p z' f g a)). Qed.
Lemma lem8114253 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term472 A B C P p lt2 s z' f y g a) = (term513 A B C P lt2 s p z' f y g a).
Proof. exact (MK_COMB (@lem8114252 A B P lt2 s p z' f g a) (@lem8114221 A B C P f y g a)). Qed.
Lemma lem8114260 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term513 A B C P lt2 s p z' f y g a) = (term514 A B C P lt2 s p z' f y g a).
Proof. exact (@lem19699 (term505 A B P p lt2 z' f g s a) (term506 A B P p z' f g a) ((term430 A B C P y f a) = (term430 A B C P y g a))). Qed.
Lemma lem8114261 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term472 A B C P p lt2 s z' f y g a) = (term514 A B C P lt2 s p z' f y g a).
Proof. exact (TRANS (@lem8114253 A B C P lt2 s p z' f y g a) (@lem8114260 A B C P lt2 s p z' f y g a)). Qed.
Lemma lem8114262 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term474 A B C P p lt2 s z' f y g) = (term515 A B C P lt2 s p z' f y g).
Proof. exact (fun_ext (fun a : P => @lem8114261 A B C P lt2 s p z' f y g a)). Qed.
Lemma lem8114263 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8114264 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term476 A B C P p lt2 s z' f y g) = (term516 A B C P lt2 s p z' f y g).
Proof. exact (MK_COMB (@lem8114263 P) (@lem8114262 A B C P lt2 s p z' f y g)). Qed.
Lemma lem8114265 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (y : type564 A B C P) : (term478 A B C P p lt2 s z' f y) = (term517 A B C P lt2 s p z' f y).
Proof. exact (fun_ext (fun g : A -> B => @lem8114264 A B C P lt2 s p z' f y g)). Qed.
Lemma lem8114266 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8114267 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (y : type564 A B C P) : (term479 A B C P p lt2 s z' f y) = (term518 A B C P lt2 s p z' f y).
Proof. exact (MK_COMB (@lem8114266 A B) (@lem8114265 A B C P lt2 s p z' f y)). Qed.
Lemma lem8114268 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (y : type564 A B C P) : (term480 A B C P p lt2 s z' y) = (term519 A B C P lt2 s p z' y).
Proof. exact (fun_ext (fun f : A -> B => @lem8114267 A B C P lt2 s p z' f y)). Qed.
Lemma lem8114269 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8114271 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (y : type564 A B C P) : (term481 A B C P p lt2 s z' y) = (term520 A B C P lt2 s p z' y).
Proof. exact (MK_COMB (@lem8114269 A B) (@lem8114268 A B C P lt2 s p z' y)). Qed.
Lemma lem8114272 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term520 A B C P lt2 s p z' y.
Proof. exact (EQ_MP (@lem8114271 A B C P lt2 s p z' y) (@lem8114157 A B C D P z g p lt2 s z' y h1)). Qed.
Lemma lem8114288 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (z : A) : (term423 A B P lt2 s a f g' z) = (term423 A B P lt2 s a f g' z).
Proof. exact (eq_refl (term423 A B P lt2 s a f g' z)). Qed.
Lemma lem8114289 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) : (term424 A B P lt2 s a f g') = (term424 A B P lt2 s a f g').
Proof. exact (fun_ext (fun z : A => @lem8114288 A B P lt2 s a f g' z)). Qed.
Lemma lem8114290 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8114292 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) : (term425 A B P lt2 s a f g') = (term425 A B P lt2 s a f g').
Proof. exact (MK_COMB (@lem8114290 A) (@lem8114289 A B P lt2 s a f g')). Qed.
Lemma lem8114293 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term425 A B P lt2 s a f g'.
Proof. exact (EQ_MP (@lem8114292 A B P lt2 s a f g') (@lem8114161 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8114294 {A B C D P : Type'} (_107457 : A -> B) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term521 A B C D P lt2 s p z g _107457.
Proof. exact (@lem8114219 A B C D P z g p lt2 s z' y h1 _107457). Qed.
Lemma lem8114295 {A B C D P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (_107457 : A -> B) (g : type565 A B C D P) : (term521 A B C D P lt2 s p z g _107457) = (term510 A B C D P lt2 s p z _107457 g).
Proof. exact (eq_refl (term521 A B C D P lt2 s p z g _107457)). Qed.
Lemma lem8114296 {A B C D P : Type'} (_107457 : A -> B) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term510 A B C D P lt2 s p z _107457 g.
Proof. exact (EQ_MP (@lem8114295 A B C D P lt2 s p z _107457 g) (@lem8114294 A B C D P _107457 z g p lt2 s z' y h1)). Qed.
Lemma lem8114297 {A B C D P : Type'} (_107457 : A -> B) (_107458 : A -> B) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term522 A B C D P lt2 s p z _107457 g _107458.
Proof. exact (@lem8114296 A B C D P _107457 z g p lt2 s z' y h1 _107458). Qed.
Lemma lem8114298 {A B C D P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (_107457 : A -> B) (g : type565 A B C D P) (_107458 : A -> B) : (term522 A B C D P lt2 s p z _107457 g _107458) = (term508 A B C D P lt2 s p z _107457 g _107458).
Proof. exact (eq_refl (term522 A B C D P lt2 s p z _107457 g _107458)). Qed.
Lemma lem8114299 {A B C D P : Type'} (_107457 : A -> B) (_107458 : A -> B) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term508 A B C D P lt2 s p z _107457 g _107458.
Proof. exact (EQ_MP (@lem8114298 A B C D P lt2 s p z _107457 g _107458) (@lem8114297 A B C D P _107457 _107458 z g p lt2 s z' y h1)). Qed.
Lemma lem8114300 {A B C D P : Type'} (_107457 : A -> B) (_107458 : A -> B) (_107459 : P) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term523 A B C D P lt2 s p z _107457 g _107458 _107459.
Proof. exact (@lem8114299 A B C D P _107457 _107458 z g p lt2 s z' y h1 _107459). Qed.
Lemma lem8114301 {A B C D P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (_107457 : A -> B) (g : type565 A B C D P) (_107458 : A -> B) (_107459 : P) : (term523 A B C D P lt2 s p z _107457 g _107458 _107459) = (term504 A B C D P lt2 s p z _107457 g _107458 _107459).
Proof. exact (eq_refl (term523 A B C D P lt2 s p z _107457 g _107458 _107459)). Qed.
Lemma lem8114302 {A B C D P : Type'} (_107457 : A -> B) (_107458 : A -> B) (_107459 : P) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term504 A B C D P lt2 s p z _107457 g _107458 _107459.
Proof. exact (EQ_MP (@lem8114301 A B C D P lt2 s p z _107457 g _107458 _107459) (@lem8114300 A B C D P _107457 _107458 _107459 z g p lt2 s z' y h1)). Qed.
Lemma lem8114303 {A B C D P : Type'} (_107460 : A -> B) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term524 A B C P lt2 s p z' y _107460.
Proof. exact (@lem8114272 A B C D P z g p lt2 s z' y h1 _107460). Qed.
Lemma lem8114304 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (_107460 : A -> B) (y : type564 A B C P) : (term524 A B C P lt2 s p z' y _107460) = (term518 A B C P lt2 s p z' _107460 y).
Proof. exact (eq_refl (term524 A B C P lt2 s p z' y _107460)). Qed.
Lemma lem8114305 {A B C D P : Type'} (_107460 : A -> B) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term518 A B C P lt2 s p z' _107460 y.
Proof. exact (EQ_MP (@lem8114304 A B C P lt2 s p z' _107460 y) (@lem8114303 A B C D P _107460 z g p lt2 s z' y h1)). Qed.
Lemma lem8114306 {A B C D P : Type'} (_107460 : A -> B) (_107461 : A -> B) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term525 A B C P lt2 s p z' _107460 y _107461.
Proof. exact (@lem8114305 A B C D P _107460 z g p lt2 s z' y h1 _107461). Qed.
Lemma lem8114307 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (_107460 : A -> B) (y : type564 A B C P) (_107461 : A -> B) : (term525 A B C P lt2 s p z' _107460 y _107461) = (term516 A B C P lt2 s p z' _107460 y _107461).
Proof. exact (eq_refl (term525 A B C P lt2 s p z' _107460 y _107461)). Qed.
Lemma lem8114308 {A B C D P : Type'} (_107460 : A -> B) (_107461 : A -> B) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term516 A B C P lt2 s p z' _107460 y _107461.
Proof. exact (EQ_MP (@lem8114307 A B C P lt2 s p z' _107460 y _107461) (@lem8114306 A B C D P _107460 _107461 z g p lt2 s z' y h1)). Qed.
Lemma lem8114309 {A B C D P : Type'} (_107460 : A -> B) (_107461 : A -> B) (_107462 : P) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term526 A B C P lt2 s p z' _107460 y _107461 _107462.
Proof. exact (@lem8114308 A B C D P _107460 _107461 z g p lt2 s z' y h1 _107462). Qed.
Lemma lem8114310 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (_107460 : A -> B) (y : type564 A B C P) (_107461 : A -> B) (_107462 : P) : (term526 A B C P lt2 s p z' _107460 y _107461 _107462) = (term514 A B C P lt2 s p z' _107460 y _107461 _107462).
Proof. exact (eq_refl (term526 A B C P lt2 s p z' _107460 y _107461 _107462)). Qed.
Lemma lem8114311 {A B C D P : Type'} (_107460 : A -> B) (_107461 : A -> B) (_107462 : P) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term514 A B C P lt2 s p z' _107460 y _107461 _107462.
Proof. exact (EQ_MP (@lem8114310 A B C P lt2 s p z' _107460 y _107461 _107462) (@lem8114309 A B C D P _107460 _107461 _107462 z g p lt2 s z' y h1)). Qed.
Lemma lem8114312 {A B P : Type'} (_107463 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term527 A B P lt2 s a f g' _107463.
Proof. exact (@lem8114293 A B P p lt2 s a f g' h1 _107463). Qed.
Lemma lem8114313 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (_107463 : A) : (term527 A B P lt2 s a f g' _107463) = (term423 A B P lt2 s a f g' _107463).
Proof. exact (eq_refl (term527 A B P lt2 s a f g' _107463)). Qed.
Lemma lem8114315 {A B C D P : Type'} (_107460 : A -> B) (_107461 : A -> B) (_107462 : P) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term528 A B C P p z' _107460 y _107461 _107462.
Proof. exact (proj2 (@lem8114311 A B C D P _107460 _107461 _107462 z g p lt2 s z' y h1)). Qed.
Lemma lem8114316 {A B C D P : Type'} (_107460 : A -> B) (_107461 : A -> B) (_107462 : P) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term529 A B C P p lt2 z' s _107460 y _107461 _107462.
Proof. exact (proj1 (@lem8114311 A B C D P _107460 _107461 _107462 z g p lt2 s z' y h1)). Qed.
Lemma lem8114317 {A B C D P : Type'} (_107457 : A -> B) (_107458 : A -> B) (_107459 : P) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term530 A B C D P p z _107457 g _107458 _107459.
Proof. exact (proj2 (@lem8114302 A B C D P _107457 _107458 _107459 z g p lt2 s z' y h1)). Qed.
Lemma lem8114318 {A B C D P : Type'} (_107457 : A -> B) (_107458 : A -> B) (_107459 : P) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term531 A B C D P p lt2 z s _107457 g _107458 _107459.
Proof. exact (proj1 (@lem8114302 A B C D P _107457 _107458 _107459 z g p lt2 s z' y h1)). Qed.
Lemma lem8114320 {A B C D P : Type'} (f : A -> B) (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) (h1 : term127 A B C D P f g y g' a) : term436 A B C D P f g y g' a.
Proof. exact (EQ_MP (@lem8113719 A B C D P f g y g' a) (@lem8113536 A B C D P f g y g' a h1)). Qed.
Lemma lem8114330 {A B P : Type'} (_107463 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term423 A B P lt2 s a f g' _107463.
Proof. exact (EQ_MP (@lem8114313 A B P lt2 s a f g' _107463) (@lem8114312 A B P _107463 p lt2 s a f g' h1)). Qed.
Lemma lem8114334 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_107460 : A -> B) (y : type564 A B C P) (_107461 : A -> B) (_107462 : P) : (term529 A B C P p lt2 z' s _107460 y _107461 _107462) = (term532 A B C P p lt2 z' s _107460 y _107461 _107462).
Proof. exact (@lem8101094 (term463 A B P p _107460 _107462) (term500 A B P p lt2 z' _107460 _107461 s _107462) ((term430 A B C P y _107460 _107462) = (term430 A B C P y _107461 _107462))). Qed.
Lemma lem8114341 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_107460 : A -> B) (y : type564 A B C P) (_107461 : A -> B) (_107462 : P) : (term533 A B C P p lt2 z' s _107460 y _107461 _107462) = (term534 A B C P p lt2 z' s _107460 y _107461 _107462).
Proof. exact (@lem8101094 (term463 A B P p _107461 _107462) (term458 A B P lt2 z' _107460 _107461 s _107462) ((term430 A B C P y _107460 _107462) = (term430 A B C P y _107461 _107462))). Qed.
Lemma lem8114342 {A B P : Type'} (p : type560 A B P) (_107460 : A -> B) (_107462 : P) : (term464 A B P p _107460 _107462) = (term464 A B P p _107460 _107462).
Proof. exact (eq_refl (term464 A B P p _107460 _107462)). Qed.
Lemma lem8114345 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_107460 : A -> B) (y : type564 A B C P) (_107461 : A -> B) (_107462 : P) : (term532 A B C P p lt2 z' s _107460 y _107461 _107462) = (term535 A B C P p lt2 z' s _107460 y _107461 _107462).
Proof. exact (MK_COMB (@lem8114342 A B P p _107460 _107462) (@lem8114341 A B C P p lt2 z' s _107460 y _107461 _107462)). Qed.
Lemma lem8114347 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_107460 : A -> B) (y : type564 A B C P) (_107461 : A -> B) (_107462 : P) : (term529 A B C P p lt2 z' s _107460 y _107461 _107462) = (term535 A B C P p lt2 z' s _107460 y _107461 _107462).
Proof. exact (TRANS (@lem8114334 A B C P p lt2 z' s _107460 y _107461 _107462) (@lem8114345 A B C P p lt2 z' s _107460 y _107461 _107462)). Qed.
Lemma lem8114348 {A B C D P : Type'} (_107460 : A -> B) (_107461 : A -> B) (_107462 : P) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term535 A B C P p lt2 z' s _107460 y _107461 _107462.
Proof. exact (EQ_MP (@lem8114347 A B C P p lt2 z' s _107460 y _107461 _107462) (@lem8114316 A B C D P _107460 _107461 _107462 z g p lt2 s z' y h1)). Qed.
Lemma lem8114352 {A B C P : Type'} (p : type560 A B P) (z' : type518 A B P) (_107460 : A -> B) (y : type564 A B C P) (_107461 : A -> B) (_107462 : P) : (term528 A B C P p z' _107460 y _107461 _107462) = (term536 A B C P p z' _107460 y _107461 _107462).
Proof. exact (@lem8101094 (term463 A B P p _107460 _107462) (term501 A B P p z' _107460 _107461 _107462) ((term430 A B C P y _107460 _107462) = (term430 A B C P y _107461 _107462))). Qed.
Lemma lem8114359 {A B C P : Type'} (p : type560 A B P) (z' : type518 A B P) (_107460 : A -> B) (y : type564 A B C P) (_107461 : A -> B) (_107462 : P) : (term537 A B C P p z' _107460 y _107461 _107462) = (term538 A B C P p z' _107460 y _107461 _107462).
Proof. exact (@lem8101094 (term463 A B P p _107461 _107462) (term451 A B P z' _107460 _107461 _107462) ((term430 A B C P y _107460 _107462) = (term430 A B C P y _107461 _107462))). Qed.
Lemma lem8114360 {A B P : Type'} (p : type560 A B P) (_107460 : A -> B) (_107462 : P) : (term464 A B P p _107460 _107462) = (term464 A B P p _107460 _107462).
Proof. exact (eq_refl (term464 A B P p _107460 _107462)). Qed.
Lemma lem8114363 {A B C P : Type'} (p : type560 A B P) (z' : type518 A B P) (_107460 : A -> B) (y : type564 A B C P) (_107461 : A -> B) (_107462 : P) : (term536 A B C P p z' _107460 y _107461 _107462) = (term539 A B C P p z' _107460 y _107461 _107462).
Proof. exact (MK_COMB (@lem8114360 A B P p _107460 _107462) (@lem8114359 A B C P p z' _107460 y _107461 _107462)). Qed.
Lemma lem8114365 {A B C P : Type'} (p : type560 A B P) (z' : type518 A B P) (_107460 : A -> B) (y : type564 A B C P) (_107461 : A -> B) (_107462 : P) : (term528 A B C P p z' _107460 y _107461 _107462) = (term539 A B C P p z' _107460 y _107461 _107462).
Proof. exact (TRANS (@lem8114352 A B C P p z' _107460 y _107461 _107462) (@lem8114363 A B C P p z' _107460 y _107461 _107462)). Qed.
Lemma lem8114366 {A B C D P : Type'} (_107460 : A -> B) (_107461 : A -> B) (_107462 : P) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term539 A B C P p z' _107460 y _107461 _107462.
Proof. exact (EQ_MP (@lem8114365 A B C P p z' _107460 y _107461 _107462) (@lem8114315 A B C D P _107460 _107461 _107462 z g p lt2 s z' y h1)). Qed.
Lemma lem8114370 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107457 : A -> B) (g : type565 A B C D P) (_107458 : A -> B) (_107459 : P) : (term531 A B C D P p lt2 z s _107457 g _107458 _107459) = (term540 A B C D P p lt2 z s _107457 g _107458 _107459).
Proof. exact (@lem8101094 (term463 A B P p _107457 _107459) (term500 A B P p lt2 z _107457 _107458 s _107459) ((term432 A B C D P g _107457 _107459) = (term432 A B C D P g _107458 _107459))). Qed.
Lemma lem8114377 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107457 : A -> B) (g : type565 A B C D P) (_107458 : A -> B) (_107459 : P) : (term541 A B C D P p lt2 z s _107457 g _107458 _107459) = (term542 A B C D P p lt2 z s _107457 g _107458 _107459).
Proof. exact (@lem8101094 (term463 A B P p _107458 _107459) (term458 A B P lt2 z _107457 _107458 s _107459) ((term432 A B C D P g _107457 _107459) = (term432 A B C D P g _107458 _107459))). Qed.
Lemma lem8114378 {A B P : Type'} (p : type560 A B P) (_107457 : A -> B) (_107459 : P) : (term464 A B P p _107457 _107459) = (term464 A B P p _107457 _107459).
Proof. exact (eq_refl (term464 A B P p _107457 _107459)). Qed.
Lemma lem8114381 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107457 : A -> B) (g : type565 A B C D P) (_107458 : A -> B) (_107459 : P) : (term540 A B C D P p lt2 z s _107457 g _107458 _107459) = (term543 A B C D P p lt2 z s _107457 g _107458 _107459).
Proof. exact (MK_COMB (@lem8114378 A B P p _107457 _107459) (@lem8114377 A B C D P p lt2 z s _107457 g _107458 _107459)). Qed.
Lemma lem8114383 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107457 : A -> B) (g : type565 A B C D P) (_107458 : A -> B) (_107459 : P) : (term531 A B C D P p lt2 z s _107457 g _107458 _107459) = (term543 A B C D P p lt2 z s _107457 g _107458 _107459).
Proof. exact (TRANS (@lem8114370 A B C D P p lt2 z s _107457 g _107458 _107459) (@lem8114381 A B C D P p lt2 z s _107457 g _107458 _107459)). Qed.
Lemma lem8114384 {A B C D P : Type'} (_107457 : A -> B) (_107458 : A -> B) (_107459 : P) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term543 A B C D P p lt2 z s _107457 g _107458 _107459.
Proof. exact (EQ_MP (@lem8114383 A B C D P p lt2 z s _107457 g _107458 _107459) (@lem8114318 A B C D P _107457 _107458 _107459 z g p lt2 s z' y h1)). Qed.
Lemma lem8114388 {A B C D P : Type'} (p : type560 A B P) (z : type518 A B P) (_107457 : A -> B) (g : type565 A B C D P) (_107458 : A -> B) (_107459 : P) : (term530 A B C D P p z _107457 g _107458 _107459) = (term544 A B C D P p z _107457 g _107458 _107459).
Proof. exact (@lem8101094 (term463 A B P p _107457 _107459) (term501 A B P p z _107457 _107458 _107459) ((term432 A B C D P g _107457 _107459) = (term432 A B C D P g _107458 _107459))). Qed.
Lemma lem8114395 {A B C D P : Type'} (p : type560 A B P) (z : type518 A B P) (_107457 : A -> B) (g : type565 A B C D P) (_107458 : A -> B) (_107459 : P) : (term545 A B C D P p z _107457 g _107458 _107459) = (term546 A B C D P p z _107457 g _107458 _107459).
Proof. exact (@lem8101094 (term463 A B P p _107458 _107459) (term451 A B P z _107457 _107458 _107459) ((term432 A B C D P g _107457 _107459) = (term432 A B C D P g _107458 _107459))). Qed.
Lemma lem8114396 {A B P : Type'} (p : type560 A B P) (_107457 : A -> B) (_107459 : P) : (term464 A B P p _107457 _107459) = (term464 A B P p _107457 _107459).
Proof. exact (eq_refl (term464 A B P p _107457 _107459)). Qed.
Lemma lem8114399 {A B C D P : Type'} (p : type560 A B P) (z : type518 A B P) (_107457 : A -> B) (g : type565 A B C D P) (_107458 : A -> B) (_107459 : P) : (term544 A B C D P p z _107457 g _107458 _107459) = (term547 A B C D P p z _107457 g _107458 _107459).
Proof. exact (MK_COMB (@lem8114396 A B P p _107457 _107459) (@lem8114395 A B C D P p z _107457 g _107458 _107459)). Qed.
Lemma lem8114401 {A B C D P : Type'} (p : type560 A B P) (z : type518 A B P) (_107457 : A -> B) (g : type565 A B C D P) (_107458 : A -> B) (_107459 : P) : (term530 A B C D P p z _107457 g _107458 _107459) = (term547 A B C D P p z _107457 g _107458 _107459).
Proof. exact (TRANS (@lem8114388 A B C D P p z _107457 g _107458 _107459) (@lem8114399 A B C D P p z _107457 g _107458 _107459)). Qed.
Lemma lem8114402 {A B C D P : Type'} (_107457 : A -> B) (_107458 : A -> B) (_107459 : P) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term547 A B C D P p z _107457 g _107458 _107459.
Proof. exact (EQ_MP (@lem8114401 A B C D P p z _107457 g _107458 _107459) (@lem8114317 A B C D P _107457 _107458 _107459 z g p lt2 s z' y h1)). Qed.
Lemma lem8114591 {C D : Type'} : (@I (C -> D)) = (@I (C -> D)).
Proof. exact (eq_refl (@I (C -> D))). Qed.
Lemma lem8114592 {C D : Type'} (_107512 : C -> D) (_107514 : C -> D) (h1 : _107512 = _107514) : _107512 = _107514.
Proof. exact (h1). Qed.
Lemma lem8114593 {C : Type'} (_107513 : C) (_107515 : C) (h1 : _107513 = _107515) : _107513 = _107515.
Proof. exact (h1). Qed.
Lemma lem8114594 {C D : Type'} (_107512 : C -> D) (_107514 : C -> D) (h1 : _107512 = _107514) : (@I (C -> D) _107512) = (@I (C -> D) _107514).
Proof. exact (MK_COMB (@lem8114591 C D) (@lem8114592 C D _107512 _107514 h1)). Qed.
Lemma lem8114595 {C D : Type'} (_107513 : C) (_107515 : C) (_107512 : C -> D) (_107514 : C -> D) (h1 : _107513 = _107515) (h2 : _107512 = _107514) : (@I (C -> D) _107512 _107513) = (@I (C -> D) _107514 _107515).
Proof. exact (MK_COMB (@lem8114594 C D _107512 _107514 h2) (@lem8114593 C _107513 _107515 h1)). Qed.
Lemma lem8114596 {C D : Type'} (_107512 : C -> D) (_107514 : C -> D) (_107513 : C) (_107515 : C) (h1 : _107513 = _107515) : term548 C D _107512 _107513 _107514 _107515.
Proof. exact (fun h0 : _107512 = _107514 => @lem8114595 C D _107513 _107515 _107512 _107514 h1 h0). Qed.
Lemma lem8114598 (a : Prop) (b : Prop) : (a -> b) = (term549 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem8114599 {C D : Type'} (_107512 : C -> D) (_107513 : C) (_107514 : C -> D) (_107515 : C) : (term548 C D _107512 _107513 _107514 _107515) = (term550 C D _107512 _107513 _107514 _107515).
Proof. exact (@lem8114598 (_107512 = _107514) ((@I (C -> D) _107512 _107513) = (@I (C -> D) _107514 _107515))). Qed.
Lemma lem8114600 {C D : Type'} (_107512 : C -> D) (_107514 : C -> D) (_107513 : C) (_107515 : C) (h1 : _107513 = _107515) : term550 C D _107512 _107513 _107514 _107515.
Proof. exact (EQ_MP (@lem8114599 C D _107512 _107513 _107514 _107515) (@lem8114596 C D _107512 _107514 _107513 _107515 h1)). Qed.
Lemma lem8114601 {C D : Type'} (_107512 : C -> D) (_107513 : C) (_107514 : C -> D) (_107515 : C) : term551 C D _107512 _107513 _107514 _107515.
Proof. exact (fun h0 : _107513 = _107515 => @lem8114600 C D _107512 _107514 _107513 _107515 h0). Qed.
Lemma lem8114603 (a : Prop) (b : Prop) : (a -> b) = (term549 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem8114604 {C D : Type'} (_107512 : C -> D) (_107513 : C) (_107514 : C -> D) (_107515 : C) : (term551 C D _107512 _107513 _107514 _107515) = (term552 C D _107512 _107513 _107514 _107515).
Proof. exact (@lem8114603 (_107513 = _107515) (term550 C D _107512 _107513 _107514 _107515)). Qed.
Lemma lem8114605 {C D : Type'} (_107512 : C -> D) (_107513 : C) (_107514 : C -> D) (_107515 : C) : term552 C D _107512 _107513 _107514 _107515.
Proof. exact (EQ_MP (@lem8114604 C D _107512 _107513 _107514 _107515) (@lem8114601 C D _107512 _107513 _107514 _107515)). Qed.
Lemma lem8114609 {C D : Type'} (x : C -> D) (y : C -> D) (z : C -> D) : term553 C D x y z.
Proof. exact (@lem21385 (C -> D) x y z). Qed.
Lemma lem8114629 {B : Type'} (x : B) (y : B) (z : B) : term554 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem8114643 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term426 A B P p f a.
Proof. exact (proj1 (@lem8113630 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8114644 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term555 A B P p f a.
Proof. exact (fun h0 : term463 A B P p f a => @lem8114643 A B P p lt2 s a f g' h1). Qed.
Lemma lem8114646 (p : Prop) : (term556 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8114647 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term555 A B P p f a) = (term426 A B P p f a).
Proof. exact (@lem8114646 (term426 A B P p f a)). Qed.
Lemma lem8114648 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term426 A B P p f a.
Proof. exact (EQ_MP (@lem8114647 A B P p f a) (@lem8114644 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8114650 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term426 A B P p g' a.
Proof. exact (proj1 (@lem8114159 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8114651 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term555 A B P p g' a.
Proof. exact (fun h0 : term463 A B P p g' a => @lem8114650 A B P p lt2 s a f g' h1). Qed.
Lemma lem8114653 (p : Prop) : (term556 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8114654 {A B P : Type'} (p : type560 A B P) (g' : A -> B) (a : P) : (term555 A B P p g' a) = (term426 A B P p g' a).
Proof. exact (@lem8114653 (term426 A B P p g' a)). Qed.
Lemma lem8114655 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term426 A B P p g' a.
Proof. exact (EQ_MP (@lem8114654 A B P p g' a) (@lem8114651 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8114657 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term426 A B P p f a.
Proof. exact (proj1 (@lem8113630 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8114658 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term555 A B P p f a.
Proof. exact (fun h0 : term463 A B P p f a => @lem8114657 A B P p lt2 s a f g' h1). Qed.
Lemma lem8114660 (p : Prop) : (term556 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8114661 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term555 A B P p f a) = (term426 A B P p f a).
Proof. exact (@lem8114660 (term426 A B P p f a)). Qed.
Lemma lem8114662 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term426 A B P p f a.
Proof. exact (EQ_MP (@lem8114661 A B P p f a) (@lem8114658 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8114664 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term426 A B P p g' a.
Proof. exact (proj1 (@lem8114159 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8114665 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term555 A B P p g' a.
Proof. exact (fun h0 : term463 A B P p g' a => @lem8114664 A B P p lt2 s a f g' h1). Qed.
Lemma lem8114667 (p : Prop) : (term556 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8114668 {A B P : Type'} (p : type560 A B P) (g' : A -> B) (a : P) : (term555 A B P p g' a) = (term426 A B P p g' a).
Proof. exact (@lem8114667 (term426 A B P p g' a)). Qed.
Lemma lem8114669 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term426 A B P p g' a.
Proof. exact (EQ_MP (@lem8114668 A B P p g' a) (@lem8114665 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8114672 {A B C P : Type'} (f : A -> B) (y : type564 A B C P) (g' : A -> B) (a : P) (h1 : term557 A B C P f y g' a) : term557 A B C P f y g' a.
Proof. exact (h1). Qed.
Lemma lem8114673 {A B C P : Type'} (f : A -> B) (y : type564 A B C P) (g' : A -> B) (a : P) (h1 : term557 A B C P f y g' a) : term558 A B C P f y g' a.
Proof. exact (fun h0 : (term430 A B C P y f a) = (term430 A B C P y g' a) => @lem8114672 A B C P f y g' a h1). Qed.
Lemma lem8114675 (p : Prop) : (term559 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem8114676 {A B C P : Type'} (f : A -> B) (y : type564 A B C P) (g' : A -> B) (a : P) : (term558 A B C P f y g' a) = (term557 A B C P f y g' a).
Proof. exact (@lem8114675 ((term430 A B C P y f a) = (term430 A B C P y g' a))). Qed.
Lemma lem8114677 {A B C P : Type'} (f : A -> B) (y : type564 A B C P) (g' : A -> B) (a : P) (h1 : term557 A B C P f y g' a) : term557 A B C P f y g' a.
Proof. exact (EQ_MP (@lem8114676 A B C P f y g' a) (@lem8114673 A B C P f y g' a h1)). Qed.
Lemma lem8114693 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8114694 {A B C P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (p : type560 A B P) (_107460 : A -> B) (y : type564 A B C P) (_107461 : A -> B) (_107462 : P) : (term534 A B C P p lt2 z' s _107460 y _107461 _107462) = (term560 A B C P lt2 z' s p _107460 y _107461 _107462).
Proof. exact (@lem8114693 (term458 A B P lt2 z' _107460 _107461 s _107462) (term463 A B P p _107461 _107462) ((term430 A B C P y _107460 _107462) = (term430 A B C P y _107461 _107462))). Qed.
Lemma lem8114708 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8114709 {A B C P : Type'} (_107460 : A -> B) (y : type564 A B C P) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term561 A B C P p _107460 y _107461 _107462) = (term562 A B C P _107460 y p _107461 _107462).
Proof. exact (@lem8114708 ((term430 A B C P y _107460 _107462) = (term430 A B C P y _107461 _107462)) (term463 A B P p _107461 _107462)). Qed.
Lemma lem8114717 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (_107460 : A -> B) (_107461 : A -> B) (s : P -> A) (_107462 : P) : (term563 A B P lt2 z' _107460 _107461 s _107462) = (term563 A B P lt2 z' _107460 _107461 s _107462).
Proof. exact (eq_refl (term563 A B P lt2 z' _107460 _107461 s _107462)). Qed.
Lemma lem8114718 {A B C P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_107460 : A -> B) (y : type564 A B C P) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term560 A B C P lt2 z' s p _107460 y _107461 _107462) = (term564 A B C P lt2 z' s _107460 y p _107461 _107462).
Proof. exact (MK_COMB (@lem8114717 A B P lt2 z' _107460 _107461 s _107462) (@lem8114709 A B C P _107460 y p _107461 _107462)). Qed.
Lemma lem8114722 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8114723 {A B C P : Type'} (y : type564 A B C P) (lt2 : type1402 A) (z' : type518 A B P) (_107460 : A -> B) (s : P -> A) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term564 A B C P lt2 z' s _107460 y p _107461 _107462) = (term565 A B C P y lt2 z' _107460 s p _107461 _107462).
Proof. exact (@lem8114722 ((term430 A B C P y _107460 _107462) = (term430 A B C P y _107461 _107462)) (term458 A B P lt2 z' _107460 _107461 s _107462) (term463 A B P p _107461 _107462)). Qed.
Lemma lem8114741 {A B C P : Type'} (y : type564 A B C P) (lt2 : type1402 A) (z' : type518 A B P) (_107460 : A -> B) (s : P -> A) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term560 A B C P lt2 z' s p _107460 y _107461 _107462) = (term565 A B C P y lt2 z' _107460 s p _107461 _107462).
Proof. exact (TRANS (@lem8114718 A B C P lt2 z' s _107460 y p _107461 _107462) (@lem8114723 A B C P y lt2 z' _107460 s p _107461 _107462)). Qed.
Lemma lem8114742 {A B C P : Type'} (y : type564 A B C P) (lt2 : type1402 A) (z' : type518 A B P) (_107460 : A -> B) (s : P -> A) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term534 A B C P p lt2 z' s _107460 y _107461 _107462) = (term565 A B C P y lt2 z' _107460 s p _107461 _107462).
Proof. exact (TRANS (@lem8114694 A B C P lt2 z' s p _107460 y _107461 _107462) (@lem8114741 A B C P y lt2 z' _107460 s p _107461 _107462)). Qed.
Lemma lem8114743 {A B P : Type'} (p : type560 A B P) (_107460 : A -> B) (_107462 : P) : (term464 A B P p _107460 _107462) = (term464 A B P p _107460 _107462).
Proof. exact (eq_refl (term464 A B P p _107460 _107462)). Qed.
Lemma lem8114744 {A B C P : Type'} (y : type564 A B C P) (lt2 : type1402 A) (z' : type518 A B P) (_107460 : A -> B) (s : P -> A) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term535 A B C P p lt2 z' s _107460 y _107461 _107462) = (term566 A B C P y lt2 z' _107460 s p _107461 _107462).
Proof. exact (MK_COMB (@lem8114743 A B P p _107460 _107462) (@lem8114742 A B C P y lt2 z' _107460 s p _107461 _107462)). Qed.
Lemma lem8114748 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8114749 {A B C P : Type'} (y : type564 A B C P) (lt2 : type1402 A) (z' : type518 A B P) (_107460 : A -> B) (s : P -> A) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term566 A B C P y lt2 z' _107460 s p _107461 _107462) = (term567 A B C P y lt2 z' _107460 s p _107461 _107462).
Proof. exact (@lem8114748 ((term430 A B C P y _107460 _107462) = (term430 A B C P y _107461 _107462)) (term463 A B P p _107460 _107462) (term568 A B P lt2 z' _107460 s p _107461 _107462)). Qed.
Lemma lem8114765 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8114766 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_107460 : A -> B) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term569 A B P lt2 z' _107460 s p _107461 _107462) = (term570 A B P lt2 z' s _107460 p _107461 _107462).
Proof. exact (@lem8114765 (term458 A B P lt2 z' _107460 _107461 s _107462) (term463 A B P p _107460 _107462) (term463 A B P p _107461 _107462)). Qed.
Lemma lem8114782 {A B C P : Type'} (_107460 : A -> B) (y : type564 A B C P) (_107461 : A -> B) (_107462 : P) : (term571 A B C P _107460 y _107461 _107462) = (term571 A B C P _107460 y _107461 _107462).
Proof. exact (eq_refl (term571 A B C P _107460 y _107461 _107462)). Qed.
Lemma lem8114783 {A B C P : Type'} (y : type564 A B C P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_107460 : A -> B) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term567 A B C P y lt2 z' _107460 s p _107461 _107462) = (term572 A B C P y lt2 z' s _107460 p _107461 _107462).
Proof. exact (MK_COMB (@lem8114782 A B C P _107460 y _107461 _107462) (@lem8114766 A B P lt2 z' s _107460 p _107461 _107462)). Qed.
Lemma lem8114794 {A B C P : Type'} (y : type564 A B C P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_107460 : A -> B) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term566 A B C P y lt2 z' _107460 s p _107461 _107462) = (term572 A B C P y lt2 z' s _107460 p _107461 _107462).
Proof. exact (TRANS (@lem8114749 A B C P y lt2 z' _107460 s p _107461 _107462) (@lem8114783 A B C P y lt2 z' s _107460 p _107461 _107462)). Qed.
Lemma lem8114795 {A B C P : Type'} (y : type564 A B C P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_107460 : A -> B) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term535 A B C P p lt2 z' s _107460 y _107461 _107462) = (term572 A B C P y lt2 z' s _107460 p _107461 _107462).
Proof. exact (TRANS (@lem8114744 A B C P y lt2 z' _107460 s p _107461 _107462) (@lem8114794 A B C P y lt2 z' s _107460 p _107461 _107462)). Qed.
Lemma lem8114796 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8114797 {A B C P : Type'} (y : type564 A B C P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_107460 : A -> B) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term573 A B C P p lt2 z' s _107460 y _107461 _107462) = (term574 A B C P y lt2 z' s _107460 p _107461 _107462).
Proof. exact (MK_COMB (@lem8114796) (@lem8114795 A B C P y lt2 z' s _107460 p _107461 _107462)). Qed.
Lemma lem8114821 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8114822 {A B C P : Type'} (_107460 : A -> B) (y : type564 A B C P) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term561 A B C P p _107460 y _107461 _107462) = (term562 A B C P _107460 y p _107461 _107462).
Proof. exact (@lem8114821 ((term430 A B C P y _107460 _107462) = (term430 A B C P y _107461 _107462)) (term463 A B P p _107461 _107462)). Qed.
Lemma lem8114830 {A B P : Type'} (p : type560 A B P) (_107460 : A -> B) (_107462 : P) : (term464 A B P p _107460 _107462) = (term464 A B P p _107460 _107462).
Proof. exact (eq_refl (term464 A B P p _107460 _107462)). Qed.
Lemma lem8114831 {A B C P : Type'} (_107460 : A -> B) (y : type564 A B C P) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term575 A B C P p _107460 y _107461 _107462) = (term576 A B C P _107460 y p _107461 _107462).
Proof. exact (MK_COMB (@lem8114830 A B P p _107460 _107462) (@lem8114822 A B C P _107460 y p _107461 _107462)). Qed.
Lemma lem8114835 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8114836 {A B C P : Type'} (y : type564 A B C P) (_107460 : A -> B) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term576 A B C P _107460 y p _107461 _107462) = (term577 A B C P y _107460 p _107461 _107462).
Proof. exact (@lem8114835 ((term430 A B C P y _107460 _107462) = (term430 A B C P y _107461 _107462)) (term463 A B P p _107460 _107462) (term463 A B P p _107461 _107462)). Qed.
Lemma lem8114854 {A B C P : Type'} (y : type564 A B C P) (_107460 : A -> B) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term575 A B C P p _107460 y _107461 _107462) = (term577 A B C P y _107460 p _107461 _107462).
Proof. exact (TRANS (@lem8114831 A B C P _107460 y p _107461 _107462) (@lem8114836 A B C P y _107460 p _107461 _107462)). Qed.
Lemma lem8114855 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (_107460 : A -> B) (_107461 : A -> B) (s : P -> A) (_107462 : P) : (term563 A B P lt2 z' _107460 _107461 s _107462) = (term563 A B P lt2 z' _107460 _107461 s _107462).
Proof. exact (eq_refl (term563 A B P lt2 z' _107460 _107461 s _107462)). Qed.
Lemma lem8114856 {A B C P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (y : type564 A B C P) (_107460 : A -> B) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term578 A B C P lt2 z' s p _107460 y _107461 _107462) = (term579 A B C P lt2 z' s y _107460 p _107461 _107462).
Proof. exact (MK_COMB (@lem8114855 A B P lt2 z' _107460 _107461 s _107462) (@lem8114854 A B C P y _107460 p _107461 _107462)). Qed.
Lemma lem8114860 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8114861 {A B C P : Type'} (y : type564 A B C P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_107460 : A -> B) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term579 A B C P lt2 z' s y _107460 p _107461 _107462) = (term572 A B C P y lt2 z' s _107460 p _107461 _107462).
Proof. exact (@lem8114860 ((term430 A B C P y _107460 _107462) = (term430 A B C P y _107461 _107462)) (term458 A B P lt2 z' _107460 _107461 s _107462) (term580 A B P _107460 p _107461 _107462)). Qed.
Lemma lem8114889 {A B C P : Type'} (y : type564 A B C P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_107460 : A -> B) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term578 A B C P lt2 z' s p _107460 y _107461 _107462) = (term572 A B C P y lt2 z' s _107460 p _107461 _107462).
Proof. exact (TRANS (@lem8114856 A B C P lt2 z' s y _107460 p _107461 _107462) (@lem8114861 A B C P y lt2 z' s _107460 p _107461 _107462)). Qed.
Lemma lem8114890 {A B C P : Type'} (y : type564 A B C P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_107460 : A -> B) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : ((term535 A B C P p lt2 z' s _107460 y _107461 _107462) = (term578 A B C P lt2 z' s p _107460 y _107461 _107462)) = ((term572 A B C P y lt2 z' s _107460 p _107461 _107462) = (term572 A B C P y lt2 z' s _107460 p _107461 _107462)).
Proof. exact (MK_COMB (@lem8114797 A B C P y lt2 z' s _107460 p _107461 _107462) (@lem8114889 A B C P y lt2 z' s _107460 p _107461 _107462)). Qed.
Lemma lem8114892 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8114893 (x : Prop) : (x = x) = True.
Proof. exact (@lem8114892 Prop x). Qed.
Lemma lem8114894 {A B C P : Type'} (y : type564 A B C P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_107460 : A -> B) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : ((term572 A B C P y lt2 z' s _107460 p _107461 _107462) = (term572 A B C P y lt2 z' s _107460 p _107461 _107462)) = True.
Proof. exact (@lem8114893 (term572 A B C P y lt2 z' s _107460 p _107461 _107462)). Qed.
Lemma lem8114895 {A B C P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (p : type560 A B P) (_107460 : A -> B) (y : type564 A B C P) (_107461 : A -> B) (_107462 : P) : ((term535 A B C P p lt2 z' s _107460 y _107461 _107462) = (term578 A B C P lt2 z' s p _107460 y _107461 _107462)) = True.
Proof. exact (TRANS (@lem8114890 A B C P y lt2 z' s _107460 p _107461 _107462) (@lem8114894 A B C P y lt2 z' s _107460 p _107461 _107462)). Qed.
Lemma lem8114896 {A B C P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (p : type560 A B P) (_107460 : A -> B) (y : type564 A B C P) (_107461 : A -> B) (_107462 : P) : True = ((term535 A B C P p lt2 z' s _107460 y _107461 _107462) = (term578 A B C P lt2 z' s p _107460 y _107461 _107462)).
Proof. exact (SYM (@lem8114895 A B C P lt2 z' s p _107460 y _107461 _107462)). Qed.
Lemma lem8114897 {A B C P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (p : type560 A B P) (_107460 : A -> B) (y : type564 A B C P) (_107461 : A -> B) (_107462 : P) : (term535 A B C P p lt2 z' s _107460 y _107461 _107462) = (term578 A B C P lt2 z' s p _107460 y _107461 _107462).
Proof. exact (EQ_MP (@lem8114896 A B C P lt2 z' s p _107460 y _107461 _107462) (@lem0)). Qed.
Lemma lem8114898 {A B C D P : Type'} (_107460 : A -> B) (_107461 : A -> B) (_107462 : P) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term578 A B C P lt2 z' s p _107460 y _107461 _107462.
Proof. exact (EQ_MP (@lem8114897 A B C P lt2 z' s p _107460 y _107461 _107462) (@lem8114348 A B C D P _107460 _107461 _107462 z g p lt2 s z' y h1)). Qed.
Lemma lem8114900 (b : Prop) (a : Prop) : (a \/ b) = (term581 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8114901 {A B C P : Type'} (p : type560 A B P) (y : type564 A B C P) (lt2 : type1402 A) (z' : type518 A B P) (_107460 : A -> B) (_107461 : A -> B) (s : P -> A) (_107462 : P) : (term578 A B C P lt2 z' s p _107460 y _107461 _107462) = (term582 A B C P p y lt2 z' _107460 _107461 s _107462).
Proof. exact (@lem8114900 (term575 A B C P p _107460 y _107461 _107462) (term458 A B P lt2 z' _107460 _107461 s _107462)). Qed.
Lemma lem8114903 (a : Prop) (b : Prop) : (term583 a b) = (term584 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8114904 {A B C P : Type'} (p : type560 A B P) (_107460 : A -> B) (y : type564 A B C P) (_107461 : A -> B) (_107462 : P) : (term585 A B C P p _107460 y _107461 _107462) = (term586 A B C P p _107460 y _107461 _107462).
Proof. exact (@lem8114903 (term463 A B P p _107460 _107462) (term561 A B C P p _107460 y _107461 _107462)). Qed.
Lemma lem8114906 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8114907 {A B P : Type'} (p : type560 A B P) (_107460 : A -> B) (_107462 : P) : (term587 A B P p _107460 _107462) = (term426 A B P p _107460 _107462).
Proof. exact (@lem8114906 (term426 A B P p _107460 _107462)). Qed.
Lemma lem8114908 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8114909 {A B P : Type'} (p : type560 A B P) (_107460 : A -> B) (_107462 : P) : (term588 A B P p _107460 _107462) = (term427 A B P p _107460 _107462).
Proof. exact (MK_COMB (@lem8114908) (@lem8114907 A B P p _107460 _107462)). Qed.
Lemma lem8114911 (a : Prop) (b : Prop) : (term583 a b) = (term584 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8114912 {A B C P : Type'} (p : type560 A B P) (_107460 : A -> B) (y : type564 A B C P) (_107461 : A -> B) (_107462 : P) : (term589 A B C P p _107460 y _107461 _107462) = (term590 A B C P p _107460 y _107461 _107462).
Proof. exact (@lem8114911 (term463 A B P p _107461 _107462) ((term430 A B C P y _107460 _107462) = (term430 A B C P y _107461 _107462))). Qed.
Lemma lem8114914 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8114915 {A B P : Type'} (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term587 A B P p _107461 _107462) = (term426 A B P p _107461 _107462).
Proof. exact (@lem8114914 (term426 A B P p _107461 _107462)). Qed.
Lemma lem8114916 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8114917 {A B P : Type'} (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term588 A B P p _107461 _107462) = (term427 A B P p _107461 _107462).
Proof. exact (MK_COMB (@lem8114916) (@lem8114915 A B P p _107461 _107462)). Qed.
Lemma lem8114918 {A B C P : Type'} (_107460 : A -> B) (y : type564 A B C P) (_107461 : A -> B) (_107462 : P) : (term557 A B C P _107460 y _107461 _107462) = (term557 A B C P _107460 y _107461 _107462).
Proof. exact (eq_refl (term557 A B C P _107460 y _107461 _107462)). Qed.
Lemma lem8114919 {A B C P : Type'} (p : type560 A B P) (_107460 : A -> B) (y : type564 A B C P) (_107461 : A -> B) (_107462 : P) : (term590 A B C P p _107460 y _107461 _107462) = (term591 A B C P p _107460 y _107461 _107462).
Proof. exact (MK_COMB (@lem8114917 A B P p _107461 _107462) (@lem8114918 A B C P _107460 y _107461 _107462)). Qed.
Lemma lem8114920 {A B C P : Type'} (p : type560 A B P) (_107460 : A -> B) (y : type564 A B C P) (_107461 : A -> B) (_107462 : P) : (term589 A B C P p _107460 y _107461 _107462) = (term591 A B C P p _107460 y _107461 _107462).
Proof. exact (TRANS (@lem8114912 A B C P p _107460 y _107461 _107462) (@lem8114919 A B C P p _107460 y _107461 _107462)). Qed.
Lemma lem8114921 {A B C P : Type'} (p : type560 A B P) (_107460 : A -> B) (y : type564 A B C P) (_107461 : A -> B) (_107462 : P) : (term586 A B C P p _107460 y _107461 _107462) = (term592 A B C P p _107460 y _107461 _107462).
Proof. exact (MK_COMB (@lem8114909 A B P p _107460 _107462) (@lem8114920 A B C P p _107460 y _107461 _107462)). Qed.
Lemma lem8114922 {A B C P : Type'} (p : type560 A B P) (_107460 : A -> B) (y : type564 A B C P) (_107461 : A -> B) (_107462 : P) : (term585 A B C P p _107460 y _107461 _107462) = (term592 A B C P p _107460 y _107461 _107462).
Proof. exact (TRANS (@lem8114904 A B C P p _107460 y _107461 _107462) (@lem8114921 A B C P p _107460 y _107461 _107462)). Qed.
Lemma lem8114923 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8114924 {A B C P : Type'} (p : type560 A B P) (_107460 : A -> B) (y : type564 A B C P) (_107461 : A -> B) (_107462 : P) : (term593 A B C P p _107460 y _107461 _107462) = (term594 A B C P p _107460 y _107461 _107462).
Proof. exact (MK_COMB (@lem8114923) (@lem8114922 A B C P p _107460 y _107461 _107462)). Qed.
Lemma lem8114925 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (_107460 : A -> B) (_107461 : A -> B) (s : P -> A) (_107462 : P) : (term458 A B P lt2 z' _107460 _107461 s _107462) = (term458 A B P lt2 z' _107460 _107461 s _107462).
Proof. exact (eq_refl (term458 A B P lt2 z' _107460 _107461 s _107462)). Qed.
Lemma lem8114926 {A B C P : Type'} (p : type560 A B P) (y : type564 A B C P) (lt2 : type1402 A) (z' : type518 A B P) (_107460 : A -> B) (_107461 : A -> B) (s : P -> A) (_107462 : P) : (term582 A B C P p y lt2 z' _107460 _107461 s _107462) = (term595 A B C P p y lt2 z' _107460 _107461 s _107462).
Proof. exact (MK_COMB (@lem8114924 A B C P p _107460 y _107461 _107462) (@lem8114925 A B P lt2 z' _107460 _107461 s _107462)). Qed.
Lemma lem8114927 {A B C P : Type'} (p : type560 A B P) (y : type564 A B C P) (lt2 : type1402 A) (z' : type518 A B P) (_107460 : A -> B) (_107461 : A -> B) (s : P -> A) (_107462 : P) : (term578 A B C P lt2 z' s p _107460 y _107461 _107462) = (term595 A B C P p y lt2 z' _107460 _107461 s _107462).
Proof. exact (TRANS (@lem8114901 A B C P p y lt2 z' _107460 _107461 s _107462) (@lem8114926 A B C P p y lt2 z' _107460 _107461 s _107462)). Qed.
Lemma lem8114929 {A B C P : Type'} (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term557 A B C P f y g' a) (h2 : term35 A B P p lt2 s a f g') : term591 A B C P p f y g' a.
Proof. exact (conj (@lem8114669 A B P p lt2 s a f g' h2) (@lem8114677 A B C P f y g' a h1)). Qed.
Lemma lem8114930 {A B C P : Type'} (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term557 A B C P f y g' a) (h2 : term35 A B P p lt2 s a f g') : term592 A B C P p f y g' a.
Proof. exact (conj (@lem8114662 A B P p lt2 s a f g' h2) (@lem8114929 A B C P y p lt2 s a f g' h1 h2)). Qed.
Lemma lem8114932 {A B C D P : Type'} (_107460 : A -> B) (_107461 : A -> B) (_107462 : P) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term595 A B C P p y lt2 z' _107460 _107461 s _107462.
Proof. exact (EQ_MP (@lem8114927 A B C P p y lt2 z' _107460 _107461 s _107462) (@lem8114898 A B C D P _107460 _107461 _107462 z g p lt2 s z' y h1)). Qed.
Lemma lem8114933 {A B C D P : Type'} (_107460 : A -> B) (_107461 : A -> B) (_107462 : P) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term595 A B C P p y lt2 z' _107460 _107461 s _107462.
Proof. exact (@lem8114932 A B C D P _107460 _107461 _107462 z g p lt2 s z' y h1). Qed.
Lemma lem8114934 {A B C D P : Type'} (f : A -> B) (g' : A -> B) (a : P) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term595 A B C P p y lt2 z' f g' s a.
Proof. exact (@lem8114933 A B C D P f g' a z g p lt2 s z' y h1). Qed.
Lemma lem8114937 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term557 A B C P f y g' a) (h2 : term403 A B C D P z g p lt2 s z' y) (h3 : term35 A B P p lt2 s a f g') : term458 A B P lt2 z' f g' s a.
Proof. exact (@lem8114934 A B C D P f g' a z g p lt2 s z' y h2 (@lem8114930 A B C P y p lt2 s a f g' h1 h3)). Qed.
Lemma lem8114938 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term557 A B C P f y g' a) (h2 : term403 A B C D P z g p lt2 s z' y) (h3 : term35 A B P p lt2 s a f g') : term596 A B P lt2 z' f g' s a.
Proof. exact (fun h0 : term597 A B P lt2 z' f g' s a => @lem8114937 A B C D P z g z' y p lt2 s a f g' h1 h2 h3). Qed.
Lemma lem8114940 (p : Prop) : (term556 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8114941 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (f : A -> B) (g' : A -> B) (s : P -> A) (a : P) : (term596 A B P lt2 z' f g' s a) = (term458 A B P lt2 z' f g' s a).
Proof. exact (@lem8114940 (term458 A B P lt2 z' f g' s a)). Qed.
Lemma lem8114942 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term557 A B C P f y g' a) (h2 : term403 A B C D P z g p lt2 s z' y) (h3 : term35 A B P p lt2 s a f g') : term458 A B P lt2 z' f g' s a.
Proof. exact (EQ_MP (@lem8114941 A B P lt2 z' f g' s a) (@lem8114938 A B C D P z g z' y p lt2 s a f g' h1 h2 h3)). Qed.
Lemma lem8114948 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8114949 {A B P : Type'} (f : A -> B) (g' : A -> B) (lt2 : type1402 A) (_107463 : A) (s : P -> A) (a : P) : (term423 A B P lt2 s a f g' _107463) = (term598 A B P f g' lt2 _107463 s a).
Proof. exact (@lem8114948 ((@I (A -> B) f _107463) = (@I (A -> B) g' _107463)) (term420 A P lt2 _107463 s a)). Qed.
Lemma lem8114957 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8114958 {A B P : Type'} (f : A -> B) (g' : A -> B) (lt2 : type1402 A) (_107463 : A) (s : P -> A) (a : P) : (term599 A B P lt2 s a f g' _107463) = (term600 A B P f g' lt2 _107463 s a).
Proof. exact (MK_COMB (@lem8114957) (@lem8114949 A B P f g' lt2 _107463 s a)). Qed.
Lemma lem8114966 {A B P : Type'} (f : A -> B) (g' : A -> B) (lt2 : type1402 A) (_107463 : A) (s : P -> A) (a : P) : (term598 A B P f g' lt2 _107463 s a) = (term598 A B P f g' lt2 _107463 s a).
Proof. exact (eq_refl (term598 A B P f g' lt2 _107463 s a)). Qed.
Lemma lem8114967 {A B P : Type'} (f : A -> B) (g' : A -> B) (lt2 : type1402 A) (_107463 : A) (s : P -> A) (a : P) : ((term423 A B P lt2 s a f g' _107463) = (term598 A B P f g' lt2 _107463 s a)) = ((term598 A B P f g' lt2 _107463 s a) = (term598 A B P f g' lt2 _107463 s a)).
Proof. exact (MK_COMB (@lem8114958 A B P f g' lt2 _107463 s a) (@lem8114966 A B P f g' lt2 _107463 s a)). Qed.
Lemma lem8114969 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8114970 (x : Prop) : (x = x) = True.
Proof. exact (@lem8114969 Prop x). Qed.
Lemma lem8114971 {A B P : Type'} (f : A -> B) (g' : A -> B) (lt2 : type1402 A) (_107463 : A) (s : P -> A) (a : P) : ((term598 A B P f g' lt2 _107463 s a) = (term598 A B P f g' lt2 _107463 s a)) = True.
Proof. exact (@lem8114970 (term598 A B P f g' lt2 _107463 s a)). Qed.
Lemma lem8114972 {A B P : Type'} (f : A -> B) (g' : A -> B) (lt2 : type1402 A) (_107463 : A) (s : P -> A) (a : P) : ((term423 A B P lt2 s a f g' _107463) = (term598 A B P f g' lt2 _107463 s a)) = True.
Proof. exact (TRANS (@lem8114967 A B P f g' lt2 _107463 s a) (@lem8114971 A B P f g' lt2 _107463 s a)). Qed.
Lemma lem8114973 {A B P : Type'} (f : A -> B) (g' : A -> B) (lt2 : type1402 A) (_107463 : A) (s : P -> A) (a : P) : True = ((term423 A B P lt2 s a f g' _107463) = (term598 A B P f g' lt2 _107463 s a)).
Proof. exact (SYM (@lem8114972 A B P f g' lt2 _107463 s a)). Qed.
Lemma lem8114974 {A B P : Type'} (f : A -> B) (g' : A -> B) (lt2 : type1402 A) (_107463 : A) (s : P -> A) (a : P) : (term423 A B P lt2 s a f g' _107463) = (term598 A B P f g' lt2 _107463 s a).
Proof. exact (EQ_MP (@lem8114973 A B P f g' lt2 _107463 s a) (@lem0)). Qed.
Lemma lem8114975 {A B P : Type'} (_107463 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term598 A B P f g' lt2 _107463 s a.
Proof. exact (EQ_MP (@lem8114974 A B P f g' lt2 _107463 s a) (@lem8114330 A B P _107463 p lt2 s a f g' h1)). Qed.
Lemma lem8114977 (b : Prop) (a : Prop) : (a \/ b) = (term581 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8114978 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (_107463 : A) : (term598 A B P f g' lt2 _107463 s a) = (term601 A B P lt2 s a f g' _107463).
Proof. exact (@lem8114977 (term420 A P lt2 _107463 s a) ((@I (A -> B) f _107463) = (@I (A -> B) g' _107463))). Qed.
Lemma lem8114980 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8114981 {A P : Type'} (lt2 : type1402 A) (_107463 : A) (s : P -> A) (a : P) : (term602 A P lt2 _107463 s a) = (term418 A P lt2 _107463 s a).
Proof. exact (@lem8114980 (term418 A P lt2 _107463 s a)). Qed.
Lemma lem8114982 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8114983 {A P : Type'} (lt2 : type1402 A) (_107463 : A) (s : P -> A) (a : P) : (term603 A P lt2 _107463 s a) = (term604 A P lt2 _107463 s a).
Proof. exact (MK_COMB (@lem8114982) (@lem8114981 A P lt2 _107463 s a)). Qed.
Lemma lem8114984 {A B : Type'} (f : A -> B) (g' : A -> B) (_107463 : A) : ((@I (A -> B) f _107463) = (@I (A -> B) g' _107463)) = ((@I (A -> B) f _107463) = (@I (A -> B) g' _107463)).
Proof. exact (eq_refl ((@I (A -> B) f _107463) = (@I (A -> B) g' _107463))). Qed.
Lemma lem8114985 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (_107463 : A) : (term601 A B P lt2 s a f g' _107463) = (term605 A B P lt2 s a f g' _107463).
Proof. exact (MK_COMB (@lem8114983 A P lt2 _107463 s a) (@lem8114984 A B f g' _107463)). Qed.
Lemma lem8114986 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (_107463 : A) : (term598 A B P f g' lt2 _107463 s a) = (term605 A B P lt2 s a f g' _107463).
Proof. exact (TRANS (@lem8114978 A B P lt2 s a f g' _107463) (@lem8114985 A B P lt2 s a f g' _107463)). Qed.
Lemma lem8114989 {A B P : Type'} (_107463 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term605 A B P lt2 s a f g' _107463.
Proof. exact (EQ_MP (@lem8114986 A B P lt2 s a f g' _107463) (@lem8114975 A B P _107463 p lt2 s a f g' h1)). Qed.
Lemma lem8114990 {A B P : Type'} (_107463 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term605 A B P lt2 s a f g' _107463.
Proof. exact (@lem8114989 A B P _107463 p lt2 s a f g' h1). Qed.
Lemma lem8114991 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term606 A B P lt2 s z' f g' a.
Proof. exact (@lem8114990 A B P (term441 A B P z' f g' a) p lt2 s a f g' h1). Qed.
Lemma lem8114994 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term557 A B C P f y g' a) (h2 : term403 A B C D P z g p lt2 s z' y) (h3 : term35 A B P p lt2 s a f g') : (term444 A B P z' f g' a) = (term447 A B P z' f g' a).
Proof. exact (@lem8114991 A B P z' p lt2 s a f g' h3 (@lem8114942 A B C D P z g z' y p lt2 s a f g' h1 h2 h3)). Qed.
Lemma lem8114995 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term557 A B C P f y g' a) (h2 : term403 A B C D P z g p lt2 s z' y) (h3 : term35 A B P p lt2 s a f g') : term607 A B P z' f g' a.
Proof. exact (fun h0 : term451 A B P z' f g' a => @lem8114994 A B C D P z g z' y p lt2 s a f g' h1 h2 h3). Qed.
Lemma lem8114997 (p : Prop) : (term556 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8114998 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g' : A -> B) (a : P) : (term607 A B P z' f g' a) = ((term444 A B P z' f g' a) = (term447 A B P z' f g' a)).
Proof. exact (@lem8114997 ((term444 A B P z' f g' a) = (term447 A B P z' f g' a))). Qed.
Lemma lem8114999 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term557 A B C P f y g' a) (h2 : term403 A B C D P z g p lt2 s z' y) (h3 : term35 A B P p lt2 s a f g') : (term444 A B P z' f g' a) = (term447 A B P z' f g' a).
Proof. exact (EQ_MP (@lem8114998 A B P z' f g' a) (@lem8114995 A B C D P z g z' y p lt2 s a f g' h1 h2 h3)). Qed.
Lemma lem8115015 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8115016 {A B C P : Type'} (z' : type518 A B P) (p : type560 A B P) (_107460 : A -> B) (y : type564 A B C P) (_107461 : A -> B) (_107462 : P) : (term538 A B C P p z' _107460 y _107461 _107462) = (term608 A B C P z' p _107460 y _107461 _107462).
Proof. exact (@lem8115015 (term451 A B P z' _107460 _107461 _107462) (term463 A B P p _107461 _107462) ((term430 A B C P y _107460 _107462) = (term430 A B C P y _107461 _107462))). Qed.
Lemma lem8115032 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8115033 {A B C P : Type'} (_107460 : A -> B) (y : type564 A B C P) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term561 A B C P p _107460 y _107461 _107462) = (term562 A B C P _107460 y p _107461 _107462).
Proof. exact (@lem8115032 ((term430 A B C P y _107460 _107462) = (term430 A B C P y _107461 _107462)) (term463 A B P p _107461 _107462)). Qed.
Lemma lem8115041 {A B P : Type'} (z' : type518 A B P) (_107460 : A -> B) (_107461 : A -> B) (_107462 : P) : (term609 A B P z' _107460 _107461 _107462) = (term609 A B P z' _107460 _107461 _107462).
Proof. exact (eq_refl (term609 A B P z' _107460 _107461 _107462)). Qed.
Lemma lem8115042 {A B C P : Type'} (z' : type518 A B P) (_107460 : A -> B) (y : type564 A B C P) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term608 A B C P z' p _107460 y _107461 _107462) = (term610 A B C P z' _107460 y p _107461 _107462).
Proof. exact (MK_COMB (@lem8115041 A B P z' _107460 _107461 _107462) (@lem8115033 A B C P _107460 y p _107461 _107462)). Qed.
Lemma lem8115046 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8115047 {A B C P : Type'} (y : type564 A B C P) (z' : type518 A B P) (_107460 : A -> B) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term610 A B C P z' _107460 y p _107461 _107462) = (term611 A B C P y z' _107460 p _107461 _107462).
Proof. exact (@lem8115046 ((term430 A B C P y _107460 _107462) = (term430 A B C P y _107461 _107462)) (term451 A B P z' _107460 _107461 _107462) (term463 A B P p _107461 _107462)). Qed.
Lemma lem8115067 {A B C P : Type'} (y : type564 A B C P) (z' : type518 A B P) (_107460 : A -> B) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term608 A B C P z' p _107460 y _107461 _107462) = (term611 A B C P y z' _107460 p _107461 _107462).
Proof. exact (TRANS (@lem8115042 A B C P z' _107460 y p _107461 _107462) (@lem8115047 A B C P y z' _107460 p _107461 _107462)). Qed.
Lemma lem8115068 {A B C P : Type'} (y : type564 A B C P) (z' : type518 A B P) (_107460 : A -> B) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term538 A B C P p z' _107460 y _107461 _107462) = (term611 A B C P y z' _107460 p _107461 _107462).
Proof. exact (TRANS (@lem8115016 A B C P z' p _107460 y _107461 _107462) (@lem8115067 A B C P y z' _107460 p _107461 _107462)). Qed.
Lemma lem8115069 {A B P : Type'} (p : type560 A B P) (_107460 : A -> B) (_107462 : P) : (term464 A B P p _107460 _107462) = (term464 A B P p _107460 _107462).
Proof. exact (eq_refl (term464 A B P p _107460 _107462)). Qed.
Lemma lem8115070 {A B C P : Type'} (y : type564 A B C P) (z' : type518 A B P) (_107460 : A -> B) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term539 A B C P p z' _107460 y _107461 _107462) = (term612 A B C P y z' _107460 p _107461 _107462).
Proof. exact (MK_COMB (@lem8115069 A B P p _107460 _107462) (@lem8115068 A B C P y z' _107460 p _107461 _107462)). Qed.
Lemma lem8115074 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8115075 {A B C P : Type'} (y : type564 A B C P) (z' : type518 A B P) (_107460 : A -> B) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term612 A B C P y z' _107460 p _107461 _107462) = (term613 A B C P y z' _107460 p _107461 _107462).
Proof. exact (@lem8115074 ((term430 A B C P y _107460 _107462) = (term430 A B C P y _107461 _107462)) (term463 A B P p _107460 _107462) (term614 A B P z' _107460 p _107461 _107462)). Qed.
Lemma lem8115091 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8115092 {A B P : Type'} (z' : type518 A B P) (_107460 : A -> B) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term615 A B P z' _107460 p _107461 _107462) = (term616 A B P z' _107460 p _107461 _107462).
Proof. exact (@lem8115091 (term451 A B P z' _107460 _107461 _107462) (term463 A B P p _107460 _107462) (term463 A B P p _107461 _107462)). Qed.
Lemma lem8115110 {A B C P : Type'} (_107460 : A -> B) (y : type564 A B C P) (_107461 : A -> B) (_107462 : P) : (term571 A B C P _107460 y _107461 _107462) = (term571 A B C P _107460 y _107461 _107462).
Proof. exact (eq_refl (term571 A B C P _107460 y _107461 _107462)). Qed.
Lemma lem8115111 {A B C P : Type'} (y : type564 A B C P) (z' : type518 A B P) (_107460 : A -> B) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term613 A B C P y z' _107460 p _107461 _107462) = (term617 A B C P y z' _107460 p _107461 _107462).
Proof. exact (MK_COMB (@lem8115110 A B C P _107460 y _107461 _107462) (@lem8115092 A B P z' _107460 p _107461 _107462)). Qed.
Lemma lem8115122 {A B C P : Type'} (y : type564 A B C P) (z' : type518 A B P) (_107460 : A -> B) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term612 A B C P y z' _107460 p _107461 _107462) = (term617 A B C P y z' _107460 p _107461 _107462).
Proof. exact (TRANS (@lem8115075 A B C P y z' _107460 p _107461 _107462) (@lem8115111 A B C P y z' _107460 p _107461 _107462)). Qed.
Lemma lem8115123 {A B C P : Type'} (y : type564 A B C P) (z' : type518 A B P) (_107460 : A -> B) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term539 A B C P p z' _107460 y _107461 _107462) = (term617 A B C P y z' _107460 p _107461 _107462).
Proof. exact (TRANS (@lem8115070 A B C P y z' _107460 p _107461 _107462) (@lem8115122 A B C P y z' _107460 p _107461 _107462)). Qed.
Lemma lem8115124 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8115125 {A B C P : Type'} (y : type564 A B C P) (z' : type518 A B P) (_107460 : A -> B) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term618 A B C P p z' _107460 y _107461 _107462) = (term619 A B C P y z' _107460 p _107461 _107462).
Proof. exact (MK_COMB (@lem8115124) (@lem8115123 A B C P y z' _107460 p _107461 _107462)). Qed.
Lemma lem8115151 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8115152 {A B P : Type'} (z' : type518 A B P) (_107460 : A -> B) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term501 A B P p z' _107460 _107461 _107462) = (term614 A B P z' _107460 p _107461 _107462).
Proof. exact (@lem8115151 (term451 A B P z' _107460 _107461 _107462) (term463 A B P p _107461 _107462)). Qed.
Lemma lem8115160 {A B P : Type'} (p : type560 A B P) (_107460 : A -> B) (_107462 : P) : (term464 A B P p _107460 _107462) = (term464 A B P p _107460 _107462).
Proof. exact (eq_refl (term464 A B P p _107460 _107462)). Qed.
Lemma lem8115161 {A B P : Type'} (z' : type518 A B P) (_107460 : A -> B) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term506 A B P p z' _107460 _107461 _107462) = (term615 A B P z' _107460 p _107461 _107462).
Proof. exact (MK_COMB (@lem8115160 A B P p _107460 _107462) (@lem8115152 A B P z' _107460 p _107461 _107462)). Qed.
Lemma lem8115165 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8115166 {A B P : Type'} (z' : type518 A B P) (_107460 : A -> B) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term615 A B P z' _107460 p _107461 _107462) = (term616 A B P z' _107460 p _107461 _107462).
Proof. exact (@lem8115165 (term451 A B P z' _107460 _107461 _107462) (term463 A B P p _107460 _107462) (term463 A B P p _107461 _107462)). Qed.
Lemma lem8115184 {A B P : Type'} (z' : type518 A B P) (_107460 : A -> B) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term506 A B P p z' _107460 _107461 _107462) = (term616 A B P z' _107460 p _107461 _107462).
Proof. exact (TRANS (@lem8115161 A B P z' _107460 p _107461 _107462) (@lem8115166 A B P z' _107460 p _107461 _107462)). Qed.
Lemma lem8115185 {A B C P : Type'} (_107460 : A -> B) (y : type564 A B C P) (_107461 : A -> B) (_107462 : P) : (term571 A B C P _107460 y _107461 _107462) = (term571 A B C P _107460 y _107461 _107462).
Proof. exact (eq_refl (term571 A B C P _107460 y _107461 _107462)). Qed.
Lemma lem8115186 {A B C P : Type'} (y : type564 A B C P) (z' : type518 A B P) (_107460 : A -> B) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term620 A B C P y p z' _107460 _107461 _107462) = (term617 A B C P y z' _107460 p _107461 _107462).
Proof. exact (MK_COMB (@lem8115185 A B C P _107460 y _107461 _107462) (@lem8115184 A B P z' _107460 p _107461 _107462)). Qed.
Lemma lem8115197 {A B C P : Type'} (y : type564 A B C P) (z' : type518 A B P) (_107460 : A -> B) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : ((term539 A B C P p z' _107460 y _107461 _107462) = (term620 A B C P y p z' _107460 _107461 _107462)) = ((term617 A B C P y z' _107460 p _107461 _107462) = (term617 A B C P y z' _107460 p _107461 _107462)).
Proof. exact (MK_COMB (@lem8115125 A B C P y z' _107460 p _107461 _107462) (@lem8115186 A B C P y z' _107460 p _107461 _107462)). Qed.
Lemma lem8115199 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8115200 (x : Prop) : (x = x) = True.
Proof. exact (@lem8115199 Prop x). Qed.
Lemma lem8115201 {A B C P : Type'} (y : type564 A B C P) (z' : type518 A B P) (_107460 : A -> B) (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : ((term617 A B C P y z' _107460 p _107461 _107462) = (term617 A B C P y z' _107460 p _107461 _107462)) = True.
Proof. exact (@lem8115200 (term617 A B C P y z' _107460 p _107461 _107462)). Qed.
Lemma lem8115202 {A B C P : Type'} (y : type564 A B C P) (p : type560 A B P) (z' : type518 A B P) (_107460 : A -> B) (_107461 : A -> B) (_107462 : P) : ((term539 A B C P p z' _107460 y _107461 _107462) = (term620 A B C P y p z' _107460 _107461 _107462)) = True.
Proof. exact (TRANS (@lem8115197 A B C P y z' _107460 p _107461 _107462) (@lem8115201 A B C P y z' _107460 p _107461 _107462)). Qed.
Lemma lem8115203 {A B C P : Type'} (y : type564 A B C P) (p : type560 A B P) (z' : type518 A B P) (_107460 : A -> B) (_107461 : A -> B) (_107462 : P) : True = ((term539 A B C P p z' _107460 y _107461 _107462) = (term620 A B C P y p z' _107460 _107461 _107462)).
Proof. exact (SYM (@lem8115202 A B C P y p z' _107460 _107461 _107462)). Qed.
Lemma lem8115204 {A B C P : Type'} (y : type564 A B C P) (p : type560 A B P) (z' : type518 A B P) (_107460 : A -> B) (_107461 : A -> B) (_107462 : P) : (term539 A B C P p z' _107460 y _107461 _107462) = (term620 A B C P y p z' _107460 _107461 _107462).
Proof. exact (EQ_MP (@lem8115203 A B C P y p z' _107460 _107461 _107462) (@lem0)). Qed.
Lemma lem8115205 {A B C D P : Type'} (_107460 : A -> B) (_107461 : A -> B) (_107462 : P) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term620 A B C P y p z' _107460 _107461 _107462.
Proof. exact (EQ_MP (@lem8115204 A B C P y p z' _107460 _107461 _107462) (@lem8114366 A B C D P _107460 _107461 _107462 z g p lt2 s z' y h1)). Qed.
Lemma lem8115207 (b : Prop) (a : Prop) : (a \/ b) = (term581 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8115208 {A B C P : Type'} (p : type560 A B P) (z' : type518 A B P) (_107460 : A -> B) (y : type564 A B C P) (_107461 : A -> B) (_107462 : P) : (term620 A B C P y p z' _107460 _107461 _107462) = (term621 A B C P p z' _107460 y _107461 _107462).
Proof. exact (@lem8115207 (term506 A B P p z' _107460 _107461 _107462) ((term430 A B C P y _107460 _107462) = (term430 A B C P y _107461 _107462))). Qed.
Lemma lem8115210 (a : Prop) (b : Prop) : (term583 a b) = (term584 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8115211 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_107460 : A -> B) (_107461 : A -> B) (_107462 : P) : (term622 A B P p z' _107460 _107461 _107462) = (term623 A B P p z' _107460 _107461 _107462).
Proof. exact (@lem8115210 (term463 A B P p _107460 _107462) (term501 A B P p z' _107460 _107461 _107462)). Qed.
Lemma lem8115213 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8115214 {A B P : Type'} (p : type560 A B P) (_107460 : A -> B) (_107462 : P) : (term587 A B P p _107460 _107462) = (term426 A B P p _107460 _107462).
Proof. exact (@lem8115213 (term426 A B P p _107460 _107462)). Qed.
Lemma lem8115215 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8115216 {A B P : Type'} (p : type560 A B P) (_107460 : A -> B) (_107462 : P) : (term588 A B P p _107460 _107462) = (term427 A B P p _107460 _107462).
Proof. exact (MK_COMB (@lem8115215) (@lem8115214 A B P p _107460 _107462)). Qed.
Lemma lem8115218 (a : Prop) (b : Prop) : (term583 a b) = (term584 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8115219 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_107460 : A -> B) (_107461 : A -> B) (_107462 : P) : (term624 A B P p z' _107460 _107461 _107462) = (term625 A B P p z' _107460 _107461 _107462).
Proof. exact (@lem8115218 (term463 A B P p _107461 _107462) (term451 A B P z' _107460 _107461 _107462)). Qed.
Lemma lem8115221 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8115222 {A B P : Type'} (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term587 A B P p _107461 _107462) = (term426 A B P p _107461 _107462).
Proof. exact (@lem8115221 (term426 A B P p _107461 _107462)). Qed.
Lemma lem8115223 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8115224 {A B P : Type'} (p : type560 A B P) (_107461 : A -> B) (_107462 : P) : (term588 A B P p _107461 _107462) = (term427 A B P p _107461 _107462).
Proof. exact (MK_COMB (@lem8115223) (@lem8115222 A B P p _107461 _107462)). Qed.
Lemma lem8115226 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8115227 {A B P : Type'} (z' : type518 A B P) (_107460 : A -> B) (_107461 : A -> B) (_107462 : P) : (term626 A B P z' _107460 _107461 _107462) = ((term444 A B P z' _107460 _107461 _107462) = (term447 A B P z' _107460 _107461 _107462)).
Proof. exact (@lem8115226 ((term444 A B P z' _107460 _107461 _107462) = (term447 A B P z' _107460 _107461 _107462))). Qed.
Lemma lem8115228 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_107460 : A -> B) (_107461 : A -> B) (_107462 : P) : (term625 A B P p z' _107460 _107461 _107462) = (term627 A B P p z' _107460 _107461 _107462).
Proof. exact (MK_COMB (@lem8115224 A B P p _107461 _107462) (@lem8115227 A B P z' _107460 _107461 _107462)). Qed.
Lemma lem8115229 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_107460 : A -> B) (_107461 : A -> B) (_107462 : P) : (term624 A B P p z' _107460 _107461 _107462) = (term627 A B P p z' _107460 _107461 _107462).
Proof. exact (TRANS (@lem8115219 A B P p z' _107460 _107461 _107462) (@lem8115228 A B P p z' _107460 _107461 _107462)). Qed.
Lemma lem8115230 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_107460 : A -> B) (_107461 : A -> B) (_107462 : P) : (term623 A B P p z' _107460 _107461 _107462) = (term628 A B P p z' _107460 _107461 _107462).
Proof. exact (MK_COMB (@lem8115216 A B P p _107460 _107462) (@lem8115229 A B P p z' _107460 _107461 _107462)). Qed.
Lemma lem8115231 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_107460 : A -> B) (_107461 : A -> B) (_107462 : P) : (term622 A B P p z' _107460 _107461 _107462) = (term628 A B P p z' _107460 _107461 _107462).
Proof. exact (TRANS (@lem8115211 A B P p z' _107460 _107461 _107462) (@lem8115230 A B P p z' _107460 _107461 _107462)). Qed.
Lemma lem8115232 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8115233 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_107460 : A -> B) (_107461 : A -> B) (_107462 : P) : (term629 A B P p z' _107460 _107461 _107462) = (term630 A B P p z' _107460 _107461 _107462).
Proof. exact (MK_COMB (@lem8115232) (@lem8115231 A B P p z' _107460 _107461 _107462)). Qed.
Lemma lem8115234 {A B C P : Type'} (_107460 : A -> B) (y : type564 A B C P) (_107461 : A -> B) (_107462 : P) : ((term430 A B C P y _107460 _107462) = (term430 A B C P y _107461 _107462)) = ((term430 A B C P y _107460 _107462) = (term430 A B C P y _107461 _107462)).
Proof. exact (eq_refl ((term430 A B C P y _107460 _107462) = (term430 A B C P y _107461 _107462))). Qed.
Lemma lem8115235 {A B C P : Type'} (p : type560 A B P) (z' : type518 A B P) (_107460 : A -> B) (y : type564 A B C P) (_107461 : A -> B) (_107462 : P) : (term621 A B C P p z' _107460 y _107461 _107462) = (term631 A B C P p z' _107460 y _107461 _107462).
Proof. exact (MK_COMB (@lem8115233 A B P p z' _107460 _107461 _107462) (@lem8115234 A B C P _107460 y _107461 _107462)). Qed.
Lemma lem8115236 {A B C P : Type'} (p : type560 A B P) (z' : type518 A B P) (_107460 : A -> B) (y : type564 A B C P) (_107461 : A -> B) (_107462 : P) : (term620 A B C P y p z' _107460 _107461 _107462) = (term631 A B C P p z' _107460 y _107461 _107462).
Proof. exact (TRANS (@lem8115208 A B C P p z' _107460 y _107461 _107462) (@lem8115235 A B C P p z' _107460 y _107461 _107462)). Qed.
Lemma lem8115238 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term557 A B C P f y g' a) (h2 : term403 A B C D P z g p lt2 s z' y) (h3 : term35 A B P p lt2 s a f g') : term627 A B P p z' f g' a.
Proof. exact (conj (@lem8114655 A B P p lt2 s a f g' h3) (@lem8114999 A B C D P z g z' y p lt2 s a f g' h1 h2 h3)). Qed.
Lemma lem8115239 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term557 A B C P f y g' a) (h2 : term403 A B C D P z g p lt2 s z' y) (h3 : term35 A B P p lt2 s a f g') : term628 A B P p z' f g' a.
Proof. exact (conj (@lem8114648 A B P p lt2 s a f g' h3) (@lem8115238 A B C D P z g z' y p lt2 s a f g' h1 h2 h3)). Qed.
Lemma lem8115241 {A B C D P : Type'} (_107460 : A -> B) (_107461 : A -> B) (_107462 : P) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term631 A B C P p z' _107460 y _107461 _107462.
Proof. exact (EQ_MP (@lem8115236 A B C P p z' _107460 y _107461 _107462) (@lem8115205 A B C D P _107460 _107461 _107462 z g p lt2 s z' y h1)). Qed.
Lemma lem8115242 {A B C D P : Type'} (_107460 : A -> B) (_107461 : A -> B) (_107462 : P) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term631 A B C P p z' _107460 y _107461 _107462.
Proof. exact (@lem8115241 A B C D P _107460 _107461 _107462 z g p lt2 s z' y h1). Qed.
Lemma lem8115243 {A B C D P : Type'} (f : A -> B) (g' : A -> B) (a : P) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term631 A B C P p z' f y g' a.
Proof. exact (@lem8115242 A B C D P f g' a z g p lt2 s z' y h1). Qed.
Lemma lem8115246 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term557 A B C P f y g' a) (h2 : term403 A B C D P z g p lt2 s z' y) (h3 : term35 A B P p lt2 s a f g') : (term430 A B C P y f a) = (term430 A B C P y g' a).
Proof. exact (@lem8115243 A B C D P f g' a z g p lt2 s z' y h2 (@lem8115239 A B C D P z g z' y p lt2 s a f g' h1 h2 h3)). Qed.
Lemma lem8115247 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term403 A B C D P z g p lt2 s z' y) (h2 : term35 A B P p lt2 s a f g') : term632 A B C P f y g' a.
Proof. exact (fun h0 : term557 A B C P f y g' a => @lem8115246 A B C D P z g z' y p lt2 s a f g' h0 h1 h2). Qed.
Lemma lem8115249 (p : Prop) : (term556 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8115250 {A B C P : Type'} (f : A -> B) (y : type564 A B C P) (g' : A -> B) (a : P) : (term632 A B C P f y g' a) = ((term430 A B C P y f a) = (term430 A B C P y g' a)).
Proof. exact (@lem8115249 ((term430 A B C P y f a) = (term430 A B C P y g' a))). Qed.
Lemma lem8115251 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term403 A B C D P z g p lt2 s z' y) (h2 : term35 A B P p lt2 s a f g') : (term430 A B C P y f a) = (term430 A B C P y g' a).
Proof. exact (EQ_MP (@lem8115250 A B C P f y g' a) (@lem8115247 A B C D P z g z' y p lt2 s a f g' h1 h2)). Qed.
Lemma lem8115253 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term426 A B P p g' a.
Proof. exact (proj1 (@lem8114159 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8115254 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term555 A B P p g' a.
Proof. exact (fun h0 : term463 A B P p g' a => @lem8115253 A B P p lt2 s a f g' h1). Qed.
Lemma lem8115256 (p : Prop) : (term556 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8115257 {A B P : Type'} (p : type560 A B P) (g' : A -> B) (a : P) : (term555 A B P p g' a) = (term426 A B P p g' a).
Proof. exact (@lem8115256 (term426 A B P p g' a)). Qed.
Lemma lem8115258 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term426 A B P p g' a.
Proof. exact (EQ_MP (@lem8115257 A B P p g' a) (@lem8115254 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8115260 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term426 A B P p f a.
Proof. exact (proj1 (@lem8113630 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8115261 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term555 A B P p f a.
Proof. exact (fun h0 : term463 A B P p f a => @lem8115260 A B P p lt2 s a f g' h1). Qed.
Lemma lem8115263 (p : Prop) : (term556 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8115264 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term555 A B P p f a) = (term426 A B P p f a).
Proof. exact (@lem8115263 (term426 A B P p f a)). Qed.
Lemma lem8115265 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term426 A B P p f a.
Proof. exact (EQ_MP (@lem8115264 A B P p f a) (@lem8115261 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8115267 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term426 A B P p g' a.
Proof. exact (proj1 (@lem8114159 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8115268 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term555 A B P p g' a.
Proof. exact (fun h0 : term463 A B P p g' a => @lem8115267 A B P p lt2 s a f g' h1). Qed.
Lemma lem8115270 (p : Prop) : (term556 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8115271 {A B P : Type'} (p : type560 A B P) (g' : A -> B) (a : P) : (term555 A B P p g' a) = (term426 A B P p g' a).
Proof. exact (@lem8115270 (term426 A B P p g' a)). Qed.
Lemma lem8115272 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term426 A B P p g' a.
Proof. exact (EQ_MP (@lem8115271 A B P p g' a) (@lem8115268 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8115274 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term426 A B P p f a.
Proof. exact (proj1 (@lem8113630 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8115275 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term555 A B P p f a.
Proof. exact (fun h0 : term463 A B P p f a => @lem8115274 A B P p lt2 s a f g' h1). Qed.
Lemma lem8115277 (p : Prop) : (term556 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8115278 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term555 A B P p f a) = (term426 A B P p f a).
Proof. exact (@lem8115277 (term426 A B P p f a)). Qed.
Lemma lem8115279 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term426 A B P p f a.
Proof. exact (EQ_MP (@lem8115278 A B P p f a) (@lem8115275 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8115282 {A B C D P : Type'} (g' : A -> B) (g : type565 A B C D P) (f : A -> B) (a : P) (h1 : term633 A B C D P g' g f a) : term633 A B C D P g' g f a.
Proof. exact (h1). Qed.
Lemma lem8115283 {A B C D P : Type'} (g' : A -> B) (g : type565 A B C D P) (f : A -> B) (a : P) (h1 : term633 A B C D P g' g f a) : term634 A B C D P g' g f a.
Proof. exact (fun h0 : (term432 A B C D P g g' a) = (term432 A B C D P g f a) => @lem8115282 A B C D P g' g f a h1). Qed.
Lemma lem8115285 (p : Prop) : (term559 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem8115286 {A B C D P : Type'} (g' : A -> B) (g : type565 A B C D P) (f : A -> B) (a : P) : (term634 A B C D P g' g f a) = (term633 A B C D P g' g f a).
Proof. exact (@lem8115285 ((term432 A B C D P g g' a) = (term432 A B C D P g f a))). Qed.
Lemma lem8115287 {A B C D P : Type'} (g' : A -> B) (g : type565 A B C D P) (f : A -> B) (a : P) (h1 : term633 A B C D P g' g f a) : term633 A B C D P g' g f a.
Proof. exact (EQ_MP (@lem8115286 A B C D P g' g f a) (@lem8115283 A B C D P g' g f a h1)). Qed.
Lemma lem8115303 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8115304 {A B C D P : Type'} (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (p : type560 A B P) (_107457 : A -> B) (g : type565 A B C D P) (_107458 : A -> B) (_107459 : P) : (term542 A B C D P p lt2 z s _107457 g _107458 _107459) = (term635 A B C D P lt2 z s p _107457 g _107458 _107459).
Proof. exact (@lem8115303 (term458 A B P lt2 z _107457 _107458 s _107459) (term463 A B P p _107458 _107459) ((term432 A B C D P g _107457 _107459) = (term432 A B C D P g _107458 _107459))). Qed.
Lemma lem8115318 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8115319 {A B C D P : Type'} (_107457 : A -> B) (g : type565 A B C D P) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term636 A B C D P p _107457 g _107458 _107459) = (term637 A B C D P _107457 g p _107458 _107459).
Proof. exact (@lem8115318 ((term432 A B C D P g _107457 _107459) = (term432 A B C D P g _107458 _107459)) (term463 A B P p _107458 _107459)). Qed.
Lemma lem8115327 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (_107457 : A -> B) (_107458 : A -> B) (s : P -> A) (_107459 : P) : (term563 A B P lt2 z _107457 _107458 s _107459) = (term563 A B P lt2 z _107457 _107458 s _107459).
Proof. exact (eq_refl (term563 A B P lt2 z _107457 _107458 s _107459)). Qed.
Lemma lem8115328 {A B C D P : Type'} (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107457 : A -> B) (g : type565 A B C D P) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term635 A B C D P lt2 z s p _107457 g _107458 _107459) = (term638 A B C D P lt2 z s _107457 g p _107458 _107459).
Proof. exact (MK_COMB (@lem8115327 A B P lt2 z _107457 _107458 s _107459) (@lem8115319 A B C D P _107457 g p _107458 _107459)). Qed.
Lemma lem8115332 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8115333 {A B C D P : Type'} (g : type565 A B C D P) (lt2 : type1402 A) (z : type518 A B P) (_107457 : A -> B) (s : P -> A) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term638 A B C D P lt2 z s _107457 g p _107458 _107459) = (term639 A B C D P g lt2 z _107457 s p _107458 _107459).
Proof. exact (@lem8115332 ((term432 A B C D P g _107457 _107459) = (term432 A B C D P g _107458 _107459)) (term458 A B P lt2 z _107457 _107458 s _107459) (term463 A B P p _107458 _107459)). Qed.
Lemma lem8115351 {A B C D P : Type'} (g : type565 A B C D P) (lt2 : type1402 A) (z : type518 A B P) (_107457 : A -> B) (s : P -> A) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term635 A B C D P lt2 z s p _107457 g _107458 _107459) = (term639 A B C D P g lt2 z _107457 s p _107458 _107459).
Proof. exact (TRANS (@lem8115328 A B C D P lt2 z s _107457 g p _107458 _107459) (@lem8115333 A B C D P g lt2 z _107457 s p _107458 _107459)). Qed.
Lemma lem8115352 {A B C D P : Type'} (g : type565 A B C D P) (lt2 : type1402 A) (z : type518 A B P) (_107457 : A -> B) (s : P -> A) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term542 A B C D P p lt2 z s _107457 g _107458 _107459) = (term639 A B C D P g lt2 z _107457 s p _107458 _107459).
Proof. exact (TRANS (@lem8115304 A B C D P lt2 z s p _107457 g _107458 _107459) (@lem8115351 A B C D P g lt2 z _107457 s p _107458 _107459)). Qed.
Lemma lem8115353 {A B P : Type'} (p : type560 A B P) (_107457 : A -> B) (_107459 : P) : (term464 A B P p _107457 _107459) = (term464 A B P p _107457 _107459).
Proof. exact (eq_refl (term464 A B P p _107457 _107459)). Qed.
Lemma lem8115354 {A B C D P : Type'} (g : type565 A B C D P) (lt2 : type1402 A) (z : type518 A B P) (_107457 : A -> B) (s : P -> A) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term543 A B C D P p lt2 z s _107457 g _107458 _107459) = (term640 A B C D P g lt2 z _107457 s p _107458 _107459).
Proof. exact (MK_COMB (@lem8115353 A B P p _107457 _107459) (@lem8115352 A B C D P g lt2 z _107457 s p _107458 _107459)). Qed.
Lemma lem8115358 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8115359 {A B C D P : Type'} (g : type565 A B C D P) (lt2 : type1402 A) (z : type518 A B P) (_107457 : A -> B) (s : P -> A) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term640 A B C D P g lt2 z _107457 s p _107458 _107459) = (term641 A B C D P g lt2 z _107457 s p _107458 _107459).
Proof. exact (@lem8115358 ((term432 A B C D P g _107457 _107459) = (term432 A B C D P g _107458 _107459)) (term463 A B P p _107457 _107459) (term568 A B P lt2 z _107457 s p _107458 _107459)). Qed.
Lemma lem8115375 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8115376 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107457 : A -> B) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term569 A B P lt2 z _107457 s p _107458 _107459) = (term570 A B P lt2 z s _107457 p _107458 _107459).
Proof. exact (@lem8115375 (term458 A B P lt2 z _107457 _107458 s _107459) (term463 A B P p _107457 _107459) (term463 A B P p _107458 _107459)). Qed.
Lemma lem8115392 {A B C D P : Type'} (_107457 : A -> B) (g : type565 A B C D P) (_107458 : A -> B) (_107459 : P) : (term642 A B C D P _107457 g _107458 _107459) = (term642 A B C D P _107457 g _107458 _107459).
Proof. exact (eq_refl (term642 A B C D P _107457 g _107458 _107459)). Qed.
Lemma lem8115393 {A B C D P : Type'} (g : type565 A B C D P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107457 : A -> B) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term641 A B C D P g lt2 z _107457 s p _107458 _107459) = (term643 A B C D P g lt2 z s _107457 p _107458 _107459).
Proof. exact (MK_COMB (@lem8115392 A B C D P _107457 g _107458 _107459) (@lem8115376 A B P lt2 z s _107457 p _107458 _107459)). Qed.
Lemma lem8115404 {A B C D P : Type'} (g : type565 A B C D P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107457 : A -> B) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term640 A B C D P g lt2 z _107457 s p _107458 _107459) = (term643 A B C D P g lt2 z s _107457 p _107458 _107459).
Proof. exact (TRANS (@lem8115359 A B C D P g lt2 z _107457 s p _107458 _107459) (@lem8115393 A B C D P g lt2 z s _107457 p _107458 _107459)). Qed.
Lemma lem8115405 {A B C D P : Type'} (g : type565 A B C D P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107457 : A -> B) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term543 A B C D P p lt2 z s _107457 g _107458 _107459) = (term643 A B C D P g lt2 z s _107457 p _107458 _107459).
Proof. exact (TRANS (@lem8115354 A B C D P g lt2 z _107457 s p _107458 _107459) (@lem8115404 A B C D P g lt2 z s _107457 p _107458 _107459)). Qed.
Lemma lem8115406 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8115407 {A B C D P : Type'} (g : type565 A B C D P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107457 : A -> B) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term644 A B C D P p lt2 z s _107457 g _107458 _107459) = (term645 A B C D P g lt2 z s _107457 p _107458 _107459).
Proof. exact (MK_COMB (@lem8115406) (@lem8115405 A B C D P g lt2 z s _107457 p _107458 _107459)). Qed.
Lemma lem8115431 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8115432 {A B C D P : Type'} (_107457 : A -> B) (g : type565 A B C D P) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term636 A B C D P p _107457 g _107458 _107459) = (term637 A B C D P _107457 g p _107458 _107459).
Proof. exact (@lem8115431 ((term432 A B C D P g _107457 _107459) = (term432 A B C D P g _107458 _107459)) (term463 A B P p _107458 _107459)). Qed.
Lemma lem8115440 {A B P : Type'} (p : type560 A B P) (_107457 : A -> B) (_107459 : P) : (term464 A B P p _107457 _107459) = (term464 A B P p _107457 _107459).
Proof. exact (eq_refl (term464 A B P p _107457 _107459)). Qed.
Lemma lem8115441 {A B C D P : Type'} (_107457 : A -> B) (g : type565 A B C D P) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term646 A B C D P p _107457 g _107458 _107459) = (term647 A B C D P _107457 g p _107458 _107459).
Proof. exact (MK_COMB (@lem8115440 A B P p _107457 _107459) (@lem8115432 A B C D P _107457 g p _107458 _107459)). Qed.
Lemma lem8115445 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8115446 {A B C D P : Type'} (g : type565 A B C D P) (_107457 : A -> B) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term647 A B C D P _107457 g p _107458 _107459) = (term648 A B C D P g _107457 p _107458 _107459).
Proof. exact (@lem8115445 ((term432 A B C D P g _107457 _107459) = (term432 A B C D P g _107458 _107459)) (term463 A B P p _107457 _107459) (term463 A B P p _107458 _107459)). Qed.
Lemma lem8115464 {A B C D P : Type'} (g : type565 A B C D P) (_107457 : A -> B) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term646 A B C D P p _107457 g _107458 _107459) = (term648 A B C D P g _107457 p _107458 _107459).
Proof. exact (TRANS (@lem8115441 A B C D P _107457 g p _107458 _107459) (@lem8115446 A B C D P g _107457 p _107458 _107459)). Qed.
Lemma lem8115465 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (_107457 : A -> B) (_107458 : A -> B) (s : P -> A) (_107459 : P) : (term563 A B P lt2 z _107457 _107458 s _107459) = (term563 A B P lt2 z _107457 _107458 s _107459).
Proof. exact (eq_refl (term563 A B P lt2 z _107457 _107458 s _107459)). Qed.
Lemma lem8115466 {A B C D P : Type'} (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (g : type565 A B C D P) (_107457 : A -> B) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term649 A B C D P lt2 z s p _107457 g _107458 _107459) = (term650 A B C D P lt2 z s g _107457 p _107458 _107459).
Proof. exact (MK_COMB (@lem8115465 A B P lt2 z _107457 _107458 s _107459) (@lem8115464 A B C D P g _107457 p _107458 _107459)). Qed.
Lemma lem8115470 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8115471 {A B C D P : Type'} (g : type565 A B C D P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107457 : A -> B) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term650 A B C D P lt2 z s g _107457 p _107458 _107459) = (term643 A B C D P g lt2 z s _107457 p _107458 _107459).
Proof. exact (@lem8115470 ((term432 A B C D P g _107457 _107459) = (term432 A B C D P g _107458 _107459)) (term458 A B P lt2 z _107457 _107458 s _107459) (term580 A B P _107457 p _107458 _107459)). Qed.
Lemma lem8115499 {A B C D P : Type'} (g : type565 A B C D P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107457 : A -> B) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term649 A B C D P lt2 z s p _107457 g _107458 _107459) = (term643 A B C D P g lt2 z s _107457 p _107458 _107459).
Proof. exact (TRANS (@lem8115466 A B C D P lt2 z s g _107457 p _107458 _107459) (@lem8115471 A B C D P g lt2 z s _107457 p _107458 _107459)). Qed.
Lemma lem8115500 {A B C D P : Type'} (g : type565 A B C D P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107457 : A -> B) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : ((term543 A B C D P p lt2 z s _107457 g _107458 _107459) = (term649 A B C D P lt2 z s p _107457 g _107458 _107459)) = ((term643 A B C D P g lt2 z s _107457 p _107458 _107459) = (term643 A B C D P g lt2 z s _107457 p _107458 _107459)).
Proof. exact (MK_COMB (@lem8115407 A B C D P g lt2 z s _107457 p _107458 _107459) (@lem8115499 A B C D P g lt2 z s _107457 p _107458 _107459)). Qed.
Lemma lem8115502 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8115503 (x : Prop) : (x = x) = True.
Proof. exact (@lem8115502 Prop x). Qed.
Lemma lem8115504 {A B C D P : Type'} (g : type565 A B C D P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107457 : A -> B) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : ((term643 A B C D P g lt2 z s _107457 p _107458 _107459) = (term643 A B C D P g lt2 z s _107457 p _107458 _107459)) = True.
Proof. exact (@lem8115503 (term643 A B C D P g lt2 z s _107457 p _107458 _107459)). Qed.
Lemma lem8115505 {A B C D P : Type'} (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (p : type560 A B P) (_107457 : A -> B) (g : type565 A B C D P) (_107458 : A -> B) (_107459 : P) : ((term543 A B C D P p lt2 z s _107457 g _107458 _107459) = (term649 A B C D P lt2 z s p _107457 g _107458 _107459)) = True.
Proof. exact (TRANS (@lem8115500 A B C D P g lt2 z s _107457 p _107458 _107459) (@lem8115504 A B C D P g lt2 z s _107457 p _107458 _107459)). Qed.
Lemma lem8115506 {A B C D P : Type'} (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (p : type560 A B P) (_107457 : A -> B) (g : type565 A B C D P) (_107458 : A -> B) (_107459 : P) : True = ((term543 A B C D P p lt2 z s _107457 g _107458 _107459) = (term649 A B C D P lt2 z s p _107457 g _107458 _107459)).
Proof. exact (SYM (@lem8115505 A B C D P lt2 z s p _107457 g _107458 _107459)). Qed.
Lemma lem8115507 {A B C D P : Type'} (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (p : type560 A B P) (_107457 : A -> B) (g : type565 A B C D P) (_107458 : A -> B) (_107459 : P) : (term543 A B C D P p lt2 z s _107457 g _107458 _107459) = (term649 A B C D P lt2 z s p _107457 g _107458 _107459).
Proof. exact (EQ_MP (@lem8115506 A B C D P lt2 z s p _107457 g _107458 _107459) (@lem0)). Qed.
Lemma lem8115508 {A B C D P : Type'} (_107457 : A -> B) (_107458 : A -> B) (_107459 : P) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term649 A B C D P lt2 z s p _107457 g _107458 _107459.
Proof. exact (EQ_MP (@lem8115507 A B C D P lt2 z s p _107457 g _107458 _107459) (@lem8114384 A B C D P _107457 _107458 _107459 z g p lt2 s z' y h1)). Qed.
Lemma lem8115510 (b : Prop) (a : Prop) : (a \/ b) = (term581 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8115511 {A B C D P : Type'} (p : type560 A B P) (g : type565 A B C D P) (lt2 : type1402 A) (z : type518 A B P) (_107457 : A -> B) (_107458 : A -> B) (s : P -> A) (_107459 : P) : (term649 A B C D P lt2 z s p _107457 g _107458 _107459) = (term651 A B C D P p g lt2 z _107457 _107458 s _107459).
Proof. exact (@lem8115510 (term646 A B C D P p _107457 g _107458 _107459) (term458 A B P lt2 z _107457 _107458 s _107459)). Qed.
Lemma lem8115513 (a : Prop) (b : Prop) : (term583 a b) = (term584 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8115514 {A B C D P : Type'} (p : type560 A B P) (_107457 : A -> B) (g : type565 A B C D P) (_107458 : A -> B) (_107459 : P) : (term652 A B C D P p _107457 g _107458 _107459) = (term653 A B C D P p _107457 g _107458 _107459).
Proof. exact (@lem8115513 (term463 A B P p _107457 _107459) (term636 A B C D P p _107457 g _107458 _107459)). Qed.
Lemma lem8115516 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8115517 {A B P : Type'} (p : type560 A B P) (_107457 : A -> B) (_107459 : P) : (term587 A B P p _107457 _107459) = (term426 A B P p _107457 _107459).
Proof. exact (@lem8115516 (term426 A B P p _107457 _107459)). Qed.
Lemma lem8115518 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8115519 {A B P : Type'} (p : type560 A B P) (_107457 : A -> B) (_107459 : P) : (term588 A B P p _107457 _107459) = (term427 A B P p _107457 _107459).
Proof. exact (MK_COMB (@lem8115518) (@lem8115517 A B P p _107457 _107459)). Qed.
Lemma lem8115521 (a : Prop) (b : Prop) : (term583 a b) = (term584 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8115522 {A B C D P : Type'} (p : type560 A B P) (_107457 : A -> B) (g : type565 A B C D P) (_107458 : A -> B) (_107459 : P) : (term654 A B C D P p _107457 g _107458 _107459) = (term655 A B C D P p _107457 g _107458 _107459).
Proof. exact (@lem8115521 (term463 A B P p _107458 _107459) ((term432 A B C D P g _107457 _107459) = (term432 A B C D P g _107458 _107459))). Qed.
Lemma lem8115524 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8115525 {A B P : Type'} (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term587 A B P p _107458 _107459) = (term426 A B P p _107458 _107459).
Proof. exact (@lem8115524 (term426 A B P p _107458 _107459)). Qed.
Lemma lem8115526 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8115527 {A B P : Type'} (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term588 A B P p _107458 _107459) = (term427 A B P p _107458 _107459).
Proof. exact (MK_COMB (@lem8115526) (@lem8115525 A B P p _107458 _107459)). Qed.
Lemma lem8115528 {A B C D P : Type'} (_107457 : A -> B) (g : type565 A B C D P) (_107458 : A -> B) (_107459 : P) : (term633 A B C D P _107457 g _107458 _107459) = (term633 A B C D P _107457 g _107458 _107459).
Proof. exact (eq_refl (term633 A B C D P _107457 g _107458 _107459)). Qed.
Lemma lem8115529 {A B C D P : Type'} (p : type560 A B P) (_107457 : A -> B) (g : type565 A B C D P) (_107458 : A -> B) (_107459 : P) : (term655 A B C D P p _107457 g _107458 _107459) = (term656 A B C D P p _107457 g _107458 _107459).
Proof. exact (MK_COMB (@lem8115527 A B P p _107458 _107459) (@lem8115528 A B C D P _107457 g _107458 _107459)). Qed.
Lemma lem8115530 {A B C D P : Type'} (p : type560 A B P) (_107457 : A -> B) (g : type565 A B C D P) (_107458 : A -> B) (_107459 : P) : (term654 A B C D P p _107457 g _107458 _107459) = (term656 A B C D P p _107457 g _107458 _107459).
Proof. exact (TRANS (@lem8115522 A B C D P p _107457 g _107458 _107459) (@lem8115529 A B C D P p _107457 g _107458 _107459)). Qed.
Lemma lem8115531 {A B C D P : Type'} (p : type560 A B P) (_107457 : A -> B) (g : type565 A B C D P) (_107458 : A -> B) (_107459 : P) : (term653 A B C D P p _107457 g _107458 _107459) = (term657 A B C D P p _107457 g _107458 _107459).
Proof. exact (MK_COMB (@lem8115519 A B P p _107457 _107459) (@lem8115530 A B C D P p _107457 g _107458 _107459)). Qed.
Lemma lem8115532 {A B C D P : Type'} (p : type560 A B P) (_107457 : A -> B) (g : type565 A B C D P) (_107458 : A -> B) (_107459 : P) : (term652 A B C D P p _107457 g _107458 _107459) = (term657 A B C D P p _107457 g _107458 _107459).
Proof. exact (TRANS (@lem8115514 A B C D P p _107457 g _107458 _107459) (@lem8115531 A B C D P p _107457 g _107458 _107459)). Qed.
Lemma lem8115533 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8115534 {A B C D P : Type'} (p : type560 A B P) (_107457 : A -> B) (g : type565 A B C D P) (_107458 : A -> B) (_107459 : P) : (term658 A B C D P p _107457 g _107458 _107459) = (term659 A B C D P p _107457 g _107458 _107459).
Proof. exact (MK_COMB (@lem8115533) (@lem8115532 A B C D P p _107457 g _107458 _107459)). Qed.
Lemma lem8115535 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (_107457 : A -> B) (_107458 : A -> B) (s : P -> A) (_107459 : P) : (term458 A B P lt2 z _107457 _107458 s _107459) = (term458 A B P lt2 z _107457 _107458 s _107459).
Proof. exact (eq_refl (term458 A B P lt2 z _107457 _107458 s _107459)). Qed.
Lemma lem8115536 {A B C D P : Type'} (p : type560 A B P) (g : type565 A B C D P) (lt2 : type1402 A) (z : type518 A B P) (_107457 : A -> B) (_107458 : A -> B) (s : P -> A) (_107459 : P) : (term651 A B C D P p g lt2 z _107457 _107458 s _107459) = (term660 A B C D P p g lt2 z _107457 _107458 s _107459).
Proof. exact (MK_COMB (@lem8115534 A B C D P p _107457 g _107458 _107459) (@lem8115535 A B P lt2 z _107457 _107458 s _107459)). Qed.
Lemma lem8115537 {A B C D P : Type'} (p : type560 A B P) (g : type565 A B C D P) (lt2 : type1402 A) (z : type518 A B P) (_107457 : A -> B) (_107458 : A -> B) (s : P -> A) (_107459 : P) : (term649 A B C D P lt2 z s p _107457 g _107458 _107459) = (term660 A B C D P p g lt2 z _107457 _107458 s _107459).
Proof. exact (TRANS (@lem8115511 A B C D P p g lt2 z _107457 _107458 s _107459) (@lem8115536 A B C D P p g lt2 z _107457 _107458 s _107459)). Qed.
Lemma lem8115539 {A B C D P : Type'} (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term633 A B C D P g' g f a) (h2 : term35 A B P p lt2 s a f g') : term656 A B C D P p g' g f a.
Proof. exact (conj (@lem8115279 A B P p lt2 s a f g' h2) (@lem8115287 A B C D P g' g f a h1)). Qed.
Lemma lem8115540 {A B C D P : Type'} (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term633 A B C D P g' g f a) (h2 : term35 A B P p lt2 s a f g') : term657 A B C D P p g' g f a.
Proof. exact (conj (@lem8115272 A B P p lt2 s a f g' h2) (@lem8115539 A B C D P g p lt2 s a f g' h1 h2)). Qed.
Lemma lem8115542 {A B C D P : Type'} (_107457 : A -> B) (_107458 : A -> B) (_107459 : P) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term660 A B C D P p g lt2 z _107457 _107458 s _107459.
Proof. exact (EQ_MP (@lem8115537 A B C D P p g lt2 z _107457 _107458 s _107459) (@lem8115508 A B C D P _107457 _107458 _107459 z g p lt2 s z' y h1)). Qed.
Lemma lem8115543 {A B C D P : Type'} (_107457 : A -> B) (_107458 : A -> B) (_107459 : P) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term660 A B C D P p g lt2 z _107457 _107458 s _107459.
Proof. exact (@lem8115542 A B C D P _107457 _107458 _107459 z g p lt2 s z' y h1). Qed.
Lemma lem8115544 {A B C D P : Type'} (g' : A -> B) (f : A -> B) (a : P) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term660 A B C D P p g lt2 z g' f s a.
Proof. exact (@lem8115543 A B C D P g' f a z g p lt2 s z' y h1). Qed.
Lemma lem8115547 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term633 A B C D P g' g f a) (h2 : term403 A B C D P z g p lt2 s z' y) (h3 : term35 A B P p lt2 s a f g') : term458 A B P lt2 z g' f s a.
Proof. exact (@lem8115544 A B C D P g' f a z g p lt2 s z' y h2 (@lem8115540 A B C D P g p lt2 s a f g' h1 h3)). Qed.
Lemma lem8115548 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term633 A B C D P g' g f a) (h2 : term403 A B C D P z g p lt2 s z' y) (h3 : term35 A B P p lt2 s a f g') : term596 A B P lt2 z g' f s a.
Proof. exact (fun h0 : term597 A B P lt2 z g' f s a => @lem8115547 A B C D P z g z' y p lt2 s a f g' h1 h2 h3). Qed.
Lemma lem8115550 (p : Prop) : (term556 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8115551 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (g' : A -> B) (f : A -> B) (s : P -> A) (a : P) : (term596 A B P lt2 z g' f s a) = (term458 A B P lt2 z g' f s a).
Proof. exact (@lem8115550 (term458 A B P lt2 z g' f s a)). Qed.
Lemma lem8115552 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term633 A B C D P g' g f a) (h2 : term403 A B C D P z g p lt2 s z' y) (h3 : term35 A B P p lt2 s a f g') : term458 A B P lt2 z g' f s a.
Proof. exact (EQ_MP (@lem8115551 A B P lt2 z g' f s a) (@lem8115548 A B C D P z g z' y p lt2 s a f g' h1 h2 h3)). Qed.
Lemma lem8115554 {A B P : Type'} (_107463 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term605 A B P lt2 s a f g' _107463.
Proof. exact (EQ_MP (@lem8114986 A B P lt2 s a f g' _107463) (@lem8114975 A B P _107463 p lt2 s a f g' h1)). Qed.
Lemma lem8115555 {A B P : Type'} (_107463 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term605 A B P lt2 s a f g' _107463.
Proof. exact (@lem8115554 A B P _107463 p lt2 s a f g' h1). Qed.
Lemma lem8115556 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term35 A B P p lt2 s a f g') : term661 A B P lt2 s z g' f a.
Proof. exact (@lem8115555 A B P (term441 A B P z g' f a) p lt2 s a f g' h1). Qed.
Lemma lem8115559 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term633 A B C D P g' g f a) (h2 : term403 A B C D P z g p lt2 s z' y) (h3 : term35 A B P p lt2 s a f g') : (term447 A B P z g' f a) = (term444 A B P z g' f a).
Proof. exact (@lem8115556 A B P z p lt2 s a f g' h3 (@lem8115552 A B C D P z g z' y p lt2 s a f g' h1 h2 h3)). Qed.
Lemma lem8115560 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term633 A B C D P g' g f a) (h2 : term403 A B C D P z g p lt2 s z' y) (h3 : term35 A B P p lt2 s a f g') : term662 A B P z g' f a.
Proof. exact (fun h0 : term663 A B P z g' f a => @lem8115559 A B C D P z g z' y p lt2 s a f g' h1 h2 h3). Qed.
Lemma lem8115562 (p : Prop) : (term556 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8115563 {A B P : Type'} (z : type518 A B P) (g' : A -> B) (f : A -> B) (a : P) : (term662 A B P z g' f a) = ((term447 A B P z g' f a) = (term444 A B P z g' f a)).
Proof. exact (@lem8115562 ((term447 A B P z g' f a) = (term444 A B P z g' f a))). Qed.
Lemma lem8115564 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term633 A B C D P g' g f a) (h2 : term403 A B C D P z g p lt2 s z' y) (h3 : term35 A B P p lt2 s a f g') : (term447 A B P z g' f a) = (term444 A B P z g' f a).
Proof. exact (EQ_MP (@lem8115563 A B P z g' f a) (@lem8115560 A B C D P z g z' y p lt2 s a f g' h1 h2 h3)). Qed.
Lemma lem8115566 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem8115567 {B : Type'} (x : B) : x = x.
Proof. exact (@lem8115566 B x). Qed.
Lemma lem8115568 {A B P : Type'} (z : type518 A B P) (g' : A -> B) (f : A -> B) (a : P) : (term447 A B P z g' f a) = (term447 A B P z g' f a).
Proof. exact (@lem8115567 B (term447 A B P z g' f a)). Qed.
Lemma lem8115569 {A B P : Type'} (z : type518 A B P) (g' : A -> B) (f : A -> B) (a : P) : term664 A B P z g' f a.
Proof. exact (fun h0 : term665 A B P z g' f a => @lem8115568 A B P z g' f a). Qed.
Lemma lem8115571 (p : Prop) : (term556 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8115572 {A B P : Type'} (z : type518 A B P) (g' : A -> B) (f : A -> B) (a : P) : (term664 A B P z g' f a) = ((term447 A B P z g' f a) = (term447 A B P z g' f a)).
Proof. exact (@lem8115571 ((term447 A B P z g' f a) = (term447 A B P z g' f a))). Qed.
Lemma lem8115573 {A B P : Type'} (z : type518 A B P) (g' : A -> B) (f : A -> B) (a : P) : (term447 A B P z g' f a) = (term447 A B P z g' f a).
Proof. exact (EQ_MP (@lem8115572 A B P z g' f a) (@lem8115569 A B P z g' f a)). Qed.
Lemma lem8115591 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8115592 {B : Type'} (y : B) (x : B) (z : B) : (term666 B x y z) = (term667 B y x z).
Proof. exact (@lem8115591 (y = z) (term668 B x z)). Qed.
Lemma lem8115602 {B : Type'} (x : B) (y : B) : (term669 B x y) = (term669 B x y).
Proof. exact (eq_refl (term669 B x y)). Qed.
Lemma lem8115603 {B : Type'} (y : B) (x : B) (z : B) : (term554 B x y z) = (term670 B y x z).
Proof. exact (MK_COMB (@lem8115602 B x y) (@lem8115592 B y x z)). Qed.
Lemma lem8115607 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8115608 {B : Type'} (y : B) (x : B) (z : B) : (term670 B y x z) = (term671 B y x z).
Proof. exact (@lem8115607 (y = z) (term668 B x y) (term668 B x z)). Qed.
Lemma lem8115630 {B : Type'} (y : B) (x : B) (z : B) : (term554 B x y z) = (term671 B y x z).
Proof. exact (TRANS (@lem8115603 B y x z) (@lem8115608 B y x z)). Qed.
Lemma lem8115631 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8115632 {B : Type'} (y : B) (x : B) (z : B) : (term672 B x y z) = (term673 B y x z).
Proof. exact (MK_COMB (@lem8115631) (@lem8115630 B y x z)). Qed.
Lemma lem8115654 {B : Type'} (y : B) (x : B) (z : B) : (term671 B y x z) = (term671 B y x z).
Proof. exact (eq_refl (term671 B y x z)). Qed.
Lemma lem8115655 {B : Type'} (y : B) (x : B) (z : B) : ((term554 B x y z) = (term671 B y x z)) = ((term671 B y x z) = (term671 B y x z)).
Proof. exact (MK_COMB (@lem8115632 B y x z) (@lem8115654 B y x z)). Qed.
Lemma lem8115657 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8115658 (x : Prop) : (x = x) = True.
Proof. exact (@lem8115657 Prop x). Qed.
Lemma lem8115659 {B : Type'} (y : B) (x : B) (z : B) : ((term671 B y x z) = (term671 B y x z)) = True.
Proof. exact (@lem8115658 (term671 B y x z)). Qed.
Lemma lem8115660 {B : Type'} (y : B) (x : B) (z : B) : ((term554 B x y z) = (term671 B y x z)) = True.
Proof. exact (TRANS (@lem8115655 B y x z) (@lem8115659 B y x z)). Qed.
Lemma lem8115661 {B : Type'} (y : B) (x : B) (z : B) : True = ((term554 B x y z) = (term671 B y x z)).
Proof. exact (SYM (@lem8115660 B y x z)). Qed.
Lemma lem8115662 {B : Type'} (y : B) (x : B) (z : B) : (term554 B x y z) = (term671 B y x z).
Proof. exact (EQ_MP (@lem8115661 B y x z) (@lem0)). Qed.
Lemma lem8115663 {B : Type'} (y : B) (x : B) (z : B) : term671 B y x z.
Proof. exact (EQ_MP (@lem8115662 B y x z) (@lem8114629 B x y z)). Qed.
Lemma lem8115665 (b : Prop) (a : Prop) : (a \/ b) = (term581 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8115666 {B : Type'} (x : B) (y : B) (z : B) : (term671 B y x z) = (term674 B x y z).
Proof. exact (@lem8115665 (term675 B y x z) (y = z)). Qed.
Lemma lem8115668 (a : Prop) (b : Prop) : (term583 a b) = (term584 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8115669 {B : Type'} (y : B) (x : B) (z : B) : (term676 B y x z) = (term677 B y x z).
Proof. exact (@lem8115668 (term668 B x y) (term668 B x z)). Qed.
Lemma lem8115671 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8115672 {B : Type'} (x : B) (y : B) : (term678 B x y) = (x = y).
Proof. exact (@lem8115671 (x = y)). Qed.
Lemma lem8115673 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8115674 {B : Type'} (x : B) (y : B) : (term679 B x y) = (term680 B x y).
Proof. exact (MK_COMB (@lem8115673) (@lem8115672 B x y)). Qed.
Lemma lem8115676 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8115677 {B : Type'} (x : B) (z : B) : (term678 B x z) = (x = z).
Proof. exact (@lem8115676 (x = z)). Qed.
Lemma lem8115678 {B : Type'} (y : B) (x : B) (z : B) : (term677 B y x z) = (term681 B y x z).
Proof. exact (MK_COMB (@lem8115674 B x y) (@lem8115677 B x z)). Qed.
Lemma lem8115679 {B : Type'} (y : B) (x : B) (z : B) : (term676 B y x z) = (term681 B y x z).
Proof. exact (TRANS (@lem8115669 B y x z) (@lem8115678 B y x z)). Qed.
Lemma lem8115680 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8115681 {B : Type'} (y : B) (x : B) (z : B) : (term682 B y x z) = (term683 B y x z).
Proof. exact (MK_COMB (@lem8115680) (@lem8115679 B y x z)). Qed.
Lemma lem8115682 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem8115683 {B : Type'} (x : B) (y : B) (z : B) : (term674 B x y z) = (term684 B x y z).
Proof. exact (MK_COMB (@lem8115681 B y x z) (@lem8115682 B y z)). Qed.
Lemma lem8115684 {B : Type'} (x : B) (y : B) (z : B) : (term671 B y x z) = (term684 B x y z).
Proof. exact (TRANS (@lem8115666 B x y z) (@lem8115683 B x y z)). Qed.
Lemma lem8115686 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term633 A B C D P g' g f a) (h2 : term403 A B C D P z g p lt2 s z' y) (h3 : term35 A B P p lt2 s a f g') : term685 A B P z g' f a.
Proof. exact (conj (@lem8115564 A B C D P z g z' y p lt2 s a f g' h1 h2 h3) (@lem8115573 A B P z g' f a)). Qed.
Lemma lem8115688 {B : Type'} (x : B) (y : B) (z : B) : term684 B x y z.
Proof. exact (EQ_MP (@lem8115684 B x y z) (@lem8115663 B y x z)). Qed.
Lemma lem8115689 {B : Type'} (x : B) (y : B) (z : B) : term684 B x y z.
Proof. exact (@lem8115688 B x y z). Qed.
Lemma lem8115690 {A B P : Type'} (z : type518 A B P) (g' : A -> B) (f : A -> B) (a : P) : term686 A B P z g' f a.
Proof. exact (@lem8115689 B (term447 A B P z g' f a) (term444 A B P z g' f a) (term447 A B P z g' f a)). Qed.
Lemma lem8115693 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term633 A B C D P g' g f a) (h2 : term403 A B C D P z g p lt2 s z' y) (h3 : term35 A B P p lt2 s a f g') : (term444 A B P z g' f a) = (term447 A B P z g' f a).
Proof. exact (@lem8115690 A B P z g' f a (@lem8115686 A B C D P z g z' y p lt2 s a f g' h1 h2 h3)). Qed.
Lemma lem8115694 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term633 A B C D P g' g f a) (h2 : term403 A B C D P z g p lt2 s z' y) (h3 : term35 A B P p lt2 s a f g') : term607 A B P z g' f a.
Proof. exact (fun h0 : term451 A B P z g' f a => @lem8115693 A B C D P z g z' y p lt2 s a f g' h1 h2 h3). Qed.
Lemma lem8115696 (p : Prop) : (term556 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8115697 {A B P : Type'} (z : type518 A B P) (g' : A -> B) (f : A -> B) (a : P) : (term607 A B P z g' f a) = ((term444 A B P z g' f a) = (term447 A B P z g' f a)).
Proof. exact (@lem8115696 ((term444 A B P z g' f a) = (term447 A B P z g' f a))). Qed.
Lemma lem8115698 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term633 A B C D P g' g f a) (h2 : term403 A B C D P z g p lt2 s z' y) (h3 : term35 A B P p lt2 s a f g') : (term444 A B P z g' f a) = (term447 A B P z g' f a).
Proof. exact (EQ_MP (@lem8115697 A B P z g' f a) (@lem8115694 A B C D P z g z' y p lt2 s a f g' h1 h2 h3)). Qed.
Lemma lem8115714 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8115715 {A B C D P : Type'} (z : type518 A B P) (p : type560 A B P) (_107457 : A -> B) (g : type565 A B C D P) (_107458 : A -> B) (_107459 : P) : (term546 A B C D P p z _107457 g _107458 _107459) = (term687 A B C D P z p _107457 g _107458 _107459).
Proof. exact (@lem8115714 (term451 A B P z _107457 _107458 _107459) (term463 A B P p _107458 _107459) ((term432 A B C D P g _107457 _107459) = (term432 A B C D P g _107458 _107459))). Qed.
Lemma lem8115731 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8115732 {A B C D P : Type'} (_107457 : A -> B) (g : type565 A B C D P) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term636 A B C D P p _107457 g _107458 _107459) = (term637 A B C D P _107457 g p _107458 _107459).
Proof. exact (@lem8115731 ((term432 A B C D P g _107457 _107459) = (term432 A B C D P g _107458 _107459)) (term463 A B P p _107458 _107459)). Qed.
Lemma lem8115740 {A B P : Type'} (z : type518 A B P) (_107457 : A -> B) (_107458 : A -> B) (_107459 : P) : (term609 A B P z _107457 _107458 _107459) = (term609 A B P z _107457 _107458 _107459).
Proof. exact (eq_refl (term609 A B P z _107457 _107458 _107459)). Qed.
Lemma lem8115741 {A B C D P : Type'} (z : type518 A B P) (_107457 : A -> B) (g : type565 A B C D P) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term687 A B C D P z p _107457 g _107458 _107459) = (term688 A B C D P z _107457 g p _107458 _107459).
Proof. exact (MK_COMB (@lem8115740 A B P z _107457 _107458 _107459) (@lem8115732 A B C D P _107457 g p _107458 _107459)). Qed.
Lemma lem8115745 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8115746 {A B C D P : Type'} (g : type565 A B C D P) (z : type518 A B P) (_107457 : A -> B) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term688 A B C D P z _107457 g p _107458 _107459) = (term689 A B C D P g z _107457 p _107458 _107459).
Proof. exact (@lem8115745 ((term432 A B C D P g _107457 _107459) = (term432 A B C D P g _107458 _107459)) (term451 A B P z _107457 _107458 _107459) (term463 A B P p _107458 _107459)). Qed.
Lemma lem8115766 {A B C D P : Type'} (g : type565 A B C D P) (z : type518 A B P) (_107457 : A -> B) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term687 A B C D P z p _107457 g _107458 _107459) = (term689 A B C D P g z _107457 p _107458 _107459).
Proof. exact (TRANS (@lem8115741 A B C D P z _107457 g p _107458 _107459) (@lem8115746 A B C D P g z _107457 p _107458 _107459)). Qed.
Lemma lem8115767 {A B C D P : Type'} (g : type565 A B C D P) (z : type518 A B P) (_107457 : A -> B) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term546 A B C D P p z _107457 g _107458 _107459) = (term689 A B C D P g z _107457 p _107458 _107459).
Proof. exact (TRANS (@lem8115715 A B C D P z p _107457 g _107458 _107459) (@lem8115766 A B C D P g z _107457 p _107458 _107459)). Qed.
Lemma lem8115768 {A B P : Type'} (p : type560 A B P) (_107457 : A -> B) (_107459 : P) : (term464 A B P p _107457 _107459) = (term464 A B P p _107457 _107459).
Proof. exact (eq_refl (term464 A B P p _107457 _107459)). Qed.
Lemma lem8115769 {A B C D P : Type'} (g : type565 A B C D P) (z : type518 A B P) (_107457 : A -> B) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term547 A B C D P p z _107457 g _107458 _107459) = (term690 A B C D P g z _107457 p _107458 _107459).
Proof. exact (MK_COMB (@lem8115768 A B P p _107457 _107459) (@lem8115767 A B C D P g z _107457 p _107458 _107459)). Qed.
Lemma lem8115773 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8115774 {A B C D P : Type'} (g : type565 A B C D P) (z : type518 A B P) (_107457 : A -> B) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term690 A B C D P g z _107457 p _107458 _107459) = (term691 A B C D P g z _107457 p _107458 _107459).
Proof. exact (@lem8115773 ((term432 A B C D P g _107457 _107459) = (term432 A B C D P g _107458 _107459)) (term463 A B P p _107457 _107459) (term614 A B P z _107457 p _107458 _107459)). Qed.
Lemma lem8115790 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8115791 {A B P : Type'} (z : type518 A B P) (_107457 : A -> B) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term615 A B P z _107457 p _107458 _107459) = (term616 A B P z _107457 p _107458 _107459).
Proof. exact (@lem8115790 (term451 A B P z _107457 _107458 _107459) (term463 A B P p _107457 _107459) (term463 A B P p _107458 _107459)). Qed.
Lemma lem8115809 {A B C D P : Type'} (_107457 : A -> B) (g : type565 A B C D P) (_107458 : A -> B) (_107459 : P) : (term642 A B C D P _107457 g _107458 _107459) = (term642 A B C D P _107457 g _107458 _107459).
Proof. exact (eq_refl (term642 A B C D P _107457 g _107458 _107459)). Qed.
Lemma lem8115810 {A B C D P : Type'} (g : type565 A B C D P) (z : type518 A B P) (_107457 : A -> B) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term691 A B C D P g z _107457 p _107458 _107459) = (term692 A B C D P g z _107457 p _107458 _107459).
Proof. exact (MK_COMB (@lem8115809 A B C D P _107457 g _107458 _107459) (@lem8115791 A B P z _107457 p _107458 _107459)). Qed.
Lemma lem8115821 {A B C D P : Type'} (g : type565 A B C D P) (z : type518 A B P) (_107457 : A -> B) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term690 A B C D P g z _107457 p _107458 _107459) = (term692 A B C D P g z _107457 p _107458 _107459).
Proof. exact (TRANS (@lem8115774 A B C D P g z _107457 p _107458 _107459) (@lem8115810 A B C D P g z _107457 p _107458 _107459)). Qed.
Lemma lem8115822 {A B C D P : Type'} (g : type565 A B C D P) (z : type518 A B P) (_107457 : A -> B) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term547 A B C D P p z _107457 g _107458 _107459) = (term692 A B C D P g z _107457 p _107458 _107459).
Proof. exact (TRANS (@lem8115769 A B C D P g z _107457 p _107458 _107459) (@lem8115821 A B C D P g z _107457 p _107458 _107459)). Qed.
Lemma lem8115823 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8115824 {A B C D P : Type'} (g : type565 A B C D P) (z : type518 A B P) (_107457 : A -> B) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term693 A B C D P p z _107457 g _107458 _107459) = (term694 A B C D P g z _107457 p _107458 _107459).
Proof. exact (MK_COMB (@lem8115823) (@lem8115822 A B C D P g z _107457 p _107458 _107459)). Qed.
Lemma lem8115850 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8115851 {A B P : Type'} (z : type518 A B P) (_107457 : A -> B) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term501 A B P p z _107457 _107458 _107459) = (term614 A B P z _107457 p _107458 _107459).
Proof. exact (@lem8115850 (term451 A B P z _107457 _107458 _107459) (term463 A B P p _107458 _107459)). Qed.
Lemma lem8115859 {A B P : Type'} (p : type560 A B P) (_107457 : A -> B) (_107459 : P) : (term464 A B P p _107457 _107459) = (term464 A B P p _107457 _107459).
Proof. exact (eq_refl (term464 A B P p _107457 _107459)). Qed.
Lemma lem8115860 {A B P : Type'} (z : type518 A B P) (_107457 : A -> B) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term506 A B P p z _107457 _107458 _107459) = (term615 A B P z _107457 p _107458 _107459).
Proof. exact (MK_COMB (@lem8115859 A B P p _107457 _107459) (@lem8115851 A B P z _107457 p _107458 _107459)). Qed.
Lemma lem8115864 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8115865 {A B P : Type'} (z : type518 A B P) (_107457 : A -> B) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term615 A B P z _107457 p _107458 _107459) = (term616 A B P z _107457 p _107458 _107459).
Proof. exact (@lem8115864 (term451 A B P z _107457 _107458 _107459) (term463 A B P p _107457 _107459) (term463 A B P p _107458 _107459)). Qed.
Lemma lem8115883 {A B P : Type'} (z : type518 A B P) (_107457 : A -> B) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term506 A B P p z _107457 _107458 _107459) = (term616 A B P z _107457 p _107458 _107459).
Proof. exact (TRANS (@lem8115860 A B P z _107457 p _107458 _107459) (@lem8115865 A B P z _107457 p _107458 _107459)). Qed.
Lemma lem8115884 {A B C D P : Type'} (_107457 : A -> B) (g : type565 A B C D P) (_107458 : A -> B) (_107459 : P) : (term642 A B C D P _107457 g _107458 _107459) = (term642 A B C D P _107457 g _107458 _107459).
Proof. exact (eq_refl (term642 A B C D P _107457 g _107458 _107459)). Qed.
Lemma lem8115885 {A B C D P : Type'} (g : type565 A B C D P) (z : type518 A B P) (_107457 : A -> B) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term695 A B C D P g p z _107457 _107458 _107459) = (term692 A B C D P g z _107457 p _107458 _107459).
Proof. exact (MK_COMB (@lem8115884 A B C D P _107457 g _107458 _107459) (@lem8115883 A B P z _107457 p _107458 _107459)). Qed.
Lemma lem8115896 {A B C D P : Type'} (g : type565 A B C D P) (z : type518 A B P) (_107457 : A -> B) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : ((term547 A B C D P p z _107457 g _107458 _107459) = (term695 A B C D P g p z _107457 _107458 _107459)) = ((term692 A B C D P g z _107457 p _107458 _107459) = (term692 A B C D P g z _107457 p _107458 _107459)).
Proof. exact (MK_COMB (@lem8115824 A B C D P g z _107457 p _107458 _107459) (@lem8115885 A B C D P g z _107457 p _107458 _107459)). Qed.
Lemma lem8115898 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8115899 (x : Prop) : (x = x) = True.
Proof. exact (@lem8115898 Prop x). Qed.
Lemma lem8115900 {A B C D P : Type'} (g : type565 A B C D P) (z : type518 A B P) (_107457 : A -> B) (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : ((term692 A B C D P g z _107457 p _107458 _107459) = (term692 A B C D P g z _107457 p _107458 _107459)) = True.
Proof. exact (@lem8115899 (term692 A B C D P g z _107457 p _107458 _107459)). Qed.
Lemma lem8115901 {A B C D P : Type'} (g : type565 A B C D P) (p : type560 A B P) (z : type518 A B P) (_107457 : A -> B) (_107458 : A -> B) (_107459 : P) : ((term547 A B C D P p z _107457 g _107458 _107459) = (term695 A B C D P g p z _107457 _107458 _107459)) = True.
Proof. exact (TRANS (@lem8115896 A B C D P g z _107457 p _107458 _107459) (@lem8115900 A B C D P g z _107457 p _107458 _107459)). Qed.
Lemma lem8115902 {A B C D P : Type'} (g : type565 A B C D P) (p : type560 A B P) (z : type518 A B P) (_107457 : A -> B) (_107458 : A -> B) (_107459 : P) : True = ((term547 A B C D P p z _107457 g _107458 _107459) = (term695 A B C D P g p z _107457 _107458 _107459)).
Proof. exact (SYM (@lem8115901 A B C D P g p z _107457 _107458 _107459)). Qed.
Lemma lem8115903 {A B C D P : Type'} (g : type565 A B C D P) (p : type560 A B P) (z : type518 A B P) (_107457 : A -> B) (_107458 : A -> B) (_107459 : P) : (term547 A B C D P p z _107457 g _107458 _107459) = (term695 A B C D P g p z _107457 _107458 _107459).
Proof. exact (EQ_MP (@lem8115902 A B C D P g p z _107457 _107458 _107459) (@lem0)). Qed.
Lemma lem8115904 {A B C D P : Type'} (_107457 : A -> B) (_107458 : A -> B) (_107459 : P) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term695 A B C D P g p z _107457 _107458 _107459.
Proof. exact (EQ_MP (@lem8115903 A B C D P g p z _107457 _107458 _107459) (@lem8114402 A B C D P _107457 _107458 _107459 z g p lt2 s z' y h1)). Qed.
Lemma lem8115906 (b : Prop) (a : Prop) : (a \/ b) = (term581 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8115907 {A B C D P : Type'} (p : type560 A B P) (z : type518 A B P) (_107457 : A -> B) (g : type565 A B C D P) (_107458 : A -> B) (_107459 : P) : (term695 A B C D P g p z _107457 _107458 _107459) = (term696 A B C D P p z _107457 g _107458 _107459).
Proof. exact (@lem8115906 (term506 A B P p z _107457 _107458 _107459) ((term432 A B C D P g _107457 _107459) = (term432 A B C D P g _107458 _107459))). Qed.
Lemma lem8115909 (a : Prop) (b : Prop) : (term583 a b) = (term584 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8115910 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_107457 : A -> B) (_107458 : A -> B) (_107459 : P) : (term622 A B P p z _107457 _107458 _107459) = (term623 A B P p z _107457 _107458 _107459).
Proof. exact (@lem8115909 (term463 A B P p _107457 _107459) (term501 A B P p z _107457 _107458 _107459)). Qed.
Lemma lem8115912 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8115913 {A B P : Type'} (p : type560 A B P) (_107457 : A -> B) (_107459 : P) : (term587 A B P p _107457 _107459) = (term426 A B P p _107457 _107459).
Proof. exact (@lem8115912 (term426 A B P p _107457 _107459)). Qed.
Lemma lem8115914 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8115915 {A B P : Type'} (p : type560 A B P) (_107457 : A -> B) (_107459 : P) : (term588 A B P p _107457 _107459) = (term427 A B P p _107457 _107459).
Proof. exact (MK_COMB (@lem8115914) (@lem8115913 A B P p _107457 _107459)). Qed.
Lemma lem8115917 (a : Prop) (b : Prop) : (term583 a b) = (term584 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8115918 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_107457 : A -> B) (_107458 : A -> B) (_107459 : P) : (term624 A B P p z _107457 _107458 _107459) = (term625 A B P p z _107457 _107458 _107459).
Proof. exact (@lem8115917 (term463 A B P p _107458 _107459) (term451 A B P z _107457 _107458 _107459)). Qed.
Lemma lem8115920 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8115921 {A B P : Type'} (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term587 A B P p _107458 _107459) = (term426 A B P p _107458 _107459).
Proof. exact (@lem8115920 (term426 A B P p _107458 _107459)). Qed.
Lemma lem8115922 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8115923 {A B P : Type'} (p : type560 A B P) (_107458 : A -> B) (_107459 : P) : (term588 A B P p _107458 _107459) = (term427 A B P p _107458 _107459).
Proof. exact (MK_COMB (@lem8115922) (@lem8115921 A B P p _107458 _107459)). Qed.
Lemma lem8115925 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8115926 {A B P : Type'} (z : type518 A B P) (_107457 : A -> B) (_107458 : A -> B) (_107459 : P) : (term626 A B P z _107457 _107458 _107459) = ((term444 A B P z _107457 _107458 _107459) = (term447 A B P z _107457 _107458 _107459)).
Proof. exact (@lem8115925 ((term444 A B P z _107457 _107458 _107459) = (term447 A B P z _107457 _107458 _107459))). Qed.
Lemma lem8115927 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_107457 : A -> B) (_107458 : A -> B) (_107459 : P) : (term625 A B P p z _107457 _107458 _107459) = (term627 A B P p z _107457 _107458 _107459).
Proof. exact (MK_COMB (@lem8115923 A B P p _107458 _107459) (@lem8115926 A B P z _107457 _107458 _107459)). Qed.
Lemma lem8115928 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_107457 : A -> B) (_107458 : A -> B) (_107459 : P) : (term624 A B P p z _107457 _107458 _107459) = (term627 A B P p z _107457 _107458 _107459).
Proof. exact (TRANS (@lem8115918 A B P p z _107457 _107458 _107459) (@lem8115927 A B P p z _107457 _107458 _107459)). Qed.
Lemma lem8115929 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_107457 : A -> B) (_107458 : A -> B) (_107459 : P) : (term623 A B P p z _107457 _107458 _107459) = (term628 A B P p z _107457 _107458 _107459).
Proof. exact (MK_COMB (@lem8115915 A B P p _107457 _107459) (@lem8115928 A B P p z _107457 _107458 _107459)). Qed.
Lemma lem8115930 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_107457 : A -> B) (_107458 : A -> B) (_107459 : P) : (term622 A B P p z _107457 _107458 _107459) = (term628 A B P p z _107457 _107458 _107459).
Proof. exact (TRANS (@lem8115910 A B P p z _107457 _107458 _107459) (@lem8115929 A B P p z _107457 _107458 _107459)). Qed.
Lemma lem8115931 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8115932 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_107457 : A -> B) (_107458 : A -> B) (_107459 : P) : (term629 A B P p z _107457 _107458 _107459) = (term630 A B P p z _107457 _107458 _107459).
Proof. exact (MK_COMB (@lem8115931) (@lem8115930 A B P p z _107457 _107458 _107459)). Qed.
Lemma lem8115933 {A B C D P : Type'} (_107457 : A -> B) (g : type565 A B C D P) (_107458 : A -> B) (_107459 : P) : ((term432 A B C D P g _107457 _107459) = (term432 A B C D P g _107458 _107459)) = ((term432 A B C D P g _107457 _107459) = (term432 A B C D P g _107458 _107459)).
Proof. exact (eq_refl ((term432 A B C D P g _107457 _107459) = (term432 A B C D P g _107458 _107459))). Qed.
Lemma lem8115934 {A B C D P : Type'} (p : type560 A B P) (z : type518 A B P) (_107457 : A -> B) (g : type565 A B C D P) (_107458 : A -> B) (_107459 : P) : (term696 A B C D P p z _107457 g _107458 _107459) = (term697 A B C D P p z _107457 g _107458 _107459).
Proof. exact (MK_COMB (@lem8115932 A B P p z _107457 _107458 _107459) (@lem8115933 A B C D P _107457 g _107458 _107459)). Qed.
Lemma lem8115935 {A B C D P : Type'} (p : type560 A B P) (z : type518 A B P) (_107457 : A -> B) (g : type565 A B C D P) (_107458 : A -> B) (_107459 : P) : (term695 A B C D P g p z _107457 _107458 _107459) = (term697 A B C D P p z _107457 g _107458 _107459).
Proof. exact (TRANS (@lem8115907 A B C D P p z _107457 g _107458 _107459) (@lem8115934 A B C D P p z _107457 g _107458 _107459)). Qed.
Lemma lem8115937 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term633 A B C D P g' g f a) (h2 : term403 A B C D P z g p lt2 s z' y) (h3 : term35 A B P p lt2 s a f g') : term627 A B P p z g' f a.
Proof. exact (conj (@lem8115265 A B P p lt2 s a f g' h3) (@lem8115698 A B C D P z g z' y p lt2 s a f g' h1 h2 h3)). Qed.
Lemma lem8115938 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term633 A B C D P g' g f a) (h2 : term403 A B C D P z g p lt2 s z' y) (h3 : term35 A B P p lt2 s a f g') : term628 A B P p z g' f a.
Proof. exact (conj (@lem8115258 A B P p lt2 s a f g' h3) (@lem8115937 A B C D P z g z' y p lt2 s a f g' h1 h2 h3)). Qed.
Lemma lem8115940 {A B C D P : Type'} (_107457 : A -> B) (_107458 : A -> B) (_107459 : P) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term697 A B C D P p z _107457 g _107458 _107459.
Proof. exact (EQ_MP (@lem8115935 A B C D P p z _107457 g _107458 _107459) (@lem8115904 A B C D P _107457 _107458 _107459 z g p lt2 s z' y h1)). Qed.
Lemma lem8115941 {A B C D P : Type'} (_107457 : A -> B) (_107458 : A -> B) (_107459 : P) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term697 A B C D P p z _107457 g _107458 _107459.
Proof. exact (@lem8115940 A B C D P _107457 _107458 _107459 z g p lt2 s z' y h1). Qed.
Lemma lem8115942 {A B C D P : Type'} (g' : A -> B) (f : A -> B) (a : P) (z : type518 A B P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (y : type564 A B C P) (h1 : term403 A B C D P z g p lt2 s z' y) : term697 A B C D P p z g' g f a.
Proof. exact (@lem8115941 A B C D P g' f a z g p lt2 s z' y h1). Qed.
Lemma lem8115945 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term633 A B C D P g' g f a) (h2 : term403 A B C D P z g p lt2 s z' y) (h3 : term35 A B P p lt2 s a f g') : (term432 A B C D P g g' a) = (term432 A B C D P g f a).
Proof. exact (@lem8115942 A B C D P g' f a z g p lt2 s z' y h2 (@lem8115938 A B C D P z g z' y p lt2 s a f g' h1 h2 h3)). Qed.
Lemma lem8115946 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term403 A B C D P z g p lt2 s z' y) (h2 : term35 A B P p lt2 s a f g') : term698 A B C D P g' g f a.
Proof. exact (fun h0 : term633 A B C D P g' g f a => @lem8115945 A B C D P z g z' y p lt2 s a f g' h0 h1 h2). Qed.
Lemma lem8115948 (p : Prop) : (term556 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8115949 {A B C D P : Type'} (g' : A -> B) (g : type565 A B C D P) (f : A -> B) (a : P) : (term698 A B C D P g' g f a) = ((term432 A B C D P g g' a) = (term432 A B C D P g f a)).
Proof. exact (@lem8115948 ((term432 A B C D P g g' a) = (term432 A B C D P g f a))). Qed.
Lemma lem8115950 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term403 A B C D P z g p lt2 s z' y) (h2 : term35 A B P p lt2 s a f g') : (term432 A B C D P g g' a) = (term432 A B C D P g f a).
Proof. exact (EQ_MP (@lem8115949 A B C D P g' g f a) (@lem8115946 A B C D P z g z' y p lt2 s a f g' h1 h2)). Qed.
Lemma lem8115952 {C D : Type'} (x : C -> D) : x = x.
Proof. exact (@lem21386 (C -> D) x). Qed.
Lemma lem8115953 {C D : Type'} (x : C -> D) : x = x.
Proof. exact (@lem8115952 C D x). Qed.
Lemma lem8115954 {A B C D P : Type'} (g : type565 A B C D P) (g' : A -> B) (a : P) : (term432 A B C D P g g' a) = (term432 A B C D P g g' a).
Proof. exact (@lem8115953 C D (term432 A B C D P g g' a)). Qed.
Lemma lem8115955 {A B C D P : Type'} (g : type565 A B C D P) (g' : A -> B) (a : P) : term699 A B C D P g g' a.
Proof. exact (fun h0 : term700 A B C D P g g' a => @lem8115954 A B C D P g g' a). Qed.
Lemma lem8115957 (p : Prop) : (term556 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8115958 {A B C D P : Type'} (g : type565 A B C D P) (g' : A -> B) (a : P) : (term699 A B C D P g g' a) = ((term432 A B C D P g g' a) = (term432 A B C D P g g' a)).
Proof. exact (@lem8115957 ((term432 A B C D P g g' a) = (term432 A B C D P g g' a))). Qed.
Lemma lem8115959 {A B C D P : Type'} (g : type565 A B C D P) (g' : A -> B) (a : P) : (term432 A B C D P g g' a) = (term432 A B C D P g g' a).
Proof. exact (EQ_MP (@lem8115958 A B C D P g g' a) (@lem8115955 A B C D P g g' a)). Qed.
Lemma lem8115977 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8115978 {C D : Type'} (y : C -> D) (x : C -> D) (z : C -> D) : (term701 C D x y z) = (term702 C D y x z).
Proof. exact (@lem8115977 (y = z) (term703 C D x z)). Qed.
Lemma lem8115988 {C D : Type'} (x : C -> D) (y : C -> D) : (term704 C D x y) = (term704 C D x y).
Proof. exact (eq_refl (term704 C D x y)). Qed.
Lemma lem8115989 {C D : Type'} (y : C -> D) (x : C -> D) (z : C -> D) : (term553 C D x y z) = (term705 C D y x z).
Proof. exact (MK_COMB (@lem8115988 C D x y) (@lem8115978 C D y x z)). Qed.
Lemma lem8115993 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8115994 {C D : Type'} (y : C -> D) (x : C -> D) (z : C -> D) : (term705 C D y x z) = (term706 C D y x z).
Proof. exact (@lem8115993 (y = z) (term703 C D x y) (term703 C D x z)). Qed.
Lemma lem8116016 {C D : Type'} (y : C -> D) (x : C -> D) (z : C -> D) : (term553 C D x y z) = (term706 C D y x z).
Proof. exact (TRANS (@lem8115989 C D y x z) (@lem8115994 C D y x z)). Qed.
Lemma lem8116017 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8116018 {C D : Type'} (y : C -> D) (x : C -> D) (z : C -> D) : (term707 C D x y z) = (term708 C D y x z).
Proof. exact (MK_COMB (@lem8116017) (@lem8116016 C D y x z)). Qed.
Lemma lem8116040 {C D : Type'} (y : C -> D) (x : C -> D) (z : C -> D) : (term706 C D y x z) = (term706 C D y x z).
Proof. exact (eq_refl (term706 C D y x z)). Qed.
Lemma lem8116041 {C D : Type'} (y : C -> D) (x : C -> D) (z : C -> D) : ((term553 C D x y z) = (term706 C D y x z)) = ((term706 C D y x z) = (term706 C D y x z)).
Proof. exact (MK_COMB (@lem8116018 C D y x z) (@lem8116040 C D y x z)). Qed.
Lemma lem8116043 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8116044 (x : Prop) : (x = x) = True.
Proof. exact (@lem8116043 Prop x). Qed.
Lemma lem8116045 {C D : Type'} (y : C -> D) (x : C -> D) (z : C -> D) : ((term706 C D y x z) = (term706 C D y x z)) = True.
Proof. exact (@lem8116044 (term706 C D y x z)). Qed.
Lemma lem8116046 {C D : Type'} (y : C -> D) (x : C -> D) (z : C -> D) : ((term553 C D x y z) = (term706 C D y x z)) = True.
Proof. exact (TRANS (@lem8116041 C D y x z) (@lem8116045 C D y x z)). Qed.
Lemma lem8116047 {C D : Type'} (y : C -> D) (x : C -> D) (z : C -> D) : True = ((term553 C D x y z) = (term706 C D y x z)).
Proof. exact (SYM (@lem8116046 C D y x z)). Qed.
Lemma lem8116048 {C D : Type'} (y : C -> D) (x : C -> D) (z : C -> D) : (term553 C D x y z) = (term706 C D y x z).
Proof. exact (EQ_MP (@lem8116047 C D y x z) (@lem0)). Qed.
Lemma lem8116049 {C D : Type'} (y : C -> D) (x : C -> D) (z : C -> D) : term706 C D y x z.
Proof. exact (EQ_MP (@lem8116048 C D y x z) (@lem8114609 C D x y z)). Qed.
Lemma lem8116051 (b : Prop) (a : Prop) : (a \/ b) = (term581 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8116052 {C D : Type'} (x : C -> D) (y : C -> D) (z : C -> D) : (term706 C D y x z) = (term709 C D x y z).
Proof. exact (@lem8116051 (term710 C D y x z) (y = z)). Qed.
Lemma lem8116054 (a : Prop) (b : Prop) : (term583 a b) = (term584 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8116055 {C D : Type'} (y : C -> D) (x : C -> D) (z : C -> D) : (term711 C D y x z) = (term712 C D y x z).
Proof. exact (@lem8116054 (term703 C D x y) (term703 C D x z)). Qed.
Lemma lem8116057 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8116058 {C D : Type'} (x : C -> D) (y : C -> D) : (term713 C D x y) = (x = y).
Proof. exact (@lem8116057 (x = y)). Qed.
Lemma lem8116059 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8116060 {C D : Type'} (x : C -> D) (y : C -> D) : (term714 C D x y) = (term715 C D x y).
Proof. exact (MK_COMB (@lem8116059) (@lem8116058 C D x y)). Qed.
Lemma lem8116062 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8116063 {C D : Type'} (x : C -> D) (z : C -> D) : (term713 C D x z) = (x = z).
Proof. exact (@lem8116062 (x = z)). Qed.
Lemma lem8116064 {C D : Type'} (y : C -> D) (x : C -> D) (z : C -> D) : (term712 C D y x z) = (term716 C D y x z).
Proof. exact (MK_COMB (@lem8116060 C D x y) (@lem8116063 C D x z)). Qed.
Lemma lem8116065 {C D : Type'} (y : C -> D) (x : C -> D) (z : C -> D) : (term711 C D y x z) = (term716 C D y x z).
Proof. exact (TRANS (@lem8116055 C D y x z) (@lem8116064 C D y x z)). Qed.
Lemma lem8116066 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8116067 {C D : Type'} (y : C -> D) (x : C -> D) (z : C -> D) : (term717 C D y x z) = (term718 C D y x z).
Proof. exact (MK_COMB (@lem8116066) (@lem8116065 C D y x z)). Qed.
Lemma lem8116068 {C D : Type'} (y : C -> D) (z : C -> D) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem8116069 {C D : Type'} (x : C -> D) (y : C -> D) (z : C -> D) : (term709 C D x y z) = (term719 C D x y z).
Proof. exact (MK_COMB (@lem8116067 C D y x z) (@lem8116068 C D y z)). Qed.
Lemma lem8116070 {C D : Type'} (x : C -> D) (y : C -> D) (z : C -> D) : (term706 C D y x z) = (term719 C D x y z).
Proof. exact (TRANS (@lem8116052 C D x y z) (@lem8116069 C D x y z)). Qed.
Lemma lem8116072 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term403 A B C D P z g p lt2 s z' y) (h2 : term35 A B P p lt2 s a f g') : term720 A B C D P f g g' a.
Proof. exact (conj (@lem8115950 A B C D P z g z' y p lt2 s a f g' h1 h2) (@lem8115959 A B C D P g g' a)). Qed.
Lemma lem8116074 {C D : Type'} (x : C -> D) (y : C -> D) (z : C -> D) : term719 C D x y z.
Proof. exact (EQ_MP (@lem8116070 C D x y z) (@lem8116049 C D y x z)). Qed.
Lemma lem8116075 {C D : Type'} (x : C -> D) (y : C -> D) (z : C -> D) : term719 C D x y z.
Proof. exact (@lem8116074 C D x y z). Qed.
Lemma lem8116076 {A B C D P : Type'} (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : term721 A B C D P f g g' a.
Proof. exact (@lem8116075 C D (term432 A B C D P g g' a) (term432 A B C D P g f a) (term432 A B C D P g g' a)). Qed.
Lemma lem8116079 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term403 A B C D P z g p lt2 s z' y) (h2 : term35 A B P p lt2 s a f g') : (term432 A B C D P g f a) = (term432 A B C D P g g' a).
Proof. exact (@lem8116076 A B C D P f g g' a (@lem8116072 A B C D P z g z' y p lt2 s a f g' h1 h2)). Qed.
Lemma lem8116080 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term403 A B C D P z g p lt2 s z' y) (h2 : term35 A B P p lt2 s a f g') : term698 A B C D P f g g' a.
Proof. exact (fun h0 : term633 A B C D P f g g' a => @lem8116079 A B C D P z g z' y p lt2 s a f g' h1 h2). Qed.
Lemma lem8116082 (p : Prop) : (term556 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8116083 {A B C D P : Type'} (f : A -> B) (g : type565 A B C D P) (g' : A -> B) (a : P) : (term698 A B C D P f g g' a) = ((term432 A B C D P g f a) = (term432 A B C D P g g' a)).
Proof. exact (@lem8116082 ((term432 A B C D P g f a) = (term432 A B C D P g g' a))). Qed.
Lemma lem8116084 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term403 A B C D P z g p lt2 s z' y) (h2 : term35 A B P p lt2 s a f g') : (term432 A B C D P g f a) = (term432 A B C D P g g' a).
Proof. exact (EQ_MP (@lem8116083 A B C D P f g g' a) (@lem8116080 A B C D P z g z' y p lt2 s a f g' h1 h2)). Qed.
Lemma lem8116102 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8116103 {C D : Type'} (_107513 : C) (_107515 : C) (_107512 : C -> D) (_107514 : C -> D) : (term550 C D _107512 _107513 _107514 _107515) = (term722 C D _107513 _107515 _107512 _107514).
Proof. exact (@lem8116102 ((@I (C -> D) _107512 _107513) = (@I (C -> D) _107514 _107515)) (term703 C D _107512 _107514)). Qed.
Lemma lem8116113 {C : Type'} (_107513 : C) (_107515 : C) : (term669 C _107513 _107515) = (term669 C _107513 _107515).
Proof. exact (eq_refl (term669 C _107513 _107515)). Qed.
Lemma lem8116114 {C D : Type'} (_107513 : C) (_107515 : C) (_107512 : C -> D) (_107514 : C -> D) : (term552 C D _107512 _107513 _107514 _107515) = (term723 C D _107513 _107515 _107512 _107514).
Proof. exact (MK_COMB (@lem8116113 C _107513 _107515) (@lem8116103 C D _107513 _107515 _107512 _107514)). Qed.
Lemma lem8116118 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8116119 {C D : Type'} (_107513 : C) (_107515 : C) (_107512 : C -> D) (_107514 : C -> D) : (term723 C D _107513 _107515 _107512 _107514) = (term724 C D _107513 _107515 _107512 _107514).
Proof. exact (@lem8116118 ((@I (C -> D) _107512 _107513) = (@I (C -> D) _107514 _107515)) (term668 C _107513 _107515) (term703 C D _107512 _107514)). Qed.
Lemma lem8116141 {C D : Type'} (_107513 : C) (_107515 : C) (_107512 : C -> D) (_107514 : C -> D) : (term552 C D _107512 _107513 _107514 _107515) = (term724 C D _107513 _107515 _107512 _107514).
Proof. exact (TRANS (@lem8116114 C D _107513 _107515 _107512 _107514) (@lem8116119 C D _107513 _107515 _107512 _107514)). Qed.
Lemma lem8116142 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8116143 {C D : Type'} (_107513 : C) (_107515 : C) (_107512 : C -> D) (_107514 : C -> D) : (term725 C D _107512 _107513 _107514 _107515) = (term726 C D _107513 _107515 _107512 _107514).
Proof. exact (MK_COMB (@lem8116142) (@lem8116141 C D _107513 _107515 _107512 _107514)). Qed.
Lemma lem8116165 {C D : Type'} (_107513 : C) (_107515 : C) (_107512 : C -> D) (_107514 : C -> D) : (term724 C D _107513 _107515 _107512 _107514) = (term724 C D _107513 _107515 _107512 _107514).
Proof. exact (eq_refl (term724 C D _107513 _107515 _107512 _107514)). Qed.
Lemma lem8116166 {C D : Type'} (_107513 : C) (_107515 : C) (_107512 : C -> D) (_107514 : C -> D) : ((term552 C D _107512 _107513 _107514 _107515) = (term724 C D _107513 _107515 _107512 _107514)) = ((term724 C D _107513 _107515 _107512 _107514) = (term724 C D _107513 _107515 _107512 _107514)).
Proof. exact (MK_COMB (@lem8116143 C D _107513 _107515 _107512 _107514) (@lem8116165 C D _107513 _107515 _107512 _107514)). Qed.
Lemma lem8116168 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8116169 (x : Prop) : (x = x) = True.
Proof. exact (@lem8116168 Prop x). Qed.
Lemma lem8116170 {C D : Type'} (_107513 : C) (_107515 : C) (_107512 : C -> D) (_107514 : C -> D) : ((term724 C D _107513 _107515 _107512 _107514) = (term724 C D _107513 _107515 _107512 _107514)) = True.
Proof. exact (@lem8116169 (term724 C D _107513 _107515 _107512 _107514)). Qed.
Lemma lem8116171 {C D : Type'} (_107513 : C) (_107515 : C) (_107512 : C -> D) (_107514 : C -> D) : ((term552 C D _107512 _107513 _107514 _107515) = (term724 C D _107513 _107515 _107512 _107514)) = True.
Proof. exact (TRANS (@lem8116166 C D _107513 _107515 _107512 _107514) (@lem8116170 C D _107513 _107515 _107512 _107514)). Qed.
Lemma lem8116172 {C D : Type'} (_107513 : C) (_107515 : C) (_107512 : C -> D) (_107514 : C -> D) : True = ((term552 C D _107512 _107513 _107514 _107515) = (term724 C D _107513 _107515 _107512 _107514)).
Proof. exact (SYM (@lem8116171 C D _107513 _107515 _107512 _107514)). Qed.
Lemma lem8116173 {C D : Type'} (_107513 : C) (_107515 : C) (_107512 : C -> D) (_107514 : C -> D) : (term552 C D _107512 _107513 _107514 _107515) = (term724 C D _107513 _107515 _107512 _107514).
Proof. exact (EQ_MP (@lem8116172 C D _107513 _107515 _107512 _107514) (@lem0)). Qed.
Lemma lem8116174 {C D : Type'} (_107513 : C) (_107515 : C) (_107512 : C -> D) (_107514 : C -> D) : term724 C D _107513 _107515 _107512 _107514.
Proof. exact (EQ_MP (@lem8116173 C D _107513 _107515 _107512 _107514) (@lem8114605 C D _107512 _107513 _107514 _107515)). Qed.
Lemma lem8116176 (b : Prop) (a : Prop) : (a \/ b) = (term581 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8116177 {C D : Type'} (_107512 : C -> D) (_107513 : C) (_107514 : C -> D) (_107515 : C) : (term724 C D _107513 _107515 _107512 _107514) = (term727 C D _107512 _107513 _107514 _107515).
Proof. exact (@lem8116176 (term728 C D _107513 _107515 _107512 _107514) ((@I (C -> D) _107512 _107513) = (@I (C -> D) _107514 _107515))). Qed.
Lemma lem8116179 (a : Prop) (b : Prop) : (term583 a b) = (term584 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8116180 {C D : Type'} (_107513 : C) (_107515 : C) (_107512 : C -> D) (_107514 : C -> D) : (term729 C D _107513 _107515 _107512 _107514) = (term730 C D _107513 _107515 _107512 _107514).
Proof. exact (@lem8116179 (term668 C _107513 _107515) (term703 C D _107512 _107514)). Qed.
Lemma lem8116182 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8116183 {C : Type'} (_107513 : C) (_107515 : C) : (term678 C _107513 _107515) = (_107513 = _107515).
Proof. exact (@lem8116182 (_107513 = _107515)). Qed.
Lemma lem8116184 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8116185 {C : Type'} (_107513 : C) (_107515 : C) : (term679 C _107513 _107515) = (term680 C _107513 _107515).
Proof. exact (MK_COMB (@lem8116184) (@lem8116183 C _107513 _107515)). Qed.
Lemma lem8116187 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8116188 {C D : Type'} (_107512 : C -> D) (_107514 : C -> D) : (term713 C D _107512 _107514) = (_107512 = _107514).
Proof. exact (@lem8116187 (_107512 = _107514)). Qed.
Lemma lem8116189 {C D : Type'} (_107513 : C) (_107515 : C) (_107512 : C -> D) (_107514 : C -> D) : (term730 C D _107513 _107515 _107512 _107514) = (term731 C D _107513 _107515 _107512 _107514).
Proof. exact (MK_COMB (@lem8116185 C _107513 _107515) (@lem8116188 C D _107512 _107514)). Qed.
Lemma lem8116190 {C D : Type'} (_107513 : C) (_107515 : C) (_107512 : C -> D) (_107514 : C -> D) : (term729 C D _107513 _107515 _107512 _107514) = (term731 C D _107513 _107515 _107512 _107514).
Proof. exact (TRANS (@lem8116180 C D _107513 _107515 _107512 _107514) (@lem8116189 C D _107513 _107515 _107512 _107514)). Qed.
Lemma lem8116191 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8116192 {C D : Type'} (_107513 : C) (_107515 : C) (_107512 : C -> D) (_107514 : C -> D) : (term732 C D _107513 _107515 _107512 _107514) = (term733 C D _107513 _107515 _107512 _107514).
Proof. exact (MK_COMB (@lem8116191) (@lem8116190 C D _107513 _107515 _107512 _107514)). Qed.
Lemma lem8116193 {C D : Type'} (_107512 : C -> D) (_107513 : C) (_107514 : C -> D) (_107515 : C) : ((@I (C -> D) _107512 _107513) = (@I (C -> D) _107514 _107515)) = ((@I (C -> D) _107512 _107513) = (@I (C -> D) _107514 _107515)).
Proof. exact (eq_refl ((@I (C -> D) _107512 _107513) = (@I (C -> D) _107514 _107515))). Qed.
Lemma lem8116194 {C D : Type'} (_107512 : C -> D) (_107513 : C) (_107514 : C -> D) (_107515 : C) : (term727 C D _107512 _107513 _107514 _107515) = (term734 C D _107512 _107513 _107514 _107515).
Proof. exact (MK_COMB (@lem8116192 C D _107513 _107515 _107512 _107514) (@lem8116193 C D _107512 _107513 _107514 _107515)). Qed.
Lemma lem8116195 {C D : Type'} (_107512 : C -> D) (_107513 : C) (_107514 : C -> D) (_107515 : C) : (term724 C D _107513 _107515 _107512 _107514) = (term734 C D _107512 _107513 _107514 _107515).
Proof. exact (TRANS (@lem8116177 C D _107512 _107513 _107514 _107515) (@lem8116194 C D _107512 _107513 _107514 _107515)). Qed.
Lemma lem8116197 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term403 A B C D P z g p lt2 s z' y) (h2 : term35 A B P p lt2 s a f g') : term735 A B C D P y f g g' a.
Proof. exact (conj (@lem8115251 A B C D P z g z' y p lt2 s a f g' h1 h2) (@lem8116084 A B C D P z g z' y p lt2 s a f g' h1 h2)). Qed.
Lemma lem8116199 {C D : Type'} (_107512 : C -> D) (_107513 : C) (_107514 : C -> D) (_107515 : C) : term734 C D _107512 _107513 _107514 _107515.
Proof. exact (EQ_MP (@lem8116195 C D _107512 _107513 _107514 _107515) (@lem8116174 C D _107513 _107515 _107512 _107514)). Qed.
Lemma lem8116200 {C D : Type'} (_107512 : C -> D) (_107513 : C) (_107514 : C -> D) (_107515 : C) : term734 C D _107512 _107513 _107514 _107515.
Proof. exact (@lem8116199 C D _107512 _107513 _107514 _107515). Qed.
Lemma lem8116201 {A B C D P : Type'} (f : A -> B) (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : term736 A B C D P f g y g' a.
Proof. exact (@lem8116200 C D (term432 A B C D P g f a) (term430 A B C P y f a) (term432 A B C D P g g' a) (term430 A B C P y g' a)). Qed.
Lemma lem8116204 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term403 A B C D P z g p lt2 s z' y) (h2 : term35 A B P p lt2 s a f g') : (term434 A B C D P g y f a) = (term434 A B C D P g y g' a).
Proof. exact (@lem8116201 A B C D P f g y g' a (@lem8116197 A B C D P z g z' y p lt2 s a f g' h1 h2)). Qed.
Lemma lem8116205 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term403 A B C D P z g p lt2 s z' y) (h2 : term35 A B P p lt2 s a f g') : term737 A B C D P f g y g' a.
Proof. exact (fun h0 : term436 A B C D P f g y g' a => @lem8116204 A B C D P z g z' y p lt2 s a f g' h1 h2). Qed.
Lemma lem8116207 (p : Prop) : (term556 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8116208 {A B C D P : Type'} (f : A -> B) (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term737 A B C D P f g y g' a) = ((term434 A B C D P g y f a) = (term434 A B C D P g y g' a)).
Proof. exact (@lem8116207 ((term434 A B C D P g y f a) = (term434 A B C D P g y g' a))). Qed.
Lemma lem8116209 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term403 A B C D P z g p lt2 s z' y) (h2 : term35 A B P p lt2 s a f g') : (term434 A B C D P g y f a) = (term434 A B C D P g y g' a).
Proof. exact (EQ_MP (@lem8116208 A B C D P f g y g' a) (@lem8116205 A B C D P z g z' y p lt2 s a f g' h1 h2)). Qed.
Lemma lem8116212 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8116214 {A B C D P : Type'} (f : A -> B) (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term436 A B C D P f g y g' a) = (term738 A B C D P f g y g' a).
Proof. exact (@lem8116212 ((term434 A B C D P g y f a) = (term434 A B C D P g y g' a))). Qed.
Lemma lem8116217 {A B C D P : Type'} (f : A -> B) (g : type565 A B C D P) (y : type564 A B C P) (g' : A -> B) (a : P) (h1 : term127 A B C D P f g y g' a) : term738 A B C D P f g y g' a.
Proof. exact (EQ_MP (@lem8116214 A B C D P f g y g' a) (@lem8114320 A B C D P f g y g' a h1)). Qed.
Lemma lem8116220 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term127 A B C D P f g y g' a) (h2 : term403 A B C D P z g p lt2 s z' y) (h3 : term35 A B P p lt2 s a f g') : False.
Proof. exact (@lem8116217 A B C D P f g y g' a h1 (@lem8116209 A B C D P z g z' y p lt2 s a f g' h2 h3)). Qed.
Lemma lem8116221 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term127 A B C D P f g y g' a) (h2 : term403 A B C D P z g p lt2 s z' y) (h3 : term35 A B P p lt2 s a f g') : term739.
Proof. exact (fun h0 : ~ False => @lem8116220 A B C D P z g z' y p lt2 s a f g' h1 h2 h3). Qed.
Lemma lem8116223 (p : Prop) : (term556 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8116224 : term739 = False.
Proof. exact (@lem8116223 False). Qed.
Lemma lem8116225 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (z' : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term127 A B C D P f g y g' a) (h2 : term403 A B C D P z g p lt2 s z' y) (h3 : term35 A B P p lt2 s a f g') : False.
Proof. exact (EQ_MP (@lem8116224) (@lem8116221 A B C D P z g z' y p lt2 s a f g' h1 h2 h3)). Qed.
Lemma lem8116226 {A B C D P : Type'} (z : type518 A B P) (g : type565 A B C D P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term406 A B C D P z g p lt2 s y) (h2 : term127 A B C D P f g y g' a) (h3 : term35 A B P p lt2 s a f g') : False.
Proof. exact (ex_elim (@lem8113537 A B C D P z g p lt2 s y h1) (fun z' : type518 A B P => fun h0 : term405 A B C D P z g p lt2 s y z' => @lem8116225 A B C D P z g z' y p lt2 s a f g' h2 h0 h3)). Qed.
Lemma lem8116227 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term127 A B C D P f g y g' a) (h2 : term29 A B C D P g p lt2 s y) (h3 : term35 A B P p lt2 s a f g') : False.
Proof. exact (ex_elim (@lem8113459 A B C D P g p lt2 s y h2) (fun z : type518 A B P => fun h0 : term407 A B C D P g p lt2 s y z => @lem8116226 A B C D P z g y p lt2 s a f g' h0 h1 h3)). Qed.
Lemma lem8116228 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term127 A B C D P f g y g' a) (h2 : term29 A B C D P g p lt2 s y) (h3 : term35 A B P p lt2 s a f g') : (term127 A B C D P f g y g' a) = False.
Proof. exact (prop_ext (fun h4 : term127 A B C D P f g y g' a => @lem8116227 A B C D P g y p lt2 s a f g' h1 h2 h3) (fun h4 : False => @lem8113536 A B C D P f g y g' a h1)). Qed.
Lemma lem8116229 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term127 A B C D P f g y g' a) (h2 : term29 A B C D P g p lt2 s y) (h3 : term35 A B P p lt2 s a f g') : False.
Proof. exact (EQ_MP (@lem8116228 A B C D P g y p lt2 s a f g' h1 h2 h3) (@lem8113536 A B C D P f g y g' a h1)). Qed.
Lemma lem8116230 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term127 A B C D P f g y g' a) (h2 : term29 A B C D P g p lt2 s y) (h3 : term35 A B P p lt2 s a f g') : (term127 A B C D P f g y g' a) = False.
Proof. exact (prop_ext (fun h4 : term127 A B C D P f g y g' a => @lem8116229 A B C D P g y p lt2 s a f g' h1 h2 h3) (fun h4 : False => @lem8112756 A B C D P f g y g' a h1)). Qed.
Lemma lem8116231 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term127 A B C D P f g y g' a) (h2 : term29 A B C D P g p lt2 s y) (h3 : term35 A B P p lt2 s a f g') : False.
Proof. exact (EQ_MP (@lem8116230 A B C D P g y p lt2 s a f g' h1 h2 h3) (@lem8112756 A B C D P f g y g' a h1)). Qed.
Lemma lem8116232 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term29 A B C D P g p lt2 s y) (h2 : term35 A B P p lt2 s a f g') : term126 A B C D P f g y g' a.
Proof. exact (fun h0 : term127 A B C D P f g y g' a => @lem8116231 A B C D P g y p lt2 s a f g' h0 h1 h2). Qed.
Lemma lem8116233 {A B C D P : Type'} (g : type565 A B C D P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term29 A B C D P g p lt2 s y) (h2 : term35 A B P p lt2 s a f g') : (term54 A B C D P g y f a) = (term54 A B C D P g y g' a).
Proof. exact (EQ_MP (@lem8112755 A B C D P f g y g' a) (@lem8116232 A B C D P g y p lt2 s a f g' h1 h2)). Qed.
Lemma lem8116234 {A B C D P : Type'} (f : A -> B) (g' : A -> B) (a : P) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) (h1 : term29 A B C D P g p lt2 s y) : term63 A B C D P p lt2 s f g y g' a.
Proof. exact (fun h0 : term35 A B P p lt2 s a f g' => @lem8116233 A B C D P g y p lt2 s a f g' h1 h0). Qed.
Lemma lem8116239 {A B C D P : Type'} (f : A -> B) (g' : A -> B) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) (h1 : term29 A B C D P g p lt2 s y) : term67 A B C D P p lt2 s f g y g'.
Proof. exact (fun a : P => @lem8116234 A B C D P f g' a g p lt2 s y h1). Qed.
Lemma lem8116244 {A B C D P : Type'} (f : A -> B) (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) (h1 : term29 A B C D P g p lt2 s y) : term71 A B C D P p lt2 s f g y.
Proof. exact (fun g' : A -> B => @lem8116239 A B C D P f g' g p lt2 s y h1). Qed.
Lemma lem8116249 {A B C D P : Type'} (g : type565 A B C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) (h1 : term29 A B C D P g p lt2 s y) : term74 A B C D P p lt2 s g y.
Proof. exact (fun f : A -> B => @lem8116244 A B C D P f g p lt2 s y h1). Qed.
Lemma lem8116250 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) (y : type564 A B C P) : term78 A B C D P p lt2 s g y.
Proof. exact (fun h0 : term29 A B C D P g p lt2 s y => @lem8116249 A B C D P g p lt2 s y h0). Qed.
Lemma lem8116255 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type565 A B C D P) : term82 A B C D P p lt2 s g.
Proof. exact (fun y : type564 A B C P => @lem8116250 A B C D P p lt2 s g y). Qed.
Lemma lem8116260 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) : term86 A B C D P p lt2 s.
Proof. exact (fun g : type565 A B C D P => @lem8116255 A B C D P p lt2 s g). Qed.
Lemma lem8116265 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) : term90 A B C D P p lt2.
Proof. exact (fun s : P -> A => @lem8116260 A B C D P p lt2 s). Qed.
Lemma lem8116270 {A B C D P : Type'} (lt2 : type1402 A) : term94 A B C D P lt2.
Proof. exact (fun p : type560 A B P => @lem8116265 A B C D P p lt2). Qed.
Lemma lem8116275 {A B C D P : Type'} : term98 A B C D P.
Proof. exact (fun lt2 : type1402 A => @lem8116270 A B C D P lt2). Qed.
Lemma lem8116276 {A B C D P : Type'} : term100 A B C D P.
Proof. exact (EQ_MP (@lem8112749 A B C D P) (@lem8116275 A B C D P)). Qed.
Lemma lem8116278 {A B C D P : Type'} : term100 A B C D P.
Proof. exact (@lem8112400 A B C D P (@lem8116276 A B C D P)). Qed.
Lemma lem8116279 {A B C D P : Type'} (h1 : term101 A B C D P) : False.
Proof. exact (@lem8116278 A B C D P (@lem8112384 A B C D P h1)). Qed.
Lemma lem8116280 {A B C D P : Type'} (h1 : term101 A B C D P) : (term101 A B C D P) = False.
Proof. exact (prop_ext (fun h2 : term101 A B C D P => @lem8116279 A B C D P h1) (fun h2 : False => @lem8112384 A B C D P h1)). Qed.
Lemma lem8116281 {A B C D P : Type'} (h1 : term101 A B C D P) : False.
Proof. exact (EQ_MP (@lem8116280 A B C D P h1) (@lem8112384 A B C D P h1)). Qed.
Lemma lem8116282 {A B C D P : Type'} : term100 A B C D P.
Proof. exact (fun h0 : term101 A B C D P => @lem8116281 A B C D P h0). Qed.
Lemma lem8116283 {A B C D P : Type'} : term98 A B C D P.
Proof. exact (EQ_MP (@lem8112383 A B C D P) (@lem8116282 A B C D P)). Qed.
Lemma lem8116284 {A B C D P : Type'} : term97 A B C D P.
Proof. exact (EQ_MP (@lem8112379 A B C D P) (@lem8116283 A B C D P)). Qed.
