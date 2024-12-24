Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUBSET_CROSS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EXTENSION_spec.
Require Import FORALL_PAIR_THM_spec.
Require Import IN_CROSS_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import SUBSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm1857_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm4211_spec.
Require Import thm82_spec.
Lemma lem4334567 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4334568 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4334569 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4334568 t1) (@lem4334567 t1)). Qed.
Lemma lem4334570 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4334569 t1 t2). Qed.
Lemma lem4334571 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4334572 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4334571 t1 t2) (@lem4334570 t1 t2)). Qed.
Lemma lem4334573 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4334572 t1 t2 t3). Qed.
Lemma lem4334574 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4334575 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4334574 t1 t2 t3) (@lem4334573 t1 t2 t3)). Qed.
Lemma lem4334576 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4334575 t1 t2 t3)). Qed.
Lemma lem4334577 {A : Type'} (x : A) : term7 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem4334578 {A : Type'} (x : A) : (term7 A x) = (term8 A x).
Proof. exact (eq_refl (term7 A x)). Qed.
Lemma lem4334579 {A : Type'} (x : A) : term8 A x.
Proof. exact (EQ_MP (@lem4334578 A x) (@lem4334577 A x)). Qed.
Lemma lem4334580 {A : Type'} (x : A) : term9 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem4334582 {_103718 _103721 : Type'} (x : _103718) : term10 _103718 _103721 x.
Proof. exact (@lem4325365 _103718 _103721 x). Qed.
Lemma lem4334583 {_103718 _103721 : Type'} (x : _103718) : (term10 _103718 _103721 x) = (term11 _103718 _103721 x).
Proof. exact (eq_refl (term10 _103718 _103721 x)). Qed.
Lemma lem4334584 {_103718 _103721 : Type'} (x : _103718) : term11 _103718 _103721 x.
Proof. exact (EQ_MP (@lem4334583 _103718 _103721 x) (@lem4334582 _103718 _103721 x)). Qed.
Lemma lem4334585 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term12 _103718 _103721 x y.
Proof. exact (@lem4334584 _103718 _103721 x y). Qed.
Lemma lem4334586 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : (term12 _103718 _103721 x y) = (term13 _103718 _103721 x y).
Proof. exact (eq_refl (term12 _103718 _103721 x y)). Qed.
Lemma lem4334587 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term13 _103718 _103721 x y.
Proof. exact (EQ_MP (@lem4334586 _103718 _103721 x y) (@lem4334585 _103718 _103721 x y)). Qed.
Lemma lem4334588 {_103718 _103721 : Type'} (x : _103718) (y : _103721) (s : _103718 -> Prop) : term14 _103718 _103721 x y s.
Proof. exact (@lem4334587 _103718 _103721 x y s). Qed.
Lemma lem4334589 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : (term14 _103718 _103721 x y s) = (term15 _103718 _103721 x s y).
Proof. exact (eq_refl (term14 _103718 _103721 x y s)). Qed.
Lemma lem4334590 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : term15 _103718 _103721 x s y.
Proof. exact (EQ_MP (@lem4334589 _103718 _103721 x s y) (@lem4334588 _103718 _103721 x y s)). Qed.
Lemma lem4334591 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : term16 _103718 _103721 x s y t.
Proof. exact (@lem4334590 _103718 _103721 x s y t). Qed.
Lemma lem4334592 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term16 _103718 _103721 x s y t) = ((term17 _103718 _103721 x y s t) = (term18 _103718 _103721 x s y t)).
Proof. exact (eq_refl (term16 _103718 _103721 x s y t)). Qed.
Lemma lem4334594 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term19 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem4334595 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term19 _5106 _5107 P) = ((term20 _5106 _5107 P) = (term21 _5106 _5107 P)).
Proof. exact (eq_refl (term19 _5106 _5107 P)). Qed.
Lemma lem4334597 {A : Type'} (s : A -> Prop) : term22 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem4334598 {A : Type'} (s : A -> Prop) : (term22 A s) = (term23 A s).
Proof. exact (eq_refl (term22 A s)). Qed.
Lemma lem4334599 {A : Type'} (s : A -> Prop) : term23 A s.
Proof. exact (EQ_MP (@lem4334598 A s) (@lem4334597 A s)). Qed.
Lemma lem4334600 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term24 A s t.
Proof. exact (@lem4334599 A s t). Qed.
Lemma lem4334601 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term24 A s t) = ((@SUBSET A s t) = (term25 A s t)).
Proof. exact (eq_refl (term24 A s t)). Qed.
Lemma lem4334612 {A : Type'} (s : A -> Prop) : term26 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4334613 {A : Type'} (s : A -> Prop) : (term26 A s) = (term27 A s).
Proof. exact (eq_refl (term26 A s)). Qed.
Lemma lem4334614 {A : Type'} (s : A -> Prop) : term27 A s.
Proof. exact (EQ_MP (@lem4334613 A s) (@lem4334612 A s)). Qed.
Lemma lem4334615 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term28 A s t.
Proof. exact (@lem4334614 A s t). Qed.
Lemma lem4334616 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term28 A s t) = ((s = t) = (term29 A s t)).
Proof. exact (eq_refl (term28 A s t)). Qed.
Lemma lem4334653 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term25 A s t).
Proof. exact (EQ_MP (@lem4334601 A s t) (@lem4334600 A s t)). Qed.
Lemma lem4334654 {_104190 _104196 : Type'} (s : type1210 _104190 _104196) (t : type1210 _104190 _104196) : (@SUBSET (prod _104190 _104196) s t) = (term30 _104190 _104196 s t).
Proof. exact (@lem4334653 (prod _104190 _104196) s t). Qed.
Lemma lem4334655 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term31 _104190 _104196 s t s' t') = (term32 _104190 _104196 s t s' t').
Proof. exact (@lem4334654 _104190 _104196 (@CROSS _104196 _104190 s t) (@CROSS _104196 _104190 s' t')). Qed.
Lemma lem4334661 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term20 _5106 _5107 P) = (term21 _5106 _5107 P).
Proof. exact (EQ_MP (@lem4334595 _5106 _5107 P) (@lem4334594 _5106 _5107 P)). Qed.
Lemma lem4334662 {_104190 _104196 : Type'} (P : type1210 _104190 _104196) : (term33 _104190 _104196 P) = (term34 _104190 _104196 P).
Proof. exact (@lem4334661 _104196 _104190 P). Qed.
Lemma lem4334663 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term35 _104190 _104196 s t s' t') = (term36 _104190 _104196 s t s' t').
Proof. exact (@lem4334662 _104190 _104196 (term37 _104190 _104196 s t s' t')). Qed.
Lemma lem4334664 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (x : prod _104190 _104196) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term38 _104190 _104196 s t s' t' x) = (term39 _104190 _104196 s t x s' t').
Proof. exact (eq_refl (term38 _104190 _104196 s t s' t' x)). Qed.
Lemma lem4334665 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term40 _104190 _104196 s t s' t') = (term37 _104190 _104196 s t s' t').
Proof. exact (fun_ext (fun x : prod _104190 _104196 => @lem4334664 _104190 _104196 s t x s' t')). Qed.
Lemma lem4334666 {_104190 _104196 : Type'} : (@all (prod _104190 _104196)) = (@all (prod _104190 _104196)).
Proof. exact (eq_refl (@all (prod _104190 _104196))). Qed.
Lemma lem4334667 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term35 _104190 _104196 s t s' t') = (term32 _104190 _104196 s t s' t').
Proof. exact (MK_COMB (@lem4334666 _104190 _104196) (@lem4334665 _104190 _104196 s t s' t')). Qed.
Lemma lem4334668 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4334669 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term41 _104190 _104196 s t s' t') = (term42 _104190 _104196 s t s' t').
Proof. exact (MK_COMB (@lem4334668) (@lem4334667 _104190 _104196 s t s' t')). Qed.
Lemma lem4334670 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (p2 : _104196) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term43 _104190 _104196 s t s' t' p1 p2) = (term44 _104190 _104196 s t p1 p2 s' t').
Proof. exact (eq_refl (term43 _104190 _104196 s t s' t' p1 p2)). Qed.
Lemma lem4334671 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term45 _104190 _104196 s t s' t' p1) = (term46 _104190 _104196 s t p1 s' t').
Proof. exact (fun_ext (fun p2 : _104196 => @lem4334670 _104190 _104196 s t p1 p2 s' t')). Qed.
Lemma lem4334672 {_104196 : Type'} : (@all _104196) = (@all _104196).
Proof. exact (eq_refl (@all _104196)). Qed.
Lemma lem4334673 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term47 _104190 _104196 s t s' t' p1) = (term48 _104190 _104196 s t p1 s' t').
Proof. exact (MK_COMB (@lem4334672 _104196) (@lem4334671 _104190 _104196 s t p1 s' t')). Qed.
Lemma lem4334674 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term49 _104190 _104196 s t s' t') = (term50 _104190 _104196 s t s' t').
Proof. exact (fun_ext (fun p1 : _104190 => @lem4334673 _104190 _104196 s t p1 s' t')). Qed.
Lemma lem4334675 {_104190 : Type'} : (@all _104190) = (@all _104190).
Proof. exact (eq_refl (@all _104190)). Qed.
Lemma lem4334676 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term36 _104190 _104196 s t s' t') = (term51 _104190 _104196 s t s' t').
Proof. exact (MK_COMB (@lem4334675 _104190) (@lem4334674 _104190 _104196 s t s' t')). Qed.
Lemma lem4334677 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : ((term35 _104190 _104196 s t s' t') = (term36 _104190 _104196 s t s' t')) = ((term32 _104190 _104196 s t s' t') = (term51 _104190 _104196 s t s' t')).
Proof. exact (MK_COMB (@lem4334669 _104190 _104196 s t s' t') (@lem4334676 _104190 _104196 s t s' t')). Qed.
Lemma lem4334678 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term32 _104190 _104196 s t s' t') = (term51 _104190 _104196 s t s' t').
Proof. exact (EQ_MP (@lem4334677 _104190 _104196 s t s' t') (@lem4334663 _104190 _104196 s t s' t')). Qed.
Lemma lem4334694 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term52 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4334695 (p : Prop) (q : Prop) (p' : Prop) : term53 p q p'.
Proof. exact (fun q' : Prop => @lem4334694 p q p' q'). Qed.
Lemma lem4334696 (p : Prop) (q : Prop) : term54 p q.
Proof. exact (fun p' : Prop => @lem4334695 p q p'). Qed.
Lemma lem4334697 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (p2 : _104196) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : term55 _104190 _104196 s t p1 p2 s' t'.
Proof. exact (@lem4334696 (term17 _104190 _104196 p1 p2 s t) (term17 _104190 _104196 p1 p2 s' t')). Qed.
Lemma lem4334698 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (p2 : _104196) (s' : _104190 -> Prop) (t' : _104196 -> Prop) (p' : Prop) : term56 _104190 _104196 s t p1 p2 s' t' p'.
Proof. exact (@lem4334697 _104190 _104196 s t p1 p2 s' t' p'). Qed.
Lemma lem4334699 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (p2 : _104196) (s' : _104190 -> Prop) (t' : _104196 -> Prop) (p' : Prop) : (term56 _104190 _104196 s t p1 p2 s' t' p') = (term57 _104190 _104196 s t p1 p2 s' t' p').
Proof. exact (eq_refl (term56 _104190 _104196 s t p1 p2 s' t' p')). Qed.
Lemma lem4334700 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (p2 : _104196) (s' : _104190 -> Prop) (t' : _104196 -> Prop) (p' : Prop) : term57 _104190 _104196 s t p1 p2 s' t' p'.
Proof. exact (EQ_MP (@lem4334699 _104190 _104196 s t p1 p2 s' t' p') (@lem4334698 _104190 _104196 s t p1 p2 s' t' p')). Qed.
Lemma lem4334701 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (p2 : _104196) (s' : _104190 -> Prop) (t' : _104196 -> Prop) (p' : Prop) (q' : Prop) : term58 _104190 _104196 s t p1 p2 s' t' p' q'.
Proof. exact (@lem4334700 _104190 _104196 s t p1 p2 s' t' p' q'). Qed.
Lemma lem4334702 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (p2 : _104196) (s' : _104190 -> Prop) (t' : _104196 -> Prop) (p' : Prop) (q' : Prop) : (term58 _104190 _104196 s t p1 p2 s' t' p' q') = (term59 _104190 _104196 s t p1 p2 s' t' p' q').
Proof. exact (eq_refl (term58 _104190 _104196 s t p1 p2 s' t' p' q')). Qed.
Lemma lem4334703 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (p2 : _104196) (s' : _104190 -> Prop) (t' : _104196 -> Prop) (p' : Prop) (q' : Prop) : term59 _104190 _104196 s t p1 p2 s' t' p' q'.
Proof. exact (EQ_MP (@lem4334702 _104190 _104196 s t p1 p2 s' t' p' q') (@lem4334701 _104190 _104196 s t p1 p2 s' t' p' q')). Qed.
Lemma lem4334705 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term17 _103718 _103721 x y s t) = (term18 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4334592 _103718 _103721 x s y t) (@lem4334591 _103718 _103721 x s y t)). Qed.
Lemma lem4334706 {_104190 _104196 : Type'} (x : _104190) (s : _104190 -> Prop) (y : _104196) (t : _104196 -> Prop) : (term17 _104190 _104196 x y s t) = (term18 _104190 _104196 x s y t).
Proof. exact (@lem4334705 _104190 _104196 x s y t). Qed.
Lemma lem4334707 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (p2 : _104196) (t : _104196 -> Prop) : (term17 _104190 _104196 p1 p2 s t) = (term18 _104190 _104196 p1 s p2 t).
Proof. exact (@lem4334706 _104190 _104196 p1 s p2 t). Qed.
Lemma lem4334710 {_104190 _104196 : Type'} (s' : _104190 -> Prop) (t' : _104196 -> Prop) (p1 : _104190) (s : _104190 -> Prop) (p2 : _104196) (t : _104196 -> Prop) (q' : Prop) : term60 _104190 _104196 s' t' p1 s p2 t q'.
Proof. exact (@lem4334703 _104190 _104196 s t p1 p2 s' t' (term18 _104190 _104196 p1 s p2 t) q'). Qed.
Lemma lem4334711 {_104190 _104196 : Type'} (s' : _104190 -> Prop) (t' : _104196 -> Prop) (p1 : _104190) (s : _104190 -> Prop) (p2 : _104196) (t : _104196 -> Prop) (q' : Prop) : term61 _104190 _104196 s' t' p1 s p2 t q'.
Proof. exact (@lem4334710 _104190 _104196 s' t' p1 s p2 t q' (@lem4334707 _104190 _104196 p1 s p2 t)). Qed.
Lemma lem4334720 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term17 _103718 _103721 x y s t) = (term18 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4334592 _103718 _103721 x s y t) (@lem4334591 _103718 _103721 x s y t)). Qed.
Lemma lem4334721 {_104190 _104196 : Type'} (x : _104190) (s : _104190 -> Prop) (y : _104196) (t : _104196 -> Prop) : (term17 _104190 _104196 x y s t) = (term18 _104190 _104196 x s y t).
Proof. exact (@lem4334720 _104190 _104196 x s y t). Qed.
Lemma lem4334722 {_104190 _104196 : Type'} (p1 : _104190) (s' : _104190 -> Prop) (p2 : _104196) (t' : _104196 -> Prop) : (term17 _104190 _104196 p1 p2 s' t') = (term18 _104190 _104196 p1 s' p2 t').
Proof. exact (@lem4334721 _104190 _104196 p1 s' p2 t'). Qed.
Lemma lem4334725 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (p2 : _104196) (t' : _104196 -> Prop) : term62 _104190 _104196 s t p1 s' p2 t'.
Proof. exact (fun h0 : term18 _104190 _104196 p1 s p2 t => @lem4334722 _104190 _104196 p1 s' p2 t'). Qed.
Lemma lem4334726 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (p2 : _104196) (t' : _104196 -> Prop) : term63 _104190 _104196 s t p1 s' p2 t'.
Proof. exact (@lem4334711 _104190 _104196 s' t' p1 s p2 t (term18 _104190 _104196 p1 s' p2 t')). Qed.
Lemma lem4334727 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (p2 : _104196) (t' : _104196 -> Prop) : (term44 _104190 _104196 s t p1 p2 s' t') = (term64 _104190 _104196 s t p1 s' p2 t').
Proof. exact (@lem4334726 _104190 _104196 s t p1 s' p2 t' (@lem4334725 _104190 _104196 s t p1 s' p2 t')). Qed.
Lemma lem4334763 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term46 _104190 _104196 s t p1 s' t') = (term65 _104190 _104196 s t p1 s' t').
Proof. exact (fun_ext (fun p2 : _104196 => @lem4334727 _104190 _104196 s t p1 s' p2 t')). Qed.
Lemma lem4334799 {_104196 : Type'} : (@all _104196) = (@all _104196).
Proof. exact (eq_refl (@all _104196)). Qed.
Lemma lem4334800 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term48 _104190 _104196 s t p1 s' t') = (term66 _104190 _104196 s t p1 s' t').
Proof. exact (MK_COMB (@lem4334799 _104196) (@lem4334763 _104190 _104196 s t p1 s' t')). Qed.
Lemma lem4334842 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term50 _104190 _104196 s t s' t') = (term67 _104190 _104196 s t s' t').
Proof. exact (fun_ext (fun p1 : _104190 => @lem4334800 _104190 _104196 s t p1 s' t')). Qed.
Lemma lem4334884 {_104190 : Type'} : (@all _104190) = (@all _104190).
Proof. exact (eq_refl (@all _104190)). Qed.
Lemma lem4334885 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term51 _104190 _104196 s t s' t') = (term68 _104190 _104196 s t s' t').
Proof. exact (MK_COMB (@lem4334884 _104190) (@lem4334842 _104190 _104196 s t s' t')). Qed.
Lemma lem4334933 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term32 _104190 _104196 s t s' t') = (term68 _104190 _104196 s t s' t').
Proof. exact (TRANS (@lem4334678 _104190 _104196 s t s' t') (@lem4334885 _104190 _104196 s t s' t')). Qed.
Lemma lem4334934 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term31 _104190 _104196 s t s' t') = (term68 _104190 _104196 s t s' t').
Proof. exact (TRANS (@lem4334655 _104190 _104196 s t s' t') (@lem4334933 _104190 _104196 s t s' t')). Qed.
Lemma lem4334935 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4334936 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term69 _104190 _104196 s t s' t') = (term70 _104190 _104196 s t s' t').
Proof. exact (MK_COMB (@lem4334935) (@lem4334934 _104190 _104196 s t s' t')). Qed.
Lemma lem4334989 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term29 A s t).
Proof. exact (EQ_MP (@lem4334616 A s t) (@lem4334615 A s t)). Qed.
Lemma lem4334990 {_104190 : Type'} (s : _104190 -> Prop) (t : _104190 -> Prop) : (s = t) = (term29 _104190 s t).
Proof. exact (@lem4334989 _104190 s t). Qed.
Lemma lem4334991 {_104190 : Type'} (s : _104190 -> Prop) : (s = (@EMPTY _104190)) = (term71 _104190 s).
Proof. exact (@lem4334990 _104190 s (@EMPTY _104190)). Qed.
Lemma lem4335003 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4334580 A x (@lem4334579 A x)). Qed.
Lemma lem4335004 {_104190 : Type'} (x : _104190) : (@IN _104190 x (@EMPTY _104190)) = False.
Proof. exact (@lem4335003 _104190 x). Qed.
Lemma lem4335005 {_104190 : Type'} (x : _104190) (s : _104190 -> Prop) : (term72 _104190 x s) = (term72 _104190 x s).
Proof. exact (eq_refl (term72 _104190 x s)). Qed.
Lemma lem4335006 {_104190 : Type'} (x : _104190) (s : _104190 -> Prop) : ((@IN _104190 x s) = (@IN _104190 x (@EMPTY _104190))) = ((@IN _104190 x s) = False).
Proof. exact (MK_COMB (@lem4335005 _104190 x s) (@lem4335004 _104190 x)). Qed.
Lemma lem4335008 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4335009 {_104190 : Type'} (x : _104190) (s : _104190 -> Prop) : ((@IN _104190 x s) = False) = (term73 _104190 x s).
Proof. exact (@lem4335008 (@IN _104190 x s)). Qed.
Lemma lem4335010 {_104190 : Type'} (x : _104190) (s : _104190 -> Prop) : ((@IN _104190 x s) = (@IN _104190 x (@EMPTY _104190))) = (term73 _104190 x s).
Proof. exact (TRANS (@lem4335006 _104190 x s) (@lem4335009 _104190 x s)). Qed.
Lemma lem4335011 {_104190 : Type'} (s : _104190 -> Prop) : (term74 _104190 s) = (term75 _104190 s).
Proof. exact (fun_ext (fun x : _104190 => @lem4335010 _104190 x s)). Qed.
Lemma lem4335012 {_104190 : Type'} : (@all _104190) = (@all _104190).
Proof. exact (eq_refl (@all _104190)). Qed.
Lemma lem4335013 {_104190 : Type'} (s : _104190 -> Prop) : (term71 _104190 s) = (term76 _104190 s).
Proof. exact (MK_COMB (@lem4335012 _104190) (@lem4335011 _104190 s)). Qed.
Lemma lem4335020 {_104190 : Type'} (s : _104190 -> Prop) : (s = (@EMPTY _104190)) = (term76 _104190 s).
Proof. exact (TRANS (@lem4334991 _104190 s) (@lem4335013 _104190 s)). Qed.
Lemma lem4335021 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4335022 {_104190 : Type'} (s : _104190 -> Prop) : (term77 _104190 s) = (term78 _104190 s).
Proof. exact (MK_COMB (@lem4335021) (@lem4335020 _104190 s)). Qed.
Lemma lem4335034 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term29 A s t).
Proof. exact (EQ_MP (@lem4334616 A s t) (@lem4334615 A s t)). Qed.
Lemma lem4335035 {_104196 : Type'} (s : _104196 -> Prop) (t : _104196 -> Prop) : (s = t) = (term29 _104196 s t).
Proof. exact (@lem4335034 _104196 s t). Qed.
Lemma lem4335036 {_104196 : Type'} (t : _104196 -> Prop) : (t = (@EMPTY _104196)) = (term71 _104196 t).
Proof. exact (@lem4335035 _104196 t (@EMPTY _104196)). Qed.
Lemma lem4335048 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4334580 A x (@lem4334579 A x)). Qed.
Lemma lem4335049 {_104196 : Type'} (x : _104196) : (@IN _104196 x (@EMPTY _104196)) = False.
Proof. exact (@lem4335048 _104196 x). Qed.
Lemma lem4335050 {_104196 : Type'} (x : _104196) (t : _104196 -> Prop) : (term72 _104196 x t) = (term72 _104196 x t).
Proof. exact (eq_refl (term72 _104196 x t)). Qed.
Lemma lem4335051 {_104196 : Type'} (x : _104196) (t : _104196 -> Prop) : ((@IN _104196 x t) = (@IN _104196 x (@EMPTY _104196))) = ((@IN _104196 x t) = False).
Proof. exact (MK_COMB (@lem4335050 _104196 x t) (@lem4335049 _104196 x)). Qed.
Lemma lem4335053 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4335054 {_104196 : Type'} (x : _104196) (t : _104196 -> Prop) : ((@IN _104196 x t) = False) = (term73 _104196 x t).
Proof. exact (@lem4335053 (@IN _104196 x t)). Qed.
Lemma lem4335055 {_104196 : Type'} (x : _104196) (t : _104196 -> Prop) : ((@IN _104196 x t) = (@IN _104196 x (@EMPTY _104196))) = (term73 _104196 x t).
Proof. exact (TRANS (@lem4335051 _104196 x t) (@lem4335054 _104196 x t)). Qed.
Lemma lem4335056 {_104196 : Type'} (t : _104196 -> Prop) : (term74 _104196 t) = (term75 _104196 t).
Proof. exact (fun_ext (fun x : _104196 => @lem4335055 _104196 x t)). Qed.
Lemma lem4335057 {_104196 : Type'} : (@all _104196) = (@all _104196).
Proof. exact (eq_refl (@all _104196)). Qed.
Lemma lem4335058 {_104196 : Type'} (t : _104196 -> Prop) : (term71 _104196 t) = (term76 _104196 t).
Proof. exact (MK_COMB (@lem4335057 _104196) (@lem4335056 _104196 t)). Qed.
Lemma lem4335065 {_104196 : Type'} (t : _104196 -> Prop) : (t = (@EMPTY _104196)) = (term76 _104196 t).
Proof. exact (TRANS (@lem4335036 _104196 t) (@lem4335058 _104196 t)). Qed.
Lemma lem4335066 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4335067 {_104196 : Type'} (t : _104196 -> Prop) : (term77 _104196 t) = (term78 _104196 t).
Proof. exact (MK_COMB (@lem4335066) (@lem4335065 _104196 t)). Qed.
Lemma lem4335077 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term25 A s t).
Proof. exact (EQ_MP (@lem4334601 A s t) (@lem4334600 A s t)). Qed.
Lemma lem4335078 {_104190 : Type'} (s : _104190 -> Prop) (t : _104190 -> Prop) : (@SUBSET _104190 s t) = (term25 _104190 s t).
Proof. exact (@lem4335077 _104190 s t). Qed.
Lemma lem4335079 {_104190 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) : (@SUBSET _104190 s s') = (term25 _104190 s s').
Proof. exact (@lem4335078 _104190 s s'). Qed.
Lemma lem4335109 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4335110 {_104190 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) : (term79 _104190 s s') = (term80 _104190 s s').
Proof. exact (MK_COMB (@lem4335109) (@lem4335079 _104190 s s')). Qed.
Lemma lem4335141 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term25 A s t).
Proof. exact (EQ_MP (@lem4334601 A s t) (@lem4334600 A s t)). Qed.
Lemma lem4335142 {_104196 : Type'} (s : _104196 -> Prop) (t : _104196 -> Prop) : (@SUBSET _104196 s t) = (term25 _104196 s t).
Proof. exact (@lem4335141 _104196 s t). Qed.
Lemma lem4335143 {_104196 : Type'} (t : _104196 -> Prop) (t' : _104196 -> Prop) : (@SUBSET _104196 t t') = (term25 _104196 t t').
Proof. exact (@lem4335142 _104196 t t'). Qed.
Lemma lem4335173 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term81 _104190 _104196 s s' t t') = (term82 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4335110 _104190 s s') (@lem4335143 _104196 t t')). Qed.
Lemma lem4335234 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term83 _104190 _104196 s s' t t') = (term84 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4335067 _104196 t) (@lem4335173 _104190 _104196 s s' t t')). Qed.
Lemma lem4335303 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term85 _104190 _104196 s s' t t') = (term86 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4335022 _104190 s) (@lem4335234 _104190 _104196 s s' t t')). Qed.
Lemma lem4335380 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : ((term31 _104190 _104196 s t s' t') = (term85 _104190 _104196 s s' t t')) = ((term68 _104190 _104196 s t s' t') = (term86 _104190 _104196 s s' t t')).
Proof. exact (MK_COMB (@lem4334936 _104190 _104196 s t s' t') (@lem4335303 _104190 _104196 s s' t t')). Qed.
Lemma lem4335508 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) : (term87 _104190 _104196 s s' t) = (term88 _104190 _104196 s s' t).
Proof. exact (fun_ext (fun t' : _104196 -> Prop => @lem4335380 _104190 _104196 s s' t t')). Qed.
Lemma lem4335636 {_104196 : Type'} : (@all (_104196 -> Prop)) = (@all (_104196 -> Prop)).
Proof. exact (eq_refl (@all (_104196 -> Prop))). Qed.
Lemma lem4335637 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) : (term89 _104190 _104196 s s' t) = (term90 _104190 _104196 s s' t).
Proof. exact (MK_COMB (@lem4335636 _104196) (@lem4335508 _104190 _104196 s s' t)). Qed.
Lemma lem4335771 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) : (term91 _104190 _104196 s t) = (term92 _104190 _104196 s t).
Proof. exact (fun_ext (fun s' : _104190 -> Prop => @lem4335637 _104190 _104196 s s' t)). Qed.
Lemma lem4335905 {_104190 : Type'} : (@all (_104190 -> Prop)) = (@all (_104190 -> Prop)).
Proof. exact (eq_refl (@all (_104190 -> Prop))). Qed.
Lemma lem4335906 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) : (term93 _104190 _104196 s t) = (term94 _104190 _104196 s t).
Proof. exact (MK_COMB (@lem4335905 _104190) (@lem4335771 _104190 _104196 s t)). Qed.
Lemma lem4336046 {_104190 _104196 : Type'} (s : _104190 -> Prop) : (term95 _104190 _104196 s) = (term96 _104190 _104196 s).
Proof. exact (fun_ext (fun t : _104196 -> Prop => @lem4335906 _104190 _104196 s t)). Qed.
Lemma lem4336186 {_104196 : Type'} : (@all (_104196 -> Prop)) = (@all (_104196 -> Prop)).
Proof. exact (eq_refl (@all (_104196 -> Prop))). Qed.
Lemma lem4336187 {_104190 _104196 : Type'} (s : _104190 -> Prop) : (term97 _104190 _104196 s) = (term98 _104190 _104196 s).
Proof. exact (MK_COMB (@lem4336186 _104196) (@lem4336046 _104190 _104196 s)). Qed.
Lemma lem4336333 {_104190 _104196 : Type'} : (term99 _104190 _104196) = (term100 _104190 _104196).
Proof. exact (fun_ext (fun s : _104190 -> Prop => @lem4336187 _104190 _104196 s)). Qed.
Lemma lem4336479 {_104190 : Type'} : (@all (_104190 -> Prop)) = (@all (_104190 -> Prop)).
Proof. exact (eq_refl (@all (_104190 -> Prop))). Qed.
Lemma lem4336480 {_104190 _104196 : Type'} : (term101 _104190 _104196) = (term102 _104190 _104196).
Proof. exact (MK_COMB (@lem4336479 _104190) (@lem4336333 _104190 _104196)). Qed.
Lemma lem4336632 {_104190 _104196 : Type'} : (term102 _104190 _104196) = (term101 _104190 _104196).
Proof. exact (SYM (@lem4336480 _104190 _104196)). Qed.
Lemma lem4336634 (p : Prop) : p = (term103 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4336635 {_104190 _104196 : Type'} : (term102 _104190 _104196) = (term104 _104190 _104196).
Proof. exact (@lem4336634 (term102 _104190 _104196)). Qed.
Lemma lem4336636 {_104190 _104196 : Type'} : (term104 _104190 _104196) = (term102 _104190 _104196).
Proof. exact (SYM (@lem4336635 _104190 _104196)). Qed.
Lemma lem4336637 {_104190 _104196 : Type'} (h1 : term105 _104190 _104196) : term105 _104190 _104196.
Proof. exact (h1). Qed.
Lemma lem4336640 {_104190 _104196 : Type'} (h1 : term104 _104190 _104196) : term104 _104190 _104196.
Proof. exact (h1). Qed.
Lemma lem4336641 {_104190 _104196 : Type'} : term106 _104190 _104196.
Proof. exact (fun h0 : term104 _104190 _104196 => @lem4336640 _104190 _104196 h0). Qed.
Lemma lem4336642 {_104190 _104196 : Type'} (h1 : term106 _104190 _104196) : term106 _104190 _104196.
Proof. exact (h1). Qed.
Lemma lem4336643 {_104190 _104196 : Type'} (h1 : term104 _104190 _104196) : term104 _104190 _104196.
Proof. exact (h1). Qed.
Lemma lem4336644 {_104190 _104196 : Type'} (h1 : term104 _104190 _104196) (h2 : term106 _104190 _104196) : term104 _104190 _104196.
Proof. exact (@lem4336642 _104190 _104196 h2 (@lem4336643 _104190 _104196 h1)). Qed.
Lemma lem4336645 {_104190 _104196 : Type'} (h1 : term104 _104190 _104196) : term107 _104190 _104196.
Proof. exact (fun h0 : term106 _104190 _104196 => @lem4336644 _104190 _104196 h1 h0). Qed.
Lemma lem4336646 {_104190 _104196 : Type'} (h1 : term106 _104190 _104196) : term106 _104190 _104196.
Proof. exact (h1). Qed.
Lemma lem4336647 {_104190 _104196 : Type'} (h1 : term104 _104190 _104196) (h2 : term106 _104190 _104196) : term104 _104190 _104196.
Proof. exact (@lem4336645 _104190 _104196 h1 (@lem4336646 _104190 _104196 h2)). Qed.
Lemma lem4336648 {_104190 _104196 : Type'} (h1 : term106 _104190 _104196) : term106 _104190 _104196.
Proof. exact (fun h0 : term104 _104190 _104196 => @lem4336647 _104190 _104196 h0 h1). Qed.
Lemma lem4336649 {_104190 _104196 : Type'} : term108 _104190 _104196.
Proof. exact (fun h0 : term106 _104190 _104196 => @lem4336648 _104190 _104196 h0). Qed.
Lemma lem4336652 {_104190 _104196 : Type'} : term106 _104190 _104196.
Proof. exact (@lem4336649 _104190 _104196 (@lem4336641 _104190 _104196)). Qed.
Lemma lem4336653 {_104190 _104196 : Type'} : term106 _104190 _104196.
Proof. exact (@lem4336652 _104190 _104196). Qed.
Lemma lem4336655 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4336656 {_104190 _104196 : Type'} : (term104 _104190 _104196) = (term109 _104190 _104196).
Proof. exact (@lem4336655 (term105 _104190 _104196)). Qed.
Lemma lem4336658 (t : Prop) : (term110 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4336659 {_104190 _104196 : Type'} : (term109 _104190 _104196) = (term102 _104190 _104196).
Proof. exact (@lem4336658 (term102 _104190 _104196)). Qed.
Lemma lem4336720 {_104190 _104196 : Type'} : (term104 _104190 _104196) = (term102 _104190 _104196).
Proof. exact (TRANS (@lem4336656 _104190 _104196) (@lem4336659 _104190 _104196)). Qed.
Lemma lem4336725 {_104196 : Type'} (t : _104196 -> Prop) (x : _104196) (t' : _104196 -> Prop) : (term111 _104196 t x t') = (term111 _104196 t x t').
Proof. exact (eq_refl (term111 _104196 t x t')). Qed.
Lemma lem4336726 {_104196 : Type'} (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term112 _104196 t t') = (term112 _104196 t t').
Proof. exact (fun_ext (fun x : _104196 => @lem4336725 _104196 t x t')). Qed.
Lemma lem4336727 {_104196 : Type'} : (@all _104196) = (@all _104196).
Proof. exact (eq_refl (@all _104196)). Qed.
Lemma lem4336728 {_104196 : Type'} (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term25 _104196 t t') = (term25 _104196 t t').
Proof. exact (MK_COMB (@lem4336727 _104196) (@lem4336726 _104196 t t')). Qed.
Lemma lem4336733 {_104190 : Type'} (s : _104190 -> Prop) (x : _104190) (s' : _104190 -> Prop) : (term111 _104190 s x s') = (term111 _104190 s x s').
Proof. exact (eq_refl (term111 _104190 s x s')). Qed.
Lemma lem4336734 {_104190 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) : (term112 _104190 s s') = (term112 _104190 s s').
Proof. exact (fun_ext (fun x : _104190 => @lem4336733 _104190 s x s')). Qed.
Lemma lem4336735 {_104190 : Type'} : (@all _104190) = (@all _104190).
Proof. exact (eq_refl (@all _104190)). Qed.
Lemma lem4336736 {_104190 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) : (term25 _104190 s s') = (term25 _104190 s s').
Proof. exact (MK_COMB (@lem4336735 _104190) (@lem4336734 _104190 s s')). Qed.
Lemma lem4336737 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4336738 {_104190 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) : (term80 _104190 s s') = (term80 _104190 s s').
Proof. exact (MK_COMB (@lem4336737) (@lem4336736 _104190 s s')). Qed.
Lemma lem4336739 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term82 _104190 _104196 s s' t t') = (term82 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4336738 _104190 s s') (@lem4336728 _104196 t t')). Qed.
Lemma lem4336742 {_104196 : Type'} (x : _104196) (t : _104196 -> Prop) : (term73 _104196 x t) = (term73 _104196 x t).
Proof. exact (eq_refl (term73 _104196 x t)). Qed.
Lemma lem4336743 {_104196 : Type'} (t : _104196 -> Prop) : (term75 _104196 t) = (term75 _104196 t).
Proof. exact (fun_ext (fun x : _104196 => @lem4336742 _104196 x t)). Qed.
Lemma lem4336744 {_104196 : Type'} : (@all _104196) = (@all _104196).
Proof. exact (eq_refl (@all _104196)). Qed.
Lemma lem4336745 {_104196 : Type'} (t : _104196 -> Prop) : (term76 _104196 t) = (term76 _104196 t).
Proof. exact (MK_COMB (@lem4336744 _104196) (@lem4336743 _104196 t)). Qed.
Lemma lem4336746 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4336747 {_104196 : Type'} (t : _104196 -> Prop) : (term78 _104196 t) = (term78 _104196 t).
Proof. exact (MK_COMB (@lem4336746) (@lem4336745 _104196 t)). Qed.
Lemma lem4336748 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term84 _104190 _104196 s s' t t') = (term84 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4336747 _104196 t) (@lem4336739 _104190 _104196 s s' t t')). Qed.
Lemma lem4336751 {_104190 : Type'} (x : _104190) (s : _104190 -> Prop) : (term73 _104190 x s) = (term73 _104190 x s).
Proof. exact (eq_refl (term73 _104190 x s)). Qed.
Lemma lem4336752 {_104190 : Type'} (s : _104190 -> Prop) : (term75 _104190 s) = (term75 _104190 s).
Proof. exact (fun_ext (fun x : _104190 => @lem4336751 _104190 x s)). Qed.
Lemma lem4336753 {_104190 : Type'} : (@all _104190) = (@all _104190).
Proof. exact (eq_refl (@all _104190)). Qed.
Lemma lem4336754 {_104190 : Type'} (s : _104190 -> Prop) : (term76 _104190 s) = (term76 _104190 s).
Proof. exact (MK_COMB (@lem4336753 _104190) (@lem4336752 _104190 s)). Qed.
Lemma lem4336755 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4336756 {_104190 : Type'} (s : _104190 -> Prop) : (term78 _104190 s) = (term78 _104190 s).
Proof. exact (MK_COMB (@lem4336755) (@lem4336754 _104190 s)). Qed.
Lemma lem4336757 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term86 _104190 _104196 s s' t t') = (term86 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4336756 _104190 s) (@lem4336748 _104190 _104196 s s' t t')). Qed.
Lemma lem4336770 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (p2 : _104196) (t' : _104196 -> Prop) : (term64 _104190 _104196 s t p1 s' p2 t') = (term64 _104190 _104196 s t p1 s' p2 t').
Proof. exact (eq_refl (term64 _104190 _104196 s t p1 s' p2 t')). Qed.
Lemma lem4336771 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term65 _104190 _104196 s t p1 s' t') = (term65 _104190 _104196 s t p1 s' t').
Proof. exact (fun_ext (fun p2 : _104196 => @lem4336770 _104190 _104196 s t p1 s' p2 t')). Qed.
Lemma lem4336772 {_104196 : Type'} : (@all _104196) = (@all _104196).
Proof. exact (eq_refl (@all _104196)). Qed.
Lemma lem4336773 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term66 _104190 _104196 s t p1 s' t') = (term66 _104190 _104196 s t p1 s' t').
Proof. exact (MK_COMB (@lem4336772 _104196) (@lem4336771 _104190 _104196 s t p1 s' t')). Qed.
Lemma lem4336774 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term67 _104190 _104196 s t s' t') = (term67 _104190 _104196 s t s' t').
Proof. exact (fun_ext (fun p1 : _104190 => @lem4336773 _104190 _104196 s t p1 s' t')). Qed.
Lemma lem4336775 {_104190 : Type'} : (@all _104190) = (@all _104190).
Proof. exact (eq_refl (@all _104190)). Qed.
Lemma lem4336776 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term68 _104190 _104196 s t s' t') = (term68 _104190 _104196 s t s' t').
Proof. exact (MK_COMB (@lem4336775 _104190) (@lem4336774 _104190 _104196 s t s' t')). Qed.
Lemma lem4336777 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4336778 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term70 _104190 _104196 s t s' t') = (term70 _104190 _104196 s t s' t').
Proof. exact (MK_COMB (@lem4336777) (@lem4336776 _104190 _104196 s t s' t')). Qed.
Lemma lem4336779 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : ((term68 _104190 _104196 s t s' t') = (term86 _104190 _104196 s s' t t')) = ((term68 _104190 _104196 s t s' t') = (term86 _104190 _104196 s s' t t')).
Proof. exact (MK_COMB (@lem4336778 _104190 _104196 s t s' t') (@lem4336757 _104190 _104196 s s' t t')). Qed.
Lemma lem4336780 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) : (term88 _104190 _104196 s s' t) = (term88 _104190 _104196 s s' t).
Proof. exact (fun_ext (fun t' : _104196 -> Prop => @lem4336779 _104190 _104196 s s' t t')). Qed.
Lemma lem4336781 {_104196 : Type'} : (@all (_104196 -> Prop)) = (@all (_104196 -> Prop)).
Proof. exact (eq_refl (@all (_104196 -> Prop))). Qed.
Lemma lem4336782 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) : (term90 _104190 _104196 s s' t) = (term90 _104190 _104196 s s' t).
Proof. exact (MK_COMB (@lem4336781 _104196) (@lem4336780 _104190 _104196 s s' t)). Qed.
Lemma lem4336783 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) : (term92 _104190 _104196 s t) = (term92 _104190 _104196 s t).
Proof. exact (fun_ext (fun s' : _104190 -> Prop => @lem4336782 _104190 _104196 s s' t)). Qed.
Lemma lem4336784 {_104190 : Type'} : (@all (_104190 -> Prop)) = (@all (_104190 -> Prop)).
Proof. exact (eq_refl (@all (_104190 -> Prop))). Qed.
Lemma lem4336785 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) : (term94 _104190 _104196 s t) = (term94 _104190 _104196 s t).
Proof. exact (MK_COMB (@lem4336784 _104190) (@lem4336783 _104190 _104196 s t)). Qed.
Lemma lem4336786 {_104190 _104196 : Type'} (s : _104190 -> Prop) : (term96 _104190 _104196 s) = (term96 _104190 _104196 s).
Proof. exact (fun_ext (fun t : _104196 -> Prop => @lem4336785 _104190 _104196 s t)). Qed.
Lemma lem4336787 {_104196 : Type'} : (@all (_104196 -> Prop)) = (@all (_104196 -> Prop)).
Proof. exact (eq_refl (@all (_104196 -> Prop))). Qed.
Lemma lem4336788 {_104190 _104196 : Type'} (s : _104190 -> Prop) : (term98 _104190 _104196 s) = (term98 _104190 _104196 s).
Proof. exact (MK_COMB (@lem4336787 _104196) (@lem4336786 _104190 _104196 s)). Qed.
Lemma lem4336789 {_104190 _104196 : Type'} : (term100 _104190 _104196) = (term100 _104190 _104196).
Proof. exact (fun_ext (fun s : _104190 -> Prop => @lem4336788 _104190 _104196 s)). Qed.
Lemma lem4336790 {_104190 : Type'} : (@all (_104190 -> Prop)) = (@all (_104190 -> Prop)).
Proof. exact (eq_refl (@all (_104190 -> Prop))). Qed.
Lemma lem4336791 {_104190 _104196 : Type'} : (term102 _104190 _104196) = (term102 _104190 _104196).
Proof. exact (MK_COMB (@lem4336790 _104190) (@lem4336789 _104190 _104196)). Qed.
Lemma lem4336870 {_104190 _104196 : Type'} : (term104 _104190 _104196) = (term102 _104190 _104196).
Proof. exact (TRANS (@lem4336720 _104190 _104196) (@lem4336791 _104190 _104196)). Qed.
Lemma lem4336871 {_104190 _104196 : Type'} : (term102 _104190 _104196) = (term104 _104190 _104196).
Proof. exact (SYM (@lem4336870 _104190 _104196)). Qed.
Lemma lem4336873 (p : Prop) : p = (term103 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4336874 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : ((term68 _104190 _104196 s t s' t') = (term86 _104190 _104196 s s' t t')) = (term113 _104190 _104196 s s' t t').
Proof. exact (@lem4336873 ((term68 _104190 _104196 s t s' t') = (term86 _104190 _104196 s s' t t'))). Qed.
Lemma lem4336875 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term113 _104190 _104196 s s' t t') = ((term68 _104190 _104196 s t s' t') = (term86 _104190 _104196 s s' t t')).
Proof. exact (SYM (@lem4336874 _104190 _104196 s s' t t')). Qed.
Lemma lem4336876 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term114 _104190 _104196 s s' t t') : term114 _104190 _104196 s s' t t'.
Proof. exact (h1). Qed.
Lemma lem4336885 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (p2 : _104196) (t : _104196 -> Prop) : (term115 _104190 _104196 p1 s p2 t) = (term116 _104190 _104196 p1 s p2 t).
Proof. exact (@lem17045 (@IN _104190 p1 s) (@IN _104196 p2 t)). Qed.
Lemma lem4336897 {_104190 _104196 : Type'} (p1 : _104190) (s' : _104190 -> Prop) (p2 : _104196) (t' : _104196 -> Prop) : (term115 _104190 _104196 p1 s' p2 t') = (term116 _104190 _104196 p1 s' p2 t').
Proof. exact (@lem17045 (@IN _104190 p1 s') (@IN _104196 p2 t')). Qed.
Lemma lem4336900 {_104190 _104196 : Type'} (p1 : _104190) (s' : _104190 -> Prop) (p2 : _104196) (t' : _104196 -> Prop) : (term18 _104190 _104196 p1 s' p2 t') = (term18 _104190 _104196 p1 s' p2 t').
Proof. exact (eq_refl (term18 _104190 _104196 p1 s' p2 t')). Qed.
Lemma lem4336902 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (p2 : _104196) (t : _104196 -> Prop) : (term117 _104190 _104196 p1 s p2 t) = (term117 _104190 _104196 p1 s p2 t).
Proof. exact (eq_refl (term117 _104190 _104196 p1 s p2 t)). Qed.
Lemma lem4336903 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (p2 : _104196) (t' : _104196 -> Prop) : (term118 _104190 _104196 s t p1 s' p2 t') = (term119 _104190 _104196 s t p1 s' p2 t').
Proof. exact (MK_COMB (@lem4336902 _104190 _104196 p1 s p2 t) (@lem4336897 _104190 _104196 p1 s' p2 t')). Qed.
Lemma lem4336904 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (p2 : _104196) (t' : _104196 -> Prop) : (term120 _104190 _104196 s t p1 s' p2 t') = (term118 _104190 _104196 s t p1 s' p2 t').
Proof. exact (@lem17362 (term18 _104190 _104196 p1 s p2 t) (term18 _104190 _104196 p1 s' p2 t')). Qed.
Lemma lem4336905 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (p2 : _104196) (t' : _104196 -> Prop) : (term120 _104190 _104196 s t p1 s' p2 t') = (term119 _104190 _104196 s t p1 s' p2 t').
Proof. exact (TRANS (@lem4336904 _104190 _104196 s t p1 s' p2 t') (@lem4336903 _104190 _104196 s t p1 s' p2 t')). Qed.
Lemma lem4336906 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4336907 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (p2 : _104196) (t : _104196 -> Prop) : (term121 _104190 _104196 p1 s p2 t) = (term122 _104190 _104196 p1 s p2 t).
Proof. exact (MK_COMB (@lem4336906) (@lem4336885 _104190 _104196 p1 s p2 t)). Qed.
Lemma lem4336908 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (p2 : _104196) (t' : _104196 -> Prop) : (term123 _104190 _104196 s t p1 s' p2 t') = (term124 _104190 _104196 s t p1 s' p2 t').
Proof. exact (MK_COMB (@lem4336907 _104190 _104196 p1 s p2 t) (@lem4336900 _104190 _104196 p1 s' p2 t')). Qed.
Lemma lem4336909 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (p2 : _104196) (t' : _104196 -> Prop) : (term64 _104190 _104196 s t p1 s' p2 t') = (term123 _104190 _104196 s t p1 s' p2 t').
Proof. exact (@lem17265 (term18 _104190 _104196 p1 s p2 t) (term18 _104190 _104196 p1 s' p2 t')). Qed.
Lemma lem4336910 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (p2 : _104196) (t' : _104196 -> Prop) : (term64 _104190 _104196 s t p1 s' p2 t') = (term124 _104190 _104196 s t p1 s' p2 t').
Proof. exact (TRANS (@lem4336909 _104190 _104196 s t p1 s' p2 t') (@lem4336908 _104190 _104196 s t p1 s' p2 t')). Qed.
Lemma lem4336911 {_104196 : Type'} (P : _104196 -> Prop) : (term125 _104196 P) = (term126 _104196 P).
Proof. exact (@lem18392 _104196 P). Qed.
Lemma lem4336912 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term127 _104190 _104196 s t p1 s' t') = (term128 _104190 _104196 s t p1 s' t').
Proof. exact (@lem4336911 _104196 (term65 _104190 _104196 s t p1 s' t')). Qed.
Lemma lem4336913 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (p2 : _104196) (t' : _104196 -> Prop) : (term129 _104190 _104196 s t p1 s' t' p2) = (term64 _104190 _104196 s t p1 s' p2 t').
Proof. exact (eq_refl (term129 _104190 _104196 s t p1 s' t' p2)). Qed.
Lemma lem4336914 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4336915 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (p2 : _104196) (t' : _104196 -> Prop) : (term130 _104190 _104196 s t p1 s' t' p2) = (term120 _104190 _104196 s t p1 s' p2 t').
Proof. exact (MK_COMB (@lem4336914) (@lem4336913 _104190 _104196 s t p1 s' p2 t')). Qed.
Lemma lem4336916 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (p2 : _104196) (t' : _104196 -> Prop) : (term130 _104190 _104196 s t p1 s' t' p2) = (term119 _104190 _104196 s t p1 s' p2 t').
Proof. exact (TRANS (@lem4336915 _104190 _104196 s t p1 s' p2 t') (@lem4336905 _104190 _104196 s t p1 s' p2 t')). Qed.
Lemma lem4336917 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term131 _104190 _104196 s t p1 s' t') = (term132 _104190 _104196 s t p1 s' t').
Proof. exact (fun_ext (fun p2 : _104196 => @lem4336916 _104190 _104196 s t p1 s' p2 t')). Qed.
Lemma lem4336918 {_104196 : Type'} : (@ex _104196) = (@ex _104196).
Proof. exact (eq_refl (@ex _104196)). Qed.
Lemma lem4336919 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term128 _104190 _104196 s t p1 s' t') = (term133 _104190 _104196 s t p1 s' t').
Proof. exact (MK_COMB (@lem4336918 _104196) (@lem4336917 _104190 _104196 s t p1 s' t')). Qed.
Lemma lem4336920 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term127 _104190 _104196 s t p1 s' t') = (term133 _104190 _104196 s t p1 s' t').
Proof. exact (TRANS (@lem4336912 _104190 _104196 s t p1 s' t') (@lem4336919 _104190 _104196 s t p1 s' t')). Qed.
Lemma lem4336921 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term65 _104190 _104196 s t p1 s' t') = (term134 _104190 _104196 s t p1 s' t').
Proof. exact (fun_ext (fun p2 : _104196 => @lem4336910 _104190 _104196 s t p1 s' p2 t')). Qed.
Lemma lem4336922 {_104196 : Type'} : (@all _104196) = (@all _104196).
Proof. exact (eq_refl (@all _104196)). Qed.
Lemma lem4336923 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term66 _104190 _104196 s t p1 s' t') = (term135 _104190 _104196 s t p1 s' t').
Proof. exact (MK_COMB (@lem4336922 _104196) (@lem4336921 _104190 _104196 s t p1 s' t')). Qed.
Lemma lem4336924 {_104190 : Type'} (P : _104190 -> Prop) : (term125 _104190 P) = (term126 _104190 P).
Proof. exact (@lem18392 _104190 P). Qed.
Lemma lem4336925 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term136 _104190 _104196 s t s' t') = (term137 _104190 _104196 s t s' t').
Proof. exact (@lem4336924 _104190 (term67 _104190 _104196 s t s' t')). Qed.
Lemma lem4336926 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term138 _104190 _104196 s t s' t' p1) = (term66 _104190 _104196 s t p1 s' t').
Proof. exact (eq_refl (term138 _104190 _104196 s t s' t' p1)). Qed.
Lemma lem4336927 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4336928 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term139 _104190 _104196 s t s' t' p1) = (term127 _104190 _104196 s t p1 s' t').
Proof. exact (MK_COMB (@lem4336927) (@lem4336926 _104190 _104196 s t p1 s' t')). Qed.
Lemma lem4336929 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term139 _104190 _104196 s t s' t' p1) = (term133 _104190 _104196 s t p1 s' t').
Proof. exact (TRANS (@lem4336928 _104190 _104196 s t p1 s' t') (@lem4336920 _104190 _104196 s t p1 s' t')). Qed.
Lemma lem4336930 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term140 _104190 _104196 s t s' t') = (term141 _104190 _104196 s t s' t').
Proof. exact (fun_ext (fun p1 : _104190 => @lem4336929 _104190 _104196 s t p1 s' t')). Qed.
Lemma lem4336931 {_104190 : Type'} : (@ex _104190) = (@ex _104190).
Proof. exact (eq_refl (@ex _104190)). Qed.
Lemma lem4336932 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term137 _104190 _104196 s t s' t') = (term142 _104190 _104196 s t s' t').
Proof. exact (MK_COMB (@lem4336931 _104190) (@lem4336930 _104190 _104196 s t s' t')). Qed.
Lemma lem4336933 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term136 _104190 _104196 s t s' t') = (term142 _104190 _104196 s t s' t').
Proof. exact (TRANS (@lem4336925 _104190 _104196 s t s' t') (@lem4336932 _104190 _104196 s t s' t')). Qed.
Lemma lem4336934 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term67 _104190 _104196 s t s' t') = (term143 _104190 _104196 s t s' t').
Proof. exact (fun_ext (fun p1 : _104190 => @lem4336923 _104190 _104196 s t p1 s' t')). Qed.
Lemma lem4336935 {_104190 : Type'} : (@all _104190) = (@all _104190).
Proof. exact (eq_refl (@all _104190)). Qed.
Lemma lem4336936 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term68 _104190 _104196 s t s' t') = (term144 _104190 _104196 s t s' t').
Proof. exact (MK_COMB (@lem4336935 _104190) (@lem4336934 _104190 _104196 s t s' t')). Qed.
Lemma lem4336937 {_104190 : Type'} (x : _104190) (s : _104190 -> Prop) : (term73 _104190 x s) = (term73 _104190 x s).
Proof. exact (eq_refl (term73 _104190 x s)). Qed.
Lemma lem4336940 {_104190 : Type'} (x : _104190) (s : _104190 -> Prop) : (term145 _104190 x s) = (@IN _104190 x s).
Proof. exact (@lem16933 (@IN _104190 x s)). Qed.
Lemma lem4336941 {_104190 : Type'} (P : _104190 -> Prop) : (term125 _104190 P) = (term126 _104190 P).
Proof. exact (@lem18392 _104190 P). Qed.
Lemma lem4336942 {_104190 : Type'} (s : _104190 -> Prop) : (term146 _104190 s) = (term147 _104190 s).
Proof. exact (@lem4336941 _104190 (term75 _104190 s)). Qed.
Lemma lem4336943 {_104190 : Type'} (x : _104190) (s : _104190 -> Prop) : (term148 _104190 s x) = (term73 _104190 x s).
Proof. exact (eq_refl (term148 _104190 s x)). Qed.
Lemma lem4336944 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4336945 {_104190 : Type'} (x : _104190) (s : _104190 -> Prop) : (term149 _104190 s x) = (term145 _104190 x s).
Proof. exact (MK_COMB (@lem4336944) (@lem4336943 _104190 x s)). Qed.
Lemma lem4336946 {_104190 : Type'} (x : _104190) (s : _104190 -> Prop) : (term149 _104190 s x) = (@IN _104190 x s).
Proof. exact (TRANS (@lem4336945 _104190 x s) (@lem4336940 _104190 x s)). Qed.
Lemma lem4336947 {_104190 : Type'} (s : _104190 -> Prop) : (term150 _104190 s) = (term151 _104190 s).
Proof. exact (fun_ext (fun x : _104190 => @lem4336946 _104190 x s)). Qed.
Lemma lem4336948 {_104190 : Type'} : (@ex _104190) = (@ex _104190).
Proof. exact (eq_refl (@ex _104190)). Qed.
Lemma lem4336949 {_104190 : Type'} (s : _104190 -> Prop) : (term147 _104190 s) = (term152 _104190 s).
Proof. exact (MK_COMB (@lem4336948 _104190) (@lem4336947 _104190 s)). Qed.
Lemma lem4336950 {_104190 : Type'} (s : _104190 -> Prop) : (term146 _104190 s) = (term152 _104190 s).
Proof. exact (TRANS (@lem4336942 _104190 s) (@lem4336949 _104190 s)). Qed.
Lemma lem4336951 {_104190 : Type'} (s : _104190 -> Prop) : (term75 _104190 s) = (term75 _104190 s).
Proof. exact (fun_ext (fun x : _104190 => @lem4336937 _104190 x s)). Qed.
Lemma lem4336952 {_104190 : Type'} : (@all _104190) = (@all _104190).
Proof. exact (eq_refl (@all _104190)). Qed.
Lemma lem4336953 {_104190 : Type'} (s : _104190 -> Prop) : (term76 _104190 s) = (term76 _104190 s).
Proof. exact (MK_COMB (@lem4336952 _104190) (@lem4336951 _104190 s)). Qed.
Lemma lem4336954 {_104196 : Type'} (x : _104196) (t : _104196 -> Prop) : (term73 _104196 x t) = (term73 _104196 x t).
Proof. exact (eq_refl (term73 _104196 x t)). Qed.
Lemma lem4336957 {_104196 : Type'} (x : _104196) (t : _104196 -> Prop) : (term145 _104196 x t) = (@IN _104196 x t).
Proof. exact (@lem16933 (@IN _104196 x t)). Qed.
Lemma lem4336958 {_104196 : Type'} (P : _104196 -> Prop) : (term125 _104196 P) = (term126 _104196 P).
Proof. exact (@lem18392 _104196 P). Qed.
Lemma lem4336959 {_104196 : Type'} (t : _104196 -> Prop) : (term146 _104196 t) = (term147 _104196 t).
Proof. exact (@lem4336958 _104196 (term75 _104196 t)). Qed.
Lemma lem4336960 {_104196 : Type'} (x : _104196) (t : _104196 -> Prop) : (term148 _104196 t x) = (term73 _104196 x t).
Proof. exact (eq_refl (term148 _104196 t x)). Qed.
Lemma lem4336961 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4336962 {_104196 : Type'} (x : _104196) (t : _104196 -> Prop) : (term149 _104196 t x) = (term145 _104196 x t).
Proof. exact (MK_COMB (@lem4336961) (@lem4336960 _104196 x t)). Qed.
Lemma lem4336963 {_104196 : Type'} (x : _104196) (t : _104196 -> Prop) : (term149 _104196 t x) = (@IN _104196 x t).
Proof. exact (TRANS (@lem4336962 _104196 x t) (@lem4336957 _104196 x t)). Qed.
Lemma lem4336964 {_104196 : Type'} (t : _104196 -> Prop) : (term150 _104196 t) = (term151 _104196 t).
Proof. exact (fun_ext (fun x : _104196 => @lem4336963 _104196 x t)). Qed.
Lemma lem4336965 {_104196 : Type'} : (@ex _104196) = (@ex _104196).
Proof. exact (eq_refl (@ex _104196)). Qed.
Lemma lem4336966 {_104196 : Type'} (t : _104196 -> Prop) : (term147 _104196 t) = (term152 _104196 t).
Proof. exact (MK_COMB (@lem4336965 _104196) (@lem4336964 _104196 t)). Qed.
Lemma lem4336967 {_104196 : Type'} (t : _104196 -> Prop) : (term146 _104196 t) = (term152 _104196 t).
Proof. exact (TRANS (@lem4336959 _104196 t) (@lem4336966 _104196 t)). Qed.
Lemma lem4336968 {_104196 : Type'} (t : _104196 -> Prop) : (term75 _104196 t) = (term75 _104196 t).
Proof. exact (fun_ext (fun x : _104196 => @lem4336954 _104196 x t)). Qed.
Lemma lem4336969 {_104196 : Type'} : (@all _104196) = (@all _104196).
Proof. exact (eq_refl (@all _104196)). Qed.
Lemma lem4336970 {_104196 : Type'} (t : _104196 -> Prop) : (term76 _104196 t) = (term76 _104196 t).
Proof. exact (MK_COMB (@lem4336969 _104196) (@lem4336968 _104196 t)). Qed.
Lemma lem4336979 {_104190 : Type'} (s : _104190 -> Prop) (x : _104190) (s' : _104190 -> Prop) : (term153 _104190 s x s') = (term154 _104190 s x s').
Proof. exact (@lem17362 (@IN _104190 x s) (@IN _104190 x s')). Qed.
Lemma lem4336984 {_104190 : Type'} (s : _104190 -> Prop) (x : _104190) (s' : _104190 -> Prop) : (term111 _104190 s x s') = (term155 _104190 s x s').
Proof. exact (@lem17265 (@IN _104190 x s) (@IN _104190 x s')). Qed.
Lemma lem4336985 {_104190 : Type'} (P : _104190 -> Prop) : (term125 _104190 P) = (term126 _104190 P).
Proof. exact (@lem18392 _104190 P). Qed.
Lemma lem4336986 {_104190 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) : (term156 _104190 s s') = (term157 _104190 s s').
Proof. exact (@lem4336985 _104190 (term112 _104190 s s')). Qed.
Lemma lem4336987 {_104190 : Type'} (s : _104190 -> Prop) (x : _104190) (s' : _104190 -> Prop) : (term158 _104190 s s' x) = (term111 _104190 s x s').
Proof. exact (eq_refl (term158 _104190 s s' x)). Qed.
Lemma lem4336988 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4336989 {_104190 : Type'} (s : _104190 -> Prop) (x : _104190) (s' : _104190 -> Prop) : (term159 _104190 s s' x) = (term153 _104190 s x s').
Proof. exact (MK_COMB (@lem4336988) (@lem4336987 _104190 s x s')). Qed.
Lemma lem4336990 {_104190 : Type'} (s : _104190 -> Prop) (x : _104190) (s' : _104190 -> Prop) : (term159 _104190 s s' x) = (term154 _104190 s x s').
Proof. exact (TRANS (@lem4336989 _104190 s x s') (@lem4336979 _104190 s x s')). Qed.
Lemma lem4336991 {_104190 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) : (term160 _104190 s s') = (term161 _104190 s s').
Proof. exact (fun_ext (fun x : _104190 => @lem4336990 _104190 s x s')). Qed.
Lemma lem4336992 {_104190 : Type'} : (@ex _104190) = (@ex _104190).
Proof. exact (eq_refl (@ex _104190)). Qed.
Lemma lem4336993 {_104190 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) : (term157 _104190 s s') = (term162 _104190 s s').
Proof. exact (MK_COMB (@lem4336992 _104190) (@lem4336991 _104190 s s')). Qed.
Lemma lem4336994 {_104190 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) : (term156 _104190 s s') = (term162 _104190 s s').
Proof. exact (TRANS (@lem4336986 _104190 s s') (@lem4336993 _104190 s s')). Qed.
Lemma lem4336995 {_104190 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) : (term112 _104190 s s') = (term163 _104190 s s').
Proof. exact (fun_ext (fun x : _104190 => @lem4336984 _104190 s x s')). Qed.
Lemma lem4336996 {_104190 : Type'} : (@all _104190) = (@all _104190).
Proof. exact (eq_refl (@all _104190)). Qed.
Lemma lem4336997 {_104190 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) : (term25 _104190 s s') = (term164 _104190 s s').
Proof. exact (MK_COMB (@lem4336996 _104190) (@lem4336995 _104190 s s')). Qed.
Lemma lem4337006 {_104196 : Type'} (t : _104196 -> Prop) (x : _104196) (t' : _104196 -> Prop) : (term153 _104196 t x t') = (term154 _104196 t x t').
Proof. exact (@lem17362 (@IN _104196 x t) (@IN _104196 x t')). Qed.
Lemma lem4337011 {_104196 : Type'} (t : _104196 -> Prop) (x : _104196) (t' : _104196 -> Prop) : (term111 _104196 t x t') = (term155 _104196 t x t').
Proof. exact (@lem17265 (@IN _104196 x t) (@IN _104196 x t')). Qed.
Lemma lem4337012 {_104196 : Type'} (P : _104196 -> Prop) : (term125 _104196 P) = (term126 _104196 P).
Proof. exact (@lem18392 _104196 P). Qed.
Lemma lem4337013 {_104196 : Type'} (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term156 _104196 t t') = (term157 _104196 t t').
Proof. exact (@lem4337012 _104196 (term112 _104196 t t')). Qed.
Lemma lem4337014 {_104196 : Type'} (t : _104196 -> Prop) (x : _104196) (t' : _104196 -> Prop) : (term158 _104196 t t' x) = (term111 _104196 t x t').
Proof. exact (eq_refl (term158 _104196 t t' x)). Qed.
Lemma lem4337015 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4337016 {_104196 : Type'} (t : _104196 -> Prop) (x : _104196) (t' : _104196 -> Prop) : (term159 _104196 t t' x) = (term153 _104196 t x t').
Proof. exact (MK_COMB (@lem4337015) (@lem4337014 _104196 t x t')). Qed.
Lemma lem4337017 {_104196 : Type'} (t : _104196 -> Prop) (x : _104196) (t' : _104196 -> Prop) : (term159 _104196 t t' x) = (term154 _104196 t x t').
Proof. exact (TRANS (@lem4337016 _104196 t x t') (@lem4337006 _104196 t x t')). Qed.
Lemma lem4337018 {_104196 : Type'} (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term160 _104196 t t') = (term161 _104196 t t').
Proof. exact (fun_ext (fun x : _104196 => @lem4337017 _104196 t x t')). Qed.
Lemma lem4337019 {_104196 : Type'} : (@ex _104196) = (@ex _104196).
Proof. exact (eq_refl (@ex _104196)). Qed.
Lemma lem4337020 {_104196 : Type'} (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term157 _104196 t t') = (term162 _104196 t t').
Proof. exact (MK_COMB (@lem4337019 _104196) (@lem4337018 _104196 t t')). Qed.
Lemma lem4337021 {_104196 : Type'} (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term156 _104196 t t') = (term162 _104196 t t').
Proof. exact (TRANS (@lem4337013 _104196 t t') (@lem4337020 _104196 t t')). Qed.
Lemma lem4337022 {_104196 : Type'} (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term112 _104196 t t') = (term163 _104196 t t').
Proof. exact (fun_ext (fun x : _104196 => @lem4337011 _104196 t x t')). Qed.
Lemma lem4337023 {_104196 : Type'} : (@all _104196) = (@all _104196).
Proof. exact (eq_refl (@all _104196)). Qed.
Lemma lem4337024 {_104196 : Type'} (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term25 _104196 t t') = (term164 _104196 t t').
Proof. exact (MK_COMB (@lem4337023 _104196) (@lem4337022 _104196 t t')). Qed.
Lemma lem4337025 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4337026 {_104190 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) : (term165 _104190 s s') = (term166 _104190 s s').
Proof. exact (MK_COMB (@lem4337025) (@lem4336994 _104190 s s')). Qed.
Lemma lem4337027 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term167 _104190 _104196 s s' t t') = (term168 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337026 _104190 s s') (@lem4337021 _104196 t t')). Qed.
Lemma lem4337028 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term169 _104190 _104196 s s' t t') = (term167 _104190 _104196 s s' t t').
Proof. exact (@lem17045 (term25 _104190 s s') (term25 _104196 t t')). Qed.
Lemma lem4337029 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term169 _104190 _104196 s s' t t') = (term168 _104190 _104196 s s' t t').
Proof. exact (TRANS (@lem4337028 _104190 _104196 s s' t t') (@lem4337027 _104190 _104196 s s' t t')). Qed.
Lemma lem4337030 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4337031 {_104190 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) : (term80 _104190 s s') = (term170 _104190 s s').
Proof. exact (MK_COMB (@lem4337030) (@lem4336997 _104190 s s')). Qed.
Lemma lem4337032 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term82 _104190 _104196 s s' t t') = (term171 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337031 _104190 s s') (@lem4337024 _104196 t t')). Qed.
Lemma lem4337033 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4337034 {_104196 : Type'} (t : _104196 -> Prop) : (term172 _104196 t) = (term173 _104196 t).
Proof. exact (MK_COMB (@lem4337033) (@lem4336967 _104196 t)). Qed.
Lemma lem4337035 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term174 _104190 _104196 s s' t t') = (term175 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337034 _104196 t) (@lem4337029 _104190 _104196 s s' t t')). Qed.
Lemma lem4337036 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term176 _104190 _104196 s s' t t') = (term174 _104190 _104196 s s' t t').
Proof. exact (@lem17160 (term76 _104196 t) (term82 _104190 _104196 s s' t t')). Qed.
Lemma lem4337037 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term176 _104190 _104196 s s' t t') = (term175 _104190 _104196 s s' t t').
Proof. exact (TRANS (@lem4337036 _104190 _104196 s s' t t') (@lem4337035 _104190 _104196 s s' t t')). Qed.
Lemma lem4337038 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4337039 {_104196 : Type'} (t : _104196 -> Prop) : (term78 _104196 t) = (term78 _104196 t).
Proof. exact (MK_COMB (@lem4337038) (@lem4336970 _104196 t)). Qed.
Lemma lem4337040 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term84 _104190 _104196 s s' t t') = (term177 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337039 _104196 t) (@lem4337032 _104190 _104196 s s' t t')). Qed.
Lemma lem4337041 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4337042 {_104190 : Type'} (s : _104190 -> Prop) : (term172 _104190 s) = (term173 _104190 s).
Proof. exact (MK_COMB (@lem4337041) (@lem4336950 _104190 s)). Qed.
Lemma lem4337043 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term178 _104190 _104196 s s' t t') = (term179 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337042 _104190 s) (@lem4337037 _104190 _104196 s s' t t')). Qed.
Lemma lem4337044 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term180 _104190 _104196 s s' t t') = (term178 _104190 _104196 s s' t t').
Proof. exact (@lem17160 (term76 _104190 s) (term84 _104190 _104196 s s' t t')). Qed.
Lemma lem4337045 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term180 _104190 _104196 s s' t t') = (term179 _104190 _104196 s s' t t').
Proof. exact (TRANS (@lem4337044 _104190 _104196 s s' t t') (@lem4337043 _104190 _104196 s s' t t')). Qed.
Lemma lem4337046 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4337047 {_104190 : Type'} (s : _104190 -> Prop) : (term78 _104190 s) = (term78 _104190 s).
Proof. exact (MK_COMB (@lem4337046) (@lem4336953 _104190 s)). Qed.
Lemma lem4337048 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term86 _104190 _104196 s s' t t') = (term181 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337047 _104190 s) (@lem4337040 _104190 _104196 s s' t t')). Qed.
Lemma lem4337049 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4337050 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term182 _104190 _104196 s t s' t') = (term183 _104190 _104196 s t s' t').
Proof. exact (MK_COMB (@lem4337049) (@lem4336933 _104190 _104196 s t s' t')). Qed.
Lemma lem4337051 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term184 _104190 _104196 s s' t t') = (term185 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337050 _104190 _104196 s t s' t') (@lem4337048 _104190 _104196 s s' t t')). Qed.
Lemma lem4337052 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4337053 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term186 _104190 _104196 s t s' t') = (term187 _104190 _104196 s t s' t').
Proof. exact (MK_COMB (@lem4337052) (@lem4336936 _104190 _104196 s t s' t')). Qed.
Lemma lem4337054 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term188 _104190 _104196 s s' t t') = (term189 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337053 _104190 _104196 s t s' t') (@lem4337045 _104190 _104196 s s' t t')). Qed.
Lemma lem4337055 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4337056 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term190 _104190 _104196 s s' t t') = (term191 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337055) (@lem4337054 _104190 _104196 s s' t t')). Qed.
Lemma lem4337057 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term192 _104190 _104196 s s' t t') = (term193 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337056 _104190 _104196 s s' t t') (@lem4337051 _104190 _104196 s s' t t')). Qed.
Lemma lem4337058 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term114 _104190 _104196 s s' t t') = (term192 _104190 _104196 s s' t t').
Proof. exact (@lem17646 (term68 _104190 _104196 s t s' t') (term86 _104190 _104196 s s' t t')). Qed.
Lemma lem4337059 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term114 _104190 _104196 s s' t t') = (term193 _104190 _104196 s s' t t').
Proof. exact (TRANS (@lem4337058 _104190 _104196 s s' t t') (@lem4337057 _104190 _104196 s s' t t')). Qed.
Lemma lem4337376 {A : Type'} (P : A -> Prop) (Q : Prop) : (term194 A P Q) = (term195 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4337377 {_104190 : Type'} (P : _104190 -> Prop) (Q : Prop) : (term194 _104190 P Q) = (term195 _104190 P Q).
Proof. exact (@lem4337376 _104190 P Q). Qed.
Lemma lem4337378 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term196 _104190 _104196 s s' t t') = (term197 _104190 _104196 s s' t t').
Proof. exact (@lem4337377 _104190 (term161 _104190 s s') (term162 _104196 t t')). Qed.
Lemma lem4337379 {_104190 : Type'} (s : _104190 -> Prop) (x : _104190) (s' : _104190 -> Prop) : (term198 _104190 s s' x) = (term154 _104190 s x s').
Proof. exact (eq_refl (term198 _104190 s s' x)). Qed.
Lemma lem4337380 {_104190 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) : (term199 _104190 s s') = (term161 _104190 s s').
Proof. exact (fun_ext (fun x : _104190 => @lem4337379 _104190 s x s')). Qed.
Lemma lem4337381 {_104190 : Type'} : (@ex _104190) = (@ex _104190).
Proof. exact (eq_refl (@ex _104190)). Qed.
Lemma lem4337382 {_104190 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) : (term200 _104190 s s') = (term162 _104190 s s').
Proof. exact (MK_COMB (@lem4337381 _104190) (@lem4337380 _104190 s s')). Qed.
Lemma lem4337383 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4337384 {_104190 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) : (term201 _104190 s s') = (term166 _104190 s s').
Proof. exact (MK_COMB (@lem4337383) (@lem4337382 _104190 s s')). Qed.
Lemma lem4337385 {_104196 : Type'} (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term162 _104196 t t') = (term162 _104196 t t').
Proof. exact (eq_refl (term162 _104196 t t')). Qed.
Lemma lem4337386 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term196 _104190 _104196 s s' t t') = (term168 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337384 _104190 s s') (@lem4337385 _104196 t t')). Qed.
Lemma lem4337387 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4337388 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term202 _104190 _104196 s s' t t') = (term203 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337387) (@lem4337386 _104190 _104196 s s' t t')). Qed.
Lemma lem4337389 {_104190 : Type'} (s : _104190 -> Prop) (x : _104190) (s' : _104190 -> Prop) : (term198 _104190 s s' x) = (term154 _104190 s x s').
Proof. exact (eq_refl (term198 _104190 s s' x)). Qed.
Lemma lem4337390 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4337391 {_104190 : Type'} (s : _104190 -> Prop) (x : _104190) (s' : _104190 -> Prop) : (term204 _104190 s s' x) = (term205 _104190 s x s').
Proof. exact (MK_COMB (@lem4337390) (@lem4337389 _104190 s x s')). Qed.
Lemma lem4337392 {_104196 : Type'} (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term162 _104196 t t') = (term162 _104196 t t').
Proof. exact (eq_refl (term162 _104196 t t')). Qed.
Lemma lem4337393 {_104190 _104196 : Type'} (s : _104190 -> Prop) (x : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term206 _104190 _104196 s s' x t t') = (term207 _104190 _104196 s x s' t t').
Proof. exact (MK_COMB (@lem4337391 _104190 s x s') (@lem4337392 _104196 t t')). Qed.
Lemma lem4337394 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term208 _104190 _104196 s s' t t') = (term209 _104190 _104196 s s' t t').
Proof. exact (fun_ext (fun x : _104190 => @lem4337393 _104190 _104196 s x s' t t')). Qed.
Lemma lem4337395 {_104190 : Type'} : (@ex _104190) = (@ex _104190).
Proof. exact (eq_refl (@ex _104190)). Qed.
Lemma lem4337396 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term197 _104190 _104196 s s' t t') = (term210 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337395 _104190) (@lem4337394 _104190 _104196 s s' t t')). Qed.
Lemma lem4337397 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : ((term196 _104190 _104196 s s' t t') = (term197 _104190 _104196 s s' t t')) = ((term168 _104190 _104196 s s' t t') = (term210 _104190 _104196 s s' t t')).
Proof. exact (MK_COMB (@lem4337388 _104190 _104196 s s' t t') (@lem4337396 _104190 _104196 s s' t t')). Qed.
Lemma lem4337398 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term168 _104190 _104196 s s' t t') = (term210 _104190 _104196 s s' t t').
Proof. exact (EQ_MP (@lem4337397 _104190 _104196 s s' t t') (@lem4337378 _104190 _104196 s s' t t')). Qed.
Lemma lem4337400 {A : Type'} (P : Prop) (Q : A -> Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4337401 {_104196 : Type'} (P : Prop) (Q : _104196 -> Prop) : (term211 _104196 P Q) = (term212 _104196 P Q).
Proof. exact (@lem4337400 _104196 P Q). Qed.
Lemma lem4337402 {_104190 _104196 : Type'} (s : _104190 -> Prop) (x : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term213 _104190 _104196 s x s' t t') = (term214 _104190 _104196 s x s' t t').
Proof. exact (@lem4337401 _104196 (term154 _104190 s x s') (term161 _104196 t t')). Qed.
Lemma lem4337403 {_104196 : Type'} (t : _104196 -> Prop) (x : _104196) (t' : _104196 -> Prop) : (term198 _104196 t t' x) = (term154 _104196 t x t').
Proof. exact (eq_refl (term198 _104196 t t' x)). Qed.
Lemma lem4337404 {_104196 : Type'} (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term199 _104196 t t') = (term161 _104196 t t').
Proof. exact (fun_ext (fun x : _104196 => @lem4337403 _104196 t x t')). Qed.
Lemma lem4337405 {_104196 : Type'} : (@ex _104196) = (@ex _104196).
Proof. exact (eq_refl (@ex _104196)). Qed.
Lemma lem4337406 {_104196 : Type'} (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term200 _104196 t t') = (term162 _104196 t t').
Proof. exact (MK_COMB (@lem4337405 _104196) (@lem4337404 _104196 t t')). Qed.
Lemma lem4337407 {_104190 : Type'} (s : _104190 -> Prop) (x : _104190) (s' : _104190 -> Prop) : (term205 _104190 s x s') = (term205 _104190 s x s').
Proof. exact (eq_refl (term205 _104190 s x s')). Qed.
Lemma lem4337408 {_104190 _104196 : Type'} (s : _104190 -> Prop) (x : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term213 _104190 _104196 s x s' t t') = (term207 _104190 _104196 s x s' t t').
Proof. exact (MK_COMB (@lem4337407 _104190 s x s') (@lem4337406 _104196 t t')). Qed.
Lemma lem4337409 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4337410 {_104190 _104196 : Type'} (s : _104190 -> Prop) (x : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term215 _104190 _104196 s x s' t t') = (term216 _104190 _104196 s x s' t t').
Proof. exact (MK_COMB (@lem4337409) (@lem4337408 _104190 _104196 s x s' t t')). Qed.
Lemma lem4337411 {_104196 : Type'} (t : _104196 -> Prop) (x : _104196) (t' : _104196 -> Prop) : (term198 _104196 t t' x) = (term154 _104196 t x t').
Proof. exact (eq_refl (term198 _104196 t t' x)). Qed.
Lemma lem4337412 {_104190 : Type'} (s : _104190 -> Prop) (x : _104190) (s' : _104190 -> Prop) : (term205 _104190 s x s') = (term205 _104190 s x s').
Proof. exact (eq_refl (term205 _104190 s x s')). Qed.
Lemma lem4337413 {_104190 _104196 : Type'} (s : _104190 -> Prop) (x : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x' : _104196) (t' : _104196 -> Prop) : (term217 _104190 _104196 s x s' t t' x') = (term218 _104190 _104196 s x s' t x' t').
Proof. exact (MK_COMB (@lem4337412 _104190 s x s') (@lem4337411 _104196 t x' t')). Qed.
Lemma lem4337414 {_104190 _104196 : Type'} (s : _104190 -> Prop) (x : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term219 _104190 _104196 s x s' t t') = (term220 _104190 _104196 s x s' t t').
Proof. exact (fun_ext (fun x' : _104196 => @lem4337413 _104190 _104196 s x s' t x' t')). Qed.
Lemma lem4337415 {_104196 : Type'} : (@ex _104196) = (@ex _104196).
Proof. exact (eq_refl (@ex _104196)). Qed.
Lemma lem4337416 {_104190 _104196 : Type'} (s : _104190 -> Prop) (x : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term214 _104190 _104196 s x s' t t') = (term221 _104190 _104196 s x s' t t').
Proof. exact (MK_COMB (@lem4337415 _104196) (@lem4337414 _104190 _104196 s x s' t t')). Qed.
Lemma lem4337417 {_104190 _104196 : Type'} (s : _104190 -> Prop) (x : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : ((term213 _104190 _104196 s x s' t t') = (term214 _104190 _104196 s x s' t t')) = ((term207 _104190 _104196 s x s' t t') = (term221 _104190 _104196 s x s' t t')).
Proof. exact (MK_COMB (@lem4337410 _104190 _104196 s x s' t t') (@lem4337416 _104190 _104196 s x s' t t')). Qed.
Lemma lem4337418 {_104190 _104196 : Type'} (s : _104190 -> Prop) (x : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term207 _104190 _104196 s x s' t t') = (term221 _104190 _104196 s x s' t t').
Proof. exact (EQ_MP (@lem4337417 _104190 _104196 s x s' t t') (@lem4337402 _104190 _104196 s x s' t t')). Qed.
Lemma lem4337419 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term209 _104190 _104196 s s' t t') = (term222 _104190 _104196 s s' t t').
Proof. exact (fun_ext (fun x : _104190 => @lem4337418 _104190 _104196 s x s' t t')). Qed.
Lemma lem4337420 {_104190 : Type'} : (@ex _104190) = (@ex _104190).
Proof. exact (eq_refl (@ex _104190)). Qed.
Lemma lem4337421 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term210 _104190 _104196 s s' t t') = (term223 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337420 _104190) (@lem4337419 _104190 _104196 s s' t t')). Qed.
Lemma lem4337422 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term168 _104190 _104196 s s' t t') = (term223 _104190 _104196 s s' t t').
Proof. exact (TRANS (@lem4337398 _104190 _104196 s s' t t') (@lem4337421 _104190 _104196 s s' t t')). Qed.
Lemma lem4337423 {_104196 : Type'} (t : _104196 -> Prop) : (term173 _104196 t) = (term173 _104196 t).
Proof. exact (eq_refl (term173 _104196 t)). Qed.
Lemma lem4337424 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term175 _104190 _104196 s s' t t') = (term224 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337423 _104196 t) (@lem4337422 _104190 _104196 s s' t t')). Qed.
Lemma lem4337426 {A : Type'} (P : A -> Prop) (Q : Prop) : (term225 A P Q) = (term226 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4337427 {_104196 : Type'} (P : _104196 -> Prop) (Q : Prop) : (term225 _104196 P Q) = (term226 _104196 P Q).
Proof. exact (@lem4337426 _104196 P Q). Qed.
Lemma lem4337428 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term227 _104190 _104196 s s' t t') = (term228 _104190 _104196 s s' t t').
Proof. exact (@lem4337427 _104196 (term151 _104196 t) (term223 _104190 _104196 s s' t t')). Qed.
Lemma lem4337429 {_104196 : Type'} (x : _104196) (t : _104196 -> Prop) : (term229 _104196 t x) = (@IN _104196 x t).
Proof. exact (eq_refl (term229 _104196 t x)). Qed.
Lemma lem4337430 {_104196 : Type'} (t : _104196 -> Prop) : (term230 _104196 t) = (term151 _104196 t).
Proof. exact (fun_ext (fun x : _104196 => @lem4337429 _104196 x t)). Qed.
Lemma lem4337431 {_104196 : Type'} : (@ex _104196) = (@ex _104196).
Proof. exact (eq_refl (@ex _104196)). Qed.
Lemma lem4337432 {_104196 : Type'} (t : _104196 -> Prop) : (term231 _104196 t) = (term152 _104196 t).
Proof. exact (MK_COMB (@lem4337431 _104196) (@lem4337430 _104196 t)). Qed.
Lemma lem4337433 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4337434 {_104196 : Type'} (t : _104196 -> Prop) : (term232 _104196 t) = (term173 _104196 t).
Proof. exact (MK_COMB (@lem4337433) (@lem4337432 _104196 t)). Qed.
Lemma lem4337435 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term223 _104190 _104196 s s' t t') = (term223 _104190 _104196 s s' t t').
Proof. exact (eq_refl (term223 _104190 _104196 s s' t t')). Qed.
Lemma lem4337436 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term227 _104190 _104196 s s' t t') = (term224 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337434 _104196 t) (@lem4337435 _104190 _104196 s s' t t')). Qed.
Lemma lem4337437 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4337438 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term233 _104190 _104196 s s' t t') = (term234 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337437) (@lem4337436 _104190 _104196 s s' t t')). Qed.
Lemma lem4337439 {_104196 : Type'} (x : _104196) (t : _104196 -> Prop) : (term229 _104196 t x) = (@IN _104196 x t).
Proof. exact (eq_refl (term229 _104196 t x)). Qed.
Lemma lem4337440 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4337441 {_104196 : Type'} (x : _104196) (t : _104196 -> Prop) : (term235 _104196 t x) = (term236 _104196 x t).
Proof. exact (MK_COMB (@lem4337440) (@lem4337439 _104196 x t)). Qed.
Lemma lem4337442 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term223 _104190 _104196 s s' t t') = (term223 _104190 _104196 s s' t t').
Proof. exact (eq_refl (term223 _104190 _104196 s s' t t')). Qed.
Lemma lem4337443 {_104190 _104196 : Type'} (x : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term237 _104190 _104196 x s s' t t') = (term238 _104190 _104196 x s s' t t').
Proof. exact (MK_COMB (@lem4337441 _104196 x t) (@lem4337442 _104190 _104196 s s' t t')). Qed.
Lemma lem4337444 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term239 _104190 _104196 s s' t t') = (term240 _104190 _104196 s s' t t').
Proof. exact (fun_ext (fun x : _104196 => @lem4337443 _104190 _104196 x s s' t t')). Qed.
Lemma lem4337445 {_104196 : Type'} : (@ex _104196) = (@ex _104196).
Proof. exact (eq_refl (@ex _104196)). Qed.
Lemma lem4337446 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term228 _104190 _104196 s s' t t') = (term241 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337445 _104196) (@lem4337444 _104190 _104196 s s' t t')). Qed.
Lemma lem4337447 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : ((term227 _104190 _104196 s s' t t') = (term228 _104190 _104196 s s' t t')) = ((term224 _104190 _104196 s s' t t') = (term241 _104190 _104196 s s' t t')).
Proof. exact (MK_COMB (@lem4337438 _104190 _104196 s s' t t') (@lem4337446 _104190 _104196 s s' t t')). Qed.
Lemma lem4337448 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term224 _104190 _104196 s s' t t') = (term241 _104190 _104196 s s' t t').
Proof. exact (EQ_MP (@lem4337447 _104190 _104196 s s' t t') (@lem4337428 _104190 _104196 s s' t t')). Qed.
Lemma lem4337450 {A : Type'} (P : Prop) (Q : A -> Prop) : (term242 A P Q) = (term243 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4337451 {_104190 : Type'} (P : Prop) (Q : _104190 -> Prop) : (term242 _104190 P Q) = (term243 _104190 P Q).
Proof. exact (@lem4337450 _104190 P Q). Qed.
Lemma lem4337452 {_104190 _104196 : Type'} (x : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term244 _104190 _104196 x s s' t t') = (term245 _104190 _104196 x s s' t t').
Proof. exact (@lem4337451 _104190 (@IN _104196 x t) (term222 _104190 _104196 s s' t t')). Qed.
Lemma lem4337453 {_104190 _104196 : Type'} (s : _104190 -> Prop) (x : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term246 _104190 _104196 s s' t t' x) = (term221 _104190 _104196 s x s' t t').
Proof. exact (eq_refl (term246 _104190 _104196 s s' t t' x)). Qed.
Lemma lem4337454 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term247 _104190 _104196 s s' t t') = (term222 _104190 _104196 s s' t t').
Proof. exact (fun_ext (fun x : _104190 => @lem4337453 _104190 _104196 s x s' t t')). Qed.
Lemma lem4337455 {_104190 : Type'} : (@ex _104190) = (@ex _104190).
Proof. exact (eq_refl (@ex _104190)). Qed.
Lemma lem4337456 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term248 _104190 _104196 s s' t t') = (term223 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337455 _104190) (@lem4337454 _104190 _104196 s s' t t')). Qed.
Lemma lem4337457 {_104196 : Type'} (x : _104196) (t : _104196 -> Prop) : (term236 _104196 x t) = (term236 _104196 x t).
Proof. exact (eq_refl (term236 _104196 x t)). Qed.
Lemma lem4337458 {_104190 _104196 : Type'} (x : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term244 _104190 _104196 x s s' t t') = (term238 _104190 _104196 x s s' t t').
Proof. exact (MK_COMB (@lem4337457 _104196 x t) (@lem4337456 _104190 _104196 s s' t t')). Qed.
Lemma lem4337459 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4337460 {_104190 _104196 : Type'} (x : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term249 _104190 _104196 x s s' t t') = (term250 _104190 _104196 x s s' t t').
Proof. exact (MK_COMB (@lem4337459) (@lem4337458 _104190 _104196 x s s' t t')). Qed.
Lemma lem4337461 {_104190 _104196 : Type'} (s : _104190 -> Prop) (x : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term246 _104190 _104196 s s' t t' x) = (term221 _104190 _104196 s x s' t t').
Proof. exact (eq_refl (term246 _104190 _104196 s s' t t' x)). Qed.
Lemma lem4337462 {_104196 : Type'} (x : _104196) (t : _104196 -> Prop) : (term236 _104196 x t) = (term236 _104196 x t).
Proof. exact (eq_refl (term236 _104196 x t)). Qed.
Lemma lem4337463 {_104190 _104196 : Type'} (x : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term251 _104190 _104196 x s s' t t' x') = (term252 _104190 _104196 x s x' s' t t').
Proof. exact (MK_COMB (@lem4337462 _104196 x t) (@lem4337461 _104190 _104196 s x' s' t t')). Qed.
Lemma lem4337464 {_104190 _104196 : Type'} (x : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term253 _104190 _104196 x s s' t t') = (term254 _104190 _104196 x s s' t t').
Proof. exact (fun_ext (fun x' : _104190 => @lem4337463 _104190 _104196 x s x' s' t t')). Qed.
Lemma lem4337465 {_104190 : Type'} : (@ex _104190) = (@ex _104190).
Proof. exact (eq_refl (@ex _104190)). Qed.
Lemma lem4337466 {_104190 _104196 : Type'} (x : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term245 _104190 _104196 x s s' t t') = (term255 _104190 _104196 x s s' t t').
Proof. exact (MK_COMB (@lem4337465 _104190) (@lem4337464 _104190 _104196 x s s' t t')). Qed.
Lemma lem4337467 {_104190 _104196 : Type'} (x : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : ((term244 _104190 _104196 x s s' t t') = (term245 _104190 _104196 x s s' t t')) = ((term238 _104190 _104196 x s s' t t') = (term255 _104190 _104196 x s s' t t')).
Proof. exact (MK_COMB (@lem4337460 _104190 _104196 x s s' t t') (@lem4337466 _104190 _104196 x s s' t t')). Qed.
Lemma lem4337468 {_104190 _104196 : Type'} (x : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term238 _104190 _104196 x s s' t t') = (term255 _104190 _104196 x s s' t t').
Proof. exact (EQ_MP (@lem4337467 _104190 _104196 x s s' t t') (@lem4337452 _104190 _104196 x s s' t t')). Qed.
Lemma lem4337470 {A : Type'} (P : Prop) (Q : A -> Prop) : (term242 A P Q) = (term243 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4337471 {_104196 : Type'} (P : Prop) (Q : _104196 -> Prop) : (term242 _104196 P Q) = (term243 _104196 P Q).
Proof. exact (@lem4337470 _104196 P Q). Qed.
Lemma lem4337472 {_104190 _104196 : Type'} (x : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term256 _104190 _104196 x s x' s' t t') = (term257 _104190 _104196 x s x' s' t t').
Proof. exact (@lem4337471 _104196 (@IN _104196 x t) (term220 _104190 _104196 s x' s' t t')). Qed.
Lemma lem4337473 {_104190 _104196 : Type'} (s : _104190 -> Prop) (x : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x' : _104196) (t' : _104196 -> Prop) : (term258 _104190 _104196 s x s' t t' x') = (term218 _104190 _104196 s x s' t x' t').
Proof. exact (eq_refl (term258 _104190 _104196 s x s' t t' x')). Qed.
Lemma lem4337474 {_104190 _104196 : Type'} (s : _104190 -> Prop) (x : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term259 _104190 _104196 s x s' t t') = (term220 _104190 _104196 s x s' t t').
Proof. exact (fun_ext (fun x' : _104196 => @lem4337473 _104190 _104196 s x s' t x' t')). Qed.
Lemma lem4337475 {_104196 : Type'} : (@ex _104196) = (@ex _104196).
Proof. exact (eq_refl (@ex _104196)). Qed.
Lemma lem4337476 {_104190 _104196 : Type'} (s : _104190 -> Prop) (x : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term260 _104190 _104196 s x s' t t') = (term221 _104190 _104196 s x s' t t').
Proof. exact (MK_COMB (@lem4337475 _104196) (@lem4337474 _104190 _104196 s x s' t t')). Qed.
Lemma lem4337477 {_104196 : Type'} (x : _104196) (t : _104196 -> Prop) : (term236 _104196 x t) = (term236 _104196 x t).
Proof. exact (eq_refl (term236 _104196 x t)). Qed.
Lemma lem4337478 {_104190 _104196 : Type'} (x : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term256 _104190 _104196 x s x' s' t t') = (term252 _104190 _104196 x s x' s' t t').
Proof. exact (MK_COMB (@lem4337477 _104196 x t) (@lem4337476 _104190 _104196 s x' s' t t')). Qed.
Lemma lem4337479 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4337480 {_104190 _104196 : Type'} (x : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term261 _104190 _104196 x s x' s' t t') = (term262 _104190 _104196 x s x' s' t t').
Proof. exact (MK_COMB (@lem4337479) (@lem4337478 _104190 _104196 x s x' s' t t')). Qed.
Lemma lem4337481 {_104190 _104196 : Type'} (s : _104190 -> Prop) (x : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x' : _104196) (t' : _104196 -> Prop) : (term258 _104190 _104196 s x s' t t' x') = (term218 _104190 _104196 s x s' t x' t').
Proof. exact (eq_refl (term258 _104190 _104196 s x s' t t' x')). Qed.
Lemma lem4337482 {_104196 : Type'} (x : _104196) (t : _104196 -> Prop) : (term236 _104196 x t) = (term236 _104196 x t).
Proof. exact (eq_refl (term236 _104196 x t)). Qed.
Lemma lem4337483 {_104190 _104196 : Type'} (x : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) : (term263 _104190 _104196 x s x' s' t t' x'') = (term264 _104190 _104196 x s x' s' t x'' t').
Proof. exact (MK_COMB (@lem4337482 _104196 x t) (@lem4337481 _104190 _104196 s x' s' t x'' t')). Qed.
Lemma lem4337484 {_104190 _104196 : Type'} (x : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term265 _104190 _104196 x s x' s' t t') = (term266 _104190 _104196 x s x' s' t t').
Proof. exact (fun_ext (fun x'' : _104196 => @lem4337483 _104190 _104196 x s x' s' t x'' t')). Qed.
Lemma lem4337485 {_104196 : Type'} : (@ex _104196) = (@ex _104196).
Proof. exact (eq_refl (@ex _104196)). Qed.
Lemma lem4337486 {_104190 _104196 : Type'} (x : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term257 _104190 _104196 x s x' s' t t') = (term267 _104190 _104196 x s x' s' t t').
Proof. exact (MK_COMB (@lem4337485 _104196) (@lem4337484 _104190 _104196 x s x' s' t t')). Qed.
Lemma lem4337487 {_104190 _104196 : Type'} (x : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : ((term256 _104190 _104196 x s x' s' t t') = (term257 _104190 _104196 x s x' s' t t')) = ((term252 _104190 _104196 x s x' s' t t') = (term267 _104190 _104196 x s x' s' t t')).
Proof. exact (MK_COMB (@lem4337480 _104190 _104196 x s x' s' t t') (@lem4337486 _104190 _104196 x s x' s' t t')). Qed.
Lemma lem4337488 {_104190 _104196 : Type'} (x : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term252 _104190 _104196 x s x' s' t t') = (term267 _104190 _104196 x s x' s' t t').
Proof. exact (EQ_MP (@lem4337487 _104190 _104196 x s x' s' t t') (@lem4337472 _104190 _104196 x s x' s' t t')). Qed.
Lemma lem4337489 {_104190 _104196 : Type'} (x : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term254 _104190 _104196 x s s' t t') = (term268 _104190 _104196 x s s' t t').
Proof. exact (fun_ext (fun x' : _104190 => @lem4337488 _104190 _104196 x s x' s' t t')). Qed.
Lemma lem4337490 {_104190 : Type'} : (@ex _104190) = (@ex _104190).
Proof. exact (eq_refl (@ex _104190)). Qed.
Lemma lem4337491 {_104190 _104196 : Type'} (x : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term255 _104190 _104196 x s s' t t') = (term269 _104190 _104196 x s s' t t').
Proof. exact (MK_COMB (@lem4337490 _104190) (@lem4337489 _104190 _104196 x s s' t t')). Qed.
Lemma lem4337492 {_104190 _104196 : Type'} (x : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term238 _104190 _104196 x s s' t t') = (term269 _104190 _104196 x s s' t t').
Proof. exact (TRANS (@lem4337468 _104190 _104196 x s s' t t') (@lem4337491 _104190 _104196 x s s' t t')). Qed.
Lemma lem4337493 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term240 _104190 _104196 s s' t t') = (term270 _104190 _104196 s s' t t').
Proof. exact (fun_ext (fun x : _104196 => @lem4337492 _104190 _104196 x s s' t t')). Qed.
Lemma lem4337494 {_104196 : Type'} : (@ex _104196) = (@ex _104196).
Proof. exact (eq_refl (@ex _104196)). Qed.
Lemma lem4337495 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term241 _104190 _104196 s s' t t') = (term271 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337494 _104196) (@lem4337493 _104190 _104196 s s' t t')). Qed.
Lemma lem4337496 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term224 _104190 _104196 s s' t t') = (term271 _104190 _104196 s s' t t').
Proof. exact (TRANS (@lem4337448 _104190 _104196 s s' t t') (@lem4337495 _104190 _104196 s s' t t')). Qed.
Lemma lem4337497 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term175 _104190 _104196 s s' t t') = (term271 _104190 _104196 s s' t t').
Proof. exact (TRANS (@lem4337424 _104190 _104196 s s' t t') (@lem4337496 _104190 _104196 s s' t t')). Qed.
Lemma lem4337498 {_104190 : Type'} (s : _104190 -> Prop) : (term173 _104190 s) = (term173 _104190 s).
Proof. exact (eq_refl (term173 _104190 s)). Qed.
Lemma lem4337499 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term179 _104190 _104196 s s' t t') = (term272 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337498 _104190 s) (@lem4337497 _104190 _104196 s s' t t')). Qed.
Lemma lem4337501 {A : Type'} (P : A -> Prop) (Q : Prop) : (term225 A P Q) = (term226 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4337502 {_104190 : Type'} (P : _104190 -> Prop) (Q : Prop) : (term225 _104190 P Q) = (term226 _104190 P Q).
Proof. exact (@lem4337501 _104190 P Q). Qed.
Lemma lem4337503 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term273 _104190 _104196 s s' t t') = (term274 _104190 _104196 s s' t t').
Proof. exact (@lem4337502 _104190 (term151 _104190 s) (term271 _104190 _104196 s s' t t')). Qed.
Lemma lem4337504 {_104190 : Type'} (x : _104190) (s : _104190 -> Prop) : (term229 _104190 s x) = (@IN _104190 x s).
Proof. exact (eq_refl (term229 _104190 s x)). Qed.
Lemma lem4337505 {_104190 : Type'} (s : _104190 -> Prop) : (term230 _104190 s) = (term151 _104190 s).
Proof. exact (fun_ext (fun x : _104190 => @lem4337504 _104190 x s)). Qed.
Lemma lem4337506 {_104190 : Type'} : (@ex _104190) = (@ex _104190).
Proof. exact (eq_refl (@ex _104190)). Qed.
Lemma lem4337507 {_104190 : Type'} (s : _104190 -> Prop) : (term231 _104190 s) = (term152 _104190 s).
Proof. exact (MK_COMB (@lem4337506 _104190) (@lem4337505 _104190 s)). Qed.
Lemma lem4337508 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4337509 {_104190 : Type'} (s : _104190 -> Prop) : (term232 _104190 s) = (term173 _104190 s).
Proof. exact (MK_COMB (@lem4337508) (@lem4337507 _104190 s)). Qed.
Lemma lem4337510 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term271 _104190 _104196 s s' t t') = (term271 _104190 _104196 s s' t t').
Proof. exact (eq_refl (term271 _104190 _104196 s s' t t')). Qed.
Lemma lem4337511 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term273 _104190 _104196 s s' t t') = (term272 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337509 _104190 s) (@lem4337510 _104190 _104196 s s' t t')). Qed.
Lemma lem4337512 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4337513 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term275 _104190 _104196 s s' t t') = (term276 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337512) (@lem4337511 _104190 _104196 s s' t t')). Qed.
Lemma lem4337514 {_104190 : Type'} (x : _104190) (s : _104190 -> Prop) : (term229 _104190 s x) = (@IN _104190 x s).
Proof. exact (eq_refl (term229 _104190 s x)). Qed.
Lemma lem4337515 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4337516 {_104190 : Type'} (x : _104190) (s : _104190 -> Prop) : (term235 _104190 s x) = (term236 _104190 x s).
Proof. exact (MK_COMB (@lem4337515) (@lem4337514 _104190 x s)). Qed.
Lemma lem4337517 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term271 _104190 _104196 s s' t t') = (term271 _104190 _104196 s s' t t').
Proof. exact (eq_refl (term271 _104190 _104196 s s' t t')). Qed.
Lemma lem4337518 {_104190 _104196 : Type'} (x : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term277 _104190 _104196 x s s' t t') = (term278 _104190 _104196 x s s' t t').
Proof. exact (MK_COMB (@lem4337516 _104190 x s) (@lem4337517 _104190 _104196 s s' t t')). Qed.
Lemma lem4337519 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term279 _104190 _104196 s s' t t') = (term280 _104190 _104196 s s' t t').
Proof. exact (fun_ext (fun x : _104190 => @lem4337518 _104190 _104196 x s s' t t')). Qed.
Lemma lem4337520 {_104190 : Type'} : (@ex _104190) = (@ex _104190).
Proof. exact (eq_refl (@ex _104190)). Qed.
Lemma lem4337521 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term274 _104190 _104196 s s' t t') = (term281 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337520 _104190) (@lem4337519 _104190 _104196 s s' t t')). Qed.
Lemma lem4337522 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : ((term273 _104190 _104196 s s' t t') = (term274 _104190 _104196 s s' t t')) = ((term272 _104190 _104196 s s' t t') = (term281 _104190 _104196 s s' t t')).
Proof. exact (MK_COMB (@lem4337513 _104190 _104196 s s' t t') (@lem4337521 _104190 _104196 s s' t t')). Qed.
Lemma lem4337523 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term272 _104190 _104196 s s' t t') = (term281 _104190 _104196 s s' t t').
Proof. exact (EQ_MP (@lem4337522 _104190 _104196 s s' t t') (@lem4337503 _104190 _104196 s s' t t')). Qed.
Lemma lem4337525 {A : Type'} (P : Prop) (Q : A -> Prop) : (term242 A P Q) = (term243 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4337526 {_104196 : Type'} (P : Prop) (Q : _104196 -> Prop) : (term242 _104196 P Q) = (term243 _104196 P Q).
Proof. exact (@lem4337525 _104196 P Q). Qed.
Lemma lem4337527 {_104190 _104196 : Type'} (x : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term282 _104190 _104196 x s s' t t') = (term283 _104190 _104196 x s s' t t').
Proof. exact (@lem4337526 _104196 (@IN _104190 x s) (term270 _104190 _104196 s s' t t')). Qed.
Lemma lem4337528 {_104190 _104196 : Type'} (x : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term284 _104190 _104196 s s' t t' x) = (term269 _104190 _104196 x s s' t t').
Proof. exact (eq_refl (term284 _104190 _104196 s s' t t' x)). Qed.
Lemma lem4337529 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term285 _104190 _104196 s s' t t') = (term270 _104190 _104196 s s' t t').
Proof. exact (fun_ext (fun x : _104196 => @lem4337528 _104190 _104196 x s s' t t')). Qed.
Lemma lem4337530 {_104196 : Type'} : (@ex _104196) = (@ex _104196).
Proof. exact (eq_refl (@ex _104196)). Qed.
Lemma lem4337531 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term286 _104190 _104196 s s' t t') = (term271 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337530 _104196) (@lem4337529 _104190 _104196 s s' t t')). Qed.
Lemma lem4337532 {_104190 : Type'} (x : _104190) (s : _104190 -> Prop) : (term236 _104190 x s) = (term236 _104190 x s).
Proof. exact (eq_refl (term236 _104190 x s)). Qed.
Lemma lem4337533 {_104190 _104196 : Type'} (x : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term282 _104190 _104196 x s s' t t') = (term278 _104190 _104196 x s s' t t').
Proof. exact (MK_COMB (@lem4337532 _104190 x s) (@lem4337531 _104190 _104196 s s' t t')). Qed.
Lemma lem4337534 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4337535 {_104190 _104196 : Type'} (x : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term287 _104190 _104196 x s s' t t') = (term288 _104190 _104196 x s s' t t').
Proof. exact (MK_COMB (@lem4337534) (@lem4337533 _104190 _104196 x s s' t t')). Qed.
Lemma lem4337536 {_104190 _104196 : Type'} (x : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term284 _104190 _104196 s s' t t' x) = (term269 _104190 _104196 x s s' t t').
Proof. exact (eq_refl (term284 _104190 _104196 s s' t t' x)). Qed.
Lemma lem4337537 {_104190 : Type'} (x : _104190) (s : _104190 -> Prop) : (term236 _104190 x s) = (term236 _104190 x s).
Proof. exact (eq_refl (term236 _104190 x s)). Qed.
Lemma lem4337538 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term289 _104190 _104196 x s s' t t' x') = (term290 _104190 _104196 x x' s s' t t').
Proof. exact (MK_COMB (@lem4337537 _104190 x s) (@lem4337536 _104190 _104196 x' s s' t t')). Qed.
Lemma lem4337539 {_104190 _104196 : Type'} (x : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term291 _104190 _104196 x s s' t t') = (term292 _104190 _104196 x s s' t t').
Proof. exact (fun_ext (fun x' : _104196 => @lem4337538 _104190 _104196 x x' s s' t t')). Qed.
Lemma lem4337540 {_104196 : Type'} : (@ex _104196) = (@ex _104196).
Proof. exact (eq_refl (@ex _104196)). Qed.
Lemma lem4337541 {_104190 _104196 : Type'} (x : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term283 _104190 _104196 x s s' t t') = (term293 _104190 _104196 x s s' t t').
Proof. exact (MK_COMB (@lem4337540 _104196) (@lem4337539 _104190 _104196 x s s' t t')). Qed.
Lemma lem4337542 {_104190 _104196 : Type'} (x : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : ((term282 _104190 _104196 x s s' t t') = (term283 _104190 _104196 x s s' t t')) = ((term278 _104190 _104196 x s s' t t') = (term293 _104190 _104196 x s s' t t')).
Proof. exact (MK_COMB (@lem4337535 _104190 _104196 x s s' t t') (@lem4337541 _104190 _104196 x s s' t t')). Qed.
Lemma lem4337543 {_104190 _104196 : Type'} (x : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term278 _104190 _104196 x s s' t t') = (term293 _104190 _104196 x s s' t t').
Proof. exact (EQ_MP (@lem4337542 _104190 _104196 x s s' t t') (@lem4337527 _104190 _104196 x s s' t t')). Qed.
Lemma lem4337545 {A : Type'} (P : Prop) (Q : A -> Prop) : (term242 A P Q) = (term243 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4337546 {_104190 : Type'} (P : Prop) (Q : _104190 -> Prop) : (term242 _104190 P Q) = (term243 _104190 P Q).
Proof. exact (@lem4337545 _104190 P Q). Qed.
Lemma lem4337547 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term294 _104190 _104196 x x' s s' t t') = (term295 _104190 _104196 x x' s s' t t').
Proof. exact (@lem4337546 _104190 (@IN _104190 x s) (term268 _104190 _104196 x' s s' t t')). Qed.
Lemma lem4337548 {_104190 _104196 : Type'} (x : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term296 _104190 _104196 x s s' t t' x') = (term267 _104190 _104196 x s x' s' t t').
Proof. exact (eq_refl (term296 _104190 _104196 x s s' t t' x')). Qed.
Lemma lem4337549 {_104190 _104196 : Type'} (x : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term297 _104190 _104196 x s s' t t') = (term268 _104190 _104196 x s s' t t').
Proof. exact (fun_ext (fun x' : _104190 => @lem4337548 _104190 _104196 x s x' s' t t')). Qed.
Lemma lem4337550 {_104190 : Type'} : (@ex _104190) = (@ex _104190).
Proof. exact (eq_refl (@ex _104190)). Qed.
Lemma lem4337551 {_104190 _104196 : Type'} (x : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term298 _104190 _104196 x s s' t t') = (term269 _104190 _104196 x s s' t t').
Proof. exact (MK_COMB (@lem4337550 _104190) (@lem4337549 _104190 _104196 x s s' t t')). Qed.
Lemma lem4337552 {_104190 : Type'} (x : _104190) (s : _104190 -> Prop) : (term236 _104190 x s) = (term236 _104190 x s).
Proof. exact (eq_refl (term236 _104190 x s)). Qed.
Lemma lem4337553 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term294 _104190 _104196 x x' s s' t t') = (term290 _104190 _104196 x x' s s' t t').
Proof. exact (MK_COMB (@lem4337552 _104190 x s) (@lem4337551 _104190 _104196 x' s s' t t')). Qed.
Lemma lem4337554 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4337555 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term299 _104190 _104196 x x' s s' t t') = (term300 _104190 _104196 x x' s s' t t').
Proof. exact (MK_COMB (@lem4337554) (@lem4337553 _104190 _104196 x x' s s' t t')). Qed.
Lemma lem4337556 {_104190 _104196 : Type'} (x : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term296 _104190 _104196 x s s' t t' x') = (term267 _104190 _104196 x s x' s' t t').
Proof. exact (eq_refl (term296 _104190 _104196 x s s' t t' x')). Qed.
Lemma lem4337557 {_104190 : Type'} (x : _104190) (s : _104190 -> Prop) : (term236 _104190 x s) = (term236 _104190 x s).
Proof. exact (eq_refl (term236 _104190 x s)). Qed.
Lemma lem4337558 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (x'' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term301 _104190 _104196 x x' s s' t t' x'') = (term302 _104190 _104196 x x' s x'' s' t t').
Proof. exact (MK_COMB (@lem4337557 _104190 x s) (@lem4337556 _104190 _104196 x' s x'' s' t t')). Qed.
Lemma lem4337559 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term303 _104190 _104196 x x' s s' t t') = (term304 _104190 _104196 x x' s s' t t').
Proof. exact (fun_ext (fun x'' : _104190 => @lem4337558 _104190 _104196 x x' s x'' s' t t')). Qed.
Lemma lem4337560 {_104190 : Type'} : (@ex _104190) = (@ex _104190).
Proof. exact (eq_refl (@ex _104190)). Qed.
Lemma lem4337561 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term295 _104190 _104196 x x' s s' t t') = (term305 _104190 _104196 x x' s s' t t').
Proof. exact (MK_COMB (@lem4337560 _104190) (@lem4337559 _104190 _104196 x x' s s' t t')). Qed.
Lemma lem4337562 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : ((term294 _104190 _104196 x x' s s' t t') = (term295 _104190 _104196 x x' s s' t t')) = ((term290 _104190 _104196 x x' s s' t t') = (term305 _104190 _104196 x x' s s' t t')).
Proof. exact (MK_COMB (@lem4337555 _104190 _104196 x x' s s' t t') (@lem4337561 _104190 _104196 x x' s s' t t')). Qed.
Lemma lem4337563 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term290 _104190 _104196 x x' s s' t t') = (term305 _104190 _104196 x x' s s' t t').
Proof. exact (EQ_MP (@lem4337562 _104190 _104196 x x' s s' t t') (@lem4337547 _104190 _104196 x x' s s' t t')). Qed.
Lemma lem4337565 {A : Type'} (P : Prop) (Q : A -> Prop) : (term242 A P Q) = (term243 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4337566 {_104196 : Type'} (P : Prop) (Q : _104196 -> Prop) : (term242 _104196 P Q) = (term243 _104196 P Q).
Proof. exact (@lem4337565 _104196 P Q). Qed.
Lemma lem4337567 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (x'' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term306 _104190 _104196 x x' s x'' s' t t') = (term307 _104190 _104196 x x' s x'' s' t t').
Proof. exact (@lem4337566 _104196 (@IN _104190 x s) (term266 _104190 _104196 x' s x'' s' t t')). Qed.
Lemma lem4337568 {_104190 _104196 : Type'} (x : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) : (term308 _104190 _104196 x s x' s' t t' x'') = (term264 _104190 _104196 x s x' s' t x'' t').
Proof. exact (eq_refl (term308 _104190 _104196 x s x' s' t t' x'')). Qed.
Lemma lem4337569 {_104190 _104196 : Type'} (x : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term309 _104190 _104196 x s x' s' t t') = (term266 _104190 _104196 x s x' s' t t').
Proof. exact (fun_ext (fun x'' : _104196 => @lem4337568 _104190 _104196 x s x' s' t x'' t')). Qed.
Lemma lem4337570 {_104196 : Type'} : (@ex _104196) = (@ex _104196).
Proof. exact (eq_refl (@ex _104196)). Qed.
Lemma lem4337571 {_104190 _104196 : Type'} (x : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term310 _104190 _104196 x s x' s' t t') = (term267 _104190 _104196 x s x' s' t t').
Proof. exact (MK_COMB (@lem4337570 _104196) (@lem4337569 _104190 _104196 x s x' s' t t')). Qed.
Lemma lem4337572 {_104190 : Type'} (x : _104190) (s : _104190 -> Prop) : (term236 _104190 x s) = (term236 _104190 x s).
Proof. exact (eq_refl (term236 _104190 x s)). Qed.
Lemma lem4337573 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (x'' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term306 _104190 _104196 x x' s x'' s' t t') = (term302 _104190 _104196 x x' s x'' s' t t').
Proof. exact (MK_COMB (@lem4337572 _104190 x s) (@lem4337571 _104190 _104196 x' s x'' s' t t')). Qed.
Lemma lem4337574 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4337575 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (x'' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term311 _104190 _104196 x x' s x'' s' t t') = (term312 _104190 _104196 x x' s x'' s' t t').
Proof. exact (MK_COMB (@lem4337574) (@lem4337573 _104190 _104196 x x' s x'' s' t t')). Qed.
Lemma lem4337576 {_104190 _104196 : Type'} (x : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) : (term308 _104190 _104196 x s x' s' t t' x'') = (term264 _104190 _104196 x s x' s' t x'' t').
Proof. exact (eq_refl (term308 _104190 _104196 x s x' s' t t' x'')). Qed.
Lemma lem4337577 {_104190 : Type'} (x : _104190) (s : _104190 -> Prop) : (term236 _104190 x s) = (term236 _104190 x s).
Proof. exact (eq_refl (term236 _104190 x s)). Qed.
Lemma lem4337578 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (x'' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x''' : _104196) (t' : _104196 -> Prop) : (term313 _104190 _104196 x x' s x'' s' t t' x''') = (term314 _104190 _104196 x x' s x'' s' t x''' t').
Proof. exact (MK_COMB (@lem4337577 _104190 x s) (@lem4337576 _104190 _104196 x' s x'' s' t x''' t')). Qed.
Lemma lem4337579 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (x'' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term315 _104190 _104196 x x' s x'' s' t t') = (term316 _104190 _104196 x x' s x'' s' t t').
Proof. exact (fun_ext (fun x''' : _104196 => @lem4337578 _104190 _104196 x x' s x'' s' t x''' t')). Qed.
Lemma lem4337580 {_104196 : Type'} : (@ex _104196) = (@ex _104196).
Proof. exact (eq_refl (@ex _104196)). Qed.
Lemma lem4337581 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (x'' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term307 _104190 _104196 x x' s x'' s' t t') = (term317 _104190 _104196 x x' s x'' s' t t').
Proof. exact (MK_COMB (@lem4337580 _104196) (@lem4337579 _104190 _104196 x x' s x'' s' t t')). Qed.
Lemma lem4337582 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (x'' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : ((term306 _104190 _104196 x x' s x'' s' t t') = (term307 _104190 _104196 x x' s x'' s' t t')) = ((term302 _104190 _104196 x x' s x'' s' t t') = (term317 _104190 _104196 x x' s x'' s' t t')).
Proof. exact (MK_COMB (@lem4337575 _104190 _104196 x x' s x'' s' t t') (@lem4337581 _104190 _104196 x x' s x'' s' t t')). Qed.
Lemma lem4337583 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (x'' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term302 _104190 _104196 x x' s x'' s' t t') = (term317 _104190 _104196 x x' s x'' s' t t').
Proof. exact (EQ_MP (@lem4337582 _104190 _104196 x x' s x'' s' t t') (@lem4337567 _104190 _104196 x x' s x'' s' t t')). Qed.
Lemma lem4337584 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term304 _104190 _104196 x x' s s' t t') = (term318 _104190 _104196 x x' s s' t t').
Proof. exact (fun_ext (fun x'' : _104190 => @lem4337583 _104190 _104196 x x' s x'' s' t t')). Qed.
Lemma lem4337585 {_104190 : Type'} : (@ex _104190) = (@ex _104190).
Proof. exact (eq_refl (@ex _104190)). Qed.
Lemma lem4337586 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term305 _104190 _104196 x x' s s' t t') = (term319 _104190 _104196 x x' s s' t t').
Proof. exact (MK_COMB (@lem4337585 _104190) (@lem4337584 _104190 _104196 x x' s s' t t')). Qed.
Lemma lem4337587 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term290 _104190 _104196 x x' s s' t t') = (term319 _104190 _104196 x x' s s' t t').
Proof. exact (TRANS (@lem4337563 _104190 _104196 x x' s s' t t') (@lem4337586 _104190 _104196 x x' s s' t t')). Qed.
Lemma lem4337588 {_104190 _104196 : Type'} (x : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term292 _104190 _104196 x s s' t t') = (term320 _104190 _104196 x s s' t t').
Proof. exact (fun_ext (fun x' : _104196 => @lem4337587 _104190 _104196 x x' s s' t t')). Qed.
Lemma lem4337589 {_104196 : Type'} : (@ex _104196) = (@ex _104196).
Proof. exact (eq_refl (@ex _104196)). Qed.
Lemma lem4337590 {_104190 _104196 : Type'} (x : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term293 _104190 _104196 x s s' t t') = (term321 _104190 _104196 x s s' t t').
Proof. exact (MK_COMB (@lem4337589 _104196) (@lem4337588 _104190 _104196 x s s' t t')). Qed.
Lemma lem4337591 {_104190 _104196 : Type'} (x : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term278 _104190 _104196 x s s' t t') = (term321 _104190 _104196 x s s' t t').
Proof. exact (TRANS (@lem4337543 _104190 _104196 x s s' t t') (@lem4337590 _104190 _104196 x s s' t t')). Qed.
Lemma lem4337592 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term280 _104190 _104196 s s' t t') = (term322 _104190 _104196 s s' t t').
Proof. exact (fun_ext (fun x : _104190 => @lem4337591 _104190 _104196 x s s' t t')). Qed.
Lemma lem4337593 {_104190 : Type'} : (@ex _104190) = (@ex _104190).
Proof. exact (eq_refl (@ex _104190)). Qed.
Lemma lem4337594 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term281 _104190 _104196 s s' t t') = (term323 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337593 _104190) (@lem4337592 _104190 _104196 s s' t t')). Qed.
Lemma lem4337595 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term272 _104190 _104196 s s' t t') = (term323 _104190 _104196 s s' t t').
Proof. exact (TRANS (@lem4337523 _104190 _104196 s s' t t') (@lem4337594 _104190 _104196 s s' t t')). Qed.
Lemma lem4337596 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term179 _104190 _104196 s s' t t') = (term323 _104190 _104196 s s' t t').
Proof. exact (TRANS (@lem4337499 _104190 _104196 s s' t t') (@lem4337595 _104190 _104196 s s' t t')). Qed.
Lemma lem4337597 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term187 _104190 _104196 s t s' t') = (term187 _104190 _104196 s t s' t').
Proof. exact (eq_refl (term187 _104190 _104196 s t s' t')). Qed.
Lemma lem4337598 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term189 _104190 _104196 s s' t t') = (term324 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337597 _104190 _104196 s t s' t') (@lem4337596 _104190 _104196 s s' t t')). Qed.
Lemma lem4337600 {A : Type'} (P : Prop) (Q : A -> Prop) : (term242 A P Q) = (term243 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4337601 {_104190 : Type'} (P : Prop) (Q : _104190 -> Prop) : (term242 _104190 P Q) = (term243 _104190 P Q).
Proof. exact (@lem4337600 _104190 P Q). Qed.
Lemma lem4337602 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term325 _104190 _104196 s s' t t') = (term326 _104190 _104196 s s' t t').
Proof. exact (@lem4337601 _104190 (term144 _104190 _104196 s t s' t') (term322 _104190 _104196 s s' t t')). Qed.
Lemma lem4337603 {_104190 _104196 : Type'} (x : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term327 _104190 _104196 s s' t t' x) = (term321 _104190 _104196 x s s' t t').
Proof. exact (eq_refl (term327 _104190 _104196 s s' t t' x)). Qed.
Lemma lem4337604 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term328 _104190 _104196 s s' t t') = (term322 _104190 _104196 s s' t t').
Proof. exact (fun_ext (fun x : _104190 => @lem4337603 _104190 _104196 x s s' t t')). Qed.
Lemma lem4337605 {_104190 : Type'} : (@ex _104190) = (@ex _104190).
Proof. exact (eq_refl (@ex _104190)). Qed.
Lemma lem4337606 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term329 _104190 _104196 s s' t t') = (term323 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337605 _104190) (@lem4337604 _104190 _104196 s s' t t')). Qed.
Lemma lem4337607 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term187 _104190 _104196 s t s' t') = (term187 _104190 _104196 s t s' t').
Proof. exact (eq_refl (term187 _104190 _104196 s t s' t')). Qed.
Lemma lem4337608 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term325 _104190 _104196 s s' t t') = (term324 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337607 _104190 _104196 s t s' t') (@lem4337606 _104190 _104196 s s' t t')). Qed.
Lemma lem4337609 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4337610 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term330 _104190 _104196 s s' t t') = (term331 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337609) (@lem4337608 _104190 _104196 s s' t t')). Qed.
Lemma lem4337611 {_104190 _104196 : Type'} (x : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term327 _104190 _104196 s s' t t' x) = (term321 _104190 _104196 x s s' t t').
Proof. exact (eq_refl (term327 _104190 _104196 s s' t t' x)). Qed.
Lemma lem4337612 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term187 _104190 _104196 s t s' t') = (term187 _104190 _104196 s t s' t').
Proof. exact (eq_refl (term187 _104190 _104196 s t s' t')). Qed.
Lemma lem4337613 {_104190 _104196 : Type'} (x : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term332 _104190 _104196 s s' t t' x) = (term333 _104190 _104196 x s s' t t').
Proof. exact (MK_COMB (@lem4337612 _104190 _104196 s t s' t') (@lem4337611 _104190 _104196 x s s' t t')). Qed.
Lemma lem4337614 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term334 _104190 _104196 s s' t t') = (term335 _104190 _104196 s s' t t').
Proof. exact (fun_ext (fun x : _104190 => @lem4337613 _104190 _104196 x s s' t t')). Qed.
Lemma lem4337615 {_104190 : Type'} : (@ex _104190) = (@ex _104190).
Proof. exact (eq_refl (@ex _104190)). Qed.
Lemma lem4337616 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term326 _104190 _104196 s s' t t') = (term336 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337615 _104190) (@lem4337614 _104190 _104196 s s' t t')). Qed.
Lemma lem4337617 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : ((term325 _104190 _104196 s s' t t') = (term326 _104190 _104196 s s' t t')) = ((term324 _104190 _104196 s s' t t') = (term336 _104190 _104196 s s' t t')).
Proof. exact (MK_COMB (@lem4337610 _104190 _104196 s s' t t') (@lem4337616 _104190 _104196 s s' t t')). Qed.
Lemma lem4337618 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term324 _104190 _104196 s s' t t') = (term336 _104190 _104196 s s' t t').
Proof. exact (EQ_MP (@lem4337617 _104190 _104196 s s' t t') (@lem4337602 _104190 _104196 s s' t t')). Qed.
Lemma lem4337620 {A : Type'} (P : Prop) (Q : A -> Prop) : (term242 A P Q) = (term243 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4337621 {_104196 : Type'} (P : Prop) (Q : _104196 -> Prop) : (term242 _104196 P Q) = (term243 _104196 P Q).
Proof. exact (@lem4337620 _104196 P Q). Qed.
Lemma lem4337622 {_104190 _104196 : Type'} (x : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term337 _104190 _104196 x s s' t t') = (term338 _104190 _104196 x s s' t t').
Proof. exact (@lem4337621 _104196 (term144 _104190 _104196 s t s' t') (term320 _104190 _104196 x s s' t t')). Qed.
Lemma lem4337623 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term339 _104190 _104196 x s s' t t' x') = (term319 _104190 _104196 x x' s s' t t').
Proof. exact (eq_refl (term339 _104190 _104196 x s s' t t' x')). Qed.
Lemma lem4337624 {_104190 _104196 : Type'} (x : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term340 _104190 _104196 x s s' t t') = (term320 _104190 _104196 x s s' t t').
Proof. exact (fun_ext (fun x' : _104196 => @lem4337623 _104190 _104196 x x' s s' t t')). Qed.
Lemma lem4337625 {_104196 : Type'} : (@ex _104196) = (@ex _104196).
Proof. exact (eq_refl (@ex _104196)). Qed.
Lemma lem4337626 {_104190 _104196 : Type'} (x : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term341 _104190 _104196 x s s' t t') = (term321 _104190 _104196 x s s' t t').
Proof. exact (MK_COMB (@lem4337625 _104196) (@lem4337624 _104190 _104196 x s s' t t')). Qed.
Lemma lem4337627 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term187 _104190 _104196 s t s' t') = (term187 _104190 _104196 s t s' t').
Proof. exact (eq_refl (term187 _104190 _104196 s t s' t')). Qed.
Lemma lem4337628 {_104190 _104196 : Type'} (x : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term337 _104190 _104196 x s s' t t') = (term333 _104190 _104196 x s s' t t').
Proof. exact (MK_COMB (@lem4337627 _104190 _104196 s t s' t') (@lem4337626 _104190 _104196 x s s' t t')). Qed.
Lemma lem4337629 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4337630 {_104190 _104196 : Type'} (x : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term342 _104190 _104196 x s s' t t') = (term343 _104190 _104196 x s s' t t').
Proof. exact (MK_COMB (@lem4337629) (@lem4337628 _104190 _104196 x s s' t t')). Qed.
Lemma lem4337631 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term339 _104190 _104196 x s s' t t' x') = (term319 _104190 _104196 x x' s s' t t').
Proof. exact (eq_refl (term339 _104190 _104196 x s s' t t' x')). Qed.
Lemma lem4337632 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term187 _104190 _104196 s t s' t') = (term187 _104190 _104196 s t s' t').
Proof. exact (eq_refl (term187 _104190 _104196 s t s' t')). Qed.
Lemma lem4337633 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term344 _104190 _104196 x s s' t t' x') = (term345 _104190 _104196 x x' s s' t t').
Proof. exact (MK_COMB (@lem4337632 _104190 _104196 s t s' t') (@lem4337631 _104190 _104196 x x' s s' t t')). Qed.
Lemma lem4337634 {_104190 _104196 : Type'} (x : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term346 _104190 _104196 x s s' t t') = (term347 _104190 _104196 x s s' t t').
Proof. exact (fun_ext (fun x' : _104196 => @lem4337633 _104190 _104196 x x' s s' t t')). Qed.
Lemma lem4337635 {_104196 : Type'} : (@ex _104196) = (@ex _104196).
Proof. exact (eq_refl (@ex _104196)). Qed.
Lemma lem4337636 {_104190 _104196 : Type'} (x : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term338 _104190 _104196 x s s' t t') = (term348 _104190 _104196 x s s' t t').
Proof. exact (MK_COMB (@lem4337635 _104196) (@lem4337634 _104190 _104196 x s s' t t')). Qed.
Lemma lem4337637 {_104190 _104196 : Type'} (x : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : ((term337 _104190 _104196 x s s' t t') = (term338 _104190 _104196 x s s' t t')) = ((term333 _104190 _104196 x s s' t t') = (term348 _104190 _104196 x s s' t t')).
Proof. exact (MK_COMB (@lem4337630 _104190 _104196 x s s' t t') (@lem4337636 _104190 _104196 x s s' t t')). Qed.
Lemma lem4337638 {_104190 _104196 : Type'} (x : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term333 _104190 _104196 x s s' t t') = (term348 _104190 _104196 x s s' t t').
Proof. exact (EQ_MP (@lem4337637 _104190 _104196 x s s' t t') (@lem4337622 _104190 _104196 x s s' t t')). Qed.
Lemma lem4337640 {A : Type'} (P : Prop) (Q : A -> Prop) : (term242 A P Q) = (term243 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4337641 {_104190 : Type'} (P : Prop) (Q : _104190 -> Prop) : (term242 _104190 P Q) = (term243 _104190 P Q).
Proof. exact (@lem4337640 _104190 P Q). Qed.
Lemma lem4337642 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term349 _104190 _104196 x x' s s' t t') = (term350 _104190 _104196 x x' s s' t t').
Proof. exact (@lem4337641 _104190 (term144 _104190 _104196 s t s' t') (term318 _104190 _104196 x x' s s' t t')). Qed.
Lemma lem4337643 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (x'' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term351 _104190 _104196 x x' s s' t t' x'') = (term317 _104190 _104196 x x' s x'' s' t t').
Proof. exact (eq_refl (term351 _104190 _104196 x x' s s' t t' x'')). Qed.
Lemma lem4337644 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term352 _104190 _104196 x x' s s' t t') = (term318 _104190 _104196 x x' s s' t t').
Proof. exact (fun_ext (fun x'' : _104190 => @lem4337643 _104190 _104196 x x' s x'' s' t t')). Qed.
Lemma lem4337645 {_104190 : Type'} : (@ex _104190) = (@ex _104190).
Proof. exact (eq_refl (@ex _104190)). Qed.
Lemma lem4337646 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term353 _104190 _104196 x x' s s' t t') = (term319 _104190 _104196 x x' s s' t t').
Proof. exact (MK_COMB (@lem4337645 _104190) (@lem4337644 _104190 _104196 x x' s s' t t')). Qed.
Lemma lem4337647 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term187 _104190 _104196 s t s' t') = (term187 _104190 _104196 s t s' t').
Proof. exact (eq_refl (term187 _104190 _104196 s t s' t')). Qed.
Lemma lem4337648 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term349 _104190 _104196 x x' s s' t t') = (term345 _104190 _104196 x x' s s' t t').
Proof. exact (MK_COMB (@lem4337647 _104190 _104196 s t s' t') (@lem4337646 _104190 _104196 x x' s s' t t')). Qed.
Lemma lem4337649 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4337650 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term354 _104190 _104196 x x' s s' t t') = (term355 _104190 _104196 x x' s s' t t').
Proof. exact (MK_COMB (@lem4337649) (@lem4337648 _104190 _104196 x x' s s' t t')). Qed.
Lemma lem4337651 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (x'' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term351 _104190 _104196 x x' s s' t t' x'') = (term317 _104190 _104196 x x' s x'' s' t t').
Proof. exact (eq_refl (term351 _104190 _104196 x x' s s' t t' x'')). Qed.
Lemma lem4337652 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term187 _104190 _104196 s t s' t') = (term187 _104190 _104196 s t s' t').
Proof. exact (eq_refl (term187 _104190 _104196 s t s' t')). Qed.
Lemma lem4337653 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (x'' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term356 _104190 _104196 x x' s s' t t' x'') = (term357 _104190 _104196 x x' s x'' s' t t').
Proof. exact (MK_COMB (@lem4337652 _104190 _104196 s t s' t') (@lem4337651 _104190 _104196 x x' s x'' s' t t')). Qed.
Lemma lem4337654 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term358 _104190 _104196 x x' s s' t t') = (term359 _104190 _104196 x x' s s' t t').
Proof. exact (fun_ext (fun x'' : _104190 => @lem4337653 _104190 _104196 x x' s x'' s' t t')). Qed.
Lemma lem4337655 {_104190 : Type'} : (@ex _104190) = (@ex _104190).
Proof. exact (eq_refl (@ex _104190)). Qed.
Lemma lem4337656 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term350 _104190 _104196 x x' s s' t t') = (term360 _104190 _104196 x x' s s' t t').
Proof. exact (MK_COMB (@lem4337655 _104190) (@lem4337654 _104190 _104196 x x' s s' t t')). Qed.
Lemma lem4337657 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : ((term349 _104190 _104196 x x' s s' t t') = (term350 _104190 _104196 x x' s s' t t')) = ((term345 _104190 _104196 x x' s s' t t') = (term360 _104190 _104196 x x' s s' t t')).
Proof. exact (MK_COMB (@lem4337650 _104190 _104196 x x' s s' t t') (@lem4337656 _104190 _104196 x x' s s' t t')). Qed.
Lemma lem4337658 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term345 _104190 _104196 x x' s s' t t') = (term360 _104190 _104196 x x' s s' t t').
Proof. exact (EQ_MP (@lem4337657 _104190 _104196 x x' s s' t t') (@lem4337642 _104190 _104196 x x' s s' t t')). Qed.
Lemma lem4337660 {A : Type'} (P : Prop) (Q : A -> Prop) : (term242 A P Q) = (term243 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4337661 {_104196 : Type'} (P : Prop) (Q : _104196 -> Prop) : (term242 _104196 P Q) = (term243 _104196 P Q).
Proof. exact (@lem4337660 _104196 P Q). Qed.
Lemma lem4337662 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (x'' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term361 _104190 _104196 x x' s x'' s' t t') = (term362 _104190 _104196 x x' s x'' s' t t').
Proof. exact (@lem4337661 _104196 (term144 _104190 _104196 s t s' t') (term316 _104190 _104196 x x' s x'' s' t t')). Qed.
Lemma lem4337663 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (x'' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x''' : _104196) (t' : _104196 -> Prop) : (term363 _104190 _104196 x x' s x'' s' t t' x''') = (term314 _104190 _104196 x x' s x'' s' t x''' t').
Proof. exact (eq_refl (term363 _104190 _104196 x x' s x'' s' t t' x''')). Qed.
Lemma lem4337664 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (x'' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term364 _104190 _104196 x x' s x'' s' t t') = (term316 _104190 _104196 x x' s x'' s' t t').
Proof. exact (fun_ext (fun x''' : _104196 => @lem4337663 _104190 _104196 x x' s x'' s' t x''' t')). Qed.
Lemma lem4337665 {_104196 : Type'} : (@ex _104196) = (@ex _104196).
Proof. exact (eq_refl (@ex _104196)). Qed.
Lemma lem4337666 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (x'' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term365 _104190 _104196 x x' s x'' s' t t') = (term317 _104190 _104196 x x' s x'' s' t t').
Proof. exact (MK_COMB (@lem4337665 _104196) (@lem4337664 _104190 _104196 x x' s x'' s' t t')). Qed.
Lemma lem4337667 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term187 _104190 _104196 s t s' t') = (term187 _104190 _104196 s t s' t').
Proof. exact (eq_refl (term187 _104190 _104196 s t s' t')). Qed.
Lemma lem4337668 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (x'' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term361 _104190 _104196 x x' s x'' s' t t') = (term357 _104190 _104196 x x' s x'' s' t t').
Proof. exact (MK_COMB (@lem4337667 _104190 _104196 s t s' t') (@lem4337666 _104190 _104196 x x' s x'' s' t t')). Qed.
Lemma lem4337669 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4337670 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (x'' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term366 _104190 _104196 x x' s x'' s' t t') = (term367 _104190 _104196 x x' s x'' s' t t').
Proof. exact (MK_COMB (@lem4337669) (@lem4337668 _104190 _104196 x x' s x'' s' t t')). Qed.
Lemma lem4337671 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (x'' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x''' : _104196) (t' : _104196 -> Prop) : (term363 _104190 _104196 x x' s x'' s' t t' x''') = (term314 _104190 _104196 x x' s x'' s' t x''' t').
Proof. exact (eq_refl (term363 _104190 _104196 x x' s x'' s' t t' x''')). Qed.
Lemma lem4337672 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term187 _104190 _104196 s t s' t') = (term187 _104190 _104196 s t s' t').
Proof. exact (eq_refl (term187 _104190 _104196 s t s' t')). Qed.
Lemma lem4337673 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (x'' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x''' : _104196) (t' : _104196 -> Prop) : (term368 _104190 _104196 x x' s x'' s' t t' x''') = (term369 _104190 _104196 x x' s x'' s' t x''' t').
Proof. exact (MK_COMB (@lem4337672 _104190 _104196 s t s' t') (@lem4337671 _104190 _104196 x x' s x'' s' t x''' t')). Qed.
Lemma lem4337674 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (x'' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term370 _104190 _104196 x x' s x'' s' t t') = (term371 _104190 _104196 x x' s x'' s' t t').
Proof. exact (fun_ext (fun x''' : _104196 => @lem4337673 _104190 _104196 x x' s x'' s' t x''' t')). Qed.
Lemma lem4337675 {_104196 : Type'} : (@ex _104196) = (@ex _104196).
Proof. exact (eq_refl (@ex _104196)). Qed.
Lemma lem4337676 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (x'' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term362 _104190 _104196 x x' s x'' s' t t') = (term372 _104190 _104196 x x' s x'' s' t t').
Proof. exact (MK_COMB (@lem4337675 _104196) (@lem4337674 _104190 _104196 x x' s x'' s' t t')). Qed.
Lemma lem4337677 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (x'' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : ((term361 _104190 _104196 x x' s x'' s' t t') = (term362 _104190 _104196 x x' s x'' s' t t')) = ((term357 _104190 _104196 x x' s x'' s' t t') = (term372 _104190 _104196 x x' s x'' s' t t')).
Proof. exact (MK_COMB (@lem4337670 _104190 _104196 x x' s x'' s' t t') (@lem4337676 _104190 _104196 x x' s x'' s' t t')). Qed.
Lemma lem4337678 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (x'' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term357 _104190 _104196 x x' s x'' s' t t') = (term372 _104190 _104196 x x' s x'' s' t t').
Proof. exact (EQ_MP (@lem4337677 _104190 _104196 x x' s x'' s' t t') (@lem4337662 _104190 _104196 x x' s x'' s' t t')). Qed.
Lemma lem4337679 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term359 _104190 _104196 x x' s s' t t') = (term373 _104190 _104196 x x' s s' t t').
Proof. exact (fun_ext (fun x'' : _104190 => @lem4337678 _104190 _104196 x x' s x'' s' t t')). Qed.
Lemma lem4337680 {_104190 : Type'} : (@ex _104190) = (@ex _104190).
Proof. exact (eq_refl (@ex _104190)). Qed.
Lemma lem4337681 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term360 _104190 _104196 x x' s s' t t') = (term374 _104190 _104196 x x' s s' t t').
Proof. exact (MK_COMB (@lem4337680 _104190) (@lem4337679 _104190 _104196 x x' s s' t t')). Qed.
Lemma lem4337682 {_104190 _104196 : Type'} (x : _104190) (x' : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term345 _104190 _104196 x x' s s' t t') = (term374 _104190 _104196 x x' s s' t t').
Proof. exact (TRANS (@lem4337658 _104190 _104196 x x' s s' t t') (@lem4337681 _104190 _104196 x x' s s' t t')). Qed.
Lemma lem4337683 {_104190 _104196 : Type'} (x : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term347 _104190 _104196 x s s' t t') = (term375 _104190 _104196 x s s' t t').
Proof. exact (fun_ext (fun x' : _104196 => @lem4337682 _104190 _104196 x x' s s' t t')). Qed.
Lemma lem4337684 {_104196 : Type'} : (@ex _104196) = (@ex _104196).
Proof. exact (eq_refl (@ex _104196)). Qed.
Lemma lem4337685 {_104190 _104196 : Type'} (x : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term348 _104190 _104196 x s s' t t') = (term376 _104190 _104196 x s s' t t').
Proof. exact (MK_COMB (@lem4337684 _104196) (@lem4337683 _104190 _104196 x s s' t t')). Qed.
Lemma lem4337686 {_104190 _104196 : Type'} (x : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term333 _104190 _104196 x s s' t t') = (term376 _104190 _104196 x s s' t t').
Proof. exact (TRANS (@lem4337638 _104190 _104196 x s s' t t') (@lem4337685 _104190 _104196 x s s' t t')). Qed.
Lemma lem4337687 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term335 _104190 _104196 s s' t t') = (term377 _104190 _104196 s s' t t').
Proof. exact (fun_ext (fun x : _104190 => @lem4337686 _104190 _104196 x s s' t t')). Qed.
Lemma lem4337688 {_104190 : Type'} : (@ex _104190) = (@ex _104190).
Proof. exact (eq_refl (@ex _104190)). Qed.
Lemma lem4337689 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term336 _104190 _104196 s s' t t') = (term378 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337688 _104190) (@lem4337687 _104190 _104196 s s' t t')). Qed.
Lemma lem4337690 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term324 _104190 _104196 s s' t t') = (term378 _104190 _104196 s s' t t').
Proof. exact (TRANS (@lem4337618 _104190 _104196 s s' t t') (@lem4337689 _104190 _104196 s s' t t')). Qed.
Lemma lem4337691 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term189 _104190 _104196 s s' t t') = (term378 _104190 _104196 s s' t t').
Proof. exact (TRANS (@lem4337598 _104190 _104196 s s' t t') (@lem4337690 _104190 _104196 s s' t t')). Qed.
Lemma lem4337692 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4337693 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term191 _104190 _104196 s s' t t') = (term379 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337692) (@lem4337691 _104190 _104196 s s' t t')). Qed.
Lemma lem4337695 {A : Type'} (P : A -> Prop) (Q : Prop) : (term225 A P Q) = (term226 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4337696 {_104190 : Type'} (P : _104190 -> Prop) (Q : Prop) : (term225 _104190 P Q) = (term226 _104190 P Q).
Proof. exact (@lem4337695 _104190 P Q). Qed.
Lemma lem4337697 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term380 _104190 _104196 s s' t t') = (term381 _104190 _104196 s s' t t').
Proof. exact (@lem4337696 _104190 (term141 _104190 _104196 s t s' t') (term181 _104190 _104196 s s' t t')). Qed.
Lemma lem4337698 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term382 _104190 _104196 s t s' t' p1) = (term133 _104190 _104196 s t p1 s' t').
Proof. exact (eq_refl (term382 _104190 _104196 s t s' t' p1)). Qed.
Lemma lem4337699 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term383 _104190 _104196 s t s' t') = (term141 _104190 _104196 s t s' t').
Proof. exact (fun_ext (fun p1 : _104190 => @lem4337698 _104190 _104196 s t p1 s' t')). Qed.
Lemma lem4337700 {_104190 : Type'} : (@ex _104190) = (@ex _104190).
Proof. exact (eq_refl (@ex _104190)). Qed.
Lemma lem4337701 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term384 _104190 _104196 s t s' t') = (term142 _104190 _104196 s t s' t').
Proof. exact (MK_COMB (@lem4337700 _104190) (@lem4337699 _104190 _104196 s t s' t')). Qed.
Lemma lem4337702 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4337703 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term385 _104190 _104196 s t s' t') = (term183 _104190 _104196 s t s' t').
Proof. exact (MK_COMB (@lem4337702) (@lem4337701 _104190 _104196 s t s' t')). Qed.
Lemma lem4337704 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term181 _104190 _104196 s s' t t') = (term181 _104190 _104196 s s' t t').
Proof. exact (eq_refl (term181 _104190 _104196 s s' t t')). Qed.
Lemma lem4337705 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term380 _104190 _104196 s s' t t') = (term185 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337703 _104190 _104196 s t s' t') (@lem4337704 _104190 _104196 s s' t t')). Qed.
Lemma lem4337706 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4337707 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term386 _104190 _104196 s s' t t') = (term387 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337706) (@lem4337705 _104190 _104196 s s' t t')). Qed.
Lemma lem4337708 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term382 _104190 _104196 s t s' t' p1) = (term133 _104190 _104196 s t p1 s' t').
Proof. exact (eq_refl (term382 _104190 _104196 s t s' t' p1)). Qed.
Lemma lem4337709 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4337710 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term388 _104190 _104196 s t s' t' p1) = (term389 _104190 _104196 s t p1 s' t').
Proof. exact (MK_COMB (@lem4337709) (@lem4337708 _104190 _104196 s t p1 s' t')). Qed.
Lemma lem4337711 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term181 _104190 _104196 s s' t t') = (term181 _104190 _104196 s s' t t').
Proof. exact (eq_refl (term181 _104190 _104196 s s' t t')). Qed.
Lemma lem4337712 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term390 _104190 _104196 p1 s s' t t') = (term391 _104190 _104196 p1 s s' t t').
Proof. exact (MK_COMB (@lem4337710 _104190 _104196 s t p1 s' t') (@lem4337711 _104190 _104196 s s' t t')). Qed.
Lemma lem4337713 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term392 _104190 _104196 s s' t t') = (term393 _104190 _104196 s s' t t').
Proof. exact (fun_ext (fun p1 : _104190 => @lem4337712 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337714 {_104190 : Type'} : (@ex _104190) = (@ex _104190).
Proof. exact (eq_refl (@ex _104190)). Qed.
Lemma lem4337715 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term381 _104190 _104196 s s' t t') = (term394 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337714 _104190) (@lem4337713 _104190 _104196 s s' t t')). Qed.
Lemma lem4337716 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : ((term380 _104190 _104196 s s' t t') = (term381 _104190 _104196 s s' t t')) = ((term185 _104190 _104196 s s' t t') = (term394 _104190 _104196 s s' t t')).
Proof. exact (MK_COMB (@lem4337707 _104190 _104196 s s' t t') (@lem4337715 _104190 _104196 s s' t t')). Qed.
Lemma lem4337717 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term185 _104190 _104196 s s' t t') = (term394 _104190 _104196 s s' t t').
Proof. exact (EQ_MP (@lem4337716 _104190 _104196 s s' t t') (@lem4337697 _104190 _104196 s s' t t')). Qed.
Lemma lem4337719 {A : Type'} (P : A -> Prop) (Q : Prop) : (term225 A P Q) = (term226 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4337720 {_104196 : Type'} (P : _104196 -> Prop) (Q : Prop) : (term225 _104196 P Q) = (term226 _104196 P Q).
Proof. exact (@lem4337719 _104196 P Q). Qed.
Lemma lem4337721 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term395 _104190 _104196 p1 s s' t t') = (term396 _104190 _104196 p1 s s' t t').
Proof. exact (@lem4337720 _104196 (term132 _104190 _104196 s t p1 s' t') (term181 _104190 _104196 s s' t t')). Qed.
Lemma lem4337722 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (p2 : _104196) (t' : _104196 -> Prop) : (term397 _104190 _104196 s t p1 s' t' p2) = (term119 _104190 _104196 s t p1 s' p2 t').
Proof. exact (eq_refl (term397 _104190 _104196 s t p1 s' t' p2)). Qed.
Lemma lem4337723 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term398 _104190 _104196 s t p1 s' t') = (term132 _104190 _104196 s t p1 s' t').
Proof. exact (fun_ext (fun p2 : _104196 => @lem4337722 _104190 _104196 s t p1 s' p2 t')). Qed.
Lemma lem4337724 {_104196 : Type'} : (@ex _104196) = (@ex _104196).
Proof. exact (eq_refl (@ex _104196)). Qed.
Lemma lem4337725 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term399 _104190 _104196 s t p1 s' t') = (term133 _104190 _104196 s t p1 s' t').
Proof. exact (MK_COMB (@lem4337724 _104196) (@lem4337723 _104190 _104196 s t p1 s' t')). Qed.
Lemma lem4337726 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4337727 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term400 _104190 _104196 s t p1 s' t') = (term389 _104190 _104196 s t p1 s' t').
Proof. exact (MK_COMB (@lem4337726) (@lem4337725 _104190 _104196 s t p1 s' t')). Qed.
Lemma lem4337728 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term181 _104190 _104196 s s' t t') = (term181 _104190 _104196 s s' t t').
Proof. exact (eq_refl (term181 _104190 _104196 s s' t t')). Qed.
Lemma lem4337729 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term395 _104190 _104196 p1 s s' t t') = (term391 _104190 _104196 p1 s s' t t').
Proof. exact (MK_COMB (@lem4337727 _104190 _104196 s t p1 s' t') (@lem4337728 _104190 _104196 s s' t t')). Qed.
Lemma lem4337730 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4337731 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term401 _104190 _104196 p1 s s' t t') = (term402 _104190 _104196 p1 s s' t t').
Proof. exact (MK_COMB (@lem4337730) (@lem4337729 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337732 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (p2 : _104196) (t' : _104196 -> Prop) : (term397 _104190 _104196 s t p1 s' t' p2) = (term119 _104190 _104196 s t p1 s' p2 t').
Proof. exact (eq_refl (term397 _104190 _104196 s t p1 s' t' p2)). Qed.
Lemma lem4337733 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4337734 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (p2 : _104196) (t' : _104196 -> Prop) : (term403 _104190 _104196 s t p1 s' t' p2) = (term404 _104190 _104196 s t p1 s' p2 t').
Proof. exact (MK_COMB (@lem4337733) (@lem4337732 _104190 _104196 s t p1 s' p2 t')). Qed.
Lemma lem4337735 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term181 _104190 _104196 s s' t t') = (term181 _104190 _104196 s s' t t').
Proof. exact (eq_refl (term181 _104190 _104196 s s' t t')). Qed.
Lemma lem4337736 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term405 _104190 _104196 p1 p2 s s' t t') = (term406 _104190 _104196 p1 p2 s s' t t').
Proof. exact (MK_COMB (@lem4337734 _104190 _104196 s t p1 s' p2 t') (@lem4337735 _104190 _104196 s s' t t')). Qed.
Lemma lem4337737 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term407 _104190 _104196 p1 s s' t t') = (term408 _104190 _104196 p1 s s' t t').
Proof. exact (fun_ext (fun p2 : _104196 => @lem4337736 _104190 _104196 p1 p2 s s' t t')). Qed.
Lemma lem4337738 {_104196 : Type'} : (@ex _104196) = (@ex _104196).
Proof. exact (eq_refl (@ex _104196)). Qed.
Lemma lem4337739 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term396 _104190 _104196 p1 s s' t t') = (term409 _104190 _104196 p1 s s' t t').
Proof. exact (MK_COMB (@lem4337738 _104196) (@lem4337737 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337740 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : ((term395 _104190 _104196 p1 s s' t t') = (term396 _104190 _104196 p1 s s' t t')) = ((term391 _104190 _104196 p1 s s' t t') = (term409 _104190 _104196 p1 s s' t t')).
Proof. exact (MK_COMB (@lem4337731 _104190 _104196 p1 s s' t t') (@lem4337739 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337741 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term391 _104190 _104196 p1 s s' t t') = (term409 _104190 _104196 p1 s s' t t').
Proof. exact (EQ_MP (@lem4337740 _104190 _104196 p1 s s' t t') (@lem4337721 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337742 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term393 _104190 _104196 s s' t t') = (term410 _104190 _104196 s s' t t').
Proof. exact (fun_ext (fun p1 : _104190 => @lem4337741 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337743 {_104190 : Type'} : (@ex _104190) = (@ex _104190).
Proof. exact (eq_refl (@ex _104190)). Qed.
Lemma lem4337744 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term394 _104190 _104196 s s' t t') = (term411 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337743 _104190) (@lem4337742 _104190 _104196 s s' t t')). Qed.
Lemma lem4337745 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term185 _104190 _104196 s s' t t') = (term411 _104190 _104196 s s' t t').
Proof. exact (TRANS (@lem4337717 _104190 _104196 s s' t t') (@lem4337744 _104190 _104196 s s' t t')). Qed.
Lemma lem4337746 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term193 _104190 _104196 s s' t t') = (term412 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337693 _104190 _104196 s s' t t') (@lem4337745 _104190 _104196 s s' t t')). Qed.
Lemma lem4337748 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term413 A P Q) = (term414 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4337749 {_104190 : Type'} (P : _104190 -> Prop) (Q : _104190 -> Prop) : (term413 _104190 P Q) = (term414 _104190 P Q).
Proof. exact (@lem4337748 _104190 P Q). Qed.
Lemma lem4337750 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term415 _104190 _104196 s s' t t') = (term416 _104190 _104196 s s' t t').
Proof. exact (@lem4337749 _104190 (term377 _104190 _104196 s s' t t') (term410 _104190 _104196 s s' t t')). Qed.
Lemma lem4337751 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term417 _104190 _104196 s s' t t' p1) = (term376 _104190 _104196 p1 s s' t t').
Proof. exact (eq_refl (term417 _104190 _104196 s s' t t' p1)). Qed.
Lemma lem4337752 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term418 _104190 _104196 s s' t t') = (term377 _104190 _104196 s s' t t').
Proof. exact (fun_ext (fun p1 : _104190 => @lem4337751 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337753 {_104190 : Type'} : (@ex _104190) = (@ex _104190).
Proof. exact (eq_refl (@ex _104190)). Qed.
Lemma lem4337754 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term419 _104190 _104196 s s' t t') = (term378 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337753 _104190) (@lem4337752 _104190 _104196 s s' t t')). Qed.
Lemma lem4337755 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4337756 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term420 _104190 _104196 s s' t t') = (term379 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337755) (@lem4337754 _104190 _104196 s s' t t')). Qed.
Lemma lem4337757 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term421 _104190 _104196 s s' t t' p1) = (term409 _104190 _104196 p1 s s' t t').
Proof. exact (eq_refl (term421 _104190 _104196 s s' t t' p1)). Qed.
Lemma lem4337758 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term422 _104190 _104196 s s' t t') = (term410 _104190 _104196 s s' t t').
Proof. exact (fun_ext (fun p1 : _104190 => @lem4337757 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337759 {_104190 : Type'} : (@ex _104190) = (@ex _104190).
Proof. exact (eq_refl (@ex _104190)). Qed.
Lemma lem4337760 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term423 _104190 _104196 s s' t t') = (term411 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337759 _104190) (@lem4337758 _104190 _104196 s s' t t')). Qed.
Lemma lem4337761 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term415 _104190 _104196 s s' t t') = (term412 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337756 _104190 _104196 s s' t t') (@lem4337760 _104190 _104196 s s' t t')). Qed.
Lemma lem4337762 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4337763 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term424 _104190 _104196 s s' t t') = (term425 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337762) (@lem4337761 _104190 _104196 s s' t t')). Qed.
Lemma lem4337764 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term417 _104190 _104196 s s' t t' p1) = (term376 _104190 _104196 p1 s s' t t').
Proof. exact (eq_refl (term417 _104190 _104196 s s' t t' p1)). Qed.
Lemma lem4337765 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4337766 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term426 _104190 _104196 s s' t t' p1) = (term427 _104190 _104196 p1 s s' t t').
Proof. exact (MK_COMB (@lem4337765) (@lem4337764 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337767 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term421 _104190 _104196 s s' t t' p1) = (term409 _104190 _104196 p1 s s' t t').
Proof. exact (eq_refl (term421 _104190 _104196 s s' t t' p1)). Qed.
Lemma lem4337768 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term428 _104190 _104196 s s' t t' p1) = (term429 _104190 _104196 p1 s s' t t').
Proof. exact (MK_COMB (@lem4337766 _104190 _104196 p1 s s' t t') (@lem4337767 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337769 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term430 _104190 _104196 s s' t t') = (term431 _104190 _104196 s s' t t').
Proof. exact (fun_ext (fun p1 : _104190 => @lem4337768 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337770 {_104190 : Type'} : (@ex _104190) = (@ex _104190).
Proof. exact (eq_refl (@ex _104190)). Qed.
Lemma lem4337771 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term416 _104190 _104196 s s' t t') = (term432 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337770 _104190) (@lem4337769 _104190 _104196 s s' t t')). Qed.
Lemma lem4337772 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : ((term415 _104190 _104196 s s' t t') = (term416 _104190 _104196 s s' t t')) = ((term412 _104190 _104196 s s' t t') = (term432 _104190 _104196 s s' t t')).
Proof. exact (MK_COMB (@lem4337763 _104190 _104196 s s' t t') (@lem4337771 _104190 _104196 s s' t t')). Qed.
Lemma lem4337773 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term412 _104190 _104196 s s' t t') = (term432 _104190 _104196 s s' t t').
Proof. exact (EQ_MP (@lem4337772 _104190 _104196 s s' t t') (@lem4337750 _104190 _104196 s s' t t')). Qed.
Lemma lem4337776 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term433 _104190 _104196 s s' t t') = (term433 _104190 _104196 s s' t t').
Proof. exact (eq_refl (term433 _104190 _104196 s s' t t')). Qed.
Lemma lem4337777 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term433 _104190 _104196 s s' t t') = ((term412 _104190 _104196 s s' t t') = (term432 _104190 _104196 s s' t t')).
Proof. exact (eq_refl (term433 _104190 _104196 s s' t t')). Qed.
Lemma lem4337778 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term434 _104190 _104196 s s' t t') = (term434 _104190 _104196 s s' t t').
Proof. exact (eq_refl (term434 _104190 _104196 s s' t t')). Qed.
Lemma lem4337779 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : ((term433 _104190 _104196 s s' t t') = (term433 _104190 _104196 s s' t t')) = ((term433 _104190 _104196 s s' t t') = ((term412 _104190 _104196 s s' t t') = (term432 _104190 _104196 s s' t t'))).
Proof. exact (MK_COMB (@lem4337778 _104190 _104196 s s' t t') (@lem4337777 _104190 _104196 s s' t t')). Qed.
Lemma lem4337780 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term433 _104190 _104196 s s' t t') = ((term412 _104190 _104196 s s' t t') = (term432 _104190 _104196 s s' t t')).
Proof. exact (eq_refl (term433 _104190 _104196 s s' t t')). Qed.
Lemma lem4337781 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4337782 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term434 _104190 _104196 s s' t t') = (term435 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337781) (@lem4337780 _104190 _104196 s s' t t')). Qed.
Lemma lem4337783 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : ((term412 _104190 _104196 s s' t t') = (term432 _104190 _104196 s s' t t')) = ((term412 _104190 _104196 s s' t t') = (term432 _104190 _104196 s s' t t')).
Proof. exact (eq_refl ((term412 _104190 _104196 s s' t t') = (term432 _104190 _104196 s s' t t'))). Qed.
Lemma lem4337784 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : ((term433 _104190 _104196 s s' t t') = ((term412 _104190 _104196 s s' t t') = (term432 _104190 _104196 s s' t t'))) = (((term412 _104190 _104196 s s' t t') = (term432 _104190 _104196 s s' t t')) = ((term412 _104190 _104196 s s' t t') = (term432 _104190 _104196 s s' t t'))).
Proof. exact (MK_COMB (@lem4337782 _104190 _104196 s s' t t') (@lem4337783 _104190 _104196 s s' t t')). Qed.
Lemma lem4337785 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : ((term433 _104190 _104196 s s' t t') = (term433 _104190 _104196 s s' t t')) = (((term412 _104190 _104196 s s' t t') = (term432 _104190 _104196 s s' t t')) = ((term412 _104190 _104196 s s' t t') = (term432 _104190 _104196 s s' t t'))).
Proof. exact (TRANS (@lem4337779 _104190 _104196 s s' t t') (@lem4337784 _104190 _104196 s s' t t')). Qed.
Lemma lem4337786 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : ((term412 _104190 _104196 s s' t t') = (term432 _104190 _104196 s s' t t')) = ((term412 _104190 _104196 s s' t t') = (term432 _104190 _104196 s s' t t')).
Proof. exact (EQ_MP (@lem4337785 _104190 _104196 s s' t t') (@lem4337776 _104190 _104196 s s' t t')). Qed.
Lemma lem4337787 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term412 _104190 _104196 s s' t t') = (term432 _104190 _104196 s s' t t').
Proof. exact (EQ_MP (@lem4337786 _104190 _104196 s s' t t') (@lem4337773 _104190 _104196 s s' t t')). Qed.
Lemma lem4337789 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term413 A P Q) = (term414 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4337790 {_104196 : Type'} (P : _104196 -> Prop) (Q : _104196 -> Prop) : (term413 _104196 P Q) = (term414 _104196 P Q).
Proof. exact (@lem4337789 _104196 P Q). Qed.
Lemma lem4337791 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term436 _104190 _104196 p1 s s' t t') = (term437 _104190 _104196 p1 s s' t t').
Proof. exact (@lem4337790 _104196 (term375 _104190 _104196 p1 s s' t t') (term408 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337792 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term438 _104190 _104196 p1 s s' t t' p2) = (term374 _104190 _104196 p1 p2 s s' t t').
Proof. exact (eq_refl (term438 _104190 _104196 p1 s s' t t' p2)). Qed.
Lemma lem4337793 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term439 _104190 _104196 p1 s s' t t') = (term375 _104190 _104196 p1 s s' t t').
Proof. exact (fun_ext (fun p2 : _104196 => @lem4337792 _104190 _104196 p1 p2 s s' t t')). Qed.
Lemma lem4337794 {_104196 : Type'} : (@ex _104196) = (@ex _104196).
Proof. exact (eq_refl (@ex _104196)). Qed.
Lemma lem4337795 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term440 _104190 _104196 p1 s s' t t') = (term376 _104190 _104196 p1 s s' t t').
Proof. exact (MK_COMB (@lem4337794 _104196) (@lem4337793 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337796 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4337797 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term441 _104190 _104196 p1 s s' t t') = (term427 _104190 _104196 p1 s s' t t').
Proof. exact (MK_COMB (@lem4337796) (@lem4337795 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337798 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term442 _104190 _104196 p1 s s' t t' p2) = (term406 _104190 _104196 p1 p2 s s' t t').
Proof. exact (eq_refl (term442 _104190 _104196 p1 s s' t t' p2)). Qed.
Lemma lem4337799 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term443 _104190 _104196 p1 s s' t t') = (term408 _104190 _104196 p1 s s' t t').
Proof. exact (fun_ext (fun p2 : _104196 => @lem4337798 _104190 _104196 p1 p2 s s' t t')). Qed.
Lemma lem4337800 {_104196 : Type'} : (@ex _104196) = (@ex _104196).
Proof. exact (eq_refl (@ex _104196)). Qed.
Lemma lem4337801 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term444 _104190 _104196 p1 s s' t t') = (term409 _104190 _104196 p1 s s' t t').
Proof. exact (MK_COMB (@lem4337800 _104196) (@lem4337799 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337802 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term436 _104190 _104196 p1 s s' t t') = (term429 _104190 _104196 p1 s s' t t').
Proof. exact (MK_COMB (@lem4337797 _104190 _104196 p1 s s' t t') (@lem4337801 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337803 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4337804 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term445 _104190 _104196 p1 s s' t t') = (term446 _104190 _104196 p1 s s' t t').
Proof. exact (MK_COMB (@lem4337803) (@lem4337802 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337805 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term438 _104190 _104196 p1 s s' t t' p2) = (term374 _104190 _104196 p1 p2 s s' t t').
Proof. exact (eq_refl (term438 _104190 _104196 p1 s s' t t' p2)). Qed.
Lemma lem4337806 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4337807 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term447 _104190 _104196 p1 s s' t t' p2) = (term448 _104190 _104196 p1 p2 s s' t t').
Proof. exact (MK_COMB (@lem4337806) (@lem4337805 _104190 _104196 p1 p2 s s' t t')). Qed.
Lemma lem4337808 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term442 _104190 _104196 p1 s s' t t' p2) = (term406 _104190 _104196 p1 p2 s s' t t').
Proof. exact (eq_refl (term442 _104190 _104196 p1 s s' t t' p2)). Qed.
Lemma lem4337809 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term449 _104190 _104196 p1 s s' t t' p2) = (term450 _104190 _104196 p1 p2 s s' t t').
Proof. exact (MK_COMB (@lem4337807 _104190 _104196 p1 p2 s s' t t') (@lem4337808 _104190 _104196 p1 p2 s s' t t')). Qed.
Lemma lem4337810 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term451 _104190 _104196 p1 s s' t t') = (term452 _104190 _104196 p1 s s' t t').
Proof. exact (fun_ext (fun p2 : _104196 => @lem4337809 _104190 _104196 p1 p2 s s' t t')). Qed.
Lemma lem4337811 {_104196 : Type'} : (@ex _104196) = (@ex _104196).
Proof. exact (eq_refl (@ex _104196)). Qed.
Lemma lem4337812 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term437 _104190 _104196 p1 s s' t t') = (term453 _104190 _104196 p1 s s' t t').
Proof. exact (MK_COMB (@lem4337811 _104196) (@lem4337810 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337813 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : ((term436 _104190 _104196 p1 s s' t t') = (term437 _104190 _104196 p1 s s' t t')) = ((term429 _104190 _104196 p1 s s' t t') = (term453 _104190 _104196 p1 s s' t t')).
Proof. exact (MK_COMB (@lem4337804 _104190 _104196 p1 s s' t t') (@lem4337812 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337814 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term429 _104190 _104196 p1 s s' t t') = (term453 _104190 _104196 p1 s s' t t').
Proof. exact (EQ_MP (@lem4337813 _104190 _104196 p1 s s' t t') (@lem4337791 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337817 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term454 _104190 _104196 p1 s s' t t') = (term454 _104190 _104196 p1 s s' t t').
Proof. exact (eq_refl (term454 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337818 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term454 _104190 _104196 p1 s s' t t') = ((term429 _104190 _104196 p1 s s' t t') = (term453 _104190 _104196 p1 s s' t t')).
Proof. exact (eq_refl (term454 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337819 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term455 _104190 _104196 p1 s s' t t') = (term455 _104190 _104196 p1 s s' t t').
Proof. exact (eq_refl (term455 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337820 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : ((term454 _104190 _104196 p1 s s' t t') = (term454 _104190 _104196 p1 s s' t t')) = ((term454 _104190 _104196 p1 s s' t t') = ((term429 _104190 _104196 p1 s s' t t') = (term453 _104190 _104196 p1 s s' t t'))).
Proof. exact (MK_COMB (@lem4337819 _104190 _104196 p1 s s' t t') (@lem4337818 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337821 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term454 _104190 _104196 p1 s s' t t') = ((term429 _104190 _104196 p1 s s' t t') = (term453 _104190 _104196 p1 s s' t t')).
Proof. exact (eq_refl (term454 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337822 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4337823 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term455 _104190 _104196 p1 s s' t t') = (term456 _104190 _104196 p1 s s' t t').
Proof. exact (MK_COMB (@lem4337822) (@lem4337821 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337824 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : ((term429 _104190 _104196 p1 s s' t t') = (term453 _104190 _104196 p1 s s' t t')) = ((term429 _104190 _104196 p1 s s' t t') = (term453 _104190 _104196 p1 s s' t t')).
Proof. exact (eq_refl ((term429 _104190 _104196 p1 s s' t t') = (term453 _104190 _104196 p1 s s' t t'))). Qed.
Lemma lem4337825 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : ((term454 _104190 _104196 p1 s s' t t') = ((term429 _104190 _104196 p1 s s' t t') = (term453 _104190 _104196 p1 s s' t t'))) = (((term429 _104190 _104196 p1 s s' t t') = (term453 _104190 _104196 p1 s s' t t')) = ((term429 _104190 _104196 p1 s s' t t') = (term453 _104190 _104196 p1 s s' t t'))).
Proof. exact (MK_COMB (@lem4337823 _104190 _104196 p1 s s' t t') (@lem4337824 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337826 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : ((term454 _104190 _104196 p1 s s' t t') = (term454 _104190 _104196 p1 s s' t t')) = (((term429 _104190 _104196 p1 s s' t t') = (term453 _104190 _104196 p1 s s' t t')) = ((term429 _104190 _104196 p1 s s' t t') = (term453 _104190 _104196 p1 s s' t t'))).
Proof. exact (TRANS (@lem4337820 _104190 _104196 p1 s s' t t') (@lem4337825 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337827 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : ((term429 _104190 _104196 p1 s s' t t') = (term453 _104190 _104196 p1 s s' t t')) = ((term429 _104190 _104196 p1 s s' t t') = (term453 _104190 _104196 p1 s s' t t')).
Proof. exact (EQ_MP (@lem4337826 _104190 _104196 p1 s s' t t') (@lem4337817 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337828 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term429 _104190 _104196 p1 s s' t t') = (term453 _104190 _104196 p1 s s' t t').
Proof. exact (EQ_MP (@lem4337827 _104190 _104196 p1 s s' t t') (@lem4337814 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337830 {A : Type'} (P : A -> Prop) (Q : Prop) : (term194 A P Q) = (term195 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4337831 {_104190 : Type'} (P : _104190 -> Prop) (Q : Prop) : (term194 _104190 P Q) = (term195 _104190 P Q).
Proof. exact (@lem4337830 _104190 P Q). Qed.
Lemma lem4337832 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term457 _104190 _104196 p1 p2 s s' t t') = (term458 _104190 _104196 p1 p2 s s' t t').
Proof. exact (@lem4337831 _104190 (term373 _104190 _104196 p1 p2 s s' t t') (term406 _104190 _104196 p1 p2 s s' t t')). Qed.
Lemma lem4337833 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term459 _104190 _104196 p1 p2 s s' t t' x') = (term372 _104190 _104196 p1 p2 s x' s' t t').
Proof. exact (eq_refl (term459 _104190 _104196 p1 p2 s s' t t' x')). Qed.
Lemma lem4337834 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term460 _104190 _104196 p1 p2 s s' t t') = (term373 _104190 _104196 p1 p2 s s' t t').
Proof. exact (fun_ext (fun x' : _104190 => @lem4337833 _104190 _104196 p1 p2 s x' s' t t')). Qed.
Lemma lem4337835 {_104190 : Type'} : (@ex _104190) = (@ex _104190).
Proof. exact (eq_refl (@ex _104190)). Qed.
Lemma lem4337836 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term461 _104190 _104196 p1 p2 s s' t t') = (term374 _104190 _104196 p1 p2 s s' t t').
Proof. exact (MK_COMB (@lem4337835 _104190) (@lem4337834 _104190 _104196 p1 p2 s s' t t')). Qed.
Lemma lem4337837 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4337838 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term462 _104190 _104196 p1 p2 s s' t t') = (term448 _104190 _104196 p1 p2 s s' t t').
Proof. exact (MK_COMB (@lem4337837) (@lem4337836 _104190 _104196 p1 p2 s s' t t')). Qed.
Lemma lem4337839 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term406 _104190 _104196 p1 p2 s s' t t') = (term406 _104190 _104196 p1 p2 s s' t t').
Proof. exact (eq_refl (term406 _104190 _104196 p1 p2 s s' t t')). Qed.
Lemma lem4337840 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term457 _104190 _104196 p1 p2 s s' t t') = (term450 _104190 _104196 p1 p2 s s' t t').
Proof. exact (MK_COMB (@lem4337838 _104190 _104196 p1 p2 s s' t t') (@lem4337839 _104190 _104196 p1 p2 s s' t t')). Qed.
Lemma lem4337841 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4337842 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term463 _104190 _104196 p1 p2 s s' t t') = (term464 _104190 _104196 p1 p2 s s' t t').
Proof. exact (MK_COMB (@lem4337841) (@lem4337840 _104190 _104196 p1 p2 s s' t t')). Qed.
Lemma lem4337843 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term459 _104190 _104196 p1 p2 s s' t t' x') = (term372 _104190 _104196 p1 p2 s x' s' t t').
Proof. exact (eq_refl (term459 _104190 _104196 p1 p2 s s' t t' x')). Qed.
Lemma lem4337844 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4337845 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term465 _104190 _104196 p1 p2 s s' t t' x') = (term466 _104190 _104196 p1 p2 s x' s' t t').
Proof. exact (MK_COMB (@lem4337844) (@lem4337843 _104190 _104196 p1 p2 s x' s' t t')). Qed.
Lemma lem4337846 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term406 _104190 _104196 p1 p2 s s' t t') = (term406 _104190 _104196 p1 p2 s s' t t').
Proof. exact (eq_refl (term406 _104190 _104196 p1 p2 s s' t t')). Qed.
Lemma lem4337847 {_104190 _104196 : Type'} (x' : _104190) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term467 _104190 _104196 x' p1 p2 s s' t t') = (term468 _104190 _104196 x' p1 p2 s s' t t').
Proof. exact (MK_COMB (@lem4337845 _104190 _104196 p1 p2 s x' s' t t') (@lem4337846 _104190 _104196 p1 p2 s s' t t')). Qed.
Lemma lem4337848 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term469 _104190 _104196 p1 p2 s s' t t') = (term470 _104190 _104196 p1 p2 s s' t t').
Proof. exact (fun_ext (fun x' : _104190 => @lem4337847 _104190 _104196 x' p1 p2 s s' t t')). Qed.
Lemma lem4337849 {_104190 : Type'} : (@ex _104190) = (@ex _104190).
Proof. exact (eq_refl (@ex _104190)). Qed.
Lemma lem4337850 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term458 _104190 _104196 p1 p2 s s' t t') = (term471 _104190 _104196 p1 p2 s s' t t').
Proof. exact (MK_COMB (@lem4337849 _104190) (@lem4337848 _104190 _104196 p1 p2 s s' t t')). Qed.
Lemma lem4337851 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : ((term457 _104190 _104196 p1 p2 s s' t t') = (term458 _104190 _104196 p1 p2 s s' t t')) = ((term450 _104190 _104196 p1 p2 s s' t t') = (term471 _104190 _104196 p1 p2 s s' t t')).
Proof. exact (MK_COMB (@lem4337842 _104190 _104196 p1 p2 s s' t t') (@lem4337850 _104190 _104196 p1 p2 s s' t t')). Qed.
Lemma lem4337852 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term450 _104190 _104196 p1 p2 s s' t t') = (term471 _104190 _104196 p1 p2 s s' t t').
Proof. exact (EQ_MP (@lem4337851 _104190 _104196 p1 p2 s s' t t') (@lem4337832 _104190 _104196 p1 p2 s s' t t')). Qed.
Lemma lem4337854 {A : Type'} (P : A -> Prop) (Q : Prop) : (term194 A P Q) = (term195 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4337855 {_104196 : Type'} (P : _104196 -> Prop) (Q : Prop) : (term194 _104196 P Q) = (term195 _104196 P Q).
Proof. exact (@lem4337854 _104196 P Q). Qed.
Lemma lem4337856 {_104190 _104196 : Type'} (x' : _104190) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term472 _104190 _104196 x' p1 p2 s s' t t') = (term473 _104190 _104196 x' p1 p2 s s' t t').
Proof. exact (@lem4337855 _104196 (term371 _104190 _104196 p1 p2 s x' s' t t') (term406 _104190 _104196 p1 p2 s s' t t')). Qed.
Lemma lem4337857 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) : (term474 _104190 _104196 p1 p2 s x' s' t t' x'') = (term369 _104190 _104196 p1 p2 s x' s' t x'' t').
Proof. exact (eq_refl (term474 _104190 _104196 p1 p2 s x' s' t t' x'')). Qed.
Lemma lem4337858 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term475 _104190 _104196 p1 p2 s x' s' t t') = (term371 _104190 _104196 p1 p2 s x' s' t t').
Proof. exact (fun_ext (fun x'' : _104196 => @lem4337857 _104190 _104196 p1 p2 s x' s' t x'' t')). Qed.
Lemma lem4337859 {_104196 : Type'} : (@ex _104196) = (@ex _104196).
Proof. exact (eq_refl (@ex _104196)). Qed.
Lemma lem4337860 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term476 _104190 _104196 p1 p2 s x' s' t t') = (term372 _104190 _104196 p1 p2 s x' s' t t').
Proof. exact (MK_COMB (@lem4337859 _104196) (@lem4337858 _104190 _104196 p1 p2 s x' s' t t')). Qed.
Lemma lem4337861 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4337862 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term477 _104190 _104196 p1 p2 s x' s' t t') = (term466 _104190 _104196 p1 p2 s x' s' t t').
Proof. exact (MK_COMB (@lem4337861) (@lem4337860 _104190 _104196 p1 p2 s x' s' t t')). Qed.
Lemma lem4337863 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term406 _104190 _104196 p1 p2 s s' t t') = (term406 _104190 _104196 p1 p2 s s' t t').
Proof. exact (eq_refl (term406 _104190 _104196 p1 p2 s s' t t')). Qed.
Lemma lem4337864 {_104190 _104196 : Type'} (x' : _104190) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term472 _104190 _104196 x' p1 p2 s s' t t') = (term468 _104190 _104196 x' p1 p2 s s' t t').
Proof. exact (MK_COMB (@lem4337862 _104190 _104196 p1 p2 s x' s' t t') (@lem4337863 _104190 _104196 p1 p2 s s' t t')). Qed.
Lemma lem4337865 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4337866 {_104190 _104196 : Type'} (x' : _104190) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term478 _104190 _104196 x' p1 p2 s s' t t') = (term479 _104190 _104196 x' p1 p2 s s' t t').
Proof. exact (MK_COMB (@lem4337865) (@lem4337864 _104190 _104196 x' p1 p2 s s' t t')). Qed.
Lemma lem4337867 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) : (term474 _104190 _104196 p1 p2 s x' s' t t' x'') = (term369 _104190 _104196 p1 p2 s x' s' t x'' t').
Proof. exact (eq_refl (term474 _104190 _104196 p1 p2 s x' s' t t' x'')). Qed.
Lemma lem4337868 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4337869 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) : (term480 _104190 _104196 p1 p2 s x' s' t t' x'') = (term481 _104190 _104196 p1 p2 s x' s' t x'' t').
Proof. exact (MK_COMB (@lem4337868) (@lem4337867 _104190 _104196 p1 p2 s x' s' t x'' t')). Qed.
Lemma lem4337870 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term406 _104190 _104196 p1 p2 s s' t t') = (term406 _104190 _104196 p1 p2 s s' t t').
Proof. exact (eq_refl (term406 _104190 _104196 p1 p2 s s' t t')). Qed.
Lemma lem4337871 {_104190 _104196 : Type'} (x' : _104190) (x'' : _104196) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term482 _104190 _104196 x' x'' p1 p2 s s' t t') = (term483 _104190 _104196 x' x'' p1 p2 s s' t t').
Proof. exact (MK_COMB (@lem4337869 _104190 _104196 p1 p2 s x' s' t x'' t') (@lem4337870 _104190 _104196 p1 p2 s s' t t')). Qed.
Lemma lem4337872 {_104190 _104196 : Type'} (x' : _104190) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term484 _104190 _104196 x' p1 p2 s s' t t') = (term485 _104190 _104196 x' p1 p2 s s' t t').
Proof. exact (fun_ext (fun x'' : _104196 => @lem4337871 _104190 _104196 x' x'' p1 p2 s s' t t')). Qed.
Lemma lem4337873 {_104196 : Type'} : (@ex _104196) = (@ex _104196).
Proof. exact (eq_refl (@ex _104196)). Qed.
Lemma lem4337874 {_104190 _104196 : Type'} (x' : _104190) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term473 _104190 _104196 x' p1 p2 s s' t t') = (term486 _104190 _104196 x' p1 p2 s s' t t').
Proof. exact (MK_COMB (@lem4337873 _104196) (@lem4337872 _104190 _104196 x' p1 p2 s s' t t')). Qed.
Lemma lem4337875 {_104190 _104196 : Type'} (x' : _104190) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : ((term472 _104190 _104196 x' p1 p2 s s' t t') = (term473 _104190 _104196 x' p1 p2 s s' t t')) = ((term468 _104190 _104196 x' p1 p2 s s' t t') = (term486 _104190 _104196 x' p1 p2 s s' t t')).
Proof. exact (MK_COMB (@lem4337866 _104190 _104196 x' p1 p2 s s' t t') (@lem4337874 _104190 _104196 x' p1 p2 s s' t t')). Qed.
Lemma lem4337876 {_104190 _104196 : Type'} (x' : _104190) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term468 _104190 _104196 x' p1 p2 s s' t t') = (term486 _104190 _104196 x' p1 p2 s s' t t').
Proof. exact (EQ_MP (@lem4337875 _104190 _104196 x' p1 p2 s s' t t') (@lem4337856 _104190 _104196 x' p1 p2 s s' t t')). Qed.
Lemma lem4337877 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term470 _104190 _104196 p1 p2 s s' t t') = (term487 _104190 _104196 p1 p2 s s' t t').
Proof. exact (fun_ext (fun x' : _104190 => @lem4337876 _104190 _104196 x' p1 p2 s s' t t')). Qed.
Lemma lem4337878 {_104190 : Type'} : (@ex _104190) = (@ex _104190).
Proof. exact (eq_refl (@ex _104190)). Qed.
Lemma lem4337879 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term471 _104190 _104196 p1 p2 s s' t t') = (term488 _104190 _104196 p1 p2 s s' t t').
Proof. exact (MK_COMB (@lem4337878 _104190) (@lem4337877 _104190 _104196 p1 p2 s s' t t')). Qed.
Lemma lem4337880 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term450 _104190 _104196 p1 p2 s s' t t') = (term488 _104190 _104196 p1 p2 s s' t t').
Proof. exact (TRANS (@lem4337852 _104190 _104196 p1 p2 s s' t t') (@lem4337879 _104190 _104196 p1 p2 s s' t t')). Qed.
Lemma lem4337881 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term452 _104190 _104196 p1 s s' t t') = (term489 _104190 _104196 p1 s s' t t').
Proof. exact (fun_ext (fun p2 : _104196 => @lem4337880 _104190 _104196 p1 p2 s s' t t')). Qed.
Lemma lem4337882 {_104196 : Type'} : (@ex _104196) = (@ex _104196).
Proof. exact (eq_refl (@ex _104196)). Qed.
Lemma lem4337883 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term453 _104190 _104196 p1 s s' t t') = (term490 _104190 _104196 p1 s s' t t').
Proof. exact (MK_COMB (@lem4337882 _104196) (@lem4337881 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337884 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term429 _104190 _104196 p1 s s' t t') = (term490 _104190 _104196 p1 s s' t t').
Proof. exact (TRANS (@lem4337828 _104190 _104196 p1 s s' t t') (@lem4337883 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337885 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term431 _104190 _104196 s s' t t') = (term491 _104190 _104196 s s' t t').
Proof. exact (fun_ext (fun p1 : _104190 => @lem4337884 _104190 _104196 p1 s s' t t')). Qed.
Lemma lem4337886 {_104190 : Type'} : (@ex _104190) = (@ex _104190).
Proof. exact (eq_refl (@ex _104190)). Qed.
Lemma lem4337887 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term432 _104190 _104196 s s' t t') = (term492 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337886 _104190) (@lem4337885 _104190 _104196 s s' t t')). Qed.
Lemma lem4337888 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term412 _104190 _104196 s s' t t') = (term492 _104190 _104196 s s' t t').
Proof. exact (TRANS (@lem4337787 _104190 _104196 s s' t t') (@lem4337887 _104190 _104196 s s' t t')). Qed.
Lemma lem4337890 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term193 _104190 _104196 s s' t t') = (term492 _104190 _104196 s s' t t').
Proof. exact (TRANS (@lem4337746 _104190 _104196 s s' t t') (@lem4337888 _104190 _104196 s s' t t')). Qed.
Lemma lem4337891 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term114 _104190 _104196 s s' t t') = (term492 _104190 _104196 s s' t t').
Proof. exact (TRANS (@lem4337059 _104190 _104196 s s' t t') (@lem4337890 _104190 _104196 s s' t t')). Qed.
Lemma lem4337892 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term114 _104190 _104196 s s' t t') : term492 _104190 _104196 s s' t t'.
Proof. exact (EQ_MP (@lem4337891 _104190 _104196 s s' t t') (@lem4336876 _104190 _104196 s s' t t' h1)). Qed.
Lemma lem4337893 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term490 _104190 _104196 p1 s s' t t') : term490 _104190 _104196 p1 s s' t t'.
Proof. exact (h1). Qed.
Lemma lem4337894 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term488 _104190 _104196 p1 p2 s s' t t') : term488 _104190 _104196 p1 p2 s s' t t'.
Proof. exact (h1). Qed.
Lemma lem4337895 {_104190 _104196 : Type'} (x' : _104190) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term486 _104190 _104196 x' p1 p2 s s' t t') : term486 _104190 _104196 x' p1 p2 s s' t t'.
Proof. exact (h1). Qed.
Lemma lem4337896 {_104190 _104196 : Type'} (x' : _104190) (x'' : _104196) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term483 _104190 _104196 x' x'' p1 p2 s s' t t') : term483 _104190 _104196 x' x'' p1 p2 s s' t t'.
Proof. exact (h1). Qed.
Lemma lem4337911 {_104196 : Type'} (t : _104196 -> Prop) (x : _104196) (t' : _104196 -> Prop) : (term155 _104196 t x t') = (term155 _104196 t x t').
Proof. exact (eq_refl (term155 _104196 t x t')). Qed.
Lemma lem4337912 {_104196 : Type'} (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term163 _104196 t t') = (term163 _104196 t t').
Proof. exact (fun_ext (fun x : _104196 => @lem4337911 _104196 t x t')). Qed.
Lemma lem4337913 {_104196 : Type'} : (@all _104196) = (@all _104196).
Proof. exact (eq_refl (@all _104196)). Qed.
Lemma lem4337914 {_104196 : Type'} (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term164 _104196 t t') = (term164 _104196 t t').
Proof. exact (MK_COMB (@lem4337913 _104196) (@lem4337912 _104196 t t')). Qed.
Lemma lem4337929 {_104190 : Type'} (s : _104190 -> Prop) (x : _104190) (s' : _104190 -> Prop) : (term155 _104190 s x s') = (term155 _104190 s x s').
Proof. exact (eq_refl (term155 _104190 s x s')). Qed.
Lemma lem4337930 {_104190 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) : (term163 _104190 s s') = (term163 _104190 s s').
Proof. exact (fun_ext (fun x : _104190 => @lem4337929 _104190 s x s')). Qed.
Lemma lem4337931 {_104190 : Type'} : (@all _104190) = (@all _104190).
Proof. exact (eq_refl (@all _104190)). Qed.
Lemma lem4337932 {_104190 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) : (term164 _104190 s s') = (term164 _104190 s s').
Proof. exact (MK_COMB (@lem4337931 _104190) (@lem4337930 _104190 s s')). Qed.
Lemma lem4337933 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4337934 {_104190 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) : (term170 _104190 s s') = (term170 _104190 s s').
Proof. exact (MK_COMB (@lem4337933) (@lem4337932 _104190 s s')). Qed.
Lemma lem4337935 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term171 _104190 _104196 s s' t t') = (term171 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337934 _104190 s s') (@lem4337914 _104196 t t')). Qed.
Lemma lem4337942 {_104196 : Type'} (x : _104196) (t : _104196 -> Prop) : (term73 _104196 x t) = (term73 _104196 x t).
Proof. exact (eq_refl (term73 _104196 x t)). Qed.
Lemma lem4337943 {_104196 : Type'} (t : _104196 -> Prop) : (term75 _104196 t) = (term75 _104196 t).
Proof. exact (fun_ext (fun x : _104196 => @lem4337942 _104196 x t)). Qed.
Lemma lem4337944 {_104196 : Type'} : (@all _104196) = (@all _104196).
Proof. exact (eq_refl (@all _104196)). Qed.
Lemma lem4337945 {_104196 : Type'} (t : _104196 -> Prop) : (term76 _104196 t) = (term76 _104196 t).
Proof. exact (MK_COMB (@lem4337944 _104196) (@lem4337943 _104196 t)). Qed.
Lemma lem4337946 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4337947 {_104196 : Type'} (t : _104196 -> Prop) : (term78 _104196 t) = (term78 _104196 t).
Proof. exact (MK_COMB (@lem4337946) (@lem4337945 _104196 t)). Qed.
Lemma lem4337948 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term177 _104190 _104196 s s' t t') = (term177 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337947 _104196 t) (@lem4337935 _104190 _104196 s s' t t')). Qed.
Lemma lem4337955 {_104190 : Type'} (x : _104190) (s : _104190 -> Prop) : (term73 _104190 x s) = (term73 _104190 x s).
Proof. exact (eq_refl (term73 _104190 x s)). Qed.
Lemma lem4337956 {_104190 : Type'} (s : _104190 -> Prop) : (term75 _104190 s) = (term75 _104190 s).
Proof. exact (fun_ext (fun x : _104190 => @lem4337955 _104190 x s)). Qed.
Lemma lem4337957 {_104190 : Type'} : (@all _104190) = (@all _104190).
Proof. exact (eq_refl (@all _104190)). Qed.
Lemma lem4337958 {_104190 : Type'} (s : _104190 -> Prop) : (term76 _104190 s) = (term76 _104190 s).
Proof. exact (MK_COMB (@lem4337957 _104190) (@lem4337956 _104190 s)). Qed.
Lemma lem4337959 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4337960 {_104190 : Type'} (s : _104190 -> Prop) : (term78 _104190 s) = (term78 _104190 s).
Proof. exact (MK_COMB (@lem4337959) (@lem4337958 _104190 s)). Qed.
Lemma lem4337961 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term181 _104190 _104196 s s' t t') = (term181 _104190 _104196 s s' t t').
Proof. exact (MK_COMB (@lem4337960 _104190 s) (@lem4337948 _104190 _104196 s s' t t')). Qed.
Lemma lem4337996 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (p2 : _104196) (t' : _104196 -> Prop) : (term404 _104190 _104196 s t p1 s' p2 t') = (term404 _104190 _104196 s t p1 s' p2 t').
Proof. exact (eq_refl (term404 _104190 _104196 s t p1 s' p2 t')). Qed.
Lemma lem4337997 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term406 _104190 _104196 p1 p2 s s' t t') = (term406 _104190 _104196 p1 p2 s s' t t').
Proof. exact (MK_COMB (@lem4337996 _104190 _104196 s t p1 s' p2 t') (@lem4337961 _104190 _104196 s s' t t')). Qed.
Lemma lem4338046 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) : (term314 _104190 _104196 p1 p2 s x' s' t x'' t') = (term314 _104190 _104196 p1 p2 s x' s' t x'' t').
Proof. exact (eq_refl (term314 _104190 _104196 p1 p2 s x' s' t x'' t')). Qed.
Lemma lem4338079 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (p2 : _104196) (t' : _104196 -> Prop) : (term124 _104190 _104196 s t p1 s' p2 t') = (term124 _104190 _104196 s t p1 s' p2 t').
Proof. exact (eq_refl (term124 _104190 _104196 s t p1 s' p2 t')). Qed.
Lemma lem4338080 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term134 _104190 _104196 s t p1 s' t') = (term134 _104190 _104196 s t p1 s' t').
Proof. exact (fun_ext (fun p2 : _104196 => @lem4338079 _104190 _104196 s t p1 s' p2 t')). Qed.
Lemma lem4338081 {_104196 : Type'} : (@all _104196) = (@all _104196).
Proof. exact (eq_refl (@all _104196)). Qed.
Lemma lem4338082 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (p1 : _104190) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term135 _104190 _104196 s t p1 s' t') = (term135 _104190 _104196 s t p1 s' t').
Proof. exact (MK_COMB (@lem4338081 _104196) (@lem4338080 _104190 _104196 s t p1 s' t')). Qed.
Lemma lem4338083 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term143 _104190 _104196 s t s' t') = (term143 _104190 _104196 s t s' t').
Proof. exact (fun_ext (fun p1 : _104190 => @lem4338082 _104190 _104196 s t p1 s' t')). Qed.
Lemma lem4338084 {_104190 : Type'} : (@all _104190) = (@all _104190).
Proof. exact (eq_refl (@all _104190)). Qed.
Lemma lem4338085 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term144 _104190 _104196 s t s' t') = (term144 _104190 _104196 s t s' t').
Proof. exact (MK_COMB (@lem4338084 _104190) (@lem4338083 _104190 _104196 s t s' t')). Qed.
Lemma lem4338086 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4338087 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) (t' : _104196 -> Prop) : (term187 _104190 _104196 s t s' t') = (term187 _104190 _104196 s t s' t').
Proof. exact (MK_COMB (@lem4338086) (@lem4338085 _104190 _104196 s t s' t')). Qed.
Lemma lem4338088 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) : (term369 _104190 _104196 p1 p2 s x' s' t x'' t') = (term369 _104190 _104196 p1 p2 s x' s' t x'' t').
Proof. exact (MK_COMB (@lem4338087 _104190 _104196 s t s' t') (@lem4338046 _104190 _104196 p1 p2 s x' s' t x'' t')). Qed.
Lemma lem4338089 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4338090 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) : (term481 _104190 _104196 p1 p2 s x' s' t x'' t') = (term481 _104190 _104196 p1 p2 s x' s' t x'' t').
Proof. exact (MK_COMB (@lem4338089) (@lem4338088 _104190 _104196 p1 p2 s x' s' t x'' t')). Qed.
Lemma lem4338091 {_104190 _104196 : Type'} (x' : _104190) (x'' : _104196) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term483 _104190 _104196 x' x'' p1 p2 s s' t t') = (term483 _104190 _104196 x' x'' p1 p2 s s' t t').
Proof. exact (MK_COMB (@lem4338090 _104190 _104196 p1 p2 s x' s' t x'' t') (@lem4337997 _104190 _104196 p1 p2 s s' t t')). Qed.
Lemma lem4338092 {_104190 _104196 : Type'} (x' : _104190) (x'' : _104196) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term483 _104190 _104196 x' x'' p1 p2 s s' t t') : term483 _104190 _104196 x' x'' p1 p2 s s' t t'.
Proof. exact (EQ_MP (@lem4338091 _104190 _104196 x' x'' p1 p2 s s' t t') (@lem4337896 _104190 _104196 x' x'' p1 p2 s s' t t' h1)). Qed.
Lemma lem4338093 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : term369 _104190 _104196 p1 p2 s x' s' t x'' t'.
Proof. exact (h1). Qed.
Lemma lem4338094 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term406 _104190 _104196 p1 p2 s s' t t') : term406 _104190 _104196 p1 p2 s s' t t'.
Proof. exact (h1). Qed.
Lemma lem4338095 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : term314 _104190 _104196 p1 p2 s x' s' t x'' t'.
Proof. exact (proj2 (@lem4338093 _104190 _104196 p1 p2 s x' s' t x'' t' h1)). Qed.
Lemma lem4338096 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : term144 _104190 _104196 s t s' t'.
Proof. exact (proj1 (@lem4338093 _104190 _104196 p1 p2 s x' s' t x'' t' h1)). Qed.
Lemma lem4338097 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : term264 _104190 _104196 p2 s x' s' t x'' t'.
Proof. exact (proj2 (@lem4338095 _104190 _104196 p1 p2 s x' s' t x'' t' h1)). Qed.
Lemma lem4338099 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : term218 _104190 _104196 s x' s' t x'' t'.
Proof. exact (proj2 (@lem4338097 _104190 _104196 p1 p2 s x' s' t x'' t' h1)). Qed.
Lemma lem4338101 {_104190 : Type'} (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (h1 : term154 _104190 s x' s') : term154 _104190 s x' s'.
Proof. exact (h1). Qed.
Lemma lem4338102 {_104196 : Type'} (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term154 _104196 t x'' t') : term154 _104196 t x'' t'.
Proof. exact (h1). Qed.
Lemma lem4338107 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term406 _104190 _104196 p1 p2 s s' t t') : term181 _104190 _104196 s s' t t'.
Proof. exact (proj2 (@lem4338094 _104190 _104196 p1 p2 s s' t t' h1)). Qed.
Lemma lem4338108 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term406 _104190 _104196 p1 p2 s s' t t') : term119 _104190 _104196 s t p1 s' p2 t'.
Proof. exact (proj1 (@lem4338094 _104190 _104196 p1 p2 s s' t t' h1)). Qed.
Lemma lem4338109 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term406 _104190 _104196 p1 p2 s s' t t') : term116 _104190 _104196 p1 s' p2 t'.
Proof. exact (proj2 (@lem4338108 _104190 _104196 p1 p2 s s' t t' h1)). Qed.
Lemma lem4338110 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term406 _104190 _104196 p1 p2 s s' t t') : term18 _104190 _104196 p1 s p2 t.
Proof. exact (proj1 (@lem4338108 _104190 _104196 p1 p2 s s' t t' h1)). Qed.
Lemma lem4338115 {_104190 : Type'} (s : _104190 -> Prop) (h1 : term76 _104190 s) : term76 _104190 s.
Proof. exact (h1). Qed.
Lemma lem4338116 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term177 _104190 _104196 s s' t t') : term177 _104190 _104196 s s' t t'.
Proof. exact (h1). Qed.
Lemma lem4338117 {_104196 : Type'} (t : _104196 -> Prop) (h1 : term76 _104196 t) : term76 _104196 t.
Proof. exact (h1). Qed.
Lemma lem4338118 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term171 _104190 _104196 s s' t t') : term171 _104190 _104196 s s' t t'.
Proof. exact (h1). Qed.
Lemma lem4338120 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term171 _104190 _104196 s s' t t') : term164 _104190 s s'.
Proof. exact (proj1 (@lem4338118 _104190 _104196 s s' t t' h1)). Qed.
Lemma lem4338121 {_104190 : Type'} (s : _104190 -> Prop) (h1 : term76 _104190 s) : term76 _104190 s.
Proof. exact (h1). Qed.
Lemma lem4338122 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term177 _104190 _104196 s s' t t') : term177 _104190 _104196 s s' t t'.
Proof. exact (h1). Qed.
Lemma lem4338123 {_104196 : Type'} (t : _104196 -> Prop) (h1 : term76 _104196 t) : term76 _104196 t.
Proof. exact (h1). Qed.
Lemma lem4338124 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term171 _104190 _104196 s s' t t') : term171 _104190 _104196 s s' t t'.
Proof. exact (h1). Qed.
Lemma lem4338125 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term171 _104190 _104196 s s' t t') : term164 _104196 t t'.
Proof. exact (proj2 (@lem4338124 _104190 _104196 s s' t t' h1)). Qed.
Lemma lem4338150 {_104190 _104196 : Type'} (s' : _104190 -> Prop) (p1 : _104190) (s : _104190 -> Prop) (t : _104196 -> Prop) (p2 : _104196) (t' : _104196 -> Prop) : (term124 _104190 _104196 s t p1 s' p2 t') = (term493 _104190 _104196 s' p1 s t p2 t').
Proof. exact (@lem19490 (@IN _104190 p1 s') (term116 _104190 _104196 p1 s p2 t) (@IN _104196 p2 t')). Qed.
Lemma lem4338151 {_104190 _104196 : Type'} (s' : _104190 -> Prop) (p1 : _104190) (s : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term134 _104190 _104196 s t p1 s' t') = (term494 _104190 _104196 s' p1 s t t').
Proof. exact (fun_ext (fun p2 : _104196 => @lem4338150 _104190 _104196 s' p1 s t p2 t')). Qed.
Lemma lem4338152 {_104196 : Type'} : (@all _104196) = (@all _104196).
Proof. exact (eq_refl (@all _104196)). Qed.
Lemma lem4338153 {_104190 _104196 : Type'} (s' : _104190 -> Prop) (p1 : _104190) (s : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term135 _104190 _104196 s t p1 s' t') = (term495 _104190 _104196 s' p1 s t t').
Proof. exact (MK_COMB (@lem4338152 _104196) (@lem4338151 _104190 _104196 s' p1 s t t')). Qed.
Lemma lem4338154 {_104190 _104196 : Type'} (s' : _104190 -> Prop) (s : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term143 _104190 _104196 s t s' t') = (term496 _104190 _104196 s' s t t').
Proof. exact (fun_ext (fun p1 : _104190 => @lem4338153 _104190 _104196 s' p1 s t t')). Qed.
Lemma lem4338155 {_104190 : Type'} : (@all _104190) = (@all _104190).
Proof. exact (eq_refl (@all _104190)). Qed.
Lemma lem4338157 {_104190 _104196 : Type'} (s' : _104190 -> Prop) (s : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term144 _104190 _104196 s t s' t') = (term497 _104190 _104196 s' s t t').
Proof. exact (MK_COMB (@lem4338155 _104190) (@lem4338154 _104190 _104196 s' s t t')). Qed.
Lemma lem4338158 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : term497 _104190 _104196 s' s t t'.
Proof. exact (EQ_MP (@lem4338157 _104190 _104196 s' s t t') (@lem4338096 _104190 _104196 p1 p2 s x' s' t x'' t' h1)). Qed.
Lemma lem4338198 {_104190 _104196 : Type'} (s' : _104190 -> Prop) (p1 : _104190) (s : _104190 -> Prop) (t : _104196 -> Prop) (p2 : _104196) (t' : _104196 -> Prop) : (term124 _104190 _104196 s t p1 s' p2 t') = (term493 _104190 _104196 s' p1 s t p2 t').
Proof. exact (@lem19490 (@IN _104190 p1 s') (term116 _104190 _104196 p1 s p2 t) (@IN _104196 p2 t')). Qed.
Lemma lem4338199 {_104190 _104196 : Type'} (s' : _104190 -> Prop) (p1 : _104190) (s : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term134 _104190 _104196 s t p1 s' t') = (term494 _104190 _104196 s' p1 s t t').
Proof. exact (fun_ext (fun p2 : _104196 => @lem4338198 _104190 _104196 s' p1 s t p2 t')). Qed.
Lemma lem4338200 {_104196 : Type'} : (@all _104196) = (@all _104196).
Proof. exact (eq_refl (@all _104196)). Qed.
Lemma lem4338201 {_104190 _104196 : Type'} (s' : _104190 -> Prop) (p1 : _104190) (s : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term135 _104190 _104196 s t p1 s' t') = (term495 _104190 _104196 s' p1 s t t').
Proof. exact (MK_COMB (@lem4338200 _104196) (@lem4338199 _104190 _104196 s' p1 s t t')). Qed.
Lemma lem4338202 {_104190 _104196 : Type'} (s' : _104190 -> Prop) (s : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term143 _104190 _104196 s t s' t') = (term496 _104190 _104196 s' s t t').
Proof. exact (fun_ext (fun p1 : _104190 => @lem4338201 _104190 _104196 s' p1 s t t')). Qed.
Lemma lem4338203 {_104190 : Type'} : (@all _104190) = (@all _104190).
Proof. exact (eq_refl (@all _104190)). Qed.
Lemma lem4338205 {_104190 _104196 : Type'} (s' : _104190 -> Prop) (s : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term144 _104190 _104196 s t s' t') = (term497 _104190 _104196 s' s t t').
Proof. exact (MK_COMB (@lem4338203 _104190) (@lem4338202 _104190 _104196 s' s t t')). Qed.
Lemma lem4338206 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : term497 _104190 _104196 s' s t t'.
Proof. exact (EQ_MP (@lem4338205 _104190 _104196 s' s t t') (@lem4338096 _104190 _104196 p1 p2 s x' s' t x'' t' h1)). Qed.
Lemma lem4338236 {_104190 : Type'} (x : _104190) (s : _104190 -> Prop) : (term73 _104190 x s) = (term73 _104190 x s).
Proof. exact (eq_refl (term73 _104190 x s)). Qed.
Lemma lem4338237 {_104190 : Type'} (s : _104190 -> Prop) : (term75 _104190 s) = (term75 _104190 s).
Proof. exact (fun_ext (fun x : _104190 => @lem4338236 _104190 x s)). Qed.
Lemma lem4338238 {_104190 : Type'} : (@all _104190) = (@all _104190).
Proof. exact (eq_refl (@all _104190)). Qed.
Lemma lem4338240 {_104190 : Type'} (s : _104190 -> Prop) : (term76 _104190 s) = (term76 _104190 s).
Proof. exact (MK_COMB (@lem4338238 _104190) (@lem4338237 _104190 s)). Qed.
Lemma lem4338241 {_104190 : Type'} (s : _104190 -> Prop) (h1 : term76 _104190 s) : term76 _104190 s.
Proof. exact (EQ_MP (@lem4338240 _104190 s) (@lem4338115 _104190 s h1)). Qed.
Lemma lem4338255 {_104196 : Type'} (x : _104196) (t : _104196 -> Prop) : (term73 _104196 x t) = (term73 _104196 x t).
Proof. exact (eq_refl (term73 _104196 x t)). Qed.
Lemma lem4338256 {_104196 : Type'} (t : _104196 -> Prop) : (term75 _104196 t) = (term75 _104196 t).
Proof. exact (fun_ext (fun x : _104196 => @lem4338255 _104196 x t)). Qed.
Lemma lem4338257 {_104196 : Type'} : (@all _104196) = (@all _104196).
Proof. exact (eq_refl (@all _104196)). Qed.
Lemma lem4338259 {_104196 : Type'} (t : _104196 -> Prop) : (term76 _104196 t) = (term76 _104196 t).
Proof. exact (MK_COMB (@lem4338257 _104196) (@lem4338256 _104196 t)). Qed.
Lemma lem4338260 {_104196 : Type'} (t : _104196 -> Prop) (h1 : term76 _104196 t) : term76 _104196 t.
Proof. exact (EQ_MP (@lem4338259 _104196 t) (@lem4338117 _104196 t h1)). Qed.
Lemma lem4338272 {_104190 : Type'} (p1 : _104190) (s' : _104190 -> Prop) (h1 : term73 _104190 p1 s') : term73 _104190 p1 s'.
Proof. exact (h1). Qed.
Lemma lem4338280 {_104190 : Type'} (s : _104190 -> Prop) (x : _104190) (s' : _104190 -> Prop) : (term155 _104190 s x s') = (term155 _104190 s x s').
Proof. exact (eq_refl (term155 _104190 s x s')). Qed.
Lemma lem4338281 {_104190 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) : (term163 _104190 s s') = (term163 _104190 s s').
Proof. exact (fun_ext (fun x : _104190 => @lem4338280 _104190 s x s')). Qed.
Lemma lem4338282 {_104190 : Type'} : (@all _104190) = (@all _104190).
Proof. exact (eq_refl (@all _104190)). Qed.
Lemma lem4338284 {_104190 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) : (term164 _104190 s s') = (term164 _104190 s s').
Proof. exact (MK_COMB (@lem4338282 _104190) (@lem4338281 _104190 s s')). Qed.
Lemma lem4338285 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term171 _104190 _104196 s s' t t') : term164 _104190 s s'.
Proof. exact (EQ_MP (@lem4338284 _104190 s s') (@lem4338120 _104190 _104196 s s' t t' h1)). Qed.
Lemma lem4338312 {_104190 : Type'} (x : _104190) (s : _104190 -> Prop) : (term73 _104190 x s) = (term73 _104190 x s).
Proof. exact (eq_refl (term73 _104190 x s)). Qed.
Lemma lem4338313 {_104190 : Type'} (s : _104190 -> Prop) : (term75 _104190 s) = (term75 _104190 s).
Proof. exact (fun_ext (fun x : _104190 => @lem4338312 _104190 x s)). Qed.
Lemma lem4338314 {_104190 : Type'} : (@all _104190) = (@all _104190).
Proof. exact (eq_refl (@all _104190)). Qed.
Lemma lem4338316 {_104190 : Type'} (s : _104190 -> Prop) : (term76 _104190 s) = (term76 _104190 s).
Proof. exact (MK_COMB (@lem4338314 _104190) (@lem4338313 _104190 s)). Qed.
Lemma lem4338317 {_104190 : Type'} (s : _104190 -> Prop) (h1 : term76 _104190 s) : term76 _104190 s.
Proof. exact (EQ_MP (@lem4338316 _104190 s) (@lem4338121 _104190 s h1)). Qed.
Lemma lem4338331 {_104196 : Type'} (x : _104196) (t : _104196 -> Prop) : (term73 _104196 x t) = (term73 _104196 x t).
Proof. exact (eq_refl (term73 _104196 x t)). Qed.
Lemma lem4338332 {_104196 : Type'} (t : _104196 -> Prop) : (term75 _104196 t) = (term75 _104196 t).
Proof. exact (fun_ext (fun x : _104196 => @lem4338331 _104196 x t)). Qed.
Lemma lem4338333 {_104196 : Type'} : (@all _104196) = (@all _104196).
Proof. exact (eq_refl (@all _104196)). Qed.
Lemma lem4338335 {_104196 : Type'} (t : _104196 -> Prop) : (term76 _104196 t) = (term76 _104196 t).
Proof. exact (MK_COMB (@lem4338333 _104196) (@lem4338332 _104196 t)). Qed.
Lemma lem4338336 {_104196 : Type'} (t : _104196 -> Prop) (h1 : term76 _104196 t) : term76 _104196 t.
Proof. exact (EQ_MP (@lem4338335 _104196 t) (@lem4338123 _104196 t h1)). Qed.
Lemma lem4338348 {_104196 : Type'} (p2 : _104196) (t' : _104196 -> Prop) (h1 : term73 _104196 p2 t') : term73 _104196 p2 t'.
Proof. exact (h1). Qed.
Lemma lem4338369 {_104196 : Type'} (t : _104196 -> Prop) (x : _104196) (t' : _104196 -> Prop) : (term155 _104196 t x t') = (term155 _104196 t x t').
Proof. exact (eq_refl (term155 _104196 t x t')). Qed.
Lemma lem4338370 {_104196 : Type'} (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term163 _104196 t t') = (term163 _104196 t t').
Proof. exact (fun_ext (fun x : _104196 => @lem4338369 _104196 t x t')). Qed.
Lemma lem4338371 {_104196 : Type'} : (@all _104196) = (@all _104196).
Proof. exact (eq_refl (@all _104196)). Qed.
Lemma lem4338373 {_104196 : Type'} (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term164 _104196 t t') = (term164 _104196 t t').
Proof. exact (MK_COMB (@lem4338371 _104196) (@lem4338370 _104196 t t')). Qed.
Lemma lem4338374 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term171 _104190 _104196 s s' t t') : term164 _104196 t t'.
Proof. exact (EQ_MP (@lem4338373 _104196 t t') (@lem4338125 _104190 _104196 s s' t t' h1)). Qed.
Lemma lem4338375 {_104190 _104196 : Type'} (_49538 : _104190) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : term498 _104190 _104196 s' s t t' _49538.
Proof. exact (@lem4338158 _104190 _104196 p1 p2 s x' s' t x'' t' h1 _49538). Qed.
Lemma lem4338376 {_104190 _104196 : Type'} (s' : _104190 -> Prop) (_49538 : _104190) (s : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term498 _104190 _104196 s' s t t' _49538) = (term495 _104190 _104196 s' _49538 s t t').
Proof. exact (eq_refl (term498 _104190 _104196 s' s t t' _49538)). Qed.
Lemma lem4338377 {_104190 _104196 : Type'} (_49538 : _104190) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : term495 _104190 _104196 s' _49538 s t t'.
Proof. exact (EQ_MP (@lem4338376 _104190 _104196 s' _49538 s t t') (@lem4338375 _104190 _104196 _49538 p1 p2 s x' s' t x'' t' h1)). Qed.
Lemma lem4338378 {_104190 _104196 : Type'} (_49538 : _104190) (_49539 : _104196) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : term499 _104190 _104196 s' _49538 s t t' _49539.
Proof. exact (@lem4338377 _104190 _104196 _49538 p1 p2 s x' s' t x'' t' h1 _49539). Qed.
Lemma lem4338379 {_104190 _104196 : Type'} (s' : _104190 -> Prop) (_49538 : _104190) (s : _104190 -> Prop) (t : _104196 -> Prop) (_49539 : _104196) (t' : _104196 -> Prop) : (term499 _104190 _104196 s' _49538 s t t' _49539) = (term493 _104190 _104196 s' _49538 s t _49539 t').
Proof. exact (eq_refl (term499 _104190 _104196 s' _49538 s t t' _49539)). Qed.
Lemma lem4338380 {_104190 _104196 : Type'} (_49538 : _104190) (_49539 : _104196) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : term493 _104190 _104196 s' _49538 s t _49539 t'.
Proof. exact (EQ_MP (@lem4338379 _104190 _104196 s' _49538 s t _49539 t') (@lem4338378 _104190 _104196 _49538 _49539 p1 p2 s x' s' t x'' t' h1)). Qed.
Lemma lem4338381 {_104190 _104196 : Type'} (_49540 : _104190) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : term498 _104190 _104196 s' s t t' _49540.
Proof. exact (@lem4338206 _104190 _104196 p1 p2 s x' s' t x'' t' h1 _49540). Qed.
Lemma lem4338382 {_104190 _104196 : Type'} (s' : _104190 -> Prop) (_49540 : _104190) (s : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term498 _104190 _104196 s' s t t' _49540) = (term495 _104190 _104196 s' _49540 s t t').
Proof. exact (eq_refl (term498 _104190 _104196 s' s t t' _49540)). Qed.
Lemma lem4338383 {_104190 _104196 : Type'} (_49540 : _104190) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : term495 _104190 _104196 s' _49540 s t t'.
Proof. exact (EQ_MP (@lem4338382 _104190 _104196 s' _49540 s t t') (@lem4338381 _104190 _104196 _49540 p1 p2 s x' s' t x'' t' h1)). Qed.
Lemma lem4338384 {_104190 _104196 : Type'} (_49540 : _104190) (_49541 : _104196) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : term499 _104190 _104196 s' _49540 s t t' _49541.
Proof. exact (@lem4338383 _104190 _104196 _49540 p1 p2 s x' s' t x'' t' h1 _49541). Qed.
Lemma lem4338385 {_104190 _104196 : Type'} (s' : _104190 -> Prop) (_49540 : _104190) (s : _104190 -> Prop) (t : _104196 -> Prop) (_49541 : _104196) (t' : _104196 -> Prop) : (term499 _104190 _104196 s' _49540 s t t' _49541) = (term493 _104190 _104196 s' _49540 s t _49541 t').
Proof. exact (eq_refl (term499 _104190 _104196 s' _49540 s t t' _49541)). Qed.
Lemma lem4338386 {_104190 _104196 : Type'} (_49540 : _104190) (_49541 : _104196) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : term493 _104190 _104196 s' _49540 s t _49541 t'.
Proof. exact (EQ_MP (@lem4338385 _104190 _104196 s' _49540 s t _49541 t') (@lem4338384 _104190 _104196 _49540 _49541 p1 p2 s x' s' t x'' t' h1)). Qed.
Lemma lem4338387 {_104190 : Type'} (_49542 : _104190) (s : _104190 -> Prop) (h1 : term76 _104190 s) : term148 _104190 s _49542.
Proof. exact (@lem4338241 _104190 s h1 _49542). Qed.
Lemma lem4338388 {_104190 : Type'} (_49542 : _104190) (s : _104190 -> Prop) : (term148 _104190 s _49542) = (term73 _104190 _49542 s).
Proof. exact (eq_refl (term148 _104190 s _49542)). Qed.
Lemma lem4338390 {_104196 : Type'} (_49543 : _104196) (t : _104196 -> Prop) (h1 : term76 _104196 t) : term148 _104196 t _49543.
Proof. exact (@lem4338260 _104196 t h1 _49543). Qed.
Lemma lem4338391 {_104196 : Type'} (_49543 : _104196) (t : _104196 -> Prop) : (term148 _104196 t _49543) = (term73 _104196 _49543 t).
Proof. exact (eq_refl (term148 _104196 t _49543)). Qed.
Lemma lem4338393 {_104190 _104196 : Type'} (_49544 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term171 _104190 _104196 s s' t t') : term500 _104190 s s' _49544.
Proof. exact (@lem4338285 _104190 _104196 s s' t t' h1 _49544). Qed.
Lemma lem4338394 {_104190 : Type'} (s : _104190 -> Prop) (_49544 : _104190) (s' : _104190 -> Prop) : (term500 _104190 s s' _49544) = (term155 _104190 s _49544 s').
Proof. exact (eq_refl (term500 _104190 s s' _49544)). Qed.
Lemma lem4338399 {_104190 : Type'} (_49546 : _104190) (s : _104190 -> Prop) (h1 : term76 _104190 s) : term148 _104190 s _49546.
Proof. exact (@lem4338317 _104190 s h1 _49546). Qed.
Lemma lem4338400 {_104190 : Type'} (_49546 : _104190) (s : _104190 -> Prop) : (term148 _104190 s _49546) = (term73 _104190 _49546 s).
Proof. exact (eq_refl (term148 _104190 s _49546)). Qed.
Lemma lem4338402 {_104196 : Type'} (_49547 : _104196) (t : _104196 -> Prop) (h1 : term76 _104196 t) : term148 _104196 t _49547.
Proof. exact (@lem4338336 _104196 t h1 _49547). Qed.
Lemma lem4338403 {_104196 : Type'} (_49547 : _104196) (t : _104196 -> Prop) : (term148 _104196 t _49547) = (term73 _104196 _49547 t).
Proof. exact (eq_refl (term148 _104196 t _49547)). Qed.
Lemma lem4338408 {_104190 _104196 : Type'} (_49549 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term171 _104190 _104196 s s' t t') : term500 _104196 t t' _49549.
Proof. exact (@lem4338374 _104190 _104196 s s' t t' h1 _49549). Qed.
Lemma lem4338409 {_104196 : Type'} (t : _104196 -> Prop) (_49549 : _104196) (t' : _104196 -> Prop) : (term500 _104196 t t' _49549) = (term155 _104196 t _49549 t').
Proof. exact (eq_refl (term500 _104196 t t' _49549)). Qed.
Lemma lem4338412 {_104190 _104196 : Type'} (_49539 : _104196) (_49538 : _104190) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : term501 _104190 _104196 s _49539 t _49538 s'.
Proof. exact (proj1 (@lem4338380 _104190 _104196 _49538 _49539 p1 p2 s x' s' t x'' t' h1)). Qed.
Lemma lem4338413 {_104190 _104196 : Type'} (_49540 : _104190) (_49541 : _104196) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : term502 _104190 _104196 _49540 s t _49541 t'.
Proof. exact (proj2 (@lem4338386 _104190 _104196 _49540 _49541 p1 p2 s x' s' t x'' t' h1)). Qed.
Lemma lem4338422 {_104190 : Type'} (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (h1 : term154 _104190 s x' s') : term73 _104190 x' s'.
Proof. exact (proj2 (@lem4338101 _104190 s x' s' h1)). Qed.
Lemma lem4338433 {_104190 _104196 : Type'} (s : _104190 -> Prop) (_49539 : _104196) (t : _104196 -> Prop) (_49538 : _104190) (s' : _104190 -> Prop) : (term501 _104190 _104196 s _49539 t _49538 s') = (term503 _104190 _104196 s _49539 t _49538 s').
Proof. exact (@lem4334576 (term73 _104190 _49538 s) (term73 _104196 _49539 t) (@IN _104190 _49538 s')). Qed.
Lemma lem4338434 {_104190 _104196 : Type'} (_49539 : _104196) (_49538 : _104190) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : term503 _104190 _104196 s _49539 t _49538 s'.
Proof. exact (EQ_MP (@lem4338433 _104190 _104196 s _49539 t _49538 s') (@lem4338412 _104190 _104196 _49539 _49538 p1 p2 s x' s' t x'' t' h1)). Qed.
Lemma lem4338454 {_104196 : Type'} (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term154 _104196 t x'' t') : term73 _104196 x'' t'.
Proof. exact (proj2 (@lem4338102 _104196 t x'' t' h1)). Qed.
Lemma lem4338477 {_104190 _104196 : Type'} (_49540 : _104190) (s : _104190 -> Prop) (t : _104196 -> Prop) (_49541 : _104196) (t' : _104196 -> Prop) : (term502 _104190 _104196 _49540 s t _49541 t') = (term504 _104190 _104196 _49540 s t _49541 t').
Proof. exact (@lem4334576 (term73 _104190 _49540 s) (term73 _104196 _49541 t) (@IN _104196 _49541 t')). Qed.
Lemma lem4338478 {_104190 _104196 : Type'} (_49540 : _104190) (_49541 : _104196) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : term504 _104190 _104196 _49540 s t _49541 t'.
Proof. exact (EQ_MP (@lem4338477 _104190 _104196 _49540 s t _49541 t') (@lem4338413 _104190 _104196 _49540 _49541 p1 p2 s x' s' t x'' t' h1)). Qed.
Lemma lem4338486 {_104190 : Type'} (_49542 : _104190) (s : _104190 -> Prop) (h1 : term76 _104190 s) : term73 _104190 _49542 s.
Proof. exact (EQ_MP (@lem4338388 _104190 _49542 s) (@lem4338387 _104190 _49542 s h1)). Qed.
Lemma lem4338494 {_104196 : Type'} (_49543 : _104196) (t : _104196 -> Prop) (h1 : term76 _104196 t) : term73 _104196 _49543 t.
Proof. exact (EQ_MP (@lem4338391 _104196 _49543 t) (@lem4338390 _104196 _49543 t h1)). Qed.
Lemma lem4338500 {_104190 : Type'} (p1 : _104190) (s' : _104190 -> Prop) (h1 : term73 _104190 p1 s') : term73 _104190 p1 s'.
Proof. exact (h1). Qed.
Lemma lem4338506 {_104190 _104196 : Type'} (_49544 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term171 _104190 _104196 s s' t t') : term155 _104190 s _49544 s'.
Proof. exact (EQ_MP (@lem4338394 _104190 s _49544 s') (@lem4338393 _104190 _104196 _49544 s s' t t' h1)). Qed.
Lemma lem4338520 {_104190 : Type'} (_49546 : _104190) (s : _104190 -> Prop) (h1 : term76 _104190 s) : term73 _104190 _49546 s.
Proof. exact (EQ_MP (@lem4338400 _104190 _49546 s) (@lem4338399 _104190 _49546 s h1)). Qed.
Lemma lem4338528 {_104196 : Type'} (_49547 : _104196) (t : _104196 -> Prop) (h1 : term76 _104196 t) : term73 _104196 _49547 t.
Proof. exact (EQ_MP (@lem4338403 _104196 _49547 t) (@lem4338402 _104196 _49547 t h1)). Qed.
Lemma lem4338534 {_104196 : Type'} (p2 : _104196) (t' : _104196 -> Prop) (h1 : term73 _104196 p2 t') : term73 _104196 p2 t'.
Proof. exact (h1). Qed.
Lemma lem4338546 {_104190 _104196 : Type'} (_49549 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term171 _104190 _104196 s s' t t') : term155 _104196 t _49549 t'.
Proof. exact (EQ_MP (@lem4338409 _104196 t _49549 t') (@lem4338408 _104190 _104196 _49549 s s' t t' h1)). Qed.
Lemma lem4338548 {_104190 : Type'} (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (h1 : term154 _104190 s x' s') : @IN _104190 x' s.
Proof. exact (proj1 (@lem4338101 _104190 s x' s' h1)). Qed.
Lemma lem4338549 {_104190 : Type'} (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (h1 : term154 _104190 s x' s') : term505 _104190 x' s.
Proof. exact (fun h0 : term73 _104190 x' s => @lem4338548 _104190 s x' s' h1). Qed.
Lemma lem4338551 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4338552 {_104190 : Type'} (x' : _104190) (s : _104190 -> Prop) : (term505 _104190 x' s) = (@IN _104190 x' s).
Proof. exact (@lem4338551 (@IN _104190 x' s)). Qed.
Lemma lem4338553 {_104190 : Type'} (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (h1 : term154 _104190 s x' s') : @IN _104190 x' s.
Proof. exact (EQ_MP (@lem4338552 _104190 x' s) (@lem4338549 _104190 s x' s' h1)). Qed.
Lemma lem4338555 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : @IN _104196 p2 t.
Proof. exact (proj1 (@lem4338097 _104190 _104196 p1 p2 s x' s' t x'' t' h1)). Qed.
Lemma lem4338556 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : term505 _104196 p2 t.
Proof. exact (fun h0 : term73 _104196 p2 t => @lem4338555 _104190 _104196 p1 p2 s x' s' t x'' t' h1). Qed.
Lemma lem4338558 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4338559 {_104196 : Type'} (p2 : _104196) (t : _104196 -> Prop) : (term505 _104196 p2 t) = (@IN _104196 p2 t).
Proof. exact (@lem4338558 (@IN _104196 p2 t)). Qed.
Lemma lem4338560 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : @IN _104196 p2 t.
Proof. exact (EQ_MP (@lem4338559 _104196 p2 t) (@lem4338556 _104190 _104196 p1 p2 s x' s' t x'' t' h1)). Qed.
Lemma lem4338576 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4338577 {_104190 _104196 : Type'} (_49538 : _104190) (s' : _104190 -> Prop) (_49539 : _104196) (t : _104196 -> Prop) : (term507 _104190 _104196 _49539 t _49538 s') = (term508 _104190 _104196 _49538 s' _49539 t).
Proof. exact (@lem4338576 (@IN _104190 _49538 s') (term73 _104196 _49539 t)). Qed.
Lemma lem4338583 {_104190 : Type'} (_49538 : _104190) (s : _104190 -> Prop) : (term509 _104190 _49538 s) = (term509 _104190 _49538 s).
Proof. exact (eq_refl (term509 _104190 _49538 s)). Qed.
Lemma lem4338584 {_104190 _104196 : Type'} (s : _104190 -> Prop) (_49538 : _104190) (s' : _104190 -> Prop) (_49539 : _104196) (t : _104196 -> Prop) : (term503 _104190 _104196 s _49539 t _49538 s') = (term510 _104190 _104196 s _49538 s' _49539 t).
Proof. exact (MK_COMB (@lem4338583 _104190 _49538 s) (@lem4338577 _104190 _104196 _49538 s' _49539 t)). Qed.
Lemma lem4338588 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4338589 {_104190 _104196 : Type'} (s' : _104190 -> Prop) (_49538 : _104190) (s : _104190 -> Prop) (_49539 : _104196) (t : _104196 -> Prop) : (term510 _104190 _104196 s _49538 s' _49539 t) = (term511 _104190 _104196 s' _49538 s _49539 t).
Proof. exact (@lem4338588 (@IN _104190 _49538 s') (term73 _104190 _49538 s) (term73 _104196 _49539 t)). Qed.
Lemma lem4338605 {_104190 _104196 : Type'} (s' : _104190 -> Prop) (_49538 : _104190) (s : _104190 -> Prop) (_49539 : _104196) (t : _104196 -> Prop) : (term503 _104190 _104196 s _49539 t _49538 s') = (term511 _104190 _104196 s' _49538 s _49539 t).
Proof. exact (TRANS (@lem4338584 _104190 _104196 s _49538 s' _49539 t) (@lem4338589 _104190 _104196 s' _49538 s _49539 t)). Qed.
Lemma lem4338606 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4338607 {_104190 _104196 : Type'} (s' : _104190 -> Prop) (_49538 : _104190) (s : _104190 -> Prop) (_49539 : _104196) (t : _104196 -> Prop) : (term512 _104190 _104196 s _49539 t _49538 s') = (term513 _104190 _104196 s' _49538 s _49539 t).
Proof. exact (MK_COMB (@lem4338606) (@lem4338605 _104190 _104196 s' _49538 s _49539 t)). Qed.
Lemma lem4338623 {_104190 _104196 : Type'} (s' : _104190 -> Prop) (_49538 : _104190) (s : _104190 -> Prop) (_49539 : _104196) (t : _104196 -> Prop) : (term511 _104190 _104196 s' _49538 s _49539 t) = (term511 _104190 _104196 s' _49538 s _49539 t).
Proof. exact (eq_refl (term511 _104190 _104196 s' _49538 s _49539 t)). Qed.
Lemma lem4338624 {_104190 _104196 : Type'} (s' : _104190 -> Prop) (_49538 : _104190) (s : _104190 -> Prop) (_49539 : _104196) (t : _104196 -> Prop) : ((term503 _104190 _104196 s _49539 t _49538 s') = (term511 _104190 _104196 s' _49538 s _49539 t)) = ((term511 _104190 _104196 s' _49538 s _49539 t) = (term511 _104190 _104196 s' _49538 s _49539 t)).
Proof. exact (MK_COMB (@lem4338607 _104190 _104196 s' _49538 s _49539 t) (@lem4338623 _104190 _104196 s' _49538 s _49539 t)). Qed.
Lemma lem4338626 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4338627 (x : Prop) : (x = x) = True.
Proof. exact (@lem4338626 Prop x). Qed.
Lemma lem4338628 {_104190 _104196 : Type'} (s' : _104190 -> Prop) (_49538 : _104190) (s : _104190 -> Prop) (_49539 : _104196) (t : _104196 -> Prop) : ((term511 _104190 _104196 s' _49538 s _49539 t) = (term511 _104190 _104196 s' _49538 s _49539 t)) = True.
Proof. exact (@lem4338627 (term511 _104190 _104196 s' _49538 s _49539 t)). Qed.
Lemma lem4338629 {_104190 _104196 : Type'} (s' : _104190 -> Prop) (_49538 : _104190) (s : _104190 -> Prop) (_49539 : _104196) (t : _104196 -> Prop) : ((term503 _104190 _104196 s _49539 t _49538 s') = (term511 _104190 _104196 s' _49538 s _49539 t)) = True.
Proof. exact (TRANS (@lem4338624 _104190 _104196 s' _49538 s _49539 t) (@lem4338628 _104190 _104196 s' _49538 s _49539 t)). Qed.
Lemma lem4338630 {_104190 _104196 : Type'} (s' : _104190 -> Prop) (_49538 : _104190) (s : _104190 -> Prop) (_49539 : _104196) (t : _104196 -> Prop) : True = ((term503 _104190 _104196 s _49539 t _49538 s') = (term511 _104190 _104196 s' _49538 s _49539 t)).
Proof. exact (SYM (@lem4338629 _104190 _104196 s' _49538 s _49539 t)). Qed.
Lemma lem4338631 {_104190 _104196 : Type'} (s' : _104190 -> Prop) (_49538 : _104190) (s : _104190 -> Prop) (_49539 : _104196) (t : _104196 -> Prop) : (term503 _104190 _104196 s _49539 t _49538 s') = (term511 _104190 _104196 s' _49538 s _49539 t).
Proof. exact (EQ_MP (@lem4338630 _104190 _104196 s' _49538 s _49539 t) (@lem0)). Qed.
Lemma lem4338632 {_104190 _104196 : Type'} (_49538 : _104190) (_49539 : _104196) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : term511 _104190 _104196 s' _49538 s _49539 t.
Proof. exact (EQ_MP (@lem4338631 _104190 _104196 s' _49538 s _49539 t) (@lem4338434 _104190 _104196 _49539 _49538 p1 p2 s x' s' t x'' t' h1)). Qed.
Lemma lem4338634 (b : Prop) (a : Prop) : (a \/ b) = (term514 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4338635 {_104190 _104196 : Type'} (s : _104190 -> Prop) (_49539 : _104196) (t : _104196 -> Prop) (_49538 : _104190) (s' : _104190 -> Prop) : (term511 _104190 _104196 s' _49538 s _49539 t) = (term515 _104190 _104196 s _49539 t _49538 s').
Proof. exact (@lem4338634 (term116 _104190 _104196 _49538 s _49539 t) (@IN _104190 _49538 s')). Qed.
Lemma lem4338637 (a : Prop) (b : Prop) : (term516 a b) = (term517 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4338638 {_104190 _104196 : Type'} (_49538 : _104190) (s : _104190 -> Prop) (_49539 : _104196) (t : _104196 -> Prop) : (term518 _104190 _104196 _49538 s _49539 t) = (term519 _104190 _104196 _49538 s _49539 t).
Proof. exact (@lem4338637 (term73 _104190 _49538 s) (term73 _104196 _49539 t)). Qed.
Lemma lem4338640 (a : Prop) : (term110 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4338641 {_104190 : Type'} (_49538 : _104190) (s : _104190 -> Prop) : (term145 _104190 _49538 s) = (@IN _104190 _49538 s).
Proof. exact (@lem4338640 (@IN _104190 _49538 s)). Qed.
Lemma lem4338642 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4338643 {_104190 : Type'} (_49538 : _104190) (s : _104190 -> Prop) : (term520 _104190 _49538 s) = (term236 _104190 _49538 s).
Proof. exact (MK_COMB (@lem4338642) (@lem4338641 _104190 _49538 s)). Qed.
Lemma lem4338645 (a : Prop) : (term110 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4338646 {_104196 : Type'} (_49539 : _104196) (t : _104196 -> Prop) : (term145 _104196 _49539 t) = (@IN _104196 _49539 t).
Proof. exact (@lem4338645 (@IN _104196 _49539 t)). Qed.
Lemma lem4338647 {_104190 _104196 : Type'} (_49538 : _104190) (s : _104190 -> Prop) (_49539 : _104196) (t : _104196 -> Prop) : (term519 _104190 _104196 _49538 s _49539 t) = (term18 _104190 _104196 _49538 s _49539 t).
Proof. exact (MK_COMB (@lem4338643 _104190 _49538 s) (@lem4338646 _104196 _49539 t)). Qed.
Lemma lem4338648 {_104190 _104196 : Type'} (_49538 : _104190) (s : _104190 -> Prop) (_49539 : _104196) (t : _104196 -> Prop) : (term518 _104190 _104196 _49538 s _49539 t) = (term18 _104190 _104196 _49538 s _49539 t).
Proof. exact (TRANS (@lem4338638 _104190 _104196 _49538 s _49539 t) (@lem4338647 _104190 _104196 _49538 s _49539 t)). Qed.
Lemma lem4338649 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4338650 {_104190 _104196 : Type'} (_49538 : _104190) (s : _104190 -> Prop) (_49539 : _104196) (t : _104196 -> Prop) : (term521 _104190 _104196 _49538 s _49539 t) = (term522 _104190 _104196 _49538 s _49539 t).
Proof. exact (MK_COMB (@lem4338649) (@lem4338648 _104190 _104196 _49538 s _49539 t)). Qed.
Lemma lem4338651 {_104190 : Type'} (_49538 : _104190) (s' : _104190 -> Prop) : (@IN _104190 _49538 s') = (@IN _104190 _49538 s').
Proof. exact (eq_refl (@IN _104190 _49538 s')). Qed.
Lemma lem4338652 {_104190 _104196 : Type'} (s : _104190 -> Prop) (_49539 : _104196) (t : _104196 -> Prop) (_49538 : _104190) (s' : _104190 -> Prop) : (term515 _104190 _104196 s _49539 t _49538 s') = (term523 _104190 _104196 s _49539 t _49538 s').
Proof. exact (MK_COMB (@lem4338650 _104190 _104196 _49538 s _49539 t) (@lem4338651 _104190 _49538 s')). Qed.
Lemma lem4338653 {_104190 _104196 : Type'} (s : _104190 -> Prop) (_49539 : _104196) (t : _104196 -> Prop) (_49538 : _104190) (s' : _104190 -> Prop) : (term511 _104190 _104196 s' _49538 s _49539 t) = (term523 _104190 _104196 s _49539 t _49538 s').
Proof. exact (TRANS (@lem4338635 _104190 _104196 s _49539 t _49538 s') (@lem4338652 _104190 _104196 s _49539 t _49538 s')). Qed.
Lemma lem4338655 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') (h2 : term154 _104190 s x' s') : term18 _104190 _104196 x' s p2 t.
Proof. exact (conj (@lem4338553 _104190 s x' s' h2) (@lem4338560 _104190 _104196 p1 p2 s x' s' t x'' t' h1)). Qed.
Lemma lem4338657 {_104190 _104196 : Type'} (_49539 : _104196) (_49538 : _104190) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : term523 _104190 _104196 s _49539 t _49538 s'.
Proof. exact (EQ_MP (@lem4338653 _104190 _104196 s _49539 t _49538 s') (@lem4338632 _104190 _104196 _49538 _49539 p1 p2 s x' s' t x'' t' h1)). Qed.
Lemma lem4338658 {_104190 _104196 : Type'} (_49539 : _104196) (_49538 : _104190) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : term523 _104190 _104196 s _49539 t _49538 s'.
Proof. exact (@lem4338657 _104190 _104196 _49539 _49538 p1 p2 s x' s' t x'' t' h1). Qed.
Lemma lem4338659 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : term523 _104190 _104196 s p2 t x' s'.
Proof. exact (@lem4338658 _104190 _104196 p2 x' p1 p2 s x' s' t x'' t' h1). Qed.
Lemma lem4338662 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') (h2 : term154 _104190 s x' s') : @IN _104190 x' s'.
Proof. exact (@lem4338659 _104190 _104196 p1 p2 s x' s' t x'' t' h1 (@lem4338655 _104190 _104196 p1 p2 t x'' t' s x' s' h1 h2)). Qed.
Lemma lem4338663 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') (h2 : term154 _104190 s x' s') : term505 _104190 x' s'.
Proof. exact (fun h0 : term73 _104190 x' s' => @lem4338662 _104190 _104196 p1 p2 t x'' t' s x' s' h1 h2). Qed.
Lemma lem4338665 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4338666 {_104190 : Type'} (x' : _104190) (s' : _104190 -> Prop) : (term505 _104190 x' s') = (@IN _104190 x' s').
Proof. exact (@lem4338665 (@IN _104190 x' s')). Qed.
Lemma lem4338667 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') (h2 : term154 _104190 s x' s') : @IN _104190 x' s'.
Proof. exact (EQ_MP (@lem4338666 _104190 x' s') (@lem4338663 _104190 _104196 p1 p2 t x'' t' s x' s' h1 h2)). Qed.
Lemma lem4338670 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4338672 {_104190 : Type'} (x' : _104190) (s' : _104190 -> Prop) : (term73 _104190 x' s') = (term524 _104190 x' s').
Proof. exact (@lem4338670 (@IN _104190 x' s')). Qed.
Lemma lem4338675 {_104190 : Type'} (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (h1 : term154 _104190 s x' s') : term524 _104190 x' s'.
Proof. exact (EQ_MP (@lem4338672 _104190 x' s') (@lem4338422 _104190 s x' s' h1)). Qed.
Lemma lem4338678 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') (h2 : term154 _104190 s x' s') : False.
Proof. exact (@lem4338675 _104190 s x' s' h2 (@lem4338667 _104190 _104196 p1 p2 t x'' t' s x' s' h1 h2)). Qed.
Lemma lem4338679 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') (h2 : term154 _104190 s x' s') : term525.
Proof. exact (fun h0 : ~ False => @lem4338678 _104190 _104196 p1 p2 t x'' t' s x' s' h1 h2). Qed.
Lemma lem4338681 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4338682 : term525 = False.
Proof. exact (@lem4338681 False). Qed.
Lemma lem4338683 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') (h2 : term154 _104190 s x' s') : False.
Proof. exact (EQ_MP (@lem4338682) (@lem4338679 _104190 _104196 p1 p2 t x'' t' s x' s' h1 h2)). Qed.
Lemma lem4338685 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : @IN _104190 p1 s.
Proof. exact (proj1 (@lem4338095 _104190 _104196 p1 p2 s x' s' t x'' t' h1)). Qed.
Lemma lem4338686 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : term505 _104190 p1 s.
Proof. exact (fun h0 : term73 _104190 p1 s => @lem4338685 _104190 _104196 p1 p2 s x' s' t x'' t' h1). Qed.
Lemma lem4338688 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4338689 {_104190 : Type'} (p1 : _104190) (s : _104190 -> Prop) : (term505 _104190 p1 s) = (@IN _104190 p1 s).
Proof. exact (@lem4338688 (@IN _104190 p1 s)). Qed.
Lemma lem4338690 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : @IN _104190 p1 s.
Proof. exact (EQ_MP (@lem4338689 _104190 p1 s) (@lem4338686 _104190 _104196 p1 p2 s x' s' t x'' t' h1)). Qed.
Lemma lem4338692 {_104196 : Type'} (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term154 _104196 t x'' t') : @IN _104196 x'' t.
Proof. exact (proj1 (@lem4338102 _104196 t x'' t' h1)). Qed.
Lemma lem4338693 {_104196 : Type'} (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term154 _104196 t x'' t') : term505 _104196 x'' t.
Proof. exact (fun h0 : term73 _104196 x'' t => @lem4338692 _104196 t x'' t' h1). Qed.
Lemma lem4338695 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4338696 {_104196 : Type'} (x'' : _104196) (t : _104196 -> Prop) : (term505 _104196 x'' t) = (@IN _104196 x'' t).
Proof. exact (@lem4338695 (@IN _104196 x'' t)). Qed.
Lemma lem4338697 {_104196 : Type'} (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term154 _104196 t x'' t') : @IN _104196 x'' t.
Proof. exact (EQ_MP (@lem4338696 _104196 x'' t) (@lem4338693 _104196 t x'' t' h1)). Qed.
Lemma lem4338713 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4338714 {_104196 : Type'} (t' : _104196 -> Prop) (_49541 : _104196) (t : _104196 -> Prop) : (term155 _104196 t _49541 t') = (term526 _104196 t' _49541 t).
Proof. exact (@lem4338713 (@IN _104196 _49541 t') (term73 _104196 _49541 t)). Qed.
Lemma lem4338720 {_104190 : Type'} (_49540 : _104190) (s : _104190 -> Prop) : (term509 _104190 _49540 s) = (term509 _104190 _49540 s).
Proof. exact (eq_refl (term509 _104190 _49540 s)). Qed.
Lemma lem4338721 {_104190 _104196 : Type'} (_49540 : _104190) (s : _104190 -> Prop) (t' : _104196 -> Prop) (_49541 : _104196) (t : _104196 -> Prop) : (term504 _104190 _104196 _49540 s t _49541 t') = (term527 _104190 _104196 _49540 s t' _49541 t).
Proof. exact (MK_COMB (@lem4338720 _104190 _49540 s) (@lem4338714 _104196 t' _49541 t)). Qed.
Lemma lem4338725 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4338726 {_104190 _104196 : Type'} (t' : _104196 -> Prop) (_49540 : _104190) (s : _104190 -> Prop) (_49541 : _104196) (t : _104196 -> Prop) : (term527 _104190 _104196 _49540 s t' _49541 t) = (term528 _104190 _104196 t' _49540 s _49541 t).
Proof. exact (@lem4338725 (@IN _104196 _49541 t') (term73 _104190 _49540 s) (term73 _104196 _49541 t)). Qed.
Lemma lem4338742 {_104190 _104196 : Type'} (t' : _104196 -> Prop) (_49540 : _104190) (s : _104190 -> Prop) (_49541 : _104196) (t : _104196 -> Prop) : (term504 _104190 _104196 _49540 s t _49541 t') = (term528 _104190 _104196 t' _49540 s _49541 t).
Proof. exact (TRANS (@lem4338721 _104190 _104196 _49540 s t' _49541 t) (@lem4338726 _104190 _104196 t' _49540 s _49541 t)). Qed.
Lemma lem4338743 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4338744 {_104190 _104196 : Type'} (t' : _104196 -> Prop) (_49540 : _104190) (s : _104190 -> Prop) (_49541 : _104196) (t : _104196 -> Prop) : (term529 _104190 _104196 _49540 s t _49541 t') = (term530 _104190 _104196 t' _49540 s _49541 t).
Proof. exact (MK_COMB (@lem4338743) (@lem4338742 _104190 _104196 t' _49540 s _49541 t)). Qed.
Lemma lem4338760 {_104190 _104196 : Type'} (t' : _104196 -> Prop) (_49540 : _104190) (s : _104190 -> Prop) (_49541 : _104196) (t : _104196 -> Prop) : (term528 _104190 _104196 t' _49540 s _49541 t) = (term528 _104190 _104196 t' _49540 s _49541 t).
Proof. exact (eq_refl (term528 _104190 _104196 t' _49540 s _49541 t)). Qed.
Lemma lem4338761 {_104190 _104196 : Type'} (t' : _104196 -> Prop) (_49540 : _104190) (s : _104190 -> Prop) (_49541 : _104196) (t : _104196 -> Prop) : ((term504 _104190 _104196 _49540 s t _49541 t') = (term528 _104190 _104196 t' _49540 s _49541 t)) = ((term528 _104190 _104196 t' _49540 s _49541 t) = (term528 _104190 _104196 t' _49540 s _49541 t)).
Proof. exact (MK_COMB (@lem4338744 _104190 _104196 t' _49540 s _49541 t) (@lem4338760 _104190 _104196 t' _49540 s _49541 t)). Qed.
Lemma lem4338763 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4338764 (x : Prop) : (x = x) = True.
Proof. exact (@lem4338763 Prop x). Qed.
Lemma lem4338765 {_104190 _104196 : Type'} (t' : _104196 -> Prop) (_49540 : _104190) (s : _104190 -> Prop) (_49541 : _104196) (t : _104196 -> Prop) : ((term528 _104190 _104196 t' _49540 s _49541 t) = (term528 _104190 _104196 t' _49540 s _49541 t)) = True.
Proof. exact (@lem4338764 (term528 _104190 _104196 t' _49540 s _49541 t)). Qed.
Lemma lem4338766 {_104190 _104196 : Type'} (t' : _104196 -> Prop) (_49540 : _104190) (s : _104190 -> Prop) (_49541 : _104196) (t : _104196 -> Prop) : ((term504 _104190 _104196 _49540 s t _49541 t') = (term528 _104190 _104196 t' _49540 s _49541 t)) = True.
Proof. exact (TRANS (@lem4338761 _104190 _104196 t' _49540 s _49541 t) (@lem4338765 _104190 _104196 t' _49540 s _49541 t)). Qed.
Lemma lem4338767 {_104190 _104196 : Type'} (t' : _104196 -> Prop) (_49540 : _104190) (s : _104190 -> Prop) (_49541 : _104196) (t : _104196 -> Prop) : True = ((term504 _104190 _104196 _49540 s t _49541 t') = (term528 _104190 _104196 t' _49540 s _49541 t)).
Proof. exact (SYM (@lem4338766 _104190 _104196 t' _49540 s _49541 t)). Qed.
Lemma lem4338768 {_104190 _104196 : Type'} (t' : _104196 -> Prop) (_49540 : _104190) (s : _104190 -> Prop) (_49541 : _104196) (t : _104196 -> Prop) : (term504 _104190 _104196 _49540 s t _49541 t') = (term528 _104190 _104196 t' _49540 s _49541 t).
Proof. exact (EQ_MP (@lem4338767 _104190 _104196 t' _49540 s _49541 t) (@lem0)). Qed.
Lemma lem4338769 {_104190 _104196 : Type'} (_49540 : _104190) (_49541 : _104196) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : term528 _104190 _104196 t' _49540 s _49541 t.
Proof. exact (EQ_MP (@lem4338768 _104190 _104196 t' _49540 s _49541 t) (@lem4338478 _104190 _104196 _49540 _49541 p1 p2 s x' s' t x'' t' h1)). Qed.
Lemma lem4338771 (b : Prop) (a : Prop) : (a \/ b) = (term514 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4338772 {_104190 _104196 : Type'} (_49540 : _104190) (s : _104190 -> Prop) (t : _104196 -> Prop) (_49541 : _104196) (t' : _104196 -> Prop) : (term528 _104190 _104196 t' _49540 s _49541 t) = (term531 _104190 _104196 _49540 s t _49541 t').
Proof. exact (@lem4338771 (term116 _104190 _104196 _49540 s _49541 t) (@IN _104196 _49541 t')). Qed.
Lemma lem4338774 (a : Prop) (b : Prop) : (term516 a b) = (term517 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4338775 {_104190 _104196 : Type'} (_49540 : _104190) (s : _104190 -> Prop) (_49541 : _104196) (t : _104196 -> Prop) : (term518 _104190 _104196 _49540 s _49541 t) = (term519 _104190 _104196 _49540 s _49541 t).
Proof. exact (@lem4338774 (term73 _104190 _49540 s) (term73 _104196 _49541 t)). Qed.
Lemma lem4338777 (a : Prop) : (term110 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4338778 {_104190 : Type'} (_49540 : _104190) (s : _104190 -> Prop) : (term145 _104190 _49540 s) = (@IN _104190 _49540 s).
Proof. exact (@lem4338777 (@IN _104190 _49540 s)). Qed.
Lemma lem4338779 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4338780 {_104190 : Type'} (_49540 : _104190) (s : _104190 -> Prop) : (term520 _104190 _49540 s) = (term236 _104190 _49540 s).
Proof. exact (MK_COMB (@lem4338779) (@lem4338778 _104190 _49540 s)). Qed.
Lemma lem4338782 (a : Prop) : (term110 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4338783 {_104196 : Type'} (_49541 : _104196) (t : _104196 -> Prop) : (term145 _104196 _49541 t) = (@IN _104196 _49541 t).
Proof. exact (@lem4338782 (@IN _104196 _49541 t)). Qed.
Lemma lem4338784 {_104190 _104196 : Type'} (_49540 : _104190) (s : _104190 -> Prop) (_49541 : _104196) (t : _104196 -> Prop) : (term519 _104190 _104196 _49540 s _49541 t) = (term18 _104190 _104196 _49540 s _49541 t).
Proof. exact (MK_COMB (@lem4338780 _104190 _49540 s) (@lem4338783 _104196 _49541 t)). Qed.
Lemma lem4338785 {_104190 _104196 : Type'} (_49540 : _104190) (s : _104190 -> Prop) (_49541 : _104196) (t : _104196 -> Prop) : (term518 _104190 _104196 _49540 s _49541 t) = (term18 _104190 _104196 _49540 s _49541 t).
Proof. exact (TRANS (@lem4338775 _104190 _104196 _49540 s _49541 t) (@lem4338784 _104190 _104196 _49540 s _49541 t)). Qed.
Lemma lem4338786 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4338787 {_104190 _104196 : Type'} (_49540 : _104190) (s : _104190 -> Prop) (_49541 : _104196) (t : _104196 -> Prop) : (term521 _104190 _104196 _49540 s _49541 t) = (term522 _104190 _104196 _49540 s _49541 t).
Proof. exact (MK_COMB (@lem4338786) (@lem4338785 _104190 _104196 _49540 s _49541 t)). Qed.
Lemma lem4338788 {_104196 : Type'} (_49541 : _104196) (t' : _104196 -> Prop) : (@IN _104196 _49541 t') = (@IN _104196 _49541 t').
Proof. exact (eq_refl (@IN _104196 _49541 t')). Qed.
Lemma lem4338789 {_104190 _104196 : Type'} (_49540 : _104190) (s : _104190 -> Prop) (t : _104196 -> Prop) (_49541 : _104196) (t' : _104196 -> Prop) : (term531 _104190 _104196 _49540 s t _49541 t') = (term532 _104190 _104196 _49540 s t _49541 t').
Proof. exact (MK_COMB (@lem4338787 _104190 _104196 _49540 s _49541 t) (@lem4338788 _104196 _49541 t')). Qed.
Lemma lem4338790 {_104190 _104196 : Type'} (_49540 : _104190) (s : _104190 -> Prop) (t : _104196 -> Prop) (_49541 : _104196) (t' : _104196 -> Prop) : (term528 _104190 _104196 t' _49540 s _49541 t) = (term532 _104190 _104196 _49540 s t _49541 t').
Proof. exact (TRANS (@lem4338772 _104190 _104196 _49540 s t _49541 t') (@lem4338789 _104190 _104196 _49540 s t _49541 t')). Qed.
Lemma lem4338792 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') (h2 : term154 _104196 t x'' t') : term18 _104190 _104196 p1 s x'' t.
Proof. exact (conj (@lem4338690 _104190 _104196 p1 p2 s x' s' t x'' t' h1) (@lem4338697 _104196 t x'' t' h2)). Qed.
Lemma lem4338794 {_104190 _104196 : Type'} (_49540 : _104190) (_49541 : _104196) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : term532 _104190 _104196 _49540 s t _49541 t'.
Proof. exact (EQ_MP (@lem4338790 _104190 _104196 _49540 s t _49541 t') (@lem4338769 _104190 _104196 _49540 _49541 p1 p2 s x' s' t x'' t' h1)). Qed.
Lemma lem4338795 {_104190 _104196 : Type'} (_49540 : _104190) (_49541 : _104196) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : term532 _104190 _104196 _49540 s t _49541 t'.
Proof. exact (@lem4338794 _104190 _104196 _49540 _49541 p1 p2 s x' s' t x'' t' h1). Qed.
Lemma lem4338796 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : term532 _104190 _104196 p1 s t x'' t'.
Proof. exact (@lem4338795 _104190 _104196 p1 x'' p1 p2 s x' s' t x'' t' h1). Qed.
Lemma lem4338799 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') (h2 : term154 _104196 t x'' t') : @IN _104196 x'' t'.
Proof. exact (@lem4338796 _104190 _104196 p1 p2 s x' s' t x'' t' h1 (@lem4338792 _104190 _104196 p1 p2 s x' s' t x'' t' h1 h2)). Qed.
Lemma lem4338800 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') (h2 : term154 _104196 t x'' t') : term505 _104196 x'' t'.
Proof. exact (fun h0 : term73 _104196 x'' t' => @lem4338799 _104190 _104196 p1 p2 s x' s' t x'' t' h1 h2). Qed.
Lemma lem4338802 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4338803 {_104196 : Type'} (x'' : _104196) (t' : _104196 -> Prop) : (term505 _104196 x'' t') = (@IN _104196 x'' t').
Proof. exact (@lem4338802 (@IN _104196 x'' t')). Qed.
Lemma lem4338804 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') (h2 : term154 _104196 t x'' t') : @IN _104196 x'' t'.
Proof. exact (EQ_MP (@lem4338803 _104196 x'' t') (@lem4338800 _104190 _104196 p1 p2 s x' s' t x'' t' h1 h2)). Qed.
Lemma lem4338807 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4338809 {_104196 : Type'} (x'' : _104196) (t' : _104196 -> Prop) : (term73 _104196 x'' t') = (term524 _104196 x'' t').
Proof. exact (@lem4338807 (@IN _104196 x'' t')). Qed.
Lemma lem4338812 {_104196 : Type'} (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term154 _104196 t x'' t') : term524 _104196 x'' t'.
Proof. exact (EQ_MP (@lem4338809 _104196 x'' t') (@lem4338454 _104196 t x'' t' h1)). Qed.
Lemma lem4338815 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') (h2 : term154 _104196 t x'' t') : False.
Proof. exact (@lem4338812 _104196 t x'' t' h2 (@lem4338804 _104190 _104196 p1 p2 s x' s' t x'' t' h1 h2)). Qed.
Lemma lem4338816 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') (h2 : term154 _104196 t x'' t') : term525.
Proof. exact (fun h0 : ~ False => @lem4338815 _104190 _104196 p1 p2 s x' s' t x'' t' h1 h2). Qed.
Lemma lem4338818 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4338819 : term525 = False.
Proof. exact (@lem4338818 False). Qed.
Lemma lem4338820 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') (h2 : term154 _104196 t x'' t') : False.
Proof. exact (EQ_MP (@lem4338819) (@lem4338816 _104190 _104196 p1 p2 s x' s' t x'' t' h1 h2)). Qed.
Lemma lem4338822 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term406 _104190 _104196 p1 p2 s s' t t') : @IN _104190 p1 s.
Proof. exact (proj1 (@lem4338110 _104190 _104196 p1 p2 s s' t t' h1)). Qed.
Lemma lem4338823 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term406 _104190 _104196 p1 p2 s s' t t') : term505 _104190 p1 s.
Proof. exact (fun h0 : term73 _104190 p1 s => @lem4338822 _104190 _104196 p1 p2 s s' t t' h1). Qed.
Lemma lem4338825 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4338826 {_104190 : Type'} (p1 : _104190) (s : _104190 -> Prop) : (term505 _104190 p1 s) = (@IN _104190 p1 s).
Proof. exact (@lem4338825 (@IN _104190 p1 s)). Qed.
Lemma lem4338827 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term406 _104190 _104196 p1 p2 s s' t t') : @IN _104190 p1 s.
Proof. exact (EQ_MP (@lem4338826 _104190 p1 s) (@lem4338823 _104190 _104196 p1 p2 s s' t t' h1)). Qed.
Lemma lem4338830 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4338832 {_104190 : Type'} (_49542 : _104190) (s : _104190 -> Prop) : (term73 _104190 _49542 s) = (term524 _104190 _49542 s).
Proof. exact (@lem4338830 (@IN _104190 _49542 s)). Qed.
Lemma lem4338835 {_104190 : Type'} (_49542 : _104190) (s : _104190 -> Prop) (h1 : term76 _104190 s) : term524 _104190 _49542 s.
Proof. exact (EQ_MP (@lem4338832 _104190 _49542 s) (@lem4338486 _104190 _49542 s h1)). Qed.
Lemma lem4338836 {_104190 : Type'} (_49542 : _104190) (s : _104190 -> Prop) (h1 : term76 _104190 s) : term524 _104190 _49542 s.
Proof. exact (@lem4338835 _104190 _49542 s h1). Qed.
Lemma lem4338837 {_104190 : Type'} (p1 : _104190) (s : _104190 -> Prop) (h1 : term76 _104190 s) : term524 _104190 p1 s.
Proof. exact (@lem4338836 _104190 p1 s h1). Qed.
Lemma lem4338840 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term76 _104190 s) (h2 : term406 _104190 _104196 p1 p2 s s' t t') : False.
Proof. exact (@lem4338837 _104190 p1 s h1 (@lem4338827 _104190 _104196 p1 p2 s s' t t' h2)). Qed.
Lemma lem4338841 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term76 _104190 s) (h2 : term406 _104190 _104196 p1 p2 s s' t t') : term525.
Proof. exact (fun h0 : ~ False => @lem4338840 _104190 _104196 p1 p2 s s' t t' h1 h2). Qed.
Lemma lem4338843 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4338844 : term525 = False.
Proof. exact (@lem4338843 False). Qed.
Lemma lem4338845 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term76 _104190 s) (h2 : term406 _104190 _104196 p1 p2 s s' t t') : False.
Proof. exact (EQ_MP (@lem4338844) (@lem4338841 _104190 _104196 p1 p2 s s' t t' h1 h2)). Qed.
Lemma lem4338847 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term406 _104190 _104196 p1 p2 s s' t t') : @IN _104196 p2 t.
Proof. exact (proj2 (@lem4338110 _104190 _104196 p1 p2 s s' t t' h1)). Qed.
Lemma lem4338848 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term406 _104190 _104196 p1 p2 s s' t t') : term505 _104196 p2 t.
Proof. exact (fun h0 : term73 _104196 p2 t => @lem4338847 _104190 _104196 p1 p2 s s' t t' h1). Qed.
Lemma lem4338850 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4338851 {_104196 : Type'} (p2 : _104196) (t : _104196 -> Prop) : (term505 _104196 p2 t) = (@IN _104196 p2 t).
Proof. exact (@lem4338850 (@IN _104196 p2 t)). Qed.
Lemma lem4338852 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term406 _104190 _104196 p1 p2 s s' t t') : @IN _104196 p2 t.
Proof. exact (EQ_MP (@lem4338851 _104196 p2 t) (@lem4338848 _104190 _104196 p1 p2 s s' t t' h1)). Qed.
Lemma lem4338855 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4338857 {_104196 : Type'} (_49543 : _104196) (t : _104196 -> Prop) : (term73 _104196 _49543 t) = (term524 _104196 _49543 t).
Proof. exact (@lem4338855 (@IN _104196 _49543 t)). Qed.
Lemma lem4338860 {_104196 : Type'} (_49543 : _104196) (t : _104196 -> Prop) (h1 : term76 _104196 t) : term524 _104196 _49543 t.
Proof. exact (EQ_MP (@lem4338857 _104196 _49543 t) (@lem4338494 _104196 _49543 t h1)). Qed.
Lemma lem4338861 {_104196 : Type'} (_49543 : _104196) (t : _104196 -> Prop) (h1 : term76 _104196 t) : term524 _104196 _49543 t.
Proof. exact (@lem4338860 _104196 _49543 t h1). Qed.
Lemma lem4338862 {_104196 : Type'} (p2 : _104196) (t : _104196 -> Prop) (h1 : term76 _104196 t) : term524 _104196 p2 t.
Proof. exact (@lem4338861 _104196 p2 t h1). Qed.
Lemma lem4338865 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term76 _104196 t) (h2 : term406 _104190 _104196 p1 p2 s s' t t') : False.
Proof. exact (@lem4338862 _104196 p2 t h1 (@lem4338852 _104190 _104196 p1 p2 s s' t t' h2)). Qed.
Lemma lem4338866 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term76 _104196 t) (h2 : term406 _104190 _104196 p1 p2 s s' t t') : term525.
Proof. exact (fun h0 : ~ False => @lem4338865 _104190 _104196 p1 p2 s s' t t' h1 h2). Qed.
Lemma lem4338868 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4338869 : term525 = False.
Proof. exact (@lem4338868 False). Qed.
Lemma lem4338870 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term76 _104196 t) (h2 : term406 _104190 _104196 p1 p2 s s' t t') : False.
Proof. exact (EQ_MP (@lem4338869) (@lem4338866 _104190 _104196 p1 p2 s s' t t' h1 h2)). Qed.
Lemma lem4338872 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term406 _104190 _104196 p1 p2 s s' t t') : @IN _104190 p1 s.
Proof. exact (proj1 (@lem4338110 _104190 _104196 p1 p2 s s' t t' h1)). Qed.
Lemma lem4338873 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term406 _104190 _104196 p1 p2 s s' t t') : term505 _104190 p1 s.
Proof. exact (fun h0 : term73 _104190 p1 s => @lem4338872 _104190 _104196 p1 p2 s s' t t' h1). Qed.
Lemma lem4338875 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4338876 {_104190 : Type'} (p1 : _104190) (s : _104190 -> Prop) : (term505 _104190 p1 s) = (@IN _104190 p1 s).
Proof. exact (@lem4338875 (@IN _104190 p1 s)). Qed.
Lemma lem4338877 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term406 _104190 _104196 p1 p2 s s' t t') : @IN _104190 p1 s.
Proof. exact (EQ_MP (@lem4338876 _104190 p1 s) (@lem4338873 _104190 _104196 p1 p2 s s' t t' h1)). Qed.
Lemma lem4338883 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4338884 {_104190 : Type'} (s' : _104190 -> Prop) (_49544 : _104190) (s : _104190 -> Prop) : (term155 _104190 s _49544 s') = (term526 _104190 s' _49544 s).
Proof. exact (@lem4338883 (@IN _104190 _49544 s') (term73 _104190 _49544 s)). Qed.
Lemma lem4338890 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4338891 {_104190 : Type'} (s' : _104190 -> Prop) (_49544 : _104190) (s : _104190 -> Prop) : (term533 _104190 s _49544 s') = (term534 _104190 s' _49544 s).
Proof. exact (MK_COMB (@lem4338890) (@lem4338884 _104190 s' _49544 s)). Qed.
Lemma lem4338897 {_104190 : Type'} (s' : _104190 -> Prop) (_49544 : _104190) (s : _104190 -> Prop) : (term526 _104190 s' _49544 s) = (term526 _104190 s' _49544 s).
Proof. exact (eq_refl (term526 _104190 s' _49544 s)). Qed.
Lemma lem4338898 {_104190 : Type'} (s' : _104190 -> Prop) (_49544 : _104190) (s : _104190 -> Prop) : ((term155 _104190 s _49544 s') = (term526 _104190 s' _49544 s)) = ((term526 _104190 s' _49544 s) = (term526 _104190 s' _49544 s)).
Proof. exact (MK_COMB (@lem4338891 _104190 s' _49544 s) (@lem4338897 _104190 s' _49544 s)). Qed.
Lemma lem4338900 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4338901 (x : Prop) : (x = x) = True.
Proof. exact (@lem4338900 Prop x). Qed.
Lemma lem4338902 {_104190 : Type'} (s' : _104190 -> Prop) (_49544 : _104190) (s : _104190 -> Prop) : ((term526 _104190 s' _49544 s) = (term526 _104190 s' _49544 s)) = True.
Proof. exact (@lem4338901 (term526 _104190 s' _49544 s)). Qed.
Lemma lem4338903 {_104190 : Type'} (s' : _104190 -> Prop) (_49544 : _104190) (s : _104190 -> Prop) : ((term155 _104190 s _49544 s') = (term526 _104190 s' _49544 s)) = True.
Proof. exact (TRANS (@lem4338898 _104190 s' _49544 s) (@lem4338902 _104190 s' _49544 s)). Qed.
Lemma lem4338904 {_104190 : Type'} (s' : _104190 -> Prop) (_49544 : _104190) (s : _104190 -> Prop) : True = ((term155 _104190 s _49544 s') = (term526 _104190 s' _49544 s)).
Proof. exact (SYM (@lem4338903 _104190 s' _49544 s)). Qed.
Lemma lem4338905 {_104190 : Type'} (s' : _104190 -> Prop) (_49544 : _104190) (s : _104190 -> Prop) : (term155 _104190 s _49544 s') = (term526 _104190 s' _49544 s).
Proof. exact (EQ_MP (@lem4338904 _104190 s' _49544 s) (@lem0)). Qed.
Lemma lem4338906 {_104190 _104196 : Type'} (_49544 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term171 _104190 _104196 s s' t t') : term526 _104190 s' _49544 s.
Proof. exact (EQ_MP (@lem4338905 _104190 s' _49544 s) (@lem4338506 _104190 _104196 _49544 s s' t t' h1)). Qed.
Lemma lem4338908 (b : Prop) (a : Prop) : (a \/ b) = (term514 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4338909 {_104190 : Type'} (s : _104190 -> Prop) (_49544 : _104190) (s' : _104190 -> Prop) : (term526 _104190 s' _49544 s) = (term535 _104190 s _49544 s').
Proof. exact (@lem4338908 (term73 _104190 _49544 s) (@IN _104190 _49544 s')). Qed.
Lemma lem4338911 (a : Prop) : (term110 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4338912 {_104190 : Type'} (_49544 : _104190) (s : _104190 -> Prop) : (term145 _104190 _49544 s) = (@IN _104190 _49544 s).
Proof. exact (@lem4338911 (@IN _104190 _49544 s)). Qed.
Lemma lem4338913 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4338914 {_104190 : Type'} (_49544 : _104190) (s : _104190 -> Prop) : (term536 _104190 _49544 s) = (term537 _104190 _49544 s).
Proof. exact (MK_COMB (@lem4338913) (@lem4338912 _104190 _49544 s)). Qed.
Lemma lem4338915 {_104190 : Type'} (_49544 : _104190) (s' : _104190 -> Prop) : (@IN _104190 _49544 s') = (@IN _104190 _49544 s').
Proof. exact (eq_refl (@IN _104190 _49544 s')). Qed.
Lemma lem4338916 {_104190 : Type'} (s : _104190 -> Prop) (_49544 : _104190) (s' : _104190 -> Prop) : (term535 _104190 s _49544 s') = (term111 _104190 s _49544 s').
Proof. exact (MK_COMB (@lem4338914 _104190 _49544 s) (@lem4338915 _104190 _49544 s')). Qed.
Lemma lem4338917 {_104190 : Type'} (s : _104190 -> Prop) (_49544 : _104190) (s' : _104190 -> Prop) : (term526 _104190 s' _49544 s) = (term111 _104190 s _49544 s').
Proof. exact (TRANS (@lem4338909 _104190 s _49544 s') (@lem4338916 _104190 s _49544 s')). Qed.
Lemma lem4338920 {_104190 _104196 : Type'} (_49544 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term171 _104190 _104196 s s' t t') : term111 _104190 s _49544 s'.
Proof. exact (EQ_MP (@lem4338917 _104190 s _49544 s') (@lem4338906 _104190 _104196 _49544 s s' t t' h1)). Qed.
Lemma lem4338921 {_104190 _104196 : Type'} (_49544 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term171 _104190 _104196 s s' t t') : term111 _104190 s _49544 s'.
Proof. exact (@lem4338920 _104190 _104196 _49544 s s' t t' h1). Qed.
Lemma lem4338922 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term171 _104190 _104196 s s' t t') : term111 _104190 s p1 s'.
Proof. exact (@lem4338921 _104190 _104196 p1 s s' t t' h1). Qed.
Lemma lem4338925 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term171 _104190 _104196 s s' t t') (h2 : term406 _104190 _104196 p1 p2 s s' t t') : @IN _104190 p1 s'.
Proof. exact (@lem4338922 _104190 _104196 p1 s s' t t' h1 (@lem4338877 _104190 _104196 p1 p2 s s' t t' h2)). Qed.
Lemma lem4338926 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term171 _104190 _104196 s s' t t') (h2 : term406 _104190 _104196 p1 p2 s s' t t') : term505 _104190 p1 s'.
Proof. exact (fun h0 : term73 _104190 p1 s' => @lem4338925 _104190 _104196 p1 p2 s s' t t' h1 h2). Qed.
Lemma lem4338928 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4338929 {_104190 : Type'} (p1 : _104190) (s' : _104190 -> Prop) : (term505 _104190 p1 s') = (@IN _104190 p1 s').
Proof. exact (@lem4338928 (@IN _104190 p1 s')). Qed.
Lemma lem4338930 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term171 _104190 _104196 s s' t t') (h2 : term406 _104190 _104196 p1 p2 s s' t t') : @IN _104190 p1 s'.
Proof. exact (EQ_MP (@lem4338929 _104190 p1 s') (@lem4338926 _104190 _104196 p1 p2 s s' t t' h1 h2)). Qed.
Lemma lem4338933 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4338935 {_104190 : Type'} (p1 : _104190) (s' : _104190 -> Prop) : (term73 _104190 p1 s') = (term524 _104190 p1 s').
Proof. exact (@lem4338933 (@IN _104190 p1 s')). Qed.
Lemma lem4338938 {_104190 : Type'} (p1 : _104190) (s' : _104190 -> Prop) (h1 : term73 _104190 p1 s') : term524 _104190 p1 s'.
Proof. exact (EQ_MP (@lem4338935 _104190 p1 s') (@lem4338500 _104190 p1 s' h1)). Qed.
Lemma lem4338941 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term73 _104190 p1 s') (h2 : term171 _104190 _104196 s s' t t') (h3 : term406 _104190 _104196 p1 p2 s s' t t') : False.
Proof. exact (@lem4338938 _104190 p1 s' h1 (@lem4338930 _104190 _104196 p1 p2 s s' t t' h2 h3)). Qed.
Lemma lem4338942 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term73 _104190 p1 s') (h2 : term171 _104190 _104196 s s' t t') (h3 : term406 _104190 _104196 p1 p2 s s' t t') : term525.
Proof. exact (fun h0 : ~ False => @lem4338941 _104190 _104196 p1 p2 s s' t t' h1 h2 h3). Qed.
Lemma lem4338944 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4338945 : term525 = False.
Proof. exact (@lem4338944 False). Qed.
Lemma lem4338946 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term73 _104190 p1 s') (h2 : term171 _104190 _104196 s s' t t') (h3 : term406 _104190 _104196 p1 p2 s s' t t') : False.
Proof. exact (EQ_MP (@lem4338945) (@lem4338942 _104190 _104196 p1 p2 s s' t t' h1 h2 h3)). Qed.
Lemma lem4338948 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term406 _104190 _104196 p1 p2 s s' t t') : @IN _104190 p1 s.
Proof. exact (proj1 (@lem4338110 _104190 _104196 p1 p2 s s' t t' h1)). Qed.
Lemma lem4338949 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term406 _104190 _104196 p1 p2 s s' t t') : term505 _104190 p1 s.
Proof. exact (fun h0 : term73 _104190 p1 s => @lem4338948 _104190 _104196 p1 p2 s s' t t' h1). Qed.
Lemma lem4338951 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4338952 {_104190 : Type'} (p1 : _104190) (s : _104190 -> Prop) : (term505 _104190 p1 s) = (@IN _104190 p1 s).
Proof. exact (@lem4338951 (@IN _104190 p1 s)). Qed.
Lemma lem4338953 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term406 _104190 _104196 p1 p2 s s' t t') : @IN _104190 p1 s.
Proof. exact (EQ_MP (@lem4338952 _104190 p1 s) (@lem4338949 _104190 _104196 p1 p2 s s' t t' h1)). Qed.
Lemma lem4338956 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4338958 {_104190 : Type'} (_49546 : _104190) (s : _104190 -> Prop) : (term73 _104190 _49546 s) = (term524 _104190 _49546 s).
Proof. exact (@lem4338956 (@IN _104190 _49546 s)). Qed.
Lemma lem4338961 {_104190 : Type'} (_49546 : _104190) (s : _104190 -> Prop) (h1 : term76 _104190 s) : term524 _104190 _49546 s.
Proof. exact (EQ_MP (@lem4338958 _104190 _49546 s) (@lem4338520 _104190 _49546 s h1)). Qed.
Lemma lem4338962 {_104190 : Type'} (_49546 : _104190) (s : _104190 -> Prop) (h1 : term76 _104190 s) : term524 _104190 _49546 s.
Proof. exact (@lem4338961 _104190 _49546 s h1). Qed.
Lemma lem4338963 {_104190 : Type'} (p1 : _104190) (s : _104190 -> Prop) (h1 : term76 _104190 s) : term524 _104190 p1 s.
Proof. exact (@lem4338962 _104190 p1 s h1). Qed.
Lemma lem4338966 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term76 _104190 s) (h2 : term406 _104190 _104196 p1 p2 s s' t t') : False.
Proof. exact (@lem4338963 _104190 p1 s h1 (@lem4338953 _104190 _104196 p1 p2 s s' t t' h2)). Qed.
Lemma lem4338967 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term76 _104190 s) (h2 : term406 _104190 _104196 p1 p2 s s' t t') : term525.
Proof. exact (fun h0 : ~ False => @lem4338966 _104190 _104196 p1 p2 s s' t t' h1 h2). Qed.
Lemma lem4338969 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4338970 : term525 = False.
Proof. exact (@lem4338969 False). Qed.
Lemma lem4338971 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term76 _104190 s) (h2 : term406 _104190 _104196 p1 p2 s s' t t') : False.
Proof. exact (EQ_MP (@lem4338970) (@lem4338967 _104190 _104196 p1 p2 s s' t t' h1 h2)). Qed.
Lemma lem4338973 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term406 _104190 _104196 p1 p2 s s' t t') : @IN _104196 p2 t.
Proof. exact (proj2 (@lem4338110 _104190 _104196 p1 p2 s s' t t' h1)). Qed.
Lemma lem4338974 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term406 _104190 _104196 p1 p2 s s' t t') : term505 _104196 p2 t.
Proof. exact (fun h0 : term73 _104196 p2 t => @lem4338973 _104190 _104196 p1 p2 s s' t t' h1). Qed.
Lemma lem4338976 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4338977 {_104196 : Type'} (p2 : _104196) (t : _104196 -> Prop) : (term505 _104196 p2 t) = (@IN _104196 p2 t).
Proof. exact (@lem4338976 (@IN _104196 p2 t)). Qed.
Lemma lem4338978 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term406 _104190 _104196 p1 p2 s s' t t') : @IN _104196 p2 t.
Proof. exact (EQ_MP (@lem4338977 _104196 p2 t) (@lem4338974 _104190 _104196 p1 p2 s s' t t' h1)). Qed.
Lemma lem4338981 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4338983 {_104196 : Type'} (_49547 : _104196) (t : _104196 -> Prop) : (term73 _104196 _49547 t) = (term524 _104196 _49547 t).
Proof. exact (@lem4338981 (@IN _104196 _49547 t)). Qed.
Lemma lem4338986 {_104196 : Type'} (_49547 : _104196) (t : _104196 -> Prop) (h1 : term76 _104196 t) : term524 _104196 _49547 t.
Proof. exact (EQ_MP (@lem4338983 _104196 _49547 t) (@lem4338528 _104196 _49547 t h1)). Qed.
Lemma lem4338987 {_104196 : Type'} (_49547 : _104196) (t : _104196 -> Prop) (h1 : term76 _104196 t) : term524 _104196 _49547 t.
Proof. exact (@lem4338986 _104196 _49547 t h1). Qed.
Lemma lem4338988 {_104196 : Type'} (p2 : _104196) (t : _104196 -> Prop) (h1 : term76 _104196 t) : term524 _104196 p2 t.
Proof. exact (@lem4338987 _104196 p2 t h1). Qed.
Lemma lem4338991 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term76 _104196 t) (h2 : term406 _104190 _104196 p1 p2 s s' t t') : False.
Proof. exact (@lem4338988 _104196 p2 t h1 (@lem4338978 _104190 _104196 p1 p2 s s' t t' h2)). Qed.
Lemma lem4338992 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term76 _104196 t) (h2 : term406 _104190 _104196 p1 p2 s s' t t') : term525.
Proof. exact (fun h0 : ~ False => @lem4338991 _104190 _104196 p1 p2 s s' t t' h1 h2). Qed.
Lemma lem4338994 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4338995 : term525 = False.
Proof. exact (@lem4338994 False). Qed.
Lemma lem4338996 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term76 _104196 t) (h2 : term406 _104190 _104196 p1 p2 s s' t t') : False.
Proof. exact (EQ_MP (@lem4338995) (@lem4338992 _104190 _104196 p1 p2 s s' t t' h1 h2)). Qed.
Lemma lem4338998 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term406 _104190 _104196 p1 p2 s s' t t') : @IN _104196 p2 t.
Proof. exact (proj2 (@lem4338110 _104190 _104196 p1 p2 s s' t t' h1)). Qed.
Lemma lem4338999 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term406 _104190 _104196 p1 p2 s s' t t') : term505 _104196 p2 t.
Proof. exact (fun h0 : term73 _104196 p2 t => @lem4338998 _104190 _104196 p1 p2 s s' t t' h1). Qed.
Lemma lem4339001 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4339002 {_104196 : Type'} (p2 : _104196) (t : _104196 -> Prop) : (term505 _104196 p2 t) = (@IN _104196 p2 t).
Proof. exact (@lem4339001 (@IN _104196 p2 t)). Qed.
Lemma lem4339003 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term406 _104190 _104196 p1 p2 s s' t t') : @IN _104196 p2 t.
Proof. exact (EQ_MP (@lem4339002 _104196 p2 t) (@lem4338999 _104190 _104196 p1 p2 s s' t t' h1)). Qed.
Lemma lem4339009 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4339010 {_104196 : Type'} (t' : _104196 -> Prop) (_49549 : _104196) (t : _104196 -> Prop) : (term155 _104196 t _49549 t') = (term526 _104196 t' _49549 t).
Proof. exact (@lem4339009 (@IN _104196 _49549 t') (term73 _104196 _49549 t)). Qed.
Lemma lem4339016 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4339017 {_104196 : Type'} (t' : _104196 -> Prop) (_49549 : _104196) (t : _104196 -> Prop) : (term533 _104196 t _49549 t') = (term534 _104196 t' _49549 t).
Proof. exact (MK_COMB (@lem4339016) (@lem4339010 _104196 t' _49549 t)). Qed.
Lemma lem4339023 {_104196 : Type'} (t' : _104196 -> Prop) (_49549 : _104196) (t : _104196 -> Prop) : (term526 _104196 t' _49549 t) = (term526 _104196 t' _49549 t).
Proof. exact (eq_refl (term526 _104196 t' _49549 t)). Qed.
Lemma lem4339024 {_104196 : Type'} (t' : _104196 -> Prop) (_49549 : _104196) (t : _104196 -> Prop) : ((term155 _104196 t _49549 t') = (term526 _104196 t' _49549 t)) = ((term526 _104196 t' _49549 t) = (term526 _104196 t' _49549 t)).
Proof. exact (MK_COMB (@lem4339017 _104196 t' _49549 t) (@lem4339023 _104196 t' _49549 t)). Qed.
Lemma lem4339026 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4339027 (x : Prop) : (x = x) = True.
Proof. exact (@lem4339026 Prop x). Qed.
Lemma lem4339028 {_104196 : Type'} (t' : _104196 -> Prop) (_49549 : _104196) (t : _104196 -> Prop) : ((term526 _104196 t' _49549 t) = (term526 _104196 t' _49549 t)) = True.
Proof. exact (@lem4339027 (term526 _104196 t' _49549 t)). Qed.
Lemma lem4339029 {_104196 : Type'} (t' : _104196 -> Prop) (_49549 : _104196) (t : _104196 -> Prop) : ((term155 _104196 t _49549 t') = (term526 _104196 t' _49549 t)) = True.
Proof. exact (TRANS (@lem4339024 _104196 t' _49549 t) (@lem4339028 _104196 t' _49549 t)). Qed.
Lemma lem4339030 {_104196 : Type'} (t' : _104196 -> Prop) (_49549 : _104196) (t : _104196 -> Prop) : True = ((term155 _104196 t _49549 t') = (term526 _104196 t' _49549 t)).
Proof. exact (SYM (@lem4339029 _104196 t' _49549 t)). Qed.
Lemma lem4339031 {_104196 : Type'} (t' : _104196 -> Prop) (_49549 : _104196) (t : _104196 -> Prop) : (term155 _104196 t _49549 t') = (term526 _104196 t' _49549 t).
Proof. exact (EQ_MP (@lem4339030 _104196 t' _49549 t) (@lem0)). Qed.
Lemma lem4339032 {_104190 _104196 : Type'} (_49549 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term171 _104190 _104196 s s' t t') : term526 _104196 t' _49549 t.
Proof. exact (EQ_MP (@lem4339031 _104196 t' _49549 t) (@lem4338546 _104190 _104196 _49549 s s' t t' h1)). Qed.
Lemma lem4339034 (b : Prop) (a : Prop) : (a \/ b) = (term514 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4339035 {_104196 : Type'} (t : _104196 -> Prop) (_49549 : _104196) (t' : _104196 -> Prop) : (term526 _104196 t' _49549 t) = (term535 _104196 t _49549 t').
Proof. exact (@lem4339034 (term73 _104196 _49549 t) (@IN _104196 _49549 t')). Qed.
Lemma lem4339037 (a : Prop) : (term110 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4339038 {_104196 : Type'} (_49549 : _104196) (t : _104196 -> Prop) : (term145 _104196 _49549 t) = (@IN _104196 _49549 t).
Proof. exact (@lem4339037 (@IN _104196 _49549 t)). Qed.
Lemma lem4339039 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4339040 {_104196 : Type'} (_49549 : _104196) (t : _104196 -> Prop) : (term536 _104196 _49549 t) = (term537 _104196 _49549 t).
Proof. exact (MK_COMB (@lem4339039) (@lem4339038 _104196 _49549 t)). Qed.
Lemma lem4339041 {_104196 : Type'} (_49549 : _104196) (t' : _104196 -> Prop) : (@IN _104196 _49549 t') = (@IN _104196 _49549 t').
Proof. exact (eq_refl (@IN _104196 _49549 t')). Qed.
Lemma lem4339042 {_104196 : Type'} (t : _104196 -> Prop) (_49549 : _104196) (t' : _104196 -> Prop) : (term535 _104196 t _49549 t') = (term111 _104196 t _49549 t').
Proof. exact (MK_COMB (@lem4339040 _104196 _49549 t) (@lem4339041 _104196 _49549 t')). Qed.
Lemma lem4339043 {_104196 : Type'} (t : _104196 -> Prop) (_49549 : _104196) (t' : _104196 -> Prop) : (term526 _104196 t' _49549 t) = (term111 _104196 t _49549 t').
Proof. exact (TRANS (@lem4339035 _104196 t _49549 t') (@lem4339042 _104196 t _49549 t')). Qed.
Lemma lem4339046 {_104190 _104196 : Type'} (_49549 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term171 _104190 _104196 s s' t t') : term111 _104196 t _49549 t'.
Proof. exact (EQ_MP (@lem4339043 _104196 t _49549 t') (@lem4339032 _104190 _104196 _49549 s s' t t' h1)). Qed.
Lemma lem4339047 {_104190 _104196 : Type'} (_49549 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term171 _104190 _104196 s s' t t') : term111 _104196 t _49549 t'.
Proof. exact (@lem4339046 _104190 _104196 _49549 s s' t t' h1). Qed.
Lemma lem4339048 {_104190 _104196 : Type'} (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term171 _104190 _104196 s s' t t') : term111 _104196 t p2 t'.
Proof. exact (@lem4339047 _104190 _104196 p2 s s' t t' h1). Qed.
Lemma lem4339051 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term171 _104190 _104196 s s' t t') (h2 : term406 _104190 _104196 p1 p2 s s' t t') : @IN _104196 p2 t'.
Proof. exact (@lem4339048 _104190 _104196 p2 s s' t t' h1 (@lem4339003 _104190 _104196 p1 p2 s s' t t' h2)). Qed.
Lemma lem4339052 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term171 _104190 _104196 s s' t t') (h2 : term406 _104190 _104196 p1 p2 s s' t t') : term505 _104196 p2 t'.
Proof. exact (fun h0 : term73 _104196 p2 t' => @lem4339051 _104190 _104196 p1 p2 s s' t t' h1 h2). Qed.
Lemma lem4339054 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4339055 {_104196 : Type'} (p2 : _104196) (t' : _104196 -> Prop) : (term505 _104196 p2 t') = (@IN _104196 p2 t').
Proof. exact (@lem4339054 (@IN _104196 p2 t')). Qed.
Lemma lem4339056 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term171 _104190 _104196 s s' t t') (h2 : term406 _104190 _104196 p1 p2 s s' t t') : @IN _104196 p2 t'.
Proof. exact (EQ_MP (@lem4339055 _104196 p2 t') (@lem4339052 _104190 _104196 p1 p2 s s' t t' h1 h2)). Qed.
Lemma lem4339059 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4339061 {_104196 : Type'} (p2 : _104196) (t' : _104196 -> Prop) : (term73 _104196 p2 t') = (term524 _104196 p2 t').
Proof. exact (@lem4339059 (@IN _104196 p2 t')). Qed.
Lemma lem4339064 {_104196 : Type'} (p2 : _104196) (t' : _104196 -> Prop) (h1 : term73 _104196 p2 t') : term524 _104196 p2 t'.
Proof. exact (EQ_MP (@lem4339061 _104196 p2 t') (@lem4338534 _104196 p2 t' h1)). Qed.
Lemma lem4339067 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term73 _104196 p2 t') (h2 : term171 _104190 _104196 s s' t t') (h3 : term406 _104190 _104196 p1 p2 s s' t t') : False.
Proof. exact (@lem4339064 _104196 p2 t' h1 (@lem4339056 _104190 _104196 p1 p2 s s' t t' h2 h3)). Qed.
Lemma lem4339068 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term73 _104196 p2 t') (h2 : term171 _104190 _104196 s s' t t') (h3 : term406 _104190 _104196 p1 p2 s s' t t') : term525.
Proof. exact (fun h0 : ~ False => @lem4339067 _104190 _104196 p1 p2 s s' t t' h1 h2 h3). Qed.
Lemma lem4339070 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4339071 : term525 = False.
Proof. exact (@lem4339070 False). Qed.
Lemma lem4339072 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term73 _104196 p2 t') (h2 : term171 _104190 _104196 s s' t t') (h3 : term406 _104190 _104196 p1 p2 s s' t t') : False.
Proof. exact (EQ_MP (@lem4339071) (@lem4339068 _104190 _104196 p1 p2 s s' t t' h1 h2 h3)). Qed.
Lemma lem4339073 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term73 _104196 p2 t') (h2 : term171 _104190 _104196 s s' t t') (h3 : term406 _104190 _104196 p1 p2 s s' t t') : (term73 _104196 p2 t') = False.
Proof. exact (prop_ext (fun h4 : term73 _104196 p2 t' => @lem4339072 _104190 _104196 p1 p2 s s' t t' h1 h2 h3) (fun h4 : False => @lem4338534 _104196 p2 t' h1)). Qed.
Lemma lem4339074 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term73 _104196 p2 t') (h2 : term171 _104190 _104196 s s' t t') (h3 : term406 _104190 _104196 p1 p2 s s' t t') : False.
Proof. exact (EQ_MP (@lem4339073 _104190 _104196 p1 p2 s s' t t' h1 h2 h3) (@lem4338534 _104196 p2 t' h1)). Qed.
Lemma lem4339075 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term73 _104190 p1 s') (h2 : term171 _104190 _104196 s s' t t') (h3 : term406 _104190 _104196 p1 p2 s s' t t') : (term73 _104190 p1 s') = False.
Proof. exact (prop_ext (fun h4 : term73 _104190 p1 s' => @lem4338946 _104190 _104196 p1 p2 s s' t t' h1 h2 h3) (fun h4 : False => @lem4338500 _104190 p1 s' h1)). Qed.
Lemma lem4339076 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term73 _104190 p1 s') (h2 : term171 _104190 _104196 s s' t t') (h3 : term406 _104190 _104196 p1 p2 s s' t t') : False.
Proof. exact (EQ_MP (@lem4339075 _104190 _104196 p1 p2 s s' t t' h1 h2 h3) (@lem4338500 _104190 p1 s' h1)). Qed.
Lemma lem4339077 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term73 _104196 p2 t') (h2 : term171 _104190 _104196 s s' t t') (h3 : term406 _104190 _104196 p1 p2 s s' t t') : (term73 _104196 p2 t') = False.
Proof. exact (prop_ext (fun h4 : term73 _104196 p2 t' => @lem4339074 _104190 _104196 p1 p2 s s' t t' h1 h2 h3) (fun h4 : False => @lem4338348 _104196 p2 t' h1)). Qed.
Lemma lem4339078 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term73 _104196 p2 t') (h2 : term171 _104190 _104196 s s' t t') (h3 : term406 _104190 _104196 p1 p2 s s' t t') : False.
Proof. exact (EQ_MP (@lem4339077 _104190 _104196 p1 p2 s s' t t' h1 h2 h3) (@lem4338348 _104196 p2 t' h1)). Qed.
Lemma lem4339079 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term73 _104190 p1 s') (h2 : term171 _104190 _104196 s s' t t') (h3 : term406 _104190 _104196 p1 p2 s s' t t') : (term73 _104190 p1 s') = False.
Proof. exact (prop_ext (fun h4 : term73 _104190 p1 s' => @lem4339076 _104190 _104196 p1 p2 s s' t t' h1 h2 h3) (fun h4 : False => @lem4338272 _104190 p1 s' h1)). Qed.
Lemma lem4339080 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term73 _104190 p1 s') (h2 : term171 _104190 _104196 s s' t t') (h3 : term406 _104190 _104196 p1 p2 s s' t t') : False.
Proof. exact (EQ_MP (@lem4339079 _104190 _104196 p1 p2 s s' t t' h1 h2 h3) (@lem4338272 _104190 p1 s' h1)). Qed.
Lemma lem4339081 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term73 _104196 p2 t') (h2 : term171 _104190 _104196 s s' t t') (h3 : term406 _104190 _104196 p1 p2 s s' t t') : (term73 _104196 p2 t') = False.
Proof. exact (prop_ext (fun h4 : term73 _104196 p2 t' => @lem4339078 _104190 _104196 p1 p2 s s' t t' h1 h2 h3) (fun h4 : False => @lem4338348 _104196 p2 t' h1)). Qed.
Lemma lem4339082 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term73 _104196 p2 t') (h2 : term171 _104190 _104196 s s' t t') (h3 : term406 _104190 _104196 p1 p2 s s' t t') : False.
Proof. exact (EQ_MP (@lem4339081 _104190 _104196 p1 p2 s s' t t' h1 h2 h3) (@lem4338348 _104196 p2 t' h1)). Qed.
Lemma lem4339083 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term76 _104196 t) (h2 : term406 _104190 _104196 p1 p2 s s' t t') : (term76 _104196 t) = False.
Proof. exact (prop_ext (fun h3 : term76 _104196 t => @lem4338996 _104190 _104196 p1 p2 s s' t t' h1 h2) (fun h3 : False => @lem4338336 _104196 t h1)). Qed.
Lemma lem4339084 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term76 _104196 t) (h2 : term406 _104190 _104196 p1 p2 s s' t t') : False.
Proof. exact (EQ_MP (@lem4339083 _104190 _104196 p1 p2 s s' t t' h1 h2) (@lem4338336 _104196 t h1)). Qed.
Lemma lem4339085 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term76 _104190 s) (h2 : term406 _104190 _104196 p1 p2 s s' t t') : (term76 _104190 s) = False.
Proof. exact (prop_ext (fun h3 : term76 _104190 s => @lem4338971 _104190 _104196 p1 p2 s s' t t' h1 h2) (fun h3 : False => @lem4338317 _104190 s h1)). Qed.
Lemma lem4339086 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term76 _104190 s) (h2 : term406 _104190 _104196 p1 p2 s s' t t') : False.
Proof. exact (EQ_MP (@lem4339085 _104190 _104196 p1 p2 s s' t t' h1 h2) (@lem4338317 _104190 s h1)). Qed.
Lemma lem4339087 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term73 _104190 p1 s') (h2 : term171 _104190 _104196 s s' t t') (h3 : term406 _104190 _104196 p1 p2 s s' t t') : (term73 _104190 p1 s') = False.
Proof. exact (prop_ext (fun h4 : term73 _104190 p1 s' => @lem4339080 _104190 _104196 p1 p2 s s' t t' h1 h2 h3) (fun h4 : False => @lem4338272 _104190 p1 s' h1)). Qed.
Lemma lem4339088 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term73 _104190 p1 s') (h2 : term171 _104190 _104196 s s' t t') (h3 : term406 _104190 _104196 p1 p2 s s' t t') : False.
Proof. exact (EQ_MP (@lem4339087 _104190 _104196 p1 p2 s s' t t' h1 h2 h3) (@lem4338272 _104190 p1 s' h1)). Qed.
Lemma lem4339089 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term76 _104196 t) (h2 : term406 _104190 _104196 p1 p2 s s' t t') : (term76 _104196 t) = False.
Proof. exact (prop_ext (fun h3 : term76 _104196 t => @lem4338870 _104190 _104196 p1 p2 s s' t t' h1 h2) (fun h3 : False => @lem4338260 _104196 t h1)). Qed.
Lemma lem4339090 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term76 _104196 t) (h2 : term406 _104190 _104196 p1 p2 s s' t t') : False.
Proof. exact (EQ_MP (@lem4339089 _104190 _104196 p1 p2 s s' t t' h1 h2) (@lem4338260 _104196 t h1)). Qed.
Lemma lem4339091 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term76 _104190 s) (h2 : term406 _104190 _104196 p1 p2 s s' t t') : (term76 _104190 s) = False.
Proof. exact (prop_ext (fun h3 : term76 _104190 s => @lem4338845 _104190 _104196 p1 p2 s s' t t' h1 h2) (fun h3 : False => @lem4338241 _104190 s h1)). Qed.
Lemma lem4339092 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term76 _104190 s) (h2 : term406 _104190 _104196 p1 p2 s s' t t') : False.
Proof. exact (EQ_MP (@lem4339091 _104190 _104196 p1 p2 s s' t t' h1 h2) (@lem4338241 _104190 s h1)). Qed.
Lemma lem4339093 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term73 _104196 p2 t') (h2 : term406 _104190 _104196 p1 p2 s s' t t') (h3 : term177 _104190 _104196 s s' t t') : False.
Proof. exact (or_elim (@lem4338122 _104190 _104196 s s' t t' h3) (fun h0 : term76 _104196 t => @lem4339084 _104190 _104196 p1 p2 s s' t t' h0 h2) (fun h0 : term171 _104190 _104196 s s' t t' => @lem4339082 _104190 _104196 p1 p2 s s' t t' h1 h0 h2)). Qed.
Lemma lem4339094 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term73 _104196 p2 t') (h2 : term406 _104190 _104196 p1 p2 s s' t t') : False.
Proof. exact (or_elim (@lem4338107 _104190 _104196 p1 p2 s s' t t' h2) (fun h0 : term76 _104190 s => @lem4339086 _104190 _104196 p1 p2 s s' t t' h0 h2) (fun h0 : term177 _104190 _104196 s s' t t' => @lem4339093 _104190 _104196 p1 p2 s s' t t' h1 h2 h0)). Qed.
Lemma lem4339095 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term73 _104190 p1 s') (h2 : term406 _104190 _104196 p1 p2 s s' t t') (h3 : term177 _104190 _104196 s s' t t') : False.
Proof. exact (or_elim (@lem4338116 _104190 _104196 s s' t t' h3) (fun h0 : term76 _104196 t => @lem4339090 _104190 _104196 p1 p2 s s' t t' h0 h2) (fun h0 : term171 _104190 _104196 s s' t t' => @lem4339088 _104190 _104196 p1 p2 s s' t t' h1 h0 h2)). Qed.
Lemma lem4339096 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term73 _104190 p1 s') (h2 : term406 _104190 _104196 p1 p2 s s' t t') : False.
Proof. exact (or_elim (@lem4338107 _104190 _104196 p1 p2 s s' t t' h2) (fun h0 : term76 _104190 s => @lem4339092 _104190 _104196 p1 p2 s s' t t' h0 h2) (fun h0 : term177 _104190 _104196 s s' t t' => @lem4339095 _104190 _104196 p1 p2 s s' t t' h1 h2 h0)). Qed.
Lemma lem4339097 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term406 _104190 _104196 p1 p2 s s' t t') : False.
Proof. exact (or_elim (@lem4338109 _104190 _104196 p1 p2 s s' t t' h1) (fun h0 : term73 _104190 p1 s' => @lem4339096 _104190 _104196 p1 p2 s s' t t' h0 h1) (fun h0 : term73 _104196 p2 t' => @lem4339094 _104190 _104196 p1 p2 s s' t t' h0 h1)). Qed.
Lemma lem4339098 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (x' : _104190) (s' : _104190 -> Prop) (t : _104196 -> Prop) (x'' : _104196) (t' : _104196 -> Prop) (h1 : term369 _104190 _104196 p1 p2 s x' s' t x'' t') : False.
Proof. exact (or_elim (@lem4338099 _104190 _104196 p1 p2 s x' s' t x'' t' h1) (fun h0 : term154 _104190 s x' s' => @lem4338683 _104190 _104196 p1 p2 t x'' t' s x' s' h1 h0) (fun h0 : term154 _104196 t x'' t' => @lem4338820 _104190 _104196 p1 p2 s x' s' t x'' t' h1 h0)). Qed.
Lemma lem4339099 {_104190 _104196 : Type'} (x' : _104190) (x'' : _104196) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term483 _104190 _104196 x' x'' p1 p2 s s' t t') : False.
Proof. exact (or_elim (@lem4338092 _104190 _104196 x' x'' p1 p2 s s' t t' h1) (fun h0 : term369 _104190 _104196 p1 p2 s x' s' t x'' t' => @lem4339098 _104190 _104196 p1 p2 s x' s' t x'' t' h0) (fun h0 : term406 _104190 _104196 p1 p2 s s' t t' => @lem4339097 _104190 _104196 p1 p2 s s' t t' h0)). Qed.
Lemma lem4339100 {_104190 _104196 : Type'} (x' : _104190) (x'' : _104196) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term483 _104190 _104196 x' x'' p1 p2 s s' t t') : (term483 _104190 _104196 x' x'' p1 p2 s s' t t') = False.
Proof. exact (prop_ext (fun h2 : term483 _104190 _104196 x' x'' p1 p2 s s' t t' => @lem4339099 _104190 _104196 x' x'' p1 p2 s s' t t' h1) (fun h2 : False => @lem4338092 _104190 _104196 x' x'' p1 p2 s s' t t' h1)). Qed.
Lemma lem4339101 {_104190 _104196 : Type'} (x' : _104190) (x'' : _104196) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term483 _104190 _104196 x' x'' p1 p2 s s' t t') : False.
Proof. exact (EQ_MP (@lem4339100 _104190 _104196 x' x'' p1 p2 s s' t t' h1) (@lem4338092 _104190 _104196 x' x'' p1 p2 s s' t t' h1)). Qed.
Lemma lem4339102 {_104190 _104196 : Type'} (x' : _104190) (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term486 _104190 _104196 x' p1 p2 s s' t t') : False.
Proof. exact (ex_elim (@lem4337895 _104190 _104196 x' p1 p2 s s' t t' h1) (fun x'' : _104196 => fun h0 : term485 _104190 _104196 x' p1 p2 s s' t t' x'' => @lem4339101 _104190 _104196 x' x'' p1 p2 s s' t t' h0)). Qed.
Lemma lem4339103 {_104190 _104196 : Type'} (p1 : _104190) (p2 : _104196) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term488 _104190 _104196 p1 p2 s s' t t') : False.
Proof. exact (ex_elim (@lem4337894 _104190 _104196 p1 p2 s s' t t' h1) (fun x' : _104190 => fun h0 : term487 _104190 _104196 p1 p2 s s' t t' x' => @lem4339102 _104190 _104196 x' p1 p2 s s' t t' h0)). Qed.
Lemma lem4339104 {_104190 _104196 : Type'} (p1 : _104190) (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term490 _104190 _104196 p1 s s' t t') : False.
Proof. exact (ex_elim (@lem4337893 _104190 _104196 p1 s s' t t' h1) (fun p2 : _104196 => fun h0 : term489 _104190 _104196 p1 s s' t t' p2 => @lem4339103 _104190 _104196 p1 p2 s s' t t' h0)). Qed.
Lemma lem4339105 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term114 _104190 _104196 s s' t t') : False.
Proof. exact (ex_elim (@lem4337892 _104190 _104196 s s' t t' h1) (fun p1 : _104190 => fun h0 : term491 _104190 _104196 s s' t t' p1 => @lem4339104 _104190 _104196 p1 s s' t t' h0)). Qed.
Lemma lem4339106 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term114 _104190 _104196 s s' t t') : (term114 _104190 _104196 s s' t t') = False.
Proof. exact (prop_ext (fun h2 : term114 _104190 _104196 s s' t t' => @lem4339105 _104190 _104196 s s' t t' h1) (fun h2 : False => @lem4336876 _104190 _104196 s s' t t' h1)). Qed.
Lemma lem4339107 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) (h1 : term114 _104190 _104196 s s' t t') : False.
Proof. exact (EQ_MP (@lem4339106 _104190 _104196 s s' t t' h1) (@lem4336876 _104190 _104196 s s' t t' h1)). Qed.
Lemma lem4339108 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : term113 _104190 _104196 s s' t t'.
Proof. exact (fun h0 : term114 _104190 _104196 s s' t t' => @lem4339107 _104190 _104196 s s' t t' h0). Qed.
Lemma lem4339109 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term68 _104190 _104196 s t s' t') = (term86 _104190 _104196 s s' t t').
Proof. exact (EQ_MP (@lem4336875 _104190 _104196 s s' t t') (@lem4339108 _104190 _104196 s s' t t')). Qed.
Lemma lem4339114 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) : term90 _104190 _104196 s s' t.
Proof. exact (fun t' : _104196 -> Prop => @lem4339109 _104190 _104196 s s' t t'). Qed.
Lemma lem4339119 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) : term94 _104190 _104196 s t.
Proof. exact (fun s' : _104190 -> Prop => @lem4339114 _104190 _104196 s s' t). Qed.
Lemma lem4339124 {_104190 _104196 : Type'} (s : _104190 -> Prop) : term98 _104190 _104196 s.
Proof. exact (fun t : _104196 -> Prop => @lem4339119 _104190 _104196 s t). Qed.
Lemma lem4339129 {_104190 _104196 : Type'} : term102 _104190 _104196.
Proof. exact (fun s : _104190 -> Prop => @lem4339124 _104190 _104196 s). Qed.
Lemma lem4339130 {_104190 _104196 : Type'} : term104 _104190 _104196.
Proof. exact (EQ_MP (@lem4336871 _104190 _104196) (@lem4339129 _104190 _104196)). Qed.
Lemma lem4339132 {_104190 _104196 : Type'} : term104 _104190 _104196.
Proof. exact (@lem4336653 _104190 _104196 (@lem4339130 _104190 _104196)). Qed.
Lemma lem4339133 {_104190 _104196 : Type'} (h1 : term105 _104190 _104196) : False.
Proof. exact (@lem4339132 _104190 _104196 (@lem4336637 _104190 _104196 h1)). Qed.
Lemma lem4339134 {_104190 _104196 : Type'} (h1 : term105 _104190 _104196) : (term105 _104190 _104196) = False.
Proof. exact (prop_ext (fun h2 : term105 _104190 _104196 => @lem4339133 _104190 _104196 h1) (fun h2 : False => @lem4336637 _104190 _104196 h1)). Qed.
Lemma lem4339135 {_104190 _104196 : Type'} (h1 : term105 _104190 _104196) : False.
Proof. exact (EQ_MP (@lem4339134 _104190 _104196 h1) (@lem4336637 _104190 _104196 h1)). Qed.
Lemma lem4339136 {_104190 _104196 : Type'} : term104 _104190 _104196.
Proof. exact (fun h0 : term105 _104190 _104196 => @lem4339135 _104190 _104196 h0). Qed.
Lemma lem4339137 {_104190 _104196 : Type'} : term102 _104190 _104196.
Proof. exact (EQ_MP (@lem4336636 _104190 _104196) (@lem4339136 _104190 _104196)). Qed.
Lemma lem4339138 {_104190 _104196 : Type'} : term101 _104190 _104196.
Proof. exact (EQ_MP (@lem4336632 _104190 _104196) (@lem4339137 _104190 _104196)). Qed.
