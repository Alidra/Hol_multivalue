Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INJECTIVE_ON_LEFT_INVERSE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import SKOLEM_THM_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
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
Require Import thm21385_spec.
Require Import thm21386_spec.
Lemma lem3562738 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3562739 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3562740 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3562739 t1) (@lem3562738 t1)). Qed.
Lemma lem3562741 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3562740 t1 t2). Qed.
Lemma lem3562742 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3562743 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3562742 t1 t2) (@lem3562741 t1 t2)). Qed.
Lemma lem3562744 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3562743 t1 t2 t3). Qed.
Lemma lem3562745 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3562746 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3562745 t1 t2 t3) (@lem3562744 t1 t2 t3)). Qed.
Lemma lem3562747 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3562746 t1 t2 t3)). Qed.
Lemma lem3562749 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3562750 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : ((term8 _91345 _91348 s g f) = (term9 _91345 _91348 s f g)) = (term10 _91345 _91348 s f g).
Proof. exact (@lem3562749 ((term8 _91345 _91348 s g f) = (term9 _91345 _91348 s f g))). Qed.
Lemma lem3562751 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term10 _91345 _91348 s f g) = ((term8 _91345 _91348 s g f) = (term9 _91345 _91348 s f g)).
Proof. exact (SYM (@lem3562750 _91345 _91348 s f g)). Qed.
Lemma lem3562752 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term11 _91345 _91348 s f g) : term11 _91345 _91348 s f g.
Proof. exact (h1). Qed.
Lemma lem3562755 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term10 _91345 _91348 s f g) : term10 _91345 _91348 s f g.
Proof. exact (h1). Qed.
Lemma lem3562756 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : term12 _91345 _91348 s f g.
Proof. exact (fun h0 : term10 _91345 _91348 s f g => @lem3562755 _91345 _91348 s f g h0). Qed.
Lemma lem3562757 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term12 _91345 _91348 s f g) : term12 _91345 _91348 s f g.
Proof. exact (h1). Qed.
Lemma lem3562758 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term10 _91345 _91348 s f g) : term10 _91345 _91348 s f g.
Proof. exact (h1). Qed.
Lemma lem3562759 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term10 _91345 _91348 s f g) (h2 : term12 _91345 _91348 s f g) : term10 _91345 _91348 s f g.
Proof. exact (@lem3562757 _91345 _91348 s f g h2 (@lem3562758 _91345 _91348 s f g h1)). Qed.
Lemma lem3562760 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term10 _91345 _91348 s f g) : term13 _91345 _91348 s f g.
Proof. exact (fun h0 : term12 _91345 _91348 s f g => @lem3562759 _91345 _91348 s f g h1 h0). Qed.
Lemma lem3562761 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term12 _91345 _91348 s f g) : term12 _91345 _91348 s f g.
Proof. exact (h1). Qed.
Lemma lem3562762 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term10 _91345 _91348 s f g) (h2 : term12 _91345 _91348 s f g) : term10 _91345 _91348 s f g.
Proof. exact (@lem3562760 _91345 _91348 s f g h1 (@lem3562761 _91345 _91348 s f g h2)). Qed.
Lemma lem3562763 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term12 _91345 _91348 s f g) : term12 _91345 _91348 s f g.
Proof. exact (fun h0 : term10 _91345 _91348 s f g => @lem3562762 _91345 _91348 s f g h0 h1). Qed.
Lemma lem3562764 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : term14 _91345 _91348 s f g.
Proof. exact (fun h0 : term12 _91345 _91348 s f g => @lem3562763 _91345 _91348 s f g h0). Qed.
Lemma lem3562767 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : term12 _91345 _91348 s f g.
Proof. exact (@lem3562764 _91345 _91348 s f g (@lem3562756 _91345 _91348 s f g)). Qed.
Lemma lem3562768 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : term12 _91345 _91348 s f g.
Proof. exact (@lem3562767 _91345 _91348 s f g). Qed.
Lemma lem3562782 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3562783 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term10 _91345 _91348 s f g) = (term15 _91345 _91348 s f g).
Proof. exact (@lem3562782 (term11 _91345 _91348 s f g)). Qed.
Lemma lem3562785 (t : Prop) : (term16 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3562786 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term15 _91345 _91348 s f g) = ((term8 _91345 _91348 s g f) = (term9 _91345 _91348 s f g)).
Proof. exact (@lem3562785 ((term8 _91345 _91348 s g f) = (term9 _91345 _91348 s f g))). Qed.
Lemma lem3562787 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term10 _91345 _91348 s f g) = ((term8 _91345 _91348 s g f) = (term9 _91345 _91348 s f g)).
Proof. exact (TRANS (@lem3562783 _91345 _91348 s f g) (@lem3562786 _91345 _91348 s f g)). Qed.
Lemma lem3562806 {_91345 _91348 : Type'} (f : _91345 -> _91348) (g : _91348 -> _91345) : (term17 _91345 _91348 f g) = (term18 _91345 _91348 f g).
Proof. exact (fun_ext (fun s : _91345 -> Prop => @lem3562787 _91345 _91348 s f g)). Qed.
Lemma lem3562807 {_91345 : Type'} : (@all (_91345 -> Prop)) = (@all (_91345 -> Prop)).
Proof. exact (eq_refl (@all (_91345 -> Prop))). Qed.
Lemma lem3562808 {_91345 _91348 : Type'} (f : _91345 -> _91348) (g : _91348 -> _91345) : (term19 _91345 _91348 f g) = (term20 _91345 _91348 f g).
Proof. exact (MK_COMB (@lem3562807 _91345) (@lem3562806 _91345 _91348 f g)). Qed.
Lemma lem3562813 {_91345 _91348 : Type'} (g : _91348 -> _91345) : (term21 _91345 _91348 g) = (term22 _91345 _91348 g).
Proof. exact (fun_ext (fun f : _91345 -> _91348 => @lem3562808 _91345 _91348 f g)). Qed.
Lemma lem3562814 {_91345 _91348 : Type'} : (@all (_91345 -> _91348)) = (@all (_91345 -> _91348)).
Proof. exact (eq_refl (@all (_91345 -> _91348))). Qed.
Lemma lem3562815 {_91345 _91348 : Type'} (g : _91348 -> _91345) : (term23 _91345 _91348 g) = (term24 _91345 _91348 g).
Proof. exact (MK_COMB (@lem3562814 _91345 _91348) (@lem3562813 _91345 _91348 g)). Qed.
Lemma lem3562820 {_91345 _91348 : Type'} : (term25 _91345 _91348) = (term26 _91345 _91348).
Proof. exact (fun_ext (fun g : _91348 -> _91345 => @lem3562815 _91345 _91348 g)). Qed.
Lemma lem3562821 {_91345 _91348 : Type'} : (@all (_91348 -> _91345)) = (@all (_91348 -> _91345)).
Proof. exact (eq_refl (@all (_91348 -> _91345))). Qed.
Lemma lem3562830 {_91345 _91348 : Type'} : (term27 _91345 _91348) = (term28 _91345 _91348).
Proof. exact (MK_COMB (@lem3562821 _91345 _91348) (@lem3562820 _91345 _91348)). Qed.
Lemma lem3562839 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) : (term29 _91345 _91348 s f g y x) = (term29 _91345 _91348 s f g y x).
Proof. exact (eq_refl (term29 _91345 _91348 s f g y x)). Qed.
Lemma lem3562840 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : (term30 _91345 _91348 s f g y) = (term30 _91345 _91348 s f g y).
Proof. exact (fun_ext (fun x : _91345 => @lem3562839 _91345 _91348 s f g y x)). Qed.
Lemma lem3562841 {_91345 : Type'} : (@all _91345) = (@all _91345).
Proof. exact (eq_refl (@all _91345)). Qed.
Lemma lem3562842 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : (term31 _91345 _91348 s f g y) = (term31 _91345 _91348 s f g y).
Proof. exact (MK_COMB (@lem3562841 _91345) (@lem3562840 _91345 _91348 s f g y)). Qed.
Lemma lem3562843 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term32 _91345 _91348 s f g) = (term32 _91345 _91348 s f g).
Proof. exact (fun_ext (fun y : _91348 => @lem3562842 _91345 _91348 s f g y)). Qed.
Lemma lem3562844 {_91348 : Type'} : (@all _91348) = (@all _91348).
Proof. exact (eq_refl (@all _91348)). Qed.
Lemma lem3562845 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term9 _91345 _91348 s f g) = (term9 _91345 _91348 s f g).
Proof. exact (MK_COMB (@lem3562844 _91348) (@lem3562843 _91345 _91348 s f g)). Qed.
Lemma lem3562850 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) (x : _91345) : (term33 _91345 _91348 s g f x) = (term33 _91345 _91348 s g f x).
Proof. exact (eq_refl (term33 _91345 _91348 s g f x)). Qed.
Lemma lem3562851 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) : (term34 _91345 _91348 s g f) = (term34 _91345 _91348 s g f).
Proof. exact (fun_ext (fun x : _91345 => @lem3562850 _91345 _91348 s g f x)). Qed.
Lemma lem3562852 {_91345 : Type'} : (@all _91345) = (@all _91345).
Proof. exact (eq_refl (@all _91345)). Qed.
Lemma lem3562853 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) : (term8 _91345 _91348 s g f) = (term8 _91345 _91348 s g f).
Proof. exact (MK_COMB (@lem3562852 _91345) (@lem3562851 _91345 _91348 s g f)). Qed.
Lemma lem3562854 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3562855 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) : (term35 _91345 _91348 s g f) = (term35 _91345 _91348 s g f).
Proof. exact (MK_COMB (@lem3562854) (@lem3562853 _91345 _91348 s g f)). Qed.
Lemma lem3562856 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : ((term8 _91345 _91348 s g f) = (term9 _91345 _91348 s f g)) = ((term8 _91345 _91348 s g f) = (term9 _91345 _91348 s f g)).
Proof. exact (MK_COMB (@lem3562855 _91345 _91348 s g f) (@lem3562845 _91345 _91348 s f g)). Qed.
Lemma lem3562857 {_91345 _91348 : Type'} (f : _91345 -> _91348) (g : _91348 -> _91345) : (term18 _91345 _91348 f g) = (term18 _91345 _91348 f g).
Proof. exact (fun_ext (fun s : _91345 -> Prop => @lem3562856 _91345 _91348 s f g)). Qed.
Lemma lem3562858 {_91345 : Type'} : (@all (_91345 -> Prop)) = (@all (_91345 -> Prop)).
Proof. exact (eq_refl (@all (_91345 -> Prop))). Qed.
Lemma lem3562859 {_91345 _91348 : Type'} (f : _91345 -> _91348) (g : _91348 -> _91345) : (term20 _91345 _91348 f g) = (term20 _91345 _91348 f g).
Proof. exact (MK_COMB (@lem3562858 _91345) (@lem3562857 _91345 _91348 f g)). Qed.
Lemma lem3562860 {_91345 _91348 : Type'} (g : _91348 -> _91345) : (term22 _91345 _91348 g) = (term22 _91345 _91348 g).
Proof. exact (fun_ext (fun f : _91345 -> _91348 => @lem3562859 _91345 _91348 f g)). Qed.
Lemma lem3562861 {_91345 _91348 : Type'} : (@all (_91345 -> _91348)) = (@all (_91345 -> _91348)).
Proof. exact (eq_refl (@all (_91345 -> _91348))). Qed.
Lemma lem3562862 {_91345 _91348 : Type'} (g : _91348 -> _91345) : (term24 _91345 _91348 g) = (term24 _91345 _91348 g).
Proof. exact (MK_COMB (@lem3562861 _91345 _91348) (@lem3562860 _91345 _91348 g)). Qed.
Lemma lem3562863 {_91345 _91348 : Type'} : (term26 _91345 _91348) = (term26 _91345 _91348).
Proof. exact (fun_ext (fun g : _91348 -> _91345 => @lem3562862 _91345 _91348 g)). Qed.
Lemma lem3562864 {_91345 _91348 : Type'} : (@all (_91348 -> _91345)) = (@all (_91348 -> _91345)).
Proof. exact (eq_refl (@all (_91348 -> _91345))). Qed.
Lemma lem3562865 {_91345 _91348 : Type'} : (term28 _91345 _91348) = (term28 _91345 _91348).
Proof. exact (MK_COMB (@lem3562864 _91345 _91348) (@lem3562863 _91345 _91348)). Qed.
Lemma lem3562910 {_91345 _91348 : Type'} : (term27 _91345 _91348) = (term28 _91345 _91348).
Proof. exact (TRANS (@lem3562830 _91345 _91348) (@lem3562865 _91345 _91348)). Qed.
Lemma lem3562911 {_91345 _91348 : Type'} : (term28 _91345 _91348) = (term27 _91345 _91348).
Proof. exact (SYM (@lem3562910 _91345 _91348)). Qed.
Lemma lem3562913 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3562914 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : ((term8 _91345 _91348 s g f) = (term9 _91345 _91348 s f g)) = (term10 _91345 _91348 s f g).
Proof. exact (@lem3562913 ((term8 _91345 _91348 s g f) = (term9 _91345 _91348 s f g))). Qed.
Lemma lem3562915 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term10 _91345 _91348 s f g) = ((term8 _91345 _91348 s g f) = (term9 _91345 _91348 s f g)).
Proof. exact (SYM (@lem3562914 _91345 _91348 s f g)). Qed.
Lemma lem3562916 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term11 _91345 _91348 s f g) : term11 _91345 _91348 s f g.
Proof. exact (h1). Qed.
Lemma lem3562925 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) (x : _91345) : (term36 _91345 _91348 s g f x) = (term37 _91345 _91348 s g f x).
Proof. exact (@lem17362 (@IN _91345 x s) ((term38 _91345 _91348 g f x) = x)). Qed.
Lemma lem3562930 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) (x : _91345) : (term33 _91345 _91348 s g f x) = (term39 _91345 _91348 s g f x).
Proof. exact (@lem17265 (@IN _91345 x s) ((term38 _91345 _91348 g f x) = x)). Qed.
Lemma lem3562931 {_91345 : Type'} (P : _91345 -> Prop) : (term40 _91345 P) = (term41 _91345 P).
Proof. exact (@lem18392 _91345 P). Qed.
Lemma lem3562932 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) : (term42 _91345 _91348 s g f) = (term43 _91345 _91348 s g f).
Proof. exact (@lem3562931 _91345 (term34 _91345 _91348 s g f)). Qed.
Lemma lem3562933 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) (x : _91345) : (term44 _91345 _91348 s g f x) = (term33 _91345 _91348 s g f x).
Proof. exact (eq_refl (term44 _91345 _91348 s g f x)). Qed.
Lemma lem3562934 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3562935 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) (x : _91345) : (term45 _91345 _91348 s g f x) = (term36 _91345 _91348 s g f x).
Proof. exact (MK_COMB (@lem3562934) (@lem3562933 _91345 _91348 s g f x)). Qed.
Lemma lem3562936 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) (x : _91345) : (term45 _91345 _91348 s g f x) = (term37 _91345 _91348 s g f x).
Proof. exact (TRANS (@lem3562935 _91345 _91348 s g f x) (@lem3562925 _91345 _91348 s g f x)). Qed.
Lemma lem3562937 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) : (term46 _91345 _91348 s g f) = (term47 _91345 _91348 s g f).
Proof. exact (fun_ext (fun x : _91345 => @lem3562936 _91345 _91348 s g f x)). Qed.
Lemma lem3562938 {_91345 : Type'} : (@ex _91345) = (@ex _91345).
Proof. exact (eq_refl (@ex _91345)). Qed.
Lemma lem3562939 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) : (term43 _91345 _91348 s g f) = (term48 _91345 _91348 s g f).
Proof. exact (MK_COMB (@lem3562938 _91345) (@lem3562937 _91345 _91348 s g f)). Qed.
Lemma lem3562940 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) : (term42 _91345 _91348 s g f) = (term48 _91345 _91348 s g f).
Proof. exact (TRANS (@lem3562932 _91345 _91348 s g f) (@lem3562939 _91345 _91348 s g f)). Qed.
Lemma lem3562941 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) : (term34 _91345 _91348 s g f) = (term49 _91345 _91348 s g f).
Proof. exact (fun_ext (fun x : _91345 => @lem3562930 _91345 _91348 s g f x)). Qed.
Lemma lem3562942 {_91345 : Type'} : (@all _91345) = (@all _91345).
Proof. exact (eq_refl (@all _91345)). Qed.
Lemma lem3562943 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) : (term8 _91345 _91348 s g f) = (term50 _91345 _91348 s g f).
Proof. exact (MK_COMB (@lem3562942 _91345) (@lem3562941 _91345 _91348 s g f)). Qed.
Lemma lem3562952 {_91345 _91348 : Type'} (s : _91345 -> Prop) (y : _91348) (f : _91345 -> _91348) (x : _91345) : (term51 _91345 _91348 s y f x) = (term52 _91345 _91348 s y f x).
Proof. exact (@lem17045 (@IN _91345 x s) (y = (f x))). Qed.
Lemma lem3562957 {_91345 _91348 : Type'} (g : _91348 -> _91345) (y : _91348) (x : _91345) : ((g y) = x) = ((g y) = x).
Proof. exact (eq_refl ((g y) = x)). Qed.
Lemma lem3562962 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) : (term53 _91345 _91348 s f g y x) = (term54 _91345 _91348 s f g y x).
Proof. exact (@lem17362 (term55 _91345 _91348 s y f x) ((g y) = x)). Qed.
Lemma lem3562963 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3562964 {_91345 _91348 : Type'} (s : _91345 -> Prop) (y : _91348) (f : _91345 -> _91348) (x : _91345) : (term56 _91345 _91348 s y f x) = (term57 _91345 _91348 s y f x).
Proof. exact (MK_COMB (@lem3562963) (@lem3562952 _91345 _91348 s y f x)). Qed.
Lemma lem3562965 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) : (term58 _91345 _91348 s f g y x) = (term59 _91345 _91348 s f g y x).
Proof. exact (MK_COMB (@lem3562964 _91345 _91348 s y f x) (@lem3562957 _91345 _91348 g y x)). Qed.
Lemma lem3562966 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) : (term29 _91345 _91348 s f g y x) = (term58 _91345 _91348 s f g y x).
Proof. exact (@lem17265 (term55 _91345 _91348 s y f x) ((g y) = x)). Qed.
Lemma lem3562967 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) : (term29 _91345 _91348 s f g y x) = (term59 _91345 _91348 s f g y x).
Proof. exact (TRANS (@lem3562966 _91345 _91348 s f g y x) (@lem3562965 _91345 _91348 s f g y x)). Qed.
Lemma lem3562968 {_91345 : Type'} (P : _91345 -> Prop) : (term40 _91345 P) = (term41 _91345 P).
Proof. exact (@lem18392 _91345 P). Qed.
Lemma lem3562969 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : (term60 _91345 _91348 s f g y) = (term61 _91345 _91348 s f g y).
Proof. exact (@lem3562968 _91345 (term30 _91345 _91348 s f g y)). Qed.
Lemma lem3562970 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) : (term62 _91345 _91348 s f g y x) = (term29 _91345 _91348 s f g y x).
Proof. exact (eq_refl (term62 _91345 _91348 s f g y x)). Qed.
Lemma lem3562971 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3562972 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) : (term63 _91345 _91348 s f g y x) = (term53 _91345 _91348 s f g y x).
Proof. exact (MK_COMB (@lem3562971) (@lem3562970 _91345 _91348 s f g y x)). Qed.
Lemma lem3562973 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) : (term63 _91345 _91348 s f g y x) = (term54 _91345 _91348 s f g y x).
Proof. exact (TRANS (@lem3562972 _91345 _91348 s f g y x) (@lem3562962 _91345 _91348 s f g y x)). Qed.
Lemma lem3562974 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : (term64 _91345 _91348 s f g y) = (term65 _91345 _91348 s f g y).
Proof. exact (fun_ext (fun x : _91345 => @lem3562973 _91345 _91348 s f g y x)). Qed.
Lemma lem3562975 {_91345 : Type'} : (@ex _91345) = (@ex _91345).
Proof. exact (eq_refl (@ex _91345)). Qed.
Lemma lem3562976 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : (term61 _91345 _91348 s f g y) = (term66 _91345 _91348 s f g y).
Proof. exact (MK_COMB (@lem3562975 _91345) (@lem3562974 _91345 _91348 s f g y)). Qed.
Lemma lem3562977 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : (term60 _91345 _91348 s f g y) = (term66 _91345 _91348 s f g y).
Proof. exact (TRANS (@lem3562969 _91345 _91348 s f g y) (@lem3562976 _91345 _91348 s f g y)). Qed.
Lemma lem3562978 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : (term30 _91345 _91348 s f g y) = (term67 _91345 _91348 s f g y).
Proof. exact (fun_ext (fun x : _91345 => @lem3562967 _91345 _91348 s f g y x)). Qed.
Lemma lem3562979 {_91345 : Type'} : (@all _91345) = (@all _91345).
Proof. exact (eq_refl (@all _91345)). Qed.
Lemma lem3562980 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : (term31 _91345 _91348 s f g y) = (term68 _91345 _91348 s f g y).
Proof. exact (MK_COMB (@lem3562979 _91345) (@lem3562978 _91345 _91348 s f g y)). Qed.
Lemma lem3562981 {_91348 : Type'} (P : _91348 -> Prop) : (term40 _91348 P) = (term41 _91348 P).
Proof. exact (@lem18392 _91348 P). Qed.
Lemma lem3562982 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term69 _91345 _91348 s f g) = (term70 _91345 _91348 s f g).
Proof. exact (@lem3562981 _91348 (term32 _91345 _91348 s f g)). Qed.
Lemma lem3562983 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : (term71 _91345 _91348 s f g y) = (term31 _91345 _91348 s f g y).
Proof. exact (eq_refl (term71 _91345 _91348 s f g y)). Qed.
Lemma lem3562984 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3562985 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : (term72 _91345 _91348 s f g y) = (term60 _91345 _91348 s f g y).
Proof. exact (MK_COMB (@lem3562984) (@lem3562983 _91345 _91348 s f g y)). Qed.
Lemma lem3562986 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : (term72 _91345 _91348 s f g y) = (term66 _91345 _91348 s f g y).
Proof. exact (TRANS (@lem3562985 _91345 _91348 s f g y) (@lem3562977 _91345 _91348 s f g y)). Qed.
Lemma lem3562987 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term73 _91345 _91348 s f g) = (term74 _91345 _91348 s f g).
Proof. exact (fun_ext (fun y : _91348 => @lem3562986 _91345 _91348 s f g y)). Qed.
Lemma lem3562988 {_91348 : Type'} : (@ex _91348) = (@ex _91348).
Proof. exact (eq_refl (@ex _91348)). Qed.
Lemma lem3562989 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term70 _91345 _91348 s f g) = (term75 _91345 _91348 s f g).
Proof. exact (MK_COMB (@lem3562988 _91348) (@lem3562987 _91345 _91348 s f g)). Qed.
Lemma lem3562990 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term69 _91345 _91348 s f g) = (term75 _91345 _91348 s f g).
Proof. exact (TRANS (@lem3562982 _91345 _91348 s f g) (@lem3562989 _91345 _91348 s f g)). Qed.
Lemma lem3562991 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term32 _91345 _91348 s f g) = (term76 _91345 _91348 s f g).
Proof. exact (fun_ext (fun y : _91348 => @lem3562980 _91345 _91348 s f g y)). Qed.
Lemma lem3562992 {_91348 : Type'} : (@all _91348) = (@all _91348).
Proof. exact (eq_refl (@all _91348)). Qed.
Lemma lem3562993 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term9 _91345 _91348 s f g) = (term77 _91345 _91348 s f g).
Proof. exact (MK_COMB (@lem3562992 _91348) (@lem3562991 _91345 _91348 s f g)). Qed.
Lemma lem3562994 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3562995 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) : (term78 _91345 _91348 s g f) = (term79 _91345 _91348 s g f).
Proof. exact (MK_COMB (@lem3562994) (@lem3562940 _91345 _91348 s g f)). Qed.
Lemma lem3562996 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term80 _91345 _91348 s f g) = (term81 _91345 _91348 s f g).
Proof. exact (MK_COMB (@lem3562995 _91345 _91348 s g f) (@lem3562993 _91345 _91348 s f g)). Qed.
Lemma lem3562997 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3562998 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) : (term82 _91345 _91348 s g f) = (term83 _91345 _91348 s g f).
Proof. exact (MK_COMB (@lem3562997) (@lem3562943 _91345 _91348 s g f)). Qed.
Lemma lem3562999 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term84 _91345 _91348 s f g) = (term85 _91345 _91348 s f g).
Proof. exact (MK_COMB (@lem3562998 _91345 _91348 s g f) (@lem3562990 _91345 _91348 s f g)). Qed.
Lemma lem3563000 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3563001 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term86 _91345 _91348 s f g) = (term87 _91345 _91348 s f g).
Proof. exact (MK_COMB (@lem3563000) (@lem3562999 _91345 _91348 s f g)). Qed.
Lemma lem3563002 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term88 _91345 _91348 s f g) = (term89 _91345 _91348 s f g).
Proof. exact (MK_COMB (@lem3563001 _91345 _91348 s f g) (@lem3562996 _91345 _91348 s f g)). Qed.
Lemma lem3563003 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term11 _91345 _91348 s f g) = (term88 _91345 _91348 s f g).
Proof. exact (@lem17646 (term8 _91345 _91348 s g f) (term9 _91345 _91348 s f g)). Qed.
Lemma lem3563004 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term11 _91345 _91348 s f g) = (term89 _91345 _91348 s f g).
Proof. exact (TRANS (@lem3563003 _91345 _91348 s f g) (@lem3563002 _91345 _91348 s f g)). Qed.
Lemma lem3563207 {A : Type'} (P : Prop) (Q : A -> Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3563208 {_91348 : Type'} (P : Prop) (Q : _91348 -> Prop) : (term90 _91348 P Q) = (term91 _91348 P Q).
Proof. exact (@lem3563207 _91348 P Q). Qed.
Lemma lem3563209 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term92 _91345 _91348 s f g) = (term93 _91345 _91348 s f g).
Proof. exact (@lem3563208 _91348 (term50 _91345 _91348 s g f) (term74 _91345 _91348 s f g)). Qed.
Lemma lem3563210 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : (term94 _91345 _91348 s f g y) = (term66 _91345 _91348 s f g y).
Proof. exact (eq_refl (term94 _91345 _91348 s f g y)). Qed.
Lemma lem3563211 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term95 _91345 _91348 s f g) = (term74 _91345 _91348 s f g).
Proof. exact (fun_ext (fun y : _91348 => @lem3563210 _91345 _91348 s f g y)). Qed.
Lemma lem3563212 {_91348 : Type'} : (@ex _91348) = (@ex _91348).
Proof. exact (eq_refl (@ex _91348)). Qed.
Lemma lem3563213 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term96 _91345 _91348 s f g) = (term75 _91345 _91348 s f g).
Proof. exact (MK_COMB (@lem3563212 _91348) (@lem3563211 _91345 _91348 s f g)). Qed.
Lemma lem3563214 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) : (term83 _91345 _91348 s g f) = (term83 _91345 _91348 s g f).
Proof. exact (eq_refl (term83 _91345 _91348 s g f)). Qed.
Lemma lem3563215 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term92 _91345 _91348 s f g) = (term85 _91345 _91348 s f g).
Proof. exact (MK_COMB (@lem3563214 _91345 _91348 s g f) (@lem3563213 _91345 _91348 s f g)). Qed.
Lemma lem3563216 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3563217 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term97 _91345 _91348 s f g) = (term98 _91345 _91348 s f g).
Proof. exact (MK_COMB (@lem3563216) (@lem3563215 _91345 _91348 s f g)). Qed.
Lemma lem3563218 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : (term94 _91345 _91348 s f g y) = (term66 _91345 _91348 s f g y).
Proof. exact (eq_refl (term94 _91345 _91348 s f g y)). Qed.
Lemma lem3563219 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) : (term83 _91345 _91348 s g f) = (term83 _91345 _91348 s g f).
Proof. exact (eq_refl (term83 _91345 _91348 s g f)). Qed.
Lemma lem3563220 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : (term99 _91345 _91348 s f g y) = (term100 _91345 _91348 s f g y).
Proof. exact (MK_COMB (@lem3563219 _91345 _91348 s g f) (@lem3563218 _91345 _91348 s f g y)). Qed.
Lemma lem3563221 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term101 _91345 _91348 s f g) = (term102 _91345 _91348 s f g).
Proof. exact (fun_ext (fun y : _91348 => @lem3563220 _91345 _91348 s f g y)). Qed.
Lemma lem3563222 {_91348 : Type'} : (@ex _91348) = (@ex _91348).
Proof. exact (eq_refl (@ex _91348)). Qed.
Lemma lem3563223 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term93 _91345 _91348 s f g) = (term103 _91345 _91348 s f g).
Proof. exact (MK_COMB (@lem3563222 _91348) (@lem3563221 _91345 _91348 s f g)). Qed.
Lemma lem3563224 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : ((term92 _91345 _91348 s f g) = (term93 _91345 _91348 s f g)) = ((term85 _91345 _91348 s f g) = (term103 _91345 _91348 s f g)).
Proof. exact (MK_COMB (@lem3563217 _91345 _91348 s f g) (@lem3563223 _91345 _91348 s f g)). Qed.
Lemma lem3563225 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term85 _91345 _91348 s f g) = (term103 _91345 _91348 s f g).
Proof. exact (EQ_MP (@lem3563224 _91345 _91348 s f g) (@lem3563209 _91345 _91348 s f g)). Qed.
Lemma lem3563227 {A : Type'} (P : Prop) (Q : A -> Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3563228 {_91345 : Type'} (P : Prop) (Q : _91345 -> Prop) : (term90 _91345 P Q) = (term91 _91345 P Q).
Proof. exact (@lem3563227 _91345 P Q). Qed.
Lemma lem3563229 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : (term104 _91345 _91348 s f g y) = (term105 _91345 _91348 s f g y).
Proof. exact (@lem3563228 _91345 (term50 _91345 _91348 s g f) (term65 _91345 _91348 s f g y)). Qed.
Lemma lem3563230 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) : (term106 _91345 _91348 s f g y x) = (term54 _91345 _91348 s f g y x).
Proof. exact (eq_refl (term106 _91345 _91348 s f g y x)). Qed.
Lemma lem3563231 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : (term107 _91345 _91348 s f g y) = (term65 _91345 _91348 s f g y).
Proof. exact (fun_ext (fun x : _91345 => @lem3563230 _91345 _91348 s f g y x)). Qed.
Lemma lem3563232 {_91345 : Type'} : (@ex _91345) = (@ex _91345).
Proof. exact (eq_refl (@ex _91345)). Qed.
Lemma lem3563233 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : (term108 _91345 _91348 s f g y) = (term66 _91345 _91348 s f g y).
Proof. exact (MK_COMB (@lem3563232 _91345) (@lem3563231 _91345 _91348 s f g y)). Qed.
Lemma lem3563234 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) : (term83 _91345 _91348 s g f) = (term83 _91345 _91348 s g f).
Proof. exact (eq_refl (term83 _91345 _91348 s g f)). Qed.
Lemma lem3563235 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : (term104 _91345 _91348 s f g y) = (term100 _91345 _91348 s f g y).
Proof. exact (MK_COMB (@lem3563234 _91345 _91348 s g f) (@lem3563233 _91345 _91348 s f g y)). Qed.
Lemma lem3563236 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3563237 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : (term109 _91345 _91348 s f g y) = (term110 _91345 _91348 s f g y).
Proof. exact (MK_COMB (@lem3563236) (@lem3563235 _91345 _91348 s f g y)). Qed.
Lemma lem3563238 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) : (term106 _91345 _91348 s f g y x) = (term54 _91345 _91348 s f g y x).
Proof. exact (eq_refl (term106 _91345 _91348 s f g y x)). Qed.
Lemma lem3563239 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) : (term83 _91345 _91348 s g f) = (term83 _91345 _91348 s g f).
Proof. exact (eq_refl (term83 _91345 _91348 s g f)). Qed.
Lemma lem3563240 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) : (term111 _91345 _91348 s f g y x) = (term112 _91345 _91348 s f g y x).
Proof. exact (MK_COMB (@lem3563239 _91345 _91348 s g f) (@lem3563238 _91345 _91348 s f g y x)). Qed.
Lemma lem3563241 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : (term113 _91345 _91348 s f g y) = (term114 _91345 _91348 s f g y).
Proof. exact (fun_ext (fun x : _91345 => @lem3563240 _91345 _91348 s f g y x)). Qed.
Lemma lem3563242 {_91345 : Type'} : (@ex _91345) = (@ex _91345).
Proof. exact (eq_refl (@ex _91345)). Qed.
Lemma lem3563243 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : (term105 _91345 _91348 s f g y) = (term115 _91345 _91348 s f g y).
Proof. exact (MK_COMB (@lem3563242 _91345) (@lem3563241 _91345 _91348 s f g y)). Qed.
Lemma lem3563244 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : ((term104 _91345 _91348 s f g y) = (term105 _91345 _91348 s f g y)) = ((term100 _91345 _91348 s f g y) = (term115 _91345 _91348 s f g y)).
Proof. exact (MK_COMB (@lem3563237 _91345 _91348 s f g y) (@lem3563243 _91345 _91348 s f g y)). Qed.
Lemma lem3563245 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : (term100 _91345 _91348 s f g y) = (term115 _91345 _91348 s f g y).
Proof. exact (EQ_MP (@lem3563244 _91345 _91348 s f g y) (@lem3563229 _91345 _91348 s f g y)). Qed.
Lemma lem3563246 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term102 _91345 _91348 s f g) = (term116 _91345 _91348 s f g).
Proof. exact (fun_ext (fun y : _91348 => @lem3563245 _91345 _91348 s f g y)). Qed.
Lemma lem3563247 {_91348 : Type'} : (@ex _91348) = (@ex _91348).
Proof. exact (eq_refl (@ex _91348)). Qed.
Lemma lem3563248 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term103 _91345 _91348 s f g) = (term117 _91345 _91348 s f g).
Proof. exact (MK_COMB (@lem3563247 _91348) (@lem3563246 _91345 _91348 s f g)). Qed.
Lemma lem3563249 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term85 _91345 _91348 s f g) = (term117 _91345 _91348 s f g).
Proof. exact (TRANS (@lem3563225 _91345 _91348 s f g) (@lem3563248 _91345 _91348 s f g)). Qed.
Lemma lem3563250 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3563251 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term87 _91345 _91348 s f g) = (term118 _91345 _91348 s f g).
Proof. exact (MK_COMB (@lem3563250) (@lem3563249 _91345 _91348 s f g)). Qed.
Lemma lem3563253 {A : Type'} (P : A -> Prop) (Q : Prop) : (term119 A P Q) = (term120 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3563254 {_91345 : Type'} (P : _91345 -> Prop) (Q : Prop) : (term119 _91345 P Q) = (term120 _91345 P Q).
Proof. exact (@lem3563253 _91345 P Q). Qed.
Lemma lem3563255 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term121 _91345 _91348 s f g) = (term122 _91345 _91348 s f g).
Proof. exact (@lem3563254 _91345 (term47 _91345 _91348 s g f) (term77 _91345 _91348 s f g)). Qed.
Lemma lem3563256 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) (x : _91345) : (term123 _91345 _91348 s g f x) = (term37 _91345 _91348 s g f x).
Proof. exact (eq_refl (term123 _91345 _91348 s g f x)). Qed.
Lemma lem3563257 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) : (term124 _91345 _91348 s g f) = (term47 _91345 _91348 s g f).
Proof. exact (fun_ext (fun x : _91345 => @lem3563256 _91345 _91348 s g f x)). Qed.
Lemma lem3563258 {_91345 : Type'} : (@ex _91345) = (@ex _91345).
Proof. exact (eq_refl (@ex _91345)). Qed.
Lemma lem3563259 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) : (term125 _91345 _91348 s g f) = (term48 _91345 _91348 s g f).
Proof. exact (MK_COMB (@lem3563258 _91345) (@lem3563257 _91345 _91348 s g f)). Qed.
Lemma lem3563260 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3563261 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) : (term126 _91345 _91348 s g f) = (term79 _91345 _91348 s g f).
Proof. exact (MK_COMB (@lem3563260) (@lem3563259 _91345 _91348 s g f)). Qed.
Lemma lem3563262 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term77 _91345 _91348 s f g) = (term77 _91345 _91348 s f g).
Proof. exact (eq_refl (term77 _91345 _91348 s f g)). Qed.
Lemma lem3563263 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term121 _91345 _91348 s f g) = (term81 _91345 _91348 s f g).
Proof. exact (MK_COMB (@lem3563261 _91345 _91348 s g f) (@lem3563262 _91345 _91348 s f g)). Qed.
Lemma lem3563264 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3563265 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term127 _91345 _91348 s f g) = (term128 _91345 _91348 s f g).
Proof. exact (MK_COMB (@lem3563264) (@lem3563263 _91345 _91348 s f g)). Qed.
Lemma lem3563266 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) (x : _91345) : (term123 _91345 _91348 s g f x) = (term37 _91345 _91348 s g f x).
Proof. exact (eq_refl (term123 _91345 _91348 s g f x)). Qed.
Lemma lem3563267 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3563268 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) (x : _91345) : (term129 _91345 _91348 s g f x) = (term130 _91345 _91348 s g f x).
Proof. exact (MK_COMB (@lem3563267) (@lem3563266 _91345 _91348 s g f x)). Qed.
Lemma lem3563269 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term77 _91345 _91348 s f g) = (term77 _91345 _91348 s f g).
Proof. exact (eq_refl (term77 _91345 _91348 s f g)). Qed.
Lemma lem3563270 {_91345 _91348 : Type'} (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term131 _91345 _91348 x s f g) = (term132 _91345 _91348 x s f g).
Proof. exact (MK_COMB (@lem3563268 _91345 _91348 s g f x) (@lem3563269 _91345 _91348 s f g)). Qed.
Lemma lem3563271 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term133 _91345 _91348 s f g) = (term134 _91345 _91348 s f g).
Proof. exact (fun_ext (fun x : _91345 => @lem3563270 _91345 _91348 x s f g)). Qed.
Lemma lem3563272 {_91345 : Type'} : (@ex _91345) = (@ex _91345).
Proof. exact (eq_refl (@ex _91345)). Qed.
Lemma lem3563273 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term122 _91345 _91348 s f g) = (term135 _91345 _91348 s f g).
Proof. exact (MK_COMB (@lem3563272 _91345) (@lem3563271 _91345 _91348 s f g)). Qed.
Lemma lem3563274 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : ((term121 _91345 _91348 s f g) = (term122 _91345 _91348 s f g)) = ((term81 _91345 _91348 s f g) = (term135 _91345 _91348 s f g)).
Proof. exact (MK_COMB (@lem3563265 _91345 _91348 s f g) (@lem3563273 _91345 _91348 s f g)). Qed.
Lemma lem3563275 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term81 _91345 _91348 s f g) = (term135 _91345 _91348 s f g).
Proof. exact (EQ_MP (@lem3563274 _91345 _91348 s f g) (@lem3563255 _91345 _91348 s f g)). Qed.
Lemma lem3563276 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term89 _91345 _91348 s f g) = (term136 _91345 _91348 s f g).
Proof. exact (MK_COMB (@lem3563251 _91345 _91348 s f g) (@lem3563275 _91345 _91348 s f g)). Qed.
Lemma lem3563280 {A : Type'} (P : A -> Prop) (Q : Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3563281 {_91348 : Type'} (P : _91348 -> Prop) (Q : Prop) : (term137 _91348 P Q) = (term138 _91348 P Q).
Proof. exact (@lem3563280 _91348 P Q). Qed.
Lemma lem3563282 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term139 _91345 _91348 s f g) = (term140 _91345 _91348 s f g).
Proof. exact (@lem3563281 _91348 (term116 _91345 _91348 s f g) (term135 _91345 _91348 s f g)). Qed.
Lemma lem3563283 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : (term141 _91345 _91348 s f g y) = (term115 _91345 _91348 s f g y).
Proof. exact (eq_refl (term141 _91345 _91348 s f g y)). Qed.
Lemma lem3563284 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term142 _91345 _91348 s f g) = (term116 _91345 _91348 s f g).
Proof. exact (fun_ext (fun y : _91348 => @lem3563283 _91345 _91348 s f g y)). Qed.
Lemma lem3563285 {_91348 : Type'} : (@ex _91348) = (@ex _91348).
Proof. exact (eq_refl (@ex _91348)). Qed.
Lemma lem3563286 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term143 _91345 _91348 s f g) = (term117 _91345 _91348 s f g).
Proof. exact (MK_COMB (@lem3563285 _91348) (@lem3563284 _91345 _91348 s f g)). Qed.
Lemma lem3563287 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3563288 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term144 _91345 _91348 s f g) = (term118 _91345 _91348 s f g).
Proof. exact (MK_COMB (@lem3563287) (@lem3563286 _91345 _91348 s f g)). Qed.
Lemma lem3563289 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term135 _91345 _91348 s f g) = (term135 _91345 _91348 s f g).
Proof. exact (eq_refl (term135 _91345 _91348 s f g)). Qed.
Lemma lem3563290 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term139 _91345 _91348 s f g) = (term136 _91345 _91348 s f g).
Proof. exact (MK_COMB (@lem3563288 _91345 _91348 s f g) (@lem3563289 _91345 _91348 s f g)). Qed.
Lemma lem3563291 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3563292 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term145 _91345 _91348 s f g) = (term146 _91345 _91348 s f g).
Proof. exact (MK_COMB (@lem3563291) (@lem3563290 _91345 _91348 s f g)). Qed.
Lemma lem3563293 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : (term141 _91345 _91348 s f g y) = (term115 _91345 _91348 s f g y).
Proof. exact (eq_refl (term141 _91345 _91348 s f g y)). Qed.
Lemma lem3563294 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3563295 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : (term147 _91345 _91348 s f g y) = (term148 _91345 _91348 s f g y).
Proof. exact (MK_COMB (@lem3563294) (@lem3563293 _91345 _91348 s f g y)). Qed.
Lemma lem3563296 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term135 _91345 _91348 s f g) = (term135 _91345 _91348 s f g).
Proof. exact (eq_refl (term135 _91345 _91348 s f g)). Qed.
Lemma lem3563297 {_91345 _91348 : Type'} (y : _91348) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term149 _91345 _91348 y s f g) = (term150 _91345 _91348 y s f g).
Proof. exact (MK_COMB (@lem3563295 _91345 _91348 s f g y) (@lem3563296 _91345 _91348 s f g)). Qed.
Lemma lem3563298 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term151 _91345 _91348 s f g) = (term152 _91345 _91348 s f g).
Proof. exact (fun_ext (fun y : _91348 => @lem3563297 _91345 _91348 y s f g)). Qed.
Lemma lem3563299 {_91348 : Type'} : (@ex _91348) = (@ex _91348).
Proof. exact (eq_refl (@ex _91348)). Qed.
Lemma lem3563300 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term140 _91345 _91348 s f g) = (term153 _91345 _91348 s f g).
Proof. exact (MK_COMB (@lem3563299 _91348) (@lem3563298 _91345 _91348 s f g)). Qed.
Lemma lem3563301 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : ((term139 _91345 _91348 s f g) = (term140 _91345 _91348 s f g)) = ((term136 _91345 _91348 s f g) = (term153 _91345 _91348 s f g)).
Proof. exact (MK_COMB (@lem3563292 _91345 _91348 s f g) (@lem3563300 _91345 _91348 s f g)). Qed.
Lemma lem3563302 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term136 _91345 _91348 s f g) = (term153 _91345 _91348 s f g).
Proof. exact (EQ_MP (@lem3563301 _91345 _91348 s f g) (@lem3563282 _91345 _91348 s f g)). Qed.
Lemma lem3563304 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term154 A P Q) = (term155 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3563305 {_91345 : Type'} (P : _91345 -> Prop) (Q : _91345 -> Prop) : (term154 _91345 P Q) = (term155 _91345 P Q).
Proof. exact (@lem3563304 _91345 P Q). Qed.
Lemma lem3563306 {_91345 _91348 : Type'} (y : _91348) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term156 _91345 _91348 y s f g) = (term157 _91345 _91348 y s f g).
Proof. exact (@lem3563305 _91345 (term114 _91345 _91348 s f g y) (term134 _91345 _91348 s f g)). Qed.
Lemma lem3563307 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) : (term158 _91345 _91348 s f g y x) = (term112 _91345 _91348 s f g y x).
Proof. exact (eq_refl (term158 _91345 _91348 s f g y x)). Qed.
Lemma lem3563308 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : (term159 _91345 _91348 s f g y) = (term114 _91345 _91348 s f g y).
Proof. exact (fun_ext (fun x : _91345 => @lem3563307 _91345 _91348 s f g y x)). Qed.
Lemma lem3563309 {_91345 : Type'} : (@ex _91345) = (@ex _91345).
Proof. exact (eq_refl (@ex _91345)). Qed.
Lemma lem3563310 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : (term160 _91345 _91348 s f g y) = (term115 _91345 _91348 s f g y).
Proof. exact (MK_COMB (@lem3563309 _91345) (@lem3563308 _91345 _91348 s f g y)). Qed.
Lemma lem3563311 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3563312 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : (term161 _91345 _91348 s f g y) = (term148 _91345 _91348 s f g y).
Proof. exact (MK_COMB (@lem3563311) (@lem3563310 _91345 _91348 s f g y)). Qed.
Lemma lem3563313 {_91345 _91348 : Type'} (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term162 _91345 _91348 s f g x) = (term132 _91345 _91348 x s f g).
Proof. exact (eq_refl (term162 _91345 _91348 s f g x)). Qed.
Lemma lem3563314 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term163 _91345 _91348 s f g) = (term134 _91345 _91348 s f g).
Proof. exact (fun_ext (fun x : _91345 => @lem3563313 _91345 _91348 x s f g)). Qed.
Lemma lem3563315 {_91345 : Type'} : (@ex _91345) = (@ex _91345).
Proof. exact (eq_refl (@ex _91345)). Qed.
Lemma lem3563316 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term164 _91345 _91348 s f g) = (term135 _91345 _91348 s f g).
Proof. exact (MK_COMB (@lem3563315 _91345) (@lem3563314 _91345 _91348 s f g)). Qed.
Lemma lem3563317 {_91345 _91348 : Type'} (y : _91348) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term156 _91345 _91348 y s f g) = (term150 _91345 _91348 y s f g).
Proof. exact (MK_COMB (@lem3563312 _91345 _91348 s f g y) (@lem3563316 _91345 _91348 s f g)). Qed.
Lemma lem3563318 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3563319 {_91345 _91348 : Type'} (y : _91348) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term165 _91345 _91348 y s f g) = (term166 _91345 _91348 y s f g).
Proof. exact (MK_COMB (@lem3563318) (@lem3563317 _91345 _91348 y s f g)). Qed.
Lemma lem3563320 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) : (term158 _91345 _91348 s f g y x) = (term112 _91345 _91348 s f g y x).
Proof. exact (eq_refl (term158 _91345 _91348 s f g y x)). Qed.
Lemma lem3563321 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3563322 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) : (term167 _91345 _91348 s f g y x) = (term168 _91345 _91348 s f g y x).
Proof. exact (MK_COMB (@lem3563321) (@lem3563320 _91345 _91348 s f g y x)). Qed.
Lemma lem3563323 {_91345 _91348 : Type'} (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term162 _91345 _91348 s f g x) = (term132 _91345 _91348 x s f g).
Proof. exact (eq_refl (term162 _91345 _91348 s f g x)). Qed.
Lemma lem3563324 {_91345 _91348 : Type'} (y : _91348) (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term169 _91345 _91348 y s f g x) = (term170 _91345 _91348 y x s f g).
Proof. exact (MK_COMB (@lem3563322 _91345 _91348 s f g y x) (@lem3563323 _91345 _91348 x s f g)). Qed.
Lemma lem3563325 {_91345 _91348 : Type'} (y : _91348) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term171 _91345 _91348 y s f g) = (term172 _91345 _91348 y s f g).
Proof. exact (fun_ext (fun x : _91345 => @lem3563324 _91345 _91348 y x s f g)). Qed.
Lemma lem3563326 {_91345 : Type'} : (@ex _91345) = (@ex _91345).
Proof. exact (eq_refl (@ex _91345)). Qed.
Lemma lem3563327 {_91345 _91348 : Type'} (y : _91348) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term157 _91345 _91348 y s f g) = (term173 _91345 _91348 y s f g).
Proof. exact (MK_COMB (@lem3563326 _91345) (@lem3563325 _91345 _91348 y s f g)). Qed.
Lemma lem3563328 {_91345 _91348 : Type'} (y : _91348) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : ((term156 _91345 _91348 y s f g) = (term157 _91345 _91348 y s f g)) = ((term150 _91345 _91348 y s f g) = (term173 _91345 _91348 y s f g)).
Proof. exact (MK_COMB (@lem3563319 _91345 _91348 y s f g) (@lem3563327 _91345 _91348 y s f g)). Qed.
Lemma lem3563329 {_91345 _91348 : Type'} (y : _91348) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term150 _91345 _91348 y s f g) = (term173 _91345 _91348 y s f g).
Proof. exact (EQ_MP (@lem3563328 _91345 _91348 y s f g) (@lem3563306 _91345 _91348 y s f g)). Qed.
Lemma lem3563330 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term152 _91345 _91348 s f g) = (term174 _91345 _91348 s f g).
Proof. exact (fun_ext (fun y : _91348 => @lem3563329 _91345 _91348 y s f g)). Qed.
Lemma lem3563331 {_91348 : Type'} : (@ex _91348) = (@ex _91348).
Proof. exact (eq_refl (@ex _91348)). Qed.
Lemma lem3563332 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term153 _91345 _91348 s f g) = (term175 _91345 _91348 s f g).
Proof. exact (MK_COMB (@lem3563331 _91348) (@lem3563330 _91345 _91348 s f g)). Qed.
Lemma lem3563333 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term136 _91345 _91348 s f g) = (term175 _91345 _91348 s f g).
Proof. exact (TRANS (@lem3563302 _91345 _91348 s f g) (@lem3563332 _91345 _91348 s f g)). Qed.
Lemma lem3563335 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term89 _91345 _91348 s f g) = (term175 _91345 _91348 s f g).
Proof. exact (TRANS (@lem3563276 _91345 _91348 s f g) (@lem3563333 _91345 _91348 s f g)). Qed.
Lemma lem3563336 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term11 _91345 _91348 s f g) = (term175 _91345 _91348 s f g).
Proof. exact (TRANS (@lem3563004 _91345 _91348 s f g) (@lem3563335 _91345 _91348 s f g)). Qed.
Lemma lem3563337 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term11 _91345 _91348 s f g) : term175 _91345 _91348 s f g.
Proof. exact (EQ_MP (@lem3563336 _91345 _91348 s f g) (@lem3562916 _91345 _91348 s f g h1)). Qed.
Lemma lem3563338 {_91345 _91348 : Type'} (y : _91348) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term173 _91345 _91348 y s f g) : term173 _91345 _91348 y s f g.
Proof. exact (h1). Qed.
Lemma lem3563339 {_91345 _91348 : Type'} (y : _91348) (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term170 _91345 _91348 y x s f g) : term170 _91345 _91348 y x s f g.
Proof. exact (h1). Qed.
Lemma lem3563368 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) : (term59 _91345 _91348 s f g y x) = (term59 _91345 _91348 s f g y x).
Proof. exact (eq_refl (term59 _91345 _91348 s f g y x)). Qed.
Lemma lem3563369 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : (term67 _91345 _91348 s f g y) = (term67 _91345 _91348 s f g y).
Proof. exact (fun_ext (fun x : _91345 => @lem3563368 _91345 _91348 s f g y x)). Qed.
Lemma lem3563370 {_91345 : Type'} : (@all _91345) = (@all _91345).
Proof. exact (eq_refl (@all _91345)). Qed.
Lemma lem3563371 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : (term68 _91345 _91348 s f g y) = (term68 _91345 _91348 s f g y).
Proof. exact (MK_COMB (@lem3563370 _91345) (@lem3563369 _91345 _91348 s f g y)). Qed.
Lemma lem3563372 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term76 _91345 _91348 s f g) = (term76 _91345 _91348 s f g).
Proof. exact (fun_ext (fun y : _91348 => @lem3563371 _91345 _91348 s f g y)). Qed.
Lemma lem3563373 {_91348 : Type'} : (@all _91348) = (@all _91348).
Proof. exact (eq_refl (@all _91348)). Qed.
Lemma lem3563374 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term77 _91345 _91348 s f g) = (term77 _91345 _91348 s f g).
Proof. exact (MK_COMB (@lem3563373 _91348) (@lem3563372 _91345 _91348 s f g)). Qed.
Lemma lem3563395 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) (x : _91345) : (term130 _91345 _91348 s g f x) = (term130 _91345 _91348 s g f x).
Proof. exact (eq_refl (term130 _91345 _91348 s g f x)). Qed.
Lemma lem3563396 {_91345 _91348 : Type'} (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term132 _91345 _91348 x s f g) = (term132 _91345 _91348 x s f g).
Proof. exact (MK_COMB (@lem3563395 _91345 _91348 s g f x) (@lem3563374 _91345 _91348 s f g)). Qed.
Lemma lem3563423 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) : (term54 _91345 _91348 s f g y x) = (term54 _91345 _91348 s f g y x).
Proof. exact (eq_refl (term54 _91345 _91348 s f g y x)). Qed.
Lemma lem3563442 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) (x : _91345) : (term39 _91345 _91348 s g f x) = (term39 _91345 _91348 s g f x).
Proof. exact (eq_refl (term39 _91345 _91348 s g f x)). Qed.
Lemma lem3563443 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) : (term49 _91345 _91348 s g f) = (term49 _91345 _91348 s g f).
Proof. exact (fun_ext (fun x : _91345 => @lem3563442 _91345 _91348 s g f x)). Qed.
Lemma lem3563444 {_91345 : Type'} : (@all _91345) = (@all _91345).
Proof. exact (eq_refl (@all _91345)). Qed.
Lemma lem3563445 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) : (term50 _91345 _91348 s g f) = (term50 _91345 _91348 s g f).
Proof. exact (MK_COMB (@lem3563444 _91345) (@lem3563443 _91345 _91348 s g f)). Qed.
Lemma lem3563446 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3563447 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) : (term83 _91345 _91348 s g f) = (term83 _91345 _91348 s g f).
Proof. exact (MK_COMB (@lem3563446) (@lem3563445 _91345 _91348 s g f)). Qed.
Lemma lem3563448 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) : (term112 _91345 _91348 s f g y x) = (term112 _91345 _91348 s f g y x).
Proof. exact (MK_COMB (@lem3563447 _91345 _91348 s g f) (@lem3563423 _91345 _91348 s f g y x)). Qed.
Lemma lem3563449 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3563450 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) : (term168 _91345 _91348 s f g y x) = (term168 _91345 _91348 s f g y x).
Proof. exact (MK_COMB (@lem3563449) (@lem3563448 _91345 _91348 s f g y x)). Qed.
Lemma lem3563451 {_91345 _91348 : Type'} (y : _91348) (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term170 _91345 _91348 y x s f g) = (term170 _91345 _91348 y x s f g).
Proof. exact (MK_COMB (@lem3563450 _91345 _91348 s f g y x) (@lem3563396 _91345 _91348 x s f g)). Qed.
Lemma lem3563452 {_91345 _91348 : Type'} (y : _91348) (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term170 _91345 _91348 y x s f g) : term170 _91345 _91348 y x s f g.
Proof. exact (EQ_MP (@lem3563451 _91345 _91348 y x s f g) (@lem3563339 _91345 _91348 y x s f g h1)). Qed.
Lemma lem3563453 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) (h1 : term112 _91345 _91348 s f g y x) : term112 _91345 _91348 s f g y x.
Proof. exact (h1). Qed.
Lemma lem3563454 {_91345 _91348 : Type'} (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term132 _91345 _91348 x s f g) : term132 _91345 _91348 x s f g.
Proof. exact (h1). Qed.
Lemma lem3563455 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) (h1 : term112 _91345 _91348 s f g y x) : term54 _91345 _91348 s f g y x.
Proof. exact (proj2 (@lem3563453 _91345 _91348 s f g y x h1)). Qed.
Lemma lem3563456 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) (h1 : term112 _91345 _91348 s f g y x) : term50 _91345 _91348 s g f.
Proof. exact (proj1 (@lem3563453 _91345 _91348 s f g y x h1)). Qed.
Lemma lem3563458 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) (h1 : term112 _91345 _91348 s f g y x) : term55 _91345 _91348 s y f x.
Proof. exact (proj1 (@lem3563455 _91345 _91348 s f g y x h1)). Qed.
Lemma lem3563461 {_91345 _91348 : Type'} (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term132 _91345 _91348 x s f g) : term77 _91345 _91348 s f g.
Proof. exact (proj2 (@lem3563454 _91345 _91348 x s f g h1)). Qed.
Lemma lem3563462 {_91345 _91348 : Type'} (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term132 _91345 _91348 x s f g) : term37 _91345 _91348 s g f x.
Proof. exact (proj1 (@lem3563454 _91345 _91348 x s f g h1)). Qed.
Lemma lem3563472 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) (x : _91345) : (term39 _91345 _91348 s g f x) = (term39 _91345 _91348 s g f x).
Proof. exact (eq_refl (term39 _91345 _91348 s g f x)). Qed.
Lemma lem3563473 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) : (term49 _91345 _91348 s g f) = (term49 _91345 _91348 s g f).
Proof. exact (fun_ext (fun x : _91345 => @lem3563472 _91345 _91348 s g f x)). Qed.
Lemma lem3563474 {_91345 : Type'} : (@all _91345) = (@all _91345).
Proof. exact (eq_refl (@all _91345)). Qed.
Lemma lem3563476 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) : (term50 _91345 _91348 s g f) = (term50 _91345 _91348 s g f).
Proof. exact (MK_COMB (@lem3563474 _91345) (@lem3563473 _91345 _91348 s g f)). Qed.
Lemma lem3563477 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) (h1 : term112 _91345 _91348 s f g y x) : term50 _91345 _91348 s g f.
Proof. exact (EQ_MP (@lem3563476 _91345 _91348 s g f) (@lem3563456 _91345 _91348 s f g y x h1)). Qed.
Lemma lem3563503 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) : (term59 _91345 _91348 s f g y x) = (term59 _91345 _91348 s f g y x).
Proof. exact (eq_refl (term59 _91345 _91348 s f g y x)). Qed.
Lemma lem3563504 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : (term67 _91345 _91348 s f g y) = (term67 _91345 _91348 s f g y).
Proof. exact (fun_ext (fun x : _91345 => @lem3563503 _91345 _91348 s f g y x)). Qed.
Lemma lem3563505 {_91345 : Type'} : (@all _91345) = (@all _91345).
Proof. exact (eq_refl (@all _91345)). Qed.
Lemma lem3563506 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) : (term68 _91345 _91348 s f g y) = (term68 _91345 _91348 s f g y).
Proof. exact (MK_COMB (@lem3563505 _91345) (@lem3563504 _91345 _91348 s f g y)). Qed.
Lemma lem3563507 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term76 _91345 _91348 s f g) = (term76 _91345 _91348 s f g).
Proof. exact (fun_ext (fun y : _91348 => @lem3563506 _91345 _91348 s f g y)). Qed.
Lemma lem3563508 {_91348 : Type'} : (@all _91348) = (@all _91348).
Proof. exact (eq_refl (@all _91348)). Qed.
Lemma lem3563510 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term77 _91345 _91348 s f g) = (term77 _91345 _91348 s f g).
Proof. exact (MK_COMB (@lem3563508 _91348) (@lem3563507 _91345 _91348 s f g)). Qed.
Lemma lem3563511 {_91345 _91348 : Type'} (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term132 _91345 _91348 x s f g) : term77 _91345 _91348 s f g.
Proof. exact (EQ_MP (@lem3563510 _91345 _91348 s f g) (@lem3563461 _91345 _91348 x s f g h1)). Qed.
Lemma lem3563520 {_91345 _91348 : Type'} (_38228 : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) (h1 : term112 _91345 _91348 s f g y x) : term176 _91345 _91348 s g f _38228.
Proof. exact (@lem3563477 _91345 _91348 s f g y x h1 _38228). Qed.
Lemma lem3563521 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) (_38228 : _91345) : (term176 _91345 _91348 s g f _38228) = (term39 _91345 _91348 s g f _38228).
Proof. exact (eq_refl (term176 _91345 _91348 s g f _38228)). Qed.
Lemma lem3563523 {_91345 _91348 : Type'} (_38229 : _91348) (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term132 _91345 _91348 x s f g) : term177 _91345 _91348 s f g _38229.
Proof. exact (@lem3563511 _91345 _91348 x s f g h1 _38229). Qed.
Lemma lem3563524 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (_38229 : _91348) : (term177 _91345 _91348 s f g _38229) = (term68 _91345 _91348 s f g _38229).
Proof. exact (eq_refl (term177 _91345 _91348 s f g _38229)). Qed.
Lemma lem3563525 {_91345 _91348 : Type'} (_38229 : _91348) (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term132 _91345 _91348 x s f g) : term68 _91345 _91348 s f g _38229.
Proof. exact (EQ_MP (@lem3563524 _91345 _91348 s f g _38229) (@lem3563523 _91345 _91348 _38229 x s f g h1)). Qed.
Lemma lem3563526 {_91345 _91348 : Type'} (_38229 : _91348) (_38230 : _91345) (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term132 _91345 _91348 x s f g) : term178 _91345 _91348 s f g _38229 _38230.
Proof. exact (@lem3563525 _91345 _91348 _38229 x s f g h1 _38230). Qed.
Lemma lem3563527 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (_38229 : _91348) (_38230 : _91345) : (term178 _91345 _91348 s f g _38229 _38230) = (term59 _91345 _91348 s f g _38229 _38230).
Proof. exact (eq_refl (term178 _91345 _91348 s f g _38229 _38230)). Qed.
Lemma lem3563528 {_91345 _91348 : Type'} (_38229 : _91348) (_38230 : _91345) (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term132 _91345 _91348 x s f g) : term59 _91345 _91348 s f g _38229 _38230.
Proof. exact (EQ_MP (@lem3563527 _91345 _91348 s f g _38229 _38230) (@lem3563526 _91345 _91348 _38229 _38230 x s f g h1)). Qed.
Lemma lem3563536 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) (h1 : term112 _91345 _91348 s f g y x) : term179 _91345 _91348 g y x.
Proof. exact (proj2 (@lem3563455 _91345 _91348 s f g y x h1)). Qed.
Lemma lem3563540 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) (h1 : term112 _91345 _91348 s f g y x) : y = (f x).
Proof. exact (proj2 (@lem3563458 _91345 _91348 s f g y x h1)). Qed.
Lemma lem3563551 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (_38229 : _91348) (_38230 : _91345) : (term59 _91345 _91348 s f g _38229 _38230) = (term180 _91345 _91348 s f g _38229 _38230).
Proof. exact (@lem3562747 (term181 _91345 _38230 s) (term182 _91345 _91348 _38229 f _38230) ((g _38229) = _38230)). Qed.
Lemma lem3563552 {_91345 _91348 : Type'} (_38229 : _91348) (_38230 : _91345) (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term132 _91345 _91348 x s f g) : term180 _91345 _91348 s f g _38229 _38230.
Proof. exact (EQ_MP (@lem3563551 _91345 _91348 s f g _38229 _38230) (@lem3563528 _91345 _91348 _38229 _38230 x s f g h1)). Qed.
Lemma lem3563556 {_91345 _91348 : Type'} (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term132 _91345 _91348 x s f g) : term183 _91345 _91348 g f x.
Proof. exact (proj2 (@lem3563462 _91345 _91348 x s f g h1)). Qed.
Lemma lem3563584 {_91345 _91348 : Type'} (_38228 : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) (h1 : term112 _91345 _91348 s f g y x) : term39 _91345 _91348 s g f _38228.
Proof. exact (EQ_MP (@lem3563521 _91345 _91348 s g f _38228) (@lem3563520 _91345 _91348 _38228 s f g y x h1)). Qed.
Lemma lem3563585 {_91345 _91348 : Type'} (g : _91348 -> _91345) (x : _91345) : (term184 _91345 _91348 g x) = (term184 _91345 _91348 g x).
Proof. exact (eq_refl (term184 _91345 _91348 g x)). Qed.
Lemma lem3563586 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) (h1 : term112 _91345 _91348 s f g y x) : (term185 _91345 _91348 g x y) = (term186 _91345 _91348 g f x).
Proof. exact (MK_COMB (@lem3563585 _91345 _91348 g x) (@lem3563540 _91345 _91348 s f g y x h1)). Qed.
Lemma lem3563587 {_91345 _91348 : Type'} (g : _91348 -> _91345) (f : _91345 -> _91348) (x : _91345) : (term186 _91345 _91348 g f x) = (term183 _91345 _91348 g f x).
Proof. exact (eq_refl (term186 _91345 _91348 g f x)). Qed.
Lemma lem3563588 {_91345 _91348 : Type'} (g : _91348 -> _91345) (x : _91345) (y : _91348) : (term187 _91345 _91348 g x y) = (term187 _91345 _91348 g x y).
Proof. exact (eq_refl (term187 _91345 _91348 g x y)). Qed.
Lemma lem3563589 {_91345 _91348 : Type'} (y : _91348) (g : _91348 -> _91345) (f : _91345 -> _91348) (x : _91345) : ((term185 _91345 _91348 g x y) = (term186 _91345 _91348 g f x)) = ((term185 _91345 _91348 g x y) = (term183 _91345 _91348 g f x)).
Proof. exact (MK_COMB (@lem3563588 _91345 _91348 g x y) (@lem3563587 _91345 _91348 g f x)). Qed.
Lemma lem3563590 {_91345 _91348 : Type'} (g : _91348 -> _91345) (y : _91348) (x : _91345) : (term185 _91345 _91348 g x y) = (term179 _91345 _91348 g y x).
Proof. exact (eq_refl (term185 _91345 _91348 g x y)). Qed.
Lemma lem3563591 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3563592 {_91345 _91348 : Type'} (g : _91348 -> _91345) (y : _91348) (x : _91345) : (term187 _91345 _91348 g x y) = (term188 _91345 _91348 g y x).
Proof. exact (MK_COMB (@lem3563591) (@lem3563590 _91345 _91348 g y x)). Qed.
Lemma lem3563593 {_91345 _91348 : Type'} (g : _91348 -> _91345) (f : _91345 -> _91348) (x : _91345) : (term183 _91345 _91348 g f x) = (term183 _91345 _91348 g f x).
Proof. exact (eq_refl (term183 _91345 _91348 g f x)). Qed.
Lemma lem3563594 {_91345 _91348 : Type'} (y : _91348) (g : _91348 -> _91345) (f : _91345 -> _91348) (x : _91345) : ((term185 _91345 _91348 g x y) = (term183 _91345 _91348 g f x)) = ((term179 _91345 _91348 g y x) = (term183 _91345 _91348 g f x)).
Proof. exact (MK_COMB (@lem3563592 _91345 _91348 g y x) (@lem3563593 _91345 _91348 g f x)). Qed.
Lemma lem3563595 {_91345 _91348 : Type'} (y : _91348) (g : _91348 -> _91345) (f : _91345 -> _91348) (x : _91345) : ((term185 _91345 _91348 g x y) = (term186 _91345 _91348 g f x)) = ((term179 _91345 _91348 g y x) = (term183 _91345 _91348 g f x)).
Proof. exact (TRANS (@lem3563589 _91345 _91348 y g f x) (@lem3563594 _91345 _91348 y g f x)). Qed.
Lemma lem3563596 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) (h1 : term112 _91345 _91348 s f g y x) : (term179 _91345 _91348 g y x) = (term183 _91345 _91348 g f x).
Proof. exact (EQ_MP (@lem3563595 _91345 _91348 y g f x) (@lem3563586 _91345 _91348 s f g y x h1)). Qed.
Lemma lem3563597 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) (h1 : term112 _91345 _91348 s f g y x) : term183 _91345 _91348 g f x.
Proof. exact (EQ_MP (@lem3563596 _91345 _91348 s f g y x h1) (@lem3563536 _91345 _91348 s f g y x h1)). Qed.
Lemma lem3563654 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) (h1 : term112 _91345 _91348 s f g y x) : @IN _91345 x s.
Proof. exact (proj1 (@lem3563458 _91345 _91348 s f g y x h1)). Qed.
Lemma lem3563655 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) (h1 : term112 _91345 _91348 s f g y x) : term189 _91345 x s.
Proof. exact (fun h0 : term181 _91345 x s => @lem3563654 _91345 _91348 s f g y x h1). Qed.
Lemma lem3563657 (p : Prop) : (term190 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3563658 {_91345 : Type'} (x : _91345) (s : _91345 -> Prop) : (term189 _91345 x s) = (@IN _91345 x s).
Proof. exact (@lem3563657 (@IN _91345 x s)). Qed.
Lemma lem3563659 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) (h1 : term112 _91345 _91348 s f g y x) : @IN _91345 x s.
Proof. exact (EQ_MP (@lem3563658 _91345 x s) (@lem3563655 _91345 _91348 s f g y x h1)). Qed.
Lemma lem3563665 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3563666 {_91345 _91348 : Type'} (g : _91348 -> _91345) (f : _91345 -> _91348) (_38228 : _91345) (s : _91345 -> Prop) : (term39 _91345 _91348 s g f _38228) = (term191 _91345 _91348 g f _38228 s).
Proof. exact (@lem3563665 ((term38 _91345 _91348 g f _38228) = _38228) (term181 _91345 _38228 s)). Qed.
Lemma lem3563674 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3563675 {_91345 _91348 : Type'} (g : _91348 -> _91345) (f : _91345 -> _91348) (_38228 : _91345) (s : _91345 -> Prop) : (term192 _91345 _91348 s g f _38228) = (term193 _91345 _91348 g f _38228 s).
Proof. exact (MK_COMB (@lem3563674) (@lem3563666 _91345 _91348 g f _38228 s)). Qed.
Lemma lem3563683 {_91345 _91348 : Type'} (g : _91348 -> _91345) (f : _91345 -> _91348) (_38228 : _91345) (s : _91345 -> Prop) : (term191 _91345 _91348 g f _38228 s) = (term191 _91345 _91348 g f _38228 s).
Proof. exact (eq_refl (term191 _91345 _91348 g f _38228 s)). Qed.
Lemma lem3563684 {_91345 _91348 : Type'} (g : _91348 -> _91345) (f : _91345 -> _91348) (_38228 : _91345) (s : _91345 -> Prop) : ((term39 _91345 _91348 s g f _38228) = (term191 _91345 _91348 g f _38228 s)) = ((term191 _91345 _91348 g f _38228 s) = (term191 _91345 _91348 g f _38228 s)).
Proof. exact (MK_COMB (@lem3563675 _91345 _91348 g f _38228 s) (@lem3563683 _91345 _91348 g f _38228 s)). Qed.
Lemma lem3563686 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3563687 (x : Prop) : (x = x) = True.
Proof. exact (@lem3563686 Prop x). Qed.
Lemma lem3563688 {_91345 _91348 : Type'} (g : _91348 -> _91345) (f : _91345 -> _91348) (_38228 : _91345) (s : _91345 -> Prop) : ((term191 _91345 _91348 g f _38228 s) = (term191 _91345 _91348 g f _38228 s)) = True.
Proof. exact (@lem3563687 (term191 _91345 _91348 g f _38228 s)). Qed.
Lemma lem3563689 {_91345 _91348 : Type'} (g : _91348 -> _91345) (f : _91345 -> _91348) (_38228 : _91345) (s : _91345 -> Prop) : ((term39 _91345 _91348 s g f _38228) = (term191 _91345 _91348 g f _38228 s)) = True.
Proof. exact (TRANS (@lem3563684 _91345 _91348 g f _38228 s) (@lem3563688 _91345 _91348 g f _38228 s)). Qed.
Lemma lem3563690 {_91345 _91348 : Type'} (g : _91348 -> _91345) (f : _91345 -> _91348) (_38228 : _91345) (s : _91345 -> Prop) : True = ((term39 _91345 _91348 s g f _38228) = (term191 _91345 _91348 g f _38228 s)).
Proof. exact (SYM (@lem3563689 _91345 _91348 g f _38228 s)). Qed.
Lemma lem3563691 {_91345 _91348 : Type'} (g : _91348 -> _91345) (f : _91345 -> _91348) (_38228 : _91345) (s : _91345 -> Prop) : (term39 _91345 _91348 s g f _38228) = (term191 _91345 _91348 g f _38228 s).
Proof. exact (EQ_MP (@lem3563690 _91345 _91348 g f _38228 s) (@lem0)). Qed.
Lemma lem3563692 {_91345 _91348 : Type'} (_38228 : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) (h1 : term112 _91345 _91348 s f g y x) : term191 _91345 _91348 g f _38228 s.
Proof. exact (EQ_MP (@lem3563691 _91345 _91348 g f _38228 s) (@lem3563584 _91345 _91348 _38228 s f g y x h1)). Qed.
Lemma lem3563694 (b : Prop) (a : Prop) : (a \/ b) = (term194 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3563695 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) (_38228 : _91345) : (term191 _91345 _91348 g f _38228 s) = (term195 _91345 _91348 s g f _38228).
Proof. exact (@lem3563694 (term181 _91345 _38228 s) ((term38 _91345 _91348 g f _38228) = _38228)). Qed.
Lemma lem3563697 (a : Prop) : (term16 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3563698 {_91345 : Type'} (_38228 : _91345) (s : _91345 -> Prop) : (term196 _91345 _38228 s) = (@IN _91345 _38228 s).
Proof. exact (@lem3563697 (@IN _91345 _38228 s)). Qed.
Lemma lem3563699 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3563700 {_91345 : Type'} (_38228 : _91345) (s : _91345 -> Prop) : (term197 _91345 _38228 s) = (term198 _91345 _38228 s).
Proof. exact (MK_COMB (@lem3563699) (@lem3563698 _91345 _38228 s)). Qed.
Lemma lem3563701 {_91345 _91348 : Type'} (g : _91348 -> _91345) (f : _91345 -> _91348) (_38228 : _91345) : ((term38 _91345 _91348 g f _38228) = _38228) = ((term38 _91345 _91348 g f _38228) = _38228).
Proof. exact (eq_refl ((term38 _91345 _91348 g f _38228) = _38228)). Qed.
Lemma lem3563702 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) (_38228 : _91345) : (term195 _91345 _91348 s g f _38228) = (term33 _91345 _91348 s g f _38228).
Proof. exact (MK_COMB (@lem3563700 _91345 _38228 s) (@lem3563701 _91345 _91348 g f _38228)). Qed.
Lemma lem3563703 {_91345 _91348 : Type'} (s : _91345 -> Prop) (g : _91348 -> _91345) (f : _91345 -> _91348) (_38228 : _91345) : (term191 _91345 _91348 g f _38228 s) = (term33 _91345 _91348 s g f _38228).
Proof. exact (TRANS (@lem3563695 _91345 _91348 s g f _38228) (@lem3563702 _91345 _91348 s g f _38228)). Qed.
Lemma lem3563706 {_91345 _91348 : Type'} (_38228 : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) (h1 : term112 _91345 _91348 s f g y x) : term33 _91345 _91348 s g f _38228.
Proof. exact (EQ_MP (@lem3563703 _91345 _91348 s g f _38228) (@lem3563692 _91345 _91348 _38228 s f g y x h1)). Qed.
Lemma lem3563707 {_91345 _91348 : Type'} (_38228 : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) (h1 : term112 _91345 _91348 s f g y x) : term33 _91345 _91348 s g f _38228.
Proof. exact (@lem3563706 _91345 _91348 _38228 s f g y x h1). Qed.
Lemma lem3563708 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) (h1 : term112 _91345 _91348 s f g y x) : term33 _91345 _91348 s g f x.
Proof. exact (@lem3563707 _91345 _91348 x s f g y x h1). Qed.
Lemma lem3563711 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) (h1 : term112 _91345 _91348 s f g y x) : (term38 _91345 _91348 g f x) = x.
Proof. exact (@lem3563708 _91345 _91348 s f g y x h1 (@lem3563659 _91345 _91348 s f g y x h1)). Qed.
Lemma lem3563712 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) (h1 : term112 _91345 _91348 s f g y x) : term199 _91345 _91348 g f x.
Proof. exact (fun h0 : term183 _91345 _91348 g f x => @lem3563711 _91345 _91348 s f g y x h1). Qed.
Lemma lem3563714 (p : Prop) : (term190 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3563715 {_91345 _91348 : Type'} (g : _91348 -> _91345) (f : _91345 -> _91348) (x : _91345) : (term199 _91345 _91348 g f x) = ((term38 _91345 _91348 g f x) = x).
Proof. exact (@lem3563714 ((term38 _91345 _91348 g f x) = x)). Qed.
Lemma lem3563716 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) (h1 : term112 _91345 _91348 s f g y x) : (term38 _91345 _91348 g f x) = x.
Proof. exact (EQ_MP (@lem3563715 _91345 _91348 g f x) (@lem3563712 _91345 _91348 s f g y x h1)). Qed.
Lemma lem3563719 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3563721 {_91345 _91348 : Type'} (g : _91348 -> _91345) (f : _91345 -> _91348) (x : _91345) : (term183 _91345 _91348 g f x) = (term200 _91345 _91348 g f x).
Proof. exact (@lem3563719 ((term38 _91345 _91348 g f x) = x)). Qed.
Lemma lem3563724 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) (h1 : term112 _91345 _91348 s f g y x) : term200 _91345 _91348 g f x.
Proof. exact (EQ_MP (@lem3563721 _91345 _91348 g f x) (@lem3563597 _91345 _91348 s f g y x h1)). Qed.
Lemma lem3563727 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) (h1 : term112 _91345 _91348 s f g y x) : False.
Proof. exact (@lem3563724 _91345 _91348 s f g y x h1 (@lem3563716 _91345 _91348 s f g y x h1)). Qed.
Lemma lem3563728 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) (h1 : term112 _91345 _91348 s f g y x) : term201.
Proof. exact (fun h0 : ~ False => @lem3563727 _91345 _91348 s f g y x h1). Qed.
Lemma lem3563730 (p : Prop) : (term190 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3563731 : term201 = False.
Proof. exact (@lem3563730 False). Qed.
Lemma lem3563775 {_91345 _91348 : Type'} (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term132 _91345 _91348 x s f g) : @IN _91345 x s.
Proof. exact (proj1 (@lem3563462 _91345 _91348 x s f g h1)). Qed.
Lemma lem3563776 {_91345 _91348 : Type'} (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term132 _91345 _91348 x s f g) : term189 _91345 x s.
Proof. exact (fun h0 : term181 _91345 x s => @lem3563775 _91345 _91348 x s f g h1). Qed.
Lemma lem3563778 (p : Prop) : (term190 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3563779 {_91345 : Type'} (x : _91345) (s : _91345 -> Prop) : (term189 _91345 x s) = (@IN _91345 x s).
Proof. exact (@lem3563778 (@IN _91345 x s)). Qed.
Lemma lem3563780 {_91345 _91348 : Type'} (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term132 _91345 _91348 x s f g) : @IN _91345 x s.
Proof. exact (EQ_MP (@lem3563779 _91345 x s) (@lem3563776 _91345 _91348 x s f g h1)). Qed.
Lemma lem3563782 {_91348 : Type'} (x : _91348) : x = x.
Proof. exact (@lem21386 _91348 x). Qed.
Lemma lem3563783 {_91348 : Type'} (x : _91348) : x = x.
Proof. exact (@lem3563782 _91348 x). Qed.
Lemma lem3563784 {_91345 _91348 : Type'} (f : _91345 -> _91348) (x : _91345) : (f x) = (f x).
Proof. exact (@lem3563783 _91348 (f x)). Qed.
Lemma lem3563785 {_91345 _91348 : Type'} (f : _91345 -> _91348) (x : _91345) : term202 _91345 _91348 f x.
Proof. exact (fun h0 : term203 _91345 _91348 f x => @lem3563784 _91345 _91348 f x). Qed.
Lemma lem3563787 (p : Prop) : (term190 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3563788 {_91345 _91348 : Type'} (f : _91345 -> _91348) (x : _91345) : (term202 _91345 _91348 f x) = ((f x) = (f x)).
Proof. exact (@lem3563787 ((f x) = (f x))). Qed.
Lemma lem3563789 {_91345 _91348 : Type'} (f : _91345 -> _91348) (x : _91345) : (f x) = (f x).
Proof. exact (EQ_MP (@lem3563788 _91345 _91348 f x) (@lem3563785 _91345 _91348 f x)). Qed.
Lemma lem3563795 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3563796 {_91345 _91348 : Type'} (f : _91345 -> _91348) (s : _91345 -> Prop) (g : _91348 -> _91345) (_38229 : _91348) (_38230 : _91345) : (term180 _91345 _91348 s f g _38229 _38230) = (term204 _91345 _91348 f s g _38229 _38230).
Proof. exact (@lem3563795 (term182 _91345 _91348 _38229 f _38230) (term181 _91345 _38230 s) ((g _38229) = _38230)). Qed.
Lemma lem3563812 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3563813 {_91345 _91348 : Type'} (g : _91348 -> _91345) (_38229 : _91348) (_38230 : _91345) (s : _91345 -> Prop) : (term205 _91345 _91348 s g _38229 _38230) = (term206 _91345 _91348 g _38229 _38230 s).
Proof. exact (@lem3563812 ((g _38229) = _38230) (term181 _91345 _38230 s)). Qed.
Lemma lem3563821 {_91345 _91348 : Type'} (_38229 : _91348) (f : _91345 -> _91348) (_38230 : _91345) : (term207 _91345 _91348 _38229 f _38230) = (term207 _91345 _91348 _38229 f _38230).
Proof. exact (eq_refl (term207 _91345 _91348 _38229 f _38230)). Qed.
Lemma lem3563822 {_91345 _91348 : Type'} (f : _91345 -> _91348) (g : _91348 -> _91345) (_38229 : _91348) (_38230 : _91345) (s : _91345 -> Prop) : (term204 _91345 _91348 f s g _38229 _38230) = (term208 _91345 _91348 f g _38229 _38230 s).
Proof. exact (MK_COMB (@lem3563821 _91345 _91348 _38229 f _38230) (@lem3563813 _91345 _91348 g _38229 _38230 s)). Qed.
Lemma lem3563826 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3563827 {_91345 _91348 : Type'} (g : _91348 -> _91345) (_38229 : _91348) (f : _91345 -> _91348) (_38230 : _91345) (s : _91345 -> Prop) : (term208 _91345 _91348 f g _38229 _38230 s) = (term209 _91345 _91348 g _38229 f _38230 s).
Proof. exact (@lem3563826 ((g _38229) = _38230) (term182 _91345 _91348 _38229 f _38230) (term181 _91345 _38230 s)). Qed.
Lemma lem3563847 {_91345 _91348 : Type'} (g : _91348 -> _91345) (_38229 : _91348) (f : _91345 -> _91348) (_38230 : _91345) (s : _91345 -> Prop) : (term204 _91345 _91348 f s g _38229 _38230) = (term209 _91345 _91348 g _38229 f _38230 s).
Proof. exact (TRANS (@lem3563822 _91345 _91348 f g _38229 _38230 s) (@lem3563827 _91345 _91348 g _38229 f _38230 s)). Qed.
Lemma lem3563848 {_91345 _91348 : Type'} (g : _91348 -> _91345) (_38229 : _91348) (f : _91345 -> _91348) (_38230 : _91345) (s : _91345 -> Prop) : (term180 _91345 _91348 s f g _38229 _38230) = (term209 _91345 _91348 g _38229 f _38230 s).
Proof. exact (TRANS (@lem3563796 _91345 _91348 f s g _38229 _38230) (@lem3563847 _91345 _91348 g _38229 f _38230 s)). Qed.
Lemma lem3563849 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3563850 {_91345 _91348 : Type'} (g : _91348 -> _91345) (_38229 : _91348) (f : _91345 -> _91348) (_38230 : _91345) (s : _91345 -> Prop) : (term210 _91345 _91348 s f g _38229 _38230) = (term211 _91345 _91348 g _38229 f _38230 s).
Proof. exact (MK_COMB (@lem3563849) (@lem3563848 _91345 _91348 g _38229 f _38230 s)). Qed.
Lemma lem3563866 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3563867 {_91345 _91348 : Type'} (_38229 : _91348) (f : _91345 -> _91348) (_38230 : _91345) (s : _91345 -> Prop) : (term52 _91345 _91348 s _38229 f _38230) = (term212 _91345 _91348 _38229 f _38230 s).
Proof. exact (@lem3563866 (term182 _91345 _91348 _38229 f _38230) (term181 _91345 _38230 s)). Qed.
Lemma lem3563875 {_91345 _91348 : Type'} (g : _91348 -> _91345) (_38229 : _91348) (_38230 : _91345) : (term213 _91345 _91348 g _38229 _38230) = (term213 _91345 _91348 g _38229 _38230).
Proof. exact (eq_refl (term213 _91345 _91348 g _38229 _38230)). Qed.
Lemma lem3563876 {_91345 _91348 : Type'} (g : _91348 -> _91345) (_38229 : _91348) (f : _91345 -> _91348) (_38230 : _91345) (s : _91345 -> Prop) : (term214 _91345 _91348 g s _38229 f _38230) = (term209 _91345 _91348 g _38229 f _38230 s).
Proof. exact (MK_COMB (@lem3563875 _91345 _91348 g _38229 _38230) (@lem3563867 _91345 _91348 _38229 f _38230 s)). Qed.
Lemma lem3563887 {_91345 _91348 : Type'} (g : _91348 -> _91345) (_38229 : _91348) (f : _91345 -> _91348) (_38230 : _91345) (s : _91345 -> Prop) : ((term180 _91345 _91348 s f g _38229 _38230) = (term214 _91345 _91348 g s _38229 f _38230)) = ((term209 _91345 _91348 g _38229 f _38230 s) = (term209 _91345 _91348 g _38229 f _38230 s)).
Proof. exact (MK_COMB (@lem3563850 _91345 _91348 g _38229 f _38230 s) (@lem3563876 _91345 _91348 g _38229 f _38230 s)). Qed.
Lemma lem3563889 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3563890 (x : Prop) : (x = x) = True.
Proof. exact (@lem3563889 Prop x). Qed.
Lemma lem3563891 {_91345 _91348 : Type'} (g : _91348 -> _91345) (_38229 : _91348) (f : _91345 -> _91348) (_38230 : _91345) (s : _91345 -> Prop) : ((term209 _91345 _91348 g _38229 f _38230 s) = (term209 _91345 _91348 g _38229 f _38230 s)) = True.
Proof. exact (@lem3563890 (term209 _91345 _91348 g _38229 f _38230 s)). Qed.
Lemma lem3563892 {_91345 _91348 : Type'} (g : _91348 -> _91345) (s : _91345 -> Prop) (_38229 : _91348) (f : _91345 -> _91348) (_38230 : _91345) : ((term180 _91345 _91348 s f g _38229 _38230) = (term214 _91345 _91348 g s _38229 f _38230)) = True.
Proof. exact (TRANS (@lem3563887 _91345 _91348 g _38229 f _38230 s) (@lem3563891 _91345 _91348 g _38229 f _38230 s)). Qed.
Lemma lem3563893 {_91345 _91348 : Type'} (g : _91348 -> _91345) (s : _91345 -> Prop) (_38229 : _91348) (f : _91345 -> _91348) (_38230 : _91345) : True = ((term180 _91345 _91348 s f g _38229 _38230) = (term214 _91345 _91348 g s _38229 f _38230)).
Proof. exact (SYM (@lem3563892 _91345 _91348 g s _38229 f _38230)). Qed.
Lemma lem3563894 {_91345 _91348 : Type'} (g : _91348 -> _91345) (s : _91345 -> Prop) (_38229 : _91348) (f : _91345 -> _91348) (_38230 : _91345) : (term180 _91345 _91348 s f g _38229 _38230) = (term214 _91345 _91348 g s _38229 f _38230).
Proof. exact (EQ_MP (@lem3563893 _91345 _91348 g s _38229 f _38230) (@lem0)). Qed.
Lemma lem3563895 {_91345 _91348 : Type'} (_38229 : _91348) (_38230 : _91345) (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term132 _91345 _91348 x s f g) : term214 _91345 _91348 g s _38229 f _38230.
Proof. exact (EQ_MP (@lem3563894 _91345 _91348 g s _38229 f _38230) (@lem3563552 _91345 _91348 _38229 _38230 x s f g h1)). Qed.
Lemma lem3563897 (b : Prop) (a : Prop) : (a \/ b) = (term194 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3563898 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (_38229 : _91348) (_38230 : _91345) : (term214 _91345 _91348 g s _38229 f _38230) = (term215 _91345 _91348 s f g _38229 _38230).
Proof. exact (@lem3563897 (term52 _91345 _91348 s _38229 f _38230) ((g _38229) = _38230)). Qed.
Lemma lem3563900 (a : Prop) (b : Prop) : (term216 a b) = (term217 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3563901 {_91345 _91348 : Type'} (s : _91345 -> Prop) (_38229 : _91348) (f : _91345 -> _91348) (_38230 : _91345) : (term218 _91345 _91348 s _38229 f _38230) = (term219 _91345 _91348 s _38229 f _38230).
Proof. exact (@lem3563900 (term181 _91345 _38230 s) (term182 _91345 _91348 _38229 f _38230)). Qed.
Lemma lem3563903 (a : Prop) : (term16 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3563904 {_91345 : Type'} (_38230 : _91345) (s : _91345 -> Prop) : (term196 _91345 _38230 s) = (@IN _91345 _38230 s).
Proof. exact (@lem3563903 (@IN _91345 _38230 s)). Qed.
Lemma lem3563905 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3563906 {_91345 : Type'} (_38230 : _91345) (s : _91345 -> Prop) : (term220 _91345 _38230 s) = (term221 _91345 _38230 s).
Proof. exact (MK_COMB (@lem3563905) (@lem3563904 _91345 _38230 s)). Qed.
Lemma lem3563908 (a : Prop) : (term16 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3563909 {_91345 _91348 : Type'} (_38229 : _91348) (f : _91345 -> _91348) (_38230 : _91345) : (term222 _91345 _91348 _38229 f _38230) = (_38229 = (f _38230)).
Proof. exact (@lem3563908 (_38229 = (f _38230))). Qed.
Lemma lem3563910 {_91345 _91348 : Type'} (s : _91345 -> Prop) (_38229 : _91348) (f : _91345 -> _91348) (_38230 : _91345) : (term219 _91345 _91348 s _38229 f _38230) = (term55 _91345 _91348 s _38229 f _38230).
Proof. exact (MK_COMB (@lem3563906 _91345 _38230 s) (@lem3563909 _91345 _91348 _38229 f _38230)). Qed.
Lemma lem3563911 {_91345 _91348 : Type'} (s : _91345 -> Prop) (_38229 : _91348) (f : _91345 -> _91348) (_38230 : _91345) : (term218 _91345 _91348 s _38229 f _38230) = (term55 _91345 _91348 s _38229 f _38230).
Proof. exact (TRANS (@lem3563901 _91345 _91348 s _38229 f _38230) (@lem3563910 _91345 _91348 s _38229 f _38230)). Qed.
Lemma lem3563912 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3563913 {_91345 _91348 : Type'} (s : _91345 -> Prop) (_38229 : _91348) (f : _91345 -> _91348) (_38230 : _91345) : (term223 _91345 _91348 s _38229 f _38230) = (term224 _91345 _91348 s _38229 f _38230).
Proof. exact (MK_COMB (@lem3563912) (@lem3563911 _91345 _91348 s _38229 f _38230)). Qed.
Lemma lem3563914 {_91345 _91348 : Type'} (g : _91348 -> _91345) (_38229 : _91348) (_38230 : _91345) : ((g _38229) = _38230) = ((g _38229) = _38230).
Proof. exact (eq_refl ((g _38229) = _38230)). Qed.
Lemma lem3563915 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (_38229 : _91348) (_38230 : _91345) : (term215 _91345 _91348 s f g _38229 _38230) = (term29 _91345 _91348 s f g _38229 _38230).
Proof. exact (MK_COMB (@lem3563913 _91345 _91348 s _38229 f _38230) (@lem3563914 _91345 _91348 g _38229 _38230)). Qed.
Lemma lem3563916 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (_38229 : _91348) (_38230 : _91345) : (term214 _91345 _91348 g s _38229 f _38230) = (term29 _91345 _91348 s f g _38229 _38230).
Proof. exact (TRANS (@lem3563898 _91345 _91348 s f g _38229 _38230) (@lem3563915 _91345 _91348 s f g _38229 _38230)). Qed.
Lemma lem3563918 {_91345 _91348 : Type'} (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term132 _91345 _91348 x s f g) : term225 _91345 _91348 s f x.
Proof. exact (conj (@lem3563780 _91345 _91348 x s f g h1) (@lem3563789 _91345 _91348 f x)). Qed.
Lemma lem3563920 {_91345 _91348 : Type'} (_38229 : _91348) (_38230 : _91345) (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term132 _91345 _91348 x s f g) : term29 _91345 _91348 s f g _38229 _38230.
Proof. exact (EQ_MP (@lem3563916 _91345 _91348 s f g _38229 _38230) (@lem3563895 _91345 _91348 _38229 _38230 x s f g h1)). Qed.
Lemma lem3563921 {_91345 _91348 : Type'} (_38229 : _91348) (_38230 : _91345) (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term132 _91345 _91348 x s f g) : term29 _91345 _91348 s f g _38229 _38230.
Proof. exact (@lem3563920 _91345 _91348 _38229 _38230 x s f g h1). Qed.
Lemma lem3563922 {_91345 _91348 : Type'} (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term132 _91345 _91348 x s f g) : term226 _91345 _91348 s g f x.
Proof. exact (@lem3563921 _91345 _91348 (f x) x x s f g h1). Qed.
Lemma lem3563925 {_91345 _91348 : Type'} (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term132 _91345 _91348 x s f g) : (term38 _91345 _91348 g f x) = x.
Proof. exact (@lem3563922 _91345 _91348 x s f g h1 (@lem3563918 _91345 _91348 x s f g h1)). Qed.
Lemma lem3563926 {_91345 _91348 : Type'} (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term132 _91345 _91348 x s f g) : term199 _91345 _91348 g f x.
Proof. exact (fun h0 : term183 _91345 _91348 g f x => @lem3563925 _91345 _91348 x s f g h1). Qed.
Lemma lem3563928 (p : Prop) : (term190 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3563929 {_91345 _91348 : Type'} (g : _91348 -> _91345) (f : _91345 -> _91348) (x : _91345) : (term199 _91345 _91348 g f x) = ((term38 _91345 _91348 g f x) = x).
Proof. exact (@lem3563928 ((term38 _91345 _91348 g f x) = x)). Qed.
Lemma lem3563930 {_91345 _91348 : Type'} (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term132 _91345 _91348 x s f g) : (term38 _91345 _91348 g f x) = x.
Proof. exact (EQ_MP (@lem3563929 _91345 _91348 g f x) (@lem3563926 _91345 _91348 x s f g h1)). Qed.
Lemma lem3563933 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3563935 {_91345 _91348 : Type'} (g : _91348 -> _91345) (f : _91345 -> _91348) (x : _91345) : (term183 _91345 _91348 g f x) = (term200 _91345 _91348 g f x).
Proof. exact (@lem3563933 ((term38 _91345 _91348 g f x) = x)). Qed.
Lemma lem3563938 {_91345 _91348 : Type'} (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term132 _91345 _91348 x s f g) : term200 _91345 _91348 g f x.
Proof. exact (EQ_MP (@lem3563935 _91345 _91348 g f x) (@lem3563556 _91345 _91348 x s f g h1)). Qed.
Lemma lem3563941 {_91345 _91348 : Type'} (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term132 _91345 _91348 x s f g) : False.
Proof. exact (@lem3563938 _91345 _91348 x s f g h1 (@lem3563930 _91345 _91348 x s f g h1)). Qed.
Lemma lem3563942 {_91345 _91348 : Type'} (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term132 _91345 _91348 x s f g) : term201.
Proof. exact (fun h0 : ~ False => @lem3563941 _91345 _91348 x s f g h1). Qed.
Lemma lem3563944 (p : Prop) : (term190 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3563945 : term201 = False.
Proof. exact (@lem3563944 False). Qed.
Lemma lem3563946 {_91345 _91348 : Type'} (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term132 _91345 _91348 x s f g) : False.
Proof. exact (EQ_MP (@lem3563945) (@lem3563942 _91345 _91348 x s f g h1)). Qed.
Lemma lem3563947 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (y : _91348) (x : _91345) (h1 : term112 _91345 _91348 s f g y x) : False.
Proof. exact (EQ_MP (@lem3563731) (@lem3563728 _91345 _91348 s f g y x h1)). Qed.
Lemma lem3563948 {_91345 _91348 : Type'} (y : _91348) (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term170 _91345 _91348 y x s f g) : False.
Proof. exact (or_elim (@lem3563452 _91345 _91348 y x s f g h1) (fun h0 : term112 _91345 _91348 s f g y x => @lem3563947 _91345 _91348 s f g y x h0) (fun h0 : term132 _91345 _91348 x s f g => @lem3563946 _91345 _91348 x s f g h0)). Qed.
Lemma lem3563949 {_91345 _91348 : Type'} (y : _91348) (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term170 _91345 _91348 y x s f g) : (term170 _91345 _91348 y x s f g) = False.
Proof. exact (prop_ext (fun h2 : term170 _91345 _91348 y x s f g => @lem3563948 _91345 _91348 y x s f g h1) (fun h2 : False => @lem3563452 _91345 _91348 y x s f g h1)). Qed.
Lemma lem3563950 {_91345 _91348 : Type'} (y : _91348) (x : _91345) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term170 _91345 _91348 y x s f g) : False.
Proof. exact (EQ_MP (@lem3563949 _91345 _91348 y x s f g h1) (@lem3563452 _91345 _91348 y x s f g h1)). Qed.
Lemma lem3563951 {_91345 _91348 : Type'} (y : _91348) (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term173 _91345 _91348 y s f g) : False.
Proof. exact (ex_elim (@lem3563338 _91345 _91348 y s f g h1) (fun x : _91345 => fun h0 : term172 _91345 _91348 y s f g x => @lem3563950 _91345 _91348 y x s f g h0)). Qed.
Lemma lem3563952 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term11 _91345 _91348 s f g) : False.
Proof. exact (ex_elim (@lem3563337 _91345 _91348 s f g h1) (fun y : _91348 => fun h0 : term174 _91345 _91348 s f g y => @lem3563951 _91345 _91348 y s f g h0)). Qed.
Lemma lem3563953 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term11 _91345 _91348 s f g) : (term11 _91345 _91348 s f g) = False.
Proof. exact (prop_ext (fun h2 : term11 _91345 _91348 s f g => @lem3563952 _91345 _91348 s f g h1) (fun h2 : False => @lem3562916 _91345 _91348 s f g h1)). Qed.
Lemma lem3563954 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term11 _91345 _91348 s f g) : False.
Proof. exact (EQ_MP (@lem3563953 _91345 _91348 s f g h1) (@lem3562916 _91345 _91348 s f g h1)). Qed.
Lemma lem3563955 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : term10 _91345 _91348 s f g.
Proof. exact (fun h0 : term11 _91345 _91348 s f g => @lem3563954 _91345 _91348 s f g h0). Qed.
Lemma lem3563956 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term8 _91345 _91348 s g f) = (term9 _91345 _91348 s f g).
Proof. exact (EQ_MP (@lem3562915 _91345 _91348 s f g) (@lem3563955 _91345 _91348 s f g)). Qed.
Lemma lem3563961 {_91345 _91348 : Type'} (f : _91345 -> _91348) (g : _91348 -> _91345) : term20 _91345 _91348 f g.
Proof. exact (fun s : _91345 -> Prop => @lem3563956 _91345 _91348 s f g). Qed.
Lemma lem3563966 {_91345 _91348 : Type'} (g : _91348 -> _91345) : term24 _91345 _91348 g.
Proof. exact (fun f : _91345 -> _91348 => @lem3563961 _91345 _91348 f g). Qed.
Lemma lem3563971 {_91345 _91348 : Type'} : term28 _91345 _91348.
Proof. exact (fun g : _91348 -> _91345 => @lem3563966 _91345 _91348 g). Qed.
Lemma lem3563972 {_91345 _91348 : Type'} : term27 _91345 _91348.
Proof. exact (EQ_MP (@lem3562911 _91345 _91348) (@lem3563971 _91345 _91348)). Qed.
Lemma lem3563973 {_91345 _91348 : Type'} (g : _91348 -> _91345) : term227 _91345 _91348 g.
Proof. exact (@lem3563972 _91345 _91348 g). Qed.
Lemma lem3563974 {_91345 _91348 : Type'} (g : _91348 -> _91345) : (term227 _91345 _91348 g) = (term23 _91345 _91348 g).
Proof. exact (eq_refl (term227 _91345 _91348 g)). Qed.
Lemma lem3563975 {_91345 _91348 : Type'} (g : _91348 -> _91345) : term23 _91345 _91348 g.
Proof. exact (EQ_MP (@lem3563974 _91345 _91348 g) (@lem3563973 _91345 _91348 g)). Qed.
Lemma lem3563976 {_91345 _91348 : Type'} (g : _91348 -> _91345) (f : _91345 -> _91348) : term228 _91345 _91348 g f.
Proof. exact (@lem3563975 _91345 _91348 g f). Qed.
Lemma lem3563977 {_91345 _91348 : Type'} (f : _91345 -> _91348) (g : _91348 -> _91345) : (term228 _91345 _91348 g f) = (term19 _91345 _91348 f g).
Proof. exact (eq_refl (term228 _91345 _91348 g f)). Qed.
Lemma lem3563978 {_91345 _91348 : Type'} (f : _91345 -> _91348) (g : _91348 -> _91345) : term19 _91345 _91348 f g.
Proof. exact (EQ_MP (@lem3563977 _91345 _91348 f g) (@lem3563976 _91345 _91348 g f)). Qed.
Lemma lem3563979 {_91345 _91348 : Type'} (f : _91345 -> _91348) (g : _91348 -> _91345) (s : _91345 -> Prop) : term229 _91345 _91348 f g s.
Proof. exact (@lem3563978 _91345 _91348 f g s). Qed.
Lemma lem3563980 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term229 _91345 _91348 f g s) = (term10 _91345 _91348 s f g).
Proof. exact (eq_refl (term229 _91345 _91348 f g s)). Qed.
Lemma lem3563981 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : term10 _91345 _91348 s f g.
Proof. exact (EQ_MP (@lem3563980 _91345 _91348 s f g) (@lem3563979 _91345 _91348 f g s)). Qed.
Lemma lem3563983 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : term10 _91345 _91348 s f g.
Proof. exact (@lem3562768 _91345 _91348 s f g (@lem3563981 _91345 _91348 s f g)). Qed.
Lemma lem3563984 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term11 _91345 _91348 s f g) : False.
Proof. exact (@lem3563983 _91345 _91348 s f g (@lem3562752 _91345 _91348 s f g h1)). Qed.
Lemma lem3563985 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term11 _91345 _91348 s f g) : (term11 _91345 _91348 s f g) = False.
Proof. exact (prop_ext (fun h2 : term11 _91345 _91348 s f g => @lem3563984 _91345 _91348 s f g h1) (fun h2 : False => @lem3562752 _91345 _91348 s f g h1)). Qed.
Lemma lem3563986 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) (h1 : term11 _91345 _91348 s f g) : False.
Proof. exact (EQ_MP (@lem3563985 _91345 _91348 s f g h1) (@lem3562752 _91345 _91348 s f g h1)). Qed.
Lemma lem3563987 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : term10 _91345 _91348 s f g.
Proof. exact (fun h0 : term11 _91345 _91348 s f g => @lem3563986 _91345 _91348 s f g h0). Qed.
Lemma lem3563989 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3563990 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3563991 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3563990 t1) (@lem3563989 t1)). Qed.
Lemma lem3563992 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3563991 t1 t2). Qed.
Lemma lem3563993 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3563994 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3563993 t1 t2) (@lem3563992 t1 t2)). Qed.
Lemma lem3563995 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3563994 t1 t2 t3). Qed.
Lemma lem3563996 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3563997 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3563996 t1 t2 t3) (@lem3563995 t1 t2 t3)). Qed.
Lemma lem3563998 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3563997 t1 t2 t3)). Qed.
Lemma lem3564000 {A B : Type'} (P : type1413 A B) (h1 : (term230 A B P) = (term231 A B P)) : (term230 A B P) = (term231 A B P).
Proof. exact (h1). Qed.
Lemma lem3564001 {A B : Type'} (P : type1413 A B) (h1 : (term230 A B P) = (term231 A B P)) : (term231 A B P) = (term230 A B P).
Proof. exact (SYM (@lem3564000 A B P h1)). Qed.
Lemma lem3564002 {A B : Type'} (P : type1413 A B) (h1 : (term231 A B P) = (term230 A B P)) : (term231 A B P) = (term230 A B P).
Proof. exact (h1). Qed.
Lemma lem3564003 {A B : Type'} (P : type1413 A B) (h1 : (term231 A B P) = (term230 A B P)) : (term230 A B P) = (term231 A B P).
Proof. exact (SYM (@lem3564002 A B P h1)). Qed.
Lemma lem3564004 {A B : Type'} (P : type1413 A B) : ((term230 A B P) = (term231 A B P)) = ((term231 A B P) = (term230 A B P)).
Proof. exact (prop_ext (fun h1 : (term230 A B P) = (term231 A B P) => @lem3564001 A B P h1) (fun h1 : (term231 A B P) = (term230 A B P) => @lem3564003 A B P h1)). Qed.
Lemma lem3564005 {A B : Type'} : (term232 A B) = (term233 A B).
Proof. exact (fun_ext (fun P : type1413 A B => @lem3564004 A B P)). Qed.
Lemma lem3564006 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem3564007 {A B : Type'} : (term234 A B) = (term235 A B).
Proof. exact (MK_COMB (@lem3564006 A B) (@lem3564005 A B)). Qed.
Lemma lem3564008 {A B : Type'} : term235 A B.
Proof. exact (EQ_MP (@lem3564007 A B) (@lem13546 A B)). Qed.
Lemma lem3564009 {A B : Type'} (P : type1413 A B) : term236 A B P.
Proof. exact (@lem3564008 A B P). Qed.
Lemma lem3564010 {A B : Type'} (P : type1413 A B) : (term236 A B P) = ((term231 A B P) = (term230 A B P)).
Proof. exact (eq_refl (term236 A B P)). Qed.
Lemma lem3564047 {_91345 _91348 : Type'} (s : _91345 -> Prop) (f : _91345 -> _91348) (g : _91348 -> _91345) : (term8 _91345 _91348 s g f) = (term9 _91345 _91348 s f g).
Proof. exact (EQ_MP (@lem3562751 _91345 _91348 s f g) (@lem3563987 _91345 _91348 s f g)). Qed.
Lemma lem3564048 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) : (term8 _91401 _91404 s g f) = (term9 _91401 _91404 s f g).
Proof. exact (@lem3564047 _91401 _91404 s f g). Qed.
Lemma lem3564065 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term237 _91401 _91404 s f) = (term238 _91401 _91404 s f).
Proof. exact (fun_ext (fun g : _91404 -> _91401 => @lem3564048 _91401 _91404 s f g)). Qed.
Lemma lem3564066 {_91401 _91404 : Type'} : (@ex (_91404 -> _91401)) = (@ex (_91404 -> _91401)).
Proof. exact (eq_refl (@ex (_91404 -> _91401))). Qed.
Lemma lem3564067 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term239 _91401 _91404 s f) = (term240 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564066 _91401 _91404) (@lem3564065 _91401 _91404 s f)). Qed.
Lemma lem3564069 {A B : Type'} (P : type1413 A B) : (term231 A B P) = (term230 A B P).
Proof. exact (EQ_MP (@lem3564010 A B P) (@lem3564009 A B P)). Qed.
Lemma lem3564070 {_91401 _91404 : Type'} (P : type1470 _91401 _91404) : (term241 _91401 _91404 P) = (term242 _91401 _91404 P).
Proof. exact (@lem3564069 _91404 _91401 P). Qed.
Lemma lem3564071 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term243 _91401 _91404 s f) = (term244 _91401 _91404 s f).
Proof. exact (@lem3564070 _91401 _91404 (term245 _91401 _91404 s f)). Qed.
Lemma lem3564072 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term246 _91401 _91404 s f y) = (term247 _91401 _91404 s y f).
Proof. exact (eq_refl (term246 _91401 _91404 s f y)). Qed.
Lemma lem3564073 {_91401 _91404 : Type'} (g : _91404 -> _91401) (y : _91404) : (g y) = (g y).
Proof. exact (eq_refl (g y)). Qed.
Lemma lem3564074 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (y : _91404) : (term248 _91401 _91404 s f g y) = (term249 _91401 _91404 s f g y).
Proof. exact (MK_COMB (@lem3564072 _91401 _91404 s y f) (@lem3564073 _91401 _91404 g y)). Qed.
Lemma lem3564075 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (y : _91404) : (term249 _91401 _91404 s f g y) = (term31 _91401 _91404 s f g y).
Proof. exact (eq_refl (term249 _91401 _91404 s f g y)). Qed.
Lemma lem3564076 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (y : _91404) : (term248 _91401 _91404 s f g y) = (term31 _91401 _91404 s f g y).
Proof. exact (TRANS (@lem3564074 _91401 _91404 s f g y) (@lem3564075 _91401 _91404 s f g y)). Qed.
Lemma lem3564077 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) : (term250 _91401 _91404 s f g) = (term32 _91401 _91404 s f g).
Proof. exact (fun_ext (fun y : _91404 => @lem3564076 _91401 _91404 s f g y)). Qed.
Lemma lem3564078 {_91404 : Type'} : (@all _91404) = (@all _91404).
Proof. exact (eq_refl (@all _91404)). Qed.
Lemma lem3564079 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) : (term251 _91401 _91404 s f g) = (term9 _91401 _91404 s f g).
Proof. exact (MK_COMB (@lem3564078 _91404) (@lem3564077 _91401 _91404 s f g)). Qed.
Lemma lem3564080 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term252 _91401 _91404 s f) = (term238 _91401 _91404 s f).
Proof. exact (fun_ext (fun g : _91404 -> _91401 => @lem3564079 _91401 _91404 s f g)). Qed.
Lemma lem3564081 {_91401 _91404 : Type'} : (@ex (_91404 -> _91401)) = (@ex (_91404 -> _91401)).
Proof. exact (eq_refl (@ex (_91404 -> _91401))). Qed.
Lemma lem3564082 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term243 _91401 _91404 s f) = (term240 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564081 _91401 _91404) (@lem3564080 _91401 _91404 s f)). Qed.
Lemma lem3564083 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3564084 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term253 _91401 _91404 s f) = (term254 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564083) (@lem3564082 _91401 _91404 s f)). Qed.
Lemma lem3564085 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term246 _91401 _91404 s f y) = (term247 _91401 _91404 s y f).
Proof. exact (eq_refl (term246 _91401 _91404 s f y)). Qed.
Lemma lem3564086 {_91401 : Type'} (g : _91401) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem3564087 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (g : _91401) : (term255 _91401 _91404 s f y g) = (term256 _91401 _91404 s y f g).
Proof. exact (MK_COMB (@lem3564085 _91401 _91404 s y f) (@lem3564086 _91401 g)). Qed.
Lemma lem3564088 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (g : _91401) : (term256 _91401 _91404 s y f g) = (term257 _91401 _91404 s y f g).
Proof. exact (eq_refl (term256 _91401 _91404 s y f g)). Qed.
Lemma lem3564089 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (g : _91401) : (term255 _91401 _91404 s f y g) = (term257 _91401 _91404 s y f g).
Proof. exact (TRANS (@lem3564087 _91401 _91404 s y f g) (@lem3564088 _91401 _91404 s y f g)). Qed.
Lemma lem3564090 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term258 _91401 _91404 s f y) = (term247 _91401 _91404 s y f).
Proof. exact (fun_ext (fun g : _91401 => @lem3564089 _91401 _91404 s y f g)). Qed.
Lemma lem3564091 {_91401 : Type'} : (@ex _91401) = (@ex _91401).
Proof. exact (eq_refl (@ex _91401)). Qed.
Lemma lem3564092 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term259 _91401 _91404 s f y) = (term260 _91401 _91404 s y f).
Proof. exact (MK_COMB (@lem3564091 _91401) (@lem3564090 _91401 _91404 s y f)). Qed.
Lemma lem3564093 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term261 _91401 _91404 s f) = (term262 _91401 _91404 s f).
Proof. exact (fun_ext (fun y : _91404 => @lem3564092 _91401 _91404 s y f)). Qed.
Lemma lem3564094 {_91404 : Type'} : (@all _91404) = (@all _91404).
Proof. exact (eq_refl (@all _91404)). Qed.
Lemma lem3564095 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term244 _91401 _91404 s f) = (term263 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564094 _91404) (@lem3564093 _91401 _91404 s f)). Qed.
Lemma lem3564096 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : ((term243 _91401 _91404 s f) = (term244 _91401 _91404 s f)) = ((term240 _91401 _91404 s f) = (term263 _91401 _91404 s f)).
Proof. exact (MK_COMB (@lem3564084 _91401 _91404 s f) (@lem3564095 _91401 _91404 s f)). Qed.
Lemma lem3564097 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term240 _91401 _91404 s f) = (term263 _91401 _91404 s f).
Proof. exact (EQ_MP (@lem3564096 _91401 _91404 s f) (@lem3564071 _91401 _91404 s f)). Qed.
Lemma lem3564120 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term239 _91401 _91404 s f) = (term263 _91401 _91404 s f).
Proof. exact (TRANS (@lem3564067 _91401 _91404 s f) (@lem3564097 _91401 _91404 s f)). Qed.
Lemma lem3564121 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term264 _91401 _91404 s f) = (term264 _91401 _91404 s f).
Proof. exact (eq_refl (term264 _91401 _91404 s f)). Qed.
Lemma lem3564122 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : ((term265 _91401 _91404 s f) = (term239 _91401 _91404 s f)) = ((term265 _91401 _91404 s f) = (term263 _91401 _91404 s f)).
Proof. exact (MK_COMB (@lem3564121 _91401 _91404 s f) (@lem3564120 _91401 _91404 s f)). Qed.
Lemma lem3564125 {_91401 _91404 : Type'} (f : _91401 -> _91404) : (term266 _91401 _91404 f) = (term267 _91401 _91404 f).
Proof. exact (fun_ext (fun s : _91401 -> Prop => @lem3564122 _91401 _91404 s f)). Qed.
Lemma lem3564126 {_91401 : Type'} : (@all (_91401 -> Prop)) = (@all (_91401 -> Prop)).
Proof. exact (eq_refl (@all (_91401 -> Prop))). Qed.
Lemma lem3564127 {_91401 _91404 : Type'} (f : _91401 -> _91404) : (term268 _91401 _91404 f) = (term269 _91401 _91404 f).
Proof. exact (MK_COMB (@lem3564126 _91401) (@lem3564125 _91401 _91404 f)). Qed.
Lemma lem3564132 {_91401 _91404 : Type'} : (term270 _91401 _91404) = (term271 _91401 _91404).
Proof. exact (fun_ext (fun f : _91401 -> _91404 => @lem3564127 _91401 _91404 f)). Qed.
Lemma lem3564133 {_91401 _91404 : Type'} : (@all (_91401 -> _91404)) = (@all (_91401 -> _91404)).
Proof. exact (eq_refl (@all (_91401 -> _91404))). Qed.
Lemma lem3564134 {_91401 _91404 : Type'} : (term272 _91401 _91404) = (term273 _91401 _91404).
Proof. exact (MK_COMB (@lem3564133 _91401 _91404) (@lem3564132 _91401 _91404)). Qed.
Lemma lem3564139 {_91401 _91404 : Type'} : (term273 _91401 _91404) = (term272 _91401 _91404).
Proof. exact (SYM (@lem3564134 _91401 _91404)). Qed.
Lemma lem3564141 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3564142 {_91401 _91404 : Type'} : (term273 _91401 _91404) = (term274 _91401 _91404).
Proof. exact (@lem3564141 (term273 _91401 _91404)). Qed.
Lemma lem3564143 {_91401 _91404 : Type'} : (term274 _91401 _91404) = (term273 _91401 _91404).
Proof. exact (SYM (@lem3564142 _91401 _91404)). Qed.
Lemma lem3564144 {_91401 _91404 : Type'} (h1 : term275 _91401 _91404) : term275 _91401 _91404.
Proof. exact (h1). Qed.
Lemma lem3564147 {_91401 _91404 : Type'} (h1 : term274 _91401 _91404) : term274 _91401 _91404.
Proof. exact (h1). Qed.
Lemma lem3564148 {_91401 _91404 : Type'} : term276 _91401 _91404.
Proof. exact (fun h0 : term274 _91401 _91404 => @lem3564147 _91401 _91404 h0). Qed.
Lemma lem3564149 {_91401 _91404 : Type'} (h1 : term276 _91401 _91404) : term276 _91401 _91404.
Proof. exact (h1). Qed.
Lemma lem3564150 {_91401 _91404 : Type'} (h1 : term274 _91401 _91404) : term274 _91401 _91404.
Proof. exact (h1). Qed.
Lemma lem3564151 {_91401 _91404 : Type'} (h1 : term274 _91401 _91404) (h2 : term276 _91401 _91404) : term274 _91401 _91404.
Proof. exact (@lem3564149 _91401 _91404 h2 (@lem3564150 _91401 _91404 h1)). Qed.
Lemma lem3564152 {_91401 _91404 : Type'} (h1 : term274 _91401 _91404) : term277 _91401 _91404.
Proof. exact (fun h0 : term276 _91401 _91404 => @lem3564151 _91401 _91404 h1 h0). Qed.
Lemma lem3564153 {_91401 _91404 : Type'} (h1 : term276 _91401 _91404) : term276 _91401 _91404.
Proof. exact (h1). Qed.
Lemma lem3564154 {_91401 _91404 : Type'} (h1 : term274 _91401 _91404) (h2 : term276 _91401 _91404) : term274 _91401 _91404.
Proof. exact (@lem3564152 _91401 _91404 h1 (@lem3564153 _91401 _91404 h2)). Qed.
Lemma lem3564155 {_91401 _91404 : Type'} (h1 : term276 _91401 _91404) : term276 _91401 _91404.
Proof. exact (fun h0 : term274 _91401 _91404 => @lem3564154 _91401 _91404 h0 h1). Qed.
Lemma lem3564156 {_91401 _91404 : Type'} : term278 _91401 _91404.
Proof. exact (fun h0 : term276 _91401 _91404 => @lem3564155 _91401 _91404 h0). Qed.
Lemma lem3564159 {_91401 _91404 : Type'} : term276 _91401 _91404.
Proof. exact (@lem3564156 _91401 _91404 (@lem3564148 _91401 _91404)). Qed.
Lemma lem3564160 {_91401 _91404 : Type'} : term276 _91401 _91404.
Proof. exact (@lem3564159 _91401 _91404). Qed.
Lemma lem3564162 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3564163 {_91401 _91404 : Type'} : (term274 _91401 _91404) = (term279 _91401 _91404).
Proof. exact (@lem3564162 (term275 _91401 _91404)). Qed.
Lemma lem3564165 (t : Prop) : (term16 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3564166 {_91401 _91404 : Type'} : (term279 _91401 _91404) = (term273 _91401 _91404).
Proof. exact (@lem3564165 (term273 _91401 _91404)). Qed.
Lemma lem3564209 {_91401 _91404 : Type'} : (term274 _91401 _91404) = (term273 _91401 _91404).
Proof. exact (TRANS (@lem3564163 _91401 _91404) (@lem3564166 _91401 _91404)). Qed.
Lemma lem3564218 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (g : _91401) (x : _91401) : (term280 _91401 _91404 s y f g x) = (term280 _91401 _91404 s y f g x).
Proof. exact (eq_refl (term280 _91401 _91404 s y f g x)). Qed.
Lemma lem3564219 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (g : _91401) : (term281 _91401 _91404 s y f g) = (term281 _91401 _91404 s y f g).
Proof. exact (fun_ext (fun x : _91401 => @lem3564218 _91401 _91404 s y f g x)). Qed.
Lemma lem3564220 {_91401 : Type'} : (@all _91401) = (@all _91401).
Proof. exact (eq_refl (@all _91401)). Qed.
Lemma lem3564221 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (g : _91401) : (term257 _91401 _91404 s y f g) = (term257 _91401 _91404 s y f g).
Proof. exact (MK_COMB (@lem3564220 _91401) (@lem3564219 _91401 _91404 s y f g)). Qed.
Lemma lem3564222 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term247 _91401 _91404 s y f) = (term247 _91401 _91404 s y f).
Proof. exact (fun_ext (fun g : _91401 => @lem3564221 _91401 _91404 s y f g)). Qed.
Lemma lem3564223 {_91401 : Type'} : (@ex _91401) = (@ex _91401).
Proof. exact (eq_refl (@ex _91401)). Qed.
Lemma lem3564224 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term260 _91401 _91404 s y f) = (term260 _91401 _91404 s y f).
Proof. exact (MK_COMB (@lem3564223 _91401) (@lem3564222 _91401 _91404 s y f)). Qed.
Lemma lem3564225 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term262 _91401 _91404 s f) = (term262 _91401 _91404 s f).
Proof. exact (fun_ext (fun y : _91404 => @lem3564224 _91401 _91404 s y f)). Qed.
Lemma lem3564226 {_91404 : Type'} : (@all _91404) = (@all _91404).
Proof. exact (eq_refl (@all _91404)). Qed.
Lemma lem3564227 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term263 _91401 _91404 s f) = (term263 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564226 _91404) (@lem3564225 _91401 _91404 s f)). Qed.
Lemma lem3564240 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) (y : _91401) : (term282 _91401 _91404 s f x y) = (term282 _91401 _91404 s f x y).
Proof. exact (eq_refl (term282 _91401 _91404 s f x y)). Qed.
Lemma lem3564241 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) : (term283 _91401 _91404 s f x) = (term283 _91401 _91404 s f x).
Proof. exact (fun_ext (fun y : _91401 => @lem3564240 _91401 _91404 s f x y)). Qed.
Lemma lem3564242 {_91401 : Type'} : (@all _91401) = (@all _91401).
Proof. exact (eq_refl (@all _91401)). Qed.
Lemma lem3564243 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) : (term284 _91401 _91404 s f x) = (term284 _91401 _91404 s f x).
Proof. exact (MK_COMB (@lem3564242 _91401) (@lem3564241 _91401 _91404 s f x)). Qed.
Lemma lem3564244 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term285 _91401 _91404 s f) = (term285 _91401 _91404 s f).
Proof. exact (fun_ext (fun x : _91401 => @lem3564243 _91401 _91404 s f x)). Qed.
Lemma lem3564245 {_91401 : Type'} : (@all _91401) = (@all _91401).
Proof. exact (eq_refl (@all _91401)). Qed.
Lemma lem3564246 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term265 _91401 _91404 s f) = (term265 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564245 _91401) (@lem3564244 _91401 _91404 s f)). Qed.
Lemma lem3564247 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3564248 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term264 _91401 _91404 s f) = (term264 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564247) (@lem3564246 _91401 _91404 s f)). Qed.
Lemma lem3564249 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : ((term265 _91401 _91404 s f) = (term263 _91401 _91404 s f)) = ((term265 _91401 _91404 s f) = (term263 _91401 _91404 s f)).
Proof. exact (MK_COMB (@lem3564248 _91401 _91404 s f) (@lem3564227 _91401 _91404 s f)). Qed.
Lemma lem3564250 {_91401 _91404 : Type'} (f : _91401 -> _91404) : (term267 _91401 _91404 f) = (term267 _91401 _91404 f).
Proof. exact (fun_ext (fun s : _91401 -> Prop => @lem3564249 _91401 _91404 s f)). Qed.
Lemma lem3564251 {_91401 : Type'} : (@all (_91401 -> Prop)) = (@all (_91401 -> Prop)).
Proof. exact (eq_refl (@all (_91401 -> Prop))). Qed.
Lemma lem3564252 {_91401 _91404 : Type'} (f : _91401 -> _91404) : (term269 _91401 _91404 f) = (term269 _91401 _91404 f).
Proof. exact (MK_COMB (@lem3564251 _91401) (@lem3564250 _91401 _91404 f)). Qed.
Lemma lem3564253 {_91401 _91404 : Type'} : (term271 _91401 _91404) = (term271 _91401 _91404).
Proof. exact (fun_ext (fun f : _91401 -> _91404 => @lem3564252 _91401 _91404 f)). Qed.
Lemma lem3564254 {_91401 _91404 : Type'} : (@all (_91401 -> _91404)) = (@all (_91401 -> _91404)).
Proof. exact (eq_refl (@all (_91401 -> _91404))). Qed.
Lemma lem3564255 {_91401 _91404 : Type'} : (term273 _91401 _91404) = (term273 _91401 _91404).
Proof. exact (MK_COMB (@lem3564254 _91401 _91404) (@lem3564253 _91401 _91404)). Qed.
Lemma lem3564310 {_91401 _91404 : Type'} : (term274 _91401 _91404) = (term273 _91401 _91404).
Proof. exact (TRANS (@lem3564209 _91401 _91404) (@lem3564255 _91401 _91404)). Qed.
Lemma lem3564311 {_91401 _91404 : Type'} : (term273 _91401 _91404) = (term274 _91401 _91404).
Proof. exact (SYM (@lem3564310 _91401 _91404)). Qed.
Lemma lem3564313 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3564314 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : ((term265 _91401 _91404 s f) = (term263 _91401 _91404 s f)) = (term286 _91401 _91404 s f).
Proof. exact (@lem3564313 ((term265 _91401 _91404 s f) = (term263 _91401 _91404 s f))). Qed.
Lemma lem3564315 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term286 _91401 _91404 s f) = ((term265 _91401 _91404 s f) = (term263 _91401 _91404 s f)).
Proof. exact (SYM (@lem3564314 _91401 _91404 s f)). Qed.
Lemma lem3564316 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (h1 : term287 _91401 _91404 s f) : term287 _91401 _91404 s f.
Proof. exact (h1). Qed.
Lemma lem3564327 {_91401 _91404 : Type'} (s : _91401 -> Prop) (x : _91401) (f : _91401 -> _91404) (y : _91401) : (term288 _91401 _91404 s x f y) = (term289 _91401 _91404 s x f y).
Proof. exact (@lem17045 (@IN _91401 y s) ((f x) = (f y))). Qed.
Lemma lem3564332 {_91401 : Type'} (x : _91401) (s : _91401 -> Prop) : (term290 _91401 x s) = (term290 _91401 x s).
Proof. exact (eq_refl (term290 _91401 x s)). Qed.
Lemma lem3564333 {_91401 _91404 : Type'} (s : _91401 -> Prop) (x : _91401) (f : _91401 -> _91404) (y : _91401) : (term291 _91401 _91404 s x f y) = (term292 _91401 _91404 s x f y).
Proof. exact (MK_COMB (@lem3564332 _91401 x s) (@lem3564327 _91401 _91404 s x f y)). Qed.
Lemma lem3564334 {_91401 _91404 : Type'} (s : _91401 -> Prop) (x : _91401) (f : _91401 -> _91404) (y : _91401) : (term293 _91401 _91404 s x f y) = (term291 _91401 _91404 s x f y).
Proof. exact (@lem17045 (@IN _91401 x s) (term294 _91401 _91404 s x f y)). Qed.
Lemma lem3564335 {_91401 _91404 : Type'} (s : _91401 -> Prop) (x : _91401) (f : _91401 -> _91404) (y : _91401) : (term293 _91401 _91404 s x f y) = (term292 _91401 _91404 s x f y).
Proof. exact (TRANS (@lem3564334 _91401 _91404 s x f y) (@lem3564333 _91401 _91404 s x f y)). Qed.
Lemma lem3564340 {_91401 : Type'} (x : _91401) (y : _91401) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem3564345 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) (y : _91401) : (term295 _91401 _91404 s f x y) = (term296 _91401 _91404 s f x y).
Proof. exact (@lem17362 (term297 _91401 _91404 s x f y) (x = y)). Qed.
Lemma lem3564346 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3564347 {_91401 _91404 : Type'} (s : _91401 -> Prop) (x : _91401) (f : _91401 -> _91404) (y : _91401) : (term298 _91401 _91404 s x f y) = (term299 _91401 _91404 s x f y).
Proof. exact (MK_COMB (@lem3564346) (@lem3564335 _91401 _91404 s x f y)). Qed.
Lemma lem3564348 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) (y : _91401) : (term300 _91401 _91404 s f x y) = (term301 _91401 _91404 s f x y).
Proof. exact (MK_COMB (@lem3564347 _91401 _91404 s x f y) (@lem3564340 _91401 x y)). Qed.
Lemma lem3564349 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) (y : _91401) : (term282 _91401 _91404 s f x y) = (term300 _91401 _91404 s f x y).
Proof. exact (@lem17265 (term297 _91401 _91404 s x f y) (x = y)). Qed.
Lemma lem3564350 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) (y : _91401) : (term282 _91401 _91404 s f x y) = (term301 _91401 _91404 s f x y).
Proof. exact (TRANS (@lem3564349 _91401 _91404 s f x y) (@lem3564348 _91401 _91404 s f x y)). Qed.
Lemma lem3564351 {_91401 : Type'} (P : _91401 -> Prop) : (term40 _91401 P) = (term41 _91401 P).
Proof. exact (@lem18392 _91401 P). Qed.
Lemma lem3564352 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) : (term302 _91401 _91404 s f x) = (term303 _91401 _91404 s f x).
Proof. exact (@lem3564351 _91401 (term283 _91401 _91404 s f x)). Qed.
Lemma lem3564353 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) (y : _91401) : (term304 _91401 _91404 s f x y) = (term282 _91401 _91404 s f x y).
Proof. exact (eq_refl (term304 _91401 _91404 s f x y)). Qed.
Lemma lem3564354 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3564355 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) (y : _91401) : (term305 _91401 _91404 s f x y) = (term295 _91401 _91404 s f x y).
Proof. exact (MK_COMB (@lem3564354) (@lem3564353 _91401 _91404 s f x y)). Qed.
Lemma lem3564356 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) (y : _91401) : (term305 _91401 _91404 s f x y) = (term296 _91401 _91404 s f x y).
Proof. exact (TRANS (@lem3564355 _91401 _91404 s f x y) (@lem3564345 _91401 _91404 s f x y)). Qed.
Lemma lem3564357 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) : (term306 _91401 _91404 s f x) = (term307 _91401 _91404 s f x).
Proof. exact (fun_ext (fun y : _91401 => @lem3564356 _91401 _91404 s f x y)). Qed.
Lemma lem3564358 {_91401 : Type'} : (@ex _91401) = (@ex _91401).
Proof. exact (eq_refl (@ex _91401)). Qed.
Lemma lem3564359 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) : (term303 _91401 _91404 s f x) = (term308 _91401 _91404 s f x).
Proof. exact (MK_COMB (@lem3564358 _91401) (@lem3564357 _91401 _91404 s f x)). Qed.
Lemma lem3564360 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) : (term302 _91401 _91404 s f x) = (term308 _91401 _91404 s f x).
Proof. exact (TRANS (@lem3564352 _91401 _91404 s f x) (@lem3564359 _91401 _91404 s f x)). Qed.
Lemma lem3564361 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) : (term283 _91401 _91404 s f x) = (term309 _91401 _91404 s f x).
Proof. exact (fun_ext (fun y : _91401 => @lem3564350 _91401 _91404 s f x y)). Qed.
Lemma lem3564362 {_91401 : Type'} : (@all _91401) = (@all _91401).
Proof. exact (eq_refl (@all _91401)). Qed.
Lemma lem3564363 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) : (term284 _91401 _91404 s f x) = (term310 _91401 _91404 s f x).
Proof. exact (MK_COMB (@lem3564362 _91401) (@lem3564361 _91401 _91404 s f x)). Qed.
Lemma lem3564364 {_91401 : Type'} (P : _91401 -> Prop) : (term40 _91401 P) = (term41 _91401 P).
Proof. exact (@lem18392 _91401 P). Qed.
Lemma lem3564365 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term311 _91401 _91404 s f) = (term312 _91401 _91404 s f).
Proof. exact (@lem3564364 _91401 (term285 _91401 _91404 s f)). Qed.
Lemma lem3564366 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) : (term313 _91401 _91404 s f x) = (term284 _91401 _91404 s f x).
Proof. exact (eq_refl (term313 _91401 _91404 s f x)). Qed.
Lemma lem3564367 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3564368 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) : (term314 _91401 _91404 s f x) = (term302 _91401 _91404 s f x).
Proof. exact (MK_COMB (@lem3564367) (@lem3564366 _91401 _91404 s f x)). Qed.
Lemma lem3564369 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) : (term314 _91401 _91404 s f x) = (term308 _91401 _91404 s f x).
Proof. exact (TRANS (@lem3564368 _91401 _91404 s f x) (@lem3564360 _91401 _91404 s f x)). Qed.
Lemma lem3564370 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term315 _91401 _91404 s f) = (term316 _91401 _91404 s f).
Proof. exact (fun_ext (fun x : _91401 => @lem3564369 _91401 _91404 s f x)). Qed.
Lemma lem3564371 {_91401 : Type'} : (@ex _91401) = (@ex _91401).
Proof. exact (eq_refl (@ex _91401)). Qed.
Lemma lem3564372 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term312 _91401 _91404 s f) = (term317 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564371 _91401) (@lem3564370 _91401 _91404 s f)). Qed.
Lemma lem3564373 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term311 _91401 _91404 s f) = (term317 _91401 _91404 s f).
Proof. exact (TRANS (@lem3564365 _91401 _91404 s f) (@lem3564372 _91401 _91404 s f)). Qed.
Lemma lem3564374 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term285 _91401 _91404 s f) = (term318 _91401 _91404 s f).
Proof. exact (fun_ext (fun x : _91401 => @lem3564363 _91401 _91404 s f x)). Qed.
Lemma lem3564375 {_91401 : Type'} : (@all _91401) = (@all _91401).
Proof. exact (eq_refl (@all _91401)). Qed.
Lemma lem3564376 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term265 _91401 _91404 s f) = (term319 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564375 _91401) (@lem3564374 _91401 _91404 s f)). Qed.
Lemma lem3564385 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401) : (term51 _91401 _91404 s y f x) = (term52 _91401 _91404 s y f x).
Proof. exact (@lem17045 (@IN _91401 x s) (y = (f x))). Qed.
Lemma lem3564390 {_91401 : Type'} (g : _91401) (x : _91401) : (g = x) = (g = x).
Proof. exact (eq_refl (g = x)). Qed.
Lemma lem3564395 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (g : _91401) (x : _91401) : (term320 _91401 _91404 s y f g x) = (term321 _91401 _91404 s y f g x).
Proof. exact (@lem17362 (term55 _91401 _91404 s y f x) (g = x)). Qed.
Lemma lem3564396 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3564397 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401) : (term56 _91401 _91404 s y f x) = (term57 _91401 _91404 s y f x).
Proof. exact (MK_COMB (@lem3564396) (@lem3564385 _91401 _91404 s y f x)). Qed.
Lemma lem3564398 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (g : _91401) (x : _91401) : (term322 _91401 _91404 s y f g x) = (term323 _91401 _91404 s y f g x).
Proof. exact (MK_COMB (@lem3564397 _91401 _91404 s y f x) (@lem3564390 _91401 g x)). Qed.
Lemma lem3564399 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (g : _91401) (x : _91401) : (term280 _91401 _91404 s y f g x) = (term322 _91401 _91404 s y f g x).
Proof. exact (@lem17265 (term55 _91401 _91404 s y f x) (g = x)). Qed.
Lemma lem3564400 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (g : _91401) (x : _91401) : (term280 _91401 _91404 s y f g x) = (term323 _91401 _91404 s y f g x).
Proof. exact (TRANS (@lem3564399 _91401 _91404 s y f g x) (@lem3564398 _91401 _91404 s y f g x)). Qed.
Lemma lem3564401 {_91401 : Type'} (P : _91401 -> Prop) : (term40 _91401 P) = (term41 _91401 P).
Proof. exact (@lem18392 _91401 P). Qed.
Lemma lem3564402 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (g : _91401) : (term324 _91401 _91404 s y f g) = (term325 _91401 _91404 s y f g).
Proof. exact (@lem3564401 _91401 (term281 _91401 _91404 s y f g)). Qed.
Lemma lem3564403 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (g : _91401) (x : _91401) : (term326 _91401 _91404 s y f g x) = (term280 _91401 _91404 s y f g x).
Proof. exact (eq_refl (term326 _91401 _91404 s y f g x)). Qed.
Lemma lem3564404 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3564405 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (g : _91401) (x : _91401) : (term327 _91401 _91404 s y f g x) = (term320 _91401 _91404 s y f g x).
Proof. exact (MK_COMB (@lem3564404) (@lem3564403 _91401 _91404 s y f g x)). Qed.
Lemma lem3564406 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (g : _91401) (x : _91401) : (term327 _91401 _91404 s y f g x) = (term321 _91401 _91404 s y f g x).
Proof. exact (TRANS (@lem3564405 _91401 _91404 s y f g x) (@lem3564395 _91401 _91404 s y f g x)). Qed.
Lemma lem3564407 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (g : _91401) : (term328 _91401 _91404 s y f g) = (term329 _91401 _91404 s y f g).
Proof. exact (fun_ext (fun x : _91401 => @lem3564406 _91401 _91404 s y f g x)). Qed.
Lemma lem3564408 {_91401 : Type'} : (@ex _91401) = (@ex _91401).
Proof. exact (eq_refl (@ex _91401)). Qed.
Lemma lem3564409 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (g : _91401) : (term325 _91401 _91404 s y f g) = (term330 _91401 _91404 s y f g).
Proof. exact (MK_COMB (@lem3564408 _91401) (@lem3564407 _91401 _91404 s y f g)). Qed.
Lemma lem3564410 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (g : _91401) : (term324 _91401 _91404 s y f g) = (term330 _91401 _91404 s y f g).
Proof. exact (TRANS (@lem3564402 _91401 _91404 s y f g) (@lem3564409 _91401 _91404 s y f g)). Qed.
Lemma lem3564411 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (g : _91401) : (term281 _91401 _91404 s y f g) = (term331 _91401 _91404 s y f g).
Proof. exact (fun_ext (fun x : _91401 => @lem3564400 _91401 _91404 s y f g x)). Qed.
Lemma lem3564412 {_91401 : Type'} : (@all _91401) = (@all _91401).
Proof. exact (eq_refl (@all _91401)). Qed.
Lemma lem3564413 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (g : _91401) : (term257 _91401 _91404 s y f g) = (term332 _91401 _91404 s y f g).
Proof. exact (MK_COMB (@lem3564412 _91401) (@lem3564411 _91401 _91404 s y f g)). Qed.
Lemma lem3564414 {_91401 : Type'} (P : _91401 -> Prop) : (term333 _91401 P) = (term334 _91401 P).
Proof. exact (@lem18394 _91401 P). Qed.
Lemma lem3564415 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term335 _91401 _91404 s y f) = (term336 _91401 _91404 s y f).
Proof. exact (@lem3564414 _91401 (term247 _91401 _91404 s y f)). Qed.
Lemma lem3564416 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (g : _91401) : (term256 _91401 _91404 s y f g) = (term257 _91401 _91404 s y f g).
Proof. exact (eq_refl (term256 _91401 _91404 s y f g)). Qed.
Lemma lem3564417 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3564418 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (g : _91401) : (term337 _91401 _91404 s y f g) = (term324 _91401 _91404 s y f g).
Proof. exact (MK_COMB (@lem3564417) (@lem3564416 _91401 _91404 s y f g)). Qed.
Lemma lem3564419 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (g : _91401) : (term337 _91401 _91404 s y f g) = (term330 _91401 _91404 s y f g).
Proof. exact (TRANS (@lem3564418 _91401 _91404 s y f g) (@lem3564410 _91401 _91404 s y f g)). Qed.
Lemma lem3564420 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term338 _91401 _91404 s y f) = (term339 _91401 _91404 s y f).
Proof. exact (fun_ext (fun g : _91401 => @lem3564419 _91401 _91404 s y f g)). Qed.
Lemma lem3564421 {_91401 : Type'} : (@all _91401) = (@all _91401).
Proof. exact (eq_refl (@all _91401)). Qed.
Lemma lem3564422 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term336 _91401 _91404 s y f) = (term340 _91401 _91404 s y f).
Proof. exact (MK_COMB (@lem3564421 _91401) (@lem3564420 _91401 _91404 s y f)). Qed.
Lemma lem3564423 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term335 _91401 _91404 s y f) = (term340 _91401 _91404 s y f).
Proof. exact (TRANS (@lem3564415 _91401 _91404 s y f) (@lem3564422 _91401 _91404 s y f)). Qed.
Lemma lem3564424 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term247 _91401 _91404 s y f) = (term341 _91401 _91404 s y f).
Proof. exact (fun_ext (fun g : _91401 => @lem3564413 _91401 _91404 s y f g)). Qed.
Lemma lem3564425 {_91401 : Type'} : (@ex _91401) = (@ex _91401).
Proof. exact (eq_refl (@ex _91401)). Qed.
Lemma lem3564426 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term260 _91401 _91404 s y f) = (term342 _91401 _91404 s y f).
Proof. exact (MK_COMB (@lem3564425 _91401) (@lem3564424 _91401 _91404 s y f)). Qed.
Lemma lem3564427 {_91404 : Type'} (P : _91404 -> Prop) : (term40 _91404 P) = (term41 _91404 P).
Proof. exact (@lem18392 _91404 P). Qed.
Lemma lem3564428 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term343 _91401 _91404 s f) = (term344 _91401 _91404 s f).
Proof. exact (@lem3564427 _91404 (term262 _91401 _91404 s f)). Qed.
Lemma lem3564429 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term345 _91401 _91404 s f y) = (term260 _91401 _91404 s y f).
Proof. exact (eq_refl (term345 _91401 _91404 s f y)). Qed.
Lemma lem3564430 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3564431 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term346 _91401 _91404 s f y) = (term335 _91401 _91404 s y f).
Proof. exact (MK_COMB (@lem3564430) (@lem3564429 _91401 _91404 s y f)). Qed.
Lemma lem3564432 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term346 _91401 _91404 s f y) = (term340 _91401 _91404 s y f).
Proof. exact (TRANS (@lem3564431 _91401 _91404 s y f) (@lem3564423 _91401 _91404 s y f)). Qed.
Lemma lem3564433 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term347 _91401 _91404 s f) = (term348 _91401 _91404 s f).
Proof. exact (fun_ext (fun y : _91404 => @lem3564432 _91401 _91404 s y f)). Qed.
Lemma lem3564434 {_91404 : Type'} : (@ex _91404) = (@ex _91404).
Proof. exact (eq_refl (@ex _91404)). Qed.
Lemma lem3564435 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term344 _91401 _91404 s f) = (term349 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564434 _91404) (@lem3564433 _91401 _91404 s f)). Qed.
Lemma lem3564436 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term343 _91401 _91404 s f) = (term349 _91401 _91404 s f).
Proof. exact (TRANS (@lem3564428 _91401 _91404 s f) (@lem3564435 _91401 _91404 s f)). Qed.
Lemma lem3564437 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term262 _91401 _91404 s f) = (term350 _91401 _91404 s f).
Proof. exact (fun_ext (fun y : _91404 => @lem3564426 _91401 _91404 s y f)). Qed.
Lemma lem3564438 {_91404 : Type'} : (@all _91404) = (@all _91404).
Proof. exact (eq_refl (@all _91404)). Qed.
Lemma lem3564439 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term263 _91401 _91404 s f) = (term351 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564438 _91404) (@lem3564437 _91401 _91404 s f)). Qed.
Lemma lem3564440 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3564441 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term352 _91401 _91404 s f) = (term353 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564440) (@lem3564373 _91401 _91404 s f)). Qed.
Lemma lem3564442 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term354 _91401 _91404 s f) = (term355 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564441 _91401 _91404 s f) (@lem3564439 _91401 _91404 s f)). Qed.
Lemma lem3564443 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3564444 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term356 _91401 _91404 s f) = (term357 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564443) (@lem3564376 _91401 _91404 s f)). Qed.
Lemma lem3564445 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term358 _91401 _91404 s f) = (term359 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564444 _91401 _91404 s f) (@lem3564436 _91401 _91404 s f)). Qed.
Lemma lem3564446 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3564447 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term360 _91401 _91404 s f) = (term361 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564446) (@lem3564445 _91401 _91404 s f)). Qed.
Lemma lem3564448 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term362 _91401 _91404 s f) = (term363 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564447 _91401 _91404 s f) (@lem3564442 _91401 _91404 s f)). Qed.
Lemma lem3564449 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term287 _91401 _91404 s f) = (term362 _91401 _91404 s f).
Proof. exact (@lem17646 (term265 _91401 _91404 s f) (term263 _91401 _91404 s f)). Qed.
Lemma lem3564450 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term287 _91401 _91404 s f) = (term363 _91401 _91404 s f).
Proof. exact (TRANS (@lem3564449 _91401 _91404 s f) (@lem3564448 _91401 _91404 s f)). Qed.
Lemma lem3564669 {A B : Type'} (P : type1413 A B) : (term230 A B P) = (term231 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3564670 {_91401 : Type'} (P : type1402 _91401) : (term364 _91401 P) = (term365 _91401 P).
Proof. exact (@lem3564669 _91401 _91401 P). Qed.
Lemma lem3564671 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term366 _91401 _91404 s y f) = (term367 _91401 _91404 s y f).
Proof. exact (@lem3564670 _91401 (term368 _91401 _91404 s y f)). Qed.
Lemma lem3564672 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (g : _91401) : (term369 _91401 _91404 s y f g) = (term329 _91401 _91404 s y f g).
Proof. exact (eq_refl (term369 _91401 _91404 s y f g)). Qed.
Lemma lem3564673 {_91401 : Type'} (x : _91401) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3564674 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (g : _91401) (x : _91401) : (term370 _91401 _91404 s y f g x) = (term371 _91401 _91404 s y f g x).
Proof. exact (MK_COMB (@lem3564672 _91401 _91404 s y f g) (@lem3564673 _91401 x)). Qed.
Lemma lem3564675 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (g : _91401) (x : _91401) : (term371 _91401 _91404 s y f g x) = (term321 _91401 _91404 s y f g x).
Proof. exact (eq_refl (term371 _91401 _91404 s y f g x)). Qed.
Lemma lem3564676 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (g : _91401) (x : _91401) : (term370 _91401 _91404 s y f g x) = (term321 _91401 _91404 s y f g x).
Proof. exact (TRANS (@lem3564674 _91401 _91404 s y f g x) (@lem3564675 _91401 _91404 s y f g x)). Qed.
Lemma lem3564677 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (g : _91401) : (term372 _91401 _91404 s y f g) = (term329 _91401 _91404 s y f g).
Proof. exact (fun_ext (fun x : _91401 => @lem3564676 _91401 _91404 s y f g x)). Qed.
Lemma lem3564678 {_91401 : Type'} : (@ex _91401) = (@ex _91401).
Proof. exact (eq_refl (@ex _91401)). Qed.
Lemma lem3564679 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (g : _91401) : (term373 _91401 _91404 s y f g) = (term330 _91401 _91404 s y f g).
Proof. exact (MK_COMB (@lem3564678 _91401) (@lem3564677 _91401 _91404 s y f g)). Qed.
Lemma lem3564680 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term374 _91401 _91404 s y f) = (term339 _91401 _91404 s y f).
Proof. exact (fun_ext (fun g : _91401 => @lem3564679 _91401 _91404 s y f g)). Qed.
Lemma lem3564681 {_91401 : Type'} : (@all _91401) = (@all _91401).
Proof. exact (eq_refl (@all _91401)). Qed.
Lemma lem3564682 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term366 _91401 _91404 s y f) = (term340 _91401 _91404 s y f).
Proof. exact (MK_COMB (@lem3564681 _91401) (@lem3564680 _91401 _91404 s y f)). Qed.
Lemma lem3564683 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3564684 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term375 _91401 _91404 s y f) = (term376 _91401 _91404 s y f).
Proof. exact (MK_COMB (@lem3564683) (@lem3564682 _91401 _91404 s y f)). Qed.
Lemma lem3564685 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (g : _91401) : (term369 _91401 _91404 s y f g) = (term329 _91401 _91404 s y f g).
Proof. exact (eq_refl (term369 _91401 _91404 s y f g)). Qed.
Lemma lem3564686 {_91401 : Type'} (x : _91401 -> _91401) (g : _91401) : (x g) = (x g).
Proof. exact (eq_refl (x g)). Qed.
Lemma lem3564687 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (g : _91401) : (term377 _91401 _91404 s y f x g) = (term378 _91401 _91404 s y f x g).
Proof. exact (MK_COMB (@lem3564685 _91401 _91404 s y f g) (@lem3564686 _91401 x g)). Qed.
Lemma lem3564688 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (g : _91401) : (term378 _91401 _91404 s y f x g) = (term379 _91401 _91404 s y f x g).
Proof. exact (eq_refl (term378 _91401 _91404 s y f x g)). Qed.
Lemma lem3564689 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (g : _91401) : (term377 _91401 _91404 s y f x g) = (term379 _91401 _91404 s y f x g).
Proof. exact (TRANS (@lem3564687 _91401 _91404 s y f x g) (@lem3564688 _91401 _91404 s y f x g)). Qed.
Lemma lem3564690 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) : (term380 _91401 _91404 s y f x) = (term381 _91401 _91404 s y f x).
Proof. exact (fun_ext (fun g : _91401 => @lem3564689 _91401 _91404 s y f x g)). Qed.
Lemma lem3564691 {_91401 : Type'} : (@all _91401) = (@all _91401).
Proof. exact (eq_refl (@all _91401)). Qed.
Lemma lem3564692 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) : (term382 _91401 _91404 s y f x) = (term383 _91401 _91404 s y f x).
Proof. exact (MK_COMB (@lem3564691 _91401) (@lem3564690 _91401 _91404 s y f x)). Qed.
Lemma lem3564693 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term384 _91401 _91404 s y f) = (term385 _91401 _91404 s y f).
Proof. exact (fun_ext (fun x : _91401 -> _91401 => @lem3564692 _91401 _91404 s y f x)). Qed.
Lemma lem3564694 {_91401 : Type'} : (@ex (_91401 -> _91401)) = (@ex (_91401 -> _91401)).
Proof. exact (eq_refl (@ex (_91401 -> _91401))). Qed.
Lemma lem3564695 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term367 _91401 _91404 s y f) = (term386 _91401 _91404 s y f).
Proof. exact (MK_COMB (@lem3564694 _91401) (@lem3564693 _91401 _91404 s y f)). Qed.
Lemma lem3564696 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : ((term366 _91401 _91404 s y f) = (term367 _91401 _91404 s y f)) = ((term340 _91401 _91404 s y f) = (term386 _91401 _91404 s y f)).
Proof. exact (MK_COMB (@lem3564684 _91401 _91404 s y f) (@lem3564695 _91401 _91404 s y f)). Qed.
Lemma lem3564697 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term340 _91401 _91404 s y f) = (term386 _91401 _91404 s y f).
Proof. exact (EQ_MP (@lem3564696 _91401 _91404 s y f) (@lem3564671 _91401 _91404 s y f)). Qed.
Lemma lem3564698 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term348 _91401 _91404 s f) = (term387 _91401 _91404 s f).
Proof. exact (fun_ext (fun y : _91404 => @lem3564697 _91401 _91404 s y f)). Qed.
Lemma lem3564699 {_91404 : Type'} : (@ex _91404) = (@ex _91404).
Proof. exact (eq_refl (@ex _91404)). Qed.
Lemma lem3564700 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term349 _91401 _91404 s f) = (term388 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564699 _91404) (@lem3564698 _91401 _91404 s f)). Qed.
Lemma lem3564701 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term357 _91401 _91404 s f) = (term357 _91401 _91404 s f).
Proof. exact (eq_refl (term357 _91401 _91404 s f)). Qed.
Lemma lem3564702 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term359 _91401 _91404 s f) = (term389 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564701 _91401 _91404 s f) (@lem3564700 _91401 _91404 s f)). Qed.
Lemma lem3564704 {A : Type'} (P : Prop) (Q : A -> Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3564705 {_91404 : Type'} (P : Prop) (Q : _91404 -> Prop) : (term90 _91404 P Q) = (term91 _91404 P Q).
Proof. exact (@lem3564704 _91404 P Q). Qed.
Lemma lem3564706 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term390 _91401 _91404 s f) = (term391 _91401 _91404 s f).
Proof. exact (@lem3564705 _91404 (term319 _91401 _91404 s f) (term387 _91401 _91404 s f)). Qed.
Lemma lem3564707 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term392 _91401 _91404 s f y) = (term386 _91401 _91404 s y f).
Proof. exact (eq_refl (term392 _91401 _91404 s f y)). Qed.
Lemma lem3564708 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term393 _91401 _91404 s f) = (term387 _91401 _91404 s f).
Proof. exact (fun_ext (fun y : _91404 => @lem3564707 _91401 _91404 s y f)). Qed.
Lemma lem3564709 {_91404 : Type'} : (@ex _91404) = (@ex _91404).
Proof. exact (eq_refl (@ex _91404)). Qed.
Lemma lem3564710 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term394 _91401 _91404 s f) = (term388 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564709 _91404) (@lem3564708 _91401 _91404 s f)). Qed.
Lemma lem3564711 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term357 _91401 _91404 s f) = (term357 _91401 _91404 s f).
Proof. exact (eq_refl (term357 _91401 _91404 s f)). Qed.
Lemma lem3564712 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term390 _91401 _91404 s f) = (term389 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564711 _91401 _91404 s f) (@lem3564710 _91401 _91404 s f)). Qed.
Lemma lem3564713 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3564714 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term395 _91401 _91404 s f) = (term396 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564713) (@lem3564712 _91401 _91404 s f)). Qed.
Lemma lem3564715 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term392 _91401 _91404 s f y) = (term386 _91401 _91404 s y f).
Proof. exact (eq_refl (term392 _91401 _91404 s f y)). Qed.
Lemma lem3564716 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term357 _91401 _91404 s f) = (term357 _91401 _91404 s f).
Proof. exact (eq_refl (term357 _91401 _91404 s f)). Qed.
Lemma lem3564717 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term397 _91401 _91404 s f y) = (term398 _91401 _91404 s y f).
Proof. exact (MK_COMB (@lem3564716 _91401 _91404 s f) (@lem3564715 _91401 _91404 s y f)). Qed.
Lemma lem3564718 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term399 _91401 _91404 s f) = (term400 _91401 _91404 s f).
Proof. exact (fun_ext (fun y : _91404 => @lem3564717 _91401 _91404 s y f)). Qed.
Lemma lem3564719 {_91404 : Type'} : (@ex _91404) = (@ex _91404).
Proof. exact (eq_refl (@ex _91404)). Qed.
Lemma lem3564720 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term391 _91401 _91404 s f) = (term401 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564719 _91404) (@lem3564718 _91401 _91404 s f)). Qed.
Lemma lem3564721 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : ((term390 _91401 _91404 s f) = (term391 _91401 _91404 s f)) = ((term389 _91401 _91404 s f) = (term401 _91401 _91404 s f)).
Proof. exact (MK_COMB (@lem3564714 _91401 _91404 s f) (@lem3564720 _91401 _91404 s f)). Qed.
Lemma lem3564722 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term389 _91401 _91404 s f) = (term401 _91401 _91404 s f).
Proof. exact (EQ_MP (@lem3564721 _91401 _91404 s f) (@lem3564706 _91401 _91404 s f)). Qed.
Lemma lem3564724 {A : Type'} (P : Prop) (Q : A -> Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3564725 {_91401 : Type'} (P : Prop) (Q : type488 _91401) : (term402 _91401 P Q) = (term403 _91401 P Q).
Proof. exact (@lem3564724 (_91401 -> _91401) P Q). Qed.
Lemma lem3564726 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term404 _91401 _91404 s y f) = (term405 _91401 _91404 s y f).
Proof. exact (@lem3564725 _91401 (term319 _91401 _91404 s f) (term385 _91401 _91404 s y f)). Qed.
Lemma lem3564727 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) : (term406 _91401 _91404 s y f x) = (term383 _91401 _91404 s y f x).
Proof. exact (eq_refl (term406 _91401 _91404 s y f x)). Qed.
Lemma lem3564728 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term407 _91401 _91404 s y f) = (term385 _91401 _91404 s y f).
Proof. exact (fun_ext (fun x : _91401 -> _91401 => @lem3564727 _91401 _91404 s y f x)). Qed.
Lemma lem3564729 {_91401 : Type'} : (@ex (_91401 -> _91401)) = (@ex (_91401 -> _91401)).
Proof. exact (eq_refl (@ex (_91401 -> _91401))). Qed.
Lemma lem3564730 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term408 _91401 _91404 s y f) = (term386 _91401 _91404 s y f).
Proof. exact (MK_COMB (@lem3564729 _91401) (@lem3564728 _91401 _91404 s y f)). Qed.
Lemma lem3564731 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term357 _91401 _91404 s f) = (term357 _91401 _91404 s f).
Proof. exact (eq_refl (term357 _91401 _91404 s f)). Qed.
Lemma lem3564732 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term404 _91401 _91404 s y f) = (term398 _91401 _91404 s y f).
Proof. exact (MK_COMB (@lem3564731 _91401 _91404 s f) (@lem3564730 _91401 _91404 s y f)). Qed.
Lemma lem3564733 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3564734 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term409 _91401 _91404 s y f) = (term410 _91401 _91404 s y f).
Proof. exact (MK_COMB (@lem3564733) (@lem3564732 _91401 _91404 s y f)). Qed.
Lemma lem3564735 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) : (term406 _91401 _91404 s y f x) = (term383 _91401 _91404 s y f x).
Proof. exact (eq_refl (term406 _91401 _91404 s y f x)). Qed.
Lemma lem3564736 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term357 _91401 _91404 s f) = (term357 _91401 _91404 s f).
Proof. exact (eq_refl (term357 _91401 _91404 s f)). Qed.
Lemma lem3564737 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) : (term411 _91401 _91404 s y f x) = (term412 _91401 _91404 s y f x).
Proof. exact (MK_COMB (@lem3564736 _91401 _91404 s f) (@lem3564735 _91401 _91404 s y f x)). Qed.
Lemma lem3564738 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term413 _91401 _91404 s y f) = (term414 _91401 _91404 s y f).
Proof. exact (fun_ext (fun x : _91401 -> _91401 => @lem3564737 _91401 _91404 s y f x)). Qed.
Lemma lem3564739 {_91401 : Type'} : (@ex (_91401 -> _91401)) = (@ex (_91401 -> _91401)).
Proof. exact (eq_refl (@ex (_91401 -> _91401))). Qed.
Lemma lem3564740 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term405 _91401 _91404 s y f) = (term415 _91401 _91404 s y f).
Proof. exact (MK_COMB (@lem3564739 _91401) (@lem3564738 _91401 _91404 s y f)). Qed.
Lemma lem3564741 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : ((term404 _91401 _91404 s y f) = (term405 _91401 _91404 s y f)) = ((term398 _91401 _91404 s y f) = (term415 _91401 _91404 s y f)).
Proof. exact (MK_COMB (@lem3564734 _91401 _91404 s y f) (@lem3564740 _91401 _91404 s y f)). Qed.
Lemma lem3564742 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term398 _91401 _91404 s y f) = (term415 _91401 _91404 s y f).
Proof. exact (EQ_MP (@lem3564741 _91401 _91404 s y f) (@lem3564726 _91401 _91404 s y f)). Qed.
Lemma lem3564743 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term400 _91401 _91404 s f) = (term416 _91401 _91404 s f).
Proof. exact (fun_ext (fun y : _91404 => @lem3564742 _91401 _91404 s y f)). Qed.
Lemma lem3564744 {_91404 : Type'} : (@ex _91404) = (@ex _91404).
Proof. exact (eq_refl (@ex _91404)). Qed.
Lemma lem3564745 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term401 _91401 _91404 s f) = (term417 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564744 _91404) (@lem3564743 _91401 _91404 s f)). Qed.
Lemma lem3564746 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term389 _91401 _91404 s f) = (term417 _91401 _91404 s f).
Proof. exact (TRANS (@lem3564722 _91401 _91404 s f) (@lem3564745 _91401 _91404 s f)). Qed.
Lemma lem3564747 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term359 _91401 _91404 s f) = (term417 _91401 _91404 s f).
Proof. exact (TRANS (@lem3564702 _91401 _91404 s f) (@lem3564746 _91401 _91404 s f)). Qed.
Lemma lem3564748 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3564749 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term361 _91401 _91404 s f) = (term418 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564748) (@lem3564747 _91401 _91404 s f)). Qed.
Lemma lem3564751 {A B : Type'} (P : type1413 A B) : (term230 A B P) = (term231 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3564752 {_91401 _91404 : Type'} (P : type1470 _91401 _91404) : (term242 _91401 _91404 P) = (term241 _91401 _91404 P).
Proof. exact (@lem3564751 _91404 _91401 P). Qed.
Lemma lem3564753 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term419 _91401 _91404 s f) = (term420 _91401 _91404 s f).
Proof. exact (@lem3564752 _91401 _91404 (term421 _91401 _91404 s f)). Qed.
Lemma lem3564754 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term422 _91401 _91404 s f y) = (term341 _91401 _91404 s y f).
Proof. exact (eq_refl (term422 _91401 _91404 s f y)). Qed.
Lemma lem3564755 {_91401 : Type'} (g : _91401) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem3564756 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (g : _91401) : (term423 _91401 _91404 s f y g) = (term424 _91401 _91404 s y f g).
Proof. exact (MK_COMB (@lem3564754 _91401 _91404 s y f) (@lem3564755 _91401 g)). Qed.
Lemma lem3564757 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (g : _91401) : (term424 _91401 _91404 s y f g) = (term332 _91401 _91404 s y f g).
Proof. exact (eq_refl (term424 _91401 _91404 s y f g)). Qed.
Lemma lem3564758 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (g : _91401) : (term423 _91401 _91404 s f y g) = (term332 _91401 _91404 s y f g).
Proof. exact (TRANS (@lem3564756 _91401 _91404 s y f g) (@lem3564757 _91401 _91404 s y f g)). Qed.
Lemma lem3564759 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term425 _91401 _91404 s f y) = (term341 _91401 _91404 s y f).
Proof. exact (fun_ext (fun g : _91401 => @lem3564758 _91401 _91404 s y f g)). Qed.
Lemma lem3564760 {_91401 : Type'} : (@ex _91401) = (@ex _91401).
Proof. exact (eq_refl (@ex _91401)). Qed.
Lemma lem3564761 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term426 _91401 _91404 s f y) = (term342 _91401 _91404 s y f).
Proof. exact (MK_COMB (@lem3564760 _91401) (@lem3564759 _91401 _91404 s y f)). Qed.
Lemma lem3564762 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term427 _91401 _91404 s f) = (term350 _91401 _91404 s f).
Proof. exact (fun_ext (fun y : _91404 => @lem3564761 _91401 _91404 s y f)). Qed.
Lemma lem3564763 {_91404 : Type'} : (@all _91404) = (@all _91404).
Proof. exact (eq_refl (@all _91404)). Qed.
Lemma lem3564764 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term419 _91401 _91404 s f) = (term351 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564763 _91404) (@lem3564762 _91401 _91404 s f)). Qed.
Lemma lem3564765 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3564766 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term428 _91401 _91404 s f) = (term429 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564765) (@lem3564764 _91401 _91404 s f)). Qed.
Lemma lem3564767 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term422 _91401 _91404 s f y) = (term341 _91401 _91404 s y f).
Proof. exact (eq_refl (term422 _91401 _91404 s f y)). Qed.
Lemma lem3564768 {_91401 _91404 : Type'} (g : _91404 -> _91401) (y : _91404) : (g y) = (g y).
Proof. exact (eq_refl (g y)). Qed.
Lemma lem3564769 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (y : _91404) : (term430 _91401 _91404 s f g y) = (term431 _91401 _91404 s f g y).
Proof. exact (MK_COMB (@lem3564767 _91401 _91404 s y f) (@lem3564768 _91401 _91404 g y)). Qed.
Lemma lem3564770 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (y : _91404) : (term431 _91401 _91404 s f g y) = (term68 _91401 _91404 s f g y).
Proof. exact (eq_refl (term431 _91401 _91404 s f g y)). Qed.
Lemma lem3564771 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (y : _91404) : (term430 _91401 _91404 s f g y) = (term68 _91401 _91404 s f g y).
Proof. exact (TRANS (@lem3564769 _91401 _91404 s f g y) (@lem3564770 _91401 _91404 s f g y)). Qed.
Lemma lem3564772 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) : (term432 _91401 _91404 s f g) = (term76 _91401 _91404 s f g).
Proof. exact (fun_ext (fun y : _91404 => @lem3564771 _91401 _91404 s f g y)). Qed.
Lemma lem3564773 {_91404 : Type'} : (@all _91404) = (@all _91404).
Proof. exact (eq_refl (@all _91404)). Qed.
Lemma lem3564774 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) : (term433 _91401 _91404 s f g) = (term77 _91401 _91404 s f g).
Proof. exact (MK_COMB (@lem3564773 _91404) (@lem3564772 _91401 _91404 s f g)). Qed.
Lemma lem3564775 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term434 _91401 _91404 s f) = (term435 _91401 _91404 s f).
Proof. exact (fun_ext (fun g : _91404 -> _91401 => @lem3564774 _91401 _91404 s f g)). Qed.
Lemma lem3564776 {_91401 _91404 : Type'} : (@ex (_91404 -> _91401)) = (@ex (_91404 -> _91401)).
Proof. exact (eq_refl (@ex (_91404 -> _91401))). Qed.
Lemma lem3564777 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term420 _91401 _91404 s f) = (term436 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564776 _91401 _91404) (@lem3564775 _91401 _91404 s f)). Qed.
Lemma lem3564778 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : ((term419 _91401 _91404 s f) = (term420 _91401 _91404 s f)) = ((term351 _91401 _91404 s f) = (term436 _91401 _91404 s f)).
Proof. exact (MK_COMB (@lem3564766 _91401 _91404 s f) (@lem3564777 _91401 _91404 s f)). Qed.
Lemma lem3564779 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term351 _91401 _91404 s f) = (term436 _91401 _91404 s f).
Proof. exact (EQ_MP (@lem3564778 _91401 _91404 s f) (@lem3564753 _91401 _91404 s f)). Qed.
Lemma lem3564780 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term353 _91401 _91404 s f) = (term353 _91401 _91404 s f).
Proof. exact (eq_refl (term353 _91401 _91404 s f)). Qed.
Lemma lem3564781 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term355 _91401 _91404 s f) = (term437 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564780 _91401 _91404 s f) (@lem3564779 _91401 _91404 s f)). Qed.
Lemma lem3564783 {A : Type'} (P : A -> Prop) (Q : Prop) : (term119 A P Q) = (term120 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3564784 {_91401 : Type'} (P : _91401 -> Prop) (Q : Prop) : (term119 _91401 P Q) = (term120 _91401 P Q).
Proof. exact (@lem3564783 _91401 P Q). Qed.
Lemma lem3564785 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term438 _91401 _91404 s f) = (term439 _91401 _91404 s f).
Proof. exact (@lem3564784 _91401 (term316 _91401 _91404 s f) (term436 _91401 _91404 s f)). Qed.
Lemma lem3564786 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) : (term440 _91401 _91404 s f x) = (term308 _91401 _91404 s f x).
Proof. exact (eq_refl (term440 _91401 _91404 s f x)). Qed.
Lemma lem3564787 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term441 _91401 _91404 s f) = (term316 _91401 _91404 s f).
Proof. exact (fun_ext (fun x : _91401 => @lem3564786 _91401 _91404 s f x)). Qed.
Lemma lem3564788 {_91401 : Type'} : (@ex _91401) = (@ex _91401).
Proof. exact (eq_refl (@ex _91401)). Qed.
Lemma lem3564789 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term442 _91401 _91404 s f) = (term317 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564788 _91401) (@lem3564787 _91401 _91404 s f)). Qed.
Lemma lem3564790 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3564791 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term443 _91401 _91404 s f) = (term353 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564790) (@lem3564789 _91401 _91404 s f)). Qed.
Lemma lem3564792 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term436 _91401 _91404 s f) = (term436 _91401 _91404 s f).
Proof. exact (eq_refl (term436 _91401 _91404 s f)). Qed.
Lemma lem3564793 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term438 _91401 _91404 s f) = (term437 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564791 _91401 _91404 s f) (@lem3564792 _91401 _91404 s f)). Qed.
Lemma lem3564794 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3564795 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term444 _91401 _91404 s f) = (term445 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564794) (@lem3564793 _91401 _91404 s f)). Qed.
Lemma lem3564796 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) : (term440 _91401 _91404 s f x) = (term308 _91401 _91404 s f x).
Proof. exact (eq_refl (term440 _91401 _91404 s f x)). Qed.
Lemma lem3564797 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3564798 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) : (term446 _91401 _91404 s f x) = (term447 _91401 _91404 s f x).
Proof. exact (MK_COMB (@lem3564797) (@lem3564796 _91401 _91404 s f x)). Qed.
Lemma lem3564799 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term436 _91401 _91404 s f) = (term436 _91401 _91404 s f).
Proof. exact (eq_refl (term436 _91401 _91404 s f)). Qed.
Lemma lem3564800 {_91401 _91404 : Type'} (x : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term448 _91401 _91404 x s f) = (term449 _91401 _91404 x s f).
Proof. exact (MK_COMB (@lem3564798 _91401 _91404 s f x) (@lem3564799 _91401 _91404 s f)). Qed.
Lemma lem3564801 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term450 _91401 _91404 s f) = (term451 _91401 _91404 s f).
Proof. exact (fun_ext (fun x : _91401 => @lem3564800 _91401 _91404 x s f)). Qed.
Lemma lem3564802 {_91401 : Type'} : (@ex _91401) = (@ex _91401).
Proof. exact (eq_refl (@ex _91401)). Qed.
Lemma lem3564803 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term439 _91401 _91404 s f) = (term452 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564802 _91401) (@lem3564801 _91401 _91404 s f)). Qed.
Lemma lem3564804 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : ((term438 _91401 _91404 s f) = (term439 _91401 _91404 s f)) = ((term437 _91401 _91404 s f) = (term452 _91401 _91404 s f)).
Proof. exact (MK_COMB (@lem3564795 _91401 _91404 s f) (@lem3564803 _91401 _91404 s f)). Qed.
Lemma lem3564805 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term437 _91401 _91404 s f) = (term452 _91401 _91404 s f).
Proof. exact (EQ_MP (@lem3564804 _91401 _91404 s f) (@lem3564785 _91401 _91404 s f)). Qed.
Lemma lem3564807 {A : Type'} (P : A -> Prop) (Q : Prop) : (term119 A P Q) = (term120 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3564808 {_91401 : Type'} (P : _91401 -> Prop) (Q : Prop) : (term119 _91401 P Q) = (term120 _91401 P Q).
Proof. exact (@lem3564807 _91401 P Q). Qed.
Lemma lem3564809 {_91401 _91404 : Type'} (x : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term453 _91401 _91404 x s f) = (term454 _91401 _91404 x s f).
Proof. exact (@lem3564808 _91401 (term307 _91401 _91404 s f x) (term436 _91401 _91404 s f)). Qed.
Lemma lem3564810 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) (y : _91401) : (term455 _91401 _91404 s f x y) = (term296 _91401 _91404 s f x y).
Proof. exact (eq_refl (term455 _91401 _91404 s f x y)). Qed.
Lemma lem3564811 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) : (term456 _91401 _91404 s f x) = (term307 _91401 _91404 s f x).
Proof. exact (fun_ext (fun y : _91401 => @lem3564810 _91401 _91404 s f x y)). Qed.
Lemma lem3564812 {_91401 : Type'} : (@ex _91401) = (@ex _91401).
Proof. exact (eq_refl (@ex _91401)). Qed.
Lemma lem3564813 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) : (term457 _91401 _91404 s f x) = (term308 _91401 _91404 s f x).
Proof. exact (MK_COMB (@lem3564812 _91401) (@lem3564811 _91401 _91404 s f x)). Qed.
Lemma lem3564814 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3564815 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) : (term458 _91401 _91404 s f x) = (term447 _91401 _91404 s f x).
Proof. exact (MK_COMB (@lem3564814) (@lem3564813 _91401 _91404 s f x)). Qed.
Lemma lem3564816 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term436 _91401 _91404 s f) = (term436 _91401 _91404 s f).
Proof. exact (eq_refl (term436 _91401 _91404 s f)). Qed.
Lemma lem3564817 {_91401 _91404 : Type'} (x : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term453 _91401 _91404 x s f) = (term449 _91401 _91404 x s f).
Proof. exact (MK_COMB (@lem3564815 _91401 _91404 s f x) (@lem3564816 _91401 _91404 s f)). Qed.
Lemma lem3564818 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3564819 {_91401 _91404 : Type'} (x : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term459 _91401 _91404 x s f) = (term460 _91401 _91404 x s f).
Proof. exact (MK_COMB (@lem3564818) (@lem3564817 _91401 _91404 x s f)). Qed.
Lemma lem3564820 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) (y : _91401) : (term455 _91401 _91404 s f x y) = (term296 _91401 _91404 s f x y).
Proof. exact (eq_refl (term455 _91401 _91404 s f x y)). Qed.
Lemma lem3564821 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3564822 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) (y : _91401) : (term461 _91401 _91404 s f x y) = (term462 _91401 _91404 s f x y).
Proof. exact (MK_COMB (@lem3564821) (@lem3564820 _91401 _91404 s f x y)). Qed.
Lemma lem3564823 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term436 _91401 _91404 s f) = (term436 _91401 _91404 s f).
Proof. exact (eq_refl (term436 _91401 _91404 s f)). Qed.
Lemma lem3564824 {_91401 _91404 : Type'} (x : _91401) (y : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term463 _91401 _91404 x y s f) = (term464 _91401 _91404 x y s f).
Proof. exact (MK_COMB (@lem3564822 _91401 _91404 s f x y) (@lem3564823 _91401 _91404 s f)). Qed.
Lemma lem3564825 {_91401 _91404 : Type'} (x : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term465 _91401 _91404 x s f) = (term466 _91401 _91404 x s f).
Proof. exact (fun_ext (fun y : _91401 => @lem3564824 _91401 _91404 x y s f)). Qed.
Lemma lem3564826 {_91401 : Type'} : (@ex _91401) = (@ex _91401).
Proof. exact (eq_refl (@ex _91401)). Qed.
Lemma lem3564827 {_91401 _91404 : Type'} (x : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term454 _91401 _91404 x s f) = (term467 _91401 _91404 x s f).
Proof. exact (MK_COMB (@lem3564826 _91401) (@lem3564825 _91401 _91404 x s f)). Qed.
Lemma lem3564828 {_91401 _91404 : Type'} (x : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : ((term453 _91401 _91404 x s f) = (term454 _91401 _91404 x s f)) = ((term449 _91401 _91404 x s f) = (term467 _91401 _91404 x s f)).
Proof. exact (MK_COMB (@lem3564819 _91401 _91404 x s f) (@lem3564827 _91401 _91404 x s f)). Qed.
Lemma lem3564829 {_91401 _91404 : Type'} (x : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term449 _91401 _91404 x s f) = (term467 _91401 _91404 x s f).
Proof. exact (EQ_MP (@lem3564828 _91401 _91404 x s f) (@lem3564809 _91401 _91404 x s f)). Qed.
Lemma lem3564831 {A : Type'} (P : Prop) (Q : A -> Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3564832 {_91401 _91404 : Type'} (P : Prop) (Q : type805 _91401 _91404) : (term468 _91401 _91404 P Q) = (term469 _91401 _91404 P Q).
Proof. exact (@lem3564831 (_91404 -> _91401) P Q). Qed.
Lemma lem3564833 {_91401 _91404 : Type'} (x : _91401) (y : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term470 _91401 _91404 x y s f) = (term471 _91401 _91404 x y s f).
Proof. exact (@lem3564832 _91401 _91404 (term296 _91401 _91404 s f x y) (term435 _91401 _91404 s f)). Qed.
Lemma lem3564834 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) : (term472 _91401 _91404 s f g) = (term77 _91401 _91404 s f g).
Proof. exact (eq_refl (term472 _91401 _91404 s f g)). Qed.
Lemma lem3564835 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term473 _91401 _91404 s f) = (term435 _91401 _91404 s f).
Proof. exact (fun_ext (fun g : _91404 -> _91401 => @lem3564834 _91401 _91404 s f g)). Qed.
Lemma lem3564836 {_91401 _91404 : Type'} : (@ex (_91404 -> _91401)) = (@ex (_91404 -> _91401)).
Proof. exact (eq_refl (@ex (_91404 -> _91401))). Qed.
Lemma lem3564837 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term474 _91401 _91404 s f) = (term436 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564836 _91401 _91404) (@lem3564835 _91401 _91404 s f)). Qed.
Lemma lem3564838 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) (y : _91401) : (term462 _91401 _91404 s f x y) = (term462 _91401 _91404 s f x y).
Proof. exact (eq_refl (term462 _91401 _91404 s f x y)). Qed.
Lemma lem3564839 {_91401 _91404 : Type'} (x : _91401) (y : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term470 _91401 _91404 x y s f) = (term464 _91401 _91404 x y s f).
Proof. exact (MK_COMB (@lem3564838 _91401 _91404 s f x y) (@lem3564837 _91401 _91404 s f)). Qed.
Lemma lem3564840 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3564841 {_91401 _91404 : Type'} (x : _91401) (y : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term475 _91401 _91404 x y s f) = (term476 _91401 _91404 x y s f).
Proof. exact (MK_COMB (@lem3564840) (@lem3564839 _91401 _91404 x y s f)). Qed.
Lemma lem3564842 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) : (term472 _91401 _91404 s f g) = (term77 _91401 _91404 s f g).
Proof. exact (eq_refl (term472 _91401 _91404 s f g)). Qed.
Lemma lem3564843 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) (y : _91401) : (term462 _91401 _91404 s f x y) = (term462 _91401 _91404 s f x y).
Proof. exact (eq_refl (term462 _91401 _91404 s f x y)). Qed.
Lemma lem3564844 {_91401 _91404 : Type'} (x : _91401) (y : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) : (term477 _91401 _91404 x y s f g) = (term478 _91401 _91404 x y s f g).
Proof. exact (MK_COMB (@lem3564843 _91401 _91404 s f x y) (@lem3564842 _91401 _91404 s f g)). Qed.
Lemma lem3564845 {_91401 _91404 : Type'} (x : _91401) (y : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term479 _91401 _91404 x y s f) = (term480 _91401 _91404 x y s f).
Proof. exact (fun_ext (fun g : _91404 -> _91401 => @lem3564844 _91401 _91404 x y s f g)). Qed.
Lemma lem3564846 {_91401 _91404 : Type'} : (@ex (_91404 -> _91401)) = (@ex (_91404 -> _91401)).
Proof. exact (eq_refl (@ex (_91404 -> _91401))). Qed.
Lemma lem3564847 {_91401 _91404 : Type'} (x : _91401) (y : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term471 _91401 _91404 x y s f) = (term481 _91401 _91404 x y s f).
Proof. exact (MK_COMB (@lem3564846 _91401 _91404) (@lem3564845 _91401 _91404 x y s f)). Qed.
Lemma lem3564848 {_91401 _91404 : Type'} (x : _91401) (y : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : ((term470 _91401 _91404 x y s f) = (term471 _91401 _91404 x y s f)) = ((term464 _91401 _91404 x y s f) = (term481 _91401 _91404 x y s f)).
Proof. exact (MK_COMB (@lem3564841 _91401 _91404 x y s f) (@lem3564847 _91401 _91404 x y s f)). Qed.
Lemma lem3564849 {_91401 _91404 : Type'} (x : _91401) (y : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term464 _91401 _91404 x y s f) = (term481 _91401 _91404 x y s f).
Proof. exact (EQ_MP (@lem3564848 _91401 _91404 x y s f) (@lem3564833 _91401 _91404 x y s f)). Qed.
Lemma lem3564850 {_91401 _91404 : Type'} (x : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term466 _91401 _91404 x s f) = (term482 _91401 _91404 x s f).
Proof. exact (fun_ext (fun y : _91401 => @lem3564849 _91401 _91404 x y s f)). Qed.
Lemma lem3564851 {_91401 : Type'} : (@ex _91401) = (@ex _91401).
Proof. exact (eq_refl (@ex _91401)). Qed.
Lemma lem3564852 {_91401 _91404 : Type'} (x : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term467 _91401 _91404 x s f) = (term483 _91401 _91404 x s f).
Proof. exact (MK_COMB (@lem3564851 _91401) (@lem3564850 _91401 _91404 x s f)). Qed.
Lemma lem3564853 {_91401 _91404 : Type'} (x : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term449 _91401 _91404 x s f) = (term483 _91401 _91404 x s f).
Proof. exact (TRANS (@lem3564829 _91401 _91404 x s f) (@lem3564852 _91401 _91404 x s f)). Qed.
Lemma lem3564854 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term451 _91401 _91404 s f) = (term484 _91401 _91404 s f).
Proof. exact (fun_ext (fun x : _91401 => @lem3564853 _91401 _91404 x s f)). Qed.
Lemma lem3564855 {_91401 : Type'} : (@ex _91401) = (@ex _91401).
Proof. exact (eq_refl (@ex _91401)). Qed.
Lemma lem3564856 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term452 _91401 _91404 s f) = (term485 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564855 _91401) (@lem3564854 _91401 _91404 s f)). Qed.
Lemma lem3564857 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term437 _91401 _91404 s f) = (term485 _91401 _91404 s f).
Proof. exact (TRANS (@lem3564805 _91401 _91404 s f) (@lem3564856 _91401 _91404 s f)). Qed.
Lemma lem3564858 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term355 _91401 _91404 s f) = (term485 _91401 _91404 s f).
Proof. exact (TRANS (@lem3564781 _91401 _91404 s f) (@lem3564857 _91401 _91404 s f)). Qed.
Lemma lem3564859 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term363 _91401 _91404 s f) = (term486 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564749 _91401 _91404 s f) (@lem3564858 _91401 _91404 s f)). Qed.
Lemma lem3564863 {A : Type'} (P : A -> Prop) (Q : Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3564864 {_91404 : Type'} (P : _91404 -> Prop) (Q : Prop) : (term137 _91404 P Q) = (term138 _91404 P Q).
Proof. exact (@lem3564863 _91404 P Q). Qed.
Lemma lem3564865 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term487 _91401 _91404 s f) = (term488 _91401 _91404 s f).
Proof. exact (@lem3564864 _91404 (term416 _91401 _91404 s f) (term485 _91401 _91404 s f)). Qed.
Lemma lem3564866 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term489 _91401 _91404 s f y) = (term415 _91401 _91404 s y f).
Proof. exact (eq_refl (term489 _91401 _91404 s f y)). Qed.
Lemma lem3564867 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term490 _91401 _91404 s f) = (term416 _91401 _91404 s f).
Proof. exact (fun_ext (fun y : _91404 => @lem3564866 _91401 _91404 s y f)). Qed.
Lemma lem3564868 {_91404 : Type'} : (@ex _91404) = (@ex _91404).
Proof. exact (eq_refl (@ex _91404)). Qed.
Lemma lem3564869 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term491 _91401 _91404 s f) = (term417 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564868 _91404) (@lem3564867 _91401 _91404 s f)). Qed.
Lemma lem3564870 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3564871 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term492 _91401 _91404 s f) = (term418 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564870) (@lem3564869 _91401 _91404 s f)). Qed.
Lemma lem3564872 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term485 _91401 _91404 s f) = (term485 _91401 _91404 s f).
Proof. exact (eq_refl (term485 _91401 _91404 s f)). Qed.
Lemma lem3564873 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term487 _91401 _91404 s f) = (term486 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564871 _91401 _91404 s f) (@lem3564872 _91401 _91404 s f)). Qed.
Lemma lem3564874 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3564875 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term493 _91401 _91404 s f) = (term494 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564874) (@lem3564873 _91401 _91404 s f)). Qed.
Lemma lem3564876 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term489 _91401 _91404 s f y) = (term415 _91401 _91404 s y f).
Proof. exact (eq_refl (term489 _91401 _91404 s f y)). Qed.
Lemma lem3564877 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3564878 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term495 _91401 _91404 s f y) = (term496 _91401 _91404 s y f).
Proof. exact (MK_COMB (@lem3564877) (@lem3564876 _91401 _91404 s y f)). Qed.
Lemma lem3564879 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term485 _91401 _91404 s f) = (term485 _91401 _91404 s f).
Proof. exact (eq_refl (term485 _91401 _91404 s f)). Qed.
Lemma lem3564880 {_91401 _91404 : Type'} (y : _91404) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term497 _91401 _91404 y s f) = (term498 _91401 _91404 y s f).
Proof. exact (MK_COMB (@lem3564878 _91401 _91404 s y f) (@lem3564879 _91401 _91404 s f)). Qed.
Lemma lem3564881 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term499 _91401 _91404 s f) = (term500 _91401 _91404 s f).
Proof. exact (fun_ext (fun y : _91404 => @lem3564880 _91401 _91404 y s f)). Qed.
Lemma lem3564882 {_91404 : Type'} : (@ex _91404) = (@ex _91404).
Proof. exact (eq_refl (@ex _91404)). Qed.
Lemma lem3564883 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term488 _91401 _91404 s f) = (term501 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564882 _91404) (@lem3564881 _91401 _91404 s f)). Qed.
Lemma lem3564884 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : ((term487 _91401 _91404 s f) = (term488 _91401 _91404 s f)) = ((term486 _91401 _91404 s f) = (term501 _91401 _91404 s f)).
Proof. exact (MK_COMB (@lem3564875 _91401 _91404 s f) (@lem3564883 _91401 _91404 s f)). Qed.
Lemma lem3564885 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term486 _91401 _91404 s f) = (term501 _91401 _91404 s f).
Proof. exact (EQ_MP (@lem3564884 _91401 _91404 s f) (@lem3564865 _91401 _91404 s f)). Qed.
Lemma lem3564889 {A : Type'} (P : A -> Prop) (Q : Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3564890 {_91401 : Type'} (P : type488 _91401) (Q : Prop) : (term502 _91401 P Q) = (term503 _91401 P Q).
Proof. exact (@lem3564889 (_91401 -> _91401) P Q). Qed.
Lemma lem3564891 {_91401 _91404 : Type'} (y : _91404) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term504 _91401 _91404 y s f) = (term505 _91401 _91404 y s f).
Proof. exact (@lem3564890 _91401 (term414 _91401 _91404 s y f) (term485 _91401 _91404 s f)). Qed.
Lemma lem3564892 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) : (term506 _91401 _91404 s y f x) = (term412 _91401 _91404 s y f x).
Proof. exact (eq_refl (term506 _91401 _91404 s y f x)). Qed.
Lemma lem3564893 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term507 _91401 _91404 s y f) = (term414 _91401 _91404 s y f).
Proof. exact (fun_ext (fun x : _91401 -> _91401 => @lem3564892 _91401 _91404 s y f x)). Qed.
Lemma lem3564894 {_91401 : Type'} : (@ex (_91401 -> _91401)) = (@ex (_91401 -> _91401)).
Proof. exact (eq_refl (@ex (_91401 -> _91401))). Qed.
Lemma lem3564895 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term508 _91401 _91404 s y f) = (term415 _91401 _91404 s y f).
Proof. exact (MK_COMB (@lem3564894 _91401) (@lem3564893 _91401 _91404 s y f)). Qed.
Lemma lem3564896 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3564897 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) : (term509 _91401 _91404 s y f) = (term496 _91401 _91404 s y f).
Proof. exact (MK_COMB (@lem3564896) (@lem3564895 _91401 _91404 s y f)). Qed.
Lemma lem3564898 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term485 _91401 _91404 s f) = (term485 _91401 _91404 s f).
Proof. exact (eq_refl (term485 _91401 _91404 s f)). Qed.
Lemma lem3564899 {_91401 _91404 : Type'} (y : _91404) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term504 _91401 _91404 y s f) = (term498 _91401 _91404 y s f).
Proof. exact (MK_COMB (@lem3564897 _91401 _91404 s y f) (@lem3564898 _91401 _91404 s f)). Qed.
Lemma lem3564900 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3564901 {_91401 _91404 : Type'} (y : _91404) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term510 _91401 _91404 y s f) = (term511 _91401 _91404 y s f).
Proof. exact (MK_COMB (@lem3564900) (@lem3564899 _91401 _91404 y s f)). Qed.
Lemma lem3564902 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) : (term506 _91401 _91404 s y f x) = (term412 _91401 _91404 s y f x).
Proof. exact (eq_refl (term506 _91401 _91404 s y f x)). Qed.
Lemma lem3564903 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3564904 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) : (term512 _91401 _91404 s y f x) = (term513 _91401 _91404 s y f x).
Proof. exact (MK_COMB (@lem3564903) (@lem3564902 _91401 _91404 s y f x)). Qed.
Lemma lem3564905 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term485 _91401 _91404 s f) = (term485 _91401 _91404 s f).
Proof. exact (eq_refl (term485 _91401 _91404 s f)). Qed.
Lemma lem3564906 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term514 _91401 _91404 y x s f) = (term515 _91401 _91404 y x s f).
Proof. exact (MK_COMB (@lem3564904 _91401 _91404 s y f x) (@lem3564905 _91401 _91404 s f)). Qed.
Lemma lem3564907 {_91401 _91404 : Type'} (y : _91404) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term516 _91401 _91404 y s f) = (term517 _91401 _91404 y s f).
Proof. exact (fun_ext (fun x : _91401 -> _91401 => @lem3564906 _91401 _91404 y x s f)). Qed.
Lemma lem3564908 {_91401 : Type'} : (@ex (_91401 -> _91401)) = (@ex (_91401 -> _91401)).
Proof. exact (eq_refl (@ex (_91401 -> _91401))). Qed.
Lemma lem3564909 {_91401 _91404 : Type'} (y : _91404) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term505 _91401 _91404 y s f) = (term518 _91401 _91404 y s f).
Proof. exact (MK_COMB (@lem3564908 _91401) (@lem3564907 _91401 _91404 y s f)). Qed.
Lemma lem3564910 {_91401 _91404 : Type'} (y : _91404) (s : _91401 -> Prop) (f : _91401 -> _91404) : ((term504 _91401 _91404 y s f) = (term505 _91401 _91404 y s f)) = ((term498 _91401 _91404 y s f) = (term518 _91401 _91404 y s f)).
Proof. exact (MK_COMB (@lem3564901 _91401 _91404 y s f) (@lem3564909 _91401 _91404 y s f)). Qed.
Lemma lem3564911 {_91401 _91404 : Type'} (y : _91404) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term498 _91401 _91404 y s f) = (term518 _91401 _91404 y s f).
Proof. exact (EQ_MP (@lem3564910 _91401 _91404 y s f) (@lem3564891 _91401 _91404 y s f)). Qed.
Lemma lem3564913 {A : Type'} (P : Prop) (Q : A -> Prop) : (term519 A P Q) = (term520 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3564914 {_91401 : Type'} (P : Prop) (Q : _91401 -> Prop) : (term519 _91401 P Q) = (term520 _91401 P Q).
Proof. exact (@lem3564913 _91401 P Q). Qed.
Lemma lem3564915 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term521 _91401 _91404 y x s f) = (term522 _91401 _91404 y x s f).
Proof. exact (@lem3564914 _91401 (term412 _91401 _91404 s y f x) (term484 _91401 _91404 s f)). Qed.
Lemma lem3564916 {_91401 _91404 : Type'} (x : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term523 _91401 _91404 s f x) = (term483 _91401 _91404 x s f).
Proof. exact (eq_refl (term523 _91401 _91404 s f x)). Qed.
Lemma lem3564917 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term524 _91401 _91404 s f) = (term484 _91401 _91404 s f).
Proof. exact (fun_ext (fun x : _91401 => @lem3564916 _91401 _91404 x s f)). Qed.
Lemma lem3564918 {_91401 : Type'} : (@ex _91401) = (@ex _91401).
Proof. exact (eq_refl (@ex _91401)). Qed.
Lemma lem3564919 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term525 _91401 _91404 s f) = (term485 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564918 _91401) (@lem3564917 _91401 _91404 s f)). Qed.
Lemma lem3564920 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) : (term513 _91401 _91404 s y f x) = (term513 _91401 _91404 s y f x).
Proof. exact (eq_refl (term513 _91401 _91404 s y f x)). Qed.
Lemma lem3564921 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term521 _91401 _91404 y x s f) = (term515 _91401 _91404 y x s f).
Proof. exact (MK_COMB (@lem3564920 _91401 _91404 s y f x) (@lem3564919 _91401 _91404 s f)). Qed.
Lemma lem3564922 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3564923 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term526 _91401 _91404 y x s f) = (term527 _91401 _91404 y x s f).
Proof. exact (MK_COMB (@lem3564922) (@lem3564921 _91401 _91404 y x s f)). Qed.
Lemma lem3564924 {_91401 _91404 : Type'} (x : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term523 _91401 _91404 s f x) = (term483 _91401 _91404 x s f).
Proof. exact (eq_refl (term523 _91401 _91404 s f x)). Qed.
Lemma lem3564925 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) : (term513 _91401 _91404 s y f x) = (term513 _91401 _91404 s y f x).
Proof. exact (eq_refl (term513 _91401 _91404 s y f x)). Qed.
Lemma lem3564926 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (x' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term528 _91401 _91404 y x s f x') = (term529 _91401 _91404 y x x' s f).
Proof. exact (MK_COMB (@lem3564925 _91401 _91404 s y f x) (@lem3564924 _91401 _91404 x' s f)). Qed.
Lemma lem3564927 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term530 _91401 _91404 y x s f) = (term531 _91401 _91404 y x s f).
Proof. exact (fun_ext (fun x' : _91401 => @lem3564926 _91401 _91404 y x x' s f)). Qed.
Lemma lem3564928 {_91401 : Type'} : (@ex _91401) = (@ex _91401).
Proof. exact (eq_refl (@ex _91401)). Qed.
Lemma lem3564929 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term522 _91401 _91404 y x s f) = (term532 _91401 _91404 y x s f).
Proof. exact (MK_COMB (@lem3564928 _91401) (@lem3564927 _91401 _91404 y x s f)). Qed.
Lemma lem3564930 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : ((term521 _91401 _91404 y x s f) = (term522 _91401 _91404 y x s f)) = ((term515 _91401 _91404 y x s f) = (term532 _91401 _91404 y x s f)).
Proof. exact (MK_COMB (@lem3564923 _91401 _91404 y x s f) (@lem3564929 _91401 _91404 y x s f)). Qed.
Lemma lem3564931 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term515 _91401 _91404 y x s f) = (term532 _91401 _91404 y x s f).
Proof. exact (EQ_MP (@lem3564930 _91401 _91404 y x s f) (@lem3564915 _91401 _91404 y x s f)). Qed.
Lemma lem3564933 {A : Type'} (P : Prop) (Q : A -> Prop) : (term519 A P Q) = (term520 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3564934 {_91401 : Type'} (P : Prop) (Q : _91401 -> Prop) : (term519 _91401 P Q) = (term520 _91401 P Q).
Proof. exact (@lem3564933 _91401 P Q). Qed.
Lemma lem3564935 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (x' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term533 _91401 _91404 y x x' s f) = (term534 _91401 _91404 y x x' s f).
Proof. exact (@lem3564934 _91401 (term412 _91401 _91404 s y f x) (term482 _91401 _91404 x' s f)). Qed.
Lemma lem3564936 {_91401 _91404 : Type'} (x : _91401) (y : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term535 _91401 _91404 x s f y) = (term481 _91401 _91404 x y s f).
Proof. exact (eq_refl (term535 _91401 _91404 x s f y)). Qed.
Lemma lem3564937 {_91401 _91404 : Type'} (x : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term536 _91401 _91404 x s f) = (term482 _91401 _91404 x s f).
Proof. exact (fun_ext (fun y : _91401 => @lem3564936 _91401 _91404 x y s f)). Qed.
Lemma lem3564938 {_91401 : Type'} : (@ex _91401) = (@ex _91401).
Proof. exact (eq_refl (@ex _91401)). Qed.
Lemma lem3564939 {_91401 _91404 : Type'} (x : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term537 _91401 _91404 x s f) = (term483 _91401 _91404 x s f).
Proof. exact (MK_COMB (@lem3564938 _91401) (@lem3564937 _91401 _91404 x s f)). Qed.
Lemma lem3564940 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) : (term513 _91401 _91404 s y f x) = (term513 _91401 _91404 s y f x).
Proof. exact (eq_refl (term513 _91401 _91404 s y f x)). Qed.
Lemma lem3564941 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (x' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term533 _91401 _91404 y x x' s f) = (term529 _91401 _91404 y x x' s f).
Proof. exact (MK_COMB (@lem3564940 _91401 _91404 s y f x) (@lem3564939 _91401 _91404 x' s f)). Qed.
Lemma lem3564942 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3564943 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (x' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term538 _91401 _91404 y x x' s f) = (term539 _91401 _91404 y x x' s f).
Proof. exact (MK_COMB (@lem3564942) (@lem3564941 _91401 _91404 y x x' s f)). Qed.
Lemma lem3564944 {_91401 _91404 : Type'} (x : _91401) (y : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term535 _91401 _91404 x s f y) = (term481 _91401 _91404 x y s f).
Proof. exact (eq_refl (term535 _91401 _91404 x s f y)). Qed.
Lemma lem3564945 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) : (term513 _91401 _91404 s y f x) = (term513 _91401 _91404 s y f x).
Proof. exact (eq_refl (term513 _91401 _91404 s y f x)). Qed.
Lemma lem3564946 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term540 _91401 _91404 y x x' s f y') = (term541 _91401 _91404 y x x' y' s f).
Proof. exact (MK_COMB (@lem3564945 _91401 _91404 s y f x) (@lem3564944 _91401 _91404 x' y' s f)). Qed.
Lemma lem3564947 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (x' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term542 _91401 _91404 y x x' s f) = (term543 _91401 _91404 y x x' s f).
Proof. exact (fun_ext (fun y' : _91401 => @lem3564946 _91401 _91404 y x x' y' s f)). Qed.
Lemma lem3564948 {_91401 : Type'} : (@ex _91401) = (@ex _91401).
Proof. exact (eq_refl (@ex _91401)). Qed.
Lemma lem3564949 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (x' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term534 _91401 _91404 y x x' s f) = (term544 _91401 _91404 y x x' s f).
Proof. exact (MK_COMB (@lem3564948 _91401) (@lem3564947 _91401 _91404 y x x' s f)). Qed.
Lemma lem3564950 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (x' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : ((term533 _91401 _91404 y x x' s f) = (term534 _91401 _91404 y x x' s f)) = ((term529 _91401 _91404 y x x' s f) = (term544 _91401 _91404 y x x' s f)).
Proof. exact (MK_COMB (@lem3564943 _91401 _91404 y x x' s f) (@lem3564949 _91401 _91404 y x x' s f)). Qed.
Lemma lem3564951 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (x' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term529 _91401 _91404 y x x' s f) = (term544 _91401 _91404 y x x' s f).
Proof. exact (EQ_MP (@lem3564950 _91401 _91404 y x x' s f) (@lem3564935 _91401 _91404 y x x' s f)). Qed.
Lemma lem3564953 {A : Type'} (P : Prop) (Q : A -> Prop) : (term519 A P Q) = (term520 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3564954 {_91401 _91404 : Type'} (P : Prop) (Q : type805 _91401 _91404) : (term545 _91401 _91404 P Q) = (term546 _91401 _91404 P Q).
Proof. exact (@lem3564953 (_91404 -> _91401) P Q). Qed.
Lemma lem3564955 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term547 _91401 _91404 y x x' y' s f) = (term548 _91401 _91404 y x x' y' s f).
Proof. exact (@lem3564954 _91401 _91404 (term412 _91401 _91404 s y f x) (term480 _91401 _91404 x' y' s f)). Qed.
Lemma lem3564956 {_91401 _91404 : Type'} (x : _91401) (y : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) : (term549 _91401 _91404 x y s f g) = (term478 _91401 _91404 x y s f g).
Proof. exact (eq_refl (term549 _91401 _91404 x y s f g)). Qed.
Lemma lem3564957 {_91401 _91404 : Type'} (x : _91401) (y : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term550 _91401 _91404 x y s f) = (term480 _91401 _91404 x y s f).
Proof. exact (fun_ext (fun g : _91404 -> _91401 => @lem3564956 _91401 _91404 x y s f g)). Qed.
Lemma lem3564958 {_91401 _91404 : Type'} : (@ex (_91404 -> _91401)) = (@ex (_91404 -> _91401)).
Proof. exact (eq_refl (@ex (_91404 -> _91401))). Qed.
Lemma lem3564959 {_91401 _91404 : Type'} (x : _91401) (y : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term551 _91401 _91404 x y s f) = (term481 _91401 _91404 x y s f).
Proof. exact (MK_COMB (@lem3564958 _91401 _91404) (@lem3564957 _91401 _91404 x y s f)). Qed.
Lemma lem3564960 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) : (term513 _91401 _91404 s y f x) = (term513 _91401 _91404 s y f x).
Proof. exact (eq_refl (term513 _91401 _91404 s y f x)). Qed.
Lemma lem3564961 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term547 _91401 _91404 y x x' y' s f) = (term541 _91401 _91404 y x x' y' s f).
Proof. exact (MK_COMB (@lem3564960 _91401 _91404 s y f x) (@lem3564959 _91401 _91404 x' y' s f)). Qed.
Lemma lem3564962 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3564963 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term552 _91401 _91404 y x x' y' s f) = (term553 _91401 _91404 y x x' y' s f).
Proof. exact (MK_COMB (@lem3564962) (@lem3564961 _91401 _91404 y x x' y' s f)). Qed.
Lemma lem3564964 {_91401 _91404 : Type'} (x : _91401) (y : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) : (term549 _91401 _91404 x y s f g) = (term478 _91401 _91404 x y s f g).
Proof. exact (eq_refl (term549 _91401 _91404 x y s f g)). Qed.
Lemma lem3564965 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) : (term513 _91401 _91404 s y f x) = (term513 _91401 _91404 s y f x).
Proof. exact (eq_refl (term513 _91401 _91404 s y f x)). Qed.
Lemma lem3564966 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) : (term554 _91401 _91404 y x x' y' s f g) = (term555 _91401 _91404 y x x' y' s f g).
Proof. exact (MK_COMB (@lem3564965 _91401 _91404 s y f x) (@lem3564964 _91401 _91404 x' y' s f g)). Qed.
Lemma lem3564967 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term556 _91401 _91404 y x x' y' s f) = (term557 _91401 _91404 y x x' y' s f).
Proof. exact (fun_ext (fun g : _91404 -> _91401 => @lem3564966 _91401 _91404 y x x' y' s f g)). Qed.
Lemma lem3564968 {_91401 _91404 : Type'} : (@ex (_91404 -> _91401)) = (@ex (_91404 -> _91401)).
Proof. exact (eq_refl (@ex (_91404 -> _91401))). Qed.
Lemma lem3564969 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term548 _91401 _91404 y x x' y' s f) = (term558 _91401 _91404 y x x' y' s f).
Proof. exact (MK_COMB (@lem3564968 _91401 _91404) (@lem3564967 _91401 _91404 y x x' y' s f)). Qed.
Lemma lem3564970 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : ((term547 _91401 _91404 y x x' y' s f) = (term548 _91401 _91404 y x x' y' s f)) = ((term541 _91401 _91404 y x x' y' s f) = (term558 _91401 _91404 y x x' y' s f)).
Proof. exact (MK_COMB (@lem3564963 _91401 _91404 y x x' y' s f) (@lem3564969 _91401 _91404 y x x' y' s f)). Qed.
Lemma lem3564971 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term541 _91401 _91404 y x x' y' s f) = (term558 _91401 _91404 y x x' y' s f).
Proof. exact (EQ_MP (@lem3564970 _91401 _91404 y x x' y' s f) (@lem3564955 _91401 _91404 y x x' y' s f)). Qed.
Lemma lem3564972 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (x' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term543 _91401 _91404 y x x' s f) = (term559 _91401 _91404 y x x' s f).
Proof. exact (fun_ext (fun y' : _91401 => @lem3564971 _91401 _91404 y x x' y' s f)). Qed.
Lemma lem3564973 {_91401 : Type'} : (@ex _91401) = (@ex _91401).
Proof. exact (eq_refl (@ex _91401)). Qed.
Lemma lem3564974 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (x' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term544 _91401 _91404 y x x' s f) = (term560 _91401 _91404 y x x' s f).
Proof. exact (MK_COMB (@lem3564973 _91401) (@lem3564972 _91401 _91404 y x x' s f)). Qed.
Lemma lem3564975 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (x' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term529 _91401 _91404 y x x' s f) = (term560 _91401 _91404 y x x' s f).
Proof. exact (TRANS (@lem3564951 _91401 _91404 y x x' s f) (@lem3564974 _91401 _91404 y x x' s f)). Qed.
Lemma lem3564976 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term531 _91401 _91404 y x s f) = (term561 _91401 _91404 y x s f).
Proof. exact (fun_ext (fun x' : _91401 => @lem3564975 _91401 _91404 y x x' s f)). Qed.
Lemma lem3564977 {_91401 : Type'} : (@ex _91401) = (@ex _91401).
Proof. exact (eq_refl (@ex _91401)). Qed.
Lemma lem3564978 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term532 _91401 _91404 y x s f) = (term562 _91401 _91404 y x s f).
Proof. exact (MK_COMB (@lem3564977 _91401) (@lem3564976 _91401 _91404 y x s f)). Qed.
Lemma lem3564979 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term515 _91401 _91404 y x s f) = (term562 _91401 _91404 y x s f).
Proof. exact (TRANS (@lem3564931 _91401 _91404 y x s f) (@lem3564978 _91401 _91404 y x s f)). Qed.
Lemma lem3564980 {_91401 _91404 : Type'} (y : _91404) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term517 _91401 _91404 y s f) = (term563 _91401 _91404 y s f).
Proof. exact (fun_ext (fun x : _91401 -> _91401 => @lem3564979 _91401 _91404 y x s f)). Qed.
Lemma lem3564981 {_91401 : Type'} : (@ex (_91401 -> _91401)) = (@ex (_91401 -> _91401)).
Proof. exact (eq_refl (@ex (_91401 -> _91401))). Qed.
Lemma lem3564982 {_91401 _91404 : Type'} (y : _91404) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term518 _91401 _91404 y s f) = (term564 _91401 _91404 y s f).
Proof. exact (MK_COMB (@lem3564981 _91401) (@lem3564980 _91401 _91404 y s f)). Qed.
Lemma lem3564983 {_91401 _91404 : Type'} (y : _91404) (s : _91401 -> Prop) (f : _91401 -> _91404) : (term498 _91401 _91404 y s f) = (term564 _91401 _91404 y s f).
Proof. exact (TRANS (@lem3564911 _91401 _91404 y s f) (@lem3564982 _91401 _91404 y s f)). Qed.
Lemma lem3564984 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term500 _91401 _91404 s f) = (term565 _91401 _91404 s f).
Proof. exact (fun_ext (fun y : _91404 => @lem3564983 _91401 _91404 y s f)). Qed.
Lemma lem3564985 {_91404 : Type'} : (@ex _91404) = (@ex _91404).
Proof. exact (eq_refl (@ex _91404)). Qed.
Lemma lem3564986 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term501 _91401 _91404 s f) = (term566 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3564985 _91404) (@lem3564984 _91401 _91404 s f)). Qed.
Lemma lem3564987 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term486 _91401 _91404 s f) = (term566 _91401 _91404 s f).
Proof. exact (TRANS (@lem3564885 _91401 _91404 s f) (@lem3564986 _91401 _91404 s f)). Qed.
Lemma lem3564989 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term363 _91401 _91404 s f) = (term566 _91401 _91404 s f).
Proof. exact (TRANS (@lem3564859 _91401 _91404 s f) (@lem3564987 _91401 _91404 s f)). Qed.
Lemma lem3564990 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term287 _91401 _91404 s f) = (term566 _91401 _91404 s f).
Proof. exact (TRANS (@lem3564450 _91401 _91404 s f) (@lem3564989 _91401 _91404 s f)). Qed.
Lemma lem3564991 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (h1 : term287 _91401 _91404 s f) : term566 _91401 _91404 s f.
Proof. exact (EQ_MP (@lem3564990 _91401 _91404 s f) (@lem3564316 _91401 _91404 s f h1)). Qed.
Lemma lem3564992 {_91401 _91404 : Type'} (y : _91404) (s : _91401 -> Prop) (f : _91401 -> _91404) (h1 : term564 _91401 _91404 y s f) : term564 _91401 _91404 y s f.
Proof. exact (h1). Qed.
Lemma lem3564993 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (h1 : term562 _91401 _91404 y x s f) : term562 _91401 _91404 y x s f.
Proof. exact (h1). Qed.
Lemma lem3564994 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (x' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (h1 : term560 _91401 _91404 y x x' s f) : term560 _91401 _91404 y x x' s f.
Proof. exact (h1). Qed.
Lemma lem3564995 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (h1 : term558 _91401 _91404 y x x' y' s f) : term558 _91401 _91404 y x x' y' s f.
Proof. exact (h1). Qed.
Lemma lem3564996 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term555 _91401 _91404 y x x' y' s f g) : term555 _91401 _91404 y x x' y' s f g.
Proof. exact (h1). Qed.
Lemma lem3565025 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (y : _91404) (x : _91401) : (term59 _91401 _91404 s f g y x) = (term59 _91401 _91404 s f g y x).
Proof. exact (eq_refl (term59 _91401 _91404 s f g y x)). Qed.
Lemma lem3565026 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (y : _91404) : (term67 _91401 _91404 s f g y) = (term67 _91401 _91404 s f g y).
Proof. exact (fun_ext (fun x : _91401 => @lem3565025 _91401 _91404 s f g y x)). Qed.
Lemma lem3565027 {_91401 : Type'} : (@all _91401) = (@all _91401).
Proof. exact (eq_refl (@all _91401)). Qed.
Lemma lem3565028 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (y : _91404) : (term68 _91401 _91404 s f g y) = (term68 _91401 _91404 s f g y).
Proof. exact (MK_COMB (@lem3565027 _91401) (@lem3565026 _91401 _91404 s f g y)). Qed.
Lemma lem3565029 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) : (term76 _91401 _91404 s f g) = (term76 _91401 _91404 s f g).
Proof. exact (fun_ext (fun y : _91404 => @lem3565028 _91401 _91404 s f g y)). Qed.
Lemma lem3565030 {_91404 : Type'} : (@all _91404) = (@all _91404).
Proof. exact (eq_refl (@all _91404)). Qed.
Lemma lem3565031 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) : (term77 _91401 _91404 s f g) = (term77 _91401 _91404 s f g).
Proof. exact (MK_COMB (@lem3565030 _91404) (@lem3565029 _91401 _91404 s f g)). Qed.
Lemma lem3565068 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x' : _91401) (y' : _91401) : (term462 _91401 _91404 s f x' y') = (term462 _91401 _91404 s f x' y').
Proof. exact (eq_refl (term462 _91401 _91404 s f x' y')). Qed.
Lemma lem3565069 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) : (term478 _91401 _91404 x' y' s f g) = (term478 _91401 _91404 x' y' s f g).
Proof. exact (MK_COMB (@lem3565068 _91401 _91404 s f x' y') (@lem3565031 _91401 _91404 s f g)). Qed.
Lemma lem3565100 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (g : _91401) : (term379 _91401 _91404 s y f x g) = (term379 _91401 _91404 s y f x g).
Proof. exact (eq_refl (term379 _91401 _91404 s y f x g)). Qed.
Lemma lem3565101 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) : (term381 _91401 _91404 s y f x) = (term381 _91401 _91404 s y f x).
Proof. exact (fun_ext (fun g : _91401 => @lem3565100 _91401 _91404 s y f x g)). Qed.
Lemma lem3565102 {_91401 : Type'} : (@all _91401) = (@all _91401).
Proof. exact (eq_refl (@all _91401)). Qed.
Lemma lem3565103 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) : (term383 _91401 _91404 s y f x) = (term383 _91401 _91404 s y f x).
Proof. exact (MK_COMB (@lem3565102 _91401) (@lem3565101 _91401 _91404 s y f x)). Qed.
Lemma lem3565142 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) (y : _91401) : (term301 _91401 _91404 s f x y) = (term301 _91401 _91404 s f x y).
Proof. exact (eq_refl (term301 _91401 _91404 s f x y)). Qed.
Lemma lem3565143 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) : (term309 _91401 _91404 s f x) = (term309 _91401 _91404 s f x).
Proof. exact (fun_ext (fun y : _91401 => @lem3565142 _91401 _91404 s f x y)). Qed.
Lemma lem3565144 {_91401 : Type'} : (@all _91401) = (@all _91401).
Proof. exact (eq_refl (@all _91401)). Qed.
Lemma lem3565145 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) : (term310 _91401 _91404 s f x) = (term310 _91401 _91404 s f x).
Proof. exact (MK_COMB (@lem3565144 _91401) (@lem3565143 _91401 _91404 s f x)). Qed.
Lemma lem3565146 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term318 _91401 _91404 s f) = (term318 _91401 _91404 s f).
Proof. exact (fun_ext (fun x : _91401 => @lem3565145 _91401 _91404 s f x)). Qed.
Lemma lem3565147 {_91401 : Type'} : (@all _91401) = (@all _91401).
Proof. exact (eq_refl (@all _91401)). Qed.
Lemma lem3565148 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term319 _91401 _91404 s f) = (term319 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3565147 _91401) (@lem3565146 _91401 _91404 s f)). Qed.
Lemma lem3565149 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3565150 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term357 _91401 _91404 s f) = (term357 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3565149) (@lem3565148 _91401 _91404 s f)). Qed.
Lemma lem3565151 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) : (term412 _91401 _91404 s y f x) = (term412 _91401 _91404 s y f x).
Proof. exact (MK_COMB (@lem3565150 _91401 _91404 s f) (@lem3565103 _91401 _91404 s y f x)). Qed.
Lemma lem3565152 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3565153 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) : (term513 _91401 _91404 s y f x) = (term513 _91401 _91404 s y f x).
Proof. exact (MK_COMB (@lem3565152) (@lem3565151 _91401 _91404 s y f x)). Qed.
Lemma lem3565154 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) : (term555 _91401 _91404 y x x' y' s f g) = (term555 _91401 _91404 y x x' y' s f g).
Proof. exact (MK_COMB (@lem3565153 _91401 _91404 s y f x) (@lem3565069 _91401 _91404 x' y' s f g)). Qed.
Lemma lem3565155 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term555 _91401 _91404 y x x' y' s f g) : term555 _91401 _91404 y x x' y' s f g.
Proof. exact (EQ_MP (@lem3565154 _91401 _91404 y x x' y' s f g) (@lem3564996 _91401 _91404 y x x' y' s f g h1)). Qed.
Lemma lem3565156 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term412 _91401 _91404 s y f x.
Proof. exact (h1). Qed.
Lemma lem3565157 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : term478 _91401 _91404 x' y' s f g.
Proof. exact (h1). Qed.
Lemma lem3565158 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term383 _91401 _91404 s y f x.
Proof. exact (proj2 (@lem3565156 _91401 _91404 s y f x h1)). Qed.
Lemma lem3565159 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term319 _91401 _91404 s f.
Proof. exact (proj1 (@lem3565156 _91401 _91404 s y f x h1)). Qed.
Lemma lem3565160 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : term77 _91401 _91404 s f g.
Proof. exact (proj2 (@lem3565157 _91401 _91404 x' y' s f g h1)). Qed.
Lemma lem3565161 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : term296 _91401 _91404 s f x' y'.
Proof. exact (proj1 (@lem3565157 _91401 _91404 x' y' s f g h1)). Qed.
Lemma lem3565163 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : term297 _91401 _91404 s x' f y'.
Proof. exact (proj1 (@lem3565161 _91401 _91404 x' y' s f g h1)). Qed.
Lemma lem3565164 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : term294 _91401 _91404 s x' f y'.
Proof. exact (proj2 (@lem3565163 _91401 _91404 x' y' s f g h1)). Qed.
Lemma lem3565187 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) (y : _91401) : (term301 _91401 _91404 s f x y) = (term301 _91401 _91404 s f x y).
Proof. exact (eq_refl (term301 _91401 _91404 s f x y)). Qed.
Lemma lem3565188 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) : (term309 _91401 _91404 s f x) = (term309 _91401 _91404 s f x).
Proof. exact (fun_ext (fun y : _91401 => @lem3565187 _91401 _91404 s f x y)). Qed.
Lemma lem3565189 {_91401 : Type'} : (@all _91401) = (@all _91401).
Proof. exact (eq_refl (@all _91401)). Qed.
Lemma lem3565190 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (x : _91401) : (term310 _91401 _91404 s f x) = (term310 _91401 _91404 s f x).
Proof. exact (MK_COMB (@lem3565189 _91401) (@lem3565188 _91401 _91404 s f x)). Qed.
Lemma lem3565191 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term318 _91401 _91404 s f) = (term318 _91401 _91404 s f).
Proof. exact (fun_ext (fun x : _91401 => @lem3565190 _91401 _91404 s f x)). Qed.
Lemma lem3565192 {_91401 : Type'} : (@all _91401) = (@all _91401).
Proof. exact (eq_refl (@all _91401)). Qed.
Lemma lem3565194 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term319 _91401 _91404 s f) = (term319 _91401 _91404 s f).
Proof. exact (MK_COMB (@lem3565192 _91401) (@lem3565191 _91401 _91404 s f)). Qed.
Lemma lem3565195 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term319 _91401 _91404 s f.
Proof. exact (EQ_MP (@lem3565194 _91401 _91404 s f) (@lem3565159 _91401 _91404 s y f x h1)). Qed.
Lemma lem3565205 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (g : _91401) : (term379 _91401 _91404 s y f x g) = (term379 _91401 _91404 s y f x g).
Proof. exact (eq_refl (term379 _91401 _91404 s y f x g)). Qed.
Lemma lem3565206 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) : (term381 _91401 _91404 s y f x) = (term381 _91401 _91404 s y f x).
Proof. exact (fun_ext (fun g : _91401 => @lem3565205 _91401 _91404 s y f x g)). Qed.
Lemma lem3565207 {_91401 : Type'} : (@all _91401) = (@all _91401).
Proof. exact (eq_refl (@all _91401)). Qed.
Lemma lem3565209 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) : (term383 _91401 _91404 s y f x) = (term383 _91401 _91404 s y f x).
Proof. exact (MK_COMB (@lem3565207 _91401) (@lem3565206 _91401 _91404 s y f x)). Qed.
Lemma lem3565210 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term383 _91401 _91404 s y f x.
Proof. exact (EQ_MP (@lem3565209 _91401 _91404 s y f x) (@lem3565158 _91401 _91404 s y f x h1)). Qed.
Lemma lem3565224 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (y : _91404) (x : _91401) : (term59 _91401 _91404 s f g y x) = (term59 _91401 _91404 s f g y x).
Proof. exact (eq_refl (term59 _91401 _91404 s f g y x)). Qed.
Lemma lem3565225 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (y : _91404) : (term67 _91401 _91404 s f g y) = (term67 _91401 _91404 s f g y).
Proof. exact (fun_ext (fun x : _91401 => @lem3565224 _91401 _91404 s f g y x)). Qed.
Lemma lem3565226 {_91401 : Type'} : (@all _91401) = (@all _91401).
Proof. exact (eq_refl (@all _91401)). Qed.
Lemma lem3565227 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (y : _91404) : (term68 _91401 _91404 s f g y) = (term68 _91401 _91404 s f g y).
Proof. exact (MK_COMB (@lem3565226 _91401) (@lem3565225 _91401 _91404 s f g y)). Qed.
Lemma lem3565228 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) : (term76 _91401 _91404 s f g) = (term76 _91401 _91404 s f g).
Proof. exact (fun_ext (fun y : _91404 => @lem3565227 _91401 _91404 s f g y)). Qed.
Lemma lem3565229 {_91404 : Type'} : (@all _91404) = (@all _91404).
Proof. exact (eq_refl (@all _91404)). Qed.
Lemma lem3565231 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) : (term77 _91401 _91404 s f g) = (term77 _91401 _91404 s f g).
Proof. exact (MK_COMB (@lem3565229 _91404) (@lem3565228 _91401 _91404 s f g)). Qed.
Lemma lem3565232 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : term77 _91401 _91404 s f g.
Proof. exact (EQ_MP (@lem3565231 _91401 _91404 s f g) (@lem3565160 _91401 _91404 x' y' s f g h1)). Qed.
Lemma lem3565249 {_91401 _91404 : Type'} (_38257 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term567 _91401 _91404 s f _38257.
Proof. exact (@lem3565195 _91401 _91404 s y f x h1 _38257). Qed.
Lemma lem3565250 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (_38257 : _91401) : (term567 _91401 _91404 s f _38257) = (term310 _91401 _91404 s f _38257).
Proof. exact (eq_refl (term567 _91401 _91404 s f _38257)). Qed.
Lemma lem3565251 {_91401 _91404 : Type'} (_38257 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term310 _91401 _91404 s f _38257.
Proof. exact (EQ_MP (@lem3565250 _91401 _91404 s f _38257) (@lem3565249 _91401 _91404 _38257 s y f x h1)). Qed.
Lemma lem3565252 {_91401 _91404 : Type'} (_38257 : _91401) (_38258 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term568 _91401 _91404 s f _38257 _38258.
Proof. exact (@lem3565251 _91401 _91404 _38257 s y f x h1 _38258). Qed.
Lemma lem3565253 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (_38257 : _91401) (_38258 : _91401) : (term568 _91401 _91404 s f _38257 _38258) = (term301 _91401 _91404 s f _38257 _38258).
Proof. exact (eq_refl (term568 _91401 _91404 s f _38257 _38258)). Qed.
Lemma lem3565254 {_91401 _91404 : Type'} (_38257 : _91401) (_38258 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term301 _91401 _91404 s f _38257 _38258.
Proof. exact (EQ_MP (@lem3565253 _91401 _91404 s f _38257 _38258) (@lem3565252 _91401 _91404 _38257 _38258 s y f x h1)). Qed.
Lemma lem3565255 {_91401 _91404 : Type'} (_38259 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term569 _91401 _91404 s y f x _38259.
Proof. exact (@lem3565210 _91401 _91404 s y f x h1 _38259). Qed.
Lemma lem3565256 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (_38259 : _91401) : (term569 _91401 _91404 s y f x _38259) = (term379 _91401 _91404 s y f x _38259).
Proof. exact (eq_refl (term569 _91401 _91404 s y f x _38259)). Qed.
Lemma lem3565257 {_91401 _91404 : Type'} (_38259 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term379 _91401 _91404 s y f x _38259.
Proof. exact (EQ_MP (@lem3565256 _91401 _91404 s y f x _38259) (@lem3565255 _91401 _91404 _38259 s y f x h1)). Qed.
Lemma lem3565258 {_91401 _91404 : Type'} (_38260 : _91404) (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : term177 _91401 _91404 s f g _38260.
Proof. exact (@lem3565232 _91401 _91404 x' y' s f g h1 _38260). Qed.
Lemma lem3565259 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (_38260 : _91404) : (term177 _91401 _91404 s f g _38260) = (term68 _91401 _91404 s f g _38260).
Proof. exact (eq_refl (term177 _91401 _91404 s f g _38260)). Qed.
Lemma lem3565260 {_91401 _91404 : Type'} (_38260 : _91404) (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : term68 _91401 _91404 s f g _38260.
Proof. exact (EQ_MP (@lem3565259 _91401 _91404 s f g _38260) (@lem3565258 _91401 _91404 _38260 x' y' s f g h1)). Qed.
Lemma lem3565261 {_91401 _91404 : Type'} (_38260 : _91404) (_38261 : _91401) (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : term178 _91401 _91404 s f g _38260 _38261.
Proof. exact (@lem3565260 _91401 _91404 _38260 x' y' s f g h1 _38261). Qed.
Lemma lem3565262 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (_38260 : _91404) (_38261 : _91401) : (term178 _91401 _91404 s f g _38260 _38261) = (term59 _91401 _91404 s f g _38260 _38261).
Proof. exact (eq_refl (term178 _91401 _91404 s f g _38260 _38261)). Qed.
Lemma lem3565263 {_91401 _91404 : Type'} (_38260 : _91404) (_38261 : _91401) (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : term59 _91401 _91404 s f g _38260 _38261.
Proof. exact (EQ_MP (@lem3565262 _91401 _91404 s f g _38260 _38261) (@lem3565261 _91401 _91404 _38260 _38261 x' y' s f g h1)). Qed.
Lemma lem3565265 {_91401 _91404 : Type'} (_38259 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term570 _91401 _91404 s y f x _38259.
Proof. exact (proj1 (@lem3565257 _91401 _91404 _38259 s y f x h1)). Qed.
Lemma lem3565271 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (_38257 : _91401) (_38258 : _91401) : (term301 _91401 _91404 s f _38257 _38258) = (term571 _91401 _91404 s f _38257 _38258).
Proof. exact (@lem3563998 (term181 _91401 _38257 s) (term289 _91401 _91404 s _38257 f _38258) (_38257 = _38258)). Qed.
Lemma lem3565278 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (_38257 : _91401) (_38258 : _91401) : (term572 _91401 _91404 s f _38257 _38258) = (term573 _91401 _91404 s f _38257 _38258).
Proof. exact (@lem3563998 (term181 _91401 _38258 s) (term574 _91401 _91404 _38257 f _38258) (_38257 = _38258)). Qed.
Lemma lem3565279 {_91401 : Type'} (_38257 : _91401) (s : _91401 -> Prop) : (term290 _91401 _38257 s) = (term290 _91401 _38257 s).
Proof. exact (eq_refl (term290 _91401 _38257 s)). Qed.
Lemma lem3565282 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (_38257 : _91401) (_38258 : _91401) : (term571 _91401 _91404 s f _38257 _38258) = (term575 _91401 _91404 s f _38257 _38258).
Proof. exact (MK_COMB (@lem3565279 _91401 _38257 s) (@lem3565278 _91401 _91404 s f _38257 _38258)). Qed.
Lemma lem3565284 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (_38257 : _91401) (_38258 : _91401) : (term301 _91401 _91404 s f _38257 _38258) = (term575 _91401 _91404 s f _38257 _38258).
Proof. exact (TRANS (@lem3565271 _91401 _91404 s f _38257 _38258) (@lem3565282 _91401 _91404 s f _38257 _38258)). Qed.
Lemma lem3565285 {_91401 _91404 : Type'} (_38257 : _91401) (_38258 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term575 _91401 _91404 s f _38257 _38258.
Proof. exact (EQ_MP (@lem3565284 _91401 _91404 s f _38257 _38258) (@lem3565254 _91401 _91404 _38257 _38258 s y f x h1)). Qed.
Lemma lem3565287 {_91401 _91404 : Type'} (_38259 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term576 _91401 x _38259.
Proof. exact (proj2 (@lem3565257 _91401 _91404 _38259 s y f x h1)). Qed.
Lemma lem3565302 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (_38260 : _91404) (_38261 : _91401) : (term59 _91401 _91404 s f g _38260 _38261) = (term180 _91401 _91404 s f g _38260 _38261).
Proof. exact (@lem3563998 (term181 _91401 _38261 s) (term182 _91401 _91404 _38260 f _38261) ((g _38260) = _38261)). Qed.
Lemma lem3565303 {_91401 _91404 : Type'} (_38260 : _91404) (_38261 : _91401) (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : term180 _91401 _91404 s f g _38260 _38261.
Proof. exact (EQ_MP (@lem3565302 _91401 _91404 s f g _38260 _38261) (@lem3565263 _91401 _91404 _38260 _38261 x' y' s f g h1)). Qed.
Lemma lem3565305 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : term577 _91401 x' y'.
Proof. exact (proj2 (@lem3565161 _91401 _91404 x' y' s f g h1)). Qed.
Lemma lem3565348 {_91404 : Type'} (x : _91404) (y : _91404) (z : _91404) : term578 _91404 x y z.
Proof. exact (@lem21385 _91404 x y z). Qed.
Lemma lem3565354 {_91401 _91404 : Type'} (_38259 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term579 _91401 x _38259 s.
Proof. exact (proj1 (@lem3565265 _91401 _91404 _38259 s y f x h1)). Qed.
Lemma lem3565355 {_91401 _91404 : Type'} (_38259 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term579 _91401 x _38259 s.
Proof. exact (@lem3565354 _91401 _91404 _38259 s y f x h1). Qed.
Lemma lem3565356 {_91401 _91404 : Type'} (_38270 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term579 _91401 x _38270 s.
Proof. exact (@lem3565355 _91401 _91404 _38270 s y f x h1). Qed.
Lemma lem3565357 {_91401 _91404 : Type'} (_38270 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term580 _91401 x _38270 s.
Proof. exact (fun h0 : term581 _91401 x _38270 s => @lem3565356 _91401 _91404 _38270 s y f x h1). Qed.
Lemma lem3565359 (p : Prop) : (term190 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3565360 {_91401 : Type'} (x : _91401 -> _91401) (_38270 : _91401) (s : _91401 -> Prop) : (term580 _91401 x _38270 s) = (term579 _91401 x _38270 s).
Proof. exact (@lem3565359 (term579 _91401 x _38270 s)). Qed.
Lemma lem3565361 {_91401 _91404 : Type'} (_38270 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term579 _91401 x _38270 s.
Proof. exact (EQ_MP (@lem3565360 _91401 x _38270 s) (@lem3565357 _91401 _91404 _38270 s y f x h1)). Qed.
Lemma lem3565363 {_91401 _91404 : Type'} (_38259 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term579 _91401 x _38259 s.
Proof. exact (proj1 (@lem3565265 _91401 _91404 _38259 s y f x h1)). Qed.
Lemma lem3565364 {_91401 _91404 : Type'} (_38259 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term579 _91401 x _38259 s.
Proof. exact (@lem3565363 _91401 _91404 _38259 s y f x h1). Qed.
Lemma lem3565365 {_91401 _91404 : Type'} (_38270 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term582 _91401 x _38270 s.
Proof. exact (@lem3565364 _91401 _91404 (x _38270) s y f x h1). Qed.
Lemma lem3565366 {_91401 _91404 : Type'} (_38270 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term583 _91401 x _38270 s.
Proof. exact (fun h0 : term584 _91401 x _38270 s => @lem3565365 _91401 _91404 _38270 s y f x h1). Qed.
Lemma lem3565368 (p : Prop) : (term190 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3565369 {_91401 : Type'} (x : _91401 -> _91401) (_38270 : _91401) (s : _91401 -> Prop) : (term583 _91401 x _38270 s) = (term582 _91401 x _38270 s).
Proof. exact (@lem3565368 (term582 _91401 x _38270 s)). Qed.
Lemma lem3565370 {_91401 _91404 : Type'} (_38270 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term582 _91401 x _38270 s.
Proof. exact (EQ_MP (@lem3565369 _91401 x _38270 s) (@lem3565366 _91401 _91404 _38270 s y f x h1)). Qed.
Lemma lem3565372 {_91401 _91404 : Type'} (_38259 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : y = (term585 _91401 _91404 f x _38259).
Proof. exact (proj2 (@lem3565265 _91401 _91404 _38259 s y f x h1)). Qed.
Lemma lem3565373 {_91401 _91404 : Type'} (_38259 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : y = (term585 _91401 _91404 f x _38259).
Proof. exact (@lem3565372 _91401 _91404 _38259 s y f x h1). Qed.
Lemma lem3565374 {_91401 _91404 : Type'} (_38270 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : y = (term585 _91401 _91404 f x _38270).
Proof. exact (@lem3565373 _91401 _91404 _38270 s y f x h1). Qed.
Lemma lem3565375 {_91401 _91404 : Type'} (_38270 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term586 _91401 _91404 y f x _38270.
Proof. exact (fun h0 : term587 _91401 _91404 y f x _38270 => @lem3565374 _91401 _91404 _38270 s y f x h1). Qed.
Lemma lem3565377 (p : Prop) : (term190 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3565378 {_91401 _91404 : Type'} (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (_38270 : _91401) : (term586 _91401 _91404 y f x _38270) = (y = (term585 _91401 _91404 f x _38270)).
Proof. exact (@lem3565377 (y = (term585 _91401 _91404 f x _38270))). Qed.
Lemma lem3565379 {_91401 _91404 : Type'} (_38270 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : y = (term585 _91401 _91404 f x _38270).
Proof. exact (EQ_MP (@lem3565378 _91401 _91404 y f x _38270) (@lem3565375 _91401 _91404 _38270 s y f x h1)). Qed.
Lemma lem3565381 {_91401 _91404 : Type'} (_38259 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : y = (term585 _91401 _91404 f x _38259).
Proof. exact (proj2 (@lem3565265 _91401 _91404 _38259 s y f x h1)). Qed.
Lemma lem3565382 {_91401 _91404 : Type'} (_38259 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : y = (term585 _91401 _91404 f x _38259).
Proof. exact (@lem3565381 _91401 _91404 _38259 s y f x h1). Qed.
Lemma lem3565383 {_91401 _91404 : Type'} (_38270 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : y = (term588 _91401 _91404 f x _38270).
Proof. exact (@lem3565382 _91401 _91404 (x _38270) s y f x h1). Qed.
Lemma lem3565384 {_91401 _91404 : Type'} (_38270 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term589 _91401 _91404 y f x _38270.
Proof. exact (fun h0 : term590 _91401 _91404 y f x _38270 => @lem3565383 _91401 _91404 _38270 s y f x h1). Qed.
Lemma lem3565386 (p : Prop) : (term190 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3565387 {_91401 _91404 : Type'} (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (_38270 : _91401) : (term589 _91401 _91404 y f x _38270) = (y = (term588 _91401 _91404 f x _38270)).
Proof. exact (@lem3565386 (y = (term588 _91401 _91404 f x _38270))). Qed.
Lemma lem3565388 {_91401 _91404 : Type'} (_38270 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : y = (term588 _91401 _91404 f x _38270).
Proof. exact (EQ_MP (@lem3565387 _91401 _91404 y f x _38270) (@lem3565384 _91401 _91404 _38270 s y f x h1)). Qed.
Lemma lem3565406 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3565407 {_91404 : Type'} (y : _91404) (x : _91404) (z : _91404) : (term591 _91404 x y z) = (term592 _91404 y x z).
Proof. exact (@lem3565406 (y = z) (term577 _91404 x z)). Qed.
Lemma lem3565417 {_91404 : Type'} (x : _91404) (y : _91404) : (term593 _91404 x y) = (term593 _91404 x y).
Proof. exact (eq_refl (term593 _91404 x y)). Qed.
Lemma lem3565418 {_91404 : Type'} (y : _91404) (x : _91404) (z : _91404) : (term578 _91404 x y z) = (term594 _91404 y x z).
Proof. exact (MK_COMB (@lem3565417 _91404 x y) (@lem3565407 _91404 y x z)). Qed.
Lemma lem3565422 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3565423 {_91404 : Type'} (y : _91404) (x : _91404) (z : _91404) : (term594 _91404 y x z) = (term595 _91404 y x z).
Proof. exact (@lem3565422 (y = z) (term577 _91404 x y) (term577 _91404 x z)). Qed.
Lemma lem3565445 {_91404 : Type'} (y : _91404) (x : _91404) (z : _91404) : (term578 _91404 x y z) = (term595 _91404 y x z).
Proof. exact (TRANS (@lem3565418 _91404 y x z) (@lem3565423 _91404 y x z)). Qed.
Lemma lem3565446 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3565447 {_91404 : Type'} (y : _91404) (x : _91404) (z : _91404) : (term596 _91404 x y z) = (term597 _91404 y x z).
Proof. exact (MK_COMB (@lem3565446) (@lem3565445 _91404 y x z)). Qed.
Lemma lem3565469 {_91404 : Type'} (y : _91404) (x : _91404) (z : _91404) : (term595 _91404 y x z) = (term595 _91404 y x z).
Proof. exact (eq_refl (term595 _91404 y x z)). Qed.
Lemma lem3565470 {_91404 : Type'} (y : _91404) (x : _91404) (z : _91404) : ((term578 _91404 x y z) = (term595 _91404 y x z)) = ((term595 _91404 y x z) = (term595 _91404 y x z)).
Proof. exact (MK_COMB (@lem3565447 _91404 y x z) (@lem3565469 _91404 y x z)). Qed.
Lemma lem3565472 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3565473 (x : Prop) : (x = x) = True.
Proof. exact (@lem3565472 Prop x). Qed.
Lemma lem3565474 {_91404 : Type'} (y : _91404) (x : _91404) (z : _91404) : ((term595 _91404 y x z) = (term595 _91404 y x z)) = True.
Proof. exact (@lem3565473 (term595 _91404 y x z)). Qed.
Lemma lem3565475 {_91404 : Type'} (y : _91404) (x : _91404) (z : _91404) : ((term578 _91404 x y z) = (term595 _91404 y x z)) = True.
Proof. exact (TRANS (@lem3565470 _91404 y x z) (@lem3565474 _91404 y x z)). Qed.
Lemma lem3565476 {_91404 : Type'} (y : _91404) (x : _91404) (z : _91404) : True = ((term578 _91404 x y z) = (term595 _91404 y x z)).
Proof. exact (SYM (@lem3565475 _91404 y x z)). Qed.
Lemma lem3565477 {_91404 : Type'} (y : _91404) (x : _91404) (z : _91404) : (term578 _91404 x y z) = (term595 _91404 y x z).
Proof. exact (EQ_MP (@lem3565476 _91404 y x z) (@lem0)). Qed.
Lemma lem3565478 {_91404 : Type'} (y : _91404) (x : _91404) (z : _91404) : term595 _91404 y x z.
Proof. exact (EQ_MP (@lem3565477 _91404 y x z) (@lem3565348 _91404 x y z)). Qed.
Lemma lem3565480 (b : Prop) (a : Prop) : (a \/ b) = (term194 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3565481 {_91404 : Type'} (x : _91404) (y : _91404) (z : _91404) : (term595 _91404 y x z) = (term598 _91404 x y z).
Proof. exact (@lem3565480 (term599 _91404 y x z) (y = z)). Qed.
Lemma lem3565483 (a : Prop) (b : Prop) : (term216 a b) = (term217 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3565484 {_91404 : Type'} (y : _91404) (x : _91404) (z : _91404) : (term600 _91404 y x z) = (term601 _91404 y x z).
Proof. exact (@lem3565483 (term577 _91404 x y) (term577 _91404 x z)). Qed.
Lemma lem3565486 (a : Prop) : (term16 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3565487 {_91404 : Type'} (x : _91404) (y : _91404) : (term602 _91404 x y) = (x = y).
Proof. exact (@lem3565486 (x = y)). Qed.
Lemma lem3565488 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3565489 {_91404 : Type'} (x : _91404) (y : _91404) : (term603 _91404 x y) = (term604 _91404 x y).
Proof. exact (MK_COMB (@lem3565488) (@lem3565487 _91404 x y)). Qed.
Lemma lem3565491 (a : Prop) : (term16 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3565492 {_91404 : Type'} (x : _91404) (z : _91404) : (term602 _91404 x z) = (x = z).
Proof. exact (@lem3565491 (x = z)). Qed.
Lemma lem3565493 {_91404 : Type'} (y : _91404) (x : _91404) (z : _91404) : (term601 _91404 y x z) = (term605 _91404 y x z).
Proof. exact (MK_COMB (@lem3565489 _91404 x y) (@lem3565492 _91404 x z)). Qed.
Lemma lem3565494 {_91404 : Type'} (y : _91404) (x : _91404) (z : _91404) : (term600 _91404 y x z) = (term605 _91404 y x z).
Proof. exact (TRANS (@lem3565484 _91404 y x z) (@lem3565493 _91404 y x z)). Qed.
Lemma lem3565495 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3565496 {_91404 : Type'} (y : _91404) (x : _91404) (z : _91404) : (term606 _91404 y x z) = (term607 _91404 y x z).
Proof. exact (MK_COMB (@lem3565495) (@lem3565494 _91404 y x z)). Qed.
Lemma lem3565497 {_91404 : Type'} (y : _91404) (z : _91404) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3565498 {_91404 : Type'} (x : _91404) (y : _91404) (z : _91404) : (term598 _91404 x y z) = (term608 _91404 x y z).
Proof. exact (MK_COMB (@lem3565496 _91404 y x z) (@lem3565497 _91404 y z)). Qed.
Lemma lem3565499 {_91404 : Type'} (x : _91404) (y : _91404) (z : _91404) : (term595 _91404 y x z) = (term608 _91404 x y z).
Proof. exact (TRANS (@lem3565481 _91404 x y z) (@lem3565498 _91404 x y z)). Qed.
Lemma lem3565501 {_91401 _91404 : Type'} (_38270 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term609 _91401 _91404 y f x _38270.
Proof. exact (conj (@lem3565379 _91401 _91404 _38270 s y f x h1) (@lem3565388 _91401 _91404 _38270 s y f x h1)). Qed.
Lemma lem3565503 {_91404 : Type'} (x : _91404) (y : _91404) (z : _91404) : term608 _91404 x y z.
Proof. exact (EQ_MP (@lem3565499 _91404 x y z) (@lem3565478 _91404 y x z)). Qed.
Lemma lem3565504 {_91404 : Type'} (x : _91404) (y : _91404) (z : _91404) : term608 _91404 x y z.
Proof. exact (@lem3565503 _91404 x y z). Qed.
Lemma lem3565505 {_91401 _91404 : Type'} (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (_38270 : _91401) : term610 _91401 _91404 y f x _38270.
Proof. exact (@lem3565504 _91404 y (term585 _91401 _91404 f x _38270) (term588 _91401 _91404 f x _38270)). Qed.
Lemma lem3565508 {_91401 _91404 : Type'} (_38270 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : (term585 _91401 _91404 f x _38270) = (term588 _91401 _91404 f x _38270).
Proof. exact (@lem3565505 _91401 _91404 y f x _38270 (@lem3565501 _91401 _91404 _38270 s y f x h1)). Qed.
Lemma lem3565509 {_91401 _91404 : Type'} (_38270 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : (term585 _91401 _91404 f x _38270) = (term588 _91401 _91404 f x _38270).
Proof. exact (@lem3565508 _91401 _91404 _38270 s y f x h1). Qed.
Lemma lem3565510 {_91401 _91404 : Type'} (_38270 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term611 _91401 _91404 f x _38270.
Proof. exact (fun h0 : term612 _91401 _91404 f x _38270 => @lem3565509 _91401 _91404 _38270 s y f x h1). Qed.
Lemma lem3565512 (p : Prop) : (term190 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3565513 {_91401 _91404 : Type'} (f : _91401 -> _91404) (x : _91401 -> _91401) (_38270 : _91401) : (term611 _91401 _91404 f x _38270) = ((term585 _91401 _91404 f x _38270) = (term588 _91401 _91404 f x _38270)).
Proof. exact (@lem3565512 ((term585 _91401 _91404 f x _38270) = (term588 _91401 _91404 f x _38270))). Qed.
Lemma lem3565514 {_91401 _91404 : Type'} (_38270 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : (term585 _91401 _91404 f x _38270) = (term588 _91401 _91404 f x _38270).
Proof. exact (EQ_MP (@lem3565513 _91401 _91404 f x _38270) (@lem3565510 _91401 _91404 _38270 s y f x h1)). Qed.
Lemma lem3565530 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3565531 {_91401 _91404 : Type'} (f : _91401 -> _91404) (s : _91401 -> Prop) (_38257 : _91401) (_38258 : _91401) : (term573 _91401 _91404 s f _38257 _38258) = (term613 _91401 _91404 f s _38257 _38258).
Proof. exact (@lem3565530 (term574 _91401 _91404 _38257 f _38258) (term181 _91401 _38258 s) (_38257 = _38258)). Qed.
Lemma lem3565547 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3565548 {_91401 : Type'} (_38257 : _91401) (_38258 : _91401) (s : _91401 -> Prop) : (term614 _91401 s _38257 _38258) = (term615 _91401 _38257 _38258 s).
Proof. exact (@lem3565547 (_38257 = _38258) (term181 _91401 _38258 s)). Qed.
Lemma lem3565556 {_91401 _91404 : Type'} (_38257 : _91401) (f : _91401 -> _91404) (_38258 : _91401) : (term616 _91401 _91404 _38257 f _38258) = (term616 _91401 _91404 _38257 f _38258).
Proof. exact (eq_refl (term616 _91401 _91404 _38257 f _38258)). Qed.
Lemma lem3565557 {_91401 _91404 : Type'} (f : _91401 -> _91404) (_38257 : _91401) (_38258 : _91401) (s : _91401 -> Prop) : (term613 _91401 _91404 f s _38257 _38258) = (term617 _91401 _91404 f _38257 _38258 s).
Proof. exact (MK_COMB (@lem3565556 _91401 _91404 _38257 f _38258) (@lem3565548 _91401 _38257 _38258 s)). Qed.
Lemma lem3565561 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3565562 {_91401 _91404 : Type'} (_38257 : _91401) (f : _91401 -> _91404) (_38258 : _91401) (s : _91401 -> Prop) : (term617 _91401 _91404 f _38257 _38258 s) = (term618 _91401 _91404 _38257 f _38258 s).
Proof. exact (@lem3565561 (_38257 = _38258) (term574 _91401 _91404 _38257 f _38258) (term181 _91401 _38258 s)). Qed.
Lemma lem3565582 {_91401 _91404 : Type'} (_38257 : _91401) (f : _91401 -> _91404) (_38258 : _91401) (s : _91401 -> Prop) : (term613 _91401 _91404 f s _38257 _38258) = (term618 _91401 _91404 _38257 f _38258 s).
Proof. exact (TRANS (@lem3565557 _91401 _91404 f _38257 _38258 s) (@lem3565562 _91401 _91404 _38257 f _38258 s)). Qed.
Lemma lem3565583 {_91401 _91404 : Type'} (_38257 : _91401) (f : _91401 -> _91404) (_38258 : _91401) (s : _91401 -> Prop) : (term573 _91401 _91404 s f _38257 _38258) = (term618 _91401 _91404 _38257 f _38258 s).
Proof. exact (TRANS (@lem3565531 _91401 _91404 f s _38257 _38258) (@lem3565582 _91401 _91404 _38257 f _38258 s)). Qed.
Lemma lem3565584 {_91401 : Type'} (_38257 : _91401) (s : _91401 -> Prop) : (term290 _91401 _38257 s) = (term290 _91401 _38257 s).
Proof. exact (eq_refl (term290 _91401 _38257 s)). Qed.
Lemma lem3565585 {_91401 _91404 : Type'} (_38257 : _91401) (f : _91401 -> _91404) (_38258 : _91401) (s : _91401 -> Prop) : (term575 _91401 _91404 s f _38257 _38258) = (term619 _91401 _91404 _38257 f _38258 s).
Proof. exact (MK_COMB (@lem3565584 _91401 _38257 s) (@lem3565583 _91401 _91404 _38257 f _38258 s)). Qed.
Lemma lem3565589 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3565590 {_91401 _91404 : Type'} (_38257 : _91401) (f : _91401 -> _91404) (_38258 : _91401) (s : _91401 -> Prop) : (term619 _91401 _91404 _38257 f _38258 s) = (term620 _91401 _91404 _38257 f _38258 s).
Proof. exact (@lem3565589 (_38257 = _38258) (term181 _91401 _38257 s) (term621 _91401 _91404 _38257 f _38258 s)). Qed.
Lemma lem3565606 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3565607 {_91401 _91404 : Type'} (f : _91401 -> _91404) (_38257 : _91401) (_38258 : _91401) (s : _91401 -> Prop) : (term622 _91401 _91404 _38257 f _38258 s) = (term623 _91401 _91404 f _38257 _38258 s).
Proof. exact (@lem3565606 (term574 _91401 _91404 _38257 f _38258) (term181 _91401 _38257 s) (term181 _91401 _38258 s)). Qed.
Lemma lem3565625 {_91401 : Type'} (_38257 : _91401) (_38258 : _91401) : (term624 _91401 _38257 _38258) = (term624 _91401 _38257 _38258).
Proof. exact (eq_refl (term624 _91401 _38257 _38258)). Qed.
Lemma lem3565626 {_91401 _91404 : Type'} (f : _91401 -> _91404) (_38257 : _91401) (_38258 : _91401) (s : _91401 -> Prop) : (term620 _91401 _91404 _38257 f _38258 s) = (term625 _91401 _91404 f _38257 _38258 s).
Proof. exact (MK_COMB (@lem3565625 _91401 _38257 _38258) (@lem3565607 _91401 _91404 f _38257 _38258 s)). Qed.
Lemma lem3565637 {_91401 _91404 : Type'} (f : _91401 -> _91404) (_38257 : _91401) (_38258 : _91401) (s : _91401 -> Prop) : (term619 _91401 _91404 _38257 f _38258 s) = (term625 _91401 _91404 f _38257 _38258 s).
Proof. exact (TRANS (@lem3565590 _91401 _91404 _38257 f _38258 s) (@lem3565626 _91401 _91404 f _38257 _38258 s)). Qed.
Lemma lem3565638 {_91401 _91404 : Type'} (f : _91401 -> _91404) (_38257 : _91401) (_38258 : _91401) (s : _91401 -> Prop) : (term575 _91401 _91404 s f _38257 _38258) = (term625 _91401 _91404 f _38257 _38258 s).
Proof. exact (TRANS (@lem3565585 _91401 _91404 _38257 f _38258 s) (@lem3565637 _91401 _91404 f _38257 _38258 s)). Qed.
Lemma lem3565639 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3565640 {_91401 _91404 : Type'} (f : _91401 -> _91404) (_38257 : _91401) (_38258 : _91401) (s : _91401 -> Prop) : (term626 _91401 _91404 s f _38257 _38258) = (term627 _91401 _91404 f _38257 _38258 s).
Proof. exact (MK_COMB (@lem3565639) (@lem3565638 _91401 _91404 f _38257 _38258 s)). Qed.
Lemma lem3565666 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3565667 {_91401 _91404 : Type'} (_38257 : _91401) (f : _91401 -> _91404) (_38258 : _91401) (s : _91401 -> Prop) : (term289 _91401 _91404 s _38257 f _38258) = (term621 _91401 _91404 _38257 f _38258 s).
Proof. exact (@lem3565666 (term574 _91401 _91404 _38257 f _38258) (term181 _91401 _38258 s)). Qed.
Lemma lem3565675 {_91401 : Type'} (_38257 : _91401) (s : _91401 -> Prop) : (term290 _91401 _38257 s) = (term290 _91401 _38257 s).
Proof. exact (eq_refl (term290 _91401 _38257 s)). Qed.
Lemma lem3565676 {_91401 _91404 : Type'} (_38257 : _91401) (f : _91401 -> _91404) (_38258 : _91401) (s : _91401 -> Prop) : (term292 _91401 _91404 s _38257 f _38258) = (term622 _91401 _91404 _38257 f _38258 s).
Proof. exact (MK_COMB (@lem3565675 _91401 _38257 s) (@lem3565667 _91401 _91404 _38257 f _38258 s)). Qed.
Lemma lem3565680 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3565681 {_91401 _91404 : Type'} (f : _91401 -> _91404) (_38257 : _91401) (_38258 : _91401) (s : _91401 -> Prop) : (term622 _91401 _91404 _38257 f _38258 s) = (term623 _91401 _91404 f _38257 _38258 s).
Proof. exact (@lem3565680 (term574 _91401 _91404 _38257 f _38258) (term181 _91401 _38257 s) (term181 _91401 _38258 s)). Qed.
Lemma lem3565699 {_91401 _91404 : Type'} (f : _91401 -> _91404) (_38257 : _91401) (_38258 : _91401) (s : _91401 -> Prop) : (term292 _91401 _91404 s _38257 f _38258) = (term623 _91401 _91404 f _38257 _38258 s).
Proof. exact (TRANS (@lem3565676 _91401 _91404 _38257 f _38258 s) (@lem3565681 _91401 _91404 f _38257 _38258 s)). Qed.
Lemma lem3565700 {_91401 : Type'} (_38257 : _91401) (_38258 : _91401) : (term624 _91401 _38257 _38258) = (term624 _91401 _38257 _38258).
Proof. exact (eq_refl (term624 _91401 _38257 _38258)). Qed.
Lemma lem3565701 {_91401 _91404 : Type'} (f : _91401 -> _91404) (_38257 : _91401) (_38258 : _91401) (s : _91401 -> Prop) : (term628 _91401 _91404 s _38257 f _38258) = (term625 _91401 _91404 f _38257 _38258 s).
Proof. exact (MK_COMB (@lem3565700 _91401 _38257 _38258) (@lem3565699 _91401 _91404 f _38257 _38258 s)). Qed.
Lemma lem3565712 {_91401 _91404 : Type'} (f : _91401 -> _91404) (_38257 : _91401) (_38258 : _91401) (s : _91401 -> Prop) : ((term575 _91401 _91404 s f _38257 _38258) = (term628 _91401 _91404 s _38257 f _38258)) = ((term625 _91401 _91404 f _38257 _38258 s) = (term625 _91401 _91404 f _38257 _38258 s)).
Proof. exact (MK_COMB (@lem3565640 _91401 _91404 f _38257 _38258 s) (@lem3565701 _91401 _91404 f _38257 _38258 s)). Qed.
Lemma lem3565714 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3565715 (x : Prop) : (x = x) = True.
Proof. exact (@lem3565714 Prop x). Qed.
Lemma lem3565716 {_91401 _91404 : Type'} (f : _91401 -> _91404) (_38257 : _91401) (_38258 : _91401) (s : _91401 -> Prop) : ((term625 _91401 _91404 f _38257 _38258 s) = (term625 _91401 _91404 f _38257 _38258 s)) = True.
Proof. exact (@lem3565715 (term625 _91401 _91404 f _38257 _38258 s)). Qed.
Lemma lem3565717 {_91401 _91404 : Type'} (s : _91401 -> Prop) (_38257 : _91401) (f : _91401 -> _91404) (_38258 : _91401) : ((term575 _91401 _91404 s f _38257 _38258) = (term628 _91401 _91404 s _38257 f _38258)) = True.
Proof. exact (TRANS (@lem3565712 _91401 _91404 f _38257 _38258 s) (@lem3565716 _91401 _91404 f _38257 _38258 s)). Qed.
Lemma lem3565718 {_91401 _91404 : Type'} (s : _91401 -> Prop) (_38257 : _91401) (f : _91401 -> _91404) (_38258 : _91401) : True = ((term575 _91401 _91404 s f _38257 _38258) = (term628 _91401 _91404 s _38257 f _38258)).
Proof. exact (SYM (@lem3565717 _91401 _91404 s _38257 f _38258)). Qed.
Lemma lem3565719 {_91401 _91404 : Type'} (s : _91401 -> Prop) (_38257 : _91401) (f : _91401 -> _91404) (_38258 : _91401) : (term575 _91401 _91404 s f _38257 _38258) = (term628 _91401 _91404 s _38257 f _38258).
Proof. exact (EQ_MP (@lem3565718 _91401 _91404 s _38257 f _38258) (@lem0)). Qed.
Lemma lem3565720 {_91401 _91404 : Type'} (_38257 : _91401) (_38258 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term628 _91401 _91404 s _38257 f _38258.
Proof. exact (EQ_MP (@lem3565719 _91401 _91404 s _38257 f _38258) (@lem3565285 _91401 _91404 _38257 _38258 s y f x h1)). Qed.
Lemma lem3565722 (b : Prop) (a : Prop) : (a \/ b) = (term194 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3565723 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (_38257 : _91401) (_38258 : _91401) : (term628 _91401 _91404 s _38257 f _38258) = (term629 _91401 _91404 s f _38257 _38258).
Proof. exact (@lem3565722 (term292 _91401 _91404 s _38257 f _38258) (_38257 = _38258)). Qed.
Lemma lem3565725 (a : Prop) (b : Prop) : (term216 a b) = (term217 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3565726 {_91401 _91404 : Type'} (s : _91401 -> Prop) (_38257 : _91401) (f : _91401 -> _91404) (_38258 : _91401) : (term630 _91401 _91404 s _38257 f _38258) = (term631 _91401 _91404 s _38257 f _38258).
Proof. exact (@lem3565725 (term181 _91401 _38257 s) (term289 _91401 _91404 s _38257 f _38258)). Qed.
Lemma lem3565728 (a : Prop) : (term16 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3565729 {_91401 : Type'} (_38257 : _91401) (s : _91401 -> Prop) : (term196 _91401 _38257 s) = (@IN _91401 _38257 s).
Proof. exact (@lem3565728 (@IN _91401 _38257 s)). Qed.
Lemma lem3565730 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3565731 {_91401 : Type'} (_38257 : _91401) (s : _91401 -> Prop) : (term220 _91401 _38257 s) = (term221 _91401 _38257 s).
Proof. exact (MK_COMB (@lem3565730) (@lem3565729 _91401 _38257 s)). Qed.
Lemma lem3565733 (a : Prop) (b : Prop) : (term216 a b) = (term217 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3565734 {_91401 _91404 : Type'} (s : _91401 -> Prop) (_38257 : _91401) (f : _91401 -> _91404) (_38258 : _91401) : (term632 _91401 _91404 s _38257 f _38258) = (term633 _91401 _91404 s _38257 f _38258).
Proof. exact (@lem3565733 (term181 _91401 _38258 s) (term574 _91401 _91404 _38257 f _38258)). Qed.
Lemma lem3565736 (a : Prop) : (term16 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3565737 {_91401 : Type'} (_38258 : _91401) (s : _91401 -> Prop) : (term196 _91401 _38258 s) = (@IN _91401 _38258 s).
Proof. exact (@lem3565736 (@IN _91401 _38258 s)). Qed.
Lemma lem3565738 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3565739 {_91401 : Type'} (_38258 : _91401) (s : _91401 -> Prop) : (term220 _91401 _38258 s) = (term221 _91401 _38258 s).
Proof. exact (MK_COMB (@lem3565738) (@lem3565737 _91401 _38258 s)). Qed.
Lemma lem3565741 (a : Prop) : (term16 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3565742 {_91401 _91404 : Type'} (_38257 : _91401) (f : _91401 -> _91404) (_38258 : _91401) : (term634 _91401 _91404 _38257 f _38258) = ((f _38257) = (f _38258)).
Proof. exact (@lem3565741 ((f _38257) = (f _38258))). Qed.
Lemma lem3565743 {_91401 _91404 : Type'} (s : _91401 -> Prop) (_38257 : _91401) (f : _91401 -> _91404) (_38258 : _91401) : (term633 _91401 _91404 s _38257 f _38258) = (term294 _91401 _91404 s _38257 f _38258).
Proof. exact (MK_COMB (@lem3565739 _91401 _38258 s) (@lem3565742 _91401 _91404 _38257 f _38258)). Qed.
Lemma lem3565744 {_91401 _91404 : Type'} (s : _91401 -> Prop) (_38257 : _91401) (f : _91401 -> _91404) (_38258 : _91401) : (term632 _91401 _91404 s _38257 f _38258) = (term294 _91401 _91404 s _38257 f _38258).
Proof. exact (TRANS (@lem3565734 _91401 _91404 s _38257 f _38258) (@lem3565743 _91401 _91404 s _38257 f _38258)). Qed.
Lemma lem3565745 {_91401 _91404 : Type'} (s : _91401 -> Prop) (_38257 : _91401) (f : _91401 -> _91404) (_38258 : _91401) : (term631 _91401 _91404 s _38257 f _38258) = (term297 _91401 _91404 s _38257 f _38258).
Proof. exact (MK_COMB (@lem3565731 _91401 _38257 s) (@lem3565744 _91401 _91404 s _38257 f _38258)). Qed.
Lemma lem3565746 {_91401 _91404 : Type'} (s : _91401 -> Prop) (_38257 : _91401) (f : _91401 -> _91404) (_38258 : _91401) : (term630 _91401 _91404 s _38257 f _38258) = (term297 _91401 _91404 s _38257 f _38258).
Proof. exact (TRANS (@lem3565726 _91401 _91404 s _38257 f _38258) (@lem3565745 _91401 _91404 s _38257 f _38258)). Qed.
Lemma lem3565747 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3565748 {_91401 _91404 : Type'} (s : _91401 -> Prop) (_38257 : _91401) (f : _91401 -> _91404) (_38258 : _91401) : (term635 _91401 _91404 s _38257 f _38258) = (term636 _91401 _91404 s _38257 f _38258).
Proof. exact (MK_COMB (@lem3565747) (@lem3565746 _91401 _91404 s _38257 f _38258)). Qed.
Lemma lem3565749 {_91401 : Type'} (_38257 : _91401) (_38258 : _91401) : (_38257 = _38258) = (_38257 = _38258).
Proof. exact (eq_refl (_38257 = _38258)). Qed.
Lemma lem3565750 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (_38257 : _91401) (_38258 : _91401) : (term629 _91401 _91404 s f _38257 _38258) = (term282 _91401 _91404 s f _38257 _38258).
Proof. exact (MK_COMB (@lem3565748 _91401 _91404 s _38257 f _38258) (@lem3565749 _91401 _38257 _38258)). Qed.
Lemma lem3565751 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (_38257 : _91401) (_38258 : _91401) : (term628 _91401 _91404 s _38257 f _38258) = (term282 _91401 _91404 s f _38257 _38258).
Proof. exact (TRANS (@lem3565723 _91401 _91404 s f _38257 _38258) (@lem3565750 _91401 _91404 s f _38257 _38258)). Qed.
Lemma lem3565753 {_91401 _91404 : Type'} (_38270 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term637 _91401 _91404 s f x _38270.
Proof. exact (conj (@lem3565370 _91401 _91404 _38270 s y f x h1) (@lem3565514 _91401 _91404 _38270 s y f x h1)). Qed.
Lemma lem3565754 {_91401 _91404 : Type'} (_38270 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term638 _91401 _91404 s f x _38270.
Proof. exact (conj (@lem3565361 _91401 _91404 _38270 s y f x h1) (@lem3565753 _91401 _91404 _38270 s y f x h1)). Qed.
Lemma lem3565756 {_91401 _91404 : Type'} (_38257 : _91401) (_38258 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term282 _91401 _91404 s f _38257 _38258.
Proof. exact (EQ_MP (@lem3565751 _91401 _91404 s f _38257 _38258) (@lem3565720 _91401 _91404 _38257 _38258 s y f x h1)). Qed.
Lemma lem3565757 {_91401 _91404 : Type'} (_38257 : _91401) (_38258 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term282 _91401 _91404 s f _38257 _38258.
Proof. exact (@lem3565756 _91401 _91404 _38257 _38258 s y f x h1). Qed.
Lemma lem3565758 {_91401 _91404 : Type'} (_38270 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term639 _91401 _91404 s f x _38270.
Proof. exact (@lem3565757 _91401 _91404 (x _38270) (term640 _91401 x _38270) s y f x h1). Qed.
Lemma lem3565761 {_91401 _91404 : Type'} (_38270 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : (x _38270) = (term640 _91401 x _38270).
Proof. exact (@lem3565758 _91401 _91404 _38270 s y f x h1 (@lem3565754 _91401 _91404 _38270 s y f x h1)). Qed.
Lemma lem3565762 {_91401 _91404 : Type'} (_38270 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : (x _38270) = (term640 _91401 x _38270).
Proof. exact (@lem3565761 _91401 _91404 _38270 s y f x h1). Qed.
Lemma lem3565763 {_91401 _91404 : Type'} (_38270 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term641 _91401 x _38270.
Proof. exact (fun h0 : term642 _91401 x _38270 => @lem3565762 _91401 _91404 _38270 s y f x h1). Qed.
Lemma lem3565765 (p : Prop) : (term190 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3565766 {_91401 : Type'} (x : _91401 -> _91401) (_38270 : _91401) : (term641 _91401 x _38270) = ((x _38270) = (term640 _91401 x _38270)).
Proof. exact (@lem3565765 ((x _38270) = (term640 _91401 x _38270))). Qed.
Lemma lem3565767 {_91401 _91404 : Type'} (_38270 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : (x _38270) = (term640 _91401 x _38270).
Proof. exact (EQ_MP (@lem3565766 _91401 x _38270) (@lem3565763 _91401 _91404 _38270 s y f x h1)). Qed.
Lemma lem3565770 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3565772 {_91401 : Type'} (x : _91401 -> _91401) (_38259 : _91401) : (term576 _91401 x _38259) = (term643 _91401 x _38259).
Proof. exact (@lem3565770 (_38259 = (x _38259))). Qed.
Lemma lem3565775 {_91401 _91404 : Type'} (_38259 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term643 _91401 x _38259.
Proof. exact (EQ_MP (@lem3565772 _91401 x _38259) (@lem3565287 _91401 _91404 _38259 s y f x h1)). Qed.
Lemma lem3565776 {_91401 _91404 : Type'} (_38259 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term643 _91401 x _38259.
Proof. exact (@lem3565775 _91401 _91404 _38259 s y f x h1). Qed.
Lemma lem3565777 {_91401 _91404 : Type'} (_38270 : _91401) (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term644 _91401 x _38270.
Proof. exact (@lem3565776 _91401 _91404 (x _38270) s y f x h1). Qed.
Lemma lem3565780 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : False.
Proof. exact (@lem3565777 _91401 _91404 (@el _91401) s y f x h1 (@lem3565767 _91401 _91404 (@el _91401) s y f x h1)). Qed.
Lemma lem3565781 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : term201.
Proof. exact (fun h0 : ~ False => @lem3565780 _91401 _91404 s y f x h1). Qed.
Lemma lem3565783 (p : Prop) : (term190 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3565784 : term201 = False.
Proof. exact (@lem3565783 False). Qed.
Lemma lem3565785 {_91401 _91404 : Type'} (s : _91401 -> Prop) (y : _91404) (f : _91401 -> _91404) (x : _91401 -> _91401) (h1 : term412 _91401 _91404 s y f x) : False.
Proof. exact (EQ_MP (@lem3565784) (@lem3565781 _91401 _91404 s y f x h1)). Qed.
Lemma lem3565822 {_91401 : Type'} (x : _91401) (y : _91401) (z : _91401) : term578 _91401 x y z.
Proof. exact (@lem21385 _91401 x y z). Qed.
Lemma lem3565828 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : @IN _91401 x' s.
Proof. exact (proj1 (@lem3565163 _91401 _91404 x' y' s f g h1)). Qed.
Lemma lem3565829 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : term189 _91401 x' s.
Proof. exact (fun h0 : term181 _91401 x' s => @lem3565828 _91401 _91404 x' y' s f g h1). Qed.
Lemma lem3565831 (p : Prop) : (term190 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3565832 {_91401 : Type'} (x' : _91401) (s : _91401 -> Prop) : (term189 _91401 x' s) = (@IN _91401 x' s).
Proof. exact (@lem3565831 (@IN _91401 x' s)). Qed.
Lemma lem3565833 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : @IN _91401 x' s.
Proof. exact (EQ_MP (@lem3565832 _91401 x' s) (@lem3565829 _91401 _91404 x' y' s f g h1)). Qed.
Lemma lem3565835 {_91404 : Type'} (x : _91404) : x = x.
Proof. exact (@lem21386 _91404 x). Qed.
Lemma lem3565836 {_91404 : Type'} (x : _91404) : x = x.
Proof. exact (@lem3565835 _91404 x). Qed.
Lemma lem3565837 {_91401 _91404 : Type'} (f : _91401 -> _91404) (x' : _91401) : (f x') = (f x').
Proof. exact (@lem3565836 _91404 (f x')). Qed.
Lemma lem3565838 {_91401 _91404 : Type'} (f : _91401 -> _91404) (x' : _91401) : term202 _91401 _91404 f x'.
Proof. exact (fun h0 : term203 _91401 _91404 f x' => @lem3565837 _91401 _91404 f x'). Qed.
Lemma lem3565840 (p : Prop) : (term190 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3565841 {_91401 _91404 : Type'} (f : _91401 -> _91404) (x' : _91401) : (term202 _91401 _91404 f x') = ((f x') = (f x')).
Proof. exact (@lem3565840 ((f x') = (f x'))). Qed.
Lemma lem3565842 {_91401 _91404 : Type'} (f : _91401 -> _91404) (x' : _91401) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3565841 _91401 _91404 f x') (@lem3565838 _91401 _91404 f x')). Qed.
Lemma lem3565848 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3565849 {_91401 _91404 : Type'} (f : _91401 -> _91404) (s : _91401 -> Prop) (g : _91404 -> _91401) (_38260 : _91404) (_38261 : _91401) : (term180 _91401 _91404 s f g _38260 _38261) = (term204 _91401 _91404 f s g _38260 _38261).
Proof. exact (@lem3565848 (term182 _91401 _91404 _38260 f _38261) (term181 _91401 _38261 s) ((g _38260) = _38261)). Qed.
Lemma lem3565865 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3565866 {_91401 _91404 : Type'} (g : _91404 -> _91401) (_38260 : _91404) (_38261 : _91401) (s : _91401 -> Prop) : (term205 _91401 _91404 s g _38260 _38261) = (term206 _91401 _91404 g _38260 _38261 s).
Proof. exact (@lem3565865 ((g _38260) = _38261) (term181 _91401 _38261 s)). Qed.
Lemma lem3565874 {_91401 _91404 : Type'} (_38260 : _91404) (f : _91401 -> _91404) (_38261 : _91401) : (term207 _91401 _91404 _38260 f _38261) = (term207 _91401 _91404 _38260 f _38261).
Proof. exact (eq_refl (term207 _91401 _91404 _38260 f _38261)). Qed.
Lemma lem3565875 {_91401 _91404 : Type'} (f : _91401 -> _91404) (g : _91404 -> _91401) (_38260 : _91404) (_38261 : _91401) (s : _91401 -> Prop) : (term204 _91401 _91404 f s g _38260 _38261) = (term208 _91401 _91404 f g _38260 _38261 s).
Proof. exact (MK_COMB (@lem3565874 _91401 _91404 _38260 f _38261) (@lem3565866 _91401 _91404 g _38260 _38261 s)). Qed.
Lemma lem3565879 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3565880 {_91401 _91404 : Type'} (g : _91404 -> _91401) (_38260 : _91404) (f : _91401 -> _91404) (_38261 : _91401) (s : _91401 -> Prop) : (term208 _91401 _91404 f g _38260 _38261 s) = (term209 _91401 _91404 g _38260 f _38261 s).
Proof. exact (@lem3565879 ((g _38260) = _38261) (term182 _91401 _91404 _38260 f _38261) (term181 _91401 _38261 s)). Qed.
Lemma lem3565900 {_91401 _91404 : Type'} (g : _91404 -> _91401) (_38260 : _91404) (f : _91401 -> _91404) (_38261 : _91401) (s : _91401 -> Prop) : (term204 _91401 _91404 f s g _38260 _38261) = (term209 _91401 _91404 g _38260 f _38261 s).
Proof. exact (TRANS (@lem3565875 _91401 _91404 f g _38260 _38261 s) (@lem3565880 _91401 _91404 g _38260 f _38261 s)). Qed.
Lemma lem3565901 {_91401 _91404 : Type'} (g : _91404 -> _91401) (_38260 : _91404) (f : _91401 -> _91404) (_38261 : _91401) (s : _91401 -> Prop) : (term180 _91401 _91404 s f g _38260 _38261) = (term209 _91401 _91404 g _38260 f _38261 s).
Proof. exact (TRANS (@lem3565849 _91401 _91404 f s g _38260 _38261) (@lem3565900 _91401 _91404 g _38260 f _38261 s)). Qed.
Lemma lem3565902 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3565903 {_91401 _91404 : Type'} (g : _91404 -> _91401) (_38260 : _91404) (f : _91401 -> _91404) (_38261 : _91401) (s : _91401 -> Prop) : (term210 _91401 _91404 s f g _38260 _38261) = (term211 _91401 _91404 g _38260 f _38261 s).
Proof. exact (MK_COMB (@lem3565902) (@lem3565901 _91401 _91404 g _38260 f _38261 s)). Qed.
Lemma lem3565919 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3565920 {_91401 _91404 : Type'} (_38260 : _91404) (f : _91401 -> _91404) (_38261 : _91401) (s : _91401 -> Prop) : (term52 _91401 _91404 s _38260 f _38261) = (term212 _91401 _91404 _38260 f _38261 s).
Proof. exact (@lem3565919 (term182 _91401 _91404 _38260 f _38261) (term181 _91401 _38261 s)). Qed.
Lemma lem3565928 {_91401 _91404 : Type'} (g : _91404 -> _91401) (_38260 : _91404) (_38261 : _91401) : (term213 _91401 _91404 g _38260 _38261) = (term213 _91401 _91404 g _38260 _38261).
Proof. exact (eq_refl (term213 _91401 _91404 g _38260 _38261)). Qed.
Lemma lem3565929 {_91401 _91404 : Type'} (g : _91404 -> _91401) (_38260 : _91404) (f : _91401 -> _91404) (_38261 : _91401) (s : _91401 -> Prop) : (term214 _91401 _91404 g s _38260 f _38261) = (term209 _91401 _91404 g _38260 f _38261 s).
Proof. exact (MK_COMB (@lem3565928 _91401 _91404 g _38260 _38261) (@lem3565920 _91401 _91404 _38260 f _38261 s)). Qed.
Lemma lem3565940 {_91401 _91404 : Type'} (g : _91404 -> _91401) (_38260 : _91404) (f : _91401 -> _91404) (_38261 : _91401) (s : _91401 -> Prop) : ((term180 _91401 _91404 s f g _38260 _38261) = (term214 _91401 _91404 g s _38260 f _38261)) = ((term209 _91401 _91404 g _38260 f _38261 s) = (term209 _91401 _91404 g _38260 f _38261 s)).
Proof. exact (MK_COMB (@lem3565903 _91401 _91404 g _38260 f _38261 s) (@lem3565929 _91401 _91404 g _38260 f _38261 s)). Qed.
Lemma lem3565942 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3565943 (x : Prop) : (x = x) = True.
Proof. exact (@lem3565942 Prop x). Qed.
Lemma lem3565944 {_91401 _91404 : Type'} (g : _91404 -> _91401) (_38260 : _91404) (f : _91401 -> _91404) (_38261 : _91401) (s : _91401 -> Prop) : ((term209 _91401 _91404 g _38260 f _38261 s) = (term209 _91401 _91404 g _38260 f _38261 s)) = True.
Proof. exact (@lem3565943 (term209 _91401 _91404 g _38260 f _38261 s)). Qed.
Lemma lem3565945 {_91401 _91404 : Type'} (g : _91404 -> _91401) (s : _91401 -> Prop) (_38260 : _91404) (f : _91401 -> _91404) (_38261 : _91401) : ((term180 _91401 _91404 s f g _38260 _38261) = (term214 _91401 _91404 g s _38260 f _38261)) = True.
Proof. exact (TRANS (@lem3565940 _91401 _91404 g _38260 f _38261 s) (@lem3565944 _91401 _91404 g _38260 f _38261 s)). Qed.
Lemma lem3565946 {_91401 _91404 : Type'} (g : _91404 -> _91401) (s : _91401 -> Prop) (_38260 : _91404) (f : _91401 -> _91404) (_38261 : _91401) : True = ((term180 _91401 _91404 s f g _38260 _38261) = (term214 _91401 _91404 g s _38260 f _38261)).
Proof. exact (SYM (@lem3565945 _91401 _91404 g s _38260 f _38261)). Qed.
Lemma lem3565947 {_91401 _91404 : Type'} (g : _91404 -> _91401) (s : _91401 -> Prop) (_38260 : _91404) (f : _91401 -> _91404) (_38261 : _91401) : (term180 _91401 _91404 s f g _38260 _38261) = (term214 _91401 _91404 g s _38260 f _38261).
Proof. exact (EQ_MP (@lem3565946 _91401 _91404 g s _38260 f _38261) (@lem0)). Qed.
Lemma lem3565948 {_91401 _91404 : Type'} (_38260 : _91404) (_38261 : _91401) (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : term214 _91401 _91404 g s _38260 f _38261.
Proof. exact (EQ_MP (@lem3565947 _91401 _91404 g s _38260 f _38261) (@lem3565303 _91401 _91404 _38260 _38261 x' y' s f g h1)). Qed.
Lemma lem3565950 (b : Prop) (a : Prop) : (a \/ b) = (term194 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3565951 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (_38260 : _91404) (_38261 : _91401) : (term214 _91401 _91404 g s _38260 f _38261) = (term215 _91401 _91404 s f g _38260 _38261).
Proof. exact (@lem3565950 (term52 _91401 _91404 s _38260 f _38261) ((g _38260) = _38261)). Qed.
Lemma lem3565953 (a : Prop) (b : Prop) : (term216 a b) = (term217 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3565954 {_91401 _91404 : Type'} (s : _91401 -> Prop) (_38260 : _91404) (f : _91401 -> _91404) (_38261 : _91401) : (term218 _91401 _91404 s _38260 f _38261) = (term219 _91401 _91404 s _38260 f _38261).
Proof. exact (@lem3565953 (term181 _91401 _38261 s) (term182 _91401 _91404 _38260 f _38261)). Qed.
Lemma lem3565956 (a : Prop) : (term16 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3565957 {_91401 : Type'} (_38261 : _91401) (s : _91401 -> Prop) : (term196 _91401 _38261 s) = (@IN _91401 _38261 s).
Proof. exact (@lem3565956 (@IN _91401 _38261 s)). Qed.
Lemma lem3565958 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3565959 {_91401 : Type'} (_38261 : _91401) (s : _91401 -> Prop) : (term220 _91401 _38261 s) = (term221 _91401 _38261 s).
Proof. exact (MK_COMB (@lem3565958) (@lem3565957 _91401 _38261 s)). Qed.
Lemma lem3565961 (a : Prop) : (term16 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3565962 {_91401 _91404 : Type'} (_38260 : _91404) (f : _91401 -> _91404) (_38261 : _91401) : (term222 _91401 _91404 _38260 f _38261) = (_38260 = (f _38261)).
Proof. exact (@lem3565961 (_38260 = (f _38261))). Qed.
Lemma lem3565963 {_91401 _91404 : Type'} (s : _91401 -> Prop) (_38260 : _91404) (f : _91401 -> _91404) (_38261 : _91401) : (term219 _91401 _91404 s _38260 f _38261) = (term55 _91401 _91404 s _38260 f _38261).
Proof. exact (MK_COMB (@lem3565959 _91401 _38261 s) (@lem3565962 _91401 _91404 _38260 f _38261)). Qed.
Lemma lem3565964 {_91401 _91404 : Type'} (s : _91401 -> Prop) (_38260 : _91404) (f : _91401 -> _91404) (_38261 : _91401) : (term218 _91401 _91404 s _38260 f _38261) = (term55 _91401 _91404 s _38260 f _38261).
Proof. exact (TRANS (@lem3565954 _91401 _91404 s _38260 f _38261) (@lem3565963 _91401 _91404 s _38260 f _38261)). Qed.
Lemma lem3565965 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3565966 {_91401 _91404 : Type'} (s : _91401 -> Prop) (_38260 : _91404) (f : _91401 -> _91404) (_38261 : _91401) : (term223 _91401 _91404 s _38260 f _38261) = (term224 _91401 _91404 s _38260 f _38261).
Proof. exact (MK_COMB (@lem3565965) (@lem3565964 _91401 _91404 s _38260 f _38261)). Qed.
Lemma lem3565967 {_91401 _91404 : Type'} (g : _91404 -> _91401) (_38260 : _91404) (_38261 : _91401) : ((g _38260) = _38261) = ((g _38260) = _38261).
Proof. exact (eq_refl ((g _38260) = _38261)). Qed.
Lemma lem3565968 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (_38260 : _91404) (_38261 : _91401) : (term215 _91401 _91404 s f g _38260 _38261) = (term29 _91401 _91404 s f g _38260 _38261).
Proof. exact (MK_COMB (@lem3565966 _91401 _91404 s _38260 f _38261) (@lem3565967 _91401 _91404 g _38260 _38261)). Qed.
Lemma lem3565969 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (_38260 : _91404) (_38261 : _91401) : (term214 _91401 _91404 g s _38260 f _38261) = (term29 _91401 _91404 s f g _38260 _38261).
Proof. exact (TRANS (@lem3565951 _91401 _91404 s f g _38260 _38261) (@lem3565968 _91401 _91404 s f g _38260 _38261)). Qed.
Lemma lem3565971 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : term225 _91401 _91404 s f x'.
Proof. exact (conj (@lem3565833 _91401 _91404 x' y' s f g h1) (@lem3565842 _91401 _91404 f x')). Qed.
Lemma lem3565973 {_91401 _91404 : Type'} (_38260 : _91404) (_38261 : _91401) (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : term29 _91401 _91404 s f g _38260 _38261.
Proof. exact (EQ_MP (@lem3565969 _91401 _91404 s f g _38260 _38261) (@lem3565948 _91401 _91404 _38260 _38261 x' y' s f g h1)). Qed.
Lemma lem3565974 {_91401 _91404 : Type'} (_38260 : _91404) (_38261 : _91401) (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : term29 _91401 _91404 s f g _38260 _38261.
Proof. exact (@lem3565973 _91401 _91404 _38260 _38261 x' y' s f g h1). Qed.
Lemma lem3565975 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : term226 _91401 _91404 s g f x'.
Proof. exact (@lem3565974 _91401 _91404 (f x') x' x' y' s f g h1). Qed.
Lemma lem3565978 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : (term38 _91401 _91404 g f x') = x'.
Proof. exact (@lem3565975 _91401 _91404 x' y' s f g h1 (@lem3565971 _91401 _91404 x' y' s f g h1)). Qed.
Lemma lem3565979 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : term199 _91401 _91404 g f x'.
Proof. exact (fun h0 : term183 _91401 _91404 g f x' => @lem3565978 _91401 _91404 x' y' s f g h1). Qed.
Lemma lem3565981 (p : Prop) : (term190 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3565982 {_91401 _91404 : Type'} (g : _91404 -> _91401) (f : _91401 -> _91404) (x' : _91401) : (term199 _91401 _91404 g f x') = ((term38 _91401 _91404 g f x') = x').
Proof. exact (@lem3565981 ((term38 _91401 _91404 g f x') = x')). Qed.
Lemma lem3565983 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : (term38 _91401 _91404 g f x') = x'.
Proof. exact (EQ_MP (@lem3565982 _91401 _91404 g f x') (@lem3565979 _91401 _91404 x' y' s f g h1)). Qed.
Lemma lem3565985 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : @IN _91401 y' s.
Proof. exact (proj1 (@lem3565164 _91401 _91404 x' y' s f g h1)). Qed.
Lemma lem3565986 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : term189 _91401 y' s.
Proof. exact (fun h0 : term181 _91401 y' s => @lem3565985 _91401 _91404 x' y' s f g h1). Qed.
Lemma lem3565988 (p : Prop) : (term190 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3565989 {_91401 : Type'} (y' : _91401) (s : _91401 -> Prop) : (term189 _91401 y' s) = (@IN _91401 y' s).
Proof. exact (@lem3565988 (@IN _91401 y' s)). Qed.
Lemma lem3565990 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : @IN _91401 y' s.
Proof. exact (EQ_MP (@lem3565989 _91401 y' s) (@lem3565986 _91401 _91404 x' y' s f g h1)). Qed.
Lemma lem3565992 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : (f x') = (f y').
Proof. exact (proj2 (@lem3565164 _91401 _91404 x' y' s f g h1)). Qed.
Lemma lem3565993 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : term645 _91401 _91404 x' f y'.
Proof. exact (fun h0 : term574 _91401 _91404 x' f y' => @lem3565992 _91401 _91404 x' y' s f g h1). Qed.
Lemma lem3565995 (p : Prop) : (term190 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3565996 {_91401 _91404 : Type'} (x' : _91401) (f : _91401 -> _91404) (y' : _91401) : (term645 _91401 _91404 x' f y') = ((f x') = (f y')).
Proof. exact (@lem3565995 ((f x') = (f y'))). Qed.
Lemma lem3565997 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : (f x') = (f y').
Proof. exact (EQ_MP (@lem3565996 _91401 _91404 x' f y') (@lem3565993 _91401 _91404 x' y' s f g h1)). Qed.
Lemma lem3565998 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : term294 _91401 _91404 s x' f y'.
Proof. exact (conj (@lem3565990 _91401 _91404 x' y' s f g h1) (@lem3565997 _91401 _91404 x' y' s f g h1)). Qed.
Lemma lem3566000 {_91401 _91404 : Type'} (_38260 : _91404) (_38261 : _91401) (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : term29 _91401 _91404 s f g _38260 _38261.
Proof. exact (EQ_MP (@lem3565969 _91401 _91404 s f g _38260 _38261) (@lem3565948 _91401 _91404 _38260 _38261 x' y' s f g h1)). Qed.
Lemma lem3566001 {_91401 _91404 : Type'} (_38260 : _91404) (_38261 : _91401) (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : term29 _91401 _91404 s f g _38260 _38261.
Proof. exact (@lem3566000 _91401 _91404 _38260 _38261 x' y' s f g h1). Qed.
Lemma lem3566002 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : term646 _91401 _91404 s g f x' y'.
Proof. exact (@lem3566001 _91401 _91404 (f x') y' x' y' s f g h1). Qed.
Lemma lem3566005 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : (term38 _91401 _91404 g f x') = y'.
Proof. exact (@lem3566002 _91401 _91404 x' y' s f g h1 (@lem3565998 _91401 _91404 x' y' s f g h1)). Qed.
Lemma lem3566006 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : term647 _91401 _91404 g f x' y'.
Proof. exact (fun h0 : term648 _91401 _91404 g f x' y' => @lem3566005 _91401 _91404 x' y' s f g h1). Qed.
Lemma lem3566008 (p : Prop) : (term190 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3566009 {_91401 _91404 : Type'} (g : _91404 -> _91401) (f : _91401 -> _91404) (x' : _91401) (y' : _91401) : (term647 _91401 _91404 g f x' y') = ((term38 _91401 _91404 g f x') = y').
Proof. exact (@lem3566008 ((term38 _91401 _91404 g f x') = y')). Qed.
Lemma lem3566010 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : (term38 _91401 _91404 g f x') = y'.
Proof. exact (EQ_MP (@lem3566009 _91401 _91404 g f x' y') (@lem3566006 _91401 _91404 x' y' s f g h1)). Qed.
Lemma lem3566028 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3566029 {_91401 : Type'} (y : _91401) (x : _91401) (z : _91401) : (term591 _91401 x y z) = (term592 _91401 y x z).
Proof. exact (@lem3566028 (y = z) (term577 _91401 x z)). Qed.
Lemma lem3566039 {_91401 : Type'} (x : _91401) (y : _91401) : (term593 _91401 x y) = (term593 _91401 x y).
Proof. exact (eq_refl (term593 _91401 x y)). Qed.
Lemma lem3566040 {_91401 : Type'} (y : _91401) (x : _91401) (z : _91401) : (term578 _91401 x y z) = (term594 _91401 y x z).
Proof. exact (MK_COMB (@lem3566039 _91401 x y) (@lem3566029 _91401 y x z)). Qed.
Lemma lem3566044 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3566045 {_91401 : Type'} (y : _91401) (x : _91401) (z : _91401) : (term594 _91401 y x z) = (term595 _91401 y x z).
Proof. exact (@lem3566044 (y = z) (term577 _91401 x y) (term577 _91401 x z)). Qed.
Lemma lem3566067 {_91401 : Type'} (y : _91401) (x : _91401) (z : _91401) : (term578 _91401 x y z) = (term595 _91401 y x z).
Proof. exact (TRANS (@lem3566040 _91401 y x z) (@lem3566045 _91401 y x z)). Qed.
Lemma lem3566068 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3566069 {_91401 : Type'} (y : _91401) (x : _91401) (z : _91401) : (term596 _91401 x y z) = (term597 _91401 y x z).
Proof. exact (MK_COMB (@lem3566068) (@lem3566067 _91401 y x z)). Qed.
Lemma lem3566091 {_91401 : Type'} (y : _91401) (x : _91401) (z : _91401) : (term595 _91401 y x z) = (term595 _91401 y x z).
Proof. exact (eq_refl (term595 _91401 y x z)). Qed.
Lemma lem3566092 {_91401 : Type'} (y : _91401) (x : _91401) (z : _91401) : ((term578 _91401 x y z) = (term595 _91401 y x z)) = ((term595 _91401 y x z) = (term595 _91401 y x z)).
Proof. exact (MK_COMB (@lem3566069 _91401 y x z) (@lem3566091 _91401 y x z)). Qed.
Lemma lem3566094 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3566095 (x : Prop) : (x = x) = True.
Proof. exact (@lem3566094 Prop x). Qed.
Lemma lem3566096 {_91401 : Type'} (y : _91401) (x : _91401) (z : _91401) : ((term595 _91401 y x z) = (term595 _91401 y x z)) = True.
Proof. exact (@lem3566095 (term595 _91401 y x z)). Qed.
Lemma lem3566097 {_91401 : Type'} (y : _91401) (x : _91401) (z : _91401) : ((term578 _91401 x y z) = (term595 _91401 y x z)) = True.
Proof. exact (TRANS (@lem3566092 _91401 y x z) (@lem3566096 _91401 y x z)). Qed.
Lemma lem3566098 {_91401 : Type'} (y : _91401) (x : _91401) (z : _91401) : True = ((term578 _91401 x y z) = (term595 _91401 y x z)).
Proof. exact (SYM (@lem3566097 _91401 y x z)). Qed.
Lemma lem3566099 {_91401 : Type'} (y : _91401) (x : _91401) (z : _91401) : (term578 _91401 x y z) = (term595 _91401 y x z).
Proof. exact (EQ_MP (@lem3566098 _91401 y x z) (@lem0)). Qed.
Lemma lem3566100 {_91401 : Type'} (y : _91401) (x : _91401) (z : _91401) : term595 _91401 y x z.
Proof. exact (EQ_MP (@lem3566099 _91401 y x z) (@lem3565822 _91401 x y z)). Qed.
Lemma lem3566102 (b : Prop) (a : Prop) : (a \/ b) = (term194 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3566103 {_91401 : Type'} (x : _91401) (y : _91401) (z : _91401) : (term595 _91401 y x z) = (term598 _91401 x y z).
Proof. exact (@lem3566102 (term599 _91401 y x z) (y = z)). Qed.
Lemma lem3566105 (a : Prop) (b : Prop) : (term216 a b) = (term217 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3566106 {_91401 : Type'} (y : _91401) (x : _91401) (z : _91401) : (term600 _91401 y x z) = (term601 _91401 y x z).
Proof. exact (@lem3566105 (term577 _91401 x y) (term577 _91401 x z)). Qed.
Lemma lem3566108 (a : Prop) : (term16 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3566109 {_91401 : Type'} (x : _91401) (y : _91401) : (term602 _91401 x y) = (x = y).
Proof. exact (@lem3566108 (x = y)). Qed.
Lemma lem3566110 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3566111 {_91401 : Type'} (x : _91401) (y : _91401) : (term603 _91401 x y) = (term604 _91401 x y).
Proof. exact (MK_COMB (@lem3566110) (@lem3566109 _91401 x y)). Qed.
Lemma lem3566113 (a : Prop) : (term16 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3566114 {_91401 : Type'} (x : _91401) (z : _91401) : (term602 _91401 x z) = (x = z).
Proof. exact (@lem3566113 (x = z)). Qed.
Lemma lem3566115 {_91401 : Type'} (y : _91401) (x : _91401) (z : _91401) : (term601 _91401 y x z) = (term605 _91401 y x z).
Proof. exact (MK_COMB (@lem3566111 _91401 x y) (@lem3566114 _91401 x z)). Qed.
Lemma lem3566116 {_91401 : Type'} (y : _91401) (x : _91401) (z : _91401) : (term600 _91401 y x z) = (term605 _91401 y x z).
Proof. exact (TRANS (@lem3566106 _91401 y x z) (@lem3566115 _91401 y x z)). Qed.
Lemma lem3566117 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3566118 {_91401 : Type'} (y : _91401) (x : _91401) (z : _91401) : (term606 _91401 y x z) = (term607 _91401 y x z).
Proof. exact (MK_COMB (@lem3566117) (@lem3566116 _91401 y x z)). Qed.
Lemma lem3566119 {_91401 : Type'} (y : _91401) (z : _91401) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3566120 {_91401 : Type'} (x : _91401) (y : _91401) (z : _91401) : (term598 _91401 x y z) = (term608 _91401 x y z).
Proof. exact (MK_COMB (@lem3566118 _91401 y x z) (@lem3566119 _91401 y z)). Qed.
Lemma lem3566121 {_91401 : Type'} (x : _91401) (y : _91401) (z : _91401) : (term595 _91401 y x z) = (term608 _91401 x y z).
Proof. exact (TRANS (@lem3566103 _91401 x y z) (@lem3566120 _91401 x y z)). Qed.
Lemma lem3566123 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : term649 _91401 _91404 g f x' y'.
Proof. exact (conj (@lem3565983 _91401 _91404 x' y' s f g h1) (@lem3566010 _91401 _91404 x' y' s f g h1)). Qed.
Lemma lem3566125 {_91401 : Type'} (x : _91401) (y : _91401) (z : _91401) : term608 _91401 x y z.
Proof. exact (EQ_MP (@lem3566121 _91401 x y z) (@lem3566100 _91401 y x z)). Qed.
Lemma lem3566126 {_91401 : Type'} (x : _91401) (y : _91401) (z : _91401) : term608 _91401 x y z.
Proof. exact (@lem3566125 _91401 x y z). Qed.
Lemma lem3566127 {_91401 _91404 : Type'} (g : _91404 -> _91401) (f : _91401 -> _91404) (x' : _91401) (y' : _91401) : term650 _91401 _91404 g f x' y'.
Proof. exact (@lem3566126 _91401 (term38 _91401 _91404 g f x') x' y'). Qed.
Lemma lem3566130 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : x' = y'.
Proof. exact (@lem3566127 _91401 _91404 g f x' y' (@lem3566123 _91401 _91404 x' y' s f g h1)). Qed.
Lemma lem3566131 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : term651 _91401 x' y'.
Proof. exact (fun h0 : term577 _91401 x' y' => @lem3566130 _91401 _91404 x' y' s f g h1). Qed.
Lemma lem3566133 (p : Prop) : (term190 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3566134 {_91401 : Type'} (x' : _91401) (y' : _91401) : (term651 _91401 x' y') = (x' = y').
Proof. exact (@lem3566133 (x' = y')). Qed.
Lemma lem3566135 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : x' = y'.
Proof. exact (EQ_MP (@lem3566134 _91401 x' y') (@lem3566131 _91401 _91404 x' y' s f g h1)). Qed.
Lemma lem3566138 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3566140 {_91401 : Type'} (x' : _91401) (y' : _91401) : (term577 _91401 x' y') = (term652 _91401 x' y').
Proof. exact (@lem3566138 (x' = y')). Qed.
Lemma lem3566143 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : term652 _91401 x' y'.
Proof. exact (EQ_MP (@lem3566140 _91401 x' y') (@lem3565305 _91401 _91404 x' y' s f g h1)). Qed.
Lemma lem3566146 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : False.
Proof. exact (@lem3566143 _91401 _91404 x' y' s f g h1 (@lem3566135 _91401 _91404 x' y' s f g h1)). Qed.
Lemma lem3566147 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : term201.
Proof. exact (fun h0 : ~ False => @lem3566146 _91401 _91404 x' y' s f g h1). Qed.
Lemma lem3566149 (p : Prop) : (term190 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3566150 : term201 = False.
Proof. exact (@lem3566149 False). Qed.
Lemma lem3566151 {_91401 _91404 : Type'} (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term478 _91401 _91404 x' y' s f g) : False.
Proof. exact (EQ_MP (@lem3566150) (@lem3566147 _91401 _91404 x' y' s f g h1)). Qed.
Lemma lem3566152 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term555 _91401 _91404 y x x' y' s f g) : False.
Proof. exact (or_elim (@lem3565155 _91401 _91404 y x x' y' s f g h1) (fun h0 : term412 _91401 _91404 s y f x => @lem3565785 _91401 _91404 s y f x h0) (fun h0 : term478 _91401 _91404 x' y' s f g => @lem3566151 _91401 _91404 x' y' s f g h0)). Qed.
Lemma lem3566153 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term555 _91401 _91404 y x x' y' s f g) : (term555 _91401 _91404 y x x' y' s f g) = False.
Proof. exact (prop_ext (fun h2 : term555 _91401 _91404 y x x' y' s f g => @lem3566152 _91401 _91404 y x x' y' s f g h1) (fun h2 : False => @lem3565155 _91401 _91404 y x x' y' s f g h1)). Qed.
Lemma lem3566154 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (g : _91404 -> _91401) (h1 : term555 _91401 _91404 y x x' y' s f g) : False.
Proof. exact (EQ_MP (@lem3566153 _91401 _91404 y x x' y' s f g h1) (@lem3565155 _91401 _91404 y x x' y' s f g h1)). Qed.
Lemma lem3566155 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (x' : _91401) (y' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (h1 : term558 _91401 _91404 y x x' y' s f) : False.
Proof. exact (ex_elim (@lem3564995 _91401 _91404 y x x' y' s f h1) (fun g : _91404 -> _91401 => fun h0 : term557 _91401 _91404 y x x' y' s f g => @lem3566154 _91401 _91404 y x x' y' s f g h0)). Qed.
Lemma lem3566156 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (x' : _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (h1 : term560 _91401 _91404 y x x' s f) : False.
Proof. exact (ex_elim (@lem3564994 _91401 _91404 y x x' s f h1) (fun y' : _91401 => fun h0 : term559 _91401 _91404 y x x' s f y' => @lem3566155 _91401 _91404 y x x' y' s f h0)). Qed.
Lemma lem3566157 {_91401 _91404 : Type'} (y : _91404) (x : _91401 -> _91401) (s : _91401 -> Prop) (f : _91401 -> _91404) (h1 : term562 _91401 _91404 y x s f) : False.
Proof. exact (ex_elim (@lem3564993 _91401 _91404 y x s f h1) (fun x' : _91401 => fun h0 : term561 _91401 _91404 y x s f x' => @lem3566156 _91401 _91404 y x x' s f h0)). Qed.
Lemma lem3566158 {_91401 _91404 : Type'} (y : _91404) (s : _91401 -> Prop) (f : _91401 -> _91404) (h1 : term564 _91401 _91404 y s f) : False.
Proof. exact (ex_elim (@lem3564992 _91401 _91404 y s f h1) (fun x : _91401 -> _91401 => fun h0 : term563 _91401 _91404 y s f x => @lem3566157 _91401 _91404 y x s f h0)). Qed.
Lemma lem3566159 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (h1 : term287 _91401 _91404 s f) : False.
Proof. exact (ex_elim (@lem3564991 _91401 _91404 s f h1) (fun y : _91404 => fun h0 : term565 _91401 _91404 s f y => @lem3566158 _91401 _91404 y s f h0)). Qed.
Lemma lem3566160 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (h1 : term287 _91401 _91404 s f) : (term287 _91401 _91404 s f) = False.
Proof. exact (prop_ext (fun h2 : term287 _91401 _91404 s f => @lem3566159 _91401 _91404 s f h1) (fun h2 : False => @lem3564316 _91401 _91404 s f h1)). Qed.
Lemma lem3566161 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) (h1 : term287 _91401 _91404 s f) : False.
Proof. exact (EQ_MP (@lem3566160 _91401 _91404 s f h1) (@lem3564316 _91401 _91404 s f h1)). Qed.
Lemma lem3566162 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : term286 _91401 _91404 s f.
Proof. exact (fun h0 : term287 _91401 _91404 s f => @lem3566161 _91401 _91404 s f h0). Qed.
Lemma lem3566163 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term265 _91401 _91404 s f) = (term263 _91401 _91404 s f).
Proof. exact (EQ_MP (@lem3564315 _91401 _91404 s f) (@lem3566162 _91401 _91404 s f)). Qed.
Lemma lem3566168 {_91401 _91404 : Type'} (f : _91401 -> _91404) : term269 _91401 _91404 f.
Proof. exact (fun s : _91401 -> Prop => @lem3566163 _91401 _91404 s f). Qed.
Lemma lem3566173 {_91401 _91404 : Type'} : term273 _91401 _91404.
Proof. exact (fun f : _91401 -> _91404 => @lem3566168 _91401 _91404 f). Qed.
Lemma lem3566174 {_91401 _91404 : Type'} : term274 _91401 _91404.
Proof. exact (EQ_MP (@lem3564311 _91401 _91404) (@lem3566173 _91401 _91404)). Qed.
Lemma lem3566176 {_91401 _91404 : Type'} : term274 _91401 _91404.
Proof. exact (@lem3564160 _91401 _91404 (@lem3566174 _91401 _91404)). Qed.
Lemma lem3566177 {_91401 _91404 : Type'} (h1 : term275 _91401 _91404) : False.
Proof. exact (@lem3566176 _91401 _91404 (@lem3564144 _91401 _91404 h1)). Qed.
Lemma lem3566178 {_91401 _91404 : Type'} (h1 : term275 _91401 _91404) : (term275 _91401 _91404) = False.
Proof. exact (prop_ext (fun h2 : term275 _91401 _91404 => @lem3566177 _91401 _91404 h1) (fun h2 : False => @lem3564144 _91401 _91404 h1)). Qed.
Lemma lem3566179 {_91401 _91404 : Type'} (h1 : term275 _91401 _91404) : False.
Proof. exact (EQ_MP (@lem3566178 _91401 _91404 h1) (@lem3564144 _91401 _91404 h1)). Qed.
Lemma lem3566180 {_91401 _91404 : Type'} : term274 _91401 _91404.
Proof. exact (fun h0 : term275 _91401 _91404 => @lem3566179 _91401 _91404 h0). Qed.
Lemma lem3566181 {_91401 _91404 : Type'} : term273 _91401 _91404.
Proof. exact (EQ_MP (@lem3564143 _91401 _91404) (@lem3566180 _91401 _91404)). Qed.
Lemma lem3566182 {_91401 _91404 : Type'} : term272 _91401 _91404.
Proof. exact (EQ_MP (@lem3564139 _91401 _91404) (@lem3566181 _91401 _91404)). Qed.
