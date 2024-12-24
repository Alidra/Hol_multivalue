Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMAGE_SUBSET_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import IN_IMAGE_spec.
Require Import SUBSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm18394_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Lemma lem3370571 {A B : Type'} (y : B) : term0 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem3370572 {A B : Type'} (y : B) : (term0 A B y) = (term1 A B y).
Proof. exact (eq_refl (term0 A B y)). Qed.
Lemma lem3370573 {A B : Type'} (y : B) : term1 A B y.
Proof. exact (EQ_MP (@lem3370572 A B y) (@lem3370571 A B y)). Qed.
Lemma lem3370574 {A B : Type'} (y : B) (s : A -> Prop) : term2 A B y s.
Proof. exact (@lem3370573 A B y s). Qed.
Lemma lem3370575 {A B : Type'} (y : B) (s : A -> Prop) : (term2 A B y s) = (term3 A B y s).
Proof. exact (eq_refl (term2 A B y s)). Qed.
Lemma lem3370576 {A B : Type'} (y : B) (s : A -> Prop) : term3 A B y s.
Proof. exact (EQ_MP (@lem3370575 A B y s) (@lem3370574 A B y s)). Qed.
Lemma lem3370577 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term4 A B y s f.
Proof. exact (@lem3370576 A B y s f). Qed.
Lemma lem3370578 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term4 A B y s f) = ((term5 A B y f s) = (term6 A B y f s)).
Proof. exact (eq_refl (term4 A B y s f)). Qed.
Lemma lem3370580 {A : Type'} (s : A -> Prop) : term7 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem3370581 {A : Type'} (s : A -> Prop) : (term7 A s) = (term8 A s).
Proof. exact (eq_refl (term7 A s)). Qed.
Lemma lem3370582 {A : Type'} (s : A -> Prop) : term8 A s.
Proof. exact (EQ_MP (@lem3370581 A s) (@lem3370580 A s)). Qed.
Lemma lem3370583 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term9 A s t.
Proof. exact (@lem3370582 A s t). Qed.
Lemma lem3370584 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term9 A s t) = ((@SUBSET A s t) = (term10 A s t)).
Proof. exact (eq_refl (term9 A s t)). Qed.
Lemma lem3370601 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (EQ_MP (@lem3370584 A s t) (@lem3370583 A s t)). Qed.
Lemma lem3370602 {_87593 : Type'} (s : _87593 -> Prop) (t : _87593 -> Prop) : (@SUBSET _87593 s t) = (term10 _87593 s t).
Proof. exact (@lem3370601 _87593 s t). Qed.
Lemma lem3370609 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3370610 {_87593 : Type'} (s : _87593 -> Prop) (t : _87593 -> Prop) : (term11 _87593 s t) = (term12 _87593 s t).
Proof. exact (MK_COMB (@lem3370609) (@lem3370602 _87593 s t)). Qed.
Lemma lem3370612 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (EQ_MP (@lem3370584 A s t) (@lem3370583 A s t)). Qed.
Lemma lem3370613 {_87604 : Type'} (s : _87604 -> Prop) (t : _87604 -> Prop) : (@SUBSET _87604 s t) = (term10 _87604 s t).
Proof. exact (@lem3370612 _87604 s t). Qed.
Lemma lem3370614 {_87593 _87604 : Type'} (s : _87593 -> Prop) (f : _87593 -> _87604) (t : _87593 -> Prop) : (term13 _87593 _87604 s f t) = (term14 _87593 _87604 s f t).
Proof. exact (@lem3370613 _87604 (@IMAGE _87593 _87604 f s) (@IMAGE _87593 _87604 f t)). Qed.
Lemma lem3370622 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term5 A B y f s) = (term6 A B y f s).
Proof. exact (EQ_MP (@lem3370578 A B y f s) (@lem3370577 A B y s f)). Qed.
Lemma lem3370623 {_87593 _87604 : Type'} (y : _87604) (f : _87593 -> _87604) (s : _87593 -> Prop) : (term5 _87593 _87604 y f s) = (term6 _87593 _87604 y f s).
Proof. exact (@lem3370622 _87593 _87604 y f s). Qed.
Lemma lem3370624 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (s : _87593 -> Prop) : (term5 _87593 _87604 x f s) = (term6 _87593 _87604 x f s).
Proof. exact (@lem3370623 _87593 _87604 x f s). Qed.
Lemma lem3370633 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3370634 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (s : _87593 -> Prop) : (term15 _87593 _87604 x f s) = (term16 _87593 _87604 x f s).
Proof. exact (MK_COMB (@lem3370633) (@lem3370624 _87593 _87604 x f s)). Qed.
Lemma lem3370636 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term5 A B y f s) = (term6 A B y f s).
Proof. exact (EQ_MP (@lem3370578 A B y f s) (@lem3370577 A B y s f)). Qed.
Lemma lem3370637 {_87593 _87604 : Type'} (y : _87604) (f : _87593 -> _87604) (s : _87593 -> Prop) : (term5 _87593 _87604 y f s) = (term6 _87593 _87604 y f s).
Proof. exact (@lem3370636 _87593 _87604 y f s). Qed.
Lemma lem3370638 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (t : _87593 -> Prop) : (term5 _87593 _87604 x f t) = (term6 _87593 _87604 x f t).
Proof. exact (@lem3370637 _87593 _87604 x f t). Qed.
Lemma lem3370647 {_87593 _87604 : Type'} (s : _87593 -> Prop) (x : _87604) (f : _87593 -> _87604) (t : _87593 -> Prop) : (term17 _87593 _87604 s x f t) = (term18 _87593 _87604 s x f t).
Proof. exact (MK_COMB (@lem3370634 _87593 _87604 x f s) (@lem3370638 _87593 _87604 x f t)). Qed.
Lemma lem3370650 {_87593 _87604 : Type'} (s : _87593 -> Prop) (f : _87593 -> _87604) (t : _87593 -> Prop) : (term19 _87593 _87604 s f t) = (term20 _87593 _87604 s f t).
Proof. exact (fun_ext (fun x : _87604 => @lem3370647 _87593 _87604 s x f t)). Qed.
Lemma lem3370651 {_87604 : Type'} : (@all _87604) = (@all _87604).
Proof. exact (eq_refl (@all _87604)). Qed.
Lemma lem3370652 {_87593 _87604 : Type'} (s : _87593 -> Prop) (f : _87593 -> _87604) (t : _87593 -> Prop) : (term14 _87593 _87604 s f t) = (term21 _87593 _87604 s f t).
Proof. exact (MK_COMB (@lem3370651 _87604) (@lem3370650 _87593 _87604 s f t)). Qed.
Lemma lem3370657 {_87593 _87604 : Type'} (s : _87593 -> Prop) (f : _87593 -> _87604) (t : _87593 -> Prop) : (term13 _87593 _87604 s f t) = (term21 _87593 _87604 s f t).
Proof. exact (TRANS (@lem3370614 _87593 _87604 s f t) (@lem3370652 _87593 _87604 s f t)). Qed.
Lemma lem3370658 {_87593 _87604 : Type'} (s : _87593 -> Prop) (f : _87593 -> _87604) (t : _87593 -> Prop) : (term22 _87593 _87604 s f t) = (term23 _87593 _87604 s f t).
Proof. exact (MK_COMB (@lem3370610 _87593 s t) (@lem3370657 _87593 _87604 s f t)). Qed.
Lemma lem3370661 {_87593 _87604 : Type'} (s : _87593 -> Prop) (f : _87593 -> _87604) : (term24 _87593 _87604 s f) = (term25 _87593 _87604 s f).
Proof. exact (fun_ext (fun t : _87593 -> Prop => @lem3370658 _87593 _87604 s f t)). Qed.
Lemma lem3370662 {_87593 : Type'} : (@all (_87593 -> Prop)) = (@all (_87593 -> Prop)).
Proof. exact (eq_refl (@all (_87593 -> Prop))). Qed.
Lemma lem3370663 {_87593 _87604 : Type'} (s : _87593 -> Prop) (f : _87593 -> _87604) : (term26 _87593 _87604 s f) = (term27 _87593 _87604 s f).
Proof. exact (MK_COMB (@lem3370662 _87593) (@lem3370661 _87593 _87604 s f)). Qed.
Lemma lem3370668 {_87593 _87604 : Type'} (f : _87593 -> _87604) : (term28 _87593 _87604 f) = (term29 _87593 _87604 f).
Proof. exact (fun_ext (fun s : _87593 -> Prop => @lem3370663 _87593 _87604 s f)). Qed.
Lemma lem3370669 {_87593 : Type'} : (@all (_87593 -> Prop)) = (@all (_87593 -> Prop)).
Proof. exact (eq_refl (@all (_87593 -> Prop))). Qed.
Lemma lem3370670 {_87593 _87604 : Type'} (f : _87593 -> _87604) : (term30 _87593 _87604 f) = (term31 _87593 _87604 f).
Proof. exact (MK_COMB (@lem3370669 _87593) (@lem3370668 _87593 _87604 f)). Qed.
Lemma lem3370675 {_87593 _87604 : Type'} : (term32 _87593 _87604) = (term33 _87593 _87604).
Proof. exact (fun_ext (fun f : _87593 -> _87604 => @lem3370670 _87593 _87604 f)). Qed.
Lemma lem3370676 {_87593 _87604 : Type'} : (@all (_87593 -> _87604)) = (@all (_87593 -> _87604)).
Proof. exact (eq_refl (@all (_87593 -> _87604))). Qed.
Lemma lem3370677 {_87593 _87604 : Type'} : (term34 _87593 _87604) = (term35 _87593 _87604).
Proof. exact (MK_COMB (@lem3370676 _87593 _87604) (@lem3370675 _87593 _87604)). Qed.
Lemma lem3370682 {_87593 _87604 : Type'} : (term35 _87593 _87604) = (term34 _87593 _87604).
Proof. exact (SYM (@lem3370677 _87593 _87604)). Qed.
Lemma lem3370684 (p : Prop) : p = (term36 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3370685 {_87593 _87604 : Type'} : (term35 _87593 _87604) = (term37 _87593 _87604).
Proof. exact (@lem3370684 (term35 _87593 _87604)). Qed.
Lemma lem3370686 {_87593 _87604 : Type'} : (term37 _87593 _87604) = (term35 _87593 _87604).
Proof. exact (SYM (@lem3370685 _87593 _87604)). Qed.
Lemma lem3370687 {_87593 _87604 : Type'} (h1 : term38 _87593 _87604) : term38 _87593 _87604.
Proof. exact (h1). Qed.
Lemma lem3370690 {_87593 _87604 : Type'} (h1 : term37 _87593 _87604) : term37 _87593 _87604.
Proof. exact (h1). Qed.
Lemma lem3370691 {_87593 _87604 : Type'} : term39 _87593 _87604.
Proof. exact (fun h0 : term37 _87593 _87604 => @lem3370690 _87593 _87604 h0). Qed.
Lemma lem3370692 {_87593 _87604 : Type'} (h1 : term39 _87593 _87604) : term39 _87593 _87604.
Proof. exact (h1). Qed.
Lemma lem3370693 {_87593 _87604 : Type'} (h1 : term37 _87593 _87604) : term37 _87593 _87604.
Proof. exact (h1). Qed.
Lemma lem3370694 {_87593 _87604 : Type'} (h1 : term37 _87593 _87604) (h2 : term39 _87593 _87604) : term37 _87593 _87604.
Proof. exact (@lem3370692 _87593 _87604 h2 (@lem3370693 _87593 _87604 h1)). Qed.
Lemma lem3370695 {_87593 _87604 : Type'} (h1 : term37 _87593 _87604) : term40 _87593 _87604.
Proof. exact (fun h0 : term39 _87593 _87604 => @lem3370694 _87593 _87604 h1 h0). Qed.
Lemma lem3370696 {_87593 _87604 : Type'} (h1 : term39 _87593 _87604) : term39 _87593 _87604.
Proof. exact (h1). Qed.
Lemma lem3370697 {_87593 _87604 : Type'} (h1 : term37 _87593 _87604) (h2 : term39 _87593 _87604) : term37 _87593 _87604.
Proof. exact (@lem3370695 _87593 _87604 h1 (@lem3370696 _87593 _87604 h2)). Qed.
Lemma lem3370698 {_87593 _87604 : Type'} (h1 : term39 _87593 _87604) : term39 _87593 _87604.
Proof. exact (fun h0 : term37 _87593 _87604 => @lem3370697 _87593 _87604 h0 h1). Qed.
Lemma lem3370699 {_87593 _87604 : Type'} : term41 _87593 _87604.
Proof. exact (fun h0 : term39 _87593 _87604 => @lem3370698 _87593 _87604 h0). Qed.
Lemma lem3370702 {_87593 _87604 : Type'} : term39 _87593 _87604.
Proof. exact (@lem3370699 _87593 _87604 (@lem3370691 _87593 _87604)). Qed.
Lemma lem3370703 {_87593 _87604 : Type'} : term39 _87593 _87604.
Proof. exact (@lem3370702 _87593 _87604). Qed.
Lemma lem3370705 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3370706 {_87593 _87604 : Type'} : (term37 _87593 _87604) = (term42 _87593 _87604).
Proof. exact (@lem3370705 (term38 _87593 _87604)). Qed.
Lemma lem3370708 (t : Prop) : (term43 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3370709 {_87593 _87604 : Type'} : (term42 _87593 _87604) = (term35 _87593 _87604).
Proof. exact (@lem3370708 (term35 _87593 _87604)). Qed.
Lemma lem3370840 {_87593 _87604 : Type'} : (term37 _87593 _87604) = (term35 _87593 _87604).
Proof. exact (TRANS (@lem3370706 _87593 _87604) (@lem3370709 _87593 _87604)). Qed.
Lemma lem3370845 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (x' : _87593) (t : _87593 -> Prop) : (term44 _87593 _87604 x f x' t) = (term44 _87593 _87604 x f x' t).
Proof. exact (eq_refl (term44 _87593 _87604 x f x' t)). Qed.
Lemma lem3370846 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (t : _87593 -> Prop) : (term45 _87593 _87604 x f t) = (term45 _87593 _87604 x f t).
Proof. exact (fun_ext (fun x' : _87593 => @lem3370845 _87593 _87604 x f x' t)). Qed.
Lemma lem3370847 {_87593 : Type'} : (@ex _87593) = (@ex _87593).
Proof. exact (eq_refl (@ex _87593)). Qed.
Lemma lem3370848 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (t : _87593 -> Prop) : (term6 _87593 _87604 x f t) = (term6 _87593 _87604 x f t).
Proof. exact (MK_COMB (@lem3370847 _87593) (@lem3370846 _87593 _87604 x f t)). Qed.
Lemma lem3370853 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (x' : _87593) (s : _87593 -> Prop) : (term44 _87593 _87604 x f x' s) = (term44 _87593 _87604 x f x' s).
Proof. exact (eq_refl (term44 _87593 _87604 x f x' s)). Qed.
Lemma lem3370854 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (s : _87593 -> Prop) : (term45 _87593 _87604 x f s) = (term45 _87593 _87604 x f s).
Proof. exact (fun_ext (fun x' : _87593 => @lem3370853 _87593 _87604 x f x' s)). Qed.
Lemma lem3370855 {_87593 : Type'} : (@ex _87593) = (@ex _87593).
Proof. exact (eq_refl (@ex _87593)). Qed.
Lemma lem3370856 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (s : _87593 -> Prop) : (term6 _87593 _87604 x f s) = (term6 _87593 _87604 x f s).
Proof. exact (MK_COMB (@lem3370855 _87593) (@lem3370854 _87593 _87604 x f s)). Qed.
Lemma lem3370857 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3370858 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (s : _87593 -> Prop) : (term16 _87593 _87604 x f s) = (term16 _87593 _87604 x f s).
Proof. exact (MK_COMB (@lem3370857) (@lem3370856 _87593 _87604 x f s)). Qed.
Lemma lem3370859 {_87593 _87604 : Type'} (s : _87593 -> Prop) (x : _87604) (f : _87593 -> _87604) (t : _87593 -> Prop) : (term18 _87593 _87604 s x f t) = (term18 _87593 _87604 s x f t).
Proof. exact (MK_COMB (@lem3370858 _87593 _87604 x f s) (@lem3370848 _87593 _87604 x f t)). Qed.
Lemma lem3370860 {_87593 _87604 : Type'} (s : _87593 -> Prop) (f : _87593 -> _87604) (t : _87593 -> Prop) : (term20 _87593 _87604 s f t) = (term20 _87593 _87604 s f t).
Proof. exact (fun_ext (fun x : _87604 => @lem3370859 _87593 _87604 s x f t)). Qed.
Lemma lem3370861 {_87604 : Type'} : (@all _87604) = (@all _87604).
Proof. exact (eq_refl (@all _87604)). Qed.
Lemma lem3370862 {_87593 _87604 : Type'} (s : _87593 -> Prop) (f : _87593 -> _87604) (t : _87593 -> Prop) : (term21 _87593 _87604 s f t) = (term21 _87593 _87604 s f t).
Proof. exact (MK_COMB (@lem3370861 _87604) (@lem3370860 _87593 _87604 s f t)). Qed.
Lemma lem3370867 {_87593 : Type'} (s : _87593 -> Prop) (x : _87593) (t : _87593 -> Prop) : (term46 _87593 s x t) = (term46 _87593 s x t).
Proof. exact (eq_refl (term46 _87593 s x t)). Qed.
Lemma lem3370868 {_87593 : Type'} (s : _87593 -> Prop) (t : _87593 -> Prop) : (term47 _87593 s t) = (term47 _87593 s t).
Proof. exact (fun_ext (fun x : _87593 => @lem3370867 _87593 s x t)). Qed.
Lemma lem3370869 {_87593 : Type'} : (@all _87593) = (@all _87593).
Proof. exact (eq_refl (@all _87593)). Qed.
Lemma lem3370870 {_87593 : Type'} (s : _87593 -> Prop) (t : _87593 -> Prop) : (term10 _87593 s t) = (term10 _87593 s t).
Proof. exact (MK_COMB (@lem3370869 _87593) (@lem3370868 _87593 s t)). Qed.
Lemma lem3370871 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3370872 {_87593 : Type'} (s : _87593 -> Prop) (t : _87593 -> Prop) : (term12 _87593 s t) = (term12 _87593 s t).
Proof. exact (MK_COMB (@lem3370871) (@lem3370870 _87593 s t)). Qed.
Lemma lem3370873 {_87593 _87604 : Type'} (s : _87593 -> Prop) (f : _87593 -> _87604) (t : _87593 -> Prop) : (term23 _87593 _87604 s f t) = (term23 _87593 _87604 s f t).
Proof. exact (MK_COMB (@lem3370872 _87593 s t) (@lem3370862 _87593 _87604 s f t)). Qed.
Lemma lem3370874 {_87593 _87604 : Type'} (s : _87593 -> Prop) (f : _87593 -> _87604) : (term25 _87593 _87604 s f) = (term25 _87593 _87604 s f).
Proof. exact (fun_ext (fun t : _87593 -> Prop => @lem3370873 _87593 _87604 s f t)). Qed.
Lemma lem3370875 {_87593 : Type'} : (@all (_87593 -> Prop)) = (@all (_87593 -> Prop)).
Proof. exact (eq_refl (@all (_87593 -> Prop))). Qed.
Lemma lem3370876 {_87593 _87604 : Type'} (s : _87593 -> Prop) (f : _87593 -> _87604) : (term27 _87593 _87604 s f) = (term27 _87593 _87604 s f).
Proof. exact (MK_COMB (@lem3370875 _87593) (@lem3370874 _87593 _87604 s f)). Qed.
Lemma lem3370877 {_87593 _87604 : Type'} (f : _87593 -> _87604) : (term29 _87593 _87604 f) = (term29 _87593 _87604 f).
Proof. exact (fun_ext (fun s : _87593 -> Prop => @lem3370876 _87593 _87604 s f)). Qed.
Lemma lem3370878 {_87593 : Type'} : (@all (_87593 -> Prop)) = (@all (_87593 -> Prop)).
Proof. exact (eq_refl (@all (_87593 -> Prop))). Qed.
Lemma lem3370879 {_87593 _87604 : Type'} (f : _87593 -> _87604) : (term31 _87593 _87604 f) = (term31 _87593 _87604 f).
Proof. exact (MK_COMB (@lem3370878 _87593) (@lem3370877 _87593 _87604 f)). Qed.
Lemma lem3370880 {_87593 _87604 : Type'} : (term33 _87593 _87604) = (term33 _87593 _87604).
Proof. exact (fun_ext (fun f : _87593 -> _87604 => @lem3370879 _87593 _87604 f)). Qed.
Lemma lem3370881 {_87593 _87604 : Type'} : (@all (_87593 -> _87604)) = (@all (_87593 -> _87604)).
Proof. exact (eq_refl (@all (_87593 -> _87604))). Qed.
Lemma lem3370882 {_87593 _87604 : Type'} : (term35 _87593 _87604) = (term35 _87593 _87604).
Proof. exact (MK_COMB (@lem3370881 _87593 _87604) (@lem3370880 _87593 _87604)). Qed.
Lemma lem3370937 {_87593 _87604 : Type'} : (term37 _87593 _87604) = (term35 _87593 _87604).
Proof. exact (TRANS (@lem3370840 _87593 _87604) (@lem3370882 _87593 _87604)). Qed.
Lemma lem3370938 {_87593 _87604 : Type'} : (term35 _87593 _87604) = (term37 _87593 _87604).
Proof. exact (SYM (@lem3370937 _87593 _87604)). Qed.
Lemma lem3370939 {_87593 : Type'} (s : _87593 -> Prop) (t : _87593 -> Prop) (h1 : term10 _87593 s t) : term10 _87593 s t.
Proof. exact (h1). Qed.
Lemma lem3370940 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (s : _87593 -> Prop) (h1 : term6 _87593 _87604 x f s) : term6 _87593 _87604 x f s.
Proof. exact (h1). Qed.
Lemma lem3370942 (p : Prop) : p = (term36 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3370943 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (t : _87593 -> Prop) : (term6 _87593 _87604 x f t) = (term48 _87593 _87604 x f t).
Proof. exact (@lem3370942 (term6 _87593 _87604 x f t)). Qed.
Lemma lem3370944 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (t : _87593 -> Prop) : (term48 _87593 _87604 x f t) = (term6 _87593 _87604 x f t).
Proof. exact (SYM (@lem3370943 _87593 _87604 x f t)). Qed.
Lemma lem3370945 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (t : _87593 -> Prop) (h1 : term49 _87593 _87604 x f t) : term49 _87593 _87604 x f t.
Proof. exact (h1). Qed.
Lemma lem3370952 {_87593 : Type'} (s : _87593 -> Prop) (x : _87593) (t : _87593 -> Prop) : (term46 _87593 s x t) = (term50 _87593 s x t).
Proof. exact (@lem17265 (@IN _87593 x s) (@IN _87593 x t)). Qed.
Lemma lem3370953 {_87593 : Type'} (s : _87593 -> Prop) (t : _87593 -> Prop) : (term47 _87593 s t) = (term51 _87593 s t).
Proof. exact (fun_ext (fun x : _87593 => @lem3370952 _87593 s x t)). Qed.
Lemma lem3370954 {_87593 : Type'} : (@all _87593) = (@all _87593).
Proof. exact (eq_refl (@all _87593)). Qed.
Lemma lem3371007 {_87593 : Type'} (s : _87593 -> Prop) (t : _87593 -> Prop) : (term10 _87593 s t) = (term52 _87593 s t).
Proof. exact (MK_COMB (@lem3370954 _87593) (@lem3370953 _87593 s t)). Qed.
Lemma lem3371008 {_87593 : Type'} (s : _87593 -> Prop) (t : _87593 -> Prop) (h1 : term10 _87593 s t) : term52 _87593 s t.
Proof. exact (EQ_MP (@lem3371007 _87593 s t) (@lem3370939 _87593 s t h1)). Qed.
Lemma lem3371013 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (x' : _87593) (s : _87593 -> Prop) : (term44 _87593 _87604 x f x' s) = (term44 _87593 _87604 x f x' s).
Proof. exact (eq_refl (term44 _87593 _87604 x f x' s)). Qed.
Lemma lem3371014 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (s : _87593 -> Prop) : (term45 _87593 _87604 x f s) = (term45 _87593 _87604 x f s).
Proof. exact (fun_ext (fun x' : _87593 => @lem3371013 _87593 _87604 x f x' s)). Qed.
Lemma lem3371015 {_87593 : Type'} : (@ex _87593) = (@ex _87593).
Proof. exact (eq_refl (@ex _87593)). Qed.
Lemma lem3371068 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (s : _87593 -> Prop) : (term6 _87593 _87604 x f s) = (term6 _87593 _87604 x f s).
Proof. exact (MK_COMB (@lem3371015 _87593) (@lem3371014 _87593 _87604 x f s)). Qed.
Lemma lem3371069 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (s : _87593 -> Prop) (h1 : term6 _87593 _87604 x f s) : term6 _87593 _87604 x f s.
Proof. exact (EQ_MP (@lem3371068 _87593 _87604 x f s) (@lem3370940 _87593 _87604 x f s h1)). Qed.
Lemma lem3371076 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (x' : _87593) (t : _87593 -> Prop) : (term53 _87593 _87604 x f x' t) = (term54 _87593 _87604 x f x' t).
Proof. exact (@lem17045 (x = (f x')) (@IN _87593 x' t)). Qed.
Lemma lem3371077 {_87593 : Type'} (P : _87593 -> Prop) : (term55 _87593 P) = (term56 _87593 P).
Proof. exact (@lem18394 _87593 P). Qed.
Lemma lem3371078 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (t : _87593 -> Prop) : (term49 _87593 _87604 x f t) = (term57 _87593 _87604 x f t).
Proof. exact (@lem3371077 _87593 (term45 _87593 _87604 x f t)). Qed.
Lemma lem3371079 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (x' : _87593) (t : _87593 -> Prop) : (term58 _87593 _87604 x f t x') = (term44 _87593 _87604 x f x' t).
Proof. exact (eq_refl (term58 _87593 _87604 x f t x')). Qed.
Lemma lem3371080 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3371081 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (x' : _87593) (t : _87593 -> Prop) : (term59 _87593 _87604 x f t x') = (term53 _87593 _87604 x f x' t).
Proof. exact (MK_COMB (@lem3371080) (@lem3371079 _87593 _87604 x f x' t)). Qed.
Lemma lem3371082 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (x' : _87593) (t : _87593 -> Prop) : (term59 _87593 _87604 x f t x') = (term54 _87593 _87604 x f x' t).
Proof. exact (TRANS (@lem3371081 _87593 _87604 x f x' t) (@lem3371076 _87593 _87604 x f x' t)). Qed.
Lemma lem3371083 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (t : _87593 -> Prop) : (term60 _87593 _87604 x f t) = (term61 _87593 _87604 x f t).
Proof. exact (fun_ext (fun x' : _87593 => @lem3371082 _87593 _87604 x f x' t)). Qed.
Lemma lem3371084 {_87593 : Type'} : (@all _87593) = (@all _87593).
Proof. exact (eq_refl (@all _87593)). Qed.
Lemma lem3371085 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (t : _87593 -> Prop) : (term57 _87593 _87604 x f t) = (term62 _87593 _87604 x f t).
Proof. exact (MK_COMB (@lem3371084 _87593) (@lem3371083 _87593 _87604 x f t)). Qed.
Lemma lem3371138 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (t : _87593 -> Prop) : (term49 _87593 _87604 x f t) = (term62 _87593 _87604 x f t).
Proof. exact (TRANS (@lem3371078 _87593 _87604 x f t) (@lem3371085 _87593 _87604 x f t)). Qed.
Lemma lem3371139 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (t : _87593 -> Prop) (h1 : term49 _87593 _87604 x f t) : term62 _87593 _87604 x f t.
Proof. exact (EQ_MP (@lem3371138 _87593 _87604 x f t) (@lem3370945 _87593 _87604 x f t h1)). Qed.
Lemma lem3371155 {_87593 : Type'} (s : _87593 -> Prop) (x : _87593) (t : _87593 -> Prop) : (term50 _87593 s x t) = (term50 _87593 s x t).
Proof. exact (eq_refl (term50 _87593 s x t)). Qed.
Lemma lem3371156 {_87593 : Type'} (s : _87593 -> Prop) (t : _87593 -> Prop) : (term51 _87593 s t) = (term51 _87593 s t).
Proof. exact (fun_ext (fun x : _87593 => @lem3371155 _87593 s x t)). Qed.
Lemma lem3371157 {_87593 : Type'} : (@all _87593) = (@all _87593).
Proof. exact (eq_refl (@all _87593)). Qed.
Lemma lem3371158 {_87593 : Type'} (s : _87593 -> Prop) (t : _87593 -> Prop) : (term52 _87593 s t) = (term52 _87593 s t).
Proof. exact (MK_COMB (@lem3371157 _87593) (@lem3371156 _87593 s t)). Qed.
Lemma lem3371159 {_87593 : Type'} (s : _87593 -> Prop) (t : _87593 -> Prop) (h1 : term10 _87593 s t) : term52 _87593 s t.
Proof. exact (EQ_MP (@lem3371158 _87593 s t) (@lem3371008 _87593 s t h1)). Qed.
Lemma lem3371178 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (x' : _87593) (t : _87593 -> Prop) : (term54 _87593 _87604 x f x' t) = (term54 _87593 _87604 x f x' t).
Proof. exact (eq_refl (term54 _87593 _87604 x f x' t)). Qed.
Lemma lem3371179 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (t : _87593 -> Prop) : (term61 _87593 _87604 x f t) = (term61 _87593 _87604 x f t).
Proof. exact (fun_ext (fun x' : _87593 => @lem3371178 _87593 _87604 x f x' t)). Qed.
Lemma lem3371180 {_87593 : Type'} : (@all _87593) = (@all _87593).
Proof. exact (eq_refl (@all _87593)). Qed.
Lemma lem3371181 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (t : _87593 -> Prop) : (term62 _87593 _87604 x f t) = (term62 _87593 _87604 x f t).
Proof. exact (MK_COMB (@lem3371180 _87593) (@lem3371179 _87593 _87604 x f t)). Qed.
Lemma lem3371182 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (t : _87593 -> Prop) (h1 : term49 _87593 _87604 x f t) : term62 _87593 _87604 x f t.
Proof. exact (EQ_MP (@lem3371181 _87593 _87604 x f t) (@lem3371139 _87593 _87604 x f t h1)). Qed.
Lemma lem3371198 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (x' : _87593) (s : _87593 -> Prop) (h1 : term44 _87593 _87604 x f x' s) : term44 _87593 _87604 x f x' s.
Proof. exact (h1). Qed.
Lemma lem3371208 {_87593 : Type'} (s : _87593 -> Prop) (x : _87593) (t : _87593 -> Prop) : (term50 _87593 s x t) = (term50 _87593 s x t).
Proof. exact (eq_refl (term50 _87593 s x t)). Qed.
Lemma lem3371209 {_87593 : Type'} (s : _87593 -> Prop) (t : _87593 -> Prop) : (term51 _87593 s t) = (term51 _87593 s t).
Proof. exact (fun_ext (fun x : _87593 => @lem3371208 _87593 s x t)). Qed.
Lemma lem3371210 {_87593 : Type'} : (@all _87593) = (@all _87593).
Proof. exact (eq_refl (@all _87593)). Qed.
Lemma lem3371212 {_87593 : Type'} (s : _87593 -> Prop) (t : _87593 -> Prop) : (term52 _87593 s t) = (term52 _87593 s t).
Proof. exact (MK_COMB (@lem3371210 _87593) (@lem3371209 _87593 s t)). Qed.
Lemma lem3371213 {_87593 : Type'} (s : _87593 -> Prop) (t : _87593 -> Prop) (h1 : term10 _87593 s t) : term52 _87593 s t.
Proof. exact (EQ_MP (@lem3371212 _87593 s t) (@lem3371159 _87593 s t h1)). Qed.
Lemma lem3371221 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (x' : _87593) (t : _87593 -> Prop) : (term54 _87593 _87604 x f x' t) = (term54 _87593 _87604 x f x' t).
Proof. exact (eq_refl (term54 _87593 _87604 x f x' t)). Qed.
Lemma lem3371222 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (t : _87593 -> Prop) : (term61 _87593 _87604 x f t) = (term61 _87593 _87604 x f t).
Proof. exact (fun_ext (fun x' : _87593 => @lem3371221 _87593 _87604 x f x' t)). Qed.
Lemma lem3371223 {_87593 : Type'} : (@all _87593) = (@all _87593).
Proof. exact (eq_refl (@all _87593)). Qed.
Lemma lem3371225 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (t : _87593 -> Prop) : (term62 _87593 _87604 x f t) = (term62 _87593 _87604 x f t).
Proof. exact (MK_COMB (@lem3371223 _87593) (@lem3371222 _87593 _87604 x f t)). Qed.
Lemma lem3371226 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (t : _87593 -> Prop) (h1 : term49 _87593 _87604 x f t) : term62 _87593 _87604 x f t.
Proof. exact (EQ_MP (@lem3371225 _87593 _87604 x f t) (@lem3371182 _87593 _87604 x f t h1)). Qed.
Lemma lem3371235 {_87593 : Type'} (_35244 : _87593) (s : _87593 -> Prop) (t : _87593 -> Prop) (h1 : term10 _87593 s t) : term63 _87593 s t _35244.
Proof. exact (@lem3371213 _87593 s t h1 _35244). Qed.
Lemma lem3371236 {_87593 : Type'} (s : _87593 -> Prop) (_35244 : _87593) (t : _87593 -> Prop) : (term63 _87593 s t _35244) = (term50 _87593 s _35244 t).
Proof. exact (eq_refl (term63 _87593 s t _35244)). Qed.
Lemma lem3371238 {_87593 _87604 : Type'} (_35245 : _87593) (x : _87604) (f : _87593 -> _87604) (t : _87593 -> Prop) (h1 : term49 _87593 _87604 x f t) : term64 _87593 _87604 x f t _35245.
Proof. exact (@lem3371226 _87593 _87604 x f t h1 _35245). Qed.
Lemma lem3371239 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (_35245 : _87593) (t : _87593 -> Prop) : (term64 _87593 _87604 x f t _35245) = (term54 _87593 _87604 x f _35245 t).
Proof. exact (eq_refl (term64 _87593 _87604 x f t _35245)). Qed.
Lemma lem3371252 {_87593 _87604 : Type'} (_35245 : _87593) (x : _87604) (f : _87593 -> _87604) (t : _87593 -> Prop) (h1 : term49 _87593 _87604 x f t) : term54 _87593 _87604 x f _35245 t.
Proof. exact (EQ_MP (@lem3371239 _87593 _87604 x f _35245 t) (@lem3371238 _87593 _87604 _35245 x f t h1)). Qed.
Lemma lem3371254 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (x' : _87593) (s : _87593 -> Prop) (h1 : term44 _87593 _87604 x f x' s) : x = (f x').
Proof. exact (proj1 (@lem3371198 _87593 _87604 x f x' s h1)). Qed.
Lemma lem3371284 {_87593 : Type'} (_35244 : _87593) (s : _87593 -> Prop) (t : _87593 -> Prop) (h1 : term10 _87593 s t) : term50 _87593 s _35244 t.
Proof. exact (EQ_MP (@lem3371236 _87593 s _35244 t) (@lem3371235 _87593 _35244 s t h1)). Qed.
Lemma lem3371285 {_87593 _87604 : Type'} (f : _87593 -> _87604) (_35245 : _87593) (t : _87593 -> Prop) : (term65 _87593 _87604 f _35245 t) = (term65 _87593 _87604 f _35245 t).
Proof. exact (eq_refl (term65 _87593 _87604 f _35245 t)). Qed.
Lemma lem3371286 {_87593 _87604 : Type'} (_35245 : _87593) (t : _87593 -> Prop) (x : _87604) (f : _87593 -> _87604) (x' : _87593) (s : _87593 -> Prop) (h1 : term44 _87593 _87604 x f x' s) : (term66 _87593 _87604 f _35245 t x) = (term67 _87593 _87604 _35245 t f x').
Proof. exact (MK_COMB (@lem3371285 _87593 _87604 f _35245 t) (@lem3371254 _87593 _87604 x f x' s h1)). Qed.
Lemma lem3371287 {_87593 _87604 : Type'} (x' : _87593) (f : _87593 -> _87604) (_35245 : _87593) (t : _87593 -> Prop) : (term67 _87593 _87604 _35245 t f x') = (term68 _87593 _87604 x' f _35245 t).
Proof. exact (eq_refl (term67 _87593 _87604 _35245 t f x')). Qed.
Lemma lem3371288 {_87593 _87604 : Type'} (f : _87593 -> _87604) (_35245 : _87593) (t : _87593 -> Prop) (x : _87604) : (term69 _87593 _87604 f _35245 t x) = (term69 _87593 _87604 f _35245 t x).
Proof. exact (eq_refl (term69 _87593 _87604 f _35245 t x)). Qed.
Lemma lem3371289 {_87593 _87604 : Type'} (x : _87604) (x' : _87593) (f : _87593 -> _87604) (_35245 : _87593) (t : _87593 -> Prop) : ((term66 _87593 _87604 f _35245 t x) = (term67 _87593 _87604 _35245 t f x')) = ((term66 _87593 _87604 f _35245 t x) = (term68 _87593 _87604 x' f _35245 t)).
Proof. exact (MK_COMB (@lem3371288 _87593 _87604 f _35245 t x) (@lem3371287 _87593 _87604 x' f _35245 t)). Qed.
Lemma lem3371290 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (_35245 : _87593) (t : _87593 -> Prop) : (term66 _87593 _87604 f _35245 t x) = (term54 _87593 _87604 x f _35245 t).
Proof. exact (eq_refl (term66 _87593 _87604 f _35245 t x)). Qed.
Lemma lem3371291 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3371292 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (_35245 : _87593) (t : _87593 -> Prop) : (term69 _87593 _87604 f _35245 t x) = (term70 _87593 _87604 x f _35245 t).
Proof. exact (MK_COMB (@lem3371291) (@lem3371290 _87593 _87604 x f _35245 t)). Qed.
Lemma lem3371293 {_87593 _87604 : Type'} (x' : _87593) (f : _87593 -> _87604) (_35245 : _87593) (t : _87593 -> Prop) : (term68 _87593 _87604 x' f _35245 t) = (term68 _87593 _87604 x' f _35245 t).
Proof. exact (eq_refl (term68 _87593 _87604 x' f _35245 t)). Qed.
Lemma lem3371294 {_87593 _87604 : Type'} (x : _87604) (x' : _87593) (f : _87593 -> _87604) (_35245 : _87593) (t : _87593 -> Prop) : ((term66 _87593 _87604 f _35245 t x) = (term68 _87593 _87604 x' f _35245 t)) = ((term54 _87593 _87604 x f _35245 t) = (term68 _87593 _87604 x' f _35245 t)).
Proof. exact (MK_COMB (@lem3371292 _87593 _87604 x f _35245 t) (@lem3371293 _87593 _87604 x' f _35245 t)). Qed.
Lemma lem3371295 {_87593 _87604 : Type'} (x : _87604) (x' : _87593) (f : _87593 -> _87604) (_35245 : _87593) (t : _87593 -> Prop) : ((term66 _87593 _87604 f _35245 t x) = (term67 _87593 _87604 _35245 t f x')) = ((term54 _87593 _87604 x f _35245 t) = (term68 _87593 _87604 x' f _35245 t)).
Proof. exact (TRANS (@lem3371289 _87593 _87604 x x' f _35245 t) (@lem3371294 _87593 _87604 x x' f _35245 t)). Qed.
Lemma lem3371296 {_87593 _87604 : Type'} (_35245 : _87593) (t : _87593 -> Prop) (x : _87604) (f : _87593 -> _87604) (x' : _87593) (s : _87593 -> Prop) (h1 : term44 _87593 _87604 x f x' s) : (term54 _87593 _87604 x f _35245 t) = (term68 _87593 _87604 x' f _35245 t).
Proof. exact (EQ_MP (@lem3371295 _87593 _87604 x x' f _35245 t) (@lem3371286 _87593 _87604 _35245 t x f x' s h1)). Qed.
Lemma lem3371297 {_87593 _87604 : Type'} (_35245 : _87593) (t : _87593 -> Prop) (x : _87604) (f : _87593 -> _87604) (x' : _87593) (s : _87593 -> Prop) (h1 : term49 _87593 _87604 x f t) (h2 : term44 _87593 _87604 x f x' s) : term68 _87593 _87604 x' f _35245 t.
Proof. exact (EQ_MP (@lem3371296 _87593 _87604 _35245 t x f x' s h2) (@lem3371252 _87593 _87604 _35245 x f t h1)). Qed.
Lemma lem3371346 {_87604 : Type'} (x : _87604) : x = x.
Proof. exact (@lem21386 _87604 x). Qed.
Lemma lem3371347 {_87604 : Type'} (x : _87604) : x = x.
Proof. exact (@lem3371346 _87604 x). Qed.
Lemma lem3371348 {_87593 _87604 : Type'} (f : _87593 -> _87604) (x' : _87593) : (f x') = (f x').
Proof. exact (@lem3371347 _87604 (f x')). Qed.
Lemma lem3371349 {_87593 _87604 : Type'} (f : _87593 -> _87604) (x' : _87593) : term71 _87593 _87604 f x'.
Proof. exact (fun h0 : term72 _87593 _87604 f x' => @lem3371348 _87593 _87604 f x'). Qed.
Lemma lem3371351 (p : Prop) : (term73 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3371352 {_87593 _87604 : Type'} (f : _87593 -> _87604) (x' : _87593) : (term71 _87593 _87604 f x') = ((f x') = (f x')).
Proof. exact (@lem3371351 ((f x') = (f x'))). Qed.
Lemma lem3371353 {_87593 _87604 : Type'} (f : _87593 -> _87604) (x' : _87593) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3371352 _87593 _87604 f x') (@lem3371349 _87593 _87604 f x')). Qed.
Lemma lem3371355 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (x' : _87593) (s : _87593 -> Prop) (h1 : term44 _87593 _87604 x f x' s) : @IN _87593 x' s.
Proof. exact (proj2 (@lem3371198 _87593 _87604 x f x' s h1)). Qed.
Lemma lem3371356 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (x' : _87593) (s : _87593 -> Prop) (h1 : term44 _87593 _87604 x f x' s) : term74 _87593 x' s.
Proof. exact (fun h0 : term75 _87593 x' s => @lem3371355 _87593 _87604 x f x' s h1). Qed.
Lemma lem3371358 (p : Prop) : (term73 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3371359 {_87593 : Type'} (x' : _87593) (s : _87593 -> Prop) : (term74 _87593 x' s) = (@IN _87593 x' s).
Proof. exact (@lem3371358 (@IN _87593 x' s)). Qed.
Lemma lem3371360 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (x' : _87593) (s : _87593 -> Prop) (h1 : term44 _87593 _87604 x f x' s) : @IN _87593 x' s.
Proof. exact (EQ_MP (@lem3371359 _87593 x' s) (@lem3371356 _87593 _87604 x f x' s h1)). Qed.
Lemma lem3371366 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3371367 {_87593 : Type'} (t : _87593 -> Prop) (_35244 : _87593) (s : _87593 -> Prop) : (term50 _87593 s _35244 t) = (term76 _87593 t _35244 s).
Proof. exact (@lem3371366 (@IN _87593 _35244 t) (term75 _87593 _35244 s)). Qed.
Lemma lem3371373 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3371374 {_87593 : Type'} (t : _87593 -> Prop) (_35244 : _87593) (s : _87593 -> Prop) : (term77 _87593 s _35244 t) = (term78 _87593 t _35244 s).
Proof. exact (MK_COMB (@lem3371373) (@lem3371367 _87593 t _35244 s)). Qed.
Lemma lem3371380 {_87593 : Type'} (t : _87593 -> Prop) (_35244 : _87593) (s : _87593 -> Prop) : (term76 _87593 t _35244 s) = (term76 _87593 t _35244 s).
Proof. exact (eq_refl (term76 _87593 t _35244 s)). Qed.
Lemma lem3371381 {_87593 : Type'} (t : _87593 -> Prop) (_35244 : _87593) (s : _87593 -> Prop) : ((term50 _87593 s _35244 t) = (term76 _87593 t _35244 s)) = ((term76 _87593 t _35244 s) = (term76 _87593 t _35244 s)).
Proof. exact (MK_COMB (@lem3371374 _87593 t _35244 s) (@lem3371380 _87593 t _35244 s)). Qed.
Lemma lem3371383 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3371384 (x : Prop) : (x = x) = True.
Proof. exact (@lem3371383 Prop x). Qed.
Lemma lem3371385 {_87593 : Type'} (t : _87593 -> Prop) (_35244 : _87593) (s : _87593 -> Prop) : ((term76 _87593 t _35244 s) = (term76 _87593 t _35244 s)) = True.
Proof. exact (@lem3371384 (term76 _87593 t _35244 s)). Qed.
Lemma lem3371386 {_87593 : Type'} (t : _87593 -> Prop) (_35244 : _87593) (s : _87593 -> Prop) : ((term50 _87593 s _35244 t) = (term76 _87593 t _35244 s)) = True.
Proof. exact (TRANS (@lem3371381 _87593 t _35244 s) (@lem3371385 _87593 t _35244 s)). Qed.
Lemma lem3371387 {_87593 : Type'} (t : _87593 -> Prop) (_35244 : _87593) (s : _87593 -> Prop) : True = ((term50 _87593 s _35244 t) = (term76 _87593 t _35244 s)).
Proof. exact (SYM (@lem3371386 _87593 t _35244 s)). Qed.
Lemma lem3371388 {_87593 : Type'} (t : _87593 -> Prop) (_35244 : _87593) (s : _87593 -> Prop) : (term50 _87593 s _35244 t) = (term76 _87593 t _35244 s).
Proof. exact (EQ_MP (@lem3371387 _87593 t _35244 s) (@lem0)). Qed.
Lemma lem3371389 {_87593 : Type'} (_35244 : _87593) (s : _87593 -> Prop) (t : _87593 -> Prop) (h1 : term10 _87593 s t) : term76 _87593 t _35244 s.
Proof. exact (EQ_MP (@lem3371388 _87593 t _35244 s) (@lem3371284 _87593 _35244 s t h1)). Qed.
Lemma lem3371391 (b : Prop) (a : Prop) : (a \/ b) = (term79 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3371392 {_87593 : Type'} (s : _87593 -> Prop) (_35244 : _87593) (t : _87593 -> Prop) : (term76 _87593 t _35244 s) = (term80 _87593 s _35244 t).
Proof. exact (@lem3371391 (term75 _87593 _35244 s) (@IN _87593 _35244 t)). Qed.
Lemma lem3371394 (a : Prop) : (term43 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3371395 {_87593 : Type'} (_35244 : _87593) (s : _87593 -> Prop) : (term81 _87593 _35244 s) = (@IN _87593 _35244 s).
Proof. exact (@lem3371394 (@IN _87593 _35244 s)). Qed.
Lemma lem3371396 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3371397 {_87593 : Type'} (_35244 : _87593) (s : _87593 -> Prop) : (term82 _87593 _35244 s) = (term83 _87593 _35244 s).
Proof. exact (MK_COMB (@lem3371396) (@lem3371395 _87593 _35244 s)). Qed.
Lemma lem3371398 {_87593 : Type'} (_35244 : _87593) (t : _87593 -> Prop) : (@IN _87593 _35244 t) = (@IN _87593 _35244 t).
Proof. exact (eq_refl (@IN _87593 _35244 t)). Qed.
Lemma lem3371399 {_87593 : Type'} (s : _87593 -> Prop) (_35244 : _87593) (t : _87593 -> Prop) : (term80 _87593 s _35244 t) = (term46 _87593 s _35244 t).
Proof. exact (MK_COMB (@lem3371397 _87593 _35244 s) (@lem3371398 _87593 _35244 t)). Qed.
Lemma lem3371400 {_87593 : Type'} (s : _87593 -> Prop) (_35244 : _87593) (t : _87593 -> Prop) : (term76 _87593 t _35244 s) = (term46 _87593 s _35244 t).
Proof. exact (TRANS (@lem3371392 _87593 s _35244 t) (@lem3371399 _87593 s _35244 t)). Qed.
Lemma lem3371403 {_87593 : Type'} (_35244 : _87593) (s : _87593 -> Prop) (t : _87593 -> Prop) (h1 : term10 _87593 s t) : term46 _87593 s _35244 t.
Proof. exact (EQ_MP (@lem3371400 _87593 s _35244 t) (@lem3371389 _87593 _35244 s t h1)). Qed.
Lemma lem3371404 {_87593 : Type'} (_35244 : _87593) (s : _87593 -> Prop) (t : _87593 -> Prop) (h1 : term10 _87593 s t) : term46 _87593 s _35244 t.
Proof. exact (@lem3371403 _87593 _35244 s t h1). Qed.
Lemma lem3371405 {_87593 : Type'} (x' : _87593) (s : _87593 -> Prop) (t : _87593 -> Prop) (h1 : term10 _87593 s t) : term46 _87593 s x' t.
Proof. exact (@lem3371404 _87593 x' s t h1). Qed.
Lemma lem3371408 {_87593 _87604 : Type'} (t : _87593 -> Prop) (x : _87604) (f : _87593 -> _87604) (x' : _87593) (s : _87593 -> Prop) (h1 : term10 _87593 s t) (h2 : term44 _87593 _87604 x f x' s) : @IN _87593 x' t.
Proof. exact (@lem3371405 _87593 x' s t h1 (@lem3371360 _87593 _87604 x f x' s h2)). Qed.
Lemma lem3371409 {_87593 _87604 : Type'} (t : _87593 -> Prop) (x : _87604) (f : _87593 -> _87604) (x' : _87593) (s : _87593 -> Prop) (h1 : term10 _87593 s t) (h2 : term44 _87593 _87604 x f x' s) : term74 _87593 x' t.
Proof. exact (fun h0 : term75 _87593 x' t => @lem3371408 _87593 _87604 t x f x' s h1 h2). Qed.
Lemma lem3371411 (p : Prop) : (term73 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3371412 {_87593 : Type'} (x' : _87593) (t : _87593 -> Prop) : (term74 _87593 x' t) = (@IN _87593 x' t).
Proof. exact (@lem3371411 (@IN _87593 x' t)). Qed.
Lemma lem3371413 {_87593 _87604 : Type'} (t : _87593 -> Prop) (x : _87604) (f : _87593 -> _87604) (x' : _87593) (s : _87593 -> Prop) (h1 : term10 _87593 s t) (h2 : term44 _87593 _87604 x f x' s) : @IN _87593 x' t.
Proof. exact (EQ_MP (@lem3371412 _87593 x' t) (@lem3371409 _87593 _87604 t x f x' s h1 h2)). Qed.
Lemma lem3371415 (a : Prop) (b : Prop) : (term84 a b) = (term85 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3371416 {_87593 _87604 : Type'} (x' : _87593) (f : _87593 -> _87604) (_35245 : _87593) (t : _87593 -> Prop) : (term68 _87593 _87604 x' f _35245 t) = (term86 _87593 _87604 x' f _35245 t).
Proof. exact (@lem3371415 ((f x') = (f _35245)) (@IN _87593 _35245 t)). Qed.
Lemma lem3371418 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3371419 {_87593 _87604 : Type'} (x' : _87593) (f : _87593 -> _87604) (_35245 : _87593) (t : _87593 -> Prop) : (term86 _87593 _87604 x' f _35245 t) = (term87 _87593 _87604 x' f _35245 t).
Proof. exact (@lem3371418 (term88 _87593 _87604 x' f _35245 t)). Qed.
Lemma lem3371420 {_87593 _87604 : Type'} (x' : _87593) (f : _87593 -> _87604) (_35245 : _87593) (t : _87593 -> Prop) : (term68 _87593 _87604 x' f _35245 t) = (term87 _87593 _87604 x' f _35245 t).
Proof. exact (TRANS (@lem3371416 _87593 _87604 x' f _35245 t) (@lem3371419 _87593 _87604 x' f _35245 t)). Qed.
Lemma lem3371422 {_87593 _87604 : Type'} (t : _87593 -> Prop) (x : _87604) (f : _87593 -> _87604) (x' : _87593) (s : _87593 -> Prop) (h1 : term10 _87593 s t) (h2 : term44 _87593 _87604 x f x' s) : term89 _87593 _87604 f x' t.
Proof. exact (conj (@lem3371353 _87593 _87604 f x') (@lem3371413 _87593 _87604 t x f x' s h1 h2)). Qed.
Lemma lem3371424 {_87593 _87604 : Type'} (_35245 : _87593) (t : _87593 -> Prop) (x : _87604) (f : _87593 -> _87604) (x' : _87593) (s : _87593 -> Prop) (h1 : term49 _87593 _87604 x f t) (h2 : term44 _87593 _87604 x f x' s) : term87 _87593 _87604 x' f _35245 t.
Proof. exact (EQ_MP (@lem3371420 _87593 _87604 x' f _35245 t) (@lem3371297 _87593 _87604 _35245 t x f x' s h1 h2)). Qed.
Lemma lem3371425 {_87593 _87604 : Type'} (_35245 : _87593) (t : _87593 -> Prop) (x : _87604) (f : _87593 -> _87604) (x' : _87593) (s : _87593 -> Prop) (h1 : term49 _87593 _87604 x f t) (h2 : term44 _87593 _87604 x f x' s) : term87 _87593 _87604 x' f _35245 t.
Proof. exact (@lem3371424 _87593 _87604 _35245 t x f x' s h1 h2). Qed.
Lemma lem3371426 {_87593 _87604 : Type'} (t : _87593 -> Prop) (x : _87604) (f : _87593 -> _87604) (x' : _87593) (s : _87593 -> Prop) (h1 : term49 _87593 _87604 x f t) (h2 : term44 _87593 _87604 x f x' s) : term90 _87593 _87604 f x' t.
Proof. exact (@lem3371425 _87593 _87604 x' t x f x' s h1 h2). Qed.
Lemma lem3371429 {_87593 _87604 : Type'} (t : _87593 -> Prop) (x : _87604) (f : _87593 -> _87604) (x' : _87593) (s : _87593 -> Prop) (h1 : term10 _87593 s t) (h2 : term49 _87593 _87604 x f t) (h3 : term44 _87593 _87604 x f x' s) : False.
Proof. exact (@lem3371426 _87593 _87604 t x f x' s h2 h3 (@lem3371422 _87593 _87604 t x f x' s h1 h3)). Qed.
Lemma lem3371430 {_87593 _87604 : Type'} (t : _87593 -> Prop) (x : _87604) (f : _87593 -> _87604) (x' : _87593) (s : _87593 -> Prop) (h1 : term10 _87593 s t) (h2 : term49 _87593 _87604 x f t) (h3 : term44 _87593 _87604 x f x' s) : term91.
Proof. exact (fun h0 : ~ False => @lem3371429 _87593 _87604 t x f x' s h1 h2 h3). Qed.
Lemma lem3371432 (p : Prop) : (term73 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3371433 : term91 = False.
Proof. exact (@lem3371432 False). Qed.
Lemma lem3371435 {_87593 _87604 : Type'} (t : _87593 -> Prop) (x : _87604) (f : _87593 -> _87604) (x' : _87593) (s : _87593 -> Prop) (h1 : term10 _87593 s t) (h2 : term49 _87593 _87604 x f t) (h3 : term44 _87593 _87604 x f x' s) : False.
Proof. exact (EQ_MP (@lem3371433) (@lem3371430 _87593 _87604 t x f x' s h1 h2 h3)). Qed.
Lemma lem3371436 {_87593 _87604 : Type'} (t : _87593 -> Prop) (x : _87604) (f : _87593 -> _87604) (x' : _87593) (s : _87593 -> Prop) (h1 : term10 _87593 s t) (h2 : term49 _87593 _87604 x f t) (h3 : term44 _87593 _87604 x f x' s) : (term44 _87593 _87604 x f x' s) = False.
Proof. exact (prop_ext (fun h4 : term44 _87593 _87604 x f x' s => @lem3371435 _87593 _87604 t x f x' s h1 h2 h3) (fun h4 : False => @lem3371198 _87593 _87604 x f x' s h3)). Qed.
Lemma lem3371437 {_87593 _87604 : Type'} (t : _87593 -> Prop) (x : _87604) (f : _87593 -> _87604) (x' : _87593) (s : _87593 -> Prop) (h1 : term10 _87593 s t) (h2 : term49 _87593 _87604 x f t) (h3 : term44 _87593 _87604 x f x' s) : False.
Proof. exact (EQ_MP (@lem3371436 _87593 _87604 t x f x' s h1 h2 h3) (@lem3371198 _87593 _87604 x f x' s h3)). Qed.
Lemma lem3371438 {_87593 _87604 : Type'} (s : _87593 -> Prop) (x : _87604) (f : _87593 -> _87604) (t : _87593 -> Prop) (h1 : term10 _87593 s t) (h2 : term6 _87593 _87604 x f s) (h3 : term49 _87593 _87604 x f t) : False.
Proof. exact (ex_elim (@lem3371069 _87593 _87604 x f s h2) (fun x' : _87593 => fun h0 : term45 _87593 _87604 x f s x' => @lem3371437 _87593 _87604 t x f x' s h1 h3 h0)). Qed.
Lemma lem3371439 {_87593 _87604 : Type'} (s : _87593 -> Prop) (x : _87604) (f : _87593 -> _87604) (t : _87593 -> Prop) (h1 : term10 _87593 s t) (h2 : term6 _87593 _87604 x f s) (h3 : term49 _87593 _87604 x f t) : (term6 _87593 _87604 x f s) = False.
Proof. exact (prop_ext (fun h4 : term6 _87593 _87604 x f s => @lem3371438 _87593 _87604 s x f t h1 h2 h3) (fun h4 : False => @lem3371069 _87593 _87604 x f s h2)). Qed.
Lemma lem3371440 {_87593 _87604 : Type'} (s : _87593 -> Prop) (x : _87604) (f : _87593 -> _87604) (t : _87593 -> Prop) (h1 : term10 _87593 s t) (h2 : term6 _87593 _87604 x f s) (h3 : term49 _87593 _87604 x f t) : False.
Proof. exact (EQ_MP (@lem3371439 _87593 _87604 s x f t h1 h2 h3) (@lem3371069 _87593 _87604 x f s h2)). Qed.
Lemma lem3371441 {_87593 _87604 : Type'} (s : _87593 -> Prop) (x : _87604) (f : _87593 -> _87604) (t : _87593 -> Prop) (h1 : term10 _87593 s t) (h2 : term6 _87593 _87604 x f s) (h3 : term49 _87593 _87604 x f t) : (term49 _87593 _87604 x f t) = False.
Proof. exact (prop_ext (fun h4 : term49 _87593 _87604 x f t => @lem3371440 _87593 _87604 s x f t h1 h2 h3) (fun h4 : False => @lem3370945 _87593 _87604 x f t h3)). Qed.
Lemma lem3371442 {_87593 _87604 : Type'} (s : _87593 -> Prop) (x : _87604) (f : _87593 -> _87604) (t : _87593 -> Prop) (h1 : term10 _87593 s t) (h2 : term6 _87593 _87604 x f s) (h3 : term49 _87593 _87604 x f t) : False.
Proof. exact (EQ_MP (@lem3371441 _87593 _87604 s x f t h1 h2 h3) (@lem3370945 _87593 _87604 x f t h3)). Qed.
Lemma lem3371443 {_87593 _87604 : Type'} (t : _87593 -> Prop) (x : _87604) (f : _87593 -> _87604) (s : _87593 -> Prop) (h1 : term10 _87593 s t) (h2 : term6 _87593 _87604 x f s) : term48 _87593 _87604 x f t.
Proof. exact (fun h0 : term49 _87593 _87604 x f t => @lem3371442 _87593 _87604 s x f t h1 h2 h0). Qed.
Lemma lem3371444 {_87593 _87604 : Type'} (t : _87593 -> Prop) (x : _87604) (f : _87593 -> _87604) (s : _87593 -> Prop) (h1 : term10 _87593 s t) (h2 : term6 _87593 _87604 x f s) : term6 _87593 _87604 x f t.
Proof. exact (EQ_MP (@lem3370944 _87593 _87604 x f t) (@lem3371443 _87593 _87604 t x f s h1 h2)). Qed.
Lemma lem3371445 {_87593 _87604 : Type'} (x : _87604) (f : _87593 -> _87604) (s : _87593 -> Prop) (t : _87593 -> Prop) (h1 : term10 _87593 s t) : term18 _87593 _87604 s x f t.
Proof. exact (fun h0 : term6 _87593 _87604 x f s => @lem3371444 _87593 _87604 t x f s h1 h0). Qed.
Lemma lem3371450 {_87593 _87604 : Type'} (f : _87593 -> _87604) (s : _87593 -> Prop) (t : _87593 -> Prop) (h1 : term10 _87593 s t) : term21 _87593 _87604 s f t.
Proof. exact (fun x : _87604 => @lem3371445 _87593 _87604 x f s t h1). Qed.
Lemma lem3371451 {_87593 _87604 : Type'} (s : _87593 -> Prop) (f : _87593 -> _87604) (t : _87593 -> Prop) : term23 _87593 _87604 s f t.
Proof. exact (fun h0 : term10 _87593 s t => @lem3371450 _87593 _87604 f s t h0). Qed.
Lemma lem3371456 {_87593 _87604 : Type'} (s : _87593 -> Prop) (f : _87593 -> _87604) : term27 _87593 _87604 s f.
Proof. exact (fun t : _87593 -> Prop => @lem3371451 _87593 _87604 s f t). Qed.
Lemma lem3371461 {_87593 _87604 : Type'} (f : _87593 -> _87604) : term31 _87593 _87604 f.
Proof. exact (fun s : _87593 -> Prop => @lem3371456 _87593 _87604 s f). Qed.
Lemma lem3371466 {_87593 _87604 : Type'} : term35 _87593 _87604.
Proof. exact (fun f : _87593 -> _87604 => @lem3371461 _87593 _87604 f). Qed.
Lemma lem3371467 {_87593 _87604 : Type'} : term37 _87593 _87604.
Proof. exact (EQ_MP (@lem3370938 _87593 _87604) (@lem3371466 _87593 _87604)). Qed.
Lemma lem3371469 {_87593 _87604 : Type'} : term37 _87593 _87604.
Proof. exact (@lem3370703 _87593 _87604 (@lem3371467 _87593 _87604)). Qed.
Lemma lem3371470 {_87593 _87604 : Type'} (h1 : term38 _87593 _87604) : False.
Proof. exact (@lem3371469 _87593 _87604 (@lem3370687 _87593 _87604 h1)). Qed.
Lemma lem3371471 {_87593 _87604 : Type'} (h1 : term38 _87593 _87604) : (term38 _87593 _87604) = False.
Proof. exact (prop_ext (fun h2 : term38 _87593 _87604 => @lem3371470 _87593 _87604 h1) (fun h2 : False => @lem3370687 _87593 _87604 h1)). Qed.
Lemma lem3371472 {_87593 _87604 : Type'} (h1 : term38 _87593 _87604) : False.
Proof. exact (EQ_MP (@lem3371471 _87593 _87604 h1) (@lem3370687 _87593 _87604 h1)). Qed.
Lemma lem3371473 {_87593 _87604 : Type'} : term37 _87593 _87604.
Proof. exact (fun h0 : term38 _87593 _87604 => @lem3371472 _87593 _87604 h0). Qed.
Lemma lem3371474 {_87593 _87604 : Type'} : term35 _87593 _87604.
Proof. exact (EQ_MP (@lem3370686 _87593 _87604) (@lem3371473 _87593 _87604)). Qed.
Lemma lem3371475 {_87593 _87604 : Type'} : term34 _87593 _87604.
Proof. exact (EQ_MP (@lem3370682 _87593 _87604) (@lem3371474 _87593 _87604)). Qed.
