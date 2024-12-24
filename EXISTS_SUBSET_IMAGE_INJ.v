Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_SUBSET_IMAGE_INJ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import SUBSET_IMAGE_INJ_spec.
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
Require Import thm17784_spec.
Require Import thm17930_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
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
Require Import thm19012_spec.
Require Import thm19013_spec.
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
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Lemma lem3648776 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3648777 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3648778 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3648777 t1) (@lem3648776 t1)). Qed.
Lemma lem3648779 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3648778 t1 t2). Qed.
Lemma lem3648780 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3648781 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3648780 t1 t2) (@lem3648779 t1 t2)). Qed.
Lemma lem3648782 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3648781 t1 t2 t3). Qed.
Lemma lem3648783 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3648784 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3648783 t1 t2 t3) (@lem3648782 t1 t2 t3)). Qed.
Lemma lem3648785 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3648784 t1 t2 t3)). Qed.
Lemma lem3648786 {A B : Type'} (f : A -> B) : term7 A B f.
Proof. exact (@lem3641047 A B f). Qed.
Lemma lem3648787 {A B : Type'} (f : A -> B) : (term7 A B f) = (term8 A B f).
Proof. exact (eq_refl (term7 A B f)). Qed.
Lemma lem3648788 {A B : Type'} (f : A -> B) : term8 A B f.
Proof. exact (EQ_MP (@lem3648787 A B f) (@lem3648786 A B f)). Qed.
Lemma lem3648789 {A B : Type'} (f : A -> B) (s : B -> Prop) : term9 A B f s.
Proof. exact (@lem3648788 A B f s). Qed.
Lemma lem3648790 {A B : Type'} (s : B -> Prop) (f : A -> B) : (term9 A B f s) = (term10 A B s f).
Proof. exact (eq_refl (term9 A B f s)). Qed.
Lemma lem3648791 {A B : Type'} (s : B -> Prop) (f : A -> B) : term10 A B s f.
Proof. exact (EQ_MP (@lem3648790 A B s f) (@lem3648789 A B f s)). Qed.
Lemma lem3648792 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : term11 A B s f t.
Proof. exact (@lem3648791 A B s f t). Qed.
Lemma lem3648793 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term11 A B s f t) = ((term12 A B s f t) = (term13 A B t s f)).
Proof. exact (eq_refl (term11 A B s f t)). Qed.
Lemma lem3648816 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term12 A B s f t) = (term13 A B t s f).
Proof. exact (EQ_MP (@lem3648793 A B t s f) (@lem3648792 A B s f t)). Qed.
Lemma lem3648817 {_93490 _93497 : Type'} (t : _93490 -> Prop) (s : _93497 -> Prop) (f : _93490 -> _93497) : (term12 _93490 _93497 s f t) = (term13 _93490 _93497 t s f).
Proof. exact (@lem3648816 _93490 _93497 t s f). Qed.
Lemma lem3648818 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term12 _93490 _93497 t f s) = (term13 _93490 _93497 s t f).
Proof. exact (@lem3648817 _93490 _93497 s t f). Qed.
Lemma lem3648847 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3648848 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term14 _93490 _93497 t f s) = (term15 _93490 _93497 s t f).
Proof. exact (MK_COMB (@lem3648847) (@lem3648818 _93490 _93497 s t f)). Qed.
Lemma lem3648849 {_93497 : Type'} (P : type686 _93497) (t : _93497 -> Prop) : (P t) = (P t).
Proof. exact (eq_refl (P t)). Qed.
Lemma lem3648850 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term16 _93490 _93497 f s P t) = (term17 _93490 _93497 s f P t).
Proof. exact (MK_COMB (@lem3648848 _93490 _93497 s t f) (@lem3648849 _93497 P t)). Qed.
Lemma lem3648853 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term18 _93490 _93497 f s P) = (term19 _93490 _93497 s f P).
Proof. exact (fun_ext (fun t : _93497 -> Prop => @lem3648850 _93490 _93497 s f P t)). Qed.
Lemma lem3648854 {_93497 : Type'} : (@ex (_93497 -> Prop)) = (@ex (_93497 -> Prop)).
Proof. exact (eq_refl (@ex (_93497 -> Prop))). Qed.
Lemma lem3648855 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term20 _93490 _93497 f s P) = (term21 _93490 _93497 s f P).
Proof. exact (MK_COMB (@lem3648854 _93497) (@lem3648853 _93490 _93497 s f P)). Qed.
Lemma lem3648860 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3648861 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term22 _93490 _93497 f s P) = (term23 _93490 _93497 s f P).
Proof. exact (MK_COMB (@lem3648860) (@lem3648855 _93490 _93497 s f P)). Qed.
Lemma lem3648888 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term24 _93490 _93497 s P f) = (term24 _93490 _93497 s P f).
Proof. exact (eq_refl (term24 _93490 _93497 s P f)). Qed.
Lemma lem3648889 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : ((term20 _93490 _93497 f s P) = (term24 _93490 _93497 s P f)) = ((term21 _93490 _93497 s f P) = (term24 _93490 _93497 s P f)).
Proof. exact (MK_COMB (@lem3648861 _93490 _93497 s f P) (@lem3648888 _93490 _93497 s P f)). Qed.
Lemma lem3648892 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) : (term25 _93490 _93497 P f) = (term26 _93490 _93497 P f).
Proof. exact (fun_ext (fun s : _93490 -> Prop => @lem3648889 _93490 _93497 s P f)). Qed.
Lemma lem3648893 {_93490 : Type'} : (@all (_93490 -> Prop)) = (@all (_93490 -> Prop)).
Proof. exact (eq_refl (@all (_93490 -> Prop))). Qed.
Lemma lem3648894 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) : (term27 _93490 _93497 P f) = (term28 _93490 _93497 P f).
Proof. exact (MK_COMB (@lem3648893 _93490) (@lem3648892 _93490 _93497 P f)). Qed.
Lemma lem3648899 {_93490 _93497 : Type'} (P : type686 _93497) : (term29 _93490 _93497 P) = (term30 _93490 _93497 P).
Proof. exact (fun_ext (fun f : _93490 -> _93497 => @lem3648894 _93490 _93497 P f)). Qed.
Lemma lem3648900 {_93490 _93497 : Type'} : (@all (_93490 -> _93497)) = (@all (_93490 -> _93497)).
Proof. exact (eq_refl (@all (_93490 -> _93497))). Qed.
Lemma lem3648901 {_93490 _93497 : Type'} (P : type686 _93497) : (term31 _93490 _93497 P) = (term32 _93490 _93497 P).
Proof. exact (MK_COMB (@lem3648900 _93490 _93497) (@lem3648899 _93490 _93497 P)). Qed.
Lemma lem3648906 {_93490 _93497 : Type'} : (term33 _93490 _93497) = (term34 _93490 _93497).
Proof. exact (fun_ext (fun P : type686 _93497 => @lem3648901 _93490 _93497 P)). Qed.
Lemma lem3648907 {_93497 : Type'} : (@all ((_93497 -> Prop) -> Prop)) = (@all ((_93497 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_93497 -> Prop) -> Prop))). Qed.
Lemma lem3648908 {_93490 _93497 : Type'} : (term35 _93490 _93497) = (term36 _93490 _93497).
Proof. exact (MK_COMB (@lem3648907 _93497) (@lem3648906 _93490 _93497)). Qed.
Lemma lem3648913 {_93490 _93497 : Type'} : (term36 _93490 _93497) = (term35 _93490 _93497).
Proof. exact (SYM (@lem3648908 _93490 _93497)). Qed.
Lemma lem3648915 (p : Prop) : p = (term37 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3648916 {_93490 _93497 : Type'} : (term36 _93490 _93497) = (term38 _93490 _93497).
Proof. exact (@lem3648915 (term36 _93490 _93497)). Qed.
Lemma lem3648917 {_93490 _93497 : Type'} : (term38 _93490 _93497) = (term36 _93490 _93497).
Proof. exact (SYM (@lem3648916 _93490 _93497)). Qed.
Lemma lem3648918 {_93490 _93497 : Type'} (h1 : term39 _93490 _93497) : term39 _93490 _93497.
Proof. exact (h1). Qed.
Lemma lem3648921 {_93490 _93497 : Type'} (h1 : term38 _93490 _93497) : term38 _93490 _93497.
Proof. exact (h1). Qed.
Lemma lem3648922 {_93490 _93497 : Type'} : term40 _93490 _93497.
Proof. exact (fun h0 : term38 _93490 _93497 => @lem3648921 _93490 _93497 h0). Qed.
Lemma lem3648923 {_93490 _93497 : Type'} (h1 : term40 _93490 _93497) : term40 _93490 _93497.
Proof. exact (h1). Qed.
Lemma lem3648924 {_93490 _93497 : Type'} (h1 : term38 _93490 _93497) : term38 _93490 _93497.
Proof. exact (h1). Qed.
Lemma lem3648925 {_93490 _93497 : Type'} (h1 : term38 _93490 _93497) (h2 : term40 _93490 _93497) : term38 _93490 _93497.
Proof. exact (@lem3648923 _93490 _93497 h2 (@lem3648924 _93490 _93497 h1)). Qed.
Lemma lem3648926 {_93490 _93497 : Type'} (h1 : term38 _93490 _93497) : term41 _93490 _93497.
Proof. exact (fun h0 : term40 _93490 _93497 => @lem3648925 _93490 _93497 h1 h0). Qed.
Lemma lem3648927 {_93490 _93497 : Type'} (h1 : term40 _93490 _93497) : term40 _93490 _93497.
Proof. exact (h1). Qed.
Lemma lem3648928 {_93490 _93497 : Type'} (h1 : term38 _93490 _93497) (h2 : term40 _93490 _93497) : term38 _93490 _93497.
Proof. exact (@lem3648926 _93490 _93497 h1 (@lem3648927 _93490 _93497 h2)). Qed.
Lemma lem3648929 {_93490 _93497 : Type'} (h1 : term40 _93490 _93497) : term40 _93490 _93497.
Proof. exact (fun h0 : term38 _93490 _93497 => @lem3648928 _93490 _93497 h0 h1). Qed.
Lemma lem3648930 {_93490 _93497 : Type'} : term42 _93490 _93497.
Proof. exact (fun h0 : term40 _93490 _93497 => @lem3648929 _93490 _93497 h0). Qed.
Lemma lem3648933 {_93490 _93497 : Type'} : term40 _93490 _93497.
Proof. exact (@lem3648930 _93490 _93497 (@lem3648922 _93490 _93497)). Qed.
Lemma lem3648934 {_93490 _93497 : Type'} : term40 _93490 _93497.
Proof. exact (@lem3648933 _93490 _93497). Qed.
Lemma lem3648936 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3648937 {_93490 _93497 : Type'} : (term38 _93490 _93497) = (term43 _93490 _93497).
Proof. exact (@lem3648936 (term39 _93490 _93497)). Qed.
Lemma lem3648939 (t : Prop) : (term44 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3648940 {_93490 _93497 : Type'} : (term43 _93490 _93497) = (term36 _93490 _93497).
Proof. exact (@lem3648939 (term36 _93490 _93497)). Qed.
Lemma lem3649119 {_93490 _93497 : Type'} : (term38 _93490 _93497) = (term36 _93490 _93497).
Proof. exact (TRANS (@lem3648937 _93490 _93497) (@lem3648940 _93490 _93497)). Qed.
Lemma lem3649120 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term45 _93490 _93497 P f t) = (term45 _93490 _93497 P f t).
Proof. exact (eq_refl (term45 _93490 _93497 P f t)). Qed.
Lemma lem3649133 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term46 _93490 _93497 t f x y) = (term46 _93490 _93497 t f x y).
Proof. exact (eq_refl (term46 _93490 _93497 t f x y)). Qed.
Lemma lem3649134 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term47 _93490 _93497 t f x) = (term47 _93490 _93497 t f x).
Proof. exact (fun_ext (fun y : _93490 => @lem3649133 _93490 _93497 t f x y)). Qed.
Lemma lem3649135 {_93490 : Type'} : (@all _93490) = (@all _93490).
Proof. exact (eq_refl (@all _93490)). Qed.
Lemma lem3649136 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term48 _93490 _93497 t f x) = (term48 _93490 _93497 t f x).
Proof. exact (MK_COMB (@lem3649135 _93490) (@lem3649134 _93490 _93497 t f x)). Qed.
Lemma lem3649137 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) : (term49 _93490 _93497 t f) = (term49 _93490 _93497 t f).
Proof. exact (fun_ext (fun x : _93490 => @lem3649136 _93490 _93497 t f x)). Qed.
Lemma lem3649138 {_93490 : Type'} : (@all _93490) = (@all _93490).
Proof. exact (eq_refl (@all _93490)). Qed.
Lemma lem3649139 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) : (term50 _93490 _93497 t f) = (term50 _93490 _93497 t f).
Proof. exact (MK_COMB (@lem3649138 _93490) (@lem3649137 _93490 _93497 t f)). Qed.
Lemma lem3649140 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3649141 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) : (term51 _93490 _93497 t f) = (term51 _93490 _93497 t f).
Proof. exact (MK_COMB (@lem3649140) (@lem3649139 _93490 _93497 t f)). Qed.
Lemma lem3649142 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term52 _93490 _93497 P f t) = (term52 _93490 _93497 P f t).
Proof. exact (MK_COMB (@lem3649141 _93490 _93497 t f) (@lem3649120 _93490 _93497 P f t)). Qed.
Lemma lem3649145 {_93490 : Type'} (t : _93490 -> Prop) (s : _93490 -> Prop) : (term53 _93490 t s) = (term53 _93490 t s).
Proof. exact (eq_refl (term53 _93490 t s)). Qed.
Lemma lem3649146 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term54 _93490 _93497 s P f t) = (term54 _93490 _93497 s P f t).
Proof. exact (MK_COMB (@lem3649145 _93490 t s) (@lem3649142 _93490 _93497 P f t)). Qed.
Lemma lem3649147 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term55 _93490 _93497 s P f) = (term55 _93490 _93497 s P f).
Proof. exact (fun_ext (fun t : _93490 -> Prop => @lem3649146 _93490 _93497 s P f t)). Qed.
Lemma lem3649148 {_93490 : Type'} : (@ex (_93490 -> Prop)) = (@ex (_93490 -> Prop)).
Proof. exact (eq_refl (@ex (_93490 -> Prop))). Qed.
Lemma lem3649149 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term24 _93490 _93497 s P f) = (term24 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3649148 _93490) (@lem3649147 _93490 _93497 s P f)). Qed.
Lemma lem3649150 {_93497 : Type'} (P : type686 _93497) (t : _93497 -> Prop) : (P t) = (P t).
Proof. exact (eq_refl (P t)). Qed.
Lemma lem3649151 {_93490 _93497 : Type'} (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (t = (@IMAGE _93490 _93497 f u)) = (t = (@IMAGE _93490 _93497 f u)).
Proof. exact (eq_refl (t = (@IMAGE _93490 _93497 f u))). Qed.
Lemma lem3649164 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term46 _93490 _93497 u f x y) = (term46 _93490 _93497 u f x y).
Proof. exact (eq_refl (term46 _93490 _93497 u f x y)). Qed.
Lemma lem3649165 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term47 _93490 _93497 u f x) = (term47 _93490 _93497 u f x).
Proof. exact (fun_ext (fun y : _93490 => @lem3649164 _93490 _93497 u f x y)). Qed.
Lemma lem3649166 {_93490 : Type'} : (@all _93490) = (@all _93490).
Proof. exact (eq_refl (@all _93490)). Qed.
Lemma lem3649167 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term48 _93490 _93497 u f x) = (term48 _93490 _93497 u f x).
Proof. exact (MK_COMB (@lem3649166 _93490) (@lem3649165 _93490 _93497 u f x)). Qed.
Lemma lem3649168 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) : (term49 _93490 _93497 u f) = (term49 _93490 _93497 u f).
Proof. exact (fun_ext (fun x : _93490 => @lem3649167 _93490 _93497 u f x)). Qed.
Lemma lem3649169 {_93490 : Type'} : (@all _93490) = (@all _93490).
Proof. exact (eq_refl (@all _93490)). Qed.
Lemma lem3649170 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) : (term50 _93490 _93497 u f) = (term50 _93490 _93497 u f).
Proof. exact (MK_COMB (@lem3649169 _93490) (@lem3649168 _93490 _93497 u f)). Qed.
Lemma lem3649171 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3649172 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) : (term51 _93490 _93497 u f) = (term51 _93490 _93497 u f).
Proof. exact (MK_COMB (@lem3649171) (@lem3649170 _93490 _93497 u f)). Qed.
Lemma lem3649173 {_93490 _93497 : Type'} (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term56 _93490 _93497 t f u) = (term56 _93490 _93497 t f u).
Proof. exact (MK_COMB (@lem3649172 _93490 _93497 u f) (@lem3649151 _93490 _93497 t f u)). Qed.
Lemma lem3649176 {_93490 : Type'} (u : _93490 -> Prop) (s : _93490 -> Prop) : (term53 _93490 u s) = (term53 _93490 u s).
Proof. exact (eq_refl (term53 _93490 u s)). Qed.
Lemma lem3649177 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term57 _93490 _93497 s t f u) = (term57 _93490 _93497 s t f u).
Proof. exact (MK_COMB (@lem3649176 _93490 u s) (@lem3649173 _93490 _93497 t f u)). Qed.
Lemma lem3649178 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term58 _93490 _93497 s t f) = (term58 _93490 _93497 s t f).
Proof. exact (fun_ext (fun u : _93490 -> Prop => @lem3649177 _93490 _93497 s t f u)). Qed.
Lemma lem3649179 {_93490 : Type'} : (@ex (_93490 -> Prop)) = (@ex (_93490 -> Prop)).
Proof. exact (eq_refl (@ex (_93490 -> Prop))). Qed.
Lemma lem3649180 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term13 _93490 _93497 s t f) = (term13 _93490 _93497 s t f).
Proof. exact (MK_COMB (@lem3649179 _93490) (@lem3649178 _93490 _93497 s t f)). Qed.
Lemma lem3649181 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3649182 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term15 _93490 _93497 s t f) = (term15 _93490 _93497 s t f).
Proof. exact (MK_COMB (@lem3649181) (@lem3649180 _93490 _93497 s t f)). Qed.
Lemma lem3649183 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term17 _93490 _93497 s f P t) = (term17 _93490 _93497 s f P t).
Proof. exact (MK_COMB (@lem3649182 _93490 _93497 s t f) (@lem3649150 _93497 P t)). Qed.
Lemma lem3649184 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term19 _93490 _93497 s f P) = (term19 _93490 _93497 s f P).
Proof. exact (fun_ext (fun t : _93497 -> Prop => @lem3649183 _93490 _93497 s f P t)). Qed.
Lemma lem3649185 {_93497 : Type'} : (@ex (_93497 -> Prop)) = (@ex (_93497 -> Prop)).
Proof. exact (eq_refl (@ex (_93497 -> Prop))). Qed.
Lemma lem3649186 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term21 _93490 _93497 s f P) = (term21 _93490 _93497 s f P).
Proof. exact (MK_COMB (@lem3649185 _93497) (@lem3649184 _93490 _93497 s f P)). Qed.
Lemma lem3649187 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3649188 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term23 _93490 _93497 s f P) = (term23 _93490 _93497 s f P).
Proof. exact (MK_COMB (@lem3649187) (@lem3649186 _93490 _93497 s f P)). Qed.
Lemma lem3649189 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : ((term21 _93490 _93497 s f P) = (term24 _93490 _93497 s P f)) = ((term21 _93490 _93497 s f P) = (term24 _93490 _93497 s P f)).
Proof. exact (MK_COMB (@lem3649188 _93490 _93497 s f P) (@lem3649149 _93490 _93497 s P f)). Qed.
Lemma lem3649190 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) : (term26 _93490 _93497 P f) = (term26 _93490 _93497 P f).
Proof. exact (fun_ext (fun s : _93490 -> Prop => @lem3649189 _93490 _93497 s P f)). Qed.
Lemma lem3649191 {_93490 : Type'} : (@all (_93490 -> Prop)) = (@all (_93490 -> Prop)).
Proof. exact (eq_refl (@all (_93490 -> Prop))). Qed.
Lemma lem3649192 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) : (term28 _93490 _93497 P f) = (term28 _93490 _93497 P f).
Proof. exact (MK_COMB (@lem3649191 _93490) (@lem3649190 _93490 _93497 P f)). Qed.
Lemma lem3649193 {_93490 _93497 : Type'} (P : type686 _93497) : (term30 _93490 _93497 P) = (term30 _93490 _93497 P).
Proof. exact (fun_ext (fun f : _93490 -> _93497 => @lem3649192 _93490 _93497 P f)). Qed.
Lemma lem3649194 {_93490 _93497 : Type'} : (@all (_93490 -> _93497)) = (@all (_93490 -> _93497)).
Proof. exact (eq_refl (@all (_93490 -> _93497))). Qed.
Lemma lem3649195 {_93490 _93497 : Type'} (P : type686 _93497) : (term32 _93490 _93497 P) = (term32 _93490 _93497 P).
Proof. exact (MK_COMB (@lem3649194 _93490 _93497) (@lem3649193 _93490 _93497 P)). Qed.
Lemma lem3649196 {_93490 _93497 : Type'} : (term34 _93490 _93497) = (term34 _93490 _93497).
Proof. exact (fun_ext (fun P : type686 _93497 => @lem3649195 _93490 _93497 P)). Qed.
Lemma lem3649197 {_93497 : Type'} : (@all ((_93497 -> Prop) -> Prop)) = (@all ((_93497 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_93497 -> Prop) -> Prop))). Qed.
Lemma lem3649198 {_93490 _93497 : Type'} : (term36 _93490 _93497) = (term36 _93490 _93497).
Proof. exact (MK_COMB (@lem3649197 _93497) (@lem3649196 _93490 _93497)). Qed.
Lemma lem3649279 {_93490 _93497 : Type'} : (term38 _93490 _93497) = (term36 _93490 _93497).
Proof. exact (TRANS (@lem3649119 _93490 _93497) (@lem3649198 _93490 _93497)). Qed.
Lemma lem3649280 {_93490 _93497 : Type'} : (term36 _93490 _93497) = (term38 _93490 _93497).
Proof. exact (SYM (@lem3649279 _93490 _93497)). Qed.
Lemma lem3649282 (p : Prop) : p = (term37 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3649283 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : ((term21 _93490 _93497 s f P) = (term24 _93490 _93497 s P f)) = (term59 _93490 _93497 s P f).
Proof. exact (@lem3649282 ((term21 _93490 _93497 s f P) = (term24 _93490 _93497 s P f))). Qed.
Lemma lem3649284 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term59 _93490 _93497 s P f) = ((term21 _93490 _93497 s f P) = (term24 _93490 _93497 s P f)).
Proof. exact (SYM (@lem3649283 _93490 _93497 s P f)). Qed.
Lemma lem3649285 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term60 _93490 _93497 s P f) : term60 _93490 _93497 s P f.
Proof. exact (h1). Qed.
Lemma lem3649296 {_93490 : Type'} (x : _93490) (y : _93490) (u : _93490 -> Prop) : (term61 _93490 x y u) = (term62 _93490 x y u).
Proof. exact (@lem17045 (@IN _93490 x u) (@IN _93490 y u)). Qed.
Lemma lem3649314 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term63 _93490 _93497 f x y) = (term64 _93490 _93497 f x y).
Proof. exact (@lem17930 ((f x) = (f y)) (x = y)). Qed.
Lemma lem3649325 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : _93490) (y : _93490) : (((f x) = (f y)) = (x = y)) = (term65 _93490 _93497 f x y).
Proof. exact (@lem17784 ((f x) = (f y)) (x = y)). Qed.
Lemma lem3649327 {_93490 : Type'} (x : _93490) (y : _93490) (u : _93490 -> Prop) : (term66 _93490 x y u) = (term66 _93490 x y u).
Proof. exact (eq_refl (term66 _93490 x y u)). Qed.
Lemma lem3649328 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term67 _93490 _93497 u f x y) = (term68 _93490 _93497 u f x y).
Proof. exact (MK_COMB (@lem3649327 _93490 x y u) (@lem3649314 _93490 _93497 f x y)). Qed.
Lemma lem3649329 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term69 _93490 _93497 u f x y) = (term67 _93490 _93497 u f x y).
Proof. exact (@lem17362 (term70 _93490 x y u) (((f x) = (f y)) = (x = y))). Qed.
Lemma lem3649330 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term69 _93490 _93497 u f x y) = (term68 _93490 _93497 u f x y).
Proof. exact (TRANS (@lem3649329 _93490 _93497 u f x y) (@lem3649328 _93490 _93497 u f x y)). Qed.
Lemma lem3649331 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3649332 {_93490 : Type'} (x : _93490) (y : _93490) (u : _93490 -> Prop) : (term71 _93490 x y u) = (term72 _93490 x y u).
Proof. exact (MK_COMB (@lem3649331) (@lem3649296 _93490 x y u)). Qed.
Lemma lem3649333 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term73 _93490 _93497 u f x y) = (term74 _93490 _93497 u f x y).
Proof. exact (MK_COMB (@lem3649332 _93490 x y u) (@lem3649325 _93490 _93497 f x y)). Qed.
Lemma lem3649334 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term46 _93490 _93497 u f x y) = (term73 _93490 _93497 u f x y).
Proof. exact (@lem17265 (term70 _93490 x y u) (((f x) = (f y)) = (x = y))). Qed.
Lemma lem3649335 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term46 _93490 _93497 u f x y) = (term74 _93490 _93497 u f x y).
Proof. exact (TRANS (@lem3649334 _93490 _93497 u f x y) (@lem3649333 _93490 _93497 u f x y)). Qed.
Lemma lem3649336 {_93490 : Type'} (P : _93490 -> Prop) : (term75 _93490 P) = (term76 _93490 P).
Proof. exact (@lem18392 _93490 P). Qed.
Lemma lem3649337 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term77 _93490 _93497 u f x) = (term78 _93490 _93497 u f x).
Proof. exact (@lem3649336 _93490 (term47 _93490 _93497 u f x)). Qed.
Lemma lem3649338 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term79 _93490 _93497 u f x y) = (term46 _93490 _93497 u f x y).
Proof. exact (eq_refl (term79 _93490 _93497 u f x y)). Qed.
Lemma lem3649339 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3649340 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term80 _93490 _93497 u f x y) = (term69 _93490 _93497 u f x y).
Proof. exact (MK_COMB (@lem3649339) (@lem3649338 _93490 _93497 u f x y)). Qed.
Lemma lem3649341 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term80 _93490 _93497 u f x y) = (term68 _93490 _93497 u f x y).
Proof. exact (TRANS (@lem3649340 _93490 _93497 u f x y) (@lem3649330 _93490 _93497 u f x y)). Qed.
Lemma lem3649342 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term81 _93490 _93497 u f x) = (term82 _93490 _93497 u f x).
Proof. exact (fun_ext (fun y : _93490 => @lem3649341 _93490 _93497 u f x y)). Qed.
Lemma lem3649343 {_93490 : Type'} : (@ex _93490) = (@ex _93490).
Proof. exact (eq_refl (@ex _93490)). Qed.
Lemma lem3649344 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term78 _93490 _93497 u f x) = (term83 _93490 _93497 u f x).
Proof. exact (MK_COMB (@lem3649343 _93490) (@lem3649342 _93490 _93497 u f x)). Qed.
Lemma lem3649345 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term77 _93490 _93497 u f x) = (term83 _93490 _93497 u f x).
Proof. exact (TRANS (@lem3649337 _93490 _93497 u f x) (@lem3649344 _93490 _93497 u f x)). Qed.
Lemma lem3649346 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term47 _93490 _93497 u f x) = (term84 _93490 _93497 u f x).
Proof. exact (fun_ext (fun y : _93490 => @lem3649335 _93490 _93497 u f x y)). Qed.
Lemma lem3649347 {_93490 : Type'} : (@all _93490) = (@all _93490).
Proof. exact (eq_refl (@all _93490)). Qed.
Lemma lem3649348 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term48 _93490 _93497 u f x) = (term85 _93490 _93497 u f x).
Proof. exact (MK_COMB (@lem3649347 _93490) (@lem3649346 _93490 _93497 u f x)). Qed.
Lemma lem3649349 {_93490 : Type'} (P : _93490 -> Prop) : (term75 _93490 P) = (term76 _93490 P).
Proof. exact (@lem18392 _93490 P). Qed.
Lemma lem3649350 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) : (term86 _93490 _93497 u f) = (term87 _93490 _93497 u f).
Proof. exact (@lem3649349 _93490 (term49 _93490 _93497 u f)). Qed.
Lemma lem3649351 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term88 _93490 _93497 u f x) = (term48 _93490 _93497 u f x).
Proof. exact (eq_refl (term88 _93490 _93497 u f x)). Qed.
Lemma lem3649352 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3649353 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term89 _93490 _93497 u f x) = (term77 _93490 _93497 u f x).
Proof. exact (MK_COMB (@lem3649352) (@lem3649351 _93490 _93497 u f x)). Qed.
Lemma lem3649354 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term89 _93490 _93497 u f x) = (term83 _93490 _93497 u f x).
Proof. exact (TRANS (@lem3649353 _93490 _93497 u f x) (@lem3649345 _93490 _93497 u f x)). Qed.
Lemma lem3649355 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) : (term90 _93490 _93497 u f) = (term91 _93490 _93497 u f).
Proof. exact (fun_ext (fun x : _93490 => @lem3649354 _93490 _93497 u f x)). Qed.
Lemma lem3649356 {_93490 : Type'} : (@ex _93490) = (@ex _93490).
Proof. exact (eq_refl (@ex _93490)). Qed.
Lemma lem3649357 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) : (term87 _93490 _93497 u f) = (term92 _93490 _93497 u f).
Proof. exact (MK_COMB (@lem3649356 _93490) (@lem3649355 _93490 _93497 u f)). Qed.
Lemma lem3649358 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) : (term86 _93490 _93497 u f) = (term92 _93490 _93497 u f).
Proof. exact (TRANS (@lem3649350 _93490 _93497 u f) (@lem3649357 _93490 _93497 u f)). Qed.
Lemma lem3649359 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) : (term49 _93490 _93497 u f) = (term93 _93490 _93497 u f).
Proof. exact (fun_ext (fun x : _93490 => @lem3649348 _93490 _93497 u f x)). Qed.
Lemma lem3649360 {_93490 : Type'} : (@all _93490) = (@all _93490).
Proof. exact (eq_refl (@all _93490)). Qed.
Lemma lem3649361 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) : (term50 _93490 _93497 u f) = (term94 _93490 _93497 u f).
Proof. exact (MK_COMB (@lem3649360 _93490) (@lem3649359 _93490 _93497 u f)). Qed.
Lemma lem3649362 {_93490 _93497 : Type'} (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term95 _93490 _93497 t f u) = (term95 _93490 _93497 t f u).
Proof. exact (eq_refl (term95 _93490 _93497 t f u)). Qed.
Lemma lem3649363 {_93490 _93497 : Type'} (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (t = (@IMAGE _93490 _93497 f u)) = (t = (@IMAGE _93490 _93497 f u)).
Proof. exact (eq_refl (t = (@IMAGE _93490 _93497 f u))). Qed.
Lemma lem3649364 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3649365 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) : (term96 _93490 _93497 u f) = (term97 _93490 _93497 u f).
Proof. exact (MK_COMB (@lem3649364) (@lem3649358 _93490 _93497 u f)). Qed.
Lemma lem3649366 {_93490 _93497 : Type'} (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term98 _93490 _93497 t f u) = (term99 _93490 _93497 t f u).
Proof. exact (MK_COMB (@lem3649365 _93490 _93497 u f) (@lem3649362 _93490 _93497 t f u)). Qed.
Lemma lem3649367 {_93490 _93497 : Type'} (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term100 _93490 _93497 t f u) = (term98 _93490 _93497 t f u).
Proof. exact (@lem17045 (term50 _93490 _93497 u f) (t = (@IMAGE _93490 _93497 f u))). Qed.
Lemma lem3649368 {_93490 _93497 : Type'} (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term100 _93490 _93497 t f u) = (term99 _93490 _93497 t f u).
Proof. exact (TRANS (@lem3649367 _93490 _93497 t f u) (@lem3649366 _93490 _93497 t f u)). Qed.
Lemma lem3649369 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3649370 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) : (term51 _93490 _93497 u f) = (term101 _93490 _93497 u f).
Proof. exact (MK_COMB (@lem3649369) (@lem3649361 _93490 _93497 u f)). Qed.
Lemma lem3649371 {_93490 _93497 : Type'} (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term56 _93490 _93497 t f u) = (term102 _93490 _93497 t f u).
Proof. exact (MK_COMB (@lem3649370 _93490 _93497 u f) (@lem3649363 _93490 _93497 t f u)). Qed.
Lemma lem3649373 {_93490 : Type'} (u : _93490 -> Prop) (s : _93490 -> Prop) : (term103 _93490 u s) = (term103 _93490 u s).
Proof. exact (eq_refl (term103 _93490 u s)). Qed.
Lemma lem3649374 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term104 _93490 _93497 s t f u) = (term105 _93490 _93497 s t f u).
Proof. exact (MK_COMB (@lem3649373 _93490 u s) (@lem3649368 _93490 _93497 t f u)). Qed.
Lemma lem3649375 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term106 _93490 _93497 s t f u) = (term104 _93490 _93497 s t f u).
Proof. exact (@lem17045 (@SUBSET _93490 u s) (term56 _93490 _93497 t f u)). Qed.
Lemma lem3649376 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term106 _93490 _93497 s t f u) = (term105 _93490 _93497 s t f u).
Proof. exact (TRANS (@lem3649375 _93490 _93497 s t f u) (@lem3649374 _93490 _93497 s t f u)). Qed.
Lemma lem3649378 {_93490 : Type'} (u : _93490 -> Prop) (s : _93490 -> Prop) : (term53 _93490 u s) = (term53 _93490 u s).
Proof. exact (eq_refl (term53 _93490 u s)). Qed.
Lemma lem3649379 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term57 _93490 _93497 s t f u) = (term107 _93490 _93497 s t f u).
Proof. exact (MK_COMB (@lem3649378 _93490 u s) (@lem3649371 _93490 _93497 t f u)). Qed.
Lemma lem3649380 {_93490 : Type'} (P : type686 _93490) : (term108 _93490 P) = (term109 _93490 P).
Proof. exact (@lem18394 (_93490 -> Prop) P). Qed.
Lemma lem3649381 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term110 _93490 _93497 s t f) = (term111 _93490 _93497 s t f).
Proof. exact (@lem3649380 _93490 (term58 _93490 _93497 s t f)). Qed.
Lemma lem3649382 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term112 _93490 _93497 s t f u) = (term57 _93490 _93497 s t f u).
Proof. exact (eq_refl (term112 _93490 _93497 s t f u)). Qed.
Lemma lem3649383 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3649384 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term113 _93490 _93497 s t f u) = (term106 _93490 _93497 s t f u).
Proof. exact (MK_COMB (@lem3649383) (@lem3649382 _93490 _93497 s t f u)). Qed.
Lemma lem3649385 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term113 _93490 _93497 s t f u) = (term105 _93490 _93497 s t f u).
Proof. exact (TRANS (@lem3649384 _93490 _93497 s t f u) (@lem3649376 _93490 _93497 s t f u)). Qed.
Lemma lem3649386 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term114 _93490 _93497 s t f) = (term115 _93490 _93497 s t f).
Proof. exact (fun_ext (fun u : _93490 -> Prop => @lem3649385 _93490 _93497 s t f u)). Qed.
Lemma lem3649387 {_93490 : Type'} : (@all (_93490 -> Prop)) = (@all (_93490 -> Prop)).
Proof. exact (eq_refl (@all (_93490 -> Prop))). Qed.
Lemma lem3649388 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term111 _93490 _93497 s t f) = (term116 _93490 _93497 s t f).
Proof. exact (MK_COMB (@lem3649387 _93490) (@lem3649386 _93490 _93497 s t f)). Qed.
Lemma lem3649389 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term110 _93490 _93497 s t f) = (term116 _93490 _93497 s t f).
Proof. exact (TRANS (@lem3649381 _93490 _93497 s t f) (@lem3649388 _93490 _93497 s t f)). Qed.
Lemma lem3649390 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term58 _93490 _93497 s t f) = (term117 _93490 _93497 s t f).
Proof. exact (fun_ext (fun u : _93490 -> Prop => @lem3649379 _93490 _93497 s t f u)). Qed.
Lemma lem3649391 {_93490 : Type'} : (@ex (_93490 -> Prop)) = (@ex (_93490 -> Prop)).
Proof. exact (eq_refl (@ex (_93490 -> Prop))). Qed.
Lemma lem3649392 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term13 _93490 _93497 s t f) = (term118 _93490 _93497 s t f).
Proof. exact (MK_COMB (@lem3649391 _93490) (@lem3649390 _93490 _93497 s t f)). Qed.
Lemma lem3649393 {_93497 : Type'} (P : type686 _93497) (t : _93497 -> Prop) : (term119 _93497 P t) = (term119 _93497 P t).
Proof. exact (eq_refl (term119 _93497 P t)). Qed.
Lemma lem3649394 {_93497 : Type'} (P : type686 _93497) (t : _93497 -> Prop) : (P t) = (P t).
Proof. exact (eq_refl (P t)). Qed.
Lemma lem3649395 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3649396 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term120 _93490 _93497 s t f) = (term121 _93490 _93497 s t f).
Proof. exact (MK_COMB (@lem3649395) (@lem3649389 _93490 _93497 s t f)). Qed.
Lemma lem3649397 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term122 _93490 _93497 s f P t) = (term123 _93490 _93497 s f P t).
Proof. exact (MK_COMB (@lem3649396 _93490 _93497 s t f) (@lem3649393 _93497 P t)). Qed.
Lemma lem3649398 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term124 _93490 _93497 s f P t) = (term122 _93490 _93497 s f P t).
Proof. exact (@lem17045 (term13 _93490 _93497 s t f) (P t)). Qed.
Lemma lem3649399 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term124 _93490 _93497 s f P t) = (term123 _93490 _93497 s f P t).
Proof. exact (TRANS (@lem3649398 _93490 _93497 s f P t) (@lem3649397 _93490 _93497 s f P t)). Qed.
Lemma lem3649400 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3649401 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term15 _93490 _93497 s t f) = (term125 _93490 _93497 s t f).
Proof. exact (MK_COMB (@lem3649400) (@lem3649392 _93490 _93497 s t f)). Qed.
Lemma lem3649402 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term17 _93490 _93497 s f P t) = (term126 _93490 _93497 s f P t).
Proof. exact (MK_COMB (@lem3649401 _93490 _93497 s t f) (@lem3649394 _93497 P t)). Qed.
Lemma lem3649403 {_93497 : Type'} (P : type686 _93497) : (term108 _93497 P) = (term109 _93497 P).
Proof. exact (@lem18394 (_93497 -> Prop) P). Qed.
Lemma lem3649404 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term127 _93490 _93497 s f P) = (term128 _93490 _93497 s f P).
Proof. exact (@lem3649403 _93497 (term19 _93490 _93497 s f P)). Qed.
Lemma lem3649405 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term129 _93490 _93497 s f P t) = (term17 _93490 _93497 s f P t).
Proof. exact (eq_refl (term129 _93490 _93497 s f P t)). Qed.
Lemma lem3649406 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3649407 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term130 _93490 _93497 s f P t) = (term124 _93490 _93497 s f P t).
Proof. exact (MK_COMB (@lem3649406) (@lem3649405 _93490 _93497 s f P t)). Qed.
Lemma lem3649408 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term130 _93490 _93497 s f P t) = (term123 _93490 _93497 s f P t).
Proof. exact (TRANS (@lem3649407 _93490 _93497 s f P t) (@lem3649399 _93490 _93497 s f P t)). Qed.
Lemma lem3649409 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term131 _93490 _93497 s f P) = (term132 _93490 _93497 s f P).
Proof. exact (fun_ext (fun t : _93497 -> Prop => @lem3649408 _93490 _93497 s f P t)). Qed.
Lemma lem3649410 {_93497 : Type'} : (@all (_93497 -> Prop)) = (@all (_93497 -> Prop)).
Proof. exact (eq_refl (@all (_93497 -> Prop))). Qed.
Lemma lem3649411 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term128 _93490 _93497 s f P) = (term133 _93490 _93497 s f P).
Proof. exact (MK_COMB (@lem3649410 _93497) (@lem3649409 _93490 _93497 s f P)). Qed.
Lemma lem3649412 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term127 _93490 _93497 s f P) = (term133 _93490 _93497 s f P).
Proof. exact (TRANS (@lem3649404 _93490 _93497 s f P) (@lem3649411 _93490 _93497 s f P)). Qed.
Lemma lem3649413 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term19 _93490 _93497 s f P) = (term134 _93490 _93497 s f P).
Proof. exact (fun_ext (fun t : _93497 -> Prop => @lem3649402 _93490 _93497 s f P t)). Qed.
Lemma lem3649414 {_93497 : Type'} : (@ex (_93497 -> Prop)) = (@ex (_93497 -> Prop)).
Proof. exact (eq_refl (@ex (_93497 -> Prop))). Qed.
Lemma lem3649415 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term21 _93490 _93497 s f P) = (term135 _93490 _93497 s f P).
Proof. exact (MK_COMB (@lem3649414 _93497) (@lem3649413 _93490 _93497 s f P)). Qed.
Lemma lem3649426 {_93490 : Type'} (x : _93490) (y : _93490) (t : _93490 -> Prop) : (term61 _93490 x y t) = (term62 _93490 x y t).
Proof. exact (@lem17045 (@IN _93490 x t) (@IN _93490 y t)). Qed.
Lemma lem3649444 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term63 _93490 _93497 f x y) = (term64 _93490 _93497 f x y).
Proof. exact (@lem17930 ((f x) = (f y)) (x = y)). Qed.
Lemma lem3649455 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : _93490) (y : _93490) : (((f x) = (f y)) = (x = y)) = (term65 _93490 _93497 f x y).
Proof. exact (@lem17784 ((f x) = (f y)) (x = y)). Qed.
Lemma lem3649457 {_93490 : Type'} (x : _93490) (y : _93490) (t : _93490 -> Prop) : (term66 _93490 x y t) = (term66 _93490 x y t).
Proof. exact (eq_refl (term66 _93490 x y t)). Qed.
Lemma lem3649458 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term67 _93490 _93497 t f x y) = (term68 _93490 _93497 t f x y).
Proof. exact (MK_COMB (@lem3649457 _93490 x y t) (@lem3649444 _93490 _93497 f x y)). Qed.
Lemma lem3649459 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term69 _93490 _93497 t f x y) = (term67 _93490 _93497 t f x y).
Proof. exact (@lem17362 (term70 _93490 x y t) (((f x) = (f y)) = (x = y))). Qed.
Lemma lem3649460 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term69 _93490 _93497 t f x y) = (term68 _93490 _93497 t f x y).
Proof. exact (TRANS (@lem3649459 _93490 _93497 t f x y) (@lem3649458 _93490 _93497 t f x y)). Qed.
Lemma lem3649461 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3649462 {_93490 : Type'} (x : _93490) (y : _93490) (t : _93490 -> Prop) : (term71 _93490 x y t) = (term72 _93490 x y t).
Proof. exact (MK_COMB (@lem3649461) (@lem3649426 _93490 x y t)). Qed.
Lemma lem3649463 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term73 _93490 _93497 t f x y) = (term74 _93490 _93497 t f x y).
Proof. exact (MK_COMB (@lem3649462 _93490 x y t) (@lem3649455 _93490 _93497 f x y)). Qed.
Lemma lem3649464 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term46 _93490 _93497 t f x y) = (term73 _93490 _93497 t f x y).
Proof. exact (@lem17265 (term70 _93490 x y t) (((f x) = (f y)) = (x = y))). Qed.
Lemma lem3649465 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term46 _93490 _93497 t f x y) = (term74 _93490 _93497 t f x y).
Proof. exact (TRANS (@lem3649464 _93490 _93497 t f x y) (@lem3649463 _93490 _93497 t f x y)). Qed.
Lemma lem3649466 {_93490 : Type'} (P : _93490 -> Prop) : (term75 _93490 P) = (term76 _93490 P).
Proof. exact (@lem18392 _93490 P). Qed.
Lemma lem3649467 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term77 _93490 _93497 t f x) = (term78 _93490 _93497 t f x).
Proof. exact (@lem3649466 _93490 (term47 _93490 _93497 t f x)). Qed.
Lemma lem3649468 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term79 _93490 _93497 t f x y) = (term46 _93490 _93497 t f x y).
Proof. exact (eq_refl (term79 _93490 _93497 t f x y)). Qed.
Lemma lem3649469 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3649470 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term80 _93490 _93497 t f x y) = (term69 _93490 _93497 t f x y).
Proof. exact (MK_COMB (@lem3649469) (@lem3649468 _93490 _93497 t f x y)). Qed.
Lemma lem3649471 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term80 _93490 _93497 t f x y) = (term68 _93490 _93497 t f x y).
Proof. exact (TRANS (@lem3649470 _93490 _93497 t f x y) (@lem3649460 _93490 _93497 t f x y)). Qed.
Lemma lem3649472 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term81 _93490 _93497 t f x) = (term82 _93490 _93497 t f x).
Proof. exact (fun_ext (fun y : _93490 => @lem3649471 _93490 _93497 t f x y)). Qed.
Lemma lem3649473 {_93490 : Type'} : (@ex _93490) = (@ex _93490).
Proof. exact (eq_refl (@ex _93490)). Qed.
Lemma lem3649474 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term78 _93490 _93497 t f x) = (term83 _93490 _93497 t f x).
Proof. exact (MK_COMB (@lem3649473 _93490) (@lem3649472 _93490 _93497 t f x)). Qed.
Lemma lem3649475 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term77 _93490 _93497 t f x) = (term83 _93490 _93497 t f x).
Proof. exact (TRANS (@lem3649467 _93490 _93497 t f x) (@lem3649474 _93490 _93497 t f x)). Qed.
Lemma lem3649476 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term47 _93490 _93497 t f x) = (term84 _93490 _93497 t f x).
Proof. exact (fun_ext (fun y : _93490 => @lem3649465 _93490 _93497 t f x y)). Qed.
Lemma lem3649477 {_93490 : Type'} : (@all _93490) = (@all _93490).
Proof. exact (eq_refl (@all _93490)). Qed.
Lemma lem3649478 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term48 _93490 _93497 t f x) = (term85 _93490 _93497 t f x).
Proof. exact (MK_COMB (@lem3649477 _93490) (@lem3649476 _93490 _93497 t f x)). Qed.
Lemma lem3649479 {_93490 : Type'} (P : _93490 -> Prop) : (term75 _93490 P) = (term76 _93490 P).
Proof. exact (@lem18392 _93490 P). Qed.
Lemma lem3649480 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) : (term86 _93490 _93497 t f) = (term87 _93490 _93497 t f).
Proof. exact (@lem3649479 _93490 (term49 _93490 _93497 t f)). Qed.
Lemma lem3649481 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term88 _93490 _93497 t f x) = (term48 _93490 _93497 t f x).
Proof. exact (eq_refl (term88 _93490 _93497 t f x)). Qed.
Lemma lem3649482 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3649483 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term89 _93490 _93497 t f x) = (term77 _93490 _93497 t f x).
Proof. exact (MK_COMB (@lem3649482) (@lem3649481 _93490 _93497 t f x)). Qed.
Lemma lem3649484 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term89 _93490 _93497 t f x) = (term83 _93490 _93497 t f x).
Proof. exact (TRANS (@lem3649483 _93490 _93497 t f x) (@lem3649475 _93490 _93497 t f x)). Qed.
Lemma lem3649485 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) : (term90 _93490 _93497 t f) = (term91 _93490 _93497 t f).
Proof. exact (fun_ext (fun x : _93490 => @lem3649484 _93490 _93497 t f x)). Qed.
Lemma lem3649486 {_93490 : Type'} : (@ex _93490) = (@ex _93490).
Proof. exact (eq_refl (@ex _93490)). Qed.
Lemma lem3649487 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) : (term87 _93490 _93497 t f) = (term92 _93490 _93497 t f).
Proof. exact (MK_COMB (@lem3649486 _93490) (@lem3649485 _93490 _93497 t f)). Qed.
Lemma lem3649488 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) : (term86 _93490 _93497 t f) = (term92 _93490 _93497 t f).
Proof. exact (TRANS (@lem3649480 _93490 _93497 t f) (@lem3649487 _93490 _93497 t f)). Qed.
Lemma lem3649489 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) : (term49 _93490 _93497 t f) = (term93 _93490 _93497 t f).
Proof. exact (fun_ext (fun x : _93490 => @lem3649478 _93490 _93497 t f x)). Qed.
Lemma lem3649490 {_93490 : Type'} : (@all _93490) = (@all _93490).
Proof. exact (eq_refl (@all _93490)). Qed.
Lemma lem3649491 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) : (term50 _93490 _93497 t f) = (term94 _93490 _93497 t f).
Proof. exact (MK_COMB (@lem3649490 _93490) (@lem3649489 _93490 _93497 t f)). Qed.
Lemma lem3649492 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term136 _93490 _93497 P f t) = (term136 _93490 _93497 P f t).
Proof. exact (eq_refl (term136 _93490 _93497 P f t)). Qed.
Lemma lem3649493 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term45 _93490 _93497 P f t) = (term45 _93490 _93497 P f t).
Proof. exact (eq_refl (term45 _93490 _93497 P f t)). Qed.
Lemma lem3649494 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3649495 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) : (term96 _93490 _93497 t f) = (term97 _93490 _93497 t f).
Proof. exact (MK_COMB (@lem3649494) (@lem3649488 _93490 _93497 t f)). Qed.
Lemma lem3649496 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term137 _93490 _93497 P f t) = (term138 _93490 _93497 P f t).
Proof. exact (MK_COMB (@lem3649495 _93490 _93497 t f) (@lem3649492 _93490 _93497 P f t)). Qed.
Lemma lem3649497 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term139 _93490 _93497 P f t) = (term137 _93490 _93497 P f t).
Proof. exact (@lem17045 (term50 _93490 _93497 t f) (term45 _93490 _93497 P f t)). Qed.
Lemma lem3649498 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term139 _93490 _93497 P f t) = (term138 _93490 _93497 P f t).
Proof. exact (TRANS (@lem3649497 _93490 _93497 P f t) (@lem3649496 _93490 _93497 P f t)). Qed.
Lemma lem3649499 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3649500 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) : (term51 _93490 _93497 t f) = (term101 _93490 _93497 t f).
Proof. exact (MK_COMB (@lem3649499) (@lem3649491 _93490 _93497 t f)). Qed.
Lemma lem3649501 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term52 _93490 _93497 P f t) = (term140 _93490 _93497 P f t).
Proof. exact (MK_COMB (@lem3649500 _93490 _93497 t f) (@lem3649493 _93490 _93497 P f t)). Qed.
Lemma lem3649503 {_93490 : Type'} (t : _93490 -> Prop) (s : _93490 -> Prop) : (term103 _93490 t s) = (term103 _93490 t s).
Proof. exact (eq_refl (term103 _93490 t s)). Qed.
Lemma lem3649504 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term141 _93490 _93497 s P f t) = (term142 _93490 _93497 s P f t).
Proof. exact (MK_COMB (@lem3649503 _93490 t s) (@lem3649498 _93490 _93497 P f t)). Qed.
Lemma lem3649505 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term143 _93490 _93497 s P f t) = (term141 _93490 _93497 s P f t).
Proof. exact (@lem17045 (@SUBSET _93490 t s) (term52 _93490 _93497 P f t)). Qed.
Lemma lem3649506 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term143 _93490 _93497 s P f t) = (term142 _93490 _93497 s P f t).
Proof. exact (TRANS (@lem3649505 _93490 _93497 s P f t) (@lem3649504 _93490 _93497 s P f t)). Qed.
Lemma lem3649508 {_93490 : Type'} (t : _93490 -> Prop) (s : _93490 -> Prop) : (term53 _93490 t s) = (term53 _93490 t s).
Proof. exact (eq_refl (term53 _93490 t s)). Qed.
Lemma lem3649509 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term54 _93490 _93497 s P f t) = (term144 _93490 _93497 s P f t).
Proof. exact (MK_COMB (@lem3649508 _93490 t s) (@lem3649501 _93490 _93497 P f t)). Qed.
Lemma lem3649510 {_93490 : Type'} (P : type686 _93490) : (term108 _93490 P) = (term109 _93490 P).
Proof. exact (@lem18394 (_93490 -> Prop) P). Qed.
Lemma lem3649511 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term145 _93490 _93497 s P f) = (term146 _93490 _93497 s P f).
Proof. exact (@lem3649510 _93490 (term55 _93490 _93497 s P f)). Qed.
Lemma lem3649512 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term147 _93490 _93497 s P f t) = (term54 _93490 _93497 s P f t).
Proof. exact (eq_refl (term147 _93490 _93497 s P f t)). Qed.
Lemma lem3649513 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3649514 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term148 _93490 _93497 s P f t) = (term143 _93490 _93497 s P f t).
Proof. exact (MK_COMB (@lem3649513) (@lem3649512 _93490 _93497 s P f t)). Qed.
Lemma lem3649515 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term148 _93490 _93497 s P f t) = (term142 _93490 _93497 s P f t).
Proof. exact (TRANS (@lem3649514 _93490 _93497 s P f t) (@lem3649506 _93490 _93497 s P f t)). Qed.
Lemma lem3649516 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term149 _93490 _93497 s P f) = (term150 _93490 _93497 s P f).
Proof. exact (fun_ext (fun t : _93490 -> Prop => @lem3649515 _93490 _93497 s P f t)). Qed.
Lemma lem3649517 {_93490 : Type'} : (@all (_93490 -> Prop)) = (@all (_93490 -> Prop)).
Proof. exact (eq_refl (@all (_93490 -> Prop))). Qed.
Lemma lem3649518 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term146 _93490 _93497 s P f) = (term151 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3649517 _93490) (@lem3649516 _93490 _93497 s P f)). Qed.
Lemma lem3649519 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term145 _93490 _93497 s P f) = (term151 _93490 _93497 s P f).
Proof. exact (TRANS (@lem3649511 _93490 _93497 s P f) (@lem3649518 _93490 _93497 s P f)). Qed.
Lemma lem3649520 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term55 _93490 _93497 s P f) = (term152 _93490 _93497 s P f).
Proof. exact (fun_ext (fun t : _93490 -> Prop => @lem3649509 _93490 _93497 s P f t)). Qed.
Lemma lem3649521 {_93490 : Type'} : (@ex (_93490 -> Prop)) = (@ex (_93490 -> Prop)).
Proof. exact (eq_refl (@ex (_93490 -> Prop))). Qed.
Lemma lem3649522 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term24 _93490 _93497 s P f) = (term153 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3649521 _93490) (@lem3649520 _93490 _93497 s P f)). Qed.
Lemma lem3649523 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3649524 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term154 _93490 _93497 s f P) = (term155 _93490 _93497 s f P).
Proof. exact (MK_COMB (@lem3649523) (@lem3649412 _93490 _93497 s f P)). Qed.
Lemma lem3649525 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term156 _93490 _93497 s P f) = (term157 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3649524 _93490 _93497 s f P) (@lem3649522 _93490 _93497 s P f)). Qed.
Lemma lem3649526 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3649527 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term158 _93490 _93497 s f P) = (term159 _93490 _93497 s f P).
Proof. exact (MK_COMB (@lem3649526) (@lem3649415 _93490 _93497 s f P)). Qed.
Lemma lem3649528 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term160 _93490 _93497 s P f) = (term161 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3649527 _93490 _93497 s f P) (@lem3649519 _93490 _93497 s P f)). Qed.
Lemma lem3649529 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3649530 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term162 _93490 _93497 s P f) = (term163 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3649529) (@lem3649528 _93490 _93497 s P f)). Qed.
Lemma lem3649531 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term164 _93490 _93497 s P f) = (term165 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3649530 _93490 _93497 s P f) (@lem3649525 _93490 _93497 s P f)). Qed.
Lemma lem3649532 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term60 _93490 _93497 s P f) = (term164 _93490 _93497 s P f).
Proof. exact (@lem17646 (term21 _93490 _93497 s f P) (term24 _93490 _93497 s P f)). Qed.
Lemma lem3649533 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term60 _93490 _93497 s P f) = (term165 _93490 _93497 s P f).
Proof. exact (TRANS (@lem3649532 _93490 _93497 s P f) (@lem3649531 _93490 _93497 s P f)). Qed.
Lemma lem3650016 {A : Type'} (P : A -> Prop) (Q : Prop) : (term166 A P Q) = (term167 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3650017 {_93490 : Type'} (P : type686 _93490) (Q : Prop) : (term168 _93490 P Q) = (term169 _93490 P Q).
Proof. exact (@lem3650016 (_93490 -> Prop) P Q). Qed.
Lemma lem3650018 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term170 _93490 _93497 s f P t) = (term171 _93490 _93497 s f P t).
Proof. exact (@lem3650017 _93490 (term117 _93490 _93497 s t f) (P t)). Qed.
Lemma lem3650019 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term172 _93490 _93497 s t f u) = (term107 _93490 _93497 s t f u).
Proof. exact (eq_refl (term172 _93490 _93497 s t f u)). Qed.
Lemma lem3650020 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term173 _93490 _93497 s t f) = (term117 _93490 _93497 s t f).
Proof. exact (fun_ext (fun u : _93490 -> Prop => @lem3650019 _93490 _93497 s t f u)). Qed.
Lemma lem3650021 {_93490 : Type'} : (@ex (_93490 -> Prop)) = (@ex (_93490 -> Prop)).
Proof. exact (eq_refl (@ex (_93490 -> Prop))). Qed.
Lemma lem3650022 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term174 _93490 _93497 s t f) = (term118 _93490 _93497 s t f).
Proof. exact (MK_COMB (@lem3650021 _93490) (@lem3650020 _93490 _93497 s t f)). Qed.
Lemma lem3650023 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3650024 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term175 _93490 _93497 s t f) = (term125 _93490 _93497 s t f).
Proof. exact (MK_COMB (@lem3650023) (@lem3650022 _93490 _93497 s t f)). Qed.
Lemma lem3650025 {_93497 : Type'} (P : type686 _93497) (t : _93497 -> Prop) : (P t) = (P t).
Proof. exact (eq_refl (P t)). Qed.
Lemma lem3650026 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term170 _93490 _93497 s f P t) = (term126 _93490 _93497 s f P t).
Proof. exact (MK_COMB (@lem3650024 _93490 _93497 s t f) (@lem3650025 _93497 P t)). Qed.
Lemma lem3650027 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3650028 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term176 _93490 _93497 s f P t) = (term177 _93490 _93497 s f P t).
Proof. exact (MK_COMB (@lem3650027) (@lem3650026 _93490 _93497 s f P t)). Qed.
Lemma lem3650029 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term172 _93490 _93497 s t f u) = (term107 _93490 _93497 s t f u).
Proof. exact (eq_refl (term172 _93490 _93497 s t f u)). Qed.
Lemma lem3650030 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3650031 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term178 _93490 _93497 s t f u) = (term179 _93490 _93497 s t f u).
Proof. exact (MK_COMB (@lem3650030) (@lem3650029 _93490 _93497 s t f u)). Qed.
Lemma lem3650032 {_93497 : Type'} (P : type686 _93497) (t : _93497 -> Prop) : (P t) = (P t).
Proof. exact (eq_refl (P t)). Qed.
Lemma lem3650033 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) (P : type686 _93497) (t : _93497 -> Prop) : (term180 _93490 _93497 s f u P t) = (term181 _93490 _93497 s f u P t).
Proof. exact (MK_COMB (@lem3650031 _93490 _93497 s t f u) (@lem3650032 _93497 P t)). Qed.
Lemma lem3650034 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term182 _93490 _93497 s f P t) = (term183 _93490 _93497 s f P t).
Proof. exact (fun_ext (fun u : _93490 -> Prop => @lem3650033 _93490 _93497 s f u P t)). Qed.
Lemma lem3650035 {_93490 : Type'} : (@ex (_93490 -> Prop)) = (@ex (_93490 -> Prop)).
Proof. exact (eq_refl (@ex (_93490 -> Prop))). Qed.
Lemma lem3650036 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term171 _93490 _93497 s f P t) = (term184 _93490 _93497 s f P t).
Proof. exact (MK_COMB (@lem3650035 _93490) (@lem3650034 _93490 _93497 s f P t)). Qed.
Lemma lem3650037 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : ((term170 _93490 _93497 s f P t) = (term171 _93490 _93497 s f P t)) = ((term126 _93490 _93497 s f P t) = (term184 _93490 _93497 s f P t)).
Proof. exact (MK_COMB (@lem3650028 _93490 _93497 s f P t) (@lem3650036 _93490 _93497 s f P t)). Qed.
Lemma lem3650038 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term126 _93490 _93497 s f P t) = (term184 _93490 _93497 s f P t).
Proof. exact (EQ_MP (@lem3650037 _93490 _93497 s f P t) (@lem3650018 _93490 _93497 s f P t)). Qed.
Lemma lem3650039 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term134 _93490 _93497 s f P) = (term185 _93490 _93497 s f P).
Proof. exact (fun_ext (fun t : _93497 -> Prop => @lem3650038 _93490 _93497 s f P t)). Qed.
Lemma lem3650040 {_93497 : Type'} : (@ex (_93497 -> Prop)) = (@ex (_93497 -> Prop)).
Proof. exact (eq_refl (@ex (_93497 -> Prop))). Qed.
Lemma lem3650041 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term135 _93490 _93497 s f P) = (term186 _93490 _93497 s f P).
Proof. exact (MK_COMB (@lem3650040 _93497) (@lem3650039 _93490 _93497 s f P)). Qed.
Lemma lem3650042 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3650043 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term159 _93490 _93497 s f P) = (term187 _93490 _93497 s f P).
Proof. exact (MK_COMB (@lem3650042) (@lem3650041 _93490 _93497 s f P)). Qed.
Lemma lem3650045 {A : Type'} (P : A -> Prop) (Q : Prop) : (term188 A P Q) = (term189 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3650046 {_93490 : Type'} (P : _93490 -> Prop) (Q : Prop) : (term188 _93490 P Q) = (term189 _93490 P Q).
Proof. exact (@lem3650045 _93490 P Q). Qed.
Lemma lem3650047 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term190 _93490 _93497 P f t) = (term191 _93490 _93497 P f t).
Proof. exact (@lem3650046 _93490 (term91 _93490 _93497 t f) (term136 _93490 _93497 P f t)). Qed.
Lemma lem3650048 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term192 _93490 _93497 t f x) = (term83 _93490 _93497 t f x).
Proof. exact (eq_refl (term192 _93490 _93497 t f x)). Qed.
Lemma lem3650049 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) : (term193 _93490 _93497 t f) = (term91 _93490 _93497 t f).
Proof. exact (fun_ext (fun x : _93490 => @lem3650048 _93490 _93497 t f x)). Qed.
Lemma lem3650050 {_93490 : Type'} : (@ex _93490) = (@ex _93490).
Proof. exact (eq_refl (@ex _93490)). Qed.
Lemma lem3650051 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) : (term194 _93490 _93497 t f) = (term92 _93490 _93497 t f).
Proof. exact (MK_COMB (@lem3650050 _93490) (@lem3650049 _93490 _93497 t f)). Qed.
Lemma lem3650052 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3650053 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) : (term195 _93490 _93497 t f) = (term97 _93490 _93497 t f).
Proof. exact (MK_COMB (@lem3650052) (@lem3650051 _93490 _93497 t f)). Qed.
Lemma lem3650054 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term136 _93490 _93497 P f t) = (term136 _93490 _93497 P f t).
Proof. exact (eq_refl (term136 _93490 _93497 P f t)). Qed.
Lemma lem3650055 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term190 _93490 _93497 P f t) = (term138 _93490 _93497 P f t).
Proof. exact (MK_COMB (@lem3650053 _93490 _93497 t f) (@lem3650054 _93490 _93497 P f t)). Qed.
Lemma lem3650056 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3650057 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term196 _93490 _93497 P f t) = (term197 _93490 _93497 P f t).
Proof. exact (MK_COMB (@lem3650056) (@lem3650055 _93490 _93497 P f t)). Qed.
Lemma lem3650058 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term192 _93490 _93497 t f x) = (term83 _93490 _93497 t f x).
Proof. exact (eq_refl (term192 _93490 _93497 t f x)). Qed.
Lemma lem3650059 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3650060 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term198 _93490 _93497 t f x) = (term199 _93490 _93497 t f x).
Proof. exact (MK_COMB (@lem3650059) (@lem3650058 _93490 _93497 t f x)). Qed.
Lemma lem3650061 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term136 _93490 _93497 P f t) = (term136 _93490 _93497 P f t).
Proof. exact (eq_refl (term136 _93490 _93497 P f t)). Qed.
Lemma lem3650062 {_93490 _93497 : Type'} (x : _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term200 _93490 _93497 x P f t) = (term201 _93490 _93497 x P f t).
Proof. exact (MK_COMB (@lem3650060 _93490 _93497 t f x) (@lem3650061 _93490 _93497 P f t)). Qed.
Lemma lem3650063 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term202 _93490 _93497 P f t) = (term203 _93490 _93497 P f t).
Proof. exact (fun_ext (fun x : _93490 => @lem3650062 _93490 _93497 x P f t)). Qed.
Lemma lem3650064 {_93490 : Type'} : (@ex _93490) = (@ex _93490).
Proof. exact (eq_refl (@ex _93490)). Qed.
Lemma lem3650065 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term191 _93490 _93497 P f t) = (term204 _93490 _93497 P f t).
Proof. exact (MK_COMB (@lem3650064 _93490) (@lem3650063 _93490 _93497 P f t)). Qed.
Lemma lem3650066 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : ((term190 _93490 _93497 P f t) = (term191 _93490 _93497 P f t)) = ((term138 _93490 _93497 P f t) = (term204 _93490 _93497 P f t)).
Proof. exact (MK_COMB (@lem3650057 _93490 _93497 P f t) (@lem3650065 _93490 _93497 P f t)). Qed.
Lemma lem3650067 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term138 _93490 _93497 P f t) = (term204 _93490 _93497 P f t).
Proof. exact (EQ_MP (@lem3650066 _93490 _93497 P f t) (@lem3650047 _93490 _93497 P f t)). Qed.
Lemma lem3650069 {A : Type'} (P : A -> Prop) (Q : Prop) : (term188 A P Q) = (term189 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3650070 {_93490 : Type'} (P : _93490 -> Prop) (Q : Prop) : (term188 _93490 P Q) = (term189 _93490 P Q).
Proof. exact (@lem3650069 _93490 P Q). Qed.
Lemma lem3650071 {_93490 _93497 : Type'} (x : _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term205 _93490 _93497 x P f t) = (term206 _93490 _93497 x P f t).
Proof. exact (@lem3650070 _93490 (term82 _93490 _93497 t f x) (term136 _93490 _93497 P f t)). Qed.
Lemma lem3650072 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term207 _93490 _93497 t f x y) = (term68 _93490 _93497 t f x y).
Proof. exact (eq_refl (term207 _93490 _93497 t f x y)). Qed.
Lemma lem3650073 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term208 _93490 _93497 t f x) = (term82 _93490 _93497 t f x).
Proof. exact (fun_ext (fun y : _93490 => @lem3650072 _93490 _93497 t f x y)). Qed.
Lemma lem3650074 {_93490 : Type'} : (@ex _93490) = (@ex _93490).
Proof. exact (eq_refl (@ex _93490)). Qed.
Lemma lem3650075 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term209 _93490 _93497 t f x) = (term83 _93490 _93497 t f x).
Proof. exact (MK_COMB (@lem3650074 _93490) (@lem3650073 _93490 _93497 t f x)). Qed.
Lemma lem3650076 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3650077 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term210 _93490 _93497 t f x) = (term199 _93490 _93497 t f x).
Proof. exact (MK_COMB (@lem3650076) (@lem3650075 _93490 _93497 t f x)). Qed.
Lemma lem3650078 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term136 _93490 _93497 P f t) = (term136 _93490 _93497 P f t).
Proof. exact (eq_refl (term136 _93490 _93497 P f t)). Qed.
Lemma lem3650079 {_93490 _93497 : Type'} (x : _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term205 _93490 _93497 x P f t) = (term201 _93490 _93497 x P f t).
Proof. exact (MK_COMB (@lem3650077 _93490 _93497 t f x) (@lem3650078 _93490 _93497 P f t)). Qed.
Lemma lem3650080 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3650081 {_93490 _93497 : Type'} (x : _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term211 _93490 _93497 x P f t) = (term212 _93490 _93497 x P f t).
Proof. exact (MK_COMB (@lem3650080) (@lem3650079 _93490 _93497 x P f t)). Qed.
Lemma lem3650082 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term207 _93490 _93497 t f x y) = (term68 _93490 _93497 t f x y).
Proof. exact (eq_refl (term207 _93490 _93497 t f x y)). Qed.
Lemma lem3650083 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3650084 {_93490 _93497 : Type'} (t : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term213 _93490 _93497 t f x y) = (term214 _93490 _93497 t f x y).
Proof. exact (MK_COMB (@lem3650083) (@lem3650082 _93490 _93497 t f x y)). Qed.
Lemma lem3650085 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term136 _93490 _93497 P f t) = (term136 _93490 _93497 P f t).
Proof. exact (eq_refl (term136 _93490 _93497 P f t)). Qed.
Lemma lem3650086 {_93490 _93497 : Type'} (x : _93490) (y : _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term215 _93490 _93497 x y P f t) = (term216 _93490 _93497 x y P f t).
Proof. exact (MK_COMB (@lem3650084 _93490 _93497 t f x y) (@lem3650085 _93490 _93497 P f t)). Qed.
Lemma lem3650087 {_93490 _93497 : Type'} (x : _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term217 _93490 _93497 x P f t) = (term218 _93490 _93497 x P f t).
Proof. exact (fun_ext (fun y : _93490 => @lem3650086 _93490 _93497 x y P f t)). Qed.
Lemma lem3650088 {_93490 : Type'} : (@ex _93490) = (@ex _93490).
Proof. exact (eq_refl (@ex _93490)). Qed.
Lemma lem3650089 {_93490 _93497 : Type'} (x : _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term206 _93490 _93497 x P f t) = (term219 _93490 _93497 x P f t).
Proof. exact (MK_COMB (@lem3650088 _93490) (@lem3650087 _93490 _93497 x P f t)). Qed.
Lemma lem3650090 {_93490 _93497 : Type'} (x : _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : ((term205 _93490 _93497 x P f t) = (term206 _93490 _93497 x P f t)) = ((term201 _93490 _93497 x P f t) = (term219 _93490 _93497 x P f t)).
Proof. exact (MK_COMB (@lem3650081 _93490 _93497 x P f t) (@lem3650089 _93490 _93497 x P f t)). Qed.
Lemma lem3650091 {_93490 _93497 : Type'} (x : _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term201 _93490 _93497 x P f t) = (term219 _93490 _93497 x P f t).
Proof. exact (EQ_MP (@lem3650090 _93490 _93497 x P f t) (@lem3650071 _93490 _93497 x P f t)). Qed.
Lemma lem3650092 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term203 _93490 _93497 P f t) = (term220 _93490 _93497 P f t).
Proof. exact (fun_ext (fun x : _93490 => @lem3650091 _93490 _93497 x P f t)). Qed.
Lemma lem3650093 {_93490 : Type'} : (@ex _93490) = (@ex _93490).
Proof. exact (eq_refl (@ex _93490)). Qed.
Lemma lem3650094 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term204 _93490 _93497 P f t) = (term221 _93490 _93497 P f t).
Proof. exact (MK_COMB (@lem3650093 _93490) (@lem3650092 _93490 _93497 P f t)). Qed.
Lemma lem3650095 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term138 _93490 _93497 P f t) = (term221 _93490 _93497 P f t).
Proof. exact (TRANS (@lem3650067 _93490 _93497 P f t) (@lem3650094 _93490 _93497 P f t)). Qed.
Lemma lem3650096 {_93490 : Type'} (t : _93490 -> Prop) (s : _93490 -> Prop) : (term103 _93490 t s) = (term103 _93490 t s).
Proof. exact (eq_refl (term103 _93490 t s)). Qed.
Lemma lem3650097 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term142 _93490 _93497 s P f t) = (term222 _93490 _93497 s P f t).
Proof. exact (MK_COMB (@lem3650096 _93490 t s) (@lem3650095 _93490 _93497 P f t)). Qed.
Lemma lem3650099 {A : Type'} (P : Prop) (Q : A -> Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3650100 {_93490 : Type'} (P : Prop) (Q : _93490 -> Prop) : (term223 _93490 P Q) = (term224 _93490 P Q).
Proof. exact (@lem3650099 _93490 P Q). Qed.
Lemma lem3650101 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term225 _93490 _93497 s P f t) = (term226 _93490 _93497 s P f t).
Proof. exact (@lem3650100 _93490 (term227 _93490 t s) (term220 _93490 _93497 P f t)). Qed.
Lemma lem3650102 {_93490 _93497 : Type'} (x : _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term228 _93490 _93497 P f t x) = (term219 _93490 _93497 x P f t).
Proof. exact (eq_refl (term228 _93490 _93497 P f t x)). Qed.
Lemma lem3650103 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term229 _93490 _93497 P f t) = (term220 _93490 _93497 P f t).
Proof. exact (fun_ext (fun x : _93490 => @lem3650102 _93490 _93497 x P f t)). Qed.
Lemma lem3650104 {_93490 : Type'} : (@ex _93490) = (@ex _93490).
Proof. exact (eq_refl (@ex _93490)). Qed.
Lemma lem3650105 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term230 _93490 _93497 P f t) = (term221 _93490 _93497 P f t).
Proof. exact (MK_COMB (@lem3650104 _93490) (@lem3650103 _93490 _93497 P f t)). Qed.
Lemma lem3650106 {_93490 : Type'} (t : _93490 -> Prop) (s : _93490 -> Prop) : (term103 _93490 t s) = (term103 _93490 t s).
Proof. exact (eq_refl (term103 _93490 t s)). Qed.
Lemma lem3650107 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term225 _93490 _93497 s P f t) = (term222 _93490 _93497 s P f t).
Proof. exact (MK_COMB (@lem3650106 _93490 t s) (@lem3650105 _93490 _93497 P f t)). Qed.
Lemma lem3650108 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3650109 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term231 _93490 _93497 s P f t) = (term232 _93490 _93497 s P f t).
Proof. exact (MK_COMB (@lem3650108) (@lem3650107 _93490 _93497 s P f t)). Qed.
Lemma lem3650110 {_93490 _93497 : Type'} (x : _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term228 _93490 _93497 P f t x) = (term219 _93490 _93497 x P f t).
Proof. exact (eq_refl (term228 _93490 _93497 P f t x)). Qed.
Lemma lem3650111 {_93490 : Type'} (t : _93490 -> Prop) (s : _93490 -> Prop) : (term103 _93490 t s) = (term103 _93490 t s).
Proof. exact (eq_refl (term103 _93490 t s)). Qed.
Lemma lem3650112 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term233 _93490 _93497 s P f t x) = (term234 _93490 _93497 s x P f t).
Proof. exact (MK_COMB (@lem3650111 _93490 t s) (@lem3650110 _93490 _93497 x P f t)). Qed.
Lemma lem3650113 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term235 _93490 _93497 s P f t) = (term236 _93490 _93497 s P f t).
Proof. exact (fun_ext (fun x : _93490 => @lem3650112 _93490 _93497 s x P f t)). Qed.
Lemma lem3650114 {_93490 : Type'} : (@ex _93490) = (@ex _93490).
Proof. exact (eq_refl (@ex _93490)). Qed.
Lemma lem3650115 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term226 _93490 _93497 s P f t) = (term237 _93490 _93497 s P f t).
Proof. exact (MK_COMB (@lem3650114 _93490) (@lem3650113 _93490 _93497 s P f t)). Qed.
Lemma lem3650116 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : ((term225 _93490 _93497 s P f t) = (term226 _93490 _93497 s P f t)) = ((term222 _93490 _93497 s P f t) = (term237 _93490 _93497 s P f t)).
Proof. exact (MK_COMB (@lem3650109 _93490 _93497 s P f t) (@lem3650115 _93490 _93497 s P f t)). Qed.
Lemma lem3650117 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term222 _93490 _93497 s P f t) = (term237 _93490 _93497 s P f t).
Proof. exact (EQ_MP (@lem3650116 _93490 _93497 s P f t) (@lem3650101 _93490 _93497 s P f t)). Qed.
Lemma lem3650119 {A : Type'} (P : Prop) (Q : A -> Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3650120 {_93490 : Type'} (P : Prop) (Q : _93490 -> Prop) : (term223 _93490 P Q) = (term224 _93490 P Q).
Proof. exact (@lem3650119 _93490 P Q). Qed.
Lemma lem3650121 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term238 _93490 _93497 s x P f t) = (term239 _93490 _93497 s x P f t).
Proof. exact (@lem3650120 _93490 (term227 _93490 t s) (term218 _93490 _93497 x P f t)). Qed.
Lemma lem3650122 {_93490 _93497 : Type'} (x : _93490) (y : _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term240 _93490 _93497 x P f t y) = (term216 _93490 _93497 x y P f t).
Proof. exact (eq_refl (term240 _93490 _93497 x P f t y)). Qed.
Lemma lem3650123 {_93490 _93497 : Type'} (x : _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term241 _93490 _93497 x P f t) = (term218 _93490 _93497 x P f t).
Proof. exact (fun_ext (fun y : _93490 => @lem3650122 _93490 _93497 x y P f t)). Qed.
Lemma lem3650124 {_93490 : Type'} : (@ex _93490) = (@ex _93490).
Proof. exact (eq_refl (@ex _93490)). Qed.
Lemma lem3650125 {_93490 _93497 : Type'} (x : _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term242 _93490 _93497 x P f t) = (term219 _93490 _93497 x P f t).
Proof. exact (MK_COMB (@lem3650124 _93490) (@lem3650123 _93490 _93497 x P f t)). Qed.
Lemma lem3650126 {_93490 : Type'} (t : _93490 -> Prop) (s : _93490 -> Prop) : (term103 _93490 t s) = (term103 _93490 t s).
Proof. exact (eq_refl (term103 _93490 t s)). Qed.
Lemma lem3650127 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term238 _93490 _93497 s x P f t) = (term234 _93490 _93497 s x P f t).
Proof. exact (MK_COMB (@lem3650126 _93490 t s) (@lem3650125 _93490 _93497 x P f t)). Qed.
Lemma lem3650128 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3650129 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term243 _93490 _93497 s x P f t) = (term244 _93490 _93497 s x P f t).
Proof. exact (MK_COMB (@lem3650128) (@lem3650127 _93490 _93497 s x P f t)). Qed.
Lemma lem3650130 {_93490 _93497 : Type'} (x : _93490) (y : _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term240 _93490 _93497 x P f t y) = (term216 _93490 _93497 x y P f t).
Proof. exact (eq_refl (term240 _93490 _93497 x P f t y)). Qed.
Lemma lem3650131 {_93490 : Type'} (t : _93490 -> Prop) (s : _93490 -> Prop) : (term103 _93490 t s) = (term103 _93490 t s).
Proof. exact (eq_refl (term103 _93490 t s)). Qed.
Lemma lem3650132 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : _93490) (y : _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term245 _93490 _93497 s x P f t y) = (term246 _93490 _93497 s x y P f t).
Proof. exact (MK_COMB (@lem3650131 _93490 t s) (@lem3650130 _93490 _93497 x y P f t)). Qed.
Lemma lem3650133 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term247 _93490 _93497 s x P f t) = (term248 _93490 _93497 s x P f t).
Proof. exact (fun_ext (fun y : _93490 => @lem3650132 _93490 _93497 s x y P f t)). Qed.
Lemma lem3650134 {_93490 : Type'} : (@ex _93490) = (@ex _93490).
Proof. exact (eq_refl (@ex _93490)). Qed.
Lemma lem3650135 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term239 _93490 _93497 s x P f t) = (term249 _93490 _93497 s x P f t).
Proof. exact (MK_COMB (@lem3650134 _93490) (@lem3650133 _93490 _93497 s x P f t)). Qed.
Lemma lem3650136 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : ((term238 _93490 _93497 s x P f t) = (term239 _93490 _93497 s x P f t)) = ((term234 _93490 _93497 s x P f t) = (term249 _93490 _93497 s x P f t)).
Proof. exact (MK_COMB (@lem3650129 _93490 _93497 s x P f t) (@lem3650135 _93490 _93497 s x P f t)). Qed.
Lemma lem3650137 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term234 _93490 _93497 s x P f t) = (term249 _93490 _93497 s x P f t).
Proof. exact (EQ_MP (@lem3650136 _93490 _93497 s x P f t) (@lem3650121 _93490 _93497 s x P f t)). Qed.
Lemma lem3650138 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term236 _93490 _93497 s P f t) = (term250 _93490 _93497 s P f t).
Proof. exact (fun_ext (fun x : _93490 => @lem3650137 _93490 _93497 s x P f t)). Qed.
Lemma lem3650139 {_93490 : Type'} : (@ex _93490) = (@ex _93490).
Proof. exact (eq_refl (@ex _93490)). Qed.
Lemma lem3650140 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term237 _93490 _93497 s P f t) = (term251 _93490 _93497 s P f t).
Proof. exact (MK_COMB (@lem3650139 _93490) (@lem3650138 _93490 _93497 s P f t)). Qed.
Lemma lem3650141 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term222 _93490 _93497 s P f t) = (term251 _93490 _93497 s P f t).
Proof. exact (TRANS (@lem3650117 _93490 _93497 s P f t) (@lem3650140 _93490 _93497 s P f t)). Qed.
Lemma lem3650142 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term142 _93490 _93497 s P f t) = (term251 _93490 _93497 s P f t).
Proof. exact (TRANS (@lem3650097 _93490 _93497 s P f t) (@lem3650141 _93490 _93497 s P f t)). Qed.
Lemma lem3650143 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term150 _93490 _93497 s P f) = (term252 _93490 _93497 s P f).
Proof. exact (fun_ext (fun t : _93490 -> Prop => @lem3650142 _93490 _93497 s P f t)). Qed.
Lemma lem3650144 {_93490 : Type'} : (@all (_93490 -> Prop)) = (@all (_93490 -> Prop)).
Proof. exact (eq_refl (@all (_93490 -> Prop))). Qed.
Lemma lem3650145 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term151 _93490 _93497 s P f) = (term253 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3650144 _93490) (@lem3650143 _93490 _93497 s P f)). Qed.
Lemma lem3650147 {A B : Type'} (P : type1413 A B) : (term254 A B P) = (term255 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3650148 {_93490 : Type'} (P : type672 _93490) : (term256 _93490 P) = (term257 _93490 P).
Proof. exact (@lem3650147 (_93490 -> Prop) _93490 P). Qed.
Lemma lem3650149 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term258 _93490 _93497 s P f) = (term259 _93490 _93497 s P f).
Proof. exact (@lem3650148 _93490 (term260 _93490 _93497 s P f)). Qed.
Lemma lem3650150 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term261 _93490 _93497 s P f t) = (term250 _93490 _93497 s P f t).
Proof. exact (eq_refl (term261 _93490 _93497 s P f t)). Qed.
Lemma lem3650151 {_93490 : Type'} (x : _93490) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3650152 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) (x : _93490) : (term262 _93490 _93497 s P f t x) = (term263 _93490 _93497 s P f t x).
Proof. exact (MK_COMB (@lem3650150 _93490 _93497 s P f t) (@lem3650151 _93490 x)). Qed.
Lemma lem3650153 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term263 _93490 _93497 s P f t x) = (term249 _93490 _93497 s x P f t).
Proof. exact (eq_refl (term263 _93490 _93497 s P f t x)). Qed.
Lemma lem3650154 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term262 _93490 _93497 s P f t x) = (term249 _93490 _93497 s x P f t).
Proof. exact (TRANS (@lem3650152 _93490 _93497 s P f t x) (@lem3650153 _93490 _93497 s x P f t)). Qed.
Lemma lem3650155 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term264 _93490 _93497 s P f t) = (term250 _93490 _93497 s P f t).
Proof. exact (fun_ext (fun x : _93490 => @lem3650154 _93490 _93497 s x P f t)). Qed.
Lemma lem3650156 {_93490 : Type'} : (@ex _93490) = (@ex _93490).
Proof. exact (eq_refl (@ex _93490)). Qed.
Lemma lem3650157 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term265 _93490 _93497 s P f t) = (term251 _93490 _93497 s P f t).
Proof. exact (MK_COMB (@lem3650156 _93490) (@lem3650155 _93490 _93497 s P f t)). Qed.
Lemma lem3650158 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term266 _93490 _93497 s P f) = (term252 _93490 _93497 s P f).
Proof. exact (fun_ext (fun t : _93490 -> Prop => @lem3650157 _93490 _93497 s P f t)). Qed.
Lemma lem3650159 {_93490 : Type'} : (@all (_93490 -> Prop)) = (@all (_93490 -> Prop)).
Proof. exact (eq_refl (@all (_93490 -> Prop))). Qed.
Lemma lem3650160 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term258 _93490 _93497 s P f) = (term253 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3650159 _93490) (@lem3650158 _93490 _93497 s P f)). Qed.
Lemma lem3650161 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3650162 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term267 _93490 _93497 s P f) = (term268 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3650161) (@lem3650160 _93490 _93497 s P f)). Qed.
Lemma lem3650163 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term261 _93490 _93497 s P f t) = (term250 _93490 _93497 s P f t).
Proof. exact (eq_refl (term261 _93490 _93497 s P f t)). Qed.
Lemma lem3650164 {_93490 : Type'} (x : type684 _93490) (t : _93490 -> Prop) : (x t) = (x t).
Proof. exact (eq_refl (x t)). Qed.
Lemma lem3650165 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (x : type684 _93490) (t : _93490 -> Prop) : (term269 _93490 _93497 s P f x t) = (term270 _93490 _93497 s P f x t).
Proof. exact (MK_COMB (@lem3650163 _93490 _93497 s P f t) (@lem3650164 _93490 x t)). Qed.
Lemma lem3650166 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term270 _93490 _93497 s P f x t) = (term271 _93490 _93497 s x P f t).
Proof. exact (eq_refl (term270 _93490 _93497 s P f x t)). Qed.
Lemma lem3650167 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term269 _93490 _93497 s P f x t) = (term271 _93490 _93497 s x P f t).
Proof. exact (TRANS (@lem3650165 _93490 _93497 s P f x t) (@lem3650166 _93490 _93497 s x P f t)). Qed.
Lemma lem3650168 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term272 _93490 _93497 s P f x) = (term273 _93490 _93497 s x P f).
Proof. exact (fun_ext (fun t : _93490 -> Prop => @lem3650167 _93490 _93497 s x P f t)). Qed.
Lemma lem3650169 {_93490 : Type'} : (@all (_93490 -> Prop)) = (@all (_93490 -> Prop)).
Proof. exact (eq_refl (@all (_93490 -> Prop))). Qed.
Lemma lem3650170 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term274 _93490 _93497 s P f x) = (term275 _93490 _93497 s x P f).
Proof. exact (MK_COMB (@lem3650169 _93490) (@lem3650168 _93490 _93497 s x P f)). Qed.
Lemma lem3650171 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term276 _93490 _93497 s P f) = (term277 _93490 _93497 s P f).
Proof. exact (fun_ext (fun x : type684 _93490 => @lem3650170 _93490 _93497 s x P f)). Qed.
Lemma lem3650172 {_93490 : Type'} : (@ex ((_93490 -> Prop) -> _93490)) = (@ex ((_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650173 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term259 _93490 _93497 s P f) = (term278 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3650172 _93490) (@lem3650171 _93490 _93497 s P f)). Qed.
Lemma lem3650174 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : ((term258 _93490 _93497 s P f) = (term259 _93490 _93497 s P f)) = ((term253 _93490 _93497 s P f) = (term278 _93490 _93497 s P f)).
Proof. exact (MK_COMB (@lem3650162 _93490 _93497 s P f) (@lem3650173 _93490 _93497 s P f)). Qed.
Lemma lem3650175 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term253 _93490 _93497 s P f) = (term278 _93490 _93497 s P f).
Proof. exact (EQ_MP (@lem3650174 _93490 _93497 s P f) (@lem3650149 _93490 _93497 s P f)). Qed.
Lemma lem3650177 {A B : Type'} (P : type1413 A B) : (term254 A B P) = (term255 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3650178 {_93490 : Type'} (P : type672 _93490) : (term256 _93490 P) = (term257 _93490 P).
Proof. exact (@lem3650177 (_93490 -> Prop) _93490 P). Qed.
Lemma lem3650179 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term279 _93490 _93497 s x P f) = (term280 _93490 _93497 s x P f).
Proof. exact (@lem3650178 _93490 (term281 _93490 _93497 s x P f)). Qed.
Lemma lem3650180 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term282 _93490 _93497 s x P f t) = (term283 _93490 _93497 s x P f t).
Proof. exact (eq_refl (term282 _93490 _93497 s x P f t)). Qed.
Lemma lem3650181 {_93490 : Type'} (y : _93490) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3650182 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) (y : _93490) : (term284 _93490 _93497 s x P f t y) = (term285 _93490 _93497 s x P f t y).
Proof. exact (MK_COMB (@lem3650180 _93490 _93497 s x P f t) (@lem3650181 _93490 y)). Qed.
Lemma lem3650183 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term285 _93490 _93497 s x P f t y) = (term286 _93490 _93497 s x y P f t).
Proof. exact (eq_refl (term285 _93490 _93497 s x P f t y)). Qed.
Lemma lem3650184 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term284 _93490 _93497 s x P f t y) = (term286 _93490 _93497 s x y P f t).
Proof. exact (TRANS (@lem3650182 _93490 _93497 s x P f t y) (@lem3650183 _93490 _93497 s x y P f t)). Qed.
Lemma lem3650185 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term287 _93490 _93497 s x P f t) = (term283 _93490 _93497 s x P f t).
Proof. exact (fun_ext (fun y : _93490 => @lem3650184 _93490 _93497 s x y P f t)). Qed.
Lemma lem3650186 {_93490 : Type'} : (@ex _93490) = (@ex _93490).
Proof. exact (eq_refl (@ex _93490)). Qed.
Lemma lem3650187 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term288 _93490 _93497 s x P f t) = (term271 _93490 _93497 s x P f t).
Proof. exact (MK_COMB (@lem3650186 _93490) (@lem3650185 _93490 _93497 s x P f t)). Qed.
Lemma lem3650188 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term289 _93490 _93497 s x P f) = (term273 _93490 _93497 s x P f).
Proof. exact (fun_ext (fun t : _93490 -> Prop => @lem3650187 _93490 _93497 s x P f t)). Qed.
Lemma lem3650189 {_93490 : Type'} : (@all (_93490 -> Prop)) = (@all (_93490 -> Prop)).
Proof. exact (eq_refl (@all (_93490 -> Prop))). Qed.
Lemma lem3650190 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term279 _93490 _93497 s x P f) = (term275 _93490 _93497 s x P f).
Proof. exact (MK_COMB (@lem3650189 _93490) (@lem3650188 _93490 _93497 s x P f)). Qed.
Lemma lem3650191 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3650192 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term290 _93490 _93497 s x P f) = (term291 _93490 _93497 s x P f).
Proof. exact (MK_COMB (@lem3650191) (@lem3650190 _93490 _93497 s x P f)). Qed.
Lemma lem3650193 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term282 _93490 _93497 s x P f t) = (term283 _93490 _93497 s x P f t).
Proof. exact (eq_refl (term282 _93490 _93497 s x P f t)). Qed.
Lemma lem3650194 {_93490 : Type'} (y : type684 _93490) (t : _93490 -> Prop) : (y t) = (y t).
Proof. exact (eq_refl (y t)). Qed.
Lemma lem3650195 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (y : type684 _93490) (t : _93490 -> Prop) : (term292 _93490 _93497 s x P f y t) = (term293 _93490 _93497 s x P f y t).
Proof. exact (MK_COMB (@lem3650193 _93490 _93497 s x P f t) (@lem3650194 _93490 y t)). Qed.
Lemma lem3650196 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term293 _93490 _93497 s x P f y t) = (term294 _93490 _93497 s x y P f t).
Proof. exact (eq_refl (term293 _93490 _93497 s x P f y t)). Qed.
Lemma lem3650197 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term292 _93490 _93497 s x P f y t) = (term294 _93490 _93497 s x y P f t).
Proof. exact (TRANS (@lem3650195 _93490 _93497 s x P f y t) (@lem3650196 _93490 _93497 s x y P f t)). Qed.
Lemma lem3650198 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term295 _93490 _93497 s x P f y) = (term296 _93490 _93497 s x y P f).
Proof. exact (fun_ext (fun t : _93490 -> Prop => @lem3650197 _93490 _93497 s x y P f t)). Qed.
Lemma lem3650199 {_93490 : Type'} : (@all (_93490 -> Prop)) = (@all (_93490 -> Prop)).
Proof. exact (eq_refl (@all (_93490 -> Prop))). Qed.
Lemma lem3650200 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term297 _93490 _93497 s x P f y) = (term298 _93490 _93497 s x y P f).
Proof. exact (MK_COMB (@lem3650199 _93490) (@lem3650198 _93490 _93497 s x y P f)). Qed.
Lemma lem3650201 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term299 _93490 _93497 s x P f) = (term300 _93490 _93497 s x P f).
Proof. exact (fun_ext (fun y : type684 _93490 => @lem3650200 _93490 _93497 s x y P f)). Qed.
Lemma lem3650202 {_93490 : Type'} : (@ex ((_93490 -> Prop) -> _93490)) = (@ex ((_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650203 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term280 _93490 _93497 s x P f) = (term301 _93490 _93497 s x P f).
Proof. exact (MK_COMB (@lem3650202 _93490) (@lem3650201 _93490 _93497 s x P f)). Qed.
Lemma lem3650204 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : ((term279 _93490 _93497 s x P f) = (term280 _93490 _93497 s x P f)) = ((term275 _93490 _93497 s x P f) = (term301 _93490 _93497 s x P f)).
Proof. exact (MK_COMB (@lem3650192 _93490 _93497 s x P f) (@lem3650203 _93490 _93497 s x P f)). Qed.
Lemma lem3650205 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term275 _93490 _93497 s x P f) = (term301 _93490 _93497 s x P f).
Proof. exact (EQ_MP (@lem3650204 _93490 _93497 s x P f) (@lem3650179 _93490 _93497 s x P f)). Qed.
Lemma lem3650206 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term277 _93490 _93497 s P f) = (term302 _93490 _93497 s P f).
Proof. exact (fun_ext (fun x : type684 _93490 => @lem3650205 _93490 _93497 s x P f)). Qed.
Lemma lem3650207 {_93490 : Type'} : (@ex ((_93490 -> Prop) -> _93490)) = (@ex ((_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650208 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term278 _93490 _93497 s P f) = (term303 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3650207 _93490) (@lem3650206 _93490 _93497 s P f)). Qed.
Lemma lem3650209 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term253 _93490 _93497 s P f) = (term303 _93490 _93497 s P f).
Proof. exact (TRANS (@lem3650175 _93490 _93497 s P f) (@lem3650208 _93490 _93497 s P f)). Qed.
Lemma lem3650210 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term151 _93490 _93497 s P f) = (term303 _93490 _93497 s P f).
Proof. exact (TRANS (@lem3650145 _93490 _93497 s P f) (@lem3650209 _93490 _93497 s P f)). Qed.
Lemma lem3650211 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term161 _93490 _93497 s P f) = (term304 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3650043 _93490 _93497 s f P) (@lem3650210 _93490 _93497 s P f)). Qed.
Lemma lem3650213 {A : Type'} (P : A -> Prop) (Q : Prop) : (term166 A P Q) = (term167 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3650214 {_93497 : Type'} (P : type686 _93497) (Q : Prop) : (term168 _93497 P Q) = (term169 _93497 P Q).
Proof. exact (@lem3650213 (_93497 -> Prop) P Q). Qed.
Lemma lem3650215 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term305 _93490 _93497 s P f) = (term306 _93490 _93497 s P f).
Proof. exact (@lem3650214 _93497 (term185 _93490 _93497 s f P) (term303 _93490 _93497 s P f)). Qed.
Lemma lem3650216 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term307 _93490 _93497 s f P t) = (term184 _93490 _93497 s f P t).
Proof. exact (eq_refl (term307 _93490 _93497 s f P t)). Qed.
Lemma lem3650217 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term308 _93490 _93497 s f P) = (term185 _93490 _93497 s f P).
Proof. exact (fun_ext (fun t : _93497 -> Prop => @lem3650216 _93490 _93497 s f P t)). Qed.
Lemma lem3650218 {_93497 : Type'} : (@ex (_93497 -> Prop)) = (@ex (_93497 -> Prop)).
Proof. exact (eq_refl (@ex (_93497 -> Prop))). Qed.
Lemma lem3650219 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term309 _93490 _93497 s f P) = (term186 _93490 _93497 s f P).
Proof. exact (MK_COMB (@lem3650218 _93497) (@lem3650217 _93490 _93497 s f P)). Qed.
Lemma lem3650220 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3650221 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term310 _93490 _93497 s f P) = (term187 _93490 _93497 s f P).
Proof. exact (MK_COMB (@lem3650220) (@lem3650219 _93490 _93497 s f P)). Qed.
Lemma lem3650222 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term303 _93490 _93497 s P f) = (term303 _93490 _93497 s P f).
Proof. exact (eq_refl (term303 _93490 _93497 s P f)). Qed.
Lemma lem3650223 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term305 _93490 _93497 s P f) = (term304 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3650221 _93490 _93497 s f P) (@lem3650222 _93490 _93497 s P f)). Qed.
Lemma lem3650224 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3650225 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term311 _93490 _93497 s P f) = (term312 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3650224) (@lem3650223 _93490 _93497 s P f)). Qed.
Lemma lem3650226 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term307 _93490 _93497 s f P t) = (term184 _93490 _93497 s f P t).
Proof. exact (eq_refl (term307 _93490 _93497 s f P t)). Qed.
Lemma lem3650227 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3650228 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term313 _93490 _93497 s f P t) = (term314 _93490 _93497 s f P t).
Proof. exact (MK_COMB (@lem3650227) (@lem3650226 _93490 _93497 s f P t)). Qed.
Lemma lem3650229 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term303 _93490 _93497 s P f) = (term303 _93490 _93497 s P f).
Proof. exact (eq_refl (term303 _93490 _93497 s P f)). Qed.
Lemma lem3650230 {_93490 _93497 : Type'} (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term315 _93490 _93497 t s P f) = (term316 _93490 _93497 t s P f).
Proof. exact (MK_COMB (@lem3650228 _93490 _93497 s f P t) (@lem3650229 _93490 _93497 s P f)). Qed.
Lemma lem3650231 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term317 _93490 _93497 s P f) = (term318 _93490 _93497 s P f).
Proof. exact (fun_ext (fun t : _93497 -> Prop => @lem3650230 _93490 _93497 t s P f)). Qed.
Lemma lem3650232 {_93497 : Type'} : (@ex (_93497 -> Prop)) = (@ex (_93497 -> Prop)).
Proof. exact (eq_refl (@ex (_93497 -> Prop))). Qed.
Lemma lem3650233 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term306 _93490 _93497 s P f) = (term319 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3650232 _93497) (@lem3650231 _93490 _93497 s P f)). Qed.
Lemma lem3650234 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : ((term305 _93490 _93497 s P f) = (term306 _93490 _93497 s P f)) = ((term304 _93490 _93497 s P f) = (term319 _93490 _93497 s P f)).
Proof. exact (MK_COMB (@lem3650225 _93490 _93497 s P f) (@lem3650233 _93490 _93497 s P f)). Qed.
Lemma lem3650235 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term304 _93490 _93497 s P f) = (term319 _93490 _93497 s P f).
Proof. exact (EQ_MP (@lem3650234 _93490 _93497 s P f) (@lem3650215 _93490 _93497 s P f)). Qed.
Lemma lem3650237 {A : Type'} (P : A -> Prop) (Q : Prop) : (term166 A P Q) = (term167 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3650238 {_93490 : Type'} (P : type686 _93490) (Q : Prop) : (term168 _93490 P Q) = (term169 _93490 P Q).
Proof. exact (@lem3650237 (_93490 -> Prop) P Q). Qed.
Lemma lem3650239 {_93490 _93497 : Type'} (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term320 _93490 _93497 t s P f) = (term321 _93490 _93497 t s P f).
Proof. exact (@lem3650238 _93490 (term183 _93490 _93497 s f P t) (term303 _93490 _93497 s P f)). Qed.
Lemma lem3650240 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) (P : type686 _93497) (t : _93497 -> Prop) : (term322 _93490 _93497 s f P t u) = (term181 _93490 _93497 s f u P t).
Proof. exact (eq_refl (term322 _93490 _93497 s f P t u)). Qed.
Lemma lem3650241 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term323 _93490 _93497 s f P t) = (term183 _93490 _93497 s f P t).
Proof. exact (fun_ext (fun u : _93490 -> Prop => @lem3650240 _93490 _93497 s f u P t)). Qed.
Lemma lem3650242 {_93490 : Type'} : (@ex (_93490 -> Prop)) = (@ex (_93490 -> Prop)).
Proof. exact (eq_refl (@ex (_93490 -> Prop))). Qed.
Lemma lem3650243 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term324 _93490 _93497 s f P t) = (term184 _93490 _93497 s f P t).
Proof. exact (MK_COMB (@lem3650242 _93490) (@lem3650241 _93490 _93497 s f P t)). Qed.
Lemma lem3650244 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3650245 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term325 _93490 _93497 s f P t) = (term314 _93490 _93497 s f P t).
Proof. exact (MK_COMB (@lem3650244) (@lem3650243 _93490 _93497 s f P t)). Qed.
Lemma lem3650246 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term303 _93490 _93497 s P f) = (term303 _93490 _93497 s P f).
Proof. exact (eq_refl (term303 _93490 _93497 s P f)). Qed.
Lemma lem3650247 {_93490 _93497 : Type'} (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term320 _93490 _93497 t s P f) = (term316 _93490 _93497 t s P f).
Proof. exact (MK_COMB (@lem3650245 _93490 _93497 s f P t) (@lem3650246 _93490 _93497 s P f)). Qed.
Lemma lem3650248 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3650249 {_93490 _93497 : Type'} (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term326 _93490 _93497 t s P f) = (term327 _93490 _93497 t s P f).
Proof. exact (MK_COMB (@lem3650248) (@lem3650247 _93490 _93497 t s P f)). Qed.
Lemma lem3650250 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) (P : type686 _93497) (t : _93497 -> Prop) : (term322 _93490 _93497 s f P t u) = (term181 _93490 _93497 s f u P t).
Proof. exact (eq_refl (term322 _93490 _93497 s f P t u)). Qed.
Lemma lem3650251 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3650252 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) (P : type686 _93497) (t : _93497 -> Prop) : (term328 _93490 _93497 s f P t u) = (term329 _93490 _93497 s f u P t).
Proof. exact (MK_COMB (@lem3650251) (@lem3650250 _93490 _93497 s f u P t)). Qed.
Lemma lem3650253 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term303 _93490 _93497 s P f) = (term303 _93490 _93497 s P f).
Proof. exact (eq_refl (term303 _93490 _93497 s P f)). Qed.
Lemma lem3650254 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term330 _93490 _93497 t u s P f) = (term331 _93490 _93497 u t s P f).
Proof. exact (MK_COMB (@lem3650252 _93490 _93497 s f u P t) (@lem3650253 _93490 _93497 s P f)). Qed.
Lemma lem3650255 {_93490 _93497 : Type'} (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term332 _93490 _93497 t s P f) = (term333 _93490 _93497 t s P f).
Proof. exact (fun_ext (fun u : _93490 -> Prop => @lem3650254 _93490 _93497 u t s P f)). Qed.
Lemma lem3650256 {_93490 : Type'} : (@ex (_93490 -> Prop)) = (@ex (_93490 -> Prop)).
Proof. exact (eq_refl (@ex (_93490 -> Prop))). Qed.
Lemma lem3650257 {_93490 _93497 : Type'} (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term321 _93490 _93497 t s P f) = (term334 _93490 _93497 t s P f).
Proof. exact (MK_COMB (@lem3650256 _93490) (@lem3650255 _93490 _93497 t s P f)). Qed.
Lemma lem3650258 {_93490 _93497 : Type'} (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : ((term320 _93490 _93497 t s P f) = (term321 _93490 _93497 t s P f)) = ((term316 _93490 _93497 t s P f) = (term334 _93490 _93497 t s P f)).
Proof. exact (MK_COMB (@lem3650249 _93490 _93497 t s P f) (@lem3650257 _93490 _93497 t s P f)). Qed.
Lemma lem3650259 {_93490 _93497 : Type'} (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term316 _93490 _93497 t s P f) = (term334 _93490 _93497 t s P f).
Proof. exact (EQ_MP (@lem3650258 _93490 _93497 t s P f) (@lem3650239 _93490 _93497 t s P f)). Qed.
Lemma lem3650261 {A : Type'} (P : Prop) (Q : A -> Prop) : (term335 A P Q) = (term336 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3650262 {_93490 : Type'} (P : Prop) (Q : type162 _93490) : (term337 _93490 P Q) = (term338 _93490 P Q).
Proof. exact (@lem3650261 (type684 _93490) P Q). Qed.
Lemma lem3650263 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term339 _93490 _93497 u t s P f) = (term340 _93490 _93497 u t s P f).
Proof. exact (@lem3650262 _93490 (term181 _93490 _93497 s f u P t) (term302 _93490 _93497 s P f)). Qed.
Lemma lem3650264 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term341 _93490 _93497 s P f x) = (term301 _93490 _93497 s x P f).
Proof. exact (eq_refl (term341 _93490 _93497 s P f x)). Qed.
Lemma lem3650265 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term342 _93490 _93497 s P f) = (term302 _93490 _93497 s P f).
Proof. exact (fun_ext (fun x : type684 _93490 => @lem3650264 _93490 _93497 s x P f)). Qed.
Lemma lem3650266 {_93490 : Type'} : (@ex ((_93490 -> Prop) -> _93490)) = (@ex ((_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650267 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term343 _93490 _93497 s P f) = (term303 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3650266 _93490) (@lem3650265 _93490 _93497 s P f)). Qed.
Lemma lem3650268 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) (P : type686 _93497) (t : _93497 -> Prop) : (term329 _93490 _93497 s f u P t) = (term329 _93490 _93497 s f u P t).
Proof. exact (eq_refl (term329 _93490 _93497 s f u P t)). Qed.
Lemma lem3650269 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term339 _93490 _93497 u t s P f) = (term331 _93490 _93497 u t s P f).
Proof. exact (MK_COMB (@lem3650268 _93490 _93497 s f u P t) (@lem3650267 _93490 _93497 s P f)). Qed.
Lemma lem3650270 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3650271 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term344 _93490 _93497 u t s P f) = (term345 _93490 _93497 u t s P f).
Proof. exact (MK_COMB (@lem3650270) (@lem3650269 _93490 _93497 u t s P f)). Qed.
Lemma lem3650272 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term341 _93490 _93497 s P f x) = (term301 _93490 _93497 s x P f).
Proof. exact (eq_refl (term341 _93490 _93497 s P f x)). Qed.
Lemma lem3650273 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) (P : type686 _93497) (t : _93497 -> Prop) : (term329 _93490 _93497 s f u P t) = (term329 _93490 _93497 s f u P t).
Proof. exact (eq_refl (term329 _93490 _93497 s f u P t)). Qed.
Lemma lem3650274 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term346 _93490 _93497 u t s P f x) = (term347 _93490 _93497 u t s x P f).
Proof. exact (MK_COMB (@lem3650273 _93490 _93497 s f u P t) (@lem3650272 _93490 _93497 s x P f)). Qed.
Lemma lem3650275 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term348 _93490 _93497 u t s P f) = (term349 _93490 _93497 u t s P f).
Proof. exact (fun_ext (fun x : type684 _93490 => @lem3650274 _93490 _93497 u t s x P f)). Qed.
Lemma lem3650276 {_93490 : Type'} : (@ex ((_93490 -> Prop) -> _93490)) = (@ex ((_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650277 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term340 _93490 _93497 u t s P f) = (term350 _93490 _93497 u t s P f).
Proof. exact (MK_COMB (@lem3650276 _93490) (@lem3650275 _93490 _93497 u t s P f)). Qed.
Lemma lem3650278 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : ((term339 _93490 _93497 u t s P f) = (term340 _93490 _93497 u t s P f)) = ((term331 _93490 _93497 u t s P f) = (term350 _93490 _93497 u t s P f)).
Proof. exact (MK_COMB (@lem3650271 _93490 _93497 u t s P f) (@lem3650277 _93490 _93497 u t s P f)). Qed.
Lemma lem3650279 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term331 _93490 _93497 u t s P f) = (term350 _93490 _93497 u t s P f).
Proof. exact (EQ_MP (@lem3650278 _93490 _93497 u t s P f) (@lem3650263 _93490 _93497 u t s P f)). Qed.
Lemma lem3650281 {A : Type'} (P : Prop) (Q : A -> Prop) : (term335 A P Q) = (term336 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3650282 {_93490 : Type'} (P : Prop) (Q : type162 _93490) : (term337 _93490 P Q) = (term338 _93490 P Q).
Proof. exact (@lem3650281 (type684 _93490) P Q). Qed.
Lemma lem3650283 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term351 _93490 _93497 u t s x P f) = (term352 _93490 _93497 u t s x P f).
Proof. exact (@lem3650282 _93490 (term181 _93490 _93497 s f u P t) (term300 _93490 _93497 s x P f)). Qed.
Lemma lem3650284 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term353 _93490 _93497 s x P f y) = (term298 _93490 _93497 s x y P f).
Proof. exact (eq_refl (term353 _93490 _93497 s x P f y)). Qed.
Lemma lem3650285 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term354 _93490 _93497 s x P f) = (term300 _93490 _93497 s x P f).
Proof. exact (fun_ext (fun y : type684 _93490 => @lem3650284 _93490 _93497 s x y P f)). Qed.
Lemma lem3650286 {_93490 : Type'} : (@ex ((_93490 -> Prop) -> _93490)) = (@ex ((_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650287 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term355 _93490 _93497 s x P f) = (term301 _93490 _93497 s x P f).
Proof. exact (MK_COMB (@lem3650286 _93490) (@lem3650285 _93490 _93497 s x P f)). Qed.
Lemma lem3650288 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) (P : type686 _93497) (t : _93497 -> Prop) : (term329 _93490 _93497 s f u P t) = (term329 _93490 _93497 s f u P t).
Proof. exact (eq_refl (term329 _93490 _93497 s f u P t)). Qed.
Lemma lem3650289 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term351 _93490 _93497 u t s x P f) = (term347 _93490 _93497 u t s x P f).
Proof. exact (MK_COMB (@lem3650288 _93490 _93497 s f u P t) (@lem3650287 _93490 _93497 s x P f)). Qed.
Lemma lem3650290 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3650291 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term356 _93490 _93497 u t s x P f) = (term357 _93490 _93497 u t s x P f).
Proof. exact (MK_COMB (@lem3650290) (@lem3650289 _93490 _93497 u t s x P f)). Qed.
Lemma lem3650292 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term353 _93490 _93497 s x P f y) = (term298 _93490 _93497 s x y P f).
Proof. exact (eq_refl (term353 _93490 _93497 s x P f y)). Qed.
Lemma lem3650293 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) (P : type686 _93497) (t : _93497 -> Prop) : (term329 _93490 _93497 s f u P t) = (term329 _93490 _93497 s f u P t).
Proof. exact (eq_refl (term329 _93490 _93497 s f u P t)). Qed.
Lemma lem3650294 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term358 _93490 _93497 u t s x P f y) = (term359 _93490 _93497 u t s x y P f).
Proof. exact (MK_COMB (@lem3650293 _93490 _93497 s f u P t) (@lem3650292 _93490 _93497 s x y P f)). Qed.
Lemma lem3650295 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term360 _93490 _93497 u t s x P f) = (term361 _93490 _93497 u t s x P f).
Proof. exact (fun_ext (fun y : type684 _93490 => @lem3650294 _93490 _93497 u t s x y P f)). Qed.
Lemma lem3650296 {_93490 : Type'} : (@ex ((_93490 -> Prop) -> _93490)) = (@ex ((_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650297 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term352 _93490 _93497 u t s x P f) = (term362 _93490 _93497 u t s x P f).
Proof. exact (MK_COMB (@lem3650296 _93490) (@lem3650295 _93490 _93497 u t s x P f)). Qed.
Lemma lem3650298 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : ((term351 _93490 _93497 u t s x P f) = (term352 _93490 _93497 u t s x P f)) = ((term347 _93490 _93497 u t s x P f) = (term362 _93490 _93497 u t s x P f)).
Proof. exact (MK_COMB (@lem3650291 _93490 _93497 u t s x P f) (@lem3650297 _93490 _93497 u t s x P f)). Qed.
Lemma lem3650299 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term347 _93490 _93497 u t s x P f) = (term362 _93490 _93497 u t s x P f).
Proof. exact (EQ_MP (@lem3650298 _93490 _93497 u t s x P f) (@lem3650283 _93490 _93497 u t s x P f)). Qed.
Lemma lem3650300 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term349 _93490 _93497 u t s P f) = (term363 _93490 _93497 u t s P f).
Proof. exact (fun_ext (fun x : type684 _93490 => @lem3650299 _93490 _93497 u t s x P f)). Qed.
Lemma lem3650301 {_93490 : Type'} : (@ex ((_93490 -> Prop) -> _93490)) = (@ex ((_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650302 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term350 _93490 _93497 u t s P f) = (term364 _93490 _93497 u t s P f).
Proof. exact (MK_COMB (@lem3650301 _93490) (@lem3650300 _93490 _93497 u t s P f)). Qed.
Lemma lem3650303 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term331 _93490 _93497 u t s P f) = (term364 _93490 _93497 u t s P f).
Proof. exact (TRANS (@lem3650279 _93490 _93497 u t s P f) (@lem3650302 _93490 _93497 u t s P f)). Qed.
Lemma lem3650304 {_93490 _93497 : Type'} (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term333 _93490 _93497 t s P f) = (term365 _93490 _93497 t s P f).
Proof. exact (fun_ext (fun u : _93490 -> Prop => @lem3650303 _93490 _93497 u t s P f)). Qed.
Lemma lem3650305 {_93490 : Type'} : (@ex (_93490 -> Prop)) = (@ex (_93490 -> Prop)).
Proof. exact (eq_refl (@ex (_93490 -> Prop))). Qed.
Lemma lem3650306 {_93490 _93497 : Type'} (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term334 _93490 _93497 t s P f) = (term366 _93490 _93497 t s P f).
Proof. exact (MK_COMB (@lem3650305 _93490) (@lem3650304 _93490 _93497 t s P f)). Qed.
Lemma lem3650307 {_93490 _93497 : Type'} (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term316 _93490 _93497 t s P f) = (term366 _93490 _93497 t s P f).
Proof. exact (TRANS (@lem3650259 _93490 _93497 t s P f) (@lem3650306 _93490 _93497 t s P f)). Qed.
Lemma lem3650308 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term318 _93490 _93497 s P f) = (term367 _93490 _93497 s P f).
Proof. exact (fun_ext (fun t : _93497 -> Prop => @lem3650307 _93490 _93497 t s P f)). Qed.
Lemma lem3650309 {_93497 : Type'} : (@ex (_93497 -> Prop)) = (@ex (_93497 -> Prop)).
Proof. exact (eq_refl (@ex (_93497 -> Prop))). Qed.
Lemma lem3650310 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term319 _93490 _93497 s P f) = (term368 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3650309 _93497) (@lem3650308 _93490 _93497 s P f)). Qed.
Lemma lem3650311 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term304 _93490 _93497 s P f) = (term368 _93490 _93497 s P f).
Proof. exact (TRANS (@lem3650235 _93490 _93497 s P f) (@lem3650310 _93490 _93497 s P f)). Qed.
Lemma lem3650312 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term161 _93490 _93497 s P f) = (term368 _93490 _93497 s P f).
Proof. exact (TRANS (@lem3650211 _93490 _93497 s P f) (@lem3650311 _93490 _93497 s P f)). Qed.
Lemma lem3650313 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3650314 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term163 _93490 _93497 s P f) = (term369 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3650313) (@lem3650312 _93490 _93497 s P f)). Qed.
Lemma lem3650316 {A : Type'} (P : A -> Prop) (Q : Prop) : (term188 A P Q) = (term189 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3650317 {_93490 : Type'} (P : _93490 -> Prop) (Q : Prop) : (term188 _93490 P Q) = (term189 _93490 P Q).
Proof. exact (@lem3650316 _93490 P Q). Qed.
Lemma lem3650318 {_93490 _93497 : Type'} (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term370 _93490 _93497 t f u) = (term371 _93490 _93497 t f u).
Proof. exact (@lem3650317 _93490 (term91 _93490 _93497 u f) (term95 _93490 _93497 t f u)). Qed.
Lemma lem3650319 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term192 _93490 _93497 u f x) = (term83 _93490 _93497 u f x).
Proof. exact (eq_refl (term192 _93490 _93497 u f x)). Qed.
Lemma lem3650320 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) : (term193 _93490 _93497 u f) = (term91 _93490 _93497 u f).
Proof. exact (fun_ext (fun x : _93490 => @lem3650319 _93490 _93497 u f x)). Qed.
Lemma lem3650321 {_93490 : Type'} : (@ex _93490) = (@ex _93490).
Proof. exact (eq_refl (@ex _93490)). Qed.
Lemma lem3650322 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) : (term194 _93490 _93497 u f) = (term92 _93490 _93497 u f).
Proof. exact (MK_COMB (@lem3650321 _93490) (@lem3650320 _93490 _93497 u f)). Qed.
Lemma lem3650323 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3650324 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) : (term195 _93490 _93497 u f) = (term97 _93490 _93497 u f).
Proof. exact (MK_COMB (@lem3650323) (@lem3650322 _93490 _93497 u f)). Qed.
Lemma lem3650325 {_93490 _93497 : Type'} (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term95 _93490 _93497 t f u) = (term95 _93490 _93497 t f u).
Proof. exact (eq_refl (term95 _93490 _93497 t f u)). Qed.
Lemma lem3650326 {_93490 _93497 : Type'} (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term370 _93490 _93497 t f u) = (term99 _93490 _93497 t f u).
Proof. exact (MK_COMB (@lem3650324 _93490 _93497 u f) (@lem3650325 _93490 _93497 t f u)). Qed.
Lemma lem3650327 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3650328 {_93490 _93497 : Type'} (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term372 _93490 _93497 t f u) = (term373 _93490 _93497 t f u).
Proof. exact (MK_COMB (@lem3650327) (@lem3650326 _93490 _93497 t f u)). Qed.
Lemma lem3650329 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term192 _93490 _93497 u f x) = (term83 _93490 _93497 u f x).
Proof. exact (eq_refl (term192 _93490 _93497 u f x)). Qed.
Lemma lem3650330 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3650331 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term198 _93490 _93497 u f x) = (term199 _93490 _93497 u f x).
Proof. exact (MK_COMB (@lem3650330) (@lem3650329 _93490 _93497 u f x)). Qed.
Lemma lem3650332 {_93490 _93497 : Type'} (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term95 _93490 _93497 t f u) = (term95 _93490 _93497 t f u).
Proof. exact (eq_refl (term95 _93490 _93497 t f u)). Qed.
Lemma lem3650333 {_93490 _93497 : Type'} (x : _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term374 _93490 _93497 x t f u) = (term375 _93490 _93497 x t f u).
Proof. exact (MK_COMB (@lem3650331 _93490 _93497 u f x) (@lem3650332 _93490 _93497 t f u)). Qed.
Lemma lem3650334 {_93490 _93497 : Type'} (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term376 _93490 _93497 t f u) = (term377 _93490 _93497 t f u).
Proof. exact (fun_ext (fun x : _93490 => @lem3650333 _93490 _93497 x t f u)). Qed.
Lemma lem3650335 {_93490 : Type'} : (@ex _93490) = (@ex _93490).
Proof. exact (eq_refl (@ex _93490)). Qed.
Lemma lem3650336 {_93490 _93497 : Type'} (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term371 _93490 _93497 t f u) = (term378 _93490 _93497 t f u).
Proof. exact (MK_COMB (@lem3650335 _93490) (@lem3650334 _93490 _93497 t f u)). Qed.
Lemma lem3650337 {_93490 _93497 : Type'} (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : ((term370 _93490 _93497 t f u) = (term371 _93490 _93497 t f u)) = ((term99 _93490 _93497 t f u) = (term378 _93490 _93497 t f u)).
Proof. exact (MK_COMB (@lem3650328 _93490 _93497 t f u) (@lem3650336 _93490 _93497 t f u)). Qed.
Lemma lem3650338 {_93490 _93497 : Type'} (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term99 _93490 _93497 t f u) = (term378 _93490 _93497 t f u).
Proof. exact (EQ_MP (@lem3650337 _93490 _93497 t f u) (@lem3650318 _93490 _93497 t f u)). Qed.
Lemma lem3650340 {A : Type'} (P : A -> Prop) (Q : Prop) : (term188 A P Q) = (term189 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3650341 {_93490 : Type'} (P : _93490 -> Prop) (Q : Prop) : (term188 _93490 P Q) = (term189 _93490 P Q).
Proof. exact (@lem3650340 _93490 P Q). Qed.
Lemma lem3650342 {_93490 _93497 : Type'} (x : _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term379 _93490 _93497 x t f u) = (term380 _93490 _93497 x t f u).
Proof. exact (@lem3650341 _93490 (term82 _93490 _93497 u f x) (term95 _93490 _93497 t f u)). Qed.
Lemma lem3650343 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term207 _93490 _93497 u f x y) = (term68 _93490 _93497 u f x y).
Proof. exact (eq_refl (term207 _93490 _93497 u f x y)). Qed.
Lemma lem3650344 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term208 _93490 _93497 u f x) = (term82 _93490 _93497 u f x).
Proof. exact (fun_ext (fun y : _93490 => @lem3650343 _93490 _93497 u f x y)). Qed.
Lemma lem3650345 {_93490 : Type'} : (@ex _93490) = (@ex _93490).
Proof. exact (eq_refl (@ex _93490)). Qed.
Lemma lem3650346 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term209 _93490 _93497 u f x) = (term83 _93490 _93497 u f x).
Proof. exact (MK_COMB (@lem3650345 _93490) (@lem3650344 _93490 _93497 u f x)). Qed.
Lemma lem3650347 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3650348 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term210 _93490 _93497 u f x) = (term199 _93490 _93497 u f x).
Proof. exact (MK_COMB (@lem3650347) (@lem3650346 _93490 _93497 u f x)). Qed.
Lemma lem3650349 {_93490 _93497 : Type'} (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term95 _93490 _93497 t f u) = (term95 _93490 _93497 t f u).
Proof. exact (eq_refl (term95 _93490 _93497 t f u)). Qed.
Lemma lem3650350 {_93490 _93497 : Type'} (x : _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term379 _93490 _93497 x t f u) = (term375 _93490 _93497 x t f u).
Proof. exact (MK_COMB (@lem3650348 _93490 _93497 u f x) (@lem3650349 _93490 _93497 t f u)). Qed.
Lemma lem3650351 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3650352 {_93490 _93497 : Type'} (x : _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term381 _93490 _93497 x t f u) = (term382 _93490 _93497 x t f u).
Proof. exact (MK_COMB (@lem3650351) (@lem3650350 _93490 _93497 x t f u)). Qed.
Lemma lem3650353 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term207 _93490 _93497 u f x y) = (term68 _93490 _93497 u f x y).
Proof. exact (eq_refl (term207 _93490 _93497 u f x y)). Qed.
Lemma lem3650354 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3650355 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term213 _93490 _93497 u f x y) = (term214 _93490 _93497 u f x y).
Proof. exact (MK_COMB (@lem3650354) (@lem3650353 _93490 _93497 u f x y)). Qed.
Lemma lem3650356 {_93490 _93497 : Type'} (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term95 _93490 _93497 t f u) = (term95 _93490 _93497 t f u).
Proof. exact (eq_refl (term95 _93490 _93497 t f u)). Qed.
Lemma lem3650357 {_93490 _93497 : Type'} (x : _93490) (y : _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term383 _93490 _93497 x y t f u) = (term384 _93490 _93497 x y t f u).
Proof. exact (MK_COMB (@lem3650355 _93490 _93497 u f x y) (@lem3650356 _93490 _93497 t f u)). Qed.
Lemma lem3650358 {_93490 _93497 : Type'} (x : _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term385 _93490 _93497 x t f u) = (term386 _93490 _93497 x t f u).
Proof. exact (fun_ext (fun y : _93490 => @lem3650357 _93490 _93497 x y t f u)). Qed.
Lemma lem3650359 {_93490 : Type'} : (@ex _93490) = (@ex _93490).
Proof. exact (eq_refl (@ex _93490)). Qed.
Lemma lem3650360 {_93490 _93497 : Type'} (x : _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term380 _93490 _93497 x t f u) = (term387 _93490 _93497 x t f u).
Proof. exact (MK_COMB (@lem3650359 _93490) (@lem3650358 _93490 _93497 x t f u)). Qed.
Lemma lem3650361 {_93490 _93497 : Type'} (x : _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : ((term379 _93490 _93497 x t f u) = (term380 _93490 _93497 x t f u)) = ((term375 _93490 _93497 x t f u) = (term387 _93490 _93497 x t f u)).
Proof. exact (MK_COMB (@lem3650352 _93490 _93497 x t f u) (@lem3650360 _93490 _93497 x t f u)). Qed.
Lemma lem3650362 {_93490 _93497 : Type'} (x : _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term375 _93490 _93497 x t f u) = (term387 _93490 _93497 x t f u).
Proof. exact (EQ_MP (@lem3650361 _93490 _93497 x t f u) (@lem3650342 _93490 _93497 x t f u)). Qed.
Lemma lem3650363 {_93490 _93497 : Type'} (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term377 _93490 _93497 t f u) = (term388 _93490 _93497 t f u).
Proof. exact (fun_ext (fun x : _93490 => @lem3650362 _93490 _93497 x t f u)). Qed.
Lemma lem3650364 {_93490 : Type'} : (@ex _93490) = (@ex _93490).
Proof. exact (eq_refl (@ex _93490)). Qed.
Lemma lem3650365 {_93490 _93497 : Type'} (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term378 _93490 _93497 t f u) = (term389 _93490 _93497 t f u).
Proof. exact (MK_COMB (@lem3650364 _93490) (@lem3650363 _93490 _93497 t f u)). Qed.
Lemma lem3650366 {_93490 _93497 : Type'} (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term99 _93490 _93497 t f u) = (term389 _93490 _93497 t f u).
Proof. exact (TRANS (@lem3650338 _93490 _93497 t f u) (@lem3650365 _93490 _93497 t f u)). Qed.
Lemma lem3650367 {_93490 : Type'} (u : _93490 -> Prop) (s : _93490 -> Prop) : (term103 _93490 u s) = (term103 _93490 u s).
Proof. exact (eq_refl (term103 _93490 u s)). Qed.
Lemma lem3650368 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term105 _93490 _93497 s t f u) = (term390 _93490 _93497 s t f u).
Proof. exact (MK_COMB (@lem3650367 _93490 u s) (@lem3650366 _93490 _93497 t f u)). Qed.
Lemma lem3650370 {A : Type'} (P : Prop) (Q : A -> Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3650371 {_93490 : Type'} (P : Prop) (Q : _93490 -> Prop) : (term223 _93490 P Q) = (term224 _93490 P Q).
Proof. exact (@lem3650370 _93490 P Q). Qed.
Lemma lem3650372 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term391 _93490 _93497 s t f u) = (term392 _93490 _93497 s t f u).
Proof. exact (@lem3650371 _93490 (term227 _93490 u s) (term388 _93490 _93497 t f u)). Qed.
Lemma lem3650373 {_93490 _93497 : Type'} (x : _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term393 _93490 _93497 t f u x) = (term387 _93490 _93497 x t f u).
Proof. exact (eq_refl (term393 _93490 _93497 t f u x)). Qed.
Lemma lem3650374 {_93490 _93497 : Type'} (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term394 _93490 _93497 t f u) = (term388 _93490 _93497 t f u).
Proof. exact (fun_ext (fun x : _93490 => @lem3650373 _93490 _93497 x t f u)). Qed.
Lemma lem3650375 {_93490 : Type'} : (@ex _93490) = (@ex _93490).
Proof. exact (eq_refl (@ex _93490)). Qed.
Lemma lem3650376 {_93490 _93497 : Type'} (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term395 _93490 _93497 t f u) = (term389 _93490 _93497 t f u).
Proof. exact (MK_COMB (@lem3650375 _93490) (@lem3650374 _93490 _93497 t f u)). Qed.
Lemma lem3650377 {_93490 : Type'} (u : _93490 -> Prop) (s : _93490 -> Prop) : (term103 _93490 u s) = (term103 _93490 u s).
Proof. exact (eq_refl (term103 _93490 u s)). Qed.
Lemma lem3650378 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term391 _93490 _93497 s t f u) = (term390 _93490 _93497 s t f u).
Proof. exact (MK_COMB (@lem3650377 _93490 u s) (@lem3650376 _93490 _93497 t f u)). Qed.
Lemma lem3650379 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3650380 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term396 _93490 _93497 s t f u) = (term397 _93490 _93497 s t f u).
Proof. exact (MK_COMB (@lem3650379) (@lem3650378 _93490 _93497 s t f u)). Qed.
Lemma lem3650381 {_93490 _93497 : Type'} (x : _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term393 _93490 _93497 t f u x) = (term387 _93490 _93497 x t f u).
Proof. exact (eq_refl (term393 _93490 _93497 t f u x)). Qed.
Lemma lem3650382 {_93490 : Type'} (u : _93490 -> Prop) (s : _93490 -> Prop) : (term103 _93490 u s) = (term103 _93490 u s).
Proof. exact (eq_refl (term103 _93490 u s)). Qed.
Lemma lem3650383 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term398 _93490 _93497 s t f u x) = (term399 _93490 _93497 s x t f u).
Proof. exact (MK_COMB (@lem3650382 _93490 u s) (@lem3650381 _93490 _93497 x t f u)). Qed.
Lemma lem3650384 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term400 _93490 _93497 s t f u) = (term401 _93490 _93497 s t f u).
Proof. exact (fun_ext (fun x : _93490 => @lem3650383 _93490 _93497 s x t f u)). Qed.
Lemma lem3650385 {_93490 : Type'} : (@ex _93490) = (@ex _93490).
Proof. exact (eq_refl (@ex _93490)). Qed.
Lemma lem3650386 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term392 _93490 _93497 s t f u) = (term402 _93490 _93497 s t f u).
Proof. exact (MK_COMB (@lem3650385 _93490) (@lem3650384 _93490 _93497 s t f u)). Qed.
Lemma lem3650387 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : ((term391 _93490 _93497 s t f u) = (term392 _93490 _93497 s t f u)) = ((term390 _93490 _93497 s t f u) = (term402 _93490 _93497 s t f u)).
Proof. exact (MK_COMB (@lem3650380 _93490 _93497 s t f u) (@lem3650386 _93490 _93497 s t f u)). Qed.
Lemma lem3650388 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term390 _93490 _93497 s t f u) = (term402 _93490 _93497 s t f u).
Proof. exact (EQ_MP (@lem3650387 _93490 _93497 s t f u) (@lem3650372 _93490 _93497 s t f u)). Qed.
Lemma lem3650390 {A : Type'} (P : Prop) (Q : A -> Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3650391 {_93490 : Type'} (P : Prop) (Q : _93490 -> Prop) : (term223 _93490 P Q) = (term224 _93490 P Q).
Proof. exact (@lem3650390 _93490 P Q). Qed.
Lemma lem3650392 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term403 _93490 _93497 s x t f u) = (term404 _93490 _93497 s x t f u).
Proof. exact (@lem3650391 _93490 (term227 _93490 u s) (term386 _93490 _93497 x t f u)). Qed.
Lemma lem3650393 {_93490 _93497 : Type'} (x : _93490) (y : _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term405 _93490 _93497 x t f u y) = (term384 _93490 _93497 x y t f u).
Proof. exact (eq_refl (term405 _93490 _93497 x t f u y)). Qed.
Lemma lem3650394 {_93490 _93497 : Type'} (x : _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term406 _93490 _93497 x t f u) = (term386 _93490 _93497 x t f u).
Proof. exact (fun_ext (fun y : _93490 => @lem3650393 _93490 _93497 x y t f u)). Qed.
Lemma lem3650395 {_93490 : Type'} : (@ex _93490) = (@ex _93490).
Proof. exact (eq_refl (@ex _93490)). Qed.
Lemma lem3650396 {_93490 _93497 : Type'} (x : _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term407 _93490 _93497 x t f u) = (term387 _93490 _93497 x t f u).
Proof. exact (MK_COMB (@lem3650395 _93490) (@lem3650394 _93490 _93497 x t f u)). Qed.
Lemma lem3650397 {_93490 : Type'} (u : _93490 -> Prop) (s : _93490 -> Prop) : (term103 _93490 u s) = (term103 _93490 u s).
Proof. exact (eq_refl (term103 _93490 u s)). Qed.
Lemma lem3650398 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term403 _93490 _93497 s x t f u) = (term399 _93490 _93497 s x t f u).
Proof. exact (MK_COMB (@lem3650397 _93490 u s) (@lem3650396 _93490 _93497 x t f u)). Qed.
Lemma lem3650399 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3650400 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term408 _93490 _93497 s x t f u) = (term409 _93490 _93497 s x t f u).
Proof. exact (MK_COMB (@lem3650399) (@lem3650398 _93490 _93497 s x t f u)). Qed.
Lemma lem3650401 {_93490 _93497 : Type'} (x : _93490) (y : _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term405 _93490 _93497 x t f u y) = (term384 _93490 _93497 x y t f u).
Proof. exact (eq_refl (term405 _93490 _93497 x t f u y)). Qed.
Lemma lem3650402 {_93490 : Type'} (u : _93490 -> Prop) (s : _93490 -> Prop) : (term103 _93490 u s) = (term103 _93490 u s).
Proof. exact (eq_refl (term103 _93490 u s)). Qed.
Lemma lem3650403 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : _93490) (y : _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term410 _93490 _93497 s x t f u y) = (term411 _93490 _93497 s x y t f u).
Proof. exact (MK_COMB (@lem3650402 _93490 u s) (@lem3650401 _93490 _93497 x y t f u)). Qed.
Lemma lem3650404 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term412 _93490 _93497 s x t f u) = (term413 _93490 _93497 s x t f u).
Proof. exact (fun_ext (fun y : _93490 => @lem3650403 _93490 _93497 s x y t f u)). Qed.
Lemma lem3650405 {_93490 : Type'} : (@ex _93490) = (@ex _93490).
Proof. exact (eq_refl (@ex _93490)). Qed.
Lemma lem3650406 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term404 _93490 _93497 s x t f u) = (term414 _93490 _93497 s x t f u).
Proof. exact (MK_COMB (@lem3650405 _93490) (@lem3650404 _93490 _93497 s x t f u)). Qed.
Lemma lem3650407 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : ((term403 _93490 _93497 s x t f u) = (term404 _93490 _93497 s x t f u)) = ((term399 _93490 _93497 s x t f u) = (term414 _93490 _93497 s x t f u)).
Proof. exact (MK_COMB (@lem3650400 _93490 _93497 s x t f u) (@lem3650406 _93490 _93497 s x t f u)). Qed.
Lemma lem3650408 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term399 _93490 _93497 s x t f u) = (term414 _93490 _93497 s x t f u).
Proof. exact (EQ_MP (@lem3650407 _93490 _93497 s x t f u) (@lem3650392 _93490 _93497 s x t f u)). Qed.
Lemma lem3650409 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term401 _93490 _93497 s t f u) = (term415 _93490 _93497 s t f u).
Proof. exact (fun_ext (fun x : _93490 => @lem3650408 _93490 _93497 s x t f u)). Qed.
Lemma lem3650410 {_93490 : Type'} : (@ex _93490) = (@ex _93490).
Proof. exact (eq_refl (@ex _93490)). Qed.
Lemma lem3650411 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term402 _93490 _93497 s t f u) = (term416 _93490 _93497 s t f u).
Proof. exact (MK_COMB (@lem3650410 _93490) (@lem3650409 _93490 _93497 s t f u)). Qed.
Lemma lem3650412 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term390 _93490 _93497 s t f u) = (term416 _93490 _93497 s t f u).
Proof. exact (TRANS (@lem3650388 _93490 _93497 s t f u) (@lem3650411 _93490 _93497 s t f u)). Qed.
Lemma lem3650413 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term105 _93490 _93497 s t f u) = (term416 _93490 _93497 s t f u).
Proof. exact (TRANS (@lem3650368 _93490 _93497 s t f u) (@lem3650412 _93490 _93497 s t f u)). Qed.
Lemma lem3650414 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term115 _93490 _93497 s t f) = (term417 _93490 _93497 s t f).
Proof. exact (fun_ext (fun u : _93490 -> Prop => @lem3650413 _93490 _93497 s t f u)). Qed.
Lemma lem3650415 {_93490 : Type'} : (@all (_93490 -> Prop)) = (@all (_93490 -> Prop)).
Proof. exact (eq_refl (@all (_93490 -> Prop))). Qed.
Lemma lem3650416 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term116 _93490 _93497 s t f) = (term418 _93490 _93497 s t f).
Proof. exact (MK_COMB (@lem3650415 _93490) (@lem3650414 _93490 _93497 s t f)). Qed.
Lemma lem3650418 {A B : Type'} (P : type1413 A B) : (term254 A B P) = (term255 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3650419 {_93490 : Type'} (P : type672 _93490) : (term256 _93490 P) = (term257 _93490 P).
Proof. exact (@lem3650418 (_93490 -> Prop) _93490 P). Qed.
Lemma lem3650420 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term419 _93490 _93497 s t f) = (term420 _93490 _93497 s t f).
Proof. exact (@lem3650419 _93490 (term421 _93490 _93497 s t f)). Qed.
Lemma lem3650421 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term422 _93490 _93497 s t f u) = (term415 _93490 _93497 s t f u).
Proof. exact (eq_refl (term422 _93490 _93497 s t f u)). Qed.
Lemma lem3650422 {_93490 : Type'} (x : _93490) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3650423 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) (x : _93490) : (term423 _93490 _93497 s t f u x) = (term424 _93490 _93497 s t f u x).
Proof. exact (MK_COMB (@lem3650421 _93490 _93497 s t f u) (@lem3650422 _93490 x)). Qed.
Lemma lem3650424 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term424 _93490 _93497 s t f u x) = (term414 _93490 _93497 s x t f u).
Proof. exact (eq_refl (term424 _93490 _93497 s t f u x)). Qed.
Lemma lem3650425 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term423 _93490 _93497 s t f u x) = (term414 _93490 _93497 s x t f u).
Proof. exact (TRANS (@lem3650423 _93490 _93497 s t f u x) (@lem3650424 _93490 _93497 s x t f u)). Qed.
Lemma lem3650426 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term425 _93490 _93497 s t f u) = (term415 _93490 _93497 s t f u).
Proof. exact (fun_ext (fun x : _93490 => @lem3650425 _93490 _93497 s x t f u)). Qed.
Lemma lem3650427 {_93490 : Type'} : (@ex _93490) = (@ex _93490).
Proof. exact (eq_refl (@ex _93490)). Qed.
Lemma lem3650428 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term426 _93490 _93497 s t f u) = (term416 _93490 _93497 s t f u).
Proof. exact (MK_COMB (@lem3650427 _93490) (@lem3650426 _93490 _93497 s t f u)). Qed.
Lemma lem3650429 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term427 _93490 _93497 s t f) = (term417 _93490 _93497 s t f).
Proof. exact (fun_ext (fun u : _93490 -> Prop => @lem3650428 _93490 _93497 s t f u)). Qed.
Lemma lem3650430 {_93490 : Type'} : (@all (_93490 -> Prop)) = (@all (_93490 -> Prop)).
Proof. exact (eq_refl (@all (_93490 -> Prop))). Qed.
Lemma lem3650431 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term419 _93490 _93497 s t f) = (term418 _93490 _93497 s t f).
Proof. exact (MK_COMB (@lem3650430 _93490) (@lem3650429 _93490 _93497 s t f)). Qed.
Lemma lem3650432 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3650433 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term428 _93490 _93497 s t f) = (term429 _93490 _93497 s t f).
Proof. exact (MK_COMB (@lem3650432) (@lem3650431 _93490 _93497 s t f)). Qed.
Lemma lem3650434 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term422 _93490 _93497 s t f u) = (term415 _93490 _93497 s t f u).
Proof. exact (eq_refl (term422 _93490 _93497 s t f u)). Qed.
Lemma lem3650435 {_93490 : Type'} (x : type684 _93490) (u : _93490 -> Prop) : (x u) = (x u).
Proof. exact (eq_refl (x u)). Qed.
Lemma lem3650436 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) (x : type684 _93490) (u : _93490 -> Prop) : (term430 _93490 _93497 s t f x u) = (term431 _93490 _93497 s t f x u).
Proof. exact (MK_COMB (@lem3650434 _93490 _93497 s t f u) (@lem3650435 _93490 x u)). Qed.
Lemma lem3650437 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term431 _93490 _93497 s t f x u) = (term432 _93490 _93497 s x t f u).
Proof. exact (eq_refl (term431 _93490 _93497 s t f x u)). Qed.
Lemma lem3650438 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term430 _93490 _93497 s t f x u) = (term432 _93490 _93497 s x t f u).
Proof. exact (TRANS (@lem3650436 _93490 _93497 s t f x u) (@lem3650437 _93490 _93497 s x t f u)). Qed.
Lemma lem3650439 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term433 _93490 _93497 s t f x) = (term434 _93490 _93497 s x t f).
Proof. exact (fun_ext (fun u : _93490 -> Prop => @lem3650438 _93490 _93497 s x t f u)). Qed.
Lemma lem3650440 {_93490 : Type'} : (@all (_93490 -> Prop)) = (@all (_93490 -> Prop)).
Proof. exact (eq_refl (@all (_93490 -> Prop))). Qed.
Lemma lem3650441 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term435 _93490 _93497 s t f x) = (term436 _93490 _93497 s x t f).
Proof. exact (MK_COMB (@lem3650440 _93490) (@lem3650439 _93490 _93497 s x t f)). Qed.
Lemma lem3650442 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term437 _93490 _93497 s t f) = (term438 _93490 _93497 s t f).
Proof. exact (fun_ext (fun x : type684 _93490 => @lem3650441 _93490 _93497 s x t f)). Qed.
Lemma lem3650443 {_93490 : Type'} : (@ex ((_93490 -> Prop) -> _93490)) = (@ex ((_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650444 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term420 _93490 _93497 s t f) = (term439 _93490 _93497 s t f).
Proof. exact (MK_COMB (@lem3650443 _93490) (@lem3650442 _93490 _93497 s t f)). Qed.
Lemma lem3650445 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : ((term419 _93490 _93497 s t f) = (term420 _93490 _93497 s t f)) = ((term418 _93490 _93497 s t f) = (term439 _93490 _93497 s t f)).
Proof. exact (MK_COMB (@lem3650433 _93490 _93497 s t f) (@lem3650444 _93490 _93497 s t f)). Qed.
Lemma lem3650446 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term418 _93490 _93497 s t f) = (term439 _93490 _93497 s t f).
Proof. exact (EQ_MP (@lem3650445 _93490 _93497 s t f) (@lem3650420 _93490 _93497 s t f)). Qed.
Lemma lem3650448 {A B : Type'} (P : type1413 A B) : (term254 A B P) = (term255 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3650449 {_93490 : Type'} (P : type672 _93490) : (term256 _93490 P) = (term257 _93490 P).
Proof. exact (@lem3650448 (_93490 -> Prop) _93490 P). Qed.
Lemma lem3650450 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term440 _93490 _93497 s x t f) = (term441 _93490 _93497 s x t f).
Proof. exact (@lem3650449 _93490 (term442 _93490 _93497 s x t f)). Qed.
Lemma lem3650451 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term443 _93490 _93497 s x t f u) = (term444 _93490 _93497 s x t f u).
Proof. exact (eq_refl (term443 _93490 _93497 s x t f u)). Qed.
Lemma lem3650452 {_93490 : Type'} (y : _93490) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3650453 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) (y : _93490) : (term445 _93490 _93497 s x t f u y) = (term446 _93490 _93497 s x t f u y).
Proof. exact (MK_COMB (@lem3650451 _93490 _93497 s x t f u) (@lem3650452 _93490 y)). Qed.
Lemma lem3650454 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term446 _93490 _93497 s x t f u y) = (term447 _93490 _93497 s x y t f u).
Proof. exact (eq_refl (term446 _93490 _93497 s x t f u y)). Qed.
Lemma lem3650455 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term445 _93490 _93497 s x t f u y) = (term447 _93490 _93497 s x y t f u).
Proof. exact (TRANS (@lem3650453 _93490 _93497 s x t f u y) (@lem3650454 _93490 _93497 s x y t f u)). Qed.
Lemma lem3650456 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term448 _93490 _93497 s x t f u) = (term444 _93490 _93497 s x t f u).
Proof. exact (fun_ext (fun y : _93490 => @lem3650455 _93490 _93497 s x y t f u)). Qed.
Lemma lem3650457 {_93490 : Type'} : (@ex _93490) = (@ex _93490).
Proof. exact (eq_refl (@ex _93490)). Qed.
Lemma lem3650458 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term449 _93490 _93497 s x t f u) = (term432 _93490 _93497 s x t f u).
Proof. exact (MK_COMB (@lem3650457 _93490) (@lem3650456 _93490 _93497 s x t f u)). Qed.
Lemma lem3650459 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term450 _93490 _93497 s x t f) = (term434 _93490 _93497 s x t f).
Proof. exact (fun_ext (fun u : _93490 -> Prop => @lem3650458 _93490 _93497 s x t f u)). Qed.
Lemma lem3650460 {_93490 : Type'} : (@all (_93490 -> Prop)) = (@all (_93490 -> Prop)).
Proof. exact (eq_refl (@all (_93490 -> Prop))). Qed.
Lemma lem3650461 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term440 _93490 _93497 s x t f) = (term436 _93490 _93497 s x t f).
Proof. exact (MK_COMB (@lem3650460 _93490) (@lem3650459 _93490 _93497 s x t f)). Qed.
Lemma lem3650462 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3650463 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term451 _93490 _93497 s x t f) = (term452 _93490 _93497 s x t f).
Proof. exact (MK_COMB (@lem3650462) (@lem3650461 _93490 _93497 s x t f)). Qed.
Lemma lem3650464 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term443 _93490 _93497 s x t f u) = (term444 _93490 _93497 s x t f u).
Proof. exact (eq_refl (term443 _93490 _93497 s x t f u)). Qed.
Lemma lem3650465 {_93490 : Type'} (y : type684 _93490) (u : _93490 -> Prop) : (y u) = (y u).
Proof. exact (eq_refl (y u)). Qed.
Lemma lem3650466 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (y : type684 _93490) (u : _93490 -> Prop) : (term453 _93490 _93497 s x t f y u) = (term454 _93490 _93497 s x t f y u).
Proof. exact (MK_COMB (@lem3650464 _93490 _93497 s x t f u) (@lem3650465 _93490 y u)). Qed.
Lemma lem3650467 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term454 _93490 _93497 s x t f y u) = (term455 _93490 _93497 s x y t f u).
Proof. exact (eq_refl (term454 _93490 _93497 s x t f y u)). Qed.
Lemma lem3650468 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term453 _93490 _93497 s x t f y u) = (term455 _93490 _93497 s x y t f u).
Proof. exact (TRANS (@lem3650466 _93490 _93497 s x t f y u) (@lem3650467 _93490 _93497 s x y t f u)). Qed.
Lemma lem3650469 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term456 _93490 _93497 s x t f y) = (term457 _93490 _93497 s x y t f).
Proof. exact (fun_ext (fun u : _93490 -> Prop => @lem3650468 _93490 _93497 s x y t f u)). Qed.
Lemma lem3650470 {_93490 : Type'} : (@all (_93490 -> Prop)) = (@all (_93490 -> Prop)).
Proof. exact (eq_refl (@all (_93490 -> Prop))). Qed.
Lemma lem3650471 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term458 _93490 _93497 s x t f y) = (term459 _93490 _93497 s x y t f).
Proof. exact (MK_COMB (@lem3650470 _93490) (@lem3650469 _93490 _93497 s x y t f)). Qed.
Lemma lem3650472 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term460 _93490 _93497 s x t f) = (term461 _93490 _93497 s x t f).
Proof. exact (fun_ext (fun y : type684 _93490 => @lem3650471 _93490 _93497 s x y t f)). Qed.
Lemma lem3650473 {_93490 : Type'} : (@ex ((_93490 -> Prop) -> _93490)) = (@ex ((_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650474 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term441 _93490 _93497 s x t f) = (term462 _93490 _93497 s x t f).
Proof. exact (MK_COMB (@lem3650473 _93490) (@lem3650472 _93490 _93497 s x t f)). Qed.
Lemma lem3650475 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) : ((term440 _93490 _93497 s x t f) = (term441 _93490 _93497 s x t f)) = ((term436 _93490 _93497 s x t f) = (term462 _93490 _93497 s x t f)).
Proof. exact (MK_COMB (@lem3650463 _93490 _93497 s x t f) (@lem3650474 _93490 _93497 s x t f)). Qed.
Lemma lem3650476 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term436 _93490 _93497 s x t f) = (term462 _93490 _93497 s x t f).
Proof. exact (EQ_MP (@lem3650475 _93490 _93497 s x t f) (@lem3650450 _93490 _93497 s x t f)). Qed.
Lemma lem3650477 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term438 _93490 _93497 s t f) = (term463 _93490 _93497 s t f).
Proof. exact (fun_ext (fun x : type684 _93490 => @lem3650476 _93490 _93497 s x t f)). Qed.
Lemma lem3650478 {_93490 : Type'} : (@ex ((_93490 -> Prop) -> _93490)) = (@ex ((_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650479 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term439 _93490 _93497 s t f) = (term464 _93490 _93497 s t f).
Proof. exact (MK_COMB (@lem3650478 _93490) (@lem3650477 _93490 _93497 s t f)). Qed.
Lemma lem3650480 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term418 _93490 _93497 s t f) = (term464 _93490 _93497 s t f).
Proof. exact (TRANS (@lem3650446 _93490 _93497 s t f) (@lem3650479 _93490 _93497 s t f)). Qed.
Lemma lem3650481 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term116 _93490 _93497 s t f) = (term464 _93490 _93497 s t f).
Proof. exact (TRANS (@lem3650416 _93490 _93497 s t f) (@lem3650480 _93490 _93497 s t f)). Qed.
Lemma lem3650482 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3650483 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term121 _93490 _93497 s t f) = (term465 _93490 _93497 s t f).
Proof. exact (MK_COMB (@lem3650482) (@lem3650481 _93490 _93497 s t f)). Qed.
Lemma lem3650484 {_93497 : Type'} (P : type686 _93497) (t : _93497 -> Prop) : (term119 _93497 P t) = (term119 _93497 P t).
Proof. exact (eq_refl (term119 _93497 P t)). Qed.
Lemma lem3650485 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term123 _93490 _93497 s f P t) = (term466 _93490 _93497 s f P t).
Proof. exact (MK_COMB (@lem3650483 _93490 _93497 s t f) (@lem3650484 _93497 P t)). Qed.
Lemma lem3650487 {A : Type'} (P : A -> Prop) (Q : Prop) : (term188 A P Q) = (term189 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3650488 {_93490 : Type'} (P : type162 _93490) (Q : Prop) : (term467 _93490 P Q) = (term468 _93490 P Q).
Proof. exact (@lem3650487 (type684 _93490) P Q). Qed.
Lemma lem3650489 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term469 _93490 _93497 s f P t) = (term470 _93490 _93497 s f P t).
Proof. exact (@lem3650488 _93490 (term463 _93490 _93497 s t f) (term119 _93497 P t)). Qed.
Lemma lem3650490 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term471 _93490 _93497 s t f x) = (term462 _93490 _93497 s x t f).
Proof. exact (eq_refl (term471 _93490 _93497 s t f x)). Qed.
Lemma lem3650491 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term472 _93490 _93497 s t f) = (term463 _93490 _93497 s t f).
Proof. exact (fun_ext (fun x : type684 _93490 => @lem3650490 _93490 _93497 s x t f)). Qed.
Lemma lem3650492 {_93490 : Type'} : (@ex ((_93490 -> Prop) -> _93490)) = (@ex ((_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650493 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term473 _93490 _93497 s t f) = (term464 _93490 _93497 s t f).
Proof. exact (MK_COMB (@lem3650492 _93490) (@lem3650491 _93490 _93497 s t f)). Qed.
Lemma lem3650494 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3650495 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term474 _93490 _93497 s t f) = (term465 _93490 _93497 s t f).
Proof. exact (MK_COMB (@lem3650494) (@lem3650493 _93490 _93497 s t f)). Qed.
Lemma lem3650496 {_93497 : Type'} (P : type686 _93497) (t : _93497 -> Prop) : (term119 _93497 P t) = (term119 _93497 P t).
Proof. exact (eq_refl (term119 _93497 P t)). Qed.
Lemma lem3650497 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term469 _93490 _93497 s f P t) = (term466 _93490 _93497 s f P t).
Proof. exact (MK_COMB (@lem3650495 _93490 _93497 s t f) (@lem3650496 _93497 P t)). Qed.
Lemma lem3650498 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3650499 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term475 _93490 _93497 s f P t) = (term476 _93490 _93497 s f P t).
Proof. exact (MK_COMB (@lem3650498) (@lem3650497 _93490 _93497 s f P t)). Qed.
Lemma lem3650500 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term471 _93490 _93497 s t f x) = (term462 _93490 _93497 s x t f).
Proof. exact (eq_refl (term471 _93490 _93497 s t f x)). Qed.
Lemma lem3650501 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3650502 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term477 _93490 _93497 s t f x) = (term478 _93490 _93497 s x t f).
Proof. exact (MK_COMB (@lem3650501) (@lem3650500 _93490 _93497 s x t f)). Qed.
Lemma lem3650503 {_93497 : Type'} (P : type686 _93497) (t : _93497 -> Prop) : (term119 _93497 P t) = (term119 _93497 P t).
Proof. exact (eq_refl (term119 _93497 P t)). Qed.
Lemma lem3650504 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term479 _93490 _93497 s f x P t) = (term480 _93490 _93497 s x f P t).
Proof. exact (MK_COMB (@lem3650502 _93490 _93497 s x t f) (@lem3650503 _93497 P t)). Qed.
Lemma lem3650505 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term481 _93490 _93497 s f P t) = (term482 _93490 _93497 s f P t).
Proof. exact (fun_ext (fun x : type684 _93490 => @lem3650504 _93490 _93497 s x f P t)). Qed.
Lemma lem3650506 {_93490 : Type'} : (@ex ((_93490 -> Prop) -> _93490)) = (@ex ((_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650507 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term470 _93490 _93497 s f P t) = (term483 _93490 _93497 s f P t).
Proof. exact (MK_COMB (@lem3650506 _93490) (@lem3650505 _93490 _93497 s f P t)). Qed.
Lemma lem3650508 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : ((term469 _93490 _93497 s f P t) = (term470 _93490 _93497 s f P t)) = ((term466 _93490 _93497 s f P t) = (term483 _93490 _93497 s f P t)).
Proof. exact (MK_COMB (@lem3650499 _93490 _93497 s f P t) (@lem3650507 _93490 _93497 s f P t)). Qed.
Lemma lem3650509 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term466 _93490 _93497 s f P t) = (term483 _93490 _93497 s f P t).
Proof. exact (EQ_MP (@lem3650508 _93490 _93497 s f P t) (@lem3650489 _93490 _93497 s f P t)). Qed.
Lemma lem3650511 {A : Type'} (P : A -> Prop) (Q : Prop) : (term188 A P Q) = (term189 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3650512 {_93490 : Type'} (P : type162 _93490) (Q : Prop) : (term467 _93490 P Q) = (term468 _93490 P Q).
Proof. exact (@lem3650511 (type684 _93490) P Q). Qed.
Lemma lem3650513 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term484 _93490 _93497 s x f P t) = (term485 _93490 _93497 s x f P t).
Proof. exact (@lem3650512 _93490 (term461 _93490 _93497 s x t f) (term119 _93497 P t)). Qed.
Lemma lem3650514 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term486 _93490 _93497 s x t f y) = (term459 _93490 _93497 s x y t f).
Proof. exact (eq_refl (term486 _93490 _93497 s x t f y)). Qed.
Lemma lem3650515 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term487 _93490 _93497 s x t f) = (term461 _93490 _93497 s x t f).
Proof. exact (fun_ext (fun y : type684 _93490 => @lem3650514 _93490 _93497 s x y t f)). Qed.
Lemma lem3650516 {_93490 : Type'} : (@ex ((_93490 -> Prop) -> _93490)) = (@ex ((_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650517 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term488 _93490 _93497 s x t f) = (term462 _93490 _93497 s x t f).
Proof. exact (MK_COMB (@lem3650516 _93490) (@lem3650515 _93490 _93497 s x t f)). Qed.
Lemma lem3650518 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3650519 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term489 _93490 _93497 s x t f) = (term478 _93490 _93497 s x t f).
Proof. exact (MK_COMB (@lem3650518) (@lem3650517 _93490 _93497 s x t f)). Qed.
Lemma lem3650520 {_93497 : Type'} (P : type686 _93497) (t : _93497 -> Prop) : (term119 _93497 P t) = (term119 _93497 P t).
Proof. exact (eq_refl (term119 _93497 P t)). Qed.
Lemma lem3650521 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term484 _93490 _93497 s x f P t) = (term480 _93490 _93497 s x f P t).
Proof. exact (MK_COMB (@lem3650519 _93490 _93497 s x t f) (@lem3650520 _93497 P t)). Qed.
Lemma lem3650522 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3650523 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term490 _93490 _93497 s x f P t) = (term491 _93490 _93497 s x f P t).
Proof. exact (MK_COMB (@lem3650522) (@lem3650521 _93490 _93497 s x f P t)). Qed.
Lemma lem3650524 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term486 _93490 _93497 s x t f y) = (term459 _93490 _93497 s x y t f).
Proof. exact (eq_refl (term486 _93490 _93497 s x t f y)). Qed.
Lemma lem3650525 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3650526 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term492 _93490 _93497 s x t f y) = (term493 _93490 _93497 s x y t f).
Proof. exact (MK_COMB (@lem3650525) (@lem3650524 _93490 _93497 s x y t f)). Qed.
Lemma lem3650527 {_93497 : Type'} (P : type686 _93497) (t : _93497 -> Prop) : (term119 _93497 P t) = (term119 _93497 P t).
Proof. exact (eq_refl (term119 _93497 P t)). Qed.
Lemma lem3650528 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term494 _93490 _93497 s x f y P t) = (term495 _93490 _93497 s x y f P t).
Proof. exact (MK_COMB (@lem3650526 _93490 _93497 s x y t f) (@lem3650527 _93497 P t)). Qed.
Lemma lem3650529 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term496 _93490 _93497 s x f P t) = (term497 _93490 _93497 s x f P t).
Proof. exact (fun_ext (fun y : type684 _93490 => @lem3650528 _93490 _93497 s x y f P t)). Qed.
Lemma lem3650530 {_93490 : Type'} : (@ex ((_93490 -> Prop) -> _93490)) = (@ex ((_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650531 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term485 _93490 _93497 s x f P t) = (term498 _93490 _93497 s x f P t).
Proof. exact (MK_COMB (@lem3650530 _93490) (@lem3650529 _93490 _93497 s x f P t)). Qed.
Lemma lem3650532 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : ((term484 _93490 _93497 s x f P t) = (term485 _93490 _93497 s x f P t)) = ((term480 _93490 _93497 s x f P t) = (term498 _93490 _93497 s x f P t)).
Proof. exact (MK_COMB (@lem3650523 _93490 _93497 s x f P t) (@lem3650531 _93490 _93497 s x f P t)). Qed.
Lemma lem3650533 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term480 _93490 _93497 s x f P t) = (term498 _93490 _93497 s x f P t).
Proof. exact (EQ_MP (@lem3650532 _93490 _93497 s x f P t) (@lem3650513 _93490 _93497 s x f P t)). Qed.
Lemma lem3650534 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term482 _93490 _93497 s f P t) = (term499 _93490 _93497 s f P t).
Proof. exact (fun_ext (fun x : type684 _93490 => @lem3650533 _93490 _93497 s x f P t)). Qed.
Lemma lem3650535 {_93490 : Type'} : (@ex ((_93490 -> Prop) -> _93490)) = (@ex ((_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650536 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term483 _93490 _93497 s f P t) = (term500 _93490 _93497 s f P t).
Proof. exact (MK_COMB (@lem3650535 _93490) (@lem3650534 _93490 _93497 s f P t)). Qed.
Lemma lem3650537 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term466 _93490 _93497 s f P t) = (term500 _93490 _93497 s f P t).
Proof. exact (TRANS (@lem3650509 _93490 _93497 s f P t) (@lem3650536 _93490 _93497 s f P t)). Qed.
Lemma lem3650538 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term123 _93490 _93497 s f P t) = (term500 _93490 _93497 s f P t).
Proof. exact (TRANS (@lem3650485 _93490 _93497 s f P t) (@lem3650537 _93490 _93497 s f P t)). Qed.
Lemma lem3650539 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term132 _93490 _93497 s f P) = (term501 _93490 _93497 s f P).
Proof. exact (fun_ext (fun t : _93497 -> Prop => @lem3650538 _93490 _93497 s f P t)). Qed.
Lemma lem3650540 {_93497 : Type'} : (@all (_93497 -> Prop)) = (@all (_93497 -> Prop)).
Proof. exact (eq_refl (@all (_93497 -> Prop))). Qed.
Lemma lem3650541 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term133 _93490 _93497 s f P) = (term502 _93490 _93497 s f P).
Proof. exact (MK_COMB (@lem3650540 _93497) (@lem3650539 _93490 _93497 s f P)). Qed.
Lemma lem3650543 {A B : Type'} (P : type1413 A B) : (term254 A B P) = (term255 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3650544 {_93490 _93497 : Type'} (P : type821 _93490 _93497) : (term503 _93490 _93497 P) = (term504 _93490 _93497 P).
Proof. exact (@lem3650543 (_93497 -> Prop) (type684 _93490) P). Qed.
Lemma lem3650545 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term505 _93490 _93497 s f P) = (term506 _93490 _93497 s f P).
Proof. exact (@lem3650544 _93490 _93497 (term507 _93490 _93497 s f P)). Qed.
Lemma lem3650546 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term508 _93490 _93497 s f P t) = (term499 _93490 _93497 s f P t).
Proof. exact (eq_refl (term508 _93490 _93497 s f P t)). Qed.
Lemma lem3650547 {_93490 : Type'} (x : type684 _93490) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3650548 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) (x : type684 _93490) : (term509 _93490 _93497 s f P t x) = (term510 _93490 _93497 s f P t x).
Proof. exact (MK_COMB (@lem3650546 _93490 _93497 s f P t) (@lem3650547 _93490 x)). Qed.
Lemma lem3650549 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term510 _93490 _93497 s f P t x) = (term498 _93490 _93497 s x f P t).
Proof. exact (eq_refl (term510 _93490 _93497 s f P t x)). Qed.
Lemma lem3650550 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term509 _93490 _93497 s f P t x) = (term498 _93490 _93497 s x f P t).
Proof. exact (TRANS (@lem3650548 _93490 _93497 s f P t x) (@lem3650549 _93490 _93497 s x f P t)). Qed.
Lemma lem3650551 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term511 _93490 _93497 s f P t) = (term499 _93490 _93497 s f P t).
Proof. exact (fun_ext (fun x : type684 _93490 => @lem3650550 _93490 _93497 s x f P t)). Qed.
Lemma lem3650552 {_93490 : Type'} : (@ex ((_93490 -> Prop) -> _93490)) = (@ex ((_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650553 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term512 _93490 _93497 s f P t) = (term500 _93490 _93497 s f P t).
Proof. exact (MK_COMB (@lem3650552 _93490) (@lem3650551 _93490 _93497 s f P t)). Qed.
Lemma lem3650554 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term513 _93490 _93497 s f P) = (term501 _93490 _93497 s f P).
Proof. exact (fun_ext (fun t : _93497 -> Prop => @lem3650553 _93490 _93497 s f P t)). Qed.
Lemma lem3650555 {_93497 : Type'} : (@all (_93497 -> Prop)) = (@all (_93497 -> Prop)).
Proof. exact (eq_refl (@all (_93497 -> Prop))). Qed.
Lemma lem3650556 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term505 _93490 _93497 s f P) = (term502 _93490 _93497 s f P).
Proof. exact (MK_COMB (@lem3650555 _93497) (@lem3650554 _93490 _93497 s f P)). Qed.
Lemma lem3650557 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3650558 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term514 _93490 _93497 s f P) = (term515 _93490 _93497 s f P).
Proof. exact (MK_COMB (@lem3650557) (@lem3650556 _93490 _93497 s f P)). Qed.
Lemma lem3650559 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term508 _93490 _93497 s f P t) = (term499 _93490 _93497 s f P t).
Proof. exact (eq_refl (term508 _93490 _93497 s f P t)). Qed.
Lemma lem3650560 {_93490 _93497 : Type'} (x : type840 _93490 _93497) (t : _93497 -> Prop) : (x t) = (x t).
Proof. exact (eq_refl (x t)). Qed.
Lemma lem3650561 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (x : type840 _93490 _93497) (t : _93497 -> Prop) : (term516 _93490 _93497 s f P x t) = (term517 _93490 _93497 s f P x t).
Proof. exact (MK_COMB (@lem3650559 _93490 _93497 s f P t) (@lem3650560 _93490 _93497 x t)). Qed.
Lemma lem3650562 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term517 _93490 _93497 s f P x t) = (term518 _93490 _93497 s x f P t).
Proof. exact (eq_refl (term517 _93490 _93497 s f P x t)). Qed.
Lemma lem3650563 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term516 _93490 _93497 s f P x t) = (term518 _93490 _93497 s x f P t).
Proof. exact (TRANS (@lem3650561 _93490 _93497 s f P x t) (@lem3650562 _93490 _93497 s x f P t)). Qed.
Lemma lem3650564 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) : (term519 _93490 _93497 s f P x) = (term520 _93490 _93497 s x f P).
Proof. exact (fun_ext (fun t : _93497 -> Prop => @lem3650563 _93490 _93497 s x f P t)). Qed.
Lemma lem3650565 {_93497 : Type'} : (@all (_93497 -> Prop)) = (@all (_93497 -> Prop)).
Proof. exact (eq_refl (@all (_93497 -> Prop))). Qed.
Lemma lem3650566 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) : (term521 _93490 _93497 s f P x) = (term522 _93490 _93497 s x f P).
Proof. exact (MK_COMB (@lem3650565 _93497) (@lem3650564 _93490 _93497 s x f P)). Qed.
Lemma lem3650567 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term523 _93490 _93497 s f P) = (term524 _93490 _93497 s f P).
Proof. exact (fun_ext (fun x : type840 _93490 _93497 => @lem3650566 _93490 _93497 s x f P)). Qed.
Lemma lem3650568 {_93490 _93497 : Type'} : (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490)) = (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650569 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term506 _93490 _93497 s f P) = (term525 _93490 _93497 s f P).
Proof. exact (MK_COMB (@lem3650568 _93490 _93497) (@lem3650567 _93490 _93497 s f P)). Qed.
Lemma lem3650570 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : ((term505 _93490 _93497 s f P) = (term506 _93490 _93497 s f P)) = ((term502 _93490 _93497 s f P) = (term525 _93490 _93497 s f P)).
Proof. exact (MK_COMB (@lem3650558 _93490 _93497 s f P) (@lem3650569 _93490 _93497 s f P)). Qed.
Lemma lem3650571 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term502 _93490 _93497 s f P) = (term525 _93490 _93497 s f P).
Proof. exact (EQ_MP (@lem3650570 _93490 _93497 s f P) (@lem3650545 _93490 _93497 s f P)). Qed.
Lemma lem3650573 {A B : Type'} (P : type1413 A B) : (term254 A B P) = (term255 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3650574 {_93490 _93497 : Type'} (P : type821 _93490 _93497) : (term503 _93490 _93497 P) = (term504 _93490 _93497 P).
Proof. exact (@lem3650573 (_93497 -> Prop) (type684 _93490) P). Qed.
Lemma lem3650575 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) : (term526 _93490 _93497 s x f P) = (term527 _93490 _93497 s x f P).
Proof. exact (@lem3650574 _93490 _93497 (term528 _93490 _93497 s x f P)). Qed.
Lemma lem3650576 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term529 _93490 _93497 s x f P t) = (term530 _93490 _93497 s x f P t).
Proof. exact (eq_refl (term529 _93490 _93497 s x f P t)). Qed.
Lemma lem3650577 {_93490 : Type'} (y : type684 _93490) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3650578 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) (y : type684 _93490) : (term531 _93490 _93497 s x f P t y) = (term532 _93490 _93497 s x f P t y).
Proof. exact (MK_COMB (@lem3650576 _93490 _93497 s x f P t) (@lem3650577 _93490 y)). Qed.
Lemma lem3650579 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (y : type684 _93490) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term532 _93490 _93497 s x f P t y) = (term533 _93490 _93497 s x y f P t).
Proof. exact (eq_refl (term532 _93490 _93497 s x f P t y)). Qed.
Lemma lem3650580 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (y : type684 _93490) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term531 _93490 _93497 s x f P t y) = (term533 _93490 _93497 s x y f P t).
Proof. exact (TRANS (@lem3650578 _93490 _93497 s x f P t y) (@lem3650579 _93490 _93497 s x y f P t)). Qed.
Lemma lem3650581 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term534 _93490 _93497 s x f P t) = (term530 _93490 _93497 s x f P t).
Proof. exact (fun_ext (fun y : type684 _93490 => @lem3650580 _93490 _93497 s x y f P t)). Qed.
Lemma lem3650582 {_93490 : Type'} : (@ex ((_93490 -> Prop) -> _93490)) = (@ex ((_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650583 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term535 _93490 _93497 s x f P t) = (term518 _93490 _93497 s x f P t).
Proof. exact (MK_COMB (@lem3650582 _93490) (@lem3650581 _93490 _93497 s x f P t)). Qed.
Lemma lem3650584 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) : (term536 _93490 _93497 s x f P) = (term520 _93490 _93497 s x f P).
Proof. exact (fun_ext (fun t : _93497 -> Prop => @lem3650583 _93490 _93497 s x f P t)). Qed.
Lemma lem3650585 {_93497 : Type'} : (@all (_93497 -> Prop)) = (@all (_93497 -> Prop)).
Proof. exact (eq_refl (@all (_93497 -> Prop))). Qed.
Lemma lem3650586 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) : (term526 _93490 _93497 s x f P) = (term522 _93490 _93497 s x f P).
Proof. exact (MK_COMB (@lem3650585 _93497) (@lem3650584 _93490 _93497 s x f P)). Qed.
Lemma lem3650587 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3650588 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) : (term537 _93490 _93497 s x f P) = (term538 _93490 _93497 s x f P).
Proof. exact (MK_COMB (@lem3650587) (@lem3650586 _93490 _93497 s x f P)). Qed.
Lemma lem3650589 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term529 _93490 _93497 s x f P t) = (term530 _93490 _93497 s x f P t).
Proof. exact (eq_refl (term529 _93490 _93497 s x f P t)). Qed.
Lemma lem3650590 {_93490 _93497 : Type'} (y : type840 _93490 _93497) (t : _93497 -> Prop) : (y t) = (y t).
Proof. exact (eq_refl (y t)). Qed.
Lemma lem3650591 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) (y : type840 _93490 _93497) (t : _93497 -> Prop) : (term539 _93490 _93497 s x f P y t) = (term540 _93490 _93497 s x f P y t).
Proof. exact (MK_COMB (@lem3650589 _93490 _93497 s x f P t) (@lem3650590 _93490 _93497 y t)). Qed.
Lemma lem3650592 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (y : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term540 _93490 _93497 s x f P y t) = (term541 _93490 _93497 s x y f P t).
Proof. exact (eq_refl (term540 _93490 _93497 s x f P y t)). Qed.
Lemma lem3650593 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (y : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term539 _93490 _93497 s x f P y t) = (term541 _93490 _93497 s x y f P t).
Proof. exact (TRANS (@lem3650591 _93490 _93497 s x f P y t) (@lem3650592 _93490 _93497 s x y f P t)). Qed.
Lemma lem3650594 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (y : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) : (term542 _93490 _93497 s x f P y) = (term543 _93490 _93497 s x y f P).
Proof. exact (fun_ext (fun t : _93497 -> Prop => @lem3650593 _93490 _93497 s x y f P t)). Qed.
Lemma lem3650595 {_93497 : Type'} : (@all (_93497 -> Prop)) = (@all (_93497 -> Prop)).
Proof. exact (eq_refl (@all (_93497 -> Prop))). Qed.
Lemma lem3650596 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (y : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) : (term544 _93490 _93497 s x f P y) = (term545 _93490 _93497 s x y f P).
Proof. exact (MK_COMB (@lem3650595 _93497) (@lem3650594 _93490 _93497 s x y f P)). Qed.
Lemma lem3650597 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) : (term546 _93490 _93497 s x f P) = (term547 _93490 _93497 s x f P).
Proof. exact (fun_ext (fun y : type840 _93490 _93497 => @lem3650596 _93490 _93497 s x y f P)). Qed.
Lemma lem3650598 {_93490 _93497 : Type'} : (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490)) = (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650599 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) : (term527 _93490 _93497 s x f P) = (term548 _93490 _93497 s x f P).
Proof. exact (MK_COMB (@lem3650598 _93490 _93497) (@lem3650597 _93490 _93497 s x f P)). Qed.
Lemma lem3650600 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) : ((term526 _93490 _93497 s x f P) = (term527 _93490 _93497 s x f P)) = ((term522 _93490 _93497 s x f P) = (term548 _93490 _93497 s x f P)).
Proof. exact (MK_COMB (@lem3650588 _93490 _93497 s x f P) (@lem3650599 _93490 _93497 s x f P)). Qed.
Lemma lem3650601 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) : (term522 _93490 _93497 s x f P) = (term548 _93490 _93497 s x f P).
Proof. exact (EQ_MP (@lem3650600 _93490 _93497 s x f P) (@lem3650575 _93490 _93497 s x f P)). Qed.
Lemma lem3650602 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term524 _93490 _93497 s f P) = (term549 _93490 _93497 s f P).
Proof. exact (fun_ext (fun x : type840 _93490 _93497 => @lem3650601 _93490 _93497 s x f P)). Qed.
Lemma lem3650603 {_93490 _93497 : Type'} : (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490)) = (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650604 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term525 _93490 _93497 s f P) = (term550 _93490 _93497 s f P).
Proof. exact (MK_COMB (@lem3650603 _93490 _93497) (@lem3650602 _93490 _93497 s f P)). Qed.
Lemma lem3650605 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term502 _93490 _93497 s f P) = (term550 _93490 _93497 s f P).
Proof. exact (TRANS (@lem3650571 _93490 _93497 s f P) (@lem3650604 _93490 _93497 s f P)). Qed.
Lemma lem3650606 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term133 _93490 _93497 s f P) = (term550 _93490 _93497 s f P).
Proof. exact (TRANS (@lem3650541 _93490 _93497 s f P) (@lem3650605 _93490 _93497 s f P)). Qed.
Lemma lem3650607 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3650608 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term155 _93490 _93497 s f P) = (term551 _93490 _93497 s f P).
Proof. exact (MK_COMB (@lem3650607) (@lem3650606 _93490 _93497 s f P)). Qed.
Lemma lem3650609 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term153 _93490 _93497 s P f) = (term153 _93490 _93497 s P f).
Proof. exact (eq_refl (term153 _93490 _93497 s P f)). Qed.
Lemma lem3650610 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term157 _93490 _93497 s P f) = (term552 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3650608 _93490 _93497 s f P) (@lem3650609 _93490 _93497 s P f)). Qed.
Lemma lem3650612 {A : Type'} (P : A -> Prop) (Q : Prop) : (term166 A P Q) = (term167 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3650613 {_93490 _93497 : Type'} (P : type215 _93490 _93497) (Q : Prop) : (term553 _93490 _93497 P Q) = (term554 _93490 _93497 P Q).
Proof. exact (@lem3650612 (type840 _93490 _93497) P Q). Qed.
Lemma lem3650614 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term555 _93490 _93497 s P f) = (term556 _93490 _93497 s P f).
Proof. exact (@lem3650613 _93490 _93497 (term549 _93490 _93497 s f P) (term153 _93490 _93497 s P f)). Qed.
Lemma lem3650615 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) : (term557 _93490 _93497 s f P x) = (term548 _93490 _93497 s x f P).
Proof. exact (eq_refl (term557 _93490 _93497 s f P x)). Qed.
Lemma lem3650616 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term558 _93490 _93497 s f P) = (term549 _93490 _93497 s f P).
Proof. exact (fun_ext (fun x : type840 _93490 _93497 => @lem3650615 _93490 _93497 s x f P)). Qed.
Lemma lem3650617 {_93490 _93497 : Type'} : (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490)) = (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650618 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term559 _93490 _93497 s f P) = (term550 _93490 _93497 s f P).
Proof. exact (MK_COMB (@lem3650617 _93490 _93497) (@lem3650616 _93490 _93497 s f P)). Qed.
Lemma lem3650619 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3650620 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) : (term560 _93490 _93497 s f P) = (term551 _93490 _93497 s f P).
Proof. exact (MK_COMB (@lem3650619) (@lem3650618 _93490 _93497 s f P)). Qed.
Lemma lem3650621 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term153 _93490 _93497 s P f) = (term153 _93490 _93497 s P f).
Proof. exact (eq_refl (term153 _93490 _93497 s P f)). Qed.
Lemma lem3650622 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term555 _93490 _93497 s P f) = (term552 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3650620 _93490 _93497 s f P) (@lem3650621 _93490 _93497 s P f)). Qed.
Lemma lem3650623 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3650624 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term561 _93490 _93497 s P f) = (term562 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3650623) (@lem3650622 _93490 _93497 s P f)). Qed.
Lemma lem3650625 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) : (term557 _93490 _93497 s f P x) = (term548 _93490 _93497 s x f P).
Proof. exact (eq_refl (term557 _93490 _93497 s f P x)). Qed.
Lemma lem3650626 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3650627 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) : (term563 _93490 _93497 s f P x) = (term564 _93490 _93497 s x f P).
Proof. exact (MK_COMB (@lem3650626) (@lem3650625 _93490 _93497 s x f P)). Qed.
Lemma lem3650628 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term153 _93490 _93497 s P f) = (term153 _93490 _93497 s P f).
Proof. exact (eq_refl (term153 _93490 _93497 s P f)). Qed.
Lemma lem3650629 {_93490 _93497 : Type'} (x : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term565 _93490 _93497 x s P f) = (term566 _93490 _93497 x s P f).
Proof. exact (MK_COMB (@lem3650627 _93490 _93497 s x f P) (@lem3650628 _93490 _93497 s P f)). Qed.
Lemma lem3650630 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term567 _93490 _93497 s P f) = (term568 _93490 _93497 s P f).
Proof. exact (fun_ext (fun x : type840 _93490 _93497 => @lem3650629 _93490 _93497 x s P f)). Qed.
Lemma lem3650631 {_93490 _93497 : Type'} : (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490)) = (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650632 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term556 _93490 _93497 s P f) = (term569 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3650631 _93490 _93497) (@lem3650630 _93490 _93497 s P f)). Qed.
Lemma lem3650633 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : ((term555 _93490 _93497 s P f) = (term556 _93490 _93497 s P f)) = ((term552 _93490 _93497 s P f) = (term569 _93490 _93497 s P f)).
Proof. exact (MK_COMB (@lem3650624 _93490 _93497 s P f) (@lem3650632 _93490 _93497 s P f)). Qed.
Lemma lem3650634 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term552 _93490 _93497 s P f) = (term569 _93490 _93497 s P f).
Proof. exact (EQ_MP (@lem3650633 _93490 _93497 s P f) (@lem3650614 _93490 _93497 s P f)). Qed.
Lemma lem3650636 {A : Type'} (P : A -> Prop) (Q : Prop) : (term166 A P Q) = (term167 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3650637 {_93490 _93497 : Type'} (P : type215 _93490 _93497) (Q : Prop) : (term553 _93490 _93497 P Q) = (term554 _93490 _93497 P Q).
Proof. exact (@lem3650636 (type840 _93490 _93497) P Q). Qed.
Lemma lem3650638 {_93490 _93497 : Type'} (x : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term570 _93490 _93497 x s P f) = (term571 _93490 _93497 x s P f).
Proof. exact (@lem3650637 _93490 _93497 (term547 _93490 _93497 s x f P) (term153 _93490 _93497 s P f)). Qed.
Lemma lem3650639 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (y : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) : (term572 _93490 _93497 s x f P y) = (term545 _93490 _93497 s x y f P).
Proof. exact (eq_refl (term572 _93490 _93497 s x f P y)). Qed.
Lemma lem3650640 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) : (term573 _93490 _93497 s x f P) = (term547 _93490 _93497 s x f P).
Proof. exact (fun_ext (fun y : type840 _93490 _93497 => @lem3650639 _93490 _93497 s x y f P)). Qed.
Lemma lem3650641 {_93490 _93497 : Type'} : (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490)) = (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650642 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) : (term574 _93490 _93497 s x f P) = (term548 _93490 _93497 s x f P).
Proof. exact (MK_COMB (@lem3650641 _93490 _93497) (@lem3650640 _93490 _93497 s x f P)). Qed.
Lemma lem3650643 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3650644 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) : (term575 _93490 _93497 s x f P) = (term564 _93490 _93497 s x f P).
Proof. exact (MK_COMB (@lem3650643) (@lem3650642 _93490 _93497 s x f P)). Qed.
Lemma lem3650645 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term153 _93490 _93497 s P f) = (term153 _93490 _93497 s P f).
Proof. exact (eq_refl (term153 _93490 _93497 s P f)). Qed.
Lemma lem3650646 {_93490 _93497 : Type'} (x : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term570 _93490 _93497 x s P f) = (term566 _93490 _93497 x s P f).
Proof. exact (MK_COMB (@lem3650644 _93490 _93497 s x f P) (@lem3650645 _93490 _93497 s P f)). Qed.
Lemma lem3650647 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3650648 {_93490 _93497 : Type'} (x : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term576 _93490 _93497 x s P f) = (term577 _93490 _93497 x s P f).
Proof. exact (MK_COMB (@lem3650647) (@lem3650646 _93490 _93497 x s P f)). Qed.
Lemma lem3650649 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (y : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) : (term572 _93490 _93497 s x f P y) = (term545 _93490 _93497 s x y f P).
Proof. exact (eq_refl (term572 _93490 _93497 s x f P y)). Qed.
Lemma lem3650650 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3650651 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (y : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) : (term578 _93490 _93497 s x f P y) = (term579 _93490 _93497 s x y f P).
Proof. exact (MK_COMB (@lem3650650) (@lem3650649 _93490 _93497 s x y f P)). Qed.
Lemma lem3650652 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term153 _93490 _93497 s P f) = (term153 _93490 _93497 s P f).
Proof. exact (eq_refl (term153 _93490 _93497 s P f)). Qed.
Lemma lem3650653 {_93490 _93497 : Type'} (x : type840 _93490 _93497) (y : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term580 _93490 _93497 x y s P f) = (term581 _93490 _93497 x y s P f).
Proof. exact (MK_COMB (@lem3650651 _93490 _93497 s x y f P) (@lem3650652 _93490 _93497 s P f)). Qed.
Lemma lem3650654 {_93490 _93497 : Type'} (x : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term582 _93490 _93497 x s P f) = (term583 _93490 _93497 x s P f).
Proof. exact (fun_ext (fun y : type840 _93490 _93497 => @lem3650653 _93490 _93497 x y s P f)). Qed.
Lemma lem3650655 {_93490 _93497 : Type'} : (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490)) = (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650656 {_93490 _93497 : Type'} (x : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term571 _93490 _93497 x s P f) = (term584 _93490 _93497 x s P f).
Proof. exact (MK_COMB (@lem3650655 _93490 _93497) (@lem3650654 _93490 _93497 x s P f)). Qed.
Lemma lem3650657 {_93490 _93497 : Type'} (x : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : ((term570 _93490 _93497 x s P f) = (term571 _93490 _93497 x s P f)) = ((term566 _93490 _93497 x s P f) = (term584 _93490 _93497 x s P f)).
Proof. exact (MK_COMB (@lem3650648 _93490 _93497 x s P f) (@lem3650656 _93490 _93497 x s P f)). Qed.
Lemma lem3650658 {_93490 _93497 : Type'} (x : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term566 _93490 _93497 x s P f) = (term584 _93490 _93497 x s P f).
Proof. exact (EQ_MP (@lem3650657 _93490 _93497 x s P f) (@lem3650638 _93490 _93497 x s P f)). Qed.
Lemma lem3650660 {A : Type'} (P : Prop) (Q : A -> Prop) : (term335 A P Q) = (term336 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3650661 {_93490 : Type'} (P : Prop) (Q : type686 _93490) : (term585 _93490 P Q) = (term586 _93490 P Q).
Proof. exact (@lem3650660 (_93490 -> Prop) P Q). Qed.
Lemma lem3650662 {_93490 _93497 : Type'} (x : type840 _93490 _93497) (y : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term587 _93490 _93497 x y s P f) = (term588 _93490 _93497 x y s P f).
Proof. exact (@lem3650661 _93490 (term545 _93490 _93497 s x y f P) (term152 _93490 _93497 s P f)). Qed.
Lemma lem3650663 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term589 _93490 _93497 s P f t) = (term144 _93490 _93497 s P f t).
Proof. exact (eq_refl (term589 _93490 _93497 s P f t)). Qed.
Lemma lem3650664 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term590 _93490 _93497 s P f) = (term152 _93490 _93497 s P f).
Proof. exact (fun_ext (fun t : _93490 -> Prop => @lem3650663 _93490 _93497 s P f t)). Qed.
Lemma lem3650665 {_93490 : Type'} : (@ex (_93490 -> Prop)) = (@ex (_93490 -> Prop)).
Proof. exact (eq_refl (@ex (_93490 -> Prop))). Qed.
Lemma lem3650666 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term591 _93490 _93497 s P f) = (term153 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3650665 _93490) (@lem3650664 _93490 _93497 s P f)). Qed.
Lemma lem3650667 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (y : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) : (term579 _93490 _93497 s x y f P) = (term579 _93490 _93497 s x y f P).
Proof. exact (eq_refl (term579 _93490 _93497 s x y f P)). Qed.
Lemma lem3650668 {_93490 _93497 : Type'} (x : type840 _93490 _93497) (y : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term587 _93490 _93497 x y s P f) = (term581 _93490 _93497 x y s P f).
Proof. exact (MK_COMB (@lem3650667 _93490 _93497 s x y f P) (@lem3650666 _93490 _93497 s P f)). Qed.
Lemma lem3650669 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3650670 {_93490 _93497 : Type'} (x : type840 _93490 _93497) (y : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term592 _93490 _93497 x y s P f) = (term593 _93490 _93497 x y s P f).
Proof. exact (MK_COMB (@lem3650669) (@lem3650668 _93490 _93497 x y s P f)). Qed.
Lemma lem3650671 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term589 _93490 _93497 s P f t) = (term144 _93490 _93497 s P f t).
Proof. exact (eq_refl (term589 _93490 _93497 s P f t)). Qed.
Lemma lem3650672 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type840 _93490 _93497) (y : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) : (term579 _93490 _93497 s x y f P) = (term579 _93490 _93497 s x y f P).
Proof. exact (eq_refl (term579 _93490 _93497 s x y f P)). Qed.
Lemma lem3650673 {_93490 _93497 : Type'} (x : type840 _93490 _93497) (y : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term594 _93490 _93497 x y s P f t) = (term595 _93490 _93497 x y s P f t).
Proof. exact (MK_COMB (@lem3650672 _93490 _93497 s x y f P) (@lem3650671 _93490 _93497 s P f t)). Qed.
Lemma lem3650674 {_93490 _93497 : Type'} (x : type840 _93490 _93497) (y : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term596 _93490 _93497 x y s P f) = (term597 _93490 _93497 x y s P f).
Proof. exact (fun_ext (fun t : _93490 -> Prop => @lem3650673 _93490 _93497 x y s P f t)). Qed.
Lemma lem3650675 {_93490 : Type'} : (@ex (_93490 -> Prop)) = (@ex (_93490 -> Prop)).
Proof. exact (eq_refl (@ex (_93490 -> Prop))). Qed.
Lemma lem3650676 {_93490 _93497 : Type'} (x : type840 _93490 _93497) (y : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term588 _93490 _93497 x y s P f) = (term598 _93490 _93497 x y s P f).
Proof. exact (MK_COMB (@lem3650675 _93490) (@lem3650674 _93490 _93497 x y s P f)). Qed.
Lemma lem3650677 {_93490 _93497 : Type'} (x : type840 _93490 _93497) (y : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : ((term587 _93490 _93497 x y s P f) = (term588 _93490 _93497 x y s P f)) = ((term581 _93490 _93497 x y s P f) = (term598 _93490 _93497 x y s P f)).
Proof. exact (MK_COMB (@lem3650670 _93490 _93497 x y s P f) (@lem3650676 _93490 _93497 x y s P f)). Qed.
Lemma lem3650678 {_93490 _93497 : Type'} (x : type840 _93490 _93497) (y : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term581 _93490 _93497 x y s P f) = (term598 _93490 _93497 x y s P f).
Proof. exact (EQ_MP (@lem3650677 _93490 _93497 x y s P f) (@lem3650662 _93490 _93497 x y s P f)). Qed.
Lemma lem3650679 {_93490 _93497 : Type'} (x : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term583 _93490 _93497 x s P f) = (term599 _93490 _93497 x s P f).
Proof. exact (fun_ext (fun y : type840 _93490 _93497 => @lem3650678 _93490 _93497 x y s P f)). Qed.
Lemma lem3650680 {_93490 _93497 : Type'} : (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490)) = (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650681 {_93490 _93497 : Type'} (x : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term584 _93490 _93497 x s P f) = (term600 _93490 _93497 x s P f).
Proof. exact (MK_COMB (@lem3650680 _93490 _93497) (@lem3650679 _93490 _93497 x s P f)). Qed.
Lemma lem3650682 {_93490 _93497 : Type'} (x : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term566 _93490 _93497 x s P f) = (term600 _93490 _93497 x s P f).
Proof. exact (TRANS (@lem3650658 _93490 _93497 x s P f) (@lem3650681 _93490 _93497 x s P f)). Qed.
Lemma lem3650683 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term568 _93490 _93497 s P f) = (term601 _93490 _93497 s P f).
Proof. exact (fun_ext (fun x : type840 _93490 _93497 => @lem3650682 _93490 _93497 x s P f)). Qed.
Lemma lem3650684 {_93490 _93497 : Type'} : (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490)) = (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650685 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term569 _93490 _93497 s P f) = (term602 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3650684 _93490 _93497) (@lem3650683 _93490 _93497 s P f)). Qed.
Lemma lem3650686 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term552 _93490 _93497 s P f) = (term602 _93490 _93497 s P f).
Proof. exact (TRANS (@lem3650634 _93490 _93497 s P f) (@lem3650685 _93490 _93497 s P f)). Qed.
Lemma lem3650687 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term157 _93490 _93497 s P f) = (term602 _93490 _93497 s P f).
Proof. exact (TRANS (@lem3650610 _93490 _93497 s P f) (@lem3650686 _93490 _93497 s P f)). Qed.
Lemma lem3650688 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term165 _93490 _93497 s P f) = (term603 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3650314 _93490 _93497 s P f) (@lem3650687 _93490 _93497 s P f)). Qed.
Lemma lem3650692 {A : Type'} (P : A -> Prop) (Q : Prop) : (term188 A P Q) = (term189 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3650693 {_93497 : Type'} (P : type686 _93497) (Q : Prop) : (term604 _93497 P Q) = (term605 _93497 P Q).
Proof. exact (@lem3650692 (_93497 -> Prop) P Q). Qed.
Lemma lem3650694 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term606 _93490 _93497 s P f) = (term607 _93490 _93497 s P f).
Proof. exact (@lem3650693 _93497 (term367 _93490 _93497 s P f) (term602 _93490 _93497 s P f)). Qed.
Lemma lem3650695 {_93490 _93497 : Type'} (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term608 _93490 _93497 s P f t) = (term366 _93490 _93497 t s P f).
Proof. exact (eq_refl (term608 _93490 _93497 s P f t)). Qed.
Lemma lem3650696 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term609 _93490 _93497 s P f) = (term367 _93490 _93497 s P f).
Proof. exact (fun_ext (fun t : _93497 -> Prop => @lem3650695 _93490 _93497 t s P f)). Qed.
Lemma lem3650697 {_93497 : Type'} : (@ex (_93497 -> Prop)) = (@ex (_93497 -> Prop)).
Proof. exact (eq_refl (@ex (_93497 -> Prop))). Qed.
Lemma lem3650698 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term610 _93490 _93497 s P f) = (term368 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3650697 _93497) (@lem3650696 _93490 _93497 s P f)). Qed.
Lemma lem3650699 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3650700 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term611 _93490 _93497 s P f) = (term369 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3650699) (@lem3650698 _93490 _93497 s P f)). Qed.
Lemma lem3650701 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term602 _93490 _93497 s P f) = (term602 _93490 _93497 s P f).
Proof. exact (eq_refl (term602 _93490 _93497 s P f)). Qed.
Lemma lem3650702 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term606 _93490 _93497 s P f) = (term603 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3650700 _93490 _93497 s P f) (@lem3650701 _93490 _93497 s P f)). Qed.
Lemma lem3650703 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3650704 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term612 _93490 _93497 s P f) = (term613 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3650703) (@lem3650702 _93490 _93497 s P f)). Qed.
Lemma lem3650705 {_93490 _93497 : Type'} (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term608 _93490 _93497 s P f t) = (term366 _93490 _93497 t s P f).
Proof. exact (eq_refl (term608 _93490 _93497 s P f t)). Qed.
Lemma lem3650706 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3650707 {_93490 _93497 : Type'} (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term614 _93490 _93497 s P f t) = (term615 _93490 _93497 t s P f).
Proof. exact (MK_COMB (@lem3650706) (@lem3650705 _93490 _93497 t s P f)). Qed.
Lemma lem3650708 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term602 _93490 _93497 s P f) = (term602 _93490 _93497 s P f).
Proof. exact (eq_refl (term602 _93490 _93497 s P f)). Qed.
Lemma lem3650709 {_93490 _93497 : Type'} (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term616 _93490 _93497 t s P f) = (term617 _93490 _93497 t s P f).
Proof. exact (MK_COMB (@lem3650707 _93490 _93497 t s P f) (@lem3650708 _93490 _93497 s P f)). Qed.
Lemma lem3650710 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term618 _93490 _93497 s P f) = (term619 _93490 _93497 s P f).
Proof. exact (fun_ext (fun t : _93497 -> Prop => @lem3650709 _93490 _93497 t s P f)). Qed.
Lemma lem3650711 {_93497 : Type'} : (@ex (_93497 -> Prop)) = (@ex (_93497 -> Prop)).
Proof. exact (eq_refl (@ex (_93497 -> Prop))). Qed.
Lemma lem3650712 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term607 _93490 _93497 s P f) = (term620 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3650711 _93497) (@lem3650710 _93490 _93497 s P f)). Qed.
Lemma lem3650713 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : ((term606 _93490 _93497 s P f) = (term607 _93490 _93497 s P f)) = ((term603 _93490 _93497 s P f) = (term620 _93490 _93497 s P f)).
Proof. exact (MK_COMB (@lem3650704 _93490 _93497 s P f) (@lem3650712 _93490 _93497 s P f)). Qed.
Lemma lem3650714 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term603 _93490 _93497 s P f) = (term620 _93490 _93497 s P f).
Proof. exact (EQ_MP (@lem3650713 _93490 _93497 s P f) (@lem3650694 _93490 _93497 s P f)). Qed.
Lemma lem3650718 {A : Type'} (P : A -> Prop) (Q : Prop) : (term188 A P Q) = (term189 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3650719 {_93490 : Type'} (P : type686 _93490) (Q : Prop) : (term604 _93490 P Q) = (term605 _93490 P Q).
Proof. exact (@lem3650718 (_93490 -> Prop) P Q). Qed.
Lemma lem3650720 {_93490 _93497 : Type'} (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term621 _93490 _93497 t s P f) = (term622 _93490 _93497 t s P f).
Proof. exact (@lem3650719 _93490 (term365 _93490 _93497 t s P f) (term602 _93490 _93497 s P f)). Qed.
Lemma lem3650721 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term623 _93490 _93497 t s P f u) = (term364 _93490 _93497 u t s P f).
Proof. exact (eq_refl (term623 _93490 _93497 t s P f u)). Qed.
Lemma lem3650722 {_93490 _93497 : Type'} (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term624 _93490 _93497 t s P f) = (term365 _93490 _93497 t s P f).
Proof. exact (fun_ext (fun u : _93490 -> Prop => @lem3650721 _93490 _93497 u t s P f)). Qed.
Lemma lem3650723 {_93490 : Type'} : (@ex (_93490 -> Prop)) = (@ex (_93490 -> Prop)).
Proof. exact (eq_refl (@ex (_93490 -> Prop))). Qed.
Lemma lem3650724 {_93490 _93497 : Type'} (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term625 _93490 _93497 t s P f) = (term366 _93490 _93497 t s P f).
Proof. exact (MK_COMB (@lem3650723 _93490) (@lem3650722 _93490 _93497 t s P f)). Qed.
Lemma lem3650725 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3650726 {_93490 _93497 : Type'} (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term626 _93490 _93497 t s P f) = (term615 _93490 _93497 t s P f).
Proof. exact (MK_COMB (@lem3650725) (@lem3650724 _93490 _93497 t s P f)). Qed.
Lemma lem3650727 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term602 _93490 _93497 s P f) = (term602 _93490 _93497 s P f).
Proof. exact (eq_refl (term602 _93490 _93497 s P f)). Qed.
Lemma lem3650728 {_93490 _93497 : Type'} (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term621 _93490 _93497 t s P f) = (term617 _93490 _93497 t s P f).
Proof. exact (MK_COMB (@lem3650726 _93490 _93497 t s P f) (@lem3650727 _93490 _93497 s P f)). Qed.
Lemma lem3650729 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3650730 {_93490 _93497 : Type'} (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term627 _93490 _93497 t s P f) = (term628 _93490 _93497 t s P f).
Proof. exact (MK_COMB (@lem3650729) (@lem3650728 _93490 _93497 t s P f)). Qed.
Lemma lem3650731 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term623 _93490 _93497 t s P f u) = (term364 _93490 _93497 u t s P f).
Proof. exact (eq_refl (term623 _93490 _93497 t s P f u)). Qed.
Lemma lem3650732 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3650733 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term629 _93490 _93497 t s P f u) = (term630 _93490 _93497 u t s P f).
Proof. exact (MK_COMB (@lem3650732) (@lem3650731 _93490 _93497 u t s P f)). Qed.
Lemma lem3650734 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term602 _93490 _93497 s P f) = (term602 _93490 _93497 s P f).
Proof. exact (eq_refl (term602 _93490 _93497 s P f)). Qed.
Lemma lem3650735 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term631 _93490 _93497 t u s P f) = (term632 _93490 _93497 u t s P f).
Proof. exact (MK_COMB (@lem3650733 _93490 _93497 u t s P f) (@lem3650734 _93490 _93497 s P f)). Qed.
Lemma lem3650736 {_93490 _93497 : Type'} (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term633 _93490 _93497 t s P f) = (term634 _93490 _93497 t s P f).
Proof. exact (fun_ext (fun u : _93490 -> Prop => @lem3650735 _93490 _93497 u t s P f)). Qed.
Lemma lem3650737 {_93490 : Type'} : (@ex (_93490 -> Prop)) = (@ex (_93490 -> Prop)).
Proof. exact (eq_refl (@ex (_93490 -> Prop))). Qed.
Lemma lem3650738 {_93490 _93497 : Type'} (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term622 _93490 _93497 t s P f) = (term635 _93490 _93497 t s P f).
Proof. exact (MK_COMB (@lem3650737 _93490) (@lem3650736 _93490 _93497 t s P f)). Qed.
Lemma lem3650739 {_93490 _93497 : Type'} (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : ((term621 _93490 _93497 t s P f) = (term622 _93490 _93497 t s P f)) = ((term617 _93490 _93497 t s P f) = (term635 _93490 _93497 t s P f)).
Proof. exact (MK_COMB (@lem3650730 _93490 _93497 t s P f) (@lem3650738 _93490 _93497 t s P f)). Qed.
Lemma lem3650740 {_93490 _93497 : Type'} (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term617 _93490 _93497 t s P f) = (term635 _93490 _93497 t s P f).
Proof. exact (EQ_MP (@lem3650739 _93490 _93497 t s P f) (@lem3650720 _93490 _93497 t s P f)). Qed.
Lemma lem3650744 {A : Type'} (P : A -> Prop) (Q : Prop) : (term188 A P Q) = (term189 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3650745 {_93490 : Type'} (P : type162 _93490) (Q : Prop) : (term467 _93490 P Q) = (term468 _93490 P Q).
Proof. exact (@lem3650744 (type684 _93490) P Q). Qed.
Lemma lem3650746 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term636 _93490 _93497 u t s P f) = (term637 _93490 _93497 u t s P f).
Proof. exact (@lem3650745 _93490 (term363 _93490 _93497 u t s P f) (term602 _93490 _93497 s P f)). Qed.
Lemma lem3650747 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term638 _93490 _93497 u t s P f x) = (term362 _93490 _93497 u t s x P f).
Proof. exact (eq_refl (term638 _93490 _93497 u t s P f x)). Qed.
Lemma lem3650748 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term639 _93490 _93497 u t s P f) = (term363 _93490 _93497 u t s P f).
Proof. exact (fun_ext (fun x : type684 _93490 => @lem3650747 _93490 _93497 u t s x P f)). Qed.
Lemma lem3650749 {_93490 : Type'} : (@ex ((_93490 -> Prop) -> _93490)) = (@ex ((_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650750 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term640 _93490 _93497 u t s P f) = (term364 _93490 _93497 u t s P f).
Proof. exact (MK_COMB (@lem3650749 _93490) (@lem3650748 _93490 _93497 u t s P f)). Qed.
Lemma lem3650751 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3650752 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term641 _93490 _93497 u t s P f) = (term630 _93490 _93497 u t s P f).
Proof. exact (MK_COMB (@lem3650751) (@lem3650750 _93490 _93497 u t s P f)). Qed.
Lemma lem3650753 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term602 _93490 _93497 s P f) = (term602 _93490 _93497 s P f).
Proof. exact (eq_refl (term602 _93490 _93497 s P f)). Qed.
Lemma lem3650754 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term636 _93490 _93497 u t s P f) = (term632 _93490 _93497 u t s P f).
Proof. exact (MK_COMB (@lem3650752 _93490 _93497 u t s P f) (@lem3650753 _93490 _93497 s P f)). Qed.
Lemma lem3650755 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3650756 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term642 _93490 _93497 u t s P f) = (term643 _93490 _93497 u t s P f).
Proof. exact (MK_COMB (@lem3650755) (@lem3650754 _93490 _93497 u t s P f)). Qed.
Lemma lem3650757 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term638 _93490 _93497 u t s P f x) = (term362 _93490 _93497 u t s x P f).
Proof. exact (eq_refl (term638 _93490 _93497 u t s P f x)). Qed.
Lemma lem3650758 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3650759 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term644 _93490 _93497 u t s P f x) = (term645 _93490 _93497 u t s x P f).
Proof. exact (MK_COMB (@lem3650758) (@lem3650757 _93490 _93497 u t s x P f)). Qed.
Lemma lem3650760 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term602 _93490 _93497 s P f) = (term602 _93490 _93497 s P f).
Proof. exact (eq_refl (term602 _93490 _93497 s P f)). Qed.
Lemma lem3650761 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term646 _93490 _93497 u t x s P f) = (term647 _93490 _93497 u t x s P f).
Proof. exact (MK_COMB (@lem3650759 _93490 _93497 u t s x P f) (@lem3650760 _93490 _93497 s P f)). Qed.
Lemma lem3650762 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term648 _93490 _93497 u t s P f) = (term649 _93490 _93497 u t s P f).
Proof. exact (fun_ext (fun x : type684 _93490 => @lem3650761 _93490 _93497 u t x s P f)). Qed.
Lemma lem3650763 {_93490 : Type'} : (@ex ((_93490 -> Prop) -> _93490)) = (@ex ((_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650764 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term637 _93490 _93497 u t s P f) = (term650 _93490 _93497 u t s P f).
Proof. exact (MK_COMB (@lem3650763 _93490) (@lem3650762 _93490 _93497 u t s P f)). Qed.
Lemma lem3650765 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : ((term636 _93490 _93497 u t s P f) = (term637 _93490 _93497 u t s P f)) = ((term632 _93490 _93497 u t s P f) = (term650 _93490 _93497 u t s P f)).
Proof. exact (MK_COMB (@lem3650756 _93490 _93497 u t s P f) (@lem3650764 _93490 _93497 u t s P f)). Qed.
Lemma lem3650766 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term632 _93490 _93497 u t s P f) = (term650 _93490 _93497 u t s P f).
Proof. exact (EQ_MP (@lem3650765 _93490 _93497 u t s P f) (@lem3650746 _93490 _93497 u t s P f)). Qed.
Lemma lem3650770 {A : Type'} (P : A -> Prop) (Q : Prop) : (term188 A P Q) = (term189 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3650771 {_93490 : Type'} (P : type162 _93490) (Q : Prop) : (term467 _93490 P Q) = (term468 _93490 P Q).
Proof. exact (@lem3650770 (type684 _93490) P Q). Qed.
Lemma lem3650772 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term651 _93490 _93497 u t x s P f) = (term652 _93490 _93497 u t x s P f).
Proof. exact (@lem3650771 _93490 (term361 _93490 _93497 u t s x P f) (term602 _93490 _93497 s P f)). Qed.
Lemma lem3650773 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term653 _93490 _93497 u t s x P f y) = (term359 _93490 _93497 u t s x y P f).
Proof. exact (eq_refl (term653 _93490 _93497 u t s x P f y)). Qed.
Lemma lem3650774 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term654 _93490 _93497 u t s x P f) = (term361 _93490 _93497 u t s x P f).
Proof. exact (fun_ext (fun y : type684 _93490 => @lem3650773 _93490 _93497 u t s x y P f)). Qed.
Lemma lem3650775 {_93490 : Type'} : (@ex ((_93490 -> Prop) -> _93490)) = (@ex ((_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650776 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term655 _93490 _93497 u t s x P f) = (term362 _93490 _93497 u t s x P f).
Proof. exact (MK_COMB (@lem3650775 _93490) (@lem3650774 _93490 _93497 u t s x P f)). Qed.
Lemma lem3650777 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3650778 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term656 _93490 _93497 u t s x P f) = (term645 _93490 _93497 u t s x P f).
Proof. exact (MK_COMB (@lem3650777) (@lem3650776 _93490 _93497 u t s x P f)). Qed.
Lemma lem3650779 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term602 _93490 _93497 s P f) = (term602 _93490 _93497 s P f).
Proof. exact (eq_refl (term602 _93490 _93497 s P f)). Qed.
Lemma lem3650780 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term651 _93490 _93497 u t x s P f) = (term647 _93490 _93497 u t x s P f).
Proof. exact (MK_COMB (@lem3650778 _93490 _93497 u t s x P f) (@lem3650779 _93490 _93497 s P f)). Qed.
Lemma lem3650781 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3650782 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term657 _93490 _93497 u t x s P f) = (term658 _93490 _93497 u t x s P f).
Proof. exact (MK_COMB (@lem3650781) (@lem3650780 _93490 _93497 u t x s P f)). Qed.
Lemma lem3650783 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term653 _93490 _93497 u t s x P f y) = (term359 _93490 _93497 u t s x y P f).
Proof. exact (eq_refl (term653 _93490 _93497 u t s x P f y)). Qed.
Lemma lem3650784 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3650785 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term659 _93490 _93497 u t s x P f y) = (term660 _93490 _93497 u t s x y P f).
Proof. exact (MK_COMB (@lem3650784) (@lem3650783 _93490 _93497 u t s x y P f)). Qed.
Lemma lem3650786 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term602 _93490 _93497 s P f) = (term602 _93490 _93497 s P f).
Proof. exact (eq_refl (term602 _93490 _93497 s P f)). Qed.
Lemma lem3650787 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term661 _93490 _93497 u t x y s P f) = (term662 _93490 _93497 u t x y s P f).
Proof. exact (MK_COMB (@lem3650785 _93490 _93497 u t s x y P f) (@lem3650786 _93490 _93497 s P f)). Qed.
Lemma lem3650788 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term663 _93490 _93497 u t x s P f) = (term664 _93490 _93497 u t x s P f).
Proof. exact (fun_ext (fun y : type684 _93490 => @lem3650787 _93490 _93497 u t x y s P f)). Qed.
Lemma lem3650789 {_93490 : Type'} : (@ex ((_93490 -> Prop) -> _93490)) = (@ex ((_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650790 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term652 _93490 _93497 u t x s P f) = (term665 _93490 _93497 u t x s P f).
Proof. exact (MK_COMB (@lem3650789 _93490) (@lem3650788 _93490 _93497 u t x s P f)). Qed.
Lemma lem3650791 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : ((term651 _93490 _93497 u t x s P f) = (term652 _93490 _93497 u t x s P f)) = ((term647 _93490 _93497 u t x s P f) = (term665 _93490 _93497 u t x s P f)).
Proof. exact (MK_COMB (@lem3650782 _93490 _93497 u t x s P f) (@lem3650790 _93490 _93497 u t x s P f)). Qed.
Lemma lem3650792 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term647 _93490 _93497 u t x s P f) = (term665 _93490 _93497 u t x s P f).
Proof. exact (EQ_MP (@lem3650791 _93490 _93497 u t x s P f) (@lem3650772 _93490 _93497 u t x s P f)). Qed.
Lemma lem3650794 {A : Type'} (P : Prop) (Q : A -> Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3650795 {_93490 _93497 : Type'} (P : Prop) (Q : type215 _93490 _93497) : (term666 _93490 _93497 P Q) = (term667 _93490 _93497 P Q).
Proof. exact (@lem3650794 (type840 _93490 _93497) P Q). Qed.
Lemma lem3650796 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term668 _93490 _93497 u t x y s P f) = (term669 _93490 _93497 u t x y s P f).
Proof. exact (@lem3650795 _93490 _93497 (term359 _93490 _93497 u t s x y P f) (term601 _93490 _93497 s P f)). Qed.
Lemma lem3650797 {_93490 _93497 : Type'} (x : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term670 _93490 _93497 s P f x) = (term600 _93490 _93497 x s P f).
Proof. exact (eq_refl (term670 _93490 _93497 s P f x)). Qed.
Lemma lem3650798 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term671 _93490 _93497 s P f) = (term601 _93490 _93497 s P f).
Proof. exact (fun_ext (fun x : type840 _93490 _93497 => @lem3650797 _93490 _93497 x s P f)). Qed.
Lemma lem3650799 {_93490 _93497 : Type'} : (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490)) = (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650800 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term672 _93490 _93497 s P f) = (term602 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3650799 _93490 _93497) (@lem3650798 _93490 _93497 s P f)). Qed.
Lemma lem3650801 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term660 _93490 _93497 u t s x y P f) = (term660 _93490 _93497 u t s x y P f).
Proof. exact (eq_refl (term660 _93490 _93497 u t s x y P f)). Qed.
Lemma lem3650802 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term668 _93490 _93497 u t x y s P f) = (term662 _93490 _93497 u t x y s P f).
Proof. exact (MK_COMB (@lem3650801 _93490 _93497 u t s x y P f) (@lem3650800 _93490 _93497 s P f)). Qed.
Lemma lem3650803 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3650804 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term673 _93490 _93497 u t x y s P f) = (term674 _93490 _93497 u t x y s P f).
Proof. exact (MK_COMB (@lem3650803) (@lem3650802 _93490 _93497 u t x y s P f)). Qed.
Lemma lem3650805 {_93490 _93497 : Type'} (x : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term670 _93490 _93497 s P f x) = (term600 _93490 _93497 x s P f).
Proof. exact (eq_refl (term670 _93490 _93497 s P f x)). Qed.
Lemma lem3650806 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term660 _93490 _93497 u t s x y P f) = (term660 _93490 _93497 u t s x y P f).
Proof. exact (eq_refl (term660 _93490 _93497 u t s x y P f)). Qed.
Lemma lem3650807 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (x' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term675 _93490 _93497 u t x y s P f x') = (term676 _93490 _93497 u t x y x' s P f).
Proof. exact (MK_COMB (@lem3650806 _93490 _93497 u t s x y P f) (@lem3650805 _93490 _93497 x' s P f)). Qed.
Lemma lem3650808 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term677 _93490 _93497 u t x y s P f) = (term678 _93490 _93497 u t x y s P f).
Proof. exact (fun_ext (fun x' : type840 _93490 _93497 => @lem3650807 _93490 _93497 u t x y x' s P f)). Qed.
Lemma lem3650809 {_93490 _93497 : Type'} : (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490)) = (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650810 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term669 _93490 _93497 u t x y s P f) = (term679 _93490 _93497 u t x y s P f).
Proof. exact (MK_COMB (@lem3650809 _93490 _93497) (@lem3650808 _93490 _93497 u t x y s P f)). Qed.
Lemma lem3650811 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : ((term668 _93490 _93497 u t x y s P f) = (term669 _93490 _93497 u t x y s P f)) = ((term662 _93490 _93497 u t x y s P f) = (term679 _93490 _93497 u t x y s P f)).
Proof. exact (MK_COMB (@lem3650804 _93490 _93497 u t x y s P f) (@lem3650810 _93490 _93497 u t x y s P f)). Qed.
Lemma lem3650812 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term662 _93490 _93497 u t x y s P f) = (term679 _93490 _93497 u t x y s P f).
Proof. exact (EQ_MP (@lem3650811 _93490 _93497 u t x y s P f) (@lem3650796 _93490 _93497 u t x y s P f)). Qed.
Lemma lem3650814 {A : Type'} (P : Prop) (Q : A -> Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3650815 {_93490 _93497 : Type'} (P : Prop) (Q : type215 _93490 _93497) : (term666 _93490 _93497 P Q) = (term667 _93490 _93497 P Q).
Proof. exact (@lem3650814 (type840 _93490 _93497) P Q). Qed.
Lemma lem3650816 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (x' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term680 _93490 _93497 u t x y x' s P f) = (term681 _93490 _93497 u t x y x' s P f).
Proof. exact (@lem3650815 _93490 _93497 (term359 _93490 _93497 u t s x y P f) (term599 _93490 _93497 x' s P f)). Qed.
Lemma lem3650817 {_93490 _93497 : Type'} (x : type840 _93490 _93497) (y : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term682 _93490 _93497 x s P f y) = (term598 _93490 _93497 x y s P f).
Proof. exact (eq_refl (term682 _93490 _93497 x s P f y)). Qed.
Lemma lem3650818 {_93490 _93497 : Type'} (x : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term683 _93490 _93497 x s P f) = (term599 _93490 _93497 x s P f).
Proof. exact (fun_ext (fun y : type840 _93490 _93497 => @lem3650817 _93490 _93497 x y s P f)). Qed.
Lemma lem3650819 {_93490 _93497 : Type'} : (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490)) = (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650820 {_93490 _93497 : Type'} (x : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term684 _93490 _93497 x s P f) = (term600 _93490 _93497 x s P f).
Proof. exact (MK_COMB (@lem3650819 _93490 _93497) (@lem3650818 _93490 _93497 x s P f)). Qed.
Lemma lem3650821 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term660 _93490 _93497 u t s x y P f) = (term660 _93490 _93497 u t s x y P f).
Proof. exact (eq_refl (term660 _93490 _93497 u t s x y P f)). Qed.
Lemma lem3650822 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (x' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term680 _93490 _93497 u t x y x' s P f) = (term676 _93490 _93497 u t x y x' s P f).
Proof. exact (MK_COMB (@lem3650821 _93490 _93497 u t s x y P f) (@lem3650820 _93490 _93497 x' s P f)). Qed.
Lemma lem3650823 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3650824 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (x' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term685 _93490 _93497 u t x y x' s P f) = (term686 _93490 _93497 u t x y x' s P f).
Proof. exact (MK_COMB (@lem3650823) (@lem3650822 _93490 _93497 u t x y x' s P f)). Qed.
Lemma lem3650825 {_93490 _93497 : Type'} (x : type840 _93490 _93497) (y : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term682 _93490 _93497 x s P f y) = (term598 _93490 _93497 x y s P f).
Proof. exact (eq_refl (term682 _93490 _93497 x s P f y)). Qed.
Lemma lem3650826 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term660 _93490 _93497 u t s x y P f) = (term660 _93490 _93497 u t s x y P f).
Proof. exact (eq_refl (term660 _93490 _93497 u t s x y P f)). Qed.
Lemma lem3650827 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term687 _93490 _93497 u t x y x' s P f y') = (term688 _93490 _93497 u t x y x' y' s P f).
Proof. exact (MK_COMB (@lem3650826 _93490 _93497 u t s x y P f) (@lem3650825 _93490 _93497 x' y' s P f)). Qed.
Lemma lem3650828 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (x' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term689 _93490 _93497 u t x y x' s P f) = (term690 _93490 _93497 u t x y x' s P f).
Proof. exact (fun_ext (fun y' : type840 _93490 _93497 => @lem3650827 _93490 _93497 u t x y x' y' s P f)). Qed.
Lemma lem3650829 {_93490 _93497 : Type'} : (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490)) = (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650830 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (x' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term681 _93490 _93497 u t x y x' s P f) = (term691 _93490 _93497 u t x y x' s P f).
Proof. exact (MK_COMB (@lem3650829 _93490 _93497) (@lem3650828 _93490 _93497 u t x y x' s P f)). Qed.
Lemma lem3650831 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (x' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : ((term680 _93490 _93497 u t x y x' s P f) = (term681 _93490 _93497 u t x y x' s P f)) = ((term676 _93490 _93497 u t x y x' s P f) = (term691 _93490 _93497 u t x y x' s P f)).
Proof. exact (MK_COMB (@lem3650824 _93490 _93497 u t x y x' s P f) (@lem3650830 _93490 _93497 u t x y x' s P f)). Qed.
Lemma lem3650832 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (x' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term676 _93490 _93497 u t x y x' s P f) = (term691 _93490 _93497 u t x y x' s P f).
Proof. exact (EQ_MP (@lem3650831 _93490 _93497 u t x y x' s P f) (@lem3650816 _93490 _93497 u t x y x' s P f)). Qed.
Lemma lem3650834 {A : Type'} (P : Prop) (Q : A -> Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3650835 {_93490 : Type'} (P : Prop) (Q : type686 _93490) : (term692 _93490 P Q) = (term693 _93490 P Q).
Proof. exact (@lem3650834 (_93490 -> Prop) P Q). Qed.
Lemma lem3650836 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term694 _93490 _93497 u t x y x' y' s P f) = (term695 _93490 _93497 u t x y x' y' s P f).
Proof. exact (@lem3650835 _93490 (term359 _93490 _93497 u t s x y P f) (term597 _93490 _93497 x' y' s P f)). Qed.
Lemma lem3650837 {_93490 _93497 : Type'} (x : type840 _93490 _93497) (y : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term696 _93490 _93497 x y s P f t) = (term595 _93490 _93497 x y s P f t).
Proof. exact (eq_refl (term696 _93490 _93497 x y s P f t)). Qed.
Lemma lem3650838 {_93490 _93497 : Type'} (x : type840 _93490 _93497) (y : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term697 _93490 _93497 x y s P f) = (term597 _93490 _93497 x y s P f).
Proof. exact (fun_ext (fun t : _93490 -> Prop => @lem3650837 _93490 _93497 x y s P f t)). Qed.
Lemma lem3650839 {_93490 : Type'} : (@ex (_93490 -> Prop)) = (@ex (_93490 -> Prop)).
Proof. exact (eq_refl (@ex (_93490 -> Prop))). Qed.
Lemma lem3650840 {_93490 _93497 : Type'} (x : type840 _93490 _93497) (y : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term698 _93490 _93497 x y s P f) = (term598 _93490 _93497 x y s P f).
Proof. exact (MK_COMB (@lem3650839 _93490) (@lem3650838 _93490 _93497 x y s P f)). Qed.
Lemma lem3650841 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term660 _93490 _93497 u t s x y P f) = (term660 _93490 _93497 u t s x y P f).
Proof. exact (eq_refl (term660 _93490 _93497 u t s x y P f)). Qed.
Lemma lem3650842 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term694 _93490 _93497 u t x y x' y' s P f) = (term688 _93490 _93497 u t x y x' y' s P f).
Proof. exact (MK_COMB (@lem3650841 _93490 _93497 u t s x y P f) (@lem3650840 _93490 _93497 x' y' s P f)). Qed.
Lemma lem3650843 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3650844 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term699 _93490 _93497 u t x y x' y' s P f) = (term700 _93490 _93497 u t x y x' y' s P f).
Proof. exact (MK_COMB (@lem3650843) (@lem3650842 _93490 _93497 u t x y x' y' s P f)). Qed.
Lemma lem3650845 {_93490 _93497 : Type'} (x : type840 _93490 _93497) (y : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term696 _93490 _93497 x y s P f t) = (term595 _93490 _93497 x y s P f t).
Proof. exact (eq_refl (term696 _93490 _93497 x y s P f t)). Qed.
Lemma lem3650846 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term660 _93490 _93497 u t s x y P f) = (term660 _93490 _93497 u t s x y P f).
Proof. exact (eq_refl (term660 _93490 _93497 u t s x y P f)). Qed.
Lemma lem3650847 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) : (term701 _93490 _93497 u t x y x' y' s P f t') = (term702 _93490 _93497 u t x y x' y' s P f t').
Proof. exact (MK_COMB (@lem3650846 _93490 _93497 u t s x y P f) (@lem3650845 _93490 _93497 x' y' s P f t')). Qed.
Lemma lem3650848 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term703 _93490 _93497 u t x y x' y' s P f) = (term704 _93490 _93497 u t x y x' y' s P f).
Proof. exact (fun_ext (fun t' : _93490 -> Prop => @lem3650847 _93490 _93497 u t x y x' y' s P f t')). Qed.
Lemma lem3650849 {_93490 : Type'} : (@ex (_93490 -> Prop)) = (@ex (_93490 -> Prop)).
Proof. exact (eq_refl (@ex (_93490 -> Prop))). Qed.
Lemma lem3650850 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term695 _93490 _93497 u t x y x' y' s P f) = (term705 _93490 _93497 u t x y x' y' s P f).
Proof. exact (MK_COMB (@lem3650849 _93490) (@lem3650848 _93490 _93497 u t x y x' y' s P f)). Qed.
Lemma lem3650851 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : ((term694 _93490 _93497 u t x y x' y' s P f) = (term695 _93490 _93497 u t x y x' y' s P f)) = ((term688 _93490 _93497 u t x y x' y' s P f) = (term705 _93490 _93497 u t x y x' y' s P f)).
Proof. exact (MK_COMB (@lem3650844 _93490 _93497 u t x y x' y' s P f) (@lem3650850 _93490 _93497 u t x y x' y' s P f)). Qed.
Lemma lem3650852 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term688 _93490 _93497 u t x y x' y' s P f) = (term705 _93490 _93497 u t x y x' y' s P f).
Proof. exact (EQ_MP (@lem3650851 _93490 _93497 u t x y x' y' s P f) (@lem3650836 _93490 _93497 u t x y x' y' s P f)). Qed.
Lemma lem3650853 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (x' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term690 _93490 _93497 u t x y x' s P f) = (term706 _93490 _93497 u t x y x' s P f).
Proof. exact (fun_ext (fun y' : type840 _93490 _93497 => @lem3650852 _93490 _93497 u t x y x' y' s P f)). Qed.
Lemma lem3650854 {_93490 _93497 : Type'} : (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490)) = (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650855 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (x' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term691 _93490 _93497 u t x y x' s P f) = (term707 _93490 _93497 u t x y x' s P f).
Proof. exact (MK_COMB (@lem3650854 _93490 _93497) (@lem3650853 _93490 _93497 u t x y x' s P f)). Qed.
Lemma lem3650856 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (x' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term676 _93490 _93497 u t x y x' s P f) = (term707 _93490 _93497 u t x y x' s P f).
Proof. exact (TRANS (@lem3650832 _93490 _93497 u t x y x' s P f) (@lem3650855 _93490 _93497 u t x y x' s P f)). Qed.
Lemma lem3650857 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term678 _93490 _93497 u t x y s P f) = (term708 _93490 _93497 u t x y s P f).
Proof. exact (fun_ext (fun x' : type840 _93490 _93497 => @lem3650856 _93490 _93497 u t x y x' s P f)). Qed.
Lemma lem3650858 {_93490 _93497 : Type'} : (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490)) = (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93497 -> Prop) -> (_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650859 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term679 _93490 _93497 u t x y s P f) = (term709 _93490 _93497 u t x y s P f).
Proof. exact (MK_COMB (@lem3650858 _93490 _93497) (@lem3650857 _93490 _93497 u t x y s P f)). Qed.
Lemma lem3650860 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term662 _93490 _93497 u t x y s P f) = (term709 _93490 _93497 u t x y s P f).
Proof. exact (TRANS (@lem3650812 _93490 _93497 u t x y s P f) (@lem3650859 _93490 _93497 u t x y s P f)). Qed.
Lemma lem3650861 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term664 _93490 _93497 u t x s P f) = (term710 _93490 _93497 u t x s P f).
Proof. exact (fun_ext (fun y : type684 _93490 => @lem3650860 _93490 _93497 u t x y s P f)). Qed.
Lemma lem3650862 {_93490 : Type'} : (@ex ((_93490 -> Prop) -> _93490)) = (@ex ((_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650863 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term665 _93490 _93497 u t x s P f) = (term711 _93490 _93497 u t x s P f).
Proof. exact (MK_COMB (@lem3650862 _93490) (@lem3650861 _93490 _93497 u t x s P f)). Qed.
Lemma lem3650864 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term647 _93490 _93497 u t x s P f) = (term711 _93490 _93497 u t x s P f).
Proof. exact (TRANS (@lem3650792 _93490 _93497 u t x s P f) (@lem3650863 _93490 _93497 u t x s P f)). Qed.
Lemma lem3650865 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term649 _93490 _93497 u t s P f) = (term712 _93490 _93497 u t s P f).
Proof. exact (fun_ext (fun x : type684 _93490 => @lem3650864 _93490 _93497 u t x s P f)). Qed.
Lemma lem3650866 {_93490 : Type'} : (@ex ((_93490 -> Prop) -> _93490)) = (@ex ((_93490 -> Prop) -> _93490)).
Proof. exact (eq_refl (@ex ((_93490 -> Prop) -> _93490))). Qed.
Lemma lem3650867 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term650 _93490 _93497 u t s P f) = (term713 _93490 _93497 u t s P f).
Proof. exact (MK_COMB (@lem3650866 _93490) (@lem3650865 _93490 _93497 u t s P f)). Qed.
Lemma lem3650868 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term632 _93490 _93497 u t s P f) = (term713 _93490 _93497 u t s P f).
Proof. exact (TRANS (@lem3650766 _93490 _93497 u t s P f) (@lem3650867 _93490 _93497 u t s P f)). Qed.
Lemma lem3650869 {_93490 _93497 : Type'} (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term634 _93490 _93497 t s P f) = (term714 _93490 _93497 t s P f).
Proof. exact (fun_ext (fun u : _93490 -> Prop => @lem3650868 _93490 _93497 u t s P f)). Qed.
Lemma lem3650870 {_93490 : Type'} : (@ex (_93490 -> Prop)) = (@ex (_93490 -> Prop)).
Proof. exact (eq_refl (@ex (_93490 -> Prop))). Qed.
Lemma lem3650871 {_93490 _93497 : Type'} (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term635 _93490 _93497 t s P f) = (term715 _93490 _93497 t s P f).
Proof. exact (MK_COMB (@lem3650870 _93490) (@lem3650869 _93490 _93497 t s P f)). Qed.
Lemma lem3650872 {_93490 _93497 : Type'} (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term617 _93490 _93497 t s P f) = (term715 _93490 _93497 t s P f).
Proof. exact (TRANS (@lem3650740 _93490 _93497 t s P f) (@lem3650871 _93490 _93497 t s P f)). Qed.
Lemma lem3650873 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term619 _93490 _93497 s P f) = (term716 _93490 _93497 s P f).
Proof. exact (fun_ext (fun t : _93497 -> Prop => @lem3650872 _93490 _93497 t s P f)). Qed.
Lemma lem3650874 {_93497 : Type'} : (@ex (_93497 -> Prop)) = (@ex (_93497 -> Prop)).
Proof. exact (eq_refl (@ex (_93497 -> Prop))). Qed.
Lemma lem3650875 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term620 _93490 _93497 s P f) = (term717 _93490 _93497 s P f).
Proof. exact (MK_COMB (@lem3650874 _93497) (@lem3650873 _93490 _93497 s P f)). Qed.
Lemma lem3650876 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term603 _93490 _93497 s P f) = (term717 _93490 _93497 s P f).
Proof. exact (TRANS (@lem3650714 _93490 _93497 s P f) (@lem3650875 _93490 _93497 s P f)). Qed.
Lemma lem3650878 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term165 _93490 _93497 s P f) = (term717 _93490 _93497 s P f).
Proof. exact (TRANS (@lem3650688 _93490 _93497 s P f) (@lem3650876 _93490 _93497 s P f)). Qed.
Lemma lem3650879 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term60 _93490 _93497 s P f) = (term717 _93490 _93497 s P f).
Proof. exact (TRANS (@lem3649533 _93490 _93497 s P f) (@lem3650878 _93490 _93497 s P f)). Qed.
Lemma lem3650880 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term60 _93490 _93497 s P f) : term717 _93490 _93497 s P f.
Proof. exact (EQ_MP (@lem3650879 _93490 _93497 s P f) (@lem3649285 _93490 _93497 s P f h1)). Qed.
Lemma lem3650881 {_93490 _93497 : Type'} (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term715 _93490 _93497 t s P f) : term715 _93490 _93497 t s P f.
Proof. exact (h1). Qed.
Lemma lem3650882 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term713 _93490 _93497 u t s P f) : term713 _93490 _93497 u t s P f.
Proof. exact (h1). Qed.
Lemma lem3650883 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term711 _93490 _93497 u t x s P f) : term711 _93490 _93497 u t x s P f.
Proof. exact (h1). Qed.
Lemma lem3650884 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term709 _93490 _93497 u t x y s P f) : term709 _93490 _93497 u t x y s P f.
Proof. exact (h1). Qed.
Lemma lem3650885 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (x' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term707 _93490 _93497 u t x y x' s P f) : term707 _93490 _93497 u t x y x' s P f.
Proof. exact (h1). Qed.
Lemma lem3650886 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term705 _93490 _93497 u t x y x' y' s P f) : term705 _93490 _93497 u t x y x' y' s P f.
Proof. exact (h1). Qed.
Lemma lem3650887 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term702 _93490 _93497 u t x y x' y' s P f t') : term702 _93490 _93497 u t x y x' y' s P f t'.
Proof. exact (h1). Qed.
Lemma lem3650894 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) : (term45 _93490 _93497 P f t') = (term45 _93490 _93497 P f t').
Proof. exact (eq_refl (term45 _93490 _93497 P f t')). Qed.
Lemma lem3650899 {_93490 : Type'} (x : _93490) (y : _93490) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem3650900 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3650901 {_93497 : Type'} : (@eq _93497) = (@eq _93497).
Proof. exact (eq_refl (@eq _93497)). Qed.
Lemma lem3650906 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3650908 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : _93490) : (f x) = (@I (_93490 -> _93497) f x).
Proof. exact (@lem3650906 _93490 _93497 f x). Qed.
Lemma lem3650913 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3650914 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : _93490) : (f x) = (@I (_93490 -> _93497) f x).
Proof. exact (@lem3650913 _93490 _93497 f x). Qed.
Lemma lem3650916 {_93490 _93497 : Type'} (f : _93490 -> _93497) (y : _93490) : (f y) = (@I (_93490 -> _93497) f y).
Proof. exact (@lem3650914 _93490 _93497 f y). Qed.
Lemma lem3650917 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : _93490) : (term718 _93490 _93497 f x) = (term719 _93490 _93497 f x).
Proof. exact (MK_COMB (@lem3650901 _93497) (@lem3650908 _93490 _93497 f x)). Qed.
Lemma lem3650918 {_93490 _93497 : Type'} (x : _93490) (f : _93490 -> _93497) (y : _93490) : ((f x) = (f y)) = ((@I (_93490 -> _93497) f x) = (@I (_93490 -> _93497) f y)).
Proof. exact (MK_COMB (@lem3650917 _93490 _93497 f x) (@lem3650916 _93490 _93497 f y)). Qed.
Lemma lem3650919 {_93490 _93497 : Type'} (x : _93490) (f : _93490 -> _93497) (y : _93490) : (term720 _93490 _93497 x f y) = (term721 _93490 _93497 x f y).
Proof. exact (MK_COMB (@lem3650900) (@lem3650918 _93490 _93497 x f y)). Qed.
Lemma lem3650920 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3650921 {_93490 _93497 : Type'} (x : _93490) (f : _93490 -> _93497) (y : _93490) : (term722 _93490 _93497 x f y) = (term723 _93490 _93497 x f y).
Proof. exact (MK_COMB (@lem3650920) (@lem3650919 _93490 _93497 x f y)). Qed.
Lemma lem3650922 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term724 _93490 _93497 f x y) = (term725 _93490 _93497 f x y).
Proof. exact (MK_COMB (@lem3650921 _93490 _93497 x f y) (@lem3650899 _93490 x y)). Qed.
Lemma lem3650929 {_93490 : Type'} (x : _93490) (y : _93490) : (term726 _93490 x y) = (term726 _93490 x y).
Proof. exact (eq_refl (term726 _93490 x y)). Qed.
Lemma lem3650930 {_93497 : Type'} : (@eq _93497) = (@eq _93497).
Proof. exact (eq_refl (@eq _93497)). Qed.
Lemma lem3650935 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3650937 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : _93490) : (f x) = (@I (_93490 -> _93497) f x).
Proof. exact (@lem3650935 _93490 _93497 f x). Qed.
Lemma lem3650942 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3650943 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : _93490) : (f x) = (@I (_93490 -> _93497) f x).
Proof. exact (@lem3650942 _93490 _93497 f x). Qed.
Lemma lem3650945 {_93490 _93497 : Type'} (f : _93490 -> _93497) (y : _93490) : (f y) = (@I (_93490 -> _93497) f y).
Proof. exact (@lem3650943 _93490 _93497 f y). Qed.
Lemma lem3650946 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : _93490) : (term718 _93490 _93497 f x) = (term719 _93490 _93497 f x).
Proof. exact (MK_COMB (@lem3650930 _93497) (@lem3650937 _93490 _93497 f x)). Qed.
Lemma lem3650947 {_93490 _93497 : Type'} (x : _93490) (f : _93490 -> _93497) (y : _93490) : ((f x) = (f y)) = ((@I (_93490 -> _93497) f x) = (@I (_93490 -> _93497) f y)).
Proof. exact (MK_COMB (@lem3650946 _93490 _93497 f x) (@lem3650945 _93490 _93497 f y)). Qed.
Lemma lem3650948 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3650949 {_93490 _93497 : Type'} (x : _93490) (f : _93490 -> _93497) (y : _93490) : (term727 _93490 _93497 x f y) = (term728 _93490 _93497 x f y).
Proof. exact (MK_COMB (@lem3650948) (@lem3650947 _93490 _93497 x f y)). Qed.
Lemma lem3650950 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term729 _93490 _93497 f x y) = (term730 _93490 _93497 f x y).
Proof. exact (MK_COMB (@lem3650949 _93490 _93497 x f y) (@lem3650929 _93490 x y)). Qed.
Lemma lem3650951 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3650952 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term731 _93490 _93497 f x y) = (term732 _93490 _93497 f x y).
Proof. exact (MK_COMB (@lem3650951) (@lem3650950 _93490 _93497 f x y)). Qed.
Lemma lem3650953 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term65 _93490 _93497 f x y) = (term733 _93490 _93497 f x y).
Proof. exact (MK_COMB (@lem3650952 _93490 _93497 f x y) (@lem3650922 _93490 _93497 f x y)). Qed.
Lemma lem3650972 {_93490 : Type'} (x : _93490) (y : _93490) (t' : _93490 -> Prop) : (term72 _93490 x y t') = (term72 _93490 x y t').
Proof. exact (eq_refl (term72 _93490 x y t')). Qed.
Lemma lem3650973 {_93490 _93497 : Type'} (t' : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term74 _93490 _93497 t' f x y) = (term734 _93490 _93497 t' f x y).
Proof. exact (MK_COMB (@lem3650972 _93490 x y t') (@lem3650953 _93490 _93497 f x y)). Qed.
Lemma lem3650974 {_93490 _93497 : Type'} (t' : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term84 _93490 _93497 t' f x) = (term735 _93490 _93497 t' f x).
Proof. exact (fun_ext (fun y : _93490 => @lem3650973 _93490 _93497 t' f x y)). Qed.
Lemma lem3650975 {_93490 : Type'} : (@all _93490) = (@all _93490).
Proof. exact (eq_refl (@all _93490)). Qed.
Lemma lem3650976 {_93490 _93497 : Type'} (t' : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term85 _93490 _93497 t' f x) = (term736 _93490 _93497 t' f x).
Proof. exact (MK_COMB (@lem3650975 _93490) (@lem3650974 _93490 _93497 t' f x)). Qed.
Lemma lem3650977 {_93490 _93497 : Type'} (t' : _93490 -> Prop) (f : _93490 -> _93497) : (term93 _93490 _93497 t' f) = (term737 _93490 _93497 t' f).
Proof. exact (fun_ext (fun x : _93490 => @lem3650976 _93490 _93497 t' f x)). Qed.
Lemma lem3650978 {_93490 : Type'} : (@all _93490) = (@all _93490).
Proof. exact (eq_refl (@all _93490)). Qed.
Lemma lem3650979 {_93490 _93497 : Type'} (t' : _93490 -> Prop) (f : _93490 -> _93497) : (term94 _93490 _93497 t' f) = (term738 _93490 _93497 t' f).
Proof. exact (MK_COMB (@lem3650978 _93490) (@lem3650977 _93490 _93497 t' f)). Qed.
Lemma lem3650980 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3650981 {_93490 _93497 : Type'} (t' : _93490 -> Prop) (f : _93490 -> _93497) : (term101 _93490 _93497 t' f) = (term739 _93490 _93497 t' f).
Proof. exact (MK_COMB (@lem3650980) (@lem3650979 _93490 _93497 t' f)). Qed.
Lemma lem3650982 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) : (term140 _93490 _93497 P f t') = (term740 _93490 _93497 P f t').
Proof. exact (MK_COMB (@lem3650981 _93490 _93497 t' f) (@lem3650894 _93490 _93497 P f t')). Qed.
Lemma lem3650989 {_93490 : Type'} (t' : _93490 -> Prop) (s : _93490 -> Prop) : (term53 _93490 t' s) = (term53 _93490 t' s).
Proof. exact (eq_refl (term53 _93490 t' s)). Qed.
Lemma lem3650990 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) : (term144 _93490 _93497 s P f t') = (term741 _93490 _93497 s P f t').
Proof. exact (MK_COMB (@lem3650989 _93490 t' s) (@lem3650982 _93490 _93497 P f t')). Qed.
Lemma lem3650995 {_93497 : Type'} (P : type686 _93497) (t : _93497 -> Prop) : (term119 _93497 P t) = (term119 _93497 P t).
Proof. exact (eq_refl (term119 _93497 P t)). Qed.
Lemma lem3651006 {_93490 _93497 : Type'} (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term95 _93490 _93497 t f u) = (term95 _93490 _93497 t f u).
Proof. exact (eq_refl (term95 _93490 _93497 t f u)). Qed.
Lemma lem3651021 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (u : _93490 -> Prop) : (term742 _93490 _93497 x' y' t u) = (term742 _93490 _93497 x' y' t u).
Proof. exact (eq_refl (term742 _93490 _93497 x' y' t u)). Qed.
Lemma lem3651022 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3651023 {_93497 : Type'} : (@eq _93497) = (@eq _93497).
Proof. exact (eq_refl (@eq _93497)). Qed.
Lemma lem3651032 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3651033 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : _93490) : (f x) = (@I (_93490 -> _93497) f x).
Proof. exact (@lem3651032 _93490 _93497 f x). Qed.
Lemma lem3651035 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x' : type840 _93490 _93497) (t : _93497 -> Prop) (u : _93490 -> Prop) : (term743 _93490 _93497 f x' t u) = (term744 _93490 _93497 f x' t u).
Proof. exact (@lem3651033 _93490 _93497 f (x' t u)). Qed.
Lemma lem3651044 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3651045 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : _93490) : (f x) = (@I (_93490 -> _93497) f x).
Proof. exact (@lem3651044 _93490 _93497 f x). Qed.
Lemma lem3651047 {_93490 _93497 : Type'} (f : _93490 -> _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (u : _93490 -> Prop) : (term743 _93490 _93497 f y' t u) = (term744 _93490 _93497 f y' t u).
Proof. exact (@lem3651045 _93490 _93497 f (y' t u)). Qed.
Lemma lem3651048 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x' : type840 _93490 _93497) (t : _93497 -> Prop) (u : _93490 -> Prop) : (term745 _93490 _93497 f x' t u) = (term746 _93490 _93497 f x' t u).
Proof. exact (MK_COMB (@lem3651023 _93497) (@lem3651035 _93490 _93497 f x' t u)). Qed.
Lemma lem3651049 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (f : _93490 -> _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (u : _93490 -> Prop) : ((term743 _93490 _93497 f x' t u) = (term743 _93490 _93497 f y' t u)) = ((term744 _93490 _93497 f x' t u) = (term744 _93490 _93497 f y' t u)).
Proof. exact (MK_COMB (@lem3651048 _93490 _93497 f x' t u) (@lem3651047 _93490 _93497 f y' t u)). Qed.
Lemma lem3651050 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (f : _93490 -> _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (u : _93490 -> Prop) : (term747 _93490 _93497 x' f y' t u) = (term748 _93490 _93497 x' f y' t u).
Proof. exact (MK_COMB (@lem3651022) (@lem3651049 _93490 _93497 x' f y' t u)). Qed.
Lemma lem3651051 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3651052 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (f : _93490 -> _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (u : _93490 -> Prop) : (term749 _93490 _93497 x' f y' t u) = (term750 _93490 _93497 x' f y' t u).
Proof. exact (MK_COMB (@lem3651051) (@lem3651050 _93490 _93497 x' f y' t u)). Qed.
Lemma lem3651053 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (u : _93490 -> Prop) : (term751 _93490 _93497 f x' y' t u) = (term752 _93490 _93497 f x' y' t u).
Proof. exact (MK_COMB (@lem3651052 _93490 _93497 x' f y' t u) (@lem3651021 _93490 _93497 x' y' t u)). Qed.
Lemma lem3651066 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (u : _93490 -> Prop) : ((x' t u) = (y' t u)) = ((x' t u) = (y' t u)).
Proof. exact (eq_refl ((x' t u) = (y' t u))). Qed.
Lemma lem3651067 {_93497 : Type'} : (@eq _93497) = (@eq _93497).
Proof. exact (eq_refl (@eq _93497)). Qed.
Lemma lem3651076 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3651077 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : _93490) : (f x) = (@I (_93490 -> _93497) f x).
Proof. exact (@lem3651076 _93490 _93497 f x). Qed.
Lemma lem3651079 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x' : type840 _93490 _93497) (t : _93497 -> Prop) (u : _93490 -> Prop) : (term743 _93490 _93497 f x' t u) = (term744 _93490 _93497 f x' t u).
Proof. exact (@lem3651077 _93490 _93497 f (x' t u)). Qed.
Lemma lem3651088 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3651089 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : _93490) : (f x) = (@I (_93490 -> _93497) f x).
Proof. exact (@lem3651088 _93490 _93497 f x). Qed.
Lemma lem3651091 {_93490 _93497 : Type'} (f : _93490 -> _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (u : _93490 -> Prop) : (term743 _93490 _93497 f y' t u) = (term744 _93490 _93497 f y' t u).
Proof. exact (@lem3651089 _93490 _93497 f (y' t u)). Qed.
Lemma lem3651092 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x' : type840 _93490 _93497) (t : _93497 -> Prop) (u : _93490 -> Prop) : (term745 _93490 _93497 f x' t u) = (term746 _93490 _93497 f x' t u).
Proof. exact (MK_COMB (@lem3651067 _93497) (@lem3651079 _93490 _93497 f x' t u)). Qed.
Lemma lem3651093 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (f : _93490 -> _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (u : _93490 -> Prop) : ((term743 _93490 _93497 f x' t u) = (term743 _93490 _93497 f y' t u)) = ((term744 _93490 _93497 f x' t u) = (term744 _93490 _93497 f y' t u)).
Proof. exact (MK_COMB (@lem3651092 _93490 _93497 f x' t u) (@lem3651091 _93490 _93497 f y' t u)). Qed.
Lemma lem3651094 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3651095 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (f : _93490 -> _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (u : _93490 -> Prop) : (term753 _93490 _93497 x' f y' t u) = (term754 _93490 _93497 x' f y' t u).
Proof. exact (MK_COMB (@lem3651094) (@lem3651093 _93490 _93497 x' f y' t u)). Qed.
Lemma lem3651096 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (u : _93490 -> Prop) : (term755 _93490 _93497 f x' y' t u) = (term756 _93490 _93497 f x' y' t u).
Proof. exact (MK_COMB (@lem3651095 _93490 _93497 x' f y' t u) (@lem3651066 _93490 _93497 x' y' t u)). Qed.
Lemma lem3651097 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3651098 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (u : _93490 -> Prop) : (term757 _93490 _93497 f x' y' t u) = (term758 _93490 _93497 f x' y' t u).
Proof. exact (MK_COMB (@lem3651097) (@lem3651096 _93490 _93497 f x' y' t u)). Qed.
Lemma lem3651099 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (u : _93490 -> Prop) : (term759 _93490 _93497 f x' y' t u) = (term760 _93490 _93497 f x' y' t u).
Proof. exact (MK_COMB (@lem3651098 _93490 _93497 f x' y' t u) (@lem3651053 _93490 _93497 f x' y' t u)). Qed.
Lemma lem3651122 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (u : _93490 -> Prop) : (term761 _93490 _93497 x' y' t u) = (term761 _93490 _93497 x' y' t u).
Proof. exact (eq_refl (term761 _93490 _93497 x' y' t u)). Qed.
Lemma lem3651123 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (u : _93490 -> Prop) : (term762 _93490 _93497 f x' y' t u) = (term763 _93490 _93497 f x' y' t u).
Proof. exact (MK_COMB (@lem3651122 _93490 _93497 x' y' t u) (@lem3651099 _93490 _93497 f x' y' t u)). Qed.
Lemma lem3651124 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3651125 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (u : _93490 -> Prop) : (term764 _93490 _93497 f x' y' t u) = (term765 _93490 _93497 f x' y' t u).
Proof. exact (MK_COMB (@lem3651124) (@lem3651123 _93490 _93497 f x' y' t u)). Qed.
Lemma lem3651126 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term766 _93490 _93497 x' y' t f u) = (term767 _93490 _93497 x' y' t f u).
Proof. exact (MK_COMB (@lem3651125 _93490 _93497 f x' y' t u) (@lem3651006 _93490 _93497 t f u)). Qed.
Lemma lem3651135 {_93490 : Type'} (u : _93490 -> Prop) (s : _93490 -> Prop) : (term103 _93490 u s) = (term103 _93490 u s).
Proof. exact (eq_refl (term103 _93490 u s)). Qed.
Lemma lem3651136 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term768 _93490 _93497 s x' y' t f u) = (term769 _93490 _93497 s x' y' t f u).
Proof. exact (MK_COMB (@lem3651135 _93490 u s) (@lem3651126 _93490 _93497 x' y' t f u)). Qed.
Lemma lem3651137 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term770 _93490 _93497 s x' y' t f) = (term771 _93490 _93497 s x' y' t f).
Proof. exact (fun_ext (fun u : _93490 -> Prop => @lem3651136 _93490 _93497 s x' y' t f u)). Qed.
Lemma lem3651138 {_93490 : Type'} : (@all (_93490 -> Prop)) = (@all (_93490 -> Prop)).
Proof. exact (eq_refl (@all (_93490 -> Prop))). Qed.
Lemma lem3651139 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term772 _93490 _93497 s x' y' t f) = (term773 _93490 _93497 s x' y' t f).
Proof. exact (MK_COMB (@lem3651138 _93490) (@lem3651137 _93490 _93497 s x' y' t f)). Qed.
Lemma lem3651140 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3651141 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term774 _93490 _93497 s x' y' t f) = (term775 _93490 _93497 s x' y' t f).
Proof. exact (MK_COMB (@lem3651140) (@lem3651139 _93490 _93497 s x' y' t f)). Qed.
Lemma lem3651142 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term541 _93490 _93497 s x' y' f P t) = (term776 _93490 _93497 s x' y' f P t).
Proof. exact (MK_COMB (@lem3651141 _93490 _93497 s x' y' t f) (@lem3650995 _93497 P t)). Qed.
Lemma lem3651143 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) : (term543 _93490 _93497 s x' y' f P) = (term777 _93490 _93497 s x' y' f P).
Proof. exact (fun_ext (fun t : _93497 -> Prop => @lem3651142 _93490 _93497 s x' y' f P t)). Qed.
Lemma lem3651144 {_93497 : Type'} : (@all (_93497 -> Prop)) = (@all (_93497 -> Prop)).
Proof. exact (eq_refl (@all (_93497 -> Prop))). Qed.
Lemma lem3651145 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) : (term545 _93490 _93497 s x' y' f P) = (term778 _93490 _93497 s x' y' f P).
Proof. exact (MK_COMB (@lem3651144 _93497) (@lem3651143 _93490 _93497 s x' y' f P)). Qed.
Lemma lem3651146 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3651147 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) : (term579 _93490 _93497 s x' y' f P) = (term779 _93490 _93497 s x' y' f P).
Proof. exact (MK_COMB (@lem3651146) (@lem3651145 _93490 _93497 s x' y' f P)). Qed.
Lemma lem3651148 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) : (term595 _93490 _93497 x' y' s P f t') = (term780 _93490 _93497 x' y' s P f t').
Proof. exact (MK_COMB (@lem3651147 _93490 _93497 s x' y' f P) (@lem3650990 _93490 _93497 s P f t')). Qed.
Lemma lem3651157 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term136 _93490 _93497 P f t) = (term136 _93490 _93497 P f t).
Proof. exact (eq_refl (term136 _93490 _93497 P f t)). Qed.
Lemma lem3651168 {_93490 : Type'} (x : type684 _93490) (y : type684 _93490) (t : _93490 -> Prop) : (term781 _93490 x y t) = (term781 _93490 x y t).
Proof. exact (eq_refl (term781 _93490 x y t)). Qed.
Lemma lem3651169 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3651170 {_93497 : Type'} : (@eq _93497) = (@eq _93497).
Proof. exact (eq_refl (@eq _93497)). Qed.
Lemma lem3651177 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3651178 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : _93490) : (f x) = (@I (_93490 -> _93497) f x).
Proof. exact (@lem3651177 _93490 _93497 f x). Qed.
Lemma lem3651180 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : type684 _93490) (t : _93490 -> Prop) : (term782 _93490 _93497 f x t) = (term783 _93490 _93497 f x t).
Proof. exact (@lem3651178 _93490 _93497 f (x t)). Qed.
Lemma lem3651187 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3651188 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : _93490) : (f x) = (@I (_93490 -> _93497) f x).
Proof. exact (@lem3651187 _93490 _93497 f x). Qed.
Lemma lem3651190 {_93490 _93497 : Type'} (f : _93490 -> _93497) (y : type684 _93490) (t : _93490 -> Prop) : (term782 _93490 _93497 f y t) = (term783 _93490 _93497 f y t).
Proof. exact (@lem3651188 _93490 _93497 f (y t)). Qed.
Lemma lem3651191 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : type684 _93490) (t : _93490 -> Prop) : (term784 _93490 _93497 f x t) = (term785 _93490 _93497 f x t).
Proof. exact (MK_COMB (@lem3651170 _93497) (@lem3651180 _93490 _93497 f x t)). Qed.
Lemma lem3651192 {_93490 _93497 : Type'} (x : type684 _93490) (f : _93490 -> _93497) (y : type684 _93490) (t : _93490 -> Prop) : ((term782 _93490 _93497 f x t) = (term782 _93490 _93497 f y t)) = ((term783 _93490 _93497 f x t) = (term783 _93490 _93497 f y t)).
Proof. exact (MK_COMB (@lem3651191 _93490 _93497 f x t) (@lem3651190 _93490 _93497 f y t)). Qed.
Lemma lem3651193 {_93490 _93497 : Type'} (x : type684 _93490) (f : _93490 -> _93497) (y : type684 _93490) (t : _93490 -> Prop) : (term786 _93490 _93497 x f y t) = (term787 _93490 _93497 x f y t).
Proof. exact (MK_COMB (@lem3651169) (@lem3651192 _93490 _93497 x f y t)). Qed.
Lemma lem3651194 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3651195 {_93490 _93497 : Type'} (x : type684 _93490) (f : _93490 -> _93497) (y : type684 _93490) (t : _93490 -> Prop) : (term788 _93490 _93497 x f y t) = (term789 _93490 _93497 x f y t).
Proof. exact (MK_COMB (@lem3651194) (@lem3651193 _93490 _93497 x f y t)). Qed.
Lemma lem3651196 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : type684 _93490) (y : type684 _93490) (t : _93490 -> Prop) : (term790 _93490 _93497 f x y t) = (term791 _93490 _93497 f x y t).
Proof. exact (MK_COMB (@lem3651195 _93490 _93497 x f y t) (@lem3651168 _93490 x y t)). Qed.
Lemma lem3651205 {_93490 : Type'} (x : type684 _93490) (y : type684 _93490) (t : _93490 -> Prop) : ((x t) = (y t)) = ((x t) = (y t)).
Proof. exact (eq_refl ((x t) = (y t))). Qed.
Lemma lem3651206 {_93497 : Type'} : (@eq _93497) = (@eq _93497).
Proof. exact (eq_refl (@eq _93497)). Qed.
Lemma lem3651213 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3651214 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : _93490) : (f x) = (@I (_93490 -> _93497) f x).
Proof. exact (@lem3651213 _93490 _93497 f x). Qed.
Lemma lem3651216 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : type684 _93490) (t : _93490 -> Prop) : (term782 _93490 _93497 f x t) = (term783 _93490 _93497 f x t).
Proof. exact (@lem3651214 _93490 _93497 f (x t)). Qed.
Lemma lem3651223 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3651224 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : _93490) : (f x) = (@I (_93490 -> _93497) f x).
Proof. exact (@lem3651223 _93490 _93497 f x). Qed.
Lemma lem3651226 {_93490 _93497 : Type'} (f : _93490 -> _93497) (y : type684 _93490) (t : _93490 -> Prop) : (term782 _93490 _93497 f y t) = (term783 _93490 _93497 f y t).
Proof. exact (@lem3651224 _93490 _93497 f (y t)). Qed.
Lemma lem3651227 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : type684 _93490) (t : _93490 -> Prop) : (term784 _93490 _93497 f x t) = (term785 _93490 _93497 f x t).
Proof. exact (MK_COMB (@lem3651206 _93497) (@lem3651216 _93490 _93497 f x t)). Qed.
Lemma lem3651228 {_93490 _93497 : Type'} (x : type684 _93490) (f : _93490 -> _93497) (y : type684 _93490) (t : _93490 -> Prop) : ((term782 _93490 _93497 f x t) = (term782 _93490 _93497 f y t)) = ((term783 _93490 _93497 f x t) = (term783 _93490 _93497 f y t)).
Proof. exact (MK_COMB (@lem3651227 _93490 _93497 f x t) (@lem3651226 _93490 _93497 f y t)). Qed.
Lemma lem3651229 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3651230 {_93490 _93497 : Type'} (x : type684 _93490) (f : _93490 -> _93497) (y : type684 _93490) (t : _93490 -> Prop) : (term792 _93490 _93497 x f y t) = (term793 _93490 _93497 x f y t).
Proof. exact (MK_COMB (@lem3651229) (@lem3651228 _93490 _93497 x f y t)). Qed.
Lemma lem3651231 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : type684 _93490) (y : type684 _93490) (t : _93490 -> Prop) : (term794 _93490 _93497 f x y t) = (term795 _93490 _93497 f x y t).
Proof. exact (MK_COMB (@lem3651230 _93490 _93497 x f y t) (@lem3651205 _93490 x y t)). Qed.
Lemma lem3651232 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3651233 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : type684 _93490) (y : type684 _93490) (t : _93490 -> Prop) : (term796 _93490 _93497 f x y t) = (term797 _93490 _93497 f x y t).
Proof. exact (MK_COMB (@lem3651232) (@lem3651231 _93490 _93497 f x y t)). Qed.
Lemma lem3651234 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : type684 _93490) (y : type684 _93490) (t : _93490 -> Prop) : (term798 _93490 _93497 f x y t) = (term799 _93490 _93497 f x y t).
Proof. exact (MK_COMB (@lem3651233 _93490 _93497 f x y t) (@lem3651196 _93490 _93497 f x y t)). Qed.
Lemma lem3651253 {_93490 : Type'} (x : type684 _93490) (y : type684 _93490) (t : _93490 -> Prop) : (term800 _93490 x y t) = (term800 _93490 x y t).
Proof. exact (eq_refl (term800 _93490 x y t)). Qed.
Lemma lem3651254 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : type684 _93490) (y : type684 _93490) (t : _93490 -> Prop) : (term801 _93490 _93497 f x y t) = (term802 _93490 _93497 f x y t).
Proof. exact (MK_COMB (@lem3651253 _93490 x y t) (@lem3651234 _93490 _93497 f x y t)). Qed.
Lemma lem3651255 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3651256 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : type684 _93490) (y : type684 _93490) (t : _93490 -> Prop) : (term803 _93490 _93497 f x y t) = (term804 _93490 _93497 f x y t).
Proof. exact (MK_COMB (@lem3651255) (@lem3651254 _93490 _93497 f x y t)). Qed.
Lemma lem3651257 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term805 _93490 _93497 x y P f t) = (term806 _93490 _93497 x y P f t).
Proof. exact (MK_COMB (@lem3651256 _93490 _93497 f x y t) (@lem3651157 _93490 _93497 P f t)). Qed.
Lemma lem3651266 {_93490 : Type'} (t : _93490 -> Prop) (s : _93490 -> Prop) : (term103 _93490 t s) = (term103 _93490 t s).
Proof. exact (eq_refl (term103 _93490 t s)). Qed.
Lemma lem3651267 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term294 _93490 _93497 s x y P f t) = (term807 _93490 _93497 s x y P f t).
Proof. exact (MK_COMB (@lem3651266 _93490 t s) (@lem3651257 _93490 _93497 x y P f t)). Qed.
Lemma lem3651268 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term296 _93490 _93497 s x y P f) = (term808 _93490 _93497 s x y P f).
Proof. exact (fun_ext (fun t : _93490 -> Prop => @lem3651267 _93490 _93497 s x y P f t)). Qed.
Lemma lem3651269 {_93490 : Type'} : (@all (_93490 -> Prop)) = (@all (_93490 -> Prop)).
Proof. exact (eq_refl (@all (_93490 -> Prop))). Qed.
Lemma lem3651270 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term298 _93490 _93497 s x y P f) = (term809 _93490 _93497 s x y P f).
Proof. exact (MK_COMB (@lem3651269 _93490) (@lem3651268 _93490 _93497 s x y P f)). Qed.
Lemma lem3651273 {_93497 : Type'} (P : type686 _93497) (t : _93497 -> Prop) : (P t) = (P t).
Proof. exact (eq_refl (P t)). Qed.
Lemma lem3651282 {_93490 _93497 : Type'} (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (t = (@IMAGE _93490 _93497 f u)) = (t = (@IMAGE _93490 _93497 f u)).
Proof. exact (eq_refl (t = (@IMAGE _93490 _93497 f u))). Qed.
Lemma lem3651287 {_93490 : Type'} (x : _93490) (y : _93490) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem3651288 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3651289 {_93497 : Type'} : (@eq _93497) = (@eq _93497).
Proof. exact (eq_refl (@eq _93497)). Qed.
Lemma lem3651294 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3651296 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : _93490) : (f x) = (@I (_93490 -> _93497) f x).
Proof. exact (@lem3651294 _93490 _93497 f x). Qed.
Lemma lem3651301 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3651302 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : _93490) : (f x) = (@I (_93490 -> _93497) f x).
Proof. exact (@lem3651301 _93490 _93497 f x). Qed.
Lemma lem3651304 {_93490 _93497 : Type'} (f : _93490 -> _93497) (y : _93490) : (f y) = (@I (_93490 -> _93497) f y).
Proof. exact (@lem3651302 _93490 _93497 f y). Qed.
Lemma lem3651305 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : _93490) : (term718 _93490 _93497 f x) = (term719 _93490 _93497 f x).
Proof. exact (MK_COMB (@lem3651289 _93497) (@lem3651296 _93490 _93497 f x)). Qed.
Lemma lem3651306 {_93490 _93497 : Type'} (x : _93490) (f : _93490 -> _93497) (y : _93490) : ((f x) = (f y)) = ((@I (_93490 -> _93497) f x) = (@I (_93490 -> _93497) f y)).
Proof. exact (MK_COMB (@lem3651305 _93490 _93497 f x) (@lem3651304 _93490 _93497 f y)). Qed.
Lemma lem3651307 {_93490 _93497 : Type'} (x : _93490) (f : _93490 -> _93497) (y : _93490) : (term720 _93490 _93497 x f y) = (term721 _93490 _93497 x f y).
Proof. exact (MK_COMB (@lem3651288) (@lem3651306 _93490 _93497 x f y)). Qed.
Lemma lem3651308 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3651309 {_93490 _93497 : Type'} (x : _93490) (f : _93490 -> _93497) (y : _93490) : (term722 _93490 _93497 x f y) = (term723 _93490 _93497 x f y).
Proof. exact (MK_COMB (@lem3651308) (@lem3651307 _93490 _93497 x f y)). Qed.
Lemma lem3651310 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term724 _93490 _93497 f x y) = (term725 _93490 _93497 f x y).
Proof. exact (MK_COMB (@lem3651309 _93490 _93497 x f y) (@lem3651287 _93490 x y)). Qed.
Lemma lem3651317 {_93490 : Type'} (x : _93490) (y : _93490) : (term726 _93490 x y) = (term726 _93490 x y).
Proof. exact (eq_refl (term726 _93490 x y)). Qed.
Lemma lem3651318 {_93497 : Type'} : (@eq _93497) = (@eq _93497).
Proof. exact (eq_refl (@eq _93497)). Qed.
Lemma lem3651323 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3651325 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : _93490) : (f x) = (@I (_93490 -> _93497) f x).
Proof. exact (@lem3651323 _93490 _93497 f x). Qed.
Lemma lem3651330 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3651331 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : _93490) : (f x) = (@I (_93490 -> _93497) f x).
Proof. exact (@lem3651330 _93490 _93497 f x). Qed.
Lemma lem3651333 {_93490 _93497 : Type'} (f : _93490 -> _93497) (y : _93490) : (f y) = (@I (_93490 -> _93497) f y).
Proof. exact (@lem3651331 _93490 _93497 f y). Qed.
Lemma lem3651334 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : _93490) : (term718 _93490 _93497 f x) = (term719 _93490 _93497 f x).
Proof. exact (MK_COMB (@lem3651318 _93497) (@lem3651325 _93490 _93497 f x)). Qed.
Lemma lem3651335 {_93490 _93497 : Type'} (x : _93490) (f : _93490 -> _93497) (y : _93490) : ((f x) = (f y)) = ((@I (_93490 -> _93497) f x) = (@I (_93490 -> _93497) f y)).
Proof. exact (MK_COMB (@lem3651334 _93490 _93497 f x) (@lem3651333 _93490 _93497 f y)). Qed.
Lemma lem3651336 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3651337 {_93490 _93497 : Type'} (x : _93490) (f : _93490 -> _93497) (y : _93490) : (term727 _93490 _93497 x f y) = (term728 _93490 _93497 x f y).
Proof. exact (MK_COMB (@lem3651336) (@lem3651335 _93490 _93497 x f y)). Qed.
Lemma lem3651338 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term729 _93490 _93497 f x y) = (term730 _93490 _93497 f x y).
Proof. exact (MK_COMB (@lem3651337 _93490 _93497 x f y) (@lem3651317 _93490 x y)). Qed.
Lemma lem3651339 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3651340 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term731 _93490 _93497 f x y) = (term732 _93490 _93497 f x y).
Proof. exact (MK_COMB (@lem3651339) (@lem3651338 _93490 _93497 f x y)). Qed.
Lemma lem3651341 {_93490 _93497 : Type'} (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term65 _93490 _93497 f x y) = (term733 _93490 _93497 f x y).
Proof. exact (MK_COMB (@lem3651340 _93490 _93497 f x y) (@lem3651310 _93490 _93497 f x y)). Qed.
Lemma lem3651360 {_93490 : Type'} (x : _93490) (y : _93490) (u : _93490 -> Prop) : (term72 _93490 x y u) = (term72 _93490 x y u).
Proof. exact (eq_refl (term72 _93490 x y u)). Qed.
Lemma lem3651361 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term74 _93490 _93497 u f x y) = (term734 _93490 _93497 u f x y).
Proof. exact (MK_COMB (@lem3651360 _93490 x y u) (@lem3651341 _93490 _93497 f x y)). Qed.
Lemma lem3651362 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term84 _93490 _93497 u f x) = (term735 _93490 _93497 u f x).
Proof. exact (fun_ext (fun y : _93490 => @lem3651361 _93490 _93497 u f x y)). Qed.
Lemma lem3651363 {_93490 : Type'} : (@all _93490) = (@all _93490).
Proof. exact (eq_refl (@all _93490)). Qed.
Lemma lem3651364 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term85 _93490 _93497 u f x) = (term736 _93490 _93497 u f x).
Proof. exact (MK_COMB (@lem3651363 _93490) (@lem3651362 _93490 _93497 u f x)). Qed.
Lemma lem3651365 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) : (term93 _93490 _93497 u f) = (term737 _93490 _93497 u f).
Proof. exact (fun_ext (fun x : _93490 => @lem3651364 _93490 _93497 u f x)). Qed.
Lemma lem3651366 {_93490 : Type'} : (@all _93490) = (@all _93490).
Proof. exact (eq_refl (@all _93490)). Qed.
Lemma lem3651367 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) : (term94 _93490 _93497 u f) = (term738 _93490 _93497 u f).
Proof. exact (MK_COMB (@lem3651366 _93490) (@lem3651365 _93490 _93497 u f)). Qed.
Lemma lem3651368 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3651369 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) : (term101 _93490 _93497 u f) = (term739 _93490 _93497 u f).
Proof. exact (MK_COMB (@lem3651368) (@lem3651367 _93490 _93497 u f)). Qed.
Lemma lem3651370 {_93490 _93497 : Type'} (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term102 _93490 _93497 t f u) = (term810 _93490 _93497 t f u).
Proof. exact (MK_COMB (@lem3651369 _93490 _93497 u f) (@lem3651282 _93490 _93497 t f u)). Qed.
Lemma lem3651377 {_93490 : Type'} (u : _93490 -> Prop) (s : _93490 -> Prop) : (term53 _93490 u s) = (term53 _93490 u s).
Proof. exact (eq_refl (term53 _93490 u s)). Qed.
Lemma lem3651378 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term107 _93490 _93497 s t f u) = (term811 _93490 _93497 s t f u).
Proof. exact (MK_COMB (@lem3651377 _93490 u s) (@lem3651370 _93490 _93497 t f u)). Qed.
Lemma lem3651379 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3651380 {_93490 _93497 : Type'} (s : _93490 -> Prop) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term179 _93490 _93497 s t f u) = (term812 _93490 _93497 s t f u).
Proof. exact (MK_COMB (@lem3651379) (@lem3651378 _93490 _93497 s t f u)). Qed.
Lemma lem3651381 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) (P : type686 _93497) (t : _93497 -> Prop) : (term181 _93490 _93497 s f u P t) = (term813 _93490 _93497 s f u P t).
Proof. exact (MK_COMB (@lem3651380 _93490 _93497 s t f u) (@lem3651273 _93497 P t)). Qed.
Lemma lem3651382 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3651383 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) (P : type686 _93497) (t : _93497 -> Prop) : (term329 _93490 _93497 s f u P t) = (term814 _93490 _93497 s f u P t).
Proof. exact (MK_COMB (@lem3651382) (@lem3651381 _93490 _93497 s f u P t)). Qed.
Lemma lem3651384 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term359 _93490 _93497 u t s x y P f) = (term815 _93490 _93497 u t s x y P f).
Proof. exact (MK_COMB (@lem3651383 _93490 _93497 s f u P t) (@lem3651270 _93490 _93497 s x y P f)). Qed.
Lemma lem3651385 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3651386 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term660 _93490 _93497 u t s x y P f) = (term816 _93490 _93497 u t s x y P f).
Proof. exact (MK_COMB (@lem3651385) (@lem3651384 _93490 _93497 u t s x y P f)). Qed.
Lemma lem3651387 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) : (term702 _93490 _93497 u t x y x' y' s P f t') = (term817 _93490 _93497 u t x y x' y' s P f t').
Proof. exact (MK_COMB (@lem3651386 _93490 _93497 u t s x y P f) (@lem3651148 _93490 _93497 x' y' s P f t')). Qed.
Lemma lem3651388 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term702 _93490 _93497 u t x y x' y' s P f t') : term817 _93490 _93497 u t x y x' y' s P f t'.
Proof. exact (EQ_MP (@lem3651387 _93490 _93497 u t x y x' y' s P f t') (@lem3650887 _93490 _93497 u t x y x' y' s P f t' h1)). Qed.
Lemma lem3651389 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term815 _93490 _93497 u t s x y P f.
Proof. exact (h1). Qed.
Lemma lem3651390 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term780 _93490 _93497 x' y' s P f t'.
Proof. exact (h1). Qed.
Lemma lem3651391 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term809 _93490 _93497 s x y P f.
Proof. exact (proj2 (@lem3651389 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3651392 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term813 _93490 _93497 s f u P t.
Proof. exact (proj1 (@lem3651389 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3651394 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term811 _93490 _93497 s t f u.
Proof. exact (proj1 (@lem3651392 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3651395 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term810 _93490 _93497 t f u.
Proof. exact (proj2 (@lem3651394 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3651398 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term738 _93490 _93497 u f.
Proof. exact (proj1 (@lem3651395 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3651399 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term741 _93490 _93497 s P f t'.
Proof. exact (proj2 (@lem3651390 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3651400 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term778 _93490 _93497 s x' y' f P.
Proof. exact (proj1 (@lem3651390 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3651401 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term740 _93490 _93497 P f t'.
Proof. exact (proj2 (@lem3651399 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3651404 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term738 _93490 _93497 t' f.
Proof. exact (proj1 (@lem3651401 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3651435 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term806 _93490 _93497 x y P f t) = (term818 _93490 _93497 x y P f t).
Proof. exact (@lem19699 (term819 _93490 x y t) (term799 _93490 _93497 f x y t) (term136 _93490 _93497 P f t)). Qed.
Lemma lem3651442 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term820 _93490 _93497 x y P f t) = (term821 _93490 _93497 x y P f t).
Proof. exact (@lem19699 (term795 _93490 _93497 f x y t) (term791 _93490 _93497 f x y t) (term136 _93490 _93497 P f t)). Qed.
Lemma lem3651449 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term822 _93490 _93497 x y P f t) = (term823 _93490 _93497 x y P f t).
Proof. exact (@lem19699 (term824 _93490 x t) (term824 _93490 y t) (term136 _93490 _93497 P f t)). Qed.
Lemma lem3651450 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3651451 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term825 _93490 _93497 x y P f t) = (term826 _93490 _93497 x y P f t).
Proof. exact (MK_COMB (@lem3651450) (@lem3651449 _93490 _93497 x y P f t)). Qed.
Lemma lem3651452 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term818 _93490 _93497 x y P f t) = (term827 _93490 _93497 x y P f t).
Proof. exact (MK_COMB (@lem3651451 _93490 _93497 x y P f t) (@lem3651442 _93490 _93497 x y P f t)). Qed.
Lemma lem3651454 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term806 _93490 _93497 x y P f t) = (term827 _93490 _93497 x y P f t).
Proof. exact (TRANS (@lem3651435 _93490 _93497 x y P f t) (@lem3651452 _93490 _93497 x y P f t)). Qed.
Lemma lem3651457 {_93490 : Type'} (t : _93490 -> Prop) (s : _93490 -> Prop) : (term103 _93490 t s) = (term103 _93490 t s).
Proof. exact (eq_refl (term103 _93490 t s)). Qed.
Lemma lem3651458 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term807 _93490 _93497 s x y P f t) = (term828 _93490 _93497 s x y P f t).
Proof. exact (MK_COMB (@lem3651457 _93490 t s) (@lem3651454 _93490 _93497 x y P f t)). Qed.
Lemma lem3651459 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term828 _93490 _93497 s x y P f t) = (term829 _93490 _93497 s x y P f t).
Proof. exact (@lem19490 (term823 _93490 _93497 x y P f t) (term227 _93490 t s) (term821 _93490 _93497 x y P f t)). Qed.
Lemma lem3651466 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term830 _93490 _93497 s x y P f t) = (term831 _93490 _93497 s x y P f t).
Proof. exact (@lem19490 (term832 _93490 _93497 x y P f t) (term227 _93490 t s) (term833 _93490 _93497 x y P f t)). Qed.
Lemma lem3651473 {_93490 _93497 : Type'} (x : type684 _93490) (s : _93490 -> Prop) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term834 _93490 _93497 s x y P f t) = (term835 _93490 _93497 x s y P f t).
Proof. exact (@lem19490 (term836 _93490 _93497 x P f t) (term227 _93490 t s) (term836 _93490 _93497 y P f t)). Qed.
Lemma lem3651474 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3651475 {_93490 _93497 : Type'} (x : type684 _93490) (s : _93490 -> Prop) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term837 _93490 _93497 s x y P f t) = (term838 _93490 _93497 x s y P f t).
Proof. exact (MK_COMB (@lem3651474) (@lem3651473 _93490 _93497 x s y P f t)). Qed.
Lemma lem3651476 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term829 _93490 _93497 s x y P f t) = (term839 _93490 _93497 s x y P f t).
Proof. exact (MK_COMB (@lem3651475 _93490 _93497 x s y P f t) (@lem3651466 _93490 _93497 s x y P f t)). Qed.
Lemma lem3651477 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term828 _93490 _93497 s x y P f t) = (term839 _93490 _93497 s x y P f t).
Proof. exact (TRANS (@lem3651459 _93490 _93497 s x y P f t) (@lem3651476 _93490 _93497 s x y P f t)). Qed.
Lemma lem3651478 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (t : _93490 -> Prop) : (term807 _93490 _93497 s x y P f t) = (term839 _93490 _93497 s x y P f t).
Proof. exact (TRANS (@lem3651458 _93490 _93497 s x y P f t) (@lem3651477 _93490 _93497 s x y P f t)). Qed.
Lemma lem3651479 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term808 _93490 _93497 s x y P f) = (term840 _93490 _93497 s x y P f).
Proof. exact (fun_ext (fun t : _93490 -> Prop => @lem3651478 _93490 _93497 s x y P f t)). Qed.
Lemma lem3651480 {_93490 : Type'} : (@all (_93490 -> Prop)) = (@all (_93490 -> Prop)).
Proof. exact (eq_refl (@all (_93490 -> Prop))). Qed.
Lemma lem3651482 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) : (term809 _93490 _93497 s x y P f) = (term841 _93490 _93497 s x y P f).
Proof. exact (MK_COMB (@lem3651480 _93490) (@lem3651479 _93490 _93497 s x y P f)). Qed.
Lemma lem3651483 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term841 _93490 _93497 s x y P f.
Proof. exact (EQ_MP (@lem3651482 _93490 _93497 s x y P f) (@lem3651391 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3651527 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term734 _93490 _93497 u f x y) = (term842 _93490 _93497 u f x y).
Proof. exact (@lem19490 (term730 _93490 _93497 f x y) (term62 _93490 x y u) (term725 _93490 _93497 f x y)). Qed.
Lemma lem3651528 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term735 _93490 _93497 u f x) = (term843 _93490 _93497 u f x).
Proof. exact (fun_ext (fun y : _93490 => @lem3651527 _93490 _93497 u f x y)). Qed.
Lemma lem3651529 {_93490 : Type'} : (@all _93490) = (@all _93490).
Proof. exact (eq_refl (@all _93490)). Qed.
Lemma lem3651530 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term736 _93490 _93497 u f x) = (term844 _93490 _93497 u f x).
Proof. exact (MK_COMB (@lem3651529 _93490) (@lem3651528 _93490 _93497 u f x)). Qed.
Lemma lem3651531 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) : (term737 _93490 _93497 u f) = (term845 _93490 _93497 u f).
Proof. exact (fun_ext (fun x : _93490 => @lem3651530 _93490 _93497 u f x)). Qed.
Lemma lem3651532 {_93490 : Type'} : (@all _93490) = (@all _93490).
Proof. exact (eq_refl (@all _93490)). Qed.
Lemma lem3651534 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) : (term738 _93490 _93497 u f) = (term846 _93490 _93497 u f).
Proof. exact (MK_COMB (@lem3651532 _93490) (@lem3651531 _93490 _93497 u f)). Qed.
Lemma lem3651535 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term846 _93490 _93497 u f.
Proof. exact (EQ_MP (@lem3651534 _93490 _93497 u f) (@lem3651398 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3651541 {A : Type'} (P : A -> Prop) (Q : Prop) : (term847 A P Q) = (term848 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3651542 {_93490 : Type'} (P : type686 _93490) (Q : Prop) : (term849 _93490 P Q) = (term850 _93490 P Q).
Proof. exact (@lem3651541 (_93490 -> Prop) P Q). Qed.
Lemma lem3651543 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term851 _93490 _93497 s x' y' f P t) = (term852 _93490 _93497 s x' y' f P t).
Proof. exact (@lem3651542 _93490 (term771 _93490 _93497 s x' y' t f) (term119 _93497 P t)). Qed.
Lemma lem3651544 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term853 _93490 _93497 s x' y' t f u) = (term769 _93490 _93497 s x' y' t f u).
Proof. exact (eq_refl (term853 _93490 _93497 s x' y' t f u)). Qed.
Lemma lem3651545 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term854 _93490 _93497 s x' y' t f) = (term771 _93490 _93497 s x' y' t f).
Proof. exact (fun_ext (fun u : _93490 -> Prop => @lem3651544 _93490 _93497 s x' y' t f u)). Qed.
Lemma lem3651546 {_93490 : Type'} : (@all (_93490 -> Prop)) = (@all (_93490 -> Prop)).
Proof. exact (eq_refl (@all (_93490 -> Prop))). Qed.
Lemma lem3651547 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term855 _93490 _93497 s x' y' t f) = (term773 _93490 _93497 s x' y' t f).
Proof. exact (MK_COMB (@lem3651546 _93490) (@lem3651545 _93490 _93497 s x' y' t f)). Qed.
Lemma lem3651548 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3651549 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (f : _93490 -> _93497) : (term856 _93490 _93497 s x' y' t f) = (term775 _93490 _93497 s x' y' t f).
Proof. exact (MK_COMB (@lem3651548) (@lem3651547 _93490 _93497 s x' y' t f)). Qed.
Lemma lem3651550 {_93497 : Type'} (P : type686 _93497) (t : _93497 -> Prop) : (term119 _93497 P t) = (term119 _93497 P t).
Proof. exact (eq_refl (term119 _93497 P t)). Qed.
Lemma lem3651551 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term851 _93490 _93497 s x' y' f P t) = (term776 _93490 _93497 s x' y' f P t).
Proof. exact (MK_COMB (@lem3651549 _93490 _93497 s x' y' t f) (@lem3651550 _93497 P t)). Qed.
Lemma lem3651552 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3651553 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term857 _93490 _93497 s x' y' f P t) = (term858 _93490 _93497 s x' y' f P t).
Proof. exact (MK_COMB (@lem3651552) (@lem3651551 _93490 _93497 s x' y' f P t)). Qed.
Lemma lem3651554 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term853 _93490 _93497 s x' y' t f u) = (term769 _93490 _93497 s x' y' t f u).
Proof. exact (eq_refl (term853 _93490 _93497 s x' y' t f u)). Qed.
Lemma lem3651555 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3651556 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term859 _93490 _93497 s x' y' t f u) = (term860 _93490 _93497 s x' y' t f u).
Proof. exact (MK_COMB (@lem3651555) (@lem3651554 _93490 _93497 s x' y' t f u)). Qed.
Lemma lem3651557 {_93497 : Type'} (P : type686 _93497) (t : _93497 -> Prop) : (term119 _93497 P t) = (term119 _93497 P t).
Proof. exact (eq_refl (term119 _93497 P t)). Qed.
Lemma lem3651558 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (u : _93490 -> Prop) (P : type686 _93497) (t : _93497 -> Prop) : (term861 _93490 _93497 s x' y' f u P t) = (term862 _93490 _93497 s x' y' f u P t).
Proof. exact (MK_COMB (@lem3651556 _93490 _93497 s x' y' t f u) (@lem3651557 _93497 P t)). Qed.
Lemma lem3651559 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term863 _93490 _93497 s x' y' f P t) = (term864 _93490 _93497 s x' y' f P t).
Proof. exact (fun_ext (fun u : _93490 -> Prop => @lem3651558 _93490 _93497 s x' y' f u P t)). Qed.
Lemma lem3651560 {_93490 : Type'} : (@all (_93490 -> Prop)) = (@all (_93490 -> Prop)).
Proof. exact (eq_refl (@all (_93490 -> Prop))). Qed.
Lemma lem3651561 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term852 _93490 _93497 s x' y' f P t) = (term865 _93490 _93497 s x' y' f P t).
Proof. exact (MK_COMB (@lem3651560 _93490) (@lem3651559 _93490 _93497 s x' y' f P t)). Qed.
Lemma lem3651562 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : ((term851 _93490 _93497 s x' y' f P t) = (term852 _93490 _93497 s x' y' f P t)) = ((term776 _93490 _93497 s x' y' f P t) = (term865 _93490 _93497 s x' y' f P t)).
Proof. exact (MK_COMB (@lem3651553 _93490 _93497 s x' y' f P t) (@lem3651561 _93490 _93497 s x' y' f P t)). Qed.
Lemma lem3651563 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term776 _93490 _93497 s x' y' f P t) = (term865 _93490 _93497 s x' y' f P t).
Proof. exact (EQ_MP (@lem3651562 _93490 _93497 s x' y' f P t) (@lem3651543 _93490 _93497 s x' y' f P t)). Qed.
Lemma lem3651564 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) : (term777 _93490 _93497 s x' y' f P) = (term866 _93490 _93497 s x' y' f P).
Proof. exact (fun_ext (fun t : _93497 -> Prop => @lem3651563 _93490 _93497 s x' y' f P t)). Qed.
Lemma lem3651565 {_93497 : Type'} : (@all (_93497 -> Prop)) = (@all (_93497 -> Prop)).
Proof. exact (eq_refl (@all (_93497 -> Prop))). Qed.
Lemma lem3651566 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) : (term778 _93490 _93497 s x' y' f P) = (term867 _93490 _93497 s x' y' f P).
Proof. exact (MK_COMB (@lem3651565 _93497) (@lem3651564 _93490 _93497 s x' y' f P)). Qed.
Lemma lem3651567 {_93497 : Type'} (P : type686 _93497) (t : _93497 -> Prop) : (term119 _93497 P t) = (term119 _93497 P t).
Proof. exact (eq_refl (term119 _93497 P t)). Qed.
Lemma lem3651597 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term767 _93490 _93497 x' y' t f u) = (term868 _93490 _93497 x' y' t f u).
Proof. exact (@lem19699 (term869 _93490 _93497 x' y' t u) (term760 _93490 _93497 f x' y' t u) (term95 _93490 _93497 t f u)). Qed.
Lemma lem3651604 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term870 _93490 _93497 x' y' t f u) = (term871 _93490 _93497 x' y' t f u).
Proof. exact (@lem19699 (term756 _93490 _93497 f x' y' t u) (term752 _93490 _93497 f x' y' t u) (term95 _93490 _93497 t f u)). Qed.
Lemma lem3651611 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term872 _93490 _93497 x' y' t f u) = (term873 _93490 _93497 x' y' t f u).
Proof. exact (@lem19699 (term874 _93490 _93497 x' t u) (term874 _93490 _93497 y' t u) (term95 _93490 _93497 t f u)). Qed.
Lemma lem3651612 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3651613 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term875 _93490 _93497 x' y' t f u) = (term876 _93490 _93497 x' y' t f u).
Proof. exact (MK_COMB (@lem3651612) (@lem3651611 _93490 _93497 x' y' t f u)). Qed.
Lemma lem3651614 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term868 _93490 _93497 x' y' t f u) = (term877 _93490 _93497 x' y' t f u).
Proof. exact (MK_COMB (@lem3651613 _93490 _93497 x' y' t f u) (@lem3651604 _93490 _93497 x' y' t f u)). Qed.
Lemma lem3651616 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term767 _93490 _93497 x' y' t f u) = (term877 _93490 _93497 x' y' t f u).
Proof. exact (TRANS (@lem3651597 _93490 _93497 x' y' t f u) (@lem3651614 _93490 _93497 x' y' t f u)). Qed.
Lemma lem3651619 {_93490 : Type'} (u : _93490 -> Prop) (s : _93490 -> Prop) : (term103 _93490 u s) = (term103 _93490 u s).
Proof. exact (eq_refl (term103 _93490 u s)). Qed.
Lemma lem3651620 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term769 _93490 _93497 s x' y' t f u) = (term878 _93490 _93497 s x' y' t f u).
Proof. exact (MK_COMB (@lem3651619 _93490 u s) (@lem3651616 _93490 _93497 x' y' t f u)). Qed.
Lemma lem3651621 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term878 _93490 _93497 s x' y' t f u) = (term879 _93490 _93497 s x' y' t f u).
Proof. exact (@lem19490 (term873 _93490 _93497 x' y' t f u) (term227 _93490 u s) (term871 _93490 _93497 x' y' t f u)). Qed.
Lemma lem3651628 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term880 _93490 _93497 s x' y' t f u) = (term881 _93490 _93497 s x' y' t f u).
Proof. exact (@lem19490 (term882 _93490 _93497 x' y' t f u) (term227 _93490 u s) (term883 _93490 _93497 x' y' t f u)). Qed.
Lemma lem3651635 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (s : _93490 -> Prop) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term884 _93490 _93497 s x' y' t f u) = (term885 _93490 _93497 x' s y' t f u).
Proof. exact (@lem19490 (term886 _93490 _93497 x' t f u) (term227 _93490 u s) (term886 _93490 _93497 y' t f u)). Qed.
Lemma lem3651636 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3651637 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (s : _93490 -> Prop) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term887 _93490 _93497 s x' y' t f u) = (term888 _93490 _93497 x' s y' t f u).
Proof. exact (MK_COMB (@lem3651636) (@lem3651635 _93490 _93497 x' s y' t f u)). Qed.
Lemma lem3651638 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term879 _93490 _93497 s x' y' t f u) = (term889 _93490 _93497 s x' y' t f u).
Proof. exact (MK_COMB (@lem3651637 _93490 _93497 x' s y' t f u) (@lem3651628 _93490 _93497 s x' y' t f u)). Qed.
Lemma lem3651639 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term878 _93490 _93497 s x' y' t f u) = (term889 _93490 _93497 s x' y' t f u).
Proof. exact (TRANS (@lem3651621 _93490 _93497 s x' y' t f u) (@lem3651638 _93490 _93497 s x' y' t f u)). Qed.
Lemma lem3651640 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term769 _93490 _93497 s x' y' t f u) = (term889 _93490 _93497 s x' y' t f u).
Proof. exact (TRANS (@lem3651620 _93490 _93497 s x' y' t f u) (@lem3651639 _93490 _93497 s x' y' t f u)). Qed.
Lemma lem3651641 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3651642 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (t : _93497 -> Prop) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term860 _93490 _93497 s x' y' t f u) = (term890 _93490 _93497 s x' y' t f u).
Proof. exact (MK_COMB (@lem3651641) (@lem3651640 _93490 _93497 s x' y' t f u)). Qed.
Lemma lem3651643 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (u : _93490 -> Prop) (P : type686 _93497) (t : _93497 -> Prop) : (term862 _93490 _93497 s x' y' f u P t) = (term891 _93490 _93497 s x' y' f u P t).
Proof. exact (MK_COMB (@lem3651642 _93490 _93497 s x' y' t f u) (@lem3651567 _93497 P t)). Qed.
Lemma lem3651644 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (u : _93490 -> Prop) (P : type686 _93497) (t : _93497 -> Prop) : (term891 _93490 _93497 s x' y' f u P t) = (term892 _93490 _93497 s x' y' f u P t).
Proof. exact (@lem19699 (term885 _93490 _93497 x' s y' t f u) (term881 _93490 _93497 s x' y' t f u) (term119 _93497 P t)). Qed.
Lemma lem3651651 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (u : _93490 -> Prop) (P : type686 _93497) (t : _93497 -> Prop) : (term893 _93490 _93497 s x' y' f u P t) = (term894 _93490 _93497 s x' y' f u P t).
Proof. exact (@lem19699 (term895 _93490 _93497 s x' y' t f u) (term896 _93490 _93497 s x' y' t f u) (term119 _93497 P t)). Qed.
Lemma lem3651658 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (s : _93490 -> Prop) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (u : _93490 -> Prop) (P : type686 _93497) (t : _93497 -> Prop) : (term897 _93490 _93497 x' s y' f u P t) = (term898 _93490 _93497 x' s y' f u P t).
Proof. exact (@lem19699 (term899 _93490 _93497 s x' t f u) (term899 _93490 _93497 s y' t f u) (term119 _93497 P t)). Qed.
Lemma lem3651659 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3651660 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (s : _93490 -> Prop) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (u : _93490 -> Prop) (P : type686 _93497) (t : _93497 -> Prop) : (term900 _93490 _93497 x' s y' f u P t) = (term901 _93490 _93497 x' s y' f u P t).
Proof. exact (MK_COMB (@lem3651659) (@lem3651658 _93490 _93497 x' s y' f u P t)). Qed.
Lemma lem3651661 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (u : _93490 -> Prop) (P : type686 _93497) (t : _93497 -> Prop) : (term892 _93490 _93497 s x' y' f u P t) = (term902 _93490 _93497 s x' y' f u P t).
Proof. exact (MK_COMB (@lem3651660 _93490 _93497 x' s y' f u P t) (@lem3651651 _93490 _93497 s x' y' f u P t)). Qed.
Lemma lem3651662 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (u : _93490 -> Prop) (P : type686 _93497) (t : _93497 -> Prop) : (term891 _93490 _93497 s x' y' f u P t) = (term902 _93490 _93497 s x' y' f u P t).
Proof. exact (TRANS (@lem3651644 _93490 _93497 s x' y' f u P t) (@lem3651661 _93490 _93497 s x' y' f u P t)). Qed.
Lemma lem3651663 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (u : _93490 -> Prop) (P : type686 _93497) (t : _93497 -> Prop) : (term862 _93490 _93497 s x' y' f u P t) = (term902 _93490 _93497 s x' y' f u P t).
Proof. exact (TRANS (@lem3651643 _93490 _93497 s x' y' f u P t) (@lem3651662 _93490 _93497 s x' y' f u P t)). Qed.
Lemma lem3651664 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term864 _93490 _93497 s x' y' f P t) = (term903 _93490 _93497 s x' y' f P t).
Proof. exact (fun_ext (fun u : _93490 -> Prop => @lem3651663 _93490 _93497 s x' y' f u P t)). Qed.
Lemma lem3651665 {_93490 : Type'} : (@all (_93490 -> Prop)) = (@all (_93490 -> Prop)).
Proof. exact (eq_refl (@all (_93490 -> Prop))). Qed.
Lemma lem3651666 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) (t : _93497 -> Prop) : (term865 _93490 _93497 s x' y' f P t) = (term904 _93490 _93497 s x' y' f P t).
Proof. exact (MK_COMB (@lem3651665 _93490) (@lem3651664 _93490 _93497 s x' y' f P t)). Qed.
Lemma lem3651667 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) : (term866 _93490 _93497 s x' y' f P) = (term905 _93490 _93497 s x' y' f P).
Proof. exact (fun_ext (fun t : _93497 -> Prop => @lem3651666 _93490 _93497 s x' y' f P t)). Qed.
Lemma lem3651668 {_93497 : Type'} : (@all (_93497 -> Prop)) = (@all (_93497 -> Prop)).
Proof. exact (eq_refl (@all (_93497 -> Prop))). Qed.
Lemma lem3651669 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) : (term867 _93490 _93497 s x' y' f P) = (term906 _93490 _93497 s x' y' f P).
Proof. exact (MK_COMB (@lem3651668 _93497) (@lem3651667 _93490 _93497 s x' y' f P)). Qed.
Lemma lem3651670 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) : (term778 _93490 _93497 s x' y' f P) = (term906 _93490 _93497 s x' y' f P).
Proof. exact (TRANS (@lem3651566 _93490 _93497 s x' y' f P) (@lem3651669 _93490 _93497 s x' y' f P)). Qed.
Lemma lem3651671 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term906 _93490 _93497 s x' y' f P.
Proof. exact (EQ_MP (@lem3651670 _93490 _93497 s x' y' f P) (@lem3651400 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3651711 {_93490 _93497 : Type'} (t' : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) (y : _93490) : (term734 _93490 _93497 t' f x y) = (term842 _93490 _93497 t' f x y).
Proof. exact (@lem19490 (term730 _93490 _93497 f x y) (term62 _93490 x y t') (term725 _93490 _93497 f x y)). Qed.
Lemma lem3651712 {_93490 _93497 : Type'} (t' : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term735 _93490 _93497 t' f x) = (term843 _93490 _93497 t' f x).
Proof. exact (fun_ext (fun y : _93490 => @lem3651711 _93490 _93497 t' f x y)). Qed.
Lemma lem3651713 {_93490 : Type'} : (@all _93490) = (@all _93490).
Proof. exact (eq_refl (@all _93490)). Qed.
Lemma lem3651714 {_93490 _93497 : Type'} (t' : _93490 -> Prop) (f : _93490 -> _93497) (x : _93490) : (term736 _93490 _93497 t' f x) = (term844 _93490 _93497 t' f x).
Proof. exact (MK_COMB (@lem3651713 _93490) (@lem3651712 _93490 _93497 t' f x)). Qed.
Lemma lem3651715 {_93490 _93497 : Type'} (t' : _93490 -> Prop) (f : _93490 -> _93497) : (term737 _93490 _93497 t' f) = (term845 _93490 _93497 t' f).
Proof. exact (fun_ext (fun x : _93490 => @lem3651714 _93490 _93497 t' f x)). Qed.
Lemma lem3651716 {_93490 : Type'} : (@all _93490) = (@all _93490).
Proof. exact (eq_refl (@all _93490)). Qed.
Lemma lem3651718 {_93490 _93497 : Type'} (t' : _93490 -> Prop) (f : _93490 -> _93497) : (term738 _93490 _93497 t' f) = (term846 _93490 _93497 t' f).
Proof. exact (MK_COMB (@lem3651716 _93490) (@lem3651715 _93490 _93497 t' f)). Qed.
Lemma lem3651719 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term846 _93490 _93497 t' f.
Proof. exact (EQ_MP (@lem3651718 _93490 _93497 t' f) (@lem3651404 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3651724 {_93490 _93497 : Type'} (_40049 : _93490 -> Prop) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term907 _93490 _93497 s x y P f _40049.
Proof. exact (@lem3651483 _93490 _93497 u t s x y P f h1 _40049). Qed.
Lemma lem3651725 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term907 _93490 _93497 s x y P f _40049) = (term839 _93490 _93497 s x y P f _40049).
Proof. exact (eq_refl (term907 _93490 _93497 s x y P f _40049)). Qed.
Lemma lem3651726 {_93490 _93497 : Type'} (_40049 : _93490 -> Prop) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term839 _93490 _93497 s x y P f _40049.
Proof. exact (EQ_MP (@lem3651725 _93490 _93497 s x y P f _40049) (@lem3651724 _93490 _93497 _40049 u t s x y P f h1)). Qed.
Lemma lem3651727 {_93490 _93497 : Type'} (_40050 : _93490) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term908 _93490 _93497 u f _40050.
Proof. exact (@lem3651535 _93490 _93497 u t s x y P f h1 _40050). Qed.
Lemma lem3651728 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (_40050 : _93490) : (term908 _93490 _93497 u f _40050) = (term844 _93490 _93497 u f _40050).
Proof. exact (eq_refl (term908 _93490 _93497 u f _40050)). Qed.
Lemma lem3651729 {_93490 _93497 : Type'} (_40050 : _93490) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term844 _93490 _93497 u f _40050.
Proof. exact (EQ_MP (@lem3651728 _93490 _93497 u f _40050) (@lem3651727 _93490 _93497 _40050 u t s x y P f h1)). Qed.
Lemma lem3651730 {_93490 _93497 : Type'} (_40050 : _93490) (_40051 : _93490) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term909 _93490 _93497 u f _40050 _40051.
Proof. exact (@lem3651729 _93490 _93497 _40050 u t s x y P f h1 _40051). Qed.
Lemma lem3651731 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (_40050 : _93490) (_40051 : _93490) : (term909 _93490 _93497 u f _40050 _40051) = (term842 _93490 _93497 u f _40050 _40051).
Proof. exact (eq_refl (term909 _93490 _93497 u f _40050 _40051)). Qed.
Lemma lem3651732 {_93490 _93497 : Type'} (_40050 : _93490) (_40051 : _93490) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term842 _93490 _93497 u f _40050 _40051.
Proof. exact (EQ_MP (@lem3651731 _93490 _93497 u f _40050 _40051) (@lem3651730 _93490 _93497 _40050 _40051 u t s x y P f h1)). Qed.
Lemma lem3651733 {_93490 _93497 : Type'} (_40052 : _93497 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term910 _93490 _93497 s x' y' f P _40052.
Proof. exact (@lem3651671 _93490 _93497 x' y' s P f t' h1 _40052). Qed.
Lemma lem3651734 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term910 _93490 _93497 s x' y' f P _40052) = (term904 _93490 _93497 s x' y' f P _40052).
Proof. exact (eq_refl (term910 _93490 _93497 s x' y' f P _40052)). Qed.
Lemma lem3651735 {_93490 _93497 : Type'} (_40052 : _93497 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term904 _93490 _93497 s x' y' f P _40052.
Proof. exact (EQ_MP (@lem3651734 _93490 _93497 s x' y' f P _40052) (@lem3651733 _93490 _93497 _40052 x' y' s P f t' h1)). Qed.
Lemma lem3651736 {_93490 _93497 : Type'} (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term911 _93490 _93497 s x' y' f P _40052 _40053.
Proof. exact (@lem3651735 _93490 _93497 _40052 x' y' s P f t' h1 _40053). Qed.
Lemma lem3651737 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term911 _93490 _93497 s x' y' f P _40052 _40053) = (term902 _93490 _93497 s x' y' f _40053 P _40052).
Proof. exact (eq_refl (term911 _93490 _93497 s x' y' f P _40052 _40053)). Qed.
Lemma lem3651738 {_93490 _93497 : Type'} (_40053 : _93490 -> Prop) (_40052 : _93497 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term902 _93490 _93497 s x' y' f _40053 P _40052.
Proof. exact (EQ_MP (@lem3651737 _93490 _93497 s x' y' f _40053 P _40052) (@lem3651736 _93490 _93497 _40052 _40053 x' y' s P f t' h1)). Qed.
Lemma lem3651739 {_93490 _93497 : Type'} (_40054 : _93490) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term908 _93490 _93497 t' f _40054.
Proof. exact (@lem3651719 _93490 _93497 x' y' s P f t' h1 _40054). Qed.
Lemma lem3651740 {_93490 _93497 : Type'} (t' : _93490 -> Prop) (f : _93490 -> _93497) (_40054 : _93490) : (term908 _93490 _93497 t' f _40054) = (term844 _93490 _93497 t' f _40054).
Proof. exact (eq_refl (term908 _93490 _93497 t' f _40054)). Qed.
Lemma lem3651741 {_93490 _93497 : Type'} (_40054 : _93490) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term844 _93490 _93497 t' f _40054.
Proof. exact (EQ_MP (@lem3651740 _93490 _93497 t' f _40054) (@lem3651739 _93490 _93497 _40054 x' y' s P f t' h1)). Qed.
Lemma lem3651742 {_93490 _93497 : Type'} (_40054 : _93490) (_40055 : _93490) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term909 _93490 _93497 t' f _40054 _40055.
Proof. exact (@lem3651741 _93490 _93497 _40054 x' y' s P f t' h1 _40055). Qed.
Lemma lem3651743 {_93490 _93497 : Type'} (t' : _93490 -> Prop) (f : _93490 -> _93497) (_40054 : _93490) (_40055 : _93490) : (term909 _93490 _93497 t' f _40054 _40055) = (term842 _93490 _93497 t' f _40054 _40055).
Proof. exact (eq_refl (term909 _93490 _93497 t' f _40054 _40055)). Qed.
Lemma lem3651744 {_93490 _93497 : Type'} (_40054 : _93490) (_40055 : _93490) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term842 _93490 _93497 t' f _40054 _40055.
Proof. exact (EQ_MP (@lem3651743 _93490 _93497 t' f _40054 _40055) (@lem3651742 _93490 _93497 _40054 _40055 x' y' s P f t' h1)). Qed.
Lemma lem3651745 {_93490 _93497 : Type'} (_40050 : _93490) (_40051 : _93490) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term912 _93490 _93497 u f _40050 _40051.
Proof. exact (proj2 (@lem3651732 _93490 _93497 _40050 _40051 u t s x y P f h1)). Qed.
Lemma lem3651747 {_93490 _93497 : Type'} (_40049 : _93490 -> Prop) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term831 _93490 _93497 s x y P f _40049.
Proof. exact (proj2 (@lem3651726 _93490 _93497 _40049 u t s x y P f h1)). Qed.
Lemma lem3651748 {_93490 _93497 : Type'} (_40049 : _93490 -> Prop) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term835 _93490 _93497 x s y P f _40049.
Proof. exact (proj1 (@lem3651726 _93490 _93497 _40049 u t s x y P f h1)). Qed.
Lemma lem3651749 {_93490 _93497 : Type'} (_40049 : _93490 -> Prop) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term913 _93490 _93497 s x y P f _40049.
Proof. exact (proj2 (@lem3651747 _93490 _93497 _40049 u t s x y P f h1)). Qed.
Lemma lem3651750 {_93490 _93497 : Type'} (_40049 : _93490 -> Prop) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term914 _93490 _93497 s x y P f _40049.
Proof. exact (proj1 (@lem3651747 _93490 _93497 _40049 u t s x y P f h1)). Qed.
Lemma lem3651753 {_93490 _93497 : Type'} (_40054 : _93490) (_40055 : _93490) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term912 _93490 _93497 t' f _40054 _40055.
Proof. exact (proj2 (@lem3651744 _93490 _93497 _40054 _40055 x' y' s P f t' h1)). Qed.
Lemma lem3651755 {_93490 _93497 : Type'} (_40053 : _93490 -> Prop) (_40052 : _93497 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term894 _93490 _93497 s x' y' f _40053 P _40052.
Proof. exact (proj2 (@lem3651738 _93490 _93497 _40053 _40052 x' y' s P f t' h1)). Qed.
Lemma lem3651756 {_93490 _93497 : Type'} (_40053 : _93490 -> Prop) (_40052 : _93497 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term898 _93490 _93497 x' s y' f _40053 P _40052.
Proof. exact (proj1 (@lem3651738 _93490 _93497 _40053 _40052 x' y' s P f t' h1)). Qed.
Lemma lem3651757 {_93490 _93497 : Type'} (_40053 : _93490 -> Prop) (_40052 : _93497 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term915 _93490 _93497 s x' y' f _40053 P _40052.
Proof. exact (proj2 (@lem3651755 _93490 _93497 _40053 _40052 x' y' s P f t' h1)). Qed.
Lemma lem3651758 {_93490 _93497 : Type'} (_40053 : _93490 -> Prop) (_40052 : _93497 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term916 _93490 _93497 s x' y' f _40053 P _40052.
Proof. exact (proj1 (@lem3651755 _93490 _93497 _40053 _40052 x' y' s P f t' h1)). Qed.
Lemma lem3651759 {_93490 _93497 : Type'} (_40053 : _93490 -> Prop) (_40052 : _93497 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term917 _93490 _93497 s y' f _40053 P _40052.
Proof. exact (proj2 (@lem3651756 _93490 _93497 _40053 _40052 x' y' s P f t' h1)). Qed.
Lemma lem3651760 {_93490 _93497 : Type'} (_40053 : _93490 -> Prop) (_40052 : _93497 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term917 _93490 _93497 s x' f _40053 P _40052.
Proof. exact (proj1 (@lem3651756 _93490 _93497 _40053 _40052 x' y' s P f t' h1)). Qed.
Lemma lem3651762 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : P t.
Proof. exact (proj2 (@lem3651392 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3651766 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : t = (@IMAGE _93490 _93497 f u).
Proof. exact (proj2 (@lem3651395 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3651797 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (_40050 : _93490) (_40051 : _93490) : (term912 _93490 _93497 u f _40050 _40051) = (term918 _93490 _93497 u f _40050 _40051).
Proof. exact (@lem3648785 (term919 _93490 _40050 u) (term919 _93490 _40051 u) (term725 _93490 _93497 f _40050 _40051)). Qed.
Lemma lem3651809 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term832 _93490 _93497 x y P f _40049) = (term920 _93490 _93497 x y P f _40049).
Proof. exact (@lem3648785 ((term783 _93490 _93497 f x _40049) = (term783 _93490 _93497 f y _40049)) ((x _40049) = (y _40049)) (term136 _93490 _93497 P f _40049)). Qed.
Lemma lem3651810 {_93490 : Type'} (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term103 _93490 _40049 s) = (term103 _93490 _40049 s).
Proof. exact (eq_refl (term103 _93490 _40049 s)). Qed.
Lemma lem3651813 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term914 _93490 _93497 s x y P f _40049) = (term921 _93490 _93497 s x y P f _40049).
Proof. exact (MK_COMB (@lem3651810 _93490 _40049 s) (@lem3651809 _93490 _93497 x y P f _40049)). Qed.
Lemma lem3651825 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term833 _93490 _93497 x y P f _40049) = (term922 _93490 _93497 x y P f _40049).
Proof. exact (@lem3648785 (term787 _93490 _93497 x f y _40049) (term781 _93490 x y _40049) (term136 _93490 _93497 P f _40049)). Qed.
Lemma lem3651826 {_93490 : Type'} (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term103 _93490 _40049 s) = (term103 _93490 _40049 s).
Proof. exact (eq_refl (term103 _93490 _40049 s)). Qed.
Lemma lem3651829 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term913 _93490 _93497 s x y P f _40049) = (term923 _93490 _93497 s x y P f _40049).
Proof. exact (MK_COMB (@lem3651826 _93490 _40049 s) (@lem3651825 _93490 _93497 x y P f _40049)). Qed.
Lemma lem3651885 {_93490 _93497 : Type'} (t' : _93490 -> Prop) (f : _93490 -> _93497) (_40054 : _93490) (_40055 : _93490) : (term912 _93490 _93497 t' f _40054 _40055) = (term918 _93490 _93497 t' f _40054 _40055).
Proof. exact (@lem3648785 (term919 _93490 _40054 t') (term919 _93490 _40055 t') (term725 _93490 _93497 f _40054 _40055)). Qed.
Lemma lem3651886 {_93490 _93497 : Type'} (_40054 : _93490) (_40055 : _93490) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term918 _93490 _93497 t' f _40054 _40055.
Proof. exact (EQ_MP (@lem3651885 _93490 _93497 t' f _40054 _40055) (@lem3651753 _93490 _93497 _40054 _40055 x' y' s P f t' h1)). Qed.
Lemma lem3651890 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term916 _93490 _93497 s x' y' f _40053 P _40052) = (term924 _93490 _93497 s x' y' f _40053 P _40052).
Proof. exact (@lem3648785 (term227 _93490 _40053 s) (term882 _93490 _93497 x' y' _40052 f _40053) (term119 _93497 P _40052)). Qed.
Lemma lem3651891 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term925 _93490 _93497 x' y' f _40053 P _40052) = (term926 _93490 _93497 x' y' f _40053 P _40052).
Proof. exact (@lem3648785 (term756 _93490 _93497 f x' y' _40052 _40053) (term95 _93490 _93497 _40052 f _40053) (term119 _93497 P _40052)). Qed.
Lemma lem3651902 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term926 _93490 _93497 x' y' f _40053 P _40052) = (term927 _93490 _93497 x' y' f _40053 P _40052).
Proof. exact (@lem3648785 ((term744 _93490 _93497 f x' _40052 _40053) = (term744 _93490 _93497 f y' _40052 _40053)) ((x' _40052 _40053) = (y' _40052 _40053)) (term928 _93490 _93497 f _40053 P _40052)). Qed.
Lemma lem3651903 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term925 _93490 _93497 x' y' f _40053 P _40052) = (term927 _93490 _93497 x' y' f _40053 P _40052).
Proof. exact (TRANS (@lem3651891 _93490 _93497 x' y' f _40053 P _40052) (@lem3651902 _93490 _93497 x' y' f _40053 P _40052)). Qed.
Lemma lem3651904 {_93490 : Type'} (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term103 _93490 _40053 s) = (term103 _93490 _40053 s).
Proof. exact (eq_refl (term103 _93490 _40053 s)). Qed.
Lemma lem3651907 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term924 _93490 _93497 s x' y' f _40053 P _40052) = (term929 _93490 _93497 s x' y' f _40053 P _40052).
Proof. exact (MK_COMB (@lem3651904 _93490 _40053 s) (@lem3651903 _93490 _93497 x' y' f _40053 P _40052)). Qed.
Lemma lem3651909 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term916 _93490 _93497 s x' y' f _40053 P _40052) = (term929 _93490 _93497 s x' y' f _40053 P _40052).
Proof. exact (TRANS (@lem3651890 _93490 _93497 s x' y' f _40053 P _40052) (@lem3651907 _93490 _93497 s x' y' f _40053 P _40052)). Qed.
Lemma lem3651910 {_93490 _93497 : Type'} (_40053 : _93490 -> Prop) (_40052 : _93497 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term929 _93490 _93497 s x' y' f _40053 P _40052.
Proof. exact (EQ_MP (@lem3651909 _93490 _93497 s x' y' f _40053 P _40052) (@lem3651758 _93490 _93497 _40053 _40052 x' y' s P f t' h1)). Qed.
Lemma lem3651914 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term915 _93490 _93497 s x' y' f _40053 P _40052) = (term930 _93490 _93497 s x' y' f _40053 P _40052).
Proof. exact (@lem3648785 (term227 _93490 _40053 s) (term883 _93490 _93497 x' y' _40052 f _40053) (term119 _93497 P _40052)). Qed.
Lemma lem3651915 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term931 _93490 _93497 x' y' f _40053 P _40052) = (term932 _93490 _93497 x' y' f _40053 P _40052).
Proof. exact (@lem3648785 (term752 _93490 _93497 f x' y' _40052 _40053) (term95 _93490 _93497 _40052 f _40053) (term119 _93497 P _40052)). Qed.
Lemma lem3651926 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term932 _93490 _93497 x' y' f _40053 P _40052) = (term933 _93490 _93497 x' y' f _40053 P _40052).
Proof. exact (@lem3648785 (term748 _93490 _93497 x' f y' _40052 _40053) (term742 _93490 _93497 x' y' _40052 _40053) (term928 _93490 _93497 f _40053 P _40052)). Qed.
Lemma lem3651927 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term931 _93490 _93497 x' y' f _40053 P _40052) = (term933 _93490 _93497 x' y' f _40053 P _40052).
Proof. exact (TRANS (@lem3651915 _93490 _93497 x' y' f _40053 P _40052) (@lem3651926 _93490 _93497 x' y' f _40053 P _40052)). Qed.
Lemma lem3651928 {_93490 : Type'} (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term103 _93490 _40053 s) = (term103 _93490 _40053 s).
Proof. exact (eq_refl (term103 _93490 _40053 s)). Qed.
Lemma lem3651931 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term930 _93490 _93497 s x' y' f _40053 P _40052) = (term934 _93490 _93497 s x' y' f _40053 P _40052).
Proof. exact (MK_COMB (@lem3651928 _93490 _40053 s) (@lem3651927 _93490 _93497 x' y' f _40053 P _40052)). Qed.
Lemma lem3651933 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term915 _93490 _93497 s x' y' f _40053 P _40052) = (term934 _93490 _93497 s x' y' f _40053 P _40052).
Proof. exact (TRANS (@lem3651914 _93490 _93497 s x' y' f _40053 P _40052) (@lem3651931 _93490 _93497 s x' y' f _40053 P _40052)). Qed.
Lemma lem3651934 {_93490 _93497 : Type'} (_40053 : _93490 -> Prop) (_40052 : _93497 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term934 _93490 _93497 s x' y' f _40053 P _40052.
Proof. exact (EQ_MP (@lem3651933 _93490 _93497 s x' y' f _40053 P _40052) (@lem3651757 _93490 _93497 _40053 _40052 x' y' s P f t' h1)). Qed.
Lemma lem3651938 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term917 _93490 _93497 s x' f _40053 P _40052) = (term935 _93490 _93497 s x' f _40053 P _40052).
Proof. exact (@lem3648785 (term227 _93490 _40053 s) (term886 _93490 _93497 x' _40052 f _40053) (term119 _93497 P _40052)). Qed.
Lemma lem3651945 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term936 _93490 _93497 x' f _40053 P _40052) = (term937 _93490 _93497 x' f _40053 P _40052).
Proof. exact (@lem3648785 (term874 _93490 _93497 x' _40052 _40053) (term95 _93490 _93497 _40052 f _40053) (term119 _93497 P _40052)). Qed.
Lemma lem3651946 {_93490 : Type'} (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term103 _93490 _40053 s) = (term103 _93490 _40053 s).
Proof. exact (eq_refl (term103 _93490 _40053 s)). Qed.
Lemma lem3651949 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term935 _93490 _93497 s x' f _40053 P _40052) = (term938 _93490 _93497 s x' f _40053 P _40052).
Proof. exact (MK_COMB (@lem3651946 _93490 _40053 s) (@lem3651945 _93490 _93497 x' f _40053 P _40052)). Qed.
Lemma lem3651951 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term917 _93490 _93497 s x' f _40053 P _40052) = (term938 _93490 _93497 s x' f _40053 P _40052).
Proof. exact (TRANS (@lem3651938 _93490 _93497 s x' f _40053 P _40052) (@lem3651949 _93490 _93497 s x' f _40053 P _40052)). Qed.
Lemma lem3651952 {_93490 _93497 : Type'} (_40053 : _93490 -> Prop) (_40052 : _93497 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term938 _93490 _93497 s x' f _40053 P _40052.
Proof. exact (EQ_MP (@lem3651951 _93490 _93497 s x' f _40053 P _40052) (@lem3651760 _93490 _93497 _40053 _40052 x' y' s P f t' h1)). Qed.
Lemma lem3651956 {_93490 _93497 : Type'} (s : _93490 -> Prop) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term917 _93490 _93497 s y' f _40053 P _40052) = (term935 _93490 _93497 s y' f _40053 P _40052).
Proof. exact (@lem3648785 (term227 _93490 _40053 s) (term886 _93490 _93497 y' _40052 f _40053) (term119 _93497 P _40052)). Qed.
Lemma lem3651963 {_93490 _93497 : Type'} (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term936 _93490 _93497 y' f _40053 P _40052) = (term937 _93490 _93497 y' f _40053 P _40052).
Proof. exact (@lem3648785 (term874 _93490 _93497 y' _40052 _40053) (term95 _93490 _93497 _40052 f _40053) (term119 _93497 P _40052)). Qed.
Lemma lem3651964 {_93490 : Type'} (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term103 _93490 _40053 s) = (term103 _93490 _40053 s).
Proof. exact (eq_refl (term103 _93490 _40053 s)). Qed.
Lemma lem3651967 {_93490 _93497 : Type'} (s : _93490 -> Prop) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term935 _93490 _93497 s y' f _40053 P _40052) = (term938 _93490 _93497 s y' f _40053 P _40052).
Proof. exact (MK_COMB (@lem3651964 _93490 _40053 s) (@lem3651963 _93490 _93497 y' f _40053 P _40052)). Qed.
Lemma lem3651969 {_93490 _93497 : Type'} (s : _93490 -> Prop) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term917 _93490 _93497 s y' f _40053 P _40052) = (term938 _93490 _93497 s y' f _40053 P _40052).
Proof. exact (TRANS (@lem3651956 _93490 _93497 s y' f _40053 P _40052) (@lem3651967 _93490 _93497 s y' f _40053 P _40052)). Qed.
Lemma lem3651970 {_93490 _93497 : Type'} (_40053 : _93490 -> Prop) (_40052 : _93497 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term938 _93490 _93497 s y' f _40053 P _40052.
Proof. exact (EQ_MP (@lem3651969 _93490 _93497 s y' f _40053 P _40052) (@lem3651759 _93490 _93497 _40053 _40052 x' y' s P f t' h1)). Qed.
Lemma lem3651985 {_93497 : Type'} (P : type686 _93497) : (term939 _93497 P) = (term939 _93497 P).
Proof. exact (eq_refl (term939 _93497 P)). Qed.
Lemma lem3651986 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : (term940 _93497 P t) = (term941 _93490 _93497 P f u).
Proof. exact (MK_COMB (@lem3651985 _93497 P) (@lem3651766 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3651987 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term941 _93490 _93497 P f u) = (term45 _93490 _93497 P f u).
Proof. exact (eq_refl (term941 _93490 _93497 P f u)). Qed.
Lemma lem3651988 {_93497 : Type'} (P : type686 _93497) (t : _93497 -> Prop) : (term942 _93497 P t) = (term942 _93497 P t).
Proof. exact (eq_refl (term942 _93497 P t)). Qed.
Lemma lem3651989 {_93490 _93497 : Type'} (t : _93497 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (u : _93490 -> Prop) : ((term940 _93497 P t) = (term941 _93490 _93497 P f u)) = ((term940 _93497 P t) = (term45 _93490 _93497 P f u)).
Proof. exact (MK_COMB (@lem3651988 _93497 P t) (@lem3651987 _93490 _93497 P f u)). Qed.
Lemma lem3651990 {_93497 : Type'} (P : type686 _93497) (t : _93497 -> Prop) : (term940 _93497 P t) = (P t).
Proof. exact (eq_refl (term940 _93497 P t)). Qed.
Lemma lem3651991 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3651992 {_93497 : Type'} (P : type686 _93497) (t : _93497 -> Prop) : (term942 _93497 P t) = (term943 _93497 P t).
Proof. exact (MK_COMB (@lem3651991) (@lem3651990 _93497 P t)). Qed.
Lemma lem3651993 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term45 _93490 _93497 P f u) = (term45 _93490 _93497 P f u).
Proof. exact (eq_refl (term45 _93490 _93497 P f u)). Qed.
Lemma lem3651994 {_93490 _93497 : Type'} (t : _93497 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (u : _93490 -> Prop) : ((term940 _93497 P t) = (term45 _93490 _93497 P f u)) = ((P t) = (term45 _93490 _93497 P f u)).
Proof. exact (MK_COMB (@lem3651992 _93497 P t) (@lem3651993 _93490 _93497 P f u)). Qed.
Lemma lem3651995 {_93490 _93497 : Type'} (t : _93497 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (u : _93490 -> Prop) : ((term940 _93497 P t) = (term941 _93490 _93497 P f u)) = ((P t) = (term45 _93490 _93497 P f u)).
Proof. exact (TRANS (@lem3651989 _93490 _93497 t P f u) (@lem3651994 _93490 _93497 t P f u)). Qed.
Lemma lem3651996 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : (P t) = (term45 _93490 _93497 P f u).
Proof. exact (EQ_MP (@lem3651995 _93490 _93497 t P f u) (@lem3651986 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3652039 {_93490 _93497 : Type'} (_40050 : _93490) (_40051 : _93490) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term918 _93490 _93497 u f _40050 _40051.
Proof. exact (EQ_MP (@lem3651797 _93490 _93497 u f _40050 _40051) (@lem3651745 _93490 _93497 _40050 _40051 u t s x y P f h1)). Qed.
Lemma lem3652053 {_93490 _93497 : Type'} (_40049 : _93490 -> Prop) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term921 _93490 _93497 s x y P f _40049.
Proof. exact (EQ_MP (@lem3651813 _93490 _93497 s x y P f _40049) (@lem3651750 _93490 _93497 _40049 u t s x y P f h1)). Qed.
Lemma lem3652067 {_93490 _93497 : Type'} (_40049 : _93490 -> Prop) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term923 _93490 _93497 s x y P f _40049.
Proof. exact (EQ_MP (@lem3651829 _93490 _93497 s x y P f _40049) (@lem3651749 _93490 _93497 _40049 u t s x y P f h1)). Qed.
Lemma lem3652081 {_93490 _93497 : Type'} (_40049 : _93490 -> Prop) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term944 _93490 _93497 s x P f _40049.
Proof. exact (proj1 (@lem3651748 _93490 _93497 _40049 u t s x y P f h1)). Qed.
Lemma lem3652095 {_93490 _93497 : Type'} (_40049 : _93490 -> Prop) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term944 _93490 _93497 s y P f _40049.
Proof. exact (proj2 (@lem3651748 _93490 _93497 _40049 u t s x y P f h1)). Qed.
Lemma lem3652162 {_93490 _93497 : Type'} : (@I (_93490 -> _93497)) = (@I (_93490 -> _93497)).
Proof. exact (eq_refl (@I (_93490 -> _93497))). Qed.
Lemma lem3652163 {_93490 _93497 : Type'} (_40088 : _93490 -> _93497) (_40090 : _93490 -> _93497) (h1 : _40088 = _40090) : _40088 = _40090.
Proof. exact (h1). Qed.
Lemma lem3652164 {_93490 : Type'} (_40089 : _93490) (_40091 : _93490) (h1 : _40089 = _40091) : _40089 = _40091.
Proof. exact (h1). Qed.
Lemma lem3652165 {_93490 _93497 : Type'} (_40088 : _93490 -> _93497) (_40090 : _93490 -> _93497) (h1 : _40088 = _40090) : (@I (_93490 -> _93497) _40088) = (@I (_93490 -> _93497) _40090).
Proof. exact (MK_COMB (@lem3652162 _93490 _93497) (@lem3652163 _93490 _93497 _40088 _40090 h1)). Qed.
Lemma lem3652166 {_93490 _93497 : Type'} (_40089 : _93490) (_40091 : _93490) (_40088 : _93490 -> _93497) (_40090 : _93490 -> _93497) (h1 : _40089 = _40091) (h2 : _40088 = _40090) : (@I (_93490 -> _93497) _40088 _40089) = (@I (_93490 -> _93497) _40090 _40091).
Proof. exact (MK_COMB (@lem3652165 _93490 _93497 _40088 _40090 h2) (@lem3652164 _93490 _40089 _40091 h1)). Qed.
Lemma lem3652167 {_93490 _93497 : Type'} (_40088 : _93490 -> _93497) (_40090 : _93490 -> _93497) (_40089 : _93490) (_40091 : _93490) (h1 : _40089 = _40091) : term945 _93490 _93497 _40088 _40089 _40090 _40091.
Proof. exact (fun h0 : _40088 = _40090 => @lem3652166 _93490 _93497 _40089 _40091 _40088 _40090 h1 h0). Qed.
Lemma lem3652169 (a : Prop) (b : Prop) : (a -> b) = (term946 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3652170 {_93490 _93497 : Type'} (_40088 : _93490 -> _93497) (_40089 : _93490) (_40090 : _93490 -> _93497) (_40091 : _93490) : (term945 _93490 _93497 _40088 _40089 _40090 _40091) = (term947 _93490 _93497 _40088 _40089 _40090 _40091).
Proof. exact (@lem3652169 (_40088 = _40090) ((@I (_93490 -> _93497) _40088 _40089) = (@I (_93490 -> _93497) _40090 _40091))). Qed.
Lemma lem3652171 {_93490 _93497 : Type'} (_40088 : _93490 -> _93497) (_40090 : _93490 -> _93497) (_40089 : _93490) (_40091 : _93490) (h1 : _40089 = _40091) : term947 _93490 _93497 _40088 _40089 _40090 _40091.
Proof. exact (EQ_MP (@lem3652170 _93490 _93497 _40088 _40089 _40090 _40091) (@lem3652167 _93490 _93497 _40088 _40090 _40089 _40091 h1)). Qed.
Lemma lem3652172 {_93490 _93497 : Type'} (_40088 : _93490 -> _93497) (_40089 : _93490) (_40090 : _93490 -> _93497) (_40091 : _93490) : term948 _93490 _93497 _40088 _40089 _40090 _40091.
Proof. exact (fun h0 : _40089 = _40091 => @lem3652171 _93490 _93497 _40088 _40090 _40089 _40091 h0). Qed.
Lemma lem3652174 (a : Prop) (b : Prop) : (a -> b) = (term946 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3652175 {_93490 _93497 : Type'} (_40088 : _93490 -> _93497) (_40089 : _93490) (_40090 : _93490 -> _93497) (_40091 : _93490) : (term948 _93490 _93497 _40088 _40089 _40090 _40091) = (term949 _93490 _93497 _40088 _40089 _40090 _40091).
Proof. exact (@lem3652174 (_40089 = _40091) (term947 _93490 _93497 _40088 _40089 _40090 _40091)). Qed.
Lemma lem3652176 {_93490 _93497 : Type'} (_40088 : _93490 -> _93497) (_40089 : _93490) (_40090 : _93490 -> _93497) (_40091 : _93490) : term949 _93490 _93497 _40088 _40089 _40090 _40091.
Proof. exact (EQ_MP (@lem3652175 _93490 _93497 _40088 _40089 _40090 _40091) (@lem3652172 _93490 _93497 _40088 _40089 _40090 _40091)). Qed.
Lemma lem3652203 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : @SUBSET _93490 u s.
Proof. exact (proj1 (@lem3651394 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3652204 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term950 _93490 u s.
Proof. exact (fun h0 : term227 _93490 u s => @lem3652203 _93490 _93497 u t s x y P f h1). Qed.
Lemma lem3652206 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3652207 {_93490 : Type'} (u : _93490 -> Prop) (s : _93490 -> Prop) : (term950 _93490 u s) = (@SUBSET _93490 u s).
Proof. exact (@lem3652206 (@SUBSET _93490 u s)). Qed.
Lemma lem3652208 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : @SUBSET _93490 u s.
Proof. exact (EQ_MP (@lem3652207 _93490 u s) (@lem3652204 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3652210 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : @SUBSET _93490 u s.
Proof. exact (proj1 (@lem3651394 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3652211 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term950 _93490 u s.
Proof. exact (fun h0 : term227 _93490 u s => @lem3652210 _93490 _93497 u t s x y P f h1). Qed.
Lemma lem3652213 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3652214 {_93490 : Type'} (u : _93490 -> Prop) (s : _93490 -> Prop) : (term950 _93490 u s) = (@SUBSET _93490 u s).
Proof. exact (@lem3652213 (@SUBSET _93490 u s)). Qed.
Lemma lem3652215 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : @SUBSET _93490 u s.
Proof. exact (EQ_MP (@lem3652214 _93490 u s) (@lem3652211 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3652218 {_93490 _93497 : Type'} (x : type684 _93490) (f : _93490 -> _93497) (y : type684 _93490) (u : _93490 -> Prop) (h1 : term787 _93490 _93497 x f y u) : term787 _93490 _93497 x f y u.
Proof. exact (h1). Qed.
Lemma lem3652219 {_93490 _93497 : Type'} (x : type684 _93490) (f : _93490 -> _93497) (y : type684 _93490) (u : _93490 -> Prop) (h1 : term787 _93490 _93497 x f y u) : term952 _93490 _93497 x f y u.
Proof. exact (fun h0 : (term783 _93490 _93497 f x u) = (term783 _93490 _93497 f y u) => @lem3652218 _93490 _93497 x f y u h1). Qed.
Lemma lem3652221 (p : Prop) : (term953 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3652222 {_93490 _93497 : Type'} (x : type684 _93490) (f : _93490 -> _93497) (y : type684 _93490) (u : _93490 -> Prop) : (term952 _93490 _93497 x f y u) = (term787 _93490 _93497 x f y u).
Proof. exact (@lem3652221 ((term783 _93490 _93497 f x u) = (term783 _93490 _93497 f y u))). Qed.
Lemma lem3652223 {_93490 _93497 : Type'} (x : type684 _93490) (f : _93490 -> _93497) (y : type684 _93490) (u : _93490 -> Prop) (h1 : term787 _93490 _93497 x f y u) : term787 _93490 _93497 x f y u.
Proof. exact (EQ_MP (@lem3652222 _93490 _93497 x f y u) (@lem3652219 _93490 _93497 x f y u h1)). Qed.
Lemma lem3652225 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term45 _93490 _93497 P f u.
Proof. exact (EQ_MP (@lem3651996 _93490 _93497 u t s x y P f h1) (@lem3651762 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3652226 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term954 _93490 _93497 P f u.
Proof. exact (fun h0 : term136 _93490 _93497 P f u => @lem3652225 _93490 _93497 u t s x y P f h1). Qed.
Lemma lem3652228 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3652229 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term954 _93490 _93497 P f u) = (term45 _93490 _93497 P f u).
Proof. exact (@lem3652228 (term45 _93490 _93497 P f u)). Qed.
Lemma lem3652230 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term45 _93490 _93497 P f u.
Proof. exact (EQ_MP (@lem3652229 _93490 _93497 P f u) (@lem3652226 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3652236 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3652237 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term921 _93490 _93497 s x y P f _40049) = (term955 _93490 _93497 s x y P f _40049).
Proof. exact (@lem3652236 ((term783 _93490 _93497 f x _40049) = (term783 _93490 _93497 f y _40049)) (term227 _93490 _40049 s) (term956 _93490 _93497 x y P f _40049)). Qed.
Lemma lem3652253 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3652254 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term957 _93490 _93497 s x y P f _40049) = (term958 _93490 _93497 x y s P f _40049).
Proof. exact (@lem3652253 ((x _40049) = (y _40049)) (term227 _93490 _40049 s) (term136 _93490 _93497 P f _40049)). Qed.
Lemma lem3652270 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3652271 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term959 _93490 _93497 s P f _40049) = (term960 _93490 _93497 P f _40049 s).
Proof. exact (@lem3652270 (term136 _93490 _93497 P f _40049) (term227 _93490 _40049 s)). Qed.
Lemma lem3652277 {_93490 : Type'} (x : type684 _93490) (y : type684 _93490) (_40049 : _93490 -> Prop) : (term961 _93490 x y _40049) = (term961 _93490 x y _40049).
Proof. exact (eq_refl (term961 _93490 x y _40049)). Qed.
Lemma lem3652278 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term958 _93490 _93497 x y s P f _40049) = (term962 _93490 _93497 x y P f _40049 s).
Proof. exact (MK_COMB (@lem3652277 _93490 x y _40049) (@lem3652271 _93490 _93497 P f _40049 s)). Qed.
Lemma lem3652289 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term957 _93490 _93497 s x y P f _40049) = (term962 _93490 _93497 x y P f _40049 s).
Proof. exact (TRANS (@lem3652254 _93490 _93497 x y s P f _40049) (@lem3652278 _93490 _93497 x y P f _40049 s)). Qed.
Lemma lem3652290 {_93490 _93497 : Type'} (x : type684 _93490) (f : _93490 -> _93497) (y : type684 _93490) (_40049 : _93490 -> Prop) : (term793 _93490 _93497 x f y _40049) = (term793 _93490 _93497 x f y _40049).
Proof. exact (eq_refl (term793 _93490 _93497 x f y _40049)). Qed.
Lemma lem3652291 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term955 _93490 _93497 s x y P f _40049) = (term963 _93490 _93497 x y P f _40049 s).
Proof. exact (MK_COMB (@lem3652290 _93490 _93497 x f y _40049) (@lem3652289 _93490 _93497 x y P f _40049 s)). Qed.
Lemma lem3652295 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3652296 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term963 _93490 _93497 x y P f _40049 s) = (term964 _93490 _93497 x y P f _40049 s).
Proof. exact (@lem3652295 ((x _40049) = (y _40049)) ((term783 _93490 _93497 f x _40049) = (term783 _93490 _93497 f y _40049)) (term960 _93490 _93497 P f _40049 s)). Qed.
Lemma lem3652326 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term955 _93490 _93497 s x y P f _40049) = (term964 _93490 _93497 x y P f _40049 s).
Proof. exact (TRANS (@lem3652291 _93490 _93497 x y P f _40049 s) (@lem3652296 _93490 _93497 x y P f _40049 s)). Qed.
Lemma lem3652327 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term921 _93490 _93497 s x y P f _40049) = (term964 _93490 _93497 x y P f _40049 s).
Proof. exact (TRANS (@lem3652237 _93490 _93497 s x y P f _40049) (@lem3652326 _93490 _93497 x y P f _40049 s)). Qed.
Lemma lem3652328 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3652329 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term965 _93490 _93497 s x y P f _40049) = (term966 _93490 _93497 x y P f _40049 s).
Proof. exact (MK_COMB (@lem3652328) (@lem3652327 _93490 _93497 x y P f _40049 s)). Qed.
Lemma lem3652345 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3652346 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term967 _93490 _93497 s x y P f _40049) = (term968 _93490 _93497 x y s P f _40049).
Proof. exact (@lem3652345 ((term783 _93490 _93497 f x _40049) = (term783 _93490 _93497 f y _40049)) (term227 _93490 _40049 s) (term136 _93490 _93497 P f _40049)). Qed.
Lemma lem3652362 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3652363 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term959 _93490 _93497 s P f _40049) = (term960 _93490 _93497 P f _40049 s).
Proof. exact (@lem3652362 (term136 _93490 _93497 P f _40049) (term227 _93490 _40049 s)). Qed.
Lemma lem3652369 {_93490 _93497 : Type'} (x : type684 _93490) (f : _93490 -> _93497) (y : type684 _93490) (_40049 : _93490 -> Prop) : (term793 _93490 _93497 x f y _40049) = (term793 _93490 _93497 x f y _40049).
Proof. exact (eq_refl (term793 _93490 _93497 x f y _40049)). Qed.
Lemma lem3652370 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term968 _93490 _93497 x y s P f _40049) = (term969 _93490 _93497 x y P f _40049 s).
Proof. exact (MK_COMB (@lem3652369 _93490 _93497 x f y _40049) (@lem3652363 _93490 _93497 P f _40049 s)). Qed.
Lemma lem3652381 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term967 _93490 _93497 s x y P f _40049) = (term969 _93490 _93497 x y P f _40049 s).
Proof. exact (TRANS (@lem3652346 _93490 _93497 x y s P f _40049) (@lem3652370 _93490 _93497 x y P f _40049 s)). Qed.
Lemma lem3652382 {_93490 : Type'} (x : type684 _93490) (y : type684 _93490) (_40049 : _93490 -> Prop) : (term961 _93490 x y _40049) = (term961 _93490 x y _40049).
Proof. exact (eq_refl (term961 _93490 x y _40049)). Qed.
Lemma lem3652383 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term970 _93490 _93497 s x y P f _40049) = (term964 _93490 _93497 x y P f _40049 s).
Proof. exact (MK_COMB (@lem3652382 _93490 x y _40049) (@lem3652381 _93490 _93497 x y P f _40049 s)). Qed.
Lemma lem3652394 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : ((term921 _93490 _93497 s x y P f _40049) = (term970 _93490 _93497 s x y P f _40049)) = ((term964 _93490 _93497 x y P f _40049 s) = (term964 _93490 _93497 x y P f _40049 s)).
Proof. exact (MK_COMB (@lem3652329 _93490 _93497 x y P f _40049 s) (@lem3652383 _93490 _93497 x y P f _40049 s)). Qed.
Lemma lem3652396 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3652397 (x : Prop) : (x = x) = True.
Proof. exact (@lem3652396 Prop x). Qed.
Lemma lem3652398 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : ((term964 _93490 _93497 x y P f _40049 s) = (term964 _93490 _93497 x y P f _40049 s)) = True.
Proof. exact (@lem3652397 (term964 _93490 _93497 x y P f _40049 s)). Qed.
Lemma lem3652399 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : ((term921 _93490 _93497 s x y P f _40049) = (term970 _93490 _93497 s x y P f _40049)) = True.
Proof. exact (TRANS (@lem3652394 _93490 _93497 x y P f _40049 s) (@lem3652398 _93490 _93497 x y P f _40049 s)). Qed.
Lemma lem3652400 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : True = ((term921 _93490 _93497 s x y P f _40049) = (term970 _93490 _93497 s x y P f _40049)).
Proof. exact (SYM (@lem3652399 _93490 _93497 s x y P f _40049)). Qed.
Lemma lem3652401 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term921 _93490 _93497 s x y P f _40049) = (term970 _93490 _93497 s x y P f _40049).
Proof. exact (EQ_MP (@lem3652400 _93490 _93497 s x y P f _40049) (@lem0)). Qed.
Lemma lem3652402 {_93490 _93497 : Type'} (_40049 : _93490 -> Prop) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term970 _93490 _93497 s x y P f _40049.
Proof. exact (EQ_MP (@lem3652401 _93490 _93497 s x y P f _40049) (@lem3652053 _93490 _93497 _40049 u t s x y P f h1)). Qed.
Lemma lem3652404 (b : Prop) (a : Prop) : (a \/ b) = (term971 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3652405 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (x : type684 _93490) (y : type684 _93490) (_40049 : _93490 -> Prop) : (term970 _93490 _93497 s x y P f _40049) = (term972 _93490 _93497 s P f x y _40049).
Proof. exact (@lem3652404 (term967 _93490 _93497 s x y P f _40049) ((x _40049) = (y _40049))). Qed.
Lemma lem3652407 (a : Prop) (b : Prop) : (term973 a b) = (term974 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3652408 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term975 _93490 _93497 s x y P f _40049) = (term976 _93490 _93497 s x y P f _40049).
Proof. exact (@lem3652407 (term227 _93490 _40049 s) (term977 _93490 _93497 x y P f _40049)). Qed.
Lemma lem3652410 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3652411 {_93490 : Type'} (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term978 _93490 _40049 s) = (@SUBSET _93490 _40049 s).
Proof. exact (@lem3652410 (@SUBSET _93490 _40049 s)). Qed.
Lemma lem3652412 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3652413 {_93490 : Type'} (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term979 _93490 _40049 s) = (term53 _93490 _40049 s).
Proof. exact (MK_COMB (@lem3652412) (@lem3652411 _93490 _40049 s)). Qed.
Lemma lem3652415 (a : Prop) (b : Prop) : (term973 a b) = (term974 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3652416 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term980 _93490 _93497 x y P f _40049) = (term981 _93490 _93497 x y P f _40049).
Proof. exact (@lem3652415 ((term783 _93490 _93497 f x _40049) = (term783 _93490 _93497 f y _40049)) (term136 _93490 _93497 P f _40049)). Qed.
Lemma lem3652418 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3652419 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term982 _93490 _93497 P f _40049) = (term45 _93490 _93497 P f _40049).
Proof. exact (@lem3652418 (term45 _93490 _93497 P f _40049)). Qed.
Lemma lem3652420 {_93490 _93497 : Type'} (x : type684 _93490) (f : _93490 -> _93497) (y : type684 _93490) (_40049 : _93490 -> Prop) : (term983 _93490 _93497 x f y _40049) = (term983 _93490 _93497 x f y _40049).
Proof. exact (eq_refl (term983 _93490 _93497 x f y _40049)). Qed.
Lemma lem3652421 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term981 _93490 _93497 x y P f _40049) = (term984 _93490 _93497 x y P f _40049).
Proof. exact (MK_COMB (@lem3652420 _93490 _93497 x f y _40049) (@lem3652419 _93490 _93497 P f _40049)). Qed.
Lemma lem3652422 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term980 _93490 _93497 x y P f _40049) = (term984 _93490 _93497 x y P f _40049).
Proof. exact (TRANS (@lem3652416 _93490 _93497 x y P f _40049) (@lem3652421 _93490 _93497 x y P f _40049)). Qed.
Lemma lem3652423 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term976 _93490 _93497 s x y P f _40049) = (term985 _93490 _93497 s x y P f _40049).
Proof. exact (MK_COMB (@lem3652413 _93490 _40049 s) (@lem3652422 _93490 _93497 x y P f _40049)). Qed.
Lemma lem3652424 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term975 _93490 _93497 s x y P f _40049) = (term985 _93490 _93497 s x y P f _40049).
Proof. exact (TRANS (@lem3652408 _93490 _93497 s x y P f _40049) (@lem3652423 _93490 _93497 s x y P f _40049)). Qed.
Lemma lem3652425 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3652426 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term986 _93490 _93497 s x y P f _40049) = (term987 _93490 _93497 s x y P f _40049).
Proof. exact (MK_COMB (@lem3652425) (@lem3652424 _93490 _93497 s x y P f _40049)). Qed.
Lemma lem3652427 {_93490 : Type'} (x : type684 _93490) (y : type684 _93490) (_40049 : _93490 -> Prop) : ((x _40049) = (y _40049)) = ((x _40049) = (y _40049)).
Proof. exact (eq_refl ((x _40049) = (y _40049))). Qed.
Lemma lem3652428 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (x : type684 _93490) (y : type684 _93490) (_40049 : _93490 -> Prop) : (term972 _93490 _93497 s P f x y _40049) = (term988 _93490 _93497 s P f x y _40049).
Proof. exact (MK_COMB (@lem3652426 _93490 _93497 s x y P f _40049) (@lem3652427 _93490 x y _40049)). Qed.
Lemma lem3652429 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (x : type684 _93490) (y : type684 _93490) (_40049 : _93490 -> Prop) : (term970 _93490 _93497 s x y P f _40049) = (term988 _93490 _93497 s P f x y _40049).
Proof. exact (TRANS (@lem3652405 _93490 _93497 s P f x y _40049) (@lem3652428 _93490 _93497 s P f x y _40049)). Qed.
Lemma lem3652431 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term787 _93490 _93497 x f y u) (h2 : term815 _93490 _93497 u t s x y P f) : term984 _93490 _93497 x y P f u.
Proof. exact (conj (@lem3652223 _93490 _93497 x f y u h1) (@lem3652230 _93490 _93497 u t s x y P f h2)). Qed.
Lemma lem3652432 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term787 _93490 _93497 x f y u) (h2 : term815 _93490 _93497 u t s x y P f) : term985 _93490 _93497 s x y P f u.
Proof. exact (conj (@lem3652215 _93490 _93497 u t s x y P f h2) (@lem3652431 _93490 _93497 u t s x y P f h1 h2)). Qed.
Lemma lem3652434 {_93490 _93497 : Type'} (_40049 : _93490 -> Prop) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term988 _93490 _93497 s P f x y _40049.
Proof. exact (EQ_MP (@lem3652429 _93490 _93497 s P f x y _40049) (@lem3652402 _93490 _93497 _40049 u t s x y P f h1)). Qed.
Lemma lem3652435 {_93490 _93497 : Type'} (_40049 : _93490 -> Prop) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term988 _93490 _93497 s P f x y _40049.
Proof. exact (@lem3652434 _93490 _93497 _40049 u t s x y P f h1). Qed.
Lemma lem3652436 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term988 _93490 _93497 s P f x y u.
Proof. exact (@lem3652435 _93490 _93497 u u t s x y P f h1). Qed.
Lemma lem3652439 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term787 _93490 _93497 x f y u) (h2 : term815 _93490 _93497 u t s x y P f) : (x u) = (y u).
Proof. exact (@lem3652436 _93490 _93497 u t s x y P f h2 (@lem3652432 _93490 _93497 u t s x y P f h1 h2)). Qed.
Lemma lem3652440 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term787 _93490 _93497 x f y u) (h2 : term815 _93490 _93497 u t s x y P f) : term989 _93490 x y u.
Proof. exact (fun h0 : term781 _93490 x y u => @lem3652439 _93490 _93497 u t s x y P f h1 h2). Qed.
Lemma lem3652442 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3652443 {_93490 : Type'} (x : type684 _93490) (y : type684 _93490) (u : _93490 -> Prop) : (term989 _93490 x y u) = ((x u) = (y u)).
Proof. exact (@lem3652442 ((x u) = (y u))). Qed.
Lemma lem3652444 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term787 _93490 _93497 x f y u) (h2 : term815 _93490 _93497 u t s x y P f) : (x u) = (y u).
Proof. exact (EQ_MP (@lem3652443 _93490 x y u) (@lem3652440 _93490 _93497 u t s x y P f h1 h2)). Qed.
Lemma lem3652446 {_93490 _93497 : Type'} (x : _93490 -> _93497) : x = x.
Proof. exact (@lem21386 (_93490 -> _93497) x). Qed.
Lemma lem3652447 {_93490 _93497 : Type'} (x : _93490 -> _93497) : x = x.
Proof. exact (@lem3652446 _93490 _93497 x). Qed.
Lemma lem3652448 {_93490 _93497 : Type'} (f : _93490 -> _93497) : f = f.
Proof. exact (@lem3652447 _93490 _93497 f). Qed.
Lemma lem3652449 {_93490 _93497 : Type'} (f : _93490 -> _93497) : term990 _93490 _93497 f.
Proof. exact (fun h0 : term991 _93490 _93497 f => @lem3652448 _93490 _93497 f). Qed.
Lemma lem3652451 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3652452 {_93490 _93497 : Type'} (f : _93490 -> _93497) : (term990 _93490 _93497 f) = (f = f).
Proof. exact (@lem3652451 (f = f)). Qed.
Lemma lem3652453 {_93490 _93497 : Type'} (f : _93490 -> _93497) : f = f.
Proof. exact (EQ_MP (@lem3652452 _93490 _93497 f) (@lem3652449 _93490 _93497 f)). Qed.
Lemma lem3652471 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3652472 {_93490 _93497 : Type'} (_40089 : _93490) (_40091 : _93490) (_40088 : _93490 -> _93497) (_40090 : _93490 -> _93497) : (term947 _93490 _93497 _40088 _40089 _40090 _40091) = (term992 _93490 _93497 _40089 _40091 _40088 _40090).
Proof. exact (@lem3652471 ((@I (_93490 -> _93497) _40088 _40089) = (@I (_93490 -> _93497) _40090 _40091)) (term993 _93490 _93497 _40088 _40090)). Qed.
Lemma lem3652482 {_93490 : Type'} (_40089 : _93490) (_40091 : _93490) : (term994 _93490 _40089 _40091) = (term994 _93490 _40089 _40091).
Proof. exact (eq_refl (term994 _93490 _40089 _40091)). Qed.
Lemma lem3652483 {_93490 _93497 : Type'} (_40089 : _93490) (_40091 : _93490) (_40088 : _93490 -> _93497) (_40090 : _93490 -> _93497) : (term949 _93490 _93497 _40088 _40089 _40090 _40091) = (term995 _93490 _93497 _40089 _40091 _40088 _40090).
Proof. exact (MK_COMB (@lem3652482 _93490 _40089 _40091) (@lem3652472 _93490 _93497 _40089 _40091 _40088 _40090)). Qed.
Lemma lem3652487 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3652488 {_93490 _93497 : Type'} (_40089 : _93490) (_40091 : _93490) (_40088 : _93490 -> _93497) (_40090 : _93490 -> _93497) : (term995 _93490 _93497 _40089 _40091 _40088 _40090) = (term996 _93490 _93497 _40089 _40091 _40088 _40090).
Proof. exact (@lem3652487 ((@I (_93490 -> _93497) _40088 _40089) = (@I (_93490 -> _93497) _40090 _40091)) (term726 _93490 _40089 _40091) (term993 _93490 _93497 _40088 _40090)). Qed.
Lemma lem3652510 {_93490 _93497 : Type'} (_40089 : _93490) (_40091 : _93490) (_40088 : _93490 -> _93497) (_40090 : _93490 -> _93497) : (term949 _93490 _93497 _40088 _40089 _40090 _40091) = (term996 _93490 _93497 _40089 _40091 _40088 _40090).
Proof. exact (TRANS (@lem3652483 _93490 _93497 _40089 _40091 _40088 _40090) (@lem3652488 _93490 _93497 _40089 _40091 _40088 _40090)). Qed.
Lemma lem3652511 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3652512 {_93490 _93497 : Type'} (_40089 : _93490) (_40091 : _93490) (_40088 : _93490 -> _93497) (_40090 : _93490 -> _93497) : (term997 _93490 _93497 _40088 _40089 _40090 _40091) = (term998 _93490 _93497 _40089 _40091 _40088 _40090).
Proof. exact (MK_COMB (@lem3652511) (@lem3652510 _93490 _93497 _40089 _40091 _40088 _40090)). Qed.
Lemma lem3652534 {_93490 _93497 : Type'} (_40089 : _93490) (_40091 : _93490) (_40088 : _93490 -> _93497) (_40090 : _93490 -> _93497) : (term996 _93490 _93497 _40089 _40091 _40088 _40090) = (term996 _93490 _93497 _40089 _40091 _40088 _40090).
Proof. exact (eq_refl (term996 _93490 _93497 _40089 _40091 _40088 _40090)). Qed.
Lemma lem3652535 {_93490 _93497 : Type'} (_40089 : _93490) (_40091 : _93490) (_40088 : _93490 -> _93497) (_40090 : _93490 -> _93497) : ((term949 _93490 _93497 _40088 _40089 _40090 _40091) = (term996 _93490 _93497 _40089 _40091 _40088 _40090)) = ((term996 _93490 _93497 _40089 _40091 _40088 _40090) = (term996 _93490 _93497 _40089 _40091 _40088 _40090)).
Proof. exact (MK_COMB (@lem3652512 _93490 _93497 _40089 _40091 _40088 _40090) (@lem3652534 _93490 _93497 _40089 _40091 _40088 _40090)). Qed.
Lemma lem3652537 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3652538 (x : Prop) : (x = x) = True.
Proof. exact (@lem3652537 Prop x). Qed.
Lemma lem3652539 {_93490 _93497 : Type'} (_40089 : _93490) (_40091 : _93490) (_40088 : _93490 -> _93497) (_40090 : _93490 -> _93497) : ((term996 _93490 _93497 _40089 _40091 _40088 _40090) = (term996 _93490 _93497 _40089 _40091 _40088 _40090)) = True.
Proof. exact (@lem3652538 (term996 _93490 _93497 _40089 _40091 _40088 _40090)). Qed.
Lemma lem3652540 {_93490 _93497 : Type'} (_40089 : _93490) (_40091 : _93490) (_40088 : _93490 -> _93497) (_40090 : _93490 -> _93497) : ((term949 _93490 _93497 _40088 _40089 _40090 _40091) = (term996 _93490 _93497 _40089 _40091 _40088 _40090)) = True.
Proof. exact (TRANS (@lem3652535 _93490 _93497 _40089 _40091 _40088 _40090) (@lem3652539 _93490 _93497 _40089 _40091 _40088 _40090)). Qed.
Lemma lem3652541 {_93490 _93497 : Type'} (_40089 : _93490) (_40091 : _93490) (_40088 : _93490 -> _93497) (_40090 : _93490 -> _93497) : True = ((term949 _93490 _93497 _40088 _40089 _40090 _40091) = (term996 _93490 _93497 _40089 _40091 _40088 _40090)).
Proof. exact (SYM (@lem3652540 _93490 _93497 _40089 _40091 _40088 _40090)). Qed.
Lemma lem3652542 {_93490 _93497 : Type'} (_40089 : _93490) (_40091 : _93490) (_40088 : _93490 -> _93497) (_40090 : _93490 -> _93497) : (term949 _93490 _93497 _40088 _40089 _40090 _40091) = (term996 _93490 _93497 _40089 _40091 _40088 _40090).
Proof. exact (EQ_MP (@lem3652541 _93490 _93497 _40089 _40091 _40088 _40090) (@lem0)). Qed.
Lemma lem3652543 {_93490 _93497 : Type'} (_40089 : _93490) (_40091 : _93490) (_40088 : _93490 -> _93497) (_40090 : _93490 -> _93497) : term996 _93490 _93497 _40089 _40091 _40088 _40090.
Proof. exact (EQ_MP (@lem3652542 _93490 _93497 _40089 _40091 _40088 _40090) (@lem3652176 _93490 _93497 _40088 _40089 _40090 _40091)). Qed.
Lemma lem3652545 (b : Prop) (a : Prop) : (a \/ b) = (term971 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3652546 {_93490 _93497 : Type'} (_40088 : _93490 -> _93497) (_40089 : _93490) (_40090 : _93490 -> _93497) (_40091 : _93490) : (term996 _93490 _93497 _40089 _40091 _40088 _40090) = (term999 _93490 _93497 _40088 _40089 _40090 _40091).
Proof. exact (@lem3652545 (term1000 _93490 _93497 _40089 _40091 _40088 _40090) ((@I (_93490 -> _93497) _40088 _40089) = (@I (_93490 -> _93497) _40090 _40091))). Qed.
Lemma lem3652548 (a : Prop) (b : Prop) : (term973 a b) = (term974 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3652549 {_93490 _93497 : Type'} (_40089 : _93490) (_40091 : _93490) (_40088 : _93490 -> _93497) (_40090 : _93490 -> _93497) : (term1001 _93490 _93497 _40089 _40091 _40088 _40090) = (term1002 _93490 _93497 _40089 _40091 _40088 _40090).
Proof. exact (@lem3652548 (term726 _93490 _40089 _40091) (term993 _93490 _93497 _40088 _40090)). Qed.
Lemma lem3652551 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3652552 {_93490 : Type'} (_40089 : _93490) (_40091 : _93490) : (term1003 _93490 _40089 _40091) = (_40089 = _40091).
Proof. exact (@lem3652551 (_40089 = _40091)). Qed.
Lemma lem3652553 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3652554 {_93490 : Type'} (_40089 : _93490) (_40091 : _93490) : (term1004 _93490 _40089 _40091) = (term1005 _93490 _40089 _40091).
Proof. exact (MK_COMB (@lem3652553) (@lem3652552 _93490 _40089 _40091)). Qed.
Lemma lem3652556 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3652557 {_93490 _93497 : Type'} (_40088 : _93490 -> _93497) (_40090 : _93490 -> _93497) : (term1006 _93490 _93497 _40088 _40090) = (_40088 = _40090).
Proof. exact (@lem3652556 (_40088 = _40090)). Qed.
Lemma lem3652558 {_93490 _93497 : Type'} (_40089 : _93490) (_40091 : _93490) (_40088 : _93490 -> _93497) (_40090 : _93490 -> _93497) : (term1002 _93490 _93497 _40089 _40091 _40088 _40090) = (term1007 _93490 _93497 _40089 _40091 _40088 _40090).
Proof. exact (MK_COMB (@lem3652554 _93490 _40089 _40091) (@lem3652557 _93490 _93497 _40088 _40090)). Qed.
Lemma lem3652559 {_93490 _93497 : Type'} (_40089 : _93490) (_40091 : _93490) (_40088 : _93490 -> _93497) (_40090 : _93490 -> _93497) : (term1001 _93490 _93497 _40089 _40091 _40088 _40090) = (term1007 _93490 _93497 _40089 _40091 _40088 _40090).
Proof. exact (TRANS (@lem3652549 _93490 _93497 _40089 _40091 _40088 _40090) (@lem3652558 _93490 _93497 _40089 _40091 _40088 _40090)). Qed.
Lemma lem3652560 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3652561 {_93490 _93497 : Type'} (_40089 : _93490) (_40091 : _93490) (_40088 : _93490 -> _93497) (_40090 : _93490 -> _93497) : (term1008 _93490 _93497 _40089 _40091 _40088 _40090) = (term1009 _93490 _93497 _40089 _40091 _40088 _40090).
Proof. exact (MK_COMB (@lem3652560) (@lem3652559 _93490 _93497 _40089 _40091 _40088 _40090)). Qed.
Lemma lem3652562 {_93490 _93497 : Type'} (_40088 : _93490 -> _93497) (_40089 : _93490) (_40090 : _93490 -> _93497) (_40091 : _93490) : ((@I (_93490 -> _93497) _40088 _40089) = (@I (_93490 -> _93497) _40090 _40091)) = ((@I (_93490 -> _93497) _40088 _40089) = (@I (_93490 -> _93497) _40090 _40091)).
Proof. exact (eq_refl ((@I (_93490 -> _93497) _40088 _40089) = (@I (_93490 -> _93497) _40090 _40091))). Qed.
Lemma lem3652563 {_93490 _93497 : Type'} (_40088 : _93490 -> _93497) (_40089 : _93490) (_40090 : _93490 -> _93497) (_40091 : _93490) : (term999 _93490 _93497 _40088 _40089 _40090 _40091) = (term1010 _93490 _93497 _40088 _40089 _40090 _40091).
Proof. exact (MK_COMB (@lem3652561 _93490 _93497 _40089 _40091 _40088 _40090) (@lem3652562 _93490 _93497 _40088 _40089 _40090 _40091)). Qed.
Lemma lem3652564 {_93490 _93497 : Type'} (_40088 : _93490 -> _93497) (_40089 : _93490) (_40090 : _93490 -> _93497) (_40091 : _93490) : (term996 _93490 _93497 _40089 _40091 _40088 _40090) = (term1010 _93490 _93497 _40088 _40089 _40090 _40091).
Proof. exact (TRANS (@lem3652546 _93490 _93497 _40088 _40089 _40090 _40091) (@lem3652563 _93490 _93497 _40088 _40089 _40090 _40091)). Qed.
Lemma lem3652566 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term787 _93490 _93497 x f y u) (h2 : term815 _93490 _93497 u t s x y P f) : term1011 _93490 _93497 x y u f.
Proof. exact (conj (@lem3652444 _93490 _93497 u t s x y P f h1 h2) (@lem3652453 _93490 _93497 f)). Qed.
Lemma lem3652568 {_93490 _93497 : Type'} (_40088 : _93490 -> _93497) (_40089 : _93490) (_40090 : _93490 -> _93497) (_40091 : _93490) : term1010 _93490 _93497 _40088 _40089 _40090 _40091.
Proof. exact (EQ_MP (@lem3652564 _93490 _93497 _40088 _40089 _40090 _40091) (@lem3652543 _93490 _93497 _40089 _40091 _40088 _40090)). Qed.
Lemma lem3652569 {_93490 _93497 : Type'} (_40088 : _93490 -> _93497) (_40089 : _93490) (_40090 : _93490 -> _93497) (_40091 : _93490) : term1010 _93490 _93497 _40088 _40089 _40090 _40091.
Proof. exact (@lem3652568 _93490 _93497 _40088 _40089 _40090 _40091). Qed.
Lemma lem3652570 {_93490 _93497 : Type'} (x : type684 _93490) (f : _93490 -> _93497) (y : type684 _93490) (u : _93490 -> Prop) : term1012 _93490 _93497 x f y u.
Proof. exact (@lem3652569 _93490 _93497 f (x u) f (y u)). Qed.
Lemma lem3652573 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term787 _93490 _93497 x f y u) (h2 : term815 _93490 _93497 u t s x y P f) : (term783 _93490 _93497 f x u) = (term783 _93490 _93497 f y u).
Proof. exact (@lem3652570 _93490 _93497 x f y u (@lem3652566 _93490 _93497 u t s x y P f h1 h2)). Qed.
Lemma lem3652574 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term1013 _93490 _93497 x f y u.
Proof. exact (fun h0 : term787 _93490 _93497 x f y u => @lem3652573 _93490 _93497 u t s x y P f h0 h1). Qed.
Lemma lem3652576 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3652577 {_93490 _93497 : Type'} (x : type684 _93490) (f : _93490 -> _93497) (y : type684 _93490) (u : _93490 -> Prop) : (term1013 _93490 _93497 x f y u) = ((term783 _93490 _93497 f x u) = (term783 _93490 _93497 f y u)).
Proof. exact (@lem3652576 ((term783 _93490 _93497 f x u) = (term783 _93490 _93497 f y u))). Qed.
Lemma lem3652578 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : (term783 _93490 _93497 f x u) = (term783 _93490 _93497 f y u).
Proof. exact (EQ_MP (@lem3652577 _93490 _93497 x f y u) (@lem3652574 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3652580 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : @SUBSET _93490 u s.
Proof. exact (proj1 (@lem3651394 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3652581 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term950 _93490 u s.
Proof. exact (fun h0 : term227 _93490 u s => @lem3652580 _93490 _93497 u t s x y P f h1). Qed.
Lemma lem3652583 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3652584 {_93490 : Type'} (u : _93490 -> Prop) (s : _93490 -> Prop) : (term950 _93490 u s) = (@SUBSET _93490 u s).
Proof. exact (@lem3652583 (@SUBSET _93490 u s)). Qed.
Lemma lem3652585 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : @SUBSET _93490 u s.
Proof. exact (EQ_MP (@lem3652584 _93490 u s) (@lem3652581 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3652587 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term45 _93490 _93497 P f u.
Proof. exact (EQ_MP (@lem3651996 _93490 _93497 u t s x y P f h1) (@lem3651762 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3652588 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term954 _93490 _93497 P f u.
Proof. exact (fun h0 : term136 _93490 _93497 P f u => @lem3652587 _93490 _93497 u t s x y P f h1). Qed.
Lemma lem3652590 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3652591 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term954 _93490 _93497 P f u) = (term45 _93490 _93497 P f u).
Proof. exact (@lem3652590 (term45 _93490 _93497 P f u)). Qed.
Lemma lem3652592 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term45 _93490 _93497 P f u.
Proof. exact (EQ_MP (@lem3652591 _93490 _93497 P f u) (@lem3652588 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3652598 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3652599 {_93490 _93497 : Type'} (x : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term944 _93490 _93497 s x P f _40049) = (term1014 _93490 _93497 x s P f _40049).
Proof. exact (@lem3652598 (term824 _93490 x _40049) (term227 _93490 _40049 s) (term136 _93490 _93497 P f _40049)). Qed.
Lemma lem3652613 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3652614 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term959 _93490 _93497 s P f _40049) = (term960 _93490 _93497 P f _40049 s).
Proof. exact (@lem3652613 (term136 _93490 _93497 P f _40049) (term227 _93490 _40049 s)). Qed.
Lemma lem3652620 {_93490 : Type'} (x : type684 _93490) (_40049 : _93490 -> Prop) : (term1015 _93490 x _40049) = (term1015 _93490 x _40049).
Proof. exact (eq_refl (term1015 _93490 x _40049)). Qed.
Lemma lem3652621 {_93490 _93497 : Type'} (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term1014 _93490 _93497 x s P f _40049) = (term1016 _93490 _93497 x P f _40049 s).
Proof. exact (MK_COMB (@lem3652620 _93490 x _40049) (@lem3652614 _93490 _93497 P f _40049 s)). Qed.
Lemma lem3652632 {_93490 _93497 : Type'} (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term944 _93490 _93497 s x P f _40049) = (term1016 _93490 _93497 x P f _40049 s).
Proof. exact (TRANS (@lem3652599 _93490 _93497 x s P f _40049) (@lem3652621 _93490 _93497 x P f _40049 s)). Qed.
Lemma lem3652633 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3652634 {_93490 _93497 : Type'} (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term1017 _93490 _93497 s x P f _40049) = (term1018 _93490 _93497 x P f _40049 s).
Proof. exact (MK_COMB (@lem3652633) (@lem3652632 _93490 _93497 x P f _40049 s)). Qed.
Lemma lem3652648 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3652649 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term959 _93490 _93497 s P f _40049) = (term960 _93490 _93497 P f _40049 s).
Proof. exact (@lem3652648 (term136 _93490 _93497 P f _40049) (term227 _93490 _40049 s)). Qed.
Lemma lem3652655 {_93490 : Type'} (x : type684 _93490) (_40049 : _93490 -> Prop) : (term1015 _93490 x _40049) = (term1015 _93490 x _40049).
Proof. exact (eq_refl (term1015 _93490 x _40049)). Qed.
Lemma lem3652656 {_93490 _93497 : Type'} (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term1014 _93490 _93497 x s P f _40049) = (term1016 _93490 _93497 x P f _40049 s).
Proof. exact (MK_COMB (@lem3652655 _93490 x _40049) (@lem3652649 _93490 _93497 P f _40049 s)). Qed.
Lemma lem3652667 {_93490 _93497 : Type'} (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : ((term944 _93490 _93497 s x P f _40049) = (term1014 _93490 _93497 x s P f _40049)) = ((term1016 _93490 _93497 x P f _40049 s) = (term1016 _93490 _93497 x P f _40049 s)).
Proof. exact (MK_COMB (@lem3652634 _93490 _93497 x P f _40049 s) (@lem3652656 _93490 _93497 x P f _40049 s)). Qed.
Lemma lem3652669 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3652670 (x : Prop) : (x = x) = True.
Proof. exact (@lem3652669 Prop x). Qed.
Lemma lem3652671 {_93490 _93497 : Type'} (x : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : ((term1016 _93490 _93497 x P f _40049 s) = (term1016 _93490 _93497 x P f _40049 s)) = True.
Proof. exact (@lem3652670 (term1016 _93490 _93497 x P f _40049 s)). Qed.
Lemma lem3652672 {_93490 _93497 : Type'} (x : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : ((term944 _93490 _93497 s x P f _40049) = (term1014 _93490 _93497 x s P f _40049)) = True.
Proof. exact (TRANS (@lem3652667 _93490 _93497 x P f _40049 s) (@lem3652671 _93490 _93497 x P f _40049 s)). Qed.
Lemma lem3652673 {_93490 _93497 : Type'} (x : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : True = ((term944 _93490 _93497 s x P f _40049) = (term1014 _93490 _93497 x s P f _40049)).
Proof. exact (SYM (@lem3652672 _93490 _93497 x s P f _40049)). Qed.
Lemma lem3652674 {_93490 _93497 : Type'} (x : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term944 _93490 _93497 s x P f _40049) = (term1014 _93490 _93497 x s P f _40049).
Proof. exact (EQ_MP (@lem3652673 _93490 _93497 x s P f _40049) (@lem0)). Qed.
Lemma lem3652675 {_93490 _93497 : Type'} (_40049 : _93490 -> Prop) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term1014 _93490 _93497 x s P f _40049.
Proof. exact (EQ_MP (@lem3652674 _93490 _93497 x s P f _40049) (@lem3652081 _93490 _93497 _40049 u t s x y P f h1)). Qed.
Lemma lem3652677 (b : Prop) (a : Prop) : (a \/ b) = (term971 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3652678 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (x : type684 _93490) (_40049 : _93490 -> Prop) : (term1014 _93490 _93497 x s P f _40049) = (term1019 _93490 _93497 s P f x _40049).
Proof. exact (@lem3652677 (term959 _93490 _93497 s P f _40049) (term824 _93490 x _40049)). Qed.
Lemma lem3652680 (a : Prop) (b : Prop) : (term973 a b) = (term974 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3652681 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term1020 _93490 _93497 s P f _40049) = (term1021 _93490 _93497 s P f _40049).
Proof. exact (@lem3652680 (term227 _93490 _40049 s) (term136 _93490 _93497 P f _40049)). Qed.
Lemma lem3652683 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3652684 {_93490 : Type'} (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term978 _93490 _40049 s) = (@SUBSET _93490 _40049 s).
Proof. exact (@lem3652683 (@SUBSET _93490 _40049 s)). Qed.
Lemma lem3652685 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3652686 {_93490 : Type'} (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term979 _93490 _40049 s) = (term53 _93490 _40049 s).
Proof. exact (MK_COMB (@lem3652685) (@lem3652684 _93490 _40049 s)). Qed.
Lemma lem3652688 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3652689 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term982 _93490 _93497 P f _40049) = (term45 _93490 _93497 P f _40049).
Proof. exact (@lem3652688 (term45 _93490 _93497 P f _40049)). Qed.
Lemma lem3652690 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term1021 _93490 _93497 s P f _40049) = (term1022 _93490 _93497 s P f _40049).
Proof. exact (MK_COMB (@lem3652686 _93490 _40049 s) (@lem3652689 _93490 _93497 P f _40049)). Qed.
Lemma lem3652691 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term1020 _93490 _93497 s P f _40049) = (term1022 _93490 _93497 s P f _40049).
Proof. exact (TRANS (@lem3652681 _93490 _93497 s P f _40049) (@lem3652690 _93490 _93497 s P f _40049)). Qed.
Lemma lem3652692 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3652693 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term1023 _93490 _93497 s P f _40049) = (term1024 _93490 _93497 s P f _40049).
Proof. exact (MK_COMB (@lem3652692) (@lem3652691 _93490 _93497 s P f _40049)). Qed.
Lemma lem3652694 {_93490 : Type'} (x : type684 _93490) (_40049 : _93490 -> Prop) : (term824 _93490 x _40049) = (term824 _93490 x _40049).
Proof. exact (eq_refl (term824 _93490 x _40049)). Qed.
Lemma lem3652695 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (x : type684 _93490) (_40049 : _93490 -> Prop) : (term1019 _93490 _93497 s P f x _40049) = (term1025 _93490 _93497 s P f x _40049).
Proof. exact (MK_COMB (@lem3652693 _93490 _93497 s P f _40049) (@lem3652694 _93490 x _40049)). Qed.
Lemma lem3652696 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (x : type684 _93490) (_40049 : _93490 -> Prop) : (term1014 _93490 _93497 x s P f _40049) = (term1025 _93490 _93497 s P f x _40049).
Proof. exact (TRANS (@lem3652678 _93490 _93497 s P f x _40049) (@lem3652695 _93490 _93497 s P f x _40049)). Qed.
Lemma lem3652698 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term1022 _93490 _93497 s P f u.
Proof. exact (conj (@lem3652585 _93490 _93497 u t s x y P f h1) (@lem3652592 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3652700 {_93490 _93497 : Type'} (_40049 : _93490 -> Prop) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term1025 _93490 _93497 s P f x _40049.
Proof. exact (EQ_MP (@lem3652696 _93490 _93497 s P f x _40049) (@lem3652675 _93490 _93497 _40049 u t s x y P f h1)). Qed.
Lemma lem3652701 {_93490 _93497 : Type'} (_40049 : _93490 -> Prop) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term1025 _93490 _93497 s P f x _40049.
Proof. exact (@lem3652700 _93490 _93497 _40049 u t s x y P f h1). Qed.
Lemma lem3652702 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term1025 _93490 _93497 s P f x u.
Proof. exact (@lem3652701 _93490 _93497 u u t s x y P f h1). Qed.
Lemma lem3652705 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term824 _93490 x u.
Proof. exact (@lem3652702 _93490 _93497 u t s x y P f h1 (@lem3652698 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3652706 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term1026 _93490 x u.
Proof. exact (fun h0 : term1027 _93490 x u => @lem3652705 _93490 _93497 u t s x y P f h1). Qed.
Lemma lem3652708 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3652709 {_93490 : Type'} (x : type684 _93490) (u : _93490 -> Prop) : (term1026 _93490 x u) = (term824 _93490 x u).
Proof. exact (@lem3652708 (term824 _93490 x u)). Qed.
Lemma lem3652710 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term824 _93490 x u.
Proof. exact (EQ_MP (@lem3652709 _93490 x u) (@lem3652706 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3652712 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : @SUBSET _93490 u s.
Proof. exact (proj1 (@lem3651394 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3652713 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term950 _93490 u s.
Proof. exact (fun h0 : term227 _93490 u s => @lem3652712 _93490 _93497 u t s x y P f h1). Qed.
Lemma lem3652715 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3652716 {_93490 : Type'} (u : _93490 -> Prop) (s : _93490 -> Prop) : (term950 _93490 u s) = (@SUBSET _93490 u s).
Proof. exact (@lem3652715 (@SUBSET _93490 u s)). Qed.
Lemma lem3652717 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : @SUBSET _93490 u s.
Proof. exact (EQ_MP (@lem3652716 _93490 u s) (@lem3652713 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3652719 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term45 _93490 _93497 P f u.
Proof. exact (EQ_MP (@lem3651996 _93490 _93497 u t s x y P f h1) (@lem3651762 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3652720 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term954 _93490 _93497 P f u.
Proof. exact (fun h0 : term136 _93490 _93497 P f u => @lem3652719 _93490 _93497 u t s x y P f h1). Qed.
Lemma lem3652722 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3652723 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term954 _93490 _93497 P f u) = (term45 _93490 _93497 P f u).
Proof. exact (@lem3652722 (term45 _93490 _93497 P f u)). Qed.
Lemma lem3652724 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term45 _93490 _93497 P f u.
Proof. exact (EQ_MP (@lem3652723 _93490 _93497 P f u) (@lem3652720 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3652730 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3652731 {_93490 _93497 : Type'} (y : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term944 _93490 _93497 s y P f _40049) = (term1014 _93490 _93497 y s P f _40049).
Proof. exact (@lem3652730 (term824 _93490 y _40049) (term227 _93490 _40049 s) (term136 _93490 _93497 P f _40049)). Qed.
Lemma lem3652745 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3652746 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term959 _93490 _93497 s P f _40049) = (term960 _93490 _93497 P f _40049 s).
Proof. exact (@lem3652745 (term136 _93490 _93497 P f _40049) (term227 _93490 _40049 s)). Qed.
Lemma lem3652752 {_93490 : Type'} (y : type684 _93490) (_40049 : _93490 -> Prop) : (term1015 _93490 y _40049) = (term1015 _93490 y _40049).
Proof. exact (eq_refl (term1015 _93490 y _40049)). Qed.
Lemma lem3652753 {_93490 _93497 : Type'} (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term1014 _93490 _93497 y s P f _40049) = (term1016 _93490 _93497 y P f _40049 s).
Proof. exact (MK_COMB (@lem3652752 _93490 y _40049) (@lem3652746 _93490 _93497 P f _40049 s)). Qed.
Lemma lem3652764 {_93490 _93497 : Type'} (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term944 _93490 _93497 s y P f _40049) = (term1016 _93490 _93497 y P f _40049 s).
Proof. exact (TRANS (@lem3652731 _93490 _93497 y s P f _40049) (@lem3652753 _93490 _93497 y P f _40049 s)). Qed.
Lemma lem3652765 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3652766 {_93490 _93497 : Type'} (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term1017 _93490 _93497 s y P f _40049) = (term1018 _93490 _93497 y P f _40049 s).
Proof. exact (MK_COMB (@lem3652765) (@lem3652764 _93490 _93497 y P f _40049 s)). Qed.
Lemma lem3652780 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3652781 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term959 _93490 _93497 s P f _40049) = (term960 _93490 _93497 P f _40049 s).
Proof. exact (@lem3652780 (term136 _93490 _93497 P f _40049) (term227 _93490 _40049 s)). Qed.
Lemma lem3652787 {_93490 : Type'} (y : type684 _93490) (_40049 : _93490 -> Prop) : (term1015 _93490 y _40049) = (term1015 _93490 y _40049).
Proof. exact (eq_refl (term1015 _93490 y _40049)). Qed.
Lemma lem3652788 {_93490 _93497 : Type'} (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term1014 _93490 _93497 y s P f _40049) = (term1016 _93490 _93497 y P f _40049 s).
Proof. exact (MK_COMB (@lem3652787 _93490 y _40049) (@lem3652781 _93490 _93497 P f _40049 s)). Qed.
Lemma lem3652799 {_93490 _93497 : Type'} (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : ((term944 _93490 _93497 s y P f _40049) = (term1014 _93490 _93497 y s P f _40049)) = ((term1016 _93490 _93497 y P f _40049 s) = (term1016 _93490 _93497 y P f _40049 s)).
Proof. exact (MK_COMB (@lem3652766 _93490 _93497 y P f _40049 s) (@lem3652788 _93490 _93497 y P f _40049 s)). Qed.
Lemma lem3652801 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3652802 (x : Prop) : (x = x) = True.
Proof. exact (@lem3652801 Prop x). Qed.
Lemma lem3652803 {_93490 _93497 : Type'} (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : ((term1016 _93490 _93497 y P f _40049 s) = (term1016 _93490 _93497 y P f _40049 s)) = True.
Proof. exact (@lem3652802 (term1016 _93490 _93497 y P f _40049 s)). Qed.
Lemma lem3652804 {_93490 _93497 : Type'} (y : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : ((term944 _93490 _93497 s y P f _40049) = (term1014 _93490 _93497 y s P f _40049)) = True.
Proof. exact (TRANS (@lem3652799 _93490 _93497 y P f _40049 s) (@lem3652803 _93490 _93497 y P f _40049 s)). Qed.
Lemma lem3652805 {_93490 _93497 : Type'} (y : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : True = ((term944 _93490 _93497 s y P f _40049) = (term1014 _93490 _93497 y s P f _40049)).
Proof. exact (SYM (@lem3652804 _93490 _93497 y s P f _40049)). Qed.
Lemma lem3652806 {_93490 _93497 : Type'} (y : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term944 _93490 _93497 s y P f _40049) = (term1014 _93490 _93497 y s P f _40049).
Proof. exact (EQ_MP (@lem3652805 _93490 _93497 y s P f _40049) (@lem0)). Qed.
Lemma lem3652807 {_93490 _93497 : Type'} (_40049 : _93490 -> Prop) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term1014 _93490 _93497 y s P f _40049.
Proof. exact (EQ_MP (@lem3652806 _93490 _93497 y s P f _40049) (@lem3652095 _93490 _93497 _40049 u t s x y P f h1)). Qed.
Lemma lem3652809 (b : Prop) (a : Prop) : (a \/ b) = (term971 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3652810 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (y : type684 _93490) (_40049 : _93490 -> Prop) : (term1014 _93490 _93497 y s P f _40049) = (term1019 _93490 _93497 s P f y _40049).
Proof. exact (@lem3652809 (term959 _93490 _93497 s P f _40049) (term824 _93490 y _40049)). Qed.
Lemma lem3652812 (a : Prop) (b : Prop) : (term973 a b) = (term974 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3652813 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term1020 _93490 _93497 s P f _40049) = (term1021 _93490 _93497 s P f _40049).
Proof. exact (@lem3652812 (term227 _93490 _40049 s) (term136 _93490 _93497 P f _40049)). Qed.
Lemma lem3652815 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3652816 {_93490 : Type'} (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term978 _93490 _40049 s) = (@SUBSET _93490 _40049 s).
Proof. exact (@lem3652815 (@SUBSET _93490 _40049 s)). Qed.
Lemma lem3652817 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3652818 {_93490 : Type'} (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term979 _93490 _40049 s) = (term53 _93490 _40049 s).
Proof. exact (MK_COMB (@lem3652817) (@lem3652816 _93490 _40049 s)). Qed.
Lemma lem3652820 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3652821 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term982 _93490 _93497 P f _40049) = (term45 _93490 _93497 P f _40049).
Proof. exact (@lem3652820 (term45 _93490 _93497 P f _40049)). Qed.
Lemma lem3652822 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term1021 _93490 _93497 s P f _40049) = (term1022 _93490 _93497 s P f _40049).
Proof. exact (MK_COMB (@lem3652818 _93490 _40049 s) (@lem3652821 _93490 _93497 P f _40049)). Qed.
Lemma lem3652823 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term1020 _93490 _93497 s P f _40049) = (term1022 _93490 _93497 s P f _40049).
Proof. exact (TRANS (@lem3652813 _93490 _93497 s P f _40049) (@lem3652822 _93490 _93497 s P f _40049)). Qed.
Lemma lem3652824 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3652825 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term1023 _93490 _93497 s P f _40049) = (term1024 _93490 _93497 s P f _40049).
Proof. exact (MK_COMB (@lem3652824) (@lem3652823 _93490 _93497 s P f _40049)). Qed.
Lemma lem3652826 {_93490 : Type'} (y : type684 _93490) (_40049 : _93490 -> Prop) : (term824 _93490 y _40049) = (term824 _93490 y _40049).
Proof. exact (eq_refl (term824 _93490 y _40049)). Qed.
Lemma lem3652827 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (y : type684 _93490) (_40049 : _93490 -> Prop) : (term1019 _93490 _93497 s P f y _40049) = (term1025 _93490 _93497 s P f y _40049).
Proof. exact (MK_COMB (@lem3652825 _93490 _93497 s P f _40049) (@lem3652826 _93490 y _40049)). Qed.
Lemma lem3652828 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (y : type684 _93490) (_40049 : _93490 -> Prop) : (term1014 _93490 _93497 y s P f _40049) = (term1025 _93490 _93497 s P f y _40049).
Proof. exact (TRANS (@lem3652810 _93490 _93497 s P f y _40049) (@lem3652827 _93490 _93497 s P f y _40049)). Qed.
Lemma lem3652830 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term1022 _93490 _93497 s P f u.
Proof. exact (conj (@lem3652717 _93490 _93497 u t s x y P f h1) (@lem3652724 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3652832 {_93490 _93497 : Type'} (_40049 : _93490 -> Prop) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term1025 _93490 _93497 s P f y _40049.
Proof. exact (EQ_MP (@lem3652828 _93490 _93497 s P f y _40049) (@lem3652807 _93490 _93497 _40049 u t s x y P f h1)). Qed.
Lemma lem3652833 {_93490 _93497 : Type'} (_40049 : _93490 -> Prop) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term1025 _93490 _93497 s P f y _40049.
Proof. exact (@lem3652832 _93490 _93497 _40049 u t s x y P f h1). Qed.
Lemma lem3652834 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term1025 _93490 _93497 s P f y u.
Proof. exact (@lem3652833 _93490 _93497 u u t s x y P f h1). Qed.
Lemma lem3652837 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term824 _93490 y u.
Proof. exact (@lem3652834 _93490 _93497 u t s x y P f h1 (@lem3652830 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3652838 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term1026 _93490 y u.
Proof. exact (fun h0 : term1027 _93490 y u => @lem3652837 _93490 _93497 u t s x y P f h1). Qed.
Lemma lem3652840 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3652841 {_93490 : Type'} (y : type684 _93490) (u : _93490 -> Prop) : (term1026 _93490 y u) = (term824 _93490 y u).
Proof. exact (@lem3652840 (term824 _93490 y u)). Qed.
Lemma lem3652842 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term824 _93490 y u.
Proof. exact (EQ_MP (@lem3652841 _93490 y u) (@lem3652838 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3652844 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : @SUBSET _93490 u s.
Proof. exact (proj1 (@lem3651394 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3652845 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term950 _93490 u s.
Proof. exact (fun h0 : term227 _93490 u s => @lem3652844 _93490 _93497 u t s x y P f h1). Qed.
Lemma lem3652847 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3652848 {_93490 : Type'} (u : _93490 -> Prop) (s : _93490 -> Prop) : (term950 _93490 u s) = (@SUBSET _93490 u s).
Proof. exact (@lem3652847 (@SUBSET _93490 u s)). Qed.
Lemma lem3652849 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : @SUBSET _93490 u s.
Proof. exact (EQ_MP (@lem3652848 _93490 u s) (@lem3652845 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3652852 {_93490 : Type'} (x : type684 _93490) (y : type684 _93490) (u : _93490 -> Prop) (h1 : term781 _93490 x y u) : term781 _93490 x y u.
Proof. exact (h1). Qed.
Lemma lem3652853 {_93490 : Type'} (x : type684 _93490) (y : type684 _93490) (u : _93490 -> Prop) (h1 : term781 _93490 x y u) : term1028 _93490 x y u.
Proof. exact (fun h0 : (x u) = (y u) => @lem3652852 _93490 x y u h1). Qed.
Lemma lem3652855 (p : Prop) : (term953 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3652856 {_93490 : Type'} (x : type684 _93490) (y : type684 _93490) (u : _93490 -> Prop) : (term1028 _93490 x y u) = (term781 _93490 x y u).
Proof. exact (@lem3652855 ((x u) = (y u))). Qed.
Lemma lem3652857 {_93490 : Type'} (x : type684 _93490) (y : type684 _93490) (u : _93490 -> Prop) (h1 : term781 _93490 x y u) : term781 _93490 x y u.
Proof. exact (EQ_MP (@lem3652856 _93490 x y u) (@lem3652853 _93490 x y u h1)). Qed.
Lemma lem3652859 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term45 _93490 _93497 P f u.
Proof. exact (EQ_MP (@lem3651996 _93490 _93497 u t s x y P f h1) (@lem3651762 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3652860 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term954 _93490 _93497 P f u.
Proof. exact (fun h0 : term136 _93490 _93497 P f u => @lem3652859 _93490 _93497 u t s x y P f h1). Qed.
Lemma lem3652862 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3652863 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term954 _93490 _93497 P f u) = (term45 _93490 _93497 P f u).
Proof. exact (@lem3652862 (term45 _93490 _93497 P f u)). Qed.
Lemma lem3652864 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term45 _93490 _93497 P f u.
Proof. exact (EQ_MP (@lem3652863 _93490 _93497 P f u) (@lem3652860 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3652870 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3652871 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term921 _93490 _93497 s x y P f _40049) = (term955 _93490 _93497 s x y P f _40049).
Proof. exact (@lem3652870 ((term783 _93490 _93497 f x _40049) = (term783 _93490 _93497 f y _40049)) (term227 _93490 _40049 s) (term956 _93490 _93497 x y P f _40049)). Qed.
Lemma lem3652887 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3652888 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term957 _93490 _93497 s x y P f _40049) = (term958 _93490 _93497 x y s P f _40049).
Proof. exact (@lem3652887 ((x _40049) = (y _40049)) (term227 _93490 _40049 s) (term136 _93490 _93497 P f _40049)). Qed.
Lemma lem3652904 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3652905 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term959 _93490 _93497 s P f _40049) = (term960 _93490 _93497 P f _40049 s).
Proof. exact (@lem3652904 (term136 _93490 _93497 P f _40049) (term227 _93490 _40049 s)). Qed.
Lemma lem3652911 {_93490 : Type'} (x : type684 _93490) (y : type684 _93490) (_40049 : _93490 -> Prop) : (term961 _93490 x y _40049) = (term961 _93490 x y _40049).
Proof. exact (eq_refl (term961 _93490 x y _40049)). Qed.
Lemma lem3652912 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term958 _93490 _93497 x y s P f _40049) = (term962 _93490 _93497 x y P f _40049 s).
Proof. exact (MK_COMB (@lem3652911 _93490 x y _40049) (@lem3652905 _93490 _93497 P f _40049 s)). Qed.
Lemma lem3652923 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term957 _93490 _93497 s x y P f _40049) = (term962 _93490 _93497 x y P f _40049 s).
Proof. exact (TRANS (@lem3652888 _93490 _93497 x y s P f _40049) (@lem3652912 _93490 _93497 x y P f _40049 s)). Qed.
Lemma lem3652924 {_93490 _93497 : Type'} (x : type684 _93490) (f : _93490 -> _93497) (y : type684 _93490) (_40049 : _93490 -> Prop) : (term793 _93490 _93497 x f y _40049) = (term793 _93490 _93497 x f y _40049).
Proof. exact (eq_refl (term793 _93490 _93497 x f y _40049)). Qed.
Lemma lem3652925 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term955 _93490 _93497 s x y P f _40049) = (term963 _93490 _93497 x y P f _40049 s).
Proof. exact (MK_COMB (@lem3652924 _93490 _93497 x f y _40049) (@lem3652923 _93490 _93497 x y P f _40049 s)). Qed.
Lemma lem3652929 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3652930 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term963 _93490 _93497 x y P f _40049 s) = (term964 _93490 _93497 x y P f _40049 s).
Proof. exact (@lem3652929 ((x _40049) = (y _40049)) ((term783 _93490 _93497 f x _40049) = (term783 _93490 _93497 f y _40049)) (term960 _93490 _93497 P f _40049 s)). Qed.
Lemma lem3652960 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term955 _93490 _93497 s x y P f _40049) = (term964 _93490 _93497 x y P f _40049 s).
Proof. exact (TRANS (@lem3652925 _93490 _93497 x y P f _40049 s) (@lem3652930 _93490 _93497 x y P f _40049 s)). Qed.
Lemma lem3652961 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term921 _93490 _93497 s x y P f _40049) = (term964 _93490 _93497 x y P f _40049 s).
Proof. exact (TRANS (@lem3652871 _93490 _93497 s x y P f _40049) (@lem3652960 _93490 _93497 x y P f _40049 s)). Qed.
Lemma lem3652962 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3652963 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term965 _93490 _93497 s x y P f _40049) = (term966 _93490 _93497 x y P f _40049 s).
Proof. exact (MK_COMB (@lem3652962) (@lem3652961 _93490 _93497 x y P f _40049 s)). Qed.
Lemma lem3652979 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3652980 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term957 _93490 _93497 s x y P f _40049) = (term958 _93490 _93497 x y s P f _40049).
Proof. exact (@lem3652979 ((x _40049) = (y _40049)) (term227 _93490 _40049 s) (term136 _93490 _93497 P f _40049)). Qed.
Lemma lem3652996 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3652997 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term959 _93490 _93497 s P f _40049) = (term960 _93490 _93497 P f _40049 s).
Proof. exact (@lem3652996 (term136 _93490 _93497 P f _40049) (term227 _93490 _40049 s)). Qed.
Lemma lem3653003 {_93490 : Type'} (x : type684 _93490) (y : type684 _93490) (_40049 : _93490 -> Prop) : (term961 _93490 x y _40049) = (term961 _93490 x y _40049).
Proof. exact (eq_refl (term961 _93490 x y _40049)). Qed.
Lemma lem3653004 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term958 _93490 _93497 x y s P f _40049) = (term962 _93490 _93497 x y P f _40049 s).
Proof. exact (MK_COMB (@lem3653003 _93490 x y _40049) (@lem3652997 _93490 _93497 P f _40049 s)). Qed.
Lemma lem3653015 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term957 _93490 _93497 s x y P f _40049) = (term962 _93490 _93497 x y P f _40049 s).
Proof. exact (TRANS (@lem3652980 _93490 _93497 x y s P f _40049) (@lem3653004 _93490 _93497 x y P f _40049 s)). Qed.
Lemma lem3653016 {_93490 _93497 : Type'} (x : type684 _93490) (f : _93490 -> _93497) (y : type684 _93490) (_40049 : _93490 -> Prop) : (term793 _93490 _93497 x f y _40049) = (term793 _93490 _93497 x f y _40049).
Proof. exact (eq_refl (term793 _93490 _93497 x f y _40049)). Qed.
Lemma lem3653017 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term955 _93490 _93497 s x y P f _40049) = (term963 _93490 _93497 x y P f _40049 s).
Proof. exact (MK_COMB (@lem3653016 _93490 _93497 x f y _40049) (@lem3653015 _93490 _93497 x y P f _40049 s)). Qed.
Lemma lem3653021 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3653022 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term963 _93490 _93497 x y P f _40049 s) = (term964 _93490 _93497 x y P f _40049 s).
Proof. exact (@lem3653021 ((x _40049) = (y _40049)) ((term783 _93490 _93497 f x _40049) = (term783 _93490 _93497 f y _40049)) (term960 _93490 _93497 P f _40049 s)). Qed.
Lemma lem3653052 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term955 _93490 _93497 s x y P f _40049) = (term964 _93490 _93497 x y P f _40049 s).
Proof. exact (TRANS (@lem3653017 _93490 _93497 x y P f _40049 s) (@lem3653022 _93490 _93497 x y P f _40049 s)). Qed.
Lemma lem3653053 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : ((term921 _93490 _93497 s x y P f _40049) = (term955 _93490 _93497 s x y P f _40049)) = ((term964 _93490 _93497 x y P f _40049 s) = (term964 _93490 _93497 x y P f _40049 s)).
Proof. exact (MK_COMB (@lem3652963 _93490 _93497 x y P f _40049 s) (@lem3653052 _93490 _93497 x y P f _40049 s)). Qed.
Lemma lem3653055 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3653056 (x : Prop) : (x = x) = True.
Proof. exact (@lem3653055 Prop x). Qed.
Lemma lem3653057 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : ((term964 _93490 _93497 x y P f _40049 s) = (term964 _93490 _93497 x y P f _40049 s)) = True.
Proof. exact (@lem3653056 (term964 _93490 _93497 x y P f _40049 s)). Qed.
Lemma lem3653058 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : ((term921 _93490 _93497 s x y P f _40049) = (term955 _93490 _93497 s x y P f _40049)) = True.
Proof. exact (TRANS (@lem3653053 _93490 _93497 x y P f _40049 s) (@lem3653057 _93490 _93497 x y P f _40049 s)). Qed.
Lemma lem3653059 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : True = ((term921 _93490 _93497 s x y P f _40049) = (term955 _93490 _93497 s x y P f _40049)).
Proof. exact (SYM (@lem3653058 _93490 _93497 s x y P f _40049)). Qed.
Lemma lem3653060 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term921 _93490 _93497 s x y P f _40049) = (term955 _93490 _93497 s x y P f _40049).
Proof. exact (EQ_MP (@lem3653059 _93490 _93497 s x y P f _40049) (@lem0)). Qed.
Lemma lem3653061 {_93490 _93497 : Type'} (_40049 : _93490 -> Prop) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term955 _93490 _93497 s x y P f _40049.
Proof. exact (EQ_MP (@lem3653060 _93490 _93497 s x y P f _40049) (@lem3652053 _93490 _93497 _40049 u t s x y P f h1)). Qed.
Lemma lem3653063 (b : Prop) (a : Prop) : (a \/ b) = (term971 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3653064 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (x : type684 _93490) (f : _93490 -> _93497) (y : type684 _93490) (_40049 : _93490 -> Prop) : (term955 _93490 _93497 s x y P f _40049) = (term1029 _93490 _93497 s P x f y _40049).
Proof. exact (@lem3653063 (term957 _93490 _93497 s x y P f _40049) ((term783 _93490 _93497 f x _40049) = (term783 _93490 _93497 f y _40049))). Qed.
Lemma lem3653066 (a : Prop) (b : Prop) : (term973 a b) = (term974 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3653067 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term1030 _93490 _93497 s x y P f _40049) = (term1031 _93490 _93497 s x y P f _40049).
Proof. exact (@lem3653066 (term227 _93490 _40049 s) (term956 _93490 _93497 x y P f _40049)). Qed.
Lemma lem3653069 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3653070 {_93490 : Type'} (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term978 _93490 _40049 s) = (@SUBSET _93490 _40049 s).
Proof. exact (@lem3653069 (@SUBSET _93490 _40049 s)). Qed.
Lemma lem3653071 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3653072 {_93490 : Type'} (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term979 _93490 _40049 s) = (term53 _93490 _40049 s).
Proof. exact (MK_COMB (@lem3653071) (@lem3653070 _93490 _40049 s)). Qed.
Lemma lem3653074 (a : Prop) (b : Prop) : (term973 a b) = (term974 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3653075 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term1032 _93490 _93497 x y P f _40049) = (term1033 _93490 _93497 x y P f _40049).
Proof. exact (@lem3653074 ((x _40049) = (y _40049)) (term136 _93490 _93497 P f _40049)). Qed.
Lemma lem3653077 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3653078 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term982 _93490 _93497 P f _40049) = (term45 _93490 _93497 P f _40049).
Proof. exact (@lem3653077 (term45 _93490 _93497 P f _40049)). Qed.
Lemma lem3653079 {_93490 : Type'} (x : type684 _93490) (y : type684 _93490) (_40049 : _93490 -> Prop) : (term1034 _93490 x y _40049) = (term1034 _93490 x y _40049).
Proof. exact (eq_refl (term1034 _93490 x y _40049)). Qed.
Lemma lem3653080 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term1033 _93490 _93497 x y P f _40049) = (term1035 _93490 _93497 x y P f _40049).
Proof. exact (MK_COMB (@lem3653079 _93490 x y _40049) (@lem3653078 _93490 _93497 P f _40049)). Qed.
Lemma lem3653081 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term1032 _93490 _93497 x y P f _40049) = (term1035 _93490 _93497 x y P f _40049).
Proof. exact (TRANS (@lem3653075 _93490 _93497 x y P f _40049) (@lem3653080 _93490 _93497 x y P f _40049)). Qed.
Lemma lem3653082 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term1031 _93490 _93497 s x y P f _40049) = (term1036 _93490 _93497 s x y P f _40049).
Proof. exact (MK_COMB (@lem3653072 _93490 _40049 s) (@lem3653081 _93490 _93497 x y P f _40049)). Qed.
Lemma lem3653083 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term1030 _93490 _93497 s x y P f _40049) = (term1036 _93490 _93497 s x y P f _40049).
Proof. exact (TRANS (@lem3653067 _93490 _93497 s x y P f _40049) (@lem3653082 _93490 _93497 s x y P f _40049)). Qed.
Lemma lem3653084 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3653085 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term1037 _93490 _93497 s x y P f _40049) = (term1038 _93490 _93497 s x y P f _40049).
Proof. exact (MK_COMB (@lem3653084) (@lem3653083 _93490 _93497 s x y P f _40049)). Qed.
Lemma lem3653086 {_93490 _93497 : Type'} (x : type684 _93490) (f : _93490 -> _93497) (y : type684 _93490) (_40049 : _93490 -> Prop) : ((term783 _93490 _93497 f x _40049) = (term783 _93490 _93497 f y _40049)) = ((term783 _93490 _93497 f x _40049) = (term783 _93490 _93497 f y _40049)).
Proof. exact (eq_refl ((term783 _93490 _93497 f x _40049) = (term783 _93490 _93497 f y _40049))). Qed.
Lemma lem3653087 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (x : type684 _93490) (f : _93490 -> _93497) (y : type684 _93490) (_40049 : _93490 -> Prop) : (term1029 _93490 _93497 s P x f y _40049) = (term1039 _93490 _93497 s P x f y _40049).
Proof. exact (MK_COMB (@lem3653085 _93490 _93497 s x y P f _40049) (@lem3653086 _93490 _93497 x f y _40049)). Qed.
Lemma lem3653088 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (x : type684 _93490) (f : _93490 -> _93497) (y : type684 _93490) (_40049 : _93490 -> Prop) : (term955 _93490 _93497 s x y P f _40049) = (term1039 _93490 _93497 s P x f y _40049).
Proof. exact (TRANS (@lem3653064 _93490 _93497 s P x f y _40049) (@lem3653087 _93490 _93497 s P x f y _40049)). Qed.
Lemma lem3653090 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term781 _93490 x y u) (h2 : term815 _93490 _93497 u t s x y P f) : term1035 _93490 _93497 x y P f u.
Proof. exact (conj (@lem3652857 _93490 x y u h1) (@lem3652864 _93490 _93497 u t s x y P f h2)). Qed.
Lemma lem3653091 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term781 _93490 x y u) (h2 : term815 _93490 _93497 u t s x y P f) : term1036 _93490 _93497 s x y P f u.
Proof. exact (conj (@lem3652849 _93490 _93497 u t s x y P f h2) (@lem3653090 _93490 _93497 u t s x y P f h1 h2)). Qed.
Lemma lem3653093 {_93490 _93497 : Type'} (_40049 : _93490 -> Prop) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term1039 _93490 _93497 s P x f y _40049.
Proof. exact (EQ_MP (@lem3653088 _93490 _93497 s P x f y _40049) (@lem3653061 _93490 _93497 _40049 u t s x y P f h1)). Qed.
Lemma lem3653094 {_93490 _93497 : Type'} (_40049 : _93490 -> Prop) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term1039 _93490 _93497 s P x f y _40049.
Proof. exact (@lem3653093 _93490 _93497 _40049 u t s x y P f h1). Qed.
Lemma lem3653095 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term1039 _93490 _93497 s P x f y u.
Proof. exact (@lem3653094 _93490 _93497 u u t s x y P f h1). Qed.
Lemma lem3653098 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term781 _93490 x y u) (h2 : term815 _93490 _93497 u t s x y P f) : (term783 _93490 _93497 f x u) = (term783 _93490 _93497 f y u).
Proof. exact (@lem3653095 _93490 _93497 u t s x y P f h2 (@lem3653091 _93490 _93497 u t s x y P f h1 h2)). Qed.
Lemma lem3653099 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term781 _93490 x y u) (h2 : term815 _93490 _93497 u t s x y P f) : term1013 _93490 _93497 x f y u.
Proof. exact (fun h0 : term787 _93490 _93497 x f y u => @lem3653098 _93490 _93497 u t s x y P f h1 h2). Qed.
Lemma lem3653101 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3653102 {_93490 _93497 : Type'} (x : type684 _93490) (f : _93490 -> _93497) (y : type684 _93490) (u : _93490 -> Prop) : (term1013 _93490 _93497 x f y u) = ((term783 _93490 _93497 f x u) = (term783 _93490 _93497 f y u)).
Proof. exact (@lem3653101 ((term783 _93490 _93497 f x u) = (term783 _93490 _93497 f y u))). Qed.
Lemma lem3653103 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term781 _93490 x y u) (h2 : term815 _93490 _93497 u t s x y P f) : (term783 _93490 _93497 f x u) = (term783 _93490 _93497 f y u).
Proof. exact (EQ_MP (@lem3653102 _93490 _93497 x f y u) (@lem3653099 _93490 _93497 u t s x y P f h1 h2)). Qed.
Lemma lem3653119 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3653120 {_93490 _93497 : Type'} (f : _93490 -> _93497) (u : _93490 -> Prop) (_40050 : _93490) (_40051 : _93490) : (term1040 _93490 _93497 u f _40050 _40051) = (term1041 _93490 _93497 f u _40050 _40051).
Proof. exact (@lem3653119 (term721 _93490 _93497 _40050 f _40051) (term919 _93490 _40051 u) (_40050 = _40051)). Qed.
Lemma lem3653136 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3653137 {_93490 : Type'} (_40050 : _93490) (_40051 : _93490) (u : _93490 -> Prop) : (term1042 _93490 u _40050 _40051) = (term1043 _93490 _40050 _40051 u).
Proof. exact (@lem3653136 (_40050 = _40051) (term919 _93490 _40051 u)). Qed.
Lemma lem3653145 {_93490 _93497 : Type'} (_40050 : _93490) (f : _93490 -> _93497) (_40051 : _93490) : (term723 _93490 _93497 _40050 f _40051) = (term723 _93490 _93497 _40050 f _40051).
Proof. exact (eq_refl (term723 _93490 _93497 _40050 f _40051)). Qed.
Lemma lem3653146 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40050 : _93490) (_40051 : _93490) (u : _93490 -> Prop) : (term1041 _93490 _93497 f u _40050 _40051) = (term1044 _93490 _93497 f _40050 _40051 u).
Proof. exact (MK_COMB (@lem3653145 _93490 _93497 _40050 f _40051) (@lem3653137 _93490 _40050 _40051 u)). Qed.
Lemma lem3653150 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3653151 {_93490 _93497 : Type'} (_40050 : _93490) (f : _93490 -> _93497) (_40051 : _93490) (u : _93490 -> Prop) : (term1044 _93490 _93497 f _40050 _40051 u) = (term1045 _93490 _93497 _40050 f _40051 u).
Proof. exact (@lem3653150 (_40050 = _40051) (term721 _93490 _93497 _40050 f _40051) (term919 _93490 _40051 u)). Qed.
Lemma lem3653171 {_93490 _93497 : Type'} (_40050 : _93490) (f : _93490 -> _93497) (_40051 : _93490) (u : _93490 -> Prop) : (term1041 _93490 _93497 f u _40050 _40051) = (term1045 _93490 _93497 _40050 f _40051 u).
Proof. exact (TRANS (@lem3653146 _93490 _93497 f _40050 _40051 u) (@lem3653151 _93490 _93497 _40050 f _40051 u)). Qed.
Lemma lem3653172 {_93490 _93497 : Type'} (_40050 : _93490) (f : _93490 -> _93497) (_40051 : _93490) (u : _93490 -> Prop) : (term1040 _93490 _93497 u f _40050 _40051) = (term1045 _93490 _93497 _40050 f _40051 u).
Proof. exact (TRANS (@lem3653120 _93490 _93497 f u _40050 _40051) (@lem3653171 _93490 _93497 _40050 f _40051 u)). Qed.
Lemma lem3653173 {_93490 : Type'} (_40050 : _93490) (u : _93490 -> Prop) : (term1046 _93490 _40050 u) = (term1046 _93490 _40050 u).
Proof. exact (eq_refl (term1046 _93490 _40050 u)). Qed.
Lemma lem3653174 {_93490 _93497 : Type'} (_40050 : _93490) (f : _93490 -> _93497) (_40051 : _93490) (u : _93490 -> Prop) : (term918 _93490 _93497 u f _40050 _40051) = (term1047 _93490 _93497 _40050 f _40051 u).
Proof. exact (MK_COMB (@lem3653173 _93490 _40050 u) (@lem3653172 _93490 _93497 _40050 f _40051 u)). Qed.
Lemma lem3653178 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3653179 {_93490 _93497 : Type'} (_40050 : _93490) (f : _93490 -> _93497) (_40051 : _93490) (u : _93490 -> Prop) : (term1047 _93490 _93497 _40050 f _40051 u) = (term1048 _93490 _93497 _40050 f _40051 u).
Proof. exact (@lem3653178 (_40050 = _40051) (term919 _93490 _40050 u) (term1049 _93490 _93497 _40050 f _40051 u)). Qed.
Lemma lem3653195 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3653196 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40050 : _93490) (_40051 : _93490) (u : _93490 -> Prop) : (term1050 _93490 _93497 _40050 f _40051 u) = (term1051 _93490 _93497 f _40050 _40051 u).
Proof. exact (@lem3653195 (term721 _93490 _93497 _40050 f _40051) (term919 _93490 _40050 u) (term919 _93490 _40051 u)). Qed.
Lemma lem3653214 {_93490 : Type'} (_40050 : _93490) (_40051 : _93490) : (term1052 _93490 _40050 _40051) = (term1052 _93490 _40050 _40051).
Proof. exact (eq_refl (term1052 _93490 _40050 _40051)). Qed.
Lemma lem3653215 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40050 : _93490) (_40051 : _93490) (u : _93490 -> Prop) : (term1048 _93490 _93497 _40050 f _40051 u) = (term1053 _93490 _93497 f _40050 _40051 u).
Proof. exact (MK_COMB (@lem3653214 _93490 _40050 _40051) (@lem3653196 _93490 _93497 f _40050 _40051 u)). Qed.
Lemma lem3653226 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40050 : _93490) (_40051 : _93490) (u : _93490 -> Prop) : (term1047 _93490 _93497 _40050 f _40051 u) = (term1053 _93490 _93497 f _40050 _40051 u).
Proof. exact (TRANS (@lem3653179 _93490 _93497 _40050 f _40051 u) (@lem3653215 _93490 _93497 f _40050 _40051 u)). Qed.
Lemma lem3653227 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40050 : _93490) (_40051 : _93490) (u : _93490 -> Prop) : (term918 _93490 _93497 u f _40050 _40051) = (term1053 _93490 _93497 f _40050 _40051 u).
Proof. exact (TRANS (@lem3653174 _93490 _93497 _40050 f _40051 u) (@lem3653226 _93490 _93497 f _40050 _40051 u)). Qed.
Lemma lem3653228 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3653229 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40050 : _93490) (_40051 : _93490) (u : _93490 -> Prop) : (term1054 _93490 _93497 u f _40050 _40051) = (term1055 _93490 _93497 f _40050 _40051 u).
Proof. exact (MK_COMB (@lem3653228) (@lem3653227 _93490 _93497 f _40050 _40051 u)). Qed.
Lemma lem3653255 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3653256 {_93490 _93497 : Type'} (_40050 : _93490) (f : _93490 -> _93497) (_40051 : _93490) (u : _93490 -> Prop) : (term1056 _93490 _93497 u _40050 f _40051) = (term1049 _93490 _93497 _40050 f _40051 u).
Proof. exact (@lem3653255 (term721 _93490 _93497 _40050 f _40051) (term919 _93490 _40051 u)). Qed.
Lemma lem3653264 {_93490 : Type'} (_40050 : _93490) (u : _93490 -> Prop) : (term1046 _93490 _40050 u) = (term1046 _93490 _40050 u).
Proof. exact (eq_refl (term1046 _93490 _40050 u)). Qed.
Lemma lem3653265 {_93490 _93497 : Type'} (_40050 : _93490) (f : _93490 -> _93497) (_40051 : _93490) (u : _93490 -> Prop) : (term1057 _93490 _93497 u _40050 f _40051) = (term1050 _93490 _93497 _40050 f _40051 u).
Proof. exact (MK_COMB (@lem3653264 _93490 _40050 u) (@lem3653256 _93490 _93497 _40050 f _40051 u)). Qed.
Lemma lem3653269 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3653270 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40050 : _93490) (_40051 : _93490) (u : _93490 -> Prop) : (term1050 _93490 _93497 _40050 f _40051 u) = (term1051 _93490 _93497 f _40050 _40051 u).
Proof. exact (@lem3653269 (term721 _93490 _93497 _40050 f _40051) (term919 _93490 _40050 u) (term919 _93490 _40051 u)). Qed.
Lemma lem3653288 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40050 : _93490) (_40051 : _93490) (u : _93490 -> Prop) : (term1057 _93490 _93497 u _40050 f _40051) = (term1051 _93490 _93497 f _40050 _40051 u).
Proof. exact (TRANS (@lem3653265 _93490 _93497 _40050 f _40051 u) (@lem3653270 _93490 _93497 f _40050 _40051 u)). Qed.
Lemma lem3653289 {_93490 : Type'} (_40050 : _93490) (_40051 : _93490) : (term1052 _93490 _40050 _40051) = (term1052 _93490 _40050 _40051).
Proof. exact (eq_refl (term1052 _93490 _40050 _40051)). Qed.
Lemma lem3653290 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40050 : _93490) (_40051 : _93490) (u : _93490 -> Prop) : (term1058 _93490 _93497 u _40050 f _40051) = (term1053 _93490 _93497 f _40050 _40051 u).
Proof. exact (MK_COMB (@lem3653289 _93490 _40050 _40051) (@lem3653288 _93490 _93497 f _40050 _40051 u)). Qed.
Lemma lem3653301 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40050 : _93490) (_40051 : _93490) (u : _93490 -> Prop) : ((term918 _93490 _93497 u f _40050 _40051) = (term1058 _93490 _93497 u _40050 f _40051)) = ((term1053 _93490 _93497 f _40050 _40051 u) = (term1053 _93490 _93497 f _40050 _40051 u)).
Proof. exact (MK_COMB (@lem3653229 _93490 _93497 f _40050 _40051 u) (@lem3653290 _93490 _93497 f _40050 _40051 u)). Qed.
Lemma lem3653303 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3653304 (x : Prop) : (x = x) = True.
Proof. exact (@lem3653303 Prop x). Qed.
Lemma lem3653305 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40050 : _93490) (_40051 : _93490) (u : _93490 -> Prop) : ((term1053 _93490 _93497 f _40050 _40051 u) = (term1053 _93490 _93497 f _40050 _40051 u)) = True.
Proof. exact (@lem3653304 (term1053 _93490 _93497 f _40050 _40051 u)). Qed.
Lemma lem3653306 {_93490 _93497 : Type'} (u : _93490 -> Prop) (_40050 : _93490) (f : _93490 -> _93497) (_40051 : _93490) : ((term918 _93490 _93497 u f _40050 _40051) = (term1058 _93490 _93497 u _40050 f _40051)) = True.
Proof. exact (TRANS (@lem3653301 _93490 _93497 f _40050 _40051 u) (@lem3653305 _93490 _93497 f _40050 _40051 u)). Qed.
Lemma lem3653307 {_93490 _93497 : Type'} (u : _93490 -> Prop) (_40050 : _93490) (f : _93490 -> _93497) (_40051 : _93490) : True = ((term918 _93490 _93497 u f _40050 _40051) = (term1058 _93490 _93497 u _40050 f _40051)).
Proof. exact (SYM (@lem3653306 _93490 _93497 u _40050 f _40051)). Qed.
Lemma lem3653308 {_93490 _93497 : Type'} (u : _93490 -> Prop) (_40050 : _93490) (f : _93490 -> _93497) (_40051 : _93490) : (term918 _93490 _93497 u f _40050 _40051) = (term1058 _93490 _93497 u _40050 f _40051).
Proof. exact (EQ_MP (@lem3653307 _93490 _93497 u _40050 f _40051) (@lem0)). Qed.
Lemma lem3653309 {_93490 _93497 : Type'} (_40050 : _93490) (_40051 : _93490) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term1058 _93490 _93497 u _40050 f _40051.
Proof. exact (EQ_MP (@lem3653308 _93490 _93497 u _40050 f _40051) (@lem3652039 _93490 _93497 _40050 _40051 u t s x y P f h1)). Qed.
Lemma lem3653311 (b : Prop) (a : Prop) : (a \/ b) = (term971 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3653312 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (_40050 : _93490) (_40051 : _93490) : (term1058 _93490 _93497 u _40050 f _40051) = (term1059 _93490 _93497 u f _40050 _40051).
Proof. exact (@lem3653311 (term1057 _93490 _93497 u _40050 f _40051) (_40050 = _40051)). Qed.
Lemma lem3653314 (a : Prop) (b : Prop) : (term973 a b) = (term974 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3653315 {_93490 _93497 : Type'} (u : _93490 -> Prop) (_40050 : _93490) (f : _93490 -> _93497) (_40051 : _93490) : (term1060 _93490 _93497 u _40050 f _40051) = (term1061 _93490 _93497 u _40050 f _40051).
Proof. exact (@lem3653314 (term919 _93490 _40050 u) (term1056 _93490 _93497 u _40050 f _40051)). Qed.
Lemma lem3653317 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3653318 {_93490 : Type'} (_40050 : _93490) (u : _93490 -> Prop) : (term1062 _93490 _40050 u) = (@IN _93490 _40050 u).
Proof. exact (@lem3653317 (@IN _93490 _40050 u)). Qed.
Lemma lem3653319 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3653320 {_93490 : Type'} (_40050 : _93490) (u : _93490 -> Prop) : (term1063 _93490 _40050 u) = (term1064 _93490 _40050 u).
Proof. exact (MK_COMB (@lem3653319) (@lem3653318 _93490 _40050 u)). Qed.
Lemma lem3653322 (a : Prop) (b : Prop) : (term973 a b) = (term974 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3653323 {_93490 _93497 : Type'} (u : _93490 -> Prop) (_40050 : _93490) (f : _93490 -> _93497) (_40051 : _93490) : (term1065 _93490 _93497 u _40050 f _40051) = (term1066 _93490 _93497 u _40050 f _40051).
Proof. exact (@lem3653322 (term919 _93490 _40051 u) (term721 _93490 _93497 _40050 f _40051)). Qed.
Lemma lem3653325 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3653326 {_93490 : Type'} (_40051 : _93490) (u : _93490 -> Prop) : (term1062 _93490 _40051 u) = (@IN _93490 _40051 u).
Proof. exact (@lem3653325 (@IN _93490 _40051 u)). Qed.
Lemma lem3653327 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3653328 {_93490 : Type'} (_40051 : _93490) (u : _93490 -> Prop) : (term1063 _93490 _40051 u) = (term1064 _93490 _40051 u).
Proof. exact (MK_COMB (@lem3653327) (@lem3653326 _93490 _40051 u)). Qed.
Lemma lem3653330 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3653331 {_93490 _93497 : Type'} (_40050 : _93490) (f : _93490 -> _93497) (_40051 : _93490) : (term1067 _93490 _93497 _40050 f _40051) = ((@I (_93490 -> _93497) f _40050) = (@I (_93490 -> _93497) f _40051)).
Proof. exact (@lem3653330 ((@I (_93490 -> _93497) f _40050) = (@I (_93490 -> _93497) f _40051))). Qed.
Lemma lem3653332 {_93490 _93497 : Type'} (u : _93490 -> Prop) (_40050 : _93490) (f : _93490 -> _93497) (_40051 : _93490) : (term1066 _93490 _93497 u _40050 f _40051) = (term1068 _93490 _93497 u _40050 f _40051).
Proof. exact (MK_COMB (@lem3653328 _93490 _40051 u) (@lem3653331 _93490 _93497 _40050 f _40051)). Qed.
Lemma lem3653333 {_93490 _93497 : Type'} (u : _93490 -> Prop) (_40050 : _93490) (f : _93490 -> _93497) (_40051 : _93490) : (term1065 _93490 _93497 u _40050 f _40051) = (term1068 _93490 _93497 u _40050 f _40051).
Proof. exact (TRANS (@lem3653323 _93490 _93497 u _40050 f _40051) (@lem3653332 _93490 _93497 u _40050 f _40051)). Qed.
Lemma lem3653334 {_93490 _93497 : Type'} (u : _93490 -> Prop) (_40050 : _93490) (f : _93490 -> _93497) (_40051 : _93490) : (term1061 _93490 _93497 u _40050 f _40051) = (term1069 _93490 _93497 u _40050 f _40051).
Proof. exact (MK_COMB (@lem3653320 _93490 _40050 u) (@lem3653333 _93490 _93497 u _40050 f _40051)). Qed.
Lemma lem3653335 {_93490 _93497 : Type'} (u : _93490 -> Prop) (_40050 : _93490) (f : _93490 -> _93497) (_40051 : _93490) : (term1060 _93490 _93497 u _40050 f _40051) = (term1069 _93490 _93497 u _40050 f _40051).
Proof. exact (TRANS (@lem3653315 _93490 _93497 u _40050 f _40051) (@lem3653334 _93490 _93497 u _40050 f _40051)). Qed.
Lemma lem3653336 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3653337 {_93490 _93497 : Type'} (u : _93490 -> Prop) (_40050 : _93490) (f : _93490 -> _93497) (_40051 : _93490) : (term1070 _93490 _93497 u _40050 f _40051) = (term1071 _93490 _93497 u _40050 f _40051).
Proof. exact (MK_COMB (@lem3653336) (@lem3653335 _93490 _93497 u _40050 f _40051)). Qed.
Lemma lem3653338 {_93490 : Type'} (_40050 : _93490) (_40051 : _93490) : (_40050 = _40051) = (_40050 = _40051).
Proof. exact (eq_refl (_40050 = _40051)). Qed.
Lemma lem3653339 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (_40050 : _93490) (_40051 : _93490) : (term1059 _93490 _93497 u f _40050 _40051) = (term1072 _93490 _93497 u f _40050 _40051).
Proof. exact (MK_COMB (@lem3653337 _93490 _93497 u _40050 f _40051) (@lem3653338 _93490 _40050 _40051)). Qed.
Lemma lem3653340 {_93490 _93497 : Type'} (u : _93490 -> Prop) (f : _93490 -> _93497) (_40050 : _93490) (_40051 : _93490) : (term1058 _93490 _93497 u _40050 f _40051) = (term1072 _93490 _93497 u f _40050 _40051).
Proof. exact (TRANS (@lem3653312 _93490 _93497 u f _40050 _40051) (@lem3653339 _93490 _93497 u f _40050 _40051)). Qed.
Lemma lem3653342 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term781 _93490 x y u) (h2 : term815 _93490 _93497 u t s x y P f) : term1073 _93490 _93497 x f y u.
Proof. exact (conj (@lem3652842 _93490 _93497 u t s x y P f h2) (@lem3653103 _93490 _93497 u t s x y P f h1 h2)). Qed.
Lemma lem3653343 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term781 _93490 x y u) (h2 : term815 _93490 _93497 u t s x y P f) : term1074 _93490 _93497 x f y u.
Proof. exact (conj (@lem3652710 _93490 _93497 u t s x y P f h2) (@lem3653342 _93490 _93497 u t s x y P f h1 h2)). Qed.
Lemma lem3653345 {_93490 _93497 : Type'} (_40050 : _93490) (_40051 : _93490) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term1072 _93490 _93497 u f _40050 _40051.
Proof. exact (EQ_MP (@lem3653340 _93490 _93497 u f _40050 _40051) (@lem3653309 _93490 _93497 _40050 _40051 u t s x y P f h1)). Qed.
Lemma lem3653346 {_93490 _93497 : Type'} (_40050 : _93490) (_40051 : _93490) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term1072 _93490 _93497 u f _40050 _40051.
Proof. exact (@lem3653345 _93490 _93497 _40050 _40051 u t s x y P f h1). Qed.
Lemma lem3653347 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term1075 _93490 _93497 f x y u.
Proof. exact (@lem3653346 _93490 _93497 (x u) (y u) u t s x y P f h1). Qed.
Lemma lem3653350 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term781 _93490 x y u) (h2 : term815 _93490 _93497 u t s x y P f) : (x u) = (y u).
Proof. exact (@lem3653347 _93490 _93497 u t s x y P f h2 (@lem3653343 _93490 _93497 u t s x y P f h1 h2)). Qed.
Lemma lem3653351 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term989 _93490 x y u.
Proof. exact (fun h0 : term781 _93490 x y u => @lem3653350 _93490 _93497 u t s x y P f h0 h1). Qed.
Lemma lem3653353 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3653354 {_93490 : Type'} (x : type684 _93490) (y : type684 _93490) (u : _93490 -> Prop) : (term989 _93490 x y u) = ((x u) = (y u)).
Proof. exact (@lem3653353 ((x u) = (y u))). Qed.
Lemma lem3653355 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : (x u) = (y u).
Proof. exact (EQ_MP (@lem3653354 _93490 x y u) (@lem3653351 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3653357 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term45 _93490 _93497 P f u.
Proof. exact (EQ_MP (@lem3651996 _93490 _93497 u t s x y P f h1) (@lem3651762 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3653358 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term954 _93490 _93497 P f u.
Proof. exact (fun h0 : term136 _93490 _93497 P f u => @lem3653357 _93490 _93497 u t s x y P f h1). Qed.
Lemma lem3653360 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3653361 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (u : _93490 -> Prop) : (term954 _93490 _93497 P f u) = (term45 _93490 _93497 P f u).
Proof. exact (@lem3653360 (term45 _93490 _93497 P f u)). Qed.
Lemma lem3653362 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term45 _93490 _93497 P f u.
Proof. exact (EQ_MP (@lem3653361 _93490 _93497 P f u) (@lem3653358 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3653364 (a : Prop) (b : Prop) : (term1076 a b) = (term1077 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3653365 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term1078 _93490 _93497 x y P f _40049) = (term1079 _93490 _93497 x y P f _40049).
Proof. exact (@lem3653364 ((x _40049) = (y _40049)) (term45 _93490 _93497 P f _40049)). Qed.
Lemma lem3653366 {_93490 _93497 : Type'} (x : type684 _93490) (f : _93490 -> _93497) (y : type684 _93490) (_40049 : _93490 -> Prop) : (term789 _93490 _93497 x f y _40049) = (term789 _93490 _93497 x f y _40049).
Proof. exact (eq_refl (term789 _93490 _93497 x f y _40049)). Qed.
Lemma lem3653367 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term922 _93490 _93497 x y P f _40049) = (term1080 _93490 _93497 x y P f _40049).
Proof. exact (MK_COMB (@lem3653366 _93490 _93497 x f y _40049) (@lem3653365 _93490 _93497 x y P f _40049)). Qed.
Lemma lem3653369 (a : Prop) (b : Prop) : (term1076 a b) = (term1077 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3653370 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term1080 _93490 _93497 x y P f _40049) = (term1081 _93490 _93497 x y P f _40049).
Proof. exact (@lem3653369 ((term783 _93490 _93497 f x _40049) = (term783 _93490 _93497 f y _40049)) (term1082 _93490 _93497 x y P f _40049)). Qed.
Lemma lem3653371 {_93490 _93497 : Type'} (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term922 _93490 _93497 x y P f _40049) = (term1081 _93490 _93497 x y P f _40049).
Proof. exact (TRANS (@lem3653367 _93490 _93497 x y P f _40049) (@lem3653370 _93490 _93497 x y P f _40049)). Qed.
Lemma lem3653372 {_93490 : Type'} (_40049 : _93490 -> Prop) (s : _93490 -> Prop) : (term103 _93490 _40049 s) = (term103 _93490 _40049 s).
Proof. exact (eq_refl (term103 _93490 _40049 s)). Qed.
Lemma lem3653373 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term923 _93490 _93497 s x y P f _40049) = (term1083 _93490 _93497 s x y P f _40049).
Proof. exact (MK_COMB (@lem3653372 _93490 _40049 s) (@lem3653371 _93490 _93497 x y P f _40049)). Qed.
Lemma lem3653375 (a : Prop) (b : Prop) : (term1076 a b) = (term1077 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3653376 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term1083 _93490 _93497 s x y P f _40049) = (term1084 _93490 _93497 s x y P f _40049).
Proof. exact (@lem3653375 (@SUBSET _93490 _40049 s) (term1085 _93490 _93497 x y P f _40049)). Qed.
Lemma lem3653377 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term923 _93490 _93497 s x y P f _40049) = (term1084 _93490 _93497 s x y P f _40049).
Proof. exact (TRANS (@lem3653373 _93490 _93497 s x y P f _40049) (@lem3653376 _93490 _93497 s x y P f _40049)). Qed.
Lemma lem3653379 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3653380 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term1084 _93490 _93497 s x y P f _40049) = (term1086 _93490 _93497 s x y P f _40049).
Proof. exact (@lem3653379 (term1087 _93490 _93497 s x y P f _40049)). Qed.
Lemma lem3653381 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (_40049 : _93490 -> Prop) : (term923 _93490 _93497 s x y P f _40049) = (term1086 _93490 _93497 s x y P f _40049).
Proof. exact (TRANS (@lem3653377 _93490 _93497 s x y P f _40049) (@lem3653380 _93490 _93497 s x y P f _40049)). Qed.
Lemma lem3653383 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term1082 _93490 _93497 x y P f u.
Proof. exact (conj (@lem3653355 _93490 _93497 u t s x y P f h1) (@lem3653362 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3653384 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term1085 _93490 _93497 x y P f u.
Proof. exact (conj (@lem3652578 _93490 _93497 u t s x y P f h1) (@lem3653383 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3653385 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term1087 _93490 _93497 s x y P f u.
Proof. exact (conj (@lem3652208 _93490 _93497 u t s x y P f h1) (@lem3653384 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3653387 {_93490 _93497 : Type'} (_40049 : _93490 -> Prop) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term1086 _93490 _93497 s x y P f _40049.
Proof. exact (EQ_MP (@lem3653381 _93490 _93497 s x y P f _40049) (@lem3652067 _93490 _93497 _40049 u t s x y P f h1)). Qed.
Lemma lem3653388 {_93490 _93497 : Type'} (_40049 : _93490 -> Prop) (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term1086 _93490 _93497 s x y P f _40049.
Proof. exact (@lem3653387 _93490 _93497 _40049 u t s x y P f h1). Qed.
Lemma lem3653389 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term1086 _93490 _93497 s x y P f u.
Proof. exact (@lem3653388 _93490 _93497 u u t s x y P f h1). Qed.
Lemma lem3653392 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : False.
Proof. exact (@lem3653389 _93490 _93497 u t s x y P f h1 (@lem3653385 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3653393 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : term1088.
Proof. exact (fun h0 : ~ False => @lem3653392 _93490 _93497 u t s x y P f h1). Qed.
Lemma lem3653395 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3653396 : term1088 = False.
Proof. exact (@lem3653395 False). Qed.
Lemma lem3653478 {_93490 _93497 : Type'} : (@I (_93490 -> _93497)) = (@I (_93490 -> _93497)).
Proof. exact (eq_refl (@I (_93490 -> _93497))). Qed.
Lemma lem3653479 {_93490 _93497 : Type'} (_40114 : _93490 -> _93497) (_40116 : _93490 -> _93497) (h1 : _40114 = _40116) : _40114 = _40116.
Proof. exact (h1). Qed.
Lemma lem3653480 {_93490 : Type'} (_40115 : _93490) (_40117 : _93490) (h1 : _40115 = _40117) : _40115 = _40117.
Proof. exact (h1). Qed.
Lemma lem3653481 {_93490 _93497 : Type'} (_40114 : _93490 -> _93497) (_40116 : _93490 -> _93497) (h1 : _40114 = _40116) : (@I (_93490 -> _93497) _40114) = (@I (_93490 -> _93497) _40116).
Proof. exact (MK_COMB (@lem3653478 _93490 _93497) (@lem3653479 _93490 _93497 _40114 _40116 h1)). Qed.
Lemma lem3653482 {_93490 _93497 : Type'} (_40115 : _93490) (_40117 : _93490) (_40114 : _93490 -> _93497) (_40116 : _93490 -> _93497) (h1 : _40115 = _40117) (h2 : _40114 = _40116) : (@I (_93490 -> _93497) _40114 _40115) = (@I (_93490 -> _93497) _40116 _40117).
Proof. exact (MK_COMB (@lem3653481 _93490 _93497 _40114 _40116 h2) (@lem3653480 _93490 _40115 _40117 h1)). Qed.
Lemma lem3653483 {_93490 _93497 : Type'} (_40114 : _93490 -> _93497) (_40116 : _93490 -> _93497) (_40115 : _93490) (_40117 : _93490) (h1 : _40115 = _40117) : term945 _93490 _93497 _40114 _40115 _40116 _40117.
Proof. exact (fun h0 : _40114 = _40116 => @lem3653482 _93490 _93497 _40115 _40117 _40114 _40116 h1 h0). Qed.
Lemma lem3653485 (a : Prop) (b : Prop) : (a -> b) = (term946 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3653486 {_93490 _93497 : Type'} (_40114 : _93490 -> _93497) (_40115 : _93490) (_40116 : _93490 -> _93497) (_40117 : _93490) : (term945 _93490 _93497 _40114 _40115 _40116 _40117) = (term947 _93490 _93497 _40114 _40115 _40116 _40117).
Proof. exact (@lem3653485 (_40114 = _40116) ((@I (_93490 -> _93497) _40114 _40115) = (@I (_93490 -> _93497) _40116 _40117))). Qed.
Lemma lem3653487 {_93490 _93497 : Type'} (_40114 : _93490 -> _93497) (_40116 : _93490 -> _93497) (_40115 : _93490) (_40117 : _93490) (h1 : _40115 = _40117) : term947 _93490 _93497 _40114 _40115 _40116 _40117.
Proof. exact (EQ_MP (@lem3653486 _93490 _93497 _40114 _40115 _40116 _40117) (@lem3653483 _93490 _93497 _40114 _40116 _40115 _40117 h1)). Qed.
Lemma lem3653488 {_93490 _93497 : Type'} (_40114 : _93490 -> _93497) (_40115 : _93490) (_40116 : _93490 -> _93497) (_40117 : _93490) : term948 _93490 _93497 _40114 _40115 _40116 _40117.
Proof. exact (fun h0 : _40115 = _40117 => @lem3653487 _93490 _93497 _40114 _40116 _40115 _40117 h0). Qed.
Lemma lem3653490 (a : Prop) (b : Prop) : (a -> b) = (term946 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3653491 {_93490 _93497 : Type'} (_40114 : _93490 -> _93497) (_40115 : _93490) (_40116 : _93490 -> _93497) (_40117 : _93490) : (term948 _93490 _93497 _40114 _40115 _40116 _40117) = (term949 _93490 _93497 _40114 _40115 _40116 _40117).
Proof. exact (@lem3653490 (_40115 = _40117) (term947 _93490 _93497 _40114 _40115 _40116 _40117)). Qed.
Lemma lem3653492 {_93490 _93497 : Type'} (_40114 : _93490 -> _93497) (_40115 : _93490) (_40116 : _93490 -> _93497) (_40117 : _93490) : term949 _93490 _93497 _40114 _40115 _40116 _40117.
Proof. exact (EQ_MP (@lem3653491 _93490 _93497 _40114 _40115 _40116 _40117) (@lem3653488 _93490 _93497 _40114 _40115 _40116 _40117)). Qed.
Lemma lem3653519 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : @SUBSET _93490 t' s.
Proof. exact (proj1 (@lem3651399 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3653520 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term950 _93490 t' s.
Proof. exact (fun h0 : term227 _93490 t' s => @lem3653519 _93490 _93497 x' y' s P f t' h1). Qed.
Lemma lem3653522 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3653523 {_93490 : Type'} (t' : _93490 -> Prop) (s : _93490 -> Prop) : (term950 _93490 t' s) = (@SUBSET _93490 t' s).
Proof. exact (@lem3653522 (@SUBSET _93490 t' s)). Qed.
Lemma lem3653524 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : @SUBSET _93490 t' s.
Proof. exact (EQ_MP (@lem3653523 _93490 t' s) (@lem3653520 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3653526 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : @SUBSET _93490 t' s.
Proof. exact (proj1 (@lem3651399 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3653527 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term950 _93490 t' s.
Proof. exact (fun h0 : term227 _93490 t' s => @lem3653526 _93490 _93497 x' y' s P f t' h1). Qed.
Lemma lem3653529 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3653530 {_93490 : Type'} (t' : _93490 -> Prop) (s : _93490 -> Prop) : (term950 _93490 t' s) = (@SUBSET _93490 t' s).
Proof. exact (@lem3653529 (@SUBSET _93490 t' s)). Qed.
Lemma lem3653531 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : @SUBSET _93490 t' s.
Proof. exact (EQ_MP (@lem3653530 _93490 t' s) (@lem3653527 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3653534 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term1089 _93490 _93497 x' y' f t') : term1089 _93490 _93497 x' y' f t'.
Proof. exact (h1). Qed.
Lemma lem3653535 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term1089 _93490 _93497 x' y' f t') : term1090 _93490 _93497 x' y' f t'.
Proof. exact (fun h0 : (term1091 _93490 _93497 x' f t') = (term1091 _93490 _93497 y' f t') => @lem3653534 _93490 _93497 x' y' f t' h1). Qed.
Lemma lem3653537 (p : Prop) : (term953 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3653538 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) : (term1090 _93490 _93497 x' y' f t') = (term1089 _93490 _93497 x' y' f t').
Proof. exact (@lem3653537 ((term1091 _93490 _93497 x' f t') = (term1091 _93490 _93497 y' f t'))). Qed.
Lemma lem3653539 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term1089 _93490 _93497 x' y' f t') : term1089 _93490 _93497 x' y' f t'.
Proof. exact (EQ_MP (@lem3653538 _93490 _93497 x' y' f t') (@lem3653535 _93490 _93497 x' y' f t' h1)). Qed.
Lemma lem3653541 {_93497 : Type'} (x : _93497 -> Prop) : x = x.
Proof. exact (@lem21386 (_93497 -> Prop) x). Qed.
Lemma lem3653542 {_93497 : Type'} (x : _93497 -> Prop) : x = x.
Proof. exact (@lem3653541 _93497 x). Qed.
Lemma lem3653543 {_93490 _93497 : Type'} (f : _93490 -> _93497) (t' : _93490 -> Prop) : (@IMAGE _93490 _93497 f t') = (@IMAGE _93490 _93497 f t').
Proof. exact (@lem3653542 _93497 (@IMAGE _93490 _93497 f t')). Qed.
Lemma lem3653544 {_93490 _93497 : Type'} (f : _93490 -> _93497) (t' : _93490 -> Prop) : term1092 _93490 _93497 f t'.
Proof. exact (fun h0 : term1093 _93490 _93497 f t' => @lem3653543 _93490 _93497 f t'). Qed.
Lemma lem3653546 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3653547 {_93490 _93497 : Type'} (f : _93490 -> _93497) (t' : _93490 -> Prop) : (term1092 _93490 _93497 f t') = ((@IMAGE _93490 _93497 f t') = (@IMAGE _93490 _93497 f t')).
Proof. exact (@lem3653546 ((@IMAGE _93490 _93497 f t') = (@IMAGE _93490 _93497 f t'))). Qed.
Lemma lem3653548 {_93490 _93497 : Type'} (f : _93490 -> _93497) (t' : _93490 -> Prop) : (@IMAGE _93490 _93497 f t') = (@IMAGE _93490 _93497 f t').
Proof. exact (EQ_MP (@lem3653547 _93490 _93497 f t') (@lem3653544 _93490 _93497 f t')). Qed.
Lemma lem3653550 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term45 _93490 _93497 P f t'.
Proof. exact (proj2 (@lem3651401 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3653551 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term954 _93490 _93497 P f t'.
Proof. exact (fun h0 : term136 _93490 _93497 P f t' => @lem3653550 _93490 _93497 x' y' s P f t' h1). Qed.
Lemma lem3653553 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3653554 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) : (term954 _93490 _93497 P f t') = (term45 _93490 _93497 P f t').
Proof. exact (@lem3653553 (term45 _93490 _93497 P f t')). Qed.
Lemma lem3653555 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term45 _93490 _93497 P f t'.
Proof. exact (EQ_MP (@lem3653554 _93490 _93497 P f t') (@lem3653551 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3653561 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3653562 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term929 _93490 _93497 s x' y' f _40053 P _40052) = (term1094 _93490 _93497 s x' y' f _40053 P _40052).
Proof. exact (@lem3653561 ((term744 _93490 _93497 f x' _40052 _40053) = (term744 _93490 _93497 f y' _40052 _40053)) (term227 _93490 _40053 s) (term1095 _93490 _93497 x' y' f _40053 P _40052)). Qed.
Lemma lem3653578 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3653579 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1096 _93490 _93497 s x' y' f _40053 P _40052) = (term1097 _93490 _93497 x' y' s f _40053 P _40052).
Proof. exact (@lem3653578 ((x' _40052 _40053) = (y' _40052 _40053)) (term227 _93490 _40053 s) (term928 _93490 _93497 f _40053 P _40052)). Qed.
Lemma lem3653595 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3653596 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1098 _93490 _93497 s f _40053 P _40052) = (term1099 _93490 _93497 f _40053 s P _40052).
Proof. exact (@lem3653595 (term95 _93490 _93497 _40052 f _40053) (term227 _93490 _40053 s) (term119 _93497 P _40052)). Qed.
Lemma lem3653612 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3653613 {_93490 _93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1100 _93490 _93497 _40053 s P _40052) = (term1101 _93490 _93497 P _40052 _40053 s).
Proof. exact (@lem3653612 (term119 _93497 P _40052) (term227 _93490 _40053 s)). Qed.
Lemma lem3653619 {_93490 _93497 : Type'} (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) : (term1102 _93490 _93497 _40052 f _40053) = (term1102 _93490 _93497 _40052 f _40053).
Proof. exact (eq_refl (term1102 _93490 _93497 _40052 f _40053)). Qed.
Lemma lem3653620 {_93490 _93497 : Type'} (f : _93490 -> _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1099 _93490 _93497 f _40053 s P _40052) = (term1103 _93490 _93497 f P _40052 _40053 s).
Proof. exact (MK_COMB (@lem3653619 _93490 _93497 _40052 f _40053) (@lem3653613 _93490 _93497 P _40052 _40053 s)). Qed.
Lemma lem3653624 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3653625 {_93490 _93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1103 _93490 _93497 f P _40052 _40053 s) = (term1104 _93490 _93497 P _40052 f _40053 s).
Proof. exact (@lem3653624 (term119 _93497 P _40052) (term95 _93490 _93497 _40052 f _40053) (term227 _93490 _40053 s)). Qed.
Lemma lem3653643 {_93490 _93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1099 _93490 _93497 f _40053 s P _40052) = (term1104 _93490 _93497 P _40052 f _40053 s).
Proof. exact (TRANS (@lem3653620 _93490 _93497 f P _40052 _40053 s) (@lem3653625 _93490 _93497 P _40052 f _40053 s)). Qed.
Lemma lem3653644 {_93490 _93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1098 _93490 _93497 s f _40053 P _40052) = (term1104 _93490 _93497 P _40052 f _40053 s).
Proof. exact (TRANS (@lem3653596 _93490 _93497 f _40053 s P _40052) (@lem3653643 _93490 _93497 P _40052 f _40053 s)). Qed.
Lemma lem3653645 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) : (term1105 _93490 _93497 x' y' _40052 _40053) = (term1105 _93490 _93497 x' y' _40052 _40053).
Proof. exact (eq_refl (term1105 _93490 _93497 x' y' _40052 _40053)). Qed.
Lemma lem3653646 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1097 _93490 _93497 x' y' s f _40053 P _40052) = (term1106 _93490 _93497 x' y' P _40052 f _40053 s).
Proof. exact (MK_COMB (@lem3653645 _93490 _93497 x' y' _40052 _40053) (@lem3653644 _93490 _93497 P _40052 f _40053 s)). Qed.
Lemma lem3653657 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1096 _93490 _93497 s x' y' f _40053 P _40052) = (term1106 _93490 _93497 x' y' P _40052 f _40053 s).
Proof. exact (TRANS (@lem3653579 _93490 _93497 x' y' s f _40053 P _40052) (@lem3653646 _93490 _93497 x' y' P _40052 f _40053 s)). Qed.
Lemma lem3653658 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (f : _93490 -> _93497) (y' : type840 _93490 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) : (term754 _93490 _93497 x' f y' _40052 _40053) = (term754 _93490 _93497 x' f y' _40052 _40053).
Proof. exact (eq_refl (term754 _93490 _93497 x' f y' _40052 _40053)). Qed.
Lemma lem3653659 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1094 _93490 _93497 s x' y' f _40053 P _40052) = (term1107 _93490 _93497 x' y' P _40052 f _40053 s).
Proof. exact (MK_COMB (@lem3653658 _93490 _93497 x' f y' _40052 _40053) (@lem3653657 _93490 _93497 x' y' P _40052 f _40053 s)). Qed.
Lemma lem3653663 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3653664 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1107 _93490 _93497 x' y' P _40052 f _40053 s) = (term1108 _93490 _93497 x' y' P _40052 f _40053 s).
Proof. exact (@lem3653663 ((x' _40052 _40053) = (y' _40052 _40053)) ((term744 _93490 _93497 f x' _40052 _40053) = (term744 _93490 _93497 f y' _40052 _40053)) (term1104 _93490 _93497 P _40052 f _40053 s)). Qed.
Lemma lem3653706 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1094 _93490 _93497 s x' y' f _40053 P _40052) = (term1108 _93490 _93497 x' y' P _40052 f _40053 s).
Proof. exact (TRANS (@lem3653659 _93490 _93497 x' y' P _40052 f _40053 s) (@lem3653664 _93490 _93497 x' y' P _40052 f _40053 s)). Qed.
Lemma lem3653707 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term929 _93490 _93497 s x' y' f _40053 P _40052) = (term1108 _93490 _93497 x' y' P _40052 f _40053 s).
Proof. exact (TRANS (@lem3653562 _93490 _93497 s x' y' f _40053 P _40052) (@lem3653706 _93490 _93497 x' y' P _40052 f _40053 s)). Qed.
Lemma lem3653708 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3653709 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1109 _93490 _93497 s x' y' f _40053 P _40052) = (term1110 _93490 _93497 x' y' P _40052 f _40053 s).
Proof. exact (MK_COMB (@lem3653708) (@lem3653707 _93490 _93497 x' y' P _40052 f _40053 s)). Qed.
Lemma lem3653725 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3653726 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1111 _93490 _93497 s x' y' f _40053 P _40052) = (term1112 _93490 _93497 x' y' s f _40053 P _40052).
Proof. exact (@lem3653725 ((term744 _93490 _93497 f x' _40052 _40053) = (term744 _93490 _93497 f y' _40052 _40053)) (term227 _93490 _40053 s) (term928 _93490 _93497 f _40053 P _40052)). Qed.
Lemma lem3653742 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3653743 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1098 _93490 _93497 s f _40053 P _40052) = (term1099 _93490 _93497 f _40053 s P _40052).
Proof. exact (@lem3653742 (term95 _93490 _93497 _40052 f _40053) (term227 _93490 _40053 s) (term119 _93497 P _40052)). Qed.
Lemma lem3653759 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3653760 {_93490 _93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1100 _93490 _93497 _40053 s P _40052) = (term1101 _93490 _93497 P _40052 _40053 s).
Proof. exact (@lem3653759 (term119 _93497 P _40052) (term227 _93490 _40053 s)). Qed.
Lemma lem3653766 {_93490 _93497 : Type'} (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) : (term1102 _93490 _93497 _40052 f _40053) = (term1102 _93490 _93497 _40052 f _40053).
Proof. exact (eq_refl (term1102 _93490 _93497 _40052 f _40053)). Qed.
Lemma lem3653767 {_93490 _93497 : Type'} (f : _93490 -> _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1099 _93490 _93497 f _40053 s P _40052) = (term1103 _93490 _93497 f P _40052 _40053 s).
Proof. exact (MK_COMB (@lem3653766 _93490 _93497 _40052 f _40053) (@lem3653760 _93490 _93497 P _40052 _40053 s)). Qed.
Lemma lem3653771 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3653772 {_93490 _93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1103 _93490 _93497 f P _40052 _40053 s) = (term1104 _93490 _93497 P _40052 f _40053 s).
Proof. exact (@lem3653771 (term119 _93497 P _40052) (term95 _93490 _93497 _40052 f _40053) (term227 _93490 _40053 s)). Qed.
Lemma lem3653790 {_93490 _93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1099 _93490 _93497 f _40053 s P _40052) = (term1104 _93490 _93497 P _40052 f _40053 s).
Proof. exact (TRANS (@lem3653767 _93490 _93497 f P _40052 _40053 s) (@lem3653772 _93490 _93497 P _40052 f _40053 s)). Qed.
Lemma lem3653791 {_93490 _93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1098 _93490 _93497 s f _40053 P _40052) = (term1104 _93490 _93497 P _40052 f _40053 s).
Proof. exact (TRANS (@lem3653743 _93490 _93497 f _40053 s P _40052) (@lem3653790 _93490 _93497 P _40052 f _40053 s)). Qed.
Lemma lem3653792 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (f : _93490 -> _93497) (y' : type840 _93490 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) : (term754 _93490 _93497 x' f y' _40052 _40053) = (term754 _93490 _93497 x' f y' _40052 _40053).
Proof. exact (eq_refl (term754 _93490 _93497 x' f y' _40052 _40053)). Qed.
Lemma lem3653793 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1112 _93490 _93497 x' y' s f _40053 P _40052) = (term1113 _93490 _93497 x' y' P _40052 f _40053 s).
Proof. exact (MK_COMB (@lem3653792 _93490 _93497 x' f y' _40052 _40053) (@lem3653791 _93490 _93497 P _40052 f _40053 s)). Qed.
Lemma lem3653804 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1111 _93490 _93497 s x' y' f _40053 P _40052) = (term1113 _93490 _93497 x' y' P _40052 f _40053 s).
Proof. exact (TRANS (@lem3653726 _93490 _93497 x' y' s f _40053 P _40052) (@lem3653793 _93490 _93497 x' y' P _40052 f _40053 s)). Qed.
Lemma lem3653805 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) : (term1105 _93490 _93497 x' y' _40052 _40053) = (term1105 _93490 _93497 x' y' _40052 _40053).
Proof. exact (eq_refl (term1105 _93490 _93497 x' y' _40052 _40053)). Qed.
Lemma lem3653806 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1114 _93490 _93497 s x' y' f _40053 P _40052) = (term1108 _93490 _93497 x' y' P _40052 f _40053 s).
Proof. exact (MK_COMB (@lem3653805 _93490 _93497 x' y' _40052 _40053) (@lem3653804 _93490 _93497 x' y' P _40052 f _40053 s)). Qed.
Lemma lem3653817 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : ((term929 _93490 _93497 s x' y' f _40053 P _40052) = (term1114 _93490 _93497 s x' y' f _40053 P _40052)) = ((term1108 _93490 _93497 x' y' P _40052 f _40053 s) = (term1108 _93490 _93497 x' y' P _40052 f _40053 s)).
Proof. exact (MK_COMB (@lem3653709 _93490 _93497 x' y' P _40052 f _40053 s) (@lem3653806 _93490 _93497 x' y' P _40052 f _40053 s)). Qed.
Lemma lem3653819 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3653820 (x : Prop) : (x = x) = True.
Proof. exact (@lem3653819 Prop x). Qed.
Lemma lem3653821 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : ((term1108 _93490 _93497 x' y' P _40052 f _40053 s) = (term1108 _93490 _93497 x' y' P _40052 f _40053 s)) = True.
Proof. exact (@lem3653820 (term1108 _93490 _93497 x' y' P _40052 f _40053 s)). Qed.
Lemma lem3653822 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : ((term929 _93490 _93497 s x' y' f _40053 P _40052) = (term1114 _93490 _93497 s x' y' f _40053 P _40052)) = True.
Proof. exact (TRANS (@lem3653817 _93490 _93497 x' y' P _40052 f _40053 s) (@lem3653821 _93490 _93497 x' y' P _40052 f _40053 s)). Qed.
Lemma lem3653823 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : True = ((term929 _93490 _93497 s x' y' f _40053 P _40052) = (term1114 _93490 _93497 s x' y' f _40053 P _40052)).
Proof. exact (SYM (@lem3653822 _93490 _93497 s x' y' f _40053 P _40052)). Qed.
Lemma lem3653824 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term929 _93490 _93497 s x' y' f _40053 P _40052) = (term1114 _93490 _93497 s x' y' f _40053 P _40052).
Proof. exact (EQ_MP (@lem3653823 _93490 _93497 s x' y' f _40053 P _40052) (@lem0)). Qed.
Lemma lem3653825 {_93490 _93497 : Type'} (_40053 : _93490 -> Prop) (_40052 : _93497 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1114 _93490 _93497 s x' y' f _40053 P _40052.
Proof. exact (EQ_MP (@lem3653824 _93490 _93497 s x' y' f _40053 P _40052) (@lem3651910 _93490 _93497 _40053 _40052 x' y' s P f t' h1)). Qed.
Lemma lem3653827 (b : Prop) (a : Prop) : (a \/ b) = (term971 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3653828 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) : (term1114 _93490 _93497 s x' y' f _40053 P _40052) = (term1115 _93490 _93497 s f P x' y' _40052 _40053).
Proof. exact (@lem3653827 (term1111 _93490 _93497 s x' y' f _40053 P _40052) ((x' _40052 _40053) = (y' _40052 _40053))). Qed.
Lemma lem3653830 (a : Prop) (b : Prop) : (term973 a b) = (term974 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3653831 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1116 _93490 _93497 s x' y' f _40053 P _40052) = (term1117 _93490 _93497 s x' y' f _40053 P _40052).
Proof. exact (@lem3653830 (term227 _93490 _40053 s) (term1118 _93490 _93497 x' y' f _40053 P _40052)). Qed.
Lemma lem3653833 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3653834 {_93490 : Type'} (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term978 _93490 _40053 s) = (@SUBSET _93490 _40053 s).
Proof. exact (@lem3653833 (@SUBSET _93490 _40053 s)). Qed.
Lemma lem3653835 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3653836 {_93490 : Type'} (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term979 _93490 _40053 s) = (term53 _93490 _40053 s).
Proof. exact (MK_COMB (@lem3653835) (@lem3653834 _93490 _40053 s)). Qed.
Lemma lem3653838 (a : Prop) (b : Prop) : (term973 a b) = (term974 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3653839 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1119 _93490 _93497 x' y' f _40053 P _40052) = (term1120 _93490 _93497 x' y' f _40053 P _40052).
Proof. exact (@lem3653838 ((term744 _93490 _93497 f x' _40052 _40053) = (term744 _93490 _93497 f y' _40052 _40053)) (term928 _93490 _93497 f _40053 P _40052)). Qed.
Lemma lem3653841 (a : Prop) (b : Prop) : (term973 a b) = (term974 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3653842 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1121 _93490 _93497 f _40053 P _40052) = (term1122 _93490 _93497 f _40053 P _40052).
Proof. exact (@lem3653841 (term95 _93490 _93497 _40052 f _40053) (term119 _93497 P _40052)). Qed.
Lemma lem3653844 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3653845 {_93490 _93497 : Type'} (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) : (term1123 _93490 _93497 _40052 f _40053) = (_40052 = (@IMAGE _93490 _93497 f _40053)).
Proof. exact (@lem3653844 (_40052 = (@IMAGE _93490 _93497 f _40053))). Qed.
Lemma lem3653846 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3653847 {_93490 _93497 : Type'} (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) : (term1124 _93490 _93497 _40052 f _40053) = (term1125 _93490 _93497 _40052 f _40053).
Proof. exact (MK_COMB (@lem3653846) (@lem3653845 _93490 _93497 _40052 f _40053)). Qed.
Lemma lem3653849 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3653850 {_93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1126 _93497 P _40052) = (P _40052).
Proof. exact (@lem3653849 (P _40052)). Qed.
Lemma lem3653851 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1122 _93490 _93497 f _40053 P _40052) = (term1127 _93490 _93497 f _40053 P _40052).
Proof. exact (MK_COMB (@lem3653847 _93490 _93497 _40052 f _40053) (@lem3653850 _93497 P _40052)). Qed.
Lemma lem3653852 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1121 _93490 _93497 f _40053 P _40052) = (term1127 _93490 _93497 f _40053 P _40052).
Proof. exact (TRANS (@lem3653842 _93490 _93497 f _40053 P _40052) (@lem3653851 _93490 _93497 f _40053 P _40052)). Qed.
Lemma lem3653853 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (f : _93490 -> _93497) (y' : type840 _93490 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) : (term1128 _93490 _93497 x' f y' _40052 _40053) = (term1128 _93490 _93497 x' f y' _40052 _40053).
Proof. exact (eq_refl (term1128 _93490 _93497 x' f y' _40052 _40053)). Qed.
Lemma lem3653854 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1120 _93490 _93497 x' y' f _40053 P _40052) = (term1129 _93490 _93497 x' y' f _40053 P _40052).
Proof. exact (MK_COMB (@lem3653853 _93490 _93497 x' f y' _40052 _40053) (@lem3653852 _93490 _93497 f _40053 P _40052)). Qed.
Lemma lem3653855 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1119 _93490 _93497 x' y' f _40053 P _40052) = (term1129 _93490 _93497 x' y' f _40053 P _40052).
Proof. exact (TRANS (@lem3653839 _93490 _93497 x' y' f _40053 P _40052) (@lem3653854 _93490 _93497 x' y' f _40053 P _40052)). Qed.
Lemma lem3653856 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1117 _93490 _93497 s x' y' f _40053 P _40052) = (term1130 _93490 _93497 s x' y' f _40053 P _40052).
Proof. exact (MK_COMB (@lem3653836 _93490 _40053 s) (@lem3653855 _93490 _93497 x' y' f _40053 P _40052)). Qed.
Lemma lem3653857 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1116 _93490 _93497 s x' y' f _40053 P _40052) = (term1130 _93490 _93497 s x' y' f _40053 P _40052).
Proof. exact (TRANS (@lem3653831 _93490 _93497 s x' y' f _40053 P _40052) (@lem3653856 _93490 _93497 s x' y' f _40053 P _40052)). Qed.
Lemma lem3653858 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3653859 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1131 _93490 _93497 s x' y' f _40053 P _40052) = (term1132 _93490 _93497 s x' y' f _40053 P _40052).
Proof. exact (MK_COMB (@lem3653858) (@lem3653857 _93490 _93497 s x' y' f _40053 P _40052)). Qed.
Lemma lem3653860 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) : ((x' _40052 _40053) = (y' _40052 _40053)) = ((x' _40052 _40053) = (y' _40052 _40053)).
Proof. exact (eq_refl ((x' _40052 _40053) = (y' _40052 _40053))). Qed.
Lemma lem3653861 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) : (term1115 _93490 _93497 s f P x' y' _40052 _40053) = (term1133 _93490 _93497 s f P x' y' _40052 _40053).
Proof. exact (MK_COMB (@lem3653859 _93490 _93497 s x' y' f _40053 P _40052) (@lem3653860 _93490 _93497 x' y' _40052 _40053)). Qed.
Lemma lem3653862 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) : (term1114 _93490 _93497 s x' y' f _40053 P _40052) = (term1133 _93490 _93497 s f P x' y' _40052 _40053).
Proof. exact (TRANS (@lem3653828 _93490 _93497 s f P x' y' _40052 _40053) (@lem3653861 _93490 _93497 s f P x' y' _40052 _40053)). Qed.
Lemma lem3653864 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1134 _93490 _93497 P f t'.
Proof. exact (conj (@lem3653548 _93490 _93497 f t') (@lem3653555 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3653865 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term1089 _93490 _93497 x' y' f t') (h2 : term780 _93490 _93497 x' y' s P f t') : term1135 _93490 _93497 x' y' P f t'.
Proof. exact (conj (@lem3653539 _93490 _93497 x' y' f t' h1) (@lem3653864 _93490 _93497 x' y' s P f t' h2)). Qed.
Lemma lem3653866 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term1089 _93490 _93497 x' y' f t') (h2 : term780 _93490 _93497 x' y' s P f t') : term1136 _93490 _93497 s x' y' P f t'.
Proof. exact (conj (@lem3653531 _93490 _93497 x' y' s P f t' h2) (@lem3653865 _93490 _93497 x' y' s P f t' h1 h2)). Qed.
Lemma lem3653868 {_93490 _93497 : Type'} (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1133 _93490 _93497 s f P x' y' _40052 _40053.
Proof. exact (EQ_MP (@lem3653862 _93490 _93497 s f P x' y' _40052 _40053) (@lem3653825 _93490 _93497 _40053 _40052 x' y' s P f t' h1)). Qed.
Lemma lem3653869 {_93490 _93497 : Type'} (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1133 _93490 _93497 s f P x' y' _40052 _40053.
Proof. exact (@lem3653868 _93490 _93497 _40052 _40053 x' y' s P f t' h1). Qed.
Lemma lem3653870 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1137 _93490 _93497 s P x' y' f t'.
Proof. exact (@lem3653869 _93490 _93497 (@IMAGE _93490 _93497 f t') t' x' y' s P f t' h1). Qed.
Lemma lem3653873 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term1089 _93490 _93497 x' y' f t') (h2 : term780 _93490 _93497 x' y' s P f t') : (term1138 _93490 _93497 x' f t') = (term1138 _93490 _93497 y' f t').
Proof. exact (@lem3653870 _93490 _93497 x' y' s P f t' h2 (@lem3653866 _93490 _93497 x' y' s P f t' h1 h2)). Qed.
Lemma lem3653874 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term1089 _93490 _93497 x' y' f t') (h2 : term780 _93490 _93497 x' y' s P f t') : term1139 _93490 _93497 x' y' f t'.
Proof. exact (fun h0 : term1140 _93490 _93497 x' y' f t' => @lem3653873 _93490 _93497 x' y' s P f t' h1 h2). Qed.
Lemma lem3653876 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3653877 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) : (term1139 _93490 _93497 x' y' f t') = ((term1138 _93490 _93497 x' f t') = (term1138 _93490 _93497 y' f t')).
Proof. exact (@lem3653876 ((term1138 _93490 _93497 x' f t') = (term1138 _93490 _93497 y' f t'))). Qed.
Lemma lem3653878 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term1089 _93490 _93497 x' y' f t') (h2 : term780 _93490 _93497 x' y' s P f t') : (term1138 _93490 _93497 x' f t') = (term1138 _93490 _93497 y' f t').
Proof. exact (EQ_MP (@lem3653877 _93490 _93497 x' y' f t') (@lem3653874 _93490 _93497 x' y' s P f t' h1 h2)). Qed.
Lemma lem3653880 {_93490 _93497 : Type'} (x : _93490 -> _93497) : x = x.
Proof. exact (@lem21386 (_93490 -> _93497) x). Qed.
Lemma lem3653881 {_93490 _93497 : Type'} (x : _93490 -> _93497) : x = x.
Proof. exact (@lem3653880 _93490 _93497 x). Qed.
Lemma lem3653882 {_93490 _93497 : Type'} (f : _93490 -> _93497) : f = f.
Proof. exact (@lem3653881 _93490 _93497 f). Qed.
Lemma lem3653883 {_93490 _93497 : Type'} (f : _93490 -> _93497) : term990 _93490 _93497 f.
Proof. exact (fun h0 : term991 _93490 _93497 f => @lem3653882 _93490 _93497 f). Qed.
Lemma lem3653885 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3653886 {_93490 _93497 : Type'} (f : _93490 -> _93497) : (term990 _93490 _93497 f) = (f = f).
Proof. exact (@lem3653885 (f = f)). Qed.
Lemma lem3653887 {_93490 _93497 : Type'} (f : _93490 -> _93497) : f = f.
Proof. exact (EQ_MP (@lem3653886 _93490 _93497 f) (@lem3653883 _93490 _93497 f)). Qed.
Lemma lem3653905 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3653906 {_93490 _93497 : Type'} (_40115 : _93490) (_40117 : _93490) (_40114 : _93490 -> _93497) (_40116 : _93490 -> _93497) : (term947 _93490 _93497 _40114 _40115 _40116 _40117) = (term992 _93490 _93497 _40115 _40117 _40114 _40116).
Proof. exact (@lem3653905 ((@I (_93490 -> _93497) _40114 _40115) = (@I (_93490 -> _93497) _40116 _40117)) (term993 _93490 _93497 _40114 _40116)). Qed.
Lemma lem3653916 {_93490 : Type'} (_40115 : _93490) (_40117 : _93490) : (term994 _93490 _40115 _40117) = (term994 _93490 _40115 _40117).
Proof. exact (eq_refl (term994 _93490 _40115 _40117)). Qed.
Lemma lem3653917 {_93490 _93497 : Type'} (_40115 : _93490) (_40117 : _93490) (_40114 : _93490 -> _93497) (_40116 : _93490 -> _93497) : (term949 _93490 _93497 _40114 _40115 _40116 _40117) = (term995 _93490 _93497 _40115 _40117 _40114 _40116).
Proof. exact (MK_COMB (@lem3653916 _93490 _40115 _40117) (@lem3653906 _93490 _93497 _40115 _40117 _40114 _40116)). Qed.
Lemma lem3653921 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3653922 {_93490 _93497 : Type'} (_40115 : _93490) (_40117 : _93490) (_40114 : _93490 -> _93497) (_40116 : _93490 -> _93497) : (term995 _93490 _93497 _40115 _40117 _40114 _40116) = (term996 _93490 _93497 _40115 _40117 _40114 _40116).
Proof. exact (@lem3653921 ((@I (_93490 -> _93497) _40114 _40115) = (@I (_93490 -> _93497) _40116 _40117)) (term726 _93490 _40115 _40117) (term993 _93490 _93497 _40114 _40116)). Qed.
Lemma lem3653944 {_93490 _93497 : Type'} (_40115 : _93490) (_40117 : _93490) (_40114 : _93490 -> _93497) (_40116 : _93490 -> _93497) : (term949 _93490 _93497 _40114 _40115 _40116 _40117) = (term996 _93490 _93497 _40115 _40117 _40114 _40116).
Proof. exact (TRANS (@lem3653917 _93490 _93497 _40115 _40117 _40114 _40116) (@lem3653922 _93490 _93497 _40115 _40117 _40114 _40116)). Qed.
Lemma lem3653945 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3653946 {_93490 _93497 : Type'} (_40115 : _93490) (_40117 : _93490) (_40114 : _93490 -> _93497) (_40116 : _93490 -> _93497) : (term997 _93490 _93497 _40114 _40115 _40116 _40117) = (term998 _93490 _93497 _40115 _40117 _40114 _40116).
Proof. exact (MK_COMB (@lem3653945) (@lem3653944 _93490 _93497 _40115 _40117 _40114 _40116)). Qed.
Lemma lem3653968 {_93490 _93497 : Type'} (_40115 : _93490) (_40117 : _93490) (_40114 : _93490 -> _93497) (_40116 : _93490 -> _93497) : (term996 _93490 _93497 _40115 _40117 _40114 _40116) = (term996 _93490 _93497 _40115 _40117 _40114 _40116).
Proof. exact (eq_refl (term996 _93490 _93497 _40115 _40117 _40114 _40116)). Qed.
Lemma lem3653969 {_93490 _93497 : Type'} (_40115 : _93490) (_40117 : _93490) (_40114 : _93490 -> _93497) (_40116 : _93490 -> _93497) : ((term949 _93490 _93497 _40114 _40115 _40116 _40117) = (term996 _93490 _93497 _40115 _40117 _40114 _40116)) = ((term996 _93490 _93497 _40115 _40117 _40114 _40116) = (term996 _93490 _93497 _40115 _40117 _40114 _40116)).
Proof. exact (MK_COMB (@lem3653946 _93490 _93497 _40115 _40117 _40114 _40116) (@lem3653968 _93490 _93497 _40115 _40117 _40114 _40116)). Qed.
Lemma lem3653971 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3653972 (x : Prop) : (x = x) = True.
Proof. exact (@lem3653971 Prop x). Qed.
Lemma lem3653973 {_93490 _93497 : Type'} (_40115 : _93490) (_40117 : _93490) (_40114 : _93490 -> _93497) (_40116 : _93490 -> _93497) : ((term996 _93490 _93497 _40115 _40117 _40114 _40116) = (term996 _93490 _93497 _40115 _40117 _40114 _40116)) = True.
Proof. exact (@lem3653972 (term996 _93490 _93497 _40115 _40117 _40114 _40116)). Qed.
Lemma lem3653974 {_93490 _93497 : Type'} (_40115 : _93490) (_40117 : _93490) (_40114 : _93490 -> _93497) (_40116 : _93490 -> _93497) : ((term949 _93490 _93497 _40114 _40115 _40116 _40117) = (term996 _93490 _93497 _40115 _40117 _40114 _40116)) = True.
Proof. exact (TRANS (@lem3653969 _93490 _93497 _40115 _40117 _40114 _40116) (@lem3653973 _93490 _93497 _40115 _40117 _40114 _40116)). Qed.
Lemma lem3653975 {_93490 _93497 : Type'} (_40115 : _93490) (_40117 : _93490) (_40114 : _93490 -> _93497) (_40116 : _93490 -> _93497) : True = ((term949 _93490 _93497 _40114 _40115 _40116 _40117) = (term996 _93490 _93497 _40115 _40117 _40114 _40116)).
Proof. exact (SYM (@lem3653974 _93490 _93497 _40115 _40117 _40114 _40116)). Qed.
Lemma lem3653976 {_93490 _93497 : Type'} (_40115 : _93490) (_40117 : _93490) (_40114 : _93490 -> _93497) (_40116 : _93490 -> _93497) : (term949 _93490 _93497 _40114 _40115 _40116 _40117) = (term996 _93490 _93497 _40115 _40117 _40114 _40116).
Proof. exact (EQ_MP (@lem3653975 _93490 _93497 _40115 _40117 _40114 _40116) (@lem0)). Qed.
Lemma lem3653977 {_93490 _93497 : Type'} (_40115 : _93490) (_40117 : _93490) (_40114 : _93490 -> _93497) (_40116 : _93490 -> _93497) : term996 _93490 _93497 _40115 _40117 _40114 _40116.
Proof. exact (EQ_MP (@lem3653976 _93490 _93497 _40115 _40117 _40114 _40116) (@lem3653492 _93490 _93497 _40114 _40115 _40116 _40117)). Qed.
Lemma lem3653979 (b : Prop) (a : Prop) : (a \/ b) = (term971 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3653980 {_93490 _93497 : Type'} (_40114 : _93490 -> _93497) (_40115 : _93490) (_40116 : _93490 -> _93497) (_40117 : _93490) : (term996 _93490 _93497 _40115 _40117 _40114 _40116) = (term999 _93490 _93497 _40114 _40115 _40116 _40117).
Proof. exact (@lem3653979 (term1000 _93490 _93497 _40115 _40117 _40114 _40116) ((@I (_93490 -> _93497) _40114 _40115) = (@I (_93490 -> _93497) _40116 _40117))). Qed.
Lemma lem3653982 (a : Prop) (b : Prop) : (term973 a b) = (term974 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3653983 {_93490 _93497 : Type'} (_40115 : _93490) (_40117 : _93490) (_40114 : _93490 -> _93497) (_40116 : _93490 -> _93497) : (term1001 _93490 _93497 _40115 _40117 _40114 _40116) = (term1002 _93490 _93497 _40115 _40117 _40114 _40116).
Proof. exact (@lem3653982 (term726 _93490 _40115 _40117) (term993 _93490 _93497 _40114 _40116)). Qed.
Lemma lem3653985 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3653986 {_93490 : Type'} (_40115 : _93490) (_40117 : _93490) : (term1003 _93490 _40115 _40117) = (_40115 = _40117).
Proof. exact (@lem3653985 (_40115 = _40117)). Qed.
Lemma lem3653987 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3653988 {_93490 : Type'} (_40115 : _93490) (_40117 : _93490) : (term1004 _93490 _40115 _40117) = (term1005 _93490 _40115 _40117).
Proof. exact (MK_COMB (@lem3653987) (@lem3653986 _93490 _40115 _40117)). Qed.
Lemma lem3653990 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3653991 {_93490 _93497 : Type'} (_40114 : _93490 -> _93497) (_40116 : _93490 -> _93497) : (term1006 _93490 _93497 _40114 _40116) = (_40114 = _40116).
Proof. exact (@lem3653990 (_40114 = _40116)). Qed.
Lemma lem3653992 {_93490 _93497 : Type'} (_40115 : _93490) (_40117 : _93490) (_40114 : _93490 -> _93497) (_40116 : _93490 -> _93497) : (term1002 _93490 _93497 _40115 _40117 _40114 _40116) = (term1007 _93490 _93497 _40115 _40117 _40114 _40116).
Proof. exact (MK_COMB (@lem3653988 _93490 _40115 _40117) (@lem3653991 _93490 _93497 _40114 _40116)). Qed.
Lemma lem3653993 {_93490 _93497 : Type'} (_40115 : _93490) (_40117 : _93490) (_40114 : _93490 -> _93497) (_40116 : _93490 -> _93497) : (term1001 _93490 _93497 _40115 _40117 _40114 _40116) = (term1007 _93490 _93497 _40115 _40117 _40114 _40116).
Proof. exact (TRANS (@lem3653983 _93490 _93497 _40115 _40117 _40114 _40116) (@lem3653992 _93490 _93497 _40115 _40117 _40114 _40116)). Qed.
Lemma lem3653994 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3653995 {_93490 _93497 : Type'} (_40115 : _93490) (_40117 : _93490) (_40114 : _93490 -> _93497) (_40116 : _93490 -> _93497) : (term1008 _93490 _93497 _40115 _40117 _40114 _40116) = (term1009 _93490 _93497 _40115 _40117 _40114 _40116).
Proof. exact (MK_COMB (@lem3653994) (@lem3653993 _93490 _93497 _40115 _40117 _40114 _40116)). Qed.
Lemma lem3653996 {_93490 _93497 : Type'} (_40114 : _93490 -> _93497) (_40115 : _93490) (_40116 : _93490 -> _93497) (_40117 : _93490) : ((@I (_93490 -> _93497) _40114 _40115) = (@I (_93490 -> _93497) _40116 _40117)) = ((@I (_93490 -> _93497) _40114 _40115) = (@I (_93490 -> _93497) _40116 _40117)).
Proof. exact (eq_refl ((@I (_93490 -> _93497) _40114 _40115) = (@I (_93490 -> _93497) _40116 _40117))). Qed.
Lemma lem3653997 {_93490 _93497 : Type'} (_40114 : _93490 -> _93497) (_40115 : _93490) (_40116 : _93490 -> _93497) (_40117 : _93490) : (term999 _93490 _93497 _40114 _40115 _40116 _40117) = (term1010 _93490 _93497 _40114 _40115 _40116 _40117).
Proof. exact (MK_COMB (@lem3653995 _93490 _93497 _40115 _40117 _40114 _40116) (@lem3653996 _93490 _93497 _40114 _40115 _40116 _40117)). Qed.
Lemma lem3653998 {_93490 _93497 : Type'} (_40114 : _93490 -> _93497) (_40115 : _93490) (_40116 : _93490 -> _93497) (_40117 : _93490) : (term996 _93490 _93497 _40115 _40117 _40114 _40116) = (term1010 _93490 _93497 _40114 _40115 _40116 _40117).
Proof. exact (TRANS (@lem3653980 _93490 _93497 _40114 _40115 _40116 _40117) (@lem3653997 _93490 _93497 _40114 _40115 _40116 _40117)). Qed.
Lemma lem3654000 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term1089 _93490 _93497 x' y' f t') (h2 : term780 _93490 _93497 x' y' s P f t') : term1141 _93490 _93497 x' y' t' f.
Proof. exact (conj (@lem3653878 _93490 _93497 x' y' s P f t' h1 h2) (@lem3653887 _93490 _93497 f)). Qed.
Lemma lem3654002 {_93490 _93497 : Type'} (_40114 : _93490 -> _93497) (_40115 : _93490) (_40116 : _93490 -> _93497) (_40117 : _93490) : term1010 _93490 _93497 _40114 _40115 _40116 _40117.
Proof. exact (EQ_MP (@lem3653998 _93490 _93497 _40114 _40115 _40116 _40117) (@lem3653977 _93490 _93497 _40115 _40117 _40114 _40116)). Qed.
Lemma lem3654003 {_93490 _93497 : Type'} (_40114 : _93490 -> _93497) (_40115 : _93490) (_40116 : _93490 -> _93497) (_40117 : _93490) : term1010 _93490 _93497 _40114 _40115 _40116 _40117.
Proof. exact (@lem3654002 _93490 _93497 _40114 _40115 _40116 _40117). Qed.
Lemma lem3654004 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) : term1142 _93490 _93497 x' y' f t'.
Proof. exact (@lem3654003 _93490 _93497 f (term1138 _93490 _93497 x' f t') f (term1138 _93490 _93497 y' f t')). Qed.
Lemma lem3654007 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term1089 _93490 _93497 x' y' f t') (h2 : term780 _93490 _93497 x' y' s P f t') : (term1091 _93490 _93497 x' f t') = (term1091 _93490 _93497 y' f t').
Proof. exact (@lem3654004 _93490 _93497 x' y' f t' (@lem3654000 _93490 _93497 x' y' s P f t' h1 h2)). Qed.
Lemma lem3654008 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1143 _93490 _93497 x' y' f t'.
Proof. exact (fun h0 : term1089 _93490 _93497 x' y' f t' => @lem3654007 _93490 _93497 x' y' s P f t' h0 h1). Qed.
Lemma lem3654010 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3654011 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) : (term1143 _93490 _93497 x' y' f t') = ((term1091 _93490 _93497 x' f t') = (term1091 _93490 _93497 y' f t')).
Proof. exact (@lem3654010 ((term1091 _93490 _93497 x' f t') = (term1091 _93490 _93497 y' f t'))). Qed.
Lemma lem3654012 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : (term1091 _93490 _93497 x' f t') = (term1091 _93490 _93497 y' f t').
Proof. exact (EQ_MP (@lem3654011 _93490 _93497 x' y' f t') (@lem3654008 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3654014 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : @SUBSET _93490 t' s.
Proof. exact (proj1 (@lem3651399 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3654015 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term950 _93490 t' s.
Proof. exact (fun h0 : term227 _93490 t' s => @lem3654014 _93490 _93497 x' y' s P f t' h1). Qed.
Lemma lem3654017 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3654018 {_93490 : Type'} (t' : _93490 -> Prop) (s : _93490 -> Prop) : (term950 _93490 t' s) = (@SUBSET _93490 t' s).
Proof. exact (@lem3654017 (@SUBSET _93490 t' s)). Qed.
Lemma lem3654019 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : @SUBSET _93490 t' s.
Proof. exact (EQ_MP (@lem3654018 _93490 t' s) (@lem3654015 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3654021 {_93497 : Type'} (x : _93497 -> Prop) : x = x.
Proof. exact (@lem21386 (_93497 -> Prop) x). Qed.
Lemma lem3654022 {_93497 : Type'} (x : _93497 -> Prop) : x = x.
Proof. exact (@lem3654021 _93497 x). Qed.
Lemma lem3654023 {_93490 _93497 : Type'} (f : _93490 -> _93497) (t' : _93490 -> Prop) : (@IMAGE _93490 _93497 f t') = (@IMAGE _93490 _93497 f t').
Proof. exact (@lem3654022 _93497 (@IMAGE _93490 _93497 f t')). Qed.
Lemma lem3654024 {_93490 _93497 : Type'} (f : _93490 -> _93497) (t' : _93490 -> Prop) : term1092 _93490 _93497 f t'.
Proof. exact (fun h0 : term1093 _93490 _93497 f t' => @lem3654023 _93490 _93497 f t'). Qed.
Lemma lem3654026 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3654027 {_93490 _93497 : Type'} (f : _93490 -> _93497) (t' : _93490 -> Prop) : (term1092 _93490 _93497 f t') = ((@IMAGE _93490 _93497 f t') = (@IMAGE _93490 _93497 f t')).
Proof. exact (@lem3654026 ((@IMAGE _93490 _93497 f t') = (@IMAGE _93490 _93497 f t'))). Qed.
Lemma lem3654028 {_93490 _93497 : Type'} (f : _93490 -> _93497) (t' : _93490 -> Prop) : (@IMAGE _93490 _93497 f t') = (@IMAGE _93490 _93497 f t').
Proof. exact (EQ_MP (@lem3654027 _93490 _93497 f t') (@lem3654024 _93490 _93497 f t')). Qed.
Lemma lem3654030 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term45 _93490 _93497 P f t'.
Proof. exact (proj2 (@lem3651401 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3654031 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term954 _93490 _93497 P f t'.
Proof. exact (fun h0 : term136 _93490 _93497 P f t' => @lem3654030 _93490 _93497 x' y' s P f t' h1). Qed.
Lemma lem3654033 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3654034 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) : (term954 _93490 _93497 P f t') = (term45 _93490 _93497 P f t').
Proof. exact (@lem3654033 (term45 _93490 _93497 P f t')). Qed.
Lemma lem3654035 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term45 _93490 _93497 P f t'.
Proof. exact (EQ_MP (@lem3654034 _93490 _93497 P f t') (@lem3654031 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3654041 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3654042 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (s : _93490 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term938 _93490 _93497 s x' f _40053 P _40052) = (term1144 _93490 _93497 x' s f _40053 P _40052).
Proof. exact (@lem3654041 (term874 _93490 _93497 x' _40052 _40053) (term227 _93490 _40053 s) (term928 _93490 _93497 f _40053 P _40052)). Qed.
Lemma lem3654056 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3654057 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1098 _93490 _93497 s f _40053 P _40052) = (term1099 _93490 _93497 f _40053 s P _40052).
Proof. exact (@lem3654056 (term95 _93490 _93497 _40052 f _40053) (term227 _93490 _40053 s) (term119 _93497 P _40052)). Qed.
Lemma lem3654073 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3654074 {_93490 _93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1100 _93490 _93497 _40053 s P _40052) = (term1101 _93490 _93497 P _40052 _40053 s).
Proof. exact (@lem3654073 (term119 _93497 P _40052) (term227 _93490 _40053 s)). Qed.
Lemma lem3654080 {_93490 _93497 : Type'} (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) : (term1102 _93490 _93497 _40052 f _40053) = (term1102 _93490 _93497 _40052 f _40053).
Proof. exact (eq_refl (term1102 _93490 _93497 _40052 f _40053)). Qed.
Lemma lem3654081 {_93490 _93497 : Type'} (f : _93490 -> _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1099 _93490 _93497 f _40053 s P _40052) = (term1103 _93490 _93497 f P _40052 _40053 s).
Proof. exact (MK_COMB (@lem3654080 _93490 _93497 _40052 f _40053) (@lem3654074 _93490 _93497 P _40052 _40053 s)). Qed.
Lemma lem3654085 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3654086 {_93490 _93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1103 _93490 _93497 f P _40052 _40053 s) = (term1104 _93490 _93497 P _40052 f _40053 s).
Proof. exact (@lem3654085 (term119 _93497 P _40052) (term95 _93490 _93497 _40052 f _40053) (term227 _93490 _40053 s)). Qed.
Lemma lem3654104 {_93490 _93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1099 _93490 _93497 f _40053 s P _40052) = (term1104 _93490 _93497 P _40052 f _40053 s).
Proof. exact (TRANS (@lem3654081 _93490 _93497 f P _40052 _40053 s) (@lem3654086 _93490 _93497 P _40052 f _40053 s)). Qed.
Lemma lem3654105 {_93490 _93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1098 _93490 _93497 s f _40053 P _40052) = (term1104 _93490 _93497 P _40052 f _40053 s).
Proof. exact (TRANS (@lem3654057 _93490 _93497 f _40053 s P _40052) (@lem3654104 _93490 _93497 P _40052 f _40053 s)). Qed.
Lemma lem3654106 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) : (term1145 _93490 _93497 x' _40052 _40053) = (term1145 _93490 _93497 x' _40052 _40053).
Proof. exact (eq_refl (term1145 _93490 _93497 x' _40052 _40053)). Qed.
Lemma lem3654107 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1144 _93490 _93497 x' s f _40053 P _40052) = (term1146 _93490 _93497 x' P _40052 f _40053 s).
Proof. exact (MK_COMB (@lem3654106 _93490 _93497 x' _40052 _40053) (@lem3654105 _93490 _93497 P _40052 f _40053 s)). Qed.
Lemma lem3654118 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term938 _93490 _93497 s x' f _40053 P _40052) = (term1146 _93490 _93497 x' P _40052 f _40053 s).
Proof. exact (TRANS (@lem3654042 _93490 _93497 x' s f _40053 P _40052) (@lem3654107 _93490 _93497 x' P _40052 f _40053 s)). Qed.
Lemma lem3654119 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3654120 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1147 _93490 _93497 s x' f _40053 P _40052) = (term1148 _93490 _93497 x' P _40052 f _40053 s).
Proof. exact (MK_COMB (@lem3654119) (@lem3654118 _93490 _93497 x' P _40052 f _40053 s)). Qed.
Lemma lem3654134 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3654135 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1098 _93490 _93497 s f _40053 P _40052) = (term1099 _93490 _93497 f _40053 s P _40052).
Proof. exact (@lem3654134 (term95 _93490 _93497 _40052 f _40053) (term227 _93490 _40053 s) (term119 _93497 P _40052)). Qed.
Lemma lem3654151 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3654152 {_93490 _93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1100 _93490 _93497 _40053 s P _40052) = (term1101 _93490 _93497 P _40052 _40053 s).
Proof. exact (@lem3654151 (term119 _93497 P _40052) (term227 _93490 _40053 s)). Qed.
Lemma lem3654158 {_93490 _93497 : Type'} (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) : (term1102 _93490 _93497 _40052 f _40053) = (term1102 _93490 _93497 _40052 f _40053).
Proof. exact (eq_refl (term1102 _93490 _93497 _40052 f _40053)). Qed.
Lemma lem3654159 {_93490 _93497 : Type'} (f : _93490 -> _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1099 _93490 _93497 f _40053 s P _40052) = (term1103 _93490 _93497 f P _40052 _40053 s).
Proof. exact (MK_COMB (@lem3654158 _93490 _93497 _40052 f _40053) (@lem3654152 _93490 _93497 P _40052 _40053 s)). Qed.
Lemma lem3654163 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3654164 {_93490 _93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1103 _93490 _93497 f P _40052 _40053 s) = (term1104 _93490 _93497 P _40052 f _40053 s).
Proof. exact (@lem3654163 (term119 _93497 P _40052) (term95 _93490 _93497 _40052 f _40053) (term227 _93490 _40053 s)). Qed.
Lemma lem3654182 {_93490 _93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1099 _93490 _93497 f _40053 s P _40052) = (term1104 _93490 _93497 P _40052 f _40053 s).
Proof. exact (TRANS (@lem3654159 _93490 _93497 f P _40052 _40053 s) (@lem3654164 _93490 _93497 P _40052 f _40053 s)). Qed.
Lemma lem3654183 {_93490 _93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1098 _93490 _93497 s f _40053 P _40052) = (term1104 _93490 _93497 P _40052 f _40053 s).
Proof. exact (TRANS (@lem3654135 _93490 _93497 f _40053 s P _40052) (@lem3654182 _93490 _93497 P _40052 f _40053 s)). Qed.
Lemma lem3654184 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) : (term1145 _93490 _93497 x' _40052 _40053) = (term1145 _93490 _93497 x' _40052 _40053).
Proof. exact (eq_refl (term1145 _93490 _93497 x' _40052 _40053)). Qed.
Lemma lem3654185 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1144 _93490 _93497 x' s f _40053 P _40052) = (term1146 _93490 _93497 x' P _40052 f _40053 s).
Proof. exact (MK_COMB (@lem3654184 _93490 _93497 x' _40052 _40053) (@lem3654183 _93490 _93497 P _40052 f _40053 s)). Qed.
Lemma lem3654196 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : ((term938 _93490 _93497 s x' f _40053 P _40052) = (term1144 _93490 _93497 x' s f _40053 P _40052)) = ((term1146 _93490 _93497 x' P _40052 f _40053 s) = (term1146 _93490 _93497 x' P _40052 f _40053 s)).
Proof. exact (MK_COMB (@lem3654120 _93490 _93497 x' P _40052 f _40053 s) (@lem3654185 _93490 _93497 x' P _40052 f _40053 s)). Qed.
Lemma lem3654198 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3654199 (x : Prop) : (x = x) = True.
Proof. exact (@lem3654198 Prop x). Qed.
Lemma lem3654200 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : ((term1146 _93490 _93497 x' P _40052 f _40053 s) = (term1146 _93490 _93497 x' P _40052 f _40053 s)) = True.
Proof. exact (@lem3654199 (term1146 _93490 _93497 x' P _40052 f _40053 s)). Qed.
Lemma lem3654201 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (s : _93490 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : ((term938 _93490 _93497 s x' f _40053 P _40052) = (term1144 _93490 _93497 x' s f _40053 P _40052)) = True.
Proof. exact (TRANS (@lem3654196 _93490 _93497 x' P _40052 f _40053 s) (@lem3654200 _93490 _93497 x' P _40052 f _40053 s)). Qed.
Lemma lem3654202 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (s : _93490 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : True = ((term938 _93490 _93497 s x' f _40053 P _40052) = (term1144 _93490 _93497 x' s f _40053 P _40052)).
Proof. exact (SYM (@lem3654201 _93490 _93497 x' s f _40053 P _40052)). Qed.
Lemma lem3654203 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (s : _93490 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term938 _93490 _93497 s x' f _40053 P _40052) = (term1144 _93490 _93497 x' s f _40053 P _40052).
Proof. exact (EQ_MP (@lem3654202 _93490 _93497 x' s f _40053 P _40052) (@lem0)). Qed.
Lemma lem3654204 {_93490 _93497 : Type'} (_40053 : _93490 -> Prop) (_40052 : _93497 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1144 _93490 _93497 x' s f _40053 P _40052.
Proof. exact (EQ_MP (@lem3654203 _93490 _93497 x' s f _40053 P _40052) (@lem3651952 _93490 _93497 _40053 _40052 x' y' s P f t' h1)). Qed.
Lemma lem3654206 (b : Prop) (a : Prop) : (a \/ b) = (term971 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3654207 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (x' : type840 _93490 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) : (term1144 _93490 _93497 x' s f _40053 P _40052) = (term1149 _93490 _93497 s f P x' _40052 _40053).
Proof. exact (@lem3654206 (term1098 _93490 _93497 s f _40053 P _40052) (term874 _93490 _93497 x' _40052 _40053)). Qed.
Lemma lem3654209 (a : Prop) (b : Prop) : (term973 a b) = (term974 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3654210 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1150 _93490 _93497 s f _40053 P _40052) = (term1151 _93490 _93497 s f _40053 P _40052).
Proof. exact (@lem3654209 (term227 _93490 _40053 s) (term928 _93490 _93497 f _40053 P _40052)). Qed.
Lemma lem3654212 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3654213 {_93490 : Type'} (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term978 _93490 _40053 s) = (@SUBSET _93490 _40053 s).
Proof. exact (@lem3654212 (@SUBSET _93490 _40053 s)). Qed.
Lemma lem3654214 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3654215 {_93490 : Type'} (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term979 _93490 _40053 s) = (term53 _93490 _40053 s).
Proof. exact (MK_COMB (@lem3654214) (@lem3654213 _93490 _40053 s)). Qed.
Lemma lem3654217 (a : Prop) (b : Prop) : (term973 a b) = (term974 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3654218 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1121 _93490 _93497 f _40053 P _40052) = (term1122 _93490 _93497 f _40053 P _40052).
Proof. exact (@lem3654217 (term95 _93490 _93497 _40052 f _40053) (term119 _93497 P _40052)). Qed.
Lemma lem3654220 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3654221 {_93490 _93497 : Type'} (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) : (term1123 _93490 _93497 _40052 f _40053) = (_40052 = (@IMAGE _93490 _93497 f _40053)).
Proof. exact (@lem3654220 (_40052 = (@IMAGE _93490 _93497 f _40053))). Qed.
Lemma lem3654222 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3654223 {_93490 _93497 : Type'} (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) : (term1124 _93490 _93497 _40052 f _40053) = (term1125 _93490 _93497 _40052 f _40053).
Proof. exact (MK_COMB (@lem3654222) (@lem3654221 _93490 _93497 _40052 f _40053)). Qed.
Lemma lem3654225 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3654226 {_93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1126 _93497 P _40052) = (P _40052).
Proof. exact (@lem3654225 (P _40052)). Qed.
Lemma lem3654227 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1122 _93490 _93497 f _40053 P _40052) = (term1127 _93490 _93497 f _40053 P _40052).
Proof. exact (MK_COMB (@lem3654223 _93490 _93497 _40052 f _40053) (@lem3654226 _93497 P _40052)). Qed.
Lemma lem3654228 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1121 _93490 _93497 f _40053 P _40052) = (term1127 _93490 _93497 f _40053 P _40052).
Proof. exact (TRANS (@lem3654218 _93490 _93497 f _40053 P _40052) (@lem3654227 _93490 _93497 f _40053 P _40052)). Qed.
Lemma lem3654229 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1151 _93490 _93497 s f _40053 P _40052) = (term1152 _93490 _93497 s f _40053 P _40052).
Proof. exact (MK_COMB (@lem3654215 _93490 _40053 s) (@lem3654228 _93490 _93497 f _40053 P _40052)). Qed.
Lemma lem3654230 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1150 _93490 _93497 s f _40053 P _40052) = (term1152 _93490 _93497 s f _40053 P _40052).
Proof. exact (TRANS (@lem3654210 _93490 _93497 s f _40053 P _40052) (@lem3654229 _93490 _93497 s f _40053 P _40052)). Qed.
Lemma lem3654231 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3654232 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1153 _93490 _93497 s f _40053 P _40052) = (term1154 _93490 _93497 s f _40053 P _40052).
Proof. exact (MK_COMB (@lem3654231) (@lem3654230 _93490 _93497 s f _40053 P _40052)). Qed.
Lemma lem3654233 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) : (term874 _93490 _93497 x' _40052 _40053) = (term874 _93490 _93497 x' _40052 _40053).
Proof. exact (eq_refl (term874 _93490 _93497 x' _40052 _40053)). Qed.
Lemma lem3654234 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (x' : type840 _93490 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) : (term1149 _93490 _93497 s f P x' _40052 _40053) = (term1155 _93490 _93497 s f P x' _40052 _40053).
Proof. exact (MK_COMB (@lem3654232 _93490 _93497 s f _40053 P _40052) (@lem3654233 _93490 _93497 x' _40052 _40053)). Qed.
Lemma lem3654235 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (x' : type840 _93490 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) : (term1144 _93490 _93497 x' s f _40053 P _40052) = (term1155 _93490 _93497 s f P x' _40052 _40053).
Proof. exact (TRANS (@lem3654207 _93490 _93497 s f P x' _40052 _40053) (@lem3654234 _93490 _93497 s f P x' _40052 _40053)). Qed.
Lemma lem3654237 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1134 _93490 _93497 P f t'.
Proof. exact (conj (@lem3654028 _93490 _93497 f t') (@lem3654035 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3654238 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1156 _93490 _93497 s P f t'.
Proof. exact (conj (@lem3654019 _93490 _93497 x' y' s P f t' h1) (@lem3654237 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3654240 {_93490 _93497 : Type'} (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1155 _93490 _93497 s f P x' _40052 _40053.
Proof. exact (EQ_MP (@lem3654235 _93490 _93497 s f P x' _40052 _40053) (@lem3654204 _93490 _93497 _40053 _40052 x' y' s P f t' h1)). Qed.
Lemma lem3654241 {_93490 _93497 : Type'} (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1155 _93490 _93497 s f P x' _40052 _40053.
Proof. exact (@lem3654240 _93490 _93497 _40052 _40053 x' y' s P f t' h1). Qed.
Lemma lem3654242 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1157 _93490 _93497 s P x' f t'.
Proof. exact (@lem3654241 _93490 _93497 (@IMAGE _93490 _93497 f t') t' x' y' s P f t' h1). Qed.
Lemma lem3654245 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1158 _93490 _93497 x' f t'.
Proof. exact (@lem3654242 _93490 _93497 x' y' s P f t' h1 (@lem3654238 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3654246 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1159 _93490 _93497 x' f t'.
Proof. exact (fun h0 : term1160 _93490 _93497 x' f t' => @lem3654245 _93490 _93497 x' y' s P f t' h1). Qed.
Lemma lem3654248 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3654249 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) : (term1159 _93490 _93497 x' f t') = (term1158 _93490 _93497 x' f t').
Proof. exact (@lem3654248 (term1158 _93490 _93497 x' f t')). Qed.
Lemma lem3654250 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1158 _93490 _93497 x' f t'.
Proof. exact (EQ_MP (@lem3654249 _93490 _93497 x' f t') (@lem3654246 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3654252 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : @SUBSET _93490 t' s.
Proof. exact (proj1 (@lem3651399 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3654253 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term950 _93490 t' s.
Proof. exact (fun h0 : term227 _93490 t' s => @lem3654252 _93490 _93497 x' y' s P f t' h1). Qed.
Lemma lem3654255 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3654256 {_93490 : Type'} (t' : _93490 -> Prop) (s : _93490 -> Prop) : (term950 _93490 t' s) = (@SUBSET _93490 t' s).
Proof. exact (@lem3654255 (@SUBSET _93490 t' s)). Qed.
Lemma lem3654257 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : @SUBSET _93490 t' s.
Proof. exact (EQ_MP (@lem3654256 _93490 t' s) (@lem3654253 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3654259 {_93497 : Type'} (x : _93497 -> Prop) : x = x.
Proof. exact (@lem21386 (_93497 -> Prop) x). Qed.
Lemma lem3654260 {_93497 : Type'} (x : _93497 -> Prop) : x = x.
Proof. exact (@lem3654259 _93497 x). Qed.
Lemma lem3654261 {_93490 _93497 : Type'} (f : _93490 -> _93497) (t' : _93490 -> Prop) : (@IMAGE _93490 _93497 f t') = (@IMAGE _93490 _93497 f t').
Proof. exact (@lem3654260 _93497 (@IMAGE _93490 _93497 f t')). Qed.
Lemma lem3654262 {_93490 _93497 : Type'} (f : _93490 -> _93497) (t' : _93490 -> Prop) : term1092 _93490 _93497 f t'.
Proof. exact (fun h0 : term1093 _93490 _93497 f t' => @lem3654261 _93490 _93497 f t'). Qed.
Lemma lem3654264 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3654265 {_93490 _93497 : Type'} (f : _93490 -> _93497) (t' : _93490 -> Prop) : (term1092 _93490 _93497 f t') = ((@IMAGE _93490 _93497 f t') = (@IMAGE _93490 _93497 f t')).
Proof. exact (@lem3654264 ((@IMAGE _93490 _93497 f t') = (@IMAGE _93490 _93497 f t'))). Qed.
Lemma lem3654266 {_93490 _93497 : Type'} (f : _93490 -> _93497) (t' : _93490 -> Prop) : (@IMAGE _93490 _93497 f t') = (@IMAGE _93490 _93497 f t').
Proof. exact (EQ_MP (@lem3654265 _93490 _93497 f t') (@lem3654262 _93490 _93497 f t')). Qed.
Lemma lem3654268 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term45 _93490 _93497 P f t'.
Proof. exact (proj2 (@lem3651401 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3654269 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term954 _93490 _93497 P f t'.
Proof. exact (fun h0 : term136 _93490 _93497 P f t' => @lem3654268 _93490 _93497 x' y' s P f t' h1). Qed.
Lemma lem3654271 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3654272 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) : (term954 _93490 _93497 P f t') = (term45 _93490 _93497 P f t').
Proof. exact (@lem3654271 (term45 _93490 _93497 P f t')). Qed.
Lemma lem3654273 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term45 _93490 _93497 P f t'.
Proof. exact (EQ_MP (@lem3654272 _93490 _93497 P f t') (@lem3654269 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3654279 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3654280 {_93490 _93497 : Type'} (y' : type840 _93490 _93497) (s : _93490 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term938 _93490 _93497 s y' f _40053 P _40052) = (term1144 _93490 _93497 y' s f _40053 P _40052).
Proof. exact (@lem3654279 (term874 _93490 _93497 y' _40052 _40053) (term227 _93490 _40053 s) (term928 _93490 _93497 f _40053 P _40052)). Qed.
Lemma lem3654294 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3654295 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1098 _93490 _93497 s f _40053 P _40052) = (term1099 _93490 _93497 f _40053 s P _40052).
Proof. exact (@lem3654294 (term95 _93490 _93497 _40052 f _40053) (term227 _93490 _40053 s) (term119 _93497 P _40052)). Qed.
Lemma lem3654311 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3654312 {_93490 _93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1100 _93490 _93497 _40053 s P _40052) = (term1101 _93490 _93497 P _40052 _40053 s).
Proof. exact (@lem3654311 (term119 _93497 P _40052) (term227 _93490 _40053 s)). Qed.
Lemma lem3654318 {_93490 _93497 : Type'} (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) : (term1102 _93490 _93497 _40052 f _40053) = (term1102 _93490 _93497 _40052 f _40053).
Proof. exact (eq_refl (term1102 _93490 _93497 _40052 f _40053)). Qed.
Lemma lem3654319 {_93490 _93497 : Type'} (f : _93490 -> _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1099 _93490 _93497 f _40053 s P _40052) = (term1103 _93490 _93497 f P _40052 _40053 s).
Proof. exact (MK_COMB (@lem3654318 _93490 _93497 _40052 f _40053) (@lem3654312 _93490 _93497 P _40052 _40053 s)). Qed.
Lemma lem3654323 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3654324 {_93490 _93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1103 _93490 _93497 f P _40052 _40053 s) = (term1104 _93490 _93497 P _40052 f _40053 s).
Proof. exact (@lem3654323 (term119 _93497 P _40052) (term95 _93490 _93497 _40052 f _40053) (term227 _93490 _40053 s)). Qed.
Lemma lem3654342 {_93490 _93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1099 _93490 _93497 f _40053 s P _40052) = (term1104 _93490 _93497 P _40052 f _40053 s).
Proof. exact (TRANS (@lem3654319 _93490 _93497 f P _40052 _40053 s) (@lem3654324 _93490 _93497 P _40052 f _40053 s)). Qed.
Lemma lem3654343 {_93490 _93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1098 _93490 _93497 s f _40053 P _40052) = (term1104 _93490 _93497 P _40052 f _40053 s).
Proof. exact (TRANS (@lem3654295 _93490 _93497 f _40053 s P _40052) (@lem3654342 _93490 _93497 P _40052 f _40053 s)). Qed.
Lemma lem3654344 {_93490 _93497 : Type'} (y' : type840 _93490 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) : (term1145 _93490 _93497 y' _40052 _40053) = (term1145 _93490 _93497 y' _40052 _40053).
Proof. exact (eq_refl (term1145 _93490 _93497 y' _40052 _40053)). Qed.
Lemma lem3654345 {_93490 _93497 : Type'} (y' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1144 _93490 _93497 y' s f _40053 P _40052) = (term1146 _93490 _93497 y' P _40052 f _40053 s).
Proof. exact (MK_COMB (@lem3654344 _93490 _93497 y' _40052 _40053) (@lem3654343 _93490 _93497 P _40052 f _40053 s)). Qed.
Lemma lem3654356 {_93490 _93497 : Type'} (y' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term938 _93490 _93497 s y' f _40053 P _40052) = (term1146 _93490 _93497 y' P _40052 f _40053 s).
Proof. exact (TRANS (@lem3654280 _93490 _93497 y' s f _40053 P _40052) (@lem3654345 _93490 _93497 y' P _40052 f _40053 s)). Qed.
Lemma lem3654357 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3654358 {_93490 _93497 : Type'} (y' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1147 _93490 _93497 s y' f _40053 P _40052) = (term1148 _93490 _93497 y' P _40052 f _40053 s).
Proof. exact (MK_COMB (@lem3654357) (@lem3654356 _93490 _93497 y' P _40052 f _40053 s)). Qed.
Lemma lem3654372 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3654373 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1098 _93490 _93497 s f _40053 P _40052) = (term1099 _93490 _93497 f _40053 s P _40052).
Proof. exact (@lem3654372 (term95 _93490 _93497 _40052 f _40053) (term227 _93490 _40053 s) (term119 _93497 P _40052)). Qed.
Lemma lem3654389 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3654390 {_93490 _93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1100 _93490 _93497 _40053 s P _40052) = (term1101 _93490 _93497 P _40052 _40053 s).
Proof. exact (@lem3654389 (term119 _93497 P _40052) (term227 _93490 _40053 s)). Qed.
Lemma lem3654396 {_93490 _93497 : Type'} (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) : (term1102 _93490 _93497 _40052 f _40053) = (term1102 _93490 _93497 _40052 f _40053).
Proof. exact (eq_refl (term1102 _93490 _93497 _40052 f _40053)). Qed.
Lemma lem3654397 {_93490 _93497 : Type'} (f : _93490 -> _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1099 _93490 _93497 f _40053 s P _40052) = (term1103 _93490 _93497 f P _40052 _40053 s).
Proof. exact (MK_COMB (@lem3654396 _93490 _93497 _40052 f _40053) (@lem3654390 _93490 _93497 P _40052 _40053 s)). Qed.
Lemma lem3654401 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3654402 {_93490 _93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1103 _93490 _93497 f P _40052 _40053 s) = (term1104 _93490 _93497 P _40052 f _40053 s).
Proof. exact (@lem3654401 (term119 _93497 P _40052) (term95 _93490 _93497 _40052 f _40053) (term227 _93490 _40053 s)). Qed.
Lemma lem3654420 {_93490 _93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1099 _93490 _93497 f _40053 s P _40052) = (term1104 _93490 _93497 P _40052 f _40053 s).
Proof. exact (TRANS (@lem3654397 _93490 _93497 f P _40052 _40053 s) (@lem3654402 _93490 _93497 P _40052 f _40053 s)). Qed.
Lemma lem3654421 {_93490 _93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1098 _93490 _93497 s f _40053 P _40052) = (term1104 _93490 _93497 P _40052 f _40053 s).
Proof. exact (TRANS (@lem3654373 _93490 _93497 f _40053 s P _40052) (@lem3654420 _93490 _93497 P _40052 f _40053 s)). Qed.
Lemma lem3654422 {_93490 _93497 : Type'} (y' : type840 _93490 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) : (term1145 _93490 _93497 y' _40052 _40053) = (term1145 _93490 _93497 y' _40052 _40053).
Proof. exact (eq_refl (term1145 _93490 _93497 y' _40052 _40053)). Qed.
Lemma lem3654423 {_93490 _93497 : Type'} (y' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1144 _93490 _93497 y' s f _40053 P _40052) = (term1146 _93490 _93497 y' P _40052 f _40053 s).
Proof. exact (MK_COMB (@lem3654422 _93490 _93497 y' _40052 _40053) (@lem3654421 _93490 _93497 P _40052 f _40053 s)). Qed.
Lemma lem3654434 {_93490 _93497 : Type'} (y' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : ((term938 _93490 _93497 s y' f _40053 P _40052) = (term1144 _93490 _93497 y' s f _40053 P _40052)) = ((term1146 _93490 _93497 y' P _40052 f _40053 s) = (term1146 _93490 _93497 y' P _40052 f _40053 s)).
Proof. exact (MK_COMB (@lem3654358 _93490 _93497 y' P _40052 f _40053 s) (@lem3654423 _93490 _93497 y' P _40052 f _40053 s)). Qed.
Lemma lem3654436 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3654437 (x : Prop) : (x = x) = True.
Proof. exact (@lem3654436 Prop x). Qed.
Lemma lem3654438 {_93490 _93497 : Type'} (y' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : ((term1146 _93490 _93497 y' P _40052 f _40053 s) = (term1146 _93490 _93497 y' P _40052 f _40053 s)) = True.
Proof. exact (@lem3654437 (term1146 _93490 _93497 y' P _40052 f _40053 s)). Qed.
Lemma lem3654439 {_93490 _93497 : Type'} (y' : type840 _93490 _93497) (s : _93490 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : ((term938 _93490 _93497 s y' f _40053 P _40052) = (term1144 _93490 _93497 y' s f _40053 P _40052)) = True.
Proof. exact (TRANS (@lem3654434 _93490 _93497 y' P _40052 f _40053 s) (@lem3654438 _93490 _93497 y' P _40052 f _40053 s)). Qed.
Lemma lem3654440 {_93490 _93497 : Type'} (y' : type840 _93490 _93497) (s : _93490 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : True = ((term938 _93490 _93497 s y' f _40053 P _40052) = (term1144 _93490 _93497 y' s f _40053 P _40052)).
Proof. exact (SYM (@lem3654439 _93490 _93497 y' s f _40053 P _40052)). Qed.
Lemma lem3654441 {_93490 _93497 : Type'} (y' : type840 _93490 _93497) (s : _93490 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term938 _93490 _93497 s y' f _40053 P _40052) = (term1144 _93490 _93497 y' s f _40053 P _40052).
Proof. exact (EQ_MP (@lem3654440 _93490 _93497 y' s f _40053 P _40052) (@lem0)). Qed.
Lemma lem3654442 {_93490 _93497 : Type'} (_40053 : _93490 -> Prop) (_40052 : _93497 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1144 _93490 _93497 y' s f _40053 P _40052.
Proof. exact (EQ_MP (@lem3654441 _93490 _93497 y' s f _40053 P _40052) (@lem3651970 _93490 _93497 _40053 _40052 x' y' s P f t' h1)). Qed.
Lemma lem3654444 (b : Prop) (a : Prop) : (a \/ b) = (term971 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3654445 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (y' : type840 _93490 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) : (term1144 _93490 _93497 y' s f _40053 P _40052) = (term1149 _93490 _93497 s f P y' _40052 _40053).
Proof. exact (@lem3654444 (term1098 _93490 _93497 s f _40053 P _40052) (term874 _93490 _93497 y' _40052 _40053)). Qed.
Lemma lem3654447 (a : Prop) (b : Prop) : (term973 a b) = (term974 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3654448 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1150 _93490 _93497 s f _40053 P _40052) = (term1151 _93490 _93497 s f _40053 P _40052).
Proof. exact (@lem3654447 (term227 _93490 _40053 s) (term928 _93490 _93497 f _40053 P _40052)). Qed.
Lemma lem3654450 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3654451 {_93490 : Type'} (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term978 _93490 _40053 s) = (@SUBSET _93490 _40053 s).
Proof. exact (@lem3654450 (@SUBSET _93490 _40053 s)). Qed.
Lemma lem3654452 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3654453 {_93490 : Type'} (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term979 _93490 _40053 s) = (term53 _93490 _40053 s).
Proof. exact (MK_COMB (@lem3654452) (@lem3654451 _93490 _40053 s)). Qed.
Lemma lem3654455 (a : Prop) (b : Prop) : (term973 a b) = (term974 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3654456 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1121 _93490 _93497 f _40053 P _40052) = (term1122 _93490 _93497 f _40053 P _40052).
Proof. exact (@lem3654455 (term95 _93490 _93497 _40052 f _40053) (term119 _93497 P _40052)). Qed.
Lemma lem3654458 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3654459 {_93490 _93497 : Type'} (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) : (term1123 _93490 _93497 _40052 f _40053) = (_40052 = (@IMAGE _93490 _93497 f _40053)).
Proof. exact (@lem3654458 (_40052 = (@IMAGE _93490 _93497 f _40053))). Qed.
Lemma lem3654460 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3654461 {_93490 _93497 : Type'} (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) : (term1124 _93490 _93497 _40052 f _40053) = (term1125 _93490 _93497 _40052 f _40053).
Proof. exact (MK_COMB (@lem3654460) (@lem3654459 _93490 _93497 _40052 f _40053)). Qed.
Lemma lem3654463 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3654464 {_93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1126 _93497 P _40052) = (P _40052).
Proof. exact (@lem3654463 (P _40052)). Qed.
Lemma lem3654465 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1122 _93490 _93497 f _40053 P _40052) = (term1127 _93490 _93497 f _40053 P _40052).
Proof. exact (MK_COMB (@lem3654461 _93490 _93497 _40052 f _40053) (@lem3654464 _93497 P _40052)). Qed.
Lemma lem3654466 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1121 _93490 _93497 f _40053 P _40052) = (term1127 _93490 _93497 f _40053 P _40052).
Proof. exact (TRANS (@lem3654456 _93490 _93497 f _40053 P _40052) (@lem3654465 _93490 _93497 f _40053 P _40052)). Qed.
Lemma lem3654467 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1151 _93490 _93497 s f _40053 P _40052) = (term1152 _93490 _93497 s f _40053 P _40052).
Proof. exact (MK_COMB (@lem3654453 _93490 _40053 s) (@lem3654466 _93490 _93497 f _40053 P _40052)). Qed.
Lemma lem3654468 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1150 _93490 _93497 s f _40053 P _40052) = (term1152 _93490 _93497 s f _40053 P _40052).
Proof. exact (TRANS (@lem3654448 _93490 _93497 s f _40053 P _40052) (@lem3654467 _93490 _93497 s f _40053 P _40052)). Qed.
Lemma lem3654469 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3654470 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1153 _93490 _93497 s f _40053 P _40052) = (term1154 _93490 _93497 s f _40053 P _40052).
Proof. exact (MK_COMB (@lem3654469) (@lem3654468 _93490 _93497 s f _40053 P _40052)). Qed.
Lemma lem3654471 {_93490 _93497 : Type'} (y' : type840 _93490 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) : (term874 _93490 _93497 y' _40052 _40053) = (term874 _93490 _93497 y' _40052 _40053).
Proof. exact (eq_refl (term874 _93490 _93497 y' _40052 _40053)). Qed.
Lemma lem3654472 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (y' : type840 _93490 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) : (term1149 _93490 _93497 s f P y' _40052 _40053) = (term1155 _93490 _93497 s f P y' _40052 _40053).
Proof. exact (MK_COMB (@lem3654470 _93490 _93497 s f _40053 P _40052) (@lem3654471 _93490 _93497 y' _40052 _40053)). Qed.
Lemma lem3654473 {_93490 _93497 : Type'} (s : _93490 -> Prop) (f : _93490 -> _93497) (P : type686 _93497) (y' : type840 _93490 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) : (term1144 _93490 _93497 y' s f _40053 P _40052) = (term1155 _93490 _93497 s f P y' _40052 _40053).
Proof. exact (TRANS (@lem3654445 _93490 _93497 s f P y' _40052 _40053) (@lem3654472 _93490 _93497 s f P y' _40052 _40053)). Qed.
Lemma lem3654475 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1134 _93490 _93497 P f t'.
Proof. exact (conj (@lem3654266 _93490 _93497 f t') (@lem3654273 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3654476 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1156 _93490 _93497 s P f t'.
Proof. exact (conj (@lem3654257 _93490 _93497 x' y' s P f t' h1) (@lem3654475 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3654478 {_93490 _93497 : Type'} (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1155 _93490 _93497 s f P y' _40052 _40053.
Proof. exact (EQ_MP (@lem3654473 _93490 _93497 s f P y' _40052 _40053) (@lem3654442 _93490 _93497 _40053 _40052 x' y' s P f t' h1)). Qed.
Lemma lem3654479 {_93490 _93497 : Type'} (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1155 _93490 _93497 s f P y' _40052 _40053.
Proof. exact (@lem3654478 _93490 _93497 _40052 _40053 x' y' s P f t' h1). Qed.
Lemma lem3654480 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1157 _93490 _93497 s P y' f t'.
Proof. exact (@lem3654479 _93490 _93497 (@IMAGE _93490 _93497 f t') t' x' y' s P f t' h1). Qed.
Lemma lem3654483 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1158 _93490 _93497 y' f t'.
Proof. exact (@lem3654480 _93490 _93497 x' y' s P f t' h1 (@lem3654476 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3654484 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1159 _93490 _93497 y' f t'.
Proof. exact (fun h0 : term1160 _93490 _93497 y' f t' => @lem3654483 _93490 _93497 x' y' s P f t' h1). Qed.
Lemma lem3654486 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3654487 {_93490 _93497 : Type'} (y' : type840 _93490 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) : (term1159 _93490 _93497 y' f t') = (term1158 _93490 _93497 y' f t').
Proof. exact (@lem3654486 (term1158 _93490 _93497 y' f t')). Qed.
Lemma lem3654488 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1158 _93490 _93497 y' f t'.
Proof. exact (EQ_MP (@lem3654487 _93490 _93497 y' f t') (@lem3654484 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3654490 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : @SUBSET _93490 t' s.
Proof. exact (proj1 (@lem3651399 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3654491 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term950 _93490 t' s.
Proof. exact (fun h0 : term227 _93490 t' s => @lem3654490 _93490 _93497 x' y' s P f t' h1). Qed.
Lemma lem3654493 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3654494 {_93490 : Type'} (t' : _93490 -> Prop) (s : _93490 -> Prop) : (term950 _93490 t' s) = (@SUBSET _93490 t' s).
Proof. exact (@lem3654493 (@SUBSET _93490 t' s)). Qed.
Lemma lem3654495 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : @SUBSET _93490 t' s.
Proof. exact (EQ_MP (@lem3654494 _93490 t' s) (@lem3654491 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3654498 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term1140 _93490 _93497 x' y' f t') : term1140 _93490 _93497 x' y' f t'.
Proof. exact (h1). Qed.
Lemma lem3654499 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term1140 _93490 _93497 x' y' f t') : term1161 _93490 _93497 x' y' f t'.
Proof. exact (fun h0 : (term1138 _93490 _93497 x' f t') = (term1138 _93490 _93497 y' f t') => @lem3654498 _93490 _93497 x' y' f t' h1). Qed.
Lemma lem3654501 (p : Prop) : (term953 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3654502 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) : (term1161 _93490 _93497 x' y' f t') = (term1140 _93490 _93497 x' y' f t').
Proof. exact (@lem3654501 ((term1138 _93490 _93497 x' f t') = (term1138 _93490 _93497 y' f t'))). Qed.
Lemma lem3654503 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term1140 _93490 _93497 x' y' f t') : term1140 _93490 _93497 x' y' f t'.
Proof. exact (EQ_MP (@lem3654502 _93490 _93497 x' y' f t') (@lem3654499 _93490 _93497 x' y' f t' h1)). Qed.
Lemma lem3654505 {_93497 : Type'} (x : _93497 -> Prop) : x = x.
Proof. exact (@lem21386 (_93497 -> Prop) x). Qed.
Lemma lem3654506 {_93497 : Type'} (x : _93497 -> Prop) : x = x.
Proof. exact (@lem3654505 _93497 x). Qed.
Lemma lem3654507 {_93490 _93497 : Type'} (f : _93490 -> _93497) (t' : _93490 -> Prop) : (@IMAGE _93490 _93497 f t') = (@IMAGE _93490 _93497 f t').
Proof. exact (@lem3654506 _93497 (@IMAGE _93490 _93497 f t')). Qed.
Lemma lem3654508 {_93490 _93497 : Type'} (f : _93490 -> _93497) (t' : _93490 -> Prop) : term1092 _93490 _93497 f t'.
Proof. exact (fun h0 : term1093 _93490 _93497 f t' => @lem3654507 _93490 _93497 f t'). Qed.
Lemma lem3654510 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3654511 {_93490 _93497 : Type'} (f : _93490 -> _93497) (t' : _93490 -> Prop) : (term1092 _93490 _93497 f t') = ((@IMAGE _93490 _93497 f t') = (@IMAGE _93490 _93497 f t')).
Proof. exact (@lem3654510 ((@IMAGE _93490 _93497 f t') = (@IMAGE _93490 _93497 f t'))). Qed.
Lemma lem3654512 {_93490 _93497 : Type'} (f : _93490 -> _93497) (t' : _93490 -> Prop) : (@IMAGE _93490 _93497 f t') = (@IMAGE _93490 _93497 f t').
Proof. exact (EQ_MP (@lem3654511 _93490 _93497 f t') (@lem3654508 _93490 _93497 f t')). Qed.
Lemma lem3654514 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term45 _93490 _93497 P f t'.
Proof. exact (proj2 (@lem3651401 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3654515 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term954 _93490 _93497 P f t'.
Proof. exact (fun h0 : term136 _93490 _93497 P f t' => @lem3654514 _93490 _93497 x' y' s P f t' h1). Qed.
Lemma lem3654517 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3654518 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) : (term954 _93490 _93497 P f t') = (term45 _93490 _93497 P f t').
Proof. exact (@lem3654517 (term45 _93490 _93497 P f t')). Qed.
Lemma lem3654519 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term45 _93490 _93497 P f t'.
Proof. exact (EQ_MP (@lem3654518 _93490 _93497 P f t') (@lem3654515 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3654525 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3654526 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term929 _93490 _93497 s x' y' f _40053 P _40052) = (term1094 _93490 _93497 s x' y' f _40053 P _40052).
Proof. exact (@lem3654525 ((term744 _93490 _93497 f x' _40052 _40053) = (term744 _93490 _93497 f y' _40052 _40053)) (term227 _93490 _40053 s) (term1095 _93490 _93497 x' y' f _40053 P _40052)). Qed.
Lemma lem3654542 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3654543 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1096 _93490 _93497 s x' y' f _40053 P _40052) = (term1097 _93490 _93497 x' y' s f _40053 P _40052).
Proof. exact (@lem3654542 ((x' _40052 _40053) = (y' _40052 _40053)) (term227 _93490 _40053 s) (term928 _93490 _93497 f _40053 P _40052)). Qed.
Lemma lem3654559 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3654560 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1098 _93490 _93497 s f _40053 P _40052) = (term1099 _93490 _93497 f _40053 s P _40052).
Proof. exact (@lem3654559 (term95 _93490 _93497 _40052 f _40053) (term227 _93490 _40053 s) (term119 _93497 P _40052)). Qed.
Lemma lem3654576 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3654577 {_93490 _93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1100 _93490 _93497 _40053 s P _40052) = (term1101 _93490 _93497 P _40052 _40053 s).
Proof. exact (@lem3654576 (term119 _93497 P _40052) (term227 _93490 _40053 s)). Qed.
Lemma lem3654583 {_93490 _93497 : Type'} (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) : (term1102 _93490 _93497 _40052 f _40053) = (term1102 _93490 _93497 _40052 f _40053).
Proof. exact (eq_refl (term1102 _93490 _93497 _40052 f _40053)). Qed.
Lemma lem3654584 {_93490 _93497 : Type'} (f : _93490 -> _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1099 _93490 _93497 f _40053 s P _40052) = (term1103 _93490 _93497 f P _40052 _40053 s).
Proof. exact (MK_COMB (@lem3654583 _93490 _93497 _40052 f _40053) (@lem3654577 _93490 _93497 P _40052 _40053 s)). Qed.
Lemma lem3654588 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3654589 {_93490 _93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1103 _93490 _93497 f P _40052 _40053 s) = (term1104 _93490 _93497 P _40052 f _40053 s).
Proof. exact (@lem3654588 (term119 _93497 P _40052) (term95 _93490 _93497 _40052 f _40053) (term227 _93490 _40053 s)). Qed.
Lemma lem3654607 {_93490 _93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1099 _93490 _93497 f _40053 s P _40052) = (term1104 _93490 _93497 P _40052 f _40053 s).
Proof. exact (TRANS (@lem3654584 _93490 _93497 f P _40052 _40053 s) (@lem3654589 _93490 _93497 P _40052 f _40053 s)). Qed.
Lemma lem3654608 {_93490 _93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1098 _93490 _93497 s f _40053 P _40052) = (term1104 _93490 _93497 P _40052 f _40053 s).
Proof. exact (TRANS (@lem3654560 _93490 _93497 f _40053 s P _40052) (@lem3654607 _93490 _93497 P _40052 f _40053 s)). Qed.
Lemma lem3654609 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) : (term1105 _93490 _93497 x' y' _40052 _40053) = (term1105 _93490 _93497 x' y' _40052 _40053).
Proof. exact (eq_refl (term1105 _93490 _93497 x' y' _40052 _40053)). Qed.
Lemma lem3654610 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1097 _93490 _93497 x' y' s f _40053 P _40052) = (term1106 _93490 _93497 x' y' P _40052 f _40053 s).
Proof. exact (MK_COMB (@lem3654609 _93490 _93497 x' y' _40052 _40053) (@lem3654608 _93490 _93497 P _40052 f _40053 s)). Qed.
Lemma lem3654621 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1096 _93490 _93497 s x' y' f _40053 P _40052) = (term1106 _93490 _93497 x' y' P _40052 f _40053 s).
Proof. exact (TRANS (@lem3654543 _93490 _93497 x' y' s f _40053 P _40052) (@lem3654610 _93490 _93497 x' y' P _40052 f _40053 s)). Qed.
Lemma lem3654622 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (f : _93490 -> _93497) (y' : type840 _93490 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) : (term754 _93490 _93497 x' f y' _40052 _40053) = (term754 _93490 _93497 x' f y' _40052 _40053).
Proof. exact (eq_refl (term754 _93490 _93497 x' f y' _40052 _40053)). Qed.
Lemma lem3654623 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1094 _93490 _93497 s x' y' f _40053 P _40052) = (term1107 _93490 _93497 x' y' P _40052 f _40053 s).
Proof. exact (MK_COMB (@lem3654622 _93490 _93497 x' f y' _40052 _40053) (@lem3654621 _93490 _93497 x' y' P _40052 f _40053 s)). Qed.
Lemma lem3654627 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3654628 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1107 _93490 _93497 x' y' P _40052 f _40053 s) = (term1108 _93490 _93497 x' y' P _40052 f _40053 s).
Proof. exact (@lem3654627 ((x' _40052 _40053) = (y' _40052 _40053)) ((term744 _93490 _93497 f x' _40052 _40053) = (term744 _93490 _93497 f y' _40052 _40053)) (term1104 _93490 _93497 P _40052 f _40053 s)). Qed.
Lemma lem3654670 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1094 _93490 _93497 s x' y' f _40053 P _40052) = (term1108 _93490 _93497 x' y' P _40052 f _40053 s).
Proof. exact (TRANS (@lem3654623 _93490 _93497 x' y' P _40052 f _40053 s) (@lem3654628 _93490 _93497 x' y' P _40052 f _40053 s)). Qed.
Lemma lem3654671 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term929 _93490 _93497 s x' y' f _40053 P _40052) = (term1108 _93490 _93497 x' y' P _40052 f _40053 s).
Proof. exact (TRANS (@lem3654526 _93490 _93497 s x' y' f _40053 P _40052) (@lem3654670 _93490 _93497 x' y' P _40052 f _40053 s)). Qed.
Lemma lem3654672 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3654673 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1109 _93490 _93497 s x' y' f _40053 P _40052) = (term1110 _93490 _93497 x' y' P _40052 f _40053 s).
Proof. exact (MK_COMB (@lem3654672) (@lem3654671 _93490 _93497 x' y' P _40052 f _40053 s)). Qed.
Lemma lem3654689 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3654690 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1096 _93490 _93497 s x' y' f _40053 P _40052) = (term1097 _93490 _93497 x' y' s f _40053 P _40052).
Proof. exact (@lem3654689 ((x' _40052 _40053) = (y' _40052 _40053)) (term227 _93490 _40053 s) (term928 _93490 _93497 f _40053 P _40052)). Qed.
Lemma lem3654706 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3654707 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1098 _93490 _93497 s f _40053 P _40052) = (term1099 _93490 _93497 f _40053 s P _40052).
Proof. exact (@lem3654706 (term95 _93490 _93497 _40052 f _40053) (term227 _93490 _40053 s) (term119 _93497 P _40052)). Qed.
Lemma lem3654723 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3654724 {_93490 _93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1100 _93490 _93497 _40053 s P _40052) = (term1101 _93490 _93497 P _40052 _40053 s).
Proof. exact (@lem3654723 (term119 _93497 P _40052) (term227 _93490 _40053 s)). Qed.
Lemma lem3654730 {_93490 _93497 : Type'} (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) : (term1102 _93490 _93497 _40052 f _40053) = (term1102 _93490 _93497 _40052 f _40053).
Proof. exact (eq_refl (term1102 _93490 _93497 _40052 f _40053)). Qed.
Lemma lem3654731 {_93490 _93497 : Type'} (f : _93490 -> _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1099 _93490 _93497 f _40053 s P _40052) = (term1103 _93490 _93497 f P _40052 _40053 s).
Proof. exact (MK_COMB (@lem3654730 _93490 _93497 _40052 f _40053) (@lem3654724 _93490 _93497 P _40052 _40053 s)). Qed.
Lemma lem3654735 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3654736 {_93490 _93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1103 _93490 _93497 f P _40052 _40053 s) = (term1104 _93490 _93497 P _40052 f _40053 s).
Proof. exact (@lem3654735 (term119 _93497 P _40052) (term95 _93490 _93497 _40052 f _40053) (term227 _93490 _40053 s)). Qed.
Lemma lem3654754 {_93490 _93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1099 _93490 _93497 f _40053 s P _40052) = (term1104 _93490 _93497 P _40052 f _40053 s).
Proof. exact (TRANS (@lem3654731 _93490 _93497 f P _40052 _40053 s) (@lem3654736 _93490 _93497 P _40052 f _40053 s)). Qed.
Lemma lem3654755 {_93490 _93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1098 _93490 _93497 s f _40053 P _40052) = (term1104 _93490 _93497 P _40052 f _40053 s).
Proof. exact (TRANS (@lem3654707 _93490 _93497 f _40053 s P _40052) (@lem3654754 _93490 _93497 P _40052 f _40053 s)). Qed.
Lemma lem3654756 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) : (term1105 _93490 _93497 x' y' _40052 _40053) = (term1105 _93490 _93497 x' y' _40052 _40053).
Proof. exact (eq_refl (term1105 _93490 _93497 x' y' _40052 _40053)). Qed.
Lemma lem3654757 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1097 _93490 _93497 x' y' s f _40053 P _40052) = (term1106 _93490 _93497 x' y' P _40052 f _40053 s).
Proof. exact (MK_COMB (@lem3654756 _93490 _93497 x' y' _40052 _40053) (@lem3654755 _93490 _93497 P _40052 f _40053 s)). Qed.
Lemma lem3654768 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1096 _93490 _93497 s x' y' f _40053 P _40052) = (term1106 _93490 _93497 x' y' P _40052 f _40053 s).
Proof. exact (TRANS (@lem3654690 _93490 _93497 x' y' s f _40053 P _40052) (@lem3654757 _93490 _93497 x' y' P _40052 f _40053 s)). Qed.
Lemma lem3654769 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (f : _93490 -> _93497) (y' : type840 _93490 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) : (term754 _93490 _93497 x' f y' _40052 _40053) = (term754 _93490 _93497 x' f y' _40052 _40053).
Proof. exact (eq_refl (term754 _93490 _93497 x' f y' _40052 _40053)). Qed.
Lemma lem3654770 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1094 _93490 _93497 s x' y' f _40053 P _40052) = (term1107 _93490 _93497 x' y' P _40052 f _40053 s).
Proof. exact (MK_COMB (@lem3654769 _93490 _93497 x' f y' _40052 _40053) (@lem3654768 _93490 _93497 x' y' P _40052 f _40053 s)). Qed.
Lemma lem3654774 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3654775 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1107 _93490 _93497 x' y' P _40052 f _40053 s) = (term1108 _93490 _93497 x' y' P _40052 f _40053 s).
Proof. exact (@lem3654774 ((x' _40052 _40053) = (y' _40052 _40053)) ((term744 _93490 _93497 f x' _40052 _40053) = (term744 _93490 _93497 f y' _40052 _40053)) (term1104 _93490 _93497 P _40052 f _40053 s)). Qed.
Lemma lem3654817 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term1094 _93490 _93497 s x' y' f _40053 P _40052) = (term1108 _93490 _93497 x' y' P _40052 f _40053 s).
Proof. exact (TRANS (@lem3654770 _93490 _93497 x' y' P _40052 f _40053 s) (@lem3654775 _93490 _93497 x' y' P _40052 f _40053 s)). Qed.
Lemma lem3654818 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : ((term929 _93490 _93497 s x' y' f _40053 P _40052) = (term1094 _93490 _93497 s x' y' f _40053 P _40052)) = ((term1108 _93490 _93497 x' y' P _40052 f _40053 s) = (term1108 _93490 _93497 x' y' P _40052 f _40053 s)).
Proof. exact (MK_COMB (@lem3654673 _93490 _93497 x' y' P _40052 f _40053 s) (@lem3654817 _93490 _93497 x' y' P _40052 f _40053 s)). Qed.
Lemma lem3654820 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3654821 (x : Prop) : (x = x) = True.
Proof. exact (@lem3654820 Prop x). Qed.
Lemma lem3654822 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (P : type686 _93497) (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : ((term1108 _93490 _93497 x' y' P _40052 f _40053 s) = (term1108 _93490 _93497 x' y' P _40052 f _40053 s)) = True.
Proof. exact (@lem3654821 (term1108 _93490 _93497 x' y' P _40052 f _40053 s)). Qed.
Lemma lem3654823 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : ((term929 _93490 _93497 s x' y' f _40053 P _40052) = (term1094 _93490 _93497 s x' y' f _40053 P _40052)) = True.
Proof. exact (TRANS (@lem3654818 _93490 _93497 x' y' P _40052 f _40053 s) (@lem3654822 _93490 _93497 x' y' P _40052 f _40053 s)). Qed.
Lemma lem3654824 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : True = ((term929 _93490 _93497 s x' y' f _40053 P _40052) = (term1094 _93490 _93497 s x' y' f _40053 P _40052)).
Proof. exact (SYM (@lem3654823 _93490 _93497 s x' y' f _40053 P _40052)). Qed.
Lemma lem3654825 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term929 _93490 _93497 s x' y' f _40053 P _40052) = (term1094 _93490 _93497 s x' y' f _40053 P _40052).
Proof. exact (EQ_MP (@lem3654824 _93490 _93497 s x' y' f _40053 P _40052) (@lem0)). Qed.
Lemma lem3654826 {_93490 _93497 : Type'} (_40053 : _93490 -> Prop) (_40052 : _93497 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1094 _93490 _93497 s x' y' f _40053 P _40052.
Proof. exact (EQ_MP (@lem3654825 _93490 _93497 s x' y' f _40053 P _40052) (@lem3651910 _93490 _93497 _40053 _40052 x' y' s P f t' h1)). Qed.
Lemma lem3654828 (b : Prop) (a : Prop) : (a \/ b) = (term971 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3654829 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (x' : type840 _93490 _93497) (f : _93490 -> _93497) (y' : type840 _93490 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) : (term1094 _93490 _93497 s x' y' f _40053 P _40052) = (term1162 _93490 _93497 s P x' f y' _40052 _40053).
Proof. exact (@lem3654828 (term1096 _93490 _93497 s x' y' f _40053 P _40052) ((term744 _93490 _93497 f x' _40052 _40053) = (term744 _93490 _93497 f y' _40052 _40053))). Qed.
Lemma lem3654831 (a : Prop) (b : Prop) : (term973 a b) = (term974 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3654832 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1163 _93490 _93497 s x' y' f _40053 P _40052) = (term1164 _93490 _93497 s x' y' f _40053 P _40052).
Proof. exact (@lem3654831 (term227 _93490 _40053 s) (term1095 _93490 _93497 x' y' f _40053 P _40052)). Qed.
Lemma lem3654834 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3654835 {_93490 : Type'} (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term978 _93490 _40053 s) = (@SUBSET _93490 _40053 s).
Proof. exact (@lem3654834 (@SUBSET _93490 _40053 s)). Qed.
Lemma lem3654836 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3654837 {_93490 : Type'} (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term979 _93490 _40053 s) = (term53 _93490 _40053 s).
Proof. exact (MK_COMB (@lem3654836) (@lem3654835 _93490 _40053 s)). Qed.
Lemma lem3654839 (a : Prop) (b : Prop) : (term973 a b) = (term974 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3654840 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1165 _93490 _93497 x' y' f _40053 P _40052) = (term1166 _93490 _93497 x' y' f _40053 P _40052).
Proof. exact (@lem3654839 ((x' _40052 _40053) = (y' _40052 _40053)) (term928 _93490 _93497 f _40053 P _40052)). Qed.
Lemma lem3654842 (a : Prop) (b : Prop) : (term973 a b) = (term974 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3654843 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1121 _93490 _93497 f _40053 P _40052) = (term1122 _93490 _93497 f _40053 P _40052).
Proof. exact (@lem3654842 (term95 _93490 _93497 _40052 f _40053) (term119 _93497 P _40052)). Qed.
Lemma lem3654845 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3654846 {_93490 _93497 : Type'} (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) : (term1123 _93490 _93497 _40052 f _40053) = (_40052 = (@IMAGE _93490 _93497 f _40053)).
Proof. exact (@lem3654845 (_40052 = (@IMAGE _93490 _93497 f _40053))). Qed.
Lemma lem3654847 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3654848 {_93490 _93497 : Type'} (_40052 : _93497 -> Prop) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) : (term1124 _93490 _93497 _40052 f _40053) = (term1125 _93490 _93497 _40052 f _40053).
Proof. exact (MK_COMB (@lem3654847) (@lem3654846 _93490 _93497 _40052 f _40053)). Qed.
Lemma lem3654850 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3654851 {_93497 : Type'} (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1126 _93497 P _40052) = (P _40052).
Proof. exact (@lem3654850 (P _40052)). Qed.
Lemma lem3654852 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1122 _93490 _93497 f _40053 P _40052) = (term1127 _93490 _93497 f _40053 P _40052).
Proof. exact (MK_COMB (@lem3654848 _93490 _93497 _40052 f _40053) (@lem3654851 _93497 P _40052)). Qed.
Lemma lem3654853 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1121 _93490 _93497 f _40053 P _40052) = (term1127 _93490 _93497 f _40053 P _40052).
Proof. exact (TRANS (@lem3654843 _93490 _93497 f _40053 P _40052) (@lem3654852 _93490 _93497 f _40053 P _40052)). Qed.
Lemma lem3654854 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) : (term1167 _93490 _93497 x' y' _40052 _40053) = (term1167 _93490 _93497 x' y' _40052 _40053).
Proof. exact (eq_refl (term1167 _93490 _93497 x' y' _40052 _40053)). Qed.
Lemma lem3654855 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1166 _93490 _93497 x' y' f _40053 P _40052) = (term1168 _93490 _93497 x' y' f _40053 P _40052).
Proof. exact (MK_COMB (@lem3654854 _93490 _93497 x' y' _40052 _40053) (@lem3654853 _93490 _93497 f _40053 P _40052)). Qed.
Lemma lem3654856 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1165 _93490 _93497 x' y' f _40053 P _40052) = (term1168 _93490 _93497 x' y' f _40053 P _40052).
Proof. exact (TRANS (@lem3654840 _93490 _93497 x' y' f _40053 P _40052) (@lem3654855 _93490 _93497 x' y' f _40053 P _40052)). Qed.
Lemma lem3654857 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1164 _93490 _93497 s x' y' f _40053 P _40052) = (term1169 _93490 _93497 s x' y' f _40053 P _40052).
Proof. exact (MK_COMB (@lem3654837 _93490 _40053 s) (@lem3654856 _93490 _93497 x' y' f _40053 P _40052)). Qed.
Lemma lem3654858 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1163 _93490 _93497 s x' y' f _40053 P _40052) = (term1169 _93490 _93497 s x' y' f _40053 P _40052).
Proof. exact (TRANS (@lem3654832 _93490 _93497 s x' y' f _40053 P _40052) (@lem3654857 _93490 _93497 s x' y' f _40053 P _40052)). Qed.
Lemma lem3654859 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3654860 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1170 _93490 _93497 s x' y' f _40053 P _40052) = (term1171 _93490 _93497 s x' y' f _40053 P _40052).
Proof. exact (MK_COMB (@lem3654859) (@lem3654858 _93490 _93497 s x' y' f _40053 P _40052)). Qed.
Lemma lem3654861 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (f : _93490 -> _93497) (y' : type840 _93490 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) : ((term744 _93490 _93497 f x' _40052 _40053) = (term744 _93490 _93497 f y' _40052 _40053)) = ((term744 _93490 _93497 f x' _40052 _40053) = (term744 _93490 _93497 f y' _40052 _40053)).
Proof. exact (eq_refl ((term744 _93490 _93497 f x' _40052 _40053) = (term744 _93490 _93497 f y' _40052 _40053))). Qed.
Lemma lem3654862 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (x' : type840 _93490 _93497) (f : _93490 -> _93497) (y' : type840 _93490 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) : (term1162 _93490 _93497 s P x' f y' _40052 _40053) = (term1172 _93490 _93497 s P x' f y' _40052 _40053).
Proof. exact (MK_COMB (@lem3654860 _93490 _93497 s x' y' f _40053 P _40052) (@lem3654861 _93490 _93497 x' f y' _40052 _40053)). Qed.
Lemma lem3654863 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (x' : type840 _93490 _93497) (f : _93490 -> _93497) (y' : type840 _93490 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) : (term1094 _93490 _93497 s x' y' f _40053 P _40052) = (term1172 _93490 _93497 s P x' f y' _40052 _40053).
Proof. exact (TRANS (@lem3654829 _93490 _93497 s P x' f y' _40052 _40053) (@lem3654862 _93490 _93497 s P x' f y' _40052 _40053)). Qed.
Lemma lem3654865 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1134 _93490 _93497 P f t'.
Proof. exact (conj (@lem3654512 _93490 _93497 f t') (@lem3654519 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3654866 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term1140 _93490 _93497 x' y' f t') (h2 : term780 _93490 _93497 x' y' s P f t') : term1173 _93490 _93497 x' y' P f t'.
Proof. exact (conj (@lem3654503 _93490 _93497 x' y' f t' h1) (@lem3654865 _93490 _93497 x' y' s P f t' h2)). Qed.
Lemma lem3654867 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term1140 _93490 _93497 x' y' f t') (h2 : term780 _93490 _93497 x' y' s P f t') : term1174 _93490 _93497 s x' y' P f t'.
Proof. exact (conj (@lem3654495 _93490 _93497 x' y' s P f t' h2) (@lem3654866 _93490 _93497 x' y' s P f t' h1 h2)). Qed.
Lemma lem3654869 {_93490 _93497 : Type'} (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1172 _93490 _93497 s P x' f y' _40052 _40053.
Proof. exact (EQ_MP (@lem3654863 _93490 _93497 s P x' f y' _40052 _40053) (@lem3654826 _93490 _93497 _40053 _40052 x' y' s P f t' h1)). Qed.
Lemma lem3654870 {_93490 _93497 : Type'} (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1172 _93490 _93497 s P x' f y' _40052 _40053.
Proof. exact (@lem3654869 _93490 _93497 _40052 _40053 x' y' s P f t' h1). Qed.
Lemma lem3654871 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1175 _93490 _93497 s P x' y' f t'.
Proof. exact (@lem3654870 _93490 _93497 (@IMAGE _93490 _93497 f t') t' x' y' s P f t' h1). Qed.
Lemma lem3654874 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term1140 _93490 _93497 x' y' f t') (h2 : term780 _93490 _93497 x' y' s P f t') : (term1091 _93490 _93497 x' f t') = (term1091 _93490 _93497 y' f t').
Proof. exact (@lem3654871 _93490 _93497 x' y' s P f t' h2 (@lem3654867 _93490 _93497 x' y' s P f t' h1 h2)). Qed.
Lemma lem3654875 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term1140 _93490 _93497 x' y' f t') (h2 : term780 _93490 _93497 x' y' s P f t') : term1143 _93490 _93497 x' y' f t'.
Proof. exact (fun h0 : term1089 _93490 _93497 x' y' f t' => @lem3654874 _93490 _93497 x' y' s P f t' h1 h2). Qed.
Lemma lem3654877 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3654878 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) : (term1143 _93490 _93497 x' y' f t') = ((term1091 _93490 _93497 x' f t') = (term1091 _93490 _93497 y' f t')).
Proof. exact (@lem3654877 ((term1091 _93490 _93497 x' f t') = (term1091 _93490 _93497 y' f t'))). Qed.
Lemma lem3654879 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term1140 _93490 _93497 x' y' f t') (h2 : term780 _93490 _93497 x' y' s P f t') : (term1091 _93490 _93497 x' f t') = (term1091 _93490 _93497 y' f t').
Proof. exact (EQ_MP (@lem3654878 _93490 _93497 x' y' f t') (@lem3654875 _93490 _93497 x' y' s P f t' h1 h2)). Qed.
Lemma lem3654895 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3654896 {_93490 _93497 : Type'} (f : _93490 -> _93497) (t' : _93490 -> Prop) (_40054 : _93490) (_40055 : _93490) : (term1040 _93490 _93497 t' f _40054 _40055) = (term1041 _93490 _93497 f t' _40054 _40055).
Proof. exact (@lem3654895 (term721 _93490 _93497 _40054 f _40055) (term919 _93490 _40055 t') (_40054 = _40055)). Qed.
Lemma lem3654912 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3654913 {_93490 : Type'} (_40054 : _93490) (_40055 : _93490) (t' : _93490 -> Prop) : (term1042 _93490 t' _40054 _40055) = (term1043 _93490 _40054 _40055 t').
Proof. exact (@lem3654912 (_40054 = _40055) (term919 _93490 _40055 t')). Qed.
Lemma lem3654921 {_93490 _93497 : Type'} (_40054 : _93490) (f : _93490 -> _93497) (_40055 : _93490) : (term723 _93490 _93497 _40054 f _40055) = (term723 _93490 _93497 _40054 f _40055).
Proof. exact (eq_refl (term723 _93490 _93497 _40054 f _40055)). Qed.
Lemma lem3654922 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40054 : _93490) (_40055 : _93490) (t' : _93490 -> Prop) : (term1041 _93490 _93497 f t' _40054 _40055) = (term1044 _93490 _93497 f _40054 _40055 t').
Proof. exact (MK_COMB (@lem3654921 _93490 _93497 _40054 f _40055) (@lem3654913 _93490 _40054 _40055 t')). Qed.
Lemma lem3654926 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3654927 {_93490 _93497 : Type'} (_40054 : _93490) (f : _93490 -> _93497) (_40055 : _93490) (t' : _93490 -> Prop) : (term1044 _93490 _93497 f _40054 _40055 t') = (term1045 _93490 _93497 _40054 f _40055 t').
Proof. exact (@lem3654926 (_40054 = _40055) (term721 _93490 _93497 _40054 f _40055) (term919 _93490 _40055 t')). Qed.
Lemma lem3654947 {_93490 _93497 : Type'} (_40054 : _93490) (f : _93490 -> _93497) (_40055 : _93490) (t' : _93490 -> Prop) : (term1041 _93490 _93497 f t' _40054 _40055) = (term1045 _93490 _93497 _40054 f _40055 t').
Proof. exact (TRANS (@lem3654922 _93490 _93497 f _40054 _40055 t') (@lem3654927 _93490 _93497 _40054 f _40055 t')). Qed.
Lemma lem3654948 {_93490 _93497 : Type'} (_40054 : _93490) (f : _93490 -> _93497) (_40055 : _93490) (t' : _93490 -> Prop) : (term1040 _93490 _93497 t' f _40054 _40055) = (term1045 _93490 _93497 _40054 f _40055 t').
Proof. exact (TRANS (@lem3654896 _93490 _93497 f t' _40054 _40055) (@lem3654947 _93490 _93497 _40054 f _40055 t')). Qed.
Lemma lem3654949 {_93490 : Type'} (_40054 : _93490) (t' : _93490 -> Prop) : (term1046 _93490 _40054 t') = (term1046 _93490 _40054 t').
Proof. exact (eq_refl (term1046 _93490 _40054 t')). Qed.
Lemma lem3654950 {_93490 _93497 : Type'} (_40054 : _93490) (f : _93490 -> _93497) (_40055 : _93490) (t' : _93490 -> Prop) : (term918 _93490 _93497 t' f _40054 _40055) = (term1047 _93490 _93497 _40054 f _40055 t').
Proof. exact (MK_COMB (@lem3654949 _93490 _40054 t') (@lem3654948 _93490 _93497 _40054 f _40055 t')). Qed.
Lemma lem3654954 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3654955 {_93490 _93497 : Type'} (_40054 : _93490) (f : _93490 -> _93497) (_40055 : _93490) (t' : _93490 -> Prop) : (term1047 _93490 _93497 _40054 f _40055 t') = (term1048 _93490 _93497 _40054 f _40055 t').
Proof. exact (@lem3654954 (_40054 = _40055) (term919 _93490 _40054 t') (term1049 _93490 _93497 _40054 f _40055 t')). Qed.
Lemma lem3654971 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3654972 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40054 : _93490) (_40055 : _93490) (t' : _93490 -> Prop) : (term1050 _93490 _93497 _40054 f _40055 t') = (term1051 _93490 _93497 f _40054 _40055 t').
Proof. exact (@lem3654971 (term721 _93490 _93497 _40054 f _40055) (term919 _93490 _40054 t') (term919 _93490 _40055 t')). Qed.
Lemma lem3654990 {_93490 : Type'} (_40054 : _93490) (_40055 : _93490) : (term1052 _93490 _40054 _40055) = (term1052 _93490 _40054 _40055).
Proof. exact (eq_refl (term1052 _93490 _40054 _40055)). Qed.
Lemma lem3654991 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40054 : _93490) (_40055 : _93490) (t' : _93490 -> Prop) : (term1048 _93490 _93497 _40054 f _40055 t') = (term1053 _93490 _93497 f _40054 _40055 t').
Proof. exact (MK_COMB (@lem3654990 _93490 _40054 _40055) (@lem3654972 _93490 _93497 f _40054 _40055 t')). Qed.
Lemma lem3655002 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40054 : _93490) (_40055 : _93490) (t' : _93490 -> Prop) : (term1047 _93490 _93497 _40054 f _40055 t') = (term1053 _93490 _93497 f _40054 _40055 t').
Proof. exact (TRANS (@lem3654955 _93490 _93497 _40054 f _40055 t') (@lem3654991 _93490 _93497 f _40054 _40055 t')). Qed.
Lemma lem3655003 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40054 : _93490) (_40055 : _93490) (t' : _93490 -> Prop) : (term918 _93490 _93497 t' f _40054 _40055) = (term1053 _93490 _93497 f _40054 _40055 t').
Proof. exact (TRANS (@lem3654950 _93490 _93497 _40054 f _40055 t') (@lem3655002 _93490 _93497 f _40054 _40055 t')). Qed.
Lemma lem3655004 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3655005 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40054 : _93490) (_40055 : _93490) (t' : _93490 -> Prop) : (term1054 _93490 _93497 t' f _40054 _40055) = (term1055 _93490 _93497 f _40054 _40055 t').
Proof. exact (MK_COMB (@lem3655004) (@lem3655003 _93490 _93497 f _40054 _40055 t')). Qed.
Lemma lem3655031 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3655032 {_93490 _93497 : Type'} (_40054 : _93490) (f : _93490 -> _93497) (_40055 : _93490) (t' : _93490 -> Prop) : (term1056 _93490 _93497 t' _40054 f _40055) = (term1049 _93490 _93497 _40054 f _40055 t').
Proof. exact (@lem3655031 (term721 _93490 _93497 _40054 f _40055) (term919 _93490 _40055 t')). Qed.
Lemma lem3655040 {_93490 : Type'} (_40054 : _93490) (t' : _93490 -> Prop) : (term1046 _93490 _40054 t') = (term1046 _93490 _40054 t').
Proof. exact (eq_refl (term1046 _93490 _40054 t')). Qed.
Lemma lem3655041 {_93490 _93497 : Type'} (_40054 : _93490) (f : _93490 -> _93497) (_40055 : _93490) (t' : _93490 -> Prop) : (term1057 _93490 _93497 t' _40054 f _40055) = (term1050 _93490 _93497 _40054 f _40055 t').
Proof. exact (MK_COMB (@lem3655040 _93490 _40054 t') (@lem3655032 _93490 _93497 _40054 f _40055 t')). Qed.
Lemma lem3655045 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3655046 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40054 : _93490) (_40055 : _93490) (t' : _93490 -> Prop) : (term1050 _93490 _93497 _40054 f _40055 t') = (term1051 _93490 _93497 f _40054 _40055 t').
Proof. exact (@lem3655045 (term721 _93490 _93497 _40054 f _40055) (term919 _93490 _40054 t') (term919 _93490 _40055 t')). Qed.
Lemma lem3655064 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40054 : _93490) (_40055 : _93490) (t' : _93490 -> Prop) : (term1057 _93490 _93497 t' _40054 f _40055) = (term1051 _93490 _93497 f _40054 _40055 t').
Proof. exact (TRANS (@lem3655041 _93490 _93497 _40054 f _40055 t') (@lem3655046 _93490 _93497 f _40054 _40055 t')). Qed.
Lemma lem3655065 {_93490 : Type'} (_40054 : _93490) (_40055 : _93490) : (term1052 _93490 _40054 _40055) = (term1052 _93490 _40054 _40055).
Proof. exact (eq_refl (term1052 _93490 _40054 _40055)). Qed.
Lemma lem3655066 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40054 : _93490) (_40055 : _93490) (t' : _93490 -> Prop) : (term1058 _93490 _93497 t' _40054 f _40055) = (term1053 _93490 _93497 f _40054 _40055 t').
Proof. exact (MK_COMB (@lem3655065 _93490 _40054 _40055) (@lem3655064 _93490 _93497 f _40054 _40055 t')). Qed.
Lemma lem3655077 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40054 : _93490) (_40055 : _93490) (t' : _93490 -> Prop) : ((term918 _93490 _93497 t' f _40054 _40055) = (term1058 _93490 _93497 t' _40054 f _40055)) = ((term1053 _93490 _93497 f _40054 _40055 t') = (term1053 _93490 _93497 f _40054 _40055 t')).
Proof. exact (MK_COMB (@lem3655005 _93490 _93497 f _40054 _40055 t') (@lem3655066 _93490 _93497 f _40054 _40055 t')). Qed.
Lemma lem3655079 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3655080 (x : Prop) : (x = x) = True.
Proof. exact (@lem3655079 Prop x). Qed.
Lemma lem3655081 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40054 : _93490) (_40055 : _93490) (t' : _93490 -> Prop) : ((term1053 _93490 _93497 f _40054 _40055 t') = (term1053 _93490 _93497 f _40054 _40055 t')) = True.
Proof. exact (@lem3655080 (term1053 _93490 _93497 f _40054 _40055 t')). Qed.
Lemma lem3655082 {_93490 _93497 : Type'} (t' : _93490 -> Prop) (_40054 : _93490) (f : _93490 -> _93497) (_40055 : _93490) : ((term918 _93490 _93497 t' f _40054 _40055) = (term1058 _93490 _93497 t' _40054 f _40055)) = True.
Proof. exact (TRANS (@lem3655077 _93490 _93497 f _40054 _40055 t') (@lem3655081 _93490 _93497 f _40054 _40055 t')). Qed.
Lemma lem3655083 {_93490 _93497 : Type'} (t' : _93490 -> Prop) (_40054 : _93490) (f : _93490 -> _93497) (_40055 : _93490) : True = ((term918 _93490 _93497 t' f _40054 _40055) = (term1058 _93490 _93497 t' _40054 f _40055)).
Proof. exact (SYM (@lem3655082 _93490 _93497 t' _40054 f _40055)). Qed.
Lemma lem3655084 {_93490 _93497 : Type'} (t' : _93490 -> Prop) (_40054 : _93490) (f : _93490 -> _93497) (_40055 : _93490) : (term918 _93490 _93497 t' f _40054 _40055) = (term1058 _93490 _93497 t' _40054 f _40055).
Proof. exact (EQ_MP (@lem3655083 _93490 _93497 t' _40054 f _40055) (@lem0)). Qed.
Lemma lem3655085 {_93490 _93497 : Type'} (_40054 : _93490) (_40055 : _93490) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1058 _93490 _93497 t' _40054 f _40055.
Proof. exact (EQ_MP (@lem3655084 _93490 _93497 t' _40054 f _40055) (@lem3651886 _93490 _93497 _40054 _40055 x' y' s P f t' h1)). Qed.
Lemma lem3655087 (b : Prop) (a : Prop) : (a \/ b) = (term971 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3655088 {_93490 _93497 : Type'} (t' : _93490 -> Prop) (f : _93490 -> _93497) (_40054 : _93490) (_40055 : _93490) : (term1058 _93490 _93497 t' _40054 f _40055) = (term1059 _93490 _93497 t' f _40054 _40055).
Proof. exact (@lem3655087 (term1057 _93490 _93497 t' _40054 f _40055) (_40054 = _40055)). Qed.
Lemma lem3655090 (a : Prop) (b : Prop) : (term973 a b) = (term974 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3655091 {_93490 _93497 : Type'} (t' : _93490 -> Prop) (_40054 : _93490) (f : _93490 -> _93497) (_40055 : _93490) : (term1060 _93490 _93497 t' _40054 f _40055) = (term1061 _93490 _93497 t' _40054 f _40055).
Proof. exact (@lem3655090 (term919 _93490 _40054 t') (term1056 _93490 _93497 t' _40054 f _40055)). Qed.
Lemma lem3655093 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3655094 {_93490 : Type'} (_40054 : _93490) (t' : _93490 -> Prop) : (term1062 _93490 _40054 t') = (@IN _93490 _40054 t').
Proof. exact (@lem3655093 (@IN _93490 _40054 t')). Qed.
Lemma lem3655095 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3655096 {_93490 : Type'} (_40054 : _93490) (t' : _93490 -> Prop) : (term1063 _93490 _40054 t') = (term1064 _93490 _40054 t').
Proof. exact (MK_COMB (@lem3655095) (@lem3655094 _93490 _40054 t')). Qed.
Lemma lem3655098 (a : Prop) (b : Prop) : (term973 a b) = (term974 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3655099 {_93490 _93497 : Type'} (t' : _93490 -> Prop) (_40054 : _93490) (f : _93490 -> _93497) (_40055 : _93490) : (term1065 _93490 _93497 t' _40054 f _40055) = (term1066 _93490 _93497 t' _40054 f _40055).
Proof. exact (@lem3655098 (term919 _93490 _40055 t') (term721 _93490 _93497 _40054 f _40055)). Qed.
Lemma lem3655101 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3655102 {_93490 : Type'} (_40055 : _93490) (t' : _93490 -> Prop) : (term1062 _93490 _40055 t') = (@IN _93490 _40055 t').
Proof. exact (@lem3655101 (@IN _93490 _40055 t')). Qed.
Lemma lem3655103 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3655104 {_93490 : Type'} (_40055 : _93490) (t' : _93490 -> Prop) : (term1063 _93490 _40055 t') = (term1064 _93490 _40055 t').
Proof. exact (MK_COMB (@lem3655103) (@lem3655102 _93490 _40055 t')). Qed.
Lemma lem3655106 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3655107 {_93490 _93497 : Type'} (_40054 : _93490) (f : _93490 -> _93497) (_40055 : _93490) : (term1067 _93490 _93497 _40054 f _40055) = ((@I (_93490 -> _93497) f _40054) = (@I (_93490 -> _93497) f _40055)).
Proof. exact (@lem3655106 ((@I (_93490 -> _93497) f _40054) = (@I (_93490 -> _93497) f _40055))). Qed.
Lemma lem3655108 {_93490 _93497 : Type'} (t' : _93490 -> Prop) (_40054 : _93490) (f : _93490 -> _93497) (_40055 : _93490) : (term1066 _93490 _93497 t' _40054 f _40055) = (term1068 _93490 _93497 t' _40054 f _40055).
Proof. exact (MK_COMB (@lem3655104 _93490 _40055 t') (@lem3655107 _93490 _93497 _40054 f _40055)). Qed.
Lemma lem3655109 {_93490 _93497 : Type'} (t' : _93490 -> Prop) (_40054 : _93490) (f : _93490 -> _93497) (_40055 : _93490) : (term1065 _93490 _93497 t' _40054 f _40055) = (term1068 _93490 _93497 t' _40054 f _40055).
Proof. exact (TRANS (@lem3655099 _93490 _93497 t' _40054 f _40055) (@lem3655108 _93490 _93497 t' _40054 f _40055)). Qed.
Lemma lem3655110 {_93490 _93497 : Type'} (t' : _93490 -> Prop) (_40054 : _93490) (f : _93490 -> _93497) (_40055 : _93490) : (term1061 _93490 _93497 t' _40054 f _40055) = (term1069 _93490 _93497 t' _40054 f _40055).
Proof. exact (MK_COMB (@lem3655096 _93490 _40054 t') (@lem3655109 _93490 _93497 t' _40054 f _40055)). Qed.
Lemma lem3655111 {_93490 _93497 : Type'} (t' : _93490 -> Prop) (_40054 : _93490) (f : _93490 -> _93497) (_40055 : _93490) : (term1060 _93490 _93497 t' _40054 f _40055) = (term1069 _93490 _93497 t' _40054 f _40055).
Proof. exact (TRANS (@lem3655091 _93490 _93497 t' _40054 f _40055) (@lem3655110 _93490 _93497 t' _40054 f _40055)). Qed.
Lemma lem3655112 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3655113 {_93490 _93497 : Type'} (t' : _93490 -> Prop) (_40054 : _93490) (f : _93490 -> _93497) (_40055 : _93490) : (term1070 _93490 _93497 t' _40054 f _40055) = (term1071 _93490 _93497 t' _40054 f _40055).
Proof. exact (MK_COMB (@lem3655112) (@lem3655111 _93490 _93497 t' _40054 f _40055)). Qed.
Lemma lem3655114 {_93490 : Type'} (_40054 : _93490) (_40055 : _93490) : (_40054 = _40055) = (_40054 = _40055).
Proof. exact (eq_refl (_40054 = _40055)). Qed.
Lemma lem3655115 {_93490 _93497 : Type'} (t' : _93490 -> Prop) (f : _93490 -> _93497) (_40054 : _93490) (_40055 : _93490) : (term1059 _93490 _93497 t' f _40054 _40055) = (term1072 _93490 _93497 t' f _40054 _40055).
Proof. exact (MK_COMB (@lem3655113 _93490 _93497 t' _40054 f _40055) (@lem3655114 _93490 _40054 _40055)). Qed.
Lemma lem3655116 {_93490 _93497 : Type'} (t' : _93490 -> Prop) (f : _93490 -> _93497) (_40054 : _93490) (_40055 : _93490) : (term1058 _93490 _93497 t' _40054 f _40055) = (term1072 _93490 _93497 t' f _40054 _40055).
Proof. exact (TRANS (@lem3655088 _93490 _93497 t' f _40054 _40055) (@lem3655115 _93490 _93497 t' f _40054 _40055)). Qed.
Lemma lem3655118 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term1140 _93490 _93497 x' y' f t') (h2 : term780 _93490 _93497 x' y' s P f t') : term1176 _93490 _93497 x' y' f t'.
Proof. exact (conj (@lem3654488 _93490 _93497 x' y' s P f t' h2) (@lem3654879 _93490 _93497 x' y' s P f t' h1 h2)). Qed.
Lemma lem3655119 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term1140 _93490 _93497 x' y' f t') (h2 : term780 _93490 _93497 x' y' s P f t') : term1177 _93490 _93497 x' y' f t'.
Proof. exact (conj (@lem3654250 _93490 _93497 x' y' s P f t' h2) (@lem3655118 _93490 _93497 x' y' s P f t' h1 h2)). Qed.
Lemma lem3655121 {_93490 _93497 : Type'} (_40054 : _93490) (_40055 : _93490) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1072 _93490 _93497 t' f _40054 _40055.
Proof. exact (EQ_MP (@lem3655116 _93490 _93497 t' f _40054 _40055) (@lem3655085 _93490 _93497 _40054 _40055 x' y' s P f t' h1)). Qed.
Lemma lem3655122 {_93490 _93497 : Type'} (_40054 : _93490) (_40055 : _93490) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1072 _93490 _93497 t' f _40054 _40055.
Proof. exact (@lem3655121 _93490 _93497 _40054 _40055 x' y' s P f t' h1). Qed.
Lemma lem3655123 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1178 _93490 _93497 x' y' f t'.
Proof. exact (@lem3655122 _93490 _93497 (term1138 _93490 _93497 x' f t') (term1138 _93490 _93497 y' f t') x' y' s P f t' h1). Qed.
Lemma lem3655126 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term1140 _93490 _93497 x' y' f t') (h2 : term780 _93490 _93497 x' y' s P f t') : (term1138 _93490 _93497 x' f t') = (term1138 _93490 _93497 y' f t').
Proof. exact (@lem3655123 _93490 _93497 x' y' s P f t' h2 (@lem3655119 _93490 _93497 x' y' s P f t' h1 h2)). Qed.
Lemma lem3655127 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1139 _93490 _93497 x' y' f t'.
Proof. exact (fun h0 : term1140 _93490 _93497 x' y' f t' => @lem3655126 _93490 _93497 x' y' s P f t' h0 h1). Qed.
Lemma lem3655129 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3655130 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) : (term1139 _93490 _93497 x' y' f t') = ((term1138 _93490 _93497 x' f t') = (term1138 _93490 _93497 y' f t')).
Proof. exact (@lem3655129 ((term1138 _93490 _93497 x' f t') = (term1138 _93490 _93497 y' f t'))). Qed.
Lemma lem3655131 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : (term1138 _93490 _93497 x' f t') = (term1138 _93490 _93497 y' f t').
Proof. exact (EQ_MP (@lem3655130 _93490 _93497 x' y' f t') (@lem3655127 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3655133 {_93497 : Type'} (x : _93497 -> Prop) : x = x.
Proof. exact (@lem21386 (_93497 -> Prop) x). Qed.
Lemma lem3655134 {_93497 : Type'} (x : _93497 -> Prop) : x = x.
Proof. exact (@lem3655133 _93497 x). Qed.
Lemma lem3655135 {_93490 _93497 : Type'} (f : _93490 -> _93497) (t' : _93490 -> Prop) : (@IMAGE _93490 _93497 f t') = (@IMAGE _93490 _93497 f t').
Proof. exact (@lem3655134 _93497 (@IMAGE _93490 _93497 f t')). Qed.
Lemma lem3655136 {_93490 _93497 : Type'} (f : _93490 -> _93497) (t' : _93490 -> Prop) : term1092 _93490 _93497 f t'.
Proof. exact (fun h0 : term1093 _93490 _93497 f t' => @lem3655135 _93490 _93497 f t'). Qed.
Lemma lem3655138 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3655139 {_93490 _93497 : Type'} (f : _93490 -> _93497) (t' : _93490 -> Prop) : (term1092 _93490 _93497 f t') = ((@IMAGE _93490 _93497 f t') = (@IMAGE _93490 _93497 f t')).
Proof. exact (@lem3655138 ((@IMAGE _93490 _93497 f t') = (@IMAGE _93490 _93497 f t'))). Qed.
Lemma lem3655140 {_93490 _93497 : Type'} (f : _93490 -> _93497) (t' : _93490 -> Prop) : (@IMAGE _93490 _93497 f t') = (@IMAGE _93490 _93497 f t').
Proof. exact (EQ_MP (@lem3655139 _93490 _93497 f t') (@lem3655136 _93490 _93497 f t')). Qed.
Lemma lem3655142 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term45 _93490 _93497 P f t'.
Proof. exact (proj2 (@lem3651401 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3655143 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term954 _93490 _93497 P f t'.
Proof. exact (fun h0 : term136 _93490 _93497 P f t' => @lem3655142 _93490 _93497 x' y' s P f t' h1). Qed.
Lemma lem3655145 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3655146 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) : (term954 _93490 _93497 P f t') = (term45 _93490 _93497 P f t').
Proof. exact (@lem3655145 (term45 _93490 _93497 P f t')). Qed.
Lemma lem3655147 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term45 _93490 _93497 P f t'.
Proof. exact (EQ_MP (@lem3655146 _93490 _93497 P f t') (@lem3655143 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3655149 (a : Prop) (b : Prop) : (term1076 a b) = (term1077 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3655150 {_93490 _93497 : Type'} (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term928 _93490 _93497 f _40053 P _40052) = (term1179 _93490 _93497 f _40053 P _40052).
Proof. exact (@lem3655149 (_40052 = (@IMAGE _93490 _93497 f _40053)) (P _40052)). Qed.
Lemma lem3655151 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) : (term1180 _93490 _93497 x' y' _40052 _40053) = (term1180 _93490 _93497 x' y' _40052 _40053).
Proof. exact (eq_refl (term1180 _93490 _93497 x' y' _40052 _40053)). Qed.
Lemma lem3655152 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1181 _93490 _93497 x' y' f _40053 P _40052) = (term1182 _93490 _93497 x' y' f _40053 P _40052).
Proof. exact (MK_COMB (@lem3655151 _93490 _93497 x' y' _40052 _40053) (@lem3655150 _93490 _93497 f _40053 P _40052)). Qed.
Lemma lem3655154 (a : Prop) (b : Prop) : (term1076 a b) = (term1077 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3655155 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1182 _93490 _93497 x' y' f _40053 P _40052) = (term1183 _93490 _93497 x' y' f _40053 P _40052).
Proof. exact (@lem3655154 ((x' _40052 _40053) = (y' _40052 _40053)) (term1127 _93490 _93497 f _40053 P _40052)). Qed.
Lemma lem3655156 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1181 _93490 _93497 x' y' f _40053 P _40052) = (term1183 _93490 _93497 x' y' f _40053 P _40052).
Proof. exact (TRANS (@lem3655152 _93490 _93497 x' y' f _40053 P _40052) (@lem3655155 _93490 _93497 x' y' f _40053 P _40052)). Qed.
Lemma lem3655157 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (f : _93490 -> _93497) (y' : type840 _93490 _93497) (_40052 : _93497 -> Prop) (_40053 : _93490 -> Prop) : (term750 _93490 _93497 x' f y' _40052 _40053) = (term750 _93490 _93497 x' f y' _40052 _40053).
Proof. exact (eq_refl (term750 _93490 _93497 x' f y' _40052 _40053)). Qed.
Lemma lem3655158 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term933 _93490 _93497 x' y' f _40053 P _40052) = (term1184 _93490 _93497 x' y' f _40053 P _40052).
Proof. exact (MK_COMB (@lem3655157 _93490 _93497 x' f y' _40052 _40053) (@lem3655156 _93490 _93497 x' y' f _40053 P _40052)). Qed.
Lemma lem3655160 (a : Prop) (b : Prop) : (term1076 a b) = (term1077 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3655161 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1184 _93490 _93497 x' y' f _40053 P _40052) = (term1185 _93490 _93497 x' y' f _40053 P _40052).
Proof. exact (@lem3655160 ((term744 _93490 _93497 f x' _40052 _40053) = (term744 _93490 _93497 f y' _40052 _40053)) (term1186 _93490 _93497 x' y' f _40053 P _40052)). Qed.
Lemma lem3655162 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term933 _93490 _93497 x' y' f _40053 P _40052) = (term1185 _93490 _93497 x' y' f _40053 P _40052).
Proof. exact (TRANS (@lem3655158 _93490 _93497 x' y' f _40053 P _40052) (@lem3655161 _93490 _93497 x' y' f _40053 P _40052)). Qed.
Lemma lem3655163 {_93490 : Type'} (_40053 : _93490 -> Prop) (s : _93490 -> Prop) : (term103 _93490 _40053 s) = (term103 _93490 _40053 s).
Proof. exact (eq_refl (term103 _93490 _40053 s)). Qed.
Lemma lem3655164 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term934 _93490 _93497 s x' y' f _40053 P _40052) = (term1187 _93490 _93497 s x' y' f _40053 P _40052).
Proof. exact (MK_COMB (@lem3655163 _93490 _40053 s) (@lem3655162 _93490 _93497 x' y' f _40053 P _40052)). Qed.
Lemma lem3655166 (a : Prop) (b : Prop) : (term1076 a b) = (term1077 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3655167 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1187 _93490 _93497 s x' y' f _40053 P _40052) = (term1188 _93490 _93497 s x' y' f _40053 P _40052).
Proof. exact (@lem3655166 (@SUBSET _93490 _40053 s) (term1189 _93490 _93497 x' y' f _40053 P _40052)). Qed.
Lemma lem3655168 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term934 _93490 _93497 s x' y' f _40053 P _40052) = (term1188 _93490 _93497 s x' y' f _40053 P _40052).
Proof. exact (TRANS (@lem3655164 _93490 _93497 s x' y' f _40053 P _40052) (@lem3655167 _93490 _93497 s x' y' f _40053 P _40052)). Qed.
Lemma lem3655170 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3655171 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term1188 _93490 _93497 s x' y' f _40053 P _40052) = (term1190 _93490 _93497 s x' y' f _40053 P _40052).
Proof. exact (@lem3655170 (term1191 _93490 _93497 s x' y' f _40053 P _40052)). Qed.
Lemma lem3655172 {_93490 _93497 : Type'} (s : _93490 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (f : _93490 -> _93497) (_40053 : _93490 -> Prop) (P : type686 _93497) (_40052 : _93497 -> Prop) : (term934 _93490 _93497 s x' y' f _40053 P _40052) = (term1190 _93490 _93497 s x' y' f _40053 P _40052).
Proof. exact (TRANS (@lem3655168 _93490 _93497 s x' y' f _40053 P _40052) (@lem3655171 _93490 _93497 s x' y' f _40053 P _40052)). Qed.
Lemma lem3655174 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1134 _93490 _93497 P f t'.
Proof. exact (conj (@lem3655140 _93490 _93497 f t') (@lem3655147 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3655175 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1192 _93490 _93497 x' y' P f t'.
Proof. exact (conj (@lem3655131 _93490 _93497 x' y' s P f t' h1) (@lem3655174 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3655176 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1193 _93490 _93497 x' y' P f t'.
Proof. exact (conj (@lem3654012 _93490 _93497 x' y' s P f t' h1) (@lem3655175 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3655177 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1194 _93490 _93497 s x' y' P f t'.
Proof. exact (conj (@lem3653524 _93490 _93497 x' y' s P f t' h1) (@lem3655176 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3655179 {_93490 _93497 : Type'} (_40053 : _93490 -> Prop) (_40052 : _93497 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1190 _93490 _93497 s x' y' f _40053 P _40052.
Proof. exact (EQ_MP (@lem3655172 _93490 _93497 s x' y' f _40053 P _40052) (@lem3651934 _93490 _93497 _40053 _40052 x' y' s P f t' h1)). Qed.
Lemma lem3655180 {_93490 _93497 : Type'} (_40053 : _93490 -> Prop) (_40052 : _93497 -> Prop) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1190 _93490 _93497 s x' y' f _40053 P _40052.
Proof. exact (@lem3655179 _93490 _93497 _40053 _40052 x' y' s P f t' h1). Qed.
Lemma lem3655181 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1195 _93490 _93497 s x' y' P f t'.
Proof. exact (@lem3655180 _93490 _93497 t' (@IMAGE _93490 _93497 f t') x' y' s P f t' h1). Qed.
Lemma lem3655184 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : False.
Proof. exact (@lem3655181 _93490 _93497 x' y' s P f t' h1 (@lem3655177 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3655185 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : term1088.
Proof. exact (fun h0 : ~ False => @lem3655184 _93490 _93497 x' y' s P f t' h1). Qed.
Lemma lem3655187 (p : Prop) : (term951 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3655188 : term1088 = False.
Proof. exact (@lem3655187 False). Qed.
Lemma lem3655189 {_93490 _93497 : Type'} (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term780 _93490 _93497 x' y' s P f t') : False.
Proof. exact (EQ_MP (@lem3655188) (@lem3655185 _93490 _93497 x' y' s P f t' h1)). Qed.
Lemma lem3655190 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (x : type684 _93490) (y : type684 _93490) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term815 _93490 _93497 u t s x y P f) : False.
Proof. exact (EQ_MP (@lem3653396) (@lem3653393 _93490 _93497 u t s x y P f h1)). Qed.
Lemma lem3655191 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (t' : _93490 -> Prop) (h1 : term702 _93490 _93497 u t x y x' y' s P f t') : False.
Proof. exact (or_elim (@lem3651388 _93490 _93497 u t x y x' y' s P f t' h1) (fun h0 : term815 _93490 _93497 u t s x y P f => @lem3655190 _93490 _93497 u t s x y P f h0) (fun h0 : term780 _93490 _93497 x' y' s P f t' => @lem3655189 _93490 _93497 x' y' s P f t' h0)). Qed.
Lemma lem3655192 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (x' : type840 _93490 _93497) (y' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term705 _93490 _93497 u t x y x' y' s P f) : False.
Proof. exact (ex_elim (@lem3650886 _93490 _93497 u t x y x' y' s P f h1) (fun t' : _93490 -> Prop => fun h0 : term704 _93490 _93497 u t x y x' y' s P f t' => @lem3655191 _93490 _93497 u t x y x' y' s P f t' h0)). Qed.
Lemma lem3655193 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (x' : type840 _93490 _93497) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term707 _93490 _93497 u t x y x' s P f) : False.
Proof. exact (ex_elim (@lem3650885 _93490 _93497 u t x y x' s P f h1) (fun y' : type840 _93490 _93497 => fun h0 : term706 _93490 _93497 u t x y x' s P f y' => @lem3655192 _93490 _93497 u t x y x' y' s P f h0)). Qed.
Lemma lem3655194 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (y : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term709 _93490 _93497 u t x y s P f) : False.
Proof. exact (ex_elim (@lem3650884 _93490 _93497 u t x y s P f h1) (fun x' : type840 _93490 _93497 => fun h0 : term708 _93490 _93497 u t x y s P f x' => @lem3655193 _93490 _93497 u t x y x' s P f h0)). Qed.
Lemma lem3655195 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (x : type684 _93490) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term711 _93490 _93497 u t x s P f) : False.
Proof. exact (ex_elim (@lem3650883 _93490 _93497 u t x s P f h1) (fun y : type684 _93490 => fun h0 : term710 _93490 _93497 u t x s P f y => @lem3655194 _93490 _93497 u t x y s P f h0)). Qed.
Lemma lem3655196 {_93490 _93497 : Type'} (u : _93490 -> Prop) (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term713 _93490 _93497 u t s P f) : False.
Proof. exact (ex_elim (@lem3650882 _93490 _93497 u t s P f h1) (fun x : type684 _93490 => fun h0 : term712 _93490 _93497 u t s P f x => @lem3655195 _93490 _93497 u t x s P f h0)). Qed.
Lemma lem3655197 {_93490 _93497 : Type'} (t : _93497 -> Prop) (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term715 _93490 _93497 t s P f) : False.
Proof. exact (ex_elim (@lem3650881 _93490 _93497 t s P f h1) (fun u : _93490 -> Prop => fun h0 : term714 _93490 _93497 t s P f u => @lem3655196 _93490 _93497 u t s P f h0)). Qed.
Lemma lem3655198 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term60 _93490 _93497 s P f) : False.
Proof. exact (ex_elim (@lem3650880 _93490 _93497 s P f h1) (fun t : _93497 -> Prop => fun h0 : term716 _93490 _93497 s P f t => @lem3655197 _93490 _93497 t s P f h0)). Qed.
Lemma lem3655199 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term60 _93490 _93497 s P f) : (term60 _93490 _93497 s P f) = False.
Proof. exact (prop_ext (fun h2 : term60 _93490 _93497 s P f => @lem3655198 _93490 _93497 s P f h1) (fun h2 : False => @lem3649285 _93490 _93497 s P f h1)). Qed.
Lemma lem3655200 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) (h1 : term60 _93490 _93497 s P f) : False.
Proof. exact (EQ_MP (@lem3655199 _93490 _93497 s P f h1) (@lem3649285 _93490 _93497 s P f h1)). Qed.
Lemma lem3655201 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : term59 _93490 _93497 s P f.
Proof. exact (fun h0 : term60 _93490 _93497 s P f => @lem3655200 _93490 _93497 s P f h0). Qed.
Lemma lem3655202 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term21 _93490 _93497 s f P) = (term24 _93490 _93497 s P f).
Proof. exact (EQ_MP (@lem3649284 _93490 _93497 s P f) (@lem3655201 _93490 _93497 s P f)). Qed.
Lemma lem3655207 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) : term28 _93490 _93497 P f.
Proof. exact (fun s : _93490 -> Prop => @lem3655202 _93490 _93497 s P f). Qed.
Lemma lem3655212 {_93490 _93497 : Type'} (P : type686 _93497) : term32 _93490 _93497 P.
Proof. exact (fun f : _93490 -> _93497 => @lem3655207 _93490 _93497 P f). Qed.
Lemma lem3655217 {_93490 _93497 : Type'} : term36 _93490 _93497.
Proof. exact (fun P : type686 _93497 => @lem3655212 _93490 _93497 P). Qed.
Lemma lem3655218 {_93490 _93497 : Type'} : term38 _93490 _93497.
Proof. exact (EQ_MP (@lem3649280 _93490 _93497) (@lem3655217 _93490 _93497)). Qed.
Lemma lem3655220 {_93490 _93497 : Type'} : term38 _93490 _93497.
Proof. exact (@lem3648934 _93490 _93497 (@lem3655218 _93490 _93497)). Qed.
Lemma lem3655221 {_93490 _93497 : Type'} (h1 : term39 _93490 _93497) : False.
Proof. exact (@lem3655220 _93490 _93497 (@lem3648918 _93490 _93497 h1)). Qed.
Lemma lem3655222 {_93490 _93497 : Type'} (h1 : term39 _93490 _93497) : (term39 _93490 _93497) = False.
Proof. exact (prop_ext (fun h2 : term39 _93490 _93497 => @lem3655221 _93490 _93497 h1) (fun h2 : False => @lem3648918 _93490 _93497 h1)). Qed.
Lemma lem3655223 {_93490 _93497 : Type'} (h1 : term39 _93490 _93497) : False.
Proof. exact (EQ_MP (@lem3655222 _93490 _93497 h1) (@lem3648918 _93490 _93497 h1)). Qed.
Lemma lem3655224 {_93490 _93497 : Type'} : term38 _93490 _93497.
Proof. exact (fun h0 : term39 _93490 _93497 => @lem3655223 _93490 _93497 h0). Qed.
Lemma lem3655225 {_93490 _93497 : Type'} : term36 _93490 _93497.
Proof. exact (EQ_MP (@lem3648917 _93490 _93497) (@lem3655224 _93490 _93497)). Qed.
Lemma lem3655226 {_93490 _93497 : Type'} : term35 _93490 _93497.
Proof. exact (EQ_MP (@lem3648913 _93490 _93497) (@lem3655225 _93490 _93497)). Qed.
