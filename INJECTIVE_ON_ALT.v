Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INJECTIVE_ON_ALT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
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
Require Import thm21386_spec.
Lemma lem3558723 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3558724 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3558725 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3558724 t1) (@lem3558723 t1)). Qed.
Lemma lem3558726 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3558725 t1 t2). Qed.
Lemma lem3558727 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3558728 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3558727 t1 t2) (@lem3558726 t1 t2)). Qed.
Lemma lem3558729 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3558728 t1 t2 t3). Qed.
Lemma lem3558730 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3558731 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3558730 t1 t2 t3) (@lem3558729 t1 t2 t3)). Qed.
Lemma lem3558732 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3558731 t1 t2 t3)). Qed.
Lemma lem3558734 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3558735 {_91201 _91206 : Type'} : (term8 _91201 _91206) = (term9 _91201 _91206).
Proof. exact (@lem3558734 (term8 _91201 _91206)). Qed.
Lemma lem3558736 {_91201 _91206 : Type'} : (term9 _91201 _91206) = (term8 _91201 _91206).
Proof. exact (SYM (@lem3558735 _91201 _91206)). Qed.
Lemma lem3558737 {_91201 _91206 : Type'} (h1 : term10 _91201 _91206) : term10 _91201 _91206.
Proof. exact (h1). Qed.
Lemma lem3558740 {_91201 _91206 : Type'} (h1 : term9 _91201 _91206) : term9 _91201 _91206.
Proof. exact (h1). Qed.
Lemma lem3558741 {_91201 _91206 : Type'} : term11 _91201 _91206.
Proof. exact (fun h0 : term9 _91201 _91206 => @lem3558740 _91201 _91206 h0). Qed.
Lemma lem3558742 {_91201 _91206 : Type'} (h1 : term11 _91201 _91206) : term11 _91201 _91206.
Proof. exact (h1). Qed.
Lemma lem3558743 {_91201 _91206 : Type'} (h1 : term9 _91201 _91206) : term9 _91201 _91206.
Proof. exact (h1). Qed.
Lemma lem3558744 {_91201 _91206 : Type'} (h1 : term9 _91201 _91206) (h2 : term11 _91201 _91206) : term9 _91201 _91206.
Proof. exact (@lem3558742 _91201 _91206 h2 (@lem3558743 _91201 _91206 h1)). Qed.
Lemma lem3558745 {_91201 _91206 : Type'} (h1 : term9 _91201 _91206) : term12 _91201 _91206.
Proof. exact (fun h0 : term11 _91201 _91206 => @lem3558744 _91201 _91206 h1 h0). Qed.
Lemma lem3558746 {_91201 _91206 : Type'} (h1 : term11 _91201 _91206) : term11 _91201 _91206.
Proof. exact (h1). Qed.
Lemma lem3558747 {_91201 _91206 : Type'} (h1 : term9 _91201 _91206) (h2 : term11 _91201 _91206) : term9 _91201 _91206.
Proof. exact (@lem3558745 _91201 _91206 h1 (@lem3558746 _91201 _91206 h2)). Qed.
Lemma lem3558748 {_91201 _91206 : Type'} (h1 : term11 _91201 _91206) : term11 _91201 _91206.
Proof. exact (fun h0 : term9 _91201 _91206 => @lem3558747 _91201 _91206 h0 h1). Qed.
Lemma lem3558749 {_91201 _91206 : Type'} : term13 _91201 _91206.
Proof. exact (fun h0 : term11 _91201 _91206 => @lem3558748 _91201 _91206 h0). Qed.
Lemma lem3558752 {_91201 _91206 : Type'} : term11 _91201 _91206.
Proof. exact (@lem3558749 _91201 _91206 (@lem3558741 _91201 _91206)). Qed.
Lemma lem3558753 {_91201 _91206 : Type'} : term11 _91201 _91206.
Proof. exact (@lem3558752 _91201 _91206). Qed.
Lemma lem3558755 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3558756 {_91201 _91206 : Type'} : (term9 _91201 _91206) = (term14 _91201 _91206).
Proof. exact (@lem3558755 (term10 _91201 _91206)). Qed.
Lemma lem3558758 (t : Prop) : (term15 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3558759 {_91201 _91206 : Type'} : (term14 _91201 _91206) = (term8 _91201 _91206).
Proof. exact (@lem3558758 (term8 _91201 _91206)). Qed.
Lemma lem3558798 {_91201 _91206 : Type'} : (term9 _91201 _91206) = (term8 _91201 _91206).
Proof. exact (TRANS (@lem3558756 _91201 _91206) (@lem3558759 _91201 _91206)). Qed.
Lemma lem3558811 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term16 _91201 _91206 P f x y) = (term16 _91201 _91206 P f x y).
Proof. exact (eq_refl (term16 _91201 _91206 P f x y)). Qed.
Lemma lem3558812 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term17 _91201 _91206 P f x) = (term17 _91201 _91206 P f x).
Proof. exact (fun_ext (fun y : _91206 => @lem3558811 _91201 _91206 P f x y)). Qed.
Lemma lem3558813 {_91206 : Type'} : (@all _91206) = (@all _91206).
Proof. exact (eq_refl (@all _91206)). Qed.
Lemma lem3558814 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term18 _91201 _91206 P f x) = (term18 _91201 _91206 P f x).
Proof. exact (MK_COMB (@lem3558813 _91206) (@lem3558812 _91201 _91206 P f x)). Qed.
Lemma lem3558815 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term19 _91201 _91206 P f) = (term19 _91201 _91206 P f).
Proof. exact (fun_ext (fun x : _91206 => @lem3558814 _91201 _91206 P f x)). Qed.
Lemma lem3558816 {_91206 : Type'} : (@all _91206) = (@all _91206).
Proof. exact (eq_refl (@all _91206)). Qed.
Lemma lem3558817 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term20 _91201 _91206 P f) = (term20 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3558816 _91206) (@lem3558815 _91201 _91206 P f)). Qed.
Lemma lem3558830 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term21 _91201 _91206 P f x y) = (term21 _91201 _91206 P f x y).
Proof. exact (eq_refl (term21 _91201 _91206 P f x y)). Qed.
Lemma lem3558831 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term22 _91201 _91206 P f x) = (term22 _91201 _91206 P f x).
Proof. exact (fun_ext (fun y : _91206 => @lem3558830 _91201 _91206 P f x y)). Qed.
Lemma lem3558832 {_91206 : Type'} : (@all _91206) = (@all _91206).
Proof. exact (eq_refl (@all _91206)). Qed.
Lemma lem3558833 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term23 _91201 _91206 P f x) = (term23 _91201 _91206 P f x).
Proof. exact (MK_COMB (@lem3558832 _91206) (@lem3558831 _91201 _91206 P f x)). Qed.
Lemma lem3558834 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term24 _91201 _91206 P f) = (term24 _91201 _91206 P f).
Proof. exact (fun_ext (fun x : _91206 => @lem3558833 _91201 _91206 P f x)). Qed.
Lemma lem3558835 {_91206 : Type'} : (@all _91206) = (@all _91206).
Proof. exact (eq_refl (@all _91206)). Qed.
Lemma lem3558836 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term25 _91201 _91206 P f) = (term25 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3558835 _91206) (@lem3558834 _91201 _91206 P f)). Qed.
Lemma lem3558837 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3558838 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term26 _91201 _91206 P f) = (term26 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3558837) (@lem3558836 _91201 _91206 P f)). Qed.
Lemma lem3558839 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : ((term25 _91201 _91206 P f) = (term20 _91201 _91206 P f)) = ((term25 _91201 _91206 P f) = (term20 _91201 _91206 P f)).
Proof. exact (MK_COMB (@lem3558838 _91201 _91206 P f) (@lem3558817 _91201 _91206 P f)). Qed.
Lemma lem3558840 {_91201 _91206 : Type'} (P : _91206 -> Prop) : (term27 _91201 _91206 P) = (term27 _91201 _91206 P).
Proof. exact (fun_ext (fun f : _91206 -> _91201 => @lem3558839 _91201 _91206 P f)). Qed.
Lemma lem3558841 {_91201 _91206 : Type'} : (@all (_91206 -> _91201)) = (@all (_91206 -> _91201)).
Proof. exact (eq_refl (@all (_91206 -> _91201))). Qed.
Lemma lem3558842 {_91201 _91206 : Type'} (P : _91206 -> Prop) : (term28 _91201 _91206 P) = (term28 _91201 _91206 P).
Proof. exact (MK_COMB (@lem3558841 _91201 _91206) (@lem3558840 _91201 _91206 P)). Qed.
Lemma lem3558843 {_91201 _91206 : Type'} : (term29 _91201 _91206) = (term29 _91201 _91206).
Proof. exact (fun_ext (fun P : _91206 -> Prop => @lem3558842 _91201 _91206 P)). Qed.
Lemma lem3558844 {_91206 : Type'} : (@all (_91206 -> Prop)) = (@all (_91206 -> Prop)).
Proof. exact (eq_refl (@all (_91206 -> Prop))). Qed.
Lemma lem3558845 {_91201 _91206 : Type'} : (term8 _91201 _91206) = (term8 _91201 _91206).
Proof. exact (MK_COMB (@lem3558844 _91206) (@lem3558843 _91201 _91206)). Qed.
Lemma lem3558894 {_91201 _91206 : Type'} : (term9 _91201 _91206) = (term8 _91201 _91206).
Proof. exact (TRANS (@lem3558798 _91201 _91206) (@lem3558845 _91201 _91206)). Qed.
Lemma lem3558895 {_91201 _91206 : Type'} : (term8 _91201 _91206) = (term9 _91201 _91206).
Proof. exact (SYM (@lem3558894 _91201 _91206)). Qed.
Lemma lem3558897 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3558898 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : ((term25 _91201 _91206 P f) = (term20 _91201 _91206 P f)) = (term30 _91201 _91206 P f).
Proof. exact (@lem3558897 ((term25 _91201 _91206 P f) = (term20 _91201 _91206 P f))). Qed.
Lemma lem3558899 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term30 _91201 _91206 P f) = ((term25 _91201 _91206 P f) = (term20 _91201 _91206 P f)).
Proof. exact (SYM (@lem3558898 _91201 _91206 P f)). Qed.
Lemma lem3558900 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term31 _91201 _91206 P f) : term31 _91201 _91206 P f.
Proof. exact (h1). Qed.
Lemma lem3558911 {_91201 _91206 : Type'} (P : _91206 -> Prop) (x : _91206) (f : _91206 -> _91201) (y : _91206) : (term32 _91201 _91206 P x f y) = (term33 _91201 _91206 P x f y).
Proof. exact (@lem17045 (P y) ((f x) = (f y))). Qed.
Lemma lem3558916 {_91206 : Type'} (P : _91206 -> Prop) (x : _91206) : (term34 _91206 P x) = (term34 _91206 P x).
Proof. exact (eq_refl (term34 _91206 P x)). Qed.
Lemma lem3558917 {_91201 _91206 : Type'} (P : _91206 -> Prop) (x : _91206) (f : _91206 -> _91201) (y : _91206) : (term35 _91201 _91206 P x f y) = (term36 _91201 _91206 P x f y).
Proof. exact (MK_COMB (@lem3558916 _91206 P x) (@lem3558911 _91201 _91206 P x f y)). Qed.
Lemma lem3558918 {_91201 _91206 : Type'} (P : _91206 -> Prop) (x : _91206) (f : _91206 -> _91201) (y : _91206) : (term37 _91201 _91206 P x f y) = (term35 _91201 _91206 P x f y).
Proof. exact (@lem17045 (P x) (term38 _91201 _91206 P x f y)). Qed.
Lemma lem3558919 {_91201 _91206 : Type'} (P : _91206 -> Prop) (x : _91206) (f : _91206 -> _91201) (y : _91206) : (term37 _91201 _91206 P x f y) = (term36 _91201 _91206 P x f y).
Proof. exact (TRANS (@lem3558918 _91201 _91206 P x f y) (@lem3558917 _91201 _91206 P x f y)). Qed.
Lemma lem3558924 {_91206 : Type'} (x : _91206) (y : _91206) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem3558929 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term39 _91201 _91206 P f x y) = (term40 _91201 _91206 P f x y).
Proof. exact (@lem17362 (term41 _91201 _91206 P x f y) (x = y)). Qed.
Lemma lem3558930 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3558931 {_91201 _91206 : Type'} (P : _91206 -> Prop) (x : _91206) (f : _91206 -> _91201) (y : _91206) : (term42 _91201 _91206 P x f y) = (term43 _91201 _91206 P x f y).
Proof. exact (MK_COMB (@lem3558930) (@lem3558919 _91201 _91206 P x f y)). Qed.
Lemma lem3558932 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term44 _91201 _91206 P f x y) = (term45 _91201 _91206 P f x y).
Proof. exact (MK_COMB (@lem3558931 _91201 _91206 P x f y) (@lem3558924 _91206 x y)). Qed.
Lemma lem3558933 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term21 _91201 _91206 P f x y) = (term44 _91201 _91206 P f x y).
Proof. exact (@lem17265 (term41 _91201 _91206 P x f y) (x = y)). Qed.
Lemma lem3558934 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term21 _91201 _91206 P f x y) = (term45 _91201 _91206 P f x y).
Proof. exact (TRANS (@lem3558933 _91201 _91206 P f x y) (@lem3558932 _91201 _91206 P f x y)). Qed.
Lemma lem3558935 {_91206 : Type'} (P : _91206 -> Prop) : (term46 _91206 P) = (term47 _91206 P).
Proof. exact (@lem18392 _91206 P). Qed.
Lemma lem3558936 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term48 _91201 _91206 P f x) = (term49 _91201 _91206 P f x).
Proof. exact (@lem3558935 _91206 (term22 _91201 _91206 P f x)). Qed.
Lemma lem3558937 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term50 _91201 _91206 P f x y) = (term21 _91201 _91206 P f x y).
Proof. exact (eq_refl (term50 _91201 _91206 P f x y)). Qed.
Lemma lem3558938 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3558939 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term51 _91201 _91206 P f x y) = (term39 _91201 _91206 P f x y).
Proof. exact (MK_COMB (@lem3558938) (@lem3558937 _91201 _91206 P f x y)). Qed.
Lemma lem3558940 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term51 _91201 _91206 P f x y) = (term40 _91201 _91206 P f x y).
Proof. exact (TRANS (@lem3558939 _91201 _91206 P f x y) (@lem3558929 _91201 _91206 P f x y)). Qed.
Lemma lem3558941 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term52 _91201 _91206 P f x) = (term53 _91201 _91206 P f x).
Proof. exact (fun_ext (fun y : _91206 => @lem3558940 _91201 _91206 P f x y)). Qed.
Lemma lem3558942 {_91206 : Type'} : (@ex _91206) = (@ex _91206).
Proof. exact (eq_refl (@ex _91206)). Qed.
Lemma lem3558943 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term49 _91201 _91206 P f x) = (term54 _91201 _91206 P f x).
Proof. exact (MK_COMB (@lem3558942 _91206) (@lem3558941 _91201 _91206 P f x)). Qed.
Lemma lem3558944 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term48 _91201 _91206 P f x) = (term54 _91201 _91206 P f x).
Proof. exact (TRANS (@lem3558936 _91201 _91206 P f x) (@lem3558943 _91201 _91206 P f x)). Qed.
Lemma lem3558945 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term22 _91201 _91206 P f x) = (term55 _91201 _91206 P f x).
Proof. exact (fun_ext (fun y : _91206 => @lem3558934 _91201 _91206 P f x y)). Qed.
Lemma lem3558946 {_91206 : Type'} : (@all _91206) = (@all _91206).
Proof. exact (eq_refl (@all _91206)). Qed.
Lemma lem3558947 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term23 _91201 _91206 P f x) = (term56 _91201 _91206 P f x).
Proof. exact (MK_COMB (@lem3558946 _91206) (@lem3558945 _91201 _91206 P f x)). Qed.
Lemma lem3558948 {_91206 : Type'} (P : _91206 -> Prop) : (term46 _91206 P) = (term47 _91206 P).
Proof. exact (@lem18392 _91206 P). Qed.
Lemma lem3558949 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term57 _91201 _91206 P f) = (term58 _91201 _91206 P f).
Proof. exact (@lem3558948 _91206 (term24 _91201 _91206 P f)). Qed.
Lemma lem3558950 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term59 _91201 _91206 P f x) = (term23 _91201 _91206 P f x).
Proof. exact (eq_refl (term59 _91201 _91206 P f x)). Qed.
Lemma lem3558951 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3558952 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term60 _91201 _91206 P f x) = (term48 _91201 _91206 P f x).
Proof. exact (MK_COMB (@lem3558951) (@lem3558950 _91201 _91206 P f x)). Qed.
Lemma lem3558953 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term60 _91201 _91206 P f x) = (term54 _91201 _91206 P f x).
Proof. exact (TRANS (@lem3558952 _91201 _91206 P f x) (@lem3558944 _91201 _91206 P f x)). Qed.
Lemma lem3558954 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term61 _91201 _91206 P f) = (term62 _91201 _91206 P f).
Proof. exact (fun_ext (fun x : _91206 => @lem3558953 _91201 _91206 P f x)). Qed.
Lemma lem3558955 {_91206 : Type'} : (@ex _91206) = (@ex _91206).
Proof. exact (eq_refl (@ex _91206)). Qed.
Lemma lem3558956 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term58 _91201 _91206 P f) = (term63 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3558955 _91206) (@lem3558954 _91201 _91206 P f)). Qed.
Lemma lem3558957 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term57 _91201 _91206 P f) = (term63 _91201 _91206 P f).
Proof. exact (TRANS (@lem3558949 _91201 _91206 P f) (@lem3558956 _91201 _91206 P f)). Qed.
Lemma lem3558958 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term24 _91201 _91206 P f) = (term64 _91201 _91206 P f).
Proof. exact (fun_ext (fun x : _91206 => @lem3558947 _91201 _91206 P f x)). Qed.
Lemma lem3558959 {_91206 : Type'} : (@all _91206) = (@all _91206).
Proof. exact (eq_refl (@all _91206)). Qed.
Lemma lem3558960 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term25 _91201 _91206 P f) = (term65 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3558959 _91206) (@lem3558958 _91201 _91206 P f)). Qed.
Lemma lem3558969 {_91206 : Type'} (x : _91206) (P : _91206 -> Prop) (y : _91206) : (term66 _91206 x P y) = (term67 _91206 x P y).
Proof. exact (@lem17045 (P x) (P y)). Qed.
Lemma lem3558987 {_91201 _91206 : Type'} (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term68 _91201 _91206 f x y) = (term69 _91201 _91206 f x y).
Proof. exact (@lem17930 ((f x) = (f y)) (x = y)). Qed.
Lemma lem3558998 {_91201 _91206 : Type'} (f : _91206 -> _91201) (x : _91206) (y : _91206) : (((f x) = (f y)) = (x = y)) = (term70 _91201 _91206 f x y).
Proof. exact (@lem17784 ((f x) = (f y)) (x = y)). Qed.
Lemma lem3559000 {_91206 : Type'} (x : _91206) (P : _91206 -> Prop) (y : _91206) : (term71 _91206 x P y) = (term71 _91206 x P y).
Proof. exact (eq_refl (term71 _91206 x P y)). Qed.
Lemma lem3559001 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term72 _91201 _91206 P f x y) = (term73 _91201 _91206 P f x y).
Proof. exact (MK_COMB (@lem3559000 _91206 x P y) (@lem3558987 _91201 _91206 f x y)). Qed.
Lemma lem3559002 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term74 _91201 _91206 P f x y) = (term72 _91201 _91206 P f x y).
Proof. exact (@lem17362 (term75 _91206 x P y) (((f x) = (f y)) = (x = y))). Qed.
Lemma lem3559003 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term74 _91201 _91206 P f x y) = (term73 _91201 _91206 P f x y).
Proof. exact (TRANS (@lem3559002 _91201 _91206 P f x y) (@lem3559001 _91201 _91206 P f x y)). Qed.
Lemma lem3559004 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3559005 {_91206 : Type'} (x : _91206) (P : _91206 -> Prop) (y : _91206) : (term76 _91206 x P y) = (term77 _91206 x P y).
Proof. exact (MK_COMB (@lem3559004) (@lem3558969 _91206 x P y)). Qed.
Lemma lem3559006 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term78 _91201 _91206 P f x y) = (term79 _91201 _91206 P f x y).
Proof. exact (MK_COMB (@lem3559005 _91206 x P y) (@lem3558998 _91201 _91206 f x y)). Qed.
Lemma lem3559007 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term16 _91201 _91206 P f x y) = (term78 _91201 _91206 P f x y).
Proof. exact (@lem17265 (term75 _91206 x P y) (((f x) = (f y)) = (x = y))). Qed.
Lemma lem3559008 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term16 _91201 _91206 P f x y) = (term79 _91201 _91206 P f x y).
Proof. exact (TRANS (@lem3559007 _91201 _91206 P f x y) (@lem3559006 _91201 _91206 P f x y)). Qed.
Lemma lem3559009 {_91206 : Type'} (P : _91206 -> Prop) : (term46 _91206 P) = (term47 _91206 P).
Proof. exact (@lem18392 _91206 P). Qed.
Lemma lem3559010 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term80 _91201 _91206 P f x) = (term81 _91201 _91206 P f x).
Proof. exact (@lem3559009 _91206 (term17 _91201 _91206 P f x)). Qed.
Lemma lem3559011 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term82 _91201 _91206 P f x y) = (term16 _91201 _91206 P f x y).
Proof. exact (eq_refl (term82 _91201 _91206 P f x y)). Qed.
Lemma lem3559012 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3559013 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term83 _91201 _91206 P f x y) = (term74 _91201 _91206 P f x y).
Proof. exact (MK_COMB (@lem3559012) (@lem3559011 _91201 _91206 P f x y)). Qed.
Lemma lem3559014 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term83 _91201 _91206 P f x y) = (term73 _91201 _91206 P f x y).
Proof. exact (TRANS (@lem3559013 _91201 _91206 P f x y) (@lem3559003 _91201 _91206 P f x y)). Qed.
Lemma lem3559015 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term84 _91201 _91206 P f x) = (term85 _91201 _91206 P f x).
Proof. exact (fun_ext (fun y : _91206 => @lem3559014 _91201 _91206 P f x y)). Qed.
Lemma lem3559016 {_91206 : Type'} : (@ex _91206) = (@ex _91206).
Proof. exact (eq_refl (@ex _91206)). Qed.
Lemma lem3559017 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term81 _91201 _91206 P f x) = (term86 _91201 _91206 P f x).
Proof. exact (MK_COMB (@lem3559016 _91206) (@lem3559015 _91201 _91206 P f x)). Qed.
Lemma lem3559018 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term80 _91201 _91206 P f x) = (term86 _91201 _91206 P f x).
Proof. exact (TRANS (@lem3559010 _91201 _91206 P f x) (@lem3559017 _91201 _91206 P f x)). Qed.
Lemma lem3559019 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term17 _91201 _91206 P f x) = (term87 _91201 _91206 P f x).
Proof. exact (fun_ext (fun y : _91206 => @lem3559008 _91201 _91206 P f x y)). Qed.
Lemma lem3559020 {_91206 : Type'} : (@all _91206) = (@all _91206).
Proof. exact (eq_refl (@all _91206)). Qed.
Lemma lem3559021 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term18 _91201 _91206 P f x) = (term88 _91201 _91206 P f x).
Proof. exact (MK_COMB (@lem3559020 _91206) (@lem3559019 _91201 _91206 P f x)). Qed.
Lemma lem3559022 {_91206 : Type'} (P : _91206 -> Prop) : (term46 _91206 P) = (term47 _91206 P).
Proof. exact (@lem18392 _91206 P). Qed.
Lemma lem3559023 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term89 _91201 _91206 P f) = (term90 _91201 _91206 P f).
Proof. exact (@lem3559022 _91206 (term19 _91201 _91206 P f)). Qed.
Lemma lem3559024 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term91 _91201 _91206 P f x) = (term18 _91201 _91206 P f x).
Proof. exact (eq_refl (term91 _91201 _91206 P f x)). Qed.
Lemma lem3559025 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3559026 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term92 _91201 _91206 P f x) = (term80 _91201 _91206 P f x).
Proof. exact (MK_COMB (@lem3559025) (@lem3559024 _91201 _91206 P f x)). Qed.
Lemma lem3559027 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term92 _91201 _91206 P f x) = (term86 _91201 _91206 P f x).
Proof. exact (TRANS (@lem3559026 _91201 _91206 P f x) (@lem3559018 _91201 _91206 P f x)). Qed.
Lemma lem3559028 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term93 _91201 _91206 P f) = (term94 _91201 _91206 P f).
Proof. exact (fun_ext (fun x : _91206 => @lem3559027 _91201 _91206 P f x)). Qed.
Lemma lem3559029 {_91206 : Type'} : (@ex _91206) = (@ex _91206).
Proof. exact (eq_refl (@ex _91206)). Qed.
Lemma lem3559030 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term90 _91201 _91206 P f) = (term95 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559029 _91206) (@lem3559028 _91201 _91206 P f)). Qed.
Lemma lem3559031 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term89 _91201 _91206 P f) = (term95 _91201 _91206 P f).
Proof. exact (TRANS (@lem3559023 _91201 _91206 P f) (@lem3559030 _91201 _91206 P f)). Qed.
Lemma lem3559032 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term19 _91201 _91206 P f) = (term96 _91201 _91206 P f).
Proof. exact (fun_ext (fun x : _91206 => @lem3559021 _91201 _91206 P f x)). Qed.
Lemma lem3559033 {_91206 : Type'} : (@all _91206) = (@all _91206).
Proof. exact (eq_refl (@all _91206)). Qed.
Lemma lem3559034 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term20 _91201 _91206 P f) = (term97 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559033 _91206) (@lem3559032 _91201 _91206 P f)). Qed.
Lemma lem3559035 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3559036 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term98 _91201 _91206 P f) = (term99 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559035) (@lem3558957 _91201 _91206 P f)). Qed.
Lemma lem3559037 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term100 _91201 _91206 P f) = (term101 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559036 _91201 _91206 P f) (@lem3559034 _91201 _91206 P f)). Qed.
Lemma lem3559038 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3559039 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term102 _91201 _91206 P f) = (term103 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559038) (@lem3558960 _91201 _91206 P f)). Qed.
Lemma lem3559040 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term104 _91201 _91206 P f) = (term105 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559039 _91201 _91206 P f) (@lem3559031 _91201 _91206 P f)). Qed.
Lemma lem3559041 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3559042 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term106 _91201 _91206 P f) = (term107 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559041) (@lem3559040 _91201 _91206 P f)). Qed.
Lemma lem3559043 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term108 _91201 _91206 P f) = (term109 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559042 _91201 _91206 P f) (@lem3559037 _91201 _91206 P f)). Qed.
Lemma lem3559044 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term31 _91201 _91206 P f) = (term108 _91201 _91206 P f).
Proof. exact (@lem17646 (term25 _91201 _91206 P f) (term20 _91201 _91206 P f)). Qed.
Lemma lem3559045 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term31 _91201 _91206 P f) = (term109 _91201 _91206 P f).
Proof. exact (TRANS (@lem3559044 _91201 _91206 P f) (@lem3559043 _91201 _91206 P f)). Qed.
Lemma lem3559256 {A : Type'} (P : Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3559257 {_91206 : Type'} (P : Prop) (Q : _91206 -> Prop) : (term110 _91206 P Q) = (term111 _91206 P Q).
Proof. exact (@lem3559256 _91206 P Q). Qed.
Lemma lem3559258 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term112 _91201 _91206 P f) = (term113 _91201 _91206 P f).
Proof. exact (@lem3559257 _91206 (term65 _91201 _91206 P f) (term94 _91201 _91206 P f)). Qed.
Lemma lem3559259 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term114 _91201 _91206 P f x) = (term86 _91201 _91206 P f x).
Proof. exact (eq_refl (term114 _91201 _91206 P f x)). Qed.
Lemma lem3559260 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term115 _91201 _91206 P f) = (term94 _91201 _91206 P f).
Proof. exact (fun_ext (fun x : _91206 => @lem3559259 _91201 _91206 P f x)). Qed.
Lemma lem3559261 {_91206 : Type'} : (@ex _91206) = (@ex _91206).
Proof. exact (eq_refl (@ex _91206)). Qed.
Lemma lem3559262 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term116 _91201 _91206 P f) = (term95 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559261 _91206) (@lem3559260 _91201 _91206 P f)). Qed.
Lemma lem3559263 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term103 _91201 _91206 P f) = (term103 _91201 _91206 P f).
Proof. exact (eq_refl (term103 _91201 _91206 P f)). Qed.
Lemma lem3559264 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term112 _91201 _91206 P f) = (term105 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559263 _91201 _91206 P f) (@lem3559262 _91201 _91206 P f)). Qed.
Lemma lem3559265 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3559266 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term117 _91201 _91206 P f) = (term118 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559265) (@lem3559264 _91201 _91206 P f)). Qed.
Lemma lem3559267 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term114 _91201 _91206 P f x) = (term86 _91201 _91206 P f x).
Proof. exact (eq_refl (term114 _91201 _91206 P f x)). Qed.
Lemma lem3559268 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term103 _91201 _91206 P f) = (term103 _91201 _91206 P f).
Proof. exact (eq_refl (term103 _91201 _91206 P f)). Qed.
Lemma lem3559269 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term119 _91201 _91206 P f x) = (term120 _91201 _91206 P f x).
Proof. exact (MK_COMB (@lem3559268 _91201 _91206 P f) (@lem3559267 _91201 _91206 P f x)). Qed.
Lemma lem3559270 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term121 _91201 _91206 P f) = (term122 _91201 _91206 P f).
Proof. exact (fun_ext (fun x : _91206 => @lem3559269 _91201 _91206 P f x)). Qed.
Lemma lem3559271 {_91206 : Type'} : (@ex _91206) = (@ex _91206).
Proof. exact (eq_refl (@ex _91206)). Qed.
Lemma lem3559272 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term113 _91201 _91206 P f) = (term123 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559271 _91206) (@lem3559270 _91201 _91206 P f)). Qed.
Lemma lem3559273 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : ((term112 _91201 _91206 P f) = (term113 _91201 _91206 P f)) = ((term105 _91201 _91206 P f) = (term123 _91201 _91206 P f)).
Proof. exact (MK_COMB (@lem3559266 _91201 _91206 P f) (@lem3559272 _91201 _91206 P f)). Qed.
Lemma lem3559274 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term105 _91201 _91206 P f) = (term123 _91201 _91206 P f).
Proof. exact (EQ_MP (@lem3559273 _91201 _91206 P f) (@lem3559258 _91201 _91206 P f)). Qed.
Lemma lem3559276 {A : Type'} (P : Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3559277 {_91206 : Type'} (P : Prop) (Q : _91206 -> Prop) : (term110 _91206 P Q) = (term111 _91206 P Q).
Proof. exact (@lem3559276 _91206 P Q). Qed.
Lemma lem3559278 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term124 _91201 _91206 P f x) = (term125 _91201 _91206 P f x).
Proof. exact (@lem3559277 _91206 (term65 _91201 _91206 P f) (term85 _91201 _91206 P f x)). Qed.
Lemma lem3559279 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term126 _91201 _91206 P f x y) = (term73 _91201 _91206 P f x y).
Proof. exact (eq_refl (term126 _91201 _91206 P f x y)). Qed.
Lemma lem3559280 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term127 _91201 _91206 P f x) = (term85 _91201 _91206 P f x).
Proof. exact (fun_ext (fun y : _91206 => @lem3559279 _91201 _91206 P f x y)). Qed.
Lemma lem3559281 {_91206 : Type'} : (@ex _91206) = (@ex _91206).
Proof. exact (eq_refl (@ex _91206)). Qed.
Lemma lem3559282 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term128 _91201 _91206 P f x) = (term86 _91201 _91206 P f x).
Proof. exact (MK_COMB (@lem3559281 _91206) (@lem3559280 _91201 _91206 P f x)). Qed.
Lemma lem3559283 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term103 _91201 _91206 P f) = (term103 _91201 _91206 P f).
Proof. exact (eq_refl (term103 _91201 _91206 P f)). Qed.
Lemma lem3559284 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term124 _91201 _91206 P f x) = (term120 _91201 _91206 P f x).
Proof. exact (MK_COMB (@lem3559283 _91201 _91206 P f) (@lem3559282 _91201 _91206 P f x)). Qed.
Lemma lem3559285 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3559286 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term129 _91201 _91206 P f x) = (term130 _91201 _91206 P f x).
Proof. exact (MK_COMB (@lem3559285) (@lem3559284 _91201 _91206 P f x)). Qed.
Lemma lem3559287 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term126 _91201 _91206 P f x y) = (term73 _91201 _91206 P f x y).
Proof. exact (eq_refl (term126 _91201 _91206 P f x y)). Qed.
Lemma lem3559288 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term103 _91201 _91206 P f) = (term103 _91201 _91206 P f).
Proof. exact (eq_refl (term103 _91201 _91206 P f)). Qed.
Lemma lem3559289 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term131 _91201 _91206 P f x y) = (term132 _91201 _91206 P f x y).
Proof. exact (MK_COMB (@lem3559288 _91201 _91206 P f) (@lem3559287 _91201 _91206 P f x y)). Qed.
Lemma lem3559290 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term133 _91201 _91206 P f x) = (term134 _91201 _91206 P f x).
Proof. exact (fun_ext (fun y : _91206 => @lem3559289 _91201 _91206 P f x y)). Qed.
Lemma lem3559291 {_91206 : Type'} : (@ex _91206) = (@ex _91206).
Proof. exact (eq_refl (@ex _91206)). Qed.
Lemma lem3559292 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term125 _91201 _91206 P f x) = (term135 _91201 _91206 P f x).
Proof. exact (MK_COMB (@lem3559291 _91206) (@lem3559290 _91201 _91206 P f x)). Qed.
Lemma lem3559293 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : ((term124 _91201 _91206 P f x) = (term125 _91201 _91206 P f x)) = ((term120 _91201 _91206 P f x) = (term135 _91201 _91206 P f x)).
Proof. exact (MK_COMB (@lem3559286 _91201 _91206 P f x) (@lem3559292 _91201 _91206 P f x)). Qed.
Lemma lem3559294 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term120 _91201 _91206 P f x) = (term135 _91201 _91206 P f x).
Proof. exact (EQ_MP (@lem3559293 _91201 _91206 P f x) (@lem3559278 _91201 _91206 P f x)). Qed.
Lemma lem3559295 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term122 _91201 _91206 P f) = (term136 _91201 _91206 P f).
Proof. exact (fun_ext (fun x : _91206 => @lem3559294 _91201 _91206 P f x)). Qed.
Lemma lem3559296 {_91206 : Type'} : (@ex _91206) = (@ex _91206).
Proof. exact (eq_refl (@ex _91206)). Qed.
Lemma lem3559297 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term123 _91201 _91206 P f) = (term137 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559296 _91206) (@lem3559295 _91201 _91206 P f)). Qed.
Lemma lem3559298 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term105 _91201 _91206 P f) = (term137 _91201 _91206 P f).
Proof. exact (TRANS (@lem3559274 _91201 _91206 P f) (@lem3559297 _91201 _91206 P f)). Qed.
Lemma lem3559299 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3559300 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term107 _91201 _91206 P f) = (term138 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559299) (@lem3559298 _91201 _91206 P f)). Qed.
Lemma lem3559302 {A : Type'} (P : A -> Prop) (Q : Prop) : (term139 A P Q) = (term140 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3559303 {_91206 : Type'} (P : _91206 -> Prop) (Q : Prop) : (term139 _91206 P Q) = (term140 _91206 P Q).
Proof. exact (@lem3559302 _91206 P Q). Qed.
Lemma lem3559304 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term141 _91201 _91206 P f) = (term142 _91201 _91206 P f).
Proof. exact (@lem3559303 _91206 (term62 _91201 _91206 P f) (term97 _91201 _91206 P f)). Qed.
Lemma lem3559305 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term143 _91201 _91206 P f x) = (term54 _91201 _91206 P f x).
Proof. exact (eq_refl (term143 _91201 _91206 P f x)). Qed.
Lemma lem3559306 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term144 _91201 _91206 P f) = (term62 _91201 _91206 P f).
Proof. exact (fun_ext (fun x : _91206 => @lem3559305 _91201 _91206 P f x)). Qed.
Lemma lem3559307 {_91206 : Type'} : (@ex _91206) = (@ex _91206).
Proof. exact (eq_refl (@ex _91206)). Qed.
Lemma lem3559308 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term145 _91201 _91206 P f) = (term63 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559307 _91206) (@lem3559306 _91201 _91206 P f)). Qed.
Lemma lem3559309 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3559310 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term146 _91201 _91206 P f) = (term99 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559309) (@lem3559308 _91201 _91206 P f)). Qed.
Lemma lem3559311 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term97 _91201 _91206 P f) = (term97 _91201 _91206 P f).
Proof. exact (eq_refl (term97 _91201 _91206 P f)). Qed.
Lemma lem3559312 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term141 _91201 _91206 P f) = (term101 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559310 _91201 _91206 P f) (@lem3559311 _91201 _91206 P f)). Qed.
Lemma lem3559313 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3559314 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term147 _91201 _91206 P f) = (term148 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559313) (@lem3559312 _91201 _91206 P f)). Qed.
Lemma lem3559315 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term143 _91201 _91206 P f x) = (term54 _91201 _91206 P f x).
Proof. exact (eq_refl (term143 _91201 _91206 P f x)). Qed.
Lemma lem3559316 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3559317 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term149 _91201 _91206 P f x) = (term150 _91201 _91206 P f x).
Proof. exact (MK_COMB (@lem3559316) (@lem3559315 _91201 _91206 P f x)). Qed.
Lemma lem3559318 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term97 _91201 _91206 P f) = (term97 _91201 _91206 P f).
Proof. exact (eq_refl (term97 _91201 _91206 P f)). Qed.
Lemma lem3559319 {_91201 _91206 : Type'} (x : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) : (term151 _91201 _91206 x P f) = (term152 _91201 _91206 x P f).
Proof. exact (MK_COMB (@lem3559317 _91201 _91206 P f x) (@lem3559318 _91201 _91206 P f)). Qed.
Lemma lem3559320 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term153 _91201 _91206 P f) = (term154 _91201 _91206 P f).
Proof. exact (fun_ext (fun x : _91206 => @lem3559319 _91201 _91206 x P f)). Qed.
Lemma lem3559321 {_91206 : Type'} : (@ex _91206) = (@ex _91206).
Proof. exact (eq_refl (@ex _91206)). Qed.
Lemma lem3559322 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term142 _91201 _91206 P f) = (term155 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559321 _91206) (@lem3559320 _91201 _91206 P f)). Qed.
Lemma lem3559323 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : ((term141 _91201 _91206 P f) = (term142 _91201 _91206 P f)) = ((term101 _91201 _91206 P f) = (term155 _91201 _91206 P f)).
Proof. exact (MK_COMB (@lem3559314 _91201 _91206 P f) (@lem3559322 _91201 _91206 P f)). Qed.
Lemma lem3559324 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term101 _91201 _91206 P f) = (term155 _91201 _91206 P f).
Proof. exact (EQ_MP (@lem3559323 _91201 _91206 P f) (@lem3559304 _91201 _91206 P f)). Qed.
Lemma lem3559326 {A : Type'} (P : A -> Prop) (Q : Prop) : (term139 A P Q) = (term140 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3559327 {_91206 : Type'} (P : _91206 -> Prop) (Q : Prop) : (term139 _91206 P Q) = (term140 _91206 P Q).
Proof. exact (@lem3559326 _91206 P Q). Qed.
Lemma lem3559328 {_91201 _91206 : Type'} (x : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) : (term156 _91201 _91206 x P f) = (term157 _91201 _91206 x P f).
Proof. exact (@lem3559327 _91206 (term53 _91201 _91206 P f x) (term97 _91201 _91206 P f)). Qed.
Lemma lem3559329 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term158 _91201 _91206 P f x y) = (term40 _91201 _91206 P f x y).
Proof. exact (eq_refl (term158 _91201 _91206 P f x y)). Qed.
Lemma lem3559330 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term159 _91201 _91206 P f x) = (term53 _91201 _91206 P f x).
Proof. exact (fun_ext (fun y : _91206 => @lem3559329 _91201 _91206 P f x y)). Qed.
Lemma lem3559331 {_91206 : Type'} : (@ex _91206) = (@ex _91206).
Proof. exact (eq_refl (@ex _91206)). Qed.
Lemma lem3559332 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term160 _91201 _91206 P f x) = (term54 _91201 _91206 P f x).
Proof. exact (MK_COMB (@lem3559331 _91206) (@lem3559330 _91201 _91206 P f x)). Qed.
Lemma lem3559333 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3559334 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term161 _91201 _91206 P f x) = (term150 _91201 _91206 P f x).
Proof. exact (MK_COMB (@lem3559333) (@lem3559332 _91201 _91206 P f x)). Qed.
Lemma lem3559335 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term97 _91201 _91206 P f) = (term97 _91201 _91206 P f).
Proof. exact (eq_refl (term97 _91201 _91206 P f)). Qed.
Lemma lem3559336 {_91201 _91206 : Type'} (x : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) : (term156 _91201 _91206 x P f) = (term152 _91201 _91206 x P f).
Proof. exact (MK_COMB (@lem3559334 _91201 _91206 P f x) (@lem3559335 _91201 _91206 P f)). Qed.
Lemma lem3559337 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3559338 {_91201 _91206 : Type'} (x : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) : (term162 _91201 _91206 x P f) = (term163 _91201 _91206 x P f).
Proof. exact (MK_COMB (@lem3559337) (@lem3559336 _91201 _91206 x P f)). Qed.
Lemma lem3559339 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term158 _91201 _91206 P f x y) = (term40 _91201 _91206 P f x y).
Proof. exact (eq_refl (term158 _91201 _91206 P f x y)). Qed.
Lemma lem3559340 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3559341 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term164 _91201 _91206 P f x y) = (term165 _91201 _91206 P f x y).
Proof. exact (MK_COMB (@lem3559340) (@lem3559339 _91201 _91206 P f x y)). Qed.
Lemma lem3559342 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term97 _91201 _91206 P f) = (term97 _91201 _91206 P f).
Proof. exact (eq_refl (term97 _91201 _91206 P f)). Qed.
Lemma lem3559343 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) : (term166 _91201 _91206 x y P f) = (term167 _91201 _91206 x y P f).
Proof. exact (MK_COMB (@lem3559341 _91201 _91206 P f x y) (@lem3559342 _91201 _91206 P f)). Qed.
Lemma lem3559344 {_91201 _91206 : Type'} (x : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) : (term168 _91201 _91206 x P f) = (term169 _91201 _91206 x P f).
Proof. exact (fun_ext (fun y : _91206 => @lem3559343 _91201 _91206 x y P f)). Qed.
Lemma lem3559345 {_91206 : Type'} : (@ex _91206) = (@ex _91206).
Proof. exact (eq_refl (@ex _91206)). Qed.
Lemma lem3559346 {_91201 _91206 : Type'} (x : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) : (term157 _91201 _91206 x P f) = (term170 _91201 _91206 x P f).
Proof. exact (MK_COMB (@lem3559345 _91206) (@lem3559344 _91201 _91206 x P f)). Qed.
Lemma lem3559347 {_91201 _91206 : Type'} (x : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) : ((term156 _91201 _91206 x P f) = (term157 _91201 _91206 x P f)) = ((term152 _91201 _91206 x P f) = (term170 _91201 _91206 x P f)).
Proof. exact (MK_COMB (@lem3559338 _91201 _91206 x P f) (@lem3559346 _91201 _91206 x P f)). Qed.
Lemma lem3559348 {_91201 _91206 : Type'} (x : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) : (term152 _91201 _91206 x P f) = (term170 _91201 _91206 x P f).
Proof. exact (EQ_MP (@lem3559347 _91201 _91206 x P f) (@lem3559328 _91201 _91206 x P f)). Qed.
Lemma lem3559349 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term154 _91201 _91206 P f) = (term171 _91201 _91206 P f).
Proof. exact (fun_ext (fun x : _91206 => @lem3559348 _91201 _91206 x P f)). Qed.
Lemma lem3559350 {_91206 : Type'} : (@ex _91206) = (@ex _91206).
Proof. exact (eq_refl (@ex _91206)). Qed.
Lemma lem3559351 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term155 _91201 _91206 P f) = (term172 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559350 _91206) (@lem3559349 _91201 _91206 P f)). Qed.
Lemma lem3559352 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term101 _91201 _91206 P f) = (term172 _91201 _91206 P f).
Proof. exact (TRANS (@lem3559324 _91201 _91206 P f) (@lem3559351 _91201 _91206 P f)). Qed.
Lemma lem3559353 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term109 _91201 _91206 P f) = (term173 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559300 _91201 _91206 P f) (@lem3559352 _91201 _91206 P f)). Qed.
Lemma lem3559355 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term174 A P Q) = (term175 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3559356 {_91206 : Type'} (P : _91206 -> Prop) (Q : _91206 -> Prop) : (term174 _91206 P Q) = (term175 _91206 P Q).
Proof. exact (@lem3559355 _91206 P Q). Qed.
Lemma lem3559357 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term176 _91201 _91206 P f) = (term177 _91201 _91206 P f).
Proof. exact (@lem3559356 _91206 (term136 _91201 _91206 P f) (term171 _91201 _91206 P f)). Qed.
Lemma lem3559358 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term178 _91201 _91206 P f x) = (term135 _91201 _91206 P f x).
Proof. exact (eq_refl (term178 _91201 _91206 P f x)). Qed.
Lemma lem3559359 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term179 _91201 _91206 P f) = (term136 _91201 _91206 P f).
Proof. exact (fun_ext (fun x : _91206 => @lem3559358 _91201 _91206 P f x)). Qed.
Lemma lem3559360 {_91206 : Type'} : (@ex _91206) = (@ex _91206).
Proof. exact (eq_refl (@ex _91206)). Qed.
Lemma lem3559361 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term180 _91201 _91206 P f) = (term137 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559360 _91206) (@lem3559359 _91201 _91206 P f)). Qed.
Lemma lem3559362 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3559363 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term181 _91201 _91206 P f) = (term138 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559362) (@lem3559361 _91201 _91206 P f)). Qed.
Lemma lem3559364 {_91201 _91206 : Type'} (x : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) : (term182 _91201 _91206 P f x) = (term170 _91201 _91206 x P f).
Proof. exact (eq_refl (term182 _91201 _91206 P f x)). Qed.
Lemma lem3559365 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term183 _91201 _91206 P f) = (term171 _91201 _91206 P f).
Proof. exact (fun_ext (fun x : _91206 => @lem3559364 _91201 _91206 x P f)). Qed.
Lemma lem3559366 {_91206 : Type'} : (@ex _91206) = (@ex _91206).
Proof. exact (eq_refl (@ex _91206)). Qed.
Lemma lem3559367 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term184 _91201 _91206 P f) = (term172 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559366 _91206) (@lem3559365 _91201 _91206 P f)). Qed.
Lemma lem3559368 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term176 _91201 _91206 P f) = (term173 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559363 _91201 _91206 P f) (@lem3559367 _91201 _91206 P f)). Qed.
Lemma lem3559369 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3559370 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term185 _91201 _91206 P f) = (term186 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559369) (@lem3559368 _91201 _91206 P f)). Qed.
Lemma lem3559371 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term178 _91201 _91206 P f x) = (term135 _91201 _91206 P f x).
Proof. exact (eq_refl (term178 _91201 _91206 P f x)). Qed.
Lemma lem3559372 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3559373 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term187 _91201 _91206 P f x) = (term188 _91201 _91206 P f x).
Proof. exact (MK_COMB (@lem3559372) (@lem3559371 _91201 _91206 P f x)). Qed.
Lemma lem3559374 {_91201 _91206 : Type'} (x : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) : (term182 _91201 _91206 P f x) = (term170 _91201 _91206 x P f).
Proof. exact (eq_refl (term182 _91201 _91206 P f x)). Qed.
Lemma lem3559375 {_91201 _91206 : Type'} (x : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) : (term189 _91201 _91206 P f x) = (term190 _91201 _91206 x P f).
Proof. exact (MK_COMB (@lem3559373 _91201 _91206 P f x) (@lem3559374 _91201 _91206 x P f)). Qed.
Lemma lem3559376 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term191 _91201 _91206 P f) = (term192 _91201 _91206 P f).
Proof. exact (fun_ext (fun x : _91206 => @lem3559375 _91201 _91206 x P f)). Qed.
Lemma lem3559377 {_91206 : Type'} : (@ex _91206) = (@ex _91206).
Proof. exact (eq_refl (@ex _91206)). Qed.
Lemma lem3559378 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term177 _91201 _91206 P f) = (term193 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559377 _91206) (@lem3559376 _91201 _91206 P f)). Qed.
Lemma lem3559379 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : ((term176 _91201 _91206 P f) = (term177 _91201 _91206 P f)) = ((term173 _91201 _91206 P f) = (term193 _91201 _91206 P f)).
Proof. exact (MK_COMB (@lem3559370 _91201 _91206 P f) (@lem3559378 _91201 _91206 P f)). Qed.
Lemma lem3559380 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term173 _91201 _91206 P f) = (term193 _91201 _91206 P f).
Proof. exact (EQ_MP (@lem3559379 _91201 _91206 P f) (@lem3559357 _91201 _91206 P f)). Qed.
Lemma lem3559382 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term174 A P Q) = (term175 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3559383 {_91206 : Type'} (P : _91206 -> Prop) (Q : _91206 -> Prop) : (term174 _91206 P Q) = (term175 _91206 P Q).
Proof. exact (@lem3559382 _91206 P Q). Qed.
Lemma lem3559384 {_91201 _91206 : Type'} (x : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) : (term194 _91201 _91206 x P f) = (term195 _91201 _91206 x P f).
Proof. exact (@lem3559383 _91206 (term134 _91201 _91206 P f x) (term169 _91201 _91206 x P f)). Qed.
Lemma lem3559385 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term196 _91201 _91206 P f x y) = (term132 _91201 _91206 P f x y).
Proof. exact (eq_refl (term196 _91201 _91206 P f x y)). Qed.
Lemma lem3559386 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term197 _91201 _91206 P f x) = (term134 _91201 _91206 P f x).
Proof. exact (fun_ext (fun y : _91206 => @lem3559385 _91201 _91206 P f x y)). Qed.
Lemma lem3559387 {_91206 : Type'} : (@ex _91206) = (@ex _91206).
Proof. exact (eq_refl (@ex _91206)). Qed.
Lemma lem3559388 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term198 _91201 _91206 P f x) = (term135 _91201 _91206 P f x).
Proof. exact (MK_COMB (@lem3559387 _91206) (@lem3559386 _91201 _91206 P f x)). Qed.
Lemma lem3559389 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3559390 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term199 _91201 _91206 P f x) = (term188 _91201 _91206 P f x).
Proof. exact (MK_COMB (@lem3559389) (@lem3559388 _91201 _91206 P f x)). Qed.
Lemma lem3559391 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) : (term200 _91201 _91206 x P f y) = (term167 _91201 _91206 x y P f).
Proof. exact (eq_refl (term200 _91201 _91206 x P f y)). Qed.
Lemma lem3559392 {_91201 _91206 : Type'} (x : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) : (term201 _91201 _91206 x P f) = (term169 _91201 _91206 x P f).
Proof. exact (fun_ext (fun y : _91206 => @lem3559391 _91201 _91206 x y P f)). Qed.
Lemma lem3559393 {_91206 : Type'} : (@ex _91206) = (@ex _91206).
Proof. exact (eq_refl (@ex _91206)). Qed.
Lemma lem3559394 {_91201 _91206 : Type'} (x : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) : (term202 _91201 _91206 x P f) = (term170 _91201 _91206 x P f).
Proof. exact (MK_COMB (@lem3559393 _91206) (@lem3559392 _91201 _91206 x P f)). Qed.
Lemma lem3559395 {_91201 _91206 : Type'} (x : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) : (term194 _91201 _91206 x P f) = (term190 _91201 _91206 x P f).
Proof. exact (MK_COMB (@lem3559390 _91201 _91206 P f x) (@lem3559394 _91201 _91206 x P f)). Qed.
Lemma lem3559396 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3559397 {_91201 _91206 : Type'} (x : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) : (term203 _91201 _91206 x P f) = (term204 _91201 _91206 x P f).
Proof. exact (MK_COMB (@lem3559396) (@lem3559395 _91201 _91206 x P f)). Qed.
Lemma lem3559398 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term196 _91201 _91206 P f x y) = (term132 _91201 _91206 P f x y).
Proof. exact (eq_refl (term196 _91201 _91206 P f x y)). Qed.
Lemma lem3559399 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3559400 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term205 _91201 _91206 P f x y) = (term206 _91201 _91206 P f x y).
Proof. exact (MK_COMB (@lem3559399) (@lem3559398 _91201 _91206 P f x y)). Qed.
Lemma lem3559401 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) : (term200 _91201 _91206 x P f y) = (term167 _91201 _91206 x y P f).
Proof. exact (eq_refl (term200 _91201 _91206 x P f y)). Qed.
Lemma lem3559402 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) : (term207 _91201 _91206 x P f y) = (term208 _91201 _91206 x y P f).
Proof. exact (MK_COMB (@lem3559400 _91201 _91206 P f x y) (@lem3559401 _91201 _91206 x y P f)). Qed.
Lemma lem3559403 {_91201 _91206 : Type'} (x : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) : (term209 _91201 _91206 x P f) = (term210 _91201 _91206 x P f).
Proof. exact (fun_ext (fun y : _91206 => @lem3559402 _91201 _91206 x y P f)). Qed.
Lemma lem3559404 {_91206 : Type'} : (@ex _91206) = (@ex _91206).
Proof. exact (eq_refl (@ex _91206)). Qed.
Lemma lem3559405 {_91201 _91206 : Type'} (x : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) : (term195 _91201 _91206 x P f) = (term211 _91201 _91206 x P f).
Proof. exact (MK_COMB (@lem3559404 _91206) (@lem3559403 _91201 _91206 x P f)). Qed.
Lemma lem3559406 {_91201 _91206 : Type'} (x : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) : ((term194 _91201 _91206 x P f) = (term195 _91201 _91206 x P f)) = ((term190 _91201 _91206 x P f) = (term211 _91201 _91206 x P f)).
Proof. exact (MK_COMB (@lem3559397 _91201 _91206 x P f) (@lem3559405 _91201 _91206 x P f)). Qed.
Lemma lem3559407 {_91201 _91206 : Type'} (x : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) : (term190 _91201 _91206 x P f) = (term211 _91201 _91206 x P f).
Proof. exact (EQ_MP (@lem3559406 _91201 _91206 x P f) (@lem3559384 _91201 _91206 x P f)). Qed.
Lemma lem3559408 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term192 _91201 _91206 P f) = (term212 _91201 _91206 P f).
Proof. exact (fun_ext (fun x : _91206 => @lem3559407 _91201 _91206 x P f)). Qed.
Lemma lem3559409 {_91206 : Type'} : (@ex _91206) = (@ex _91206).
Proof. exact (eq_refl (@ex _91206)). Qed.
Lemma lem3559410 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term193 _91201 _91206 P f) = (term213 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559409 _91206) (@lem3559408 _91201 _91206 P f)). Qed.
Lemma lem3559411 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term173 _91201 _91206 P f) = (term213 _91201 _91206 P f).
Proof. exact (TRANS (@lem3559380 _91201 _91206 P f) (@lem3559410 _91201 _91206 P f)). Qed.
Lemma lem3559413 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term109 _91201 _91206 P f) = (term213 _91201 _91206 P f).
Proof. exact (TRANS (@lem3559353 _91201 _91206 P f) (@lem3559411 _91201 _91206 P f)). Qed.
Lemma lem3559414 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term31 _91201 _91206 P f) = (term213 _91201 _91206 P f).
Proof. exact (TRANS (@lem3559045 _91201 _91206 P f) (@lem3559413 _91201 _91206 P f)). Qed.
Lemma lem3559415 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term31 _91201 _91206 P f) : term213 _91201 _91206 P f.
Proof. exact (EQ_MP (@lem3559414 _91201 _91206 P f) (@lem3558900 _91201 _91206 P f h1)). Qed.
Lemma lem3559416 {_91201 _91206 : Type'} (x : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term211 _91201 _91206 x P f) : term211 _91201 _91206 x P f.
Proof. exact (h1). Qed.
Lemma lem3559417 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term208 _91201 _91206 x y P f) : term208 _91201 _91206 x y P f.
Proof. exact (h1). Qed.
Lemma lem3559474 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term79 _91201 _91206 P f x y) = (term79 _91201 _91206 P f x y).
Proof. exact (eq_refl (term79 _91201 _91206 P f x y)). Qed.
Lemma lem3559475 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term87 _91201 _91206 P f x) = (term87 _91201 _91206 P f x).
Proof. exact (fun_ext (fun y : _91206 => @lem3559474 _91201 _91206 P f x y)). Qed.
Lemma lem3559476 {_91206 : Type'} : (@all _91206) = (@all _91206).
Proof. exact (eq_refl (@all _91206)). Qed.
Lemma lem3559477 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term88 _91201 _91206 P f x) = (term88 _91201 _91206 P f x).
Proof. exact (MK_COMB (@lem3559476 _91206) (@lem3559475 _91201 _91206 P f x)). Qed.
Lemma lem3559478 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term96 _91201 _91206 P f) = (term96 _91201 _91206 P f).
Proof. exact (fun_ext (fun x : _91206 => @lem3559477 _91201 _91206 P f x)). Qed.
Lemma lem3559479 {_91206 : Type'} : (@all _91206) = (@all _91206).
Proof. exact (eq_refl (@all _91206)). Qed.
Lemma lem3559480 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term97 _91201 _91206 P f) = (term97 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559479 _91206) (@lem3559478 _91201 _91206 P f)). Qed.
Lemma lem3559513 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term165 _91201 _91206 P f x y) = (term165 _91201 _91206 P f x y).
Proof. exact (eq_refl (term165 _91201 _91206 P f x y)). Qed.
Lemma lem3559514 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) : (term167 _91201 _91206 x y P f) = (term167 _91201 _91206 x y P f).
Proof. exact (MK_COMB (@lem3559513 _91201 _91206 P f x y) (@lem3559480 _91201 _91206 P f)). Qed.
Lemma lem3559567 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term73 _91201 _91206 P f x y) = (term73 _91201 _91206 P f x y).
Proof. exact (eq_refl (term73 _91201 _91206 P f x y)). Qed.
Lemma lem3559602 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term45 _91201 _91206 P f x y) = (term45 _91201 _91206 P f x y).
Proof. exact (eq_refl (term45 _91201 _91206 P f x y)). Qed.
Lemma lem3559603 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term55 _91201 _91206 P f x) = (term55 _91201 _91206 P f x).
Proof. exact (fun_ext (fun y : _91206 => @lem3559602 _91201 _91206 P f x y)). Qed.
Lemma lem3559604 {_91206 : Type'} : (@all _91206) = (@all _91206).
Proof. exact (eq_refl (@all _91206)). Qed.
Lemma lem3559605 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term56 _91201 _91206 P f x) = (term56 _91201 _91206 P f x).
Proof. exact (MK_COMB (@lem3559604 _91206) (@lem3559603 _91201 _91206 P f x)). Qed.
Lemma lem3559606 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term64 _91201 _91206 P f) = (term64 _91201 _91206 P f).
Proof. exact (fun_ext (fun x : _91206 => @lem3559605 _91201 _91206 P f x)). Qed.
Lemma lem3559607 {_91206 : Type'} : (@all _91206) = (@all _91206).
Proof. exact (eq_refl (@all _91206)). Qed.
Lemma lem3559608 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term65 _91201 _91206 P f) = (term65 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559607 _91206) (@lem3559606 _91201 _91206 P f)). Qed.
Lemma lem3559609 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3559610 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term103 _91201 _91206 P f) = (term103 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559609) (@lem3559608 _91201 _91206 P f)). Qed.
Lemma lem3559611 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term132 _91201 _91206 P f x y) = (term132 _91201 _91206 P f x y).
Proof. exact (MK_COMB (@lem3559610 _91201 _91206 P f) (@lem3559567 _91201 _91206 P f x y)). Qed.
Lemma lem3559612 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3559613 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term206 _91201 _91206 P f x y) = (term206 _91201 _91206 P f x y).
Proof. exact (MK_COMB (@lem3559612) (@lem3559611 _91201 _91206 P f x y)). Qed.
Lemma lem3559614 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) : (term208 _91201 _91206 x y P f) = (term208 _91201 _91206 x y P f).
Proof. exact (MK_COMB (@lem3559613 _91201 _91206 P f x y) (@lem3559514 _91201 _91206 x y P f)). Qed.
Lemma lem3559615 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term208 _91201 _91206 x y P f) : term208 _91201 _91206 x y P f.
Proof. exact (EQ_MP (@lem3559614 _91201 _91206 x y P f) (@lem3559417 _91201 _91206 x y P f h1)). Qed.
Lemma lem3559616 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term132 _91201 _91206 P f x y) : term132 _91201 _91206 P f x y.
Proof. exact (h1). Qed.
Lemma lem3559617 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : term167 _91201 _91206 x y P f.
Proof. exact (h1). Qed.
Lemma lem3559618 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term132 _91201 _91206 P f x y) : term73 _91201 _91206 P f x y.
Proof. exact (proj2 (@lem3559616 _91201 _91206 P f x y h1)). Qed.
Lemma lem3559619 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term132 _91201 _91206 P f x y) : term65 _91201 _91206 P f.
Proof. exact (proj1 (@lem3559616 _91201 _91206 P f x y h1)). Qed.
Lemma lem3559620 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term132 _91201 _91206 P f x y) : term69 _91201 _91206 f x y.
Proof. exact (proj2 (@lem3559618 _91201 _91206 P f x y h1)). Qed.
Lemma lem3559621 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term132 _91201 _91206 P f x y) : term75 _91206 x P y.
Proof. exact (proj1 (@lem3559618 _91201 _91206 P f x y h1)). Qed.
Lemma lem3559622 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term132 _91201 _91206 P f x y) : term214 _91201 _91206 f x y.
Proof. exact (proj2 (@lem3559620 _91201 _91206 P f x y h1)). Qed.
Lemma lem3559623 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term132 _91201 _91206 P f x y) : term215 _91201 _91206 f x y.
Proof. exact (proj1 (@lem3559620 _91201 _91206 P f x y h1)). Qed.
Lemma lem3559632 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : term97 _91201 _91206 P f.
Proof. exact (proj2 (@lem3559617 _91201 _91206 x y P f h1)). Qed.
Lemma lem3559633 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : term40 _91201 _91206 P f x y.
Proof. exact (proj1 (@lem3559617 _91201 _91206 x y P f h1)). Qed.
Lemma lem3559635 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : term41 _91201 _91206 P x f y.
Proof. exact (proj1 (@lem3559633 _91201 _91206 x y P f h1)). Qed.
Lemma lem3559636 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : term38 _91201 _91206 P x f y.
Proof. exact (proj2 (@lem3559635 _91201 _91206 x y P f h1)). Qed.
Lemma lem3559679 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term216 _91201 _91206 x f y) : term216 _91201 _91206 x f y.
Proof. exact (h1). Qed.
Lemma lem3559683 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : (f x) = (f y)) : (f x) = (f y).
Proof. exact (h1). Qed.
Lemma lem3559723 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term216 _91201 _91206 x f y) : term216 _91201 _91206 x f y.
Proof. exact (h1). Qed.
Lemma lem3559727 {_91206 : Type'} (x : _91206) (y : _91206) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem3559747 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term45 _91201 _91206 P f x y) = (term45 _91201 _91206 P f x y).
Proof. exact (eq_refl (term45 _91201 _91206 P f x y)). Qed.
Lemma lem3559748 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term55 _91201 _91206 P f x) = (term55 _91201 _91206 P f x).
Proof. exact (fun_ext (fun y : _91206 => @lem3559747 _91201 _91206 P f x y)). Qed.
Lemma lem3559749 {_91206 : Type'} : (@all _91206) = (@all _91206).
Proof. exact (eq_refl (@all _91206)). Qed.
Lemma lem3559750 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term56 _91201 _91206 P f x) = (term56 _91201 _91206 P f x).
Proof. exact (MK_COMB (@lem3559749 _91206) (@lem3559748 _91201 _91206 P f x)). Qed.
Lemma lem3559751 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term64 _91201 _91206 P f) = (term64 _91201 _91206 P f).
Proof. exact (fun_ext (fun x : _91206 => @lem3559750 _91201 _91206 P f x)). Qed.
Lemma lem3559752 {_91206 : Type'} : (@all _91206) = (@all _91206).
Proof. exact (eq_refl (@all _91206)). Qed.
Lemma lem3559754 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term65 _91201 _91206 P f) = (term65 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559752 _91206) (@lem3559751 _91201 _91206 P f)). Qed.
Lemma lem3559755 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term132 _91201 _91206 P f x y) : term65 _91201 _91206 P f.
Proof. exact (EQ_MP (@lem3559754 _91201 _91206 P f) (@lem3559619 _91201 _91206 P f x y h1)). Qed.
Lemma lem3559767 {_91206 : Type'} (x : _91206) (y : _91206) (h1 : term217 _91206 x y) : term217 _91206 x y.
Proof. exact (h1). Qed.
Lemma lem3559771 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : (f x) = (f y)) : (f x) = (f y).
Proof. exact (h1). Qed.
Lemma lem3559811 {_91206 : Type'} (x : _91206) (y : _91206) (h1 : term217 _91206 x y) : term217 _91206 x y.
Proof. exact (h1). Qed.
Lemma lem3559815 {_91206 : Type'} (x : _91206) (y : _91206) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem3559851 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) : (term79 _91201 _91206 P f x y) = (term218 _91201 _91206 P f x y).
Proof. exact (@lem19490 (term219 _91201 _91206 f x y) (term67 _91206 x P y) (term220 _91201 _91206 f x y)). Qed.
Lemma lem3559852 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term87 _91201 _91206 P f x) = (term221 _91201 _91206 P f x).
Proof. exact (fun_ext (fun y : _91206 => @lem3559851 _91201 _91206 P f x y)). Qed.
Lemma lem3559853 {_91206 : Type'} : (@all _91206) = (@all _91206).
Proof. exact (eq_refl (@all _91206)). Qed.
Lemma lem3559854 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) : (term88 _91201 _91206 P f x) = (term222 _91201 _91206 P f x).
Proof. exact (MK_COMB (@lem3559853 _91206) (@lem3559852 _91201 _91206 P f x)). Qed.
Lemma lem3559855 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term96 _91201 _91206 P f) = (term223 _91201 _91206 P f).
Proof. exact (fun_ext (fun x : _91206 => @lem3559854 _91201 _91206 P f x)). Qed.
Lemma lem3559856 {_91206 : Type'} : (@all _91206) = (@all _91206).
Proof. exact (eq_refl (@all _91206)). Qed.
Lemma lem3559858 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term97 _91201 _91206 P f) = (term224 _91201 _91206 P f).
Proof. exact (MK_COMB (@lem3559856 _91206) (@lem3559855 _91201 _91206 P f)). Qed.
Lemma lem3559859 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : term224 _91201 _91206 P f.
Proof. exact (EQ_MP (@lem3559858 _91201 _91206 P f) (@lem3559632 _91201 _91206 x y P f h1)). Qed.
Lemma lem3559888 {_91201 _91206 : Type'} (_38146 : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term132 _91201 _91206 P f x y) : term225 _91201 _91206 P f _38146.
Proof. exact (@lem3559755 _91201 _91206 P f x y h1 _38146). Qed.
Lemma lem3559889 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (_38146 : _91206) : (term225 _91201 _91206 P f _38146) = (term56 _91201 _91206 P f _38146).
Proof. exact (eq_refl (term225 _91201 _91206 P f _38146)). Qed.
Lemma lem3559890 {_91201 _91206 : Type'} (_38146 : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term132 _91201 _91206 P f x y) : term56 _91201 _91206 P f _38146.
Proof. exact (EQ_MP (@lem3559889 _91201 _91206 P f _38146) (@lem3559888 _91201 _91206 _38146 P f x y h1)). Qed.
Lemma lem3559891 {_91201 _91206 : Type'} (_38146 : _91206) (_38147 : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term132 _91201 _91206 P f x y) : term226 _91201 _91206 P f _38146 _38147.
Proof. exact (@lem3559890 _91201 _91206 _38146 P f x y h1 _38147). Qed.
Lemma lem3559892 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (_38146 : _91206) (_38147 : _91206) : (term226 _91201 _91206 P f _38146 _38147) = (term45 _91201 _91206 P f _38146 _38147).
Proof. exact (eq_refl (term226 _91201 _91206 P f _38146 _38147)). Qed.
Lemma lem3559893 {_91201 _91206 : Type'} (_38146 : _91206) (_38147 : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term132 _91201 _91206 P f x y) : term45 _91201 _91206 P f _38146 _38147.
Proof. exact (EQ_MP (@lem3559892 _91201 _91206 P f _38146 _38147) (@lem3559891 _91201 _91206 _38146 _38147 P f x y h1)). Qed.
Lemma lem3559900 {_91201 _91206 : Type'} (_38150 : _91206) (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : term227 _91201 _91206 P f _38150.
Proof. exact (@lem3559859 _91201 _91206 x y P f h1 _38150). Qed.
Lemma lem3559901 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (_38150 : _91206) : (term227 _91201 _91206 P f _38150) = (term222 _91201 _91206 P f _38150).
Proof. exact (eq_refl (term227 _91201 _91206 P f _38150)). Qed.
Lemma lem3559902 {_91201 _91206 : Type'} (_38150 : _91206) (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : term222 _91201 _91206 P f _38150.
Proof. exact (EQ_MP (@lem3559901 _91201 _91206 P f _38150) (@lem3559900 _91201 _91206 _38150 x y P f h1)). Qed.
Lemma lem3559903 {_91201 _91206 : Type'} (_38150 : _91206) (_38151 : _91206) (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : term228 _91201 _91206 P f _38150 _38151.
Proof. exact (@lem3559902 _91201 _91206 _38150 x y P f h1 _38151). Qed.
Lemma lem3559904 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (_38150 : _91206) (_38151 : _91206) : (term228 _91201 _91206 P f _38150 _38151) = (term218 _91201 _91206 P f _38150 _38151).
Proof. exact (eq_refl (term228 _91201 _91206 P f _38150 _38151)). Qed.
Lemma lem3559905 {_91201 _91206 : Type'} (_38150 : _91206) (_38151 : _91206) (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : term218 _91201 _91206 P f _38150 _38151.
Proof. exact (EQ_MP (@lem3559904 _91201 _91206 P f _38150 _38151) (@lem3559903 _91201 _91206 _38150 _38151 x y P f h1)). Qed.
Lemma lem3559906 {_91201 _91206 : Type'} (_38150 : _91206) (_38151 : _91206) (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : term229 _91201 _91206 P f _38150 _38151.
Proof. exact (proj2 (@lem3559905 _91201 _91206 _38150 _38151 x y P f h1)). Qed.
Lemma lem3559931 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term216 _91201 _91206 x f y) : term216 _91201 _91206 x f y.
Proof. exact (h1). Qed.
Lemma lem3559933 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : (f x) = (f y)) : (f x) = (f y).
Proof. exact (h1). Qed.
Lemma lem3559957 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term216 _91201 _91206 x f y) : term216 _91201 _91206 x f y.
Proof. exact (h1). Qed.
Lemma lem3559959 {_91206 : Type'} (x : _91206) (y : _91206) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem3559963 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (_38146 : _91206) (_38147 : _91206) : (term45 _91201 _91206 P f _38146 _38147) = (term230 _91201 _91206 P f _38146 _38147).
Proof. exact (@lem3558732 (term231 _91206 P _38146) (term33 _91201 _91206 P _38146 f _38147) (_38146 = _38147)). Qed.
Lemma lem3559970 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (_38146 : _91206) (_38147 : _91206) : (term232 _91201 _91206 P f _38146 _38147) = (term233 _91201 _91206 P f _38146 _38147).
Proof. exact (@lem3558732 (term231 _91206 P _38147) (term216 _91201 _91206 _38146 f _38147) (_38146 = _38147)). Qed.
Lemma lem3559971 {_91206 : Type'} (P : _91206 -> Prop) (_38146 : _91206) : (term34 _91206 P _38146) = (term34 _91206 P _38146).
Proof. exact (eq_refl (term34 _91206 P _38146)). Qed.
Lemma lem3559974 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (_38146 : _91206) (_38147 : _91206) : (term230 _91201 _91206 P f _38146 _38147) = (term234 _91201 _91206 P f _38146 _38147).
Proof. exact (MK_COMB (@lem3559971 _91206 P _38146) (@lem3559970 _91201 _91206 P f _38146 _38147)). Qed.
Lemma lem3559976 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (_38146 : _91206) (_38147 : _91206) : (term45 _91201 _91206 P f _38146 _38147) = (term234 _91201 _91206 P f _38146 _38147).
Proof. exact (TRANS (@lem3559963 _91201 _91206 P f _38146 _38147) (@lem3559974 _91201 _91206 P f _38146 _38147)). Qed.
Lemma lem3559977 {_91201 _91206 : Type'} (_38146 : _91206) (_38147 : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term132 _91201 _91206 P f x y) : term234 _91201 _91206 P f _38146 _38147.
Proof. exact (EQ_MP (@lem3559976 _91201 _91206 P f _38146 _38147) (@lem3559893 _91201 _91206 _38146 _38147 P f x y h1)). Qed.
Lemma lem3559983 {_91206 : Type'} (x : _91206) (y : _91206) (h1 : term217 _91206 x y) : term217 _91206 x y.
Proof. exact (h1). Qed.
Lemma lem3559985 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : (f x) = (f y)) : (f x) = (f y).
Proof. exact (h1). Qed.
Lemma lem3560009 {_91206 : Type'} (x : _91206) (y : _91206) (h1 : term217 _91206 x y) : term217 _91206 x y.
Proof. exact (h1). Qed.
Lemma lem3560011 {_91206 : Type'} (x : _91206) (y : _91206) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem3560013 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : term217 _91206 x y.
Proof. exact (proj2 (@lem3559633 _91201 _91206 x y P f h1)). Qed.
Lemma lem3560050 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (_38150 : _91206) (_38151 : _91206) : (term229 _91201 _91206 P f _38150 _38151) = (term234 _91201 _91206 P f _38150 _38151).
Proof. exact (@lem3558732 (term231 _91206 P _38150) (term231 _91206 P _38151) (term220 _91201 _91206 f _38150 _38151)). Qed.
Lemma lem3560051 {_91201 _91206 : Type'} (_38150 : _91206) (_38151 : _91206) (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : term234 _91201 _91206 P f _38150 _38151.
Proof. exact (EQ_MP (@lem3560050 _91201 _91206 P f _38150 _38151) (@lem3559906 _91201 _91206 _38150 _38151 x y P f h1)). Qed.
Lemma lem3560107 {_91201 _91206 : Type'} (f : _91206 -> _91201) (y : _91206) : (term235 _91201 _91206 f y) = (term235 _91201 _91206 f y).
Proof. exact (eq_refl (term235 _91201 _91206 f y)). Qed.
Lemma lem3560108 {_91201 _91206 : Type'} (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : x = y) : (term236 _91201 _91206 f y x) = (term237 _91201 _91206 f y).
Proof. exact (MK_COMB (@lem3560107 _91201 _91206 f y) (@lem3559959 _91206 x y h1)). Qed.
Lemma lem3560109 {_91201 _91206 : Type'} (f : _91206 -> _91201) (y : _91206) : (term237 _91201 _91206 f y) = (term238 _91201 _91206 f y).
Proof. exact (eq_refl (term237 _91201 _91206 f y)). Qed.
Lemma lem3560110 {_91201 _91206 : Type'} (f : _91206 -> _91201) (y : _91206) (x : _91206) : (term239 _91201 _91206 f y x) = (term239 _91201 _91206 f y x).
Proof. exact (eq_refl (term239 _91201 _91206 f y x)). Qed.
Lemma lem3560111 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) : ((term236 _91201 _91206 f y x) = (term237 _91201 _91206 f y)) = ((term236 _91201 _91206 f y x) = (term238 _91201 _91206 f y)).
Proof. exact (MK_COMB (@lem3560110 _91201 _91206 f y x) (@lem3560109 _91201 _91206 f y)). Qed.
Lemma lem3560112 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) : (term236 _91201 _91206 f y x) = (term216 _91201 _91206 x f y).
Proof. exact (eq_refl (term236 _91201 _91206 f y x)). Qed.
Lemma lem3560113 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3560114 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) : (term239 _91201 _91206 f y x) = (term240 _91201 _91206 x f y).
Proof. exact (MK_COMB (@lem3560113) (@lem3560112 _91201 _91206 x f y)). Qed.
Lemma lem3560115 {_91201 _91206 : Type'} (f : _91206 -> _91201) (y : _91206) : (term238 _91201 _91206 f y) = (term238 _91201 _91206 f y).
Proof. exact (eq_refl (term238 _91201 _91206 f y)). Qed.
Lemma lem3560116 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) : ((term236 _91201 _91206 f y x) = (term238 _91201 _91206 f y)) = ((term216 _91201 _91206 x f y) = (term238 _91201 _91206 f y)).
Proof. exact (MK_COMB (@lem3560114 _91201 _91206 x f y) (@lem3560115 _91201 _91206 f y)). Qed.
Lemma lem3560117 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) : ((term236 _91201 _91206 f y x) = (term237 _91201 _91206 f y)) = ((term216 _91201 _91206 x f y) = (term238 _91201 _91206 f y)).
Proof. exact (TRANS (@lem3560111 _91201 _91206 x f y) (@lem3560116 _91201 _91206 x f y)). Qed.
Lemma lem3560118 {_91201 _91206 : Type'} (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : x = y) : (term216 _91201 _91206 x f y) = (term238 _91201 _91206 f y).
Proof. exact (EQ_MP (@lem3560117 _91201 _91206 x f y) (@lem3560108 _91201 _91206 f x y h1)). Qed.
Lemma lem3560119 {_91201 _91206 : Type'} (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : x = y) : term238 _91201 _91206 f y.
Proof. exact (EQ_MP (@lem3560118 _91201 _91206 f x y h2) (@lem3559957 _91201 _91206 x f y h1)). Qed.
Lemma lem3560175 {_91206 : Type'} (y : _91206) : (term241 _91206 y) = (term241 _91206 y).
Proof. exact (eq_refl (term241 _91206 y)). Qed.
Lemma lem3560176 {_91206 : Type'} (x : _91206) (y : _91206) (h1 : x = y) : (term242 _91206 y x) = (term243 _91206 y).
Proof. exact (MK_COMB (@lem3560175 _91206 y) (@lem3560011 _91206 x y h1)). Qed.
Lemma lem3560177 {_91206 : Type'} (y : _91206) : (term243 _91206 y) = (term244 _91206 y).
Proof. exact (eq_refl (term243 _91206 y)). Qed.
Lemma lem3560178 {_91206 : Type'} (y : _91206) (x : _91206) : (term245 _91206 y x) = (term245 _91206 y x).
Proof. exact (eq_refl (term245 _91206 y x)). Qed.
Lemma lem3560179 {_91206 : Type'} (x : _91206) (y : _91206) : ((term242 _91206 y x) = (term243 _91206 y)) = ((term242 _91206 y x) = (term244 _91206 y)).
Proof. exact (MK_COMB (@lem3560178 _91206 y x) (@lem3560177 _91206 y)). Qed.
Lemma lem3560180 {_91206 : Type'} (x : _91206) (y : _91206) : (term242 _91206 y x) = (term217 _91206 x y).
Proof. exact (eq_refl (term242 _91206 y x)). Qed.
Lemma lem3560181 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3560182 {_91206 : Type'} (x : _91206) (y : _91206) : (term245 _91206 y x) = (term246 _91206 x y).
Proof. exact (MK_COMB (@lem3560181) (@lem3560180 _91206 x y)). Qed.
Lemma lem3560183 {_91206 : Type'} (y : _91206) : (term244 _91206 y) = (term244 _91206 y).
Proof. exact (eq_refl (term244 _91206 y)). Qed.
Lemma lem3560184 {_91206 : Type'} (x : _91206) (y : _91206) : ((term242 _91206 y x) = (term244 _91206 y)) = ((term217 _91206 x y) = (term244 _91206 y)).
Proof. exact (MK_COMB (@lem3560182 _91206 x y) (@lem3560183 _91206 y)). Qed.
Lemma lem3560185 {_91206 : Type'} (x : _91206) (y : _91206) : ((term242 _91206 y x) = (term243 _91206 y)) = ((term217 _91206 x y) = (term244 _91206 y)).
Proof. exact (TRANS (@lem3560179 _91206 x y) (@lem3560184 _91206 x y)). Qed.
Lemma lem3560186 {_91206 : Type'} (x : _91206) (y : _91206) (h1 : x = y) : (term217 _91206 x y) = (term244 _91206 y).
Proof. exact (EQ_MP (@lem3560185 _91206 x y) (@lem3560176 _91206 x y h1)). Qed.
Lemma lem3560187 {_91206 : Type'} (x : _91206) (y : _91206) (h1 : term217 _91206 x y) (h2 : x = y) : term244 _91206 y.
Proof. exact (EQ_MP (@lem3560186 _91206 x y h2) (@lem3560009 _91206 x y h1)). Qed.
Lemma lem3560213 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : (f x) = (f y)) : (f x) = (f y).
Proof. exact (h1). Qed.
Lemma lem3560214 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : (f x) = (f y)) : term247 _91201 _91206 x f y.
Proof. exact (fun h0 : term216 _91201 _91206 x f y => @lem3560213 _91201 _91206 x f y h1). Qed.
Lemma lem3560216 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3560217 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) : (term247 _91201 _91206 x f y) = ((f x) = (f y)).
Proof. exact (@lem3560216 ((f x) = (f y))). Qed.
Lemma lem3560218 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : (f x) = (f y)) : (f x) = (f y).
Proof. exact (EQ_MP (@lem3560217 _91201 _91206 x f y) (@lem3560214 _91201 _91206 x f y h1)). Qed.
Lemma lem3560221 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3560223 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) : (term216 _91201 _91206 x f y) = (term249 _91201 _91206 x f y).
Proof. exact (@lem3560221 ((f x) = (f y))). Qed.
Lemma lem3560226 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term216 _91201 _91206 x f y) : term249 _91201 _91206 x f y.
Proof. exact (EQ_MP (@lem3560223 _91201 _91206 x f y) (@lem3559931 _91201 _91206 x f y h1)). Qed.
Lemma lem3560229 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : (f x) = (f y)) : False.
Proof. exact (@lem3560226 _91201 _91206 x f y h1 (@lem3560218 _91201 _91206 x f y h2)). Qed.
Lemma lem3560230 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : (f x) = (f y)) : term250.
Proof. exact (fun h0 : ~ False => @lem3560229 _91201 _91206 x f y h1 h2). Qed.
Lemma lem3560232 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3560233 : term250 = False.
Proof. exact (@lem3560232 False). Qed.
Lemma lem3560234 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : (f x) = (f y)) : False.
Proof. exact (EQ_MP (@lem3560233) (@lem3560230 _91201 _91206 x f y h1 h2)). Qed.
Lemma lem3560260 {_91201 : Type'} (x : _91201) : x = x.
Proof. exact (@lem21386 _91201 x). Qed.
Lemma lem3560261 {_91201 : Type'} (x : _91201) : x = x.
Proof. exact (@lem3560260 _91201 x). Qed.
Lemma lem3560262 {_91201 _91206 : Type'} (f : _91206 -> _91201) (y : _91206) : (f y) = (f y).
Proof. exact (@lem3560261 _91201 (f y)). Qed.
Lemma lem3560263 {_91201 _91206 : Type'} (f : _91206 -> _91201) (y : _91206) : term251 _91201 _91206 f y.
Proof. exact (fun h0 : term238 _91201 _91206 f y => @lem3560262 _91201 _91206 f y). Qed.
Lemma lem3560265 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3560266 {_91201 _91206 : Type'} (f : _91206 -> _91201) (y : _91206) : (term251 _91201 _91206 f y) = ((f y) = (f y)).
Proof. exact (@lem3560265 ((f y) = (f y))). Qed.
Lemma lem3560267 {_91201 _91206 : Type'} (f : _91206 -> _91201) (y : _91206) : (f y) = (f y).
Proof. exact (EQ_MP (@lem3560266 _91201 _91206 f y) (@lem3560263 _91201 _91206 f y)). Qed.
Lemma lem3560270 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3560272 {_91201 _91206 : Type'} (f : _91206 -> _91201) (y : _91206) : (term238 _91201 _91206 f y) = (term252 _91201 _91206 f y).
Proof. exact (@lem3560270 ((f y) = (f y))). Qed.
Lemma lem3560275 {_91201 _91206 : Type'} (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : x = y) : term252 _91201 _91206 f y.
Proof. exact (EQ_MP (@lem3560272 _91201 _91206 f y) (@lem3560119 _91201 _91206 f x y h1 h2)). Qed.
Lemma lem3560278 {_91201 _91206 : Type'} (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : x = y) : False.
Proof. exact (@lem3560275 _91201 _91206 f x y h1 h2 (@lem3560267 _91201 _91206 f y)). Qed.
Lemma lem3560279 {_91201 _91206 : Type'} (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : x = y) : term250.
Proof. exact (fun h0 : ~ False => @lem3560278 _91201 _91206 f x y h1 h2). Qed.
Lemma lem3560281 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3560282 : term250 = False.
Proof. exact (@lem3560281 False). Qed.
Lemma lem3560309 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term132 _91201 _91206 P f x y) : P x.
Proof. exact (proj1 (@lem3559621 _91201 _91206 P f x y h1)). Qed.
Lemma lem3560310 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term132 _91201 _91206 P f x y) : term253 _91206 P x.
Proof. exact (fun h0 : term231 _91206 P x => @lem3560309 _91201 _91206 P f x y h1). Qed.
Lemma lem3560312 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3560313 {_91206 : Type'} (P : _91206 -> Prop) (x : _91206) : (term253 _91206 P x) = (P x).
Proof. exact (@lem3560312 (P x)). Qed.
Lemma lem3560314 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term132 _91201 _91206 P f x y) : P x.
Proof. exact (EQ_MP (@lem3560313 _91206 P x) (@lem3560310 _91201 _91206 P f x y h1)). Qed.
Lemma lem3560316 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term132 _91201 _91206 P f x y) : P y.
Proof. exact (proj2 (@lem3559621 _91201 _91206 P f x y h1)). Qed.
Lemma lem3560317 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term132 _91201 _91206 P f x y) : term253 _91206 P y.
Proof. exact (fun h0 : term231 _91206 P y => @lem3560316 _91201 _91206 P f x y h1). Qed.
Lemma lem3560319 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3560320 {_91206 : Type'} (P : _91206 -> Prop) (y : _91206) : (term253 _91206 P y) = (P y).
Proof. exact (@lem3560319 (P y)). Qed.
Lemma lem3560321 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term132 _91201 _91206 P f x y) : P y.
Proof. exact (EQ_MP (@lem3560320 _91206 P y) (@lem3560317 _91201 _91206 P f x y h1)). Qed.
Lemma lem3560323 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : (f x) = (f y)) : (f x) = (f y).
Proof. exact (h1). Qed.
Lemma lem3560324 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : (f x) = (f y)) : term247 _91201 _91206 x f y.
Proof. exact (fun h0 : term216 _91201 _91206 x f y => @lem3560323 _91201 _91206 x f y h1). Qed.
Lemma lem3560326 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3560327 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) : (term247 _91201 _91206 x f y) = ((f x) = (f y)).
Proof. exact (@lem3560326 ((f x) = (f y))). Qed.
Lemma lem3560328 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : (f x) = (f y)) : (f x) = (f y).
Proof. exact (EQ_MP (@lem3560327 _91201 _91206 x f y) (@lem3560324 _91201 _91206 x f y h1)). Qed.
Lemma lem3560354 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3560355 {_91201 _91206 : Type'} (_38146 : _91206) (f : _91206 -> _91201) (_38147 : _91206) : (term220 _91201 _91206 f _38146 _38147) = (term254 _91201 _91206 _38146 f _38147).
Proof. exact (@lem3560354 (_38146 = _38147) (term216 _91201 _91206 _38146 f _38147)). Qed.
Lemma lem3560365 {_91206 : Type'} (P : _91206 -> Prop) (_38147 : _91206) : (term34 _91206 P _38147) = (term34 _91206 P _38147).
Proof. exact (eq_refl (term34 _91206 P _38147)). Qed.
Lemma lem3560366 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38146 : _91206) (f : _91206 -> _91201) (_38147 : _91206) : (term233 _91201 _91206 P f _38146 _38147) = (term255 _91201 _91206 P _38146 f _38147).
Proof. exact (MK_COMB (@lem3560365 _91206 P _38147) (@lem3560355 _91201 _91206 _38146 f _38147)). Qed.
Lemma lem3560370 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3560371 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38146 : _91206) (f : _91206 -> _91201) (_38147 : _91206) : (term255 _91201 _91206 P _38146 f _38147) = (term256 _91201 _91206 P _38146 f _38147).
Proof. exact (@lem3560370 (_38146 = _38147) (term231 _91206 P _38147) (term216 _91201 _91206 _38146 f _38147)). Qed.
Lemma lem3560391 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38146 : _91206) (f : _91206 -> _91201) (_38147 : _91206) : (term233 _91201 _91206 P f _38146 _38147) = (term256 _91201 _91206 P _38146 f _38147).
Proof. exact (TRANS (@lem3560366 _91201 _91206 P _38146 f _38147) (@lem3560371 _91201 _91206 P _38146 f _38147)). Qed.
Lemma lem3560392 {_91206 : Type'} (P : _91206 -> Prop) (_38146 : _91206) : (term34 _91206 P _38146) = (term34 _91206 P _38146).
Proof. exact (eq_refl (term34 _91206 P _38146)). Qed.
Lemma lem3560393 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38146 : _91206) (f : _91206 -> _91201) (_38147 : _91206) : (term234 _91201 _91206 P f _38146 _38147) = (term257 _91201 _91206 P _38146 f _38147).
Proof. exact (MK_COMB (@lem3560392 _91206 P _38146) (@lem3560391 _91201 _91206 P _38146 f _38147)). Qed.
Lemma lem3560397 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3560398 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38146 : _91206) (f : _91206 -> _91201) (_38147 : _91206) : (term257 _91201 _91206 P _38146 f _38147) = (term258 _91201 _91206 P _38146 f _38147).
Proof. exact (@lem3560397 (_38146 = _38147) (term231 _91206 P _38146) (term33 _91201 _91206 P _38146 f _38147)). Qed.
Lemma lem3560428 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38146 : _91206) (f : _91206 -> _91201) (_38147 : _91206) : (term234 _91201 _91206 P f _38146 _38147) = (term258 _91201 _91206 P _38146 f _38147).
Proof. exact (TRANS (@lem3560393 _91201 _91206 P _38146 f _38147) (@lem3560398 _91201 _91206 P _38146 f _38147)). Qed.
Lemma lem3560429 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3560430 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38146 : _91206) (f : _91206 -> _91201) (_38147 : _91206) : (term259 _91201 _91206 P f _38146 _38147) = (term260 _91201 _91206 P _38146 f _38147).
Proof. exact (MK_COMB (@lem3560429) (@lem3560428 _91201 _91206 P _38146 f _38147)). Qed.
Lemma lem3560460 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38146 : _91206) (f : _91206 -> _91201) (_38147 : _91206) : (term258 _91201 _91206 P _38146 f _38147) = (term258 _91201 _91206 P _38146 f _38147).
Proof. exact (eq_refl (term258 _91201 _91206 P _38146 f _38147)). Qed.
Lemma lem3560461 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38146 : _91206) (f : _91206 -> _91201) (_38147 : _91206) : ((term234 _91201 _91206 P f _38146 _38147) = (term258 _91201 _91206 P _38146 f _38147)) = ((term258 _91201 _91206 P _38146 f _38147) = (term258 _91201 _91206 P _38146 f _38147)).
Proof. exact (MK_COMB (@lem3560430 _91201 _91206 P _38146 f _38147) (@lem3560460 _91201 _91206 P _38146 f _38147)). Qed.
Lemma lem3560463 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3560464 (x : Prop) : (x = x) = True.
Proof. exact (@lem3560463 Prop x). Qed.
Lemma lem3560465 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38146 : _91206) (f : _91206 -> _91201) (_38147 : _91206) : ((term258 _91201 _91206 P _38146 f _38147) = (term258 _91201 _91206 P _38146 f _38147)) = True.
Proof. exact (@lem3560464 (term258 _91201 _91206 P _38146 f _38147)). Qed.
Lemma lem3560466 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38146 : _91206) (f : _91206 -> _91201) (_38147 : _91206) : ((term234 _91201 _91206 P f _38146 _38147) = (term258 _91201 _91206 P _38146 f _38147)) = True.
Proof. exact (TRANS (@lem3560461 _91201 _91206 P _38146 f _38147) (@lem3560465 _91201 _91206 P _38146 f _38147)). Qed.
Lemma lem3560467 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38146 : _91206) (f : _91206 -> _91201) (_38147 : _91206) : True = ((term234 _91201 _91206 P f _38146 _38147) = (term258 _91201 _91206 P _38146 f _38147)).
Proof. exact (SYM (@lem3560466 _91201 _91206 P _38146 f _38147)). Qed.
Lemma lem3560468 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38146 : _91206) (f : _91206 -> _91201) (_38147 : _91206) : (term234 _91201 _91206 P f _38146 _38147) = (term258 _91201 _91206 P _38146 f _38147).
Proof. exact (EQ_MP (@lem3560467 _91201 _91206 P _38146 f _38147) (@lem0)). Qed.
Lemma lem3560469 {_91201 _91206 : Type'} (_38146 : _91206) (_38147 : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term132 _91201 _91206 P f x y) : term258 _91201 _91206 P _38146 f _38147.
Proof. exact (EQ_MP (@lem3560468 _91201 _91206 P _38146 f _38147) (@lem3559977 _91201 _91206 _38146 _38147 P f x y h1)). Qed.
Lemma lem3560471 (b : Prop) (a : Prop) : (a \/ b) = (term261 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3560472 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (_38146 : _91206) (_38147 : _91206) : (term258 _91201 _91206 P _38146 f _38147) = (term262 _91201 _91206 P f _38146 _38147).
Proof. exact (@lem3560471 (term36 _91201 _91206 P _38146 f _38147) (_38146 = _38147)). Qed.
Lemma lem3560474 (a : Prop) (b : Prop) : (term263 a b) = (term264 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3560475 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38146 : _91206) (f : _91206 -> _91201) (_38147 : _91206) : (term265 _91201 _91206 P _38146 f _38147) = (term266 _91201 _91206 P _38146 f _38147).
Proof. exact (@lem3560474 (term231 _91206 P _38146) (term33 _91201 _91206 P _38146 f _38147)). Qed.
Lemma lem3560477 (a : Prop) : (term15 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3560478 {_91206 : Type'} (P : _91206 -> Prop) (_38146 : _91206) : (term267 _91206 P _38146) = (P _38146).
Proof. exact (@lem3560477 (P _38146)). Qed.
Lemma lem3560479 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3560480 {_91206 : Type'} (P : _91206 -> Prop) (_38146 : _91206) : (term268 _91206 P _38146) = (term269 _91206 P _38146).
Proof. exact (MK_COMB (@lem3560479) (@lem3560478 _91206 P _38146)). Qed.
Lemma lem3560482 (a : Prop) (b : Prop) : (term263 a b) = (term264 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3560483 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38146 : _91206) (f : _91206 -> _91201) (_38147 : _91206) : (term270 _91201 _91206 P _38146 f _38147) = (term271 _91201 _91206 P _38146 f _38147).
Proof. exact (@lem3560482 (term231 _91206 P _38147) (term216 _91201 _91206 _38146 f _38147)). Qed.
Lemma lem3560485 (a : Prop) : (term15 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3560486 {_91206 : Type'} (P : _91206 -> Prop) (_38147 : _91206) : (term267 _91206 P _38147) = (P _38147).
Proof. exact (@lem3560485 (P _38147)). Qed.
Lemma lem3560487 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3560488 {_91206 : Type'} (P : _91206 -> Prop) (_38147 : _91206) : (term268 _91206 P _38147) = (term269 _91206 P _38147).
Proof. exact (MK_COMB (@lem3560487) (@lem3560486 _91206 P _38147)). Qed.
Lemma lem3560490 (a : Prop) : (term15 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3560491 {_91201 _91206 : Type'} (_38146 : _91206) (f : _91206 -> _91201) (_38147 : _91206) : (term272 _91201 _91206 _38146 f _38147) = ((f _38146) = (f _38147)).
Proof. exact (@lem3560490 ((f _38146) = (f _38147))). Qed.
Lemma lem3560492 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38146 : _91206) (f : _91206 -> _91201) (_38147 : _91206) : (term271 _91201 _91206 P _38146 f _38147) = (term38 _91201 _91206 P _38146 f _38147).
Proof. exact (MK_COMB (@lem3560488 _91206 P _38147) (@lem3560491 _91201 _91206 _38146 f _38147)). Qed.
Lemma lem3560493 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38146 : _91206) (f : _91206 -> _91201) (_38147 : _91206) : (term270 _91201 _91206 P _38146 f _38147) = (term38 _91201 _91206 P _38146 f _38147).
Proof. exact (TRANS (@lem3560483 _91201 _91206 P _38146 f _38147) (@lem3560492 _91201 _91206 P _38146 f _38147)). Qed.
Lemma lem3560494 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38146 : _91206) (f : _91206 -> _91201) (_38147 : _91206) : (term266 _91201 _91206 P _38146 f _38147) = (term41 _91201 _91206 P _38146 f _38147).
Proof. exact (MK_COMB (@lem3560480 _91206 P _38146) (@lem3560493 _91201 _91206 P _38146 f _38147)). Qed.
Lemma lem3560495 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38146 : _91206) (f : _91206 -> _91201) (_38147 : _91206) : (term265 _91201 _91206 P _38146 f _38147) = (term41 _91201 _91206 P _38146 f _38147).
Proof. exact (TRANS (@lem3560475 _91201 _91206 P _38146 f _38147) (@lem3560494 _91201 _91206 P _38146 f _38147)). Qed.
Lemma lem3560496 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3560497 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38146 : _91206) (f : _91206 -> _91201) (_38147 : _91206) : (term273 _91201 _91206 P _38146 f _38147) = (term274 _91201 _91206 P _38146 f _38147).
Proof. exact (MK_COMB (@lem3560496) (@lem3560495 _91201 _91206 P _38146 f _38147)). Qed.
Lemma lem3560498 {_91206 : Type'} (_38146 : _91206) (_38147 : _91206) : (_38146 = _38147) = (_38146 = _38147).
Proof. exact (eq_refl (_38146 = _38147)). Qed.
Lemma lem3560499 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (_38146 : _91206) (_38147 : _91206) : (term262 _91201 _91206 P f _38146 _38147) = (term21 _91201 _91206 P f _38146 _38147).
Proof. exact (MK_COMB (@lem3560497 _91201 _91206 P _38146 f _38147) (@lem3560498 _91206 _38146 _38147)). Qed.
Lemma lem3560500 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (_38146 : _91206) (_38147 : _91206) : (term258 _91201 _91206 P _38146 f _38147) = (term21 _91201 _91206 P f _38146 _38147).
Proof. exact (TRANS (@lem3560472 _91201 _91206 P f _38146 _38147) (@lem3560499 _91201 _91206 P f _38146 _38147)). Qed.
Lemma lem3560502 {_91201 _91206 : Type'} (P : _91206 -> Prop) (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term132 _91201 _91206 P f x y) (h2 : (f x) = (f y)) : term38 _91201 _91206 P x f y.
Proof. exact (conj (@lem3560321 _91201 _91206 P f x y h1) (@lem3560328 _91201 _91206 x f y h2)). Qed.
Lemma lem3560503 {_91201 _91206 : Type'} (P : _91206 -> Prop) (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term132 _91201 _91206 P f x y) (h2 : (f x) = (f y)) : term41 _91201 _91206 P x f y.
Proof. exact (conj (@lem3560314 _91201 _91206 P f x y h1) (@lem3560502 _91201 _91206 P x f y h1 h2)). Qed.
Lemma lem3560505 {_91201 _91206 : Type'} (_38146 : _91206) (_38147 : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term132 _91201 _91206 P f x y) : term21 _91201 _91206 P f _38146 _38147.
Proof. exact (EQ_MP (@lem3560500 _91201 _91206 P f _38146 _38147) (@lem3560469 _91201 _91206 _38146 _38147 P f x y h1)). Qed.
Lemma lem3560506 {_91201 _91206 : Type'} (_38146 : _91206) (_38147 : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term132 _91201 _91206 P f x y) : term21 _91201 _91206 P f _38146 _38147.
Proof. exact (@lem3560505 _91201 _91206 _38146 _38147 P f x y h1). Qed.
Lemma lem3560507 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term132 _91201 _91206 P f x y) : term21 _91201 _91206 P f x y.
Proof. exact (@lem3560506 _91201 _91206 x y P f x y h1). Qed.
Lemma lem3560510 {_91201 _91206 : Type'} (P : _91206 -> Prop) (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term132 _91201 _91206 P f x y) (h2 : (f x) = (f y)) : x = y.
Proof. exact (@lem3560507 _91201 _91206 P f x y h1 (@lem3560503 _91201 _91206 P x f y h1 h2)). Qed.
Lemma lem3560511 {_91201 _91206 : Type'} (P : _91206 -> Prop) (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term132 _91201 _91206 P f x y) (h2 : (f x) = (f y)) : term275 _91206 x y.
Proof. exact (fun h0 : term217 _91206 x y => @lem3560510 _91201 _91206 P x f y h1 h2). Qed.
Lemma lem3560513 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3560514 {_91206 : Type'} (x : _91206) (y : _91206) : (term275 _91206 x y) = (x = y).
Proof. exact (@lem3560513 (x = y)). Qed.
Lemma lem3560515 {_91201 _91206 : Type'} (P : _91206 -> Prop) (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term132 _91201 _91206 P f x y) (h2 : (f x) = (f y)) : x = y.
Proof. exact (EQ_MP (@lem3560514 _91206 x y) (@lem3560511 _91201 _91206 P x f y h1 h2)). Qed.
Lemma lem3560518 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3560520 {_91206 : Type'} (x : _91206) (y : _91206) : (term217 _91206 x y) = (term276 _91206 x y).
Proof. exact (@lem3560518 (x = y)). Qed.
Lemma lem3560523 {_91206 : Type'} (x : _91206) (y : _91206) (h1 : term217 _91206 x y) : term276 _91206 x y.
Proof. exact (EQ_MP (@lem3560520 _91206 x y) (@lem3559983 _91206 x y h1)). Qed.
Lemma lem3560526 {_91201 _91206 : Type'} (P : _91206 -> Prop) (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term217 _91206 x y) (h2 : term132 _91201 _91206 P f x y) (h3 : (f x) = (f y)) : False.
Proof. exact (@lem3560523 _91206 x y h1 (@lem3560515 _91201 _91206 P x f y h2 h3)). Qed.
Lemma lem3560527 {_91201 _91206 : Type'} (P : _91206 -> Prop) (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term217 _91206 x y) (h2 : term132 _91201 _91206 P f x y) (h3 : (f x) = (f y)) : term250.
Proof. exact (fun h0 : ~ False => @lem3560526 _91201 _91206 P x f y h1 h2 h3). Qed.
Lemma lem3560529 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3560530 : term250 = False.
Proof. exact (@lem3560529 False). Qed.
Lemma lem3560531 {_91201 _91206 : Type'} (P : _91206 -> Prop) (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term217 _91206 x y) (h2 : term132 _91201 _91206 P f x y) (h3 : (f x) = (f y)) : False.
Proof. exact (EQ_MP (@lem3560530) (@lem3560527 _91201 _91206 P x f y h1 h2 h3)). Qed.
Lemma lem3560557 {_91206 : Type'} (x : _91206) : x = x.
Proof. exact (@lem21386 _91206 x). Qed.
Lemma lem3560558 {_91206 : Type'} (x : _91206) : x = x.
Proof. exact (@lem3560557 _91206 x). Qed.
Lemma lem3560559 {_91206 : Type'} (y : _91206) : y = y.
Proof. exact (@lem3560558 _91206 y). Qed.
Lemma lem3560560 {_91206 : Type'} (y : _91206) : term277 _91206 y.
Proof. exact (fun h0 : term244 _91206 y => @lem3560559 _91206 y). Qed.
Lemma lem3560562 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3560563 {_91206 : Type'} (y : _91206) : (term277 _91206 y) = (y = y).
Proof. exact (@lem3560562 (y = y)). Qed.
Lemma lem3560564 {_91206 : Type'} (y : _91206) : y = y.
Proof. exact (EQ_MP (@lem3560563 _91206 y) (@lem3560560 _91206 y)). Qed.
Lemma lem3560567 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3560569 {_91206 : Type'} (y : _91206) : (term244 _91206 y) = (term278 _91206 y).
Proof. exact (@lem3560567 (y = y)). Qed.
Lemma lem3560572 {_91206 : Type'} (x : _91206) (y : _91206) (h1 : term217 _91206 x y) (h2 : x = y) : term278 _91206 y.
Proof. exact (EQ_MP (@lem3560569 _91206 y) (@lem3560187 _91206 x y h1 h2)). Qed.
Lemma lem3560575 {_91206 : Type'} (x : _91206) (y : _91206) (h1 : term217 _91206 x y) (h2 : x = y) : False.
Proof. exact (@lem3560572 _91206 x y h1 h2 (@lem3560564 _91206 y)). Qed.
Lemma lem3560576 {_91206 : Type'} (x : _91206) (y : _91206) (h1 : term217 _91206 x y) (h2 : x = y) : term250.
Proof. exact (fun h0 : ~ False => @lem3560575 _91206 x y h1 h2). Qed.
Lemma lem3560578 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3560579 : term250 = False.
Proof. exact (@lem3560578 False). Qed.
Lemma lem3560606 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : P x.
Proof. exact (proj1 (@lem3559635 _91201 _91206 x y P f h1)). Qed.
Lemma lem3560607 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : term253 _91206 P x.
Proof. exact (fun h0 : term231 _91206 P x => @lem3560606 _91201 _91206 x y P f h1). Qed.
Lemma lem3560609 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3560610 {_91206 : Type'} (P : _91206 -> Prop) (x : _91206) : (term253 _91206 P x) = (P x).
Proof. exact (@lem3560609 (P x)). Qed.
Lemma lem3560611 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : P x.
Proof. exact (EQ_MP (@lem3560610 _91206 P x) (@lem3560607 _91201 _91206 x y P f h1)). Qed.
Lemma lem3560613 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : P y.
Proof. exact (proj1 (@lem3559636 _91201 _91206 x y P f h1)). Qed.
Lemma lem3560614 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : term253 _91206 P y.
Proof. exact (fun h0 : term231 _91206 P y => @lem3560613 _91201 _91206 x y P f h1). Qed.
Lemma lem3560616 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3560617 {_91206 : Type'} (P : _91206 -> Prop) (y : _91206) : (term253 _91206 P y) = (P y).
Proof. exact (@lem3560616 (P y)). Qed.
Lemma lem3560618 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : P y.
Proof. exact (EQ_MP (@lem3560617 _91206 P y) (@lem3560614 _91201 _91206 x y P f h1)). Qed.
Lemma lem3560620 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : (f x) = (f y).
Proof. exact (proj2 (@lem3559636 _91201 _91206 x y P f h1)). Qed.
Lemma lem3560621 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : term247 _91201 _91206 x f y.
Proof. exact (fun h0 : term216 _91201 _91206 x f y => @lem3560620 _91201 _91206 x y P f h1). Qed.
Lemma lem3560623 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3560624 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) : (term247 _91201 _91206 x f y) = ((f x) = (f y)).
Proof. exact (@lem3560623 ((f x) = (f y))). Qed.
Lemma lem3560625 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : (f x) = (f y).
Proof. exact (EQ_MP (@lem3560624 _91201 _91206 x f y) (@lem3560621 _91201 _91206 x y P f h1)). Qed.
Lemma lem3560651 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3560652 {_91201 _91206 : Type'} (_38150 : _91206) (f : _91206 -> _91201) (_38151 : _91206) : (term220 _91201 _91206 f _38150 _38151) = (term254 _91201 _91206 _38150 f _38151).
Proof. exact (@lem3560651 (_38150 = _38151) (term216 _91201 _91206 _38150 f _38151)). Qed.
Lemma lem3560662 {_91206 : Type'} (P : _91206 -> Prop) (_38151 : _91206) : (term34 _91206 P _38151) = (term34 _91206 P _38151).
Proof. exact (eq_refl (term34 _91206 P _38151)). Qed.
Lemma lem3560663 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38150 : _91206) (f : _91206 -> _91201) (_38151 : _91206) : (term233 _91201 _91206 P f _38150 _38151) = (term255 _91201 _91206 P _38150 f _38151).
Proof. exact (MK_COMB (@lem3560662 _91206 P _38151) (@lem3560652 _91201 _91206 _38150 f _38151)). Qed.
Lemma lem3560667 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3560668 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38150 : _91206) (f : _91206 -> _91201) (_38151 : _91206) : (term255 _91201 _91206 P _38150 f _38151) = (term256 _91201 _91206 P _38150 f _38151).
Proof. exact (@lem3560667 (_38150 = _38151) (term231 _91206 P _38151) (term216 _91201 _91206 _38150 f _38151)). Qed.
Lemma lem3560688 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38150 : _91206) (f : _91206 -> _91201) (_38151 : _91206) : (term233 _91201 _91206 P f _38150 _38151) = (term256 _91201 _91206 P _38150 f _38151).
Proof. exact (TRANS (@lem3560663 _91201 _91206 P _38150 f _38151) (@lem3560668 _91201 _91206 P _38150 f _38151)). Qed.
Lemma lem3560689 {_91206 : Type'} (P : _91206 -> Prop) (_38150 : _91206) : (term34 _91206 P _38150) = (term34 _91206 P _38150).
Proof. exact (eq_refl (term34 _91206 P _38150)). Qed.
Lemma lem3560690 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38150 : _91206) (f : _91206 -> _91201) (_38151 : _91206) : (term234 _91201 _91206 P f _38150 _38151) = (term257 _91201 _91206 P _38150 f _38151).
Proof. exact (MK_COMB (@lem3560689 _91206 P _38150) (@lem3560688 _91201 _91206 P _38150 f _38151)). Qed.
Lemma lem3560694 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3560695 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38150 : _91206) (f : _91206 -> _91201) (_38151 : _91206) : (term257 _91201 _91206 P _38150 f _38151) = (term258 _91201 _91206 P _38150 f _38151).
Proof. exact (@lem3560694 (_38150 = _38151) (term231 _91206 P _38150) (term33 _91201 _91206 P _38150 f _38151)). Qed.
Lemma lem3560725 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38150 : _91206) (f : _91206 -> _91201) (_38151 : _91206) : (term234 _91201 _91206 P f _38150 _38151) = (term258 _91201 _91206 P _38150 f _38151).
Proof. exact (TRANS (@lem3560690 _91201 _91206 P _38150 f _38151) (@lem3560695 _91201 _91206 P _38150 f _38151)). Qed.
Lemma lem3560726 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3560727 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38150 : _91206) (f : _91206 -> _91201) (_38151 : _91206) : (term259 _91201 _91206 P f _38150 _38151) = (term260 _91201 _91206 P _38150 f _38151).
Proof. exact (MK_COMB (@lem3560726) (@lem3560725 _91201 _91206 P _38150 f _38151)). Qed.
Lemma lem3560757 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38150 : _91206) (f : _91206 -> _91201) (_38151 : _91206) : (term258 _91201 _91206 P _38150 f _38151) = (term258 _91201 _91206 P _38150 f _38151).
Proof. exact (eq_refl (term258 _91201 _91206 P _38150 f _38151)). Qed.
Lemma lem3560758 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38150 : _91206) (f : _91206 -> _91201) (_38151 : _91206) : ((term234 _91201 _91206 P f _38150 _38151) = (term258 _91201 _91206 P _38150 f _38151)) = ((term258 _91201 _91206 P _38150 f _38151) = (term258 _91201 _91206 P _38150 f _38151)).
Proof. exact (MK_COMB (@lem3560727 _91201 _91206 P _38150 f _38151) (@lem3560757 _91201 _91206 P _38150 f _38151)). Qed.
Lemma lem3560760 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3560761 (x : Prop) : (x = x) = True.
Proof. exact (@lem3560760 Prop x). Qed.
Lemma lem3560762 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38150 : _91206) (f : _91206 -> _91201) (_38151 : _91206) : ((term258 _91201 _91206 P _38150 f _38151) = (term258 _91201 _91206 P _38150 f _38151)) = True.
Proof. exact (@lem3560761 (term258 _91201 _91206 P _38150 f _38151)). Qed.
Lemma lem3560763 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38150 : _91206) (f : _91206 -> _91201) (_38151 : _91206) : ((term234 _91201 _91206 P f _38150 _38151) = (term258 _91201 _91206 P _38150 f _38151)) = True.
Proof. exact (TRANS (@lem3560758 _91201 _91206 P _38150 f _38151) (@lem3560762 _91201 _91206 P _38150 f _38151)). Qed.
Lemma lem3560764 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38150 : _91206) (f : _91206 -> _91201) (_38151 : _91206) : True = ((term234 _91201 _91206 P f _38150 _38151) = (term258 _91201 _91206 P _38150 f _38151)).
Proof. exact (SYM (@lem3560763 _91201 _91206 P _38150 f _38151)). Qed.
Lemma lem3560765 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38150 : _91206) (f : _91206 -> _91201) (_38151 : _91206) : (term234 _91201 _91206 P f _38150 _38151) = (term258 _91201 _91206 P _38150 f _38151).
Proof. exact (EQ_MP (@lem3560764 _91201 _91206 P _38150 f _38151) (@lem0)). Qed.
Lemma lem3560766 {_91201 _91206 : Type'} (_38150 : _91206) (_38151 : _91206) (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : term258 _91201 _91206 P _38150 f _38151.
Proof. exact (EQ_MP (@lem3560765 _91201 _91206 P _38150 f _38151) (@lem3560051 _91201 _91206 _38150 _38151 x y P f h1)). Qed.
Lemma lem3560768 (b : Prop) (a : Prop) : (a \/ b) = (term261 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3560769 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (_38150 : _91206) (_38151 : _91206) : (term258 _91201 _91206 P _38150 f _38151) = (term262 _91201 _91206 P f _38150 _38151).
Proof. exact (@lem3560768 (term36 _91201 _91206 P _38150 f _38151) (_38150 = _38151)). Qed.
Lemma lem3560771 (a : Prop) (b : Prop) : (term263 a b) = (term264 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3560772 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38150 : _91206) (f : _91206 -> _91201) (_38151 : _91206) : (term265 _91201 _91206 P _38150 f _38151) = (term266 _91201 _91206 P _38150 f _38151).
Proof. exact (@lem3560771 (term231 _91206 P _38150) (term33 _91201 _91206 P _38150 f _38151)). Qed.
Lemma lem3560774 (a : Prop) : (term15 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3560775 {_91206 : Type'} (P : _91206 -> Prop) (_38150 : _91206) : (term267 _91206 P _38150) = (P _38150).
Proof. exact (@lem3560774 (P _38150)). Qed.
Lemma lem3560776 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3560777 {_91206 : Type'} (P : _91206 -> Prop) (_38150 : _91206) : (term268 _91206 P _38150) = (term269 _91206 P _38150).
Proof. exact (MK_COMB (@lem3560776) (@lem3560775 _91206 P _38150)). Qed.
Lemma lem3560779 (a : Prop) (b : Prop) : (term263 a b) = (term264 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3560780 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38150 : _91206) (f : _91206 -> _91201) (_38151 : _91206) : (term270 _91201 _91206 P _38150 f _38151) = (term271 _91201 _91206 P _38150 f _38151).
Proof. exact (@lem3560779 (term231 _91206 P _38151) (term216 _91201 _91206 _38150 f _38151)). Qed.
Lemma lem3560782 (a : Prop) : (term15 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3560783 {_91206 : Type'} (P : _91206 -> Prop) (_38151 : _91206) : (term267 _91206 P _38151) = (P _38151).
Proof. exact (@lem3560782 (P _38151)). Qed.
Lemma lem3560784 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3560785 {_91206 : Type'} (P : _91206 -> Prop) (_38151 : _91206) : (term268 _91206 P _38151) = (term269 _91206 P _38151).
Proof. exact (MK_COMB (@lem3560784) (@lem3560783 _91206 P _38151)). Qed.
Lemma lem3560787 (a : Prop) : (term15 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3560788 {_91201 _91206 : Type'} (_38150 : _91206) (f : _91206 -> _91201) (_38151 : _91206) : (term272 _91201 _91206 _38150 f _38151) = ((f _38150) = (f _38151)).
Proof. exact (@lem3560787 ((f _38150) = (f _38151))). Qed.
Lemma lem3560789 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38150 : _91206) (f : _91206 -> _91201) (_38151 : _91206) : (term271 _91201 _91206 P _38150 f _38151) = (term38 _91201 _91206 P _38150 f _38151).
Proof. exact (MK_COMB (@lem3560785 _91206 P _38151) (@lem3560788 _91201 _91206 _38150 f _38151)). Qed.
Lemma lem3560790 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38150 : _91206) (f : _91206 -> _91201) (_38151 : _91206) : (term270 _91201 _91206 P _38150 f _38151) = (term38 _91201 _91206 P _38150 f _38151).
Proof. exact (TRANS (@lem3560780 _91201 _91206 P _38150 f _38151) (@lem3560789 _91201 _91206 P _38150 f _38151)). Qed.
Lemma lem3560791 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38150 : _91206) (f : _91206 -> _91201) (_38151 : _91206) : (term266 _91201 _91206 P _38150 f _38151) = (term41 _91201 _91206 P _38150 f _38151).
Proof. exact (MK_COMB (@lem3560777 _91206 P _38150) (@lem3560790 _91201 _91206 P _38150 f _38151)). Qed.
Lemma lem3560792 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38150 : _91206) (f : _91206 -> _91201) (_38151 : _91206) : (term265 _91201 _91206 P _38150 f _38151) = (term41 _91201 _91206 P _38150 f _38151).
Proof. exact (TRANS (@lem3560772 _91201 _91206 P _38150 f _38151) (@lem3560791 _91201 _91206 P _38150 f _38151)). Qed.
Lemma lem3560793 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3560794 {_91201 _91206 : Type'} (P : _91206 -> Prop) (_38150 : _91206) (f : _91206 -> _91201) (_38151 : _91206) : (term273 _91201 _91206 P _38150 f _38151) = (term274 _91201 _91206 P _38150 f _38151).
Proof. exact (MK_COMB (@lem3560793) (@lem3560792 _91201 _91206 P _38150 f _38151)). Qed.
Lemma lem3560795 {_91206 : Type'} (_38150 : _91206) (_38151 : _91206) : (_38150 = _38151) = (_38150 = _38151).
Proof. exact (eq_refl (_38150 = _38151)). Qed.
Lemma lem3560796 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (_38150 : _91206) (_38151 : _91206) : (term262 _91201 _91206 P f _38150 _38151) = (term21 _91201 _91206 P f _38150 _38151).
Proof. exact (MK_COMB (@lem3560794 _91201 _91206 P _38150 f _38151) (@lem3560795 _91206 _38150 _38151)). Qed.
Lemma lem3560797 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (_38150 : _91206) (_38151 : _91206) : (term258 _91201 _91206 P _38150 f _38151) = (term21 _91201 _91206 P f _38150 _38151).
Proof. exact (TRANS (@lem3560769 _91201 _91206 P f _38150 _38151) (@lem3560796 _91201 _91206 P f _38150 _38151)). Qed.
Lemma lem3560799 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : term38 _91201 _91206 P x f y.
Proof. exact (conj (@lem3560618 _91201 _91206 x y P f h1) (@lem3560625 _91201 _91206 x y P f h1)). Qed.
Lemma lem3560800 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : term41 _91201 _91206 P x f y.
Proof. exact (conj (@lem3560611 _91201 _91206 x y P f h1) (@lem3560799 _91201 _91206 x y P f h1)). Qed.
Lemma lem3560802 {_91201 _91206 : Type'} (_38150 : _91206) (_38151 : _91206) (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : term21 _91201 _91206 P f _38150 _38151.
Proof. exact (EQ_MP (@lem3560797 _91201 _91206 P f _38150 _38151) (@lem3560766 _91201 _91206 _38150 _38151 x y P f h1)). Qed.
Lemma lem3560803 {_91201 _91206 : Type'} (_38150 : _91206) (_38151 : _91206) (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : term21 _91201 _91206 P f _38150 _38151.
Proof. exact (@lem3560802 _91201 _91206 _38150 _38151 x y P f h1). Qed.
Lemma lem3560804 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : term21 _91201 _91206 P f x y.
Proof. exact (@lem3560803 _91201 _91206 x y x y P f h1). Qed.
Lemma lem3560807 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : x = y.
Proof. exact (@lem3560804 _91201 _91206 x y P f h1 (@lem3560800 _91201 _91206 x y P f h1)). Qed.
Lemma lem3560808 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : term275 _91206 x y.
Proof. exact (fun h0 : term217 _91206 x y => @lem3560807 _91201 _91206 x y P f h1). Qed.
Lemma lem3560810 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3560811 {_91206 : Type'} (x : _91206) (y : _91206) : (term275 _91206 x y) = (x = y).
Proof. exact (@lem3560810 (x = y)). Qed.
Lemma lem3560812 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : x = y.
Proof. exact (EQ_MP (@lem3560811 _91206 x y) (@lem3560808 _91201 _91206 x y P f h1)). Qed.
Lemma lem3560815 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3560817 {_91206 : Type'} (x : _91206) (y : _91206) : (term217 _91206 x y) = (term276 _91206 x y).
Proof. exact (@lem3560815 (x = y)). Qed.
Lemma lem3560820 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : term276 _91206 x y.
Proof. exact (EQ_MP (@lem3560817 _91206 x y) (@lem3560013 _91201 _91206 x y P f h1)). Qed.
Lemma lem3560823 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : False.
Proof. exact (@lem3560820 _91201 _91206 x y P f h1 (@lem3560812 _91201 _91206 x y P f h1)). Qed.
Lemma lem3560824 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : term250.
Proof. exact (fun h0 : ~ False => @lem3560823 _91201 _91206 x y P f h1). Qed.
Lemma lem3560826 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3560827 : term250 = False.
Proof. exact (@lem3560826 False). Qed.
Lemma lem3560828 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term167 _91201 _91206 x y P f) : False.
Proof. exact (EQ_MP (@lem3560827) (@lem3560824 _91201 _91206 x y P f h1)). Qed.
Lemma lem3560829 {_91206 : Type'} (x : _91206) (y : _91206) (h1 : term217 _91206 x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem3560579) (@lem3560576 _91206 x y h1 h2)). Qed.
Lemma lem3560830 {_91201 _91206 : Type'} (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem3560282) (@lem3560279 _91201 _91206 f x y h1 h2)). Qed.
Lemma lem3560831 {_91206 : Type'} (x : _91206) (y : _91206) (h1 : term217 _91206 x y) (h2 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h3 : x = y => @lem3560829 _91206 x y h1 h2) (fun h3 : False => @lem3560011 _91206 x y h2)). Qed.
Lemma lem3560832 {_91206 : Type'} (x : _91206) (y : _91206) (h1 : term217 _91206 x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem3560831 _91206 x y h1 h2) (@lem3560011 _91206 x y h2)). Qed.
Lemma lem3560833 {_91206 : Type'} (x : _91206) (y : _91206) (h1 : term217 _91206 x y) (h2 : x = y) : (term217 _91206 x y) = False.
Proof. exact (prop_ext (fun h3 : term217 _91206 x y => @lem3560832 _91206 x y h1 h2) (fun h3 : False => @lem3560009 _91206 x y h1)). Qed.
Lemma lem3560834 {_91206 : Type'} (x : _91206) (y : _91206) (h1 : term217 _91206 x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem3560833 _91206 x y h1 h2) (@lem3560009 _91206 x y h1)). Qed.
Lemma lem3560835 {_91201 _91206 : Type'} (P : _91206 -> Prop) (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term217 _91206 x y) (h2 : term132 _91201 _91206 P f x y) (h3 : (f x) = (f y)) : ((f x) = (f y)) = False.
Proof. exact (prop_ext (fun h4 : (f x) = (f y) => @lem3560531 _91201 _91206 P x f y h1 h2 h3) (fun h4 : False => @lem3559985 _91201 _91206 x f y h3)). Qed.
Lemma lem3560836 {_91201 _91206 : Type'} (P : _91206 -> Prop) (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term217 _91206 x y) (h2 : term132 _91201 _91206 P f x y) (h3 : (f x) = (f y)) : False.
Proof. exact (EQ_MP (@lem3560835 _91201 _91206 P x f y h1 h2 h3) (@lem3559985 _91201 _91206 x f y h3)). Qed.
Lemma lem3560837 {_91201 _91206 : Type'} (P : _91206 -> Prop) (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term217 _91206 x y) (h2 : term132 _91201 _91206 P f x y) (h3 : (f x) = (f y)) : (term217 _91206 x y) = False.
Proof. exact (prop_ext (fun h4 : term217 _91206 x y => @lem3560836 _91201 _91206 P x f y h1 h2 h3) (fun h4 : False => @lem3559983 _91206 x y h1)). Qed.
Lemma lem3560838 {_91201 _91206 : Type'} (P : _91206 -> Prop) (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term217 _91206 x y) (h2 : term132 _91201 _91206 P f x y) (h3 : (f x) = (f y)) : False.
Proof. exact (EQ_MP (@lem3560837 _91201 _91206 P x f y h1 h2 h3) (@lem3559983 _91206 x y h1)). Qed.
Lemma lem3560839 {_91201 _91206 : Type'} (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h3 : x = y => @lem3560830 _91201 _91206 f x y h1 h2) (fun h3 : False => @lem3559959 _91206 x y h2)). Qed.
Lemma lem3560840 {_91201 _91206 : Type'} (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem3560839 _91201 _91206 f x y h1 h2) (@lem3559959 _91206 x y h2)). Qed.
Lemma lem3560841 {_91201 _91206 : Type'} (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : x = y) : (term216 _91201 _91206 x f y) = False.
Proof. exact (prop_ext (fun h3 : term216 _91201 _91206 x f y => @lem3560840 _91201 _91206 f x y h1 h2) (fun h3 : False => @lem3559957 _91201 _91206 x f y h1)). Qed.
Lemma lem3560842 {_91201 _91206 : Type'} (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem3560841 _91201 _91206 f x y h1 h2) (@lem3559957 _91201 _91206 x f y h1)). Qed.
Lemma lem3560843 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : (f x) = (f y)) : ((f x) = (f y)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (f y) => @lem3560234 _91201 _91206 x f y h1 h2) (fun h3 : False => @lem3559933 _91201 _91206 x f y h2)). Qed.
Lemma lem3560844 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : (f x) = (f y)) : False.
Proof. exact (EQ_MP (@lem3560843 _91201 _91206 x f y h1 h2) (@lem3559933 _91201 _91206 x f y h2)). Qed.
Lemma lem3560845 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : (f x) = (f y)) : (term216 _91201 _91206 x f y) = False.
Proof. exact (prop_ext (fun h3 : term216 _91201 _91206 x f y => @lem3560844 _91201 _91206 x f y h1 h2) (fun h3 : False => @lem3559931 _91201 _91206 x f y h1)). Qed.
Lemma lem3560846 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : (f x) = (f y)) : False.
Proof. exact (EQ_MP (@lem3560845 _91201 _91206 x f y h1 h2) (@lem3559931 _91201 _91206 x f y h1)). Qed.
Lemma lem3560847 {_91206 : Type'} (x : _91206) (y : _91206) (h1 : term217 _91206 x y) (h2 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h3 : x = y => @lem3560834 _91206 x y h1 h2) (fun h3 : False => @lem3559815 _91206 x y h2)). Qed.
Lemma lem3560848 {_91206 : Type'} (x : _91206) (y : _91206) (h1 : term217 _91206 x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem3560847 _91206 x y h1 h2) (@lem3559815 _91206 x y h2)). Qed.
Lemma lem3560849 {_91206 : Type'} (x : _91206) (y : _91206) (h1 : term217 _91206 x y) (h2 : x = y) : (term217 _91206 x y) = False.
Proof. exact (prop_ext (fun h3 : term217 _91206 x y => @lem3560848 _91206 x y h1 h2) (fun h3 : False => @lem3559811 _91206 x y h1)). Qed.
Lemma lem3560850 {_91206 : Type'} (x : _91206) (y : _91206) (h1 : term217 _91206 x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem3560849 _91206 x y h1 h2) (@lem3559811 _91206 x y h1)). Qed.
Lemma lem3560851 {_91201 _91206 : Type'} (P : _91206 -> Prop) (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term217 _91206 x y) (h2 : term132 _91201 _91206 P f x y) (h3 : (f x) = (f y)) : ((f x) = (f y)) = False.
Proof. exact (prop_ext (fun h4 : (f x) = (f y) => @lem3560838 _91201 _91206 P x f y h1 h2 h3) (fun h4 : False => @lem3559771 _91201 _91206 x f y h3)). Qed.
Lemma lem3560852 {_91201 _91206 : Type'} (P : _91206 -> Prop) (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term217 _91206 x y) (h2 : term132 _91201 _91206 P f x y) (h3 : (f x) = (f y)) : False.
Proof. exact (EQ_MP (@lem3560851 _91201 _91206 P x f y h1 h2 h3) (@lem3559771 _91201 _91206 x f y h3)). Qed.
Lemma lem3560853 {_91201 _91206 : Type'} (P : _91206 -> Prop) (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term217 _91206 x y) (h2 : term132 _91201 _91206 P f x y) (h3 : (f x) = (f y)) : (term217 _91206 x y) = False.
Proof. exact (prop_ext (fun h4 : term217 _91206 x y => @lem3560852 _91201 _91206 P x f y h1 h2 h3) (fun h4 : False => @lem3559767 _91206 x y h1)). Qed.
Lemma lem3560854 {_91201 _91206 : Type'} (P : _91206 -> Prop) (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term217 _91206 x y) (h2 : term132 _91201 _91206 P f x y) (h3 : (f x) = (f y)) : False.
Proof. exact (EQ_MP (@lem3560853 _91201 _91206 P x f y h1 h2 h3) (@lem3559767 _91206 x y h1)). Qed.
Lemma lem3560855 {_91201 _91206 : Type'} (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h3 : x = y => @lem3560842 _91201 _91206 f x y h1 h2) (fun h3 : False => @lem3559727 _91206 x y h2)). Qed.
Lemma lem3560856 {_91201 _91206 : Type'} (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem3560855 _91201 _91206 f x y h1 h2) (@lem3559727 _91206 x y h2)). Qed.
Lemma lem3560857 {_91201 _91206 : Type'} (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : x = y) : (term216 _91201 _91206 x f y) = False.
Proof. exact (prop_ext (fun h3 : term216 _91201 _91206 x f y => @lem3560856 _91201 _91206 f x y h1 h2) (fun h3 : False => @lem3559723 _91201 _91206 x f y h1)). Qed.
Lemma lem3560858 {_91201 _91206 : Type'} (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem3560857 _91201 _91206 f x y h1 h2) (@lem3559723 _91201 _91206 x f y h1)). Qed.
Lemma lem3560859 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : (f x) = (f y)) : ((f x) = (f y)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (f y) => @lem3560846 _91201 _91206 x f y h1 h2) (fun h3 : False => @lem3559683 _91201 _91206 x f y h2)). Qed.
Lemma lem3560860 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : (f x) = (f y)) : False.
Proof. exact (EQ_MP (@lem3560859 _91201 _91206 x f y h1 h2) (@lem3559683 _91201 _91206 x f y h2)). Qed.
Lemma lem3560861 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : (f x) = (f y)) : (term216 _91201 _91206 x f y) = False.
Proof. exact (prop_ext (fun h3 : term216 _91201 _91206 x f y => @lem3560860 _91201 _91206 x f y h1 h2) (fun h3 : False => @lem3559679 _91201 _91206 x f y h1)). Qed.
Lemma lem3560862 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : (f x) = (f y)) : False.
Proof. exact (EQ_MP (@lem3560861 _91201 _91206 x f y h1 h2) (@lem3559679 _91201 _91206 x f y h1)). Qed.
Lemma lem3560863 {_91206 : Type'} (x : _91206) (y : _91206) (h1 : term217 _91206 x y) (h2 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h3 : x = y => @lem3560850 _91206 x y h1 h2) (fun h3 : False => @lem3559815 _91206 x y h2)). Qed.
Lemma lem3560864 {_91206 : Type'} (x : _91206) (y : _91206) (h1 : term217 _91206 x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem3560863 _91206 x y h1 h2) (@lem3559815 _91206 x y h2)). Qed.
Lemma lem3560865 {_91206 : Type'} (x : _91206) (y : _91206) (h1 : term217 _91206 x y) (h2 : x = y) : (term217 _91206 x y) = False.
Proof. exact (prop_ext (fun h3 : term217 _91206 x y => @lem3560864 _91206 x y h1 h2) (fun h3 : False => @lem3559811 _91206 x y h1)). Qed.
Lemma lem3560866 {_91206 : Type'} (x : _91206) (y : _91206) (h1 : term217 _91206 x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem3560865 _91206 x y h1 h2) (@lem3559811 _91206 x y h1)). Qed.
Lemma lem3560867 {_91201 _91206 : Type'} (P : _91206 -> Prop) (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term217 _91206 x y) (h2 : term132 _91201 _91206 P f x y) (h3 : (f x) = (f y)) : ((f x) = (f y)) = False.
Proof. exact (prop_ext (fun h4 : (f x) = (f y) => @lem3560854 _91201 _91206 P x f y h1 h2 h3) (fun h4 : False => @lem3559771 _91201 _91206 x f y h3)). Qed.
Lemma lem3560868 {_91201 _91206 : Type'} (P : _91206 -> Prop) (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term217 _91206 x y) (h2 : term132 _91201 _91206 P f x y) (h3 : (f x) = (f y)) : False.
Proof. exact (EQ_MP (@lem3560867 _91201 _91206 P x f y h1 h2 h3) (@lem3559771 _91201 _91206 x f y h3)). Qed.
Lemma lem3560869 {_91201 _91206 : Type'} (P : _91206 -> Prop) (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term217 _91206 x y) (h2 : term132 _91201 _91206 P f x y) (h3 : (f x) = (f y)) : (term217 _91206 x y) = False.
Proof. exact (prop_ext (fun h4 : term217 _91206 x y => @lem3560868 _91201 _91206 P x f y h1 h2 h3) (fun h4 : False => @lem3559767 _91206 x y h1)). Qed.
Lemma lem3560870 {_91201 _91206 : Type'} (P : _91206 -> Prop) (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term217 _91206 x y) (h2 : term132 _91201 _91206 P f x y) (h3 : (f x) = (f y)) : False.
Proof. exact (EQ_MP (@lem3560869 _91201 _91206 P x f y h1 h2 h3) (@lem3559767 _91206 x y h1)). Qed.
Lemma lem3560871 {_91201 _91206 : Type'} (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h3 : x = y => @lem3560858 _91201 _91206 f x y h1 h2) (fun h3 : False => @lem3559727 _91206 x y h2)). Qed.
Lemma lem3560872 {_91201 _91206 : Type'} (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem3560871 _91201 _91206 f x y h1 h2) (@lem3559727 _91206 x y h2)). Qed.
Lemma lem3560873 {_91201 _91206 : Type'} (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : x = y) : (term216 _91201 _91206 x f y) = False.
Proof. exact (prop_ext (fun h3 : term216 _91201 _91206 x f y => @lem3560872 _91201 _91206 f x y h1 h2) (fun h3 : False => @lem3559723 _91201 _91206 x f y h1)). Qed.
Lemma lem3560874 {_91201 _91206 : Type'} (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem3560873 _91201 _91206 f x y h1 h2) (@lem3559723 _91201 _91206 x f y h1)). Qed.
Lemma lem3560875 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : (f x) = (f y)) : ((f x) = (f y)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (f y) => @lem3560862 _91201 _91206 x f y h1 h2) (fun h3 : False => @lem3559683 _91201 _91206 x f y h2)). Qed.
Lemma lem3560876 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : (f x) = (f y)) : False.
Proof. exact (EQ_MP (@lem3560875 _91201 _91206 x f y h1 h2) (@lem3559683 _91201 _91206 x f y h2)). Qed.
Lemma lem3560877 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : (f x) = (f y)) : (term216 _91201 _91206 x f y) = False.
Proof. exact (prop_ext (fun h3 : term216 _91201 _91206 x f y => @lem3560876 _91201 _91206 x f y h1 h2) (fun h3 : False => @lem3559679 _91201 _91206 x f y h1)). Qed.
Lemma lem3560878 {_91201 _91206 : Type'} (x : _91206) (f : _91206 -> _91201) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : (f x) = (f y)) : False.
Proof. exact (EQ_MP (@lem3560877 _91201 _91206 x f y h1 h2) (@lem3559679 _91201 _91206 x f y h1)). Qed.
Lemma lem3560879 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term217 _91206 x y) (h2 : term132 _91201 _91206 P f x y) : False.
Proof. exact (or_elim (@lem3559623 _91201 _91206 P f x y h2) (fun h0 : (f x) = (f y) => @lem3560870 _91201 _91206 P x f y h1 h2 h0) (fun h0 : x = y => @lem3560866 _91206 x y h1 h0)). Qed.
Lemma lem3560880 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term216 _91201 _91206 x f y) (h2 : term132 _91201 _91206 P f x y) : False.
Proof. exact (or_elim (@lem3559623 _91201 _91206 P f x y h2) (fun h0 : (f x) = (f y) => @lem3560878 _91201 _91206 x f y h1 h0) (fun h0 : x = y => @lem3560874 _91201 _91206 f x y h1 h0)). Qed.
Lemma lem3560881 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (x : _91206) (y : _91206) (h1 : term132 _91201 _91206 P f x y) : False.
Proof. exact (or_elim (@lem3559622 _91201 _91206 P f x y h1) (fun h0 : term216 _91201 _91206 x f y => @lem3560880 _91201 _91206 P f x y h0 h1) (fun h0 : term217 _91206 x y => @lem3560879 _91201 _91206 P f x y h0 h1)). Qed.
Lemma lem3560882 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term208 _91201 _91206 x y P f) : False.
Proof. exact (or_elim (@lem3559615 _91201 _91206 x y P f h1) (fun h0 : term132 _91201 _91206 P f x y => @lem3560881 _91201 _91206 P f x y h0) (fun h0 : term167 _91201 _91206 x y P f => @lem3560828 _91201 _91206 x y P f h0)). Qed.
Lemma lem3560883 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term208 _91201 _91206 x y P f) : (term208 _91201 _91206 x y P f) = False.
Proof. exact (prop_ext (fun h2 : term208 _91201 _91206 x y P f => @lem3560882 _91201 _91206 x y P f h1) (fun h2 : False => @lem3559615 _91201 _91206 x y P f h1)). Qed.
Lemma lem3560884 {_91201 _91206 : Type'} (x : _91206) (y : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term208 _91201 _91206 x y P f) : False.
Proof. exact (EQ_MP (@lem3560883 _91201 _91206 x y P f h1) (@lem3559615 _91201 _91206 x y P f h1)). Qed.
Lemma lem3560885 {_91201 _91206 : Type'} (x : _91206) (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term211 _91201 _91206 x P f) : False.
Proof. exact (ex_elim (@lem3559416 _91201 _91206 x P f h1) (fun y : _91206 => fun h0 : term210 _91201 _91206 x P f y => @lem3560884 _91201 _91206 x y P f h0)). Qed.
Lemma lem3560886 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term31 _91201 _91206 P f) : False.
Proof. exact (ex_elim (@lem3559415 _91201 _91206 P f h1) (fun x : _91206 => fun h0 : term212 _91201 _91206 P f x => @lem3560885 _91201 _91206 x P f h0)). Qed.
Lemma lem3560887 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term31 _91201 _91206 P f) : (term31 _91201 _91206 P f) = False.
Proof. exact (prop_ext (fun h2 : term31 _91201 _91206 P f => @lem3560886 _91201 _91206 P f h1) (fun h2 : False => @lem3558900 _91201 _91206 P f h1)). Qed.
Lemma lem3560888 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) (h1 : term31 _91201 _91206 P f) : False.
Proof. exact (EQ_MP (@lem3560887 _91201 _91206 P f h1) (@lem3558900 _91201 _91206 P f h1)). Qed.
Lemma lem3560889 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : term30 _91201 _91206 P f.
Proof. exact (fun h0 : term31 _91201 _91206 P f => @lem3560888 _91201 _91206 P f h0). Qed.
Lemma lem3560890 {_91201 _91206 : Type'} (P : _91206 -> Prop) (f : _91206 -> _91201) : (term25 _91201 _91206 P f) = (term20 _91201 _91206 P f).
Proof. exact (EQ_MP (@lem3558899 _91201 _91206 P f) (@lem3560889 _91201 _91206 P f)). Qed.
Lemma lem3560895 {_91201 _91206 : Type'} (P : _91206 -> Prop) : term28 _91201 _91206 P.
Proof. exact (fun f : _91206 -> _91201 => @lem3560890 _91201 _91206 P f). Qed.
Lemma lem3560900 {_91201 _91206 : Type'} : term8 _91201 _91206.
Proof. exact (fun P : _91206 -> Prop => @lem3560895 _91201 _91206 P). Qed.
Lemma lem3560901 {_91201 _91206 : Type'} : term9 _91201 _91206.
Proof. exact (EQ_MP (@lem3558895 _91201 _91206) (@lem3560900 _91201 _91206)). Qed.
Lemma lem3560903 {_91201 _91206 : Type'} : term9 _91201 _91206.
Proof. exact (@lem3558753 _91201 _91206 (@lem3560901 _91201 _91206)). Qed.
Lemma lem3560904 {_91201 _91206 : Type'} (h1 : term10 _91201 _91206) : False.
Proof. exact (@lem3560903 _91201 _91206 (@lem3558737 _91201 _91206 h1)). Qed.
Lemma lem3560905 {_91201 _91206 : Type'} (h1 : term10 _91201 _91206) : (term10 _91201 _91206) = False.
Proof. exact (prop_ext (fun h2 : term10 _91201 _91206 => @lem3560904 _91201 _91206 h1) (fun h2 : False => @lem3558737 _91201 _91206 h1)). Qed.
Lemma lem3560906 {_91201 _91206 : Type'} (h1 : term10 _91201 _91206) : False.
Proof. exact (EQ_MP (@lem3560905 _91201 _91206 h1) (@lem3558737 _91201 _91206 h1)). Qed.
Lemma lem3560907 {_91201 _91206 : Type'} : term9 _91201 _91206.
Proof. exact (fun h0 : term10 _91201 _91206 => @lem3560906 _91201 _91206 h0). Qed.
Lemma lem3560908 {_91201 _91206 : Type'} : term8 _91201 _91206.
Proof. exact (EQ_MP (@lem3558736 _91201 _91206) (@lem3560907 _91201 _91206)). Qed.
