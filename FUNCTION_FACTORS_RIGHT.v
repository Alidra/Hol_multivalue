Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FUNCTION_FACTORS_RIGHT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import FUN_EQ_THM_spec.
Require Import SKOLEM_THM_spec.
Require Import o_THM_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
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
Lemma lem3582891 {A B : Type'} (P : type1413 A B) (h1 : (term0 A B P) = (term1 A B P)) : (term0 A B P) = (term1 A B P).
Proof. exact (h1). Qed.
Lemma lem3582892 {A B : Type'} (P : type1413 A B) (h1 : (term0 A B P) = (term1 A B P)) : (term1 A B P) = (term0 A B P).
Proof. exact (SYM (@lem3582891 A B P h1)). Qed.
Lemma lem3582893 {A B : Type'} (P : type1413 A B) (h1 : (term1 A B P) = (term0 A B P)) : (term1 A B P) = (term0 A B P).
Proof. exact (h1). Qed.
Lemma lem3582894 {A B : Type'} (P : type1413 A B) (h1 : (term1 A B P) = (term0 A B P)) : (term0 A B P) = (term1 A B P).
Proof. exact (SYM (@lem3582893 A B P h1)). Qed.
Lemma lem3582895 {A B : Type'} (P : type1413 A B) : ((term0 A B P) = (term1 A B P)) = ((term1 A B P) = (term0 A B P)).
Proof. exact (prop_ext (fun h1 : (term0 A B P) = (term1 A B P) => @lem3582892 A B P h1) (fun h1 : (term1 A B P) = (term0 A B P) => @lem3582894 A B P h1)). Qed.
Lemma lem3582896 {A B : Type'} : (term2 A B) = (term3 A B).
Proof. exact (fun_ext (fun P : type1413 A B => @lem3582895 A B P)). Qed.
Lemma lem3582897 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem3582898 {A B : Type'} : (term4 A B) = (term5 A B).
Proof. exact (MK_COMB (@lem3582897 A B) (@lem3582896 A B)). Qed.
Lemma lem3582899 {A B : Type'} : term5 A B.
Proof. exact (EQ_MP (@lem3582898 A B) (@lem13546 A B)). Qed.
Lemma lem3582900 {A B : Type'} (P : type1413 A B) : term6 A B P.
Proof. exact (@lem3582899 A B P). Qed.
Lemma lem3582901 {A B : Type'} (P : type1413 A B) : (term6 A B P) = ((term1 A B P) = (term0 A B P)).
Proof. exact (eq_refl (term6 A B P)). Qed.
Lemma lem3582903 {A B C : Type'} (f : B -> C) : term7 A B C f.
Proof. exact (@lem15456 A B C f). Qed.
Lemma lem3582904 {A B C : Type'} (f : B -> C) : (term7 A B C f) = (term8 A B C f).
Proof. exact (eq_refl (term7 A B C f)). Qed.
Lemma lem3582905 {A B C : Type'} (f : B -> C) : term8 A B C f.
Proof. exact (EQ_MP (@lem3582904 A B C f) (@lem3582903 A B C f)). Qed.
Lemma lem3582906 {A B C : Type'} (f : B -> C) (g : A -> B) : term9 A B C f g.
Proof. exact (@lem3582905 A B C f g). Qed.
Lemma lem3582907 {A B C : Type'} (f : B -> C) (g : A -> B) : (term9 A B C f g) = (term10 A B C f g).
Proof. exact (eq_refl (term9 A B C f g)). Qed.
Lemma lem3582908 {A B C : Type'} (f : B -> C) (g : A -> B) : term10 A B C f g.
Proof. exact (EQ_MP (@lem3582907 A B C f g) (@lem3582906 A B C f g)). Qed.
Lemma lem3582909 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : term11 A B C f g x.
Proof. exact (@lem3582908 A B C f g x). Qed.
Lemma lem3582910 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (term11 A B C f g x) = ((@o A B C f g x) = (term12 A B C f g x)).
Proof. exact (eq_refl (term11 A B C f g x)). Qed.
Lemma lem3582912 {A B : Type'} (f : A -> B) : term13 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem3582913 {A B : Type'} (f : A -> B) : (term13 A B f) = (term14 A B f).
Proof. exact (eq_refl (term13 A B f)). Qed.
Lemma lem3582914 {A B : Type'} (f : A -> B) : term14 A B f.
Proof. exact (EQ_MP (@lem3582913 A B f) (@lem3582912 A B f)). Qed.
Lemma lem3582915 {A B : Type'} (f : A -> B) (g : A -> B) : term15 A B f g.
Proof. exact (@lem3582914 A B f g). Qed.
Lemma lem3582916 {A B : Type'} (f : A -> B) (g : A -> B) : (term15 A B f g) = ((f = g) = (term16 A B f g)).
Proof. exact (eq_refl (term15 A B f g)). Qed.
Lemma lem3582949 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term16 A B f g).
Proof. exact (EQ_MP (@lem3582916 A B f g) (@lem3582915 A B f g)). Qed.
Lemma lem3582950 {_91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91894 -> _91895) : (f = g) = (term16 _91894 _91895 f g).
Proof. exact (@lem3582949 _91894 _91895 f g). Qed.
Lemma lem3582951 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) : (f = (@o _91894 _91882 _91895 g h)) = (term17 _91882 _91894 _91895 f g h).
Proof. exact (@lem3582950 _91894 _91895 f (@o _91894 _91882 _91895 g h)). Qed.
Lemma lem3582961 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (@o A B C f g x) = (term12 A B C f g x).
Proof. exact (EQ_MP (@lem3582910 A B C f g x) (@lem3582909 A B C f g x)). Qed.
Lemma lem3582962 {_91882 _91894 _91895 : Type'} (f : _91882 -> _91895) (g : _91894 -> _91882) (x : _91894) : (@o _91894 _91882 _91895 f g x) = (term18 _91882 _91894 _91895 f g x).
Proof. exact (@lem3582961 _91894 _91882 _91895 f g x). Qed.
Lemma lem3582963 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (h : _91894 -> _91882) (x : _91894) : (@o _91894 _91882 _91895 g h x) = (term18 _91882 _91894 _91895 g h x).
Proof. exact (@lem3582962 _91882 _91894 _91895 g h x). Qed.
Lemma lem3582964 {_91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) : (term19 _91894 _91895 f x) = (term19 _91894 _91895 f x).
Proof. exact (eq_refl (term19 _91894 _91895 f x)). Qed.
Lemma lem3582965 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (x : _91894) : ((f x) = (@o _91894 _91882 _91895 g h x)) = ((f x) = (term18 _91882 _91894 _91895 g h x)).
Proof. exact (MK_COMB (@lem3582964 _91894 _91895 f x) (@lem3582963 _91882 _91894 _91895 g h x)). Qed.
Lemma lem3582970 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) : (term20 _91882 _91894 _91895 f g h) = (term21 _91882 _91894 _91895 f g h).
Proof. exact (fun_ext (fun x : _91894 => @lem3582965 _91882 _91894 _91895 f g h x)). Qed.
Lemma lem3582971 {_91894 : Type'} : (@all _91894) = (@all _91894).
Proof. exact (eq_refl (@all _91894)). Qed.
Lemma lem3582972 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) : (term17 _91882 _91894 _91895 f g h) = (term22 _91882 _91894 _91895 f g h).
Proof. exact (MK_COMB (@lem3582971 _91894) (@lem3582970 _91882 _91894 _91895 f g h)). Qed.
Lemma lem3582977 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) : (f = (@o _91894 _91882 _91895 g h)) = (term22 _91882 _91894 _91895 f g h).
Proof. exact (TRANS (@lem3582951 _91882 _91894 _91895 f g h) (@lem3582972 _91882 _91894 _91895 f g h)). Qed.
Lemma lem3582978 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term23 _91882 _91894 _91895 f g) = (term24 _91882 _91894 _91895 f g).
Proof. exact (fun_ext (fun h : _91894 -> _91882 => @lem3582977 _91882 _91894 _91895 f g h)). Qed.
Lemma lem3582979 {_91882 _91894 : Type'} : (@ex (_91894 -> _91882)) = (@ex (_91894 -> _91882)).
Proof. exact (eq_refl (@ex (_91894 -> _91882))). Qed.
Lemma lem3582980 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term25 _91882 _91894 _91895 f g) = (term26 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3582979 _91882 _91894) (@lem3582978 _91882 _91894 _91895 f g)). Qed.
Lemma lem3582982 {A B : Type'} (P : type1413 A B) : (term1 A B P) = (term0 A B P).
Proof. exact (EQ_MP (@lem3582901 A B P) (@lem3582900 A B P)). Qed.
Lemma lem3582983 {_91882 _91894 : Type'} (P : type1470 _91882 _91894) : (term27 _91882 _91894 P) = (term28 _91882 _91894 P).
Proof. exact (@lem3582982 _91894 _91882 P). Qed.
Lemma lem3582984 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term29 _91882 _91894 _91895 f g) = (term30 _91882 _91894 _91895 f g).
Proof. exact (@lem3582983 _91882 _91894 (term31 _91882 _91894 _91895 f g)). Qed.
Lemma lem3582985 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term32 _91882 _91894 _91895 f g x) = (term33 _91882 _91894 _91895 f x g).
Proof. exact (eq_refl (term32 _91882 _91894 _91895 f g x)). Qed.
Lemma lem3582986 {_91882 _91894 : Type'} (h : _91894 -> _91882) (x : _91894) : (h x) = (h x).
Proof. exact (eq_refl (h x)). Qed.
Lemma lem3582987 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (x : _91894) : (term34 _91882 _91894 _91895 f g h x) = (term35 _91882 _91894 _91895 f g h x).
Proof. exact (MK_COMB (@lem3582985 _91882 _91894 _91895 f x g) (@lem3582986 _91882 _91894 h x)). Qed.
Lemma lem3582988 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (x : _91894) : (term35 _91882 _91894 _91895 f g h x) = ((f x) = (term18 _91882 _91894 _91895 g h x)).
Proof. exact (eq_refl (term35 _91882 _91894 _91895 f g h x)). Qed.
Lemma lem3582989 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (x : _91894) : (term34 _91882 _91894 _91895 f g h x) = ((f x) = (term18 _91882 _91894 _91895 g h x)).
Proof. exact (TRANS (@lem3582987 _91882 _91894 _91895 f g h x) (@lem3582988 _91882 _91894 _91895 f g h x)). Qed.
Lemma lem3582990 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) : (term36 _91882 _91894 _91895 f g h) = (term21 _91882 _91894 _91895 f g h).
Proof. exact (fun_ext (fun x : _91894 => @lem3582989 _91882 _91894 _91895 f g h x)). Qed.
Lemma lem3582991 {_91894 : Type'} : (@all _91894) = (@all _91894).
Proof. exact (eq_refl (@all _91894)). Qed.
Lemma lem3582992 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) : (term37 _91882 _91894 _91895 f g h) = (term22 _91882 _91894 _91895 f g h).
Proof. exact (MK_COMB (@lem3582991 _91894) (@lem3582990 _91882 _91894 _91895 f g h)). Qed.
Lemma lem3582993 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term38 _91882 _91894 _91895 f g) = (term24 _91882 _91894 _91895 f g).
Proof. exact (fun_ext (fun h : _91894 -> _91882 => @lem3582992 _91882 _91894 _91895 f g h)). Qed.
Lemma lem3582994 {_91882 _91894 : Type'} : (@ex (_91894 -> _91882)) = (@ex (_91894 -> _91882)).
Proof. exact (eq_refl (@ex (_91894 -> _91882))). Qed.
Lemma lem3582995 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term29 _91882 _91894 _91895 f g) = (term26 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3582994 _91882 _91894) (@lem3582993 _91882 _91894 _91895 f g)). Qed.
Lemma lem3582996 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3582997 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term39 _91882 _91894 _91895 f g) = (term40 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3582996) (@lem3582995 _91882 _91894 _91895 f g)). Qed.
Lemma lem3582998 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term32 _91882 _91894 _91895 f g x) = (term33 _91882 _91894 _91895 f x g).
Proof. exact (eq_refl (term32 _91882 _91894 _91895 f g x)). Qed.
Lemma lem3582999 {_91882 : Type'} (h : _91882) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem3583000 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h : _91882) : (term41 _91882 _91894 _91895 f g x h) = (term42 _91882 _91894 _91895 f x g h).
Proof. exact (MK_COMB (@lem3582998 _91882 _91894 _91895 f x g) (@lem3582999 _91882 h)). Qed.
Lemma lem3583001 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h : _91882) : (term42 _91882 _91894 _91895 f x g h) = ((f x) = (g h)).
Proof. exact (eq_refl (term42 _91882 _91894 _91895 f x g h)). Qed.
Lemma lem3583002 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h : _91882) : (term41 _91882 _91894 _91895 f g x h) = ((f x) = (g h)).
Proof. exact (TRANS (@lem3583000 _91882 _91894 _91895 f x g h) (@lem3583001 _91882 _91894 _91895 f x g h)). Qed.
Lemma lem3583003 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term43 _91882 _91894 _91895 f g x) = (term33 _91882 _91894 _91895 f x g).
Proof. exact (fun_ext (fun h : _91882 => @lem3583002 _91882 _91894 _91895 f x g h)). Qed.
Lemma lem3583004 {_91882 : Type'} : (@ex _91882) = (@ex _91882).
Proof. exact (eq_refl (@ex _91882)). Qed.
Lemma lem3583005 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term44 _91882 _91894 _91895 f g x) = (term45 _91882 _91894 _91895 f x g).
Proof. exact (MK_COMB (@lem3583004 _91882) (@lem3583003 _91882 _91894 _91895 f x g)). Qed.
Lemma lem3583006 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term46 _91882 _91894 _91895 f g) = (term47 _91882 _91894 _91895 f g).
Proof. exact (fun_ext (fun x : _91894 => @lem3583005 _91882 _91894 _91895 f x g)). Qed.
Lemma lem3583007 {_91894 : Type'} : (@all _91894) = (@all _91894).
Proof. exact (eq_refl (@all _91894)). Qed.
Lemma lem3583008 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term30 _91882 _91894 _91895 f g) = (term48 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3583007 _91894) (@lem3583006 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583009 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : ((term29 _91882 _91894 _91895 f g) = (term30 _91882 _91894 _91895 f g)) = ((term26 _91882 _91894 _91895 f g) = (term48 _91882 _91894 _91895 f g)).
Proof. exact (MK_COMB (@lem3582997 _91882 _91894 _91895 f g) (@lem3583008 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583010 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term26 _91882 _91894 _91895 f g) = (term48 _91882 _91894 _91895 f g).
Proof. exact (EQ_MP (@lem3583009 _91882 _91894 _91895 f g) (@lem3582984 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583023 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term25 _91882 _91894 _91895 f g) = (term48 _91882 _91894 _91895 f g).
Proof. exact (TRANS (@lem3582980 _91882 _91894 _91895 f g) (@lem3583010 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583024 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) : (term49 _91882 _91894 _91895 g f) = (term49 _91882 _91894 _91895 g f).
Proof. exact (eq_refl (term49 _91882 _91894 _91895 g f)). Qed.
Lemma lem3583025 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : ((term50 _91882 _91894 _91895 g f) = (term25 _91882 _91894 _91895 f g)) = ((term50 _91882 _91894 _91895 g f) = (term48 _91882 _91894 _91895 f g)).
Proof. exact (MK_COMB (@lem3583024 _91882 _91894 _91895 g f) (@lem3583023 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583030 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) : (term51 _91882 _91894 _91895 f) = (term52 _91882 _91894 _91895 f).
Proof. exact (fun_ext (fun g : _91882 -> _91895 => @lem3583025 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583031 {_91882 _91895 : Type'} : (@all (_91882 -> _91895)) = (@all (_91882 -> _91895)).
Proof. exact (eq_refl (@all (_91882 -> _91895))). Qed.
Lemma lem3583032 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) : (term53 _91882 _91894 _91895 f) = (term54 _91882 _91894 _91895 f).
Proof. exact (MK_COMB (@lem3583031 _91882 _91895) (@lem3583030 _91882 _91894 _91895 f)). Qed.
Lemma lem3583037 {_91882 _91894 _91895 : Type'} : (term55 _91882 _91894 _91895) = (term56 _91882 _91894 _91895).
Proof. exact (fun_ext (fun f : _91894 -> _91895 => @lem3583032 _91882 _91894 _91895 f)). Qed.
Lemma lem3583038 {_91894 _91895 : Type'} : (@all (_91894 -> _91895)) = (@all (_91894 -> _91895)).
Proof. exact (eq_refl (@all (_91894 -> _91895))). Qed.
Lemma lem3583039 {_91882 _91894 _91895 : Type'} : (term57 _91882 _91894 _91895) = (term58 _91882 _91894 _91895).
Proof. exact (MK_COMB (@lem3583038 _91894 _91895) (@lem3583037 _91882 _91894 _91895)). Qed.
Lemma lem3583044 {_91882 _91894 _91895 : Type'} : (term58 _91882 _91894 _91895) = (term57 _91882 _91894 _91895).
Proof. exact (SYM (@lem3583039 _91882 _91894 _91895)). Qed.
Lemma lem3583046 (p : Prop) : p = (term59 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3583047 {_91882 _91894 _91895 : Type'} : (term58 _91882 _91894 _91895) = (term60 _91882 _91894 _91895).
Proof. exact (@lem3583046 (term58 _91882 _91894 _91895)). Qed.
Lemma lem3583048 {_91882 _91894 _91895 : Type'} : (term60 _91882 _91894 _91895) = (term58 _91882 _91894 _91895).
Proof. exact (SYM (@lem3583047 _91882 _91894 _91895)). Qed.
Lemma lem3583049 {_91882 _91894 _91895 : Type'} (h1 : term61 _91882 _91894 _91895) : term61 _91882 _91894 _91895.
Proof. exact (h1). Qed.
Lemma lem3583052 {_91882 _91894 _91895 : Type'} (h1 : term60 _91882 _91894 _91895) : term60 _91882 _91894 _91895.
Proof. exact (h1). Qed.
Lemma lem3583053 {_91882 _91894 _91895 : Type'} : term62 _91882 _91894 _91895.
Proof. exact (fun h0 : term60 _91882 _91894 _91895 => @lem3583052 _91882 _91894 _91895 h0). Qed.
Lemma lem3583054 {_91882 _91894 _91895 : Type'} (h1 : term62 _91882 _91894 _91895) : term62 _91882 _91894 _91895.
Proof. exact (h1). Qed.
Lemma lem3583055 {_91882 _91894 _91895 : Type'} (h1 : term60 _91882 _91894 _91895) : term60 _91882 _91894 _91895.
Proof. exact (h1). Qed.
Lemma lem3583056 {_91882 _91894 _91895 : Type'} (h1 : term60 _91882 _91894 _91895) (h2 : term62 _91882 _91894 _91895) : term60 _91882 _91894 _91895.
Proof. exact (@lem3583054 _91882 _91894 _91895 h2 (@lem3583055 _91882 _91894 _91895 h1)). Qed.
Lemma lem3583057 {_91882 _91894 _91895 : Type'} (h1 : term60 _91882 _91894 _91895) : term63 _91882 _91894 _91895.
Proof. exact (fun h0 : term62 _91882 _91894 _91895 => @lem3583056 _91882 _91894 _91895 h1 h0). Qed.
Lemma lem3583058 {_91882 _91894 _91895 : Type'} (h1 : term62 _91882 _91894 _91895) : term62 _91882 _91894 _91895.
Proof. exact (h1). Qed.
Lemma lem3583059 {_91882 _91894 _91895 : Type'} (h1 : term60 _91882 _91894 _91895) (h2 : term62 _91882 _91894 _91895) : term60 _91882 _91894 _91895.
Proof. exact (@lem3583057 _91882 _91894 _91895 h1 (@lem3583058 _91882 _91894 _91895 h2)). Qed.
Lemma lem3583060 {_91882 _91894 _91895 : Type'} (h1 : term62 _91882 _91894 _91895) : term62 _91882 _91894 _91895.
Proof. exact (fun h0 : term60 _91882 _91894 _91895 => @lem3583059 _91882 _91894 _91895 h0 h1). Qed.
Lemma lem3583061 {_91882 _91894 _91895 : Type'} : term64 _91882 _91894 _91895.
Proof. exact (fun h0 : term62 _91882 _91894 _91895 => @lem3583060 _91882 _91894 _91895 h0). Qed.
Lemma lem3583064 {_91882 _91894 _91895 : Type'} : term62 _91882 _91894 _91895.
Proof. exact (@lem3583061 _91882 _91894 _91895 (@lem3583053 _91882 _91894 _91895)). Qed.
Lemma lem3583065 {_91882 _91894 _91895 : Type'} : term62 _91882 _91894 _91895.
Proof. exact (@lem3583064 _91882 _91894 _91895). Qed.
Lemma lem3583067 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3583068 {_91882 _91894 _91895 : Type'} : (term60 _91882 _91894 _91895) = (term65 _91882 _91894 _91895).
Proof. exact (@lem3583067 (term61 _91882 _91894 _91895)). Qed.
Lemma lem3583070 (t : Prop) : (term66 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3583071 {_91882 _91894 _91895 : Type'} : (term65 _91882 _91894 _91895) = (term58 _91882 _91894 _91895).
Proof. exact (@lem3583070 (term58 _91882 _91894 _91895)). Qed.
Lemma lem3583100 {_91882 _91894 _91895 : Type'} : (term60 _91882 _91894 _91895) = (term58 _91882 _91894 _91895).
Proof. exact (TRANS (@lem3583068 _91882 _91894 _91895) (@lem3583071 _91882 _91894 _91895)). Qed.
Lemma lem3583101 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h : _91882) : ((f x) = (g h)) = ((f x) = (g h)).
Proof. exact (eq_refl ((f x) = (g h))). Qed.
Lemma lem3583102 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term33 _91882 _91894 _91895 f x g) = (term33 _91882 _91894 _91895 f x g).
Proof. exact (fun_ext (fun h : _91882 => @lem3583101 _91882 _91894 _91895 f x g h)). Qed.
Lemma lem3583103 {_91882 : Type'} : (@ex _91882) = (@ex _91882).
Proof. exact (eq_refl (@ex _91882)). Qed.
Lemma lem3583104 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term45 _91882 _91894 _91895 f x g) = (term45 _91882 _91894 _91895 f x g).
Proof. exact (MK_COMB (@lem3583103 _91882) (@lem3583102 _91882 _91894 _91895 f x g)). Qed.
Lemma lem3583105 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term47 _91882 _91894 _91895 f g) = (term47 _91882 _91894 _91895 f g).
Proof. exact (fun_ext (fun x : _91894 => @lem3583104 _91882 _91894 _91895 f x g)). Qed.
Lemma lem3583106 {_91894 : Type'} : (@all _91894) = (@all _91894).
Proof. exact (eq_refl (@all _91894)). Qed.
Lemma lem3583107 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term48 _91882 _91894 _91895 f g) = (term48 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3583106 _91894) (@lem3583105 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583108 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (y : _91882) (f : _91894 -> _91895) (x : _91894) : ((g y) = (f x)) = ((g y) = (f x)).
Proof. exact (eq_refl ((g y) = (f x))). Qed.
Lemma lem3583109 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) (x : _91894) : (term67 _91882 _91894 _91895 g f x) = (term67 _91882 _91894 _91895 g f x).
Proof. exact (fun_ext (fun y : _91882 => @lem3583108 _91882 _91894 _91895 g y f x)). Qed.
Lemma lem3583110 {_91882 : Type'} : (@ex _91882) = (@ex _91882).
Proof. exact (eq_refl (@ex _91882)). Qed.
Lemma lem3583111 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) (x : _91894) : (term68 _91882 _91894 _91895 g f x) = (term68 _91882 _91894 _91895 g f x).
Proof. exact (MK_COMB (@lem3583110 _91882) (@lem3583109 _91882 _91894 _91895 g f x)). Qed.
Lemma lem3583112 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) : (term69 _91882 _91894 _91895 g f) = (term69 _91882 _91894 _91895 g f).
Proof. exact (fun_ext (fun x : _91894 => @lem3583111 _91882 _91894 _91895 g f x)). Qed.
Lemma lem3583113 {_91894 : Type'} : (@all _91894) = (@all _91894).
Proof. exact (eq_refl (@all _91894)). Qed.
Lemma lem3583114 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) : (term50 _91882 _91894 _91895 g f) = (term50 _91882 _91894 _91895 g f).
Proof. exact (MK_COMB (@lem3583113 _91894) (@lem3583112 _91882 _91894 _91895 g f)). Qed.
Lemma lem3583115 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3583116 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) : (term49 _91882 _91894 _91895 g f) = (term49 _91882 _91894 _91895 g f).
Proof. exact (MK_COMB (@lem3583115) (@lem3583114 _91882 _91894 _91895 g f)). Qed.
Lemma lem3583117 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : ((term50 _91882 _91894 _91895 g f) = (term48 _91882 _91894 _91895 f g)) = ((term50 _91882 _91894 _91895 g f) = (term48 _91882 _91894 _91895 f g)).
Proof. exact (MK_COMB (@lem3583116 _91882 _91894 _91895 g f) (@lem3583107 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583118 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) : (term52 _91882 _91894 _91895 f) = (term52 _91882 _91894 _91895 f).
Proof. exact (fun_ext (fun g : _91882 -> _91895 => @lem3583117 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583119 {_91882 _91895 : Type'} : (@all (_91882 -> _91895)) = (@all (_91882 -> _91895)).
Proof. exact (eq_refl (@all (_91882 -> _91895))). Qed.
Lemma lem3583120 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) : (term54 _91882 _91894 _91895 f) = (term54 _91882 _91894 _91895 f).
Proof. exact (MK_COMB (@lem3583119 _91882 _91895) (@lem3583118 _91882 _91894 _91895 f)). Qed.
Lemma lem3583121 {_91882 _91894 _91895 : Type'} : (term56 _91882 _91894 _91895) = (term56 _91882 _91894 _91895).
Proof. exact (fun_ext (fun f : _91894 -> _91895 => @lem3583120 _91882 _91894 _91895 f)). Qed.
Lemma lem3583122 {_91894 _91895 : Type'} : (@all (_91894 -> _91895)) = (@all (_91894 -> _91895)).
Proof. exact (eq_refl (@all (_91894 -> _91895))). Qed.
Lemma lem3583123 {_91882 _91894 _91895 : Type'} : (term58 _91882 _91894 _91895) = (term58 _91882 _91894 _91895).
Proof. exact (MK_COMB (@lem3583122 _91894 _91895) (@lem3583121 _91882 _91894 _91895)). Qed.
Lemma lem3583162 {_91882 _91894 _91895 : Type'} : (term60 _91882 _91894 _91895) = (term58 _91882 _91894 _91895).
Proof. exact (TRANS (@lem3583100 _91882 _91894 _91895) (@lem3583123 _91882 _91894 _91895)). Qed.
Lemma lem3583163 {_91882 _91894 _91895 : Type'} : (term58 _91882 _91894 _91895) = (term60 _91882 _91894 _91895).
Proof. exact (SYM (@lem3583162 _91882 _91894 _91895)). Qed.
Lemma lem3583165 (p : Prop) : p = (term59 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3583166 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : ((term50 _91882 _91894 _91895 g f) = (term48 _91882 _91894 _91895 f g)) = (term70 _91882 _91894 _91895 f g).
Proof. exact (@lem3583165 ((term50 _91882 _91894 _91895 g f) = (term48 _91882 _91894 _91895 f g))). Qed.
Lemma lem3583167 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term70 _91882 _91894 _91895 f g) = ((term50 _91882 _91894 _91895 g f) = (term48 _91882 _91894 _91895 f g)).
Proof. exact (SYM (@lem3583166 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583168 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) (h1 : term71 _91882 _91894 _91895 f g) : term71 _91882 _91894 _91895 f g.
Proof. exact (h1). Qed.
Lemma lem3583170 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (y : _91882) (f : _91894 -> _91895) (x : _91894) : ((g y) = (f x)) = ((g y) = (f x)).
Proof. exact (eq_refl ((g y) = (f x))). Qed.
Lemma lem3583171 {_91882 : Type'} (P : _91882 -> Prop) : (term72 _91882 P) = (term73 _91882 P).
Proof. exact (@lem18394 _91882 P). Qed.
Lemma lem3583172 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) (x : _91894) : (term74 _91882 _91894 _91895 g f x) = (term75 _91882 _91894 _91895 g f x).
Proof. exact (@lem3583171 _91882 (term67 _91882 _91894 _91895 g f x)). Qed.
Lemma lem3583173 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (y : _91882) (f : _91894 -> _91895) (x : _91894) : (term76 _91882 _91894 _91895 g f x y) = ((g y) = (f x)).
Proof. exact (eq_refl (term76 _91882 _91894 _91895 g f x y)). Qed.
Lemma lem3583174 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3583176 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (y : _91882) (f : _91894 -> _91895) (x : _91894) : (term77 _91882 _91894 _91895 g f x y) = (term78 _91882 _91894 _91895 g y f x).
Proof. exact (MK_COMB (@lem3583174) (@lem3583173 _91882 _91894 _91895 g y f x)). Qed.
Lemma lem3583177 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) (x : _91894) : (term79 _91882 _91894 _91895 g f x) = (term80 _91882 _91894 _91895 g f x).
Proof. exact (fun_ext (fun y : _91882 => @lem3583176 _91882 _91894 _91895 g y f x)). Qed.
Lemma lem3583178 {_91882 : Type'} : (@all _91882) = (@all _91882).
Proof. exact (eq_refl (@all _91882)). Qed.
Lemma lem3583179 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) (x : _91894) : (term75 _91882 _91894 _91895 g f x) = (term81 _91882 _91894 _91895 g f x).
Proof. exact (MK_COMB (@lem3583178 _91882) (@lem3583177 _91882 _91894 _91895 g f x)). Qed.
Lemma lem3583180 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) (x : _91894) : (term74 _91882 _91894 _91895 g f x) = (term81 _91882 _91894 _91895 g f x).
Proof. exact (TRANS (@lem3583172 _91882 _91894 _91895 g f x) (@lem3583179 _91882 _91894 _91895 g f x)). Qed.
Lemma lem3583181 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) (x : _91894) : (term67 _91882 _91894 _91895 g f x) = (term67 _91882 _91894 _91895 g f x).
Proof. exact (fun_ext (fun y : _91882 => @lem3583170 _91882 _91894 _91895 g y f x)). Qed.
Lemma lem3583182 {_91882 : Type'} : (@ex _91882) = (@ex _91882).
Proof. exact (eq_refl (@ex _91882)). Qed.
Lemma lem3583183 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) (x : _91894) : (term68 _91882 _91894 _91895 g f x) = (term68 _91882 _91894 _91895 g f x).
Proof. exact (MK_COMB (@lem3583182 _91882) (@lem3583181 _91882 _91894 _91895 g f x)). Qed.
Lemma lem3583184 {_91894 : Type'} (P : _91894 -> Prop) : (term82 _91894 P) = (term83 _91894 P).
Proof. exact (@lem18392 _91894 P). Qed.
Lemma lem3583185 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) : (term84 _91882 _91894 _91895 g f) = (term85 _91882 _91894 _91895 g f).
Proof. exact (@lem3583184 _91894 (term69 _91882 _91894 _91895 g f)). Qed.
Lemma lem3583186 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) (x : _91894) : (term86 _91882 _91894 _91895 g f x) = (term68 _91882 _91894 _91895 g f x).
Proof. exact (eq_refl (term86 _91882 _91894 _91895 g f x)). Qed.
Lemma lem3583187 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3583188 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) (x : _91894) : (term87 _91882 _91894 _91895 g f x) = (term74 _91882 _91894 _91895 g f x).
Proof. exact (MK_COMB (@lem3583187) (@lem3583186 _91882 _91894 _91895 g f x)). Qed.
Lemma lem3583189 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) (x : _91894) : (term87 _91882 _91894 _91895 g f x) = (term81 _91882 _91894 _91895 g f x).
Proof. exact (TRANS (@lem3583188 _91882 _91894 _91895 g f x) (@lem3583180 _91882 _91894 _91895 g f x)). Qed.
Lemma lem3583190 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) : (term88 _91882 _91894 _91895 g f) = (term89 _91882 _91894 _91895 g f).
Proof. exact (fun_ext (fun x : _91894 => @lem3583189 _91882 _91894 _91895 g f x)). Qed.
Lemma lem3583191 {_91894 : Type'} : (@ex _91894) = (@ex _91894).
Proof. exact (eq_refl (@ex _91894)). Qed.
Lemma lem3583192 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) : (term85 _91882 _91894 _91895 g f) = (term90 _91882 _91894 _91895 g f).
Proof. exact (MK_COMB (@lem3583191 _91894) (@lem3583190 _91882 _91894 _91895 g f)). Qed.
Lemma lem3583193 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) : (term84 _91882 _91894 _91895 g f) = (term90 _91882 _91894 _91895 g f).
Proof. exact (TRANS (@lem3583185 _91882 _91894 _91895 g f) (@lem3583192 _91882 _91894 _91895 g f)). Qed.
Lemma lem3583194 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) : (term69 _91882 _91894 _91895 g f) = (term69 _91882 _91894 _91895 g f).
Proof. exact (fun_ext (fun x : _91894 => @lem3583183 _91882 _91894 _91895 g f x)). Qed.
Lemma lem3583195 {_91894 : Type'} : (@all _91894) = (@all _91894).
Proof. exact (eq_refl (@all _91894)). Qed.
Lemma lem3583196 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) : (term50 _91882 _91894 _91895 g f) = (term50 _91882 _91894 _91895 g f).
Proof. exact (MK_COMB (@lem3583195 _91894) (@lem3583194 _91882 _91894 _91895 g f)). Qed.
Lemma lem3583198 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h : _91882) : ((f x) = (g h)) = ((f x) = (g h)).
Proof. exact (eq_refl ((f x) = (g h))). Qed.
Lemma lem3583199 {_91882 : Type'} (P : _91882 -> Prop) : (term72 _91882 P) = (term73 _91882 P).
Proof. exact (@lem18394 _91882 P). Qed.
Lemma lem3583200 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term91 _91882 _91894 _91895 f x g) = (term92 _91882 _91894 _91895 f x g).
Proof. exact (@lem3583199 _91882 (term33 _91882 _91894 _91895 f x g)). Qed.
Lemma lem3583201 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h : _91882) : (term42 _91882 _91894 _91895 f x g h) = ((f x) = (g h)).
Proof. exact (eq_refl (term42 _91882 _91894 _91895 f x g h)). Qed.
Lemma lem3583202 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3583204 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h : _91882) : (term93 _91882 _91894 _91895 f x g h) = (term94 _91882 _91894 _91895 f x g h).
Proof. exact (MK_COMB (@lem3583202) (@lem3583201 _91882 _91894 _91895 f x g h)). Qed.
Lemma lem3583205 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term95 _91882 _91894 _91895 f x g) = (term96 _91882 _91894 _91895 f x g).
Proof. exact (fun_ext (fun h : _91882 => @lem3583204 _91882 _91894 _91895 f x g h)). Qed.
Lemma lem3583206 {_91882 : Type'} : (@all _91882) = (@all _91882).
Proof. exact (eq_refl (@all _91882)). Qed.
Lemma lem3583207 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term92 _91882 _91894 _91895 f x g) = (term97 _91882 _91894 _91895 f x g).
Proof. exact (MK_COMB (@lem3583206 _91882) (@lem3583205 _91882 _91894 _91895 f x g)). Qed.
Lemma lem3583208 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term91 _91882 _91894 _91895 f x g) = (term97 _91882 _91894 _91895 f x g).
Proof. exact (TRANS (@lem3583200 _91882 _91894 _91895 f x g) (@lem3583207 _91882 _91894 _91895 f x g)). Qed.
Lemma lem3583209 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term33 _91882 _91894 _91895 f x g) = (term33 _91882 _91894 _91895 f x g).
Proof. exact (fun_ext (fun h : _91882 => @lem3583198 _91882 _91894 _91895 f x g h)). Qed.
Lemma lem3583210 {_91882 : Type'} : (@ex _91882) = (@ex _91882).
Proof. exact (eq_refl (@ex _91882)). Qed.
Lemma lem3583211 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term45 _91882 _91894 _91895 f x g) = (term45 _91882 _91894 _91895 f x g).
Proof. exact (MK_COMB (@lem3583210 _91882) (@lem3583209 _91882 _91894 _91895 f x g)). Qed.
Lemma lem3583212 {_91894 : Type'} (P : _91894 -> Prop) : (term82 _91894 P) = (term83 _91894 P).
Proof. exact (@lem18392 _91894 P). Qed.
Lemma lem3583213 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term98 _91882 _91894 _91895 f g) = (term99 _91882 _91894 _91895 f g).
Proof. exact (@lem3583212 _91894 (term47 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583214 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term100 _91882 _91894 _91895 f g x) = (term45 _91882 _91894 _91895 f x g).
Proof. exact (eq_refl (term100 _91882 _91894 _91895 f g x)). Qed.
Lemma lem3583215 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3583216 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term101 _91882 _91894 _91895 f g x) = (term91 _91882 _91894 _91895 f x g).
Proof. exact (MK_COMB (@lem3583215) (@lem3583214 _91882 _91894 _91895 f x g)). Qed.
Lemma lem3583217 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term101 _91882 _91894 _91895 f g x) = (term97 _91882 _91894 _91895 f x g).
Proof. exact (TRANS (@lem3583216 _91882 _91894 _91895 f x g) (@lem3583208 _91882 _91894 _91895 f x g)). Qed.
Lemma lem3583218 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term102 _91882 _91894 _91895 f g) = (term103 _91882 _91894 _91895 f g).
Proof. exact (fun_ext (fun x : _91894 => @lem3583217 _91882 _91894 _91895 f x g)). Qed.
Lemma lem3583219 {_91894 : Type'} : (@ex _91894) = (@ex _91894).
Proof. exact (eq_refl (@ex _91894)). Qed.
Lemma lem3583220 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term99 _91882 _91894 _91895 f g) = (term104 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3583219 _91894) (@lem3583218 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583221 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term98 _91882 _91894 _91895 f g) = (term104 _91882 _91894 _91895 f g).
Proof. exact (TRANS (@lem3583213 _91882 _91894 _91895 f g) (@lem3583220 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583222 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term47 _91882 _91894 _91895 f g) = (term47 _91882 _91894 _91895 f g).
Proof. exact (fun_ext (fun x : _91894 => @lem3583211 _91882 _91894 _91895 f x g)). Qed.
Lemma lem3583223 {_91894 : Type'} : (@all _91894) = (@all _91894).
Proof. exact (eq_refl (@all _91894)). Qed.
Lemma lem3583224 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term48 _91882 _91894 _91895 f g) = (term48 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3583223 _91894) (@lem3583222 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583225 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3583226 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) : (term105 _91882 _91894 _91895 g f) = (term106 _91882 _91894 _91895 g f).
Proof. exact (MK_COMB (@lem3583225) (@lem3583193 _91882 _91894 _91895 g f)). Qed.
Lemma lem3583227 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term107 _91882 _91894 _91895 f g) = (term108 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3583226 _91882 _91894 _91895 g f) (@lem3583224 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583228 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3583229 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) : (term109 _91882 _91894 _91895 g f) = (term109 _91882 _91894 _91895 g f).
Proof. exact (MK_COMB (@lem3583228) (@lem3583196 _91882 _91894 _91895 g f)). Qed.
Lemma lem3583230 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term110 _91882 _91894 _91895 f g) = (term111 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3583229 _91882 _91894 _91895 g f) (@lem3583221 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583231 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3583232 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term112 _91882 _91894 _91895 f g) = (term113 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3583231) (@lem3583230 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583233 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term114 _91882 _91894 _91895 f g) = (term115 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3583232 _91882 _91894 _91895 f g) (@lem3583227 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583234 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term71 _91882 _91894 _91895 f g) = (term114 _91882 _91894 _91895 f g).
Proof. exact (@lem17646 (term50 _91882 _91894 _91895 g f) (term48 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583235 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term71 _91882 _91894 _91895 f g) = (term115 _91882 _91894 _91895 f g).
Proof. exact (TRANS (@lem3583234 _91882 _91894 _91895 f g) (@lem3583233 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583270 {A B : Type'} (P : type1413 A B) : (term0 A B P) = (term1 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3583271 {_91882 _91894 : Type'} (P : type1470 _91882 _91894) : (term28 _91882 _91894 P) = (term27 _91882 _91894 P).
Proof. exact (@lem3583270 _91894 _91882 P). Qed.
Lemma lem3583272 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) : (term116 _91882 _91894 _91895 g f) = (term117 _91882 _91894 _91895 g f).
Proof. exact (@lem3583271 _91882 _91894 (term118 _91882 _91894 _91895 g f)). Qed.
Lemma lem3583273 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) (x : _91894) : (term119 _91882 _91894 _91895 g f x) = (term67 _91882 _91894 _91895 g f x).
Proof. exact (eq_refl (term119 _91882 _91894 _91895 g f x)). Qed.
Lemma lem3583274 {_91882 : Type'} (y : _91882) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3583275 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) (x : _91894) (y : _91882) : (term120 _91882 _91894 _91895 g f x y) = (term76 _91882 _91894 _91895 g f x y).
Proof. exact (MK_COMB (@lem3583273 _91882 _91894 _91895 g f x) (@lem3583274 _91882 y)). Qed.
Lemma lem3583276 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (y : _91882) (f : _91894 -> _91895) (x : _91894) : (term76 _91882 _91894 _91895 g f x y) = ((g y) = (f x)).
Proof. exact (eq_refl (term76 _91882 _91894 _91895 g f x y)). Qed.
Lemma lem3583277 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (y : _91882) (f : _91894 -> _91895) (x : _91894) : (term120 _91882 _91894 _91895 g f x y) = ((g y) = (f x)).
Proof. exact (TRANS (@lem3583275 _91882 _91894 _91895 g f x y) (@lem3583276 _91882 _91894 _91895 g y f x)). Qed.
Lemma lem3583278 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) (x : _91894) : (term121 _91882 _91894 _91895 g f x) = (term67 _91882 _91894 _91895 g f x).
Proof. exact (fun_ext (fun y : _91882 => @lem3583277 _91882 _91894 _91895 g y f x)). Qed.
Lemma lem3583279 {_91882 : Type'} : (@ex _91882) = (@ex _91882).
Proof. exact (eq_refl (@ex _91882)). Qed.
Lemma lem3583280 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) (x : _91894) : (term122 _91882 _91894 _91895 g f x) = (term68 _91882 _91894 _91895 g f x).
Proof. exact (MK_COMB (@lem3583279 _91882) (@lem3583278 _91882 _91894 _91895 g f x)). Qed.
Lemma lem3583281 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) : (term123 _91882 _91894 _91895 g f) = (term69 _91882 _91894 _91895 g f).
Proof. exact (fun_ext (fun x : _91894 => @lem3583280 _91882 _91894 _91895 g f x)). Qed.
Lemma lem3583282 {_91894 : Type'} : (@all _91894) = (@all _91894).
Proof. exact (eq_refl (@all _91894)). Qed.
Lemma lem3583283 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) : (term116 _91882 _91894 _91895 g f) = (term50 _91882 _91894 _91895 g f).
Proof. exact (MK_COMB (@lem3583282 _91894) (@lem3583281 _91882 _91894 _91895 g f)). Qed.
Lemma lem3583284 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3583285 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) : (term124 _91882 _91894 _91895 g f) = (term49 _91882 _91894 _91895 g f).
Proof. exact (MK_COMB (@lem3583284) (@lem3583283 _91882 _91894 _91895 g f)). Qed.
Lemma lem3583286 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) (x : _91894) : (term119 _91882 _91894 _91895 g f x) = (term67 _91882 _91894 _91895 g f x).
Proof. exact (eq_refl (term119 _91882 _91894 _91895 g f x)). Qed.
Lemma lem3583287 {_91882 _91894 : Type'} (y : _91894 -> _91882) (x : _91894) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem3583288 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) (y : _91894 -> _91882) (x : _91894) : (term125 _91882 _91894 _91895 g f y x) = (term126 _91882 _91894 _91895 g f y x).
Proof. exact (MK_COMB (@lem3583286 _91882 _91894 _91895 g f x) (@lem3583287 _91882 _91894 y x)). Qed.
Lemma lem3583289 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) : (term126 _91882 _91894 _91895 g f y x) = ((term18 _91882 _91894 _91895 g y x) = (f x)).
Proof. exact (eq_refl (term126 _91882 _91894 _91895 g f y x)). Qed.
Lemma lem3583290 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) : (term125 _91882 _91894 _91895 g f y x) = ((term18 _91882 _91894 _91895 g y x) = (f x)).
Proof. exact (TRANS (@lem3583288 _91882 _91894 _91895 g f y x) (@lem3583289 _91882 _91894 _91895 g y f x)). Qed.
Lemma lem3583291 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (y : _91894 -> _91882) (f : _91894 -> _91895) : (term127 _91882 _91894 _91895 g f y) = (term128 _91882 _91894 _91895 g y f).
Proof. exact (fun_ext (fun x : _91894 => @lem3583290 _91882 _91894 _91895 g y f x)). Qed.
Lemma lem3583292 {_91894 : Type'} : (@all _91894) = (@all _91894).
Proof. exact (eq_refl (@all _91894)). Qed.
Lemma lem3583293 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (y : _91894 -> _91882) (f : _91894 -> _91895) : (term129 _91882 _91894 _91895 g f y) = (term130 _91882 _91894 _91895 g y f).
Proof. exact (MK_COMB (@lem3583292 _91894) (@lem3583291 _91882 _91894 _91895 g y f)). Qed.
Lemma lem3583294 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) : (term131 _91882 _91894 _91895 g f) = (term132 _91882 _91894 _91895 g f).
Proof. exact (fun_ext (fun y : _91894 -> _91882 => @lem3583293 _91882 _91894 _91895 g y f)). Qed.
Lemma lem3583295 {_91882 _91894 : Type'} : (@ex (_91894 -> _91882)) = (@ex (_91894 -> _91882)).
Proof. exact (eq_refl (@ex (_91894 -> _91882))). Qed.
Lemma lem3583296 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) : (term117 _91882 _91894 _91895 g f) = (term133 _91882 _91894 _91895 g f).
Proof. exact (MK_COMB (@lem3583295 _91882 _91894) (@lem3583294 _91882 _91894 _91895 g f)). Qed.
Lemma lem3583297 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) : ((term116 _91882 _91894 _91895 g f) = (term117 _91882 _91894 _91895 g f)) = ((term50 _91882 _91894 _91895 g f) = (term133 _91882 _91894 _91895 g f)).
Proof. exact (MK_COMB (@lem3583285 _91882 _91894 _91895 g f) (@lem3583296 _91882 _91894 _91895 g f)). Qed.
Lemma lem3583298 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) : (term50 _91882 _91894 _91895 g f) = (term133 _91882 _91894 _91895 g f).
Proof. exact (EQ_MP (@lem3583297 _91882 _91894 _91895 g f) (@lem3583272 _91882 _91894 _91895 g f)). Qed.
Lemma lem3583299 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3583300 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) : (term109 _91882 _91894 _91895 g f) = (term134 _91882 _91894 _91895 g f).
Proof. exact (MK_COMB (@lem3583299) (@lem3583298 _91882 _91894 _91895 g f)). Qed.
Lemma lem3583301 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term104 _91882 _91894 _91895 f g) = (term104 _91882 _91894 _91895 f g).
Proof. exact (eq_refl (term104 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583302 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term111 _91882 _91894 _91895 f g) = (term135 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3583300 _91882 _91894 _91895 g f) (@lem3583301 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583304 {A : Type'} (P : A -> Prop) (Q : Prop) : (term136 A P Q) = (term137 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3583305 {_91882 _91894 : Type'} (P : type805 _91882 _91894) (Q : Prop) : (term138 _91882 _91894 P Q) = (term139 _91882 _91894 P Q).
Proof. exact (@lem3583304 (_91894 -> _91882) P Q). Qed.
Lemma lem3583306 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term140 _91882 _91894 _91895 f g) = (term141 _91882 _91894 _91895 f g).
Proof. exact (@lem3583305 _91882 _91894 (term132 _91882 _91894 _91895 g f) (term104 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583307 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (y : _91894 -> _91882) (f : _91894 -> _91895) : (term142 _91882 _91894 _91895 g f y) = (term130 _91882 _91894 _91895 g y f).
Proof. exact (eq_refl (term142 _91882 _91894 _91895 g f y)). Qed.
Lemma lem3583308 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) : (term143 _91882 _91894 _91895 g f) = (term132 _91882 _91894 _91895 g f).
Proof. exact (fun_ext (fun y : _91894 -> _91882 => @lem3583307 _91882 _91894 _91895 g y f)). Qed.
Lemma lem3583309 {_91882 _91894 : Type'} : (@ex (_91894 -> _91882)) = (@ex (_91894 -> _91882)).
Proof. exact (eq_refl (@ex (_91894 -> _91882))). Qed.
Lemma lem3583310 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) : (term144 _91882 _91894 _91895 g f) = (term133 _91882 _91894 _91895 g f).
Proof. exact (MK_COMB (@lem3583309 _91882 _91894) (@lem3583308 _91882 _91894 _91895 g f)). Qed.
Lemma lem3583311 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3583312 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) : (term145 _91882 _91894 _91895 g f) = (term134 _91882 _91894 _91895 g f).
Proof. exact (MK_COMB (@lem3583311) (@lem3583310 _91882 _91894 _91895 g f)). Qed.
Lemma lem3583313 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term104 _91882 _91894 _91895 f g) = (term104 _91882 _91894 _91895 f g).
Proof. exact (eq_refl (term104 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583314 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term140 _91882 _91894 _91895 f g) = (term135 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3583312 _91882 _91894 _91895 g f) (@lem3583313 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583315 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3583316 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term146 _91882 _91894 _91895 f g) = (term147 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3583315) (@lem3583314 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583317 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (y : _91894 -> _91882) (f : _91894 -> _91895) : (term142 _91882 _91894 _91895 g f y) = (term130 _91882 _91894 _91895 g y f).
Proof. exact (eq_refl (term142 _91882 _91894 _91895 g f y)). Qed.
Lemma lem3583318 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3583319 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (y : _91894 -> _91882) (f : _91894 -> _91895) : (term148 _91882 _91894 _91895 g f y) = (term149 _91882 _91894 _91895 g y f).
Proof. exact (MK_COMB (@lem3583318) (@lem3583317 _91882 _91894 _91895 g y f)). Qed.
Lemma lem3583320 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term104 _91882 _91894 _91895 f g) = (term104 _91882 _91894 _91895 f g).
Proof. exact (eq_refl (term104 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583321 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term150 _91882 _91894 _91895 y f g) = (term151 _91882 _91894 _91895 y f g).
Proof. exact (MK_COMB (@lem3583319 _91882 _91894 _91895 g y f) (@lem3583320 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583322 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term152 _91882 _91894 _91895 f g) = (term153 _91882 _91894 _91895 f g).
Proof. exact (fun_ext (fun y : _91894 -> _91882 => @lem3583321 _91882 _91894 _91895 y f g)). Qed.
Lemma lem3583323 {_91882 _91894 : Type'} : (@ex (_91894 -> _91882)) = (@ex (_91894 -> _91882)).
Proof. exact (eq_refl (@ex (_91894 -> _91882))). Qed.
Lemma lem3583324 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term141 _91882 _91894 _91895 f g) = (term154 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3583323 _91882 _91894) (@lem3583322 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583325 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : ((term140 _91882 _91894 _91895 f g) = (term141 _91882 _91894 _91895 f g)) = ((term135 _91882 _91894 _91895 f g) = (term154 _91882 _91894 _91895 f g)).
Proof. exact (MK_COMB (@lem3583316 _91882 _91894 _91895 f g) (@lem3583324 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583326 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term135 _91882 _91894 _91895 f g) = (term154 _91882 _91894 _91895 f g).
Proof. exact (EQ_MP (@lem3583325 _91882 _91894 _91895 f g) (@lem3583306 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583328 {A : Type'} (P : Prop) (Q : A -> Prop) : (term155 A P Q) = (term156 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3583329 {_91894 : Type'} (P : Prop) (Q : _91894 -> Prop) : (term155 _91894 P Q) = (term156 _91894 P Q).
Proof. exact (@lem3583328 _91894 P Q). Qed.
Lemma lem3583330 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term157 _91882 _91894 _91895 y f g) = (term158 _91882 _91894 _91895 y f g).
Proof. exact (@lem3583329 _91894 (term130 _91882 _91894 _91895 g y f) (term103 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583331 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term159 _91882 _91894 _91895 f g x) = (term97 _91882 _91894 _91895 f x g).
Proof. exact (eq_refl (term159 _91882 _91894 _91895 f g x)). Qed.
Lemma lem3583332 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term160 _91882 _91894 _91895 f g) = (term103 _91882 _91894 _91895 f g).
Proof. exact (fun_ext (fun x : _91894 => @lem3583331 _91882 _91894 _91895 f x g)). Qed.
Lemma lem3583333 {_91894 : Type'} : (@ex _91894) = (@ex _91894).
Proof. exact (eq_refl (@ex _91894)). Qed.
Lemma lem3583334 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term161 _91882 _91894 _91895 f g) = (term104 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3583333 _91894) (@lem3583332 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583335 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (y : _91894 -> _91882) (f : _91894 -> _91895) : (term149 _91882 _91894 _91895 g y f) = (term149 _91882 _91894 _91895 g y f).
Proof. exact (eq_refl (term149 _91882 _91894 _91895 g y f)). Qed.
Lemma lem3583336 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term157 _91882 _91894 _91895 y f g) = (term151 _91882 _91894 _91895 y f g).
Proof. exact (MK_COMB (@lem3583335 _91882 _91894 _91895 g y f) (@lem3583334 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583337 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3583338 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term162 _91882 _91894 _91895 y f g) = (term163 _91882 _91894 _91895 y f g).
Proof. exact (MK_COMB (@lem3583337) (@lem3583336 _91882 _91894 _91895 y f g)). Qed.
Lemma lem3583339 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term159 _91882 _91894 _91895 f g x) = (term97 _91882 _91894 _91895 f x g).
Proof. exact (eq_refl (term159 _91882 _91894 _91895 f g x)). Qed.
Lemma lem3583340 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (y : _91894 -> _91882) (f : _91894 -> _91895) : (term149 _91882 _91894 _91895 g y f) = (term149 _91882 _91894 _91895 g y f).
Proof. exact (eq_refl (term149 _91882 _91894 _91895 g y f)). Qed.
Lemma lem3583341 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term164 _91882 _91894 _91895 y f g x) = (term165 _91882 _91894 _91895 y f x g).
Proof. exact (MK_COMB (@lem3583340 _91882 _91894 _91895 g y f) (@lem3583339 _91882 _91894 _91895 f x g)). Qed.
Lemma lem3583342 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term166 _91882 _91894 _91895 y f g) = (term167 _91882 _91894 _91895 y f g).
Proof. exact (fun_ext (fun x : _91894 => @lem3583341 _91882 _91894 _91895 y f x g)). Qed.
Lemma lem3583343 {_91894 : Type'} : (@ex _91894) = (@ex _91894).
Proof. exact (eq_refl (@ex _91894)). Qed.
Lemma lem3583344 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term158 _91882 _91894 _91895 y f g) = (term168 _91882 _91894 _91895 y f g).
Proof. exact (MK_COMB (@lem3583343 _91894) (@lem3583342 _91882 _91894 _91895 y f g)). Qed.
Lemma lem3583345 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (g : _91882 -> _91895) : ((term157 _91882 _91894 _91895 y f g) = (term158 _91882 _91894 _91895 y f g)) = ((term151 _91882 _91894 _91895 y f g) = (term168 _91882 _91894 _91895 y f g)).
Proof. exact (MK_COMB (@lem3583338 _91882 _91894 _91895 y f g) (@lem3583344 _91882 _91894 _91895 y f g)). Qed.
Lemma lem3583346 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term151 _91882 _91894 _91895 y f g) = (term168 _91882 _91894 _91895 y f g).
Proof. exact (EQ_MP (@lem3583345 _91882 _91894 _91895 y f g) (@lem3583330 _91882 _91894 _91895 y f g)). Qed.
Lemma lem3583347 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term153 _91882 _91894 _91895 f g) = (term169 _91882 _91894 _91895 f g).
Proof. exact (fun_ext (fun y : _91894 -> _91882 => @lem3583346 _91882 _91894 _91895 y f g)). Qed.
Lemma lem3583348 {_91882 _91894 : Type'} : (@ex (_91894 -> _91882)) = (@ex (_91894 -> _91882)).
Proof. exact (eq_refl (@ex (_91894 -> _91882))). Qed.
Lemma lem3583349 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term154 _91882 _91894 _91895 f g) = (term170 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3583348 _91882 _91894) (@lem3583347 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583350 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term135 _91882 _91894 _91895 f g) = (term170 _91882 _91894 _91895 f g).
Proof. exact (TRANS (@lem3583326 _91882 _91894 _91895 f g) (@lem3583349 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583351 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term111 _91882 _91894 _91895 f g) = (term170 _91882 _91894 _91895 f g).
Proof. exact (TRANS (@lem3583302 _91882 _91894 _91895 f g) (@lem3583350 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583352 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3583353 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term113 _91882 _91894 _91895 f g) = (term171 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3583352) (@lem3583351 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583355 {A B : Type'} (P : type1413 A B) : (term0 A B P) = (term1 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3583356 {_91882 _91894 : Type'} (P : type1470 _91882 _91894) : (term28 _91882 _91894 P) = (term27 _91882 _91894 P).
Proof. exact (@lem3583355 _91894 _91882 P). Qed.
Lemma lem3583357 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term30 _91882 _91894 _91895 f g) = (term29 _91882 _91894 _91895 f g).
Proof. exact (@lem3583356 _91882 _91894 (term31 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583358 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term32 _91882 _91894 _91895 f g x) = (term33 _91882 _91894 _91895 f x g).
Proof. exact (eq_refl (term32 _91882 _91894 _91895 f g x)). Qed.
Lemma lem3583359 {_91882 : Type'} (h : _91882) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem3583360 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h : _91882) : (term41 _91882 _91894 _91895 f g x h) = (term42 _91882 _91894 _91895 f x g h).
Proof. exact (MK_COMB (@lem3583358 _91882 _91894 _91895 f x g) (@lem3583359 _91882 h)). Qed.
Lemma lem3583361 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h : _91882) : (term42 _91882 _91894 _91895 f x g h) = ((f x) = (g h)).
Proof. exact (eq_refl (term42 _91882 _91894 _91895 f x g h)). Qed.
Lemma lem3583362 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h : _91882) : (term41 _91882 _91894 _91895 f g x h) = ((f x) = (g h)).
Proof. exact (TRANS (@lem3583360 _91882 _91894 _91895 f x g h) (@lem3583361 _91882 _91894 _91895 f x g h)). Qed.
Lemma lem3583363 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term43 _91882 _91894 _91895 f g x) = (term33 _91882 _91894 _91895 f x g).
Proof. exact (fun_ext (fun h : _91882 => @lem3583362 _91882 _91894 _91895 f x g h)). Qed.
Lemma lem3583364 {_91882 : Type'} : (@ex _91882) = (@ex _91882).
Proof. exact (eq_refl (@ex _91882)). Qed.
Lemma lem3583365 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term44 _91882 _91894 _91895 f g x) = (term45 _91882 _91894 _91895 f x g).
Proof. exact (MK_COMB (@lem3583364 _91882) (@lem3583363 _91882 _91894 _91895 f x g)). Qed.
Lemma lem3583366 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term46 _91882 _91894 _91895 f g) = (term47 _91882 _91894 _91895 f g).
Proof. exact (fun_ext (fun x : _91894 => @lem3583365 _91882 _91894 _91895 f x g)). Qed.
Lemma lem3583367 {_91894 : Type'} : (@all _91894) = (@all _91894).
Proof. exact (eq_refl (@all _91894)). Qed.
Lemma lem3583368 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term30 _91882 _91894 _91895 f g) = (term48 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3583367 _91894) (@lem3583366 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583369 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3583370 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term172 _91882 _91894 _91895 f g) = (term173 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3583369) (@lem3583368 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583371 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term32 _91882 _91894 _91895 f g x) = (term33 _91882 _91894 _91895 f x g).
Proof. exact (eq_refl (term32 _91882 _91894 _91895 f g x)). Qed.
Lemma lem3583372 {_91882 _91894 : Type'} (h : _91894 -> _91882) (x : _91894) : (h x) = (h x).
Proof. exact (eq_refl (h x)). Qed.
Lemma lem3583373 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (x : _91894) : (term34 _91882 _91894 _91895 f g h x) = (term35 _91882 _91894 _91895 f g h x).
Proof. exact (MK_COMB (@lem3583371 _91882 _91894 _91895 f x g) (@lem3583372 _91882 _91894 h x)). Qed.
Lemma lem3583374 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (x : _91894) : (term35 _91882 _91894 _91895 f g h x) = ((f x) = (term18 _91882 _91894 _91895 g h x)).
Proof. exact (eq_refl (term35 _91882 _91894 _91895 f g h x)). Qed.
Lemma lem3583375 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (x : _91894) : (term34 _91882 _91894 _91895 f g h x) = ((f x) = (term18 _91882 _91894 _91895 g h x)).
Proof. exact (TRANS (@lem3583373 _91882 _91894 _91895 f g h x) (@lem3583374 _91882 _91894 _91895 f g h x)). Qed.
Lemma lem3583376 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) : (term36 _91882 _91894 _91895 f g h) = (term21 _91882 _91894 _91895 f g h).
Proof. exact (fun_ext (fun x : _91894 => @lem3583375 _91882 _91894 _91895 f g h x)). Qed.
Lemma lem3583377 {_91894 : Type'} : (@all _91894) = (@all _91894).
Proof. exact (eq_refl (@all _91894)). Qed.
Lemma lem3583378 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) : (term37 _91882 _91894 _91895 f g h) = (term22 _91882 _91894 _91895 f g h).
Proof. exact (MK_COMB (@lem3583377 _91894) (@lem3583376 _91882 _91894 _91895 f g h)). Qed.
Lemma lem3583379 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term38 _91882 _91894 _91895 f g) = (term24 _91882 _91894 _91895 f g).
Proof. exact (fun_ext (fun h : _91894 -> _91882 => @lem3583378 _91882 _91894 _91895 f g h)). Qed.
Lemma lem3583380 {_91882 _91894 : Type'} : (@ex (_91894 -> _91882)) = (@ex (_91894 -> _91882)).
Proof. exact (eq_refl (@ex (_91894 -> _91882))). Qed.
Lemma lem3583381 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term29 _91882 _91894 _91895 f g) = (term26 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3583380 _91882 _91894) (@lem3583379 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583382 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : ((term30 _91882 _91894 _91895 f g) = (term29 _91882 _91894 _91895 f g)) = ((term48 _91882 _91894 _91895 f g) = (term26 _91882 _91894 _91895 f g)).
Proof. exact (MK_COMB (@lem3583370 _91882 _91894 _91895 f g) (@lem3583381 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583383 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term48 _91882 _91894 _91895 f g) = (term26 _91882 _91894 _91895 f g).
Proof. exact (EQ_MP (@lem3583382 _91882 _91894 _91895 f g) (@lem3583357 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583384 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) : (term106 _91882 _91894 _91895 g f) = (term106 _91882 _91894 _91895 g f).
Proof. exact (eq_refl (term106 _91882 _91894 _91895 g f)). Qed.
Lemma lem3583385 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term108 _91882 _91894 _91895 f g) = (term174 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3583384 _91882 _91894 _91895 g f) (@lem3583383 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583387 {A : Type'} (P : A -> Prop) (Q : Prop) : (term136 A P Q) = (term137 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3583388 {_91894 : Type'} (P : _91894 -> Prop) (Q : Prop) : (term136 _91894 P Q) = (term137 _91894 P Q).
Proof. exact (@lem3583387 _91894 P Q). Qed.
Lemma lem3583389 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term175 _91882 _91894 _91895 f g) = (term176 _91882 _91894 _91895 f g).
Proof. exact (@lem3583388 _91894 (term89 _91882 _91894 _91895 g f) (term26 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583390 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) (x : _91894) : (term177 _91882 _91894 _91895 g f x) = (term81 _91882 _91894 _91895 g f x).
Proof. exact (eq_refl (term177 _91882 _91894 _91895 g f x)). Qed.
Lemma lem3583391 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) : (term178 _91882 _91894 _91895 g f) = (term89 _91882 _91894 _91895 g f).
Proof. exact (fun_ext (fun x : _91894 => @lem3583390 _91882 _91894 _91895 g f x)). Qed.
Lemma lem3583392 {_91894 : Type'} : (@ex _91894) = (@ex _91894).
Proof. exact (eq_refl (@ex _91894)). Qed.
Lemma lem3583393 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) : (term179 _91882 _91894 _91895 g f) = (term90 _91882 _91894 _91895 g f).
Proof. exact (MK_COMB (@lem3583392 _91894) (@lem3583391 _91882 _91894 _91895 g f)). Qed.
Lemma lem3583394 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3583395 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) : (term180 _91882 _91894 _91895 g f) = (term106 _91882 _91894 _91895 g f).
Proof. exact (MK_COMB (@lem3583394) (@lem3583393 _91882 _91894 _91895 g f)). Qed.
Lemma lem3583396 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term26 _91882 _91894 _91895 f g) = (term26 _91882 _91894 _91895 f g).
Proof. exact (eq_refl (term26 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583397 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term175 _91882 _91894 _91895 f g) = (term174 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3583395 _91882 _91894 _91895 g f) (@lem3583396 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583398 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3583399 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term181 _91882 _91894 _91895 f g) = (term182 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3583398) (@lem3583397 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583400 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) (x : _91894) : (term177 _91882 _91894 _91895 g f x) = (term81 _91882 _91894 _91895 g f x).
Proof. exact (eq_refl (term177 _91882 _91894 _91895 g f x)). Qed.
Lemma lem3583401 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3583402 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) (x : _91894) : (term183 _91882 _91894 _91895 g f x) = (term184 _91882 _91894 _91895 g f x).
Proof. exact (MK_COMB (@lem3583401) (@lem3583400 _91882 _91894 _91895 g f x)). Qed.
Lemma lem3583403 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term26 _91882 _91894 _91895 f g) = (term26 _91882 _91894 _91895 f g).
Proof. exact (eq_refl (term26 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583404 {_91882 _91894 _91895 : Type'} (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term185 _91882 _91894 _91895 x f g) = (term186 _91882 _91894 _91895 x f g).
Proof. exact (MK_COMB (@lem3583402 _91882 _91894 _91895 g f x) (@lem3583403 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583405 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term187 _91882 _91894 _91895 f g) = (term188 _91882 _91894 _91895 f g).
Proof. exact (fun_ext (fun x : _91894 => @lem3583404 _91882 _91894 _91895 x f g)). Qed.
Lemma lem3583406 {_91894 : Type'} : (@ex _91894) = (@ex _91894).
Proof. exact (eq_refl (@ex _91894)). Qed.
Lemma lem3583407 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term176 _91882 _91894 _91895 f g) = (term189 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3583406 _91894) (@lem3583405 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583408 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : ((term175 _91882 _91894 _91895 f g) = (term176 _91882 _91894 _91895 f g)) = ((term174 _91882 _91894 _91895 f g) = (term189 _91882 _91894 _91895 f g)).
Proof. exact (MK_COMB (@lem3583399 _91882 _91894 _91895 f g) (@lem3583407 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583409 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term174 _91882 _91894 _91895 f g) = (term189 _91882 _91894 _91895 f g).
Proof. exact (EQ_MP (@lem3583408 _91882 _91894 _91895 f g) (@lem3583389 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583411 {A : Type'} (P : Prop) (Q : A -> Prop) : (term155 A P Q) = (term156 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3583412 {_91882 _91894 : Type'} (P : Prop) (Q : type805 _91882 _91894) : (term190 _91882 _91894 P Q) = (term191 _91882 _91894 P Q).
Proof. exact (@lem3583411 (_91894 -> _91882) P Q). Qed.
Lemma lem3583413 {_91882 _91894 _91895 : Type'} (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term192 _91882 _91894 _91895 x f g) = (term193 _91882 _91894 _91895 x f g).
Proof. exact (@lem3583412 _91882 _91894 (term81 _91882 _91894 _91895 g f x) (term24 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583414 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) : (term194 _91882 _91894 _91895 f g h) = (term22 _91882 _91894 _91895 f g h).
Proof. exact (eq_refl (term194 _91882 _91894 _91895 f g h)). Qed.
Lemma lem3583415 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term195 _91882 _91894 _91895 f g) = (term24 _91882 _91894 _91895 f g).
Proof. exact (fun_ext (fun h : _91894 -> _91882 => @lem3583414 _91882 _91894 _91895 f g h)). Qed.
Lemma lem3583416 {_91882 _91894 : Type'} : (@ex (_91894 -> _91882)) = (@ex (_91894 -> _91882)).
Proof. exact (eq_refl (@ex (_91894 -> _91882))). Qed.
Lemma lem3583417 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term196 _91882 _91894 _91895 f g) = (term26 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3583416 _91882 _91894) (@lem3583415 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583418 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) (x : _91894) : (term184 _91882 _91894 _91895 g f x) = (term184 _91882 _91894 _91895 g f x).
Proof. exact (eq_refl (term184 _91882 _91894 _91895 g f x)). Qed.
Lemma lem3583419 {_91882 _91894 _91895 : Type'} (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term192 _91882 _91894 _91895 x f g) = (term186 _91882 _91894 _91895 x f g).
Proof. exact (MK_COMB (@lem3583418 _91882 _91894 _91895 g f x) (@lem3583417 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583420 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3583421 {_91882 _91894 _91895 : Type'} (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term197 _91882 _91894 _91895 x f g) = (term198 _91882 _91894 _91895 x f g).
Proof. exact (MK_COMB (@lem3583420) (@lem3583419 _91882 _91894 _91895 x f g)). Qed.
Lemma lem3583422 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) : (term194 _91882 _91894 _91895 f g h) = (term22 _91882 _91894 _91895 f g h).
Proof. exact (eq_refl (term194 _91882 _91894 _91895 f g h)). Qed.
Lemma lem3583423 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) (x : _91894) : (term184 _91882 _91894 _91895 g f x) = (term184 _91882 _91894 _91895 g f x).
Proof. exact (eq_refl (term184 _91882 _91894 _91895 g f x)). Qed.
Lemma lem3583424 {_91882 _91894 _91895 : Type'} (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) : (term199 _91882 _91894 _91895 x f g h) = (term200 _91882 _91894 _91895 x f g h).
Proof. exact (MK_COMB (@lem3583423 _91882 _91894 _91895 g f x) (@lem3583422 _91882 _91894 _91895 f g h)). Qed.
Lemma lem3583425 {_91882 _91894 _91895 : Type'} (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term201 _91882 _91894 _91895 x f g) = (term202 _91882 _91894 _91895 x f g).
Proof. exact (fun_ext (fun h : _91894 -> _91882 => @lem3583424 _91882 _91894 _91895 x f g h)). Qed.
Lemma lem3583426 {_91882 _91894 : Type'} : (@ex (_91894 -> _91882)) = (@ex (_91894 -> _91882)).
Proof. exact (eq_refl (@ex (_91894 -> _91882))). Qed.
Lemma lem3583427 {_91882 _91894 _91895 : Type'} (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term193 _91882 _91894 _91895 x f g) = (term203 _91882 _91894 _91895 x f g).
Proof. exact (MK_COMB (@lem3583426 _91882 _91894) (@lem3583425 _91882 _91894 _91895 x f g)). Qed.
Lemma lem3583428 {_91882 _91894 _91895 : Type'} (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) : ((term192 _91882 _91894 _91895 x f g) = (term193 _91882 _91894 _91895 x f g)) = ((term186 _91882 _91894 _91895 x f g) = (term203 _91882 _91894 _91895 x f g)).
Proof. exact (MK_COMB (@lem3583421 _91882 _91894 _91895 x f g) (@lem3583427 _91882 _91894 _91895 x f g)). Qed.
Lemma lem3583429 {_91882 _91894 _91895 : Type'} (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term186 _91882 _91894 _91895 x f g) = (term203 _91882 _91894 _91895 x f g).
Proof. exact (EQ_MP (@lem3583428 _91882 _91894 _91895 x f g) (@lem3583413 _91882 _91894 _91895 x f g)). Qed.
Lemma lem3583430 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term188 _91882 _91894 _91895 f g) = (term204 _91882 _91894 _91895 f g).
Proof. exact (fun_ext (fun x : _91894 => @lem3583429 _91882 _91894 _91895 x f g)). Qed.
Lemma lem3583431 {_91894 : Type'} : (@ex _91894) = (@ex _91894).
Proof. exact (eq_refl (@ex _91894)). Qed.
Lemma lem3583432 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term189 _91882 _91894 _91895 f g) = (term205 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3583431 _91894) (@lem3583430 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583433 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term174 _91882 _91894 _91895 f g) = (term205 _91882 _91894 _91895 f g).
Proof. exact (TRANS (@lem3583409 _91882 _91894 _91895 f g) (@lem3583432 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583434 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term108 _91882 _91894 _91895 f g) = (term205 _91882 _91894 _91895 f g).
Proof. exact (TRANS (@lem3583385 _91882 _91894 _91895 f g) (@lem3583433 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583435 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term115 _91882 _91894 _91895 f g) = (term206 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3583353 _91882 _91894 _91895 f g) (@lem3583434 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583439 {A : Type'} (P : A -> Prop) (Q : Prop) : (term207 A P Q) = (term208 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3583440 {_91882 _91894 : Type'} (P : type805 _91882 _91894) (Q : Prop) : (term209 _91882 _91894 P Q) = (term210 _91882 _91894 P Q).
Proof. exact (@lem3583439 (_91894 -> _91882) P Q). Qed.
Lemma lem3583441 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term211 _91882 _91894 _91895 f g) = (term212 _91882 _91894 _91895 f g).
Proof. exact (@lem3583440 _91882 _91894 (term169 _91882 _91894 _91895 f g) (term205 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583442 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term213 _91882 _91894 _91895 f g y) = (term168 _91882 _91894 _91895 y f g).
Proof. exact (eq_refl (term213 _91882 _91894 _91895 f g y)). Qed.
Lemma lem3583443 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term214 _91882 _91894 _91895 f g) = (term169 _91882 _91894 _91895 f g).
Proof. exact (fun_ext (fun y : _91894 -> _91882 => @lem3583442 _91882 _91894 _91895 y f g)). Qed.
Lemma lem3583444 {_91882 _91894 : Type'} : (@ex (_91894 -> _91882)) = (@ex (_91894 -> _91882)).
Proof. exact (eq_refl (@ex (_91894 -> _91882))). Qed.
Lemma lem3583445 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term215 _91882 _91894 _91895 f g) = (term170 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3583444 _91882 _91894) (@lem3583443 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583446 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3583447 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term216 _91882 _91894 _91895 f g) = (term171 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3583446) (@lem3583445 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583448 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term205 _91882 _91894 _91895 f g) = (term205 _91882 _91894 _91895 f g).
Proof. exact (eq_refl (term205 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583449 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term211 _91882 _91894 _91895 f g) = (term206 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3583447 _91882 _91894 _91895 f g) (@lem3583448 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583450 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3583451 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term217 _91882 _91894 _91895 f g) = (term218 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3583450) (@lem3583449 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583452 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term213 _91882 _91894 _91895 f g y) = (term168 _91882 _91894 _91895 y f g).
Proof. exact (eq_refl (term213 _91882 _91894 _91895 f g y)). Qed.
Lemma lem3583453 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3583454 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term219 _91882 _91894 _91895 f g y) = (term220 _91882 _91894 _91895 y f g).
Proof. exact (MK_COMB (@lem3583453) (@lem3583452 _91882 _91894 _91895 y f g)). Qed.
Lemma lem3583455 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term205 _91882 _91894 _91895 f g) = (term205 _91882 _91894 _91895 f g).
Proof. exact (eq_refl (term205 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583456 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term221 _91882 _91894 _91895 y f g) = (term222 _91882 _91894 _91895 y f g).
Proof. exact (MK_COMB (@lem3583454 _91882 _91894 _91895 y f g) (@lem3583455 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583457 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term223 _91882 _91894 _91895 f g) = (term224 _91882 _91894 _91895 f g).
Proof. exact (fun_ext (fun y : _91894 -> _91882 => @lem3583456 _91882 _91894 _91895 y f g)). Qed.
Lemma lem3583458 {_91882 _91894 : Type'} : (@ex (_91894 -> _91882)) = (@ex (_91894 -> _91882)).
Proof. exact (eq_refl (@ex (_91894 -> _91882))). Qed.
Lemma lem3583459 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term212 _91882 _91894 _91895 f g) = (term225 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3583458 _91882 _91894) (@lem3583457 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583460 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : ((term211 _91882 _91894 _91895 f g) = (term212 _91882 _91894 _91895 f g)) = ((term206 _91882 _91894 _91895 f g) = (term225 _91882 _91894 _91895 f g)).
Proof. exact (MK_COMB (@lem3583451 _91882 _91894 _91895 f g) (@lem3583459 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583461 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term206 _91882 _91894 _91895 f g) = (term225 _91882 _91894 _91895 f g).
Proof. exact (EQ_MP (@lem3583460 _91882 _91894 _91895 f g) (@lem3583441 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583463 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term226 A P Q) = (term227 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3583464 {_91894 : Type'} (P : _91894 -> Prop) (Q : _91894 -> Prop) : (term226 _91894 P Q) = (term227 _91894 P Q).
Proof. exact (@lem3583463 _91894 P Q). Qed.
Lemma lem3583465 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term228 _91882 _91894 _91895 y f g) = (term229 _91882 _91894 _91895 y f g).
Proof. exact (@lem3583464 _91894 (term167 _91882 _91894 _91895 y f g) (term204 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583466 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term230 _91882 _91894 _91895 y f g x) = (term165 _91882 _91894 _91895 y f x g).
Proof. exact (eq_refl (term230 _91882 _91894 _91895 y f g x)). Qed.
Lemma lem3583467 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term231 _91882 _91894 _91895 y f g) = (term167 _91882 _91894 _91895 y f g).
Proof. exact (fun_ext (fun x : _91894 => @lem3583466 _91882 _91894 _91895 y f x g)). Qed.
Lemma lem3583468 {_91894 : Type'} : (@ex _91894) = (@ex _91894).
Proof. exact (eq_refl (@ex _91894)). Qed.
Lemma lem3583469 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term232 _91882 _91894 _91895 y f g) = (term168 _91882 _91894 _91895 y f g).
Proof. exact (MK_COMB (@lem3583468 _91894) (@lem3583467 _91882 _91894 _91895 y f g)). Qed.
Lemma lem3583470 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3583471 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term233 _91882 _91894 _91895 y f g) = (term220 _91882 _91894 _91895 y f g).
Proof. exact (MK_COMB (@lem3583470) (@lem3583469 _91882 _91894 _91895 y f g)). Qed.
Lemma lem3583472 {_91882 _91894 _91895 : Type'} (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term234 _91882 _91894 _91895 f g x) = (term203 _91882 _91894 _91895 x f g).
Proof. exact (eq_refl (term234 _91882 _91894 _91895 f g x)). Qed.
Lemma lem3583473 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term235 _91882 _91894 _91895 f g) = (term204 _91882 _91894 _91895 f g).
Proof. exact (fun_ext (fun x : _91894 => @lem3583472 _91882 _91894 _91895 x f g)). Qed.
Lemma lem3583474 {_91894 : Type'} : (@ex _91894) = (@ex _91894).
Proof. exact (eq_refl (@ex _91894)). Qed.
Lemma lem3583475 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term236 _91882 _91894 _91895 f g) = (term205 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3583474 _91894) (@lem3583473 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583476 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term228 _91882 _91894 _91895 y f g) = (term222 _91882 _91894 _91895 y f g).
Proof. exact (MK_COMB (@lem3583471 _91882 _91894 _91895 y f g) (@lem3583475 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583477 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3583478 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term237 _91882 _91894 _91895 y f g) = (term238 _91882 _91894 _91895 y f g).
Proof. exact (MK_COMB (@lem3583477) (@lem3583476 _91882 _91894 _91895 y f g)). Qed.
Lemma lem3583479 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term230 _91882 _91894 _91895 y f g x) = (term165 _91882 _91894 _91895 y f x g).
Proof. exact (eq_refl (term230 _91882 _91894 _91895 y f g x)). Qed.
Lemma lem3583480 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3583481 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term239 _91882 _91894 _91895 y f g x) = (term240 _91882 _91894 _91895 y f x g).
Proof. exact (MK_COMB (@lem3583480) (@lem3583479 _91882 _91894 _91895 y f x g)). Qed.
Lemma lem3583482 {_91882 _91894 _91895 : Type'} (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term234 _91882 _91894 _91895 f g x) = (term203 _91882 _91894 _91895 x f g).
Proof. exact (eq_refl (term234 _91882 _91894 _91895 f g x)). Qed.
Lemma lem3583483 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term241 _91882 _91894 _91895 y f g x) = (term242 _91882 _91894 _91895 y x f g).
Proof. exact (MK_COMB (@lem3583481 _91882 _91894 _91895 y f x g) (@lem3583482 _91882 _91894 _91895 x f g)). Qed.
Lemma lem3583484 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term243 _91882 _91894 _91895 y f g) = (term244 _91882 _91894 _91895 y f g).
Proof. exact (fun_ext (fun x : _91894 => @lem3583483 _91882 _91894 _91895 y x f g)). Qed.
Lemma lem3583485 {_91894 : Type'} : (@ex _91894) = (@ex _91894).
Proof. exact (eq_refl (@ex _91894)). Qed.
Lemma lem3583486 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term229 _91882 _91894 _91895 y f g) = (term245 _91882 _91894 _91895 y f g).
Proof. exact (MK_COMB (@lem3583485 _91894) (@lem3583484 _91882 _91894 _91895 y f g)). Qed.
Lemma lem3583487 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (g : _91882 -> _91895) : ((term228 _91882 _91894 _91895 y f g) = (term229 _91882 _91894 _91895 y f g)) = ((term222 _91882 _91894 _91895 y f g) = (term245 _91882 _91894 _91895 y f g)).
Proof. exact (MK_COMB (@lem3583478 _91882 _91894 _91895 y f g) (@lem3583486 _91882 _91894 _91895 y f g)). Qed.
Lemma lem3583488 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term222 _91882 _91894 _91895 y f g) = (term245 _91882 _91894 _91895 y f g).
Proof. exact (EQ_MP (@lem3583487 _91882 _91894 _91895 y f g) (@lem3583465 _91882 _91894 _91895 y f g)). Qed.
Lemma lem3583490 {A : Type'} (P : Prop) (Q : A -> Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3583491 {_91882 _91894 : Type'} (P : Prop) (Q : type805 _91882 _91894) : (term248 _91882 _91894 P Q) = (term249 _91882 _91894 P Q).
Proof. exact (@lem3583490 (_91894 -> _91882) P Q). Qed.
Lemma lem3583492 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term250 _91882 _91894 _91895 y x f g) = (term251 _91882 _91894 _91895 y x f g).
Proof. exact (@lem3583491 _91882 _91894 (term165 _91882 _91894 _91895 y f x g) (term202 _91882 _91894 _91895 x f g)). Qed.
Lemma lem3583493 {_91882 _91894 _91895 : Type'} (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) : (term252 _91882 _91894 _91895 x f g h) = (term200 _91882 _91894 _91895 x f g h).
Proof. exact (eq_refl (term252 _91882 _91894 _91895 x f g h)). Qed.
Lemma lem3583494 {_91882 _91894 _91895 : Type'} (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term253 _91882 _91894 _91895 x f g) = (term202 _91882 _91894 _91895 x f g).
Proof. exact (fun_ext (fun h : _91894 -> _91882 => @lem3583493 _91882 _91894 _91895 x f g h)). Qed.
Lemma lem3583495 {_91882 _91894 : Type'} : (@ex (_91894 -> _91882)) = (@ex (_91894 -> _91882)).
Proof. exact (eq_refl (@ex (_91894 -> _91882))). Qed.
Lemma lem3583496 {_91882 _91894 _91895 : Type'} (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term254 _91882 _91894 _91895 x f g) = (term203 _91882 _91894 _91895 x f g).
Proof. exact (MK_COMB (@lem3583495 _91882 _91894) (@lem3583494 _91882 _91894 _91895 x f g)). Qed.
Lemma lem3583497 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term240 _91882 _91894 _91895 y f x g) = (term240 _91882 _91894 _91895 y f x g).
Proof. exact (eq_refl (term240 _91882 _91894 _91895 y f x g)). Qed.
Lemma lem3583498 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term250 _91882 _91894 _91895 y x f g) = (term242 _91882 _91894 _91895 y x f g).
Proof. exact (MK_COMB (@lem3583497 _91882 _91894 _91895 y f x g) (@lem3583496 _91882 _91894 _91895 x f g)). Qed.
Lemma lem3583499 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3583500 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term255 _91882 _91894 _91895 y x f g) = (term256 _91882 _91894 _91895 y x f g).
Proof. exact (MK_COMB (@lem3583499) (@lem3583498 _91882 _91894 _91895 y x f g)). Qed.
Lemma lem3583501 {_91882 _91894 _91895 : Type'} (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) : (term252 _91882 _91894 _91895 x f g h) = (term200 _91882 _91894 _91895 x f g h).
Proof. exact (eq_refl (term252 _91882 _91894 _91895 x f g h)). Qed.
Lemma lem3583502 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term240 _91882 _91894 _91895 y f x g) = (term240 _91882 _91894 _91895 y f x g).
Proof. exact (eq_refl (term240 _91882 _91894 _91895 y f x g)). Qed.
Lemma lem3583503 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) : (term257 _91882 _91894 _91895 y x f g h) = (term258 _91882 _91894 _91895 y x f g h).
Proof. exact (MK_COMB (@lem3583502 _91882 _91894 _91895 y f x g) (@lem3583501 _91882 _91894 _91895 x f g h)). Qed.
Lemma lem3583504 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term259 _91882 _91894 _91895 y x f g) = (term260 _91882 _91894 _91895 y x f g).
Proof. exact (fun_ext (fun h : _91894 -> _91882 => @lem3583503 _91882 _91894 _91895 y x f g h)). Qed.
Lemma lem3583505 {_91882 _91894 : Type'} : (@ex (_91894 -> _91882)) = (@ex (_91894 -> _91882)).
Proof. exact (eq_refl (@ex (_91894 -> _91882))). Qed.
Lemma lem3583506 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term251 _91882 _91894 _91895 y x f g) = (term261 _91882 _91894 _91895 y x f g).
Proof. exact (MK_COMB (@lem3583505 _91882 _91894) (@lem3583504 _91882 _91894 _91895 y x f g)). Qed.
Lemma lem3583507 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) : ((term250 _91882 _91894 _91895 y x f g) = (term251 _91882 _91894 _91895 y x f g)) = ((term242 _91882 _91894 _91895 y x f g) = (term261 _91882 _91894 _91895 y x f g)).
Proof. exact (MK_COMB (@lem3583500 _91882 _91894 _91895 y x f g) (@lem3583506 _91882 _91894 _91895 y x f g)). Qed.
Lemma lem3583508 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term242 _91882 _91894 _91895 y x f g) = (term261 _91882 _91894 _91895 y x f g).
Proof. exact (EQ_MP (@lem3583507 _91882 _91894 _91895 y x f g) (@lem3583492 _91882 _91894 _91895 y x f g)). Qed.
Lemma lem3583509 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term244 _91882 _91894 _91895 y f g) = (term262 _91882 _91894 _91895 y f g).
Proof. exact (fun_ext (fun x : _91894 => @lem3583508 _91882 _91894 _91895 y x f g)). Qed.
Lemma lem3583510 {_91894 : Type'} : (@ex _91894) = (@ex _91894).
Proof. exact (eq_refl (@ex _91894)). Qed.
Lemma lem3583511 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term245 _91882 _91894 _91895 y f g) = (term263 _91882 _91894 _91895 y f g).
Proof. exact (MK_COMB (@lem3583510 _91894) (@lem3583509 _91882 _91894 _91895 y f g)). Qed.
Lemma lem3583512 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (g : _91882 -> _91895) : (term222 _91882 _91894 _91895 y f g) = (term263 _91882 _91894 _91895 y f g).
Proof. exact (TRANS (@lem3583488 _91882 _91894 _91895 y f g) (@lem3583511 _91882 _91894 _91895 y f g)). Qed.
Lemma lem3583513 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term224 _91882 _91894 _91895 f g) = (term264 _91882 _91894 _91895 f g).
Proof. exact (fun_ext (fun y : _91894 -> _91882 => @lem3583512 _91882 _91894 _91895 y f g)). Qed.
Lemma lem3583514 {_91882 _91894 : Type'} : (@ex (_91894 -> _91882)) = (@ex (_91894 -> _91882)).
Proof. exact (eq_refl (@ex (_91894 -> _91882))). Qed.
Lemma lem3583515 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term225 _91882 _91894 _91895 f g) = (term265 _91882 _91894 _91895 f g).
Proof. exact (MK_COMB (@lem3583514 _91882 _91894) (@lem3583513 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583516 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term206 _91882 _91894 _91895 f g) = (term265 _91882 _91894 _91895 f g).
Proof. exact (TRANS (@lem3583461 _91882 _91894 _91895 f g) (@lem3583515 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583518 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term115 _91882 _91894 _91895 f g) = (term265 _91882 _91894 _91895 f g).
Proof. exact (TRANS (@lem3583435 _91882 _91894 _91895 f g) (@lem3583516 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583519 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term71 _91882 _91894 _91895 f g) = (term265 _91882 _91894 _91895 f g).
Proof. exact (TRANS (@lem3583235 _91882 _91894 _91895 f g) (@lem3583518 _91882 _91894 _91895 f g)). Qed.
Lemma lem3583520 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) (h1 : term71 _91882 _91894 _91895 f g) : term265 _91882 _91894 _91895 f g.
Proof. exact (EQ_MP (@lem3583519 _91882 _91894 _91895 f g) (@lem3583168 _91882 _91894 _91895 f g h1)). Qed.
Lemma lem3583521 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (g : _91882 -> _91895) (h1 : term263 _91882 _91894 _91895 y f g) : term263 _91882 _91894 _91895 y f g.
Proof. exact (h1). Qed.
Lemma lem3583522 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h1 : term261 _91882 _91894 _91895 y x f g) : term261 _91882 _91894 _91895 y x f g.
Proof. exact (h1). Qed.
Lemma lem3583523 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (h1 : term258 _91882 _91894 _91895 y x f g h) : term258 _91882 _91894 _91895 y x f g h.
Proof. exact (h1). Qed.
Lemma lem3583534 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (x : _91894) : ((f x) = (term18 _91882 _91894 _91895 g h x)) = ((f x) = (term18 _91882 _91894 _91895 g h x)).
Proof. exact (eq_refl ((f x) = (term18 _91882 _91894 _91895 g h x))). Qed.
Lemma lem3583535 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) : (term21 _91882 _91894 _91895 f g h) = (term21 _91882 _91894 _91895 f g h).
Proof. exact (fun_ext (fun x : _91894 => @lem3583534 _91882 _91894 _91895 f g h x)). Qed.
Lemma lem3583536 {_91894 : Type'} : (@all _91894) = (@all _91894).
Proof. exact (eq_refl (@all _91894)). Qed.
Lemma lem3583537 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) : (term22 _91882 _91894 _91895 f g h) = (term22 _91882 _91894 _91895 f g h).
Proof. exact (MK_COMB (@lem3583536 _91894) (@lem3583535 _91882 _91894 _91895 f g h)). Qed.
Lemma lem3583548 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (y : _91882) (f : _91894 -> _91895) (x : _91894) : (term78 _91882 _91894 _91895 g y f x) = (term78 _91882 _91894 _91895 g y f x).
Proof. exact (eq_refl (term78 _91882 _91894 _91895 g y f x)). Qed.
Lemma lem3583549 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) (x : _91894) : (term80 _91882 _91894 _91895 g f x) = (term80 _91882 _91894 _91895 g f x).
Proof. exact (fun_ext (fun y : _91882 => @lem3583548 _91882 _91894 _91895 g y f x)). Qed.
Lemma lem3583550 {_91882 : Type'} : (@all _91882) = (@all _91882).
Proof. exact (eq_refl (@all _91882)). Qed.
Lemma lem3583551 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) (x : _91894) : (term81 _91882 _91894 _91895 g f x) = (term81 _91882 _91894 _91895 g f x).
Proof. exact (MK_COMB (@lem3583550 _91882) (@lem3583549 _91882 _91894 _91895 g f x)). Qed.
Lemma lem3583552 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3583553 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) (x : _91894) : (term184 _91882 _91894 _91895 g f x) = (term184 _91882 _91894 _91895 g f x).
Proof. exact (MK_COMB (@lem3583552) (@lem3583551 _91882 _91894 _91895 g f x)). Qed.
Lemma lem3583554 {_91882 _91894 _91895 : Type'} (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) : (term200 _91882 _91894 _91895 x f g h) = (term200 _91882 _91894 _91895 x f g h).
Proof. exact (MK_COMB (@lem3583553 _91882 _91894 _91895 g f x) (@lem3583537 _91882 _91894 _91895 f g h)). Qed.
Lemma lem3583565 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h : _91882) : (term94 _91882 _91894 _91895 f x g h) = (term94 _91882 _91894 _91895 f x g h).
Proof. exact (eq_refl (term94 _91882 _91894 _91895 f x g h)). Qed.
Lemma lem3583566 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term96 _91882 _91894 _91895 f x g) = (term96 _91882 _91894 _91895 f x g).
Proof. exact (fun_ext (fun h : _91882 => @lem3583565 _91882 _91894 _91895 f x g h)). Qed.
Lemma lem3583567 {_91882 : Type'} : (@all _91882) = (@all _91882).
Proof. exact (eq_refl (@all _91882)). Qed.
Lemma lem3583568 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term97 _91882 _91894 _91895 f x g) = (term97 _91882 _91894 _91895 f x g).
Proof. exact (MK_COMB (@lem3583567 _91882) (@lem3583566 _91882 _91894 _91895 f x g)). Qed.
Lemma lem3583579 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) : ((term18 _91882 _91894 _91895 g y x) = (f x)) = ((term18 _91882 _91894 _91895 g y x) = (f x)).
Proof. exact (eq_refl ((term18 _91882 _91894 _91895 g y x) = (f x))). Qed.
Lemma lem3583580 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (y : _91894 -> _91882) (f : _91894 -> _91895) : (term128 _91882 _91894 _91895 g y f) = (term128 _91882 _91894 _91895 g y f).
Proof. exact (fun_ext (fun x : _91894 => @lem3583579 _91882 _91894 _91895 g y f x)). Qed.
Lemma lem3583581 {_91894 : Type'} : (@all _91894) = (@all _91894).
Proof. exact (eq_refl (@all _91894)). Qed.
Lemma lem3583582 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (y : _91894 -> _91882) (f : _91894 -> _91895) : (term130 _91882 _91894 _91895 g y f) = (term130 _91882 _91894 _91895 g y f).
Proof. exact (MK_COMB (@lem3583581 _91894) (@lem3583580 _91882 _91894 _91895 g y f)). Qed.
Lemma lem3583583 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3583584 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (y : _91894 -> _91882) (f : _91894 -> _91895) : (term149 _91882 _91894 _91895 g y f) = (term149 _91882 _91894 _91895 g y f).
Proof. exact (MK_COMB (@lem3583583) (@lem3583582 _91882 _91894 _91895 g y f)). Qed.
Lemma lem3583585 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term165 _91882 _91894 _91895 y f x g) = (term165 _91882 _91894 _91895 y f x g).
Proof. exact (MK_COMB (@lem3583584 _91882 _91894 _91895 g y f) (@lem3583568 _91882 _91894 _91895 f x g)). Qed.
Lemma lem3583586 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3583587 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term240 _91882 _91894 _91895 y f x g) = (term240 _91882 _91894 _91895 y f x g).
Proof. exact (MK_COMB (@lem3583586) (@lem3583585 _91882 _91894 _91895 y f x g)). Qed.
Lemma lem3583588 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) : (term258 _91882 _91894 _91895 y x f g h) = (term258 _91882 _91894 _91895 y x f g h).
Proof. exact (MK_COMB (@lem3583587 _91882 _91894 _91895 y f x g) (@lem3583554 _91882 _91894 _91895 x f g h)). Qed.
Lemma lem3583589 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (h1 : term258 _91882 _91894 _91895 y x f g h) : term258 _91882 _91894 _91895 y x f g h.
Proof. exact (EQ_MP (@lem3583588 _91882 _91894 _91895 y x f g h) (@lem3583523 _91882 _91894 _91895 y x f g h h1)). Qed.
Lemma lem3583590 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h1 : term165 _91882 _91894 _91895 y f x g) : term165 _91882 _91894 _91895 y f x g.
Proof. exact (h1). Qed.
Lemma lem3583591 {_91882 _91894 _91895 : Type'} (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (h1 : term200 _91882 _91894 _91895 x f g h) : term200 _91882 _91894 _91895 x f g h.
Proof. exact (h1). Qed.
Lemma lem3583592 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h1 : term165 _91882 _91894 _91895 y f x g) : term97 _91882 _91894 _91895 f x g.
Proof. exact (proj2 (@lem3583590 _91882 _91894 _91895 y f x g h1)). Qed.
Lemma lem3583593 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h1 : term165 _91882 _91894 _91895 y f x g) : term130 _91882 _91894 _91895 g y f.
Proof. exact (proj1 (@lem3583590 _91882 _91894 _91895 y f x g h1)). Qed.
Lemma lem3583594 {_91882 _91894 _91895 : Type'} (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (h1 : term200 _91882 _91894 _91895 x f g h) : term22 _91882 _91894 _91895 f g h.
Proof. exact (proj2 (@lem3583591 _91882 _91894 _91895 x f g h h1)). Qed.
Lemma lem3583595 {_91882 _91894 _91895 : Type'} (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (h1 : term200 _91882 _91894 _91895 x f g h) : term81 _91882 _91894 _91895 g f x.
Proof. exact (proj1 (@lem3583591 _91882 _91894 _91895 x f g h h1)). Qed.
Lemma lem3583597 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) : ((term18 _91882 _91894 _91895 g y x) = (f x)) = ((term18 _91882 _91894 _91895 g y x) = (f x)).
Proof. exact (eq_refl ((term18 _91882 _91894 _91895 g y x) = (f x))). Qed.
Lemma lem3583598 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (y : _91894 -> _91882) (f : _91894 -> _91895) : (term128 _91882 _91894 _91895 g y f) = (term128 _91882 _91894 _91895 g y f).
Proof. exact (fun_ext (fun x : _91894 => @lem3583597 _91882 _91894 _91895 g y f x)). Qed.
Lemma lem3583599 {_91894 : Type'} : (@all _91894) = (@all _91894).
Proof. exact (eq_refl (@all _91894)). Qed.
Lemma lem3583601 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (y : _91894 -> _91882) (f : _91894 -> _91895) : (term130 _91882 _91894 _91895 g y f) = (term130 _91882 _91894 _91895 g y f).
Proof. exact (MK_COMB (@lem3583599 _91894) (@lem3583598 _91882 _91894 _91895 g y f)). Qed.
Lemma lem3583602 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h1 : term165 _91882 _91894 _91895 y f x g) : term130 _91882 _91894 _91895 g y f.
Proof. exact (EQ_MP (@lem3583601 _91882 _91894 _91895 g y f) (@lem3583593 _91882 _91894 _91895 y f x g h1)). Qed.
Lemma lem3583604 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h : _91882) : (term94 _91882 _91894 _91895 f x g h) = (term94 _91882 _91894 _91895 f x g h).
Proof. exact (eq_refl (term94 _91882 _91894 _91895 f x g h)). Qed.
Lemma lem3583605 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term96 _91882 _91894 _91895 f x g) = (term96 _91882 _91894 _91895 f x g).
Proof. exact (fun_ext (fun h : _91882 => @lem3583604 _91882 _91894 _91895 f x g h)). Qed.
Lemma lem3583606 {_91882 : Type'} : (@all _91882) = (@all _91882).
Proof. exact (eq_refl (@all _91882)). Qed.
Lemma lem3583608 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) : (term97 _91882 _91894 _91895 f x g) = (term97 _91882 _91894 _91895 f x g).
Proof. exact (MK_COMB (@lem3583606 _91882) (@lem3583605 _91882 _91894 _91895 f x g)). Qed.
Lemma lem3583609 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h1 : term165 _91882 _91894 _91895 y f x g) : term97 _91882 _91894 _91895 f x g.
Proof. exact (EQ_MP (@lem3583608 _91882 _91894 _91895 f x g) (@lem3583592 _91882 _91894 _91895 y f x g h1)). Qed.
Lemma lem3583611 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (y : _91882) (f : _91894 -> _91895) (x : _91894) : (term78 _91882 _91894 _91895 g y f x) = (term78 _91882 _91894 _91895 g y f x).
Proof. exact (eq_refl (term78 _91882 _91894 _91895 g y f x)). Qed.
Lemma lem3583612 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) (x : _91894) : (term80 _91882 _91894 _91895 g f x) = (term80 _91882 _91894 _91895 g f x).
Proof. exact (fun_ext (fun y : _91882 => @lem3583611 _91882 _91894 _91895 g y f x)). Qed.
Lemma lem3583613 {_91882 : Type'} : (@all _91882) = (@all _91882).
Proof. exact (eq_refl (@all _91882)). Qed.
Lemma lem3583615 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (f : _91894 -> _91895) (x : _91894) : (term81 _91882 _91894 _91895 g f x) = (term81 _91882 _91894 _91895 g f x).
Proof. exact (MK_COMB (@lem3583613 _91882) (@lem3583612 _91882 _91894 _91895 g f x)). Qed.
Lemma lem3583616 {_91882 _91894 _91895 : Type'} (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (h1 : term200 _91882 _91894 _91895 x f g h) : term81 _91882 _91894 _91895 g f x.
Proof. exact (EQ_MP (@lem3583615 _91882 _91894 _91895 g f x) (@lem3583595 _91882 _91894 _91895 x f g h h1)). Qed.
Lemma lem3583618 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (x : _91894) : ((f x) = (term18 _91882 _91894 _91895 g h x)) = ((f x) = (term18 _91882 _91894 _91895 g h x)).
Proof. exact (eq_refl ((f x) = (term18 _91882 _91894 _91895 g h x))). Qed.
Lemma lem3583619 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) : (term21 _91882 _91894 _91895 f g h) = (term21 _91882 _91894 _91895 f g h).
Proof. exact (fun_ext (fun x : _91894 => @lem3583618 _91882 _91894 _91895 f g h x)). Qed.
Lemma lem3583620 {_91894 : Type'} : (@all _91894) = (@all _91894).
Proof. exact (eq_refl (@all _91894)). Qed.
Lemma lem3583622 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) : (term22 _91882 _91894 _91895 f g h) = (term22 _91882 _91894 _91895 f g h).
Proof. exact (MK_COMB (@lem3583620 _91894) (@lem3583619 _91882 _91894 _91895 f g h)). Qed.
Lemma lem3583623 {_91882 _91894 _91895 : Type'} (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (h1 : term200 _91882 _91894 _91895 x f g h) : term22 _91882 _91894 _91895 f g h.
Proof. exact (EQ_MP (@lem3583622 _91882 _91894 _91895 f g h) (@lem3583594 _91882 _91894 _91895 x f g h h1)). Qed.
Lemma lem3583624 {_91882 _91894 _91895 : Type'} (_38683 : _91894) (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h1 : term165 _91882 _91894 _91895 y f x g) : term266 _91882 _91894 _91895 g y f _38683.
Proof. exact (@lem3583602 _91882 _91894 _91895 y f x g h1 _38683). Qed.
Lemma lem3583625 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (y : _91894 -> _91882) (f : _91894 -> _91895) (_38683 : _91894) : (term266 _91882 _91894 _91895 g y f _38683) = ((term18 _91882 _91894 _91895 g y _38683) = (f _38683)).
Proof. exact (eq_refl (term266 _91882 _91894 _91895 g y f _38683)). Qed.
Lemma lem3583627 {_91882 _91894 _91895 : Type'} (_38684 : _91882) (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h1 : term165 _91882 _91894 _91895 y f x g) : term267 _91882 _91894 _91895 f x g _38684.
Proof. exact (@lem3583609 _91882 _91894 _91895 y f x g h1 _38684). Qed.
Lemma lem3583628 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (_38684 : _91882) : (term267 _91882 _91894 _91895 f x g _38684) = (term94 _91882 _91894 _91895 f x g _38684).
Proof. exact (eq_refl (term267 _91882 _91894 _91895 f x g _38684)). Qed.
Lemma lem3583630 {_91882 _91894 _91895 : Type'} (_38685 : _91882) (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (h1 : term200 _91882 _91894 _91895 x f g h) : term268 _91882 _91894 _91895 g f x _38685.
Proof. exact (@lem3583616 _91882 _91894 _91895 x f g h h1 _38685). Qed.
Lemma lem3583631 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (_38685 : _91882) (f : _91894 -> _91895) (x : _91894) : (term268 _91882 _91894 _91895 g f x _38685) = (term78 _91882 _91894 _91895 g _38685 f x).
Proof. exact (eq_refl (term268 _91882 _91894 _91895 g f x _38685)). Qed.
Lemma lem3583633 {_91882 _91894 _91895 : Type'} (_38686 : _91894) (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (h1 : term200 _91882 _91894 _91895 x f g h) : term269 _91882 _91894 _91895 f g h _38686.
Proof. exact (@lem3583623 _91882 _91894 _91895 x f g h h1 _38686). Qed.
Lemma lem3583634 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (_38686 : _91894) : (term269 _91882 _91894 _91895 f g h _38686) = ((f _38686) = (term18 _91882 _91894 _91895 g h _38686)).
Proof. exact (eq_refl (term269 _91882 _91894 _91895 f g h _38686)). Qed.
Lemma lem3583639 {_91882 _91894 _91895 : Type'} (_38684 : _91882) (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h1 : term165 _91882 _91894 _91895 y f x g) : term94 _91882 _91894 _91895 f x g _38684.
Proof. exact (EQ_MP (@lem3583628 _91882 _91894 _91895 f x g _38684) (@lem3583627 _91882 _91894 _91895 _38684 y f x g h1)). Qed.
Lemma lem3583641 {_91882 _91894 _91895 : Type'} (_38685 : _91882) (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (h1 : term200 _91882 _91894 _91895 x f g h) : term78 _91882 _91894 _91895 g _38685 f x.
Proof. exact (EQ_MP (@lem3583631 _91882 _91894 _91895 g _38685 f x) (@lem3583630 _91882 _91894 _91895 _38685 x f g h h1)). Qed.
Lemma lem3583669 {_91895 : Type'} (x : _91895) (y : _91895) (z : _91895) : term270 _91895 x y z.
Proof. exact (@lem21385 _91895 x y z). Qed.
Lemma lem3583675 {_91882 _91894 _91895 : Type'} (_38683 : _91894) (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h1 : term165 _91882 _91894 _91895 y f x g) : (term18 _91882 _91894 _91895 g y _38683) = (f _38683).
Proof. exact (EQ_MP (@lem3583625 _91882 _91894 _91895 g y f _38683) (@lem3583624 _91882 _91894 _91895 _38683 y f x g h1)). Qed.
Lemma lem3583676 {_91882 _91894 _91895 : Type'} (_38683 : _91894) (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h1 : term165 _91882 _91894 _91895 y f x g) : (term18 _91882 _91894 _91895 g y _38683) = (f _38683).
Proof. exact (@lem3583675 _91882 _91894 _91895 _38683 y f x g h1). Qed.
Lemma lem3583677 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h1 : term165 _91882 _91894 _91895 y f x g) : (term18 _91882 _91894 _91895 g y x) = (f x).
Proof. exact (@lem3583676 _91882 _91894 _91895 x y f x g h1). Qed.
Lemma lem3583678 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h1 : term165 _91882 _91894 _91895 y f x g) : term271 _91882 _91894 _91895 g y f x.
Proof. exact (fun h0 : term272 _91882 _91894 _91895 g y f x => @lem3583677 _91882 _91894 _91895 y f x g h1). Qed.
Lemma lem3583680 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3583681 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) : (term271 _91882 _91894 _91895 g y f x) = ((term18 _91882 _91894 _91895 g y x) = (f x)).
Proof. exact (@lem3583680 ((term18 _91882 _91894 _91895 g y x) = (f x))). Qed.
Lemma lem3583682 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h1 : term165 _91882 _91894 _91895 y f x g) : (term18 _91882 _91894 _91895 g y x) = (f x).
Proof. exact (EQ_MP (@lem3583681 _91882 _91894 _91895 g y f x) (@lem3583678 _91882 _91894 _91895 y f x g h1)). Qed.
Lemma lem3583684 {_91895 : Type'} (x : _91895) : x = x.
Proof. exact (@lem21386 _91895 x). Qed.
Lemma lem3583685 {_91895 : Type'} (x : _91895) : x = x.
Proof. exact (@lem3583684 _91895 x). Qed.
Lemma lem3583686 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (y : _91894 -> _91882) (x : _91894) : (term18 _91882 _91894 _91895 g y x) = (term18 _91882 _91894 _91895 g y x).
Proof. exact (@lem3583685 _91895 (term18 _91882 _91894 _91895 g y x)). Qed.
Lemma lem3583687 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (y : _91894 -> _91882) (x : _91894) : term274 _91882 _91894 _91895 g y x.
Proof. exact (fun h0 : term275 _91882 _91894 _91895 g y x => @lem3583686 _91882 _91894 _91895 g y x). Qed.
Lemma lem3583689 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3583690 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (y : _91894 -> _91882) (x : _91894) : (term274 _91882 _91894 _91895 g y x) = ((term18 _91882 _91894 _91895 g y x) = (term18 _91882 _91894 _91895 g y x)).
Proof. exact (@lem3583689 ((term18 _91882 _91894 _91895 g y x) = (term18 _91882 _91894 _91895 g y x))). Qed.
Lemma lem3583691 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (y : _91894 -> _91882) (x : _91894) : (term18 _91882 _91894 _91895 g y x) = (term18 _91882 _91894 _91895 g y x).
Proof. exact (EQ_MP (@lem3583690 _91882 _91894 _91895 g y x) (@lem3583687 _91882 _91894 _91895 g y x)). Qed.
Lemma lem3583709 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3583710 {_91895 : Type'} (y : _91895) (x : _91895) (z : _91895) : (term276 _91895 x y z) = (term277 _91895 y x z).
Proof. exact (@lem3583709 (y = z) (term278 _91895 x z)). Qed.
Lemma lem3583720 {_91895 : Type'} (x : _91895) (y : _91895) : (term279 _91895 x y) = (term279 _91895 x y).
Proof. exact (eq_refl (term279 _91895 x y)). Qed.
Lemma lem3583721 {_91895 : Type'} (y : _91895) (x : _91895) (z : _91895) : (term270 _91895 x y z) = (term280 _91895 y x z).
Proof. exact (MK_COMB (@lem3583720 _91895 x y) (@lem3583710 _91895 y x z)). Qed.
Lemma lem3583725 (q : Prop) (p : Prop) (r : Prop) : (term281 p q r) = (term281 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3583726 {_91895 : Type'} (y : _91895) (x : _91895) (z : _91895) : (term280 _91895 y x z) = (term282 _91895 y x z).
Proof. exact (@lem3583725 (y = z) (term278 _91895 x y) (term278 _91895 x z)). Qed.
Lemma lem3583748 {_91895 : Type'} (y : _91895) (x : _91895) (z : _91895) : (term270 _91895 x y z) = (term282 _91895 y x z).
Proof. exact (TRANS (@lem3583721 _91895 y x z) (@lem3583726 _91895 y x z)). Qed.
Lemma lem3583749 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3583750 {_91895 : Type'} (y : _91895) (x : _91895) (z : _91895) : (term283 _91895 x y z) = (term284 _91895 y x z).
Proof. exact (MK_COMB (@lem3583749) (@lem3583748 _91895 y x z)). Qed.
Lemma lem3583772 {_91895 : Type'} (y : _91895) (x : _91895) (z : _91895) : (term282 _91895 y x z) = (term282 _91895 y x z).
Proof. exact (eq_refl (term282 _91895 y x z)). Qed.
Lemma lem3583773 {_91895 : Type'} (y : _91895) (x : _91895) (z : _91895) : ((term270 _91895 x y z) = (term282 _91895 y x z)) = ((term282 _91895 y x z) = (term282 _91895 y x z)).
Proof. exact (MK_COMB (@lem3583750 _91895 y x z) (@lem3583772 _91895 y x z)). Qed.
Lemma lem3583775 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3583776 (x : Prop) : (x = x) = True.
Proof. exact (@lem3583775 Prop x). Qed.
Lemma lem3583777 {_91895 : Type'} (y : _91895) (x : _91895) (z : _91895) : ((term282 _91895 y x z) = (term282 _91895 y x z)) = True.
Proof. exact (@lem3583776 (term282 _91895 y x z)). Qed.
Lemma lem3583778 {_91895 : Type'} (y : _91895) (x : _91895) (z : _91895) : ((term270 _91895 x y z) = (term282 _91895 y x z)) = True.
Proof. exact (TRANS (@lem3583773 _91895 y x z) (@lem3583777 _91895 y x z)). Qed.
Lemma lem3583779 {_91895 : Type'} (y : _91895) (x : _91895) (z : _91895) : True = ((term270 _91895 x y z) = (term282 _91895 y x z)).
Proof. exact (SYM (@lem3583778 _91895 y x z)). Qed.
Lemma lem3583780 {_91895 : Type'} (y : _91895) (x : _91895) (z : _91895) : (term270 _91895 x y z) = (term282 _91895 y x z).
Proof. exact (EQ_MP (@lem3583779 _91895 y x z) (@lem0)). Qed.
Lemma lem3583781 {_91895 : Type'} (y : _91895) (x : _91895) (z : _91895) : term282 _91895 y x z.
Proof. exact (EQ_MP (@lem3583780 _91895 y x z) (@lem3583669 _91895 x y z)). Qed.
Lemma lem3583783 (b : Prop) (a : Prop) : (a \/ b) = (term285 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3583784 {_91895 : Type'} (x : _91895) (y : _91895) (z : _91895) : (term282 _91895 y x z) = (term286 _91895 x y z).
Proof. exact (@lem3583783 (term287 _91895 y x z) (y = z)). Qed.
Lemma lem3583786 (a : Prop) (b : Prop) : (term288 a b) = (term289 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3583787 {_91895 : Type'} (y : _91895) (x : _91895) (z : _91895) : (term290 _91895 y x z) = (term291 _91895 y x z).
Proof. exact (@lem3583786 (term278 _91895 x y) (term278 _91895 x z)). Qed.
Lemma lem3583789 (a : Prop) : (term66 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3583790 {_91895 : Type'} (x : _91895) (y : _91895) : (term292 _91895 x y) = (x = y).
Proof. exact (@lem3583789 (x = y)). Qed.
Lemma lem3583791 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3583792 {_91895 : Type'} (x : _91895) (y : _91895) : (term293 _91895 x y) = (term294 _91895 x y).
Proof. exact (MK_COMB (@lem3583791) (@lem3583790 _91895 x y)). Qed.
Lemma lem3583794 (a : Prop) : (term66 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3583795 {_91895 : Type'} (x : _91895) (z : _91895) : (term292 _91895 x z) = (x = z).
Proof. exact (@lem3583794 (x = z)). Qed.
Lemma lem3583796 {_91895 : Type'} (y : _91895) (x : _91895) (z : _91895) : (term291 _91895 y x z) = (term295 _91895 y x z).
Proof. exact (MK_COMB (@lem3583792 _91895 x y) (@lem3583795 _91895 x z)). Qed.
Lemma lem3583797 {_91895 : Type'} (y : _91895) (x : _91895) (z : _91895) : (term290 _91895 y x z) = (term295 _91895 y x z).
Proof. exact (TRANS (@lem3583787 _91895 y x z) (@lem3583796 _91895 y x z)). Qed.
Lemma lem3583798 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3583799 {_91895 : Type'} (y : _91895) (x : _91895) (z : _91895) : (term296 _91895 y x z) = (term297 _91895 y x z).
Proof. exact (MK_COMB (@lem3583798) (@lem3583797 _91895 y x z)). Qed.
Lemma lem3583800 {_91895 : Type'} (y : _91895) (z : _91895) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3583801 {_91895 : Type'} (x : _91895) (y : _91895) (z : _91895) : (term286 _91895 x y z) = (term298 _91895 x y z).
Proof. exact (MK_COMB (@lem3583799 _91895 y x z) (@lem3583800 _91895 y z)). Qed.
Lemma lem3583802 {_91895 : Type'} (x : _91895) (y : _91895) (z : _91895) : (term282 _91895 y x z) = (term298 _91895 x y z).
Proof. exact (TRANS (@lem3583784 _91895 x y z) (@lem3583801 _91895 x y z)). Qed.
Lemma lem3583804 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h1 : term165 _91882 _91894 _91895 y f x g) : term299 _91882 _91894 _91895 f g y x.
Proof. exact (conj (@lem3583682 _91882 _91894 _91895 y f x g h1) (@lem3583691 _91882 _91894 _91895 g y x)). Qed.
Lemma lem3583806 {_91895 : Type'} (x : _91895) (y : _91895) (z : _91895) : term298 _91895 x y z.
Proof. exact (EQ_MP (@lem3583802 _91895 x y z) (@lem3583781 _91895 y x z)). Qed.
Lemma lem3583807 {_91895 : Type'} (x : _91895) (y : _91895) (z : _91895) : term298 _91895 x y z.
Proof. exact (@lem3583806 _91895 x y z). Qed.
Lemma lem3583808 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) (y : _91894 -> _91882) (x : _91894) : term300 _91882 _91894 _91895 f g y x.
Proof. exact (@lem3583807 _91895 (term18 _91882 _91894 _91895 g y x) (f x) (term18 _91882 _91894 _91895 g y x)). Qed.
Lemma lem3583811 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h1 : term165 _91882 _91894 _91895 y f x g) : (f x) = (term18 _91882 _91894 _91895 g y x).
Proof. exact (@lem3583808 _91882 _91894 _91895 f g y x (@lem3583804 _91882 _91894 _91895 y f x g h1)). Qed.
Lemma lem3583812 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h1 : term165 _91882 _91894 _91895 y f x g) : term301 _91882 _91894 _91895 f g y x.
Proof. exact (fun h0 : term302 _91882 _91894 _91895 f g y x => @lem3583811 _91882 _91894 _91895 y f x g h1). Qed.
Lemma lem3583814 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3583815 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) (y : _91894 -> _91882) (x : _91894) : (term301 _91882 _91894 _91895 f g y x) = ((f x) = (term18 _91882 _91894 _91895 g y x)).
Proof. exact (@lem3583814 ((f x) = (term18 _91882 _91894 _91895 g y x))). Qed.
Lemma lem3583816 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h1 : term165 _91882 _91894 _91895 y f x g) : (f x) = (term18 _91882 _91894 _91895 g y x).
Proof. exact (EQ_MP (@lem3583815 _91882 _91894 _91895 f g y x) (@lem3583812 _91882 _91894 _91895 y f x g h1)). Qed.
Lemma lem3583819 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3583821 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (_38684 : _91882) : (term94 _91882 _91894 _91895 f x g _38684) = (term303 _91882 _91894 _91895 f x g _38684).
Proof. exact (@lem3583819 ((f x) = (g _38684))). Qed.
Lemma lem3583824 {_91882 _91894 _91895 : Type'} (_38684 : _91882) (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h1 : term165 _91882 _91894 _91895 y f x g) : term303 _91882 _91894 _91895 f x g _38684.
Proof. exact (EQ_MP (@lem3583821 _91882 _91894 _91895 f x g _38684) (@lem3583639 _91882 _91894 _91895 _38684 y f x g h1)). Qed.
Lemma lem3583825 {_91882 _91894 _91895 : Type'} (_38684 : _91882) (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h1 : term165 _91882 _91894 _91895 y f x g) : term303 _91882 _91894 _91895 f x g _38684.
Proof. exact (@lem3583824 _91882 _91894 _91895 _38684 y f x g h1). Qed.
Lemma lem3583826 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h1 : term165 _91882 _91894 _91895 y f x g) : term304 _91882 _91894 _91895 f g y x.
Proof. exact (@lem3583825 _91882 _91894 _91895 (y x) y f x g h1). Qed.
Lemma lem3583829 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h1 : term165 _91882 _91894 _91895 y f x g) : False.
Proof. exact (@lem3583826 _91882 _91894 _91895 y f x g h1 (@lem3583816 _91882 _91894 _91895 y f x g h1)). Qed.
Lemma lem3583830 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h1 : term165 _91882 _91894 _91895 y f x g) : term305.
Proof. exact (fun h0 : ~ False => @lem3583829 _91882 _91894 _91895 y f x g h1). Qed.
Lemma lem3583832 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3583833 : term305 = False.
Proof. exact (@lem3583832 False). Qed.
Lemma lem3583834 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) (g : _91882 -> _91895) (h1 : term165 _91882 _91894 _91895 y f x g) : False.
Proof. exact (EQ_MP (@lem3583833) (@lem3583830 _91882 _91894 _91895 y f x g h1)). Qed.
Lemma lem3583860 {_91895 : Type'} (x : _91895) (y : _91895) (z : _91895) : term270 _91895 x y z.
Proof. exact (@lem21385 _91895 x y z). Qed.
Lemma lem3583866 {_91882 _91894 _91895 : Type'} (_38686 : _91894) (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (h1 : term200 _91882 _91894 _91895 x f g h) : (f _38686) = (term18 _91882 _91894 _91895 g h _38686).
Proof. exact (EQ_MP (@lem3583634 _91882 _91894 _91895 f g h _38686) (@lem3583633 _91882 _91894 _91895 _38686 x f g h h1)). Qed.
Lemma lem3583867 {_91882 _91894 _91895 : Type'} (_38686 : _91894) (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (h1 : term200 _91882 _91894 _91895 x f g h) : (f _38686) = (term18 _91882 _91894 _91895 g h _38686).
Proof. exact (@lem3583866 _91882 _91894 _91895 _38686 x f g h h1). Qed.
Lemma lem3583868 {_91882 _91894 _91895 : Type'} (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (h1 : term200 _91882 _91894 _91895 x f g h) : (f x) = (term18 _91882 _91894 _91895 g h x).
Proof. exact (@lem3583867 _91882 _91894 _91895 x x f g h h1). Qed.
Lemma lem3583869 {_91882 _91894 _91895 : Type'} (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (h1 : term200 _91882 _91894 _91895 x f g h) : term301 _91882 _91894 _91895 f g h x.
Proof. exact (fun h0 : term302 _91882 _91894 _91895 f g h x => @lem3583868 _91882 _91894 _91895 x f g h h1). Qed.
Lemma lem3583871 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3583872 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (x : _91894) : (term301 _91882 _91894 _91895 f g h x) = ((f x) = (term18 _91882 _91894 _91895 g h x)).
Proof. exact (@lem3583871 ((f x) = (term18 _91882 _91894 _91895 g h x))). Qed.
Lemma lem3583873 {_91882 _91894 _91895 : Type'} (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (h1 : term200 _91882 _91894 _91895 x f g h) : (f x) = (term18 _91882 _91894 _91895 g h x).
Proof. exact (EQ_MP (@lem3583872 _91882 _91894 _91895 f g h x) (@lem3583869 _91882 _91894 _91895 x f g h h1)). Qed.
Lemma lem3583875 {_91895 : Type'} (x : _91895) : x = x.
Proof. exact (@lem21386 _91895 x). Qed.
Lemma lem3583876 {_91895 : Type'} (x : _91895) : x = x.
Proof. exact (@lem3583875 _91895 x). Qed.
Lemma lem3583877 {_91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) : (f x) = (f x).
Proof. exact (@lem3583876 _91895 (f x)). Qed.
Lemma lem3583878 {_91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) : term306 _91894 _91895 f x.
Proof. exact (fun h0 : term307 _91894 _91895 f x => @lem3583877 _91894 _91895 f x). Qed.
Lemma lem3583880 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3583881 {_91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) : (term306 _91894 _91895 f x) = ((f x) = (f x)).
Proof. exact (@lem3583880 ((f x) = (f x))). Qed.
Lemma lem3583882 {_91894 _91895 : Type'} (f : _91894 -> _91895) (x : _91894) : (f x) = (f x).
Proof. exact (EQ_MP (@lem3583881 _91894 _91895 f x) (@lem3583878 _91894 _91895 f x)). Qed.
Lemma lem3583900 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3583901 {_91895 : Type'} (y : _91895) (x : _91895) (z : _91895) : (term276 _91895 x y z) = (term277 _91895 y x z).
Proof. exact (@lem3583900 (y = z) (term278 _91895 x z)). Qed.
Lemma lem3583911 {_91895 : Type'} (x : _91895) (y : _91895) : (term279 _91895 x y) = (term279 _91895 x y).
Proof. exact (eq_refl (term279 _91895 x y)). Qed.
Lemma lem3583912 {_91895 : Type'} (y : _91895) (x : _91895) (z : _91895) : (term270 _91895 x y z) = (term280 _91895 y x z).
Proof. exact (MK_COMB (@lem3583911 _91895 x y) (@lem3583901 _91895 y x z)). Qed.
Lemma lem3583916 (q : Prop) (p : Prop) (r : Prop) : (term281 p q r) = (term281 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3583917 {_91895 : Type'} (y : _91895) (x : _91895) (z : _91895) : (term280 _91895 y x z) = (term282 _91895 y x z).
Proof. exact (@lem3583916 (y = z) (term278 _91895 x y) (term278 _91895 x z)). Qed.
Lemma lem3583939 {_91895 : Type'} (y : _91895) (x : _91895) (z : _91895) : (term270 _91895 x y z) = (term282 _91895 y x z).
Proof. exact (TRANS (@lem3583912 _91895 y x z) (@lem3583917 _91895 y x z)). Qed.
Lemma lem3583940 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3583941 {_91895 : Type'} (y : _91895) (x : _91895) (z : _91895) : (term283 _91895 x y z) = (term284 _91895 y x z).
Proof. exact (MK_COMB (@lem3583940) (@lem3583939 _91895 y x z)). Qed.
Lemma lem3583963 {_91895 : Type'} (y : _91895) (x : _91895) (z : _91895) : (term282 _91895 y x z) = (term282 _91895 y x z).
Proof. exact (eq_refl (term282 _91895 y x z)). Qed.
Lemma lem3583964 {_91895 : Type'} (y : _91895) (x : _91895) (z : _91895) : ((term270 _91895 x y z) = (term282 _91895 y x z)) = ((term282 _91895 y x z) = (term282 _91895 y x z)).
Proof. exact (MK_COMB (@lem3583941 _91895 y x z) (@lem3583963 _91895 y x z)). Qed.
Lemma lem3583966 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3583967 (x : Prop) : (x = x) = True.
Proof. exact (@lem3583966 Prop x). Qed.
Lemma lem3583968 {_91895 : Type'} (y : _91895) (x : _91895) (z : _91895) : ((term282 _91895 y x z) = (term282 _91895 y x z)) = True.
Proof. exact (@lem3583967 (term282 _91895 y x z)). Qed.
Lemma lem3583969 {_91895 : Type'} (y : _91895) (x : _91895) (z : _91895) : ((term270 _91895 x y z) = (term282 _91895 y x z)) = True.
Proof. exact (TRANS (@lem3583964 _91895 y x z) (@lem3583968 _91895 y x z)). Qed.
Lemma lem3583970 {_91895 : Type'} (y : _91895) (x : _91895) (z : _91895) : True = ((term270 _91895 x y z) = (term282 _91895 y x z)).
Proof. exact (SYM (@lem3583969 _91895 y x z)). Qed.
Lemma lem3583971 {_91895 : Type'} (y : _91895) (x : _91895) (z : _91895) : (term270 _91895 x y z) = (term282 _91895 y x z).
Proof. exact (EQ_MP (@lem3583970 _91895 y x z) (@lem0)). Qed.
Lemma lem3583972 {_91895 : Type'} (y : _91895) (x : _91895) (z : _91895) : term282 _91895 y x z.
Proof. exact (EQ_MP (@lem3583971 _91895 y x z) (@lem3583860 _91895 x y z)). Qed.
Lemma lem3583974 (b : Prop) (a : Prop) : (a \/ b) = (term285 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3583975 {_91895 : Type'} (x : _91895) (y : _91895) (z : _91895) : (term282 _91895 y x z) = (term286 _91895 x y z).
Proof. exact (@lem3583974 (term287 _91895 y x z) (y = z)). Qed.
Lemma lem3583977 (a : Prop) (b : Prop) : (term288 a b) = (term289 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3583978 {_91895 : Type'} (y : _91895) (x : _91895) (z : _91895) : (term290 _91895 y x z) = (term291 _91895 y x z).
Proof. exact (@lem3583977 (term278 _91895 x y) (term278 _91895 x z)). Qed.
Lemma lem3583980 (a : Prop) : (term66 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3583981 {_91895 : Type'} (x : _91895) (y : _91895) : (term292 _91895 x y) = (x = y).
Proof. exact (@lem3583980 (x = y)). Qed.
Lemma lem3583982 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3583983 {_91895 : Type'} (x : _91895) (y : _91895) : (term293 _91895 x y) = (term294 _91895 x y).
Proof. exact (MK_COMB (@lem3583982) (@lem3583981 _91895 x y)). Qed.
Lemma lem3583985 (a : Prop) : (term66 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3583986 {_91895 : Type'} (x : _91895) (z : _91895) : (term292 _91895 x z) = (x = z).
Proof. exact (@lem3583985 (x = z)). Qed.
Lemma lem3583987 {_91895 : Type'} (y : _91895) (x : _91895) (z : _91895) : (term291 _91895 y x z) = (term295 _91895 y x z).
Proof. exact (MK_COMB (@lem3583983 _91895 x y) (@lem3583986 _91895 x z)). Qed.
Lemma lem3583988 {_91895 : Type'} (y : _91895) (x : _91895) (z : _91895) : (term290 _91895 y x z) = (term295 _91895 y x z).
Proof. exact (TRANS (@lem3583978 _91895 y x z) (@lem3583987 _91895 y x z)). Qed.
Lemma lem3583989 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3583990 {_91895 : Type'} (y : _91895) (x : _91895) (z : _91895) : (term296 _91895 y x z) = (term297 _91895 y x z).
Proof. exact (MK_COMB (@lem3583989) (@lem3583988 _91895 y x z)). Qed.
Lemma lem3583991 {_91895 : Type'} (y : _91895) (z : _91895) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3583992 {_91895 : Type'} (x : _91895) (y : _91895) (z : _91895) : (term286 _91895 x y z) = (term298 _91895 x y z).
Proof. exact (MK_COMB (@lem3583990 _91895 y x z) (@lem3583991 _91895 y z)). Qed.
Lemma lem3583993 {_91895 : Type'} (x : _91895) (y : _91895) (z : _91895) : (term282 _91895 y x z) = (term298 _91895 x y z).
Proof. exact (TRANS (@lem3583975 _91895 x y z) (@lem3583992 _91895 x y z)). Qed.
Lemma lem3583995 {_91882 _91894 _91895 : Type'} (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (h1 : term200 _91882 _91894 _91895 x f g h) : term308 _91882 _91894 _91895 g h f x.
Proof. exact (conj (@lem3583873 _91882 _91894 _91895 x f g h h1) (@lem3583882 _91894 _91895 f x)). Qed.
Lemma lem3583997 {_91895 : Type'} (x : _91895) (y : _91895) (z : _91895) : term298 _91895 x y z.
Proof. exact (EQ_MP (@lem3583993 _91895 x y z) (@lem3583972 _91895 y x z)). Qed.
Lemma lem3583998 {_91895 : Type'} (x : _91895) (y : _91895) (z : _91895) : term298 _91895 x y z.
Proof. exact (@lem3583997 _91895 x y z). Qed.
Lemma lem3583999 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (h : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) : term309 _91882 _91894 _91895 g h f x.
Proof. exact (@lem3583998 _91895 (f x) (term18 _91882 _91894 _91895 g h x) (f x)). Qed.
Lemma lem3584002 {_91882 _91894 _91895 : Type'} (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (h1 : term200 _91882 _91894 _91895 x f g h) : (term18 _91882 _91894 _91895 g h x) = (f x).
Proof. exact (@lem3583999 _91882 _91894 _91895 g h f x (@lem3583995 _91882 _91894 _91895 x f g h h1)). Qed.
Lemma lem3584003 {_91882 _91894 _91895 : Type'} (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (h1 : term200 _91882 _91894 _91895 x f g h) : term271 _91882 _91894 _91895 g h f x.
Proof. exact (fun h0 : term272 _91882 _91894 _91895 g h f x => @lem3584002 _91882 _91894 _91895 x f g h h1). Qed.
Lemma lem3584005 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3584006 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (h : _91894 -> _91882) (f : _91894 -> _91895) (x : _91894) : (term271 _91882 _91894 _91895 g h f x) = ((term18 _91882 _91894 _91895 g h x) = (f x)).
Proof. exact (@lem3584005 ((term18 _91882 _91894 _91895 g h x) = (f x))). Qed.
Lemma lem3584007 {_91882 _91894 _91895 : Type'} (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (h1 : term200 _91882 _91894 _91895 x f g h) : (term18 _91882 _91894 _91895 g h x) = (f x).
Proof. exact (EQ_MP (@lem3584006 _91882 _91894 _91895 g h f x) (@lem3584003 _91882 _91894 _91895 x f g h h1)). Qed.
Lemma lem3584010 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3584012 {_91882 _91894 _91895 : Type'} (g : _91882 -> _91895) (_38685 : _91882) (f : _91894 -> _91895) (x : _91894) : (term78 _91882 _91894 _91895 g _38685 f x) = (term310 _91882 _91894 _91895 g _38685 f x).
Proof. exact (@lem3584010 ((g _38685) = (f x))). Qed.
Lemma lem3584015 {_91882 _91894 _91895 : Type'} (_38685 : _91882) (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (h1 : term200 _91882 _91894 _91895 x f g h) : term310 _91882 _91894 _91895 g _38685 f x.
Proof. exact (EQ_MP (@lem3584012 _91882 _91894 _91895 g _38685 f x) (@lem3583641 _91882 _91894 _91895 _38685 x f g h h1)). Qed.
Lemma lem3584016 {_91882 _91894 _91895 : Type'} (_38685 : _91882) (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (h1 : term200 _91882 _91894 _91895 x f g h) : term310 _91882 _91894 _91895 g _38685 f x.
Proof. exact (@lem3584015 _91882 _91894 _91895 _38685 x f g h h1). Qed.
Lemma lem3584017 {_91882 _91894 _91895 : Type'} (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (h1 : term200 _91882 _91894 _91895 x f g h) : term311 _91882 _91894 _91895 g h f x.
Proof. exact (@lem3584016 _91882 _91894 _91895 (h x) x f g h h1). Qed.
Lemma lem3584020 {_91882 _91894 _91895 : Type'} (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (h1 : term200 _91882 _91894 _91895 x f g h) : False.
Proof. exact (@lem3584017 _91882 _91894 _91895 x f g h h1 (@lem3584007 _91882 _91894 _91895 x f g h h1)). Qed.
Lemma lem3584021 {_91882 _91894 _91895 : Type'} (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (h1 : term200 _91882 _91894 _91895 x f g h) : term305.
Proof. exact (fun h0 : ~ False => @lem3584020 _91882 _91894 _91895 x f g h h1). Qed.
Lemma lem3584023 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3584024 : term305 = False.
Proof. exact (@lem3584023 False). Qed.
Lemma lem3584025 {_91882 _91894 _91895 : Type'} (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (h1 : term200 _91882 _91894 _91895 x f g h) : False.
Proof. exact (EQ_MP (@lem3584024) (@lem3584021 _91882 _91894 _91895 x f g h h1)). Qed.
Lemma lem3584026 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (h1 : term258 _91882 _91894 _91895 y x f g h) : False.
Proof. exact (or_elim (@lem3583589 _91882 _91894 _91895 y x f g h h1) (fun h0 : term165 _91882 _91894 _91895 y f x g => @lem3583834 _91882 _91894 _91895 y f x g h0) (fun h0 : term200 _91882 _91894 _91895 x f g h => @lem3584025 _91882 _91894 _91895 x f g h h0)). Qed.
Lemma lem3584027 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (h1 : term258 _91882 _91894 _91895 y x f g h) : (term258 _91882 _91894 _91895 y x f g h) = False.
Proof. exact (prop_ext (fun h2 : term258 _91882 _91894 _91895 y x f g h => @lem3584026 _91882 _91894 _91895 y x f g h h1) (fun h2 : False => @lem3583589 _91882 _91894 _91895 y x f g h h1)). Qed.
Lemma lem3584028 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h : _91894 -> _91882) (h1 : term258 _91882 _91894 _91895 y x f g h) : False.
Proof. exact (EQ_MP (@lem3584027 _91882 _91894 _91895 y x f g h h1) (@lem3583589 _91882 _91894 _91895 y x f g h h1)). Qed.
Lemma lem3584029 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (x : _91894) (f : _91894 -> _91895) (g : _91882 -> _91895) (h1 : term261 _91882 _91894 _91895 y x f g) : False.
Proof. exact (ex_elim (@lem3583522 _91882 _91894 _91895 y x f g h1) (fun h : _91894 -> _91882 => fun h0 : term260 _91882 _91894 _91895 y x f g h => @lem3584028 _91882 _91894 _91895 y x f g h h0)). Qed.
Lemma lem3584030 {_91882 _91894 _91895 : Type'} (y : _91894 -> _91882) (f : _91894 -> _91895) (g : _91882 -> _91895) (h1 : term263 _91882 _91894 _91895 y f g) : False.
Proof. exact (ex_elim (@lem3583521 _91882 _91894 _91895 y f g h1) (fun x : _91894 => fun h0 : term262 _91882 _91894 _91895 y f g x => @lem3584029 _91882 _91894 _91895 y x f g h0)). Qed.
Lemma lem3584031 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) (h1 : term71 _91882 _91894 _91895 f g) : False.
Proof. exact (ex_elim (@lem3583520 _91882 _91894 _91895 f g h1) (fun y : _91894 -> _91882 => fun h0 : term264 _91882 _91894 _91895 f g y => @lem3584030 _91882 _91894 _91895 y f g h0)). Qed.
Lemma lem3584032 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) (h1 : term71 _91882 _91894 _91895 f g) : (term71 _91882 _91894 _91895 f g) = False.
Proof. exact (prop_ext (fun h2 : term71 _91882 _91894 _91895 f g => @lem3584031 _91882 _91894 _91895 f g h1) (fun h2 : False => @lem3583168 _91882 _91894 _91895 f g h1)). Qed.
Lemma lem3584033 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) (h1 : term71 _91882 _91894 _91895 f g) : False.
Proof. exact (EQ_MP (@lem3584032 _91882 _91894 _91895 f g h1) (@lem3583168 _91882 _91894 _91895 f g h1)). Qed.
Lemma lem3584034 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : term70 _91882 _91894 _91895 f g.
Proof. exact (fun h0 : term71 _91882 _91894 _91895 f g => @lem3584033 _91882 _91894 _91895 f g h0). Qed.
Lemma lem3584035 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) (g : _91882 -> _91895) : (term50 _91882 _91894 _91895 g f) = (term48 _91882 _91894 _91895 f g).
Proof. exact (EQ_MP (@lem3583167 _91882 _91894 _91895 f g) (@lem3584034 _91882 _91894 _91895 f g)). Qed.
Lemma lem3584040 {_91882 _91894 _91895 : Type'} (f : _91894 -> _91895) : term54 _91882 _91894 _91895 f.
Proof. exact (fun g : _91882 -> _91895 => @lem3584035 _91882 _91894 _91895 f g). Qed.
Lemma lem3584045 {_91882 _91894 _91895 : Type'} : term58 _91882 _91894 _91895.
Proof. exact (fun f : _91894 -> _91895 => @lem3584040 _91882 _91894 _91895 f). Qed.
Lemma lem3584046 {_91882 _91894 _91895 : Type'} : term60 _91882 _91894 _91895.
Proof. exact (EQ_MP (@lem3583163 _91882 _91894 _91895) (@lem3584045 _91882 _91894 _91895)). Qed.
Lemma lem3584048 {_91882 _91894 _91895 : Type'} : term60 _91882 _91894 _91895.
Proof. exact (@lem3583065 _91882 _91894 _91895 (@lem3584046 _91882 _91894 _91895)). Qed.
Lemma lem3584049 {_91882 _91894 _91895 : Type'} (h1 : term61 _91882 _91894 _91895) : False.
Proof. exact (@lem3584048 _91882 _91894 _91895 (@lem3583049 _91882 _91894 _91895 h1)). Qed.
Lemma lem3584050 {_91882 _91894 _91895 : Type'} (h1 : term61 _91882 _91894 _91895) : (term61 _91882 _91894 _91895) = False.
Proof. exact (prop_ext (fun h2 : term61 _91882 _91894 _91895 => @lem3584049 _91882 _91894 _91895 h1) (fun h2 : False => @lem3583049 _91882 _91894 _91895 h1)). Qed.
Lemma lem3584051 {_91882 _91894 _91895 : Type'} (h1 : term61 _91882 _91894 _91895) : False.
Proof. exact (EQ_MP (@lem3584050 _91882 _91894 _91895 h1) (@lem3583049 _91882 _91894 _91895 h1)). Qed.
Lemma lem3584052 {_91882 _91894 _91895 : Type'} : term60 _91882 _91894 _91895.
Proof. exact (fun h0 : term61 _91882 _91894 _91895 => @lem3584051 _91882 _91894 _91895 h0). Qed.
Lemma lem3584053 {_91882 _91894 _91895 : Type'} : term58 _91882 _91894 _91895.
Proof. exact (EQ_MP (@lem3583048 _91882 _91894 _91895) (@lem3584052 _91882 _91894 _91895)). Qed.
Lemma lem3584054 {_91882 _91894 _91895 : Type'} : term57 _91882 _91894 _91895.
Proof. exact (EQ_MP (@lem3583044 _91882 _91894 _91895) (@lem3584053 _91882 _91894 _91895)). Qed.
