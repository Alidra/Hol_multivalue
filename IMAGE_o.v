Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMAGE_o_term_abbrevs.
Require Import EXTENSION_spec.
Require Import IN_IMAGE_spec.
Require Import o_THM_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Lemma lem3368961 {A B C : Type'} (f : B -> C) : term0 A B C f.
Proof. exact (@lem15456 A B C f). Qed.
Lemma lem3368962 {A B C : Type'} (f : B -> C) : (term0 A B C f) = (term1 A B C f).
Proof. exact (eq_refl (term0 A B C f)). Qed.
Lemma lem3368963 {A B C : Type'} (f : B -> C) : term1 A B C f.
Proof. exact (EQ_MP (@lem3368962 A B C f) (@lem3368961 A B C f)). Qed.
Lemma lem3368964 {A B C : Type'} (f : B -> C) (g : A -> B) : term2 A B C f g.
Proof. exact (@lem3368963 A B C f g). Qed.
Lemma lem3368965 {A B C : Type'} (f : B -> C) (g : A -> B) : (term2 A B C f g) = (term3 A B C f g).
Proof. exact (eq_refl (term2 A B C f g)). Qed.
Lemma lem3368966 {A B C : Type'} (f : B -> C) (g : A -> B) : term3 A B C f g.
Proof. exact (EQ_MP (@lem3368965 A B C f g) (@lem3368964 A B C f g)). Qed.
Lemma lem3368967 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : term4 A B C f g x.
Proof. exact (@lem3368966 A B C f g x). Qed.
Lemma lem3368968 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (term4 A B C f g x) = ((@o A B C f g x) = (term5 A B C f g x)).
Proof. exact (eq_refl (term4 A B C f g x)). Qed.
Lemma lem3368970 {A B : Type'} (y : B) : term6 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem3368971 {A B : Type'} (y : B) : (term6 A B y) = (term7 A B y).
Proof. exact (eq_refl (term6 A B y)). Qed.
Lemma lem3368972 {A B : Type'} (y : B) : term7 A B y.
Proof. exact (EQ_MP (@lem3368971 A B y) (@lem3368970 A B y)). Qed.
Lemma lem3368973 {A B : Type'} (y : B) (s : A -> Prop) : term8 A B y s.
Proof. exact (@lem3368972 A B y s). Qed.
Lemma lem3368974 {A B : Type'} (y : B) (s : A -> Prop) : (term8 A B y s) = (term9 A B y s).
Proof. exact (eq_refl (term8 A B y s)). Qed.
Lemma lem3368975 {A B : Type'} (y : B) (s : A -> Prop) : term9 A B y s.
Proof. exact (EQ_MP (@lem3368974 A B y s) (@lem3368973 A B y s)). Qed.
Lemma lem3368976 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term10 A B y s f.
Proof. exact (@lem3368975 A B y s f). Qed.
Lemma lem3368977 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term10 A B y s f) = ((term11 A B y f s) = (term12 A B y f s)).
Proof. exact (eq_refl (term10 A B y s f)). Qed.
Lemma lem3368979 {A : Type'} (s : A -> Prop) : term13 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem3368980 {A : Type'} (s : A -> Prop) : (term13 A s) = (term14 A s).
Proof. exact (eq_refl (term13 A s)). Qed.
Lemma lem3368981 {A : Type'} (s : A -> Prop) : term14 A s.
Proof. exact (EQ_MP (@lem3368980 A s) (@lem3368979 A s)). Qed.
Lemma lem3368982 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term15 A s t.
Proof. exact (@lem3368981 A s t). Qed.
Lemma lem3368983 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term15 A s t) = ((s = t) = (term16 A s t)).
Proof. exact (eq_refl (term15 A s t)). Qed.
Lemma lem3369000 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term16 A s t).
Proof. exact (EQ_MP (@lem3368983 A s t) (@lem3368982 A s t)). Qed.
Lemma lem3369001 {_87571 : Type'} (s : _87571 -> Prop) (t : _87571 -> Prop) : (s = t) = (term16 _87571 s t).
Proof. exact (@lem3369000 _87571 s t). Qed.
Lemma lem3369002 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : ((term17 _87566 _87571 _87575 f g s) = (term18 _87566 _87571 _87575 f g s)) = (term19 _87566 _87571 _87575 f g s).
Proof. exact (@lem3369001 _87571 (term17 _87566 _87571 _87575 f g s) (term18 _87566 _87571 _87575 f g s)). Qed.
Lemma lem3369012 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term11 A B y f s) = (term12 A B y f s).
Proof. exact (EQ_MP (@lem3368977 A B y f s) (@lem3368976 A B y s f)). Qed.
Lemma lem3369013 {_87566 _87571 : Type'} (y : _87571) (f : _87566 -> _87571) (s : _87566 -> Prop) : (term11 _87566 _87571 y f s) = (term12 _87566 _87571 y f s).
Proof. exact (@lem3369012 _87566 _87571 y f s). Qed.
Lemma lem3369014 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term20 _87566 _87571 _87575 x f g s) = (term21 _87566 _87571 _87575 x f g s).
Proof. exact (@lem3369013 _87566 _87571 x (@o _87566 _87575 _87571 f g) s). Qed.
Lemma lem3369026 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (@o A B C f g x) = (term5 A B C f g x).
Proof. exact (EQ_MP (@lem3368968 A B C f g x) (@lem3368967 A B C f g x)). Qed.
Lemma lem3369027 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) (x : _87566) : (@o _87566 _87575 _87571 f g x) = (term22 _87566 _87571 _87575 f g x).
Proof. exact (@lem3369026 _87566 _87575 _87571 f g x). Qed.
Lemma lem3369028 {_87571 : Type'} (x : _87571) : (@eq _87571 x) = (@eq _87571 x).
Proof. exact (eq_refl (@eq _87571 x)). Qed.
Lemma lem3369029 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (x' : _87566) : (x = (@o _87566 _87575 _87571 f g x')) = (x = (term22 _87566 _87571 _87575 f g x')).
Proof. exact (MK_COMB (@lem3369028 _87571 x) (@lem3369027 _87566 _87571 _87575 f g x')). Qed.
Lemma lem3369034 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3369035 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (x' : _87566) : (term23 _87566 _87571 _87575 x f g x') = (term24 _87566 _87571 _87575 x f g x').
Proof. exact (MK_COMB (@lem3369034) (@lem3369029 _87566 _87571 _87575 x f g x')). Qed.
Lemma lem3369036 {_87566 : Type'} (x : _87566) (s : _87566 -> Prop) : (@IN _87566 x s) = (@IN _87566 x s).
Proof. exact (eq_refl (@IN _87566 x s)). Qed.
Lemma lem3369037 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (x' : _87566) (s : _87566 -> Prop) : (term25 _87566 _87571 _87575 x f g x' s) = (term26 _87566 _87571 _87575 x f g x' s).
Proof. exact (MK_COMB (@lem3369035 _87566 _87571 _87575 x f g x') (@lem3369036 _87566 x' s)). Qed.
Lemma lem3369040 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term27 _87566 _87571 _87575 x f g s) = (term28 _87566 _87571 _87575 x f g s).
Proof. exact (fun_ext (fun x' : _87566 => @lem3369037 _87566 _87571 _87575 x f g x' s)). Qed.
Lemma lem3369041 {_87566 : Type'} : (@ex _87566) = (@ex _87566).
Proof. exact (eq_refl (@ex _87566)). Qed.
Lemma lem3369042 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term21 _87566 _87571 _87575 x f g s) = (term29 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369041 _87566) (@lem3369040 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369047 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term20 _87566 _87571 _87575 x f g s) = (term29 _87566 _87571 _87575 x f g s).
Proof. exact (TRANS (@lem3369014 _87566 _87571 _87575 x f g s) (@lem3369042 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369048 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3369049 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term30 _87566 _87571 _87575 x f g s) = (term31 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369048) (@lem3369047 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369051 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term11 A B y f s) = (term12 A B y f s).
Proof. exact (EQ_MP (@lem3368977 A B y f s) (@lem3368976 A B y s f)). Qed.
Lemma lem3369052 {_87571 _87575 : Type'} (y : _87571) (f : _87575 -> _87571) (s : _87575 -> Prop) : (term32 _87571 _87575 y f s) = (term33 _87571 _87575 y f s).
Proof. exact (@lem3369051 _87575 _87571 y f s). Qed.
Lemma lem3369053 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term34 _87566 _87571 _87575 x f g s) = (term35 _87566 _87571 _87575 x f g s).
Proof. exact (@lem3369052 _87571 _87575 x f (@IMAGE _87566 _87575 g s)). Qed.
Lemma lem3369065 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term11 A B y f s) = (term12 A B y f s).
Proof. exact (EQ_MP (@lem3368977 A B y f s) (@lem3368976 A B y s f)). Qed.
Lemma lem3369066 {_87566 _87575 : Type'} (y : _87575) (f : _87566 -> _87575) (s : _87566 -> Prop) : (term11 _87566 _87575 y f s) = (term12 _87566 _87575 y f s).
Proof. exact (@lem3369065 _87566 _87575 y f s). Qed.
Lemma lem3369067 {_87566 _87575 : Type'} (x : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term11 _87566 _87575 x g s) = (term12 _87566 _87575 x g s).
Proof. exact (@lem3369066 _87566 _87575 x g s). Qed.
Lemma lem3369078 {_87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) : (term36 _87571 _87575 x f x') = (term36 _87571 _87575 x f x').
Proof. exact (eq_refl (term36 _87571 _87575 x f x')). Qed.
Lemma lem3369079 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term37 _87566 _87571 _87575 x f x' g s) = (term38 _87566 _87571 _87575 x f x' g s).
Proof. exact (MK_COMB (@lem3369078 _87571 _87575 x f x') (@lem3369067 _87566 _87575 x' g s)). Qed.
Lemma lem3369082 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term39 _87566 _87571 _87575 x f g s) = (term40 _87566 _87571 _87575 x f g s).
Proof. exact (fun_ext (fun x' : _87575 => @lem3369079 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3369083 {_87575 : Type'} : (@ex _87575) = (@ex _87575).
Proof. exact (eq_refl (@ex _87575)). Qed.
Lemma lem3369084 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term35 _87566 _87571 _87575 x f g s) = (term41 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369083 _87575) (@lem3369082 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369089 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term34 _87566 _87571 _87575 x f g s) = (term41 _87566 _87571 _87575 x f g s).
Proof. exact (TRANS (@lem3369053 _87566 _87571 _87575 x f g s) (@lem3369084 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369090 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : ((term20 _87566 _87571 _87575 x f g s) = (term34 _87566 _87571 _87575 x f g s)) = ((term29 _87566 _87571 _87575 x f g s) = (term41 _87566 _87571 _87575 x f g s)).
Proof. exact (MK_COMB (@lem3369049 _87566 _87571 _87575 x f g s) (@lem3369089 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369095 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term42 _87566 _87571 _87575 f g s) = (term43 _87566 _87571 _87575 f g s).
Proof. exact (fun_ext (fun x : _87571 => @lem3369090 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369096 {_87571 : Type'} : (@all _87571) = (@all _87571).
Proof. exact (eq_refl (@all _87571)). Qed.
Lemma lem3369097 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term19 _87566 _87571 _87575 f g s) = (term44 _87566 _87571 _87575 f g s).
Proof. exact (MK_COMB (@lem3369096 _87571) (@lem3369095 _87566 _87571 _87575 f g s)). Qed.
Lemma lem3369102 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : ((term17 _87566 _87571 _87575 f g s) = (term18 _87566 _87571 _87575 f g s)) = (term44 _87566 _87571 _87575 f g s).
Proof. exact (TRANS (@lem3369002 _87566 _87571 _87575 f g s) (@lem3369097 _87566 _87571 _87575 f g s)). Qed.
Lemma lem3369103 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) : (term45 _87566 _87571 _87575 f g) = (term46 _87566 _87571 _87575 f g).
Proof. exact (fun_ext (fun s : _87566 -> Prop => @lem3369102 _87566 _87571 _87575 f g s)). Qed.
Lemma lem3369104 {_87566 : Type'} : (@all (_87566 -> Prop)) = (@all (_87566 -> Prop)).
Proof. exact (eq_refl (@all (_87566 -> Prop))). Qed.
Lemma lem3369105 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) : (term47 _87566 _87571 _87575 f g) = (term48 _87566 _87571 _87575 f g).
Proof. exact (MK_COMB (@lem3369104 _87566) (@lem3369103 _87566 _87571 _87575 f g)). Qed.
Lemma lem3369110 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) : (term49 _87566 _87571 _87575 f) = (term50 _87566 _87571 _87575 f).
Proof. exact (fun_ext (fun g : _87566 -> _87575 => @lem3369105 _87566 _87571 _87575 f g)). Qed.
Lemma lem3369111 {_87566 _87575 : Type'} : (@all (_87566 -> _87575)) = (@all (_87566 -> _87575)).
Proof. exact (eq_refl (@all (_87566 -> _87575))). Qed.
Lemma lem3369112 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) : (term51 _87566 _87571 _87575 f) = (term52 _87566 _87571 _87575 f).
Proof. exact (MK_COMB (@lem3369111 _87566 _87575) (@lem3369110 _87566 _87571 _87575 f)). Qed.
Lemma lem3369117 {_87566 _87571 _87575 : Type'} : (term53 _87566 _87571 _87575) = (term54 _87566 _87571 _87575).
Proof. exact (fun_ext (fun f : _87575 -> _87571 => @lem3369112 _87566 _87571 _87575 f)). Qed.
Lemma lem3369118 {_87571 _87575 : Type'} : (@all (_87575 -> _87571)) = (@all (_87575 -> _87571)).
Proof. exact (eq_refl (@all (_87575 -> _87571))). Qed.
Lemma lem3369119 {_87566 _87571 _87575 : Type'} : (term55 _87566 _87571 _87575) = (term56 _87566 _87571 _87575).
Proof. exact (MK_COMB (@lem3369118 _87571 _87575) (@lem3369117 _87566 _87571 _87575)). Qed.
Lemma lem3369124 {_87566 _87571 _87575 : Type'} : (term56 _87566 _87571 _87575) = (term55 _87566 _87571 _87575).
Proof. exact (SYM (@lem3369119 _87566 _87571 _87575)). Qed.
Lemma lem3369126 (p : Prop) : p = (term57 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3369127 {_87566 _87571 _87575 : Type'} : (term56 _87566 _87571 _87575) = (term58 _87566 _87571 _87575).
Proof. exact (@lem3369126 (term56 _87566 _87571 _87575)). Qed.
Lemma lem3369128 {_87566 _87571 _87575 : Type'} : (term58 _87566 _87571 _87575) = (term56 _87566 _87571 _87575).
Proof. exact (SYM (@lem3369127 _87566 _87571 _87575)). Qed.
Lemma lem3369129 {_87566 _87571 _87575 : Type'} (h1 : term59 _87566 _87571 _87575) : term59 _87566 _87571 _87575.
Proof. exact (h1). Qed.
Lemma lem3369132 {_87566 _87571 _87575 : Type'} (h1 : term58 _87566 _87571 _87575) : term58 _87566 _87571 _87575.
Proof. exact (h1). Qed.
Lemma lem3369133 {_87566 _87571 _87575 : Type'} : term60 _87566 _87571 _87575.
Proof. exact (fun h0 : term58 _87566 _87571 _87575 => @lem3369132 _87566 _87571 _87575 h0). Qed.
Lemma lem3369134 {_87566 _87571 _87575 : Type'} (h1 : term60 _87566 _87571 _87575) : term60 _87566 _87571 _87575.
Proof. exact (h1). Qed.
Lemma lem3369135 {_87566 _87571 _87575 : Type'} (h1 : term58 _87566 _87571 _87575) : term58 _87566 _87571 _87575.
Proof. exact (h1). Qed.
Lemma lem3369136 {_87566 _87571 _87575 : Type'} (h1 : term58 _87566 _87571 _87575) (h2 : term60 _87566 _87571 _87575) : term58 _87566 _87571 _87575.
Proof. exact (@lem3369134 _87566 _87571 _87575 h2 (@lem3369135 _87566 _87571 _87575 h1)). Qed.
Lemma lem3369137 {_87566 _87571 _87575 : Type'} (h1 : term58 _87566 _87571 _87575) : term61 _87566 _87571 _87575.
Proof. exact (fun h0 : term60 _87566 _87571 _87575 => @lem3369136 _87566 _87571 _87575 h1 h0). Qed.
Lemma lem3369138 {_87566 _87571 _87575 : Type'} (h1 : term60 _87566 _87571 _87575) : term60 _87566 _87571 _87575.
Proof. exact (h1). Qed.
Lemma lem3369139 {_87566 _87571 _87575 : Type'} (h1 : term58 _87566 _87571 _87575) (h2 : term60 _87566 _87571 _87575) : term58 _87566 _87571 _87575.
Proof. exact (@lem3369137 _87566 _87571 _87575 h1 (@lem3369138 _87566 _87571 _87575 h2)). Qed.
Lemma lem3369140 {_87566 _87571 _87575 : Type'} (h1 : term60 _87566 _87571 _87575) : term60 _87566 _87571 _87575.
Proof. exact (fun h0 : term58 _87566 _87571 _87575 => @lem3369139 _87566 _87571 _87575 h0 h1). Qed.
Lemma lem3369141 {_87566 _87571 _87575 : Type'} : term62 _87566 _87571 _87575.
Proof. exact (fun h0 : term60 _87566 _87571 _87575 => @lem3369140 _87566 _87571 _87575 h0). Qed.
Lemma lem3369144 {_87566 _87571 _87575 : Type'} : term60 _87566 _87571 _87575.
Proof. exact (@lem3369141 _87566 _87571 _87575 (@lem3369133 _87566 _87571 _87575)). Qed.
Lemma lem3369145 {_87566 _87571 _87575 : Type'} : term60 _87566 _87571 _87575.
Proof. exact (@lem3369144 _87566 _87571 _87575). Qed.
Lemma lem3369147 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3369148 {_87566 _87571 _87575 : Type'} : (term58 _87566 _87571 _87575) = (term63 _87566 _87571 _87575).
Proof. exact (@lem3369147 (term59 _87566 _87571 _87575)). Qed.
Lemma lem3369150 (t : Prop) : (term64 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3369151 {_87566 _87571 _87575 : Type'} : (term63 _87566 _87571 _87575) = (term56 _87566 _87571 _87575).
Proof. exact (@lem3369150 (term56 _87566 _87571 _87575)). Qed.
Lemma lem3369322 {_87566 _87571 _87575 : Type'} : (term58 _87566 _87571 _87575) = (term56 _87566 _87571 _87575).
Proof. exact (TRANS (@lem3369148 _87566 _87571 _87575) (@lem3369151 _87566 _87571 _87575)). Qed.
Lemma lem3369327 {_87566 _87575 : Type'} (x : _87575) (g : _87566 -> _87575) (x' : _87566) (s : _87566 -> Prop) : (term65 _87566 _87575 x g x' s) = (term65 _87566 _87575 x g x' s).
Proof. exact (eq_refl (term65 _87566 _87575 x g x' s)). Qed.
Lemma lem3369328 {_87566 _87575 : Type'} (x : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term66 _87566 _87575 x g s) = (term66 _87566 _87575 x g s).
Proof. exact (fun_ext (fun x' : _87566 => @lem3369327 _87566 _87575 x g x' s)). Qed.
Lemma lem3369329 {_87566 : Type'} : (@ex _87566) = (@ex _87566).
Proof. exact (eq_refl (@ex _87566)). Qed.
Lemma lem3369330 {_87566 _87575 : Type'} (x : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term12 _87566 _87575 x g s) = (term12 _87566 _87575 x g s).
Proof. exact (MK_COMB (@lem3369329 _87566) (@lem3369328 _87566 _87575 x g s)). Qed.
Lemma lem3369333 {_87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) : (term36 _87571 _87575 x f x') = (term36 _87571 _87575 x f x').
Proof. exact (eq_refl (term36 _87571 _87575 x f x')). Qed.
Lemma lem3369334 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term38 _87566 _87571 _87575 x f x' g s) = (term38 _87566 _87571 _87575 x f x' g s).
Proof. exact (MK_COMB (@lem3369333 _87571 _87575 x f x') (@lem3369330 _87566 _87575 x' g s)). Qed.
Lemma lem3369335 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term40 _87566 _87571 _87575 x f g s) = (term40 _87566 _87571 _87575 x f g s).
Proof. exact (fun_ext (fun x' : _87575 => @lem3369334 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3369336 {_87575 : Type'} : (@ex _87575) = (@ex _87575).
Proof. exact (eq_refl (@ex _87575)). Qed.
Lemma lem3369337 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term41 _87566 _87571 _87575 x f g s) = (term41 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369336 _87575) (@lem3369335 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369342 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (x' : _87566) (s : _87566 -> Prop) : (term26 _87566 _87571 _87575 x f g x' s) = (term26 _87566 _87571 _87575 x f g x' s).
Proof. exact (eq_refl (term26 _87566 _87571 _87575 x f g x' s)). Qed.
Lemma lem3369343 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term28 _87566 _87571 _87575 x f g s) = (term28 _87566 _87571 _87575 x f g s).
Proof. exact (fun_ext (fun x' : _87566 => @lem3369342 _87566 _87571 _87575 x f g x' s)). Qed.
Lemma lem3369344 {_87566 : Type'} : (@ex _87566) = (@ex _87566).
Proof. exact (eq_refl (@ex _87566)). Qed.
Lemma lem3369345 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term29 _87566 _87571 _87575 x f g s) = (term29 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369344 _87566) (@lem3369343 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369346 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3369347 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term31 _87566 _87571 _87575 x f g s) = (term31 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369346) (@lem3369345 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369348 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : ((term29 _87566 _87571 _87575 x f g s) = (term41 _87566 _87571 _87575 x f g s)) = ((term29 _87566 _87571 _87575 x f g s) = (term41 _87566 _87571 _87575 x f g s)).
Proof. exact (MK_COMB (@lem3369347 _87566 _87571 _87575 x f g s) (@lem3369337 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369349 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term43 _87566 _87571 _87575 f g s) = (term43 _87566 _87571 _87575 f g s).
Proof. exact (fun_ext (fun x : _87571 => @lem3369348 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369350 {_87571 : Type'} : (@all _87571) = (@all _87571).
Proof. exact (eq_refl (@all _87571)). Qed.
Lemma lem3369351 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term44 _87566 _87571 _87575 f g s) = (term44 _87566 _87571 _87575 f g s).
Proof. exact (MK_COMB (@lem3369350 _87571) (@lem3369349 _87566 _87571 _87575 f g s)). Qed.
Lemma lem3369352 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) : (term46 _87566 _87571 _87575 f g) = (term46 _87566 _87571 _87575 f g).
Proof. exact (fun_ext (fun s : _87566 -> Prop => @lem3369351 _87566 _87571 _87575 f g s)). Qed.
Lemma lem3369353 {_87566 : Type'} : (@all (_87566 -> Prop)) = (@all (_87566 -> Prop)).
Proof. exact (eq_refl (@all (_87566 -> Prop))). Qed.
Lemma lem3369354 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) : (term48 _87566 _87571 _87575 f g) = (term48 _87566 _87571 _87575 f g).
Proof. exact (MK_COMB (@lem3369353 _87566) (@lem3369352 _87566 _87571 _87575 f g)). Qed.
Lemma lem3369355 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) : (term50 _87566 _87571 _87575 f) = (term50 _87566 _87571 _87575 f).
Proof. exact (fun_ext (fun g : _87566 -> _87575 => @lem3369354 _87566 _87571 _87575 f g)). Qed.
Lemma lem3369356 {_87566 _87575 : Type'} : (@all (_87566 -> _87575)) = (@all (_87566 -> _87575)).
Proof. exact (eq_refl (@all (_87566 -> _87575))). Qed.
Lemma lem3369357 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) : (term52 _87566 _87571 _87575 f) = (term52 _87566 _87571 _87575 f).
Proof. exact (MK_COMB (@lem3369356 _87566 _87575) (@lem3369355 _87566 _87571 _87575 f)). Qed.
Lemma lem3369358 {_87566 _87571 _87575 : Type'} : (term54 _87566 _87571 _87575) = (term54 _87566 _87571 _87575).
Proof. exact (fun_ext (fun f : _87575 -> _87571 => @lem3369357 _87566 _87571 _87575 f)). Qed.
Lemma lem3369359 {_87571 _87575 : Type'} : (@all (_87575 -> _87571)) = (@all (_87575 -> _87571)).
Proof. exact (eq_refl (@all (_87575 -> _87571))). Qed.
Lemma lem3369360 {_87566 _87571 _87575 : Type'} : (term56 _87566 _87571 _87575) = (term56 _87566 _87571 _87575).
Proof. exact (MK_COMB (@lem3369359 _87571 _87575) (@lem3369358 _87566 _87571 _87575)). Qed.
Lemma lem3369411 {_87566 _87571 _87575 : Type'} : (term58 _87566 _87571 _87575) = (term56 _87566 _87571 _87575).
Proof. exact (TRANS (@lem3369322 _87566 _87571 _87575) (@lem3369360 _87566 _87571 _87575)). Qed.
Lemma lem3369412 {_87566 _87571 _87575 : Type'} : (term56 _87566 _87571 _87575) = (term58 _87566 _87571 _87575).
Proof. exact (SYM (@lem3369411 _87566 _87571 _87575)). Qed.
Lemma lem3369414 (p : Prop) : p = (term57 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3369415 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : ((term29 _87566 _87571 _87575 x f g s) = (term41 _87566 _87571 _87575 x f g s)) = (term67 _87566 _87571 _87575 x f g s).
Proof. exact (@lem3369414 ((term29 _87566 _87571 _87575 x f g s) = (term41 _87566 _87571 _87575 x f g s))). Qed.
Lemma lem3369416 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term67 _87566 _87571 _87575 x f g s) = ((term29 _87566 _87571 _87575 x f g s) = (term41 _87566 _87571 _87575 x f g s)).
Proof. exact (SYM (@lem3369415 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369417 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : term68 _87566 _87571 _87575 x f g s) : term68 _87566 _87571 _87575 x f g s.
Proof. exact (h1). Qed.
Lemma lem3369426 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (x' : _87566) (s : _87566 -> Prop) : (term69 _87566 _87571 _87575 x f g x' s) = (term70 _87566 _87571 _87575 x f g x' s).
Proof. exact (@lem17045 (x = (term22 _87566 _87571 _87575 f g x')) (@IN _87566 x' s)). Qed.
Lemma lem3369429 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (x' : _87566) (s : _87566 -> Prop) : (term26 _87566 _87571 _87575 x f g x' s) = (term26 _87566 _87571 _87575 x f g x' s).
Proof. exact (eq_refl (term26 _87566 _87571 _87575 x f g x' s)). Qed.
Lemma lem3369430 {_87566 : Type'} (P : _87566 -> Prop) : (term71 _87566 P) = (term72 _87566 P).
Proof. exact (@lem18394 _87566 P). Qed.
Lemma lem3369431 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term73 _87566 _87571 _87575 x f g s) = (term74 _87566 _87571 _87575 x f g s).
Proof. exact (@lem3369430 _87566 (term28 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369432 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (x' : _87566) (s : _87566 -> Prop) : (term75 _87566 _87571 _87575 x f g s x') = (term26 _87566 _87571 _87575 x f g x' s).
Proof. exact (eq_refl (term75 _87566 _87571 _87575 x f g s x')). Qed.
Lemma lem3369433 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3369434 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (x' : _87566) (s : _87566 -> Prop) : (term76 _87566 _87571 _87575 x f g s x') = (term69 _87566 _87571 _87575 x f g x' s).
Proof. exact (MK_COMB (@lem3369433) (@lem3369432 _87566 _87571 _87575 x f g x' s)). Qed.
Lemma lem3369435 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (x' : _87566) (s : _87566 -> Prop) : (term76 _87566 _87571 _87575 x f g s x') = (term70 _87566 _87571 _87575 x f g x' s).
Proof. exact (TRANS (@lem3369434 _87566 _87571 _87575 x f g x' s) (@lem3369426 _87566 _87571 _87575 x f g x' s)). Qed.
Lemma lem3369436 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term77 _87566 _87571 _87575 x f g s) = (term78 _87566 _87571 _87575 x f g s).
Proof. exact (fun_ext (fun x' : _87566 => @lem3369435 _87566 _87571 _87575 x f g x' s)). Qed.
Lemma lem3369437 {_87566 : Type'} : (@all _87566) = (@all _87566).
Proof. exact (eq_refl (@all _87566)). Qed.
Lemma lem3369438 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term74 _87566 _87571 _87575 x f g s) = (term79 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369437 _87566) (@lem3369436 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369439 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term73 _87566 _87571 _87575 x f g s) = (term79 _87566 _87571 _87575 x f g s).
Proof. exact (TRANS (@lem3369431 _87566 _87571 _87575 x f g s) (@lem3369438 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369440 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term28 _87566 _87571 _87575 x f g s) = (term28 _87566 _87571 _87575 x f g s).
Proof. exact (fun_ext (fun x' : _87566 => @lem3369429 _87566 _87571 _87575 x f g x' s)). Qed.
Lemma lem3369441 {_87566 : Type'} : (@ex _87566) = (@ex _87566).
Proof. exact (eq_refl (@ex _87566)). Qed.
Lemma lem3369442 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term29 _87566 _87571 _87575 x f g s) = (term29 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369441 _87566) (@lem3369440 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369453 {_87566 _87575 : Type'} (x : _87575) (g : _87566 -> _87575) (x' : _87566) (s : _87566 -> Prop) : (term80 _87566 _87575 x g x' s) = (term81 _87566 _87575 x g x' s).
Proof. exact (@lem17045 (x = (g x')) (@IN _87566 x' s)). Qed.
Lemma lem3369456 {_87566 _87575 : Type'} (x : _87575) (g : _87566 -> _87575) (x' : _87566) (s : _87566 -> Prop) : (term65 _87566 _87575 x g x' s) = (term65 _87566 _87575 x g x' s).
Proof. exact (eq_refl (term65 _87566 _87575 x g x' s)). Qed.
Lemma lem3369457 {_87566 : Type'} (P : _87566 -> Prop) : (term71 _87566 P) = (term72 _87566 P).
Proof. exact (@lem18394 _87566 P). Qed.
Lemma lem3369458 {_87566 _87575 : Type'} (x : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term82 _87566 _87575 x g s) = (term83 _87566 _87575 x g s).
Proof. exact (@lem3369457 _87566 (term66 _87566 _87575 x g s)). Qed.
Lemma lem3369459 {_87566 _87575 : Type'} (x : _87575) (g : _87566 -> _87575) (x' : _87566) (s : _87566 -> Prop) : (term84 _87566 _87575 x g s x') = (term65 _87566 _87575 x g x' s).
Proof. exact (eq_refl (term84 _87566 _87575 x g s x')). Qed.
Lemma lem3369460 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3369461 {_87566 _87575 : Type'} (x : _87575) (g : _87566 -> _87575) (x' : _87566) (s : _87566 -> Prop) : (term85 _87566 _87575 x g s x') = (term80 _87566 _87575 x g x' s).
Proof. exact (MK_COMB (@lem3369460) (@lem3369459 _87566 _87575 x g x' s)). Qed.
Lemma lem3369462 {_87566 _87575 : Type'} (x : _87575) (g : _87566 -> _87575) (x' : _87566) (s : _87566 -> Prop) : (term85 _87566 _87575 x g s x') = (term81 _87566 _87575 x g x' s).
Proof. exact (TRANS (@lem3369461 _87566 _87575 x g x' s) (@lem3369453 _87566 _87575 x g x' s)). Qed.
Lemma lem3369463 {_87566 _87575 : Type'} (x : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term86 _87566 _87575 x g s) = (term87 _87566 _87575 x g s).
Proof. exact (fun_ext (fun x' : _87566 => @lem3369462 _87566 _87575 x g x' s)). Qed.
Lemma lem3369464 {_87566 : Type'} : (@all _87566) = (@all _87566).
Proof. exact (eq_refl (@all _87566)). Qed.
Lemma lem3369465 {_87566 _87575 : Type'} (x : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term83 _87566 _87575 x g s) = (term88 _87566 _87575 x g s).
Proof. exact (MK_COMB (@lem3369464 _87566) (@lem3369463 _87566 _87575 x g s)). Qed.
Lemma lem3369466 {_87566 _87575 : Type'} (x : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term82 _87566 _87575 x g s) = (term88 _87566 _87575 x g s).
Proof. exact (TRANS (@lem3369458 _87566 _87575 x g s) (@lem3369465 _87566 _87575 x g s)). Qed.
Lemma lem3369467 {_87566 _87575 : Type'} (x : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term66 _87566 _87575 x g s) = (term66 _87566 _87575 x g s).
Proof. exact (fun_ext (fun x' : _87566 => @lem3369456 _87566 _87575 x g x' s)). Qed.
Lemma lem3369468 {_87566 : Type'} : (@ex _87566) = (@ex _87566).
Proof. exact (eq_refl (@ex _87566)). Qed.
Lemma lem3369469 {_87566 _87575 : Type'} (x : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term12 _87566 _87575 x g s) = (term12 _87566 _87575 x g s).
Proof. exact (MK_COMB (@lem3369468 _87566) (@lem3369467 _87566 _87575 x g s)). Qed.
Lemma lem3369471 {_87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) : (term89 _87571 _87575 x f x') = (term89 _87571 _87575 x f x').
Proof. exact (eq_refl (term89 _87571 _87575 x f x')). Qed.
Lemma lem3369472 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term90 _87566 _87571 _87575 x f x' g s) = (term91 _87566 _87571 _87575 x f x' g s).
Proof. exact (MK_COMB (@lem3369471 _87571 _87575 x f x') (@lem3369466 _87566 _87575 x' g s)). Qed.
Lemma lem3369473 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term92 _87566 _87571 _87575 x f x' g s) = (term90 _87566 _87571 _87575 x f x' g s).
Proof. exact (@lem17045 (x = (f x')) (term12 _87566 _87575 x' g s)). Qed.
Lemma lem3369474 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term92 _87566 _87571 _87575 x f x' g s) = (term91 _87566 _87571 _87575 x f x' g s).
Proof. exact (TRANS (@lem3369473 _87566 _87571 _87575 x f x' g s) (@lem3369472 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3369476 {_87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) : (term36 _87571 _87575 x f x') = (term36 _87571 _87575 x f x').
Proof. exact (eq_refl (term36 _87571 _87575 x f x')). Qed.
Lemma lem3369477 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term38 _87566 _87571 _87575 x f x' g s) = (term38 _87566 _87571 _87575 x f x' g s).
Proof. exact (MK_COMB (@lem3369476 _87571 _87575 x f x') (@lem3369469 _87566 _87575 x' g s)). Qed.
Lemma lem3369478 {_87575 : Type'} (P : _87575 -> Prop) : (term71 _87575 P) = (term72 _87575 P).
Proof. exact (@lem18394 _87575 P). Qed.
Lemma lem3369479 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term93 _87566 _87571 _87575 x f g s) = (term94 _87566 _87571 _87575 x f g s).
Proof. exact (@lem3369478 _87575 (term40 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369480 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term95 _87566 _87571 _87575 x f g s x') = (term38 _87566 _87571 _87575 x f x' g s).
Proof. exact (eq_refl (term95 _87566 _87571 _87575 x f g s x')). Qed.
Lemma lem3369481 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3369482 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term96 _87566 _87571 _87575 x f g s x') = (term92 _87566 _87571 _87575 x f x' g s).
Proof. exact (MK_COMB (@lem3369481) (@lem3369480 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3369483 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term96 _87566 _87571 _87575 x f g s x') = (term91 _87566 _87571 _87575 x f x' g s).
Proof. exact (TRANS (@lem3369482 _87566 _87571 _87575 x f x' g s) (@lem3369474 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3369484 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term97 _87566 _87571 _87575 x f g s) = (term98 _87566 _87571 _87575 x f g s).
Proof. exact (fun_ext (fun x' : _87575 => @lem3369483 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3369485 {_87575 : Type'} : (@all _87575) = (@all _87575).
Proof. exact (eq_refl (@all _87575)). Qed.
Lemma lem3369486 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term94 _87566 _87571 _87575 x f g s) = (term99 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369485 _87575) (@lem3369484 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369487 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term93 _87566 _87571 _87575 x f g s) = (term99 _87566 _87571 _87575 x f g s).
Proof. exact (TRANS (@lem3369479 _87566 _87571 _87575 x f g s) (@lem3369486 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369488 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term40 _87566 _87571 _87575 x f g s) = (term40 _87566 _87571 _87575 x f g s).
Proof. exact (fun_ext (fun x' : _87575 => @lem3369477 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3369489 {_87575 : Type'} : (@ex _87575) = (@ex _87575).
Proof. exact (eq_refl (@ex _87575)). Qed.
Lemma lem3369490 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term41 _87566 _87571 _87575 x f g s) = (term41 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369489 _87575) (@lem3369488 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369491 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3369492 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term100 _87566 _87571 _87575 x f g s) = (term101 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369491) (@lem3369439 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369493 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term102 _87566 _87571 _87575 x f g s) = (term103 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369492 _87566 _87571 _87575 x f g s) (@lem3369490 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369494 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3369495 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term104 _87566 _87571 _87575 x f g s) = (term104 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369494) (@lem3369442 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369496 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term105 _87566 _87571 _87575 x f g s) = (term106 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369495 _87566 _87571 _87575 x f g s) (@lem3369487 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369497 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3369498 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term107 _87566 _87571 _87575 x f g s) = (term108 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369497) (@lem3369496 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369499 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term109 _87566 _87571 _87575 x f g s) = (term110 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369498 _87566 _87571 _87575 x f g s) (@lem3369493 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369500 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term68 _87566 _87571 _87575 x f g s) = (term109 _87566 _87571 _87575 x f g s).
Proof. exact (@lem17646 (term29 _87566 _87571 _87575 x f g s) (term41 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369501 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term68 _87566 _87571 _87575 x f g s) = (term110 _87566 _87571 _87575 x f g s).
Proof. exact (TRANS (@lem3369500 _87566 _87571 _87575 x f g s) (@lem3369499 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369792 {A : Type'} (P : A -> Prop) (Q : Prop) : (term111 A P Q) = (term112 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3369793 {_87566 : Type'} (P : _87566 -> Prop) (Q : Prop) : (term111 _87566 P Q) = (term112 _87566 P Q).
Proof. exact (@lem3369792 _87566 P Q). Qed.
Lemma lem3369794 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term113 _87566 _87571 _87575 x f g s) = (term114 _87566 _87571 _87575 x f g s).
Proof. exact (@lem3369793 _87566 (term28 _87566 _87571 _87575 x f g s) (term99 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369795 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (x' : _87566) (s : _87566 -> Prop) : (term75 _87566 _87571 _87575 x f g s x') = (term26 _87566 _87571 _87575 x f g x' s).
Proof. exact (eq_refl (term75 _87566 _87571 _87575 x f g s x')). Qed.
Lemma lem3369796 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term115 _87566 _87571 _87575 x f g s) = (term28 _87566 _87571 _87575 x f g s).
Proof. exact (fun_ext (fun x' : _87566 => @lem3369795 _87566 _87571 _87575 x f g x' s)). Qed.
Lemma lem3369797 {_87566 : Type'} : (@ex _87566) = (@ex _87566).
Proof. exact (eq_refl (@ex _87566)). Qed.
Lemma lem3369798 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term116 _87566 _87571 _87575 x f g s) = (term29 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369797 _87566) (@lem3369796 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369799 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3369800 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term117 _87566 _87571 _87575 x f g s) = (term104 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369799) (@lem3369798 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369801 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term99 _87566 _87571 _87575 x f g s) = (term99 _87566 _87571 _87575 x f g s).
Proof. exact (eq_refl (term99 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369802 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term113 _87566 _87571 _87575 x f g s) = (term106 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369800 _87566 _87571 _87575 x f g s) (@lem3369801 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369803 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3369804 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term118 _87566 _87571 _87575 x f g s) = (term119 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369803) (@lem3369802 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369805 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (x' : _87566) (s : _87566 -> Prop) : (term75 _87566 _87571 _87575 x f g s x') = (term26 _87566 _87571 _87575 x f g x' s).
Proof. exact (eq_refl (term75 _87566 _87571 _87575 x f g s x')). Qed.
Lemma lem3369806 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3369807 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (x' : _87566) (s : _87566 -> Prop) : (term120 _87566 _87571 _87575 x f g s x') = (term121 _87566 _87571 _87575 x f g x' s).
Proof. exact (MK_COMB (@lem3369806) (@lem3369805 _87566 _87571 _87575 x f g x' s)). Qed.
Lemma lem3369808 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term99 _87566 _87571 _87575 x f g s) = (term99 _87566 _87571 _87575 x f g s).
Proof. exact (eq_refl (term99 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369809 {_87566 _87571 _87575 : Type'} (x : _87566) (x' : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term122 _87566 _87571 _87575 x x' f g s) = (term123 _87566 _87571 _87575 x x' f g s).
Proof. exact (MK_COMB (@lem3369807 _87566 _87571 _87575 x' f g x s) (@lem3369808 _87566 _87571 _87575 x' f g s)). Qed.
Lemma lem3369810 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term124 _87566 _87571 _87575 x f g s) = (term125 _87566 _87571 _87575 x f g s).
Proof. exact (fun_ext (fun x' : _87566 => @lem3369809 _87566 _87571 _87575 x' x f g s)). Qed.
Lemma lem3369811 {_87566 : Type'} : (@ex _87566) = (@ex _87566).
Proof. exact (eq_refl (@ex _87566)). Qed.
Lemma lem3369812 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term114 _87566 _87571 _87575 x f g s) = (term126 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369811 _87566) (@lem3369810 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369813 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : ((term113 _87566 _87571 _87575 x f g s) = (term114 _87566 _87571 _87575 x f g s)) = ((term106 _87566 _87571 _87575 x f g s) = (term126 _87566 _87571 _87575 x f g s)).
Proof. exact (MK_COMB (@lem3369804 _87566 _87571 _87575 x f g s) (@lem3369812 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369814 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term106 _87566 _87571 _87575 x f g s) = (term126 _87566 _87571 _87575 x f g s).
Proof. exact (EQ_MP (@lem3369813 _87566 _87571 _87575 x f g s) (@lem3369794 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369815 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3369816 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term108 _87566 _87571 _87575 x f g s) = (term127 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369815) (@lem3369814 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369818 {A : Type'} (P : Prop) (Q : A -> Prop) : (term128 A P Q) = (term129 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3369819 {_87566 : Type'} (P : Prop) (Q : _87566 -> Prop) : (term128 _87566 P Q) = (term129 _87566 P Q).
Proof. exact (@lem3369818 _87566 P Q). Qed.
Lemma lem3369820 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term130 _87566 _87571 _87575 x f x' g s) = (term131 _87566 _87571 _87575 x f x' g s).
Proof. exact (@lem3369819 _87566 (x = (f x')) (term66 _87566 _87575 x' g s)). Qed.
Lemma lem3369821 {_87566 _87575 : Type'} (x : _87575) (g : _87566 -> _87575) (x' : _87566) (s : _87566 -> Prop) : (term84 _87566 _87575 x g s x') = (term65 _87566 _87575 x g x' s).
Proof. exact (eq_refl (term84 _87566 _87575 x g s x')). Qed.
Lemma lem3369822 {_87566 _87575 : Type'} (x : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term132 _87566 _87575 x g s) = (term66 _87566 _87575 x g s).
Proof. exact (fun_ext (fun x' : _87566 => @lem3369821 _87566 _87575 x g x' s)). Qed.
Lemma lem3369823 {_87566 : Type'} : (@ex _87566) = (@ex _87566).
Proof. exact (eq_refl (@ex _87566)). Qed.
Lemma lem3369824 {_87566 _87575 : Type'} (x : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term133 _87566 _87575 x g s) = (term12 _87566 _87575 x g s).
Proof. exact (MK_COMB (@lem3369823 _87566) (@lem3369822 _87566 _87575 x g s)). Qed.
Lemma lem3369825 {_87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) : (term36 _87571 _87575 x f x') = (term36 _87571 _87575 x f x').
Proof. exact (eq_refl (term36 _87571 _87575 x f x')). Qed.
Lemma lem3369826 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term130 _87566 _87571 _87575 x f x' g s) = (term38 _87566 _87571 _87575 x f x' g s).
Proof. exact (MK_COMB (@lem3369825 _87571 _87575 x f x') (@lem3369824 _87566 _87575 x' g s)). Qed.
Lemma lem3369827 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3369828 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term134 _87566 _87571 _87575 x f x' g s) = (term135 _87566 _87571 _87575 x f x' g s).
Proof. exact (MK_COMB (@lem3369827) (@lem3369826 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3369829 {_87566 _87575 : Type'} (x : _87575) (g : _87566 -> _87575) (x' : _87566) (s : _87566 -> Prop) : (term84 _87566 _87575 x g s x') = (term65 _87566 _87575 x g x' s).
Proof. exact (eq_refl (term84 _87566 _87575 x g s x')). Qed.
Lemma lem3369830 {_87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) : (term36 _87571 _87575 x f x') = (term36 _87571 _87575 x f x').
Proof. exact (eq_refl (term36 _87571 _87575 x f x')). Qed.
Lemma lem3369831 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (x'' : _87566) (s : _87566 -> Prop) : (term136 _87566 _87571 _87575 x f x' g s x'') = (term137 _87566 _87571 _87575 x f x' g x'' s).
Proof. exact (MK_COMB (@lem3369830 _87571 _87575 x f x') (@lem3369829 _87566 _87575 x' g x'' s)). Qed.
Lemma lem3369832 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term138 _87566 _87571 _87575 x f x' g s) = (term139 _87566 _87571 _87575 x f x' g s).
Proof. exact (fun_ext (fun x'' : _87566 => @lem3369831 _87566 _87571 _87575 x f x' g x'' s)). Qed.
Lemma lem3369833 {_87566 : Type'} : (@ex _87566) = (@ex _87566).
Proof. exact (eq_refl (@ex _87566)). Qed.
Lemma lem3369834 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term131 _87566 _87571 _87575 x f x' g s) = (term140 _87566 _87571 _87575 x f x' g s).
Proof. exact (MK_COMB (@lem3369833 _87566) (@lem3369832 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3369835 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : ((term130 _87566 _87571 _87575 x f x' g s) = (term131 _87566 _87571 _87575 x f x' g s)) = ((term38 _87566 _87571 _87575 x f x' g s) = (term140 _87566 _87571 _87575 x f x' g s)).
Proof. exact (MK_COMB (@lem3369828 _87566 _87571 _87575 x f x' g s) (@lem3369834 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3369836 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term38 _87566 _87571 _87575 x f x' g s) = (term140 _87566 _87571 _87575 x f x' g s).
Proof. exact (EQ_MP (@lem3369835 _87566 _87571 _87575 x f x' g s) (@lem3369820 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3369837 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term40 _87566 _87571 _87575 x f g s) = (term141 _87566 _87571 _87575 x f g s).
Proof. exact (fun_ext (fun x' : _87575 => @lem3369836 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3369838 {_87575 : Type'} : (@ex _87575) = (@ex _87575).
Proof. exact (eq_refl (@ex _87575)). Qed.
Lemma lem3369839 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term41 _87566 _87571 _87575 x f g s) = (term142 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369838 _87575) (@lem3369837 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369840 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term101 _87566 _87571 _87575 x f g s) = (term101 _87566 _87571 _87575 x f g s).
Proof. exact (eq_refl (term101 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369841 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term103 _87566 _87571 _87575 x f g s) = (term143 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369840 _87566 _87571 _87575 x f g s) (@lem3369839 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369843 {A : Type'} (P : Prop) (Q : A -> Prop) : (term128 A P Q) = (term129 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3369844 {_87575 : Type'} (P : Prop) (Q : _87575 -> Prop) : (term128 _87575 P Q) = (term129 _87575 P Q).
Proof. exact (@lem3369843 _87575 P Q). Qed.
Lemma lem3369845 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term144 _87566 _87571 _87575 x f g s) = (term145 _87566 _87571 _87575 x f g s).
Proof. exact (@lem3369844 _87575 (term79 _87566 _87571 _87575 x f g s) (term141 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369846 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term146 _87566 _87571 _87575 x f g s x') = (term140 _87566 _87571 _87575 x f x' g s).
Proof. exact (eq_refl (term146 _87566 _87571 _87575 x f g s x')). Qed.
Lemma lem3369847 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term147 _87566 _87571 _87575 x f g s) = (term141 _87566 _87571 _87575 x f g s).
Proof. exact (fun_ext (fun x' : _87575 => @lem3369846 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3369848 {_87575 : Type'} : (@ex _87575) = (@ex _87575).
Proof. exact (eq_refl (@ex _87575)). Qed.
Lemma lem3369849 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term148 _87566 _87571 _87575 x f g s) = (term142 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369848 _87575) (@lem3369847 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369850 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term101 _87566 _87571 _87575 x f g s) = (term101 _87566 _87571 _87575 x f g s).
Proof. exact (eq_refl (term101 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369851 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term144 _87566 _87571 _87575 x f g s) = (term143 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369850 _87566 _87571 _87575 x f g s) (@lem3369849 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369852 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3369853 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term149 _87566 _87571 _87575 x f g s) = (term150 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369852) (@lem3369851 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369854 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term146 _87566 _87571 _87575 x f g s x') = (term140 _87566 _87571 _87575 x f x' g s).
Proof. exact (eq_refl (term146 _87566 _87571 _87575 x f g s x')). Qed.
Lemma lem3369855 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term101 _87566 _87571 _87575 x f g s) = (term101 _87566 _87571 _87575 x f g s).
Proof. exact (eq_refl (term101 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369856 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term151 _87566 _87571 _87575 x f g s x') = (term152 _87566 _87571 _87575 x f x' g s).
Proof. exact (MK_COMB (@lem3369855 _87566 _87571 _87575 x f g s) (@lem3369854 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3369857 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term153 _87566 _87571 _87575 x f g s) = (term154 _87566 _87571 _87575 x f g s).
Proof. exact (fun_ext (fun x' : _87575 => @lem3369856 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3369858 {_87575 : Type'} : (@ex _87575) = (@ex _87575).
Proof. exact (eq_refl (@ex _87575)). Qed.
Lemma lem3369859 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term145 _87566 _87571 _87575 x f g s) = (term155 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369858 _87575) (@lem3369857 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369860 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : ((term144 _87566 _87571 _87575 x f g s) = (term145 _87566 _87571 _87575 x f g s)) = ((term143 _87566 _87571 _87575 x f g s) = (term155 _87566 _87571 _87575 x f g s)).
Proof. exact (MK_COMB (@lem3369853 _87566 _87571 _87575 x f g s) (@lem3369859 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369861 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term143 _87566 _87571 _87575 x f g s) = (term155 _87566 _87571 _87575 x f g s).
Proof. exact (EQ_MP (@lem3369860 _87566 _87571 _87575 x f g s) (@lem3369845 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369863 {A : Type'} (P : Prop) (Q : A -> Prop) : (term128 A P Q) = (term129 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3369864 {_87566 : Type'} (P : Prop) (Q : _87566 -> Prop) : (term128 _87566 P Q) = (term129 _87566 P Q).
Proof. exact (@lem3369863 _87566 P Q). Qed.
Lemma lem3369865 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term156 _87566 _87571 _87575 x f x' g s) = (term157 _87566 _87571 _87575 x f x' g s).
Proof. exact (@lem3369864 _87566 (term79 _87566 _87571 _87575 x f g s) (term139 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3369866 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (x'' : _87566) (s : _87566 -> Prop) : (term158 _87566 _87571 _87575 x f x' g s x'') = (term137 _87566 _87571 _87575 x f x' g x'' s).
Proof. exact (eq_refl (term158 _87566 _87571 _87575 x f x' g s x'')). Qed.
Lemma lem3369867 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term159 _87566 _87571 _87575 x f x' g s) = (term139 _87566 _87571 _87575 x f x' g s).
Proof. exact (fun_ext (fun x'' : _87566 => @lem3369866 _87566 _87571 _87575 x f x' g x'' s)). Qed.
Lemma lem3369868 {_87566 : Type'} : (@ex _87566) = (@ex _87566).
Proof. exact (eq_refl (@ex _87566)). Qed.
Lemma lem3369869 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term160 _87566 _87571 _87575 x f x' g s) = (term140 _87566 _87571 _87575 x f x' g s).
Proof. exact (MK_COMB (@lem3369868 _87566) (@lem3369867 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3369870 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term101 _87566 _87571 _87575 x f g s) = (term101 _87566 _87571 _87575 x f g s).
Proof. exact (eq_refl (term101 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369871 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term156 _87566 _87571 _87575 x f x' g s) = (term152 _87566 _87571 _87575 x f x' g s).
Proof. exact (MK_COMB (@lem3369870 _87566 _87571 _87575 x f g s) (@lem3369869 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3369872 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3369873 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term161 _87566 _87571 _87575 x f x' g s) = (term162 _87566 _87571 _87575 x f x' g s).
Proof. exact (MK_COMB (@lem3369872) (@lem3369871 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3369874 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (x'' : _87566) (s : _87566 -> Prop) : (term158 _87566 _87571 _87575 x f x' g s x'') = (term137 _87566 _87571 _87575 x f x' g x'' s).
Proof. exact (eq_refl (term158 _87566 _87571 _87575 x f x' g s x'')). Qed.
Lemma lem3369875 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term101 _87566 _87571 _87575 x f g s) = (term101 _87566 _87571 _87575 x f g s).
Proof. exact (eq_refl (term101 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369876 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (x'' : _87566) (s : _87566 -> Prop) : (term163 _87566 _87571 _87575 x f x' g s x'') = (term164 _87566 _87571 _87575 x f x' g x'' s).
Proof. exact (MK_COMB (@lem3369875 _87566 _87571 _87575 x f g s) (@lem3369874 _87566 _87571 _87575 x f x' g x'' s)). Qed.
Lemma lem3369877 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term165 _87566 _87571 _87575 x f x' g s) = (term166 _87566 _87571 _87575 x f x' g s).
Proof. exact (fun_ext (fun x'' : _87566 => @lem3369876 _87566 _87571 _87575 x f x' g x'' s)). Qed.
Lemma lem3369878 {_87566 : Type'} : (@ex _87566) = (@ex _87566).
Proof. exact (eq_refl (@ex _87566)). Qed.
Lemma lem3369879 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term157 _87566 _87571 _87575 x f x' g s) = (term167 _87566 _87571 _87575 x f x' g s).
Proof. exact (MK_COMB (@lem3369878 _87566) (@lem3369877 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3369880 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : ((term156 _87566 _87571 _87575 x f x' g s) = (term157 _87566 _87571 _87575 x f x' g s)) = ((term152 _87566 _87571 _87575 x f x' g s) = (term167 _87566 _87571 _87575 x f x' g s)).
Proof. exact (MK_COMB (@lem3369873 _87566 _87571 _87575 x f x' g s) (@lem3369879 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3369881 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term152 _87566 _87571 _87575 x f x' g s) = (term167 _87566 _87571 _87575 x f x' g s).
Proof. exact (EQ_MP (@lem3369880 _87566 _87571 _87575 x f x' g s) (@lem3369865 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3369882 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term154 _87566 _87571 _87575 x f g s) = (term168 _87566 _87571 _87575 x f g s).
Proof. exact (fun_ext (fun x' : _87575 => @lem3369881 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3369883 {_87575 : Type'} : (@ex _87575) = (@ex _87575).
Proof. exact (eq_refl (@ex _87575)). Qed.
Lemma lem3369884 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term155 _87566 _87571 _87575 x f g s) = (term169 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369883 _87575) (@lem3369882 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369885 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term143 _87566 _87571 _87575 x f g s) = (term169 _87566 _87571 _87575 x f g s).
Proof. exact (TRANS (@lem3369861 _87566 _87571 _87575 x f g s) (@lem3369884 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369886 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term103 _87566 _87571 _87575 x f g s) = (term169 _87566 _87571 _87575 x f g s).
Proof. exact (TRANS (@lem3369841 _87566 _87571 _87575 x f g s) (@lem3369885 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369887 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term110 _87566 _87571 _87575 x f g s) = (term170 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369816 _87566 _87571 _87575 x f g s) (@lem3369886 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369891 {A : Type'} (P : A -> Prop) (Q : Prop) : (term171 A P Q) = (term172 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3369892 {_87566 : Type'} (P : _87566 -> Prop) (Q : Prop) : (term171 _87566 P Q) = (term172 _87566 P Q).
Proof. exact (@lem3369891 _87566 P Q). Qed.
Lemma lem3369893 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term173 _87566 _87571 _87575 x f g s) = (term174 _87566 _87571 _87575 x f g s).
Proof. exact (@lem3369892 _87566 (term125 _87566 _87571 _87575 x f g s) (term169 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369894 {_87566 _87571 _87575 : Type'} (x : _87566) (x' : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term175 _87566 _87571 _87575 x' f g s x) = (term123 _87566 _87571 _87575 x x' f g s).
Proof. exact (eq_refl (term175 _87566 _87571 _87575 x' f g s x)). Qed.
Lemma lem3369895 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term176 _87566 _87571 _87575 x f g s) = (term125 _87566 _87571 _87575 x f g s).
Proof. exact (fun_ext (fun x' : _87566 => @lem3369894 _87566 _87571 _87575 x' x f g s)). Qed.
Lemma lem3369896 {_87566 : Type'} : (@ex _87566) = (@ex _87566).
Proof. exact (eq_refl (@ex _87566)). Qed.
Lemma lem3369897 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term177 _87566 _87571 _87575 x f g s) = (term126 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369896 _87566) (@lem3369895 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369898 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3369899 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term178 _87566 _87571 _87575 x f g s) = (term127 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369898) (@lem3369897 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369900 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term169 _87566 _87571 _87575 x f g s) = (term169 _87566 _87571 _87575 x f g s).
Proof. exact (eq_refl (term169 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369901 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term173 _87566 _87571 _87575 x f g s) = (term170 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369899 _87566 _87571 _87575 x f g s) (@lem3369900 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369902 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3369903 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term179 _87566 _87571 _87575 x f g s) = (term180 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369902) (@lem3369901 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369904 {_87566 _87571 _87575 : Type'} (x : _87566) (x' : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term175 _87566 _87571 _87575 x' f g s x) = (term123 _87566 _87571 _87575 x x' f g s).
Proof. exact (eq_refl (term175 _87566 _87571 _87575 x' f g s x)). Qed.
Lemma lem3369905 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3369906 {_87566 _87571 _87575 : Type'} (x : _87566) (x' : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term181 _87566 _87571 _87575 x' f g s x) = (term182 _87566 _87571 _87575 x x' f g s).
Proof. exact (MK_COMB (@lem3369905) (@lem3369904 _87566 _87571 _87575 x x' f g s)). Qed.
Lemma lem3369907 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term169 _87566 _87571 _87575 x f g s) = (term169 _87566 _87571 _87575 x f g s).
Proof. exact (eq_refl (term169 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369908 {_87566 _87571 _87575 : Type'} (x : _87566) (x' : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term183 _87566 _87571 _87575 x x' f g s) = (term184 _87566 _87571 _87575 x x' f g s).
Proof. exact (MK_COMB (@lem3369906 _87566 _87571 _87575 x x' f g s) (@lem3369907 _87566 _87571 _87575 x' f g s)). Qed.
Lemma lem3369909 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term185 _87566 _87571 _87575 x f g s) = (term186 _87566 _87571 _87575 x f g s).
Proof. exact (fun_ext (fun x' : _87566 => @lem3369908 _87566 _87571 _87575 x' x f g s)). Qed.
Lemma lem3369910 {_87566 : Type'} : (@ex _87566) = (@ex _87566).
Proof. exact (eq_refl (@ex _87566)). Qed.
Lemma lem3369911 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term174 _87566 _87571 _87575 x f g s) = (term187 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369910 _87566) (@lem3369909 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369912 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : ((term173 _87566 _87571 _87575 x f g s) = (term174 _87566 _87571 _87575 x f g s)) = ((term170 _87566 _87571 _87575 x f g s) = (term187 _87566 _87571 _87575 x f g s)).
Proof. exact (MK_COMB (@lem3369903 _87566 _87571 _87575 x f g s) (@lem3369911 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369913 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term170 _87566 _87571 _87575 x f g s) = (term187 _87566 _87571 _87575 x f g s).
Proof. exact (EQ_MP (@lem3369912 _87566 _87571 _87575 x f g s) (@lem3369893 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369915 {A : Type'} (P : Prop) (Q : A -> Prop) : (term188 A P Q) = (term189 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3369916 {_87575 : Type'} (P : Prop) (Q : _87575 -> Prop) : (term188 _87575 P Q) = (term189 _87575 P Q).
Proof. exact (@lem3369915 _87575 P Q). Qed.
Lemma lem3369917 {_87566 _87571 _87575 : Type'} (x : _87566) (x' : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term190 _87566 _87571 _87575 x x' f g s) = (term191 _87566 _87571 _87575 x x' f g s).
Proof. exact (@lem3369916 _87575 (term123 _87566 _87571 _87575 x x' f g s) (term168 _87566 _87571 _87575 x' f g s)). Qed.
Lemma lem3369918 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term192 _87566 _87571 _87575 x f g s x') = (term167 _87566 _87571 _87575 x f x' g s).
Proof. exact (eq_refl (term192 _87566 _87571 _87575 x f g s x')). Qed.
Lemma lem3369919 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term193 _87566 _87571 _87575 x f g s) = (term168 _87566 _87571 _87575 x f g s).
Proof. exact (fun_ext (fun x' : _87575 => @lem3369918 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3369920 {_87575 : Type'} : (@ex _87575) = (@ex _87575).
Proof. exact (eq_refl (@ex _87575)). Qed.
Lemma lem3369921 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term194 _87566 _87571 _87575 x f g s) = (term169 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369920 _87575) (@lem3369919 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369922 {_87566 _87571 _87575 : Type'} (x : _87566) (x' : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term182 _87566 _87571 _87575 x x' f g s) = (term182 _87566 _87571 _87575 x x' f g s).
Proof. exact (eq_refl (term182 _87566 _87571 _87575 x x' f g s)). Qed.
Lemma lem3369923 {_87566 _87571 _87575 : Type'} (x : _87566) (x' : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term190 _87566 _87571 _87575 x x' f g s) = (term184 _87566 _87571 _87575 x x' f g s).
Proof. exact (MK_COMB (@lem3369922 _87566 _87571 _87575 x x' f g s) (@lem3369921 _87566 _87571 _87575 x' f g s)). Qed.
Lemma lem3369924 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3369925 {_87566 _87571 _87575 : Type'} (x : _87566) (x' : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term195 _87566 _87571 _87575 x x' f g s) = (term196 _87566 _87571 _87575 x x' f g s).
Proof. exact (MK_COMB (@lem3369924) (@lem3369923 _87566 _87571 _87575 x x' f g s)). Qed.
Lemma lem3369926 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term192 _87566 _87571 _87575 x f g s x') = (term167 _87566 _87571 _87575 x f x' g s).
Proof. exact (eq_refl (term192 _87566 _87571 _87575 x f g s x')). Qed.
Lemma lem3369927 {_87566 _87571 _87575 : Type'} (x : _87566) (x' : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term182 _87566 _87571 _87575 x x' f g s) = (term182 _87566 _87571 _87575 x x' f g s).
Proof. exact (eq_refl (term182 _87566 _87571 _87575 x x' f g s)). Qed.
Lemma lem3369928 {_87566 _87571 _87575 : Type'} (x : _87566) (x' : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term197 _87566 _87571 _87575 x x' f g s x'') = (term198 _87566 _87571 _87575 x x' f x'' g s).
Proof. exact (MK_COMB (@lem3369927 _87566 _87571 _87575 x x' f g s) (@lem3369926 _87566 _87571 _87575 x' f x'' g s)). Qed.
Lemma lem3369929 {_87566 _87571 _87575 : Type'} (x : _87566) (x' : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term199 _87566 _87571 _87575 x x' f g s) = (term200 _87566 _87571 _87575 x x' f g s).
Proof. exact (fun_ext (fun x'' : _87575 => @lem3369928 _87566 _87571 _87575 x x' f x'' g s)). Qed.
Lemma lem3369930 {_87575 : Type'} : (@ex _87575) = (@ex _87575).
Proof. exact (eq_refl (@ex _87575)). Qed.
Lemma lem3369931 {_87566 _87571 _87575 : Type'} (x : _87566) (x' : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term191 _87566 _87571 _87575 x x' f g s) = (term201 _87566 _87571 _87575 x x' f g s).
Proof. exact (MK_COMB (@lem3369930 _87575) (@lem3369929 _87566 _87571 _87575 x x' f g s)). Qed.
Lemma lem3369932 {_87566 _87571 _87575 : Type'} (x : _87566) (x' : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : ((term190 _87566 _87571 _87575 x x' f g s) = (term191 _87566 _87571 _87575 x x' f g s)) = ((term184 _87566 _87571 _87575 x x' f g s) = (term201 _87566 _87571 _87575 x x' f g s)).
Proof. exact (MK_COMB (@lem3369925 _87566 _87571 _87575 x x' f g s) (@lem3369931 _87566 _87571 _87575 x x' f g s)). Qed.
Lemma lem3369933 {_87566 _87571 _87575 : Type'} (x : _87566) (x' : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term184 _87566 _87571 _87575 x x' f g s) = (term201 _87566 _87571 _87575 x x' f g s).
Proof. exact (EQ_MP (@lem3369932 _87566 _87571 _87575 x x' f g s) (@lem3369917 _87566 _87571 _87575 x x' f g s)). Qed.
Lemma lem3369935 {A : Type'} (P : Prop) (Q : A -> Prop) : (term188 A P Q) = (term189 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3369936 {_87566 : Type'} (P : Prop) (Q : _87566 -> Prop) : (term188 _87566 P Q) = (term189 _87566 P Q).
Proof. exact (@lem3369935 _87566 P Q). Qed.
Lemma lem3369937 {_87566 _87571 _87575 : Type'} (x : _87566) (x' : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term202 _87566 _87571 _87575 x x' f x'' g s) = (term203 _87566 _87571 _87575 x x' f x'' g s).
Proof. exact (@lem3369936 _87566 (term123 _87566 _87571 _87575 x x' f g s) (term166 _87566 _87571 _87575 x' f x'' g s)). Qed.
Lemma lem3369938 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (x'' : _87566) (s : _87566 -> Prop) : (term204 _87566 _87571 _87575 x f x' g s x'') = (term164 _87566 _87571 _87575 x f x' g x'' s).
Proof. exact (eq_refl (term204 _87566 _87571 _87575 x f x' g s x'')). Qed.
Lemma lem3369939 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term205 _87566 _87571 _87575 x f x' g s) = (term166 _87566 _87571 _87575 x f x' g s).
Proof. exact (fun_ext (fun x'' : _87566 => @lem3369938 _87566 _87571 _87575 x f x' g x'' s)). Qed.
Lemma lem3369940 {_87566 : Type'} : (@ex _87566) = (@ex _87566).
Proof. exact (eq_refl (@ex _87566)). Qed.
Lemma lem3369941 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term206 _87566 _87571 _87575 x f x' g s) = (term167 _87566 _87571 _87575 x f x' g s).
Proof. exact (MK_COMB (@lem3369940 _87566) (@lem3369939 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3369942 {_87566 _87571 _87575 : Type'} (x : _87566) (x' : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term182 _87566 _87571 _87575 x x' f g s) = (term182 _87566 _87571 _87575 x x' f g s).
Proof. exact (eq_refl (term182 _87566 _87571 _87575 x x' f g s)). Qed.
Lemma lem3369943 {_87566 _87571 _87575 : Type'} (x : _87566) (x' : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term202 _87566 _87571 _87575 x x' f x'' g s) = (term198 _87566 _87571 _87575 x x' f x'' g s).
Proof. exact (MK_COMB (@lem3369942 _87566 _87571 _87575 x x' f g s) (@lem3369941 _87566 _87571 _87575 x' f x'' g s)). Qed.
Lemma lem3369944 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3369945 {_87566 _87571 _87575 : Type'} (x : _87566) (x' : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term207 _87566 _87571 _87575 x x' f x'' g s) = (term208 _87566 _87571 _87575 x x' f x'' g s).
Proof. exact (MK_COMB (@lem3369944) (@lem3369943 _87566 _87571 _87575 x x' f x'' g s)). Qed.
Lemma lem3369946 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (x'' : _87566) (s : _87566 -> Prop) : (term204 _87566 _87571 _87575 x f x' g s x'') = (term164 _87566 _87571 _87575 x f x' g x'' s).
Proof. exact (eq_refl (term204 _87566 _87571 _87575 x f x' g s x'')). Qed.
Lemma lem3369947 {_87566 _87571 _87575 : Type'} (x : _87566) (x' : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term182 _87566 _87571 _87575 x x' f g s) = (term182 _87566 _87571 _87575 x x' f g s).
Proof. exact (eq_refl (term182 _87566 _87571 _87575 x x' f g s)). Qed.
Lemma lem3369948 {_87566 _87571 _87575 : Type'} (x : _87566) (x' : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) : (term209 _87566 _87571 _87575 x x' f x'' g s x''') = (term210 _87566 _87571 _87575 x x' f x'' g x''' s).
Proof. exact (MK_COMB (@lem3369947 _87566 _87571 _87575 x x' f g s) (@lem3369946 _87566 _87571 _87575 x' f x'' g x''' s)). Qed.
Lemma lem3369949 {_87566 _87571 _87575 : Type'} (x : _87566) (x' : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term211 _87566 _87571 _87575 x x' f x'' g s) = (term212 _87566 _87571 _87575 x x' f x'' g s).
Proof. exact (fun_ext (fun x''' : _87566 => @lem3369948 _87566 _87571 _87575 x x' f x'' g x''' s)). Qed.
Lemma lem3369950 {_87566 : Type'} : (@ex _87566) = (@ex _87566).
Proof. exact (eq_refl (@ex _87566)). Qed.
Lemma lem3369951 {_87566 _87571 _87575 : Type'} (x : _87566) (x' : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term203 _87566 _87571 _87575 x x' f x'' g s) = (term213 _87566 _87571 _87575 x x' f x'' g s).
Proof. exact (MK_COMB (@lem3369950 _87566) (@lem3369949 _87566 _87571 _87575 x x' f x'' g s)). Qed.
Lemma lem3369952 {_87566 _87571 _87575 : Type'} (x : _87566) (x' : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : ((term202 _87566 _87571 _87575 x x' f x'' g s) = (term203 _87566 _87571 _87575 x x' f x'' g s)) = ((term198 _87566 _87571 _87575 x x' f x'' g s) = (term213 _87566 _87571 _87575 x x' f x'' g s)).
Proof. exact (MK_COMB (@lem3369945 _87566 _87571 _87575 x x' f x'' g s) (@lem3369951 _87566 _87571 _87575 x x' f x'' g s)). Qed.
Lemma lem3369953 {_87566 _87571 _87575 : Type'} (x : _87566) (x' : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term198 _87566 _87571 _87575 x x' f x'' g s) = (term213 _87566 _87571 _87575 x x' f x'' g s).
Proof. exact (EQ_MP (@lem3369952 _87566 _87571 _87575 x x' f x'' g s) (@lem3369937 _87566 _87571 _87575 x x' f x'' g s)). Qed.
Lemma lem3369954 {_87566 _87571 _87575 : Type'} (x : _87566) (x' : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term200 _87566 _87571 _87575 x x' f g s) = (term214 _87566 _87571 _87575 x x' f g s).
Proof. exact (fun_ext (fun x'' : _87575 => @lem3369953 _87566 _87571 _87575 x x' f x'' g s)). Qed.
Lemma lem3369955 {_87575 : Type'} : (@ex _87575) = (@ex _87575).
Proof. exact (eq_refl (@ex _87575)). Qed.
Lemma lem3369956 {_87566 _87571 _87575 : Type'} (x : _87566) (x' : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term201 _87566 _87571 _87575 x x' f g s) = (term215 _87566 _87571 _87575 x x' f g s).
Proof. exact (MK_COMB (@lem3369955 _87575) (@lem3369954 _87566 _87571 _87575 x x' f g s)). Qed.
Lemma lem3369957 {_87566 _87571 _87575 : Type'} (x : _87566) (x' : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term184 _87566 _87571 _87575 x x' f g s) = (term215 _87566 _87571 _87575 x x' f g s).
Proof. exact (TRANS (@lem3369933 _87566 _87571 _87575 x x' f g s) (@lem3369956 _87566 _87571 _87575 x x' f g s)). Qed.
Lemma lem3369958 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term186 _87566 _87571 _87575 x f g s) = (term216 _87566 _87571 _87575 x f g s).
Proof. exact (fun_ext (fun x' : _87566 => @lem3369957 _87566 _87571 _87575 x' x f g s)). Qed.
Lemma lem3369959 {_87566 : Type'} : (@ex _87566) = (@ex _87566).
Proof. exact (eq_refl (@ex _87566)). Qed.
Lemma lem3369960 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term187 _87566 _87571 _87575 x f g s) = (term217 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3369959 _87566) (@lem3369958 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369961 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term170 _87566 _87571 _87575 x f g s) = (term217 _87566 _87571 _87575 x f g s).
Proof. exact (TRANS (@lem3369913 _87566 _87571 _87575 x f g s) (@lem3369960 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369963 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term110 _87566 _87571 _87575 x f g s) = (term217 _87566 _87571 _87575 x f g s).
Proof. exact (TRANS (@lem3369887 _87566 _87571 _87575 x f g s) (@lem3369961 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369964 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term68 _87566 _87571 _87575 x f g s) = (term217 _87566 _87571 _87575 x f g s).
Proof. exact (TRANS (@lem3369501 _87566 _87571 _87575 x f g s) (@lem3369963 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3369965 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : term68 _87566 _87571 _87575 x f g s) : term217 _87566 _87571 _87575 x f g s.
Proof. exact (EQ_MP (@lem3369964 _87566 _87571 _87575 x f g s) (@lem3369417 _87566 _87571 _87575 x f g s h1)). Qed.
Lemma lem3369966 {_87566 _87571 _87575 : Type'} (x' : _87566) (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : term215 _87566 _87571 _87575 x' x f g s) : term215 _87566 _87571 _87575 x' x f g s.
Proof. exact (h1). Qed.
Lemma lem3369967 {_87566 _87571 _87575 : Type'} (x' : _87566) (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : term213 _87566 _87571 _87575 x' x f x'' g s) : term213 _87566 _87571 _87575 x' x f x'' g s.
Proof. exact (h1). Qed.
Lemma lem3369968 {_87566 _87571 _87575 : Type'} (x' : _87566) (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) (h1 : term210 _87566 _87571 _87575 x' x f x'' g x''' s) : term210 _87566 _87571 _87575 x' x f x'' g x''' s.
Proof. exact (h1). Qed.
Lemma lem3369993 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) : (term137 _87566 _87571 _87575 x f x'' g x''' s) = (term137 _87566 _87571 _87575 x f x'' g x''' s).
Proof. exact (eq_refl (term137 _87566 _87571 _87575 x f x'' g x''' s)). Qed.
Lemma lem3370014 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (x' : _87566) (s : _87566 -> Prop) : (term70 _87566 _87571 _87575 x f g x' s) = (term70 _87566 _87571 _87575 x f g x' s).
Proof. exact (eq_refl (term70 _87566 _87571 _87575 x f g x' s)). Qed.
Lemma lem3370015 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term78 _87566 _87571 _87575 x f g s) = (term78 _87566 _87571 _87575 x f g s).
Proof. exact (fun_ext (fun x' : _87566 => @lem3370014 _87566 _87571 _87575 x f g x' s)). Qed.
Lemma lem3370016 {_87566 : Type'} : (@all _87566) = (@all _87566).
Proof. exact (eq_refl (@all _87566)). Qed.
Lemma lem3370017 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term79 _87566 _87571 _87575 x f g s) = (term79 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3370016 _87566) (@lem3370015 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3370018 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3370019 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term101 _87566 _87571 _87575 x f g s) = (term101 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3370018) (@lem3370017 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3370020 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) : (term164 _87566 _87571 _87575 x f x'' g x''' s) = (term164 _87566 _87571 _87575 x f x'' g x''' s).
Proof. exact (MK_COMB (@lem3370019 _87566 _87571 _87575 x f g s) (@lem3369993 _87566 _87571 _87575 x f x'' g x''' s)). Qed.
Lemma lem3370039 {_87566 _87575 : Type'} (x : _87575) (g : _87566 -> _87575) (x' : _87566) (s : _87566 -> Prop) : (term81 _87566 _87575 x g x' s) = (term81 _87566 _87575 x g x' s).
Proof. exact (eq_refl (term81 _87566 _87575 x g x' s)). Qed.
Lemma lem3370040 {_87566 _87575 : Type'} (x : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term87 _87566 _87575 x g s) = (term87 _87566 _87575 x g s).
Proof. exact (fun_ext (fun x' : _87566 => @lem3370039 _87566 _87575 x g x' s)). Qed.
Lemma lem3370041 {_87566 : Type'} : (@all _87566) = (@all _87566).
Proof. exact (eq_refl (@all _87566)). Qed.
Lemma lem3370042 {_87566 _87575 : Type'} (x : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term88 _87566 _87575 x g s) = (term88 _87566 _87575 x g s).
Proof. exact (MK_COMB (@lem3370041 _87566) (@lem3370040 _87566 _87575 x g s)). Qed.
Lemma lem3370053 {_87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) : (term89 _87571 _87575 x f x') = (term89 _87571 _87575 x f x').
Proof. exact (eq_refl (term89 _87571 _87575 x f x')). Qed.
Lemma lem3370054 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term91 _87566 _87571 _87575 x f x' g s) = (term91 _87566 _87571 _87575 x f x' g s).
Proof. exact (MK_COMB (@lem3370053 _87571 _87575 x f x') (@lem3370042 _87566 _87575 x' g s)). Qed.
Lemma lem3370055 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term98 _87566 _87571 _87575 x f g s) = (term98 _87566 _87571 _87575 x f g s).
Proof. exact (fun_ext (fun x' : _87575 => @lem3370054 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3370056 {_87575 : Type'} : (@all _87575) = (@all _87575).
Proof. exact (eq_refl (@all _87575)). Qed.
Lemma lem3370057 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term99 _87566 _87571 _87575 x f g s) = (term99 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3370056 _87575) (@lem3370055 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3370076 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (x' : _87566) (s : _87566 -> Prop) : (term121 _87566 _87571 _87575 x f g x' s) = (term121 _87566 _87571 _87575 x f g x' s).
Proof. exact (eq_refl (term121 _87566 _87571 _87575 x f g x' s)). Qed.
Lemma lem3370077 {_87566 _87571 _87575 : Type'} (x' : _87566) (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term123 _87566 _87571 _87575 x' x f g s) = (term123 _87566 _87571 _87575 x' x f g s).
Proof. exact (MK_COMB (@lem3370076 _87566 _87571 _87575 x f g x' s) (@lem3370057 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3370078 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3370079 {_87566 _87571 _87575 : Type'} (x' : _87566) (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term182 _87566 _87571 _87575 x' x f g s) = (term182 _87566 _87571 _87575 x' x f g s).
Proof. exact (MK_COMB (@lem3370078) (@lem3370077 _87566 _87571 _87575 x' x f g s)). Qed.
Lemma lem3370080 {_87566 _87571 _87575 : Type'} (x' : _87566) (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) : (term210 _87566 _87571 _87575 x' x f x'' g x''' s) = (term210 _87566 _87571 _87575 x' x f x'' g x''' s).
Proof. exact (MK_COMB (@lem3370079 _87566 _87571 _87575 x' x f g s) (@lem3370020 _87566 _87571 _87575 x f x'' g x''' s)). Qed.
Lemma lem3370081 {_87566 _87571 _87575 : Type'} (x' : _87566) (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) (h1 : term210 _87566 _87571 _87575 x' x f x'' g x''' s) : term210 _87566 _87571 _87575 x' x f x'' g x''' s.
Proof. exact (EQ_MP (@lem3370080 _87566 _87571 _87575 x' x f x'' g x''' s) (@lem3369968 _87566 _87571 _87575 x' x f x'' g x''' s h1)). Qed.
Lemma lem3370082 {_87566 _87571 _87575 : Type'} (x' : _87566) (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : term123 _87566 _87571 _87575 x' x f g s) : term123 _87566 _87571 _87575 x' x f g s.
Proof. exact (h1). Qed.
Lemma lem3370083 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) (h1 : term164 _87566 _87571 _87575 x f x'' g x''' s) : term164 _87566 _87571 _87575 x f x'' g x''' s.
Proof. exact (h1). Qed.
Lemma lem3370084 {_87566 _87571 _87575 : Type'} (x' : _87566) (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : term123 _87566 _87571 _87575 x' x f g s) : term99 _87566 _87571 _87575 x f g s.
Proof. exact (proj2 (@lem3370082 _87566 _87571 _87575 x' x f g s h1)). Qed.
Lemma lem3370085 {_87566 _87571 _87575 : Type'} (x' : _87566) (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : term123 _87566 _87571 _87575 x' x f g s) : term26 _87566 _87571 _87575 x f g x' s.
Proof. exact (proj1 (@lem3370082 _87566 _87571 _87575 x' x f g s h1)). Qed.
Lemma lem3370088 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) (h1 : term164 _87566 _87571 _87575 x f x'' g x''' s) : term137 _87566 _87571 _87575 x f x'' g x''' s.
Proof. exact (proj2 (@lem3370083 _87566 _87571 _87575 x f x'' g x''' s h1)). Qed.
Lemma lem3370089 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) (h1 : term164 _87566 _87571 _87575 x f x'' g x''' s) : term79 _87566 _87571 _87575 x f g s.
Proof. exact (proj1 (@lem3370083 _87566 _87571 _87575 x f x'' g x''' s h1)). Qed.
Lemma lem3370090 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) (h1 : term164 _87566 _87571 _87575 x f x'' g x''' s) : term65 _87566 _87575 x'' g x''' s.
Proof. exact (proj2 (@lem3370088 _87566 _87571 _87575 x f x'' g x''' s h1)). Qed.
Lemma lem3370095 {A : Type'} (P : Prop) (Q : A -> Prop) : (term218 A P Q) = (term219 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3370096 {_87566 : Type'} (P : Prop) (Q : _87566 -> Prop) : (term218 _87566 P Q) = (term219 _87566 P Q).
Proof. exact (@lem3370095 _87566 P Q). Qed.
Lemma lem3370097 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term220 _87566 _87571 _87575 x f x' g s) = (term221 _87566 _87571 _87575 x f x' g s).
Proof. exact (@lem3370096 _87566 (term222 _87571 _87575 x f x') (term87 _87566 _87575 x' g s)). Qed.
Lemma lem3370098 {_87566 _87575 : Type'} (x : _87575) (g : _87566 -> _87575) (x' : _87566) (s : _87566 -> Prop) : (term223 _87566 _87575 x g s x') = (term81 _87566 _87575 x g x' s).
Proof. exact (eq_refl (term223 _87566 _87575 x g s x')). Qed.
Lemma lem3370099 {_87566 _87575 : Type'} (x : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term224 _87566 _87575 x g s) = (term87 _87566 _87575 x g s).
Proof. exact (fun_ext (fun x' : _87566 => @lem3370098 _87566 _87575 x g x' s)). Qed.
Lemma lem3370100 {_87566 : Type'} : (@all _87566) = (@all _87566).
Proof. exact (eq_refl (@all _87566)). Qed.
Lemma lem3370101 {_87566 _87575 : Type'} (x : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term225 _87566 _87575 x g s) = (term88 _87566 _87575 x g s).
Proof. exact (MK_COMB (@lem3370100 _87566) (@lem3370099 _87566 _87575 x g s)). Qed.
Lemma lem3370102 {_87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) : (term89 _87571 _87575 x f x') = (term89 _87571 _87575 x f x').
Proof. exact (eq_refl (term89 _87571 _87575 x f x')). Qed.
Lemma lem3370103 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term220 _87566 _87571 _87575 x f x' g s) = (term91 _87566 _87571 _87575 x f x' g s).
Proof. exact (MK_COMB (@lem3370102 _87571 _87575 x f x') (@lem3370101 _87566 _87575 x' g s)). Qed.
Lemma lem3370104 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3370105 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term226 _87566 _87571 _87575 x f x' g s) = (term227 _87566 _87571 _87575 x f x' g s).
Proof. exact (MK_COMB (@lem3370104) (@lem3370103 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3370106 {_87566 _87575 : Type'} (x : _87575) (g : _87566 -> _87575) (x' : _87566) (s : _87566 -> Prop) : (term223 _87566 _87575 x g s x') = (term81 _87566 _87575 x g x' s).
Proof. exact (eq_refl (term223 _87566 _87575 x g s x')). Qed.
Lemma lem3370107 {_87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) : (term89 _87571 _87575 x f x') = (term89 _87571 _87575 x f x').
Proof. exact (eq_refl (term89 _87571 _87575 x f x')). Qed.
Lemma lem3370108 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (x'' : _87566) (s : _87566 -> Prop) : (term228 _87566 _87571 _87575 x f x' g s x'') = (term229 _87566 _87571 _87575 x f x' g x'' s).
Proof. exact (MK_COMB (@lem3370107 _87571 _87575 x f x') (@lem3370106 _87566 _87575 x' g x'' s)). Qed.
Lemma lem3370109 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term230 _87566 _87571 _87575 x f x' g s) = (term231 _87566 _87571 _87575 x f x' g s).
Proof. exact (fun_ext (fun x'' : _87566 => @lem3370108 _87566 _87571 _87575 x f x' g x'' s)). Qed.
Lemma lem3370110 {_87566 : Type'} : (@all _87566) = (@all _87566).
Proof. exact (eq_refl (@all _87566)). Qed.
Lemma lem3370111 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term221 _87566 _87571 _87575 x f x' g s) = (term232 _87566 _87571 _87575 x f x' g s).
Proof. exact (MK_COMB (@lem3370110 _87566) (@lem3370109 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3370112 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : ((term220 _87566 _87571 _87575 x f x' g s) = (term221 _87566 _87571 _87575 x f x' g s)) = ((term91 _87566 _87571 _87575 x f x' g s) = (term232 _87566 _87571 _87575 x f x' g s)).
Proof. exact (MK_COMB (@lem3370105 _87566 _87571 _87575 x f x' g s) (@lem3370111 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3370113 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term91 _87566 _87571 _87575 x f x' g s) = (term232 _87566 _87571 _87575 x f x' g s).
Proof. exact (EQ_MP (@lem3370112 _87566 _87571 _87575 x f x' g s) (@lem3370097 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3370114 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term98 _87566 _87571 _87575 x f g s) = (term233 _87566 _87571 _87575 x f g s).
Proof. exact (fun_ext (fun x' : _87575 => @lem3370113 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3370115 {_87575 : Type'} : (@all _87575) = (@all _87575).
Proof. exact (eq_refl (@all _87575)). Qed.
Lemma lem3370116 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term99 _87566 _87571 _87575 x f g s) = (term234 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3370115 _87575) (@lem3370114 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3370129 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (x'' : _87566) (s : _87566 -> Prop) : (term229 _87566 _87571 _87575 x f x' g x'' s) = (term229 _87566 _87571 _87575 x f x' g x'' s).
Proof. exact (eq_refl (term229 _87566 _87571 _87575 x f x' g x'' s)). Qed.
Lemma lem3370130 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term231 _87566 _87571 _87575 x f x' g s) = (term231 _87566 _87571 _87575 x f x' g s).
Proof. exact (fun_ext (fun x'' : _87566 => @lem3370129 _87566 _87571 _87575 x f x' g x'' s)). Qed.
Lemma lem3370131 {_87566 : Type'} : (@all _87566) = (@all _87566).
Proof. exact (eq_refl (@all _87566)). Qed.
Lemma lem3370132 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term232 _87566 _87571 _87575 x f x' g s) = (term232 _87566 _87571 _87575 x f x' g s).
Proof. exact (MK_COMB (@lem3370131 _87566) (@lem3370130 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3370133 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term233 _87566 _87571 _87575 x f g s) = (term233 _87566 _87571 _87575 x f g s).
Proof. exact (fun_ext (fun x' : _87575 => @lem3370132 _87566 _87571 _87575 x f x' g s)). Qed.
Lemma lem3370134 {_87575 : Type'} : (@all _87575) = (@all _87575).
Proof. exact (eq_refl (@all _87575)). Qed.
Lemma lem3370135 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term234 _87566 _87571 _87575 x f g s) = (term234 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3370134 _87575) (@lem3370133 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3370136 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term99 _87566 _87571 _87575 x f g s) = (term234 _87566 _87571 _87575 x f g s).
Proof. exact (TRANS (@lem3370116 _87566 _87571 _87575 x f g s) (@lem3370135 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3370137 {_87566 _87571 _87575 : Type'} (x' : _87566) (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : term123 _87566 _87571 _87575 x' x f g s) : term234 _87566 _87571 _87575 x f g s.
Proof. exact (EQ_MP (@lem3370136 _87566 _87571 _87575 x f g s) (@lem3370084 _87566 _87571 _87575 x' x f g s h1)). Qed.
Lemma lem3370153 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (x' : _87566) (s : _87566 -> Prop) : (term70 _87566 _87571 _87575 x f g x' s) = (term70 _87566 _87571 _87575 x f g x' s).
Proof. exact (eq_refl (term70 _87566 _87571 _87575 x f g x' s)). Qed.
Lemma lem3370154 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term78 _87566 _87571 _87575 x f g s) = (term78 _87566 _87571 _87575 x f g s).
Proof. exact (fun_ext (fun x' : _87566 => @lem3370153 _87566 _87571 _87575 x f g x' s)). Qed.
Lemma lem3370155 {_87566 : Type'} : (@all _87566) = (@all _87566).
Proof. exact (eq_refl (@all _87566)). Qed.
Lemma lem3370157 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term79 _87566 _87571 _87575 x f g s) = (term79 _87566 _87571 _87575 x f g s).
Proof. exact (MK_COMB (@lem3370155 _87566) (@lem3370154 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3370158 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) (h1 : term164 _87566 _87571 _87575 x f x'' g x''' s) : term79 _87566 _87571 _87575 x f g s.
Proof. exact (EQ_MP (@lem3370157 _87566 _87571 _87575 x f g s) (@lem3370089 _87566 _87571 _87575 x f x'' g x''' s h1)). Qed.
Lemma lem3370171 {_87566 _87571 _87575 : Type'} (_35205 : _87575) (x' : _87566) (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : term123 _87566 _87571 _87575 x' x f g s) : term235 _87566 _87571 _87575 x f g s _35205.
Proof. exact (@lem3370137 _87566 _87571 _87575 x' x f g s h1 _35205). Qed.
Lemma lem3370172 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (_35205 : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term235 _87566 _87571 _87575 x f g s _35205) = (term232 _87566 _87571 _87575 x f _35205 g s).
Proof. exact (eq_refl (term235 _87566 _87571 _87575 x f g s _35205)). Qed.
Lemma lem3370173 {_87566 _87571 _87575 : Type'} (_35205 : _87575) (x' : _87566) (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : term123 _87566 _87571 _87575 x' x f g s) : term232 _87566 _87571 _87575 x f _35205 g s.
Proof. exact (EQ_MP (@lem3370172 _87566 _87571 _87575 x f _35205 g s) (@lem3370171 _87566 _87571 _87575 _35205 x' x f g s h1)). Qed.
Lemma lem3370174 {_87566 _87571 _87575 : Type'} (_35205 : _87575) (_35206 : _87566) (x' : _87566) (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : term123 _87566 _87571 _87575 x' x f g s) : term236 _87566 _87571 _87575 x f _35205 g s _35206.
Proof. exact (@lem3370173 _87566 _87571 _87575 _35205 x' x f g s h1 _35206). Qed.
Lemma lem3370175 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (_35205 : _87575) (g : _87566 -> _87575) (_35206 : _87566) (s : _87566 -> Prop) : (term236 _87566 _87571 _87575 x f _35205 g s _35206) = (term229 _87566 _87571 _87575 x f _35205 g _35206 s).
Proof. exact (eq_refl (term236 _87566 _87571 _87575 x f _35205 g s _35206)). Qed.
Lemma lem3370177 {_87566 _87571 _87575 : Type'} (_35207 : _87566) (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) (h1 : term164 _87566 _87571 _87575 x f x'' g x''' s) : term237 _87566 _87571 _87575 x f g s _35207.
Proof. exact (@lem3370158 _87566 _87571 _87575 x f x'' g x''' s h1 _35207). Qed.
Lemma lem3370178 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (_35207 : _87566) (s : _87566 -> Prop) : (term237 _87566 _87571 _87575 x f g s _35207) = (term70 _87566 _87571 _87575 x f g _35207 s).
Proof. exact (eq_refl (term237 _87566 _87571 _87575 x f g s _35207)). Qed.
Lemma lem3370189 {_87566 _87571 _87575 : Type'} (_35205 : _87575) (_35206 : _87566) (x' : _87566) (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : term123 _87566 _87571 _87575 x' x f g s) : term229 _87566 _87571 _87575 x f _35205 g _35206 s.
Proof. exact (EQ_MP (@lem3370175 _87566 _87571 _87575 x f _35205 g _35206 s) (@lem3370174 _87566 _87571 _87575 _35205 _35206 x' x f g s h1)). Qed.
Lemma lem3370191 {_87566 _87571 _87575 : Type'} (x' : _87566) (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : term123 _87566 _87571 _87575 x' x f g s) : x = (term22 _87566 _87571 _87575 f g x').
Proof. exact (proj1 (@lem3370085 _87566 _87571 _87575 x' x f g s h1)). Qed.
Lemma lem3370201 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) (h1 : term164 _87566 _87571 _87575 x f x'' g x''' s) : x = (f x'').
Proof. exact (proj1 (@lem3370088 _87566 _87571 _87575 x f x'' g x''' s h1)). Qed.
Lemma lem3370203 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) (h1 : term164 _87566 _87571 _87575 x f x'' g x''' s) : x'' = (g x''').
Proof. exact (proj1 (@lem3370090 _87566 _87571 _87575 x f x'' g x''' s h1)). Qed.
Lemma lem3370220 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (_35205 : _87575) (g : _87566 -> _87575) (_35206 : _87566) (s : _87566 -> Prop) : (term238 _87566 _87571 _87575 f _35205 g _35206 s) = (term238 _87566 _87571 _87575 f _35205 g _35206 s).
Proof. exact (eq_refl (term238 _87566 _87571 _87575 f _35205 g _35206 s)). Qed.
Lemma lem3370221 {_87566 _87571 _87575 : Type'} (_35205 : _87575) (_35206 : _87566) (x' : _87566) (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : term123 _87566 _87571 _87575 x' x f g s) : (term239 _87566 _87571 _87575 f _35205 g _35206 s x) = (term240 _87566 _87571 _87575 _35205 _35206 s f g x').
Proof. exact (MK_COMB (@lem3370220 _87566 _87571 _87575 f _35205 g _35206 s) (@lem3370191 _87566 _87571 _87575 x' x f g s h1)). Qed.
Lemma lem3370222 {_87566 _87571 _87575 : Type'} (x' : _87566) (f : _87575 -> _87571) (_35205 : _87575) (g : _87566 -> _87575) (_35206 : _87566) (s : _87566 -> Prop) : (term240 _87566 _87571 _87575 _35205 _35206 s f g x') = (term241 _87566 _87571 _87575 x' f _35205 g _35206 s).
Proof. exact (eq_refl (term240 _87566 _87571 _87575 _35205 _35206 s f g x')). Qed.
Lemma lem3370223 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (_35205 : _87575) (g : _87566 -> _87575) (_35206 : _87566) (s : _87566 -> Prop) (x : _87571) : (term242 _87566 _87571 _87575 f _35205 g _35206 s x) = (term242 _87566 _87571 _87575 f _35205 g _35206 s x).
Proof. exact (eq_refl (term242 _87566 _87571 _87575 f _35205 g _35206 s x)). Qed.
Lemma lem3370224 {_87566 _87571 _87575 : Type'} (x : _87571) (x' : _87566) (f : _87575 -> _87571) (_35205 : _87575) (g : _87566 -> _87575) (_35206 : _87566) (s : _87566 -> Prop) : ((term239 _87566 _87571 _87575 f _35205 g _35206 s x) = (term240 _87566 _87571 _87575 _35205 _35206 s f g x')) = ((term239 _87566 _87571 _87575 f _35205 g _35206 s x) = (term241 _87566 _87571 _87575 x' f _35205 g _35206 s)).
Proof. exact (MK_COMB (@lem3370223 _87566 _87571 _87575 f _35205 g _35206 s x) (@lem3370222 _87566 _87571 _87575 x' f _35205 g _35206 s)). Qed.
Lemma lem3370225 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (_35205 : _87575) (g : _87566 -> _87575) (_35206 : _87566) (s : _87566 -> Prop) : (term239 _87566 _87571 _87575 f _35205 g _35206 s x) = (term229 _87566 _87571 _87575 x f _35205 g _35206 s).
Proof. exact (eq_refl (term239 _87566 _87571 _87575 f _35205 g _35206 s x)). Qed.
Lemma lem3370226 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3370227 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (_35205 : _87575) (g : _87566 -> _87575) (_35206 : _87566) (s : _87566 -> Prop) : (term242 _87566 _87571 _87575 f _35205 g _35206 s x) = (term243 _87566 _87571 _87575 x f _35205 g _35206 s).
Proof. exact (MK_COMB (@lem3370226) (@lem3370225 _87566 _87571 _87575 x f _35205 g _35206 s)). Qed.
Lemma lem3370228 {_87566 _87571 _87575 : Type'} (x' : _87566) (f : _87575 -> _87571) (_35205 : _87575) (g : _87566 -> _87575) (_35206 : _87566) (s : _87566 -> Prop) : (term241 _87566 _87571 _87575 x' f _35205 g _35206 s) = (term241 _87566 _87571 _87575 x' f _35205 g _35206 s).
Proof. exact (eq_refl (term241 _87566 _87571 _87575 x' f _35205 g _35206 s)). Qed.
Lemma lem3370229 {_87566 _87571 _87575 : Type'} (x : _87571) (x' : _87566) (f : _87575 -> _87571) (_35205 : _87575) (g : _87566 -> _87575) (_35206 : _87566) (s : _87566 -> Prop) : ((term239 _87566 _87571 _87575 f _35205 g _35206 s x) = (term241 _87566 _87571 _87575 x' f _35205 g _35206 s)) = ((term229 _87566 _87571 _87575 x f _35205 g _35206 s) = (term241 _87566 _87571 _87575 x' f _35205 g _35206 s)).
Proof. exact (MK_COMB (@lem3370227 _87566 _87571 _87575 x f _35205 g _35206 s) (@lem3370228 _87566 _87571 _87575 x' f _35205 g _35206 s)). Qed.
Lemma lem3370230 {_87566 _87571 _87575 : Type'} (x : _87571) (x' : _87566) (f : _87575 -> _87571) (_35205 : _87575) (g : _87566 -> _87575) (_35206 : _87566) (s : _87566 -> Prop) : ((term239 _87566 _87571 _87575 f _35205 g _35206 s x) = (term240 _87566 _87571 _87575 _35205 _35206 s f g x')) = ((term229 _87566 _87571 _87575 x f _35205 g _35206 s) = (term241 _87566 _87571 _87575 x' f _35205 g _35206 s)).
Proof. exact (TRANS (@lem3370224 _87566 _87571 _87575 x x' f _35205 g _35206 s) (@lem3370229 _87566 _87571 _87575 x x' f _35205 g _35206 s)). Qed.
Lemma lem3370231 {_87566 _87571 _87575 : Type'} (_35205 : _87575) (_35206 : _87566) (x' : _87566) (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : term123 _87566 _87571 _87575 x' x f g s) : (term229 _87566 _87571 _87575 x f _35205 g _35206 s) = (term241 _87566 _87571 _87575 x' f _35205 g _35206 s).
Proof. exact (EQ_MP (@lem3370230 _87566 _87571 _87575 x x' f _35205 g _35206 s) (@lem3370221 _87566 _87571 _87575 _35205 _35206 x' x f g s h1)). Qed.
Lemma lem3370232 {_87566 _87571 _87575 : Type'} (_35205 : _87575) (_35206 : _87566) (x' : _87566) (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : term123 _87566 _87571 _87575 x' x f g s) : term241 _87566 _87571 _87575 x' f _35205 g _35206 s.
Proof. exact (EQ_MP (@lem3370231 _87566 _87571 _87575 _35205 _35206 x' x f g s h1) (@lem3370189 _87566 _87571 _87575 _35205 _35206 x' x f g s h1)). Qed.
Lemma lem3370274 {_87566 _87571 _87575 : Type'} (_35207 : _87566) (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) (h1 : term164 _87566 _87571 _87575 x f x'' g x''' s) : term70 _87566 _87571 _87575 x f g _35207 s.
Proof. exact (EQ_MP (@lem3370178 _87566 _87571 _87575 x f g _35207 s) (@lem3370177 _87566 _87571 _87575 _35207 x f x'' g x''' s h1)). Qed.
Lemma lem3370275 {_87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) : (term244 _87571 _87575 x f) = (term244 _87571 _87575 x f).
Proof. exact (eq_refl (term244 _87571 _87575 x f)). Qed.
Lemma lem3370276 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) (h1 : term164 _87566 _87571 _87575 x f x'' g x''' s) : (term245 _87571 _87575 x f x'') = (term246 _87566 _87571 _87575 x f g x''').
Proof. exact (MK_COMB (@lem3370275 _87571 _87575 x f) (@lem3370203 _87566 _87571 _87575 x f x'' g x''' s h1)). Qed.
Lemma lem3370277 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (x''' : _87566) : (term246 _87566 _87571 _87575 x f g x''') = (x = (term22 _87566 _87571 _87575 f g x''')).
Proof. exact (eq_refl (term246 _87566 _87571 _87575 x f g x''')). Qed.
Lemma lem3370278 {_87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x'' : _87575) : (term247 _87571 _87575 x f x'') = (term247 _87571 _87575 x f x'').
Proof. exact (eq_refl (term247 _87571 _87575 x f x'')). Qed.
Lemma lem3370279 {_87566 _87571 _87575 : Type'} (x'' : _87575) (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (x''' : _87566) : ((term245 _87571 _87575 x f x'') = (term246 _87566 _87571 _87575 x f g x''')) = ((term245 _87571 _87575 x f x'') = (x = (term22 _87566 _87571 _87575 f g x'''))).
Proof. exact (MK_COMB (@lem3370278 _87571 _87575 x f x'') (@lem3370277 _87566 _87571 _87575 x f g x''')). Qed.
Lemma lem3370280 {_87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x'' : _87575) : (term245 _87571 _87575 x f x'') = (x = (f x'')).
Proof. exact (eq_refl (term245 _87571 _87575 x f x'')). Qed.
Lemma lem3370281 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3370282 {_87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x'' : _87575) : (term247 _87571 _87575 x f x'') = (term248 _87571 _87575 x f x'').
Proof. exact (MK_COMB (@lem3370281) (@lem3370280 _87571 _87575 x f x'')). Qed.
Lemma lem3370283 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (x''' : _87566) : (x = (term22 _87566 _87571 _87575 f g x''')) = (x = (term22 _87566 _87571 _87575 f g x''')).
Proof. exact (eq_refl (x = (term22 _87566 _87571 _87575 f g x'''))). Qed.
Lemma lem3370284 {_87566 _87571 _87575 : Type'} (x'' : _87575) (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (x''' : _87566) : ((term245 _87571 _87575 x f x'') = (x = (term22 _87566 _87571 _87575 f g x'''))) = ((x = (f x'')) = (x = (term22 _87566 _87571 _87575 f g x'''))).
Proof. exact (MK_COMB (@lem3370282 _87571 _87575 x f x'') (@lem3370283 _87566 _87571 _87575 x f g x''')). Qed.
Lemma lem3370285 {_87566 _87571 _87575 : Type'} (x'' : _87575) (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (x''' : _87566) : ((term245 _87571 _87575 x f x'') = (term246 _87566 _87571 _87575 x f g x''')) = ((x = (f x'')) = (x = (term22 _87566 _87571 _87575 f g x'''))).
Proof. exact (TRANS (@lem3370279 _87566 _87571 _87575 x'' x f g x''') (@lem3370284 _87566 _87571 _87575 x'' x f g x''')). Qed.
Lemma lem3370286 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) (h1 : term164 _87566 _87571 _87575 x f x'' g x''' s) : (x = (f x'')) = (x = (term22 _87566 _87571 _87575 f g x''')).
Proof. exact (EQ_MP (@lem3370285 _87566 _87571 _87575 x'' x f g x''') (@lem3370276 _87566 _87571 _87575 x f x'' g x''' s h1)). Qed.
Lemma lem3370287 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) (h1 : term164 _87566 _87571 _87575 x f x'' g x''' s) : x = (term22 _87566 _87571 _87575 f g x''').
Proof. exact (EQ_MP (@lem3370286 _87566 _87571 _87575 x f x'' g x''' s h1) (@lem3370201 _87566 _87571 _87575 x f x'' g x''' s h1)). Qed.
Lemma lem3370316 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) (_35207 : _87566) (s : _87566 -> Prop) : (term249 _87566 _87571 _87575 f g _35207 s) = (term249 _87566 _87571 _87575 f g _35207 s).
Proof. exact (eq_refl (term249 _87566 _87571 _87575 f g _35207 s)). Qed.
Lemma lem3370317 {_87566 _87571 _87575 : Type'} (_35207 : _87566) (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) (h1 : term164 _87566 _87571 _87575 x f x'' g x''' s) : (term250 _87566 _87571 _87575 f g _35207 s x) = (term251 _87566 _87571 _87575 _35207 s f g x''').
Proof. exact (MK_COMB (@lem3370316 _87566 _87571 _87575 f g _35207 s) (@lem3370287 _87566 _87571 _87575 x f x'' g x''' s h1)). Qed.
Lemma lem3370318 {_87566 _87571 _87575 : Type'} (x''' : _87566) (f : _87575 -> _87571) (g : _87566 -> _87575) (_35207 : _87566) (s : _87566 -> Prop) : (term251 _87566 _87571 _87575 _35207 s f g x''') = (term252 _87566 _87571 _87575 x''' f g _35207 s).
Proof. exact (eq_refl (term251 _87566 _87571 _87575 _35207 s f g x''')). Qed.
Lemma lem3370319 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) (_35207 : _87566) (s : _87566 -> Prop) (x : _87571) : (term253 _87566 _87571 _87575 f g _35207 s x) = (term253 _87566 _87571 _87575 f g _35207 s x).
Proof. exact (eq_refl (term253 _87566 _87571 _87575 f g _35207 s x)). Qed.
Lemma lem3370320 {_87566 _87571 _87575 : Type'} (x : _87571) (x''' : _87566) (f : _87575 -> _87571) (g : _87566 -> _87575) (_35207 : _87566) (s : _87566 -> Prop) : ((term250 _87566 _87571 _87575 f g _35207 s x) = (term251 _87566 _87571 _87575 _35207 s f g x''')) = ((term250 _87566 _87571 _87575 f g _35207 s x) = (term252 _87566 _87571 _87575 x''' f g _35207 s)).
Proof. exact (MK_COMB (@lem3370319 _87566 _87571 _87575 f g _35207 s x) (@lem3370318 _87566 _87571 _87575 x''' f g _35207 s)). Qed.
Lemma lem3370321 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (_35207 : _87566) (s : _87566 -> Prop) : (term250 _87566 _87571 _87575 f g _35207 s x) = (term70 _87566 _87571 _87575 x f g _35207 s).
Proof. exact (eq_refl (term250 _87566 _87571 _87575 f g _35207 s x)). Qed.
Lemma lem3370322 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3370323 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (_35207 : _87566) (s : _87566 -> Prop) : (term253 _87566 _87571 _87575 f g _35207 s x) = (term254 _87566 _87571 _87575 x f g _35207 s).
Proof. exact (MK_COMB (@lem3370322) (@lem3370321 _87566 _87571 _87575 x f g _35207 s)). Qed.
Lemma lem3370324 {_87566 _87571 _87575 : Type'} (x''' : _87566) (f : _87575 -> _87571) (g : _87566 -> _87575) (_35207 : _87566) (s : _87566 -> Prop) : (term252 _87566 _87571 _87575 x''' f g _35207 s) = (term252 _87566 _87571 _87575 x''' f g _35207 s).
Proof. exact (eq_refl (term252 _87566 _87571 _87575 x''' f g _35207 s)). Qed.
Lemma lem3370325 {_87566 _87571 _87575 : Type'} (x : _87571) (x''' : _87566) (f : _87575 -> _87571) (g : _87566 -> _87575) (_35207 : _87566) (s : _87566 -> Prop) : ((term250 _87566 _87571 _87575 f g _35207 s x) = (term252 _87566 _87571 _87575 x''' f g _35207 s)) = ((term70 _87566 _87571 _87575 x f g _35207 s) = (term252 _87566 _87571 _87575 x''' f g _35207 s)).
Proof. exact (MK_COMB (@lem3370323 _87566 _87571 _87575 x f g _35207 s) (@lem3370324 _87566 _87571 _87575 x''' f g _35207 s)). Qed.
Lemma lem3370326 {_87566 _87571 _87575 : Type'} (x : _87571) (x''' : _87566) (f : _87575 -> _87571) (g : _87566 -> _87575) (_35207 : _87566) (s : _87566 -> Prop) : ((term250 _87566 _87571 _87575 f g _35207 s x) = (term251 _87566 _87571 _87575 _35207 s f g x''')) = ((term70 _87566 _87571 _87575 x f g _35207 s) = (term252 _87566 _87571 _87575 x''' f g _35207 s)).
Proof. exact (TRANS (@lem3370320 _87566 _87571 _87575 x x''' f g _35207 s) (@lem3370325 _87566 _87571 _87575 x x''' f g _35207 s)). Qed.
Lemma lem3370327 {_87566 _87571 _87575 : Type'} (_35207 : _87566) (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) (h1 : term164 _87566 _87571 _87575 x f x'' g x''' s) : (term70 _87566 _87571 _87575 x f g _35207 s) = (term252 _87566 _87571 _87575 x''' f g _35207 s).
Proof. exact (EQ_MP (@lem3370326 _87566 _87571 _87575 x x''' f g _35207 s) (@lem3370317 _87566 _87571 _87575 _35207 x f x'' g x''' s h1)). Qed.
Lemma lem3370328 {_87566 _87571 _87575 : Type'} (_35207 : _87566) (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) (h1 : term164 _87566 _87571 _87575 x f x'' g x''' s) : term252 _87566 _87571 _87575 x''' f g _35207 s.
Proof. exact (EQ_MP (@lem3370327 _87566 _87571 _87575 _35207 x f x'' g x''' s h1) (@lem3370274 _87566 _87571 _87575 _35207 x f x'' g x''' s h1)). Qed.
Lemma lem3370387 {_87571 : Type'} (x : _87571) : x = x.
Proof. exact (@lem21386 _87571 x). Qed.
Lemma lem3370388 {_87571 : Type'} (x : _87571) : x = x.
Proof. exact (@lem3370387 _87571 x). Qed.
Lemma lem3370389 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) (x' : _87566) : (term22 _87566 _87571 _87575 f g x') = (term22 _87566 _87571 _87575 f g x').
Proof. exact (@lem3370388 _87571 (term22 _87566 _87571 _87575 f g x')). Qed.
Lemma lem3370390 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) (x' : _87566) : term255 _87566 _87571 _87575 f g x'.
Proof. exact (fun h0 : term256 _87566 _87571 _87575 f g x' => @lem3370389 _87566 _87571 _87575 f g x'). Qed.
Lemma lem3370392 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3370393 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) (x' : _87566) : (term255 _87566 _87571 _87575 f g x') = ((term22 _87566 _87571 _87575 f g x') = (term22 _87566 _87571 _87575 f g x')).
Proof. exact (@lem3370392 ((term22 _87566 _87571 _87575 f g x') = (term22 _87566 _87571 _87575 f g x'))). Qed.
Lemma lem3370394 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) (x' : _87566) : (term22 _87566 _87571 _87575 f g x') = (term22 _87566 _87571 _87575 f g x').
Proof. exact (EQ_MP (@lem3370393 _87566 _87571 _87575 f g x') (@lem3370390 _87566 _87571 _87575 f g x')). Qed.
Lemma lem3370396 {_87575 : Type'} (x : _87575) : x = x.
Proof. exact (@lem21386 _87575 x). Qed.
Lemma lem3370397 {_87575 : Type'} (x : _87575) : x = x.
Proof. exact (@lem3370396 _87575 x). Qed.
Lemma lem3370398 {_87566 _87575 : Type'} (g : _87566 -> _87575) (x' : _87566) : (g x') = (g x').
Proof. exact (@lem3370397 _87575 (g x')). Qed.
Lemma lem3370399 {_87566 _87575 : Type'} (g : _87566 -> _87575) (x' : _87566) : term258 _87566 _87575 g x'.
Proof. exact (fun h0 : term259 _87566 _87575 g x' => @lem3370398 _87566 _87575 g x'). Qed.
Lemma lem3370401 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3370402 {_87566 _87575 : Type'} (g : _87566 -> _87575) (x' : _87566) : (term258 _87566 _87575 g x') = ((g x') = (g x')).
Proof. exact (@lem3370401 ((g x') = (g x'))). Qed.
Lemma lem3370403 {_87566 _87575 : Type'} (g : _87566 -> _87575) (x' : _87566) : (g x') = (g x').
Proof. exact (EQ_MP (@lem3370402 _87566 _87575 g x') (@lem3370399 _87566 _87575 g x')). Qed.
Lemma lem3370405 {_87566 _87571 _87575 : Type'} (x' : _87566) (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : term123 _87566 _87571 _87575 x' x f g s) : @IN _87566 x' s.
Proof. exact (proj2 (@lem3370085 _87566 _87571 _87575 x' x f g s h1)). Qed.
Lemma lem3370406 {_87566 _87571 _87575 : Type'} (x' : _87566) (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : term123 _87566 _87571 _87575 x' x f g s) : term260 _87566 x' s.
Proof. exact (fun h0 : term261 _87566 x' s => @lem3370405 _87566 _87571 _87575 x' x f g s h1). Qed.
Lemma lem3370408 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3370409 {_87566 : Type'} (x' : _87566) (s : _87566 -> Prop) : (term260 _87566 x' s) = (@IN _87566 x' s).
Proof. exact (@lem3370408 (@IN _87566 x' s)). Qed.
Lemma lem3370410 {_87566 _87571 _87575 : Type'} (x' : _87566) (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : term123 _87566 _87571 _87575 x' x f g s) : @IN _87566 x' s.
Proof. exact (EQ_MP (@lem3370409 _87566 x' s) (@lem3370406 _87566 _87571 _87575 x' x f g s h1)). Qed.
Lemma lem3370412 (a : Prop) (b : Prop) : (term262 a b) = (term263 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3370413 {_87566 _87575 : Type'} (_35205 : _87575) (g : _87566 -> _87575) (_35206 : _87566) (s : _87566 -> Prop) : (term81 _87566 _87575 _35205 g _35206 s) = (term80 _87566 _87575 _35205 g _35206 s).
Proof. exact (@lem3370412 (_35205 = (g _35206)) (@IN _87566 _35206 s)). Qed.
Lemma lem3370414 {_87566 _87571 _87575 : Type'} (g : _87566 -> _87575) (x' : _87566) (f : _87575 -> _87571) (_35205 : _87575) : (term264 _87566 _87571 _87575 g x' f _35205) = (term264 _87566 _87571 _87575 g x' f _35205).
Proof. exact (eq_refl (term264 _87566 _87571 _87575 g x' f _35205)). Qed.
Lemma lem3370415 {_87566 _87571 _87575 : Type'} (x' : _87566) (f : _87575 -> _87571) (_35205 : _87575) (g : _87566 -> _87575) (_35206 : _87566) (s : _87566 -> Prop) : (term241 _87566 _87571 _87575 x' f _35205 g _35206 s) = (term265 _87566 _87571 _87575 x' f _35205 g _35206 s).
Proof. exact (MK_COMB (@lem3370414 _87566 _87571 _87575 g x' f _35205) (@lem3370413 _87566 _87575 _35205 g _35206 s)). Qed.
Lemma lem3370417 (a : Prop) (b : Prop) : (term262 a b) = (term263 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3370418 {_87566 _87571 _87575 : Type'} (x' : _87566) (f : _87575 -> _87571) (_35205 : _87575) (g : _87566 -> _87575) (_35206 : _87566) (s : _87566 -> Prop) : (term265 _87566 _87571 _87575 x' f _35205 g _35206 s) = (term266 _87566 _87571 _87575 x' f _35205 g _35206 s).
Proof. exact (@lem3370417 ((term22 _87566 _87571 _87575 f g x') = (f _35205)) (term65 _87566 _87575 _35205 g _35206 s)). Qed.
Lemma lem3370419 {_87566 _87571 _87575 : Type'} (x' : _87566) (f : _87575 -> _87571) (_35205 : _87575) (g : _87566 -> _87575) (_35206 : _87566) (s : _87566 -> Prop) : (term241 _87566 _87571 _87575 x' f _35205 g _35206 s) = (term266 _87566 _87571 _87575 x' f _35205 g _35206 s).
Proof. exact (TRANS (@lem3370415 _87566 _87571 _87575 x' f _35205 g _35206 s) (@lem3370418 _87566 _87571 _87575 x' f _35205 g _35206 s)). Qed.
Lemma lem3370421 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3370422 {_87566 _87571 _87575 : Type'} (x' : _87566) (f : _87575 -> _87571) (_35205 : _87575) (g : _87566 -> _87575) (_35206 : _87566) (s : _87566 -> Prop) : (term266 _87566 _87571 _87575 x' f _35205 g _35206 s) = (term267 _87566 _87571 _87575 x' f _35205 g _35206 s).
Proof. exact (@lem3370421 (term268 _87566 _87571 _87575 x' f _35205 g _35206 s)). Qed.
Lemma lem3370423 {_87566 _87571 _87575 : Type'} (x' : _87566) (f : _87575 -> _87571) (_35205 : _87575) (g : _87566 -> _87575) (_35206 : _87566) (s : _87566 -> Prop) : (term241 _87566 _87571 _87575 x' f _35205 g _35206 s) = (term267 _87566 _87571 _87575 x' f _35205 g _35206 s).
Proof. exact (TRANS (@lem3370419 _87566 _87571 _87575 x' f _35205 g _35206 s) (@lem3370422 _87566 _87571 _87575 x' f _35205 g _35206 s)). Qed.
Lemma lem3370425 {_87566 _87571 _87575 : Type'} (x' : _87566) (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : term123 _87566 _87571 _87575 x' x f g s) : term269 _87566 _87575 g x' s.
Proof. exact (conj (@lem3370403 _87566 _87575 g x') (@lem3370410 _87566 _87571 _87575 x' x f g s h1)). Qed.
Lemma lem3370426 {_87566 _87571 _87575 : Type'} (x' : _87566) (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : term123 _87566 _87571 _87575 x' x f g s) : term270 _87566 _87571 _87575 f g x' s.
Proof. exact (conj (@lem3370394 _87566 _87571 _87575 f g x') (@lem3370425 _87566 _87571 _87575 x' x f g s h1)). Qed.
Lemma lem3370428 {_87566 _87571 _87575 : Type'} (_35205 : _87575) (_35206 : _87566) (x' : _87566) (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : term123 _87566 _87571 _87575 x' x f g s) : term267 _87566 _87571 _87575 x' f _35205 g _35206 s.
Proof. exact (EQ_MP (@lem3370423 _87566 _87571 _87575 x' f _35205 g _35206 s) (@lem3370232 _87566 _87571 _87575 _35205 _35206 x' x f g s h1)). Qed.
Lemma lem3370429 {_87566 _87571 _87575 : Type'} (_35205 : _87575) (_35206 : _87566) (x' : _87566) (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : term123 _87566 _87571 _87575 x' x f g s) : term267 _87566 _87571 _87575 x' f _35205 g _35206 s.
Proof. exact (@lem3370428 _87566 _87571 _87575 _35205 _35206 x' x f g s h1). Qed.
Lemma lem3370430 {_87566 _87571 _87575 : Type'} (x' : _87566) (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : term123 _87566 _87571 _87575 x' x f g s) : term271 _87566 _87571 _87575 f g x' s.
Proof. exact (@lem3370429 _87566 _87571 _87575 (g x') x' x' x f g s h1). Qed.
Lemma lem3370433 {_87566 _87571 _87575 : Type'} (x' : _87566) (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : term123 _87566 _87571 _87575 x' x f g s) : False.
Proof. exact (@lem3370430 _87566 _87571 _87575 x' x f g s h1 (@lem3370426 _87566 _87571 _87575 x' x f g s h1)). Qed.
Lemma lem3370434 {_87566 _87571 _87575 : Type'} (x' : _87566) (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : term123 _87566 _87571 _87575 x' x f g s) : term272.
Proof. exact (fun h0 : ~ False => @lem3370433 _87566 _87571 _87575 x' x f g s h1). Qed.
Lemma lem3370436 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3370437 : term272 = False.
Proof. exact (@lem3370436 False). Qed.
Lemma lem3370483 {_87571 : Type'} (x : _87571) : x = x.
Proof. exact (@lem21386 _87571 x). Qed.
Lemma lem3370484 {_87571 : Type'} (x : _87571) : x = x.
Proof. exact (@lem3370483 _87571 x). Qed.
Lemma lem3370485 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) (x''' : _87566) : (term22 _87566 _87571 _87575 f g x''') = (term22 _87566 _87571 _87575 f g x''').
Proof. exact (@lem3370484 _87571 (term22 _87566 _87571 _87575 f g x''')). Qed.
Lemma lem3370486 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) (x''' : _87566) : term255 _87566 _87571 _87575 f g x'''.
Proof. exact (fun h0 : term256 _87566 _87571 _87575 f g x''' => @lem3370485 _87566 _87571 _87575 f g x'''). Qed.
Lemma lem3370488 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3370489 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) (x''' : _87566) : (term255 _87566 _87571 _87575 f g x''') = ((term22 _87566 _87571 _87575 f g x''') = (term22 _87566 _87571 _87575 f g x''')).
Proof. exact (@lem3370488 ((term22 _87566 _87571 _87575 f g x''') = (term22 _87566 _87571 _87575 f g x'''))). Qed.
Lemma lem3370490 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) (x''' : _87566) : (term22 _87566 _87571 _87575 f g x''') = (term22 _87566 _87571 _87575 f g x''').
Proof. exact (EQ_MP (@lem3370489 _87566 _87571 _87575 f g x''') (@lem3370486 _87566 _87571 _87575 f g x''')). Qed.
Lemma lem3370492 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) (h1 : term164 _87566 _87571 _87575 x f x'' g x''' s) : @IN _87566 x''' s.
Proof. exact (proj2 (@lem3370090 _87566 _87571 _87575 x f x'' g x''' s h1)). Qed.
Lemma lem3370493 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) (h1 : term164 _87566 _87571 _87575 x f x'' g x''' s) : term260 _87566 x''' s.
Proof. exact (fun h0 : term261 _87566 x''' s => @lem3370492 _87566 _87571 _87575 x f x'' g x''' s h1). Qed.
Lemma lem3370495 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3370496 {_87566 : Type'} (x''' : _87566) (s : _87566 -> Prop) : (term260 _87566 x''' s) = (@IN _87566 x''' s).
Proof. exact (@lem3370495 (@IN _87566 x''' s)). Qed.
Lemma lem3370497 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) (h1 : term164 _87566 _87571 _87575 x f x'' g x''' s) : @IN _87566 x''' s.
Proof. exact (EQ_MP (@lem3370496 _87566 x''' s) (@lem3370493 _87566 _87571 _87575 x f x'' g x''' s h1)). Qed.
Lemma lem3370499 (a : Prop) (b : Prop) : (term262 a b) = (term263 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3370500 {_87566 _87571 _87575 : Type'} (x''' : _87566) (f : _87575 -> _87571) (g : _87566 -> _87575) (_35207 : _87566) (s : _87566 -> Prop) : (term252 _87566 _87571 _87575 x''' f g _35207 s) = (term273 _87566 _87571 _87575 x''' f g _35207 s).
Proof. exact (@lem3370499 ((term22 _87566 _87571 _87575 f g x''') = (term22 _87566 _87571 _87575 f g _35207)) (@IN _87566 _35207 s)). Qed.
Lemma lem3370502 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3370503 {_87566 _87571 _87575 : Type'} (x''' : _87566) (f : _87575 -> _87571) (g : _87566 -> _87575) (_35207 : _87566) (s : _87566 -> Prop) : (term273 _87566 _87571 _87575 x''' f g _35207 s) = (term274 _87566 _87571 _87575 x''' f g _35207 s).
Proof. exact (@lem3370502 (term275 _87566 _87571 _87575 x''' f g _35207 s)). Qed.
Lemma lem3370504 {_87566 _87571 _87575 : Type'} (x''' : _87566) (f : _87575 -> _87571) (g : _87566 -> _87575) (_35207 : _87566) (s : _87566 -> Prop) : (term252 _87566 _87571 _87575 x''' f g _35207 s) = (term274 _87566 _87571 _87575 x''' f g _35207 s).
Proof. exact (TRANS (@lem3370500 _87566 _87571 _87575 x''' f g _35207 s) (@lem3370503 _87566 _87571 _87575 x''' f g _35207 s)). Qed.
Lemma lem3370506 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) (h1 : term164 _87566 _87571 _87575 x f x'' g x''' s) : term276 _87566 _87571 _87575 f g x''' s.
Proof. exact (conj (@lem3370490 _87566 _87571 _87575 f g x''') (@lem3370497 _87566 _87571 _87575 x f x'' g x''' s h1)). Qed.
Lemma lem3370508 {_87566 _87571 _87575 : Type'} (_35207 : _87566) (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) (h1 : term164 _87566 _87571 _87575 x f x'' g x''' s) : term274 _87566 _87571 _87575 x''' f g _35207 s.
Proof. exact (EQ_MP (@lem3370504 _87566 _87571 _87575 x''' f g _35207 s) (@lem3370328 _87566 _87571 _87575 _35207 x f x'' g x''' s h1)). Qed.
Lemma lem3370509 {_87566 _87571 _87575 : Type'} (_35207 : _87566) (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) (h1 : term164 _87566 _87571 _87575 x f x'' g x''' s) : term274 _87566 _87571 _87575 x''' f g _35207 s.
Proof. exact (@lem3370508 _87566 _87571 _87575 _35207 x f x'' g x''' s h1). Qed.
Lemma lem3370510 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) (h1 : term164 _87566 _87571 _87575 x f x'' g x''' s) : term277 _87566 _87571 _87575 f g x''' s.
Proof. exact (@lem3370509 _87566 _87571 _87575 x''' x f x'' g x''' s h1). Qed.
Lemma lem3370513 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) (h1 : term164 _87566 _87571 _87575 x f x'' g x''' s) : False.
Proof. exact (@lem3370510 _87566 _87571 _87575 x f x'' g x''' s h1 (@lem3370506 _87566 _87571 _87575 x f x'' g x''' s h1)). Qed.
Lemma lem3370514 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) (h1 : term164 _87566 _87571 _87575 x f x'' g x''' s) : term272.
Proof. exact (fun h0 : ~ False => @lem3370513 _87566 _87571 _87575 x f x'' g x''' s h1). Qed.
Lemma lem3370516 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3370517 : term272 = False.
Proof. exact (@lem3370516 False). Qed.
Lemma lem3370520 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) (h1 : term164 _87566 _87571 _87575 x f x'' g x''' s) : False.
Proof. exact (EQ_MP (@lem3370517) (@lem3370514 _87566 _87571 _87575 x f x'' g x''' s h1)). Qed.
Lemma lem3370521 {_87566 _87571 _87575 : Type'} (x' : _87566) (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : term123 _87566 _87571 _87575 x' x f g s) : False.
Proof. exact (EQ_MP (@lem3370437) (@lem3370434 _87566 _87571 _87575 x' x f g s h1)). Qed.
Lemma lem3370522 {_87566 _87571 _87575 : Type'} (x' : _87566) (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) (h1 : term210 _87566 _87571 _87575 x' x f x'' g x''' s) : False.
Proof. exact (or_elim (@lem3370081 _87566 _87571 _87575 x' x f x'' g x''' s h1) (fun h0 : term123 _87566 _87571 _87575 x' x f g s => @lem3370521 _87566 _87571 _87575 x' x f g s h0) (fun h0 : term164 _87566 _87571 _87575 x f x'' g x''' s => @lem3370520 _87566 _87571 _87575 x f x'' g x''' s h0)). Qed.
Lemma lem3370523 {_87566 _87571 _87575 : Type'} (x' : _87566) (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) (h1 : term210 _87566 _87571 _87575 x' x f x'' g x''' s) : (term210 _87566 _87571 _87575 x' x f x'' g x''' s) = False.
Proof. exact (prop_ext (fun h2 : term210 _87566 _87571 _87575 x' x f x'' g x''' s => @lem3370522 _87566 _87571 _87575 x' x f x'' g x''' s h1) (fun h2 : False => @lem3370081 _87566 _87571 _87575 x' x f x'' g x''' s h1)). Qed.
Lemma lem3370524 {_87566 _87571 _87575 : Type'} (x' : _87566) (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (x''' : _87566) (s : _87566 -> Prop) (h1 : term210 _87566 _87571 _87575 x' x f x'' g x''' s) : False.
Proof. exact (EQ_MP (@lem3370523 _87566 _87571 _87575 x' x f x'' g x''' s h1) (@lem3370081 _87566 _87571 _87575 x' x f x'' g x''' s h1)). Qed.
Lemma lem3370525 {_87566 _87571 _87575 : Type'} (x' : _87566) (x : _87571) (f : _87575 -> _87571) (x'' : _87575) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : term213 _87566 _87571 _87575 x' x f x'' g s) : False.
Proof. exact (ex_elim (@lem3369967 _87566 _87571 _87575 x' x f x'' g s h1) (fun x''' : _87566 => fun h0 : term212 _87566 _87571 _87575 x' x f x'' g s x''' => @lem3370524 _87566 _87571 _87575 x' x f x'' g x''' s h0)). Qed.
Lemma lem3370526 {_87566 _87571 _87575 : Type'} (x' : _87566) (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : term215 _87566 _87571 _87575 x' x f g s) : False.
Proof. exact (ex_elim (@lem3369966 _87566 _87571 _87575 x' x f g s h1) (fun x'' : _87575 => fun h0 : term214 _87566 _87571 _87575 x' x f g s x'' => @lem3370525 _87566 _87571 _87575 x' x f x'' g s h0)). Qed.
Lemma lem3370527 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : term68 _87566 _87571 _87575 x f g s) : False.
Proof. exact (ex_elim (@lem3369965 _87566 _87571 _87575 x f g s h1) (fun x' : _87566 => fun h0 : term216 _87566 _87571 _87575 x f g s x' => @lem3370526 _87566 _87571 _87575 x' x f g s h0)). Qed.
Lemma lem3370528 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : term68 _87566 _87571 _87575 x f g s) : (term68 _87566 _87571 _87575 x f g s) = False.
Proof. exact (prop_ext (fun h2 : term68 _87566 _87571 _87575 x f g s => @lem3370527 _87566 _87571 _87575 x f g s h1) (fun h2 : False => @lem3369417 _87566 _87571 _87575 x f g s h1)). Qed.
Lemma lem3370529 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : term68 _87566 _87571 _87575 x f g s) : False.
Proof. exact (EQ_MP (@lem3370528 _87566 _87571 _87575 x f g s h1) (@lem3369417 _87566 _87571 _87575 x f g s h1)). Qed.
Lemma lem3370530 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : term67 _87566 _87571 _87575 x f g s.
Proof. exact (fun h0 : term68 _87566 _87571 _87575 x f g s => @lem3370529 _87566 _87571 _87575 x f g s h0). Qed.
Lemma lem3370531 {_87566 _87571 _87575 : Type'} (x : _87571) (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term29 _87566 _87571 _87575 x f g s) = (term41 _87566 _87571 _87575 x f g s).
Proof. exact (EQ_MP (@lem3369416 _87566 _87571 _87575 x f g s) (@lem3370530 _87566 _87571 _87575 x f g s)). Qed.
Lemma lem3370536 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : term44 _87566 _87571 _87575 f g s.
Proof. exact (fun x : _87571 => @lem3370531 _87566 _87571 _87575 x f g s). Qed.
Lemma lem3370541 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) : term48 _87566 _87571 _87575 f g.
Proof. exact (fun s : _87566 -> Prop => @lem3370536 _87566 _87571 _87575 f g s). Qed.
Lemma lem3370546 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) : term52 _87566 _87571 _87575 f.
Proof. exact (fun g : _87566 -> _87575 => @lem3370541 _87566 _87571 _87575 f g). Qed.
Lemma lem3370551 {_87566 _87571 _87575 : Type'} : term56 _87566 _87571 _87575.
Proof. exact (fun f : _87575 -> _87571 => @lem3370546 _87566 _87571 _87575 f). Qed.
Lemma lem3370552 {_87566 _87571 _87575 : Type'} : term58 _87566 _87571 _87575.
Proof. exact (EQ_MP (@lem3369412 _87566 _87571 _87575) (@lem3370551 _87566 _87571 _87575)). Qed.
Lemma lem3370554 {_87566 _87571 _87575 : Type'} : term58 _87566 _87571 _87575.
Proof. exact (@lem3369145 _87566 _87571 _87575 (@lem3370552 _87566 _87571 _87575)). Qed.
Lemma lem3370555 {_87566 _87571 _87575 : Type'} (h1 : term59 _87566 _87571 _87575) : False.
Proof. exact (@lem3370554 _87566 _87571 _87575 (@lem3369129 _87566 _87571 _87575 h1)). Qed.
Lemma lem3370556 {_87566 _87571 _87575 : Type'} (h1 : term59 _87566 _87571 _87575) : (term59 _87566 _87571 _87575) = False.
Proof. exact (prop_ext (fun h2 : term59 _87566 _87571 _87575 => @lem3370555 _87566 _87571 _87575 h1) (fun h2 : False => @lem3369129 _87566 _87571 _87575 h1)). Qed.
Lemma lem3370557 {_87566 _87571 _87575 : Type'} (h1 : term59 _87566 _87571 _87575) : False.
Proof. exact (EQ_MP (@lem3370556 _87566 _87571 _87575 h1) (@lem3369129 _87566 _87571 _87575 h1)). Qed.
Lemma lem3370558 {_87566 _87571 _87575 : Type'} : term58 _87566 _87571 _87575.
Proof. exact (fun h0 : term59 _87566 _87571 _87575 => @lem3370557 _87566 _87571 _87575 h0). Qed.
Lemma lem3370559 {_87566 _87571 _87575 : Type'} : term56 _87566 _87571 _87575.
Proof. exact (EQ_MP (@lem3369128 _87566 _87571 _87575) (@lem3370558 _87566 _87571 _87575)). Qed.
Lemma lem3370560 {_87566 _87571 _87575 : Type'} : term55 _87566 _87571 _87575.
Proof. exact (EQ_MP (@lem3369124 _87566 _87571 _87575) (@lem3370559 _87566 _87571 _87575)). Qed.
