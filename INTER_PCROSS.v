Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTER_PCROSS_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import EXTENSION_spec.
Require Import IN_INTER_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import PASTECART_IN_PCROSS_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7660850_spec.
Require Import thm7662539_spec.
Lemma lem8039092 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : term0 _141927 _141928 _141929 s.
Proof. exact (@lem8004229 _141927 _141928 _141929 s). Qed.
Lemma lem8039093 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : (term0 _141927 _141928 _141929 s) = (term1 _141927 _141928 _141929 s).
Proof. exact (eq_refl (term0 _141927 _141928 _141929 s)). Qed.
Lemma lem8039094 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : term1 _141927 _141928 _141929 s.
Proof. exact (EQ_MP (@lem8039093 _141927 _141928 _141929 s) (@lem8039092 _141927 _141928 _141929 s)). Qed.
Lemma lem8039095 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term2 _141927 _141928 _141929 s t.
Proof. exact (@lem8039094 _141927 _141928 _141929 s t). Qed.
Lemma lem8039096 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term2 _141927 _141928 _141929 s t) = (term3 _141927 _141928 _141929 s t).
Proof. exact (eq_refl (term2 _141927 _141928 _141929 s t)). Qed.
Lemma lem8039097 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term3 _141927 _141928 _141929 s t.
Proof. exact (EQ_MP (@lem8039096 _141927 _141928 _141929 s t) (@lem8039095 _141927 _141928 _141929 s t)). Qed.
Lemma lem8039098 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) (x : cart _141927 _141928) : term4 _141927 _141928 _141929 s t x.
Proof. exact (@lem8039097 _141927 _141928 _141929 s t x). Qed.
Lemma lem8039099 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term4 _141927 _141928 _141929 s t x) = (term5 _141927 _141928 _141929 x s t).
Proof. exact (eq_refl (term4 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8039100 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term5 _141927 _141928 _141929 x s t.
Proof. exact (EQ_MP (@lem8039099 _141927 _141928 _141929 x s t) (@lem8039098 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8039101 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) (y : cart _141927 _141929) : term6 _141927 _141928 _141929 x s t y.
Proof. exact (@lem8039100 _141927 _141928 _141929 x s t y). Qed.
Lemma lem8039102 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term6 _141927 _141928 _141929 x s t y) = ((term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t)).
Proof. exact (eq_refl (term6 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8039104 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (@lem3205222 A s). Qed.
Lemma lem8039105 {A : Type'} (s : A -> Prop) : (term9 A s) = (term10 A s).
Proof. exact (eq_refl (term9 A s)). Qed.
Lemma lem8039106 {A : Type'} (s : A -> Prop) : term10 A s.
Proof. exact (EQ_MP (@lem8039105 A s) (@lem8039104 A s)). Qed.
Lemma lem8039107 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term11 A s t.
Proof. exact (@lem8039106 A s t). Qed.
Lemma lem8039108 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term11 A s t) = (term12 A s t).
Proof. exact (eq_refl (term11 A s t)). Qed.
Lemma lem8039109 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term12 A s t.
Proof. exact (EQ_MP (@lem8039108 A s t) (@lem8039107 A s t)). Qed.
Lemma lem8039110 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term13 A s t x.
Proof. exact (@lem8039109 A s t x). Qed.
Lemma lem8039111 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term13 A s t x) = ((term14 A x s t) = (term15 A s x t)).
Proof. exact (eq_refl (term13 A s t x)). Qed.
Lemma lem8039113 {A : Type'} (s : A -> Prop) : term16 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem8039114 {A : Type'} (s : A -> Prop) : (term16 A s) = (term17 A s).
Proof. exact (eq_refl (term16 A s)). Qed.
Lemma lem8039115 {A : Type'} (s : A -> Prop) : term17 A s.
Proof. exact (EQ_MP (@lem8039114 A s) (@lem8039113 A s)). Qed.
Lemma lem8039116 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term18 A s t.
Proof. exact (@lem8039115 A s t). Qed.
Lemma lem8039117 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term18 A s t) = ((s = t) = (term19 A s t)).
Proof. exact (eq_refl (term18 A s t)). Qed.
Lemma lem8039146 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term19 A s t).
Proof. exact (EQ_MP (@lem8039117 A s t) (@lem8039116 A s t)). Qed.
Lemma lem8039147 {_142693 _142694 _142695 : Type'} (s : type16 _142693 _142694 _142695) (t : type16 _142693 _142694 _142695) : (s = t) = (term20 _142693 _142694 _142695 s t).
Proof. exact (@lem8039146 (type2 _142693 _142694 _142695) s t). Qed.
Lemma lem8039148 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (t' : type24 _142693 _142695) : ((term21 _142693 _142694 _142695 s t s' t') = (term22 _142693 _142694 _142695 s s' t t')) = (term23 _142693 _142694 _142695 s s' t t').
Proof. exact (@lem8039147 _142693 _142694 _142695 (term21 _142693 _142694 _142695 s t s' t') (term22 _142693 _142694 _142695 s s' t t')). Qed.
Lemma lem8039154 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term24 _140454 _140455 _140456 P) = (term25 _140454 _140455 _140456 P).
Proof. exact (EQ_MP (@lem7660850 _140454 _140455 _140456 P) (@lem7662539 _140454 _140455 _140456 P)). Qed.
Lemma lem8039155 {_142693 _142694 _142695 : Type'} (P : type16 _142693 _142694 _142695) : (term24 _142693 _142694 _142695 P) = (term25 _142693 _142694 _142695 P).
Proof. exact (@lem8039154 _142693 _142694 _142695 P). Qed.
Lemma lem8039156 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (t' : type24 _142693 _142695) : (term26 _142693 _142694 _142695 s s' t t') = (term27 _142693 _142694 _142695 s s' t t').
Proof. exact (@lem8039155 _142693 _142694 _142695 (term28 _142693 _142694 _142695 s s' t t')). Qed.
Lemma lem8039157 {_142693 _142694 _142695 : Type'} (x : type2 _142693 _142694 _142695) (s : type24 _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (t' : type24 _142693 _142695) : (term29 _142693 _142694 _142695 s s' t t' x) = ((term30 _142693 _142694 _142695 x s t s' t') = (term31 _142693 _142694 _142695 x s s' t t')).
Proof. exact (eq_refl (term29 _142693 _142694 _142695 s s' t t' x)). Qed.
Lemma lem8039158 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (t' : type24 _142693 _142695) : (term32 _142693 _142694 _142695 s s' t t') = (term28 _142693 _142694 _142695 s s' t t').
Proof. exact (fun_ext (fun x : type2 _142693 _142694 _142695 => @lem8039157 _142693 _142694 _142695 x s s' t t')). Qed.
Lemma lem8039159 {_142693 _142694 _142695 : Type'} : (@all (cart _142693 (finite_sum _142694 _142695))) = (@all (cart _142693 (finite_sum _142694 _142695))).
Proof. exact (eq_refl (@all (cart _142693 (finite_sum _142694 _142695)))). Qed.
Lemma lem8039160 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (t' : type24 _142693 _142695) : (term26 _142693 _142694 _142695 s s' t t') = (term23 _142693 _142694 _142695 s s' t t').
Proof. exact (MK_COMB (@lem8039159 _142693 _142694 _142695) (@lem8039158 _142693 _142694 _142695 s s' t t')). Qed.
Lemma lem8039161 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8039162 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (t' : type24 _142693 _142695) : (term33 _142693 _142694 _142695 s s' t t') = (term34 _142693 _142694 _142695 s s' t t').
Proof. exact (MK_COMB (@lem8039161) (@lem8039160 _142693 _142694 _142695 s s' t t')). Qed.
Lemma lem8039163 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (y : cart _142693 _142695) (s : type24 _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (t' : type24 _142693 _142695) : (term35 _142693 _142694 _142695 s s' t t' x y) = ((term36 _142693 _142694 _142695 x y s t s' t') = (term37 _142693 _142694 _142695 x y s s' t t')).
Proof. exact (eq_refl (term35 _142693 _142694 _142695 s s' t t' x y)). Qed.
Lemma lem8039164 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s : type24 _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (t' : type24 _142693 _142695) : (term38 _142693 _142694 _142695 s s' t t' x) = (term39 _142693 _142694 _142695 x s s' t t').
Proof. exact (fun_ext (fun y : cart _142693 _142695 => @lem8039163 _142693 _142694 _142695 x y s s' t t')). Qed.
Lemma lem8039165 {_142693 _142695 : Type'} : (@all (cart _142693 _142695)) = (@all (cart _142693 _142695)).
Proof. exact (eq_refl (@all (cart _142693 _142695))). Qed.
Lemma lem8039166 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s : type24 _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (t' : type24 _142693 _142695) : (term40 _142693 _142694 _142695 s s' t t' x) = (term41 _142693 _142694 _142695 x s s' t t').
Proof. exact (MK_COMB (@lem8039165 _142693 _142695) (@lem8039164 _142693 _142694 _142695 x s s' t t')). Qed.
Lemma lem8039167 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (t' : type24 _142693 _142695) : (term42 _142693 _142694 _142695 s s' t t') = (term43 _142693 _142694 _142695 s s' t t').
Proof. exact (fun_ext (fun x : cart _142693 _142694 => @lem8039166 _142693 _142694 _142695 x s s' t t')). Qed.
Lemma lem8039168 {_142693 _142694 : Type'} : (@all (cart _142693 _142694)) = (@all (cart _142693 _142694)).
Proof. exact (eq_refl (@all (cart _142693 _142694))). Qed.
Lemma lem8039169 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (t' : type24 _142693 _142695) : (term27 _142693 _142694 _142695 s s' t t') = (term44 _142693 _142694 _142695 s s' t t').
Proof. exact (MK_COMB (@lem8039168 _142693 _142694) (@lem8039167 _142693 _142694 _142695 s s' t t')). Qed.
Lemma lem8039170 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (t' : type24 _142693 _142695) : ((term26 _142693 _142694 _142695 s s' t t') = (term27 _142693 _142694 _142695 s s' t t')) = ((term23 _142693 _142694 _142695 s s' t t') = (term44 _142693 _142694 _142695 s s' t t')).
Proof. exact (MK_COMB (@lem8039162 _142693 _142694 _142695 s s' t t') (@lem8039169 _142693 _142694 _142695 s s' t t')). Qed.
Lemma lem8039171 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (t' : type24 _142693 _142695) : (term23 _142693 _142694 _142695 s s' t t') = (term44 _142693 _142694 _142695 s s' t t').
Proof. exact (EQ_MP (@lem8039170 _142693 _142694 _142695 s s' t t') (@lem8039156 _142693 _142694 _142695 s s' t t')). Qed.
Lemma lem8039178 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (t' : type24 _142693 _142695) : ((term21 _142693 _142694 _142695 s t s' t') = (term22 _142693 _142694 _142695 s s' t t')) = (term44 _142693 _142694 _142695 s s' t t').
Proof. exact (TRANS (@lem8039148 _142693 _142694 _142695 s s' t t') (@lem8039171 _142693 _142694 _142695 s s' t t')). Qed.
Lemma lem8039190 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem8039111 A s x t) (@lem8039110 A s t x)). Qed.
Lemma lem8039191 {_142693 _142694 _142695 : Type'} (s : type16 _142693 _142694 _142695) (x : type2 _142693 _142694 _142695) (t : type16 _142693 _142694 _142695) : (term45 _142693 _142694 _142695 x s t) = (term46 _142693 _142694 _142695 s x t).
Proof. exact (@lem8039190 (type2 _142693 _142694 _142695) s x t). Qed.
Lemma lem8039192 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (t : type24 _142693 _142695) (x : cart _142693 _142694) (y : cart _142693 _142695) (s' : type24 _142693 _142694) (t' : type24 _142693 _142695) : (term36 _142693 _142694 _142695 x y s t s' t') = (term47 _142693 _142694 _142695 s t x y s' t').
Proof. exact (@lem8039191 _142693 _142694 _142695 (@PCROSS _142693 _142694 _142695 s t) (@pastecart _142693 _142694 _142695 x y) (@PCROSS _142693 _142694 _142695 s' t')). Qed.
Lemma lem8039196 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8039102 _141927 _141928 _141929 x s y t) (@lem8039101 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8039197 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s : type24 _142693 _142694) (y : cart _142693 _142695) (t : type24 _142693 _142695) : (term7 _142693 _142694 _142695 x y s t) = (term8 _142693 _142694 _142695 x s y t).
Proof. exact (@lem8039196 _142693 _142694 _142695 x s y t). Qed.
Lemma lem8039200 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8039201 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s : type24 _142693 _142694) (y : cart _142693 _142695) (t : type24 _142693 _142695) : (term48 _142693 _142694 _142695 x y s t) = (term49 _142693 _142694 _142695 x s y t).
Proof. exact (MK_COMB (@lem8039200) (@lem8039197 _142693 _142694 _142695 x s y t)). Qed.
Lemma lem8039203 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8039102 _141927 _141928 _141929 x s y t) (@lem8039101 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8039204 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s : type24 _142693 _142694) (y : cart _142693 _142695) (t : type24 _142693 _142695) : (term7 _142693 _142694 _142695 x y s t) = (term8 _142693 _142694 _142695 x s y t).
Proof. exact (@lem8039203 _142693 _142694 _142695 x s y t). Qed.
Lemma lem8039205 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term7 _142693 _142694 _142695 x y s' t') = (term8 _142693 _142694 _142695 x s' y t').
Proof. exact (@lem8039204 _142693 _142694 _142695 x s' y t'). Qed.
Lemma lem8039208 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (t : type24 _142693 _142695) (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term47 _142693 _142694 _142695 s t x y s' t') = (term50 _142693 _142694 _142695 s t x s' y t').
Proof. exact (MK_COMB (@lem8039201 _142693 _142694 _142695 x s y t) (@lem8039205 _142693 _142694 _142695 x s' y t')). Qed.
Lemma lem8039211 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (t : type24 _142693 _142695) (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term36 _142693 _142694 _142695 x y s t s' t') = (term50 _142693 _142694 _142695 s t x s' y t').
Proof. exact (TRANS (@lem8039192 _142693 _142694 _142695 s t x y s' t') (@lem8039208 _142693 _142694 _142695 s t x s' y t')). Qed.
Lemma lem8039212 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8039213 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (t : type24 _142693 _142695) (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term51 _142693 _142694 _142695 x y s t s' t') = (term52 _142693 _142694 _142695 s t x s' y t').
Proof. exact (MK_COMB (@lem8039212) (@lem8039211 _142693 _142694 _142695 s t x s' y t')). Qed.
Lemma lem8039215 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8039102 _141927 _141928 _141929 x s y t) (@lem8039101 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8039216 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s : type24 _142693 _142694) (y : cart _142693 _142695) (t : type24 _142693 _142695) : (term7 _142693 _142694 _142695 x y s t) = (term8 _142693 _142694 _142695 x s y t).
Proof. exact (@lem8039215 _142693 _142694 _142695 x s y t). Qed.
Lemma lem8039217 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s : type24 _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t : type24 _142693 _142695) (t' : type24 _142693 _142695) : (term37 _142693 _142694 _142695 x y s s' t t') = (term53 _142693 _142694 _142695 x s s' y t t').
Proof. exact (@lem8039216 _142693 _142694 _142695 x (@INTER (cart _142693 _142694) s s') y (@INTER (cart _142693 _142695) t t')). Qed.
Lemma lem8039221 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem8039111 A s x t) (@lem8039110 A s t x)). Qed.
Lemma lem8039222 {_142693 _142694 : Type'} (s : type24 _142693 _142694) (x : cart _142693 _142694) (t : type24 _142693 _142694) : (term54 _142693 _142694 x s t) = (term55 _142693 _142694 s x t).
Proof. exact (@lem8039221 (cart _142693 _142694) s x t). Qed.
Lemma lem8039223 {_142693 _142694 : Type'} (s : type24 _142693 _142694) (x : cart _142693 _142694) (s' : type24 _142693 _142694) : (term54 _142693 _142694 x s s') = (term55 _142693 _142694 s x s').
Proof. exact (@lem8039222 _142693 _142694 s x s'). Qed.
Lemma lem8039226 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8039227 {_142693 _142694 : Type'} (s : type24 _142693 _142694) (x : cart _142693 _142694) (s' : type24 _142693 _142694) : (term56 _142693 _142694 x s s') = (term57 _142693 _142694 s x s').
Proof. exact (MK_COMB (@lem8039226) (@lem8039223 _142693 _142694 s x s')). Qed.
Lemma lem8039229 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem8039111 A s x t) (@lem8039110 A s t x)). Qed.
Lemma lem8039230 {_142693 _142695 : Type'} (s : type24 _142693 _142695) (x : cart _142693 _142695) (t : type24 _142693 _142695) : (term54 _142693 _142695 x s t) = (term55 _142693 _142695 s x t).
Proof. exact (@lem8039229 (cart _142693 _142695) s x t). Qed.
Lemma lem8039231 {_142693 _142695 : Type'} (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term54 _142693 _142695 y t t') = (term55 _142693 _142695 t y t').
Proof. exact (@lem8039230 _142693 _142695 t y t'). Qed.
Lemma lem8039234 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term53 _142693 _142694 _142695 x s s' y t t') = (term58 _142693 _142694 _142695 s x s' t y t').
Proof. exact (MK_COMB (@lem8039227 _142693 _142694 s x s') (@lem8039231 _142693 _142695 t y t')). Qed.
Lemma lem8039237 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term37 _142693 _142694 _142695 x y s s' t t') = (term58 _142693 _142694 _142695 s x s' t y t').
Proof. exact (TRANS (@lem8039217 _142693 _142694 _142695 x s s' y t t') (@lem8039234 _142693 _142694 _142695 s x s' t y t')). Qed.
Lemma lem8039238 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : ((term36 _142693 _142694 _142695 x y s t s' t') = (term37 _142693 _142694 _142695 x y s s' t t')) = ((term50 _142693 _142694 _142695 s t x s' y t') = (term58 _142693 _142694 _142695 s x s' t y t')).
Proof. exact (MK_COMB (@lem8039213 _142693 _142694 _142695 s t x s' y t') (@lem8039237 _142693 _142694 _142695 s x s' t y t')). Qed.
Lemma lem8039243 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (t' : type24 _142693 _142695) : (term39 _142693 _142694 _142695 x s s' t t') = (term59 _142693 _142694 _142695 s x s' t t').
Proof. exact (fun_ext (fun y : cart _142693 _142695 => @lem8039238 _142693 _142694 _142695 s x s' t y t')). Qed.
Lemma lem8039244 {_142693 _142695 : Type'} : (@all (cart _142693 _142695)) = (@all (cart _142693 _142695)).
Proof. exact (eq_refl (@all (cart _142693 _142695))). Qed.
Lemma lem8039245 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (t' : type24 _142693 _142695) : (term41 _142693 _142694 _142695 x s s' t t') = (term60 _142693 _142694 _142695 s x s' t t').
Proof. exact (MK_COMB (@lem8039244 _142693 _142695) (@lem8039243 _142693 _142694 _142695 s x s' t t')). Qed.
Lemma lem8039252 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (t' : type24 _142693 _142695) : (term43 _142693 _142694 _142695 s s' t t') = (term61 _142693 _142694 _142695 s s' t t').
Proof. exact (fun_ext (fun x : cart _142693 _142694 => @lem8039245 _142693 _142694 _142695 s x s' t t')). Qed.
Lemma lem8039253 {_142693 _142694 : Type'} : (@all (cart _142693 _142694)) = (@all (cart _142693 _142694)).
Proof. exact (eq_refl (@all (cart _142693 _142694))). Qed.
Lemma lem8039254 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (t' : type24 _142693 _142695) : (term44 _142693 _142694 _142695 s s' t t') = (term62 _142693 _142694 _142695 s s' t t').
Proof. exact (MK_COMB (@lem8039253 _142693 _142694) (@lem8039252 _142693 _142694 _142695 s s' t t')). Qed.
Lemma lem8039261 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (t' : type24 _142693 _142695) : ((term21 _142693 _142694 _142695 s t s' t') = (term22 _142693 _142694 _142695 s s' t t')) = (term62 _142693 _142694 _142695 s s' t t').
Proof. exact (TRANS (@lem8039178 _142693 _142694 _142695 s s' t t') (@lem8039254 _142693 _142694 _142695 s s' t t')). Qed.
Lemma lem8039262 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) : (term63 _142693 _142694 _142695 s s' t) = (term64 _142693 _142694 _142695 s s' t).
Proof. exact (fun_ext (fun t' : type24 _142693 _142695 => @lem8039261 _142693 _142694 _142695 s s' t t')). Qed.
Lemma lem8039263 {_142693 _142695 : Type'} : (@all ((cart _142693 _142695) -> Prop)) = (@all ((cart _142693 _142695) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142693 _142695) -> Prop))). Qed.
Lemma lem8039264 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) : (term65 _142693 _142694 _142695 s s' t) = (term66 _142693 _142694 _142695 s s' t).
Proof. exact (MK_COMB (@lem8039263 _142693 _142695) (@lem8039262 _142693 _142694 _142695 s s' t)). Qed.
Lemma lem8039271 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (s' : type24 _142693 _142694) : (term67 _142693 _142694 _142695 s s') = (term68 _142693 _142694 _142695 s s').
Proof. exact (fun_ext (fun t : type24 _142693 _142695 => @lem8039264 _142693 _142694 _142695 s s' t)). Qed.
Lemma lem8039272 {_142693 _142695 : Type'} : (@all ((cart _142693 _142695) -> Prop)) = (@all ((cart _142693 _142695) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142693 _142695) -> Prop))). Qed.
Lemma lem8039273 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (s' : type24 _142693 _142694) : (term69 _142693 _142694 _142695 s s') = (term70 _142693 _142694 _142695 s s').
Proof. exact (MK_COMB (@lem8039272 _142693 _142695) (@lem8039271 _142693 _142694 _142695 s s')). Qed.
Lemma lem8039280 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) : (term71 _142693 _142694 _142695 s) = (term72 _142693 _142694 _142695 s).
Proof. exact (fun_ext (fun s' : type24 _142693 _142694 => @lem8039273 _142693 _142694 _142695 s s')). Qed.
Lemma lem8039281 {_142693 _142694 : Type'} : (@all ((cart _142693 _142694) -> Prop)) = (@all ((cart _142693 _142694) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142693 _142694) -> Prop))). Qed.
Lemma lem8039282 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) : (term73 _142693 _142694 _142695 s) = (term74 _142693 _142694 _142695 s).
Proof. exact (MK_COMB (@lem8039281 _142693 _142694) (@lem8039280 _142693 _142694 _142695 s)). Qed.
Lemma lem8039289 {_142693 _142694 _142695 : Type'} : (term75 _142693 _142694 _142695) = (term76 _142693 _142694 _142695).
Proof. exact (fun_ext (fun s : type24 _142693 _142694 => @lem8039282 _142693 _142694 _142695 s)). Qed.
Lemma lem8039290 {_142693 _142694 : Type'} : (@all ((cart _142693 _142694) -> Prop)) = (@all ((cart _142693 _142694) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142693 _142694) -> Prop))). Qed.
Lemma lem8039291 {_142693 _142694 _142695 : Type'} : (term77 _142693 _142694 _142695) = (term78 _142693 _142694 _142695).
Proof. exact (MK_COMB (@lem8039290 _142693 _142694) (@lem8039289 _142693 _142694 _142695)). Qed.
Lemma lem8039298 {_142693 _142694 _142695 : Type'} : (term78 _142693 _142694 _142695) = (term77 _142693 _142694 _142695).
Proof. exact (SYM (@lem8039291 _142693 _142694 _142695)). Qed.
Lemma lem8039315 {_142693 _142694 : Type'} (x : cart _142693 _142694) (s : type24 _142693 _142694) : term79 _142693 _142694 x s.
Proof. exact (@lem9851 (@IN (cart _142693 _142694) x s)). Qed.
Lemma lem8039316 {_142693 _142694 : Type'} (x : cart _142693 _142694) (s : type24 _142693 _142694) : (term79 _142693 _142694 x s) = (term80 _142693 _142694 x s).
Proof. exact (eq_refl (term79 _142693 _142694 x s)). Qed.
Lemma lem8039317 {_142693 _142694 : Type'} (x : cart _142693 _142694) (s : type24 _142693 _142694) : term80 _142693 _142694 x s.
Proof. exact (EQ_MP (@lem8039316 _142693 _142694 x s) (@lem8039315 _142693 _142694 x s)). Qed.
Lemma lem8039318 {_142693 _142694 : Type'} (x : cart _142693 _142694) (s : type24 _142693 _142694) (h1 : (@IN (cart _142693 _142694) x s) = True) : (@IN (cart _142693 _142694) x s) = True.
Proof. exact (h1). Qed.
Lemma lem8039319 {_142693 _142694 : Type'} (x : cart _142693 _142694) (s : type24 _142693 _142694) (h1 : (@IN (cart _142693 _142694) x s) = False) : (@IN (cart _142693 _142694) x s) = False.
Proof. exact (h1). Qed.
Lemma lem8039336 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term81 _142693 _142694 _142695 x s' t y t') = (term81 _142693 _142694 _142695 x s' t y t').
Proof. exact (eq_refl (term81 _142693 _142694 _142695 x s' t y t')). Qed.
Lemma lem8039337 {_142693 _142694 _142695 : Type'} (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) (x : cart _142693 _142694) (s : type24 _142693 _142694) (h1 : (@IN (cart _142693 _142694) x s) = True) : (term82 _142693 _142694 _142695 s' t y t' x s) = (term83 _142693 _142694 _142695 x s' t y t').
Proof. exact (MK_COMB (@lem8039336 _142693 _142694 _142695 x s' t y t') (@lem8039318 _142693 _142694 x s h1)). Qed.
Lemma lem8039338 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term83 _142693 _142694 _142695 x s' t y t') = ((term84 _142693 _142694 _142695 t x s' y t') = (term85 _142693 _142694 _142695 x s' t y t')).
Proof. exact (eq_refl (term83 _142693 _142694 _142695 x s' t y t')). Qed.
Lemma lem8039339 {_142693 _142694 _142695 : Type'} (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) (x : cart _142693 _142694) (s : type24 _142693 _142694) : (term86 _142693 _142694 _142695 s' t y t' x s) = (term86 _142693 _142694 _142695 s' t y t' x s).
Proof. exact (eq_refl (term86 _142693 _142694 _142695 s' t y t' x s)). Qed.
Lemma lem8039340 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : ((term82 _142693 _142694 _142695 s' t y t' x s) = (term83 _142693 _142694 _142695 x s' t y t')) = ((term82 _142693 _142694 _142695 s' t y t' x s) = ((term84 _142693 _142694 _142695 t x s' y t') = (term85 _142693 _142694 _142695 x s' t y t'))).
Proof. exact (MK_COMB (@lem8039339 _142693 _142694 _142695 s' t y t' x s) (@lem8039338 _142693 _142694 _142695 x s' t y t')). Qed.
Lemma lem8039341 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term82 _142693 _142694 _142695 s' t y t' x s) = ((term50 _142693 _142694 _142695 s t x s' y t') = (term58 _142693 _142694 _142695 s x s' t y t')).
Proof. exact (eq_refl (term82 _142693 _142694 _142695 s' t y t' x s)). Qed.
Lemma lem8039342 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8039343 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term86 _142693 _142694 _142695 s' t y t' x s) = (term87 _142693 _142694 _142695 s x s' t y t').
Proof. exact (MK_COMB (@lem8039342) (@lem8039341 _142693 _142694 _142695 s x s' t y t')). Qed.
Lemma lem8039344 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : ((term84 _142693 _142694 _142695 t x s' y t') = (term85 _142693 _142694 _142695 x s' t y t')) = ((term84 _142693 _142694 _142695 t x s' y t') = (term85 _142693 _142694 _142695 x s' t y t')).
Proof. exact (eq_refl ((term84 _142693 _142694 _142695 t x s' y t') = (term85 _142693 _142694 _142695 x s' t y t'))). Qed.
Lemma lem8039345 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : ((term82 _142693 _142694 _142695 s' t y t' x s) = ((term84 _142693 _142694 _142695 t x s' y t') = (term85 _142693 _142694 _142695 x s' t y t'))) = (((term50 _142693 _142694 _142695 s t x s' y t') = (term58 _142693 _142694 _142695 s x s' t y t')) = ((term84 _142693 _142694 _142695 t x s' y t') = (term85 _142693 _142694 _142695 x s' t y t'))).
Proof. exact (MK_COMB (@lem8039343 _142693 _142694 _142695 s x s' t y t') (@lem8039344 _142693 _142694 _142695 x s' t y t')). Qed.
Lemma lem8039346 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : ((term82 _142693 _142694 _142695 s' t y t' x s) = (term83 _142693 _142694 _142695 x s' t y t')) = (((term50 _142693 _142694 _142695 s t x s' y t') = (term58 _142693 _142694 _142695 s x s' t y t')) = ((term84 _142693 _142694 _142695 t x s' y t') = (term85 _142693 _142694 _142695 x s' t y t'))).
Proof. exact (TRANS (@lem8039340 _142693 _142694 _142695 s x s' t y t') (@lem8039345 _142693 _142694 _142695 s x s' t y t')). Qed.
Lemma lem8039347 {_142693 _142694 _142695 : Type'} (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) (x : cart _142693 _142694) (s : type24 _142693 _142694) (h1 : (@IN (cart _142693 _142694) x s) = True) : ((term50 _142693 _142694 _142695 s t x s' y t') = (term58 _142693 _142694 _142695 s x s' t y t')) = ((term84 _142693 _142694 _142695 t x s' y t') = (term85 _142693 _142694 _142695 x s' t y t')).
Proof. exact (EQ_MP (@lem8039346 _142693 _142694 _142695 s x s' t y t') (@lem8039337 _142693 _142694 _142695 s' t y t' x s h1)). Qed.
Lemma lem8039348 {_142693 _142694 _142695 : Type'} (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) (x : cart _142693 _142694) (s : type24 _142693 _142694) (h1 : (@IN (cart _142693 _142694) x s) = True) : ((term84 _142693 _142694 _142695 t x s' y t') = (term85 _142693 _142694 _142695 x s' t y t')) = ((term50 _142693 _142694 _142695 s t x s' y t') = (term58 _142693 _142694 _142695 s x s' t y t')).
Proof. exact (SYM (@lem8039347 _142693 _142694 _142695 s' t y t' x s h1)). Qed.
Lemma lem8039349 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term81 _142693 _142694 _142695 x s' t y t') = (term81 _142693 _142694 _142695 x s' t y t').
Proof. exact (eq_refl (term81 _142693 _142694 _142695 x s' t y t')). Qed.
Lemma lem8039350 {_142693 _142694 _142695 : Type'} (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) (x : cart _142693 _142694) (s : type24 _142693 _142694) (h1 : (@IN (cart _142693 _142694) x s) = False) : (term82 _142693 _142694 _142695 s' t y t' x s) = (term88 _142693 _142694 _142695 x s' t y t').
Proof. exact (MK_COMB (@lem8039349 _142693 _142694 _142695 x s' t y t') (@lem8039319 _142693 _142694 x s h1)). Qed.
Lemma lem8039351 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term88 _142693 _142694 _142695 x s' t y t') = ((term89 _142693 _142694 _142695 t x s' y t') = (term90 _142693 _142694 _142695 x s' t y t')).
Proof. exact (eq_refl (term88 _142693 _142694 _142695 x s' t y t')). Qed.
Lemma lem8039352 {_142693 _142694 _142695 : Type'} (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) (x : cart _142693 _142694) (s : type24 _142693 _142694) : (term86 _142693 _142694 _142695 s' t y t' x s) = (term86 _142693 _142694 _142695 s' t y t' x s).
Proof. exact (eq_refl (term86 _142693 _142694 _142695 s' t y t' x s)). Qed.
Lemma lem8039353 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : ((term82 _142693 _142694 _142695 s' t y t' x s) = (term88 _142693 _142694 _142695 x s' t y t')) = ((term82 _142693 _142694 _142695 s' t y t' x s) = ((term89 _142693 _142694 _142695 t x s' y t') = (term90 _142693 _142694 _142695 x s' t y t'))).
Proof. exact (MK_COMB (@lem8039352 _142693 _142694 _142695 s' t y t' x s) (@lem8039351 _142693 _142694 _142695 x s' t y t')). Qed.
Lemma lem8039354 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term82 _142693 _142694 _142695 s' t y t' x s) = ((term50 _142693 _142694 _142695 s t x s' y t') = (term58 _142693 _142694 _142695 s x s' t y t')).
Proof. exact (eq_refl (term82 _142693 _142694 _142695 s' t y t' x s)). Qed.
Lemma lem8039355 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8039356 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term86 _142693 _142694 _142695 s' t y t' x s) = (term87 _142693 _142694 _142695 s x s' t y t').
Proof. exact (MK_COMB (@lem8039355) (@lem8039354 _142693 _142694 _142695 s x s' t y t')). Qed.
Lemma lem8039357 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : ((term89 _142693 _142694 _142695 t x s' y t') = (term90 _142693 _142694 _142695 x s' t y t')) = ((term89 _142693 _142694 _142695 t x s' y t') = (term90 _142693 _142694 _142695 x s' t y t')).
Proof. exact (eq_refl ((term89 _142693 _142694 _142695 t x s' y t') = (term90 _142693 _142694 _142695 x s' t y t'))). Qed.
Lemma lem8039358 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : ((term82 _142693 _142694 _142695 s' t y t' x s) = ((term89 _142693 _142694 _142695 t x s' y t') = (term90 _142693 _142694 _142695 x s' t y t'))) = (((term50 _142693 _142694 _142695 s t x s' y t') = (term58 _142693 _142694 _142695 s x s' t y t')) = ((term89 _142693 _142694 _142695 t x s' y t') = (term90 _142693 _142694 _142695 x s' t y t'))).
Proof. exact (MK_COMB (@lem8039356 _142693 _142694 _142695 s x s' t y t') (@lem8039357 _142693 _142694 _142695 x s' t y t')). Qed.
Lemma lem8039359 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : ((term82 _142693 _142694 _142695 s' t y t' x s) = (term88 _142693 _142694 _142695 x s' t y t')) = (((term50 _142693 _142694 _142695 s t x s' y t') = (term58 _142693 _142694 _142695 s x s' t y t')) = ((term89 _142693 _142694 _142695 t x s' y t') = (term90 _142693 _142694 _142695 x s' t y t'))).
Proof. exact (TRANS (@lem8039353 _142693 _142694 _142695 s x s' t y t') (@lem8039358 _142693 _142694 _142695 s x s' t y t')). Qed.
Lemma lem8039360 {_142693 _142694 _142695 : Type'} (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) (x : cart _142693 _142694) (s : type24 _142693 _142694) (h1 : (@IN (cart _142693 _142694) x s) = False) : ((term50 _142693 _142694 _142695 s t x s' y t') = (term58 _142693 _142694 _142695 s x s' t y t')) = ((term89 _142693 _142694 _142695 t x s' y t') = (term90 _142693 _142694 _142695 x s' t y t')).
Proof. exact (EQ_MP (@lem8039359 _142693 _142694 _142695 s x s' t y t') (@lem8039350 _142693 _142694 _142695 s' t y t' x s h1)). Qed.
Lemma lem8039361 {_142693 _142694 _142695 : Type'} (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) (x : cart _142693 _142694) (s : type24 _142693 _142694) (h1 : (@IN (cart _142693 _142694) x s) = False) : ((term89 _142693 _142694 _142695 t x s' y t') = (term90 _142693 _142694 _142695 x s' t y t')) = ((term50 _142693 _142694 _142695 s t x s' y t') = (term58 _142693 _142694 _142695 s x s' t y t')).
Proof. exact (SYM (@lem8039360 _142693 _142694 _142695 s' t y t' x s h1)). Qed.
Lemma lem8039367 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8039368 {_142693 _142695 : Type'} (y : cart _142693 _142695) (t : type24 _142693 _142695) : (term91 _142693 _142695 y t) = (@IN (cart _142693 _142695) y t).
Proof. exact (@lem8039367 (@IN (cart _142693 _142695) y t)). Qed.
Lemma lem8039369 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8039370 {_142693 _142695 : Type'} (y : cart _142693 _142695) (t : type24 _142693 _142695) : (term92 _142693 _142695 y t) = (term93 _142693 _142695 y t).
Proof. exact (MK_COMB (@lem8039369) (@lem8039368 _142693 _142695 y t)). Qed.
Lemma lem8039373 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term8 _142693 _142694 _142695 x s' y t') = (term8 _142693 _142694 _142695 x s' y t').
Proof. exact (eq_refl (term8 _142693 _142694 _142695 x s' y t')). Qed.
Lemma lem8039374 {_142693 _142694 _142695 : Type'} (t : type24 _142693 _142695) (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term84 _142693 _142694 _142695 t x s' y t') = (term94 _142693 _142694 _142695 t x s' y t').
Proof. exact (MK_COMB (@lem8039370 _142693 _142695 y t) (@lem8039373 _142693 _142694 _142695 x s' y t')). Qed.
Lemma lem8039377 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8039378 {_142693 _142694 _142695 : Type'} (t : type24 _142693 _142695) (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term95 _142693 _142694 _142695 t x s' y t') = (term96 _142693 _142694 _142695 t x s' y t').
Proof. exact (MK_COMB (@lem8039377) (@lem8039374 _142693 _142694 _142695 t x s' y t')). Qed.
Lemma lem8039382 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8039383 {_142693 _142694 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) : (term91 _142693 _142694 x s') = (@IN (cart _142693 _142694) x s').
Proof. exact (@lem8039382 (@IN (cart _142693 _142694) x s')). Qed.
Lemma lem8039384 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8039385 {_142693 _142694 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) : (term92 _142693 _142694 x s') = (term93 _142693 _142694 x s').
Proof. exact (MK_COMB (@lem8039384) (@lem8039383 _142693 _142694 x s')). Qed.
Lemma lem8039388 {_142693 _142695 : Type'} (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term55 _142693 _142695 t y t') = (term55 _142693 _142695 t y t').
Proof. exact (eq_refl (term55 _142693 _142695 t y t')). Qed.
Lemma lem8039389 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term85 _142693 _142694 _142695 x s' t y t') = (term97 _142693 _142694 _142695 x s' t y t').
Proof. exact (MK_COMB (@lem8039385 _142693 _142694 x s') (@lem8039388 _142693 _142695 t y t')). Qed.
Lemma lem8039392 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : ((term84 _142693 _142694 _142695 t x s' y t') = (term85 _142693 _142694 _142695 x s' t y t')) = ((term94 _142693 _142694 _142695 t x s' y t') = (term97 _142693 _142694 _142695 x s' t y t')).
Proof. exact (MK_COMB (@lem8039378 _142693 _142694 _142695 t x s' y t') (@lem8039389 _142693 _142694 _142695 x s' t y t')). Qed.
Lemma lem8039395 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : ((term94 _142693 _142694 _142695 t x s' y t') = (term97 _142693 _142694 _142695 x s' t y t')) = ((term84 _142693 _142694 _142695 t x s' y t') = (term85 _142693 _142694 _142695 x s' t y t')).
Proof. exact (SYM (@lem8039392 _142693 _142694 _142695 x s' t y t')). Qed.
Lemma lem8039396 {_142693 _142695 : Type'} (y : cart _142693 _142695) (t : type24 _142693 _142695) : term79 _142693 _142695 y t.
Proof. exact (@lem9851 (@IN (cart _142693 _142695) y t)). Qed.
Lemma lem8039397 {_142693 _142695 : Type'} (y : cart _142693 _142695) (t : type24 _142693 _142695) : (term79 _142693 _142695 y t) = (term80 _142693 _142695 y t).
Proof. exact (eq_refl (term79 _142693 _142695 y t)). Qed.
Lemma lem8039398 {_142693 _142695 : Type'} (y : cart _142693 _142695) (t : type24 _142693 _142695) : term80 _142693 _142695 y t.
Proof. exact (EQ_MP (@lem8039397 _142693 _142695 y t) (@lem8039396 _142693 _142695 y t)). Qed.
Lemma lem8039399 {_142693 _142695 : Type'} (y : cart _142693 _142695) (t : type24 _142693 _142695) (h1 : (@IN (cart _142693 _142695) y t) = True) : (@IN (cart _142693 _142695) y t) = True.
Proof. exact (h1). Qed.
Lemma lem8039400 {_142693 _142695 : Type'} (y : cart _142693 _142695) (t : type24 _142693 _142695) (h1 : (@IN (cart _142693 _142695) y t) = False) : (@IN (cart _142693 _142695) y t) = False.
Proof. exact (h1). Qed.
Lemma lem8039413 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term98 _142693 _142694 _142695 x s' y t') = (term98 _142693 _142694 _142695 x s' y t').
Proof. exact (eq_refl (term98 _142693 _142694 _142695 x s' y t')). Qed.
Lemma lem8039414 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t' : type24 _142693 _142695) (y : cart _142693 _142695) (t : type24 _142693 _142695) (h1 : (@IN (cart _142693 _142695) y t) = True) : (term99 _142693 _142694 _142695 x s' t' y t) = (term100 _142693 _142694 _142695 x s' y t').
Proof. exact (MK_COMB (@lem8039413 _142693 _142694 _142695 x s' y t') (@lem8039399 _142693 _142695 y t h1)). Qed.
Lemma lem8039415 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term100 _142693 _142694 _142695 x s' y t') = ((term101 _142693 _142694 _142695 x s' y t') = (term102 _142693 _142694 _142695 x s' y t')).
Proof. exact (eq_refl (term100 _142693 _142694 _142695 x s' y t')). Qed.
Lemma lem8039416 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t' : type24 _142693 _142695) (y : cart _142693 _142695) (t : type24 _142693 _142695) : (term103 _142693 _142694 _142695 x s' t' y t) = (term103 _142693 _142694 _142695 x s' t' y t).
Proof. exact (eq_refl (term103 _142693 _142694 _142695 x s' t' y t)). Qed.
Lemma lem8039417 {_142693 _142694 _142695 : Type'} (t : type24 _142693 _142695) (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : ((term99 _142693 _142694 _142695 x s' t' y t) = (term100 _142693 _142694 _142695 x s' y t')) = ((term99 _142693 _142694 _142695 x s' t' y t) = ((term101 _142693 _142694 _142695 x s' y t') = (term102 _142693 _142694 _142695 x s' y t'))).
Proof. exact (MK_COMB (@lem8039416 _142693 _142694 _142695 x s' t' y t) (@lem8039415 _142693 _142694 _142695 x s' y t')). Qed.
Lemma lem8039418 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term99 _142693 _142694 _142695 x s' t' y t) = ((term94 _142693 _142694 _142695 t x s' y t') = (term97 _142693 _142694 _142695 x s' t y t')).
Proof. exact (eq_refl (term99 _142693 _142694 _142695 x s' t' y t)). Qed.
Lemma lem8039419 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8039420 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term103 _142693 _142694 _142695 x s' t' y t) = (term104 _142693 _142694 _142695 x s' t y t').
Proof. exact (MK_COMB (@lem8039419) (@lem8039418 _142693 _142694 _142695 x s' t y t')). Qed.
Lemma lem8039421 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : ((term101 _142693 _142694 _142695 x s' y t') = (term102 _142693 _142694 _142695 x s' y t')) = ((term101 _142693 _142694 _142695 x s' y t') = (term102 _142693 _142694 _142695 x s' y t')).
Proof. exact (eq_refl ((term101 _142693 _142694 _142695 x s' y t') = (term102 _142693 _142694 _142695 x s' y t'))). Qed.
Lemma lem8039422 {_142693 _142694 _142695 : Type'} (t : type24 _142693 _142695) (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : ((term99 _142693 _142694 _142695 x s' t' y t) = ((term101 _142693 _142694 _142695 x s' y t') = (term102 _142693 _142694 _142695 x s' y t'))) = (((term94 _142693 _142694 _142695 t x s' y t') = (term97 _142693 _142694 _142695 x s' t y t')) = ((term101 _142693 _142694 _142695 x s' y t') = (term102 _142693 _142694 _142695 x s' y t'))).
Proof. exact (MK_COMB (@lem8039420 _142693 _142694 _142695 x s' t y t') (@lem8039421 _142693 _142694 _142695 x s' y t')). Qed.
Lemma lem8039423 {_142693 _142694 _142695 : Type'} (t : type24 _142693 _142695) (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : ((term99 _142693 _142694 _142695 x s' t' y t) = (term100 _142693 _142694 _142695 x s' y t')) = (((term94 _142693 _142694 _142695 t x s' y t') = (term97 _142693 _142694 _142695 x s' t y t')) = ((term101 _142693 _142694 _142695 x s' y t') = (term102 _142693 _142694 _142695 x s' y t'))).
Proof. exact (TRANS (@lem8039417 _142693 _142694 _142695 t x s' y t') (@lem8039422 _142693 _142694 _142695 t x s' y t')). Qed.
Lemma lem8039424 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t' : type24 _142693 _142695) (y : cart _142693 _142695) (t : type24 _142693 _142695) (h1 : (@IN (cart _142693 _142695) y t) = True) : ((term94 _142693 _142694 _142695 t x s' y t') = (term97 _142693 _142694 _142695 x s' t y t')) = ((term101 _142693 _142694 _142695 x s' y t') = (term102 _142693 _142694 _142695 x s' y t')).
Proof. exact (EQ_MP (@lem8039423 _142693 _142694 _142695 t x s' y t') (@lem8039414 _142693 _142694 _142695 x s' t' y t h1)). Qed.
Lemma lem8039425 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t' : type24 _142693 _142695) (y : cart _142693 _142695) (t : type24 _142693 _142695) (h1 : (@IN (cart _142693 _142695) y t) = True) : ((term101 _142693 _142694 _142695 x s' y t') = (term102 _142693 _142694 _142695 x s' y t')) = ((term94 _142693 _142694 _142695 t x s' y t') = (term97 _142693 _142694 _142695 x s' t y t')).
Proof. exact (SYM (@lem8039424 _142693 _142694 _142695 x s' t' y t h1)). Qed.
Lemma lem8039426 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term98 _142693 _142694 _142695 x s' y t') = (term98 _142693 _142694 _142695 x s' y t').
Proof. exact (eq_refl (term98 _142693 _142694 _142695 x s' y t')). Qed.
Lemma lem8039427 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t' : type24 _142693 _142695) (y : cart _142693 _142695) (t : type24 _142693 _142695) (h1 : (@IN (cart _142693 _142695) y t) = False) : (term99 _142693 _142694 _142695 x s' t' y t) = (term105 _142693 _142694 _142695 x s' y t').
Proof. exact (MK_COMB (@lem8039426 _142693 _142694 _142695 x s' y t') (@lem8039400 _142693 _142695 y t h1)). Qed.
Lemma lem8039428 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term105 _142693 _142694 _142695 x s' y t') = ((term106 _142693 _142694 _142695 x s' y t') = (term107 _142693 _142694 _142695 x s' y t')).
Proof. exact (eq_refl (term105 _142693 _142694 _142695 x s' y t')). Qed.
Lemma lem8039429 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t' : type24 _142693 _142695) (y : cart _142693 _142695) (t : type24 _142693 _142695) : (term103 _142693 _142694 _142695 x s' t' y t) = (term103 _142693 _142694 _142695 x s' t' y t).
Proof. exact (eq_refl (term103 _142693 _142694 _142695 x s' t' y t)). Qed.
Lemma lem8039430 {_142693 _142694 _142695 : Type'} (t : type24 _142693 _142695) (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : ((term99 _142693 _142694 _142695 x s' t' y t) = (term105 _142693 _142694 _142695 x s' y t')) = ((term99 _142693 _142694 _142695 x s' t' y t) = ((term106 _142693 _142694 _142695 x s' y t') = (term107 _142693 _142694 _142695 x s' y t'))).
Proof. exact (MK_COMB (@lem8039429 _142693 _142694 _142695 x s' t' y t) (@lem8039428 _142693 _142694 _142695 x s' y t')). Qed.
Lemma lem8039431 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term99 _142693 _142694 _142695 x s' t' y t) = ((term94 _142693 _142694 _142695 t x s' y t') = (term97 _142693 _142694 _142695 x s' t y t')).
Proof. exact (eq_refl (term99 _142693 _142694 _142695 x s' t' y t)). Qed.
Lemma lem8039432 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8039433 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term103 _142693 _142694 _142695 x s' t' y t) = (term104 _142693 _142694 _142695 x s' t y t').
Proof. exact (MK_COMB (@lem8039432) (@lem8039431 _142693 _142694 _142695 x s' t y t')). Qed.
Lemma lem8039434 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : ((term106 _142693 _142694 _142695 x s' y t') = (term107 _142693 _142694 _142695 x s' y t')) = ((term106 _142693 _142694 _142695 x s' y t') = (term107 _142693 _142694 _142695 x s' y t')).
Proof. exact (eq_refl ((term106 _142693 _142694 _142695 x s' y t') = (term107 _142693 _142694 _142695 x s' y t'))). Qed.
Lemma lem8039435 {_142693 _142694 _142695 : Type'} (t : type24 _142693 _142695) (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : ((term99 _142693 _142694 _142695 x s' t' y t) = ((term106 _142693 _142694 _142695 x s' y t') = (term107 _142693 _142694 _142695 x s' y t'))) = (((term94 _142693 _142694 _142695 t x s' y t') = (term97 _142693 _142694 _142695 x s' t y t')) = ((term106 _142693 _142694 _142695 x s' y t') = (term107 _142693 _142694 _142695 x s' y t'))).
Proof. exact (MK_COMB (@lem8039433 _142693 _142694 _142695 x s' t y t') (@lem8039434 _142693 _142694 _142695 x s' y t')). Qed.
Lemma lem8039436 {_142693 _142694 _142695 : Type'} (t : type24 _142693 _142695) (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : ((term99 _142693 _142694 _142695 x s' t' y t) = (term105 _142693 _142694 _142695 x s' y t')) = (((term94 _142693 _142694 _142695 t x s' y t') = (term97 _142693 _142694 _142695 x s' t y t')) = ((term106 _142693 _142694 _142695 x s' y t') = (term107 _142693 _142694 _142695 x s' y t'))).
Proof. exact (TRANS (@lem8039430 _142693 _142694 _142695 t x s' y t') (@lem8039435 _142693 _142694 _142695 t x s' y t')). Qed.
Lemma lem8039437 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t' : type24 _142693 _142695) (y : cart _142693 _142695) (t : type24 _142693 _142695) (h1 : (@IN (cart _142693 _142695) y t) = False) : ((term94 _142693 _142694 _142695 t x s' y t') = (term97 _142693 _142694 _142695 x s' t y t')) = ((term106 _142693 _142694 _142695 x s' y t') = (term107 _142693 _142694 _142695 x s' y t')).
Proof. exact (EQ_MP (@lem8039436 _142693 _142694 _142695 t x s' y t') (@lem8039427 _142693 _142694 _142695 x s' t' y t h1)). Qed.
Lemma lem8039438 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t' : type24 _142693 _142695) (y : cart _142693 _142695) (t : type24 _142693 _142695) (h1 : (@IN (cart _142693 _142695) y t) = False) : ((term106 _142693 _142694 _142695 x s' y t') = (term107 _142693 _142694 _142695 x s' y t')) = ((term94 _142693 _142694 _142695 t x s' y t') = (term97 _142693 _142694 _142695 x s' t y t')).
Proof. exact (SYM (@lem8039437 _142693 _142694 _142695 x s' t' y t h1)). Qed.
Lemma lem8039442 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8039443 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term101 _142693 _142694 _142695 x s' y t') = (term8 _142693 _142694 _142695 x s' y t').
Proof. exact (@lem8039442 (term8 _142693 _142694 _142695 x s' y t')). Qed.
Lemma lem8039446 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8039447 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term108 _142693 _142694 _142695 x s' y t') = (term109 _142693 _142694 _142695 x s' y t').
Proof. exact (MK_COMB (@lem8039446) (@lem8039443 _142693 _142694 _142695 x s' y t')). Qed.
Lemma lem8039451 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8039452 {_142693 _142695 : Type'} (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term91 _142693 _142695 y t') = (@IN (cart _142693 _142695) y t').
Proof. exact (@lem8039451 (@IN (cart _142693 _142695) y t')). Qed.
Lemma lem8039453 {_142693 _142694 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) : (term93 _142693 _142694 x s') = (term93 _142693 _142694 x s').
Proof. exact (eq_refl (term93 _142693 _142694 x s')). Qed.
Lemma lem8039454 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term102 _142693 _142694 _142695 x s' y t') = (term8 _142693 _142694 _142695 x s' y t').
Proof. exact (MK_COMB (@lem8039453 _142693 _142694 x s') (@lem8039452 _142693 _142695 y t')). Qed.
Lemma lem8039457 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : ((term101 _142693 _142694 _142695 x s' y t') = (term102 _142693 _142694 _142695 x s' y t')) = ((term8 _142693 _142694 _142695 x s' y t') = (term8 _142693 _142694 _142695 x s' y t')).
Proof. exact (MK_COMB (@lem8039447 _142693 _142694 _142695 x s' y t') (@lem8039454 _142693 _142694 _142695 x s' y t')). Qed.
Lemma lem8039459 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8039460 (x : Prop) : (x = x) = True.
Proof. exact (@lem8039459 Prop x). Qed.
Lemma lem8039461 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : ((term8 _142693 _142694 _142695 x s' y t') = (term8 _142693 _142694 _142695 x s' y t')) = True.
Proof. exact (@lem8039460 (term8 _142693 _142694 _142695 x s' y t')). Qed.
Lemma lem8039462 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : ((term101 _142693 _142694 _142695 x s' y t') = (term102 _142693 _142694 _142695 x s' y t')) = True.
Proof. exact (TRANS (@lem8039457 _142693 _142694 _142695 x s' y t') (@lem8039461 _142693 _142694 _142695 x s' y t')). Qed.
Lemma lem8039463 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : True = ((term101 _142693 _142694 _142695 x s' y t') = (term102 _142693 _142694 _142695 x s' y t')).
Proof. exact (SYM (@lem8039462 _142693 _142694 _142695 x s' y t')). Qed.
Lemma lem8039464 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term101 _142693 _142694 _142695 x s' y t') = (term102 _142693 _142694 _142695 x s' y t').
Proof. exact (EQ_MP (@lem8039463 _142693 _142694 _142695 x s' y t') (@lem0)). Qed.
Lemma lem8039468 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8039469 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term106 _142693 _142694 _142695 x s' y t') = False.
Proof. exact (@lem8039468 (term8 _142693 _142694 _142695 x s' y t')). Qed.
Lemma lem8039470 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8039471 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term110 _142693 _142694 _142695 x s' y t') = (@eq Prop False).
Proof. exact (MK_COMB (@lem8039470) (@lem8039469 _142693 _142694 _142695 x s' y t')). Qed.
Lemma lem8039475 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8039476 {_142693 _142695 : Type'} (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term111 _142693 _142695 y t') = False.
Proof. exact (@lem8039475 (@IN (cart _142693 _142695) y t')). Qed.
Lemma lem8039477 {_142693 _142694 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) : (term93 _142693 _142694 x s') = (term93 _142693 _142694 x s').
Proof. exact (eq_refl (term93 _142693 _142694 x s')). Qed.
Lemma lem8039478 {_142693 _142694 _142695 : Type'} (y : cart _142693 _142695) (t' : type24 _142693 _142695) (x : cart _142693 _142694) (s' : type24 _142693 _142694) : (term107 _142693 _142694 _142695 x s' y t') = (term112 _142693 _142694 x s').
Proof. exact (MK_COMB (@lem8039477 _142693 _142694 x s') (@lem8039476 _142693 _142695 y t')). Qed.
Lemma lem8039480 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem8039481 {_142693 _142694 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) : (term112 _142693 _142694 x s') = False.
Proof. exact (@lem8039480 (@IN (cart _142693 _142694) x s')). Qed.
Lemma lem8039482 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term107 _142693 _142694 _142695 x s' y t') = False.
Proof. exact (TRANS (@lem8039478 _142693 _142694 _142695 y t' x s') (@lem8039481 _142693 _142694 x s')). Qed.
Lemma lem8039483 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : ((term106 _142693 _142694 _142695 x s' y t') = (term107 _142693 _142694 _142695 x s' y t')) = (False = False).
Proof. exact (MK_COMB (@lem8039471 _142693 _142694 _142695 x s' y t') (@lem8039482 _142693 _142694 _142695 x s' y t')). Qed.
Lemma lem8039485 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem8039486 : (False = False) = (~ False).
Proof. exact (@lem8039485 False). Qed.
Lemma lem8039488 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem8039489 : (False = False) = True.
Proof. exact (TRANS (@lem8039486) (@lem8039488)). Qed.
Lemma lem8039490 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : ((term106 _142693 _142694 _142695 x s' y t') = (term107 _142693 _142694 _142695 x s' y t')) = True.
Proof. exact (TRANS (@lem8039483 _142693 _142694 _142695 x s' y t') (@lem8039489)). Qed.
Lemma lem8039491 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : True = ((term106 _142693 _142694 _142695 x s' y t') = (term107 _142693 _142694 _142695 x s' y t')).
Proof. exact (SYM (@lem8039490 _142693 _142694 _142695 x s' y t')). Qed.
Lemma lem8039492 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term106 _142693 _142694 _142695 x s' y t') = (term107 _142693 _142694 _142695 x s' y t').
Proof. exact (EQ_MP (@lem8039491 _142693 _142694 _142695 x s' y t') (@lem0)). Qed.
Lemma lem8039493 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t' : type24 _142693 _142695) (y : cart _142693 _142695) (t : type24 _142693 _142695) (h1 : (@IN (cart _142693 _142695) y t) = False) : (term94 _142693 _142694 _142695 t x s' y t') = (term97 _142693 _142694 _142695 x s' t y t').
Proof. exact (EQ_MP (@lem8039438 _142693 _142694 _142695 x s' t' y t h1) (@lem8039492 _142693 _142694 _142695 x s' y t')). Qed.
Lemma lem8039494 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t' : type24 _142693 _142695) (y : cart _142693 _142695) (t : type24 _142693 _142695) (h1 : (@IN (cart _142693 _142695) y t) = True) : (term94 _142693 _142694 _142695 t x s' y t') = (term97 _142693 _142694 _142695 x s' t y t').
Proof. exact (EQ_MP (@lem8039425 _142693 _142694 _142695 x s' t' y t h1) (@lem8039464 _142693 _142694 _142695 x s' y t')). Qed.
Lemma lem8039496 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term94 _142693 _142694 _142695 t x s' y t') = (term97 _142693 _142694 _142695 x s' t y t').
Proof. exact (or_elim (@lem8039398 _142693 _142695 y t) (fun h0 : (@IN (cart _142693 _142695) y t) = True => @lem8039494 _142693 _142694 _142695 x s' t' y t h0) (fun h0 : (@IN (cart _142693 _142695) y t) = False => @lem8039493 _142693 _142694 _142695 x s' t' y t h0)). Qed.
Lemma lem8039497 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term84 _142693 _142694 _142695 t x s' y t') = (term85 _142693 _142694 _142695 x s' t y t').
Proof. exact (EQ_MP (@lem8039395 _142693 _142694 _142695 x s' t y t') (@lem8039496 _142693 _142694 _142695 x s' t y t')). Qed.
Lemma lem8039503 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8039504 {_142693 _142695 : Type'} (y : cart _142693 _142695) (t : type24 _142693 _142695) : (term111 _142693 _142695 y t) = False.
Proof. exact (@lem8039503 (@IN (cart _142693 _142695) y t)). Qed.
Lemma lem8039505 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8039506 {_142693 _142695 : Type'} (y : cart _142693 _142695) (t : type24 _142693 _142695) : (term113 _142693 _142695 y t) = (and False).
Proof. exact (MK_COMB (@lem8039505) (@lem8039504 _142693 _142695 y t)). Qed.
Lemma lem8039509 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term8 _142693 _142694 _142695 x s' y t') = (term8 _142693 _142694 _142695 x s' y t').
Proof. exact (eq_refl (term8 _142693 _142694 _142695 x s' y t')). Qed.
Lemma lem8039510 {_142693 _142694 _142695 : Type'} (t : type24 _142693 _142695) (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term89 _142693 _142694 _142695 t x s' y t') = (term106 _142693 _142694 _142695 x s' y t').
Proof. exact (MK_COMB (@lem8039506 _142693 _142695 y t) (@lem8039509 _142693 _142694 _142695 x s' y t')). Qed.
Lemma lem8039512 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8039513 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term106 _142693 _142694 _142695 x s' y t') = False.
Proof. exact (@lem8039512 (term8 _142693 _142694 _142695 x s' y t')). Qed.
Lemma lem8039514 {_142693 _142694 _142695 : Type'} (t : type24 _142693 _142695) (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term89 _142693 _142694 _142695 t x s' y t') = False.
Proof. exact (TRANS (@lem8039510 _142693 _142694 _142695 t x s' y t') (@lem8039513 _142693 _142694 _142695 x s' y t')). Qed.
Lemma lem8039515 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8039516 {_142693 _142694 _142695 : Type'} (t : type24 _142693 _142695) (x : cart _142693 _142694) (s' : type24 _142693 _142694) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term114 _142693 _142694 _142695 t x s' y t') = (@eq Prop False).
Proof. exact (MK_COMB (@lem8039515) (@lem8039514 _142693 _142694 _142695 t x s' y t')). Qed.
Lemma lem8039520 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8039521 {_142693 _142694 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) : (term111 _142693 _142694 x s') = False.
Proof. exact (@lem8039520 (@IN (cart _142693 _142694) x s')). Qed.
Lemma lem8039522 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8039523 {_142693 _142694 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) : (term113 _142693 _142694 x s') = (and False).
Proof. exact (MK_COMB (@lem8039522) (@lem8039521 _142693 _142694 x s')). Qed.
Lemma lem8039526 {_142693 _142695 : Type'} (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term55 _142693 _142695 t y t') = (term55 _142693 _142695 t y t').
Proof. exact (eq_refl (term55 _142693 _142695 t y t')). Qed.
Lemma lem8039527 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term90 _142693 _142694 _142695 x s' t y t') = (term115 _142693 _142695 t y t').
Proof. exact (MK_COMB (@lem8039523 _142693 _142694 x s') (@lem8039526 _142693 _142695 t y t')). Qed.
Lemma lem8039529 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8039530 {_142693 _142695 : Type'} (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term115 _142693 _142695 t y t') = False.
Proof. exact (@lem8039529 (term55 _142693 _142695 t y t')). Qed.
Lemma lem8039531 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term90 _142693 _142694 _142695 x s' t y t') = False.
Proof. exact (TRANS (@lem8039527 _142693 _142694 _142695 x s' t y t') (@lem8039530 _142693 _142695 t y t')). Qed.
Lemma lem8039532 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : ((term89 _142693 _142694 _142695 t x s' y t') = (term90 _142693 _142694 _142695 x s' t y t')) = (False = False).
Proof. exact (MK_COMB (@lem8039516 _142693 _142694 _142695 t x s' y t') (@lem8039531 _142693 _142694 _142695 x s' t y t')). Qed.
Lemma lem8039534 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem8039535 : (False = False) = (~ False).
Proof. exact (@lem8039534 False). Qed.
Lemma lem8039537 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem8039538 : (False = False) = True.
Proof. exact (TRANS (@lem8039535) (@lem8039537)). Qed.
Lemma lem8039539 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : ((term89 _142693 _142694 _142695 t x s' y t') = (term90 _142693 _142694 _142695 x s' t y t')) = True.
Proof. exact (TRANS (@lem8039532 _142693 _142694 _142695 x s' t y t') (@lem8039538)). Qed.
Lemma lem8039540 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : True = ((term89 _142693 _142694 _142695 t x s' y t') = (term90 _142693 _142694 _142695 x s' t y t')).
Proof. exact (SYM (@lem8039539 _142693 _142694 _142695 x s' t y t')). Qed.
Lemma lem8039541 {_142693 _142694 _142695 : Type'} (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term89 _142693 _142694 _142695 t x s' y t') = (term90 _142693 _142694 _142695 x s' t y t').
Proof. exact (EQ_MP (@lem8039540 _142693 _142694 _142695 x s' t y t') (@lem0)). Qed.
Lemma lem8039542 {_142693 _142694 _142695 : Type'} (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) (x : cart _142693 _142694) (s : type24 _142693 _142694) (h1 : (@IN (cart _142693 _142694) x s) = False) : (term50 _142693 _142694 _142695 s t x s' y t') = (term58 _142693 _142694 _142695 s x s' t y t').
Proof. exact (EQ_MP (@lem8039361 _142693 _142694 _142695 s' t y t' x s h1) (@lem8039541 _142693 _142694 _142695 x s' t y t')). Qed.
Lemma lem8039543 {_142693 _142694 _142695 : Type'} (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) (x : cart _142693 _142694) (s : type24 _142693 _142694) (h1 : (@IN (cart _142693 _142694) x s) = True) : (term50 _142693 _142694 _142695 s t x s' y t') = (term58 _142693 _142694 _142695 s x s' t y t').
Proof. exact (EQ_MP (@lem8039348 _142693 _142694 _142695 s' t y t' x s h1) (@lem8039497 _142693 _142694 _142695 x s' t y t')). Qed.
Lemma lem8039546 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (y : cart _142693 _142695) (t' : type24 _142693 _142695) : (term50 _142693 _142694 _142695 s t x s' y t') = (term58 _142693 _142694 _142695 s x s' t y t').
Proof. exact (or_elim (@lem8039317 _142693 _142694 x s) (fun h0 : (@IN (cart _142693 _142694) x s) = True => @lem8039543 _142693 _142694 _142695 s' t y t' x s h0) (fun h0 : (@IN (cart _142693 _142694) x s) = False => @lem8039542 _142693 _142694 _142695 s' t y t' x s h0)). Qed.
Lemma lem8039551 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (x : cart _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (t' : type24 _142693 _142695) : term60 _142693 _142694 _142695 s x s' t t'.
Proof. exact (fun y : cart _142693 _142695 => @lem8039546 _142693 _142694 _142695 s x s' t y t'). Qed.
Lemma lem8039556 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (t' : type24 _142693 _142695) : term62 _142693 _142694 _142695 s s' t t'.
Proof. exact (fun x : cart _142693 _142694 => @lem8039551 _142693 _142694 _142695 s x s' t t'). Qed.
Lemma lem8039561 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) : term66 _142693 _142694 _142695 s s' t.
Proof. exact (fun t' : type24 _142693 _142695 => @lem8039556 _142693 _142694 _142695 s s' t t'). Qed.
Lemma lem8039566 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (s' : type24 _142693 _142694) : term70 _142693 _142694 _142695 s s'.
Proof. exact (fun t : type24 _142693 _142695 => @lem8039561 _142693 _142694 _142695 s s' t). Qed.
Lemma lem8039571 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) : term74 _142693 _142694 _142695 s.
Proof. exact (fun s' : type24 _142693 _142694 => @lem8039566 _142693 _142694 _142695 s s'). Qed.
Lemma lem8039576 {_142693 _142694 _142695 : Type'} : term78 _142693 _142694 _142695.
Proof. exact (fun s : type24 _142693 _142694 => @lem8039571 _142693 _142694 _142695 s). Qed.
Lemma lem8039577 {_142693 _142694 _142695 : Type'} : term77 _142693 _142694 _142695.
Proof. exact (EQ_MP (@lem8039298 _142693 _142694 _142695) (@lem8039576 _142693 _142694 _142695)). Qed.
