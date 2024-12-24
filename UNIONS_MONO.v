Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNIONS_MONO_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
Require Import thm19490_spec.
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
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211662_spec.
Require Import thm3211663_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem3346957 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3346958 {_87154 : Type'} (s : _87154 -> Prop) (t : _87154 -> Prop) : (@SUBSET _87154 s t) = (term0 _87154 s t).
Proof. exact (@lem3346957 _87154 s t). Qed.
Lemma lem3346959 {_87154 : Type'} (x : _87154 -> Prop) (y : _87154 -> Prop) : (@SUBSET _87154 x y) = (term0 _87154 x y).
Proof. exact (@lem3346958 _87154 x y). Qed.
Lemma lem3346966 {_87154 : Type'} (y : _87154 -> Prop) (t : type686 _87154) : (term1 _87154 y t) = (term1 _87154 y t).
Proof. exact (eq_refl (term1 _87154 y t)). Qed.
Lemma lem3346967 {_87154 : Type'} (t : type686 _87154) (x : _87154 -> Prop) (y : _87154 -> Prop) : (term2 _87154 t x y) = (term3 _87154 t x y).
Proof. exact (MK_COMB (@lem3346966 _87154 y t) (@lem3346959 _87154 x y)). Qed.
Lemma lem3346970 {_87154 : Type'} (t : type686 _87154) (x : _87154 -> Prop) : (term4 _87154 t x) = (term5 _87154 t x).
Proof. exact (fun_ext (fun y : _87154 -> Prop => @lem3346967 _87154 t x y)). Qed.
Lemma lem3346971 {_87154 : Type'} : (@ex (_87154 -> Prop)) = (@ex (_87154 -> Prop)).
Proof. exact (eq_refl (@ex (_87154 -> Prop))). Qed.
Lemma lem3346972 {_87154 : Type'} (t : type686 _87154) (x : _87154 -> Prop) : (term6 _87154 t x) = (term7 _87154 t x).
Proof. exact (MK_COMB (@lem3346971 _87154) (@lem3346970 _87154 t x)). Qed.
Lemma lem3346977 {_87154 : Type'} (x : _87154 -> Prop) (s : type686 _87154) : (term8 _87154 x s) = (term8 _87154 x s).
Proof. exact (eq_refl (term8 _87154 x s)). Qed.
Lemma lem3346978 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (x : _87154 -> Prop) : (term9 _87154 s t x) = (term10 _87154 s t x).
Proof. exact (MK_COMB (@lem3346977 _87154 x s) (@lem3346972 _87154 t x)). Qed.
Lemma lem3346981 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term11 _87154 s t) = (term12 _87154 s t).
Proof. exact (fun_ext (fun x : _87154 -> Prop => @lem3346978 _87154 s t x)). Qed.
Lemma lem3346982 {_87154 : Type'} : (@all (_87154 -> Prop)) = (@all (_87154 -> Prop)).
Proof. exact (eq_refl (@all (_87154 -> Prop))). Qed.
Lemma lem3346983 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term13 _87154 s t) = (term14 _87154 s t).
Proof. exact (MK_COMB (@lem3346982 _87154) (@lem3346981 _87154 s t)). Qed.
Lemma lem3346988 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3346989 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term15 _87154 s t) = (term16 _87154 s t).
Proof. exact (MK_COMB (@lem3346988) (@lem3346983 _87154 s t)). Qed.
Lemma lem3346991 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3346992 {_87154 : Type'} (s : _87154 -> Prop) (t : _87154 -> Prop) : (@SUBSET _87154 s t) = (term0 _87154 s t).
Proof. exact (@lem3346991 _87154 s t). Qed.
Lemma lem3346993 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term17 _87154 s t) = (term18 _87154 s t).
Proof. exact (@lem3346992 _87154 (@UNIONS _87154 s) (@UNIONS _87154 t)). Qed.
Lemma lem3347000 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term19 _87154 s t) = (term20 _87154 s t).
Proof. exact (MK_COMB (@lem3346989 _87154 s t) (@lem3346993 _87154 s t)). Qed.
Lemma lem3347003 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term20 _87154 s t) = (term19 _87154 s t).
Proof. exact (SYM (@lem3347000 _87154 s t)). Qed.
Lemma lem3347013 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3347014 {_87154 : Type'} (P : type686 _87154) (x : _87154 -> Prop) : (@IN (_87154 -> Prop) x P) = (P x).
Proof. exact (@lem3347013 (_87154 -> Prop) P x). Qed.
Lemma lem3347015 {_87154 : Type'} (s : type686 _87154) (x : _87154 -> Prop) : (@IN (_87154 -> Prop) x s) = (s x).
Proof. exact (@lem3347014 _87154 s x). Qed.
Lemma lem3347016 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3347017 {_87154 : Type'} (s : type686 _87154) (x : _87154 -> Prop) : (term8 _87154 x s) = (term21 _87154 s x).
Proof. exact (MK_COMB (@lem3347016) (@lem3347015 _87154 s x)). Qed.
Lemma lem3347025 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3347026 {_87154 : Type'} (P : type686 _87154) (x : _87154 -> Prop) : (@IN (_87154 -> Prop) x P) = (P x).
Proof. exact (@lem3347025 (_87154 -> Prop) P x). Qed.
Lemma lem3347027 {_87154 : Type'} (t : type686 _87154) (y : _87154 -> Prop) : (@IN (_87154 -> Prop) y t) = (t y).
Proof. exact (@lem3347026 _87154 t y). Qed.
Lemma lem3347028 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3347029 {_87154 : Type'} (t : type686 _87154) (y : _87154 -> Prop) : (term1 _87154 y t) = (term22 _87154 t y).
Proof. exact (MK_COMB (@lem3347028) (@lem3347027 _87154 t y)). Qed.
Lemma lem3347037 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3347038 {_87154 : Type'} (P : _87154 -> Prop) (x : _87154) : (@IN _87154 x P) = (P x).
Proof. exact (@lem3347037 _87154 P x). Qed.
Lemma lem3347039 {_87154 : Type'} (x : _87154 -> Prop) (x' : _87154) : (@IN _87154 x' x) = (x x').
Proof. exact (@lem3347038 _87154 x x'). Qed.
Lemma lem3347040 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3347041 {_87154 : Type'} (x : _87154 -> Prop) (x' : _87154) : (term23 _87154 x' x) = (term24 _87154 x x').
Proof. exact (MK_COMB (@lem3347040) (@lem3347039 _87154 x x')). Qed.
Lemma lem3347043 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3347044 {_87154 : Type'} (P : _87154 -> Prop) (x : _87154) : (@IN _87154 x P) = (P x).
Proof. exact (@lem3347043 _87154 P x). Qed.
Lemma lem3347045 {_87154 : Type'} (y : _87154 -> Prop) (x : _87154) : (@IN _87154 x y) = (y x).
Proof. exact (@lem3347044 _87154 y x). Qed.
Lemma lem3347046 {_87154 : Type'} (x : _87154 -> Prop) (y : _87154 -> Prop) (x' : _87154) : (term25 _87154 x x' y) = (term26 _87154 x y x').
Proof. exact (MK_COMB (@lem3347041 _87154 x x') (@lem3347045 _87154 y x')). Qed.
Lemma lem3347049 {_87154 : Type'} (x : _87154 -> Prop) (y : _87154 -> Prop) : (term27 _87154 x y) = (term28 _87154 x y).
Proof. exact (fun_ext (fun x' : _87154 => @lem3347046 _87154 x y x')). Qed.
Lemma lem3347050 {_87154 : Type'} : (@all _87154) = (@all _87154).
Proof. exact (eq_refl (@all _87154)). Qed.
Lemma lem3347051 {_87154 : Type'} (x : _87154 -> Prop) (y : _87154 -> Prop) : (term0 _87154 x y) = (term29 _87154 x y).
Proof. exact (MK_COMB (@lem3347050 _87154) (@lem3347049 _87154 x y)). Qed.
Lemma lem3347056 {_87154 : Type'} (t : type686 _87154) (x : _87154 -> Prop) (y : _87154 -> Prop) : (term3 _87154 t x y) = (term30 _87154 t x y).
Proof. exact (MK_COMB (@lem3347029 _87154 t y) (@lem3347051 _87154 x y)). Qed.
Lemma lem3347059 {_87154 : Type'} (t : type686 _87154) (x : _87154 -> Prop) : (term5 _87154 t x) = (term31 _87154 t x).
Proof. exact (fun_ext (fun y : _87154 -> Prop => @lem3347056 _87154 t x y)). Qed.
Lemma lem3347060 {_87154 : Type'} : (@ex (_87154 -> Prop)) = (@ex (_87154 -> Prop)).
Proof. exact (eq_refl (@ex (_87154 -> Prop))). Qed.
Lemma lem3347061 {_87154 : Type'} (t : type686 _87154) (x : _87154 -> Prop) : (term7 _87154 t x) = (term32 _87154 t x).
Proof. exact (MK_COMB (@lem3347060 _87154) (@lem3347059 _87154 t x)). Qed.
Lemma lem3347066 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (x : _87154 -> Prop) : (term10 _87154 s t x) = (term33 _87154 s t x).
Proof. exact (MK_COMB (@lem3347017 _87154 s x) (@lem3347061 _87154 t x)). Qed.
Lemma lem3347069 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term12 _87154 s t) = (term34 _87154 s t).
Proof. exact (fun_ext (fun x : _87154 -> Prop => @lem3347066 _87154 s t x)). Qed.
Lemma lem3347070 {_87154 : Type'} : (@all (_87154 -> Prop)) = (@all (_87154 -> Prop)).
Proof. exact (eq_refl (@all (_87154 -> Prop))). Qed.
Lemma lem3347071 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term14 _87154 s t) = (term35 _87154 s t).
Proof. exact (MK_COMB (@lem3347070 _87154) (@lem3347069 _87154 s t)). Qed.
Lemma lem3347076 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3347077 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term16 _87154 s t) = (term36 _87154 s t).
Proof. exact (MK_COMB (@lem3347076) (@lem3347071 _87154 s t)). Qed.
Lemma lem3347085 {A : Type'} (s : type686 A) (x : A) : (term37 A x s) = (term38 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem3347086 {_87154 : Type'} (s : type686 _87154) (x : _87154) : (term37 _87154 x s) = (term38 _87154 s x).
Proof. exact (@lem3347085 _87154 s x). Qed.
Lemma lem3347094 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3347095 {_87154 : Type'} (P : type686 _87154) (x : _87154 -> Prop) : (@IN (_87154 -> Prop) x P) = (P x).
Proof. exact (@lem3347094 (_87154 -> Prop) P x). Qed.
Lemma lem3347096 {_87154 : Type'} (s : type686 _87154) (t : _87154 -> Prop) : (@IN (_87154 -> Prop) t s) = (s t).
Proof. exact (@lem3347095 _87154 s t). Qed.
Lemma lem3347097 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3347098 {_87154 : Type'} (s : type686 _87154) (t : _87154 -> Prop) : (term1 _87154 t s) = (term22 _87154 s t).
Proof. exact (MK_COMB (@lem3347097) (@lem3347096 _87154 s t)). Qed.
Lemma lem3347100 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3347101 {_87154 : Type'} (P : _87154 -> Prop) (x : _87154) : (@IN _87154 x P) = (P x).
Proof. exact (@lem3347100 _87154 P x). Qed.
Lemma lem3347102 {_87154 : Type'} (t : _87154 -> Prop) (x : _87154) : (@IN _87154 x t) = (t x).
Proof. exact (@lem3347101 _87154 t x). Qed.
Lemma lem3347103 {_87154 : Type'} (s : type686 _87154) (t : _87154 -> Prop) (x : _87154) : (term39 _87154 s x t) = (term40 _87154 s t x).
Proof. exact (MK_COMB (@lem3347098 _87154 s t) (@lem3347102 _87154 t x)). Qed.
Lemma lem3347106 {_87154 : Type'} (s : type686 _87154) (x : _87154) : (term41 _87154 s x) = (term42 _87154 s x).
Proof. exact (fun_ext (fun t : _87154 -> Prop => @lem3347103 _87154 s t x)). Qed.
Lemma lem3347107 {_87154 : Type'} : (@ex (_87154 -> Prop)) = (@ex (_87154 -> Prop)).
Proof. exact (eq_refl (@ex (_87154 -> Prop))). Qed.
Lemma lem3347108 {_87154 : Type'} (s : type686 _87154) (x : _87154) : (term38 _87154 s x) = (term43 _87154 s x).
Proof. exact (MK_COMB (@lem3347107 _87154) (@lem3347106 _87154 s x)). Qed.
Lemma lem3347113 {_87154 : Type'} (s : type686 _87154) (x : _87154) : (term37 _87154 x s) = (term43 _87154 s x).
Proof. exact (TRANS (@lem3347086 _87154 s x) (@lem3347108 _87154 s x)). Qed.
Lemma lem3347114 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3347115 {_87154 : Type'} (s : type686 _87154) (x : _87154) : (term44 _87154 x s) = (term45 _87154 s x).
Proof. exact (MK_COMB (@lem3347114) (@lem3347113 _87154 s x)). Qed.
Lemma lem3347117 {A : Type'} (s : type686 A) (x : A) : (term37 A x s) = (term38 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem3347118 {_87154 : Type'} (s : type686 _87154) (x : _87154) : (term37 _87154 x s) = (term38 _87154 s x).
Proof. exact (@lem3347117 _87154 s x). Qed.
Lemma lem3347119 {_87154 : Type'} (t : type686 _87154) (x : _87154) : (term37 _87154 x t) = (term38 _87154 t x).
Proof. exact (@lem3347118 _87154 t x). Qed.
Lemma lem3347127 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3347128 {_87154 : Type'} (P : type686 _87154) (x : _87154 -> Prop) : (@IN (_87154 -> Prop) x P) = (P x).
Proof. exact (@lem3347127 (_87154 -> Prop) P x). Qed.
Lemma lem3347129 {_87154 : Type'} (t : type686 _87154) (t' : _87154 -> Prop) : (@IN (_87154 -> Prop) t' t) = (t t').
Proof. exact (@lem3347128 _87154 t t'). Qed.
Lemma lem3347130 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3347131 {_87154 : Type'} (t : type686 _87154) (t' : _87154 -> Prop) : (term1 _87154 t' t) = (term22 _87154 t t').
Proof. exact (MK_COMB (@lem3347130) (@lem3347129 _87154 t t')). Qed.
Lemma lem3347133 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3347134 {_87154 : Type'} (P : _87154 -> Prop) (x : _87154) : (@IN _87154 x P) = (P x).
Proof. exact (@lem3347133 _87154 P x). Qed.
Lemma lem3347135 {_87154 : Type'} (t : _87154 -> Prop) (x : _87154) : (@IN _87154 x t) = (t x).
Proof. exact (@lem3347134 _87154 t x). Qed.
Lemma lem3347136 {_87154 : Type'} (t : type686 _87154) (t' : _87154 -> Prop) (x : _87154) : (term39 _87154 t x t') = (term40 _87154 t t' x).
Proof. exact (MK_COMB (@lem3347131 _87154 t t') (@lem3347135 _87154 t' x)). Qed.
Lemma lem3347139 {_87154 : Type'} (t : type686 _87154) (x : _87154) : (term41 _87154 t x) = (term42 _87154 t x).
Proof. exact (fun_ext (fun t' : _87154 -> Prop => @lem3347136 _87154 t t' x)). Qed.
Lemma lem3347140 {_87154 : Type'} : (@ex (_87154 -> Prop)) = (@ex (_87154 -> Prop)).
Proof. exact (eq_refl (@ex (_87154 -> Prop))). Qed.
Lemma lem3347141 {_87154 : Type'} (t : type686 _87154) (x : _87154) : (term38 _87154 t x) = (term43 _87154 t x).
Proof. exact (MK_COMB (@lem3347140 _87154) (@lem3347139 _87154 t x)). Qed.
Lemma lem3347146 {_87154 : Type'} (t : type686 _87154) (x : _87154) : (term37 _87154 x t) = (term43 _87154 t x).
Proof. exact (TRANS (@lem3347119 _87154 t x) (@lem3347141 _87154 t x)). Qed.
Lemma lem3347147 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (x : _87154) : (term46 _87154 s x t) = (term47 _87154 s t x).
Proof. exact (MK_COMB (@lem3347115 _87154 s x) (@lem3347146 _87154 t x)). Qed.
Lemma lem3347150 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term48 _87154 s t) = (term49 _87154 s t).
Proof. exact (fun_ext (fun x : _87154 => @lem3347147 _87154 s t x)). Qed.
Lemma lem3347151 {_87154 : Type'} : (@all _87154) = (@all _87154).
Proof. exact (eq_refl (@all _87154)). Qed.
Lemma lem3347152 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term18 _87154 s t) = (term50 _87154 s t).
Proof. exact (MK_COMB (@lem3347151 _87154) (@lem3347150 _87154 s t)). Qed.
Lemma lem3347157 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term20 _87154 s t) = (term51 _87154 s t).
Proof. exact (MK_COMB (@lem3347077 _87154 s t) (@lem3347152 _87154 s t)). Qed.
Lemma lem3347160 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term51 _87154 s t) = (term20 _87154 s t).
Proof. exact (SYM (@lem3347157 _87154 s t)). Qed.
Lemma lem3347162 (p : Prop) : p = (term52 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3347163 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term51 _87154 s t) = (term53 _87154 s t).
Proof. exact (@lem3347162 (term51 _87154 s t)). Qed.
Lemma lem3347164 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term53 _87154 s t) = (term51 _87154 s t).
Proof. exact (SYM (@lem3347163 _87154 s t)). Qed.
Lemma lem3347165 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (h1 : term54 _87154 s t) : term54 _87154 s t.
Proof. exact (h1). Qed.
Lemma lem3347168 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (h1 : term53 _87154 s t) : term53 _87154 s t.
Proof. exact (h1). Qed.
Lemma lem3347169 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : term55 _87154 s t.
Proof. exact (fun h0 : term53 _87154 s t => @lem3347168 _87154 s t h0). Qed.
Lemma lem3347170 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (h1 : term55 _87154 s t) : term55 _87154 s t.
Proof. exact (h1). Qed.
Lemma lem3347171 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (h1 : term53 _87154 s t) : term53 _87154 s t.
Proof. exact (h1). Qed.
Lemma lem3347172 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (h1 : term53 _87154 s t) (h2 : term55 _87154 s t) : term53 _87154 s t.
Proof. exact (@lem3347170 _87154 s t h2 (@lem3347171 _87154 s t h1)). Qed.
Lemma lem3347173 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (h1 : term53 _87154 s t) : term56 _87154 s t.
Proof. exact (fun h0 : term55 _87154 s t => @lem3347172 _87154 s t h1 h0). Qed.
Lemma lem3347174 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (h1 : term55 _87154 s t) : term55 _87154 s t.
Proof. exact (h1). Qed.
Lemma lem3347175 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (h1 : term53 _87154 s t) (h2 : term55 _87154 s t) : term53 _87154 s t.
Proof. exact (@lem3347173 _87154 s t h1 (@lem3347174 _87154 s t h2)). Qed.
Lemma lem3347176 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (h1 : term55 _87154 s t) : term55 _87154 s t.
Proof. exact (fun h0 : term53 _87154 s t => @lem3347175 _87154 s t h0 h1). Qed.
Lemma lem3347177 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : term57 _87154 s t.
Proof. exact (fun h0 : term55 _87154 s t => @lem3347176 _87154 s t h0). Qed.
Lemma lem3347180 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : term55 _87154 s t.
Proof. exact (@lem3347177 _87154 s t (@lem3347169 _87154 s t)). Qed.
Lemma lem3347181 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : term55 _87154 s t.
Proof. exact (@lem3347180 _87154 s t). Qed.
Lemma lem3347191 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3347192 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term53 _87154 s t) = (term58 _87154 s t).
Proof. exact (@lem3347191 (term54 _87154 s t)). Qed.
Lemma lem3347194 (t : Prop) : (term59 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3347195 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term58 _87154 s t) = (term51 _87154 s t).
Proof. exact (@lem3347194 (term51 _87154 s t)). Qed.
Lemma lem3347198 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term53 _87154 s t) = (term51 _87154 s t).
Proof. exact (TRANS (@lem3347192 _87154 s t) (@lem3347195 _87154 s t)). Qed.
Lemma lem3347307 {_87154 : Type'} (t : type686 _87154) : (term60 _87154 t) = (term61 _87154 t).
Proof. exact (fun_ext (fun s : type686 _87154 => @lem3347198 _87154 s t)). Qed.
Lemma lem3347308 {_87154 : Type'} : (@all ((_87154 -> Prop) -> Prop)) = (@all ((_87154 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87154 -> Prop) -> Prop))). Qed.
Lemma lem3347309 {_87154 : Type'} (t : type686 _87154) : (term62 _87154 t) = (term63 _87154 t).
Proof. exact (MK_COMB (@lem3347308 _87154) (@lem3347307 _87154 t)). Qed.
Lemma lem3347314 {_87154 : Type'} : (term64 _87154) = (term65 _87154).
Proof. exact (fun_ext (fun t : type686 _87154 => @lem3347309 _87154 t)). Qed.
Lemma lem3347315 {_87154 : Type'} : (@all ((_87154 -> Prop) -> Prop)) = (@all ((_87154 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87154 -> Prop) -> Prop))). Qed.
Lemma lem3347324 {_87154 : Type'} : (term66 _87154) = (term67 _87154).
Proof. exact (MK_COMB (@lem3347315 _87154) (@lem3347314 _87154)). Qed.
Lemma lem3347329 {_87154 : Type'} (t : type686 _87154) (t' : _87154 -> Prop) (x : _87154) : (term40 _87154 t t' x) = (term40 _87154 t t' x).
Proof. exact (eq_refl (term40 _87154 t t' x)). Qed.
Lemma lem3347330 {_87154 : Type'} (t : type686 _87154) (x : _87154) : (term42 _87154 t x) = (term42 _87154 t x).
Proof. exact (fun_ext (fun t' : _87154 -> Prop => @lem3347329 _87154 t t' x)). Qed.
Lemma lem3347331 {_87154 : Type'} : (@ex (_87154 -> Prop)) = (@ex (_87154 -> Prop)).
Proof. exact (eq_refl (@ex (_87154 -> Prop))). Qed.
Lemma lem3347332 {_87154 : Type'} (t : type686 _87154) (x : _87154) : (term43 _87154 t x) = (term43 _87154 t x).
Proof. exact (MK_COMB (@lem3347331 _87154) (@lem3347330 _87154 t x)). Qed.
Lemma lem3347337 {_87154 : Type'} (s : type686 _87154) (t : _87154 -> Prop) (x : _87154) : (term40 _87154 s t x) = (term40 _87154 s t x).
Proof. exact (eq_refl (term40 _87154 s t x)). Qed.
Lemma lem3347338 {_87154 : Type'} (s : type686 _87154) (x : _87154) : (term42 _87154 s x) = (term42 _87154 s x).
Proof. exact (fun_ext (fun t : _87154 -> Prop => @lem3347337 _87154 s t x)). Qed.
Lemma lem3347339 {_87154 : Type'} : (@ex (_87154 -> Prop)) = (@ex (_87154 -> Prop)).
Proof. exact (eq_refl (@ex (_87154 -> Prop))). Qed.
Lemma lem3347340 {_87154 : Type'} (s : type686 _87154) (x : _87154) : (term43 _87154 s x) = (term43 _87154 s x).
Proof. exact (MK_COMB (@lem3347339 _87154) (@lem3347338 _87154 s x)). Qed.
Lemma lem3347341 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3347342 {_87154 : Type'} (s : type686 _87154) (x : _87154) : (term45 _87154 s x) = (term45 _87154 s x).
Proof. exact (MK_COMB (@lem3347341) (@lem3347340 _87154 s x)). Qed.
Lemma lem3347343 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (x : _87154) : (term47 _87154 s t x) = (term47 _87154 s t x).
Proof. exact (MK_COMB (@lem3347342 _87154 s x) (@lem3347332 _87154 t x)). Qed.
Lemma lem3347344 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term49 _87154 s t) = (term49 _87154 s t).
Proof. exact (fun_ext (fun x : _87154 => @lem3347343 _87154 s t x)). Qed.
Lemma lem3347345 {_87154 : Type'} : (@all _87154) = (@all _87154).
Proof. exact (eq_refl (@all _87154)). Qed.
Lemma lem3347346 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term50 _87154 s t) = (term50 _87154 s t).
Proof. exact (MK_COMB (@lem3347345 _87154) (@lem3347344 _87154 s t)). Qed.
Lemma lem3347351 {_87154 : Type'} (x : _87154 -> Prop) (y : _87154 -> Prop) (x' : _87154) : (term26 _87154 x y x') = (term26 _87154 x y x').
Proof. exact (eq_refl (term26 _87154 x y x')). Qed.
Lemma lem3347352 {_87154 : Type'} (x : _87154 -> Prop) (y : _87154 -> Prop) : (term28 _87154 x y) = (term28 _87154 x y).
Proof. exact (fun_ext (fun x' : _87154 => @lem3347351 _87154 x y x')). Qed.
Lemma lem3347353 {_87154 : Type'} : (@all _87154) = (@all _87154).
Proof. exact (eq_refl (@all _87154)). Qed.
Lemma lem3347354 {_87154 : Type'} (x : _87154 -> Prop) (y : _87154 -> Prop) : (term29 _87154 x y) = (term29 _87154 x y).
Proof. exact (MK_COMB (@lem3347353 _87154) (@lem3347352 _87154 x y)). Qed.
Lemma lem3347357 {_87154 : Type'} (t : type686 _87154) (y : _87154 -> Prop) : (term22 _87154 t y) = (term22 _87154 t y).
Proof. exact (eq_refl (term22 _87154 t y)). Qed.
Lemma lem3347358 {_87154 : Type'} (t : type686 _87154) (x : _87154 -> Prop) (y : _87154 -> Prop) : (term30 _87154 t x y) = (term30 _87154 t x y).
Proof. exact (MK_COMB (@lem3347357 _87154 t y) (@lem3347354 _87154 x y)). Qed.
Lemma lem3347359 {_87154 : Type'} (t : type686 _87154) (x : _87154 -> Prop) : (term31 _87154 t x) = (term31 _87154 t x).
Proof. exact (fun_ext (fun y : _87154 -> Prop => @lem3347358 _87154 t x y)). Qed.
Lemma lem3347360 {_87154 : Type'} : (@ex (_87154 -> Prop)) = (@ex (_87154 -> Prop)).
Proof. exact (eq_refl (@ex (_87154 -> Prop))). Qed.
Lemma lem3347361 {_87154 : Type'} (t : type686 _87154) (x : _87154 -> Prop) : (term32 _87154 t x) = (term32 _87154 t x).
Proof. exact (MK_COMB (@lem3347360 _87154) (@lem3347359 _87154 t x)). Qed.
Lemma lem3347364 {_87154 : Type'} (s : type686 _87154) (x : _87154 -> Prop) : (term21 _87154 s x) = (term21 _87154 s x).
Proof. exact (eq_refl (term21 _87154 s x)). Qed.
Lemma lem3347365 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (x : _87154 -> Prop) : (term33 _87154 s t x) = (term33 _87154 s t x).
Proof. exact (MK_COMB (@lem3347364 _87154 s x) (@lem3347361 _87154 t x)). Qed.
Lemma lem3347366 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term34 _87154 s t) = (term34 _87154 s t).
Proof. exact (fun_ext (fun x : _87154 -> Prop => @lem3347365 _87154 s t x)). Qed.
Lemma lem3347367 {_87154 : Type'} : (@all (_87154 -> Prop)) = (@all (_87154 -> Prop)).
Proof. exact (eq_refl (@all (_87154 -> Prop))). Qed.
Lemma lem3347368 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term35 _87154 s t) = (term35 _87154 s t).
Proof. exact (MK_COMB (@lem3347367 _87154) (@lem3347366 _87154 s t)). Qed.
Lemma lem3347369 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3347370 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term36 _87154 s t) = (term36 _87154 s t).
Proof. exact (MK_COMB (@lem3347369) (@lem3347368 _87154 s t)). Qed.
Lemma lem3347371 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term51 _87154 s t) = (term51 _87154 s t).
Proof. exact (MK_COMB (@lem3347370 _87154 s t) (@lem3347346 _87154 s t)). Qed.
Lemma lem3347372 {_87154 : Type'} (t : type686 _87154) : (term61 _87154 t) = (term61 _87154 t).
Proof. exact (fun_ext (fun s : type686 _87154 => @lem3347371 _87154 s t)). Qed.
Lemma lem3347373 {_87154 : Type'} : (@all ((_87154 -> Prop) -> Prop)) = (@all ((_87154 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87154 -> Prop) -> Prop))). Qed.
Lemma lem3347374 {_87154 : Type'} (t : type686 _87154) : (term63 _87154 t) = (term63 _87154 t).
Proof. exact (MK_COMB (@lem3347373 _87154) (@lem3347372 _87154 t)). Qed.
Lemma lem3347375 {_87154 : Type'} : (term65 _87154) = (term65 _87154).
Proof. exact (fun_ext (fun t : type686 _87154 => @lem3347374 _87154 t)). Qed.
Lemma lem3347376 {_87154 : Type'} : (@all ((_87154 -> Prop) -> Prop)) = (@all ((_87154 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87154 -> Prop) -> Prop))). Qed.
Lemma lem3347377 {_87154 : Type'} : (term67 _87154) = (term67 _87154).
Proof. exact (MK_COMB (@lem3347376 _87154) (@lem3347375 _87154)). Qed.
Lemma lem3347442 {_87154 : Type'} : (term66 _87154) = (term67 _87154).
Proof. exact (TRANS (@lem3347324 _87154) (@lem3347377 _87154)). Qed.
Lemma lem3347443 {_87154 : Type'} : (term67 _87154) = (term66 _87154).
Proof. exact (SYM (@lem3347442 _87154)). Qed.
Lemma lem3347444 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (h1 : term35 _87154 s t) : term35 _87154 s t.
Proof. exact (h1). Qed.
Lemma lem3347445 {_87154 : Type'} (s : type686 _87154) (x : _87154) (h1 : term43 _87154 s x) : term43 _87154 s x.
Proof. exact (h1). Qed.
Lemma lem3347447 (p : Prop) : p = (term52 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3347448 {_87154 : Type'} (t : type686 _87154) (x : _87154) : (term43 _87154 t x) = (term68 _87154 t x).
Proof. exact (@lem3347447 (term43 _87154 t x)). Qed.
Lemma lem3347449 {_87154 : Type'} (t : type686 _87154) (x : _87154) : (term68 _87154 t x) = (term43 _87154 t x).
Proof. exact (SYM (@lem3347448 _87154 t x)). Qed.
Lemma lem3347450 {_87154 : Type'} (t : type686 _87154) (x : _87154) (h1 : term69 _87154 t x) : term69 _87154 t x.
Proof. exact (h1). Qed.
Lemma lem3347459 {_87154 : Type'} (x : _87154 -> Prop) (y : _87154 -> Prop) (x' : _87154) : (term26 _87154 x y x') = (term70 _87154 x y x').
Proof. exact (@lem17265 (x x') (y x')). Qed.
Lemma lem3347460 {_87154 : Type'} (x : _87154 -> Prop) (y : _87154 -> Prop) : (term28 _87154 x y) = (term71 _87154 x y).
Proof. exact (fun_ext (fun x' : _87154 => @lem3347459 _87154 x y x')). Qed.
Lemma lem3347461 {_87154 : Type'} : (@all _87154) = (@all _87154).
Proof. exact (eq_refl (@all _87154)). Qed.
Lemma lem3347462 {_87154 : Type'} (x : _87154 -> Prop) (y : _87154 -> Prop) : (term29 _87154 x y) = (term72 _87154 x y).
Proof. exact (MK_COMB (@lem3347461 _87154) (@lem3347460 _87154 x y)). Qed.
Lemma lem3347464 {_87154 : Type'} (t : type686 _87154) (y : _87154 -> Prop) : (term22 _87154 t y) = (term22 _87154 t y).
Proof. exact (eq_refl (term22 _87154 t y)). Qed.
Lemma lem3347465 {_87154 : Type'} (t : type686 _87154) (x : _87154 -> Prop) (y : _87154 -> Prop) : (term30 _87154 t x y) = (term73 _87154 t x y).
Proof. exact (MK_COMB (@lem3347464 _87154 t y) (@lem3347462 _87154 x y)). Qed.
Lemma lem3347466 {_87154 : Type'} (t : type686 _87154) (x : _87154 -> Prop) : (term31 _87154 t x) = (term74 _87154 t x).
Proof. exact (fun_ext (fun y : _87154 -> Prop => @lem3347465 _87154 t x y)). Qed.
Lemma lem3347467 {_87154 : Type'} : (@ex (_87154 -> Prop)) = (@ex (_87154 -> Prop)).
Proof. exact (eq_refl (@ex (_87154 -> Prop))). Qed.
Lemma lem3347468 {_87154 : Type'} (t : type686 _87154) (x : _87154 -> Prop) : (term32 _87154 t x) = (term75 _87154 t x).
Proof. exact (MK_COMB (@lem3347467 _87154) (@lem3347466 _87154 t x)). Qed.
Lemma lem3347470 {_87154 : Type'} (s : type686 _87154) (x : _87154 -> Prop) : (term76 _87154 s x) = (term76 _87154 s x).
Proof. exact (eq_refl (term76 _87154 s x)). Qed.
Lemma lem3347471 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (x : _87154 -> Prop) : (term77 _87154 s t x) = (term78 _87154 s t x).
Proof. exact (MK_COMB (@lem3347470 _87154 s x) (@lem3347468 _87154 t x)). Qed.
Lemma lem3347472 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (x : _87154 -> Prop) : (term33 _87154 s t x) = (term77 _87154 s t x).
Proof. exact (@lem17265 (s x) (term32 _87154 t x)). Qed.
Lemma lem3347473 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (x : _87154 -> Prop) : (term33 _87154 s t x) = (term78 _87154 s t x).
Proof. exact (TRANS (@lem3347472 _87154 s t x) (@lem3347471 _87154 s t x)). Qed.
Lemma lem3347474 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term34 _87154 s t) = (term79 _87154 s t).
Proof. exact (fun_ext (fun x : _87154 -> Prop => @lem3347473 _87154 s t x)). Qed.
Lemma lem3347475 {_87154 : Type'} : (@all (_87154 -> Prop)) = (@all (_87154 -> Prop)).
Proof. exact (eq_refl (@all (_87154 -> Prop))). Qed.
Lemma lem3347476 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term35 _87154 s t) = (term80 _87154 s t).
Proof. exact (MK_COMB (@lem3347475 _87154) (@lem3347474 _87154 s t)). Qed.
Lemma lem3347587 {A : Type'} (P : Prop) (Q : A -> Prop) : (term81 A P Q) = (term82 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3347588 {_87154 : Type'} (P : Prop) (Q : type686 _87154) : (term83 _87154 P Q) = (term84 _87154 P Q).
Proof. exact (@lem3347587 (_87154 -> Prop) P Q). Qed.
Lemma lem3347589 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (x : _87154 -> Prop) : (term85 _87154 s t x) = (term86 _87154 s t x).
Proof. exact (@lem3347588 _87154 (term87 _87154 s x) (term74 _87154 t x)). Qed.
Lemma lem3347590 {_87154 : Type'} (t : type686 _87154) (x : _87154 -> Prop) (y : _87154 -> Prop) : (term88 _87154 t x y) = (term73 _87154 t x y).
Proof. exact (eq_refl (term88 _87154 t x y)). Qed.
Lemma lem3347591 {_87154 : Type'} (t : type686 _87154) (x : _87154 -> Prop) : (term89 _87154 t x) = (term74 _87154 t x).
Proof. exact (fun_ext (fun y : _87154 -> Prop => @lem3347590 _87154 t x y)). Qed.
Lemma lem3347592 {_87154 : Type'} : (@ex (_87154 -> Prop)) = (@ex (_87154 -> Prop)).
Proof. exact (eq_refl (@ex (_87154 -> Prop))). Qed.
Lemma lem3347593 {_87154 : Type'} (t : type686 _87154) (x : _87154 -> Prop) : (term90 _87154 t x) = (term75 _87154 t x).
Proof. exact (MK_COMB (@lem3347592 _87154) (@lem3347591 _87154 t x)). Qed.
Lemma lem3347594 {_87154 : Type'} (s : type686 _87154) (x : _87154 -> Prop) : (term76 _87154 s x) = (term76 _87154 s x).
Proof. exact (eq_refl (term76 _87154 s x)). Qed.
Lemma lem3347595 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (x : _87154 -> Prop) : (term85 _87154 s t x) = (term78 _87154 s t x).
Proof. exact (MK_COMB (@lem3347594 _87154 s x) (@lem3347593 _87154 t x)). Qed.
Lemma lem3347596 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3347597 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (x : _87154 -> Prop) : (term91 _87154 s t x) = (term92 _87154 s t x).
Proof. exact (MK_COMB (@lem3347596) (@lem3347595 _87154 s t x)). Qed.
Lemma lem3347598 {_87154 : Type'} (t : type686 _87154) (x : _87154 -> Prop) (y : _87154 -> Prop) : (term88 _87154 t x y) = (term73 _87154 t x y).
Proof. exact (eq_refl (term88 _87154 t x y)). Qed.
Lemma lem3347599 {_87154 : Type'} (s : type686 _87154) (x : _87154 -> Prop) : (term76 _87154 s x) = (term76 _87154 s x).
Proof. exact (eq_refl (term76 _87154 s x)). Qed.
Lemma lem3347600 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (x : _87154 -> Prop) (y : _87154 -> Prop) : (term93 _87154 s t x y) = (term94 _87154 s t x y).
Proof. exact (MK_COMB (@lem3347599 _87154 s x) (@lem3347598 _87154 t x y)). Qed.
Lemma lem3347601 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (x : _87154 -> Prop) : (term95 _87154 s t x) = (term96 _87154 s t x).
Proof. exact (fun_ext (fun y : _87154 -> Prop => @lem3347600 _87154 s t x y)). Qed.
Lemma lem3347602 {_87154 : Type'} : (@ex (_87154 -> Prop)) = (@ex (_87154 -> Prop)).
Proof. exact (eq_refl (@ex (_87154 -> Prop))). Qed.
Lemma lem3347603 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (x : _87154 -> Prop) : (term86 _87154 s t x) = (term97 _87154 s t x).
Proof. exact (MK_COMB (@lem3347602 _87154) (@lem3347601 _87154 s t x)). Qed.
Lemma lem3347604 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (x : _87154 -> Prop) : ((term85 _87154 s t x) = (term86 _87154 s t x)) = ((term78 _87154 s t x) = (term97 _87154 s t x)).
Proof. exact (MK_COMB (@lem3347597 _87154 s t x) (@lem3347603 _87154 s t x)). Qed.
Lemma lem3347605 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (x : _87154 -> Prop) : (term78 _87154 s t x) = (term97 _87154 s t x).
Proof. exact (EQ_MP (@lem3347604 _87154 s t x) (@lem3347589 _87154 s t x)). Qed.
Lemma lem3347606 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term79 _87154 s t) = (term98 _87154 s t).
Proof. exact (fun_ext (fun x : _87154 -> Prop => @lem3347605 _87154 s t x)). Qed.
Lemma lem3347607 {_87154 : Type'} : (@all (_87154 -> Prop)) = (@all (_87154 -> Prop)).
Proof. exact (eq_refl (@all (_87154 -> Prop))). Qed.
Lemma lem3347608 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term80 _87154 s t) = (term99 _87154 s t).
Proof. exact (MK_COMB (@lem3347607 _87154) (@lem3347606 _87154 s t)). Qed.
Lemma lem3347610 {A B : Type'} (P : type1413 A B) : (term100 A B P) = (term101 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3347611 {_87154 : Type'} (P : type639 _87154) : (term102 _87154 P) = (term103 _87154 P).
Proof. exact (@lem3347610 (_87154 -> Prop) (_87154 -> Prop) P). Qed.
Lemma lem3347612 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term104 _87154 s t) = (term105 _87154 s t).
Proof. exact (@lem3347611 _87154 (term106 _87154 s t)). Qed.
Lemma lem3347613 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (x : _87154 -> Prop) : (term107 _87154 s t x) = (term96 _87154 s t x).
Proof. exact (eq_refl (term107 _87154 s t x)). Qed.
Lemma lem3347614 {_87154 : Type'} (y : _87154 -> Prop) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3347615 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (x : _87154 -> Prop) (y : _87154 -> Prop) : (term108 _87154 s t x y) = (term109 _87154 s t x y).
Proof. exact (MK_COMB (@lem3347613 _87154 s t x) (@lem3347614 _87154 y)). Qed.
Lemma lem3347616 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (x : _87154 -> Prop) (y : _87154 -> Prop) : (term109 _87154 s t x y) = (term94 _87154 s t x y).
Proof. exact (eq_refl (term109 _87154 s t x y)). Qed.
Lemma lem3347617 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (x : _87154 -> Prop) (y : _87154 -> Prop) : (term108 _87154 s t x y) = (term94 _87154 s t x y).
Proof. exact (TRANS (@lem3347615 _87154 s t x y) (@lem3347616 _87154 s t x y)). Qed.
Lemma lem3347618 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (x : _87154 -> Prop) : (term110 _87154 s t x) = (term96 _87154 s t x).
Proof. exact (fun_ext (fun y : _87154 -> Prop => @lem3347617 _87154 s t x y)). Qed.
Lemma lem3347619 {_87154 : Type'} : (@ex (_87154 -> Prop)) = (@ex (_87154 -> Prop)).
Proof. exact (eq_refl (@ex (_87154 -> Prop))). Qed.
Lemma lem3347620 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (x : _87154 -> Prop) : (term111 _87154 s t x) = (term97 _87154 s t x).
Proof. exact (MK_COMB (@lem3347619 _87154) (@lem3347618 _87154 s t x)). Qed.
Lemma lem3347621 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term112 _87154 s t) = (term98 _87154 s t).
Proof. exact (fun_ext (fun x : _87154 -> Prop => @lem3347620 _87154 s t x)). Qed.
Lemma lem3347622 {_87154 : Type'} : (@all (_87154 -> Prop)) = (@all (_87154 -> Prop)).
Proof. exact (eq_refl (@all (_87154 -> Prop))). Qed.
Lemma lem3347623 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term104 _87154 s t) = (term99 _87154 s t).
Proof. exact (MK_COMB (@lem3347622 _87154) (@lem3347621 _87154 s t)). Qed.
Lemma lem3347624 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3347625 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term113 _87154 s t) = (term114 _87154 s t).
Proof. exact (MK_COMB (@lem3347624) (@lem3347623 _87154 s t)). Qed.
Lemma lem3347626 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (x : _87154 -> Prop) : (term107 _87154 s t x) = (term96 _87154 s t x).
Proof. exact (eq_refl (term107 _87154 s t x)). Qed.
Lemma lem3347627 {_87154 : Type'} (y : type672 _87154) (x : _87154 -> Prop) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem3347628 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) : (term115 _87154 s t y x) = (term116 _87154 s t y x).
Proof. exact (MK_COMB (@lem3347626 _87154 s t x) (@lem3347627 _87154 y x)). Qed.
Lemma lem3347629 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) : (term116 _87154 s t y x) = (term117 _87154 s t y x).
Proof. exact (eq_refl (term116 _87154 s t y x)). Qed.
Lemma lem3347630 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) : (term115 _87154 s t y x) = (term117 _87154 s t y x).
Proof. exact (TRANS (@lem3347628 _87154 s t y x) (@lem3347629 _87154 s t y x)). Qed.
Lemma lem3347631 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) : (term118 _87154 s t y) = (term119 _87154 s t y).
Proof. exact (fun_ext (fun x : _87154 -> Prop => @lem3347630 _87154 s t y x)). Qed.
Lemma lem3347632 {_87154 : Type'} : (@all (_87154 -> Prop)) = (@all (_87154 -> Prop)).
Proof. exact (eq_refl (@all (_87154 -> Prop))). Qed.
Lemma lem3347633 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) : (term120 _87154 s t y) = (term121 _87154 s t y).
Proof. exact (MK_COMB (@lem3347632 _87154) (@lem3347631 _87154 s t y)). Qed.
Lemma lem3347634 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term122 _87154 s t) = (term123 _87154 s t).
Proof. exact (fun_ext (fun y : type672 _87154 => @lem3347633 _87154 s t y)). Qed.
Lemma lem3347635 {_87154 : Type'} : (@ex ((_87154 -> Prop) -> _87154 -> Prop)) = (@ex ((_87154 -> Prop) -> _87154 -> Prop)).
Proof. exact (eq_refl (@ex ((_87154 -> Prop) -> _87154 -> Prop))). Qed.
Lemma lem3347636 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term105 _87154 s t) = (term124 _87154 s t).
Proof. exact (MK_COMB (@lem3347635 _87154) (@lem3347634 _87154 s t)). Qed.
Lemma lem3347637 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : ((term104 _87154 s t) = (term105 _87154 s t)) = ((term99 _87154 s t) = (term124 _87154 s t)).
Proof. exact (MK_COMB (@lem3347625 _87154 s t) (@lem3347636 _87154 s t)). Qed.
Lemma lem3347638 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term99 _87154 s t) = (term124 _87154 s t).
Proof. exact (EQ_MP (@lem3347637 _87154 s t) (@lem3347612 _87154 s t)). Qed.
Lemma lem3347640 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term80 _87154 s t) = (term124 _87154 s t).
Proof. exact (TRANS (@lem3347608 _87154 s t) (@lem3347638 _87154 s t)). Qed.
Lemma lem3347641 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term35 _87154 s t) = (term124 _87154 s t).
Proof. exact (TRANS (@lem3347476 _87154 s t) (@lem3347640 _87154 s t)). Qed.
Lemma lem3347642 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (h1 : term35 _87154 s t) : term124 _87154 s t.
Proof. exact (EQ_MP (@lem3347641 _87154 s t) (@lem3347444 _87154 s t h1)). Qed.
Lemma lem3347647 {_87154 : Type'} (s : type686 _87154) (t : _87154 -> Prop) (x : _87154) : (term40 _87154 s t x) = (term40 _87154 s t x).
Proof. exact (eq_refl (term40 _87154 s t x)). Qed.
Lemma lem3347648 {_87154 : Type'} (s : type686 _87154) (x : _87154) : (term42 _87154 s x) = (term42 _87154 s x).
Proof. exact (fun_ext (fun t : _87154 -> Prop => @lem3347647 _87154 s t x)). Qed.
Lemma lem3347649 {_87154 : Type'} : (@ex (_87154 -> Prop)) = (@ex (_87154 -> Prop)).
Proof. exact (eq_refl (@ex (_87154 -> Prop))). Qed.
Lemma lem3347682 {_87154 : Type'} (s : type686 _87154) (x : _87154) : (term43 _87154 s x) = (term43 _87154 s x).
Proof. exact (MK_COMB (@lem3347649 _87154) (@lem3347648 _87154 s x)). Qed.
Lemma lem3347683 {_87154 : Type'} (s : type686 _87154) (x : _87154) (h1 : term43 _87154 s x) : term43 _87154 s x.
Proof. exact (EQ_MP (@lem3347682 _87154 s x) (@lem3347445 _87154 s x h1)). Qed.
Lemma lem3347690 {_87154 : Type'} (t : type686 _87154) (t' : _87154 -> Prop) (x : _87154) : (term125 _87154 t t' x) = (term126 _87154 t t' x).
Proof. exact (@lem17045 (t t') (t' x)). Qed.
Lemma lem3347691 {_87154 : Type'} (P : type686 _87154) : (term127 _87154 P) = (term128 _87154 P).
Proof. exact (@lem18394 (_87154 -> Prop) P). Qed.
Lemma lem3347692 {_87154 : Type'} (t : type686 _87154) (x : _87154) : (term69 _87154 t x) = (term129 _87154 t x).
Proof. exact (@lem3347691 _87154 (term42 _87154 t x)). Qed.
Lemma lem3347693 {_87154 : Type'} (t : type686 _87154) (t' : _87154 -> Prop) (x : _87154) : (term130 _87154 t x t') = (term40 _87154 t t' x).
Proof. exact (eq_refl (term130 _87154 t x t')). Qed.
Lemma lem3347694 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3347695 {_87154 : Type'} (t : type686 _87154) (t' : _87154 -> Prop) (x : _87154) : (term131 _87154 t x t') = (term125 _87154 t t' x).
Proof. exact (MK_COMB (@lem3347694) (@lem3347693 _87154 t t' x)). Qed.
Lemma lem3347696 {_87154 : Type'} (t : type686 _87154) (t' : _87154 -> Prop) (x : _87154) : (term131 _87154 t x t') = (term126 _87154 t t' x).
Proof. exact (TRANS (@lem3347695 _87154 t t' x) (@lem3347690 _87154 t t' x)). Qed.
Lemma lem3347697 {_87154 : Type'} (t : type686 _87154) (x : _87154) : (term132 _87154 t x) = (term133 _87154 t x).
Proof. exact (fun_ext (fun t' : _87154 -> Prop => @lem3347696 _87154 t t' x)). Qed.
Lemma lem3347698 {_87154 : Type'} : (@all (_87154 -> Prop)) = (@all (_87154 -> Prop)).
Proof. exact (eq_refl (@all (_87154 -> Prop))). Qed.
Lemma lem3347699 {_87154 : Type'} (t : type686 _87154) (x : _87154) : (term129 _87154 t x) = (term134 _87154 t x).
Proof. exact (MK_COMB (@lem3347698 _87154) (@lem3347697 _87154 t x)). Qed.
Lemma lem3347752 {_87154 : Type'} (t : type686 _87154) (x : _87154) : (term69 _87154 t x) = (term134 _87154 t x).
Proof. exact (TRANS (@lem3347692 _87154 t x) (@lem3347699 _87154 t x)). Qed.
Lemma lem3347753 {_87154 : Type'} (t : type686 _87154) (x : _87154) (h1 : term69 _87154 t x) : term134 _87154 t x.
Proof. exact (EQ_MP (@lem3347752 _87154 t x) (@lem3347450 _87154 t x h1)). Qed.
Lemma lem3347754 {_87154 : Type'} (s : type686 _87154) (t' : _87154 -> Prop) (x : _87154) (h1 : term40 _87154 s t' x) : term40 _87154 s t' x.
Proof. exact (h1). Qed.
Lemma lem3347755 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (h1 : term121 _87154 s t y) : term121 _87154 s t y.
Proof. exact (h1). Qed.
Lemma lem3347756 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3347761 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3347762 {_87154 : Type'} (f : _87154 -> Prop) (x : _87154) : (f x) = (@I (_87154 -> Prop) f x).
Proof. exact (@lem3347761 _87154 Prop f x). Qed.
Lemma lem3347764 {_87154 : Type'} (t : _87154 -> Prop) (x : _87154) : (t x) = (@I (_87154 -> Prop) t x).
Proof. exact (@lem3347762 _87154 t x). Qed.
Lemma lem3347765 {_87154 : Type'} (t : _87154 -> Prop) (x : _87154) : (term135 _87154 t x) = (term136 _87154 t x).
Proof. exact (MK_COMB (@lem3347756) (@lem3347764 _87154 t x)). Qed.
Lemma lem3347766 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3347771 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3347772 {_87154 : Type'} (f : type686 _87154) (x : _87154 -> Prop) : (f x) = (@I ((_87154 -> Prop) -> Prop) f x).
Proof. exact (@lem3347771 (_87154 -> Prop) Prop f x). Qed.
Lemma lem3347774 {_87154 : Type'} (t : type686 _87154) (t' : _87154 -> Prop) : (t t') = (@I ((_87154 -> Prop) -> Prop) t t').
Proof. exact (@lem3347772 _87154 t t'). Qed.
Lemma lem3347775 {_87154 : Type'} (t : type686 _87154) (t' : _87154 -> Prop) : (term87 _87154 t t') = (term137 _87154 t t').
Proof. exact (MK_COMB (@lem3347766) (@lem3347774 _87154 t t')). Qed.
Lemma lem3347776 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3347777 {_87154 : Type'} (t : type686 _87154) (t' : _87154 -> Prop) : (term76 _87154 t t') = (term138 _87154 t t').
Proof. exact (MK_COMB (@lem3347776) (@lem3347775 _87154 t t')). Qed.
Lemma lem3347778 {_87154 : Type'} (t : type686 _87154) (t' : _87154 -> Prop) (x : _87154) : (term126 _87154 t t' x) = (term139 _87154 t t' x).
Proof. exact (MK_COMB (@lem3347777 _87154 t t') (@lem3347765 _87154 t' x)). Qed.
Lemma lem3347779 {_87154 : Type'} (t : type686 _87154) (x : _87154) : (term133 _87154 t x) = (term140 _87154 t x).
Proof. exact (fun_ext (fun t' : _87154 -> Prop => @lem3347778 _87154 t t' x)). Qed.
Lemma lem3347780 {_87154 : Type'} : (@all (_87154 -> Prop)) = (@all (_87154 -> Prop)).
Proof. exact (eq_refl (@all (_87154 -> Prop))). Qed.
Lemma lem3347781 {_87154 : Type'} (t : type686 _87154) (x : _87154) : (term134 _87154 t x) = (term141 _87154 t x).
Proof. exact (MK_COMB (@lem3347780 _87154) (@lem3347779 _87154 t x)). Qed.
Lemma lem3347782 {_87154 : Type'} (t : type686 _87154) (x : _87154) (h1 : term69 _87154 t x) : term141 _87154 t x.
Proof. exact (EQ_MP (@lem3347781 _87154 t x) (@lem3347753 _87154 t x h1)). Qed.
Lemma lem3347787 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3347788 {_87154 : Type'} (f : _87154 -> Prop) (x : _87154) : (f x) = (@I (_87154 -> Prop) f x).
Proof. exact (@lem3347787 _87154 Prop f x). Qed.
Lemma lem3347790 {_87154 : Type'} (t' : _87154 -> Prop) (x : _87154) : (t' x) = (@I (_87154 -> Prop) t' x).
Proof. exact (@lem3347788 _87154 t' x). Qed.
Lemma lem3347795 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3347796 {_87154 : Type'} (f : type686 _87154) (x : _87154 -> Prop) : (f x) = (@I ((_87154 -> Prop) -> Prop) f x).
Proof. exact (@lem3347795 (_87154 -> Prop) Prop f x). Qed.
Lemma lem3347798 {_87154 : Type'} (s : type686 _87154) (t' : _87154 -> Prop) : (s t') = (@I ((_87154 -> Prop) -> Prop) s t').
Proof. exact (@lem3347796 _87154 s t'). Qed.
Lemma lem3347799 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3347800 {_87154 : Type'} (s : type686 _87154) (t' : _87154 -> Prop) : (term22 _87154 s t') = (term142 _87154 s t').
Proof. exact (MK_COMB (@lem3347799) (@lem3347798 _87154 s t')). Qed.
Lemma lem3347801 {_87154 : Type'} (s : type686 _87154) (t' : _87154 -> Prop) (x : _87154) : (term40 _87154 s t' x) = (term143 _87154 s t' x).
Proof. exact (MK_COMB (@lem3347800 _87154 s t') (@lem3347790 _87154 t' x)). Qed.
Lemma lem3347802 {_87154 : Type'} (s : type686 _87154) (t' : _87154 -> Prop) (x : _87154) (h1 : term40 _87154 s t' x) : term143 _87154 s t' x.
Proof. exact (EQ_MP (@lem3347801 _87154 s t' x) (@lem3347754 _87154 s t' x h1)). Qed.
Lemma lem3347809 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3347810 {_87154 : Type'} (f : type672 _87154) (x : _87154 -> Prop) : (f x) = (@I ((_87154 -> Prop) -> _87154 -> Prop) f x).
Proof. exact (@lem3347809 (_87154 -> Prop) (_87154 -> Prop) f x). Qed.
Lemma lem3347811 {_87154 : Type'} (y : type672 _87154) (x : _87154 -> Prop) : (y x) = (@I ((_87154 -> Prop) -> _87154 -> Prop) y x).
Proof. exact (@lem3347810 _87154 y x). Qed.
Lemma lem3347812 {_87154 : Type'} (x : _87154) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3347813 {_87154 : Type'} (y : type672 _87154) (x : _87154 -> Prop) (x' : _87154) : (y x x') = (@I ((_87154 -> Prop) -> _87154 -> Prop) y x x').
Proof. exact (MK_COMB (@lem3347811 _87154 y x) (@lem3347812 _87154 x')). Qed.
Lemma lem3347815 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3347816 {_87154 : Type'} (f : _87154 -> Prop) (x : _87154) : (f x) = (@I (_87154 -> Prop) f x).
Proof. exact (@lem3347815 _87154 Prop f x). Qed.
Lemma lem3347817 {_87154 : Type'} (y : type672 _87154) (x : _87154 -> Prop) (x' : _87154) : (@I ((_87154 -> Prop) -> _87154 -> Prop) y x x') = (term144 _87154 y x x').
Proof. exact (@lem3347816 _87154 (@I ((_87154 -> Prop) -> _87154 -> Prop) y x) x'). Qed.
Lemma lem3347819 {_87154 : Type'} (y : type672 _87154) (x : _87154 -> Prop) (x' : _87154) : (y x x') = (term144 _87154 y x x').
Proof. exact (TRANS (@lem3347813 _87154 y x x') (@lem3347817 _87154 y x x')). Qed.
Lemma lem3347820 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3347825 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3347826 {_87154 : Type'} (f : _87154 -> Prop) (x : _87154) : (f x) = (@I (_87154 -> Prop) f x).
Proof. exact (@lem3347825 _87154 Prop f x). Qed.
Lemma lem3347828 {_87154 : Type'} (x : _87154 -> Prop) (x' : _87154) : (x x') = (@I (_87154 -> Prop) x x').
Proof. exact (@lem3347826 _87154 x x'). Qed.
Lemma lem3347829 {_87154 : Type'} (x : _87154 -> Prop) (x' : _87154) : (term135 _87154 x x') = (term136 _87154 x x').
Proof. exact (MK_COMB (@lem3347820) (@lem3347828 _87154 x x')). Qed.
Lemma lem3347830 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3347831 {_87154 : Type'} (x : _87154 -> Prop) (x' : _87154) : (term145 _87154 x x') = (term146 _87154 x x').
Proof. exact (MK_COMB (@lem3347830) (@lem3347829 _87154 x x')). Qed.
Lemma lem3347832 {_87154 : Type'} (y : type672 _87154) (x : _87154 -> Prop) (x' : _87154) : (term147 _87154 y x x') = (term148 _87154 y x x').
Proof. exact (MK_COMB (@lem3347831 _87154 x x') (@lem3347819 _87154 y x x')). Qed.
Lemma lem3347833 {_87154 : Type'} (y : type672 _87154) (x : _87154 -> Prop) : (term149 _87154 y x) = (term150 _87154 y x).
Proof. exact (fun_ext (fun x' : _87154 => @lem3347832 _87154 y x x')). Qed.
Lemma lem3347834 {_87154 : Type'} : (@all _87154) = (@all _87154).
Proof. exact (eq_refl (@all _87154)). Qed.
Lemma lem3347835 {_87154 : Type'} (y : type672 _87154) (x : _87154 -> Prop) : (term151 _87154 y x) = (term152 _87154 y x).
Proof. exact (MK_COMB (@lem3347834 _87154) (@lem3347833 _87154 y x)). Qed.
Lemma lem3347836 {_87154 : Type'} (t : type686 _87154) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3347841 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3347842 {_87154 : Type'} (f : type672 _87154) (x : _87154 -> Prop) : (f x) = (@I ((_87154 -> Prop) -> _87154 -> Prop) f x).
Proof. exact (@lem3347841 (_87154 -> Prop) (_87154 -> Prop) f x). Qed.
Lemma lem3347844 {_87154 : Type'} (y : type672 _87154) (x : _87154 -> Prop) : (y x) = (@I ((_87154 -> Prop) -> _87154 -> Prop) y x).
Proof. exact (@lem3347842 _87154 y x). Qed.
Lemma lem3347845 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) : (term153 _87154 t y x) = (term154 _87154 t y x).
Proof. exact (MK_COMB (@lem3347836 _87154 t) (@lem3347844 _87154 y x)). Qed.
Lemma lem3347847 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3347848 {_87154 : Type'} (f : type686 _87154) (x : _87154 -> Prop) : (f x) = (@I ((_87154 -> Prop) -> Prop) f x).
Proof. exact (@lem3347847 (_87154 -> Prop) Prop f x). Qed.
Lemma lem3347849 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) : (term154 _87154 t y x) = (term155 _87154 t y x).
Proof. exact (@lem3347848 _87154 t (@I ((_87154 -> Prop) -> _87154 -> Prop) y x)). Qed.
Lemma lem3347850 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) : (term153 _87154 t y x) = (term155 _87154 t y x).
Proof. exact (TRANS (@lem3347845 _87154 t y x) (@lem3347849 _87154 t y x)). Qed.
Lemma lem3347851 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3347852 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) : (term156 _87154 t y x) = (term157 _87154 t y x).
Proof. exact (MK_COMB (@lem3347851) (@lem3347850 _87154 t y x)). Qed.
Lemma lem3347853 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) : (term158 _87154 t y x) = (term159 _87154 t y x).
Proof. exact (MK_COMB (@lem3347852 _87154 t y x) (@lem3347835 _87154 y x)). Qed.
Lemma lem3347854 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3347859 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3347860 {_87154 : Type'} (f : type686 _87154) (x : _87154 -> Prop) : (f x) = (@I ((_87154 -> Prop) -> Prop) f x).
Proof. exact (@lem3347859 (_87154 -> Prop) Prop f x). Qed.
Lemma lem3347862 {_87154 : Type'} (s : type686 _87154) (x : _87154 -> Prop) : (s x) = (@I ((_87154 -> Prop) -> Prop) s x).
Proof. exact (@lem3347860 _87154 s x). Qed.
Lemma lem3347863 {_87154 : Type'} (s : type686 _87154) (x : _87154 -> Prop) : (term87 _87154 s x) = (term137 _87154 s x).
Proof. exact (MK_COMB (@lem3347854) (@lem3347862 _87154 s x)). Qed.
Lemma lem3347864 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3347865 {_87154 : Type'} (s : type686 _87154) (x : _87154 -> Prop) : (term76 _87154 s x) = (term138 _87154 s x).
Proof. exact (MK_COMB (@lem3347864) (@lem3347863 _87154 s x)). Qed.
Lemma lem3347866 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) : (term117 _87154 s t y x) = (term160 _87154 s t y x).
Proof. exact (MK_COMB (@lem3347865 _87154 s x) (@lem3347853 _87154 t y x)). Qed.
Lemma lem3347867 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) : (term119 _87154 s t y) = (term161 _87154 s t y).
Proof. exact (fun_ext (fun x : _87154 -> Prop => @lem3347866 _87154 s t y x)). Qed.
Lemma lem3347868 {_87154 : Type'} : (@all (_87154 -> Prop)) = (@all (_87154 -> Prop)).
Proof. exact (eq_refl (@all (_87154 -> Prop))). Qed.
Lemma lem3347869 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) : (term121 _87154 s t y) = (term162 _87154 s t y).
Proof. exact (MK_COMB (@lem3347868 _87154) (@lem3347867 _87154 s t y)). Qed.
Lemma lem3347870 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (h1 : term121 _87154 s t y) : term162 _87154 s t y.
Proof. exact (EQ_MP (@lem3347869 _87154 s t y) (@lem3347755 _87154 s t y h1)). Qed.
Lemma lem3347880 {_87154 : Type'} (t : type686 _87154) (t' : _87154 -> Prop) (x : _87154) : (term139 _87154 t t' x) = (term139 _87154 t t' x).
Proof. exact (eq_refl (term139 _87154 t t' x)). Qed.
Lemma lem3347881 {_87154 : Type'} (t : type686 _87154) (x : _87154) : (term140 _87154 t x) = (term140 _87154 t x).
Proof. exact (fun_ext (fun t' : _87154 -> Prop => @lem3347880 _87154 t t' x)). Qed.
Lemma lem3347882 {_87154 : Type'} : (@all (_87154 -> Prop)) = (@all (_87154 -> Prop)).
Proof. exact (eq_refl (@all (_87154 -> Prop))). Qed.
Lemma lem3347884 {_87154 : Type'} (t : type686 _87154) (x : _87154) : (term141 _87154 t x) = (term141 _87154 t x).
Proof. exact (MK_COMB (@lem3347882 _87154) (@lem3347881 _87154 t x)). Qed.
Lemma lem3347885 {_87154 : Type'} (t : type686 _87154) (x : _87154) (h1 : term69 _87154 t x) : term141 _87154 t x.
Proof. exact (EQ_MP (@lem3347884 _87154 t x) (@lem3347782 _87154 t x h1)). Qed.
Lemma lem3347887 {A : Type'} (P : Prop) (Q : A -> Prop) : (term163 A P Q) = (term164 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem3347888 {_87154 : Type'} (P : Prop) (Q : _87154 -> Prop) : (term163 _87154 P Q) = (term164 _87154 P Q).
Proof. exact (@lem3347887 _87154 P Q). Qed.
Lemma lem3347889 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) : (term165 _87154 t y x) = (term166 _87154 t y x).
Proof. exact (@lem3347888 _87154 (term155 _87154 t y x) (term150 _87154 y x)). Qed.
Lemma lem3347890 {_87154 : Type'} (y : type672 _87154) (x : _87154 -> Prop) (x' : _87154) : (term167 _87154 y x x') = (term148 _87154 y x x').
Proof. exact (eq_refl (term167 _87154 y x x')). Qed.
Lemma lem3347891 {_87154 : Type'} (y : type672 _87154) (x : _87154 -> Prop) : (term168 _87154 y x) = (term150 _87154 y x).
Proof. exact (fun_ext (fun x' : _87154 => @lem3347890 _87154 y x x')). Qed.
Lemma lem3347892 {_87154 : Type'} : (@all _87154) = (@all _87154).
Proof. exact (eq_refl (@all _87154)). Qed.
Lemma lem3347893 {_87154 : Type'} (y : type672 _87154) (x : _87154 -> Prop) : (term169 _87154 y x) = (term152 _87154 y x).
Proof. exact (MK_COMB (@lem3347892 _87154) (@lem3347891 _87154 y x)). Qed.
Lemma lem3347894 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) : (term157 _87154 t y x) = (term157 _87154 t y x).
Proof. exact (eq_refl (term157 _87154 t y x)). Qed.
Lemma lem3347895 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) : (term165 _87154 t y x) = (term159 _87154 t y x).
Proof. exact (MK_COMB (@lem3347894 _87154 t y x) (@lem3347893 _87154 y x)). Qed.
Lemma lem3347896 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3347897 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) : (term170 _87154 t y x) = (term171 _87154 t y x).
Proof. exact (MK_COMB (@lem3347896) (@lem3347895 _87154 t y x)). Qed.
Lemma lem3347898 {_87154 : Type'} (y : type672 _87154) (x : _87154 -> Prop) (x' : _87154) : (term167 _87154 y x x') = (term148 _87154 y x x').
Proof. exact (eq_refl (term167 _87154 y x x')). Qed.
Lemma lem3347899 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) : (term157 _87154 t y x) = (term157 _87154 t y x).
Proof. exact (eq_refl (term157 _87154 t y x)). Qed.
Lemma lem3347900 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) (x' : _87154) : (term172 _87154 t y x x') = (term173 _87154 t y x x').
Proof. exact (MK_COMB (@lem3347899 _87154 t y x) (@lem3347898 _87154 y x x')). Qed.
Lemma lem3347901 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) : (term174 _87154 t y x) = (term175 _87154 t y x).
Proof. exact (fun_ext (fun x' : _87154 => @lem3347900 _87154 t y x x')). Qed.
Lemma lem3347902 {_87154 : Type'} : (@all _87154) = (@all _87154).
Proof. exact (eq_refl (@all _87154)). Qed.
Lemma lem3347903 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) : (term166 _87154 t y x) = (term176 _87154 t y x).
Proof. exact (MK_COMB (@lem3347902 _87154) (@lem3347901 _87154 t y x)). Qed.
Lemma lem3347904 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) : ((term165 _87154 t y x) = (term166 _87154 t y x)) = ((term159 _87154 t y x) = (term176 _87154 t y x)).
Proof. exact (MK_COMB (@lem3347897 _87154 t y x) (@lem3347903 _87154 t y x)). Qed.
Lemma lem3347905 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) : (term159 _87154 t y x) = (term176 _87154 t y x).
Proof. exact (EQ_MP (@lem3347904 _87154 t y x) (@lem3347889 _87154 t y x)). Qed.
Lemma lem3347906 {_87154 : Type'} (s : type686 _87154) (x : _87154 -> Prop) : (term138 _87154 s x) = (term138 _87154 s x).
Proof. exact (eq_refl (term138 _87154 s x)). Qed.
Lemma lem3347907 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) : (term160 _87154 s t y x) = (term177 _87154 s t y x).
Proof. exact (MK_COMB (@lem3347906 _87154 s x) (@lem3347905 _87154 t y x)). Qed.
Lemma lem3347909 {A : Type'} (P : Prop) (Q : A -> Prop) : (term178 A P Q) = (term179 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3347910 {_87154 : Type'} (P : Prop) (Q : _87154 -> Prop) : (term178 _87154 P Q) = (term179 _87154 P Q).
Proof. exact (@lem3347909 _87154 P Q). Qed.
Lemma lem3347911 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) : (term180 _87154 s t y x) = (term181 _87154 s t y x).
Proof. exact (@lem3347910 _87154 (term137 _87154 s x) (term175 _87154 t y x)). Qed.
Lemma lem3347912 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) (x' : _87154) : (term182 _87154 t y x x') = (term173 _87154 t y x x').
Proof. exact (eq_refl (term182 _87154 t y x x')). Qed.
Lemma lem3347913 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) : (term183 _87154 t y x) = (term175 _87154 t y x).
Proof. exact (fun_ext (fun x' : _87154 => @lem3347912 _87154 t y x x')). Qed.
Lemma lem3347914 {_87154 : Type'} : (@all _87154) = (@all _87154).
Proof. exact (eq_refl (@all _87154)). Qed.
Lemma lem3347915 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) : (term184 _87154 t y x) = (term176 _87154 t y x).
Proof. exact (MK_COMB (@lem3347914 _87154) (@lem3347913 _87154 t y x)). Qed.
Lemma lem3347916 {_87154 : Type'} (s : type686 _87154) (x : _87154 -> Prop) : (term138 _87154 s x) = (term138 _87154 s x).
Proof. exact (eq_refl (term138 _87154 s x)). Qed.
Lemma lem3347917 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) : (term180 _87154 s t y x) = (term177 _87154 s t y x).
Proof. exact (MK_COMB (@lem3347916 _87154 s x) (@lem3347915 _87154 t y x)). Qed.
Lemma lem3347918 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3347919 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) : (term185 _87154 s t y x) = (term186 _87154 s t y x).
Proof. exact (MK_COMB (@lem3347918) (@lem3347917 _87154 s t y x)). Qed.
Lemma lem3347920 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) (x' : _87154) : (term182 _87154 t y x x') = (term173 _87154 t y x x').
Proof. exact (eq_refl (term182 _87154 t y x x')). Qed.
Lemma lem3347921 {_87154 : Type'} (s : type686 _87154) (x : _87154 -> Prop) : (term138 _87154 s x) = (term138 _87154 s x).
Proof. exact (eq_refl (term138 _87154 s x)). Qed.
Lemma lem3347922 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) (x' : _87154) : (term187 _87154 s t y x x') = (term188 _87154 s t y x x').
Proof. exact (MK_COMB (@lem3347921 _87154 s x) (@lem3347920 _87154 t y x x')). Qed.
Lemma lem3347923 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) : (term189 _87154 s t y x) = (term190 _87154 s t y x).
Proof. exact (fun_ext (fun x' : _87154 => @lem3347922 _87154 s t y x x')). Qed.
Lemma lem3347924 {_87154 : Type'} : (@all _87154) = (@all _87154).
Proof. exact (eq_refl (@all _87154)). Qed.
Lemma lem3347925 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) : (term181 _87154 s t y x) = (term191 _87154 s t y x).
Proof. exact (MK_COMB (@lem3347924 _87154) (@lem3347923 _87154 s t y x)). Qed.
Lemma lem3347926 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) : ((term180 _87154 s t y x) = (term181 _87154 s t y x)) = ((term177 _87154 s t y x) = (term191 _87154 s t y x)).
Proof. exact (MK_COMB (@lem3347919 _87154 s t y x) (@lem3347925 _87154 s t y x)). Qed.
Lemma lem3347927 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) : (term177 _87154 s t y x) = (term191 _87154 s t y x).
Proof. exact (EQ_MP (@lem3347926 _87154 s t y x) (@lem3347911 _87154 s t y x)). Qed.
Lemma lem3347928 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) : (term160 _87154 s t y x) = (term191 _87154 s t y x).
Proof. exact (TRANS (@lem3347907 _87154 s t y x) (@lem3347927 _87154 s t y x)). Qed.
Lemma lem3347929 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) : (term161 _87154 s t y) = (term192 _87154 s t y).
Proof. exact (fun_ext (fun x : _87154 -> Prop => @lem3347928 _87154 s t y x)). Qed.
Lemma lem3347930 {_87154 : Type'} : (@all (_87154 -> Prop)) = (@all (_87154 -> Prop)).
Proof. exact (eq_refl (@all (_87154 -> Prop))). Qed.
Lemma lem3347931 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) : (term162 _87154 s t y) = (term193 _87154 s t y).
Proof. exact (MK_COMB (@lem3347930 _87154) (@lem3347929 _87154 s t y)). Qed.
Lemma lem3347954 {_87154 : Type'} (t : type686 _87154) (s : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) (x' : _87154) : (term188 _87154 s t y x x') = (term194 _87154 t s y x x').
Proof. exact (@lem19490 (term155 _87154 t y x) (term137 _87154 s x) (term148 _87154 y x x')). Qed.
Lemma lem3347955 {_87154 : Type'} (t : type686 _87154) (s : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) : (term190 _87154 s t y x) = (term195 _87154 t s y x).
Proof. exact (fun_ext (fun x' : _87154 => @lem3347954 _87154 t s y x x')). Qed.
Lemma lem3347956 {_87154 : Type'} : (@all _87154) = (@all _87154).
Proof. exact (eq_refl (@all _87154)). Qed.
Lemma lem3347957 {_87154 : Type'} (t : type686 _87154) (s : type686 _87154) (y : type672 _87154) (x : _87154 -> Prop) : (term191 _87154 s t y x) = (term196 _87154 t s y x).
Proof. exact (MK_COMB (@lem3347956 _87154) (@lem3347955 _87154 t s y x)). Qed.
Lemma lem3347958 {_87154 : Type'} (t : type686 _87154) (s : type686 _87154) (y : type672 _87154) : (term192 _87154 s t y) = (term197 _87154 t s y).
Proof. exact (fun_ext (fun x : _87154 -> Prop => @lem3347957 _87154 t s y x)). Qed.
Lemma lem3347959 {_87154 : Type'} : (@all (_87154 -> Prop)) = (@all (_87154 -> Prop)).
Proof. exact (eq_refl (@all (_87154 -> Prop))). Qed.
Lemma lem3347960 {_87154 : Type'} (t : type686 _87154) (s : type686 _87154) (y : type672 _87154) : (term193 _87154 s t y) = (term198 _87154 t s y).
Proof. exact (MK_COMB (@lem3347959 _87154) (@lem3347958 _87154 t s y)). Qed.
Lemma lem3347961 {_87154 : Type'} (t : type686 _87154) (s : type686 _87154) (y : type672 _87154) : (term162 _87154 s t y) = (term198 _87154 t s y).
Proof. exact (TRANS (@lem3347931 _87154 s t y) (@lem3347960 _87154 t s y)). Qed.
Lemma lem3347962 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (h1 : term121 _87154 s t y) : term198 _87154 t s y.
Proof. exact (EQ_MP (@lem3347961 _87154 t s y) (@lem3347870 _87154 s t y h1)). Qed.
Lemma lem3347971 {_87154 : Type'} (_34905 : _87154 -> Prop) (t : type686 _87154) (x : _87154) (h1 : term69 _87154 t x) : term199 _87154 t x _34905.
Proof. exact (@lem3347885 _87154 t x h1 _34905). Qed.
Lemma lem3347972 {_87154 : Type'} (t : type686 _87154) (_34905 : _87154 -> Prop) (x : _87154) : (term199 _87154 t x _34905) = (term139 _87154 t _34905 x).
Proof. exact (eq_refl (term199 _87154 t x _34905)). Qed.
Lemma lem3347974 {_87154 : Type'} (_34906 : _87154 -> Prop) (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (h1 : term121 _87154 s t y) : term200 _87154 t s y _34906.
Proof. exact (@lem3347962 _87154 s t y h1 _34906). Qed.
Lemma lem3347975 {_87154 : Type'} (t : type686 _87154) (s : type686 _87154) (y : type672 _87154) (_34906 : _87154 -> Prop) : (term200 _87154 t s y _34906) = (term196 _87154 t s y _34906).
Proof. exact (eq_refl (term200 _87154 t s y _34906)). Qed.
Lemma lem3347976 {_87154 : Type'} (_34906 : _87154 -> Prop) (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (h1 : term121 _87154 s t y) : term196 _87154 t s y _34906.
Proof. exact (EQ_MP (@lem3347975 _87154 t s y _34906) (@lem3347974 _87154 _34906 s t y h1)). Qed.
Lemma lem3347977 {_87154 : Type'} (_34906 : _87154 -> Prop) (_34907 : _87154) (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (h1 : term121 _87154 s t y) : term201 _87154 t s y _34906 _34907.
Proof. exact (@lem3347976 _87154 _34906 s t y h1 _34907). Qed.
Lemma lem3347978 {_87154 : Type'} (t : type686 _87154) (s : type686 _87154) (y : type672 _87154) (_34906 : _87154 -> Prop) (_34907 : _87154) : (term201 _87154 t s y _34906 _34907) = (term194 _87154 t s y _34906 _34907).
Proof. exact (eq_refl (term201 _87154 t s y _34906 _34907)). Qed.
Lemma lem3347979 {_87154 : Type'} (_34906 : _87154 -> Prop) (_34907 : _87154) (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (h1 : term121 _87154 s t y) : term194 _87154 t s y _34906 _34907.
Proof. exact (EQ_MP (@lem3347978 _87154 t s y _34906 _34907) (@lem3347977 _87154 _34906 _34907 s t y h1)). Qed.
Lemma lem3347987 {_87154 : Type'} (_34905 : _87154 -> Prop) (t : type686 _87154) (x : _87154) (h1 : term69 _87154 t x) : term139 _87154 t _34905 x.
Proof. exact (EQ_MP (@lem3347972 _87154 t _34905 x) (@lem3347971 _87154 _34905 t x h1)). Qed.
Lemma lem3347997 {_87154 : Type'} (_34906 : _87154 -> Prop) (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (h1 : term121 _87154 s t y) : term202 _87154 s t y _34906.
Proof. exact (proj1 (@lem3347979 _87154 _34906 (@el _87154) s t y h1)). Qed.
Lemma lem3348007 {_87154 : Type'} (_34906 : _87154 -> Prop) (_34907 : _87154) (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (h1 : term121 _87154 s t y) : term203 _87154 s y _34906 _34907.
Proof. exact (proj2 (@lem3347979 _87154 _34906 _34907 s t y h1)). Qed.
Lemma lem3348009 {_87154 : Type'} (s : type686 _87154) (t' : _87154 -> Prop) (x : _87154) (h1 : term40 _87154 s t' x) : @I ((_87154 -> Prop) -> Prop) s t'.
Proof. exact (proj1 (@lem3347802 _87154 s t' x h1)). Qed.
Lemma lem3348010 {_87154 : Type'} (s : type686 _87154) (t' : _87154 -> Prop) (x : _87154) (h1 : term40 _87154 s t' x) : term204 _87154 s t'.
Proof. exact (fun h0 : term137 _87154 s t' => @lem3348009 _87154 s t' x h1). Qed.
Lemma lem3348012 (p : Prop) : (term205 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3348013 {_87154 : Type'} (s : type686 _87154) (t' : _87154 -> Prop) : (term204 _87154 s t') = (@I ((_87154 -> Prop) -> Prop) s t').
Proof. exact (@lem3348012 (@I ((_87154 -> Prop) -> Prop) s t')). Qed.
Lemma lem3348014 {_87154 : Type'} (s : type686 _87154) (t' : _87154 -> Prop) (x : _87154) (h1 : term40 _87154 s t' x) : @I ((_87154 -> Prop) -> Prop) s t'.
Proof. exact (EQ_MP (@lem3348013 _87154 s t') (@lem3348010 _87154 s t' x h1)). Qed.
Lemma lem3348020 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3348021 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (s : type686 _87154) (_34906 : _87154 -> Prop) : (term202 _87154 s t y _34906) = (term206 _87154 t y s _34906).
Proof. exact (@lem3348020 (term155 _87154 t y _34906) (term137 _87154 s _34906)). Qed.
Lemma lem3348027 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3348028 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (s : type686 _87154) (_34906 : _87154 -> Prop) : (term207 _87154 s t y _34906) = (term208 _87154 t y s _34906).
Proof. exact (MK_COMB (@lem3348027) (@lem3348021 _87154 t y s _34906)). Qed.
Lemma lem3348034 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (s : type686 _87154) (_34906 : _87154 -> Prop) : (term206 _87154 t y s _34906) = (term206 _87154 t y s _34906).
Proof. exact (eq_refl (term206 _87154 t y s _34906)). Qed.
Lemma lem3348035 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (s : type686 _87154) (_34906 : _87154 -> Prop) : ((term202 _87154 s t y _34906) = (term206 _87154 t y s _34906)) = ((term206 _87154 t y s _34906) = (term206 _87154 t y s _34906)).
Proof. exact (MK_COMB (@lem3348028 _87154 t y s _34906) (@lem3348034 _87154 t y s _34906)). Qed.
Lemma lem3348037 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3348038 (x : Prop) : (x = x) = True.
Proof. exact (@lem3348037 Prop x). Qed.
Lemma lem3348039 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (s : type686 _87154) (_34906 : _87154 -> Prop) : ((term206 _87154 t y s _34906) = (term206 _87154 t y s _34906)) = True.
Proof. exact (@lem3348038 (term206 _87154 t y s _34906)). Qed.
Lemma lem3348040 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (s : type686 _87154) (_34906 : _87154 -> Prop) : ((term202 _87154 s t y _34906) = (term206 _87154 t y s _34906)) = True.
Proof. exact (TRANS (@lem3348035 _87154 t y s _34906) (@lem3348039 _87154 t y s _34906)). Qed.
Lemma lem3348041 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (s : type686 _87154) (_34906 : _87154 -> Prop) : True = ((term202 _87154 s t y _34906) = (term206 _87154 t y s _34906)).
Proof. exact (SYM (@lem3348040 _87154 t y s _34906)). Qed.
Lemma lem3348042 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (s : type686 _87154) (_34906 : _87154 -> Prop) : (term202 _87154 s t y _34906) = (term206 _87154 t y s _34906).
Proof. exact (EQ_MP (@lem3348041 _87154 t y s _34906) (@lem0)). Qed.
Lemma lem3348043 {_87154 : Type'} (_34906 : _87154 -> Prop) (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (h1 : term121 _87154 s t y) : term206 _87154 t y s _34906.
Proof. exact (EQ_MP (@lem3348042 _87154 t y s _34906) (@lem3347997 _87154 _34906 s t y h1)). Qed.
Lemma lem3348045 (b : Prop) (a : Prop) : (a \/ b) = (term209 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3348046 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (_34906 : _87154 -> Prop) : (term206 _87154 t y s _34906) = (term210 _87154 s t y _34906).
Proof. exact (@lem3348045 (term137 _87154 s _34906) (term155 _87154 t y _34906)). Qed.
Lemma lem3348048 (a : Prop) : (term59 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3348049 {_87154 : Type'} (s : type686 _87154) (_34906 : _87154 -> Prop) : (term211 _87154 s _34906) = (@I ((_87154 -> Prop) -> Prop) s _34906).
Proof. exact (@lem3348048 (@I ((_87154 -> Prop) -> Prop) s _34906)). Qed.
Lemma lem3348050 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3348051 {_87154 : Type'} (s : type686 _87154) (_34906 : _87154 -> Prop) : (term212 _87154 s _34906) = (term213 _87154 s _34906).
Proof. exact (MK_COMB (@lem3348050) (@lem3348049 _87154 s _34906)). Qed.
Lemma lem3348052 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (_34906 : _87154 -> Prop) : (term155 _87154 t y _34906) = (term155 _87154 t y _34906).
Proof. exact (eq_refl (term155 _87154 t y _34906)). Qed.
Lemma lem3348053 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (_34906 : _87154 -> Prop) : (term210 _87154 s t y _34906) = (term214 _87154 s t y _34906).
Proof. exact (MK_COMB (@lem3348051 _87154 s _34906) (@lem3348052 _87154 t y _34906)). Qed.
Lemma lem3348054 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (_34906 : _87154 -> Prop) : (term206 _87154 t y s _34906) = (term214 _87154 s t y _34906).
Proof. exact (TRANS (@lem3348046 _87154 s t y _34906) (@lem3348053 _87154 s t y _34906)). Qed.
Lemma lem3348057 {_87154 : Type'} (_34906 : _87154 -> Prop) (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (h1 : term121 _87154 s t y) : term214 _87154 s t y _34906.
Proof. exact (EQ_MP (@lem3348054 _87154 s t y _34906) (@lem3348043 _87154 _34906 s t y h1)). Qed.
Lemma lem3348058 {_87154 : Type'} (_34906 : _87154 -> Prop) (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (h1 : term121 _87154 s t y) : term214 _87154 s t y _34906.
Proof. exact (@lem3348057 _87154 _34906 s t y h1). Qed.
Lemma lem3348059 {_87154 : Type'} (t' : _87154 -> Prop) (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (h1 : term121 _87154 s t y) : term214 _87154 s t y t'.
Proof. exact (@lem3348058 _87154 t' s t y h1). Qed.
Lemma lem3348062 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (s : type686 _87154) (t' : _87154 -> Prop) (x : _87154) (h1 : term121 _87154 s t y) (h2 : term40 _87154 s t' x) : term155 _87154 t y t'.
Proof. exact (@lem3348059 _87154 t' s t y h1 (@lem3348014 _87154 s t' x h2)). Qed.
Lemma lem3348063 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (s : type686 _87154) (t' : _87154 -> Prop) (x : _87154) (h1 : term121 _87154 s t y) (h2 : term40 _87154 s t' x) : term215 _87154 t y t'.
Proof. exact (fun h0 : term216 _87154 t y t' => @lem3348062 _87154 t y s t' x h1 h2). Qed.
Lemma lem3348065 (p : Prop) : (term205 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3348066 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (t' : _87154 -> Prop) : (term215 _87154 t y t') = (term155 _87154 t y t').
Proof. exact (@lem3348065 (term155 _87154 t y t')). Qed.
Lemma lem3348067 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (s : type686 _87154) (t' : _87154 -> Prop) (x : _87154) (h1 : term121 _87154 s t y) (h2 : term40 _87154 s t' x) : term155 _87154 t y t'.
Proof. exact (EQ_MP (@lem3348066 _87154 t y t') (@lem3348063 _87154 t y s t' x h1 h2)). Qed.
Lemma lem3348069 {_87154 : Type'} (s : type686 _87154) (t' : _87154 -> Prop) (x : _87154) (h1 : term40 _87154 s t' x) : @I ((_87154 -> Prop) -> Prop) s t'.
Proof. exact (proj1 (@lem3347802 _87154 s t' x h1)). Qed.
Lemma lem3348070 {_87154 : Type'} (s : type686 _87154) (t' : _87154 -> Prop) (x : _87154) (h1 : term40 _87154 s t' x) : term204 _87154 s t'.
Proof. exact (fun h0 : term137 _87154 s t' => @lem3348069 _87154 s t' x h1). Qed.
Lemma lem3348072 (p : Prop) : (term205 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3348073 {_87154 : Type'} (s : type686 _87154) (t' : _87154 -> Prop) : (term204 _87154 s t') = (@I ((_87154 -> Prop) -> Prop) s t').
Proof. exact (@lem3348072 (@I ((_87154 -> Prop) -> Prop) s t')). Qed.
Lemma lem3348074 {_87154 : Type'} (s : type686 _87154) (t' : _87154 -> Prop) (x : _87154) (h1 : term40 _87154 s t' x) : @I ((_87154 -> Prop) -> Prop) s t'.
Proof. exact (EQ_MP (@lem3348073 _87154 s t') (@lem3348070 _87154 s t' x h1)). Qed.
Lemma lem3348076 {_87154 : Type'} (s : type686 _87154) (t' : _87154 -> Prop) (x : _87154) (h1 : term40 _87154 s t' x) : @I (_87154 -> Prop) t' x.
Proof. exact (proj2 (@lem3347802 _87154 s t' x h1)). Qed.
Lemma lem3348077 {_87154 : Type'} (s : type686 _87154) (t' : _87154 -> Prop) (x : _87154) (h1 : term40 _87154 s t' x) : term217 _87154 t' x.
Proof. exact (fun h0 : term136 _87154 t' x => @lem3348076 _87154 s t' x h1). Qed.
Lemma lem3348079 (p : Prop) : (term205 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3348080 {_87154 : Type'} (t' : _87154 -> Prop) (x : _87154) : (term217 _87154 t' x) = (@I (_87154 -> Prop) t' x).
Proof. exact (@lem3348079 (@I (_87154 -> Prop) t' x)). Qed.
Lemma lem3348081 {_87154 : Type'} (s : type686 _87154) (t' : _87154 -> Prop) (x : _87154) (h1 : term40 _87154 s t' x) : @I (_87154 -> Prop) t' x.
Proof. exact (EQ_MP (@lem3348080 _87154 t' x) (@lem3348077 _87154 s t' x h1)). Qed.
Lemma lem3348087 (q : Prop) (p : Prop) (r : Prop) : (term218 p q r) = (term218 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3348088 {_87154 : Type'} (s : type686 _87154) (y : type672 _87154) (_34906 : _87154 -> Prop) (_34907 : _87154) : (term203 _87154 s y _34906 _34907) = (term219 _87154 s y _34906 _34907).
Proof. exact (@lem3348087 (term136 _87154 _34906 _34907) (term137 _87154 s _34906) (term144 _87154 y _34906 _34907)). Qed.
Lemma lem3348102 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3348103 {_87154 : Type'} (y : type672 _87154) (_34907 : _87154) (s : type686 _87154) (_34906 : _87154 -> Prop) : (term220 _87154 s y _34906 _34907) = (term221 _87154 y _34907 s _34906).
Proof. exact (@lem3348102 (term144 _87154 y _34906 _34907) (term137 _87154 s _34906)). Qed.
Lemma lem3348109 {_87154 : Type'} (_34906 : _87154 -> Prop) (_34907 : _87154) : (term146 _87154 _34906 _34907) = (term146 _87154 _34906 _34907).
Proof. exact (eq_refl (term146 _87154 _34906 _34907)). Qed.
Lemma lem3348110 {_87154 : Type'} (y : type672 _87154) (_34907 : _87154) (s : type686 _87154) (_34906 : _87154 -> Prop) : (term219 _87154 s y _34906 _34907) = (term222 _87154 y _34907 s _34906).
Proof. exact (MK_COMB (@lem3348109 _87154 _34906 _34907) (@lem3348103 _87154 y _34907 s _34906)). Qed.
Lemma lem3348114 (q : Prop) (p : Prop) (r : Prop) : (term218 p q r) = (term218 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3348115 {_87154 : Type'} (y : type672 _87154) (_34907 : _87154) (s : type686 _87154) (_34906 : _87154 -> Prop) : (term222 _87154 y _34907 s _34906) = (term223 _87154 y _34907 s _34906).
Proof. exact (@lem3348114 (term144 _87154 y _34906 _34907) (term136 _87154 _34906 _34907) (term137 _87154 s _34906)). Qed.
Lemma lem3348131 {_87154 : Type'} (y : type672 _87154) (_34907 : _87154) (s : type686 _87154) (_34906 : _87154 -> Prop) : (term219 _87154 s y _34906 _34907) = (term223 _87154 y _34907 s _34906).
Proof. exact (TRANS (@lem3348110 _87154 y _34907 s _34906) (@lem3348115 _87154 y _34907 s _34906)). Qed.
Lemma lem3348132 {_87154 : Type'} (y : type672 _87154) (_34907 : _87154) (s : type686 _87154) (_34906 : _87154 -> Prop) : (term203 _87154 s y _34906 _34907) = (term223 _87154 y _34907 s _34906).
Proof. exact (TRANS (@lem3348088 _87154 s y _34906 _34907) (@lem3348131 _87154 y _34907 s _34906)). Qed.
Lemma lem3348133 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3348134 {_87154 : Type'} (y : type672 _87154) (_34907 : _87154) (s : type686 _87154) (_34906 : _87154 -> Prop) : (term224 _87154 s y _34906 _34907) = (term225 _87154 y _34907 s _34906).
Proof. exact (MK_COMB (@lem3348133) (@lem3348132 _87154 y _34907 s _34906)). Qed.
Lemma lem3348148 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3348149 {_87154 : Type'} (_34907 : _87154) (s : type686 _87154) (_34906 : _87154 -> Prop) : (term139 _87154 s _34906 _34907) = (term226 _87154 _34907 s _34906).
Proof. exact (@lem3348148 (term136 _87154 _34906 _34907) (term137 _87154 s _34906)). Qed.
Lemma lem3348155 {_87154 : Type'} (y : type672 _87154) (_34906 : _87154 -> Prop) (_34907 : _87154) : (term227 _87154 y _34906 _34907) = (term227 _87154 y _34906 _34907).
Proof. exact (eq_refl (term227 _87154 y _34906 _34907)). Qed.
Lemma lem3348156 {_87154 : Type'} (y : type672 _87154) (_34907 : _87154) (s : type686 _87154) (_34906 : _87154 -> Prop) : (term228 _87154 y s _34906 _34907) = (term223 _87154 y _34907 s _34906).
Proof. exact (MK_COMB (@lem3348155 _87154 y _34906 _34907) (@lem3348149 _87154 _34907 s _34906)). Qed.
Lemma lem3348167 {_87154 : Type'} (y : type672 _87154) (_34907 : _87154) (s : type686 _87154) (_34906 : _87154 -> Prop) : ((term203 _87154 s y _34906 _34907) = (term228 _87154 y s _34906 _34907)) = ((term223 _87154 y _34907 s _34906) = (term223 _87154 y _34907 s _34906)).
Proof. exact (MK_COMB (@lem3348134 _87154 y _34907 s _34906) (@lem3348156 _87154 y _34907 s _34906)). Qed.
Lemma lem3348169 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3348170 (x : Prop) : (x = x) = True.
Proof. exact (@lem3348169 Prop x). Qed.
Lemma lem3348171 {_87154 : Type'} (y : type672 _87154) (_34907 : _87154) (s : type686 _87154) (_34906 : _87154 -> Prop) : ((term223 _87154 y _34907 s _34906) = (term223 _87154 y _34907 s _34906)) = True.
Proof. exact (@lem3348170 (term223 _87154 y _34907 s _34906)). Qed.
Lemma lem3348172 {_87154 : Type'} (y : type672 _87154) (s : type686 _87154) (_34906 : _87154 -> Prop) (_34907 : _87154) : ((term203 _87154 s y _34906 _34907) = (term228 _87154 y s _34906 _34907)) = True.
Proof. exact (TRANS (@lem3348167 _87154 y _34907 s _34906) (@lem3348171 _87154 y _34907 s _34906)). Qed.
Lemma lem3348173 {_87154 : Type'} (y : type672 _87154) (s : type686 _87154) (_34906 : _87154 -> Prop) (_34907 : _87154) : True = ((term203 _87154 s y _34906 _34907) = (term228 _87154 y s _34906 _34907)).
Proof. exact (SYM (@lem3348172 _87154 y s _34906 _34907)). Qed.
Lemma lem3348174 {_87154 : Type'} (y : type672 _87154) (s : type686 _87154) (_34906 : _87154 -> Prop) (_34907 : _87154) : (term203 _87154 s y _34906 _34907) = (term228 _87154 y s _34906 _34907).
Proof. exact (EQ_MP (@lem3348173 _87154 y s _34906 _34907) (@lem0)). Qed.
Lemma lem3348175 {_87154 : Type'} (_34906 : _87154 -> Prop) (_34907 : _87154) (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (h1 : term121 _87154 s t y) : term228 _87154 y s _34906 _34907.
Proof. exact (EQ_MP (@lem3348174 _87154 y s _34906 _34907) (@lem3348007 _87154 _34906 _34907 s t y h1)). Qed.
Lemma lem3348177 (b : Prop) (a : Prop) : (a \/ b) = (term209 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3348178 {_87154 : Type'} (s : type686 _87154) (y : type672 _87154) (_34906 : _87154 -> Prop) (_34907 : _87154) : (term228 _87154 y s _34906 _34907) = (term229 _87154 s y _34906 _34907).
Proof. exact (@lem3348177 (term139 _87154 s _34906 _34907) (term144 _87154 y _34906 _34907)). Qed.
Lemma lem3348180 (a : Prop) (b : Prop) : (term230 a b) = (term231 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3348181 {_87154 : Type'} (s : type686 _87154) (_34906 : _87154 -> Prop) (_34907 : _87154) : (term232 _87154 s _34906 _34907) = (term233 _87154 s _34906 _34907).
Proof. exact (@lem3348180 (term137 _87154 s _34906) (term136 _87154 _34906 _34907)). Qed.
Lemma lem3348183 (a : Prop) : (term59 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3348184 {_87154 : Type'} (s : type686 _87154) (_34906 : _87154 -> Prop) : (term211 _87154 s _34906) = (@I ((_87154 -> Prop) -> Prop) s _34906).
Proof. exact (@lem3348183 (@I ((_87154 -> Prop) -> Prop) s _34906)). Qed.
Lemma lem3348185 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3348186 {_87154 : Type'} (s : type686 _87154) (_34906 : _87154 -> Prop) : (term234 _87154 s _34906) = (term142 _87154 s _34906).
Proof. exact (MK_COMB (@lem3348185) (@lem3348184 _87154 s _34906)). Qed.
Lemma lem3348188 (a : Prop) : (term59 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3348189 {_87154 : Type'} (_34906 : _87154 -> Prop) (_34907 : _87154) : (term235 _87154 _34906 _34907) = (@I (_87154 -> Prop) _34906 _34907).
Proof. exact (@lem3348188 (@I (_87154 -> Prop) _34906 _34907)). Qed.
Lemma lem3348190 {_87154 : Type'} (s : type686 _87154) (_34906 : _87154 -> Prop) (_34907 : _87154) : (term233 _87154 s _34906 _34907) = (term143 _87154 s _34906 _34907).
Proof. exact (MK_COMB (@lem3348186 _87154 s _34906) (@lem3348189 _87154 _34906 _34907)). Qed.
Lemma lem3348191 {_87154 : Type'} (s : type686 _87154) (_34906 : _87154 -> Prop) (_34907 : _87154) : (term232 _87154 s _34906 _34907) = (term143 _87154 s _34906 _34907).
Proof. exact (TRANS (@lem3348181 _87154 s _34906 _34907) (@lem3348190 _87154 s _34906 _34907)). Qed.
Lemma lem3348192 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3348193 {_87154 : Type'} (s : type686 _87154) (_34906 : _87154 -> Prop) (_34907 : _87154) : (term236 _87154 s _34906 _34907) = (term237 _87154 s _34906 _34907).
Proof. exact (MK_COMB (@lem3348192) (@lem3348191 _87154 s _34906 _34907)). Qed.
Lemma lem3348194 {_87154 : Type'} (y : type672 _87154) (_34906 : _87154 -> Prop) (_34907 : _87154) : (term144 _87154 y _34906 _34907) = (term144 _87154 y _34906 _34907).
Proof. exact (eq_refl (term144 _87154 y _34906 _34907)). Qed.
Lemma lem3348195 {_87154 : Type'} (s : type686 _87154) (y : type672 _87154) (_34906 : _87154 -> Prop) (_34907 : _87154) : (term229 _87154 s y _34906 _34907) = (term238 _87154 s y _34906 _34907).
Proof. exact (MK_COMB (@lem3348193 _87154 s _34906 _34907) (@lem3348194 _87154 y _34906 _34907)). Qed.
Lemma lem3348196 {_87154 : Type'} (s : type686 _87154) (y : type672 _87154) (_34906 : _87154 -> Prop) (_34907 : _87154) : (term228 _87154 y s _34906 _34907) = (term238 _87154 s y _34906 _34907).
Proof. exact (TRANS (@lem3348178 _87154 s y _34906 _34907) (@lem3348195 _87154 s y _34906 _34907)). Qed.
Lemma lem3348198 {_87154 : Type'} (s : type686 _87154) (t' : _87154 -> Prop) (x : _87154) (h1 : term40 _87154 s t' x) : term143 _87154 s t' x.
Proof. exact (conj (@lem3348074 _87154 s t' x h1) (@lem3348081 _87154 s t' x h1)). Qed.
Lemma lem3348200 {_87154 : Type'} (_34906 : _87154 -> Prop) (_34907 : _87154) (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (h1 : term121 _87154 s t y) : term238 _87154 s y _34906 _34907.
Proof. exact (EQ_MP (@lem3348196 _87154 s y _34906 _34907) (@lem3348175 _87154 _34906 _34907 s t y h1)). Qed.
Lemma lem3348201 {_87154 : Type'} (_34906 : _87154 -> Prop) (_34907 : _87154) (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (h1 : term121 _87154 s t y) : term238 _87154 s y _34906 _34907.
Proof. exact (@lem3348200 _87154 _34906 _34907 s t y h1). Qed.
Lemma lem3348202 {_87154 : Type'} (t' : _87154 -> Prop) (x : _87154) (s : type686 _87154) (t : type686 _87154) (y : type672 _87154) (h1 : term121 _87154 s t y) : term238 _87154 s y t' x.
Proof. exact (@lem3348201 _87154 t' x s t y h1). Qed.
Lemma lem3348205 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (s : type686 _87154) (t' : _87154 -> Prop) (x : _87154) (h1 : term121 _87154 s t y) (h2 : term40 _87154 s t' x) : term144 _87154 y t' x.
Proof. exact (@lem3348202 _87154 t' x s t y h1 (@lem3348198 _87154 s t' x h2)). Qed.
Lemma lem3348206 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (s : type686 _87154) (t' : _87154 -> Prop) (x : _87154) (h1 : term121 _87154 s t y) (h2 : term40 _87154 s t' x) : term239 _87154 y t' x.
Proof. exact (fun h0 : term240 _87154 y t' x => @lem3348205 _87154 t y s t' x h1 h2). Qed.
Lemma lem3348208 (p : Prop) : (term205 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3348209 {_87154 : Type'} (y : type672 _87154) (t' : _87154 -> Prop) (x : _87154) : (term239 _87154 y t' x) = (term144 _87154 y t' x).
Proof. exact (@lem3348208 (term144 _87154 y t' x)). Qed.
Lemma lem3348210 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (s : type686 _87154) (t' : _87154 -> Prop) (x : _87154) (h1 : term121 _87154 s t y) (h2 : term40 _87154 s t' x) : term144 _87154 y t' x.
Proof. exact (EQ_MP (@lem3348209 _87154 y t' x) (@lem3348206 _87154 t y s t' x h1 h2)). Qed.
Lemma lem3348212 (a : Prop) (b : Prop) : (term241 a b) = (term242 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3348213 {_87154 : Type'} (t : type686 _87154) (_34905 : _87154 -> Prop) (x : _87154) : (term139 _87154 t _34905 x) = (term243 _87154 t _34905 x).
Proof. exact (@lem3348212 (@I ((_87154 -> Prop) -> Prop) t _34905) (@I (_87154 -> Prop) _34905 x)). Qed.
Lemma lem3348215 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3348216 {_87154 : Type'} (t : type686 _87154) (_34905 : _87154 -> Prop) (x : _87154) : (term243 _87154 t _34905 x) = (term244 _87154 t _34905 x).
Proof. exact (@lem3348215 (term143 _87154 t _34905 x)). Qed.
Lemma lem3348217 {_87154 : Type'} (t : type686 _87154) (_34905 : _87154 -> Prop) (x : _87154) : (term139 _87154 t _34905 x) = (term244 _87154 t _34905 x).
Proof. exact (TRANS (@lem3348213 _87154 t _34905 x) (@lem3348216 _87154 t _34905 x)). Qed.
Lemma lem3348219 {_87154 : Type'} (t : type686 _87154) (y : type672 _87154) (s : type686 _87154) (t' : _87154 -> Prop) (x : _87154) (h1 : term121 _87154 s t y) (h2 : term40 _87154 s t' x) : term245 _87154 t y t' x.
Proof. exact (conj (@lem3348067 _87154 t y s t' x h1 h2) (@lem3348210 _87154 t y s t' x h1 h2)). Qed.
Lemma lem3348221 {_87154 : Type'} (_34905 : _87154 -> Prop) (t : type686 _87154) (x : _87154) (h1 : term69 _87154 t x) : term244 _87154 t _34905 x.
Proof. exact (EQ_MP (@lem3348217 _87154 t _34905 x) (@lem3347987 _87154 _34905 t x h1)). Qed.
Lemma lem3348222 {_87154 : Type'} (_34905 : _87154 -> Prop) (t : type686 _87154) (x : _87154) (h1 : term69 _87154 t x) : term244 _87154 t _34905 x.
Proof. exact (@lem3348221 _87154 _34905 t x h1). Qed.
Lemma lem3348223 {_87154 : Type'} (y : type672 _87154) (t' : _87154 -> Prop) (t : type686 _87154) (x : _87154) (h1 : term69 _87154 t x) : term246 _87154 t y t' x.
Proof. exact (@lem3348222 _87154 (@I ((_87154 -> Prop) -> _87154 -> Prop) y t') t x h1). Qed.
Lemma lem3348226 {_87154 : Type'} (y : type672 _87154) (t : type686 _87154) (s : type686 _87154) (t' : _87154 -> Prop) (x : _87154) (h1 : term121 _87154 s t y) (h2 : term69 _87154 t x) (h3 : term40 _87154 s t' x) : False.
Proof. exact (@lem3348223 _87154 y t' t x h2 (@lem3348219 _87154 t y s t' x h1 h3)). Qed.
Lemma lem3348227 {_87154 : Type'} (y : type672 _87154) (t : type686 _87154) (s : type686 _87154) (t' : _87154 -> Prop) (x : _87154) (h1 : term121 _87154 s t y) (h2 : term69 _87154 t x) (h3 : term40 _87154 s t' x) : term247.
Proof. exact (fun h0 : ~ False => @lem3348226 _87154 y t s t' x h1 h2 h3). Qed.
Lemma lem3348229 (p : Prop) : (term205 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3348230 : term247 = False.
Proof. exact (@lem3348229 False). Qed.
Lemma lem3348231 {_87154 : Type'} (y : type672 _87154) (t : type686 _87154) (s : type686 _87154) (t' : _87154 -> Prop) (x : _87154) (h1 : term121 _87154 s t y) (h2 : term69 _87154 t x) (h3 : term40 _87154 s t' x) : False.
Proof. exact (EQ_MP (@lem3348230) (@lem3348227 _87154 y t s t' x h1 h2 h3)). Qed.
Lemma lem3348232 {_87154 : Type'} (t : type686 _87154) (s : type686 _87154) (t' : _87154 -> Prop) (x : _87154) (h1 : term35 _87154 s t) (h2 : term69 _87154 t x) (h3 : term40 _87154 s t' x) : False.
Proof. exact (ex_elim (@lem3347642 _87154 s t h1) (fun y : type672 _87154 => fun h0 : term123 _87154 s t y => @lem3348231 _87154 y t s t' x h0 h2 h3)). Qed.
Lemma lem3348233 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (x : _87154) (h1 : term35 _87154 s t) (h2 : term43 _87154 s x) (h3 : term69 _87154 t x) : False.
Proof. exact (ex_elim (@lem3347683 _87154 s x h2) (fun t' : _87154 -> Prop => fun h0 : term42 _87154 s x t' => @lem3348232 _87154 t s t' x h1 h3 h0)). Qed.
Lemma lem3348234 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (x : _87154) (h1 : term35 _87154 s t) (h2 : term43 _87154 s x) (h3 : term69 _87154 t x) : (term43 _87154 s x) = False.
Proof. exact (prop_ext (fun h4 : term43 _87154 s x => @lem3348233 _87154 s t x h1 h2 h3) (fun h4 : False => @lem3347683 _87154 s x h2)). Qed.
Lemma lem3348235 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (x : _87154) (h1 : term35 _87154 s t) (h2 : term43 _87154 s x) (h3 : term69 _87154 t x) : False.
Proof. exact (EQ_MP (@lem3348234 _87154 s t x h1 h2 h3) (@lem3347683 _87154 s x h2)). Qed.
Lemma lem3348236 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (x : _87154) (h1 : term35 _87154 s t) (h2 : term43 _87154 s x) (h3 : term69 _87154 t x) : (term69 _87154 t x) = False.
Proof. exact (prop_ext (fun h4 : term69 _87154 t x => @lem3348235 _87154 s t x h1 h2 h3) (fun h4 : False => @lem3347450 _87154 t x h3)). Qed.
Lemma lem3348237 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (x : _87154) (h1 : term35 _87154 s t) (h2 : term43 _87154 s x) (h3 : term69 _87154 t x) : False.
Proof. exact (EQ_MP (@lem3348236 _87154 s t x h1 h2 h3) (@lem3347450 _87154 t x h3)). Qed.
Lemma lem3348238 {_87154 : Type'} (t : type686 _87154) (s : type686 _87154) (x : _87154) (h1 : term35 _87154 s t) (h2 : term43 _87154 s x) : term68 _87154 t x.
Proof. exact (fun h0 : term69 _87154 t x => @lem3348237 _87154 s t x h1 h2 h0). Qed.
Lemma lem3348239 {_87154 : Type'} (t : type686 _87154) (s : type686 _87154) (x : _87154) (h1 : term35 _87154 s t) (h2 : term43 _87154 s x) : term43 _87154 t x.
Proof. exact (EQ_MP (@lem3347449 _87154 t x) (@lem3348238 _87154 t s x h1 h2)). Qed.
Lemma lem3348240 {_87154 : Type'} (x : _87154) (s : type686 _87154) (t : type686 _87154) (h1 : term35 _87154 s t) : term47 _87154 s t x.
Proof. exact (fun h0 : term43 _87154 s x => @lem3348239 _87154 t s x h1 h0). Qed.
Lemma lem3348245 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (h1 : term35 _87154 s t) : term50 _87154 s t.
Proof. exact (fun x : _87154 => @lem3348240 _87154 x s t h1). Qed.
Lemma lem3348246 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : term51 _87154 s t.
Proof. exact (fun h0 : term35 _87154 s t => @lem3348245 _87154 s t h0). Qed.
Lemma lem3348251 {_87154 : Type'} (t : type686 _87154) : term63 _87154 t.
Proof. exact (fun s : type686 _87154 => @lem3348246 _87154 s t). Qed.
Lemma lem3348256 {_87154 : Type'} : term67 _87154.
Proof. exact (fun t : type686 _87154 => @lem3348251 _87154 t). Qed.
Lemma lem3348257 {_87154 : Type'} : term66 _87154.
Proof. exact (EQ_MP (@lem3347443 _87154) (@lem3348256 _87154)). Qed.
Lemma lem3348258 {_87154 : Type'} (t : type686 _87154) : term248 _87154 t.
Proof. exact (@lem3348257 _87154 t). Qed.
Lemma lem3348259 {_87154 : Type'} (t : type686 _87154) : (term248 _87154 t) = (term62 _87154 t).
Proof. exact (eq_refl (term248 _87154 t)). Qed.
Lemma lem3348260 {_87154 : Type'} (t : type686 _87154) : term62 _87154 t.
Proof. exact (EQ_MP (@lem3348259 _87154 t) (@lem3348258 _87154 t)). Qed.
Lemma lem3348261 {_87154 : Type'} (t : type686 _87154) (s : type686 _87154) : term249 _87154 t s.
Proof. exact (@lem3348260 _87154 t s). Qed.
Lemma lem3348262 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : (term249 _87154 t s) = (term53 _87154 s t).
Proof. exact (eq_refl (term249 _87154 t s)). Qed.
Lemma lem3348263 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : term53 _87154 s t.
Proof. exact (EQ_MP (@lem3348262 _87154 s t) (@lem3348261 _87154 t s)). Qed.
Lemma lem3348265 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : term53 _87154 s t.
Proof. exact (@lem3347181 _87154 s t (@lem3348263 _87154 s t)). Qed.
Lemma lem3348266 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (h1 : term54 _87154 s t) : False.
Proof. exact (@lem3348265 _87154 s t (@lem3347165 _87154 s t h1)). Qed.
Lemma lem3348267 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (h1 : term54 _87154 s t) : (term54 _87154 s t) = False.
Proof. exact (prop_ext (fun h2 : term54 _87154 s t => @lem3348266 _87154 s t h1) (fun h2 : False => @lem3347165 _87154 s t h1)). Qed.
Lemma lem3348268 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (h1 : term54 _87154 s t) : False.
Proof. exact (EQ_MP (@lem3348267 _87154 s t h1) (@lem3347165 _87154 s t h1)). Qed.
Lemma lem3348269 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : term53 _87154 s t.
Proof. exact (fun h0 : term54 _87154 s t => @lem3348268 _87154 s t h0). Qed.
Lemma lem3348270 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : term51 _87154 s t.
Proof. exact (EQ_MP (@lem3347164 _87154 s t) (@lem3348269 _87154 s t)). Qed.
Lemma lem3348271 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : term20 _87154 s t.
Proof. exact (EQ_MP (@lem3347160 _87154 s t) (@lem3348270 _87154 s t)). Qed.
Lemma lem3348272 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : term19 _87154 s t.
Proof. exact (EQ_MP (@lem3347003 _87154 s t) (@lem3348271 _87154 s t)). Qed.
