Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUBSET_IMAGE_INJ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import IMAGE_SUBSET_spec.
Require Import SURJECTIVE_ON_RIGHT_INVERSE_spec.
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
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
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
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm32_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm69_spec.
Lemma lem3632104 {_91307 _91308 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91308) : term0 _91307 _91308 s f.
Proof. exact (@lem3562737 _91307 _91308 s f). Qed.
Lemma lem3632105 {_91307 _91308 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91308) : (term0 _91307 _91308 s f) = (term1 _91307 _91308 s f).
Proof. exact (eq_refl (term0 _91307 _91308 s f)). Qed.
Lemma lem3632106 {_91307 _91308 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91308) : term1 _91307 _91308 s f.
Proof. exact (EQ_MP (@lem3632105 _91307 _91308 s f) (@lem3632104 _91307 _91308 s f)). Qed.
Lemma lem3632107 {_91307 _91308 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91308) (t : _91308 -> Prop) : term2 _91307 _91308 s f t.
Proof. exact (@lem3632106 _91307 _91308 s f t). Qed.
Lemma lem3632108 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : (term2 _91307 _91308 s f t) = ((term3 _91307 _91308 t s f) = (term4 _91307 _91308 t s f)).
Proof. exact (eq_refl (term2 _91307 _91308 s f t)). Qed.
Lemma lem3632123 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term5 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3632124 {_93229 : Type'} (s : _93229 -> Prop) (t : _93229 -> Prop) : (@SUBSET _93229 s t) = (term5 _93229 s t).
Proof. exact (@lem3632123 _93229 s t). Qed.
Lemma lem3632125 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term6 _93229 _93232 s f t) = (term7 _93229 _93232 s f t).
Proof. exact (@lem3632124 _93229 s (@IMAGE _93232 _93229 f t)). Qed.
Lemma lem3632132 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3632133 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term8 _93229 _93232 s f t) = (term9 _93229 _93232 s f t).
Proof. exact (MK_COMB (@lem3632132) (@lem3632125 _93229 _93232 s f t)). Qed.
Lemma lem3632150 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) : (term10 _93229 _93232 s t f) = (term10 _93229 _93232 s t f).
Proof. exact (eq_refl (term10 _93229 _93232 s t f)). Qed.
Lemma lem3632151 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) : (term11 _93229 _93232 s t f) = (term12 _93229 _93232 s t f).
Proof. exact (MK_COMB (@lem3632133 _93229 _93232 s f t) (@lem3632150 _93229 _93232 s t f)). Qed.
Lemma lem3632154 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) : (term12 _93229 _93232 s t f) = (term11 _93229 _93232 s t f).
Proof. exact (SYM (@lem3632151 _93229 _93232 s t f)). Qed.
Lemma lem3632164 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3632165 {_93229 : Type'} (P : _93229 -> Prop) (x : _93229) : (@IN _93229 x P) = (P x).
Proof. exact (@lem3632164 _93229 P x). Qed.
Lemma lem3632166 {_93229 : Type'} (s : _93229 -> Prop) (x : _93229) : (@IN _93229 x s) = (s x).
Proof. exact (@lem3632165 _93229 s x). Qed.
Lemma lem3632167 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3632168 {_93229 : Type'} (s : _93229 -> Prop) (x : _93229) : (term13 _93229 x s) = (term14 _93229 s x).
Proof. exact (MK_COMB (@lem3632167) (@lem3632166 _93229 s x)). Qed.
Lemma lem3632170 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term16 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3632171 {_93229 _93232 : Type'} (y : _93229) (f : _93232 -> _93229) (s : _93232 -> Prop) : (term17 _93229 _93232 y f s) = (term18 _93229 _93232 y f s).
Proof. exact (@lem3632170 _93232 _93229 y f s). Qed.
Lemma lem3632172 {_93229 _93232 : Type'} (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term17 _93229 _93232 x f t) = (term18 _93229 _93232 x f t).
Proof. exact (@lem3632171 _93229 _93232 x f t). Qed.
Lemma lem3632182 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3632183 {_93232 : Type'} (P : _93232 -> Prop) (x : _93232) : (@IN _93232 x P) = (P x).
Proof. exact (@lem3632182 _93232 P x). Qed.
Lemma lem3632184 {_93232 : Type'} (t : _93232 -> Prop) (x : _93232) : (@IN _93232 x t) = (t x).
Proof. exact (@lem3632183 _93232 t x). Qed.
Lemma lem3632185 {_93229 _93232 : Type'} (x : _93229) (f : _93232 -> _93229) (x' : _93232) : (term19 _93229 _93232 x f x') = (term19 _93229 _93232 x f x').
Proof. exact (eq_refl (term19 _93229 _93232 x f x')). Qed.
Lemma lem3632186 {_93229 _93232 : Type'} (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93232) : (term20 _93229 _93232 x f x' t) = (term21 _93229 _93232 x f t x').
Proof. exact (MK_COMB (@lem3632185 _93229 _93232 x f x') (@lem3632184 _93232 t x')). Qed.
Lemma lem3632189 {_93229 _93232 : Type'} (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term22 _93229 _93232 x f t) = (term23 _93229 _93232 x f t).
Proof. exact (fun_ext (fun x' : _93232 => @lem3632186 _93229 _93232 x f t x')). Qed.
Lemma lem3632190 {_93232 : Type'} : (@ex _93232) = (@ex _93232).
Proof. exact (eq_refl (@ex _93232)). Qed.
Lemma lem3632191 {_93229 _93232 : Type'} (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term18 _93229 _93232 x f t) = (term24 _93229 _93232 x f t).
Proof. exact (MK_COMB (@lem3632190 _93232) (@lem3632189 _93229 _93232 x f t)). Qed.
Lemma lem3632196 {_93229 _93232 : Type'} (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term17 _93229 _93232 x f t) = (term24 _93229 _93232 x f t).
Proof. exact (TRANS (@lem3632172 _93229 _93232 x f t) (@lem3632191 _93229 _93232 x f t)). Qed.
Lemma lem3632197 {_93229 _93232 : Type'} (s : _93229 -> Prop) (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term25 _93229 _93232 s x f t) = (term26 _93229 _93232 s x f t).
Proof. exact (MK_COMB (@lem3632168 _93229 s x) (@lem3632196 _93229 _93232 x f t)). Qed.
Lemma lem3632200 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term27 _93229 _93232 s f t) = (term28 _93229 _93232 s f t).
Proof. exact (fun_ext (fun x : _93229 => @lem3632197 _93229 _93232 s x f t)). Qed.
Lemma lem3632201 {_93229 : Type'} : (@all _93229) = (@all _93229).
Proof. exact (eq_refl (@all _93229)). Qed.
Lemma lem3632202 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term7 _93229 _93232 s f t) = (term29 _93229 _93232 s f t).
Proof. exact (MK_COMB (@lem3632201 _93229) (@lem3632200 _93229 _93232 s f t)). Qed.
Lemma lem3632207 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3632208 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term9 _93229 _93232 s f t) = (term30 _93229 _93232 s f t).
Proof. exact (MK_COMB (@lem3632207) (@lem3632202 _93229 _93232 s f t)). Qed.
Lemma lem3632216 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3632217 {_93229 : Type'} (P : _93229 -> Prop) (x : _93229) : (@IN _93229 x P) = (P x).
Proof. exact (@lem3632216 _93229 P x). Qed.
Lemma lem3632218 {_93229 : Type'} (s : _93229 -> Prop) (x : _93229) : (@IN _93229 x s) = (s x).
Proof. exact (@lem3632217 _93229 s x). Qed.
Lemma lem3632219 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3632220 {_93229 : Type'} (s : _93229 -> Prop) (x : _93229) : (term13 _93229 x s) = (term14 _93229 s x).
Proof. exact (MK_COMB (@lem3632219) (@lem3632218 _93229 s x)). Qed.
Lemma lem3632228 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3632229 {_93232 : Type'} (P : _93232 -> Prop) (x : _93232) : (@IN _93232 x P) = (P x).
Proof. exact (@lem3632228 _93232 P x). Qed.
Lemma lem3632230 {_93232 : Type'} (t : _93232 -> Prop) (y : _93232) : (@IN _93232 y t) = (t y).
Proof. exact (@lem3632229 _93232 t y). Qed.
Lemma lem3632231 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3632232 {_93232 : Type'} (t : _93232 -> Prop) (y : _93232) : (term31 _93232 y t) = (term32 _93232 t y).
Proof. exact (MK_COMB (@lem3632231) (@lem3632230 _93232 t y)). Qed.
Lemma lem3632235 {_93229 _93232 : Type'} (f : _93232 -> _93229) (y : _93232) (x : _93229) : ((f y) = x) = ((f y) = x).
Proof. exact (eq_refl ((f y) = x)). Qed.
Lemma lem3632236 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (y : _93232) (x : _93229) : (term33 _93229 _93232 t f y x) = (term34 _93229 _93232 t f y x).
Proof. exact (MK_COMB (@lem3632232 _93232 t y) (@lem3632235 _93229 _93232 f y x)). Qed.
Lemma lem3632239 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (x : _93229) : (term35 _93229 _93232 t f x) = (term36 _93229 _93232 t f x).
Proof. exact (fun_ext (fun y : _93232 => @lem3632236 _93229 _93232 t f y x)). Qed.
Lemma lem3632240 {_93232 : Type'} : (@ex _93232) = (@ex _93232).
Proof. exact (eq_refl (@ex _93232)). Qed.
Lemma lem3632241 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (x : _93229) : (term37 _93229 _93232 t f x) = (term38 _93229 _93232 t f x).
Proof. exact (MK_COMB (@lem3632240 _93232) (@lem3632239 _93229 _93232 t f x)). Qed.
Lemma lem3632246 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) (x : _93229) : (term39 _93229 _93232 s t f x) = (term40 _93229 _93232 s t f x).
Proof. exact (MK_COMB (@lem3632220 _93229 s x) (@lem3632241 _93229 _93232 t f x)). Qed.
Lemma lem3632249 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) : (term41 _93229 _93232 s t f) = (term42 _93229 _93232 s t f).
Proof. exact (fun_ext (fun x : _93229 => @lem3632246 _93229 _93232 s t f x)). Qed.
Lemma lem3632250 {_93229 : Type'} : (@all _93229) = (@all _93229).
Proof. exact (eq_refl (@all _93229)). Qed.
Lemma lem3632251 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) : (term10 _93229 _93232 s t f) = (term43 _93229 _93232 s t f).
Proof. exact (MK_COMB (@lem3632250 _93229) (@lem3632249 _93229 _93232 s t f)). Qed.
Lemma lem3632256 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) : (term12 _93229 _93232 s t f) = (term44 _93229 _93232 s t f).
Proof. exact (MK_COMB (@lem3632208 _93229 _93232 s f t) (@lem3632251 _93229 _93232 s t f)). Qed.
Lemma lem3632259 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) : (term44 _93229 _93232 s t f) = (term12 _93229 _93232 s t f).
Proof. exact (SYM (@lem3632256 _93229 _93232 s t f)). Qed.
Lemma lem3632261 (p : Prop) : p = (term45 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3632262 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) : (term44 _93229 _93232 s t f) = (term46 _93229 _93232 s t f).
Proof. exact (@lem3632261 (term44 _93229 _93232 s t f)). Qed.
Lemma lem3632263 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) : (term46 _93229 _93232 s t f) = (term44 _93229 _93232 s t f).
Proof. exact (SYM (@lem3632262 _93229 _93232 s t f)). Qed.
Lemma lem3632264 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) (h1 : term47 _93229 _93232 s t f) : term47 _93229 _93232 s t f.
Proof. exact (h1). Qed.
Lemma lem3632267 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) (h1 : term46 _93229 _93232 s t f) : term46 _93229 _93232 s t f.
Proof. exact (h1). Qed.
Lemma lem3632268 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) : term48 _93229 _93232 s t f.
Proof. exact (fun h0 : term46 _93229 _93232 s t f => @lem3632267 _93229 _93232 s t f h0). Qed.
Lemma lem3632269 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) (h1 : term48 _93229 _93232 s t f) : term48 _93229 _93232 s t f.
Proof. exact (h1). Qed.
Lemma lem3632270 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) (h1 : term46 _93229 _93232 s t f) : term46 _93229 _93232 s t f.
Proof. exact (h1). Qed.
Lemma lem3632271 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) (h1 : term46 _93229 _93232 s t f) (h2 : term48 _93229 _93232 s t f) : term46 _93229 _93232 s t f.
Proof. exact (@lem3632269 _93229 _93232 s t f h2 (@lem3632270 _93229 _93232 s t f h1)). Qed.
Lemma lem3632272 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) (h1 : term46 _93229 _93232 s t f) : term49 _93229 _93232 s t f.
Proof. exact (fun h0 : term48 _93229 _93232 s t f => @lem3632271 _93229 _93232 s t f h1 h0). Qed.
Lemma lem3632273 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) (h1 : term48 _93229 _93232 s t f) : term48 _93229 _93232 s t f.
Proof. exact (h1). Qed.
Lemma lem3632274 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) (h1 : term46 _93229 _93232 s t f) (h2 : term48 _93229 _93232 s t f) : term46 _93229 _93232 s t f.
Proof. exact (@lem3632272 _93229 _93232 s t f h1 (@lem3632273 _93229 _93232 s t f h2)). Qed.
Lemma lem3632275 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) (h1 : term48 _93229 _93232 s t f) : term48 _93229 _93232 s t f.
Proof. exact (fun h0 : term46 _93229 _93232 s t f => @lem3632274 _93229 _93232 s t f h0 h1). Qed.
Lemma lem3632276 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) : term50 _93229 _93232 s t f.
Proof. exact (fun h0 : term48 _93229 _93232 s t f => @lem3632275 _93229 _93232 s t f h0). Qed.
Lemma lem3632279 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) : term48 _93229 _93232 s t f.
Proof. exact (@lem3632276 _93229 _93232 s t f (@lem3632268 _93229 _93232 s t f)). Qed.
Lemma lem3632280 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) : term48 _93229 _93232 s t f.
Proof. exact (@lem3632279 _93229 _93232 s t f). Qed.
Lemma lem3632294 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3632295 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) : (term46 _93229 _93232 s t f) = (term51 _93229 _93232 s t f).
Proof. exact (@lem3632294 (term47 _93229 _93232 s t f)). Qed.
Lemma lem3632297 (t : Prop) : (term52 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3632298 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) : (term51 _93229 _93232 s t f) = (term44 _93229 _93232 s t f).
Proof. exact (@lem3632297 (term44 _93229 _93232 s t f)). Qed.
Lemma lem3632301 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) : (term46 _93229 _93232 s t f) = (term44 _93229 _93232 s t f).
Proof. exact (TRANS (@lem3632295 _93229 _93232 s t f) (@lem3632298 _93229 _93232 s t f)). Qed.
Lemma lem3632378 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) : (term53 _93229 _93232 t f) = (term54 _93229 _93232 t f).
Proof. exact (fun_ext (fun s : _93229 -> Prop => @lem3632301 _93229 _93232 s t f)). Qed.
Lemma lem3632379 {_93229 : Type'} : (@all (_93229 -> Prop)) = (@all (_93229 -> Prop)).
Proof. exact (eq_refl (@all (_93229 -> Prop))). Qed.
Lemma lem3632380 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) : (term55 _93229 _93232 t f) = (term56 _93229 _93232 t f).
Proof. exact (MK_COMB (@lem3632379 _93229) (@lem3632378 _93229 _93232 t f)). Qed.
Lemma lem3632385 {_93229 _93232 : Type'} (f : _93232 -> _93229) : (term57 _93229 _93232 f) = (term58 _93229 _93232 f).
Proof. exact (fun_ext (fun t : _93232 -> Prop => @lem3632380 _93229 _93232 t f)). Qed.
Lemma lem3632386 {_93232 : Type'} : (@all (_93232 -> Prop)) = (@all (_93232 -> Prop)).
Proof. exact (eq_refl (@all (_93232 -> Prop))). Qed.
Lemma lem3632387 {_93229 _93232 : Type'} (f : _93232 -> _93229) : (term59 _93229 _93232 f) = (term60 _93229 _93232 f).
Proof. exact (MK_COMB (@lem3632386 _93232) (@lem3632385 _93229 _93232 f)). Qed.
Lemma lem3632392 {_93229 _93232 : Type'} : (term61 _93229 _93232) = (term62 _93229 _93232).
Proof. exact (fun_ext (fun f : _93232 -> _93229 => @lem3632387 _93229 _93232 f)). Qed.
Lemma lem3632393 {_93229 _93232 : Type'} : (@all (_93232 -> _93229)) = (@all (_93232 -> _93229)).
Proof. exact (eq_refl (@all (_93232 -> _93229))). Qed.
Lemma lem3632402 {_93229 _93232 : Type'} : (term63 _93229 _93232) = (term64 _93229 _93232).
Proof. exact (MK_COMB (@lem3632393 _93229 _93232) (@lem3632392 _93229 _93232)). Qed.
Lemma lem3632407 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (y : _93232) (x : _93229) : (term34 _93229 _93232 t f y x) = (term34 _93229 _93232 t f y x).
Proof. exact (eq_refl (term34 _93229 _93232 t f y x)). Qed.
Lemma lem3632408 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (x : _93229) : (term36 _93229 _93232 t f x) = (term36 _93229 _93232 t f x).
Proof. exact (fun_ext (fun y : _93232 => @lem3632407 _93229 _93232 t f y x)). Qed.
Lemma lem3632409 {_93232 : Type'} : (@ex _93232) = (@ex _93232).
Proof. exact (eq_refl (@ex _93232)). Qed.
Lemma lem3632410 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (x : _93229) : (term38 _93229 _93232 t f x) = (term38 _93229 _93232 t f x).
Proof. exact (MK_COMB (@lem3632409 _93232) (@lem3632408 _93229 _93232 t f x)). Qed.
Lemma lem3632413 {_93229 : Type'} (s : _93229 -> Prop) (x : _93229) : (term14 _93229 s x) = (term14 _93229 s x).
Proof. exact (eq_refl (term14 _93229 s x)). Qed.
Lemma lem3632414 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) (x : _93229) : (term40 _93229 _93232 s t f x) = (term40 _93229 _93232 s t f x).
Proof. exact (MK_COMB (@lem3632413 _93229 s x) (@lem3632410 _93229 _93232 t f x)). Qed.
Lemma lem3632415 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) : (term42 _93229 _93232 s t f) = (term42 _93229 _93232 s t f).
Proof. exact (fun_ext (fun x : _93229 => @lem3632414 _93229 _93232 s t f x)). Qed.
Lemma lem3632416 {_93229 : Type'} : (@all _93229) = (@all _93229).
Proof. exact (eq_refl (@all _93229)). Qed.
Lemma lem3632417 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) : (term43 _93229 _93232 s t f) = (term43 _93229 _93232 s t f).
Proof. exact (MK_COMB (@lem3632416 _93229) (@lem3632415 _93229 _93232 s t f)). Qed.
Lemma lem3632422 {_93229 _93232 : Type'} (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93232) : (term21 _93229 _93232 x f t x') = (term21 _93229 _93232 x f t x').
Proof. exact (eq_refl (term21 _93229 _93232 x f t x')). Qed.
Lemma lem3632423 {_93229 _93232 : Type'} (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term23 _93229 _93232 x f t) = (term23 _93229 _93232 x f t).
Proof. exact (fun_ext (fun x' : _93232 => @lem3632422 _93229 _93232 x f t x')). Qed.
Lemma lem3632424 {_93232 : Type'} : (@ex _93232) = (@ex _93232).
Proof. exact (eq_refl (@ex _93232)). Qed.
Lemma lem3632425 {_93229 _93232 : Type'} (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term24 _93229 _93232 x f t) = (term24 _93229 _93232 x f t).
Proof. exact (MK_COMB (@lem3632424 _93232) (@lem3632423 _93229 _93232 x f t)). Qed.
Lemma lem3632428 {_93229 : Type'} (s : _93229 -> Prop) (x : _93229) : (term14 _93229 s x) = (term14 _93229 s x).
Proof. exact (eq_refl (term14 _93229 s x)). Qed.
Lemma lem3632429 {_93229 _93232 : Type'} (s : _93229 -> Prop) (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term26 _93229 _93232 s x f t) = (term26 _93229 _93232 s x f t).
Proof. exact (MK_COMB (@lem3632428 _93229 s x) (@lem3632425 _93229 _93232 x f t)). Qed.
Lemma lem3632430 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term28 _93229 _93232 s f t) = (term28 _93229 _93232 s f t).
Proof. exact (fun_ext (fun x : _93229 => @lem3632429 _93229 _93232 s x f t)). Qed.
Lemma lem3632431 {_93229 : Type'} : (@all _93229) = (@all _93229).
Proof. exact (eq_refl (@all _93229)). Qed.
Lemma lem3632432 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term29 _93229 _93232 s f t) = (term29 _93229 _93232 s f t).
Proof. exact (MK_COMB (@lem3632431 _93229) (@lem3632430 _93229 _93232 s f t)). Qed.
Lemma lem3632433 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3632434 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term30 _93229 _93232 s f t) = (term30 _93229 _93232 s f t).
Proof. exact (MK_COMB (@lem3632433) (@lem3632432 _93229 _93232 s f t)). Qed.
Lemma lem3632435 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) : (term44 _93229 _93232 s t f) = (term44 _93229 _93232 s t f).
Proof. exact (MK_COMB (@lem3632434 _93229 _93232 s f t) (@lem3632417 _93229 _93232 s t f)). Qed.
Lemma lem3632436 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) : (term54 _93229 _93232 t f) = (term54 _93229 _93232 t f).
Proof. exact (fun_ext (fun s : _93229 -> Prop => @lem3632435 _93229 _93232 s t f)). Qed.
Lemma lem3632437 {_93229 : Type'} : (@all (_93229 -> Prop)) = (@all (_93229 -> Prop)).
Proof. exact (eq_refl (@all (_93229 -> Prop))). Qed.
Lemma lem3632438 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) : (term56 _93229 _93232 t f) = (term56 _93229 _93232 t f).
Proof. exact (MK_COMB (@lem3632437 _93229) (@lem3632436 _93229 _93232 t f)). Qed.
Lemma lem3632439 {_93229 _93232 : Type'} (f : _93232 -> _93229) : (term58 _93229 _93232 f) = (term58 _93229 _93232 f).
Proof. exact (fun_ext (fun t : _93232 -> Prop => @lem3632438 _93229 _93232 t f)). Qed.
Lemma lem3632440 {_93232 : Type'} : (@all (_93232 -> Prop)) = (@all (_93232 -> Prop)).
Proof. exact (eq_refl (@all (_93232 -> Prop))). Qed.
Lemma lem3632441 {_93229 _93232 : Type'} (f : _93232 -> _93229) : (term60 _93229 _93232 f) = (term60 _93229 _93232 f).
Proof. exact (MK_COMB (@lem3632440 _93232) (@lem3632439 _93229 _93232 f)). Qed.
Lemma lem3632442 {_93229 _93232 : Type'} : (term62 _93229 _93232) = (term62 _93229 _93232).
Proof. exact (fun_ext (fun f : _93232 -> _93229 => @lem3632441 _93229 _93232 f)). Qed.
Lemma lem3632443 {_93229 _93232 : Type'} : (@all (_93232 -> _93229)) = (@all (_93232 -> _93229)).
Proof. exact (eq_refl (@all (_93232 -> _93229))). Qed.
Lemma lem3632444 {_93229 _93232 : Type'} : (term64 _93229 _93232) = (term64 _93229 _93232).
Proof. exact (MK_COMB (@lem3632443 _93229 _93232) (@lem3632442 _93229 _93232)). Qed.
Lemma lem3632499 {_93229 _93232 : Type'} : (term63 _93229 _93232) = (term64 _93229 _93232).
Proof. exact (TRANS (@lem3632402 _93229 _93232) (@lem3632444 _93229 _93232)). Qed.
Lemma lem3632500 {_93229 _93232 : Type'} : (term64 _93229 _93232) = (term63 _93229 _93232).
Proof. exact (SYM (@lem3632499 _93229 _93232)). Qed.
Lemma lem3632501 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) (h1 : term29 _93229 _93232 s f t) : term29 _93229 _93232 s f t.
Proof. exact (h1). Qed.
Lemma lem3632504 (p : Prop) : p = (term45 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3632505 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (x : _93229) : (term38 _93229 _93232 t f x) = (term65 _93229 _93232 t f x).
Proof. exact (@lem3632504 (term38 _93229 _93232 t f x)). Qed.
Lemma lem3632506 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (x : _93229) : (term65 _93229 _93232 t f x) = (term38 _93229 _93232 t f x).
Proof. exact (SYM (@lem3632505 _93229 _93232 t f x)). Qed.
Lemma lem3632507 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (x : _93229) (h1 : term66 _93229 _93232 t f x) : term66 _93229 _93232 t f x.
Proof. exact (h1). Qed.
Lemma lem3632513 {_93229 _93232 : Type'} (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93232) : (term21 _93229 _93232 x f t x') = (term21 _93229 _93232 x f t x').
Proof. exact (eq_refl (term21 _93229 _93232 x f t x')). Qed.
Lemma lem3632514 {_93229 _93232 : Type'} (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term23 _93229 _93232 x f t) = (term23 _93229 _93232 x f t).
Proof. exact (fun_ext (fun x' : _93232 => @lem3632513 _93229 _93232 x f t x')). Qed.
Lemma lem3632515 {_93232 : Type'} : (@ex _93232) = (@ex _93232).
Proof. exact (eq_refl (@ex _93232)). Qed.
Lemma lem3632516 {_93229 _93232 : Type'} (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term24 _93229 _93232 x f t) = (term24 _93229 _93232 x f t).
Proof. exact (MK_COMB (@lem3632515 _93232) (@lem3632514 _93229 _93232 x f t)). Qed.
Lemma lem3632518 {_93229 : Type'} (s : _93229 -> Prop) (x : _93229) : (term67 _93229 s x) = (term67 _93229 s x).
Proof. exact (eq_refl (term67 _93229 s x)). Qed.
Lemma lem3632519 {_93229 _93232 : Type'} (s : _93229 -> Prop) (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term68 _93229 _93232 s x f t) = (term68 _93229 _93232 s x f t).
Proof. exact (MK_COMB (@lem3632518 _93229 s x) (@lem3632516 _93229 _93232 x f t)). Qed.
Lemma lem3632520 {_93229 _93232 : Type'} (s : _93229 -> Prop) (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term26 _93229 _93232 s x f t) = (term68 _93229 _93232 s x f t).
Proof. exact (@lem17265 (s x) (term24 _93229 _93232 x f t)). Qed.
Lemma lem3632521 {_93229 _93232 : Type'} (s : _93229 -> Prop) (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term26 _93229 _93232 s x f t) = (term68 _93229 _93232 s x f t).
Proof. exact (TRANS (@lem3632520 _93229 _93232 s x f t) (@lem3632519 _93229 _93232 s x f t)). Qed.
Lemma lem3632522 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term28 _93229 _93232 s f t) = (term69 _93229 _93232 s f t).
Proof. exact (fun_ext (fun x : _93229 => @lem3632521 _93229 _93232 s x f t)). Qed.
Lemma lem3632523 {_93229 : Type'} : (@all _93229) = (@all _93229).
Proof. exact (eq_refl (@all _93229)). Qed.
Lemma lem3632524 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term29 _93229 _93232 s f t) = (term70 _93229 _93232 s f t).
Proof. exact (MK_COMB (@lem3632523 _93229) (@lem3632522 _93229 _93232 s f t)). Qed.
Lemma lem3632607 {A : Type'} (P : Prop) (Q : A -> Prop) : (term71 A P Q) = (term72 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3632608 {_93232 : Type'} (P : Prop) (Q : _93232 -> Prop) : (term71 _93232 P Q) = (term72 _93232 P Q).
Proof. exact (@lem3632607 _93232 P Q). Qed.
Lemma lem3632609 {_93229 _93232 : Type'} (s : _93229 -> Prop) (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term73 _93229 _93232 s x f t) = (term74 _93229 _93232 s x f t).
Proof. exact (@lem3632608 _93232 (term75 _93229 s x) (term23 _93229 _93232 x f t)). Qed.
Lemma lem3632610 {_93229 _93232 : Type'} (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93232) : (term76 _93229 _93232 x f t x') = (term21 _93229 _93232 x f t x').
Proof. exact (eq_refl (term76 _93229 _93232 x f t x')). Qed.
Lemma lem3632611 {_93229 _93232 : Type'} (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term77 _93229 _93232 x f t) = (term23 _93229 _93232 x f t).
Proof. exact (fun_ext (fun x' : _93232 => @lem3632610 _93229 _93232 x f t x')). Qed.
Lemma lem3632612 {_93232 : Type'} : (@ex _93232) = (@ex _93232).
Proof. exact (eq_refl (@ex _93232)). Qed.
Lemma lem3632613 {_93229 _93232 : Type'} (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term78 _93229 _93232 x f t) = (term24 _93229 _93232 x f t).
Proof. exact (MK_COMB (@lem3632612 _93232) (@lem3632611 _93229 _93232 x f t)). Qed.
Lemma lem3632614 {_93229 : Type'} (s : _93229 -> Prop) (x : _93229) : (term67 _93229 s x) = (term67 _93229 s x).
Proof. exact (eq_refl (term67 _93229 s x)). Qed.
Lemma lem3632615 {_93229 _93232 : Type'} (s : _93229 -> Prop) (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term73 _93229 _93232 s x f t) = (term68 _93229 _93232 s x f t).
Proof. exact (MK_COMB (@lem3632614 _93229 s x) (@lem3632613 _93229 _93232 x f t)). Qed.
Lemma lem3632616 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3632617 {_93229 _93232 : Type'} (s : _93229 -> Prop) (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term79 _93229 _93232 s x f t) = (term80 _93229 _93232 s x f t).
Proof. exact (MK_COMB (@lem3632616) (@lem3632615 _93229 _93232 s x f t)). Qed.
Lemma lem3632618 {_93229 _93232 : Type'} (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93232) : (term76 _93229 _93232 x f t x') = (term21 _93229 _93232 x f t x').
Proof. exact (eq_refl (term76 _93229 _93232 x f t x')). Qed.
Lemma lem3632619 {_93229 : Type'} (s : _93229 -> Prop) (x : _93229) : (term67 _93229 s x) = (term67 _93229 s x).
Proof. exact (eq_refl (term67 _93229 s x)). Qed.
Lemma lem3632620 {_93229 _93232 : Type'} (s : _93229 -> Prop) (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93232) : (term81 _93229 _93232 s x f t x') = (term82 _93229 _93232 s x f t x').
Proof. exact (MK_COMB (@lem3632619 _93229 s x) (@lem3632618 _93229 _93232 x f t x')). Qed.
Lemma lem3632621 {_93229 _93232 : Type'} (s : _93229 -> Prop) (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term83 _93229 _93232 s x f t) = (term84 _93229 _93232 s x f t).
Proof. exact (fun_ext (fun x' : _93232 => @lem3632620 _93229 _93232 s x f t x')). Qed.
Lemma lem3632622 {_93232 : Type'} : (@ex _93232) = (@ex _93232).
Proof. exact (eq_refl (@ex _93232)). Qed.
Lemma lem3632623 {_93229 _93232 : Type'} (s : _93229 -> Prop) (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term74 _93229 _93232 s x f t) = (term85 _93229 _93232 s x f t).
Proof. exact (MK_COMB (@lem3632622 _93232) (@lem3632621 _93229 _93232 s x f t)). Qed.
Lemma lem3632624 {_93229 _93232 : Type'} (s : _93229 -> Prop) (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) : ((term73 _93229 _93232 s x f t) = (term74 _93229 _93232 s x f t)) = ((term68 _93229 _93232 s x f t) = (term85 _93229 _93232 s x f t)).
Proof. exact (MK_COMB (@lem3632617 _93229 _93232 s x f t) (@lem3632623 _93229 _93232 s x f t)). Qed.
Lemma lem3632625 {_93229 _93232 : Type'} (s : _93229 -> Prop) (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term68 _93229 _93232 s x f t) = (term85 _93229 _93232 s x f t).
Proof. exact (EQ_MP (@lem3632624 _93229 _93232 s x f t) (@lem3632609 _93229 _93232 s x f t)). Qed.
Lemma lem3632626 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term69 _93229 _93232 s f t) = (term86 _93229 _93232 s f t).
Proof. exact (fun_ext (fun x : _93229 => @lem3632625 _93229 _93232 s x f t)). Qed.
Lemma lem3632627 {_93229 : Type'} : (@all _93229) = (@all _93229).
Proof. exact (eq_refl (@all _93229)). Qed.
Lemma lem3632628 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term70 _93229 _93232 s f t) = (term87 _93229 _93232 s f t).
Proof. exact (MK_COMB (@lem3632627 _93229) (@lem3632626 _93229 _93232 s f t)). Qed.
Lemma lem3632630 {A B : Type'} (P : type1413 A B) : (term88 A B P) = (term89 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3632631 {_93229 _93232 : Type'} (P : type1413 _93229 _93232) : (term88 _93229 _93232 P) = (term89 _93229 _93232 P).
Proof. exact (@lem3632630 _93229 _93232 P). Qed.
Lemma lem3632632 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term90 _93229 _93232 s f t) = (term91 _93229 _93232 s f t).
Proof. exact (@lem3632631 _93229 _93232 (term92 _93229 _93232 s f t)). Qed.
Lemma lem3632633 {_93229 _93232 : Type'} (s : _93229 -> Prop) (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term93 _93229 _93232 s f t x) = (term84 _93229 _93232 s x f t).
Proof. exact (eq_refl (term93 _93229 _93232 s f t x)). Qed.
Lemma lem3632634 {_93232 : Type'} (x : _93232) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3632635 {_93229 _93232 : Type'} (s : _93229 -> Prop) (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93232) : (term94 _93229 _93232 s f t x x') = (term95 _93229 _93232 s x f t x').
Proof. exact (MK_COMB (@lem3632633 _93229 _93232 s x f t) (@lem3632634 _93232 x')). Qed.
Lemma lem3632636 {_93229 _93232 : Type'} (s : _93229 -> Prop) (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93232) : (term95 _93229 _93232 s x f t x') = (term82 _93229 _93232 s x f t x').
Proof. exact (eq_refl (term95 _93229 _93232 s x f t x')). Qed.
Lemma lem3632637 {_93229 _93232 : Type'} (s : _93229 -> Prop) (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93232) : (term94 _93229 _93232 s f t x x') = (term82 _93229 _93232 s x f t x').
Proof. exact (TRANS (@lem3632635 _93229 _93232 s x f t x') (@lem3632636 _93229 _93232 s x f t x')). Qed.
Lemma lem3632638 {_93229 _93232 : Type'} (s : _93229 -> Prop) (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term96 _93229 _93232 s f t x) = (term84 _93229 _93232 s x f t).
Proof. exact (fun_ext (fun x' : _93232 => @lem3632637 _93229 _93232 s x f t x')). Qed.
Lemma lem3632639 {_93232 : Type'} : (@ex _93232) = (@ex _93232).
Proof. exact (eq_refl (@ex _93232)). Qed.
Lemma lem3632640 {_93229 _93232 : Type'} (s : _93229 -> Prop) (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term97 _93229 _93232 s f t x) = (term85 _93229 _93232 s x f t).
Proof. exact (MK_COMB (@lem3632639 _93232) (@lem3632638 _93229 _93232 s x f t)). Qed.
Lemma lem3632641 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term98 _93229 _93232 s f t) = (term86 _93229 _93232 s f t).
Proof. exact (fun_ext (fun x : _93229 => @lem3632640 _93229 _93232 s x f t)). Qed.
Lemma lem3632642 {_93229 : Type'} : (@all _93229) = (@all _93229).
Proof. exact (eq_refl (@all _93229)). Qed.
Lemma lem3632643 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term90 _93229 _93232 s f t) = (term87 _93229 _93232 s f t).
Proof. exact (MK_COMB (@lem3632642 _93229) (@lem3632641 _93229 _93232 s f t)). Qed.
Lemma lem3632644 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3632645 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term99 _93229 _93232 s f t) = (term100 _93229 _93232 s f t).
Proof. exact (MK_COMB (@lem3632644) (@lem3632643 _93229 _93232 s f t)). Qed.
Lemma lem3632646 {_93229 _93232 : Type'} (s : _93229 -> Prop) (x : _93229) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term93 _93229 _93232 s f t x) = (term84 _93229 _93232 s x f t).
Proof. exact (eq_refl (term93 _93229 _93232 s f t x)). Qed.
Lemma lem3632647 {_93229 _93232 : Type'} (x : _93229 -> _93232) (x' : _93229) : (x x') = (x x').
Proof. exact (eq_refl (x x')). Qed.
Lemma lem3632648 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) (x : _93229 -> _93232) (x' : _93229) : (term101 _93229 _93232 s f t x x') = (term102 _93229 _93232 s f t x x').
Proof. exact (MK_COMB (@lem3632646 _93229 _93232 s x' f t) (@lem3632647 _93229 _93232 x x')). Qed.
Lemma lem3632649 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) (x : _93229 -> _93232) (x' : _93229) : (term102 _93229 _93232 s f t x x') = (term103 _93229 _93232 s f t x x').
Proof. exact (eq_refl (term102 _93229 _93232 s f t x x')). Qed.
Lemma lem3632650 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) (x : _93229 -> _93232) (x' : _93229) : (term101 _93229 _93232 s f t x x') = (term103 _93229 _93232 s f t x x').
Proof. exact (TRANS (@lem3632648 _93229 _93232 s f t x x') (@lem3632649 _93229 _93232 s f t x x')). Qed.
Lemma lem3632651 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) (x : _93229 -> _93232) : (term104 _93229 _93232 s f t x) = (term105 _93229 _93232 s f t x).
Proof. exact (fun_ext (fun x' : _93229 => @lem3632650 _93229 _93232 s f t x x')). Qed.
Lemma lem3632652 {_93229 : Type'} : (@all _93229) = (@all _93229).
Proof. exact (eq_refl (@all _93229)). Qed.
Lemma lem3632653 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) (x : _93229 -> _93232) : (term106 _93229 _93232 s f t x) = (term107 _93229 _93232 s f t x).
Proof. exact (MK_COMB (@lem3632652 _93229) (@lem3632651 _93229 _93232 s f t x)). Qed.
Lemma lem3632654 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term108 _93229 _93232 s f t) = (term109 _93229 _93232 s f t).
Proof. exact (fun_ext (fun x : _93229 -> _93232 => @lem3632653 _93229 _93232 s f t x)). Qed.
Lemma lem3632655 {_93229 _93232 : Type'} : (@ex (_93229 -> _93232)) = (@ex (_93229 -> _93232)).
Proof. exact (eq_refl (@ex (_93229 -> _93232))). Qed.
Lemma lem3632656 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term91 _93229 _93232 s f t) = (term110 _93229 _93232 s f t).
Proof. exact (MK_COMB (@lem3632655 _93229 _93232) (@lem3632654 _93229 _93232 s f t)). Qed.
Lemma lem3632657 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) : ((term90 _93229 _93232 s f t) = (term91 _93229 _93232 s f t)) = ((term87 _93229 _93232 s f t) = (term110 _93229 _93232 s f t)).
Proof. exact (MK_COMB (@lem3632645 _93229 _93232 s f t) (@lem3632656 _93229 _93232 s f t)). Qed.
Lemma lem3632658 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term87 _93229 _93232 s f t) = (term110 _93229 _93232 s f t).
Proof. exact (EQ_MP (@lem3632657 _93229 _93232 s f t) (@lem3632632 _93229 _93232 s f t)). Qed.
Lemma lem3632660 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term70 _93229 _93232 s f t) = (term110 _93229 _93232 s f t).
Proof. exact (TRANS (@lem3632628 _93229 _93232 s f t) (@lem3632658 _93229 _93232 s f t)). Qed.
Lemma lem3632661 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) : (term29 _93229 _93232 s f t) = (term110 _93229 _93232 s f t).
Proof. exact (TRANS (@lem3632524 _93229 _93232 s f t) (@lem3632660 _93229 _93232 s f t)). Qed.
Lemma lem3632662 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) (h1 : term29 _93229 _93232 s f t) : term110 _93229 _93232 s f t.
Proof. exact (EQ_MP (@lem3632661 _93229 _93232 s f t) (@lem3632501 _93229 _93232 s f t h1)). Qed.
Lemma lem3632668 {_93229 : Type'} (s : _93229 -> Prop) (x : _93229) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3632675 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (y : _93232) (x : _93229) : (term111 _93229 _93232 t f y x) = (term112 _93229 _93232 t f y x).
Proof. exact (@lem17045 (t y) ((f y) = x)). Qed.
Lemma lem3632676 {_93232 : Type'} (P : _93232 -> Prop) : (term113 _93232 P) = (term114 _93232 P).
Proof. exact (@lem18394 _93232 P). Qed.
Lemma lem3632677 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (x : _93229) : (term66 _93229 _93232 t f x) = (term115 _93229 _93232 t f x).
Proof. exact (@lem3632676 _93232 (term36 _93229 _93232 t f x)). Qed.
Lemma lem3632678 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (y : _93232) (x : _93229) : (term116 _93229 _93232 t f x y) = (term34 _93229 _93232 t f y x).
Proof. exact (eq_refl (term116 _93229 _93232 t f x y)). Qed.
Lemma lem3632679 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3632680 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (y : _93232) (x : _93229) : (term117 _93229 _93232 t f x y) = (term111 _93229 _93232 t f y x).
Proof. exact (MK_COMB (@lem3632679) (@lem3632678 _93229 _93232 t f y x)). Qed.
Lemma lem3632681 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (y : _93232) (x : _93229) : (term117 _93229 _93232 t f x y) = (term112 _93229 _93232 t f y x).
Proof. exact (TRANS (@lem3632680 _93229 _93232 t f y x) (@lem3632675 _93229 _93232 t f y x)). Qed.
Lemma lem3632682 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (x : _93229) : (term118 _93229 _93232 t f x) = (term119 _93229 _93232 t f x).
Proof. exact (fun_ext (fun y : _93232 => @lem3632681 _93229 _93232 t f y x)). Qed.
Lemma lem3632683 {_93232 : Type'} : (@all _93232) = (@all _93232).
Proof. exact (eq_refl (@all _93232)). Qed.
Lemma lem3632684 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (x : _93229) : (term115 _93229 _93232 t f x) = (term120 _93229 _93232 t f x).
Proof. exact (MK_COMB (@lem3632683 _93232) (@lem3632682 _93229 _93232 t f x)). Qed.
Lemma lem3632737 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (x : _93229) : (term66 _93229 _93232 t f x) = (term120 _93229 _93232 t f x).
Proof. exact (TRANS (@lem3632677 _93229 _93232 t f x) (@lem3632684 _93229 _93232 t f x)). Qed.
Lemma lem3632738 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (x : _93229) (h1 : term66 _93229 _93232 t f x) : term120 _93229 _93232 t f x.
Proof. exact (EQ_MP (@lem3632737 _93229 _93232 t f x) (@lem3632507 _93229 _93232 t f x h1)). Qed.
Lemma lem3632739 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93229 -> _93232) (h1 : term107 _93229 _93232 s f t x') : term107 _93229 _93232 s f t x'.
Proof. exact (h1). Qed.
Lemma lem3632743 {_93229 : Type'} (s : _93229 -> Prop) (x : _93229) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3632760 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (y : _93232) (x : _93229) : (term112 _93229 _93232 t f y x) = (term112 _93229 _93232 t f y x).
Proof. exact (eq_refl (term112 _93229 _93232 t f y x)). Qed.
Lemma lem3632761 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (x : _93229) : (term119 _93229 _93232 t f x) = (term119 _93229 _93232 t f x).
Proof. exact (fun_ext (fun y : _93232 => @lem3632760 _93229 _93232 t f y x)). Qed.
Lemma lem3632762 {_93232 : Type'} : (@all _93232) = (@all _93232).
Proof. exact (eq_refl (@all _93232)). Qed.
Lemma lem3632763 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (x : _93229) : (term120 _93229 _93232 t f x) = (term120 _93229 _93232 t f x).
Proof. exact (MK_COMB (@lem3632762 _93232) (@lem3632761 _93229 _93232 t f x)). Qed.
Lemma lem3632764 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (x : _93229) (h1 : term66 _93229 _93232 t f x) : term120 _93229 _93232 t f x.
Proof. exact (EQ_MP (@lem3632763 _93229 _93232 t f x) (@lem3632738 _93229 _93232 t f x h1)). Qed.
Lemma lem3632789 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93229 -> _93232) (x : _93229) : (term103 _93229 _93232 s f t x' x) = (term103 _93229 _93232 s f t x' x).
Proof. exact (eq_refl (term103 _93229 _93232 s f t x' x)). Qed.
Lemma lem3632790 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93229 -> _93232) : (term105 _93229 _93232 s f t x') = (term105 _93229 _93232 s f t x').
Proof. exact (fun_ext (fun x : _93229 => @lem3632789 _93229 _93232 s f t x' x)). Qed.
Lemma lem3632791 {_93229 : Type'} : (@all _93229) = (@all _93229).
Proof. exact (eq_refl (@all _93229)). Qed.
Lemma lem3632792 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93229 -> _93232) : (term107 _93229 _93232 s f t x') = (term107 _93229 _93232 s f t x').
Proof. exact (MK_COMB (@lem3632791 _93229) (@lem3632790 _93229 _93232 s f t x')). Qed.
Lemma lem3632793 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93229 -> _93232) (h1 : term107 _93229 _93232 s f t x') : term107 _93229 _93232 s f t x'.
Proof. exact (EQ_MP (@lem3632792 _93229 _93232 s f t x') (@lem3632739 _93229 _93232 s f t x' h1)). Qed.
Lemma lem3632797 {_93229 : Type'} (s : _93229 -> Prop) (x : _93229) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3632805 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (y : _93232) (x : _93229) : (term112 _93229 _93232 t f y x) = (term112 _93229 _93232 t f y x).
Proof. exact (eq_refl (term112 _93229 _93232 t f y x)). Qed.
Lemma lem3632806 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (x : _93229) : (term119 _93229 _93232 t f x) = (term119 _93229 _93232 t f x).
Proof. exact (fun_ext (fun y : _93232 => @lem3632805 _93229 _93232 t f y x)). Qed.
Lemma lem3632807 {_93232 : Type'} : (@all _93232) = (@all _93232).
Proof. exact (eq_refl (@all _93232)). Qed.
Lemma lem3632809 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (x : _93229) : (term120 _93229 _93232 t f x) = (term120 _93229 _93232 t f x).
Proof. exact (MK_COMB (@lem3632807 _93232) (@lem3632806 _93229 _93232 t f x)). Qed.
Lemma lem3632810 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (x : _93229) (h1 : term66 _93229 _93232 t f x) : term120 _93229 _93232 t f x.
Proof. exact (EQ_MP (@lem3632809 _93229 _93232 t f x) (@lem3632764 _93229 _93232 t f x h1)). Qed.
Lemma lem3632828 {_93229 _93232 : Type'} (f : _93232 -> _93229) (s : _93229 -> Prop) (t : _93232 -> Prop) (x' : _93229 -> _93232) (x : _93229) : (term103 _93229 _93232 s f t x' x) = (term121 _93229 _93232 f s t x' x).
Proof. exact (@lem19490 (x = (term122 _93229 _93232 f x' x)) (term75 _93229 s x) (term123 _93229 _93232 t x' x)). Qed.
Lemma lem3632829 {_93229 _93232 : Type'} (f : _93232 -> _93229) (s : _93229 -> Prop) (t : _93232 -> Prop) (x' : _93229 -> _93232) : (term105 _93229 _93232 s f t x') = (term124 _93229 _93232 f s t x').
Proof. exact (fun_ext (fun x : _93229 => @lem3632828 _93229 _93232 f s t x' x)). Qed.
Lemma lem3632830 {_93229 : Type'} : (@all _93229) = (@all _93229).
Proof. exact (eq_refl (@all _93229)). Qed.
Lemma lem3632832 {_93229 _93232 : Type'} (f : _93232 -> _93229) (s : _93229 -> Prop) (t : _93232 -> Prop) (x' : _93229 -> _93232) : (term107 _93229 _93232 s f t x') = (term125 _93229 _93232 f s t x').
Proof. exact (MK_COMB (@lem3632830 _93229) (@lem3632829 _93229 _93232 f s t x')). Qed.
Lemma lem3632833 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93229 -> _93232) (h1 : term107 _93229 _93232 s f t x') : term125 _93229 _93232 f s t x'.
Proof. exact (EQ_MP (@lem3632832 _93229 _93232 f s t x') (@lem3632793 _93229 _93232 s f t x' h1)). Qed.
Lemma lem3632834 {_93229 _93232 : Type'} (_39634 : _93232) (t : _93232 -> Prop) (f : _93232 -> _93229) (x : _93229) (h1 : term66 _93229 _93232 t f x) : term126 _93229 _93232 t f x _39634.
Proof. exact (@lem3632810 _93229 _93232 t f x h1 _39634). Qed.
Lemma lem3632835 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (_39634 : _93232) (x : _93229) : (term126 _93229 _93232 t f x _39634) = (term112 _93229 _93232 t f _39634 x).
Proof. exact (eq_refl (term126 _93229 _93232 t f x _39634)). Qed.
Lemma lem3632837 {_93229 _93232 : Type'} (_39635 : _93229) (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93229 -> _93232) (h1 : term107 _93229 _93232 s f t x') : term127 _93229 _93232 f s t x' _39635.
Proof. exact (@lem3632833 _93229 _93232 s f t x' h1 _39635). Qed.
Lemma lem3632838 {_93229 _93232 : Type'} (f : _93232 -> _93229) (s : _93229 -> Prop) (t : _93232 -> Prop) (x' : _93229 -> _93232) (_39635 : _93229) : (term127 _93229 _93232 f s t x' _39635) = (term121 _93229 _93232 f s t x' _39635).
Proof. exact (eq_refl (term127 _93229 _93232 f s t x' _39635)). Qed.
Lemma lem3632839 {_93229 _93232 : Type'} (_39635 : _93229) (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93229 -> _93232) (h1 : term107 _93229 _93232 s f t x') : term121 _93229 _93232 f s t x' _39635.
Proof. exact (EQ_MP (@lem3632838 _93229 _93232 f s t x' _39635) (@lem3632837 _93229 _93232 _39635 s f t x' h1)). Qed.
Lemma lem3632843 {_93229 : Type'} (s : _93229 -> Prop) (x : _93229) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3632849 {_93229 _93232 : Type'} (_39634 : _93232) (t : _93232 -> Prop) (f : _93232 -> _93229) (x : _93229) (h1 : term66 _93229 _93232 t f x) : term112 _93229 _93232 t f _39634 x.
Proof. exact (EQ_MP (@lem3632835 _93229 _93232 t f _39634 x) (@lem3632834 _93229 _93232 _39634 t f x h1)). Qed.
Lemma lem3632855 {_93229 _93232 : Type'} (_39635 : _93229) (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93229 -> _93232) (h1 : term107 _93229 _93232 s f t x') : term128 _93229 _93232 s f x' _39635.
Proof. exact (proj1 (@lem3632839 _93229 _93232 _39635 s f t x' h1)). Qed.
Lemma lem3632861 {_93229 _93232 : Type'} (_39635 : _93229) (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93229 -> _93232) (h1 : term107 _93229 _93232 s f t x') : term129 _93229 _93232 s t x' _39635.
Proof. exact (proj2 (@lem3632839 _93229 _93232 _39635 s f t x' h1)). Qed.
Lemma lem3632903 {_93229 : Type'} (x : _93229) (y : _93229) (z : _93229) : term130 _93229 x y z.
Proof. exact (@lem21385 _93229 x y z). Qed.
Lemma lem3632907 {_93229 : Type'} (s : _93229 -> Prop) (x : _93229) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3632908 {_93229 : Type'} (s : _93229 -> Prop) (x : _93229) (h1 : s x) : term131 _93229 s x.
Proof. exact (fun h0 : term75 _93229 s x => @lem3632907 _93229 s x h1). Qed.
Lemma lem3632910 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3632911 {_93229 : Type'} (s : _93229 -> Prop) (x : _93229) : (term131 _93229 s x) = (s x).
Proof. exact (@lem3632910 (s x)). Qed.
Lemma lem3632912 {_93229 : Type'} (s : _93229 -> Prop) (x : _93229) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3632911 _93229 s x) (@lem3632908 _93229 s x h1)). Qed.
Lemma lem3632918 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3632919 {_93229 _93232 : Type'} (t : _93232 -> Prop) (x' : _93229 -> _93232) (s : _93229 -> Prop) (_39635 : _93229) : (term129 _93229 _93232 s t x' _39635) = (term133 _93229 _93232 t x' s _39635).
Proof. exact (@lem3632918 (term123 _93229 _93232 t x' _39635) (term75 _93229 s _39635)). Qed.
Lemma lem3632925 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3632926 {_93229 _93232 : Type'} (t : _93232 -> Prop) (x' : _93229 -> _93232) (s : _93229 -> Prop) (_39635 : _93229) : (term134 _93229 _93232 s t x' _39635) = (term135 _93229 _93232 t x' s _39635).
Proof. exact (MK_COMB (@lem3632925) (@lem3632919 _93229 _93232 t x' s _39635)). Qed.
Lemma lem3632932 {_93229 _93232 : Type'} (t : _93232 -> Prop) (x' : _93229 -> _93232) (s : _93229 -> Prop) (_39635 : _93229) : (term133 _93229 _93232 t x' s _39635) = (term133 _93229 _93232 t x' s _39635).
Proof. exact (eq_refl (term133 _93229 _93232 t x' s _39635)). Qed.
Lemma lem3632933 {_93229 _93232 : Type'} (t : _93232 -> Prop) (x' : _93229 -> _93232) (s : _93229 -> Prop) (_39635 : _93229) : ((term129 _93229 _93232 s t x' _39635) = (term133 _93229 _93232 t x' s _39635)) = ((term133 _93229 _93232 t x' s _39635) = (term133 _93229 _93232 t x' s _39635)).
Proof. exact (MK_COMB (@lem3632926 _93229 _93232 t x' s _39635) (@lem3632932 _93229 _93232 t x' s _39635)). Qed.
Lemma lem3632935 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3632936 (x : Prop) : (x = x) = True.
Proof. exact (@lem3632935 Prop x). Qed.
Lemma lem3632937 {_93229 _93232 : Type'} (t : _93232 -> Prop) (x' : _93229 -> _93232) (s : _93229 -> Prop) (_39635 : _93229) : ((term133 _93229 _93232 t x' s _39635) = (term133 _93229 _93232 t x' s _39635)) = True.
Proof. exact (@lem3632936 (term133 _93229 _93232 t x' s _39635)). Qed.
Lemma lem3632938 {_93229 _93232 : Type'} (t : _93232 -> Prop) (x' : _93229 -> _93232) (s : _93229 -> Prop) (_39635 : _93229) : ((term129 _93229 _93232 s t x' _39635) = (term133 _93229 _93232 t x' s _39635)) = True.
Proof. exact (TRANS (@lem3632933 _93229 _93232 t x' s _39635) (@lem3632937 _93229 _93232 t x' s _39635)). Qed.
Lemma lem3632939 {_93229 _93232 : Type'} (t : _93232 -> Prop) (x' : _93229 -> _93232) (s : _93229 -> Prop) (_39635 : _93229) : True = ((term129 _93229 _93232 s t x' _39635) = (term133 _93229 _93232 t x' s _39635)).
Proof. exact (SYM (@lem3632938 _93229 _93232 t x' s _39635)). Qed.
Lemma lem3632940 {_93229 _93232 : Type'} (t : _93232 -> Prop) (x' : _93229 -> _93232) (s : _93229 -> Prop) (_39635 : _93229) : (term129 _93229 _93232 s t x' _39635) = (term133 _93229 _93232 t x' s _39635).
Proof. exact (EQ_MP (@lem3632939 _93229 _93232 t x' s _39635) (@lem0)). Qed.
Lemma lem3632941 {_93229 _93232 : Type'} (_39635 : _93229) (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93229 -> _93232) (h1 : term107 _93229 _93232 s f t x') : term133 _93229 _93232 t x' s _39635.
Proof. exact (EQ_MP (@lem3632940 _93229 _93232 t x' s _39635) (@lem3632861 _93229 _93232 _39635 s f t x' h1)). Qed.
Lemma lem3632943 (b : Prop) (a : Prop) : (a \/ b) = (term136 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3632944 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (x' : _93229 -> _93232) (_39635 : _93229) : (term133 _93229 _93232 t x' s _39635) = (term137 _93229 _93232 s t x' _39635).
Proof. exact (@lem3632943 (term75 _93229 s _39635) (term123 _93229 _93232 t x' _39635)). Qed.
Lemma lem3632946 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3632947 {_93229 : Type'} (s : _93229 -> Prop) (_39635 : _93229) : (term138 _93229 s _39635) = (s _39635).
Proof. exact (@lem3632946 (s _39635)). Qed.
Lemma lem3632948 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3632949 {_93229 : Type'} (s : _93229 -> Prop) (_39635 : _93229) : (term139 _93229 s _39635) = (term14 _93229 s _39635).
Proof. exact (MK_COMB (@lem3632948) (@lem3632947 _93229 s _39635)). Qed.
Lemma lem3632950 {_93229 _93232 : Type'} (t : _93232 -> Prop) (x' : _93229 -> _93232) (_39635 : _93229) : (term123 _93229 _93232 t x' _39635) = (term123 _93229 _93232 t x' _39635).
Proof. exact (eq_refl (term123 _93229 _93232 t x' _39635)). Qed.
Lemma lem3632951 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (x' : _93229 -> _93232) (_39635 : _93229) : (term137 _93229 _93232 s t x' _39635) = (term140 _93229 _93232 s t x' _39635).
Proof. exact (MK_COMB (@lem3632949 _93229 s _39635) (@lem3632950 _93229 _93232 t x' _39635)). Qed.
Lemma lem3632952 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (x' : _93229 -> _93232) (_39635 : _93229) : (term133 _93229 _93232 t x' s _39635) = (term140 _93229 _93232 s t x' _39635).
Proof. exact (TRANS (@lem3632944 _93229 _93232 s t x' _39635) (@lem3632951 _93229 _93232 s t x' _39635)). Qed.
Lemma lem3632955 {_93229 _93232 : Type'} (_39635 : _93229) (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93229 -> _93232) (h1 : term107 _93229 _93232 s f t x') : term140 _93229 _93232 s t x' _39635.
Proof. exact (EQ_MP (@lem3632952 _93229 _93232 s t x' _39635) (@lem3632941 _93229 _93232 _39635 s f t x' h1)). Qed.
Lemma lem3632956 {_93229 _93232 : Type'} (_39635 : _93229) (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93229 -> _93232) (h1 : term107 _93229 _93232 s f t x') : term140 _93229 _93232 s t x' _39635.
Proof. exact (@lem3632955 _93229 _93232 _39635 s f t x' h1). Qed.
Lemma lem3632957 {_93229 _93232 : Type'} (x : _93229) (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93229 -> _93232) (h1 : term107 _93229 _93232 s f t x') : term140 _93229 _93232 s t x' x.
Proof. exact (@lem3632956 _93229 _93232 x s f t x' h1). Qed.
Lemma lem3632960 {_93229 _93232 : Type'} (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93229 -> _93232) (s : _93229 -> Prop) (x : _93229) (h1 : term107 _93229 _93232 s f t x') (h2 : s x) : term123 _93229 _93232 t x' x.
Proof. exact (@lem3632957 _93229 _93232 x s f t x' h1 (@lem3632912 _93229 s x h2)). Qed.
Lemma lem3632961 {_93229 _93232 : Type'} (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93229 -> _93232) (s : _93229 -> Prop) (x : _93229) (h1 : term107 _93229 _93232 s f t x') (h2 : s x) : term141 _93229 _93232 t x' x.
Proof. exact (fun h0 : term142 _93229 _93232 t x' x => @lem3632960 _93229 _93232 f t x' s x h1 h2). Qed.
Lemma lem3632963 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3632964 {_93229 _93232 : Type'} (t : _93232 -> Prop) (x' : _93229 -> _93232) (x : _93229) : (term141 _93229 _93232 t x' x) = (term123 _93229 _93232 t x' x).
Proof. exact (@lem3632963 (term123 _93229 _93232 t x' x)). Qed.
Lemma lem3632965 {_93229 _93232 : Type'} (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93229 -> _93232) (s : _93229 -> Prop) (x : _93229) (h1 : term107 _93229 _93232 s f t x') (h2 : s x) : term123 _93229 _93232 t x' x.
Proof. exact (EQ_MP (@lem3632964 _93229 _93232 t x' x) (@lem3632961 _93229 _93232 f t x' s x h1 h2)). Qed.
Lemma lem3632967 {_93229 : Type'} (s : _93229 -> Prop) (x : _93229) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3632968 {_93229 : Type'} (s : _93229 -> Prop) (x : _93229) (h1 : s x) : term131 _93229 s x.
Proof. exact (fun h0 : term75 _93229 s x => @lem3632967 _93229 s x h1). Qed.
Lemma lem3632970 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3632971 {_93229 : Type'} (s : _93229 -> Prop) (x : _93229) : (term131 _93229 s x) = (s x).
Proof. exact (@lem3632970 (s x)). Qed.
Lemma lem3632972 {_93229 : Type'} (s : _93229 -> Prop) (x : _93229) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3632971 _93229 s x) (@lem3632968 _93229 s x h1)). Qed.
Lemma lem3632978 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3632979 {_93229 _93232 : Type'} (f : _93232 -> _93229) (x' : _93229 -> _93232) (s : _93229 -> Prop) (_39635 : _93229) : (term128 _93229 _93232 s f x' _39635) = (term143 _93229 _93232 f x' s _39635).
Proof. exact (@lem3632978 (_39635 = (term122 _93229 _93232 f x' _39635)) (term75 _93229 s _39635)). Qed.
Lemma lem3632987 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3632988 {_93229 _93232 : Type'} (f : _93232 -> _93229) (x' : _93229 -> _93232) (s : _93229 -> Prop) (_39635 : _93229) : (term144 _93229 _93232 s f x' _39635) = (term145 _93229 _93232 f x' s _39635).
Proof. exact (MK_COMB (@lem3632987) (@lem3632979 _93229 _93232 f x' s _39635)). Qed.
Lemma lem3632996 {_93229 _93232 : Type'} (f : _93232 -> _93229) (x' : _93229 -> _93232) (s : _93229 -> Prop) (_39635 : _93229) : (term143 _93229 _93232 f x' s _39635) = (term143 _93229 _93232 f x' s _39635).
Proof. exact (eq_refl (term143 _93229 _93232 f x' s _39635)). Qed.
Lemma lem3632997 {_93229 _93232 : Type'} (f : _93232 -> _93229) (x' : _93229 -> _93232) (s : _93229 -> Prop) (_39635 : _93229) : ((term128 _93229 _93232 s f x' _39635) = (term143 _93229 _93232 f x' s _39635)) = ((term143 _93229 _93232 f x' s _39635) = (term143 _93229 _93232 f x' s _39635)).
Proof. exact (MK_COMB (@lem3632988 _93229 _93232 f x' s _39635) (@lem3632996 _93229 _93232 f x' s _39635)). Qed.
Lemma lem3632999 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3633000 (x : Prop) : (x = x) = True.
Proof. exact (@lem3632999 Prop x). Qed.
Lemma lem3633001 {_93229 _93232 : Type'} (f : _93232 -> _93229) (x' : _93229 -> _93232) (s : _93229 -> Prop) (_39635 : _93229) : ((term143 _93229 _93232 f x' s _39635) = (term143 _93229 _93232 f x' s _39635)) = True.
Proof. exact (@lem3633000 (term143 _93229 _93232 f x' s _39635)). Qed.
Lemma lem3633002 {_93229 _93232 : Type'} (f : _93232 -> _93229) (x' : _93229 -> _93232) (s : _93229 -> Prop) (_39635 : _93229) : ((term128 _93229 _93232 s f x' _39635) = (term143 _93229 _93232 f x' s _39635)) = True.
Proof. exact (TRANS (@lem3632997 _93229 _93232 f x' s _39635) (@lem3633001 _93229 _93232 f x' s _39635)). Qed.
Lemma lem3633003 {_93229 _93232 : Type'} (f : _93232 -> _93229) (x' : _93229 -> _93232) (s : _93229 -> Prop) (_39635 : _93229) : True = ((term128 _93229 _93232 s f x' _39635) = (term143 _93229 _93232 f x' s _39635)).
Proof. exact (SYM (@lem3633002 _93229 _93232 f x' s _39635)). Qed.
Lemma lem3633004 {_93229 _93232 : Type'} (f : _93232 -> _93229) (x' : _93229 -> _93232) (s : _93229 -> Prop) (_39635 : _93229) : (term128 _93229 _93232 s f x' _39635) = (term143 _93229 _93232 f x' s _39635).
Proof. exact (EQ_MP (@lem3633003 _93229 _93232 f x' s _39635) (@lem0)). Qed.
Lemma lem3633005 {_93229 _93232 : Type'} (_39635 : _93229) (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93229 -> _93232) (h1 : term107 _93229 _93232 s f t x') : term143 _93229 _93232 f x' s _39635.
Proof. exact (EQ_MP (@lem3633004 _93229 _93232 f x' s _39635) (@lem3632855 _93229 _93232 _39635 s f t x' h1)). Qed.
Lemma lem3633007 (b : Prop) (a : Prop) : (a \/ b) = (term136 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3633008 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (x' : _93229 -> _93232) (_39635 : _93229) : (term143 _93229 _93232 f x' s _39635) = (term146 _93229 _93232 s f x' _39635).
Proof. exact (@lem3633007 (term75 _93229 s _39635) (_39635 = (term122 _93229 _93232 f x' _39635))). Qed.
Lemma lem3633010 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3633011 {_93229 : Type'} (s : _93229 -> Prop) (_39635 : _93229) : (term138 _93229 s _39635) = (s _39635).
Proof. exact (@lem3633010 (s _39635)). Qed.
Lemma lem3633012 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3633013 {_93229 : Type'} (s : _93229 -> Prop) (_39635 : _93229) : (term139 _93229 s _39635) = (term14 _93229 s _39635).
Proof. exact (MK_COMB (@lem3633012) (@lem3633011 _93229 s _39635)). Qed.
Lemma lem3633014 {_93229 _93232 : Type'} (f : _93232 -> _93229) (x' : _93229 -> _93232) (_39635 : _93229) : (_39635 = (term122 _93229 _93232 f x' _39635)) = (_39635 = (term122 _93229 _93232 f x' _39635)).
Proof. exact (eq_refl (_39635 = (term122 _93229 _93232 f x' _39635))). Qed.
Lemma lem3633015 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (x' : _93229 -> _93232) (_39635 : _93229) : (term146 _93229 _93232 s f x' _39635) = (term147 _93229 _93232 s f x' _39635).
Proof. exact (MK_COMB (@lem3633013 _93229 s _39635) (@lem3633014 _93229 _93232 f x' _39635)). Qed.
Lemma lem3633016 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (x' : _93229 -> _93232) (_39635 : _93229) : (term143 _93229 _93232 f x' s _39635) = (term147 _93229 _93232 s f x' _39635).
Proof. exact (TRANS (@lem3633008 _93229 _93232 s f x' _39635) (@lem3633015 _93229 _93232 s f x' _39635)). Qed.
Lemma lem3633019 {_93229 _93232 : Type'} (_39635 : _93229) (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93229 -> _93232) (h1 : term107 _93229 _93232 s f t x') : term147 _93229 _93232 s f x' _39635.
Proof. exact (EQ_MP (@lem3633016 _93229 _93232 s f x' _39635) (@lem3633005 _93229 _93232 _39635 s f t x' h1)). Qed.
Lemma lem3633020 {_93229 _93232 : Type'} (_39635 : _93229) (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93229 -> _93232) (h1 : term107 _93229 _93232 s f t x') : term147 _93229 _93232 s f x' _39635.
Proof. exact (@lem3633019 _93229 _93232 _39635 s f t x' h1). Qed.
Lemma lem3633021 {_93229 _93232 : Type'} (x : _93229) (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93229 -> _93232) (h1 : term107 _93229 _93232 s f t x') : term147 _93229 _93232 s f x' x.
Proof. exact (@lem3633020 _93229 _93232 x s f t x' h1). Qed.
Lemma lem3633024 {_93229 _93232 : Type'} (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93229 -> _93232) (s : _93229 -> Prop) (x : _93229) (h1 : term107 _93229 _93232 s f t x') (h2 : s x) : x = (term122 _93229 _93232 f x' x).
Proof. exact (@lem3633021 _93229 _93232 x s f t x' h1 (@lem3632972 _93229 s x h2)). Qed.
Lemma lem3633025 {_93229 _93232 : Type'} (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93229 -> _93232) (s : _93229 -> Prop) (x : _93229) (h1 : term107 _93229 _93232 s f t x') (h2 : s x) : term148 _93229 _93232 f x' x.
Proof. exact (fun h0 : term149 _93229 _93232 f x' x => @lem3633024 _93229 _93232 f t x' s x h1 h2). Qed.
Lemma lem3633027 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3633028 {_93229 _93232 : Type'} (f : _93232 -> _93229) (x' : _93229 -> _93232) (x : _93229) : (term148 _93229 _93232 f x' x) = (x = (term122 _93229 _93232 f x' x)).
Proof. exact (@lem3633027 (x = (term122 _93229 _93232 f x' x))). Qed.
Lemma lem3633029 {_93229 _93232 : Type'} (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93229 -> _93232) (s : _93229 -> Prop) (x : _93229) (h1 : term107 _93229 _93232 s f t x') (h2 : s x) : x = (term122 _93229 _93232 f x' x).
Proof. exact (EQ_MP (@lem3633028 _93229 _93232 f x' x) (@lem3633025 _93229 _93232 f t x' s x h1 h2)). Qed.
Lemma lem3633031 {_93229 : Type'} (x : _93229) : x = x.
Proof. exact (@lem21386 _93229 x). Qed.
Lemma lem3633032 {_93229 : Type'} (x : _93229) : x = x.
Proof. exact (@lem3633031 _93229 x). Qed.
Lemma lem3633033 {_93229 : Type'} (x : _93229) : term150 _93229 x.
Proof. exact (fun h0 : term151 _93229 x => @lem3633032 _93229 x). Qed.
Lemma lem3633035 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3633036 {_93229 : Type'} (x : _93229) : (term150 _93229 x) = (x = x).
Proof. exact (@lem3633035 (x = x)). Qed.
Lemma lem3633037 {_93229 : Type'} (x : _93229) : x = x.
Proof. exact (EQ_MP (@lem3633036 _93229 x) (@lem3633033 _93229 x)). Qed.
Lemma lem3633055 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3633056 {_93229 : Type'} (y : _93229) (x : _93229) (z : _93229) : (term152 _93229 x y z) = (term153 _93229 y x z).
Proof. exact (@lem3633055 (y = z) (term154 _93229 x z)). Qed.
Lemma lem3633066 {_93229 : Type'} (x : _93229) (y : _93229) : (term155 _93229 x y) = (term155 _93229 x y).
Proof. exact (eq_refl (term155 _93229 x y)). Qed.
Lemma lem3633067 {_93229 : Type'} (y : _93229) (x : _93229) (z : _93229) : (term130 _93229 x y z) = (term156 _93229 y x z).
Proof. exact (MK_COMB (@lem3633066 _93229 x y) (@lem3633056 _93229 y x z)). Qed.
Lemma lem3633071 (q : Prop) (p : Prop) (r : Prop) : (term157 p q r) = (term157 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3633072 {_93229 : Type'} (y : _93229) (x : _93229) (z : _93229) : (term156 _93229 y x z) = (term158 _93229 y x z).
Proof. exact (@lem3633071 (y = z) (term154 _93229 x y) (term154 _93229 x z)). Qed.
Lemma lem3633094 {_93229 : Type'} (y : _93229) (x : _93229) (z : _93229) : (term130 _93229 x y z) = (term158 _93229 y x z).
Proof. exact (TRANS (@lem3633067 _93229 y x z) (@lem3633072 _93229 y x z)). Qed.
Lemma lem3633095 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3633096 {_93229 : Type'} (y : _93229) (x : _93229) (z : _93229) : (term159 _93229 x y z) = (term160 _93229 y x z).
Proof. exact (MK_COMB (@lem3633095) (@lem3633094 _93229 y x z)). Qed.
Lemma lem3633118 {_93229 : Type'} (y : _93229) (x : _93229) (z : _93229) : (term158 _93229 y x z) = (term158 _93229 y x z).
Proof. exact (eq_refl (term158 _93229 y x z)). Qed.
Lemma lem3633119 {_93229 : Type'} (y : _93229) (x : _93229) (z : _93229) : ((term130 _93229 x y z) = (term158 _93229 y x z)) = ((term158 _93229 y x z) = (term158 _93229 y x z)).
Proof. exact (MK_COMB (@lem3633096 _93229 y x z) (@lem3633118 _93229 y x z)). Qed.
Lemma lem3633121 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3633122 (x : Prop) : (x = x) = True.
Proof. exact (@lem3633121 Prop x). Qed.
Lemma lem3633123 {_93229 : Type'} (y : _93229) (x : _93229) (z : _93229) : ((term158 _93229 y x z) = (term158 _93229 y x z)) = True.
Proof. exact (@lem3633122 (term158 _93229 y x z)). Qed.
Lemma lem3633124 {_93229 : Type'} (y : _93229) (x : _93229) (z : _93229) : ((term130 _93229 x y z) = (term158 _93229 y x z)) = True.
Proof. exact (TRANS (@lem3633119 _93229 y x z) (@lem3633123 _93229 y x z)). Qed.
Lemma lem3633125 {_93229 : Type'} (y : _93229) (x : _93229) (z : _93229) : True = ((term130 _93229 x y z) = (term158 _93229 y x z)).
Proof. exact (SYM (@lem3633124 _93229 y x z)). Qed.
Lemma lem3633126 {_93229 : Type'} (y : _93229) (x : _93229) (z : _93229) : (term130 _93229 x y z) = (term158 _93229 y x z).
Proof. exact (EQ_MP (@lem3633125 _93229 y x z) (@lem0)). Qed.
Lemma lem3633127 {_93229 : Type'} (y : _93229) (x : _93229) (z : _93229) : term158 _93229 y x z.
Proof. exact (EQ_MP (@lem3633126 _93229 y x z) (@lem3632903 _93229 x y z)). Qed.
Lemma lem3633129 (b : Prop) (a : Prop) : (a \/ b) = (term136 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3633130 {_93229 : Type'} (x : _93229) (y : _93229) (z : _93229) : (term158 _93229 y x z) = (term161 _93229 x y z).
Proof. exact (@lem3633129 (term162 _93229 y x z) (y = z)). Qed.
Lemma lem3633132 (a : Prop) (b : Prop) : (term163 a b) = (term164 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3633133 {_93229 : Type'} (y : _93229) (x : _93229) (z : _93229) : (term165 _93229 y x z) = (term166 _93229 y x z).
Proof. exact (@lem3633132 (term154 _93229 x y) (term154 _93229 x z)). Qed.
Lemma lem3633135 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3633136 {_93229 : Type'} (x : _93229) (y : _93229) : (term167 _93229 x y) = (x = y).
Proof. exact (@lem3633135 (x = y)). Qed.
Lemma lem3633137 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3633138 {_93229 : Type'} (x : _93229) (y : _93229) : (term168 _93229 x y) = (term169 _93229 x y).
Proof. exact (MK_COMB (@lem3633137) (@lem3633136 _93229 x y)). Qed.
Lemma lem3633140 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3633141 {_93229 : Type'} (x : _93229) (z : _93229) : (term167 _93229 x z) = (x = z).
Proof. exact (@lem3633140 (x = z)). Qed.
Lemma lem3633142 {_93229 : Type'} (y : _93229) (x : _93229) (z : _93229) : (term166 _93229 y x z) = (term170 _93229 y x z).
Proof. exact (MK_COMB (@lem3633138 _93229 x y) (@lem3633141 _93229 x z)). Qed.
Lemma lem3633143 {_93229 : Type'} (y : _93229) (x : _93229) (z : _93229) : (term165 _93229 y x z) = (term170 _93229 y x z).
Proof. exact (TRANS (@lem3633133 _93229 y x z) (@lem3633142 _93229 y x z)). Qed.
Lemma lem3633144 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3633145 {_93229 : Type'} (y : _93229) (x : _93229) (z : _93229) : (term171 _93229 y x z) = (term172 _93229 y x z).
Proof. exact (MK_COMB (@lem3633144) (@lem3633143 _93229 y x z)). Qed.
Lemma lem3633146 {_93229 : Type'} (y : _93229) (z : _93229) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3633147 {_93229 : Type'} (x : _93229) (y : _93229) (z : _93229) : (term161 _93229 x y z) = (term173 _93229 x y z).
Proof. exact (MK_COMB (@lem3633145 _93229 y x z) (@lem3633146 _93229 y z)). Qed.
Lemma lem3633148 {_93229 : Type'} (x : _93229) (y : _93229) (z : _93229) : (term158 _93229 y x z) = (term173 _93229 x y z).
Proof. exact (TRANS (@lem3633130 _93229 x y z) (@lem3633147 _93229 x y z)). Qed.
Lemma lem3633150 {_93229 _93232 : Type'} (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93229 -> _93232) (s : _93229 -> Prop) (x : _93229) (h1 : term107 _93229 _93232 s f t x') (h2 : s x) : term174 _93229 _93232 f x' x.
Proof. exact (conj (@lem3633029 _93229 _93232 f t x' s x h1 h2) (@lem3633037 _93229 x)). Qed.
Lemma lem3633152 {_93229 : Type'} (x : _93229) (y : _93229) (z : _93229) : term173 _93229 x y z.
Proof. exact (EQ_MP (@lem3633148 _93229 x y z) (@lem3633127 _93229 y x z)). Qed.
Lemma lem3633153 {_93229 : Type'} (x : _93229) (y : _93229) (z : _93229) : term173 _93229 x y z.
Proof. exact (@lem3633152 _93229 x y z). Qed.
Lemma lem3633154 {_93229 _93232 : Type'} (f : _93232 -> _93229) (x' : _93229 -> _93232) (x : _93229) : term175 _93229 _93232 f x' x.
Proof. exact (@lem3633153 _93229 x (term122 _93229 _93232 f x' x) x). Qed.
Lemma lem3633157 {_93229 _93232 : Type'} (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93229 -> _93232) (s : _93229 -> Prop) (x : _93229) (h1 : term107 _93229 _93232 s f t x') (h2 : s x) : (term122 _93229 _93232 f x' x) = x.
Proof. exact (@lem3633154 _93229 _93232 f x' x (@lem3633150 _93229 _93232 f t x' s x h1 h2)). Qed.
Lemma lem3633158 {_93229 _93232 : Type'} (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93229 -> _93232) (s : _93229 -> Prop) (x : _93229) (h1 : term107 _93229 _93232 s f t x') (h2 : s x) : term176 _93229 _93232 f x' x.
Proof. exact (fun h0 : term177 _93229 _93232 f x' x => @lem3633157 _93229 _93232 f t x' s x h1 h2). Qed.
Lemma lem3633160 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3633161 {_93229 _93232 : Type'} (f : _93232 -> _93229) (x' : _93229 -> _93232) (x : _93229) : (term176 _93229 _93232 f x' x) = ((term122 _93229 _93232 f x' x) = x).
Proof. exact (@lem3633160 ((term122 _93229 _93232 f x' x) = x)). Qed.
Lemma lem3633162 {_93229 _93232 : Type'} (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93229 -> _93232) (s : _93229 -> Prop) (x : _93229) (h1 : term107 _93229 _93232 s f t x') (h2 : s x) : (term122 _93229 _93232 f x' x) = x.
Proof. exact (EQ_MP (@lem3633161 _93229 _93232 f x' x) (@lem3633158 _93229 _93232 f t x' s x h1 h2)). Qed.
Lemma lem3633164 (a : Prop) (b : Prop) : (term178 a b) = (term179 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3633165 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (_39634 : _93232) (x : _93229) : (term112 _93229 _93232 t f _39634 x) = (term111 _93229 _93232 t f _39634 x).
Proof. exact (@lem3633164 (t _39634) ((f _39634) = x)). Qed.
Lemma lem3633167 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3633168 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (_39634 : _93232) (x : _93229) : (term111 _93229 _93232 t f _39634 x) = (term180 _93229 _93232 t f _39634 x).
Proof. exact (@lem3633167 (term34 _93229 _93232 t f _39634 x)). Qed.
Lemma lem3633169 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (_39634 : _93232) (x : _93229) : (term112 _93229 _93232 t f _39634 x) = (term180 _93229 _93232 t f _39634 x).
Proof. exact (TRANS (@lem3633165 _93229 _93232 t f _39634 x) (@lem3633168 _93229 _93232 t f _39634 x)). Qed.
Lemma lem3633171 {_93229 _93232 : Type'} (f : _93232 -> _93229) (t : _93232 -> Prop) (x' : _93229 -> _93232) (s : _93229 -> Prop) (x : _93229) (h1 : term107 _93229 _93232 s f t x') (h2 : s x) : term181 _93229 _93232 t f x' x.
Proof. exact (conj (@lem3632965 _93229 _93232 f t x' s x h1 h2) (@lem3633162 _93229 _93232 f t x' s x h1 h2)). Qed.
Lemma lem3633173 {_93229 _93232 : Type'} (_39634 : _93232) (t : _93232 -> Prop) (f : _93232 -> _93229) (x : _93229) (h1 : term66 _93229 _93232 t f x) : term180 _93229 _93232 t f _39634 x.
Proof. exact (EQ_MP (@lem3633169 _93229 _93232 t f _39634 x) (@lem3632849 _93229 _93232 _39634 t f x h1)). Qed.
Lemma lem3633174 {_93229 _93232 : Type'} (_39634 : _93232) (t : _93232 -> Prop) (f : _93232 -> _93229) (x : _93229) (h1 : term66 _93229 _93232 t f x) : term180 _93229 _93232 t f _39634 x.
Proof. exact (@lem3633173 _93229 _93232 _39634 t f x h1). Qed.
Lemma lem3633175 {_93229 _93232 : Type'} (x' : _93229 -> _93232) (t : _93232 -> Prop) (f : _93232 -> _93229) (x : _93229) (h1 : term66 _93229 _93232 t f x) : term182 _93229 _93232 t f x' x.
Proof. exact (@lem3633174 _93229 _93232 (x' x) t f x h1). Qed.
Lemma lem3633178 {_93229 _93232 : Type'} (x' : _93229 -> _93232) (t : _93232 -> Prop) (f : _93232 -> _93229) (s : _93229 -> Prop) (x : _93229) (h1 : term107 _93229 _93232 s f t x') (h2 : term66 _93229 _93232 t f x) (h3 : s x) : False.
Proof. exact (@lem3633175 _93229 _93232 x' t f x h2 (@lem3633171 _93229 _93232 f t x' s x h1 h3)). Qed.
Lemma lem3633179 {_93229 _93232 : Type'} (x' : _93229 -> _93232) (t : _93232 -> Prop) (f : _93232 -> _93229) (s : _93229 -> Prop) (x : _93229) (h1 : term107 _93229 _93232 s f t x') (h2 : term66 _93229 _93232 t f x) (h3 : s x) : term183.
Proof. exact (fun h0 : ~ False => @lem3633178 _93229 _93232 x' t f s x h1 h2 h3). Qed.
Lemma lem3633181 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3633182 : term183 = False.
Proof. exact (@lem3633181 False). Qed.
Lemma lem3633183 {_93229 _93232 : Type'} (x' : _93229 -> _93232) (t : _93232 -> Prop) (f : _93232 -> _93229) (s : _93229 -> Prop) (x : _93229) (h1 : term107 _93229 _93232 s f t x') (h2 : term66 _93229 _93232 t f x) (h3 : s x) : False.
Proof. exact (EQ_MP (@lem3633182) (@lem3633179 _93229 _93232 x' t f s x h1 h2 h3)). Qed.
Lemma lem3633184 {_93229 _93232 : Type'} (x' : _93229 -> _93232) (t : _93232 -> Prop) (f : _93232 -> _93229) (s : _93229 -> Prop) (x : _93229) (h1 : term107 _93229 _93232 s f t x') (h2 : term66 _93229 _93232 t f x) (h3 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3633183 _93229 _93232 x' t f s x h1 h2 h3) (fun h4 : False => @lem3632843 _93229 s x h3)). Qed.
Lemma lem3633185 {_93229 _93232 : Type'} (x' : _93229 -> _93232) (t : _93232 -> Prop) (f : _93232 -> _93229) (s : _93229 -> Prop) (x : _93229) (h1 : term107 _93229 _93232 s f t x') (h2 : term66 _93229 _93232 t f x) (h3 : s x) : False.
Proof. exact (EQ_MP (@lem3633184 _93229 _93232 x' t f s x h1 h2 h3) (@lem3632843 _93229 s x h3)). Qed.
Lemma lem3633186 {_93229 _93232 : Type'} (x' : _93229 -> _93232) (t : _93232 -> Prop) (f : _93232 -> _93229) (s : _93229 -> Prop) (x : _93229) (h1 : term107 _93229 _93232 s f t x') (h2 : term66 _93229 _93232 t f x) (h3 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3633185 _93229 _93232 x' t f s x h1 h2 h3) (fun h4 : False => @lem3632797 _93229 s x h3)). Qed.
Lemma lem3633187 {_93229 _93232 : Type'} (x' : _93229 -> _93232) (t : _93232 -> Prop) (f : _93232 -> _93229) (s : _93229 -> Prop) (x : _93229) (h1 : term107 _93229 _93232 s f t x') (h2 : term66 _93229 _93232 t f x) (h3 : s x) : False.
Proof. exact (EQ_MP (@lem3633186 _93229 _93232 x' t f s x h1 h2 h3) (@lem3632797 _93229 s x h3)). Qed.
Lemma lem3633188 {_93229 _93232 : Type'} (x' : _93229 -> _93232) (t : _93232 -> Prop) (f : _93232 -> _93229) (s : _93229 -> Prop) (x : _93229) (h1 : term107 _93229 _93232 s f t x') (h2 : term66 _93229 _93232 t f x) (h3 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3633187 _93229 _93232 x' t f s x h1 h2 h3) (fun h4 : False => @lem3632797 _93229 s x h3)). Qed.
Lemma lem3633189 {_93229 _93232 : Type'} (x' : _93229 -> _93232) (t : _93232 -> Prop) (f : _93232 -> _93229) (s : _93229 -> Prop) (x : _93229) (h1 : term107 _93229 _93232 s f t x') (h2 : term66 _93229 _93232 t f x) (h3 : s x) : False.
Proof. exact (EQ_MP (@lem3633188 _93229 _93232 x' t f s x h1 h2 h3) (@lem3632797 _93229 s x h3)). Qed.
Lemma lem3633190 {_93229 _93232 : Type'} (x' : _93229 -> _93232) (t : _93232 -> Prop) (f : _93232 -> _93229) (s : _93229 -> Prop) (x : _93229) (h1 : term107 _93229 _93232 s f t x') (h2 : term66 _93229 _93232 t f x) (h3 : s x) : (term107 _93229 _93232 s f t x') = False.
Proof. exact (prop_ext (fun h4 : term107 _93229 _93232 s f t x' => @lem3633189 _93229 _93232 x' t f s x h1 h2 h3) (fun h4 : False => @lem3632793 _93229 _93232 s f t x' h1)). Qed.
Lemma lem3633191 {_93229 _93232 : Type'} (x' : _93229 -> _93232) (t : _93232 -> Prop) (f : _93232 -> _93229) (s : _93229 -> Prop) (x : _93229) (h1 : term107 _93229 _93232 s f t x') (h2 : term66 _93229 _93232 t f x) (h3 : s x) : False.
Proof. exact (EQ_MP (@lem3633190 _93229 _93232 x' t f s x h1 h2 h3) (@lem3632793 _93229 _93232 s f t x' h1)). Qed.
Lemma lem3633192 {_93229 _93232 : Type'} (x' : _93229 -> _93232) (t : _93232 -> Prop) (f : _93232 -> _93229) (s : _93229 -> Prop) (x : _93229) (h1 : term107 _93229 _93232 s f t x') (h2 : term66 _93229 _93232 t f x) (h3 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3633191 _93229 _93232 x' t f s x h1 h2 h3) (fun h4 : False => @lem3632743 _93229 s x h3)). Qed.
Lemma lem3633193 {_93229 _93232 : Type'} (x' : _93229 -> _93232) (t : _93232 -> Prop) (f : _93232 -> _93229) (s : _93229 -> Prop) (x : _93229) (h1 : term107 _93229 _93232 s f t x') (h2 : term66 _93229 _93232 t f x) (h3 : s x) : False.
Proof. exact (EQ_MP (@lem3633192 _93229 _93232 x' t f s x h1 h2 h3) (@lem3632743 _93229 s x h3)). Qed.
Lemma lem3633194 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (s : _93229 -> Prop) (x : _93229) (h1 : term29 _93229 _93232 s f t) (h2 : term66 _93229 _93232 t f x) (h3 : s x) : False.
Proof. exact (ex_elim (@lem3632662 _93229 _93232 s f t h1) (fun x' : _93229 -> _93232 => fun h0 : term109 _93229 _93232 s f t x' => @lem3633193 _93229 _93232 x' t f s x h0 h2 h3)). Qed.
Lemma lem3633195 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (s : _93229 -> Prop) (x : _93229) (h1 : term29 _93229 _93232 s f t) (h2 : term66 _93229 _93232 t f x) (h3 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3633194 _93229 _93232 t f s x h1 h2 h3) (fun h4 : False => @lem3632668 _93229 s x h3)). Qed.
Lemma lem3633196 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (s : _93229 -> Prop) (x : _93229) (h1 : term29 _93229 _93232 s f t) (h2 : term66 _93229 _93232 t f x) (h3 : s x) : False.
Proof. exact (EQ_MP (@lem3633195 _93229 _93232 t f s x h1 h2 h3) (@lem3632668 _93229 s x h3)). Qed.
Lemma lem3633197 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (s : _93229 -> Prop) (x : _93229) (h1 : term29 _93229 _93232 s f t) (h2 : term66 _93229 _93232 t f x) (h3 : s x) : (term66 _93229 _93232 t f x) = False.
Proof. exact (prop_ext (fun h4 : term66 _93229 _93232 t f x => @lem3633196 _93229 _93232 t f s x h1 h2 h3) (fun h4 : False => @lem3632507 _93229 _93232 t f x h2)). Qed.
Lemma lem3633198 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (s : _93229 -> Prop) (x : _93229) (h1 : term29 _93229 _93232 s f t) (h2 : term66 _93229 _93232 t f x) (h3 : s x) : False.
Proof. exact (EQ_MP (@lem3633197 _93229 _93232 t f s x h1 h2 h3) (@lem3632507 _93229 _93232 t f x h2)). Qed.
Lemma lem3633199 {_93229 _93232 : Type'} (f : _93232 -> _93229) (t : _93232 -> Prop) (s : _93229 -> Prop) (x : _93229) (h1 : term29 _93229 _93232 s f t) (h2 : s x) : term65 _93229 _93232 t f x.
Proof. exact (fun h0 : term66 _93229 _93232 t f x => @lem3633198 _93229 _93232 t f s x h1 h0 h2). Qed.
Lemma lem3633200 {_93229 _93232 : Type'} (f : _93232 -> _93229) (t : _93232 -> Prop) (s : _93229 -> Prop) (x : _93229) (h1 : term29 _93229 _93232 s f t) (h2 : s x) : term38 _93229 _93232 t f x.
Proof. exact (EQ_MP (@lem3632506 _93229 _93232 t f x) (@lem3633199 _93229 _93232 f t s x h1 h2)). Qed.
Lemma lem3633201 {_93229 _93232 : Type'} (x : _93229) (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) (h1 : term29 _93229 _93232 s f t) : term40 _93229 _93232 s t f x.
Proof. exact (fun h0 : s x => @lem3633200 _93229 _93232 f t s x h1 h0). Qed.
Lemma lem3633206 {_93229 _93232 : Type'} (s : _93229 -> Prop) (f : _93232 -> _93229) (t : _93232 -> Prop) (h1 : term29 _93229 _93232 s f t) : term43 _93229 _93232 s t f.
Proof. exact (fun x : _93229 => @lem3633201 _93229 _93232 x s f t h1). Qed.
Lemma lem3633207 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) : term44 _93229 _93232 s t f.
Proof. exact (fun h0 : term29 _93229 _93232 s f t => @lem3633206 _93229 _93232 s f t h0). Qed.
Lemma lem3633212 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) : term56 _93229 _93232 t f.
Proof. exact (fun s : _93229 -> Prop => @lem3633207 _93229 _93232 s t f). Qed.
Lemma lem3633217 {_93229 _93232 : Type'} (f : _93232 -> _93229) : term60 _93229 _93232 f.
Proof. exact (fun t : _93232 -> Prop => @lem3633212 _93229 _93232 t f). Qed.
Lemma lem3633222 {_93229 _93232 : Type'} : term64 _93229 _93232.
Proof. exact (fun f : _93232 -> _93229 => @lem3633217 _93229 _93232 f). Qed.
Lemma lem3633223 {_93229 _93232 : Type'} : term63 _93229 _93232.
Proof. exact (EQ_MP (@lem3632500 _93229 _93232) (@lem3633222 _93229 _93232)). Qed.
Lemma lem3633224 {_93229 _93232 : Type'} (f : _93232 -> _93229) : term184 _93229 _93232 f.
Proof. exact (@lem3633223 _93229 _93232 f). Qed.
Lemma lem3633225 {_93229 _93232 : Type'} (f : _93232 -> _93229) : (term184 _93229 _93232 f) = (term59 _93229 _93232 f).
Proof. exact (eq_refl (term184 _93229 _93232 f)). Qed.
Lemma lem3633226 {_93229 _93232 : Type'} (f : _93232 -> _93229) : term59 _93229 _93232 f.
Proof. exact (EQ_MP (@lem3633225 _93229 _93232 f) (@lem3633224 _93229 _93232 f)). Qed.
Lemma lem3633227 {_93229 _93232 : Type'} (f : _93232 -> _93229) (t : _93232 -> Prop) : term185 _93229 _93232 f t.
Proof. exact (@lem3633226 _93229 _93232 f t). Qed.
Lemma lem3633228 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) : (term185 _93229 _93232 f t) = (term55 _93229 _93232 t f).
Proof. exact (eq_refl (term185 _93229 _93232 f t)). Qed.
Lemma lem3633229 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) : term55 _93229 _93232 t f.
Proof. exact (EQ_MP (@lem3633228 _93229 _93232 t f) (@lem3633227 _93229 _93232 f t)). Qed.
Lemma lem3633230 {_93229 _93232 : Type'} (t : _93232 -> Prop) (f : _93232 -> _93229) (s : _93229 -> Prop) : term186 _93229 _93232 t f s.
Proof. exact (@lem3633229 _93229 _93232 t f s). Qed.
Lemma lem3633231 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) : (term186 _93229 _93232 t f s) = (term46 _93229 _93232 s t f).
Proof. exact (eq_refl (term186 _93229 _93232 t f s)). Qed.
Lemma lem3633232 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) : term46 _93229 _93232 s t f.
Proof. exact (EQ_MP (@lem3633231 _93229 _93232 s t f) (@lem3633230 _93229 _93232 t f s)). Qed.
Lemma lem3633234 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) : term46 _93229 _93232 s t f.
Proof. exact (@lem3632280 _93229 _93232 s t f (@lem3633232 _93229 _93232 s t f)). Qed.
Lemma lem3633235 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) (h1 : term47 _93229 _93232 s t f) : False.
Proof. exact (@lem3633234 _93229 _93232 s t f (@lem3632264 _93229 _93232 s t f h1)). Qed.
Lemma lem3633236 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) (h1 : term47 _93229 _93232 s t f) : (term47 _93229 _93232 s t f) = False.
Proof. exact (prop_ext (fun h2 : term47 _93229 _93232 s t f => @lem3633235 _93229 _93232 s t f h1) (fun h2 : False => @lem3632264 _93229 _93232 s t f h1)). Qed.
Lemma lem3633237 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) (h1 : term47 _93229 _93232 s t f) : False.
Proof. exact (EQ_MP (@lem3633236 _93229 _93232 s t f h1) (@lem3632264 _93229 _93232 s t f h1)). Qed.
Lemma lem3633238 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) : term46 _93229 _93232 s t f.
Proof. exact (fun h0 : term47 _93229 _93232 s t f => @lem3633237 _93229 _93232 s t f h0). Qed.
Lemma lem3633239 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) : term44 _93229 _93232 s t f.
Proof. exact (EQ_MP (@lem3632263 _93229 _93232 s t f) (@lem3633238 _93229 _93232 s t f)). Qed.
Lemma lem3633240 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) : term12 _93229 _93232 s t f.
Proof. exact (EQ_MP (@lem3632259 _93229 _93232 s t f) (@lem3633239 _93229 _93232 s t f)). Qed.
Lemma lem3633253 (p : Prop) : p = (term45 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3633254 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term187 A B s f t) = (term188 A B s f t).
Proof. exact (@lem3633253 (term187 A B s f t)). Qed.
Lemma lem3633255 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term188 A B s f t) = (term187 A B s f t).
Proof. exact (SYM (@lem3633254 A B s f t)). Qed.
Lemma lem3633256 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term189 A B s f t) : term189 A B s f t.
Proof. exact (h1). Qed.
Lemma lem3633257 {_87604 A : Type'} : term190 _87604 A.
Proof. exact (@lem3371475 A _87604). Qed.
Lemma lem3633258 {_87604 B : Type'} : term190 _87604 B.
Proof. exact (@lem3371475 B _87604). Qed.
Lemma lem3633259 {_87593 A : Type'} : term191 _87593 A.
Proof. exact (@lem3371475 _87593 A). Qed.
Lemma lem3633260 {_87593 B : Type'} : term191 _87593 B.
Proof. exact (@lem3371475 _87593 B). Qed.
Lemma lem3633261 {A B : Type'} : term191 A B.
Proof. exact (@lem3371475 A B). Qed.
Lemma lem3633264 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term192 _87593 _87604 A B s f t) : term192 _87593 _87604 A B s f t.
Proof. exact (h1). Qed.
Lemma lem3633265 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : term193 _87593 _87604 A B s f t.
Proof. exact (fun h0 : term192 _87593 _87604 A B s f t => @lem3633264 _87593 _87604 A B s f t h0). Qed.
Lemma lem3633266 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term193 _87593 _87604 A B s f t) : term193 _87593 _87604 A B s f t.
Proof. exact (h1). Qed.
Lemma lem3633267 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term192 _87593 _87604 A B s f t) : term192 _87593 _87604 A B s f t.
Proof. exact (h1). Qed.
Lemma lem3633268 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term192 _87593 _87604 A B s f t) (h2 : term193 _87593 _87604 A B s f t) : term192 _87593 _87604 A B s f t.
Proof. exact (@lem3633266 _87593 _87604 A B s f t h2 (@lem3633267 _87593 _87604 A B s f t h1)). Qed.
Lemma lem3633269 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term192 _87593 _87604 A B s f t) : term194 _87593 _87604 A B s f t.
Proof. exact (fun h0 : term193 _87593 _87604 A B s f t => @lem3633268 _87593 _87604 A B s f t h1 h0). Qed.
Lemma lem3633270 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term193 _87593 _87604 A B s f t) : term193 _87593 _87604 A B s f t.
Proof. exact (h1). Qed.
Lemma lem3633271 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term192 _87593 _87604 A B s f t) (h2 : term193 _87593 _87604 A B s f t) : term192 _87593 _87604 A B s f t.
Proof. exact (@lem3633269 _87593 _87604 A B s f t h1 (@lem3633270 _87593 _87604 A B s f t h2)). Qed.
Lemma lem3633272 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term193 _87593 _87604 A B s f t) : term193 _87593 _87604 A B s f t.
Proof. exact (fun h0 : term192 _87593 _87604 A B s f t => @lem3633271 _87593 _87604 A B s f t h0 h1). Qed.
Lemma lem3633273 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : term195 _87593 _87604 A B s f t.
Proof. exact (fun h0 : term193 _87593 _87604 A B s f t => @lem3633272 _87593 _87604 A B s f t h0). Qed.
Lemma lem3633276 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : term193 _87593 _87604 A B s f t.
Proof. exact (@lem3633273 _87593 _87604 A B s f t (@lem3633265 _87593 _87604 A B s f t)). Qed.
Lemma lem3633277 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : term193 _87593 _87604 A B s f t.
Proof. exact (@lem3633276 _87593 _87604 A B s f t). Qed.
Lemma lem3633423 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3633424 {_87604 B : Type'} : (term196 _87604 B) = (term197 _87604 B).
Proof. exact (@lem3633423 (term190 _87604 B)). Qed.
Lemma lem3633439 {A B : Type'} : (term198 A B) = (term198 A B).
Proof. exact (eq_refl (term198 A B)). Qed.
Lemma lem3633440 {_87604 A B : Type'} : (term199 _87604 A B) = (term200 _87604 A B).
Proof. exact (MK_COMB (@lem3633439 A B) (@lem3633424 _87604 B)). Qed.
Lemma lem3633443 {_87604 A : Type'} : (term201 _87604 A) = (term201 _87604 A).
Proof. exact (eq_refl (term201 _87604 A)). Qed.
Lemma lem3633444 {_87604 A B : Type'} : (term202 _87604 A B) = (term203 _87604 A B).
Proof. exact (MK_COMB (@lem3633443 _87604 A) (@lem3633440 _87604 A B)). Qed.
Lemma lem3633447 {_87593 B : Type'} : (term198 _87593 B) = (term198 _87593 B).
Proof. exact (eq_refl (term198 _87593 B)). Qed.
Lemma lem3633448 {_87593 _87604 A B : Type'} : (term204 _87593 _87604 A B) = (term205 _87593 _87604 A B).
Proof. exact (MK_COMB (@lem3633447 _87593 B) (@lem3633444 _87604 A B)). Qed.
Lemma lem3633451 {_87593 A : Type'} : (term198 _87593 A) = (term198 _87593 A).
Proof. exact (eq_refl (term198 _87593 A)). Qed.
Lemma lem3633452 {_87593 _87604 A B : Type'} : (term206 _87593 _87604 A B) = (term207 _87593 _87604 A B).
Proof. exact (MK_COMB (@lem3633451 _87593 A) (@lem3633448 _87593 _87604 A B)). Qed.
Lemma lem3633455 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term208 A B s f t) = (term208 A B s f t).
Proof. exact (eq_refl (term208 A B s f t)). Qed.
Lemma lem3633456 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term192 _87593 _87604 A B s f t) = (term209 _87593 _87604 A B s f t).
Proof. exact (MK_COMB (@lem3633455 A B s f t) (@lem3633452 _87593 _87604 A B)). Qed.
Lemma lem3633459 {_87593 _87604 A B : Type'} (f : A -> B) (t : A -> Prop) : (term210 _87593 _87604 A B f t) = (term211 _87593 _87604 A B f t).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3633456 _87593 _87604 A B s f t)). Qed.
Lemma lem3633460 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3633461 {_87593 _87604 A B : Type'} (f : A -> B) (t : A -> Prop) : (term212 _87593 _87604 A B f t) = (term213 _87593 _87604 A B f t).
Proof. exact (MK_COMB (@lem3633460 B) (@lem3633459 _87593 _87604 A B f t)). Qed.
Lemma lem3633466 {_87593 _87604 A B : Type'} (t : A -> Prop) : (term214 _87593 _87604 A B t) = (term215 _87593 _87604 A B t).
Proof. exact (fun_ext (fun f : A -> B => @lem3633461 _87593 _87604 A B f t)). Qed.
Lemma lem3633467 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3633468 {_87593 _87604 A B : Type'} (t : A -> Prop) : (term216 _87593 _87604 A B t) = (term217 _87593 _87604 A B t).
Proof. exact (MK_COMB (@lem3633467 A B) (@lem3633466 _87593 _87604 A B t)). Qed.
Lemma lem3633473 {_87593 _87604 A B : Type'} : (term218 _87593 _87604 A B) = (term219 _87593 _87604 A B).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3633468 _87593 _87604 A B t)). Qed.
Lemma lem3633474 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3633483 {_87593 _87604 A B : Type'} : (term220 _87593 _87604 A B) = (term221 _87593 _87604 A B).
Proof. exact (MK_COMB (@lem3633474 A) (@lem3633473 _87593 _87604 A B)). Qed.
Lemma lem3633488 {_87604 B : Type'} (s : B -> Prop) (f : B -> _87604) (t : B -> Prop) : (term222 _87604 B s f t) = (term222 _87604 B s f t).
Proof. exact (eq_refl (term222 _87604 B s f t)). Qed.
Lemma lem3633489 {_87604 B : Type'} (s : B -> Prop) (f : B -> _87604) : (term223 _87604 B s f) = (term223 _87604 B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3633488 _87604 B s f t)). Qed.
Lemma lem3633490 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3633491 {_87604 B : Type'} (s : B -> Prop) (f : B -> _87604) : (term224 _87604 B s f) = (term224 _87604 B s f).
Proof. exact (MK_COMB (@lem3633490 B) (@lem3633489 _87604 B s f)). Qed.
Lemma lem3633492 {_87604 B : Type'} (f : B -> _87604) : (term225 _87604 B f) = (term225 _87604 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3633491 _87604 B s f)). Qed.
Lemma lem3633493 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3633494 {_87604 B : Type'} (f : B -> _87604) : (term226 _87604 B f) = (term226 _87604 B f).
Proof. exact (MK_COMB (@lem3633493 B) (@lem3633492 _87604 B f)). Qed.
Lemma lem3633495 {_87604 B : Type'} : (term227 _87604 B) = (term227 _87604 B).
Proof. exact (fun_ext (fun f : B -> _87604 => @lem3633494 _87604 B f)). Qed.
Lemma lem3633496 {_87604 B : Type'} : (@all (B -> _87604)) = (@all (B -> _87604)).
Proof. exact (eq_refl (@all (B -> _87604))). Qed.
Lemma lem3633497 {_87604 B : Type'} : (term190 _87604 B) = (term190 _87604 B).
Proof. exact (MK_COMB (@lem3633496 _87604 B) (@lem3633495 _87604 B)). Qed.
Lemma lem3633498 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3633499 {_87604 B : Type'} : (term197 _87604 B) = (term197 _87604 B).
Proof. exact (MK_COMB (@lem3633498) (@lem3633497 _87604 B)). Qed.
Lemma lem3633504 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term228 A B s f t) = (term228 A B s f t).
Proof. exact (eq_refl (term228 A B s f t)). Qed.
Lemma lem3633505 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term229 A B s f) = (term229 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3633504 A B s f t)). Qed.
Lemma lem3633506 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3633507 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term230 A B s f) = (term230 A B s f).
Proof. exact (MK_COMB (@lem3633506 A) (@lem3633505 A B s f)). Qed.
Lemma lem3633508 {A B : Type'} (f : A -> B) : (term231 A B f) = (term231 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3633507 A B s f)). Qed.
Lemma lem3633509 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3633510 {A B : Type'} (f : A -> B) : (term232 A B f) = (term232 A B f).
Proof. exact (MK_COMB (@lem3633509 A) (@lem3633508 A B f)). Qed.
Lemma lem3633511 {A B : Type'} : (term233 A B) = (term233 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3633510 A B f)). Qed.
Lemma lem3633512 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3633513 {A B : Type'} : (term191 A B) = (term191 A B).
Proof. exact (MK_COMB (@lem3633512 A B) (@lem3633511 A B)). Qed.
Lemma lem3633514 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3633515 {A B : Type'} : (term198 A B) = (term198 A B).
Proof. exact (MK_COMB (@lem3633514) (@lem3633513 A B)). Qed.
Lemma lem3633516 {_87604 A B : Type'} : (term200 _87604 A B) = (term200 _87604 A B).
Proof. exact (MK_COMB (@lem3633515 A B) (@lem3633499 _87604 B)). Qed.
Lemma lem3633521 {_87604 A : Type'} (s : A -> Prop) (f : A -> _87604) (t : A -> Prop) : (term222 _87604 A s f t) = (term222 _87604 A s f t).
Proof. exact (eq_refl (term222 _87604 A s f t)). Qed.
Lemma lem3633522 {_87604 A : Type'} (s : A -> Prop) (f : A -> _87604) : (term223 _87604 A s f) = (term223 _87604 A s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3633521 _87604 A s f t)). Qed.
Lemma lem3633523 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3633524 {_87604 A : Type'} (s : A -> Prop) (f : A -> _87604) : (term224 _87604 A s f) = (term224 _87604 A s f).
Proof. exact (MK_COMB (@lem3633523 A) (@lem3633522 _87604 A s f)). Qed.
Lemma lem3633525 {_87604 A : Type'} (f : A -> _87604) : (term225 _87604 A f) = (term225 _87604 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3633524 _87604 A s f)). Qed.
Lemma lem3633526 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3633527 {_87604 A : Type'} (f : A -> _87604) : (term226 _87604 A f) = (term226 _87604 A f).
Proof. exact (MK_COMB (@lem3633526 A) (@lem3633525 _87604 A f)). Qed.
Lemma lem3633528 {_87604 A : Type'} : (term227 _87604 A) = (term227 _87604 A).
Proof. exact (fun_ext (fun f : A -> _87604 => @lem3633527 _87604 A f)). Qed.
Lemma lem3633529 {_87604 A : Type'} : (@all (A -> _87604)) = (@all (A -> _87604)).
Proof. exact (eq_refl (@all (A -> _87604))). Qed.
Lemma lem3633530 {_87604 A : Type'} : (term190 _87604 A) = (term190 _87604 A).
Proof. exact (MK_COMB (@lem3633529 _87604 A) (@lem3633528 _87604 A)). Qed.
Lemma lem3633531 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3633532 {_87604 A : Type'} : (term201 _87604 A) = (term201 _87604 A).
Proof. exact (MK_COMB (@lem3633531) (@lem3633530 _87604 A)). Qed.
Lemma lem3633533 {_87604 A B : Type'} : (term203 _87604 A B) = (term203 _87604 A B).
Proof. exact (MK_COMB (@lem3633532 _87604 A) (@lem3633516 _87604 A B)). Qed.
Lemma lem3633538 {_87593 B : Type'} (s : _87593 -> Prop) (f : _87593 -> B) (t : _87593 -> Prop) : (term228 _87593 B s f t) = (term228 _87593 B s f t).
Proof. exact (eq_refl (term228 _87593 B s f t)). Qed.
Lemma lem3633539 {_87593 B : Type'} (s : _87593 -> Prop) (f : _87593 -> B) : (term229 _87593 B s f) = (term229 _87593 B s f).
Proof. exact (fun_ext (fun t : _87593 -> Prop => @lem3633538 _87593 B s f t)). Qed.
Lemma lem3633540 {_87593 : Type'} : (@all (_87593 -> Prop)) = (@all (_87593 -> Prop)).
Proof. exact (eq_refl (@all (_87593 -> Prop))). Qed.
Lemma lem3633541 {_87593 B : Type'} (s : _87593 -> Prop) (f : _87593 -> B) : (term230 _87593 B s f) = (term230 _87593 B s f).
Proof. exact (MK_COMB (@lem3633540 _87593) (@lem3633539 _87593 B s f)). Qed.
Lemma lem3633542 {_87593 B : Type'} (f : _87593 -> B) : (term231 _87593 B f) = (term231 _87593 B f).
Proof. exact (fun_ext (fun s : _87593 -> Prop => @lem3633541 _87593 B s f)). Qed.
Lemma lem3633543 {_87593 : Type'} : (@all (_87593 -> Prop)) = (@all (_87593 -> Prop)).
Proof. exact (eq_refl (@all (_87593 -> Prop))). Qed.
Lemma lem3633544 {_87593 B : Type'} (f : _87593 -> B) : (term232 _87593 B f) = (term232 _87593 B f).
Proof. exact (MK_COMB (@lem3633543 _87593) (@lem3633542 _87593 B f)). Qed.
Lemma lem3633545 {_87593 B : Type'} : (term233 _87593 B) = (term233 _87593 B).
Proof. exact (fun_ext (fun f : _87593 -> B => @lem3633544 _87593 B f)). Qed.
Lemma lem3633546 {_87593 B : Type'} : (@all (_87593 -> B)) = (@all (_87593 -> B)).
Proof. exact (eq_refl (@all (_87593 -> B))). Qed.
Lemma lem3633547 {_87593 B : Type'} : (term191 _87593 B) = (term191 _87593 B).
Proof. exact (MK_COMB (@lem3633546 _87593 B) (@lem3633545 _87593 B)). Qed.
Lemma lem3633548 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3633549 {_87593 B : Type'} : (term198 _87593 B) = (term198 _87593 B).
Proof. exact (MK_COMB (@lem3633548) (@lem3633547 _87593 B)). Qed.
Lemma lem3633550 {_87593 _87604 A B : Type'} : (term205 _87593 _87604 A B) = (term205 _87593 _87604 A B).
Proof. exact (MK_COMB (@lem3633549 _87593 B) (@lem3633533 _87604 A B)). Qed.
Lemma lem3633555 {_87593 A : Type'} (s : _87593 -> Prop) (f : _87593 -> A) (t : _87593 -> Prop) : (term228 _87593 A s f t) = (term228 _87593 A s f t).
Proof. exact (eq_refl (term228 _87593 A s f t)). Qed.
Lemma lem3633556 {_87593 A : Type'} (s : _87593 -> Prop) (f : _87593 -> A) : (term229 _87593 A s f) = (term229 _87593 A s f).
Proof. exact (fun_ext (fun t : _87593 -> Prop => @lem3633555 _87593 A s f t)). Qed.
Lemma lem3633557 {_87593 : Type'} : (@all (_87593 -> Prop)) = (@all (_87593 -> Prop)).
Proof. exact (eq_refl (@all (_87593 -> Prop))). Qed.
Lemma lem3633558 {_87593 A : Type'} (s : _87593 -> Prop) (f : _87593 -> A) : (term230 _87593 A s f) = (term230 _87593 A s f).
Proof. exact (MK_COMB (@lem3633557 _87593) (@lem3633556 _87593 A s f)). Qed.
Lemma lem3633559 {_87593 A : Type'} (f : _87593 -> A) : (term231 _87593 A f) = (term231 _87593 A f).
Proof. exact (fun_ext (fun s : _87593 -> Prop => @lem3633558 _87593 A s f)). Qed.
Lemma lem3633560 {_87593 : Type'} : (@all (_87593 -> Prop)) = (@all (_87593 -> Prop)).
Proof. exact (eq_refl (@all (_87593 -> Prop))). Qed.
Lemma lem3633561 {_87593 A : Type'} (f : _87593 -> A) : (term232 _87593 A f) = (term232 _87593 A f).
Proof. exact (MK_COMB (@lem3633560 _87593) (@lem3633559 _87593 A f)). Qed.
Lemma lem3633562 {_87593 A : Type'} : (term233 _87593 A) = (term233 _87593 A).
Proof. exact (fun_ext (fun f : _87593 -> A => @lem3633561 _87593 A f)). Qed.
Lemma lem3633563 {_87593 A : Type'} : (@all (_87593 -> A)) = (@all (_87593 -> A)).
Proof. exact (eq_refl (@all (_87593 -> A))). Qed.
Lemma lem3633564 {_87593 A : Type'} : (term191 _87593 A) = (term191 _87593 A).
Proof. exact (MK_COMB (@lem3633563 _87593 A) (@lem3633562 _87593 A)). Qed.
Lemma lem3633565 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3633566 {_87593 A : Type'} : (term198 _87593 A) = (term198 _87593 A).
Proof. exact (MK_COMB (@lem3633565) (@lem3633564 _87593 A)). Qed.
Lemma lem3633567 {_87593 _87604 A B : Type'} : (term207 _87593 _87604 A B) = (term207 _87593 _87604 A B).
Proof. exact (MK_COMB (@lem3633566 _87593 A) (@lem3633550 _87593 _87604 A B)). Qed.
Lemma lem3633568 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term234 A B s f t) = (term234 A B s f t).
Proof. exact (eq_refl (term234 A B s f t)). Qed.
Lemma lem3633569 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (s = (@IMAGE A B f u)) = (s = (@IMAGE A B f u)).
Proof. exact (eq_refl (s = (@IMAGE A B f u))). Qed.
Lemma lem3633582 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : A) : (term235 A B u f x y) = (term235 A B u f x y).
Proof. exact (eq_refl (term235 A B u f x y)). Qed.
Lemma lem3633583 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) : (term236 A B u f x) = (term236 A B u f x).
Proof. exact (fun_ext (fun y : A => @lem3633582 A B u f x y)). Qed.
Lemma lem3633584 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3633585 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) : (term237 A B u f x) = (term237 A B u f x).
Proof. exact (MK_COMB (@lem3633584 A) (@lem3633583 A B u f x)). Qed.
Lemma lem3633586 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term238 A B u f) = (term238 A B u f).
Proof. exact (fun_ext (fun x : A => @lem3633585 A B u f x)). Qed.
Lemma lem3633587 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3633588 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term239 A B u f) = (term239 A B u f).
Proof. exact (MK_COMB (@lem3633587 A) (@lem3633586 A B u f)). Qed.
Lemma lem3633589 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3633590 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term240 A B u f) = (term240 A B u f).
Proof. exact (MK_COMB (@lem3633589) (@lem3633588 A B u f)). Qed.
Lemma lem3633591 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term241 A B s f u) = (term241 A B s f u).
Proof. exact (MK_COMB (@lem3633590 A B u f) (@lem3633569 A B s f u)). Qed.
Lemma lem3633594 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term242 A u t) = (term242 A u t).
Proof. exact (eq_refl (term242 A u t)). Qed.
Lemma lem3633595 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term243 A B t s f u) = (term243 A B t s f u).
Proof. exact (MK_COMB (@lem3633594 A u t) (@lem3633591 A B s f u)). Qed.
Lemma lem3633596 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term244 A B t s f) = (term244 A B t s f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3633595 A B t s f u)). Qed.
Lemma lem3633597 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3633598 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term245 A B t s f) = (term245 A B t s f).
Proof. exact (MK_COMB (@lem3633597 A) (@lem3633596 A B t s f)). Qed.
Lemma lem3633599 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3633600 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term246 A B t s f) = (term246 A B t s f).
Proof. exact (MK_COMB (@lem3633599) (@lem3633598 A B t s f)). Qed.
Lemma lem3633601 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term187 A B s f t) = (term187 A B s f t).
Proof. exact (MK_COMB (@lem3633600 A B t s f) (@lem3633568 A B s f t)). Qed.
Lemma lem3633602 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3633603 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term189 A B s f t) = (term189 A B s f t).
Proof. exact (MK_COMB (@lem3633602) (@lem3633601 A B s f t)). Qed.
Lemma lem3633604 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3633605 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term208 A B s f t) = (term208 A B s f t).
Proof. exact (MK_COMB (@lem3633604) (@lem3633603 A B s f t)). Qed.
Lemma lem3633606 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term209 _87593 _87604 A B s f t) = (term209 _87593 _87604 A B s f t).
Proof. exact (MK_COMB (@lem3633605 A B s f t) (@lem3633567 _87593 _87604 A B)). Qed.
Lemma lem3633607 {_87593 _87604 A B : Type'} (f : A -> B) (t : A -> Prop) : (term211 _87593 _87604 A B f t) = (term211 _87593 _87604 A B f t).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3633606 _87593 _87604 A B s f t)). Qed.
Lemma lem3633608 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3633609 {_87593 _87604 A B : Type'} (f : A -> B) (t : A -> Prop) : (term213 _87593 _87604 A B f t) = (term213 _87593 _87604 A B f t).
Proof. exact (MK_COMB (@lem3633608 B) (@lem3633607 _87593 _87604 A B f t)). Qed.
Lemma lem3633610 {_87593 _87604 A B : Type'} (t : A -> Prop) : (term215 _87593 _87604 A B t) = (term215 _87593 _87604 A B t).
Proof. exact (fun_ext (fun f : A -> B => @lem3633609 _87593 _87604 A B f t)). Qed.
Lemma lem3633611 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3633612 {_87593 _87604 A B : Type'} (t : A -> Prop) : (term217 _87593 _87604 A B t) = (term217 _87593 _87604 A B t).
Proof. exact (MK_COMB (@lem3633611 A B) (@lem3633610 _87593 _87604 A B t)). Qed.
Lemma lem3633613 {_87593 _87604 A B : Type'} : (term219 _87593 _87604 A B) = (term219 _87593 _87604 A B).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3633612 _87593 _87604 A B t)). Qed.
Lemma lem3633614 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3633615 {_87593 _87604 A B : Type'} : (term221 _87593 _87604 A B) = (term221 _87593 _87604 A B).
Proof. exact (MK_COMB (@lem3633614 A) (@lem3633613 _87593 _87604 A B)). Qed.
Lemma lem3633774 {_87593 _87604 A B : Type'} : (term220 _87593 _87604 A B) = (term221 _87593 _87604 A B).
Proof. exact (TRANS (@lem3633483 _87593 _87604 A B) (@lem3633615 _87593 _87604 A B)). Qed.
Lemma lem3633775 {_87593 _87604 A B : Type'} : (term221 _87593 _87604 A B) = (term220 _87593 _87604 A B).
Proof. exact (SYM (@lem3633774 _87593 _87604 A B)). Qed.
Lemma lem3633776 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term189 A B s f t) : term189 A B s f t.
Proof. exact (h1). Qed.
Lemma lem3633780 {A B : Type'} (h1 : term191 A B) : term191 A B.
Proof. exact (h1). Qed.
Lemma lem3633789 {A : Type'} (x : A) (y : A) (u : A -> Prop) : (term247 A x y u) = (term248 A x y u).
Proof. exact (@lem17045 (@IN A x u) (@IN A y u)). Qed.
Lemma lem3633804 {A B : Type'} (f : A -> B) (x : A) (y : A) : (((f x) = (f y)) = (x = y)) = (term249 A B f x y).
Proof. exact (@lem17784 ((f x) = (f y)) (x = y)). Qed.
Lemma lem3633805 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3633806 {A : Type'} (x : A) (y : A) (u : A -> Prop) : (term250 A x y u) = (term251 A x y u).
Proof. exact (MK_COMB (@lem3633805) (@lem3633789 A x y u)). Qed.
Lemma lem3633807 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : A) : (term252 A B u f x y) = (term253 A B u f x y).
Proof. exact (MK_COMB (@lem3633806 A x y u) (@lem3633804 A B f x y)). Qed.
Lemma lem3633808 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : A) : (term235 A B u f x y) = (term252 A B u f x y).
Proof. exact (@lem17265 (term254 A x y u) (((f x) = (f y)) = (x = y))). Qed.
Lemma lem3633809 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : A) : (term235 A B u f x y) = (term253 A B u f x y).
Proof. exact (TRANS (@lem3633808 A B u f x y) (@lem3633807 A B u f x y)). Qed.
Lemma lem3633810 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) : (term236 A B u f x) = (term255 A B u f x).
Proof. exact (fun_ext (fun y : A => @lem3633809 A B u f x y)). Qed.
Lemma lem3633811 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3633812 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) : (term237 A B u f x) = (term256 A B u f x).
Proof. exact (MK_COMB (@lem3633811 A) (@lem3633810 A B u f x)). Qed.
Lemma lem3633813 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term238 A B u f) = (term257 A B u f).
Proof. exact (fun_ext (fun x : A => @lem3633812 A B u f x)). Qed.
Lemma lem3633814 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3633815 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term239 A B u f) = (term258 A B u f).
Proof. exact (MK_COMB (@lem3633814 A) (@lem3633813 A B u f)). Qed.
Lemma lem3633816 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (s = (@IMAGE A B f u)) = (s = (@IMAGE A B f u)).
Proof. exact (eq_refl (s = (@IMAGE A B f u))). Qed.
Lemma lem3633817 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3633818 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term240 A B u f) = (term259 A B u f).
Proof. exact (MK_COMB (@lem3633817) (@lem3633815 A B u f)). Qed.
Lemma lem3633819 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term241 A B s f u) = (term260 A B s f u).
Proof. exact (MK_COMB (@lem3633818 A B u f) (@lem3633816 A B s f u)). Qed.
Lemma lem3633821 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term242 A u t) = (term242 A u t).
Proof. exact (eq_refl (term242 A u t)). Qed.
Lemma lem3633822 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term243 A B t s f u) = (term261 A B t s f u).
Proof. exact (MK_COMB (@lem3633821 A u t) (@lem3633819 A B s f u)). Qed.
Lemma lem3633823 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term244 A B t s f) = (term262 A B t s f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3633822 A B t s f u)). Qed.
Lemma lem3633824 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3633825 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term245 A B t s f) = (term263 A B t s f).
Proof. exact (MK_COMB (@lem3633824 A) (@lem3633823 A B t s f)). Qed.
Lemma lem3633826 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term264 A B s f t) = (term264 A B s f t).
Proof. exact (eq_refl (term264 A B s f t)). Qed.
Lemma lem3633827 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3633828 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term265 A B t s f) = (term266 A B t s f).
Proof. exact (MK_COMB (@lem3633827) (@lem3633825 A B t s f)). Qed.
Lemma lem3633829 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term267 A B s f t) = (term268 A B s f t).
Proof. exact (MK_COMB (@lem3633828 A B t s f) (@lem3633826 A B s f t)). Qed.
Lemma lem3633830 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term189 A B s f t) = (term267 A B s f t).
Proof. exact (@lem17362 (term245 A B t s f) (term234 A B s f t)). Qed.
Lemma lem3633831 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term189 A B s f t) = (term268 A B s f t).
Proof. exact (TRANS (@lem3633830 A B s f t) (@lem3633829 A B s f t)). Qed.
Lemma lem3633934 {A : Type'} (P : A -> Prop) (Q : Prop) : (term269 A P Q) = (term270 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3633935 {A : Type'} (P : type686 A) (Q : Prop) : (term271 A P Q) = (term272 A P Q).
Proof. exact (@lem3633934 (A -> Prop) P Q). Qed.
Lemma lem3633936 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term273 A B s f t) = (term274 A B s f t).
Proof. exact (@lem3633935 A (term262 A B t s f) (term264 A B s f t)). Qed.
Lemma lem3633937 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term275 A B t s f u) = (term261 A B t s f u).
Proof. exact (eq_refl (term275 A B t s f u)). Qed.
Lemma lem3633938 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term276 A B t s f) = (term262 A B t s f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3633937 A B t s f u)). Qed.
Lemma lem3633939 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3633940 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term277 A B t s f) = (term263 A B t s f).
Proof. exact (MK_COMB (@lem3633939 A) (@lem3633938 A B t s f)). Qed.
Lemma lem3633941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3633942 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term278 A B t s f) = (term266 A B t s f).
Proof. exact (MK_COMB (@lem3633941) (@lem3633940 A B t s f)). Qed.
Lemma lem3633943 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term264 A B s f t) = (term264 A B s f t).
Proof. exact (eq_refl (term264 A B s f t)). Qed.
Lemma lem3633944 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term273 A B s f t) = (term268 A B s f t).
Proof. exact (MK_COMB (@lem3633942 A B t s f) (@lem3633943 A B s f t)). Qed.
Lemma lem3633945 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3633946 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term279 A B s f t) = (term280 A B s f t).
Proof. exact (MK_COMB (@lem3633945) (@lem3633944 A B s f t)). Qed.
Lemma lem3633947 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term275 A B t s f u) = (term261 A B t s f u).
Proof. exact (eq_refl (term275 A B t s f u)). Qed.
Lemma lem3633948 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3633949 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term281 A B t s f u) = (term282 A B t s f u).
Proof. exact (MK_COMB (@lem3633948) (@lem3633947 A B t s f u)). Qed.
Lemma lem3633950 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term264 A B s f t) = (term264 A B s f t).
Proof. exact (eq_refl (term264 A B s f t)). Qed.
Lemma lem3633951 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term283 A B u s f t) = (term284 A B u s f t).
Proof. exact (MK_COMB (@lem3633949 A B t s f u) (@lem3633950 A B s f t)). Qed.
Lemma lem3633952 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term285 A B s f t) = (term286 A B s f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3633951 A B u s f t)). Qed.
Lemma lem3633953 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3633954 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term274 A B s f t) = (term287 A B s f t).
Proof. exact (MK_COMB (@lem3633953 A) (@lem3633952 A B s f t)). Qed.
Lemma lem3633955 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : ((term273 A B s f t) = (term274 A B s f t)) = ((term268 A B s f t) = (term287 A B s f t)).
Proof. exact (MK_COMB (@lem3633946 A B s f t) (@lem3633954 A B s f t)). Qed.
Lemma lem3633957 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term268 A B s f t) = (term287 A B s f t).
Proof. exact (EQ_MP (@lem3633955 A B s f t) (@lem3633936 A B s f t)). Qed.
Lemma lem3633958 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term189 A B s f t) = (term287 A B s f t).
Proof. exact (TRANS (@lem3633831 A B s f t) (@lem3633957 A B s f t)). Qed.
Lemma lem3633959 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term189 A B s f t) : term287 A B s f t.
Proof. exact (EQ_MP (@lem3633958 A B s f t) (@lem3633776 A B s f t h1)). Qed.
Lemma lem3634197 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term228 A B s f t) = (term288 A B s f t).
Proof. exact (@lem17265 (@SUBSET A s t) (term289 A B s f t)). Qed.
Lemma lem3634198 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term229 A B s f) = (term290 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3634197 A B s f t)). Qed.
Lemma lem3634199 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3634200 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term230 A B s f) = (term291 A B s f).
Proof. exact (MK_COMB (@lem3634199 A) (@lem3634198 A B s f)). Qed.
Lemma lem3634201 {A B : Type'} (f : A -> B) : (term231 A B f) = (term292 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3634200 A B s f)). Qed.
Lemma lem3634202 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3634203 {A B : Type'} (f : A -> B) : (term232 A B f) = (term293 A B f).
Proof. exact (MK_COMB (@lem3634202 A) (@lem3634201 A B f)). Qed.
Lemma lem3634204 {A B : Type'} : (term233 A B) = (term294 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3634203 A B f)). Qed.
Lemma lem3634205 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3634266 {A B : Type'} : (term191 A B) = (term295 A B).
Proof. exact (MK_COMB (@lem3634205 A B) (@lem3634204 A B)). Qed.
Lemma lem3634267 {A B : Type'} (h1 : term191 A B) : term295 A B.
Proof. exact (EQ_MP (@lem3634266 A B) (@lem3633780 A B h1)). Qed.
Lemma lem3634345 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term284 A B u s f t) : term284 A B u s f t.
Proof. exact (h1). Qed.
Lemma lem3634467 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term288 A B s f t) = (term288 A B s f t).
Proof. exact (eq_refl (term288 A B s f t)). Qed.
Lemma lem3634468 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term290 A B s f) = (term290 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3634467 A B s f t)). Qed.
Lemma lem3634469 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3634470 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term291 A B s f) = (term291 A B s f).
Proof. exact (MK_COMB (@lem3634469 A) (@lem3634468 A B s f)). Qed.
Lemma lem3634471 {A B : Type'} (f : A -> B) : (term292 A B f) = (term292 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3634470 A B s f)). Qed.
Lemma lem3634472 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3634473 {A B : Type'} (f : A -> B) : (term293 A B f) = (term293 A B f).
Proof. exact (MK_COMB (@lem3634472 A) (@lem3634471 A B f)). Qed.
Lemma lem3634474 {A B : Type'} : (term294 A B) = (term294 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3634473 A B f)). Qed.
Lemma lem3634475 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3634476 {A B : Type'} : (term295 A B) = (term295 A B).
Proof. exact (MK_COMB (@lem3634475 A B) (@lem3634474 A B)). Qed.
Lemma lem3634477 {A B : Type'} (h1 : term191 A B) : term295 A B.
Proof. exact (EQ_MP (@lem3634476 A B) (@lem3634267 A B h1)). Qed.
Lemma lem3634521 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term264 A B s f t) = (term264 A B s f t).
Proof. exact (eq_refl (term264 A B s f t)). Qed.
Lemma lem3634530 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (s = (@IMAGE A B f u)) = (s = (@IMAGE A B f u)).
Proof. exact (eq_refl (s = (@IMAGE A B f u))). Qed.
Lemma lem3634535 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem3634536 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3634537 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem3634542 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3634544 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem3634542 A B f x). Qed.
Lemma lem3634549 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3634550 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem3634549 A B f x). Qed.
Lemma lem3634552 {A B : Type'} (f : A -> B) (y : A) : (f y) = (@I (A -> B) f y).
Proof. exact (@lem3634550 A B f y). Qed.
Lemma lem3634553 {A B : Type'} (f : A -> B) (x : A) : (term296 A B f x) = (term297 A B f x).
Proof. exact (MK_COMB (@lem3634537 B) (@lem3634544 A B f x)). Qed.
Lemma lem3634554 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((@I (A -> B) f x) = (@I (A -> B) f y)).
Proof. exact (MK_COMB (@lem3634553 A B f x) (@lem3634552 A B f y)). Qed.
Lemma lem3634555 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term298 A B x f y) = (term299 A B x f y).
Proof. exact (MK_COMB (@lem3634536) (@lem3634554 A B x f y)). Qed.
Lemma lem3634556 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3634557 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term300 A B x f y) = (term301 A B x f y).
Proof. exact (MK_COMB (@lem3634556) (@lem3634555 A B x f y)). Qed.
Lemma lem3634558 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term302 A B f x y) = (term303 A B f x y).
Proof. exact (MK_COMB (@lem3634557 A B x f y) (@lem3634535 A x y)). Qed.
Lemma lem3634565 {A : Type'} (x : A) (y : A) : (term154 A x y) = (term154 A x y).
Proof. exact (eq_refl (term154 A x y)). Qed.
Lemma lem3634566 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem3634571 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3634573 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem3634571 A B f x). Qed.
Lemma lem3634578 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3634579 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem3634578 A B f x). Qed.
Lemma lem3634581 {A B : Type'} (f : A -> B) (y : A) : (f y) = (@I (A -> B) f y).
Proof. exact (@lem3634579 A B f y). Qed.
Lemma lem3634582 {A B : Type'} (f : A -> B) (x : A) : (term296 A B f x) = (term297 A B f x).
Proof. exact (MK_COMB (@lem3634566 B) (@lem3634573 A B f x)). Qed.
Lemma lem3634583 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((@I (A -> B) f x) = (@I (A -> B) f y)).
Proof. exact (MK_COMB (@lem3634582 A B f x) (@lem3634581 A B f y)). Qed.
Lemma lem3634584 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3634585 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term304 A B x f y) = (term305 A B x f y).
Proof. exact (MK_COMB (@lem3634584) (@lem3634583 A B x f y)). Qed.
Lemma lem3634586 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term306 A B f x y) = (term307 A B f x y).
Proof. exact (MK_COMB (@lem3634585 A B x f y) (@lem3634565 A x y)). Qed.
Lemma lem3634587 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3634588 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term308 A B f x y) = (term309 A B f x y).
Proof. exact (MK_COMB (@lem3634587) (@lem3634586 A B f x y)). Qed.
Lemma lem3634589 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term249 A B f x y) = (term310 A B f x y).
Proof. exact (MK_COMB (@lem3634588 A B f x y) (@lem3634558 A B f x y)). Qed.
Lemma lem3634608 {A : Type'} (x : A) (y : A) (u : A -> Prop) : (term251 A x y u) = (term251 A x y u).
Proof. exact (eq_refl (term251 A x y u)). Qed.
Lemma lem3634609 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : A) : (term253 A B u f x y) = (term311 A B u f x y).
Proof. exact (MK_COMB (@lem3634608 A x y u) (@lem3634589 A B f x y)). Qed.
Lemma lem3634610 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) : (term255 A B u f x) = (term312 A B u f x).
Proof. exact (fun_ext (fun y : A => @lem3634609 A B u f x y)). Qed.
Lemma lem3634611 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3634612 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) : (term256 A B u f x) = (term313 A B u f x).
Proof. exact (MK_COMB (@lem3634611 A) (@lem3634610 A B u f x)). Qed.
Lemma lem3634613 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term257 A B u f) = (term314 A B u f).
Proof. exact (fun_ext (fun x : A => @lem3634612 A B u f x)). Qed.
Lemma lem3634614 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3634615 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term258 A B u f) = (term315 A B u f).
Proof. exact (MK_COMB (@lem3634614 A) (@lem3634613 A B u f)). Qed.
Lemma lem3634616 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3634617 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term259 A B u f) = (term316 A B u f).
Proof. exact (MK_COMB (@lem3634616) (@lem3634615 A B u f)). Qed.
Lemma lem3634618 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term260 A B s f u) = (term317 A B s f u).
Proof. exact (MK_COMB (@lem3634617 A B u f) (@lem3634530 A B s f u)). Qed.
Lemma lem3634625 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term242 A u t) = (term242 A u t).
Proof. exact (eq_refl (term242 A u t)). Qed.
Lemma lem3634626 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term261 A B t s f u) = (term318 A B t s f u).
Proof. exact (MK_COMB (@lem3634625 A u t) (@lem3634618 A B s f u)). Qed.
Lemma lem3634627 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3634628 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term282 A B t s f u) = (term319 A B t s f u).
Proof. exact (MK_COMB (@lem3634627) (@lem3634626 A B t s f u)). Qed.
Lemma lem3634629 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term284 A B u s f t) = (term320 A B u s f t).
Proof. exact (MK_COMB (@lem3634628 A B t s f u) (@lem3634521 A B s f t)). Qed.
Lemma lem3634630 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term284 A B u s f t) : term320 A B u s f t.
Proof. exact (EQ_MP (@lem3634629 A B u s f t) (@lem3634345 A B u s f t h1)). Qed.
Lemma lem3634632 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term284 A B u s f t) : term318 A B t s f u.
Proof. exact (proj1 (@lem3634630 A B u s f t h1)). Qed.
Lemma lem3634633 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term284 A B u s f t) : term317 A B s f u.
Proof. exact (proj2 (@lem3634632 A B u s f t h1)). Qed.
Lemma lem3634701 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term288 A B s f t) = (term288 A B s f t).
Proof. exact (eq_refl (term288 A B s f t)). Qed.
Lemma lem3634702 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term290 A B s f) = (term290 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3634701 A B s f t)). Qed.
Lemma lem3634703 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3634704 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term291 A B s f) = (term291 A B s f).
Proof. exact (MK_COMB (@lem3634703 A) (@lem3634702 A B s f)). Qed.
Lemma lem3634705 {A B : Type'} (f : A -> B) : (term292 A B f) = (term292 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3634704 A B s f)). Qed.
Lemma lem3634706 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3634707 {A B : Type'} (f : A -> B) : (term293 A B f) = (term293 A B f).
Proof. exact (MK_COMB (@lem3634706 A) (@lem3634705 A B f)). Qed.
Lemma lem3634708 {A B : Type'} : (term294 A B) = (term294 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3634707 A B f)). Qed.
Lemma lem3634709 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3634711 {A B : Type'} : (term295 A B) = (term295 A B).
Proof. exact (MK_COMB (@lem3634709 A B) (@lem3634708 A B)). Qed.
Lemma lem3634712 {A B : Type'} (h1 : term191 A B) : term295 A B.
Proof. exact (EQ_MP (@lem3634711 A B) (@lem3634477 A B h1)). Qed.
Lemma lem3634815 {A B : Type'} (_39653 : A -> B) (h1 : term191 A B) : term321 A B _39653.
Proof. exact (@lem3634712 A B h1 _39653). Qed.
Lemma lem3634816 {A B : Type'} (_39653 : A -> B) : (term321 A B _39653) = (term293 A B _39653).
Proof. exact (eq_refl (term321 A B _39653)). Qed.
Lemma lem3634817 {A B : Type'} (_39653 : A -> B) (h1 : term191 A B) : term293 A B _39653.
Proof. exact (EQ_MP (@lem3634816 A B _39653) (@lem3634815 A B _39653 h1)). Qed.
Lemma lem3634818 {A B : Type'} (_39653 : A -> B) (_39654 : A -> Prop) (h1 : term191 A B) : term322 A B _39653 _39654.
Proof. exact (@lem3634817 A B _39653 h1 _39654). Qed.
Lemma lem3634819 {A B : Type'} (_39654 : A -> Prop) (_39653 : A -> B) : (term322 A B _39653 _39654) = (term291 A B _39654 _39653).
Proof. exact (eq_refl (term322 A B _39653 _39654)). Qed.
Lemma lem3634820 {A B : Type'} (_39654 : A -> Prop) (_39653 : A -> B) (h1 : term191 A B) : term291 A B _39654 _39653.
Proof. exact (EQ_MP (@lem3634819 A B _39654 _39653) (@lem3634818 A B _39653 _39654 h1)). Qed.
Lemma lem3634821 {A B : Type'} (_39654 : A -> Prop) (_39653 : A -> B) (_39655 : A -> Prop) (h1 : term191 A B) : term323 A B _39654 _39653 _39655.
Proof. exact (@lem3634820 A B _39654 _39653 h1 _39655). Qed.
Lemma lem3634822 {A B : Type'} (_39654 : A -> Prop) (_39653 : A -> B) (_39655 : A -> Prop) : (term323 A B _39654 _39653 _39655) = (term288 A B _39654 _39653 _39655).
Proof. exact (eq_refl (term323 A B _39654 _39653 _39655)). Qed.
Lemma lem3634872 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term284 A B u s f t) : term264 A B s f t.
Proof. exact (proj2 (@lem3634630 A B u s f t h1)). Qed.
Lemma lem3634876 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term284 A B u s f t) : s = (@IMAGE A B f u).
Proof. exact (proj2 (@lem3634633 A B u s f t h1)). Qed.
Lemma lem3634978 {A B : Type'} (_39654 : A -> Prop) (_39653 : A -> B) (_39655 : A -> Prop) (h1 : term191 A B) : term288 A B _39654 _39653 _39655.
Proof. exact (EQ_MP (@lem3634822 A B _39654 _39653 _39655) (@lem3634821 A B _39654 _39653 _39655 h1)). Qed.
Lemma lem3634993 {A B : Type'} (f : A -> B) (t : A -> Prop) : (term324 A B f t) = (term324 A B f t).
Proof. exact (eq_refl (term324 A B f t)). Qed.
Lemma lem3634994 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term284 A B u s f t) : (term325 A B f t s) = (term326 A B t f u).
Proof. exact (MK_COMB (@lem3634993 A B f t) (@lem3634876 A B u s f t h1)). Qed.
Lemma lem3634995 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term326 A B t f u) = (term327 A B u f t).
Proof. exact (eq_refl (term326 A B t f u)). Qed.
Lemma lem3634996 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : B -> Prop) : (term328 A B f t s) = (term328 A B f t s).
Proof. exact (eq_refl (term328 A B f t s)). Qed.
Lemma lem3634997 {A B : Type'} (s : B -> Prop) (u : A -> Prop) (f : A -> B) (t : A -> Prop) : ((term325 A B f t s) = (term326 A B t f u)) = ((term325 A B f t s) = (term327 A B u f t)).
Proof. exact (MK_COMB (@lem3634996 A B f t s) (@lem3634995 A B u f t)). Qed.
Lemma lem3634998 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term325 A B f t s) = (term264 A B s f t).
Proof. exact (eq_refl (term325 A B f t s)). Qed.
Lemma lem3634999 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3635000 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term328 A B f t s) = (term329 A B s f t).
Proof. exact (MK_COMB (@lem3634999) (@lem3634998 A B s f t)). Qed.
Lemma lem3635001 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term327 A B u f t) = (term327 A B u f t).
Proof. exact (eq_refl (term327 A B u f t)). Qed.
Lemma lem3635002 {A B : Type'} (s : B -> Prop) (u : A -> Prop) (f : A -> B) (t : A -> Prop) : ((term325 A B f t s) = (term327 A B u f t)) = ((term264 A B s f t) = (term327 A B u f t)).
Proof. exact (MK_COMB (@lem3635000 A B s f t) (@lem3635001 A B u f t)). Qed.
Lemma lem3635003 {A B : Type'} (s : B -> Prop) (u : A -> Prop) (f : A -> B) (t : A -> Prop) : ((term325 A B f t s) = (term326 A B t f u)) = ((term264 A B s f t) = (term327 A B u f t)).
Proof. exact (TRANS (@lem3634997 A B s u f t) (@lem3635002 A B s u f t)). Qed.
Lemma lem3635004 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term284 A B u s f t) : (term264 A B s f t) = (term327 A B u f t).
Proof. exact (EQ_MP (@lem3635003 A B s u f t) (@lem3634994 A B u s f t h1)). Qed.
Lemma lem3635005 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term284 A B u s f t) : term327 A B u f t.
Proof. exact (EQ_MP (@lem3635004 A B u s f t h1) (@lem3634872 A B u s f t h1)). Qed.
Lemma lem3635256 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term284 A B u s f t) : @SUBSET A u t.
Proof. exact (proj1 (@lem3634632 A B u s f t h1)). Qed.
Lemma lem3635257 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term284 A B u s f t) : term330 A u t.
Proof. exact (fun h0 : term331 A u t => @lem3635256 A B u s f t h1). Qed.
Lemma lem3635259 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3635260 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term330 A u t) = (@SUBSET A u t).
Proof. exact (@lem3635259 (@SUBSET A u t)). Qed.
Lemma lem3635261 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term284 A B u s f t) : @SUBSET A u t.
Proof. exact (EQ_MP (@lem3635260 A u t) (@lem3635257 A B u s f t h1)). Qed.
Lemma lem3635267 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3635268 {A B : Type'} (_39653 : A -> B) (_39654 : A -> Prop) (_39655 : A -> Prop) : (term288 A B _39654 _39653 _39655) = (term332 A B _39653 _39654 _39655).
Proof. exact (@lem3635267 (term289 A B _39654 _39653 _39655) (term331 A _39654 _39655)). Qed.
Lemma lem3635274 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3635275 {A B : Type'} (_39653 : A -> B) (_39654 : A -> Prop) (_39655 : A -> Prop) : (term333 A B _39654 _39653 _39655) = (term334 A B _39653 _39654 _39655).
Proof. exact (MK_COMB (@lem3635274) (@lem3635268 A B _39653 _39654 _39655)). Qed.
Lemma lem3635281 {A B : Type'} (_39653 : A -> B) (_39654 : A -> Prop) (_39655 : A -> Prop) : (term332 A B _39653 _39654 _39655) = (term332 A B _39653 _39654 _39655).
Proof. exact (eq_refl (term332 A B _39653 _39654 _39655)). Qed.
Lemma lem3635282 {A B : Type'} (_39653 : A -> B) (_39654 : A -> Prop) (_39655 : A -> Prop) : ((term288 A B _39654 _39653 _39655) = (term332 A B _39653 _39654 _39655)) = ((term332 A B _39653 _39654 _39655) = (term332 A B _39653 _39654 _39655)).
Proof. exact (MK_COMB (@lem3635275 A B _39653 _39654 _39655) (@lem3635281 A B _39653 _39654 _39655)). Qed.
Lemma lem3635284 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3635285 (x : Prop) : (x = x) = True.
Proof. exact (@lem3635284 Prop x). Qed.
Lemma lem3635286 {A B : Type'} (_39653 : A -> B) (_39654 : A -> Prop) (_39655 : A -> Prop) : ((term332 A B _39653 _39654 _39655) = (term332 A B _39653 _39654 _39655)) = True.
Proof. exact (@lem3635285 (term332 A B _39653 _39654 _39655)). Qed.
Lemma lem3635287 {A B : Type'} (_39653 : A -> B) (_39654 : A -> Prop) (_39655 : A -> Prop) : ((term288 A B _39654 _39653 _39655) = (term332 A B _39653 _39654 _39655)) = True.
Proof. exact (TRANS (@lem3635282 A B _39653 _39654 _39655) (@lem3635286 A B _39653 _39654 _39655)). Qed.
Lemma lem3635288 {A B : Type'} (_39653 : A -> B) (_39654 : A -> Prop) (_39655 : A -> Prop) : True = ((term288 A B _39654 _39653 _39655) = (term332 A B _39653 _39654 _39655)).
Proof. exact (SYM (@lem3635287 A B _39653 _39654 _39655)). Qed.
Lemma lem3635289 {A B : Type'} (_39653 : A -> B) (_39654 : A -> Prop) (_39655 : A -> Prop) : (term288 A B _39654 _39653 _39655) = (term332 A B _39653 _39654 _39655).
Proof. exact (EQ_MP (@lem3635288 A B _39653 _39654 _39655) (@lem0)). Qed.
Lemma lem3635290 {A B : Type'} (_39653 : A -> B) (_39654 : A -> Prop) (_39655 : A -> Prop) (h1 : term191 A B) : term332 A B _39653 _39654 _39655.
Proof. exact (EQ_MP (@lem3635289 A B _39653 _39654 _39655) (@lem3634978 A B _39654 _39653 _39655 h1)). Qed.
Lemma lem3635292 (b : Prop) (a : Prop) : (a \/ b) = (term136 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3635293 {A B : Type'} (_39654 : A -> Prop) (_39653 : A -> B) (_39655 : A -> Prop) : (term332 A B _39653 _39654 _39655) = (term335 A B _39654 _39653 _39655).
Proof. exact (@lem3635292 (term331 A _39654 _39655) (term289 A B _39654 _39653 _39655)). Qed.
Lemma lem3635295 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3635296 {A : Type'} (_39654 : A -> Prop) (_39655 : A -> Prop) : (term336 A _39654 _39655) = (@SUBSET A _39654 _39655).
Proof. exact (@lem3635295 (@SUBSET A _39654 _39655)). Qed.
Lemma lem3635297 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3635298 {A : Type'} (_39654 : A -> Prop) (_39655 : A -> Prop) : (term337 A _39654 _39655) = (term338 A _39654 _39655).
Proof. exact (MK_COMB (@lem3635297) (@lem3635296 A _39654 _39655)). Qed.
Lemma lem3635299 {A B : Type'} (_39654 : A -> Prop) (_39653 : A -> B) (_39655 : A -> Prop) : (term289 A B _39654 _39653 _39655) = (term289 A B _39654 _39653 _39655).
Proof. exact (eq_refl (term289 A B _39654 _39653 _39655)). Qed.
Lemma lem3635300 {A B : Type'} (_39654 : A -> Prop) (_39653 : A -> B) (_39655 : A -> Prop) : (term335 A B _39654 _39653 _39655) = (term228 A B _39654 _39653 _39655).
Proof. exact (MK_COMB (@lem3635298 A _39654 _39655) (@lem3635299 A B _39654 _39653 _39655)). Qed.
Lemma lem3635301 {A B : Type'} (_39654 : A -> Prop) (_39653 : A -> B) (_39655 : A -> Prop) : (term332 A B _39653 _39654 _39655) = (term228 A B _39654 _39653 _39655).
Proof. exact (TRANS (@lem3635293 A B _39654 _39653 _39655) (@lem3635300 A B _39654 _39653 _39655)). Qed.
Lemma lem3635304 {A B : Type'} (_39654 : A -> Prop) (_39653 : A -> B) (_39655 : A -> Prop) (h1 : term191 A B) : term228 A B _39654 _39653 _39655.
Proof. exact (EQ_MP (@lem3635301 A B _39654 _39653 _39655) (@lem3635290 A B _39653 _39654 _39655 h1)). Qed.
Lemma lem3635305 {A B : Type'} (_39654 : A -> Prop) (_39653 : A -> B) (_39655 : A -> Prop) (h1 : term191 A B) : term228 A B _39654 _39653 _39655.
Proof. exact (@lem3635304 A B _39654 _39653 _39655 h1). Qed.
Lemma lem3635306 {A B : Type'} (u : A -> Prop) (_39653 : A -> B) (t : A -> Prop) (h1 : term191 A B) : term228 A B u _39653 t.
Proof. exact (@lem3635305 A B u _39653 t h1). Qed.
Lemma lem3635309 {A B : Type'} (_39653 : A -> B) (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term191 A B) (h2 : term284 A B u s f t) : term289 A B u _39653 t.
Proof. exact (@lem3635306 A B u _39653 t h1 (@lem3635261 A B u s f t h2)). Qed.
Lemma lem3635310 {A B : Type'} (_39653 : A -> B) (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term191 A B) (h2 : term284 A B u s f t) : term289 A B u _39653 t.
Proof. exact (@lem3635309 A B _39653 u s f t h1 h2). Qed.
Lemma lem3635311 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term191 A B) (h2 : term284 A B u s f t) : term289 A B u f t.
Proof. exact (@lem3635310 A B f u s f t h1 h2). Qed.
Lemma lem3635312 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term191 A B) (h2 : term284 A B u s f t) : term339 A B u f t.
Proof. exact (fun h0 : term327 A B u f t => @lem3635311 A B u s f t h1 h2). Qed.
Lemma lem3635314 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3635315 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term339 A B u f t) = (term289 A B u f t).
Proof. exact (@lem3635314 (term289 A B u f t)). Qed.
Lemma lem3635316 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term191 A B) (h2 : term284 A B u s f t) : term289 A B u f t.
Proof. exact (EQ_MP (@lem3635315 A B u f t) (@lem3635312 A B u s f t h1 h2)). Qed.
Lemma lem3635319 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3635321 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term327 A B u f t) = (term340 A B u f t).
Proof. exact (@lem3635319 (term289 A B u f t)). Qed.
Lemma lem3635324 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term284 A B u s f t) : term340 A B u f t.
Proof. exact (EQ_MP (@lem3635321 A B u f t) (@lem3635005 A B u s f t h1)). Qed.
Lemma lem3635327 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term191 A B) (h2 : term284 A B u s f t) : False.
Proof. exact (@lem3635324 A B u s f t h2 (@lem3635316 A B u s f t h1 h2)). Qed.
Lemma lem3635328 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term191 A B) (h2 : term284 A B u s f t) : term183.
Proof. exact (fun h0 : ~ False => @lem3635327 A B u s f t h1 h2). Qed.
Lemma lem3635330 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3635331 : term183 = False.
Proof. exact (@lem3635330 False). Qed.
Lemma lem3635333 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term191 A B) (h2 : term284 A B u s f t) : False.
Proof. exact (EQ_MP (@lem3635331) (@lem3635328 A B u s f t h1 h2)). Qed.
Lemma lem3635334 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term191 A B) (h2 : term189 A B s f t) : False.
Proof. exact (ex_elim (@lem3633959 A B s f t h2) (fun u : A -> Prop => fun h0 : term286 A B s f t u => @lem3635333 A B u s f t h1 h0)). Qed.
Lemma lem3635335 {_87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term191 A B) (h2 : term189 A B s f t) : term196 _87604 B.
Proof. exact (fun h0 : term190 _87604 B => @lem3635334 A B s f t h1 h2). Qed.
Lemma lem3635336 {_87604 B : Type'} : (term196 _87604 B) = (term197 _87604 B).
Proof. exact (@lem69 (term190 _87604 B)). Qed.
Lemma lem3635337 {_87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term191 A B) (h2 : term189 A B s f t) : term197 _87604 B.
Proof. exact (EQ_MP (@lem3635336 _87604 B) (@lem3635335 _87604 A B s f t h1 h2)). Qed.
Lemma lem3635338 {_87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term189 A B s f t) : term200 _87604 A B.
Proof. exact (fun h0 : term191 A B => @lem3635337 _87604 A B s f t h0 h1). Qed.
Lemma lem3635339 {_87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term189 A B s f t) : term203 _87604 A B.
Proof. exact (fun h0 : term190 _87604 A => @lem3635338 _87604 A B s f t h1). Qed.
Lemma lem3635340 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term189 A B s f t) : term205 _87593 _87604 A B.
Proof. exact (fun h0 : term191 _87593 B => @lem3635339 _87604 A B s f t h1). Qed.
Lemma lem3635341 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term189 A B s f t) : term207 _87593 _87604 A B.
Proof. exact (fun h0 : term191 _87593 A => @lem3635340 _87593 _87604 A B s f t h1). Qed.
Lemma lem3635342 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : term209 _87593 _87604 A B s f t.
Proof. exact (fun h0 : term189 A B s f t => @lem3635341 _87593 _87604 A B s f t h0). Qed.
Lemma lem3635347 {_87593 _87604 A B : Type'} (f : A -> B) (t : A -> Prop) : term213 _87593 _87604 A B f t.
Proof. exact (fun s : B -> Prop => @lem3635342 _87593 _87604 A B s f t). Qed.
Lemma lem3635352 {_87593 _87604 A B : Type'} (t : A -> Prop) : term217 _87593 _87604 A B t.
Proof. exact (fun f : A -> B => @lem3635347 _87593 _87604 A B f t). Qed.
Lemma lem3635357 {_87593 _87604 A B : Type'} : term221 _87593 _87604 A B.
Proof. exact (fun t : A -> Prop => @lem3635352 _87593 _87604 A B t). Qed.
Lemma lem3635358 {_87593 _87604 A B : Type'} : term220 _87593 _87604 A B.
Proof. exact (EQ_MP (@lem3633775 _87593 _87604 A B) (@lem3635357 _87593 _87604 A B)). Qed.
Lemma lem3635359 {_87593 _87604 A B : Type'} (t : A -> Prop) : term341 _87593 _87604 A B t.
Proof. exact (@lem3635358 _87593 _87604 A B t). Qed.
Lemma lem3635360 {_87593 _87604 A B : Type'} (t : A -> Prop) : (term341 _87593 _87604 A B t) = (term216 _87593 _87604 A B t).
Proof. exact (eq_refl (term341 _87593 _87604 A B t)). Qed.
Lemma lem3635361 {_87593 _87604 A B : Type'} (t : A -> Prop) : term216 _87593 _87604 A B t.
Proof. exact (EQ_MP (@lem3635360 _87593 _87604 A B t) (@lem3635359 _87593 _87604 A B t)). Qed.
Lemma lem3635362 {_87593 _87604 A B : Type'} (t : A -> Prop) (f : A -> B) : term342 _87593 _87604 A B t f.
Proof. exact (@lem3635361 _87593 _87604 A B t f). Qed.
Lemma lem3635363 {_87593 _87604 A B : Type'} (f : A -> B) (t : A -> Prop) : (term342 _87593 _87604 A B t f) = (term212 _87593 _87604 A B f t).
Proof. exact (eq_refl (term342 _87593 _87604 A B t f)). Qed.
Lemma lem3635364 {_87593 _87604 A B : Type'} (f : A -> B) (t : A -> Prop) : term212 _87593 _87604 A B f t.
Proof. exact (EQ_MP (@lem3635363 _87593 _87604 A B f t) (@lem3635362 _87593 _87604 A B t f)). Qed.
Lemma lem3635365 {_87593 _87604 A B : Type'} (f : A -> B) (t : A -> Prop) (s : B -> Prop) : term343 _87593 _87604 A B f t s.
Proof. exact (@lem3635364 _87593 _87604 A B f t s). Qed.
Lemma lem3635366 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term343 _87593 _87604 A B f t s) = (term192 _87593 _87604 A B s f t).
Proof. exact (eq_refl (term343 _87593 _87604 A B f t s)). Qed.
Lemma lem3635367 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : term192 _87593 _87604 A B s f t.
Proof. exact (EQ_MP (@lem3635366 _87593 _87604 A B s f t) (@lem3635365 _87593 _87604 A B f t s)). Qed.
Lemma lem3635369 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : term192 _87593 _87604 A B s f t.
Proof. exact (@lem3633277 _87593 _87604 A B s f t (@lem3635367 _87593 _87604 A B s f t)). Qed.
Lemma lem3635370 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term189 A B s f t) : term206 _87593 _87604 A B.
Proof. exact (@lem3635369 _87593 _87604 A B s f t (@lem3633256 A B s f t h1)). Qed.
Lemma lem3635371 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term189 A B s f t) : term204 _87593 _87604 A B.
Proof. exact (@lem3635370 _87593 _87604 A B s f t h1 (@lem3633259 _87593 A)). Qed.
Lemma lem3635372 {_87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term189 A B s f t) : term202 _87604 A B.
Proof. exact (@lem3635371 Prop _87604 A B s f t h1 (@lem3633260 Prop B)). Qed.
Lemma lem3635373 {_87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term189 A B s f t) : term199 _87604 A B.
Proof. exact (@lem3635372 _87604 A B s f t h1 (@lem3633257 _87604 A)). Qed.
Lemma lem3635374 {_87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term189 A B s f t) : term196 _87604 B.
Proof. exact (@lem3635373 _87604 A B s f t h1 (@lem3633261 A B)). Qed.
Lemma lem3635375 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term189 A B s f t) : False.
Proof. exact (@lem3635374 Prop A B s f t h1 (@lem3633258 Prop B)). Qed.
Lemma lem3635376 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term189 A B s f t) : (term189 A B s f t) = False.
Proof. exact (prop_ext (fun h2 : term189 A B s f t => @lem3635375 A B s f t h1) (fun h2 : False => @lem3633256 A B s f t h1)). Qed.
Lemma lem3635377 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term189 A B s f t) : False.
Proof. exact (EQ_MP (@lem3635376 A B s f t h1) (@lem3633256 A B s f t h1)). Qed.
Lemma lem3635378 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : term188 A B s f t.
Proof. exact (fun h0 : term189 A B s f t => @lem3635377 A B s f t h0). Qed.
Lemma lem3635379 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : term187 A B s f t.
Proof. exact (EQ_MP (@lem3633255 A B s f t) (@lem3635378 A B s f t)). Qed.
Lemma lem3635380 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term234 A B s f t) : term234 A B s f t.
Proof. exact (h1). Qed.
Lemma lem3635382 {_93229 _93232 : Type'} (s : _93229 -> Prop) (t : _93232 -> Prop) (f : _93232 -> _93229) : term11 _93229 _93232 s t f.
Proof. exact (EQ_MP (@lem3632154 _93229 _93232 s t f) (@lem3633240 _93229 _93232 s t f)). Qed.
Lemma lem3635383 {A B : Type'} (s : B -> Prop) (t : A -> Prop) (f : A -> B) : term344 A B s t f.
Proof. exact (@lem3635382 B A s t f). Qed.
Lemma lem3635384 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term234 A B s f t) : term3 A B s t f.
Proof. exact (@lem3635383 A B s t f (@lem3635380 A B s f t h1)). Qed.
Lemma lem3635388 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : (term3 _91307 _91308 t s f) = (term4 _91307 _91308 t s f).
Proof. exact (EQ_MP (@lem3632108 _91307 _91308 t s f) (@lem3632107 _91307 _91308 s f t)). Qed.
Lemma lem3635389 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term3 A B t s f) = (term4 A B t s f).
Proof. exact (@lem3635388 A B t s f). Qed.
Lemma lem3635390 {A B : Type'} (s : B -> Prop) (t : A -> Prop) (f : A -> B) : (term3 A B s t f) = (term4 A B s t f).
Proof. exact (@lem3635389 A B s t f). Qed.
Lemma lem3635405 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3635406 {A B : Type'} (s : B -> Prop) (t : A -> Prop) (f : A -> B) : (term345 A B s t f) = (term346 A B s t f).
Proof. exact (MK_COMB (@lem3635405) (@lem3635390 A B s t f)). Qed.
Lemma lem3635435 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term245 A B t s f) = (term245 A B t s f).
Proof. exact (eq_refl (term245 A B t s f)). Qed.
Lemma lem3635436 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term347 A B t s f) = (term348 A B t s f).
Proof. exact (MK_COMB (@lem3635406 A B s t f) (@lem3635435 A B t s f)). Qed.
Lemma lem3635439 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term348 A B t s f) = (term347 A B t s f).
Proof. exact (SYM (@lem3635436 A B t s f)). Qed.
Lemma lem3635440 {A B : Type'} (s : B -> Prop) (t : A -> Prop) (f : A -> B) (h1 : term4 A B s t f) : term4 A B s t f.
Proof. exact (h1). Qed.
Lemma lem3635441 {A B : Type'} (s : B -> Prop) (t : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term349 A B s t f g) : term349 A B s t f g.
Proof. exact (h1). Qed.
Lemma lem3635452 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term349 A B s t f g) (h2 : term234 A B s f t) : term350 A B g s f t.
Proof. exact (conj (@lem3635441 A B s t f g h1) (@lem3635380 A B s f t h2)). Qed.
Lemma lem3635470 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term5 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3635471 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term5 B s t).
Proof. exact (@lem3635470 B s t). Qed.
Lemma lem3635472 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term234 A B s f t) = (term351 A B s f t).
Proof. exact (@lem3635471 B s (@IMAGE A B f t)). Qed.
Lemma lem3635479 {A B : Type'} (s : B -> Prop) (t : A -> Prop) (f : A -> B) (g : B -> A) : (term352 A B s t f g) = (term352 A B s t f g).
Proof. exact (eq_refl (term352 A B s t f g)). Qed.
Lemma lem3635480 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term350 A B g s f t) = (term353 A B g s f t).
Proof. exact (MK_COMB (@lem3635479 A B s t f g) (@lem3635472 A B s f t)). Qed.
Lemma lem3635483 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3635484 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term354 A B g s f t) = (term355 A B g s f t).
Proof. exact (MK_COMB (@lem3635483) (@lem3635480 A B g s f t)). Qed.
Lemma lem3635488 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term5 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3635489 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term5 A s t).
Proof. exact (@lem3635488 A s t). Qed.
Lemma lem3635490 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) : (term356 A B g s t) = (term357 A B g s t).
Proof. exact (@lem3635489 A (@IMAGE B A g s) t). Qed.
Lemma lem3635497 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3635498 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) : (term358 A B g s t) = (term359 A B g s t).
Proof. exact (MK_COMB (@lem3635497) (@lem3635490 A B g s t)). Qed.
Lemma lem3635528 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term360 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3635529 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (s = t) = (term360 B s t).
Proof. exact (@lem3635528 B s t). Qed.
Lemma lem3635530 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (s = (term361 A B f g s)) = (term362 A B f g s).
Proof. exact (@lem3635529 B s (term361 A B f g s)). Qed.
Lemma lem3635539 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) : (term363 A B g s f) = (term363 A B g s f).
Proof. exact (eq_refl (term363 A B g s f)). Qed.
Lemma lem3635540 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term364 A B f g s) = (term365 A B f g s).
Proof. exact (MK_COMB (@lem3635539 A B g s f) (@lem3635530 A B f g s)). Qed.
Lemma lem3635543 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term366 A B t f g s) = (term367 A B t f g s).
Proof. exact (MK_COMB (@lem3635498 A B g s t) (@lem3635540 A B f g s)). Qed.
Lemma lem3635546 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term368 A B t f g s) = (term369 A B t f g s).
Proof. exact (MK_COMB (@lem3635484 A B g s f t) (@lem3635543 A B t f g s)). Qed.
Lemma lem3635549 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term369 A B t f g s) = (term368 A B t f g s).
Proof. exact (SYM (@lem3635546 A B t f g s)). Qed.
Lemma lem3635561 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3635562 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem3635561 B P x). Qed.
Lemma lem3635563 {B : Type'} (s : B -> Prop) (x : B) : (@IN B x s) = (s x).
Proof. exact (@lem3635562 B s x). Qed.
Lemma lem3635564 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3635565 {B : Type'} (s : B -> Prop) (x : B) : (term13 B x s) = (term14 B s x).
Proof. exact (MK_COMB (@lem3635564) (@lem3635563 B s x)). Qed.
Lemma lem3635569 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3635570 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3635569 A P x). Qed.
Lemma lem3635571 {A B : Type'} (t : A -> Prop) (g : B -> A) (x : B) : (term370 A B g x t) = (term371 A B t g x).
Proof. exact (@lem3635570 A t (g x)). Qed.
Lemma lem3635572 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3635573 {A B : Type'} (t : A -> Prop) (g : B -> A) (x : B) : (term372 A B g x t) = (term373 A B t g x).
Proof. exact (MK_COMB (@lem3635572) (@lem3635571 A B t g x)). Qed.
Lemma lem3635576 {A B : Type'} (f : A -> B) (g : B -> A) (x : B) : ((term374 A B f g x) = x) = ((term374 A B f g x) = x).
Proof. exact (eq_refl ((term374 A B f g x) = x)). Qed.
Lemma lem3635577 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (x : B) : (term375 A B t f g x) = (term376 A B t f g x).
Proof. exact (MK_COMB (@lem3635573 A B t g x) (@lem3635576 A B f g x)). Qed.
Lemma lem3635580 {A B : Type'} (s : B -> Prop) (t : A -> Prop) (f : A -> B) (g : B -> A) (x : B) : (term377 A B s t f g x) = (term378 A B s t f g x).
Proof. exact (MK_COMB (@lem3635565 B s x) (@lem3635577 A B t f g x)). Qed.
Lemma lem3635583 {A B : Type'} (s : B -> Prop) (t : A -> Prop) (f : A -> B) (g : B -> A) : (term379 A B s t f g) = (term380 A B s t f g).
Proof. exact (fun_ext (fun x : B => @lem3635580 A B s t f g x)). Qed.
Lemma lem3635584 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3635585 {A B : Type'} (s : B -> Prop) (t : A -> Prop) (f : A -> B) (g : B -> A) : (term349 A B s t f g) = (term381 A B s t f g).
Proof. exact (MK_COMB (@lem3635584 B) (@lem3635583 A B s t f g)). Qed.
Lemma lem3635590 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3635591 {A B : Type'} (s : B -> Prop) (t : A -> Prop) (f : A -> B) (g : B -> A) : (term352 A B s t f g) = (term382 A B s t f g).
Proof. exact (MK_COMB (@lem3635590) (@lem3635585 A B s t f g)). Qed.
Lemma lem3635599 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3635600 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem3635599 B P x). Qed.
Lemma lem3635601 {B : Type'} (s : B -> Prop) (x : B) : (@IN B x s) = (s x).
Proof. exact (@lem3635600 B s x). Qed.
Lemma lem3635602 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3635603 {B : Type'} (s : B -> Prop) (x : B) : (term13 B x s) = (term14 B s x).
Proof. exact (MK_COMB (@lem3635602) (@lem3635601 B s x)). Qed.
Lemma lem3635605 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term16 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3635606 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term16 A B y f s).
Proof. exact (@lem3635605 A B y f s). Qed.
Lemma lem3635607 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term15 A B x f t) = (term16 A B x f t).
Proof. exact (@lem3635606 A B x f t). Qed.
Lemma lem3635617 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3635618 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3635617 A P x). Qed.
Lemma lem3635619 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3635618 A t x). Qed.
Lemma lem3635620 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term383 A B x f x') = (term383 A B x f x').
Proof. exact (eq_refl (term383 A B x f x')). Qed.
Lemma lem3635621 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term384 A B x f x' t) = (term385 A B x f t x').
Proof. exact (MK_COMB (@lem3635620 A B x f x') (@lem3635619 A t x')). Qed.
Lemma lem3635624 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term386 A B x f t) = (term387 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3635621 A B x f t x')). Qed.
Lemma lem3635625 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3635626 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term16 A B x f t) = (term388 A B x f t).
Proof. exact (MK_COMB (@lem3635625 A) (@lem3635624 A B x f t)). Qed.
Lemma lem3635631 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term15 A B x f t) = (term388 A B x f t).
Proof. exact (TRANS (@lem3635607 A B x f t) (@lem3635626 A B x f t)). Qed.
Lemma lem3635632 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term389 A B s x f t) = (term390 A B s x f t).
Proof. exact (MK_COMB (@lem3635603 B s x) (@lem3635631 A B x f t)). Qed.
Lemma lem3635635 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term391 A B s f t) = (term392 A B s f t).
Proof. exact (fun_ext (fun x : B => @lem3635632 A B s x f t)). Qed.
Lemma lem3635636 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3635637 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term351 A B s f t) = (term393 A B s f t).
Proof. exact (MK_COMB (@lem3635636 B) (@lem3635635 A B s f t)). Qed.
Lemma lem3635642 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term353 A B g s f t) = (term394 A B g s f t).
Proof. exact (MK_COMB (@lem3635591 A B s t f g) (@lem3635637 A B s f t)). Qed.
Lemma lem3635645 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3635646 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term355 A B g s f t) = (term395 A B g s f t).
Proof. exact (MK_COMB (@lem3635645) (@lem3635642 A B g s f t)). Qed.
Lemma lem3635656 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term16 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3635657 {A B : Type'} (y : A) (f : B -> A) (s : B -> Prop) : (term17 A B y f s) = (term18 A B y f s).
Proof. exact (@lem3635656 B A y f s). Qed.
Lemma lem3635658 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term17 A B x g s) = (term18 A B x g s).
Proof. exact (@lem3635657 A B x g s). Qed.
Lemma lem3635668 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3635669 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem3635668 B P x). Qed.
Lemma lem3635670 {B : Type'} (s : B -> Prop) (x : B) : (@IN B x s) = (s x).
Proof. exact (@lem3635669 B s x). Qed.
Lemma lem3635671 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term19 A B x g x') = (term19 A B x g x').
Proof. exact (eq_refl (term19 A B x g x')). Qed.
Lemma lem3635672 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) (x' : B) : (term20 A B x g x' s) = (term21 A B x g s x').
Proof. exact (MK_COMB (@lem3635671 A B x g x') (@lem3635670 B s x')). Qed.
Lemma lem3635675 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term22 A B x g s) = (term23 A B x g s).
Proof. exact (fun_ext (fun x' : B => @lem3635672 A B x g s x')). Qed.
Lemma lem3635676 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3635677 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term18 A B x g s) = (term24 A B x g s).
Proof. exact (MK_COMB (@lem3635676 B) (@lem3635675 A B x g s)). Qed.
Lemma lem3635682 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term17 A B x g s) = (term24 A B x g s).
Proof. exact (TRANS (@lem3635658 A B x g s) (@lem3635677 A B x g s)). Qed.
Lemma lem3635683 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3635684 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term396 A B x g s) = (term397 A B x g s).
Proof. exact (MK_COMB (@lem3635683) (@lem3635682 A B x g s)). Qed.
Lemma lem3635686 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3635687 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3635686 A P x). Qed.
Lemma lem3635688 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3635687 A t x). Qed.
Lemma lem3635689 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) (x : A) : (term398 A B g s x t) = (term399 A B g s t x).
Proof. exact (MK_COMB (@lem3635684 A B x g s) (@lem3635688 A t x)). Qed.
Lemma lem3635692 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) : (term400 A B g s t) = (term401 A B g s t).
Proof. exact (fun_ext (fun x : A => @lem3635689 A B g s t x)). Qed.
Lemma lem3635693 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3635694 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) : (term357 A B g s t) = (term402 A B g s t).
Proof. exact (MK_COMB (@lem3635693 A) (@lem3635692 A B g s t)). Qed.
Lemma lem3635699 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3635700 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) : (term359 A B g s t) = (term403 A B g s t).
Proof. exact (MK_COMB (@lem3635699) (@lem3635694 A B g s t)). Qed.
Lemma lem3635716 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term16 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3635717 {A B : Type'} (y : A) (f : B -> A) (s : B -> Prop) : (term17 A B y f s) = (term18 A B y f s).
Proof. exact (@lem3635716 B A y f s). Qed.
Lemma lem3635718 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term17 A B x g s) = (term18 A B x g s).
Proof. exact (@lem3635717 A B x g s). Qed.
Lemma lem3635728 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3635729 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem3635728 B P x). Qed.
Lemma lem3635730 {B : Type'} (s : B -> Prop) (x : B) : (@IN B x s) = (s x).
Proof. exact (@lem3635729 B s x). Qed.
Lemma lem3635731 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term19 A B x g x') = (term19 A B x g x').
Proof. exact (eq_refl (term19 A B x g x')). Qed.
Lemma lem3635732 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) (x' : B) : (term20 A B x g x' s) = (term21 A B x g s x').
Proof. exact (MK_COMB (@lem3635731 A B x g x') (@lem3635730 B s x')). Qed.
Lemma lem3635735 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term22 A B x g s) = (term23 A B x g s).
Proof. exact (fun_ext (fun x' : B => @lem3635732 A B x g s x')). Qed.
Lemma lem3635736 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3635737 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term18 A B x g s) = (term24 A B x g s).
Proof. exact (MK_COMB (@lem3635736 B) (@lem3635735 A B x g s)). Qed.
Lemma lem3635742 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term17 A B x g s) = (term24 A B x g s).
Proof. exact (TRANS (@lem3635718 A B x g s) (@lem3635737 A B x g s)). Qed.
Lemma lem3635743 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3635744 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term404 A B x g s) = (term405 A B x g s).
Proof. exact (MK_COMB (@lem3635743) (@lem3635742 A B x g s)). Qed.
Lemma lem3635746 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term16 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3635747 {A B : Type'} (y : A) (f : B -> A) (s : B -> Prop) : (term17 A B y f s) = (term18 A B y f s).
Proof. exact (@lem3635746 B A y f s). Qed.
Lemma lem3635748 {A B : Type'} (y : A) (g : B -> A) (s : B -> Prop) : (term17 A B y g s) = (term18 A B y g s).
Proof. exact (@lem3635747 A B y g s). Qed.
Lemma lem3635758 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3635759 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem3635758 B P x). Qed.
Lemma lem3635760 {B : Type'} (s : B -> Prop) (x : B) : (@IN B x s) = (s x).
Proof. exact (@lem3635759 B s x). Qed.
Lemma lem3635761 {A B : Type'} (y : A) (g : B -> A) (x : B) : (term19 A B y g x) = (term19 A B y g x).
Proof. exact (eq_refl (term19 A B y g x)). Qed.
Lemma lem3635762 {A B : Type'} (y : A) (g : B -> A) (s : B -> Prop) (x : B) : (term20 A B y g x s) = (term21 A B y g s x).
Proof. exact (MK_COMB (@lem3635761 A B y g x) (@lem3635760 B s x)). Qed.
Lemma lem3635765 {A B : Type'} (y : A) (g : B -> A) (s : B -> Prop) : (term22 A B y g s) = (term23 A B y g s).
Proof. exact (fun_ext (fun x : B => @lem3635762 A B y g s x)). Qed.
Lemma lem3635766 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3635767 {A B : Type'} (y : A) (g : B -> A) (s : B -> Prop) : (term18 A B y g s) = (term24 A B y g s).
Proof. exact (MK_COMB (@lem3635766 B) (@lem3635765 A B y g s)). Qed.
Lemma lem3635772 {A B : Type'} (y : A) (g : B -> A) (s : B -> Prop) : (term17 A B y g s) = (term24 A B y g s).
Proof. exact (TRANS (@lem3635748 A B y g s) (@lem3635767 A B y g s)). Qed.
Lemma lem3635773 {A B : Type'} (x : A) (y : A) (g : B -> A) (s : B -> Prop) : (term406 A B x y g s) = (term407 A B x y g s).
Proof. exact (MK_COMB (@lem3635744 A B x g s) (@lem3635772 A B y g s)). Qed.
Lemma lem3635776 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3635777 {A B : Type'} (x : A) (y : A) (g : B -> A) (s : B -> Prop) : (term408 A B x y g s) = (term409 A B x y g s).
Proof. exact (MK_COMB (@lem3635776) (@lem3635773 A B x y g s)). Qed.
Lemma lem3635784 {A B : Type'} (f : A -> B) (x : A) (y : A) : (((f x) = (f y)) = (x = y)) = (((f x) = (f y)) = (x = y)).
Proof. exact (eq_refl (((f x) = (f y)) = (x = y))). Qed.
Lemma lem3635785 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) (y : A) : (term410 A B g s f x y) = (term411 A B g s f x y).
Proof. exact (MK_COMB (@lem3635777 A B x y g s) (@lem3635784 A B f x y)). Qed.
Lemma lem3635788 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) : (term412 A B g s f x) = (term413 A B g s f x).
Proof. exact (fun_ext (fun y : A => @lem3635785 A B g s f x y)). Qed.
Lemma lem3635789 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3635790 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) : (term414 A B g s f x) = (term415 A B g s f x).
Proof. exact (MK_COMB (@lem3635789 A) (@lem3635788 A B g s f x)). Qed.
Lemma lem3635795 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) : (term416 A B g s f) = (term417 A B g s f).
Proof. exact (fun_ext (fun x : A => @lem3635790 A B g s f x)). Qed.
Lemma lem3635796 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3635797 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) : (term418 A B g s f) = (term419 A B g s f).
Proof. exact (MK_COMB (@lem3635796 A) (@lem3635795 A B g s f)). Qed.
Lemma lem3635802 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3635803 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) : (term363 A B g s f) = (term420 A B g s f).
Proof. exact (MK_COMB (@lem3635802) (@lem3635797 A B g s f)). Qed.
Lemma lem3635811 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3635812 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem3635811 B P x). Qed.
Lemma lem3635813 {B : Type'} (s : B -> Prop) (x : B) : (@IN B x s) = (s x).
Proof. exact (@lem3635812 B s x). Qed.
Lemma lem3635814 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3635815 {B : Type'} (s : B -> Prop) (x : B) : (term421 B x s) = (term422 B s x).
Proof. exact (MK_COMB (@lem3635814) (@lem3635813 B s x)). Qed.
Lemma lem3635817 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term16 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3635818 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term16 A B y f s).
Proof. exact (@lem3635817 A B y f s). Qed.
Lemma lem3635819 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term423 A B x f g s) = (term424 A B x f g s).
Proof. exact (@lem3635818 A B x f (@IMAGE B A g s)). Qed.
Lemma lem3635829 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term16 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3635830 {A B : Type'} (y : A) (f : B -> A) (s : B -> Prop) : (term17 A B y f s) = (term18 A B y f s).
Proof. exact (@lem3635829 B A y f s). Qed.
Lemma lem3635831 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term17 A B x g s) = (term18 A B x g s).
Proof. exact (@lem3635830 A B x g s). Qed.
Lemma lem3635841 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3635842 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem3635841 B P x). Qed.
Lemma lem3635843 {B : Type'} (s : B -> Prop) (x : B) : (@IN B x s) = (s x).
Proof. exact (@lem3635842 B s x). Qed.
Lemma lem3635844 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term19 A B x g x') = (term19 A B x g x').
Proof. exact (eq_refl (term19 A B x g x')). Qed.
Lemma lem3635845 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) (x' : B) : (term20 A B x g x' s) = (term21 A B x g s x').
Proof. exact (MK_COMB (@lem3635844 A B x g x') (@lem3635843 B s x')). Qed.
Lemma lem3635848 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term22 A B x g s) = (term23 A B x g s).
Proof. exact (fun_ext (fun x' : B => @lem3635845 A B x g s x')). Qed.
Lemma lem3635849 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3635850 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term18 A B x g s) = (term24 A B x g s).
Proof. exact (MK_COMB (@lem3635849 B) (@lem3635848 A B x g s)). Qed.
Lemma lem3635855 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term17 A B x g s) = (term24 A B x g s).
Proof. exact (TRANS (@lem3635831 A B x g s) (@lem3635850 A B x g s)). Qed.
Lemma lem3635856 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term383 A B x f x') = (term383 A B x f x').
Proof. exact (eq_refl (term383 A B x f x')). Qed.
Lemma lem3635857 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term425 A B x f x' g s) = (term426 A B x f x' g s).
Proof. exact (MK_COMB (@lem3635856 A B x f x') (@lem3635855 A B x' g s)). Qed.
Lemma lem3635860 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term427 A B x f g s) = (term428 A B x f g s).
Proof. exact (fun_ext (fun x' : A => @lem3635857 A B x f x' g s)). Qed.
Lemma lem3635861 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3635862 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term424 A B x f g s) = (term429 A B x f g s).
Proof. exact (MK_COMB (@lem3635861 A) (@lem3635860 A B x f g s)). Qed.
Lemma lem3635867 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term423 A B x f g s) = (term429 A B x f g s).
Proof. exact (TRANS (@lem3635819 A B x f g s) (@lem3635862 A B x f g s)). Qed.
Lemma lem3635868 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : ((@IN B x s) = (term423 A B x f g s)) = ((s x) = (term429 A B x f g s)).
Proof. exact (MK_COMB (@lem3635815 B s x) (@lem3635867 A B x f g s)). Qed.
Lemma lem3635871 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term430 A B f g s) = (term431 A B f g s).
Proof. exact (fun_ext (fun x : B => @lem3635868 A B x f g s)). Qed.
Lemma lem3635872 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3635873 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term362 A B f g s) = (term432 A B f g s).
Proof. exact (MK_COMB (@lem3635872 B) (@lem3635871 A B f g s)). Qed.
Lemma lem3635878 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term365 A B f g s) = (term433 A B f g s).
Proof. exact (MK_COMB (@lem3635803 A B g s f) (@lem3635873 A B f g s)). Qed.
Lemma lem3635881 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term367 A B t f g s) = (term434 A B t f g s).
Proof. exact (MK_COMB (@lem3635700 A B g s t) (@lem3635878 A B f g s)). Qed.
Lemma lem3635884 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term369 A B t f g s) = (term435 A B t f g s).
Proof. exact (MK_COMB (@lem3635646 A B g s f t) (@lem3635881 A B t f g s)). Qed.
Lemma lem3635887 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term435 A B t f g s) = (term369 A B t f g s).
Proof. exact (SYM (@lem3635884 A B t f g s)). Qed.
Lemma lem3635889 (p : Prop) : p = (term45 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3635890 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term435 A B t f g s) = (term436 A B t f g s).
Proof. exact (@lem3635889 (term435 A B t f g s)). Qed.
Lemma lem3635891 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term436 A B t f g s) = (term435 A B t f g s).
Proof. exact (SYM (@lem3635890 A B t f g s)). Qed.
Lemma lem3635892 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term437 A B t f g s) : term437 A B t f g s.
Proof. exact (h1). Qed.
Lemma lem3635895 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term436 A B t f g s) : term436 A B t f g s.
Proof. exact (h1). Qed.
Lemma lem3635896 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : term438 A B t f g s.
Proof. exact (fun h0 : term436 A B t f g s => @lem3635895 A B t f g s h0). Qed.
Lemma lem3635897 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term438 A B t f g s) : term438 A B t f g s.
Proof. exact (h1). Qed.
Lemma lem3635898 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term436 A B t f g s) : term436 A B t f g s.
Proof. exact (h1). Qed.
Lemma lem3635899 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term436 A B t f g s) (h2 : term438 A B t f g s) : term436 A B t f g s.
Proof. exact (@lem3635897 A B t f g s h2 (@lem3635898 A B t f g s h1)). Qed.
Lemma lem3635900 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term436 A B t f g s) : term439 A B t f g s.
Proof. exact (fun h0 : term438 A B t f g s => @lem3635899 A B t f g s h1 h0). Qed.
Lemma lem3635901 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term438 A B t f g s) : term438 A B t f g s.
Proof. exact (h1). Qed.
Lemma lem3635902 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term436 A B t f g s) (h2 : term438 A B t f g s) : term436 A B t f g s.
Proof. exact (@lem3635900 A B t f g s h1 (@lem3635901 A B t f g s h2)). Qed.
Lemma lem3635903 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term438 A B t f g s) : term438 A B t f g s.
Proof. exact (fun h0 : term436 A B t f g s => @lem3635902 A B t f g s h0 h1). Qed.
Lemma lem3635904 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : term440 A B t f g s.
Proof. exact (fun h0 : term438 A B t f g s => @lem3635903 A B t f g s h0). Qed.
Lemma lem3635907 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : term438 A B t f g s.
Proof. exact (@lem3635904 A B t f g s (@lem3635896 A B t f g s)). Qed.
Lemma lem3635908 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : term438 A B t f g s.
Proof. exact (@lem3635907 A B t f g s). Qed.
Lemma lem3635926 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3635927 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term436 A B t f g s) = (term441 A B t f g s).
Proof. exact (@lem3635926 (term437 A B t f g s)). Qed.
Lemma lem3635929 (t : Prop) : (term52 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3635930 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term441 A B t f g s) = (term435 A B t f g s).
Proof. exact (@lem3635929 (term435 A B t f g s)). Qed.
Lemma lem3635933 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term436 A B t f g s) = (term435 A B t f g s).
Proof. exact (TRANS (@lem3635927 A B t f g s) (@lem3635930 A B t f g s)). Qed.
Lemma lem3636196 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term442 A B f g s) = (term443 A B f g s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3635933 A B t f g s)). Qed.
Lemma lem3636197 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3636198 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term444 A B f g s) = (term445 A B f g s).
Proof. exact (MK_COMB (@lem3636197 A) (@lem3636196 A B f g s)). Qed.
Lemma lem3636203 {A B : Type'} (g : B -> A) (s : B -> Prop) : (term446 A B g s) = (term447 A B g s).
Proof. exact (fun_ext (fun f : A -> B => @lem3636198 A B f g s)). Qed.
Lemma lem3636204 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3636205 {A B : Type'} (g : B -> A) (s : B -> Prop) : (term448 A B g s) = (term449 A B g s).
Proof. exact (MK_COMB (@lem3636204 A B) (@lem3636203 A B g s)). Qed.
Lemma lem3636210 {A B : Type'} (s : B -> Prop) : (term450 A B s) = (term451 A B s).
Proof. exact (fun_ext (fun g : B -> A => @lem3636205 A B g s)). Qed.
Lemma lem3636211 {A B : Type'} : (@all (B -> A)) = (@all (B -> A)).
Proof. exact (eq_refl (@all (B -> A))). Qed.
Lemma lem3636212 {A B : Type'} (s : B -> Prop) : (term452 A B s) = (term453 A B s).
Proof. exact (MK_COMB (@lem3636211 A B) (@lem3636210 A B s)). Qed.
Lemma lem3636217 {A B : Type'} : (term454 A B) = (term455 A B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3636212 A B s)). Qed.
Lemma lem3636218 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3636227 {A B : Type'} : (term456 A B) = (term457 A B).
Proof. exact (MK_COMB (@lem3636218 B) (@lem3636217 A B)). Qed.
Lemma lem3636232 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) (x' : B) : (term21 A B x g s x') = (term21 A B x g s x').
Proof. exact (eq_refl (term21 A B x g s x')). Qed.
Lemma lem3636233 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term23 A B x g s) = (term23 A B x g s).
Proof. exact (fun_ext (fun x' : B => @lem3636232 A B x g s x')). Qed.
Lemma lem3636234 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3636235 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term24 A B x g s) = (term24 A B x g s).
Proof. exact (MK_COMB (@lem3636234 B) (@lem3636233 A B x g s)). Qed.
Lemma lem3636238 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term383 A B x f x') = (term383 A B x f x').
Proof. exact (eq_refl (term383 A B x f x')). Qed.
Lemma lem3636239 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term426 A B x f x' g s) = (term426 A B x f x' g s).
Proof. exact (MK_COMB (@lem3636238 A B x f x') (@lem3636235 A B x' g s)). Qed.
Lemma lem3636240 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term428 A B x f g s) = (term428 A B x f g s).
Proof. exact (fun_ext (fun x' : A => @lem3636239 A B x f x' g s)). Qed.
Lemma lem3636241 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3636242 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term429 A B x f g s) = (term429 A B x f g s).
Proof. exact (MK_COMB (@lem3636241 A) (@lem3636240 A B x f g s)). Qed.
Lemma lem3636245 {B : Type'} (s : B -> Prop) (x : B) : (term422 B s x) = (term422 B s x).
Proof. exact (eq_refl (term422 B s x)). Qed.
Lemma lem3636246 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : ((s x) = (term429 A B x f g s)) = ((s x) = (term429 A B x f g s)).
Proof. exact (MK_COMB (@lem3636245 B s x) (@lem3636242 A B x f g s)). Qed.
Lemma lem3636247 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term431 A B f g s) = (term431 A B f g s).
Proof. exact (fun_ext (fun x : B => @lem3636246 A B x f g s)). Qed.
Lemma lem3636248 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3636249 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term432 A B f g s) = (term432 A B f g s).
Proof. exact (MK_COMB (@lem3636248 B) (@lem3636247 A B f g s)). Qed.
Lemma lem3636254 {A B : Type'} (f : A -> B) (x : A) (y : A) : (((f x) = (f y)) = (x = y)) = (((f x) = (f y)) = (x = y)).
Proof. exact (eq_refl (((f x) = (f y)) = (x = y))). Qed.
Lemma lem3636259 {A B : Type'} (y : A) (g : B -> A) (s : B -> Prop) (x : B) : (term21 A B y g s x) = (term21 A B y g s x).
Proof. exact (eq_refl (term21 A B y g s x)). Qed.
Lemma lem3636260 {A B : Type'} (y : A) (g : B -> A) (s : B -> Prop) : (term23 A B y g s) = (term23 A B y g s).
Proof. exact (fun_ext (fun x : B => @lem3636259 A B y g s x)). Qed.
Lemma lem3636261 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3636262 {A B : Type'} (y : A) (g : B -> A) (s : B -> Prop) : (term24 A B y g s) = (term24 A B y g s).
Proof. exact (MK_COMB (@lem3636261 B) (@lem3636260 A B y g s)). Qed.
Lemma lem3636267 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) (x' : B) : (term21 A B x g s x') = (term21 A B x g s x').
Proof. exact (eq_refl (term21 A B x g s x')). Qed.
Lemma lem3636268 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term23 A B x g s) = (term23 A B x g s).
Proof. exact (fun_ext (fun x' : B => @lem3636267 A B x g s x')). Qed.
Lemma lem3636269 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3636270 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term24 A B x g s) = (term24 A B x g s).
Proof. exact (MK_COMB (@lem3636269 B) (@lem3636268 A B x g s)). Qed.
Lemma lem3636271 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3636272 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term405 A B x g s) = (term405 A B x g s).
Proof. exact (MK_COMB (@lem3636271) (@lem3636270 A B x g s)). Qed.
Lemma lem3636273 {A B : Type'} (x : A) (y : A) (g : B -> A) (s : B -> Prop) : (term407 A B x y g s) = (term407 A B x y g s).
Proof. exact (MK_COMB (@lem3636272 A B x g s) (@lem3636262 A B y g s)). Qed.
Lemma lem3636274 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3636275 {A B : Type'} (x : A) (y : A) (g : B -> A) (s : B -> Prop) : (term409 A B x y g s) = (term409 A B x y g s).
Proof. exact (MK_COMB (@lem3636274) (@lem3636273 A B x y g s)). Qed.
Lemma lem3636276 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) (y : A) : (term411 A B g s f x y) = (term411 A B g s f x y).
Proof. exact (MK_COMB (@lem3636275 A B x y g s) (@lem3636254 A B f x y)). Qed.
Lemma lem3636277 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) : (term413 A B g s f x) = (term413 A B g s f x).
Proof. exact (fun_ext (fun y : A => @lem3636276 A B g s f x y)). Qed.
Lemma lem3636278 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3636279 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) : (term415 A B g s f x) = (term415 A B g s f x).
Proof. exact (MK_COMB (@lem3636278 A) (@lem3636277 A B g s f x)). Qed.
Lemma lem3636280 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) : (term417 A B g s f) = (term417 A B g s f).
Proof. exact (fun_ext (fun x : A => @lem3636279 A B g s f x)). Qed.
Lemma lem3636281 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3636282 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) : (term419 A B g s f) = (term419 A B g s f).
Proof. exact (MK_COMB (@lem3636281 A) (@lem3636280 A B g s f)). Qed.
Lemma lem3636283 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3636284 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) : (term420 A B g s f) = (term420 A B g s f).
Proof. exact (MK_COMB (@lem3636283) (@lem3636282 A B g s f)). Qed.
Lemma lem3636285 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term433 A B f g s) = (term433 A B f g s).
Proof. exact (MK_COMB (@lem3636284 A B g s f) (@lem3636249 A B f g s)). Qed.
Lemma lem3636286 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3636291 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) (x' : B) : (term21 A B x g s x') = (term21 A B x g s x').
Proof. exact (eq_refl (term21 A B x g s x')). Qed.
Lemma lem3636292 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term23 A B x g s) = (term23 A B x g s).
Proof. exact (fun_ext (fun x' : B => @lem3636291 A B x g s x')). Qed.
Lemma lem3636293 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3636294 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term24 A B x g s) = (term24 A B x g s).
Proof. exact (MK_COMB (@lem3636293 B) (@lem3636292 A B x g s)). Qed.
Lemma lem3636295 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3636296 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term397 A B x g s) = (term397 A B x g s).
Proof. exact (MK_COMB (@lem3636295) (@lem3636294 A B x g s)). Qed.
Lemma lem3636297 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) (x : A) : (term399 A B g s t x) = (term399 A B g s t x).
Proof. exact (MK_COMB (@lem3636296 A B x g s) (@lem3636286 A t x)). Qed.
Lemma lem3636298 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) : (term401 A B g s t) = (term401 A B g s t).
Proof. exact (fun_ext (fun x : A => @lem3636297 A B g s t x)). Qed.
Lemma lem3636299 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3636300 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) : (term402 A B g s t) = (term402 A B g s t).
Proof. exact (MK_COMB (@lem3636299 A) (@lem3636298 A B g s t)). Qed.
Lemma lem3636301 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3636302 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) : (term403 A B g s t) = (term403 A B g s t).
Proof. exact (MK_COMB (@lem3636301) (@lem3636300 A B g s t)). Qed.
Lemma lem3636303 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term434 A B t f g s) = (term434 A B t f g s).
Proof. exact (MK_COMB (@lem3636302 A B g s t) (@lem3636285 A B f g s)). Qed.
Lemma lem3636308 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term385 A B x f t x') = (term385 A B x f t x').
Proof. exact (eq_refl (term385 A B x f t x')). Qed.
Lemma lem3636309 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term387 A B x f t) = (term387 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3636308 A B x f t x')). Qed.
Lemma lem3636310 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3636311 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term388 A B x f t) = (term388 A B x f t).
Proof. exact (MK_COMB (@lem3636310 A) (@lem3636309 A B x f t)). Qed.
Lemma lem3636314 {B : Type'} (s : B -> Prop) (x : B) : (term14 B s x) = (term14 B s x).
Proof. exact (eq_refl (term14 B s x)). Qed.
Lemma lem3636315 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term390 A B s x f t) = (term390 A B s x f t).
Proof. exact (MK_COMB (@lem3636314 B s x) (@lem3636311 A B x f t)). Qed.
Lemma lem3636316 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term392 A B s f t) = (term392 A B s f t).
Proof. exact (fun_ext (fun x : B => @lem3636315 A B s x f t)). Qed.
Lemma lem3636317 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3636318 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term393 A B s f t) = (term393 A B s f t).
Proof. exact (MK_COMB (@lem3636317 B) (@lem3636316 A B s f t)). Qed.
Lemma lem3636327 {A B : Type'} (s : B -> Prop) (t : A -> Prop) (f : A -> B) (g : B -> A) (x : B) : (term378 A B s t f g x) = (term378 A B s t f g x).
Proof. exact (eq_refl (term378 A B s t f g x)). Qed.
Lemma lem3636328 {A B : Type'} (s : B -> Prop) (t : A -> Prop) (f : A -> B) (g : B -> A) : (term380 A B s t f g) = (term380 A B s t f g).
Proof. exact (fun_ext (fun x : B => @lem3636327 A B s t f g x)). Qed.
Lemma lem3636329 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3636330 {A B : Type'} (s : B -> Prop) (t : A -> Prop) (f : A -> B) (g : B -> A) : (term381 A B s t f g) = (term381 A B s t f g).
Proof. exact (MK_COMB (@lem3636329 B) (@lem3636328 A B s t f g)). Qed.
Lemma lem3636331 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3636332 {A B : Type'} (s : B -> Prop) (t : A -> Prop) (f : A -> B) (g : B -> A) : (term382 A B s t f g) = (term382 A B s t f g).
Proof. exact (MK_COMB (@lem3636331) (@lem3636330 A B s t f g)). Qed.
Lemma lem3636333 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term394 A B g s f t) = (term394 A B g s f t).
Proof. exact (MK_COMB (@lem3636332 A B s t f g) (@lem3636318 A B s f t)). Qed.
Lemma lem3636334 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3636335 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term395 A B g s f t) = (term395 A B g s f t).
Proof. exact (MK_COMB (@lem3636334) (@lem3636333 A B g s f t)). Qed.
Lemma lem3636336 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term435 A B t f g s) = (term435 A B t f g s).
Proof. exact (MK_COMB (@lem3636335 A B g s f t) (@lem3636303 A B t f g s)). Qed.
Lemma lem3636337 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term443 A B f g s) = (term443 A B f g s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3636336 A B t f g s)). Qed.
Lemma lem3636338 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3636339 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term445 A B f g s) = (term445 A B f g s).
Proof. exact (MK_COMB (@lem3636338 A) (@lem3636337 A B f g s)). Qed.
Lemma lem3636340 {A B : Type'} (g : B -> A) (s : B -> Prop) : (term447 A B g s) = (term447 A B g s).
Proof. exact (fun_ext (fun f : A -> B => @lem3636339 A B f g s)). Qed.
Lemma lem3636341 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3636342 {A B : Type'} (g : B -> A) (s : B -> Prop) : (term449 A B g s) = (term449 A B g s).
Proof. exact (MK_COMB (@lem3636341 A B) (@lem3636340 A B g s)). Qed.
Lemma lem3636343 {A B : Type'} (s : B -> Prop) : (term451 A B s) = (term451 A B s).
Proof. exact (fun_ext (fun g : B -> A => @lem3636342 A B g s)). Qed.
Lemma lem3636344 {A B : Type'} : (@all (B -> A)) = (@all (B -> A)).
Proof. exact (eq_refl (@all (B -> A))). Qed.
Lemma lem3636345 {A B : Type'} (s : B -> Prop) : (term453 A B s) = (term453 A B s).
Proof. exact (MK_COMB (@lem3636344 A B) (@lem3636343 A B s)). Qed.
Lemma lem3636346 {A B : Type'} : (term455 A B) = (term455 A B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3636345 A B s)). Qed.
Lemma lem3636347 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3636348 {A B : Type'} : (term457 A B) = (term457 A B).
Proof. exact (MK_COMB (@lem3636347 B) (@lem3636346 A B)). Qed.
Lemma lem3636479 {A B : Type'} : (term456 A B) = (term457 A B).
Proof. exact (TRANS (@lem3636227 A B) (@lem3636348 A B)). Qed.
Lemma lem3636480 {A B : Type'} : (term457 A B) = (term456 A B).
Proof. exact (SYM (@lem3636479 A B)). Qed.
Lemma lem3636481 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term394 A B g s f t) : term394 A B g s f t.
Proof. exact (h1). Qed.
Lemma lem3636483 (p : Prop) : p = (term45 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3636484 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term434 A B t f g s) = (term458 A B t f g s).
Proof. exact (@lem3636483 (term434 A B t f g s)). Qed.
Lemma lem3636485 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term458 A B t f g s) = (term434 A B t f g s).
Proof. exact (SYM (@lem3636484 A B t f g s)). Qed.
Lemma lem3636486 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term459 A B t f g s) : term459 A B t f g s.
Proof. exact (h1). Qed.
Lemma lem3636497 {A B : Type'} (s : B -> Prop) (t : A -> Prop) (f : A -> B) (g : B -> A) (x : B) : (term378 A B s t f g x) = (term460 A B s t f g x).
Proof. exact (@lem17265 (s x) (term376 A B t f g x)). Qed.
Lemma lem3636498 {A B : Type'} (s : B -> Prop) (t : A -> Prop) (f : A -> B) (g : B -> A) : (term380 A B s t f g) = (term461 A B s t f g).
Proof. exact (fun_ext (fun x : B => @lem3636497 A B s t f g x)). Qed.
Lemma lem3636499 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3636500 {A B : Type'} (s : B -> Prop) (t : A -> Prop) (f : A -> B) (g : B -> A) : (term381 A B s t f g) = (term462 A B s t f g).
Proof. exact (MK_COMB (@lem3636499 B) (@lem3636498 A B s t f g)). Qed.
Lemma lem3636506 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term385 A B x f t x') = (term385 A B x f t x').
Proof. exact (eq_refl (term385 A B x f t x')). Qed.
Lemma lem3636507 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term387 A B x f t) = (term387 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3636506 A B x f t x')). Qed.
Lemma lem3636508 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3636509 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term388 A B x f t) = (term388 A B x f t).
Proof. exact (MK_COMB (@lem3636508 A) (@lem3636507 A B x f t)). Qed.
Lemma lem3636511 {B : Type'} (s : B -> Prop) (x : B) : (term67 B s x) = (term67 B s x).
Proof. exact (eq_refl (term67 B s x)). Qed.
Lemma lem3636512 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term463 A B s x f t) = (term463 A B s x f t).
Proof. exact (MK_COMB (@lem3636511 B s x) (@lem3636509 A B x f t)). Qed.
Lemma lem3636513 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term390 A B s x f t) = (term463 A B s x f t).
Proof. exact (@lem17265 (s x) (term388 A B x f t)). Qed.
Lemma lem3636514 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term390 A B s x f t) = (term463 A B s x f t).
Proof. exact (TRANS (@lem3636513 A B s x f t) (@lem3636512 A B s x f t)). Qed.
Lemma lem3636515 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term392 A B s f t) = (term464 A B s f t).
Proof. exact (fun_ext (fun x : B => @lem3636514 A B s x f t)). Qed.
Lemma lem3636516 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3636517 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term393 A B s f t) = (term465 A B s f t).
Proof. exact (MK_COMB (@lem3636516 B) (@lem3636515 A B s f t)). Qed.
Lemma lem3636518 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3636519 {A B : Type'} (s : B -> Prop) (t : A -> Prop) (f : A -> B) (g : B -> A) : (term382 A B s t f g) = (term466 A B s t f g).
Proof. exact (MK_COMB (@lem3636518) (@lem3636500 A B s t f g)). Qed.
Lemma lem3636520 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term394 A B g s f t) = (term467 A B g s f t).
Proof. exact (MK_COMB (@lem3636519 A B s t f g) (@lem3636517 A B s f t)). Qed.
Lemma lem3636651 {A : Type'} (P : Prop) (Q : A -> Prop) : (term71 A P Q) = (term72 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3636652 {A : Type'} (P : Prop) (Q : A -> Prop) : (term71 A P Q) = (term72 A P Q).
Proof. exact (@lem3636651 A P Q). Qed.
Lemma lem3636653 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term468 A B s x f t) = (term469 A B s x f t).
Proof. exact (@lem3636652 A (term75 B s x) (term387 A B x f t)). Qed.
Lemma lem3636654 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term470 A B x f t x') = (term385 A B x f t x').
Proof. exact (eq_refl (term470 A B x f t x')). Qed.
Lemma lem3636655 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term471 A B x f t) = (term387 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3636654 A B x f t x')). Qed.
Lemma lem3636656 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3636657 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term472 A B x f t) = (term388 A B x f t).
Proof. exact (MK_COMB (@lem3636656 A) (@lem3636655 A B x f t)). Qed.
Lemma lem3636658 {B : Type'} (s : B -> Prop) (x : B) : (term67 B s x) = (term67 B s x).
Proof. exact (eq_refl (term67 B s x)). Qed.
Lemma lem3636659 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term468 A B s x f t) = (term463 A B s x f t).
Proof. exact (MK_COMB (@lem3636658 B s x) (@lem3636657 A B x f t)). Qed.
Lemma lem3636660 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3636661 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term473 A B s x f t) = (term474 A B s x f t).
Proof. exact (MK_COMB (@lem3636660) (@lem3636659 A B s x f t)). Qed.
Lemma lem3636662 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term470 A B x f t x') = (term385 A B x f t x').
Proof. exact (eq_refl (term470 A B x f t x')). Qed.
Lemma lem3636663 {B : Type'} (s : B -> Prop) (x : B) : (term67 B s x) = (term67 B s x).
Proof. exact (eq_refl (term67 B s x)). Qed.
Lemma lem3636664 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term475 A B s x f t x') = (term476 A B s x f t x').
Proof. exact (MK_COMB (@lem3636663 B s x) (@lem3636662 A B x f t x')). Qed.
Lemma lem3636665 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term477 A B s x f t) = (term478 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3636664 A B s x f t x')). Qed.
Lemma lem3636666 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3636667 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term469 A B s x f t) = (term479 A B s x f t).
Proof. exact (MK_COMB (@lem3636666 A) (@lem3636665 A B s x f t)). Qed.
Lemma lem3636668 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term468 A B s x f t) = (term469 A B s x f t)) = ((term463 A B s x f t) = (term479 A B s x f t)).
Proof. exact (MK_COMB (@lem3636661 A B s x f t) (@lem3636667 A B s x f t)). Qed.
Lemma lem3636669 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term463 A B s x f t) = (term479 A B s x f t).
Proof. exact (EQ_MP (@lem3636668 A B s x f t) (@lem3636653 A B s x f t)). Qed.
Lemma lem3636670 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term464 A B s f t) = (term480 A B s f t).
Proof. exact (fun_ext (fun x : B => @lem3636669 A B s x f t)). Qed.
Lemma lem3636671 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3636672 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term465 A B s f t) = (term481 A B s f t).
Proof. exact (MK_COMB (@lem3636671 B) (@lem3636670 A B s f t)). Qed.
Lemma lem3636674 {A B : Type'} (P : type1413 A B) : (term88 A B P) = (term89 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3636675 {A B : Type'} (P : type1470 A B) : (term482 A B P) = (term483 A B P).
Proof. exact (@lem3636674 B A P). Qed.
Lemma lem3636676 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term484 A B s f t) = (term485 A B s f t).
Proof. exact (@lem3636675 A B (term486 A B s f t)). Qed.
Lemma lem3636677 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term487 A B s f t x) = (term478 A B s x f t).
Proof. exact (eq_refl (term487 A B s f t x)). Qed.
Lemma lem3636678 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3636679 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term488 A B s f t x x') = (term489 A B s x f t x').
Proof. exact (MK_COMB (@lem3636677 A B s x f t) (@lem3636678 A x')). Qed.
Lemma lem3636680 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term489 A B s x f t x') = (term476 A B s x f t x').
Proof. exact (eq_refl (term489 A B s x f t x')). Qed.
Lemma lem3636681 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term488 A B s f t x x') = (term476 A B s x f t x').
Proof. exact (TRANS (@lem3636679 A B s x f t x') (@lem3636680 A B s x f t x')). Qed.
Lemma lem3636682 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term490 A B s f t x) = (term478 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3636681 A B s x f t x')). Qed.
Lemma lem3636683 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3636684 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term491 A B s f t x) = (term479 A B s x f t).
Proof. exact (MK_COMB (@lem3636683 A) (@lem3636682 A B s x f t)). Qed.
Lemma lem3636685 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term492 A B s f t) = (term480 A B s f t).
Proof. exact (fun_ext (fun x : B => @lem3636684 A B s x f t)). Qed.
Lemma lem3636686 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3636687 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term484 A B s f t) = (term481 A B s f t).
Proof. exact (MK_COMB (@lem3636686 B) (@lem3636685 A B s f t)). Qed.
Lemma lem3636688 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3636689 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term493 A B s f t) = (term494 A B s f t).
Proof. exact (MK_COMB (@lem3636688) (@lem3636687 A B s f t)). Qed.
Lemma lem3636690 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term487 A B s f t x) = (term478 A B s x f t).
Proof. exact (eq_refl (term487 A B s f t x)). Qed.
Lemma lem3636691 {A B : Type'} (x : B -> A) (x' : B) : (x x') = (x x').
Proof. exact (eq_refl (x x')). Qed.
Lemma lem3636692 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x : B -> A) (x' : B) : (term495 A B s f t x x') = (term496 A B s f t x x').
Proof. exact (MK_COMB (@lem3636690 A B s x' f t) (@lem3636691 A B x x')). Qed.
Lemma lem3636693 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x : B -> A) (x' : B) : (term496 A B s f t x x') = (term497 A B s f t x x').
Proof. exact (eq_refl (term496 A B s f t x x')). Qed.
Lemma lem3636694 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x : B -> A) (x' : B) : (term495 A B s f t x x') = (term497 A B s f t x x').
Proof. exact (TRANS (@lem3636692 A B s f t x x') (@lem3636693 A B s f t x x')). Qed.
Lemma lem3636695 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x : B -> A) : (term498 A B s f t x) = (term499 A B s f t x).
Proof. exact (fun_ext (fun x' : B => @lem3636694 A B s f t x x')). Qed.
Lemma lem3636696 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3636697 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x : B -> A) : (term500 A B s f t x) = (term501 A B s f t x).
Proof. exact (MK_COMB (@lem3636696 B) (@lem3636695 A B s f t x)). Qed.
Lemma lem3636698 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term502 A B s f t) = (term503 A B s f t).
Proof. exact (fun_ext (fun x : B -> A => @lem3636697 A B s f t x)). Qed.
Lemma lem3636699 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem3636700 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term485 A B s f t) = (term504 A B s f t).
Proof. exact (MK_COMB (@lem3636699 A B) (@lem3636698 A B s f t)). Qed.
Lemma lem3636701 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : ((term484 A B s f t) = (term485 A B s f t)) = ((term481 A B s f t) = (term504 A B s f t)).
Proof. exact (MK_COMB (@lem3636689 A B s f t) (@lem3636700 A B s f t)). Qed.
Lemma lem3636702 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term481 A B s f t) = (term504 A B s f t).
Proof. exact (EQ_MP (@lem3636701 A B s f t) (@lem3636676 A B s f t)). Qed.
Lemma lem3636703 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term465 A B s f t) = (term504 A B s f t).
Proof. exact (TRANS (@lem3636672 A B s f t) (@lem3636702 A B s f t)). Qed.
Lemma lem3636704 {A B : Type'} (s : B -> Prop) (t : A -> Prop) (f : A -> B) (g : B -> A) : (term466 A B s t f g) = (term466 A B s t f g).
Proof. exact (eq_refl (term466 A B s t f g)). Qed.
Lemma lem3636705 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term467 A B g s f t) = (term505 A B g s f t).
Proof. exact (MK_COMB (@lem3636704 A B s t f g) (@lem3636703 A B s f t)). Qed.
Lemma lem3636707 {A : Type'} (P : Prop) (Q : A -> Prop) : (term506 A P Q) = (term507 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3636708 {A B : Type'} (P : Prop) (Q : type805 A B) : (term508 A B P Q) = (term509 A B P Q).
Proof. exact (@lem3636707 (B -> A) P Q). Qed.
Lemma lem3636709 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term510 A B g s f t) = (term511 A B g s f t).
Proof. exact (@lem3636708 A B (term462 A B s t f g) (term503 A B s f t)). Qed.
Lemma lem3636710 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x : B -> A) : (term512 A B s f t x) = (term501 A B s f t x).
Proof. exact (eq_refl (term512 A B s f t x)). Qed.
Lemma lem3636711 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term513 A B s f t) = (term503 A B s f t).
Proof. exact (fun_ext (fun x : B -> A => @lem3636710 A B s f t x)). Qed.
Lemma lem3636712 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem3636713 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term514 A B s f t) = (term504 A B s f t).
Proof. exact (MK_COMB (@lem3636712 A B) (@lem3636711 A B s f t)). Qed.
Lemma lem3636714 {A B : Type'} (s : B -> Prop) (t : A -> Prop) (f : A -> B) (g : B -> A) : (term466 A B s t f g) = (term466 A B s t f g).
Proof. exact (eq_refl (term466 A B s t f g)). Qed.
Lemma lem3636715 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term510 A B g s f t) = (term505 A B g s f t).
Proof. exact (MK_COMB (@lem3636714 A B s t f g) (@lem3636713 A B s f t)). Qed.
Lemma lem3636716 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3636717 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term515 A B g s f t) = (term516 A B g s f t).
Proof. exact (MK_COMB (@lem3636716) (@lem3636715 A B g s f t)). Qed.
Lemma lem3636718 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x : B -> A) : (term512 A B s f t x) = (term501 A B s f t x).
Proof. exact (eq_refl (term512 A B s f t x)). Qed.
Lemma lem3636719 {A B : Type'} (s : B -> Prop) (t : A -> Prop) (f : A -> B) (g : B -> A) : (term466 A B s t f g) = (term466 A B s t f g).
Proof. exact (eq_refl (term466 A B s t f g)). Qed.
Lemma lem3636720 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x : B -> A) : (term517 A B g s f t x) = (term518 A B g s f t x).
Proof. exact (MK_COMB (@lem3636719 A B s t f g) (@lem3636718 A B s f t x)). Qed.
Lemma lem3636721 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term519 A B g s f t) = (term520 A B g s f t).
Proof. exact (fun_ext (fun x : B -> A => @lem3636720 A B g s f t x)). Qed.
Lemma lem3636722 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem3636723 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term511 A B g s f t) = (term521 A B g s f t).
Proof. exact (MK_COMB (@lem3636722 A B) (@lem3636721 A B g s f t)). Qed.
Lemma lem3636724 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) : ((term510 A B g s f t) = (term511 A B g s f t)) = ((term505 A B g s f t) = (term521 A B g s f t)).
Proof. exact (MK_COMB (@lem3636717 A B g s f t) (@lem3636723 A B g s f t)). Qed.
Lemma lem3636725 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term505 A B g s f t) = (term521 A B g s f t).
Proof. exact (EQ_MP (@lem3636724 A B g s f t) (@lem3636709 A B g s f t)). Qed.
Lemma lem3636727 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term467 A B g s f t) = (term521 A B g s f t).
Proof. exact (TRANS (@lem3636705 A B g s f t) (@lem3636725 A B g s f t)). Qed.
Lemma lem3636728 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term394 A B g s f t) = (term521 A B g s f t).
Proof. exact (TRANS (@lem3636520 A B g s f t) (@lem3636727 A B g s f t)). Qed.
Lemma lem3636729 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term394 A B g s f t) : term521 A B g s f t.
Proof. exact (EQ_MP (@lem3636728 A B g s f t) (@lem3636481 A B g s f t h1)). Qed.
Lemma lem3636734 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) (x' : B) : (term21 A B x g s x') = (term21 A B x g s x').
Proof. exact (eq_refl (term21 A B x g s x')). Qed.
Lemma lem3636735 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term23 A B x g s) = (term23 A B x g s).
Proof. exact (fun_ext (fun x' : B => @lem3636734 A B x g s x')). Qed.
Lemma lem3636736 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3636737 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term24 A B x g s) = (term24 A B x g s).
Proof. exact (MK_COMB (@lem3636736 B) (@lem3636735 A B x g s)). Qed.
Lemma lem3636738 {A : Type'} (t : A -> Prop) (x : A) : (term75 A t x) = (term75 A t x).
Proof. exact (eq_refl (term75 A t x)). Qed.
Lemma lem3636739 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3636740 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term405 A B x g s) = (term405 A B x g s).
Proof. exact (MK_COMB (@lem3636739) (@lem3636737 A B x g s)). Qed.
Lemma lem3636741 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) (x : A) : (term522 A B g s t x) = (term522 A B g s t x).
Proof. exact (MK_COMB (@lem3636740 A B x g s) (@lem3636738 A t x)). Qed.
Lemma lem3636742 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) (x : A) : (term523 A B g s t x) = (term522 A B g s t x).
Proof. exact (@lem17362 (term24 A B x g s) (t x)). Qed.
Lemma lem3636743 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) (x : A) : (term523 A B g s t x) = (term522 A B g s t x).
Proof. exact (TRANS (@lem3636742 A B g s t x) (@lem3636741 A B g s t x)). Qed.
Lemma lem3636744 {A : Type'} (P : A -> Prop) : (term524 A P) = (term525 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3636745 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) : (term526 A B g s t) = (term527 A B g s t).
Proof. exact (@lem3636744 A (term401 A B g s t)). Qed.
Lemma lem3636746 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) (x : A) : (term528 A B g s t x) = (term399 A B g s t x).
Proof. exact (eq_refl (term528 A B g s t x)). Qed.
Lemma lem3636747 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3636748 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) (x : A) : (term529 A B g s t x) = (term523 A B g s t x).
Proof. exact (MK_COMB (@lem3636747) (@lem3636746 A B g s t x)). Qed.
Lemma lem3636749 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) (x : A) : (term529 A B g s t x) = (term522 A B g s t x).
Proof. exact (TRANS (@lem3636748 A B g s t x) (@lem3636743 A B g s t x)). Qed.
Lemma lem3636750 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) : (term530 A B g s t) = (term531 A B g s t).
Proof. exact (fun_ext (fun x : A => @lem3636749 A B g s t x)). Qed.
Lemma lem3636751 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3636752 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) : (term527 A B g s t) = (term532 A B g s t).
Proof. exact (MK_COMB (@lem3636751 A) (@lem3636750 A B g s t)). Qed.
Lemma lem3636753 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) : (term526 A B g s t) = (term532 A B g s t).
Proof. exact (TRANS (@lem3636745 A B g s t) (@lem3636752 A B g s t)). Qed.
Lemma lem3636758 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) (x' : B) : (term21 A B x g s x') = (term21 A B x g s x').
Proof. exact (eq_refl (term21 A B x g s x')). Qed.
Lemma lem3636759 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term23 A B x g s) = (term23 A B x g s).
Proof. exact (fun_ext (fun x' : B => @lem3636758 A B x g s x')). Qed.
Lemma lem3636760 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3636761 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term24 A B x g s) = (term24 A B x g s).
Proof. exact (MK_COMB (@lem3636760 B) (@lem3636759 A B x g s)). Qed.
Lemma lem3636766 {A B : Type'} (y : A) (g : B -> A) (s : B -> Prop) (x : B) : (term21 A B y g s x) = (term21 A B y g s x).
Proof. exact (eq_refl (term21 A B y g s x)). Qed.
Lemma lem3636767 {A B : Type'} (y : A) (g : B -> A) (s : B -> Prop) : (term23 A B y g s) = (term23 A B y g s).
Proof. exact (fun_ext (fun x : B => @lem3636766 A B y g s x)). Qed.
Lemma lem3636768 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3636769 {A B : Type'} (y : A) (g : B -> A) (s : B -> Prop) : (term24 A B y g s) = (term24 A B y g s).
Proof. exact (MK_COMB (@lem3636768 B) (@lem3636767 A B y g s)). Qed.
Lemma lem3636770 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3636771 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term405 A B x g s) = (term405 A B x g s).
Proof. exact (MK_COMB (@lem3636770) (@lem3636761 A B x g s)). Qed.
Lemma lem3636772 {A B : Type'} (x : A) (y : A) (g : B -> A) (s : B -> Prop) : (term407 A B x y g s) = (term407 A B x y g s).
Proof. exact (MK_COMB (@lem3636771 A B x g s) (@lem3636769 A B y g s)). Qed.
Lemma lem3636787 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term533 A B f x y) = (term534 A B f x y).
Proof. exact (@lem17646 ((f x) = (f y)) (x = y)). Qed.
Lemma lem3636788 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3636789 {A B : Type'} (x : A) (y : A) (g : B -> A) (s : B -> Prop) : (term535 A B x y g s) = (term535 A B x y g s).
Proof. exact (MK_COMB (@lem3636788) (@lem3636772 A B x y g s)). Qed.
Lemma lem3636790 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) (y : A) : (term536 A B g s f x y) = (term537 A B g s f x y).
Proof. exact (MK_COMB (@lem3636789 A B x y g s) (@lem3636787 A B f x y)). Qed.
Lemma lem3636791 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) (y : A) : (term538 A B g s f x y) = (term536 A B g s f x y).
Proof. exact (@lem17362 (term407 A B x y g s) (((f x) = (f y)) = (x = y))). Qed.
Lemma lem3636792 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) (y : A) : (term538 A B g s f x y) = (term537 A B g s f x y).
Proof. exact (TRANS (@lem3636791 A B g s f x y) (@lem3636790 A B g s f x y)). Qed.
Lemma lem3636793 {A : Type'} (P : A -> Prop) : (term524 A P) = (term525 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3636794 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) : (term539 A B g s f x) = (term540 A B g s f x).
Proof. exact (@lem3636793 A (term413 A B g s f x)). Qed.
Lemma lem3636795 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) (y : A) : (term541 A B g s f x y) = (term411 A B g s f x y).
Proof. exact (eq_refl (term541 A B g s f x y)). Qed.
Lemma lem3636796 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3636797 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) (y : A) : (term542 A B g s f x y) = (term538 A B g s f x y).
Proof. exact (MK_COMB (@lem3636796) (@lem3636795 A B g s f x y)). Qed.
Lemma lem3636798 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) (y : A) : (term542 A B g s f x y) = (term537 A B g s f x y).
Proof. exact (TRANS (@lem3636797 A B g s f x y) (@lem3636792 A B g s f x y)). Qed.
Lemma lem3636799 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) : (term543 A B g s f x) = (term544 A B g s f x).
Proof. exact (fun_ext (fun y : A => @lem3636798 A B g s f x y)). Qed.
Lemma lem3636800 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3636801 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) : (term540 A B g s f x) = (term545 A B g s f x).
Proof. exact (MK_COMB (@lem3636800 A) (@lem3636799 A B g s f x)). Qed.
Lemma lem3636802 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) : (term539 A B g s f x) = (term545 A B g s f x).
Proof. exact (TRANS (@lem3636794 A B g s f x) (@lem3636801 A B g s f x)). Qed.
Lemma lem3636803 {A : Type'} (P : A -> Prop) : (term524 A P) = (term525 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3636804 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) : (term546 A B g s f) = (term547 A B g s f).
Proof. exact (@lem3636803 A (term417 A B g s f)). Qed.
Lemma lem3636805 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) : (term548 A B g s f x) = (term415 A B g s f x).
Proof. exact (eq_refl (term548 A B g s f x)). Qed.
Lemma lem3636806 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3636807 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) : (term549 A B g s f x) = (term539 A B g s f x).
Proof. exact (MK_COMB (@lem3636806) (@lem3636805 A B g s f x)). Qed.
Lemma lem3636808 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) : (term549 A B g s f x) = (term545 A B g s f x).
Proof. exact (TRANS (@lem3636807 A B g s f x) (@lem3636802 A B g s f x)). Qed.
Lemma lem3636809 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) : (term550 A B g s f) = (term551 A B g s f).
Proof. exact (fun_ext (fun x : A => @lem3636808 A B g s f x)). Qed.
Lemma lem3636810 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3636811 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) : (term547 A B g s f) = (term552 A B g s f).
Proof. exact (MK_COMB (@lem3636810 A) (@lem3636809 A B g s f)). Qed.
Lemma lem3636812 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) : (term546 A B g s f) = (term552 A B g s f).
Proof. exact (TRANS (@lem3636804 A B g s f) (@lem3636811 A B g s f)). Qed.
Lemma lem3636825 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) (x' : B) : (term553 A B x g s x') = (term554 A B x g s x').
Proof. exact (@lem17045 (x = (g x')) (s x')). Qed.
Lemma lem3636828 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) (x' : B) : (term21 A B x g s x') = (term21 A B x g s x').
Proof. exact (eq_refl (term21 A B x g s x')). Qed.
Lemma lem3636829 {B : Type'} (P : B -> Prop) : (term113 B P) = (term114 B P).
Proof. exact (@lem18394 B P). Qed.
Lemma lem3636830 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term555 A B x g s) = (term556 A B x g s).
Proof. exact (@lem3636829 B (term23 A B x g s)). Qed.
Lemma lem3636831 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) (x' : B) : (term76 A B x g s x') = (term21 A B x g s x').
Proof. exact (eq_refl (term76 A B x g s x')). Qed.
Lemma lem3636832 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3636833 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) (x' : B) : (term557 A B x g s x') = (term553 A B x g s x').
Proof. exact (MK_COMB (@lem3636832) (@lem3636831 A B x g s x')). Qed.
Lemma lem3636834 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) (x' : B) : (term557 A B x g s x') = (term554 A B x g s x').
Proof. exact (TRANS (@lem3636833 A B x g s x') (@lem3636825 A B x g s x')). Qed.
Lemma lem3636835 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term558 A B x g s) = (term559 A B x g s).
Proof. exact (fun_ext (fun x' : B => @lem3636834 A B x g s x')). Qed.
Lemma lem3636836 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3636837 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term556 A B x g s) = (term560 A B x g s).
Proof. exact (MK_COMB (@lem3636836 B) (@lem3636835 A B x g s)). Qed.
Lemma lem3636838 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term555 A B x g s) = (term560 A B x g s).
Proof. exact (TRANS (@lem3636830 A B x g s) (@lem3636837 A B x g s)). Qed.
Lemma lem3636839 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term23 A B x g s) = (term23 A B x g s).
Proof. exact (fun_ext (fun x' : B => @lem3636828 A B x g s x')). Qed.
Lemma lem3636840 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3636841 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term24 A B x g s) = (term24 A B x g s).
Proof. exact (MK_COMB (@lem3636840 B) (@lem3636839 A B x g s)). Qed.
Lemma lem3636843 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term561 A B x f x') = (term561 A B x f x').
Proof. exact (eq_refl (term561 A B x f x')). Qed.
Lemma lem3636844 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term562 A B x f x' g s) = (term563 A B x f x' g s).
Proof. exact (MK_COMB (@lem3636843 A B x f x') (@lem3636838 A B x' g s)). Qed.
Lemma lem3636845 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term564 A B x f x' g s) = (term562 A B x f x' g s).
Proof. exact (@lem17045 (x = (f x')) (term24 A B x' g s)). Qed.
Lemma lem3636846 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term564 A B x f x' g s) = (term563 A B x f x' g s).
Proof. exact (TRANS (@lem3636845 A B x f x' g s) (@lem3636844 A B x f x' g s)). Qed.
Lemma lem3636848 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term383 A B x f x') = (term383 A B x f x').
Proof. exact (eq_refl (term383 A B x f x')). Qed.
Lemma lem3636849 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term426 A B x f x' g s) = (term426 A B x f x' g s).
Proof. exact (MK_COMB (@lem3636848 A B x f x') (@lem3636841 A B x' g s)). Qed.
Lemma lem3636850 {A : Type'} (P : A -> Prop) : (term113 A P) = (term114 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3636851 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term565 A B x f g s) = (term566 A B x f g s).
Proof. exact (@lem3636850 A (term428 A B x f g s)). Qed.
Lemma lem3636852 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term567 A B x f g s x') = (term426 A B x f x' g s).
Proof. exact (eq_refl (term567 A B x f g s x')). Qed.
Lemma lem3636853 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3636854 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term568 A B x f g s x') = (term564 A B x f x' g s).
Proof. exact (MK_COMB (@lem3636853) (@lem3636852 A B x f x' g s)). Qed.
Lemma lem3636855 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term568 A B x f g s x') = (term563 A B x f x' g s).
Proof. exact (TRANS (@lem3636854 A B x f x' g s) (@lem3636846 A B x f x' g s)). Qed.
Lemma lem3636856 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term569 A B x f g s) = (term570 A B x f g s).
Proof. exact (fun_ext (fun x' : A => @lem3636855 A B x f x' g s)). Qed.
Lemma lem3636857 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3636858 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term566 A B x f g s) = (term571 A B x f g s).
Proof. exact (MK_COMB (@lem3636857 A) (@lem3636856 A B x f g s)). Qed.
Lemma lem3636859 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term565 A B x f g s) = (term571 A B x f g s).
Proof. exact (TRANS (@lem3636851 A B x f g s) (@lem3636858 A B x f g s)). Qed.
Lemma lem3636860 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term428 A B x f g s) = (term428 A B x f g s).
Proof. exact (fun_ext (fun x' : A => @lem3636849 A B x f x' g s)). Qed.
Lemma lem3636861 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3636862 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term429 A B x f g s) = (term429 A B x f g s).
Proof. exact (MK_COMB (@lem3636861 A) (@lem3636860 A B x f g s)). Qed.
Lemma lem3636864 {B : Type'} (s : B -> Prop) (x : B) : (term572 B s x) = (term572 B s x).
Proof. exact (eq_refl (term572 B s x)). Qed.
Lemma lem3636865 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term573 A B x f g s) = (term573 A B x f g s).
Proof. exact (MK_COMB (@lem3636864 B s x) (@lem3636862 A B x f g s)). Qed.
Lemma lem3636867 {B : Type'} (s : B -> Prop) (x : B) : (term32 B s x) = (term32 B s x).
Proof. exact (eq_refl (term32 B s x)). Qed.
Lemma lem3636868 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term574 A B x f g s) = (term575 A B x f g s).
Proof. exact (MK_COMB (@lem3636867 B s x) (@lem3636859 A B x f g s)). Qed.
Lemma lem3636869 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3636870 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term576 A B x f g s) = (term577 A B x f g s).
Proof. exact (MK_COMB (@lem3636869) (@lem3636868 A B x f g s)). Qed.
Lemma lem3636871 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term578 A B x f g s) = (term579 A B x f g s).
Proof. exact (MK_COMB (@lem3636870 A B x f g s) (@lem3636865 A B x f g s)). Qed.
Lemma lem3636872 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term580 A B x f g s) = (term578 A B x f g s).
Proof. exact (@lem17646 (s x) (term429 A B x f g s)). Qed.
Lemma lem3636873 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term580 A B x f g s) = (term579 A B x f g s).
Proof. exact (TRANS (@lem3636872 A B x f g s) (@lem3636871 A B x f g s)). Qed.
Lemma lem3636874 {B : Type'} (P : B -> Prop) : (term524 B P) = (term525 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem3636875 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term581 A B f g s) = (term582 A B f g s).
Proof. exact (@lem3636874 B (term431 A B f g s)). Qed.
Lemma lem3636876 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term583 A B f g s x) = ((s x) = (term429 A B x f g s)).
Proof. exact (eq_refl (term583 A B f g s x)). Qed.
Lemma lem3636877 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3636878 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term584 A B f g s x) = (term580 A B x f g s).
Proof. exact (MK_COMB (@lem3636877) (@lem3636876 A B x f g s)). Qed.
Lemma lem3636879 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term584 A B f g s x) = (term579 A B x f g s).
Proof. exact (TRANS (@lem3636878 A B x f g s) (@lem3636873 A B x f g s)). Qed.
Lemma lem3636880 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term585 A B f g s) = (term586 A B f g s).
Proof. exact (fun_ext (fun x : B => @lem3636879 A B x f g s)). Qed.
Lemma lem3636881 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3636882 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term582 A B f g s) = (term587 A B f g s).
Proof. exact (MK_COMB (@lem3636881 B) (@lem3636880 A B f g s)). Qed.
Lemma lem3636883 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term581 A B f g s) = (term587 A B f g s).
Proof. exact (TRANS (@lem3636875 A B f g s) (@lem3636882 A B f g s)). Qed.
Lemma lem3636884 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3636885 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) : (term588 A B g s f) = (term589 A B g s f).
Proof. exact (MK_COMB (@lem3636884) (@lem3636812 A B g s f)). Qed.
Lemma lem3636886 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term590 A B f g s) = (term591 A B f g s).
Proof. exact (MK_COMB (@lem3636885 A B g s f) (@lem3636883 A B f g s)). Qed.
Lemma lem3636887 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term592 A B f g s) = (term590 A B f g s).
Proof. exact (@lem17045 (term419 A B g s f) (term432 A B f g s)). Qed.
Lemma lem3636888 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term592 A B f g s) = (term591 A B f g s).
Proof. exact (TRANS (@lem3636887 A B f g s) (@lem3636886 A B f g s)). Qed.
Lemma lem3636889 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3636890 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) : (term593 A B g s t) = (term594 A B g s t).
Proof. exact (MK_COMB (@lem3636889) (@lem3636753 A B g s t)). Qed.
Lemma lem3636891 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term595 A B t f g s) = (term596 A B t f g s).
Proof. exact (MK_COMB (@lem3636890 A B g s t) (@lem3636888 A B f g s)). Qed.
Lemma lem3636892 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term459 A B t f g s) = (term595 A B t f g s).
Proof. exact (@lem17045 (term402 A B g s t) (term433 A B f g s)). Qed.
Lemma lem3636893 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term459 A B t f g s) = (term596 A B t f g s).
Proof. exact (TRANS (@lem3636892 A B t f g s) (@lem3636891 A B t f g s)). Qed.
Lemma lem3637091 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term597 A P Q) = (term598 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3637092 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term597 B P Q) = (term598 B P Q).
Proof. exact (@lem3637091 B P Q). Qed.
Lemma lem3637093 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term599 A B f g s) = (term600 A B f g s).
Proof. exact (@lem3637092 B (term601 A B f g s) (term602 A B f g s)). Qed.
Lemma lem3637094 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term603 A B f g s x) = (term575 A B x f g s).
Proof. exact (eq_refl (term603 A B f g s x)). Qed.
Lemma lem3637095 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3637096 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term604 A B f g s x) = (term577 A B x f g s).
Proof. exact (MK_COMB (@lem3637095) (@lem3637094 A B x f g s)). Qed.
Lemma lem3637097 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term605 A B f g s x) = (term573 A B x f g s).
Proof. exact (eq_refl (term605 A B f g s x)). Qed.
Lemma lem3637098 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term606 A B f g s x) = (term579 A B x f g s).
Proof. exact (MK_COMB (@lem3637096 A B x f g s) (@lem3637097 A B x f g s)). Qed.
Lemma lem3637099 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term607 A B f g s) = (term586 A B f g s).
Proof. exact (fun_ext (fun x : B => @lem3637098 A B x f g s)). Qed.
Lemma lem3637100 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637101 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term599 A B f g s) = (term587 A B f g s).
Proof. exact (MK_COMB (@lem3637100 B) (@lem3637099 A B f g s)). Qed.
Lemma lem3637102 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3637103 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term608 A B f g s) = (term609 A B f g s).
Proof. exact (MK_COMB (@lem3637102) (@lem3637101 A B f g s)). Qed.
Lemma lem3637104 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term603 A B f g s x) = (term575 A B x f g s).
Proof. exact (eq_refl (term603 A B f g s x)). Qed.
Lemma lem3637105 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term610 A B f g s) = (term601 A B f g s).
Proof. exact (fun_ext (fun x : B => @lem3637104 A B x f g s)). Qed.
Lemma lem3637106 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637107 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term611 A B f g s) = (term612 A B f g s).
Proof. exact (MK_COMB (@lem3637106 B) (@lem3637105 A B f g s)). Qed.
Lemma lem3637108 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3637109 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term613 A B f g s) = (term614 A B f g s).
Proof. exact (MK_COMB (@lem3637108) (@lem3637107 A B f g s)). Qed.
Lemma lem3637110 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term605 A B f g s x) = (term573 A B x f g s).
Proof. exact (eq_refl (term605 A B f g s x)). Qed.
Lemma lem3637111 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term615 A B f g s) = (term602 A B f g s).
Proof. exact (fun_ext (fun x : B => @lem3637110 A B x f g s)). Qed.
Lemma lem3637112 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637113 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term616 A B f g s) = (term617 A B f g s).
Proof. exact (MK_COMB (@lem3637112 B) (@lem3637111 A B f g s)). Qed.
Lemma lem3637114 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term600 A B f g s) = (term618 A B f g s).
Proof. exact (MK_COMB (@lem3637109 A B f g s) (@lem3637113 A B f g s)). Qed.
Lemma lem3637115 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : ((term599 A B f g s) = (term600 A B f g s)) = ((term587 A B f g s) = (term618 A B f g s)).
Proof. exact (MK_COMB (@lem3637103 A B f g s) (@lem3637114 A B f g s)). Qed.
Lemma lem3637116 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term587 A B f g s) = (term618 A B f g s).
Proof. exact (EQ_MP (@lem3637115 A B f g s) (@lem3637093 A B f g s)). Qed.
Lemma lem3637369 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) : (term589 A B g s f) = (term589 A B g s f).
Proof. exact (eq_refl (term589 A B g s f)). Qed.
Lemma lem3637370 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term591 A B f g s) = (term619 A B f g s).
Proof. exact (MK_COMB (@lem3637369 A B g s f) (@lem3637116 A B f g s)). Qed.
Lemma lem3637371 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) : (term594 A B g s t) = (term594 A B g s t).
Proof. exact (eq_refl (term594 A B g s t)). Qed.
Lemma lem3637372 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term596 A B t f g s) = (term620 A B t f g s).
Proof. exact (MK_COMB (@lem3637371 A B g s t) (@lem3637370 A B f g s)). Qed.
Lemma lem3637374 {A : Type'} (P : A -> Prop) (Q : Prop) : (term269 A P Q) = (term270 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3637375 {B : Type'} (P : B -> Prop) (Q : Prop) : (term269 B P Q) = (term270 B P Q).
Proof. exact (@lem3637374 B P Q). Qed.
Lemma lem3637376 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) (x : A) : (term621 A B g s t x) = (term622 A B g s t x).
Proof. exact (@lem3637375 B (term23 A B x g s) (term75 A t x)). Qed.
Lemma lem3637377 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) (x' : B) : (term76 A B x g s x') = (term21 A B x g s x').
Proof. exact (eq_refl (term76 A B x g s x')). Qed.
Lemma lem3637378 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term77 A B x g s) = (term23 A B x g s).
Proof. exact (fun_ext (fun x' : B => @lem3637377 A B x g s x')). Qed.
Lemma lem3637379 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637380 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term78 A B x g s) = (term24 A B x g s).
Proof. exact (MK_COMB (@lem3637379 B) (@lem3637378 A B x g s)). Qed.
Lemma lem3637381 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3637382 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term623 A B x g s) = (term405 A B x g s).
Proof. exact (MK_COMB (@lem3637381) (@lem3637380 A B x g s)). Qed.
Lemma lem3637383 {A : Type'} (t : A -> Prop) (x : A) : (term75 A t x) = (term75 A t x).
Proof. exact (eq_refl (term75 A t x)). Qed.
Lemma lem3637384 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) (x : A) : (term621 A B g s t x) = (term522 A B g s t x).
Proof. exact (MK_COMB (@lem3637382 A B x g s) (@lem3637383 A t x)). Qed.
Lemma lem3637385 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3637386 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) (x : A) : (term624 A B g s t x) = (term625 A B g s t x).
Proof. exact (MK_COMB (@lem3637385) (@lem3637384 A B g s t x)). Qed.
Lemma lem3637387 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) (x' : B) : (term76 A B x g s x') = (term21 A B x g s x').
Proof. exact (eq_refl (term76 A B x g s x')). Qed.
Lemma lem3637388 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3637389 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) (x' : B) : (term626 A B x g s x') = (term627 A B x g s x').
Proof. exact (MK_COMB (@lem3637388) (@lem3637387 A B x g s x')). Qed.
Lemma lem3637390 {A : Type'} (t : A -> Prop) (x : A) : (term75 A t x) = (term75 A t x).
Proof. exact (eq_refl (term75 A t x)). Qed.
Lemma lem3637391 {A B : Type'} (g : B -> A) (s : B -> Prop) (x : B) (t : A -> Prop) (x' : A) : (term628 A B g s x t x') = (term629 A B g s x t x').
Proof. exact (MK_COMB (@lem3637389 A B x' g s x) (@lem3637390 A t x')). Qed.
Lemma lem3637392 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) (x : A) : (term630 A B g s t x) = (term631 A B g s t x).
Proof. exact (fun_ext (fun x' : B => @lem3637391 A B g s x' t x)). Qed.
Lemma lem3637393 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637394 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) (x : A) : (term622 A B g s t x) = (term632 A B g s t x).
Proof. exact (MK_COMB (@lem3637393 B) (@lem3637392 A B g s t x)). Qed.
Lemma lem3637395 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) (x : A) : ((term621 A B g s t x) = (term622 A B g s t x)) = ((term522 A B g s t x) = (term632 A B g s t x)).
Proof. exact (MK_COMB (@lem3637386 A B g s t x) (@lem3637394 A B g s t x)). Qed.
Lemma lem3637396 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) (x : A) : (term522 A B g s t x) = (term632 A B g s t x).
Proof. exact (EQ_MP (@lem3637395 A B g s t x) (@lem3637376 A B g s t x)). Qed.
Lemma lem3637397 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) : (term531 A B g s t) = (term633 A B g s t).
Proof. exact (fun_ext (fun x : A => @lem3637396 A B g s t x)). Qed.
Lemma lem3637398 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3637399 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) : (term532 A B g s t) = (term634 A B g s t).
Proof. exact (MK_COMB (@lem3637398 A) (@lem3637397 A B g s t)). Qed.
Lemma lem3637400 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3637401 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) : (term594 A B g s t) = (term635 A B g s t).
Proof. exact (MK_COMB (@lem3637400) (@lem3637399 A B g s t)). Qed.
Lemma lem3637403 {A : Type'} (P : A -> Prop) (Q : Prop) : (term269 A P Q) = (term270 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3637404 {B : Type'} (P : B -> Prop) (Q : Prop) : (term269 B P Q) = (term270 B P Q).
Proof. exact (@lem3637403 B P Q). Qed.
Lemma lem3637405 {A B : Type'} (x : A) (y : A) (g : B -> A) (s : B -> Prop) : (term636 A B x y g s) = (term637 A B x y g s).
Proof. exact (@lem3637404 B (term23 A B x g s) (term24 A B y g s)). Qed.
Lemma lem3637406 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) (x' : B) : (term76 A B x g s x') = (term21 A B x g s x').
Proof. exact (eq_refl (term76 A B x g s x')). Qed.
Lemma lem3637407 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term77 A B x g s) = (term23 A B x g s).
Proof. exact (fun_ext (fun x' : B => @lem3637406 A B x g s x')). Qed.
Lemma lem3637408 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637409 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term78 A B x g s) = (term24 A B x g s).
Proof. exact (MK_COMB (@lem3637408 B) (@lem3637407 A B x g s)). Qed.
Lemma lem3637410 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3637411 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term623 A B x g s) = (term405 A B x g s).
Proof. exact (MK_COMB (@lem3637410) (@lem3637409 A B x g s)). Qed.
Lemma lem3637412 {A B : Type'} (y : A) (g : B -> A) (s : B -> Prop) : (term24 A B y g s) = (term24 A B y g s).
Proof. exact (eq_refl (term24 A B y g s)). Qed.
Lemma lem3637413 {A B : Type'} (x : A) (y : A) (g : B -> A) (s : B -> Prop) : (term636 A B x y g s) = (term407 A B x y g s).
Proof. exact (MK_COMB (@lem3637411 A B x g s) (@lem3637412 A B y g s)). Qed.
Lemma lem3637414 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3637415 {A B : Type'} (x : A) (y : A) (g : B -> A) (s : B -> Prop) : (term638 A B x y g s) = (term639 A B x y g s).
Proof. exact (MK_COMB (@lem3637414) (@lem3637413 A B x y g s)). Qed.
Lemma lem3637416 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) (x' : B) : (term76 A B x g s x') = (term21 A B x g s x').
Proof. exact (eq_refl (term76 A B x g s x')). Qed.
Lemma lem3637417 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3637418 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) (x' : B) : (term626 A B x g s x') = (term627 A B x g s x').
Proof. exact (MK_COMB (@lem3637417) (@lem3637416 A B x g s x')). Qed.
Lemma lem3637419 {A B : Type'} (y : A) (g : B -> A) (s : B -> Prop) : (term24 A B y g s) = (term24 A B y g s).
Proof. exact (eq_refl (term24 A B y g s)). Qed.
Lemma lem3637420 {A B : Type'} (x : A) (x' : B) (y : A) (g : B -> A) (s : B -> Prop) : (term640 A B x x' y g s) = (term641 A B x x' y g s).
Proof. exact (MK_COMB (@lem3637418 A B x g s x') (@lem3637419 A B y g s)). Qed.
Lemma lem3637421 {A B : Type'} (x : A) (y : A) (g : B -> A) (s : B -> Prop) : (term642 A B x y g s) = (term643 A B x y g s).
Proof. exact (fun_ext (fun x' : B => @lem3637420 A B x x' y g s)). Qed.
Lemma lem3637422 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637423 {A B : Type'} (x : A) (y : A) (g : B -> A) (s : B -> Prop) : (term637 A B x y g s) = (term644 A B x y g s).
Proof. exact (MK_COMB (@lem3637422 B) (@lem3637421 A B x y g s)). Qed.
Lemma lem3637424 {A B : Type'} (x : A) (y : A) (g : B -> A) (s : B -> Prop) : ((term636 A B x y g s) = (term637 A B x y g s)) = ((term407 A B x y g s) = (term644 A B x y g s)).
Proof. exact (MK_COMB (@lem3637415 A B x y g s) (@lem3637423 A B x y g s)). Qed.
Lemma lem3637425 {A B : Type'} (x : A) (y : A) (g : B -> A) (s : B -> Prop) : (term407 A B x y g s) = (term644 A B x y g s).
Proof. exact (EQ_MP (@lem3637424 A B x y g s) (@lem3637405 A B x y g s)). Qed.
Lemma lem3637427 {A : Type'} (P : Prop) (Q : A -> Prop) : (term506 A P Q) = (term507 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3637428 {B : Type'} (P : Prop) (Q : B -> Prop) : (term506 B P Q) = (term507 B P Q).
Proof. exact (@lem3637427 B P Q). Qed.
Lemma lem3637429 {A B : Type'} (x : A) (x' : B) (y : A) (g : B -> A) (s : B -> Prop) : (term645 A B x x' y g s) = (term646 A B x x' y g s).
Proof. exact (@lem3637428 B (term21 A B x g s x') (term23 A B y g s)). Qed.
Lemma lem3637430 {A B : Type'} (y : A) (g : B -> A) (s : B -> Prop) (x : B) : (term76 A B y g s x) = (term21 A B y g s x).
Proof. exact (eq_refl (term76 A B y g s x)). Qed.
Lemma lem3637431 {A B : Type'} (y : A) (g : B -> A) (s : B -> Prop) : (term77 A B y g s) = (term23 A B y g s).
Proof. exact (fun_ext (fun x : B => @lem3637430 A B y g s x)). Qed.
Lemma lem3637432 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637433 {A B : Type'} (y : A) (g : B -> A) (s : B -> Prop) : (term78 A B y g s) = (term24 A B y g s).
Proof. exact (MK_COMB (@lem3637432 B) (@lem3637431 A B y g s)). Qed.
Lemma lem3637434 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) (x' : B) : (term627 A B x g s x') = (term627 A B x g s x').
Proof. exact (eq_refl (term627 A B x g s x')). Qed.
Lemma lem3637435 {A B : Type'} (x : A) (x' : B) (y : A) (g : B -> A) (s : B -> Prop) : (term645 A B x x' y g s) = (term641 A B x x' y g s).
Proof. exact (MK_COMB (@lem3637434 A B x g s x') (@lem3637433 A B y g s)). Qed.
Lemma lem3637436 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3637437 {A B : Type'} (x : A) (x' : B) (y : A) (g : B -> A) (s : B -> Prop) : (term647 A B x x' y g s) = (term648 A B x x' y g s).
Proof. exact (MK_COMB (@lem3637436) (@lem3637435 A B x x' y g s)). Qed.
Lemma lem3637438 {A B : Type'} (y : A) (g : B -> A) (s : B -> Prop) (x' : B) : (term76 A B y g s x') = (term21 A B y g s x').
Proof. exact (eq_refl (term76 A B y g s x')). Qed.
Lemma lem3637439 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) (x' : B) : (term627 A B x g s x') = (term627 A B x g s x').
Proof. exact (eq_refl (term627 A B x g s x')). Qed.
Lemma lem3637440 {A B : Type'} (x : A) (x' : B) (y : A) (g : B -> A) (s : B -> Prop) (x'' : B) : (term649 A B x x' y g s x'') = (term650 A B x x' y g s x'').
Proof. exact (MK_COMB (@lem3637439 A B x g s x') (@lem3637438 A B y g s x'')). Qed.
Lemma lem3637441 {A B : Type'} (x : A) (x' : B) (y : A) (g : B -> A) (s : B -> Prop) : (term651 A B x x' y g s) = (term652 A B x x' y g s).
Proof. exact (fun_ext (fun x'' : B => @lem3637440 A B x x' y g s x'')). Qed.
Lemma lem3637442 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637443 {A B : Type'} (x : A) (x' : B) (y : A) (g : B -> A) (s : B -> Prop) : (term646 A B x x' y g s) = (term653 A B x x' y g s).
Proof. exact (MK_COMB (@lem3637442 B) (@lem3637441 A B x x' y g s)). Qed.
Lemma lem3637444 {A B : Type'} (x : A) (x' : B) (y : A) (g : B -> A) (s : B -> Prop) : ((term645 A B x x' y g s) = (term646 A B x x' y g s)) = ((term641 A B x x' y g s) = (term653 A B x x' y g s)).
Proof. exact (MK_COMB (@lem3637437 A B x x' y g s) (@lem3637443 A B x x' y g s)). Qed.
Lemma lem3637445 {A B : Type'} (x : A) (x' : B) (y : A) (g : B -> A) (s : B -> Prop) : (term641 A B x x' y g s) = (term653 A B x x' y g s).
Proof. exact (EQ_MP (@lem3637444 A B x x' y g s) (@lem3637429 A B x x' y g s)). Qed.
Lemma lem3637446 {A B : Type'} (x : A) (y : A) (g : B -> A) (s : B -> Prop) : (term643 A B x y g s) = (term654 A B x y g s).
Proof. exact (fun_ext (fun x' : B => @lem3637445 A B x x' y g s)). Qed.
Lemma lem3637447 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637448 {A B : Type'} (x : A) (y : A) (g : B -> A) (s : B -> Prop) : (term644 A B x y g s) = (term655 A B x y g s).
Proof. exact (MK_COMB (@lem3637447 B) (@lem3637446 A B x y g s)). Qed.
Lemma lem3637449 {A B : Type'} (x : A) (y : A) (g : B -> A) (s : B -> Prop) : (term407 A B x y g s) = (term655 A B x y g s).
Proof. exact (TRANS (@lem3637425 A B x y g s) (@lem3637448 A B x y g s)). Qed.
Lemma lem3637450 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3637451 {A B : Type'} (x : A) (y : A) (g : B -> A) (s : B -> Prop) : (term535 A B x y g s) = (term656 A B x y g s).
Proof. exact (MK_COMB (@lem3637450) (@lem3637449 A B x y g s)). Qed.
Lemma lem3637452 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term534 A B f x y) = (term534 A B f x y).
Proof. exact (eq_refl (term534 A B f x y)). Qed.
Lemma lem3637453 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) (y : A) : (term537 A B g s f x y) = (term657 A B g s f x y).
Proof. exact (MK_COMB (@lem3637451 A B x y g s) (@lem3637452 A B f x y)). Qed.
Lemma lem3637455 {A : Type'} (P : A -> Prop) (Q : Prop) : (term269 A P Q) = (term270 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3637456 {B : Type'} (P : B -> Prop) (Q : Prop) : (term269 B P Q) = (term270 B P Q).
Proof. exact (@lem3637455 B P Q). Qed.
Lemma lem3637457 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) (y : A) : (term658 A B g s f x y) = (term659 A B g s f x y).
Proof. exact (@lem3637456 B (term654 A B x y g s) (term534 A B f x y)). Qed.
Lemma lem3637458 {A B : Type'} (x : A) (x' : B) (y : A) (g : B -> A) (s : B -> Prop) : (term660 A B x y g s x') = (term653 A B x x' y g s).
Proof. exact (eq_refl (term660 A B x y g s x')). Qed.
Lemma lem3637459 {A B : Type'} (x : A) (y : A) (g : B -> A) (s : B -> Prop) : (term661 A B x y g s) = (term654 A B x y g s).
Proof. exact (fun_ext (fun x' : B => @lem3637458 A B x x' y g s)). Qed.
Lemma lem3637460 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637461 {A B : Type'} (x : A) (y : A) (g : B -> A) (s : B -> Prop) : (term662 A B x y g s) = (term655 A B x y g s).
Proof. exact (MK_COMB (@lem3637460 B) (@lem3637459 A B x y g s)). Qed.
Lemma lem3637462 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3637463 {A B : Type'} (x : A) (y : A) (g : B -> A) (s : B -> Prop) : (term663 A B x y g s) = (term656 A B x y g s).
Proof. exact (MK_COMB (@lem3637462) (@lem3637461 A B x y g s)). Qed.
Lemma lem3637464 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term534 A B f x y) = (term534 A B f x y).
Proof. exact (eq_refl (term534 A B f x y)). Qed.
Lemma lem3637465 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) (y : A) : (term658 A B g s f x y) = (term657 A B g s f x y).
Proof. exact (MK_COMB (@lem3637463 A B x y g s) (@lem3637464 A B f x y)). Qed.
Lemma lem3637466 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3637467 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) (y : A) : (term664 A B g s f x y) = (term665 A B g s f x y).
Proof. exact (MK_COMB (@lem3637466) (@lem3637465 A B g s f x y)). Qed.
Lemma lem3637468 {A B : Type'} (x : A) (x' : B) (y : A) (g : B -> A) (s : B -> Prop) : (term660 A B x y g s x') = (term653 A B x x' y g s).
Proof. exact (eq_refl (term660 A B x y g s x')). Qed.
Lemma lem3637469 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3637470 {A B : Type'} (x : A) (x' : B) (y : A) (g : B -> A) (s : B -> Prop) : (term666 A B x y g s x') = (term667 A B x x' y g s).
Proof. exact (MK_COMB (@lem3637469) (@lem3637468 A B x x' y g s)). Qed.
Lemma lem3637471 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term534 A B f x y) = (term534 A B f x y).
Proof. exact (eq_refl (term534 A B f x y)). Qed.
Lemma lem3637472 {A B : Type'} (x : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (x' : A) (y : A) : (term668 A B g s x f x' y) = (term669 A B x g s f x' y).
Proof. exact (MK_COMB (@lem3637470 A B x' x y g s) (@lem3637471 A B f x' y)). Qed.
Lemma lem3637473 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) (y : A) : (term670 A B g s f x y) = (term671 A B g s f x y).
Proof. exact (fun_ext (fun x' : B => @lem3637472 A B x' g s f x y)). Qed.
Lemma lem3637474 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637475 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) (y : A) : (term659 A B g s f x y) = (term672 A B g s f x y).
Proof. exact (MK_COMB (@lem3637474 B) (@lem3637473 A B g s f x y)). Qed.
Lemma lem3637476 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) (y : A) : ((term658 A B g s f x y) = (term659 A B g s f x y)) = ((term657 A B g s f x y) = (term672 A B g s f x y)).
Proof. exact (MK_COMB (@lem3637467 A B g s f x y) (@lem3637475 A B g s f x y)). Qed.
Lemma lem3637477 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) (y : A) : (term657 A B g s f x y) = (term672 A B g s f x y).
Proof. exact (EQ_MP (@lem3637476 A B g s f x y) (@lem3637457 A B g s f x y)). Qed.
Lemma lem3637479 {A : Type'} (P : A -> Prop) (Q : Prop) : (term269 A P Q) = (term270 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3637480 {B : Type'} (P : B -> Prop) (Q : Prop) : (term269 B P Q) = (term270 B P Q).
Proof. exact (@lem3637479 B P Q). Qed.
Lemma lem3637481 {A B : Type'} (x : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (x' : A) (y : A) : (term673 A B x g s f x' y) = (term674 A B x g s f x' y).
Proof. exact (@lem3637480 B (term652 A B x' x y g s) (term534 A B f x' y)). Qed.
Lemma lem3637482 {A B : Type'} (x : A) (x' : B) (y : A) (g : B -> A) (s : B -> Prop) (x'' : B) : (term675 A B x x' y g s x'') = (term650 A B x x' y g s x'').
Proof. exact (eq_refl (term675 A B x x' y g s x'')). Qed.
Lemma lem3637483 {A B : Type'} (x : A) (x' : B) (y : A) (g : B -> A) (s : B -> Prop) : (term676 A B x x' y g s) = (term652 A B x x' y g s).
Proof. exact (fun_ext (fun x'' : B => @lem3637482 A B x x' y g s x'')). Qed.
Lemma lem3637484 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637485 {A B : Type'} (x : A) (x' : B) (y : A) (g : B -> A) (s : B -> Prop) : (term677 A B x x' y g s) = (term653 A B x x' y g s).
Proof. exact (MK_COMB (@lem3637484 B) (@lem3637483 A B x x' y g s)). Qed.
Lemma lem3637486 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3637487 {A B : Type'} (x : A) (x' : B) (y : A) (g : B -> A) (s : B -> Prop) : (term678 A B x x' y g s) = (term667 A B x x' y g s).
Proof. exact (MK_COMB (@lem3637486) (@lem3637485 A B x x' y g s)). Qed.
Lemma lem3637488 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term534 A B f x y) = (term534 A B f x y).
Proof. exact (eq_refl (term534 A B f x y)). Qed.
Lemma lem3637489 {A B : Type'} (x : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (x' : A) (y : A) : (term673 A B x g s f x' y) = (term669 A B x g s f x' y).
Proof. exact (MK_COMB (@lem3637487 A B x' x y g s) (@lem3637488 A B f x' y)). Qed.
Lemma lem3637490 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3637491 {A B : Type'} (x : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (x' : A) (y : A) : (term679 A B x g s f x' y) = (term680 A B x g s f x' y).
Proof. exact (MK_COMB (@lem3637490) (@lem3637489 A B x g s f x' y)). Qed.
Lemma lem3637492 {A B : Type'} (x : A) (x' : B) (y : A) (g : B -> A) (s : B -> Prop) (x'' : B) : (term675 A B x x' y g s x'') = (term650 A B x x' y g s x'').
Proof. exact (eq_refl (term675 A B x x' y g s x'')). Qed.
Lemma lem3637493 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3637494 {A B : Type'} (x : A) (x' : B) (y : A) (g : B -> A) (s : B -> Prop) (x'' : B) : (term681 A B x x' y g s x'') = (term682 A B x x' y g s x'').
Proof. exact (MK_COMB (@lem3637493) (@lem3637492 A B x x' y g s x'')). Qed.
Lemma lem3637495 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term534 A B f x y) = (term534 A B f x y).
Proof. exact (eq_refl (term534 A B f x y)). Qed.
Lemma lem3637496 {A B : Type'} (x : B) (g : B -> A) (s : B -> Prop) (x' : B) (f : A -> B) (x'' : A) (y : A) : (term683 A B x g s x' f x'' y) = (term684 A B x g s x' f x'' y).
Proof. exact (MK_COMB (@lem3637494 A B x'' x y g s x') (@lem3637495 A B f x'' y)). Qed.
Lemma lem3637497 {A B : Type'} (x : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (x' : A) (y : A) : (term685 A B x g s f x' y) = (term686 A B x g s f x' y).
Proof. exact (fun_ext (fun x'' : B => @lem3637496 A B x g s x'' f x' y)). Qed.
Lemma lem3637498 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637499 {A B : Type'} (x : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (x' : A) (y : A) : (term674 A B x g s f x' y) = (term687 A B x g s f x' y).
Proof. exact (MK_COMB (@lem3637498 B) (@lem3637497 A B x g s f x' y)). Qed.
Lemma lem3637500 {A B : Type'} (x : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (x' : A) (y : A) : ((term673 A B x g s f x' y) = (term674 A B x g s f x' y)) = ((term669 A B x g s f x' y) = (term687 A B x g s f x' y)).
Proof. exact (MK_COMB (@lem3637491 A B x g s f x' y) (@lem3637499 A B x g s f x' y)). Qed.
Lemma lem3637501 {A B : Type'} (x : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (x' : A) (y : A) : (term669 A B x g s f x' y) = (term687 A B x g s f x' y).
Proof. exact (EQ_MP (@lem3637500 A B x g s f x' y) (@lem3637481 A B x g s f x' y)). Qed.
Lemma lem3637502 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) (y : A) : (term671 A B g s f x y) = (term688 A B g s f x y).
Proof. exact (fun_ext (fun x' : B => @lem3637501 A B x' g s f x y)). Qed.
Lemma lem3637503 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637504 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) (y : A) : (term672 A B g s f x y) = (term689 A B g s f x y).
Proof. exact (MK_COMB (@lem3637503 B) (@lem3637502 A B g s f x y)). Qed.
Lemma lem3637505 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) (y : A) : (term657 A B g s f x y) = (term689 A B g s f x y).
Proof. exact (TRANS (@lem3637477 A B g s f x y) (@lem3637504 A B g s f x y)). Qed.
Lemma lem3637506 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) (y : A) : (term537 A B g s f x y) = (term689 A B g s f x y).
Proof. exact (TRANS (@lem3637453 A B g s f x y) (@lem3637505 A B g s f x y)). Qed.
Lemma lem3637507 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) : (term544 A B g s f x) = (term690 A B g s f x).
Proof. exact (fun_ext (fun y : A => @lem3637506 A B g s f x y)). Qed.
Lemma lem3637508 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3637509 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) : (term545 A B g s f x) = (term691 A B g s f x).
Proof. exact (MK_COMB (@lem3637508 A) (@lem3637507 A B g s f x)). Qed.
Lemma lem3637510 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) : (term551 A B g s f) = (term692 A B g s f).
Proof. exact (fun_ext (fun x : A => @lem3637509 A B g s f x)). Qed.
Lemma lem3637511 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3637512 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) : (term552 A B g s f) = (term693 A B g s f).
Proof. exact (MK_COMB (@lem3637511 A) (@lem3637510 A B g s f)). Qed.
Lemma lem3637513 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3637514 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) : (term589 A B g s f) = (term694 A B g s f).
Proof. exact (MK_COMB (@lem3637513) (@lem3637512 A B g s f)). Qed.
Lemma lem3637516 {A : Type'} (P : Prop) (Q : A -> Prop) : (term506 A P Q) = (term507 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3637517 {B : Type'} (P : Prop) (Q : B -> Prop) : (term506 B P Q) = (term507 B P Q).
Proof. exact (@lem3637516 B P Q). Qed.
Lemma lem3637518 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term695 A B x f x' g s) = (term696 A B x f x' g s).
Proof. exact (@lem3637517 B (x = (f x')) (term23 A B x' g s)). Qed.
Lemma lem3637519 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) (x' : B) : (term76 A B x g s x') = (term21 A B x g s x').
Proof. exact (eq_refl (term76 A B x g s x')). Qed.
Lemma lem3637520 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term77 A B x g s) = (term23 A B x g s).
Proof. exact (fun_ext (fun x' : B => @lem3637519 A B x g s x')). Qed.
Lemma lem3637521 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637522 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term78 A B x g s) = (term24 A B x g s).
Proof. exact (MK_COMB (@lem3637521 B) (@lem3637520 A B x g s)). Qed.
Lemma lem3637523 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term383 A B x f x') = (term383 A B x f x').
Proof. exact (eq_refl (term383 A B x f x')). Qed.
Lemma lem3637524 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term695 A B x f x' g s) = (term426 A B x f x' g s).
Proof. exact (MK_COMB (@lem3637523 A B x f x') (@lem3637522 A B x' g s)). Qed.
Lemma lem3637525 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3637526 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term697 A B x f x' g s) = (term698 A B x f x' g s).
Proof. exact (MK_COMB (@lem3637525) (@lem3637524 A B x f x' g s)). Qed.
Lemma lem3637527 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) (x' : B) : (term76 A B x g s x') = (term21 A B x g s x').
Proof. exact (eq_refl (term76 A B x g s x')). Qed.
Lemma lem3637528 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term383 A B x f x') = (term383 A B x f x').
Proof. exact (eq_refl (term383 A B x f x')). Qed.
Lemma lem3637529 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) (x'' : B) : (term699 A B x f x' g s x'') = (term700 A B x f x' g s x'').
Proof. exact (MK_COMB (@lem3637528 A B x f x') (@lem3637527 A B x' g s x'')). Qed.
Lemma lem3637530 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term701 A B x f x' g s) = (term702 A B x f x' g s).
Proof. exact (fun_ext (fun x'' : B => @lem3637529 A B x f x' g s x'')). Qed.
Lemma lem3637531 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637532 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term696 A B x f x' g s) = (term703 A B x f x' g s).
Proof. exact (MK_COMB (@lem3637531 B) (@lem3637530 A B x f x' g s)). Qed.
Lemma lem3637533 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : ((term695 A B x f x' g s) = (term696 A B x f x' g s)) = ((term426 A B x f x' g s) = (term703 A B x f x' g s)).
Proof. exact (MK_COMB (@lem3637526 A B x f x' g s) (@lem3637532 A B x f x' g s)). Qed.
Lemma lem3637534 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term426 A B x f x' g s) = (term703 A B x f x' g s).
Proof. exact (EQ_MP (@lem3637533 A B x f x' g s) (@lem3637518 A B x f x' g s)). Qed.
Lemma lem3637535 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term428 A B x f g s) = (term704 A B x f g s).
Proof. exact (fun_ext (fun x' : A => @lem3637534 A B x f x' g s)). Qed.
Lemma lem3637536 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3637537 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term429 A B x f g s) = (term705 A B x f g s).
Proof. exact (MK_COMB (@lem3637536 A) (@lem3637535 A B x f g s)). Qed.
Lemma lem3637538 {B : Type'} (s : B -> Prop) (x : B) : (term572 B s x) = (term572 B s x).
Proof. exact (eq_refl (term572 B s x)). Qed.
Lemma lem3637539 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term573 A B x f g s) = (term706 A B x f g s).
Proof. exact (MK_COMB (@lem3637538 B s x) (@lem3637537 A B x f g s)). Qed.
Lemma lem3637541 {A : Type'} (P : Prop) (Q : A -> Prop) : (term506 A P Q) = (term507 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3637542 {A : Type'} (P : Prop) (Q : A -> Prop) : (term506 A P Q) = (term507 A P Q).
Proof. exact (@lem3637541 A P Q). Qed.
Lemma lem3637543 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term707 A B x f g s) = (term708 A B x f g s).
Proof. exact (@lem3637542 A (term75 B s x) (term704 A B x f g s)). Qed.
Lemma lem3637544 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term709 A B x f g s x') = (term703 A B x f x' g s).
Proof. exact (eq_refl (term709 A B x f g s x')). Qed.
Lemma lem3637545 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term710 A B x f g s) = (term704 A B x f g s).
Proof. exact (fun_ext (fun x' : A => @lem3637544 A B x f x' g s)). Qed.
Lemma lem3637546 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3637547 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term711 A B x f g s) = (term705 A B x f g s).
Proof. exact (MK_COMB (@lem3637546 A) (@lem3637545 A B x f g s)). Qed.
Lemma lem3637548 {B : Type'} (s : B -> Prop) (x : B) : (term572 B s x) = (term572 B s x).
Proof. exact (eq_refl (term572 B s x)). Qed.
Lemma lem3637549 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term707 A B x f g s) = (term706 A B x f g s).
Proof. exact (MK_COMB (@lem3637548 B s x) (@lem3637547 A B x f g s)). Qed.
Lemma lem3637550 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3637551 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term712 A B x f g s) = (term713 A B x f g s).
Proof. exact (MK_COMB (@lem3637550) (@lem3637549 A B x f g s)). Qed.
Lemma lem3637552 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term709 A B x f g s x') = (term703 A B x f x' g s).
Proof. exact (eq_refl (term709 A B x f g s x')). Qed.
Lemma lem3637553 {B : Type'} (s : B -> Prop) (x : B) : (term572 B s x) = (term572 B s x).
Proof. exact (eq_refl (term572 B s x)). Qed.
Lemma lem3637554 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term714 A B x f g s x') = (term715 A B x f x' g s).
Proof. exact (MK_COMB (@lem3637553 B s x) (@lem3637552 A B x f x' g s)). Qed.
Lemma lem3637555 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term716 A B x f g s) = (term717 A B x f g s).
Proof. exact (fun_ext (fun x' : A => @lem3637554 A B x f x' g s)). Qed.
Lemma lem3637556 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3637557 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term708 A B x f g s) = (term718 A B x f g s).
Proof. exact (MK_COMB (@lem3637556 A) (@lem3637555 A B x f g s)). Qed.
Lemma lem3637558 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : ((term707 A B x f g s) = (term708 A B x f g s)) = ((term706 A B x f g s) = (term718 A B x f g s)).
Proof. exact (MK_COMB (@lem3637551 A B x f g s) (@lem3637557 A B x f g s)). Qed.
Lemma lem3637559 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term706 A B x f g s) = (term718 A B x f g s).
Proof. exact (EQ_MP (@lem3637558 A B x f g s) (@lem3637543 A B x f g s)). Qed.
Lemma lem3637561 {A : Type'} (P : Prop) (Q : A -> Prop) : (term506 A P Q) = (term507 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3637562 {B : Type'} (P : Prop) (Q : B -> Prop) : (term506 B P Q) = (term507 B P Q).
Proof. exact (@lem3637561 B P Q). Qed.
Lemma lem3637563 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term719 A B x f x' g s) = (term720 A B x f x' g s).
Proof. exact (@lem3637562 B (term75 B s x) (term702 A B x f x' g s)). Qed.
Lemma lem3637564 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) (x'' : B) : (term721 A B x f x' g s x'') = (term700 A B x f x' g s x'').
Proof. exact (eq_refl (term721 A B x f x' g s x'')). Qed.
Lemma lem3637565 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term722 A B x f x' g s) = (term702 A B x f x' g s).
Proof. exact (fun_ext (fun x'' : B => @lem3637564 A B x f x' g s x'')). Qed.
Lemma lem3637566 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637567 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term723 A B x f x' g s) = (term703 A B x f x' g s).
Proof. exact (MK_COMB (@lem3637566 B) (@lem3637565 A B x f x' g s)). Qed.
Lemma lem3637568 {B : Type'} (s : B -> Prop) (x : B) : (term572 B s x) = (term572 B s x).
Proof. exact (eq_refl (term572 B s x)). Qed.
Lemma lem3637569 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term719 A B x f x' g s) = (term715 A B x f x' g s).
Proof. exact (MK_COMB (@lem3637568 B s x) (@lem3637567 A B x f x' g s)). Qed.
Lemma lem3637570 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3637571 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term724 A B x f x' g s) = (term725 A B x f x' g s).
Proof. exact (MK_COMB (@lem3637570) (@lem3637569 A B x f x' g s)). Qed.
Lemma lem3637572 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) (x'' : B) : (term721 A B x f x' g s x'') = (term700 A B x f x' g s x'').
Proof. exact (eq_refl (term721 A B x f x' g s x'')). Qed.
Lemma lem3637573 {B : Type'} (s : B -> Prop) (x : B) : (term572 B s x) = (term572 B s x).
Proof. exact (eq_refl (term572 B s x)). Qed.
Lemma lem3637574 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) (x'' : B) : (term726 A B x f x' g s x'') = (term727 A B x f x' g s x'').
Proof. exact (MK_COMB (@lem3637573 B s x) (@lem3637572 A B x f x' g s x'')). Qed.
Lemma lem3637575 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term728 A B x f x' g s) = (term729 A B x f x' g s).
Proof. exact (fun_ext (fun x'' : B => @lem3637574 A B x f x' g s x'')). Qed.
Lemma lem3637576 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637577 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term720 A B x f x' g s) = (term730 A B x f x' g s).
Proof. exact (MK_COMB (@lem3637576 B) (@lem3637575 A B x f x' g s)). Qed.
Lemma lem3637578 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : ((term719 A B x f x' g s) = (term720 A B x f x' g s)) = ((term715 A B x f x' g s) = (term730 A B x f x' g s)).
Proof. exact (MK_COMB (@lem3637571 A B x f x' g s) (@lem3637577 A B x f x' g s)). Qed.
Lemma lem3637579 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term715 A B x f x' g s) = (term730 A B x f x' g s).
Proof. exact (EQ_MP (@lem3637578 A B x f x' g s) (@lem3637563 A B x f x' g s)). Qed.
Lemma lem3637580 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term717 A B x f g s) = (term731 A B x f g s).
Proof. exact (fun_ext (fun x' : A => @lem3637579 A B x f x' g s)). Qed.
Lemma lem3637581 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3637582 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term718 A B x f g s) = (term732 A B x f g s).
Proof. exact (MK_COMB (@lem3637581 A) (@lem3637580 A B x f g s)). Qed.
Lemma lem3637583 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term706 A B x f g s) = (term732 A B x f g s).
Proof. exact (TRANS (@lem3637559 A B x f g s) (@lem3637582 A B x f g s)). Qed.
Lemma lem3637584 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term573 A B x f g s) = (term732 A B x f g s).
Proof. exact (TRANS (@lem3637539 A B x f g s) (@lem3637583 A B x f g s)). Qed.
Lemma lem3637585 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term602 A B f g s) = (term733 A B f g s).
Proof. exact (fun_ext (fun x : B => @lem3637584 A B x f g s)). Qed.
Lemma lem3637586 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637587 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term617 A B f g s) = (term734 A B f g s).
Proof. exact (MK_COMB (@lem3637586 B) (@lem3637585 A B f g s)). Qed.
Lemma lem3637588 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term614 A B f g s) = (term614 A B f g s).
Proof. exact (eq_refl (term614 A B f g s)). Qed.
Lemma lem3637589 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term618 A B f g s) = (term735 A B f g s).
Proof. exact (MK_COMB (@lem3637588 A B f g s) (@lem3637587 A B f g s)). Qed.
Lemma lem3637591 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term598 A P Q) = (term597 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3637592 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term598 B P Q) = (term597 B P Q).
Proof. exact (@lem3637591 B P Q). Qed.
Lemma lem3637593 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term736 A B f g s) = (term737 A B f g s).
Proof. exact (@lem3637592 B (term601 A B f g s) (term733 A B f g s)). Qed.
Lemma lem3637594 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term603 A B f g s x) = (term575 A B x f g s).
Proof. exact (eq_refl (term603 A B f g s x)). Qed.
Lemma lem3637595 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term610 A B f g s) = (term601 A B f g s).
Proof. exact (fun_ext (fun x : B => @lem3637594 A B x f g s)). Qed.
Lemma lem3637596 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637597 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term611 A B f g s) = (term612 A B f g s).
Proof. exact (MK_COMB (@lem3637596 B) (@lem3637595 A B f g s)). Qed.
Lemma lem3637598 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3637599 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term613 A B f g s) = (term614 A B f g s).
Proof. exact (MK_COMB (@lem3637598) (@lem3637597 A B f g s)). Qed.
Lemma lem3637600 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term738 A B f g s x) = (term732 A B x f g s).
Proof. exact (eq_refl (term738 A B f g s x)). Qed.
Lemma lem3637601 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term739 A B f g s) = (term733 A B f g s).
Proof. exact (fun_ext (fun x : B => @lem3637600 A B x f g s)). Qed.
Lemma lem3637602 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637603 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term740 A B f g s) = (term734 A B f g s).
Proof. exact (MK_COMB (@lem3637602 B) (@lem3637601 A B f g s)). Qed.
Lemma lem3637604 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term736 A B f g s) = (term735 A B f g s).
Proof. exact (MK_COMB (@lem3637599 A B f g s) (@lem3637603 A B f g s)). Qed.
Lemma lem3637605 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3637606 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term741 A B f g s) = (term742 A B f g s).
Proof. exact (MK_COMB (@lem3637605) (@lem3637604 A B f g s)). Qed.
Lemma lem3637607 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term603 A B f g s x) = (term575 A B x f g s).
Proof. exact (eq_refl (term603 A B f g s x)). Qed.
Lemma lem3637608 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3637609 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term604 A B f g s x) = (term577 A B x f g s).
Proof. exact (MK_COMB (@lem3637608) (@lem3637607 A B x f g s)). Qed.
Lemma lem3637610 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term738 A B f g s x) = (term732 A B x f g s).
Proof. exact (eq_refl (term738 A B f g s x)). Qed.
Lemma lem3637611 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term743 A B f g s x) = (term744 A B x f g s).
Proof. exact (MK_COMB (@lem3637609 A B x f g s) (@lem3637610 A B x f g s)). Qed.
Lemma lem3637612 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term745 A B f g s) = (term746 A B f g s).
Proof. exact (fun_ext (fun x : B => @lem3637611 A B x f g s)). Qed.
Lemma lem3637613 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637614 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term737 A B f g s) = (term747 A B f g s).
Proof. exact (MK_COMB (@lem3637613 B) (@lem3637612 A B f g s)). Qed.
Lemma lem3637615 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : ((term736 A B f g s) = (term737 A B f g s)) = ((term735 A B f g s) = (term747 A B f g s)).
Proof. exact (MK_COMB (@lem3637606 A B f g s) (@lem3637614 A B f g s)). Qed.
Lemma lem3637616 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term735 A B f g s) = (term747 A B f g s).
Proof. exact (EQ_MP (@lem3637615 A B f g s) (@lem3637593 A B f g s)). Qed.
Lemma lem3637618 {A : Type'} (P : Prop) (Q : A -> Prop) : (term71 A P Q) = (term72 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3637619 {A : Type'} (P : Prop) (Q : A -> Prop) : (term71 A P Q) = (term72 A P Q).
Proof. exact (@lem3637618 A P Q). Qed.
Lemma lem3637620 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term748 A B x f g s) = (term749 A B x f g s).
Proof. exact (@lem3637619 A (term575 A B x f g s) (term731 A B x f g s)). Qed.
Lemma lem3637621 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term750 A B x f g s x') = (term730 A B x f x' g s).
Proof. exact (eq_refl (term750 A B x f g s x')). Qed.
Lemma lem3637622 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term751 A B x f g s) = (term731 A B x f g s).
Proof. exact (fun_ext (fun x' : A => @lem3637621 A B x f x' g s)). Qed.
Lemma lem3637623 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3637624 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term752 A B x f g s) = (term732 A B x f g s).
Proof. exact (MK_COMB (@lem3637623 A) (@lem3637622 A B x f g s)). Qed.
Lemma lem3637625 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term577 A B x f g s) = (term577 A B x f g s).
Proof. exact (eq_refl (term577 A B x f g s)). Qed.
Lemma lem3637626 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term748 A B x f g s) = (term744 A B x f g s).
Proof. exact (MK_COMB (@lem3637625 A B x f g s) (@lem3637624 A B x f g s)). Qed.
Lemma lem3637627 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3637628 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term753 A B x f g s) = (term754 A B x f g s).
Proof. exact (MK_COMB (@lem3637627) (@lem3637626 A B x f g s)). Qed.
Lemma lem3637629 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term750 A B x f g s x') = (term730 A B x f x' g s).
Proof. exact (eq_refl (term750 A B x f g s x')). Qed.
Lemma lem3637630 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term577 A B x f g s) = (term577 A B x f g s).
Proof. exact (eq_refl (term577 A B x f g s)). Qed.
Lemma lem3637631 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term755 A B x f g s x') = (term756 A B x f x' g s).
Proof. exact (MK_COMB (@lem3637630 A B x f g s) (@lem3637629 A B x f x' g s)). Qed.
Lemma lem3637632 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term757 A B x f g s) = (term758 A B x f g s).
Proof. exact (fun_ext (fun x' : A => @lem3637631 A B x f x' g s)). Qed.
Lemma lem3637633 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3637634 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term749 A B x f g s) = (term759 A B x f g s).
Proof. exact (MK_COMB (@lem3637633 A) (@lem3637632 A B x f g s)). Qed.
Lemma lem3637635 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : ((term748 A B x f g s) = (term749 A B x f g s)) = ((term744 A B x f g s) = (term759 A B x f g s)).
Proof. exact (MK_COMB (@lem3637628 A B x f g s) (@lem3637634 A B x f g s)). Qed.
Lemma lem3637636 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term744 A B x f g s) = (term759 A B x f g s).
Proof. exact (EQ_MP (@lem3637635 A B x f g s) (@lem3637620 A B x f g s)). Qed.
Lemma lem3637638 {A : Type'} (P : Prop) (Q : A -> Prop) : (term71 A P Q) = (term72 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3637639 {B : Type'} (P : Prop) (Q : B -> Prop) : (term71 B P Q) = (term72 B P Q).
Proof. exact (@lem3637638 B P Q). Qed.
Lemma lem3637640 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term760 A B x f x' g s) = (term761 A B x f x' g s).
Proof. exact (@lem3637639 B (term575 A B x f g s) (term729 A B x f x' g s)). Qed.
Lemma lem3637641 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) (x'' : B) : (term762 A B x f x' g s x'') = (term727 A B x f x' g s x'').
Proof. exact (eq_refl (term762 A B x f x' g s x'')). Qed.
Lemma lem3637642 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term763 A B x f x' g s) = (term729 A B x f x' g s).
Proof. exact (fun_ext (fun x'' : B => @lem3637641 A B x f x' g s x'')). Qed.
Lemma lem3637643 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637644 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term764 A B x f x' g s) = (term730 A B x f x' g s).
Proof. exact (MK_COMB (@lem3637643 B) (@lem3637642 A B x f x' g s)). Qed.
Lemma lem3637645 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term577 A B x f g s) = (term577 A B x f g s).
Proof. exact (eq_refl (term577 A B x f g s)). Qed.
Lemma lem3637646 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term760 A B x f x' g s) = (term756 A B x f x' g s).
Proof. exact (MK_COMB (@lem3637645 A B x f g s) (@lem3637644 A B x f x' g s)). Qed.
Lemma lem3637647 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3637648 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term765 A B x f x' g s) = (term766 A B x f x' g s).
Proof. exact (MK_COMB (@lem3637647) (@lem3637646 A B x f x' g s)). Qed.
Lemma lem3637649 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) (x'' : B) : (term762 A B x f x' g s x'') = (term727 A B x f x' g s x'').
Proof. exact (eq_refl (term762 A B x f x' g s x'')). Qed.
Lemma lem3637650 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term577 A B x f g s) = (term577 A B x f g s).
Proof. exact (eq_refl (term577 A B x f g s)). Qed.
Lemma lem3637651 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) (x'' : B) : (term767 A B x f x' g s x'') = (term768 A B x f x' g s x'').
Proof. exact (MK_COMB (@lem3637650 A B x f g s) (@lem3637649 A B x f x' g s x'')). Qed.
Lemma lem3637652 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term769 A B x f x' g s) = (term770 A B x f x' g s).
Proof. exact (fun_ext (fun x'' : B => @lem3637651 A B x f x' g s x'')). Qed.
Lemma lem3637653 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637654 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term761 A B x f x' g s) = (term771 A B x f x' g s).
Proof. exact (MK_COMB (@lem3637653 B) (@lem3637652 A B x f x' g s)). Qed.
Lemma lem3637655 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : ((term760 A B x f x' g s) = (term761 A B x f x' g s)) = ((term756 A B x f x' g s) = (term771 A B x f x' g s)).
Proof. exact (MK_COMB (@lem3637648 A B x f x' g s) (@lem3637654 A B x f x' g s)). Qed.
Lemma lem3637656 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term756 A B x f x' g s) = (term771 A B x f x' g s).
Proof. exact (EQ_MP (@lem3637655 A B x f x' g s) (@lem3637640 A B x f x' g s)). Qed.
Lemma lem3637657 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term758 A B x f g s) = (term772 A B x f g s).
Proof. exact (fun_ext (fun x' : A => @lem3637656 A B x f x' g s)). Qed.
Lemma lem3637658 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3637659 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term759 A B x f g s) = (term773 A B x f g s).
Proof. exact (MK_COMB (@lem3637658 A) (@lem3637657 A B x f g s)). Qed.
Lemma lem3637660 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term744 A B x f g s) = (term773 A B x f g s).
Proof. exact (TRANS (@lem3637636 A B x f g s) (@lem3637659 A B x f g s)). Qed.
Lemma lem3637661 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term746 A B f g s) = (term774 A B f g s).
Proof. exact (fun_ext (fun x : B => @lem3637660 A B x f g s)). Qed.
Lemma lem3637662 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637663 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term747 A B f g s) = (term775 A B f g s).
Proof. exact (MK_COMB (@lem3637662 B) (@lem3637661 A B f g s)). Qed.
Lemma lem3637664 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term735 A B f g s) = (term775 A B f g s).
Proof. exact (TRANS (@lem3637616 A B f g s) (@lem3637663 A B f g s)). Qed.
Lemma lem3637665 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term618 A B f g s) = (term775 A B f g s).
Proof. exact (TRANS (@lem3637589 A B f g s) (@lem3637664 A B f g s)). Qed.
Lemma lem3637666 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term619 A B f g s) = (term776 A B f g s).
Proof. exact (MK_COMB (@lem3637514 A B g s f) (@lem3637665 A B f g s)). Qed.
Lemma lem3637670 {A : Type'} (P : A -> Prop) (Q : Prop) : (term777 A P Q) = (term778 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3637671 {A : Type'} (P : A -> Prop) (Q : Prop) : (term777 A P Q) = (term778 A P Q).
Proof. exact (@lem3637670 A P Q). Qed.
Lemma lem3637672 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term779 A B f g s) = (term780 A B f g s).
Proof. exact (@lem3637671 A (term692 A B g s f) (term775 A B f g s)). Qed.
Lemma lem3637673 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) : (term781 A B g s f x) = (term691 A B g s f x).
Proof. exact (eq_refl (term781 A B g s f x)). Qed.
Lemma lem3637674 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) : (term782 A B g s f) = (term692 A B g s f).
Proof. exact (fun_ext (fun x : A => @lem3637673 A B g s f x)). Qed.
Lemma lem3637675 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3637676 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) : (term783 A B g s f) = (term693 A B g s f).
Proof. exact (MK_COMB (@lem3637675 A) (@lem3637674 A B g s f)). Qed.
Lemma lem3637677 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3637678 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) : (term784 A B g s f) = (term694 A B g s f).
Proof. exact (MK_COMB (@lem3637677) (@lem3637676 A B g s f)). Qed.
Lemma lem3637679 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term775 A B f g s) = (term775 A B f g s).
Proof. exact (eq_refl (term775 A B f g s)). Qed.
Lemma lem3637680 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term779 A B f g s) = (term776 A B f g s).
Proof. exact (MK_COMB (@lem3637678 A B g s f) (@lem3637679 A B f g s)). Qed.
Lemma lem3637681 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3637682 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term785 A B f g s) = (term786 A B f g s).
Proof. exact (MK_COMB (@lem3637681) (@lem3637680 A B f g s)). Qed.
Lemma lem3637683 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) : (term781 A B g s f x) = (term691 A B g s f x).
Proof. exact (eq_refl (term781 A B g s f x)). Qed.
Lemma lem3637684 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3637685 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) : (term787 A B g s f x) = (term788 A B g s f x).
Proof. exact (MK_COMB (@lem3637684) (@lem3637683 A B g s f x)). Qed.
Lemma lem3637686 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term775 A B f g s) = (term775 A B f g s).
Proof. exact (eq_refl (term775 A B f g s)). Qed.
Lemma lem3637687 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term789 A B x f g s) = (term790 A B x f g s).
Proof. exact (MK_COMB (@lem3637685 A B g s f x) (@lem3637686 A B f g s)). Qed.
Lemma lem3637688 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term791 A B f g s) = (term792 A B f g s).
Proof. exact (fun_ext (fun x : A => @lem3637687 A B x f g s)). Qed.
Lemma lem3637689 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3637690 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term780 A B f g s) = (term793 A B f g s).
Proof. exact (MK_COMB (@lem3637689 A) (@lem3637688 A B f g s)). Qed.
Lemma lem3637691 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : ((term779 A B f g s) = (term780 A B f g s)) = ((term776 A B f g s) = (term793 A B f g s)).
Proof. exact (MK_COMB (@lem3637682 A B f g s) (@lem3637690 A B f g s)). Qed.
Lemma lem3637692 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term776 A B f g s) = (term793 A B f g s).
Proof. exact (EQ_MP (@lem3637691 A B f g s) (@lem3637672 A B f g s)). Qed.
Lemma lem3637696 {A : Type'} (P : A -> Prop) (Q : Prop) : (term777 A P Q) = (term778 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3637697 {A : Type'} (P : A -> Prop) (Q : Prop) : (term777 A P Q) = (term778 A P Q).
Proof. exact (@lem3637696 A P Q). Qed.
Lemma lem3637698 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term794 A B x f g s) = (term795 A B x f g s).
Proof. exact (@lem3637697 A (term690 A B g s f x) (term775 A B f g s)). Qed.
Lemma lem3637699 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) (y : A) : (term796 A B g s f x y) = (term689 A B g s f x y).
Proof. exact (eq_refl (term796 A B g s f x y)). Qed.
Lemma lem3637700 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) : (term797 A B g s f x) = (term690 A B g s f x).
Proof. exact (fun_ext (fun y : A => @lem3637699 A B g s f x y)). Qed.
Lemma lem3637701 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3637702 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) : (term798 A B g s f x) = (term691 A B g s f x).
Proof. exact (MK_COMB (@lem3637701 A) (@lem3637700 A B g s f x)). Qed.
Lemma lem3637703 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3637704 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) : (term799 A B g s f x) = (term788 A B g s f x).
Proof. exact (MK_COMB (@lem3637703) (@lem3637702 A B g s f x)). Qed.
Lemma lem3637705 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term775 A B f g s) = (term775 A B f g s).
Proof. exact (eq_refl (term775 A B f g s)). Qed.
Lemma lem3637706 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term794 A B x f g s) = (term790 A B x f g s).
Proof. exact (MK_COMB (@lem3637704 A B g s f x) (@lem3637705 A B f g s)). Qed.
Lemma lem3637707 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3637708 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term800 A B x f g s) = (term801 A B x f g s).
Proof. exact (MK_COMB (@lem3637707) (@lem3637706 A B x f g s)). Qed.
Lemma lem3637709 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) (y : A) : (term796 A B g s f x y) = (term689 A B g s f x y).
Proof. exact (eq_refl (term796 A B g s f x y)). Qed.
Lemma lem3637710 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3637711 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) (y : A) : (term802 A B g s f x y) = (term803 A B g s f x y).
Proof. exact (MK_COMB (@lem3637710) (@lem3637709 A B g s f x y)). Qed.
Lemma lem3637712 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term775 A B f g s) = (term775 A B f g s).
Proof. exact (eq_refl (term775 A B f g s)). Qed.
Lemma lem3637713 {A B : Type'} (x : A) (y : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term804 A B x y f g s) = (term805 A B x y f g s).
Proof. exact (MK_COMB (@lem3637711 A B g s f x y) (@lem3637712 A B f g s)). Qed.
Lemma lem3637714 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term806 A B x f g s) = (term807 A B x f g s).
Proof. exact (fun_ext (fun y : A => @lem3637713 A B x y f g s)). Qed.
Lemma lem3637715 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3637716 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term795 A B x f g s) = (term808 A B x f g s).
Proof. exact (MK_COMB (@lem3637715 A) (@lem3637714 A B x f g s)). Qed.
Lemma lem3637717 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : ((term794 A B x f g s) = (term795 A B x f g s)) = ((term790 A B x f g s) = (term808 A B x f g s)).
Proof. exact (MK_COMB (@lem3637708 A B x f g s) (@lem3637716 A B x f g s)). Qed.
Lemma lem3637718 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term790 A B x f g s) = (term808 A B x f g s).
Proof. exact (EQ_MP (@lem3637717 A B x f g s) (@lem3637698 A B x f g s)). Qed.
Lemma lem3637720 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term598 A P Q) = (term597 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3637721 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term598 B P Q) = (term597 B P Q).
Proof. exact (@lem3637720 B P Q). Qed.
Lemma lem3637722 {A B : Type'} (x : A) (y : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term809 A B x y f g s) = (term810 A B x y f g s).
Proof. exact (@lem3637721 B (term688 A B g s f x y) (term774 A B f g s)). Qed.
Lemma lem3637723 {A B : Type'} (x : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (x' : A) (y : A) : (term811 A B g s f x' y x) = (term687 A B x g s f x' y).
Proof. exact (eq_refl (term811 A B g s f x' y x)). Qed.
Lemma lem3637724 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) (y : A) : (term812 A B g s f x y) = (term688 A B g s f x y).
Proof. exact (fun_ext (fun x' : B => @lem3637723 A B x' g s f x y)). Qed.
Lemma lem3637725 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637726 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) (y : A) : (term813 A B g s f x y) = (term689 A B g s f x y).
Proof. exact (MK_COMB (@lem3637725 B) (@lem3637724 A B g s f x y)). Qed.
Lemma lem3637727 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3637728 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (x : A) (y : A) : (term814 A B g s f x y) = (term803 A B g s f x y).
Proof. exact (MK_COMB (@lem3637727) (@lem3637726 A B g s f x y)). Qed.
Lemma lem3637729 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term815 A B f g s x) = (term773 A B x f g s).
Proof. exact (eq_refl (term815 A B f g s x)). Qed.
Lemma lem3637730 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term816 A B f g s) = (term774 A B f g s).
Proof. exact (fun_ext (fun x : B => @lem3637729 A B x f g s)). Qed.
Lemma lem3637731 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637732 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term817 A B f g s) = (term775 A B f g s).
Proof. exact (MK_COMB (@lem3637731 B) (@lem3637730 A B f g s)). Qed.
Lemma lem3637733 {A B : Type'} (x : A) (y : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term809 A B x y f g s) = (term805 A B x y f g s).
Proof. exact (MK_COMB (@lem3637728 A B g s f x y) (@lem3637732 A B f g s)). Qed.
Lemma lem3637734 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3637735 {A B : Type'} (x : A) (y : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term818 A B x y f g s) = (term819 A B x y f g s).
Proof. exact (MK_COMB (@lem3637734) (@lem3637733 A B x y f g s)). Qed.
Lemma lem3637736 {A B : Type'} (x : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (x' : A) (y : A) : (term811 A B g s f x' y x) = (term687 A B x g s f x' y).
Proof. exact (eq_refl (term811 A B g s f x' y x)). Qed.
Lemma lem3637737 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3637738 {A B : Type'} (x : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (x' : A) (y : A) : (term820 A B g s f x' y x) = (term821 A B x g s f x' y).
Proof. exact (MK_COMB (@lem3637737) (@lem3637736 A B x g s f x' y)). Qed.
Lemma lem3637739 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term815 A B f g s x) = (term773 A B x f g s).
Proof. exact (eq_refl (term815 A B f g s x)). Qed.
Lemma lem3637740 {A B : Type'} (x : A) (y : A) (x' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term822 A B x y f g s x') = (term823 A B x y x' f g s).
Proof. exact (MK_COMB (@lem3637738 A B x' g s f x y) (@lem3637739 A B x' f g s)). Qed.
Lemma lem3637741 {A B : Type'} (x : A) (y : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term824 A B x y f g s) = (term825 A B x y f g s).
Proof. exact (fun_ext (fun x' : B => @lem3637740 A B x y x' f g s)). Qed.
Lemma lem3637742 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637743 {A B : Type'} (x : A) (y : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term810 A B x y f g s) = (term826 A B x y f g s).
Proof. exact (MK_COMB (@lem3637742 B) (@lem3637741 A B x y f g s)). Qed.
Lemma lem3637744 {A B : Type'} (x : A) (y : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : ((term809 A B x y f g s) = (term810 A B x y f g s)) = ((term805 A B x y f g s) = (term826 A B x y f g s)).
Proof. exact (MK_COMB (@lem3637735 A B x y f g s) (@lem3637743 A B x y f g s)). Qed.
Lemma lem3637745 {A B : Type'} (x : A) (y : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term805 A B x y f g s) = (term826 A B x y f g s).
Proof. exact (EQ_MP (@lem3637744 A B x y f g s) (@lem3637722 A B x y f g s)). Qed.
Lemma lem3637749 {A : Type'} (P : A -> Prop) (Q : Prop) : (term777 A P Q) = (term778 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3637750 {B : Type'} (P : B -> Prop) (Q : Prop) : (term777 B P Q) = (term778 B P Q).
Proof. exact (@lem3637749 B P Q). Qed.
Lemma lem3637751 {A B : Type'} (x : A) (y : A) (x' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term827 A B x y x' f g s) = (term828 A B x y x' f g s).
Proof. exact (@lem3637750 B (term686 A B x' g s f x y) (term773 A B x' f g s)). Qed.
Lemma lem3637752 {A B : Type'} (x : B) (g : B -> A) (s : B -> Prop) (x' : B) (f : A -> B) (x'' : A) (y : A) : (term829 A B x g s f x'' y x') = (term684 A B x g s x' f x'' y).
Proof. exact (eq_refl (term829 A B x g s f x'' y x')). Qed.
Lemma lem3637753 {A B : Type'} (x : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (x' : A) (y : A) : (term830 A B x g s f x' y) = (term686 A B x g s f x' y).
Proof. exact (fun_ext (fun x'' : B => @lem3637752 A B x g s x'' f x' y)). Qed.
Lemma lem3637754 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637755 {A B : Type'} (x : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (x' : A) (y : A) : (term831 A B x g s f x' y) = (term687 A B x g s f x' y).
Proof. exact (MK_COMB (@lem3637754 B) (@lem3637753 A B x g s f x' y)). Qed.
Lemma lem3637756 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3637757 {A B : Type'} (x : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (x' : A) (y : A) : (term832 A B x g s f x' y) = (term821 A B x g s f x' y).
Proof. exact (MK_COMB (@lem3637756) (@lem3637755 A B x g s f x' y)). Qed.
Lemma lem3637758 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term773 A B x f g s) = (term773 A B x f g s).
Proof. exact (eq_refl (term773 A B x f g s)). Qed.
Lemma lem3637759 {A B : Type'} (x : A) (y : A) (x' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term827 A B x y x' f g s) = (term823 A B x y x' f g s).
Proof. exact (MK_COMB (@lem3637757 A B x' g s f x y) (@lem3637758 A B x' f g s)). Qed.
Lemma lem3637760 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3637761 {A B : Type'} (x : A) (y : A) (x' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term833 A B x y x' f g s) = (term834 A B x y x' f g s).
Proof. exact (MK_COMB (@lem3637760) (@lem3637759 A B x y x' f g s)). Qed.
Lemma lem3637762 {A B : Type'} (x : B) (g : B -> A) (s : B -> Prop) (x' : B) (f : A -> B) (x'' : A) (y : A) : (term829 A B x g s f x'' y x') = (term684 A B x g s x' f x'' y).
Proof. exact (eq_refl (term829 A B x g s f x'' y x')). Qed.
Lemma lem3637763 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3637764 {A B : Type'} (x : B) (g : B -> A) (s : B -> Prop) (x' : B) (f : A -> B) (x'' : A) (y : A) : (term835 A B x g s f x'' y x') = (term836 A B x g s x' f x'' y).
Proof. exact (MK_COMB (@lem3637763) (@lem3637762 A B x g s x' f x'' y)). Qed.
Lemma lem3637765 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term773 A B x f g s) = (term773 A B x f g s).
Proof. exact (eq_refl (term773 A B x f g s)). Qed.
Lemma lem3637766 {A B : Type'} (x' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term837 A B x y x' x'' f g s) = (term838 A B x' x y x'' f g s).
Proof. exact (MK_COMB (@lem3637764 A B x'' g s x' f x y) (@lem3637765 A B x'' f g s)). Qed.
Lemma lem3637767 {A B : Type'} (x : A) (y : A) (x' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term839 A B x y x' f g s) = (term840 A B x y x' f g s).
Proof. exact (fun_ext (fun x'' : B => @lem3637766 A B x'' x y x' f g s)). Qed.
Lemma lem3637768 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637769 {A B : Type'} (x : A) (y : A) (x' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term828 A B x y x' f g s) = (term841 A B x y x' f g s).
Proof. exact (MK_COMB (@lem3637768 B) (@lem3637767 A B x y x' f g s)). Qed.
Lemma lem3637770 {A B : Type'} (x : A) (y : A) (x' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : ((term827 A B x y x' f g s) = (term828 A B x y x' f g s)) = ((term823 A B x y x' f g s) = (term841 A B x y x' f g s)).
Proof. exact (MK_COMB (@lem3637761 A B x y x' f g s) (@lem3637769 A B x y x' f g s)). Qed.
Lemma lem3637771 {A B : Type'} (x : A) (y : A) (x' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term823 A B x y x' f g s) = (term841 A B x y x' f g s).
Proof. exact (EQ_MP (@lem3637770 A B x y x' f g s) (@lem3637751 A B x y x' f g s)). Qed.
Lemma lem3637773 {A : Type'} (P : Prop) (Q : A -> Prop) : (term71 A P Q) = (term72 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3637774 {A : Type'} (P : Prop) (Q : A -> Prop) : (term71 A P Q) = (term72 A P Q).
Proof. exact (@lem3637773 A P Q). Qed.
Lemma lem3637775 {A B : Type'} (x' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term842 A B x' x y x'' f g s) = (term843 A B x' x y x'' f g s).
Proof. exact (@lem3637774 A (term684 A B x'' g s x' f x y) (term772 A B x'' f g s)). Qed.
Lemma lem3637776 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term844 A B x f g s x') = (term771 A B x f x' g s).
Proof. exact (eq_refl (term844 A B x f g s x')). Qed.
Lemma lem3637777 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term845 A B x f g s) = (term772 A B x f g s).
Proof. exact (fun_ext (fun x' : A => @lem3637776 A B x f x' g s)). Qed.
Lemma lem3637778 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3637779 {A B : Type'} (x : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term846 A B x f g s) = (term773 A B x f g s).
Proof. exact (MK_COMB (@lem3637778 A) (@lem3637777 A B x f g s)). Qed.
Lemma lem3637780 {A B : Type'} (x : B) (g : B -> A) (s : B -> Prop) (x' : B) (f : A -> B) (x'' : A) (y : A) : (term836 A B x g s x' f x'' y) = (term836 A B x g s x' f x'' y).
Proof. exact (eq_refl (term836 A B x g s x' f x'' y)). Qed.
Lemma lem3637781 {A B : Type'} (x' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term842 A B x' x y x'' f g s) = (term838 A B x' x y x'' f g s).
Proof. exact (MK_COMB (@lem3637780 A B x'' g s x' f x y) (@lem3637779 A B x'' f g s)). Qed.
Lemma lem3637782 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3637783 {A B : Type'} (x' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term847 A B x' x y x'' f g s) = (term848 A B x' x y x'' f g s).
Proof. exact (MK_COMB (@lem3637782) (@lem3637781 A B x' x y x'' f g s)). Qed.
Lemma lem3637784 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term844 A B x f g s x') = (term771 A B x f x' g s).
Proof. exact (eq_refl (term844 A B x f g s x')). Qed.
Lemma lem3637785 {A B : Type'} (x : B) (g : B -> A) (s : B -> Prop) (x' : B) (f : A -> B) (x'' : A) (y : A) : (term836 A B x g s x' f x'' y) = (term836 A B x g s x' f x'' y).
Proof. exact (eq_refl (term836 A B x g s x' f x'' y)). Qed.
Lemma lem3637786 {A B : Type'} (x' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (x''' : A) (g : B -> A) (s : B -> Prop) : (term849 A B x' x y x'' f g s x''') = (term850 A B x' x y x'' f x''' g s).
Proof. exact (MK_COMB (@lem3637785 A B x'' g s x' f x y) (@lem3637784 A B x'' f x''' g s)). Qed.
Lemma lem3637787 {A B : Type'} (x' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term851 A B x' x y x'' f g s) = (term852 A B x' x y x'' f g s).
Proof. exact (fun_ext (fun x''' : A => @lem3637786 A B x' x y x'' f x''' g s)). Qed.
Lemma lem3637788 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3637789 {A B : Type'} (x' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term843 A B x' x y x'' f g s) = (term853 A B x' x y x'' f g s).
Proof. exact (MK_COMB (@lem3637788 A) (@lem3637787 A B x' x y x'' f g s)). Qed.
Lemma lem3637790 {A B : Type'} (x' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : ((term842 A B x' x y x'' f g s) = (term843 A B x' x y x'' f g s)) = ((term838 A B x' x y x'' f g s) = (term853 A B x' x y x'' f g s)).
Proof. exact (MK_COMB (@lem3637783 A B x' x y x'' f g s) (@lem3637789 A B x' x y x'' f g s)). Qed.
Lemma lem3637791 {A B : Type'} (x' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term838 A B x' x y x'' f g s) = (term853 A B x' x y x'' f g s).
Proof. exact (EQ_MP (@lem3637790 A B x' x y x'' f g s) (@lem3637775 A B x' x y x'' f g s)). Qed.
Lemma lem3637793 {A : Type'} (P : Prop) (Q : A -> Prop) : (term71 A P Q) = (term72 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3637794 {B : Type'} (P : Prop) (Q : B -> Prop) : (term71 B P Q) = (term72 B P Q).
Proof. exact (@lem3637793 B P Q). Qed.
Lemma lem3637795 {A B : Type'} (x' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (x''' : A) (g : B -> A) (s : B -> Prop) : (term854 A B x' x y x'' f x''' g s) = (term855 A B x' x y x'' f x''' g s).
Proof. exact (@lem3637794 B (term684 A B x'' g s x' f x y) (term770 A B x'' f x''' g s)). Qed.
Lemma lem3637796 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) (x'' : B) : (term856 A B x f x' g s x'') = (term768 A B x f x' g s x'').
Proof. exact (eq_refl (term856 A B x f x' g s x'')). Qed.
Lemma lem3637797 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term857 A B x f x' g s) = (term770 A B x f x' g s).
Proof. exact (fun_ext (fun x'' : B => @lem3637796 A B x f x' g s x'')). Qed.
Lemma lem3637798 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637799 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) : (term858 A B x f x' g s) = (term771 A B x f x' g s).
Proof. exact (MK_COMB (@lem3637798 B) (@lem3637797 A B x f x' g s)). Qed.
Lemma lem3637800 {A B : Type'} (x : B) (g : B -> A) (s : B -> Prop) (x' : B) (f : A -> B) (x'' : A) (y : A) : (term836 A B x g s x' f x'' y) = (term836 A B x g s x' f x'' y).
Proof. exact (eq_refl (term836 A B x g s x' f x'' y)). Qed.
Lemma lem3637801 {A B : Type'} (x' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (x''' : A) (g : B -> A) (s : B -> Prop) : (term854 A B x' x y x'' f x''' g s) = (term850 A B x' x y x'' f x''' g s).
Proof. exact (MK_COMB (@lem3637800 A B x'' g s x' f x y) (@lem3637799 A B x'' f x''' g s)). Qed.
Lemma lem3637802 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3637803 {A B : Type'} (x' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (x''' : A) (g : B -> A) (s : B -> Prop) : (term859 A B x' x y x'' f x''' g s) = (term860 A B x' x y x'' f x''' g s).
Proof. exact (MK_COMB (@lem3637802) (@lem3637801 A B x' x y x'' f x''' g s)). Qed.
Lemma lem3637804 {A B : Type'} (x : B) (f : A -> B) (x' : A) (g : B -> A) (s : B -> Prop) (x'' : B) : (term856 A B x f x' g s x'') = (term768 A B x f x' g s x'').
Proof. exact (eq_refl (term856 A B x f x' g s x'')). Qed.
Lemma lem3637805 {A B : Type'} (x : B) (g : B -> A) (s : B -> Prop) (x' : B) (f : A -> B) (x'' : A) (y : A) : (term836 A B x g s x' f x'' y) = (term836 A B x g s x' f x'' y).
Proof. exact (eq_refl (term836 A B x g s x' f x'' y)). Qed.
Lemma lem3637806 {A B : Type'} (x' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (x''' : A) (g : B -> A) (s : B -> Prop) (x'''' : B) : (term861 A B x' x y x'' f x''' g s x'''') = (term862 A B x' x y x'' f x''' g s x'''').
Proof. exact (MK_COMB (@lem3637805 A B x'' g s x' f x y) (@lem3637804 A B x'' f x''' g s x'''')). Qed.
Lemma lem3637807 {A B : Type'} (x' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (x''' : A) (g : B -> A) (s : B -> Prop) : (term863 A B x' x y x'' f x''' g s) = (term864 A B x' x y x'' f x''' g s).
Proof. exact (fun_ext (fun x'''' : B => @lem3637806 A B x' x y x'' f x''' g s x'''')). Qed.
Lemma lem3637808 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637809 {A B : Type'} (x' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (x''' : A) (g : B -> A) (s : B -> Prop) : (term855 A B x' x y x'' f x''' g s) = (term865 A B x' x y x'' f x''' g s).
Proof. exact (MK_COMB (@lem3637808 B) (@lem3637807 A B x' x y x'' f x''' g s)). Qed.
Lemma lem3637810 {A B : Type'} (x' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (x''' : A) (g : B -> A) (s : B -> Prop) : ((term854 A B x' x y x'' f x''' g s) = (term855 A B x' x y x'' f x''' g s)) = ((term850 A B x' x y x'' f x''' g s) = (term865 A B x' x y x'' f x''' g s)).
Proof. exact (MK_COMB (@lem3637803 A B x' x y x'' f x''' g s) (@lem3637809 A B x' x y x'' f x''' g s)). Qed.
Lemma lem3637811 {A B : Type'} (x' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (x''' : A) (g : B -> A) (s : B -> Prop) : (term850 A B x' x y x'' f x''' g s) = (term865 A B x' x y x'' f x''' g s).
Proof. exact (EQ_MP (@lem3637810 A B x' x y x'' f x''' g s) (@lem3637795 A B x' x y x'' f x''' g s)). Qed.
Lemma lem3637812 {A B : Type'} (x' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term852 A B x' x y x'' f g s) = (term866 A B x' x y x'' f g s).
Proof. exact (fun_ext (fun x''' : A => @lem3637811 A B x' x y x'' f x''' g s)). Qed.
Lemma lem3637813 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3637814 {A B : Type'} (x' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term853 A B x' x y x'' f g s) = (term867 A B x' x y x'' f g s).
Proof. exact (MK_COMB (@lem3637813 A) (@lem3637812 A B x' x y x'' f g s)). Qed.
Lemma lem3637815 {A B : Type'} (x' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term838 A B x' x y x'' f g s) = (term867 A B x' x y x'' f g s).
Proof. exact (TRANS (@lem3637791 A B x' x y x'' f g s) (@lem3637814 A B x' x y x'' f g s)). Qed.
Lemma lem3637816 {A B : Type'} (x : A) (y : A) (x' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term840 A B x y x' f g s) = (term868 A B x y x' f g s).
Proof. exact (fun_ext (fun x'' : B => @lem3637815 A B x'' x y x' f g s)). Qed.
Lemma lem3637817 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637818 {A B : Type'} (x : A) (y : A) (x' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term841 A B x y x' f g s) = (term869 A B x y x' f g s).
Proof. exact (MK_COMB (@lem3637817 B) (@lem3637816 A B x y x' f g s)). Qed.
Lemma lem3637819 {A B : Type'} (x : A) (y : A) (x' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term823 A B x y x' f g s) = (term869 A B x y x' f g s).
Proof. exact (TRANS (@lem3637771 A B x y x' f g s) (@lem3637818 A B x y x' f g s)). Qed.
Lemma lem3637820 {A B : Type'} (x : A) (y : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term825 A B x y f g s) = (term870 A B x y f g s).
Proof. exact (fun_ext (fun x' : B => @lem3637819 A B x y x' f g s)). Qed.
Lemma lem3637821 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637822 {A B : Type'} (x : A) (y : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term826 A B x y f g s) = (term871 A B x y f g s).
Proof. exact (MK_COMB (@lem3637821 B) (@lem3637820 A B x y f g s)). Qed.
Lemma lem3637823 {A B : Type'} (x : A) (y : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term805 A B x y f g s) = (term871 A B x y f g s).
Proof. exact (TRANS (@lem3637745 A B x y f g s) (@lem3637822 A B x y f g s)). Qed.
Lemma lem3637824 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term807 A B x f g s) = (term872 A B x f g s).
Proof. exact (fun_ext (fun y : A => @lem3637823 A B x y f g s)). Qed.
Lemma lem3637825 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3637826 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term808 A B x f g s) = (term873 A B x f g s).
Proof. exact (MK_COMB (@lem3637825 A) (@lem3637824 A B x f g s)). Qed.
Lemma lem3637827 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term790 A B x f g s) = (term873 A B x f g s).
Proof. exact (TRANS (@lem3637718 A B x f g s) (@lem3637826 A B x f g s)). Qed.
Lemma lem3637828 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term792 A B f g s) = (term874 A B f g s).
Proof. exact (fun_ext (fun x : A => @lem3637827 A B x f g s)). Qed.
Lemma lem3637829 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3637830 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term793 A B f g s) = (term875 A B f g s).
Proof. exact (MK_COMB (@lem3637829 A) (@lem3637828 A B f g s)). Qed.
Lemma lem3637831 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term776 A B f g s) = (term875 A B f g s).
Proof. exact (TRANS (@lem3637692 A B f g s) (@lem3637830 A B f g s)). Qed.
Lemma lem3637832 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term619 A B f g s) = (term875 A B f g s).
Proof. exact (TRANS (@lem3637666 A B f g s) (@lem3637831 A B f g s)). Qed.
Lemma lem3637833 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term620 A B t f g s) = (term876 A B t f g s).
Proof. exact (MK_COMB (@lem3637401 A B g s t) (@lem3637832 A B f g s)). Qed.
Lemma lem3637835 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term598 A P Q) = (term597 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3637836 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term598 A P Q) = (term597 A P Q).
Proof. exact (@lem3637835 A P Q). Qed.
Lemma lem3637837 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term877 A B t f g s) = (term878 A B t f g s).
Proof. exact (@lem3637836 A (term633 A B g s t) (term874 A B f g s)). Qed.
Lemma lem3637838 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) (x : A) : (term879 A B g s t x) = (term632 A B g s t x).
Proof. exact (eq_refl (term879 A B g s t x)). Qed.
Lemma lem3637839 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) : (term880 A B g s t) = (term633 A B g s t).
Proof. exact (fun_ext (fun x : A => @lem3637838 A B g s t x)). Qed.
Lemma lem3637840 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3637841 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) : (term881 A B g s t) = (term634 A B g s t).
Proof. exact (MK_COMB (@lem3637840 A) (@lem3637839 A B g s t)). Qed.
Lemma lem3637842 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3637843 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) : (term882 A B g s t) = (term635 A B g s t).
Proof. exact (MK_COMB (@lem3637842) (@lem3637841 A B g s t)). Qed.
Lemma lem3637844 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term883 A B f g s x) = (term873 A B x f g s).
Proof. exact (eq_refl (term883 A B f g s x)). Qed.
Lemma lem3637845 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term884 A B f g s) = (term874 A B f g s).
Proof. exact (fun_ext (fun x : A => @lem3637844 A B x f g s)). Qed.
Lemma lem3637846 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3637847 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term885 A B f g s) = (term875 A B f g s).
Proof. exact (MK_COMB (@lem3637846 A) (@lem3637845 A B f g s)). Qed.
Lemma lem3637848 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term877 A B t f g s) = (term876 A B t f g s).
Proof. exact (MK_COMB (@lem3637843 A B g s t) (@lem3637847 A B f g s)). Qed.
Lemma lem3637849 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3637850 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term886 A B t f g s) = (term887 A B t f g s).
Proof. exact (MK_COMB (@lem3637849) (@lem3637848 A B t f g s)). Qed.
Lemma lem3637851 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) (x : A) : (term879 A B g s t x) = (term632 A B g s t x).
Proof. exact (eq_refl (term879 A B g s t x)). Qed.
Lemma lem3637852 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3637853 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) (x : A) : (term888 A B g s t x) = (term889 A B g s t x).
Proof. exact (MK_COMB (@lem3637852) (@lem3637851 A B g s t x)). Qed.
Lemma lem3637854 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term883 A B f g s x) = (term873 A B x f g s).
Proof. exact (eq_refl (term883 A B f g s x)). Qed.
Lemma lem3637855 {A B : Type'} (t : A -> Prop) (x : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term890 A B t f g s x) = (term891 A B t x f g s).
Proof. exact (MK_COMB (@lem3637853 A B g s t x) (@lem3637854 A B x f g s)). Qed.
Lemma lem3637856 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term892 A B t f g s) = (term893 A B t f g s).
Proof. exact (fun_ext (fun x : A => @lem3637855 A B t x f g s)). Qed.
Lemma lem3637857 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3637858 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term878 A B t f g s) = (term894 A B t f g s).
Proof. exact (MK_COMB (@lem3637857 A) (@lem3637856 A B t f g s)). Qed.
Lemma lem3637859 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : ((term877 A B t f g s) = (term878 A B t f g s)) = ((term876 A B t f g s) = (term894 A B t f g s)).
Proof. exact (MK_COMB (@lem3637850 A B t f g s) (@lem3637858 A B t f g s)). Qed.
Lemma lem3637860 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term876 A B t f g s) = (term894 A B t f g s).
Proof. exact (EQ_MP (@lem3637859 A B t f g s) (@lem3637837 A B t f g s)). Qed.
Lemma lem3637864 {A : Type'} (P : A -> Prop) (Q : Prop) : (term777 A P Q) = (term778 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3637865 {B : Type'} (P : B -> Prop) (Q : Prop) : (term777 B P Q) = (term778 B P Q).
Proof. exact (@lem3637864 B P Q). Qed.
Lemma lem3637866 {A B : Type'} (t : A -> Prop) (x : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term895 A B t x f g s) = (term896 A B t x f g s).
Proof. exact (@lem3637865 B (term631 A B g s t x) (term873 A B x f g s)). Qed.
Lemma lem3637867 {A B : Type'} (g : B -> A) (s : B -> Prop) (x : B) (t : A -> Prop) (x' : A) : (term897 A B g s t x' x) = (term629 A B g s x t x').
Proof. exact (eq_refl (term897 A B g s t x' x)). Qed.
Lemma lem3637868 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) (x : A) : (term898 A B g s t x) = (term631 A B g s t x).
Proof. exact (fun_ext (fun x' : B => @lem3637867 A B g s x' t x)). Qed.
Lemma lem3637869 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637870 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) (x : A) : (term899 A B g s t x) = (term632 A B g s t x).
Proof. exact (MK_COMB (@lem3637869 B) (@lem3637868 A B g s t x)). Qed.
Lemma lem3637871 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3637872 {A B : Type'} (g : B -> A) (s : B -> Prop) (t : A -> Prop) (x : A) : (term900 A B g s t x) = (term889 A B g s t x).
Proof. exact (MK_COMB (@lem3637871) (@lem3637870 A B g s t x)). Qed.
Lemma lem3637873 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term873 A B x f g s) = (term873 A B x f g s).
Proof. exact (eq_refl (term873 A B x f g s)). Qed.
Lemma lem3637874 {A B : Type'} (t : A -> Prop) (x : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term895 A B t x f g s) = (term891 A B t x f g s).
Proof. exact (MK_COMB (@lem3637872 A B g s t x) (@lem3637873 A B x f g s)). Qed.
Lemma lem3637875 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3637876 {A B : Type'} (t : A -> Prop) (x : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term901 A B t x f g s) = (term902 A B t x f g s).
Proof. exact (MK_COMB (@lem3637875) (@lem3637874 A B t x f g s)). Qed.
Lemma lem3637877 {A B : Type'} (g : B -> A) (s : B -> Prop) (x : B) (t : A -> Prop) (x' : A) : (term897 A B g s t x' x) = (term629 A B g s x t x').
Proof. exact (eq_refl (term897 A B g s t x' x)). Qed.
Lemma lem3637878 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3637879 {A B : Type'} (g : B -> A) (s : B -> Prop) (x : B) (t : A -> Prop) (x' : A) : (term903 A B g s t x' x) = (term904 A B g s x t x').
Proof. exact (MK_COMB (@lem3637878) (@lem3637877 A B g s x t x')). Qed.
Lemma lem3637880 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term873 A B x f g s) = (term873 A B x f g s).
Proof. exact (eq_refl (term873 A B x f g s)). Qed.
Lemma lem3637881 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term905 A B t x x' f g s) = (term906 A B x t x' f g s).
Proof. exact (MK_COMB (@lem3637879 A B g s x t x') (@lem3637880 A B x' f g s)). Qed.
Lemma lem3637882 {A B : Type'} (t : A -> Prop) (x : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term907 A B t x f g s) = (term908 A B t x f g s).
Proof. exact (fun_ext (fun x' : B => @lem3637881 A B x' t x f g s)). Qed.
Lemma lem3637883 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637884 {A B : Type'} (t : A -> Prop) (x : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term896 A B t x f g s) = (term909 A B t x f g s).
Proof. exact (MK_COMB (@lem3637883 B) (@lem3637882 A B t x f g s)). Qed.
Lemma lem3637885 {A B : Type'} (t : A -> Prop) (x : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : ((term895 A B t x f g s) = (term896 A B t x f g s)) = ((term891 A B t x f g s) = (term909 A B t x f g s)).
Proof. exact (MK_COMB (@lem3637876 A B t x f g s) (@lem3637884 A B t x f g s)). Qed.
Lemma lem3637886 {A B : Type'} (t : A -> Prop) (x : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term891 A B t x f g s) = (term909 A B t x f g s).
Proof. exact (EQ_MP (@lem3637885 A B t x f g s) (@lem3637866 A B t x f g s)). Qed.
Lemma lem3637888 {A : Type'} (P : Prop) (Q : A -> Prop) : (term71 A P Q) = (term72 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3637889 {A : Type'} (P : Prop) (Q : A -> Prop) : (term71 A P Q) = (term72 A P Q).
Proof. exact (@lem3637888 A P Q). Qed.
Lemma lem3637890 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term910 A B x t x' f g s) = (term911 A B x t x' f g s).
Proof. exact (@lem3637889 A (term629 A B g s x t x') (term872 A B x' f g s)). Qed.
Lemma lem3637891 {A B : Type'} (x : A) (y : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term912 A B x f g s y) = (term871 A B x y f g s).
Proof. exact (eq_refl (term912 A B x f g s y)). Qed.
Lemma lem3637892 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term913 A B x f g s) = (term872 A B x f g s).
Proof. exact (fun_ext (fun y : A => @lem3637891 A B x y f g s)). Qed.
Lemma lem3637893 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3637894 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term914 A B x f g s) = (term873 A B x f g s).
Proof. exact (MK_COMB (@lem3637893 A) (@lem3637892 A B x f g s)). Qed.
Lemma lem3637895 {A B : Type'} (g : B -> A) (s : B -> Prop) (x : B) (t : A -> Prop) (x' : A) : (term904 A B g s x t x') = (term904 A B g s x t x').
Proof. exact (eq_refl (term904 A B g s x t x')). Qed.
Lemma lem3637896 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term910 A B x t x' f g s) = (term906 A B x t x' f g s).
Proof. exact (MK_COMB (@lem3637895 A B g s x t x') (@lem3637894 A B x' f g s)). Qed.
Lemma lem3637897 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3637898 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term915 A B x t x' f g s) = (term916 A B x t x' f g s).
Proof. exact (MK_COMB (@lem3637897) (@lem3637896 A B x t x' f g s)). Qed.
Lemma lem3637899 {A B : Type'} (x : A) (y : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term912 A B x f g s y) = (term871 A B x y f g s).
Proof. exact (eq_refl (term912 A B x f g s y)). Qed.
Lemma lem3637900 {A B : Type'} (g : B -> A) (s : B -> Prop) (x : B) (t : A -> Prop) (x' : A) : (term904 A B g s x t x') = (term904 A B g s x t x').
Proof. exact (eq_refl (term904 A B g s x t x')). Qed.
Lemma lem3637901 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (y : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term917 A B x t x' f g s y) = (term918 A B x t x' y f g s).
Proof. exact (MK_COMB (@lem3637900 A B g s x t x') (@lem3637899 A B x' y f g s)). Qed.
Lemma lem3637902 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term919 A B x t x' f g s) = (term920 A B x t x' f g s).
Proof. exact (fun_ext (fun y : A => @lem3637901 A B x t x' y f g s)). Qed.
Lemma lem3637903 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3637904 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term911 A B x t x' f g s) = (term921 A B x t x' f g s).
Proof. exact (MK_COMB (@lem3637903 A) (@lem3637902 A B x t x' f g s)). Qed.
Lemma lem3637905 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : ((term910 A B x t x' f g s) = (term911 A B x t x' f g s)) = ((term906 A B x t x' f g s) = (term921 A B x t x' f g s)).
Proof. exact (MK_COMB (@lem3637898 A B x t x' f g s) (@lem3637904 A B x t x' f g s)). Qed.
Lemma lem3637906 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term906 A B x t x' f g s) = (term921 A B x t x' f g s).
Proof. exact (EQ_MP (@lem3637905 A B x t x' f g s) (@lem3637890 A B x t x' f g s)). Qed.
Lemma lem3637908 {A : Type'} (P : Prop) (Q : A -> Prop) : (term71 A P Q) = (term72 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3637909 {B : Type'} (P : Prop) (Q : B -> Prop) : (term71 B P Q) = (term72 B P Q).
Proof. exact (@lem3637908 B P Q). Qed.
Lemma lem3637910 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (y : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term922 A B x t x' y f g s) = (term923 A B x t x' y f g s).
Proof. exact (@lem3637909 B (term629 A B g s x t x') (term870 A B x' y f g s)). Qed.
Lemma lem3637911 {A B : Type'} (x : A) (y : A) (x' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term924 A B x y f g s x') = (term869 A B x y x' f g s).
Proof. exact (eq_refl (term924 A B x y f g s x')). Qed.
Lemma lem3637912 {A B : Type'} (x : A) (y : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term925 A B x y f g s) = (term870 A B x y f g s).
Proof. exact (fun_ext (fun x' : B => @lem3637911 A B x y x' f g s)). Qed.
Lemma lem3637913 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637914 {A B : Type'} (x : A) (y : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term926 A B x y f g s) = (term871 A B x y f g s).
Proof. exact (MK_COMB (@lem3637913 B) (@lem3637912 A B x y f g s)). Qed.
Lemma lem3637915 {A B : Type'} (g : B -> A) (s : B -> Prop) (x : B) (t : A -> Prop) (x' : A) : (term904 A B g s x t x') = (term904 A B g s x t x').
Proof. exact (eq_refl (term904 A B g s x t x')). Qed.
Lemma lem3637916 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (y : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term922 A B x t x' y f g s) = (term918 A B x t x' y f g s).
Proof. exact (MK_COMB (@lem3637915 A B g s x t x') (@lem3637914 A B x' y f g s)). Qed.
Lemma lem3637917 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3637918 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (y : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term927 A B x t x' y f g s) = (term928 A B x t x' y f g s).
Proof. exact (MK_COMB (@lem3637917) (@lem3637916 A B x t x' y f g s)). Qed.
Lemma lem3637919 {A B : Type'} (x : A) (y : A) (x' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term924 A B x y f g s x') = (term869 A B x y x' f g s).
Proof. exact (eq_refl (term924 A B x y f g s x')). Qed.
Lemma lem3637920 {A B : Type'} (g : B -> A) (s : B -> Prop) (x : B) (t : A -> Prop) (x' : A) : (term904 A B g s x t x') = (term904 A B g s x t x').
Proof. exact (eq_refl (term904 A B g s x t x')). Qed.
Lemma lem3637921 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (y : A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term929 A B x t x' y f g s x'') = (term930 A B x t x' y x'' f g s).
Proof. exact (MK_COMB (@lem3637920 A B g s x t x') (@lem3637919 A B x' y x'' f g s)). Qed.
Lemma lem3637922 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (y : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term931 A B x t x' y f g s) = (term932 A B x t x' y f g s).
Proof. exact (fun_ext (fun x'' : B => @lem3637921 A B x t x' y x'' f g s)). Qed.
Lemma lem3637923 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637924 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (y : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term923 A B x t x' y f g s) = (term933 A B x t x' y f g s).
Proof. exact (MK_COMB (@lem3637923 B) (@lem3637922 A B x t x' y f g s)). Qed.
Lemma lem3637925 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (y : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : ((term922 A B x t x' y f g s) = (term923 A B x t x' y f g s)) = ((term918 A B x t x' y f g s) = (term933 A B x t x' y f g s)).
Proof. exact (MK_COMB (@lem3637918 A B x t x' y f g s) (@lem3637924 A B x t x' y f g s)). Qed.
Lemma lem3637926 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (y : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term918 A B x t x' y f g s) = (term933 A B x t x' y f g s).
Proof. exact (EQ_MP (@lem3637925 A B x t x' y f g s) (@lem3637910 A B x t x' y f g s)). Qed.
Lemma lem3637928 {A : Type'} (P : Prop) (Q : A -> Prop) : (term71 A P Q) = (term72 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3637929 {B : Type'} (P : Prop) (Q : B -> Prop) : (term71 B P Q) = (term72 B P Q).
Proof. exact (@lem3637928 B P Q). Qed.
Lemma lem3637930 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (y : A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term934 A B x t x' y x'' f g s) = (term935 A B x t x' y x'' f g s).
Proof. exact (@lem3637929 B (term629 A B g s x t x') (term868 A B x' y x'' f g s)). Qed.
Lemma lem3637931 {A B : Type'} (x'' : B) (x : A) (y : A) (x' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term936 A B x y x' f g s x'') = (term867 A B x'' x y x' f g s).
Proof. exact (eq_refl (term936 A B x y x' f g s x'')). Qed.
Lemma lem3637932 {A B : Type'} (x : A) (y : A) (x' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term937 A B x y x' f g s) = (term868 A B x y x' f g s).
Proof. exact (fun_ext (fun x'' : B => @lem3637931 A B x'' x y x' f g s)). Qed.
Lemma lem3637933 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637934 {A B : Type'} (x : A) (y : A) (x' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term938 A B x y x' f g s) = (term869 A B x y x' f g s).
Proof. exact (MK_COMB (@lem3637933 B) (@lem3637932 A B x y x' f g s)). Qed.
Lemma lem3637935 {A B : Type'} (g : B -> A) (s : B -> Prop) (x : B) (t : A -> Prop) (x' : A) : (term904 A B g s x t x') = (term904 A B g s x t x').
Proof. exact (eq_refl (term904 A B g s x t x')). Qed.
Lemma lem3637936 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (y : A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term934 A B x t x' y x'' f g s) = (term930 A B x t x' y x'' f g s).
Proof. exact (MK_COMB (@lem3637935 A B g s x t x') (@lem3637934 A B x' y x'' f g s)). Qed.
Lemma lem3637937 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3637938 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (y : A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term939 A B x t x' y x'' f g s) = (term940 A B x t x' y x'' f g s).
Proof. exact (MK_COMB (@lem3637937) (@lem3637936 A B x t x' y x'' f g s)). Qed.
Lemma lem3637939 {A B : Type'} (x'' : B) (x : A) (y : A) (x' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term936 A B x y x' f g s x'') = (term867 A B x'' x y x' f g s).
Proof. exact (eq_refl (term936 A B x y x' f g s x'')). Qed.
Lemma lem3637940 {A B : Type'} (g : B -> A) (s : B -> Prop) (x : B) (t : A -> Prop) (x' : A) : (term904 A B g s x t x') = (term904 A B g s x t x').
Proof. exact (eq_refl (term904 A B g s x t x')). Qed.
Lemma lem3637941 {A B : Type'} (x : B) (t : A -> Prop) (x'' : B) (x' : A) (y : A) (x''' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term941 A B x t x' y x''' f g s x'') = (term942 A B x t x'' x' y x''' f g s).
Proof. exact (MK_COMB (@lem3637940 A B g s x t x') (@lem3637939 A B x'' x' y x''' f g s)). Qed.
Lemma lem3637942 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (y : A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term943 A B x t x' y x'' f g s) = (term944 A B x t x' y x'' f g s).
Proof. exact (fun_ext (fun x''' : B => @lem3637941 A B x t x''' x' y x'' f g s)). Qed.
Lemma lem3637943 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637944 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (y : A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term935 A B x t x' y x'' f g s) = (term945 A B x t x' y x'' f g s).
Proof. exact (MK_COMB (@lem3637943 B) (@lem3637942 A B x t x' y x'' f g s)). Qed.
Lemma lem3637945 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (y : A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : ((term934 A B x t x' y x'' f g s) = (term935 A B x t x' y x'' f g s)) = ((term930 A B x t x' y x'' f g s) = (term945 A B x t x' y x'' f g s)).
Proof. exact (MK_COMB (@lem3637938 A B x t x' y x'' f g s) (@lem3637944 A B x t x' y x'' f g s)). Qed.
Lemma lem3637946 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (y : A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term930 A B x t x' y x'' f g s) = (term945 A B x t x' y x'' f g s).
Proof. exact (EQ_MP (@lem3637945 A B x t x' y x'' f g s) (@lem3637930 A B x t x' y x'' f g s)). Qed.
Lemma lem3637948 {A : Type'} (P : Prop) (Q : A -> Prop) : (term71 A P Q) = (term72 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3637949 {A : Type'} (P : Prop) (Q : A -> Prop) : (term71 A P Q) = (term72 A P Q).
Proof. exact (@lem3637948 A P Q). Qed.
Lemma lem3637950 {A B : Type'} (x : B) (t : A -> Prop) (x'' : B) (x' : A) (y : A) (x''' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term946 A B x t x'' x' y x''' f g s) = (term947 A B x t x'' x' y x''' f g s).
Proof. exact (@lem3637949 A (term629 A B g s x t x') (term866 A B x'' x' y x''' f g s)). Qed.
Lemma lem3637951 {A B : Type'} (x'' : B) (x : A) (y : A) (x' : B) (f : A -> B) (x''' : A) (g : B -> A) (s : B -> Prop) : (term948 A B x'' x y x' f g s x''') = (term865 A B x'' x y x' f x''' g s).
Proof. exact (eq_refl (term948 A B x'' x y x' f g s x''')). Qed.
Lemma lem3637952 {A B : Type'} (x'' : B) (x : A) (y : A) (x' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term949 A B x'' x y x' f g s) = (term866 A B x'' x y x' f g s).
Proof. exact (fun_ext (fun x''' : A => @lem3637951 A B x'' x y x' f x''' g s)). Qed.
Lemma lem3637953 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3637954 {A B : Type'} (x'' : B) (x : A) (y : A) (x' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term950 A B x'' x y x' f g s) = (term867 A B x'' x y x' f g s).
Proof. exact (MK_COMB (@lem3637953 A) (@lem3637952 A B x'' x y x' f g s)). Qed.
Lemma lem3637955 {A B : Type'} (g : B -> A) (s : B -> Prop) (x : B) (t : A -> Prop) (x' : A) : (term904 A B g s x t x') = (term904 A B g s x t x').
Proof. exact (eq_refl (term904 A B g s x t x')). Qed.
Lemma lem3637956 {A B : Type'} (x : B) (t : A -> Prop) (x'' : B) (x' : A) (y : A) (x''' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term946 A B x t x'' x' y x''' f g s) = (term942 A B x t x'' x' y x''' f g s).
Proof. exact (MK_COMB (@lem3637955 A B g s x t x') (@lem3637954 A B x'' x' y x''' f g s)). Qed.
Lemma lem3637957 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3637958 {A B : Type'} (x : B) (t : A -> Prop) (x'' : B) (x' : A) (y : A) (x''' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term951 A B x t x'' x' y x''' f g s) = (term952 A B x t x'' x' y x''' f g s).
Proof. exact (MK_COMB (@lem3637957) (@lem3637956 A B x t x'' x' y x''' f g s)). Qed.
Lemma lem3637959 {A B : Type'} (x'' : B) (x : A) (y : A) (x' : B) (f : A -> B) (x''' : A) (g : B -> A) (s : B -> Prop) : (term948 A B x'' x y x' f g s x''') = (term865 A B x'' x y x' f x''' g s).
Proof. exact (eq_refl (term948 A B x'' x y x' f g s x''')). Qed.
Lemma lem3637960 {A B : Type'} (g : B -> A) (s : B -> Prop) (x : B) (t : A -> Prop) (x' : A) : (term904 A B g s x t x') = (term904 A B g s x t x').
Proof. exact (eq_refl (term904 A B g s x t x')). Qed.
Lemma lem3637961 {A B : Type'} (x : B) (t : A -> Prop) (x'' : B) (x' : A) (y : A) (x''' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) : (term953 A B x t x'' x' y x''' f g s x'''') = (term954 A B x t x'' x' y x''' f x'''' g s).
Proof. exact (MK_COMB (@lem3637960 A B g s x t x') (@lem3637959 A B x'' x' y x''' f x'''' g s)). Qed.
Lemma lem3637962 {A B : Type'} (x : B) (t : A -> Prop) (x'' : B) (x' : A) (y : A) (x''' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term955 A B x t x'' x' y x''' f g s) = (term956 A B x t x'' x' y x''' f g s).
Proof. exact (fun_ext (fun x'''' : A => @lem3637961 A B x t x'' x' y x''' f x'''' g s)). Qed.
Lemma lem3637963 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3637964 {A B : Type'} (x : B) (t : A -> Prop) (x'' : B) (x' : A) (y : A) (x''' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term947 A B x t x'' x' y x''' f g s) = (term957 A B x t x'' x' y x''' f g s).
Proof. exact (MK_COMB (@lem3637963 A) (@lem3637962 A B x t x'' x' y x''' f g s)). Qed.
Lemma lem3637965 {A B : Type'} (x : B) (t : A -> Prop) (x'' : B) (x' : A) (y : A) (x''' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : ((term946 A B x t x'' x' y x''' f g s) = (term947 A B x t x'' x' y x''' f g s)) = ((term942 A B x t x'' x' y x''' f g s) = (term957 A B x t x'' x' y x''' f g s)).
Proof. exact (MK_COMB (@lem3637958 A B x t x'' x' y x''' f g s) (@lem3637964 A B x t x'' x' y x''' f g s)). Qed.
Lemma lem3637966 {A B : Type'} (x : B) (t : A -> Prop) (x'' : B) (x' : A) (y : A) (x''' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term942 A B x t x'' x' y x''' f g s) = (term957 A B x t x'' x' y x''' f g s).
Proof. exact (EQ_MP (@lem3637965 A B x t x'' x' y x''' f g s) (@lem3637950 A B x t x'' x' y x''' f g s)). Qed.
Lemma lem3637968 {A : Type'} (P : Prop) (Q : A -> Prop) : (term71 A P Q) = (term72 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3637969 {B : Type'} (P : Prop) (Q : B -> Prop) : (term71 B P Q) = (term72 B P Q).
Proof. exact (@lem3637968 B P Q). Qed.
Lemma lem3637970 {A B : Type'} (x : B) (t : A -> Prop) (x'' : B) (x' : A) (y : A) (x''' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) : (term958 A B x t x'' x' y x''' f x'''' g s) = (term959 A B x t x'' x' y x''' f x'''' g s).
Proof. exact (@lem3637969 B (term629 A B g s x t x') (term864 A B x'' x' y x''' f x'''' g s)). Qed.
Lemma lem3637971 {A B : Type'} (x'' : B) (x : A) (y : A) (x' : B) (f : A -> B) (x''' : A) (g : B -> A) (s : B -> Prop) (x'''' : B) : (term960 A B x'' x y x' f x''' g s x'''') = (term862 A B x'' x y x' f x''' g s x'''').
Proof. exact (eq_refl (term960 A B x'' x y x' f x''' g s x'''')). Qed.
Lemma lem3637972 {A B : Type'} (x'' : B) (x : A) (y : A) (x' : B) (f : A -> B) (x''' : A) (g : B -> A) (s : B -> Prop) : (term961 A B x'' x y x' f x''' g s) = (term864 A B x'' x y x' f x''' g s).
Proof. exact (fun_ext (fun x'''' : B => @lem3637971 A B x'' x y x' f x''' g s x'''')). Qed.
Lemma lem3637973 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637974 {A B : Type'} (x'' : B) (x : A) (y : A) (x' : B) (f : A -> B) (x''' : A) (g : B -> A) (s : B -> Prop) : (term962 A B x'' x y x' f x''' g s) = (term865 A B x'' x y x' f x''' g s).
Proof. exact (MK_COMB (@lem3637973 B) (@lem3637972 A B x'' x y x' f x''' g s)). Qed.
Lemma lem3637975 {A B : Type'} (g : B -> A) (s : B -> Prop) (x : B) (t : A -> Prop) (x' : A) : (term904 A B g s x t x') = (term904 A B g s x t x').
Proof. exact (eq_refl (term904 A B g s x t x')). Qed.
Lemma lem3637976 {A B : Type'} (x : B) (t : A -> Prop) (x'' : B) (x' : A) (y : A) (x''' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) : (term958 A B x t x'' x' y x''' f x'''' g s) = (term954 A B x t x'' x' y x''' f x'''' g s).
Proof. exact (MK_COMB (@lem3637975 A B g s x t x') (@lem3637974 A B x'' x' y x''' f x'''' g s)). Qed.
Lemma lem3637977 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3637978 {A B : Type'} (x : B) (t : A -> Prop) (x'' : B) (x' : A) (y : A) (x''' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) : (term963 A B x t x'' x' y x''' f x'''' g s) = (term964 A B x t x'' x' y x''' f x'''' g s).
Proof. exact (MK_COMB (@lem3637977) (@lem3637976 A B x t x'' x' y x''' f x'''' g s)). Qed.
Lemma lem3637979 {A B : Type'} (x'' : B) (x : A) (y : A) (x' : B) (f : A -> B) (x''' : A) (g : B -> A) (s : B -> Prop) (x'''' : B) : (term960 A B x'' x y x' f x''' g s x'''') = (term862 A B x'' x y x' f x''' g s x'''').
Proof. exact (eq_refl (term960 A B x'' x y x' f x''' g s x'''')). Qed.
Lemma lem3637980 {A B : Type'} (g : B -> A) (s : B -> Prop) (x : B) (t : A -> Prop) (x' : A) : (term904 A B g s x t x') = (term904 A B g s x t x').
Proof. exact (eq_refl (term904 A B g s x t x')). Qed.
Lemma lem3637981 {A B : Type'} (x : B) (t : A -> Prop) (x'' : B) (x' : A) (y : A) (x''' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) : (term965 A B x t x'' x' y x''' f x'''' g s x''''') = (term966 A B x t x'' x' y x''' f x'''' g s x''''').
Proof. exact (MK_COMB (@lem3637980 A B g s x t x') (@lem3637979 A B x'' x' y x''' f x'''' g s x''''')). Qed.
Lemma lem3637982 {A B : Type'} (x : B) (t : A -> Prop) (x'' : B) (x' : A) (y : A) (x''' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) : (term967 A B x t x'' x' y x''' f x'''' g s) = (term968 A B x t x'' x' y x''' f x'''' g s).
Proof. exact (fun_ext (fun x''''' : B => @lem3637981 A B x t x'' x' y x''' f x'''' g s x''''')). Qed.
Lemma lem3637983 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637984 {A B : Type'} (x : B) (t : A -> Prop) (x'' : B) (x' : A) (y : A) (x''' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) : (term959 A B x t x'' x' y x''' f x'''' g s) = (term969 A B x t x'' x' y x''' f x'''' g s).
Proof. exact (MK_COMB (@lem3637983 B) (@lem3637982 A B x t x'' x' y x''' f x'''' g s)). Qed.
Lemma lem3637985 {A B : Type'} (x : B) (t : A -> Prop) (x'' : B) (x' : A) (y : A) (x''' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) : ((term958 A B x t x'' x' y x''' f x'''' g s) = (term959 A B x t x'' x' y x''' f x'''' g s)) = ((term954 A B x t x'' x' y x''' f x'''' g s) = (term969 A B x t x'' x' y x''' f x'''' g s)).
Proof. exact (MK_COMB (@lem3637978 A B x t x'' x' y x''' f x'''' g s) (@lem3637984 A B x t x'' x' y x''' f x'''' g s)). Qed.
Lemma lem3637986 {A B : Type'} (x : B) (t : A -> Prop) (x'' : B) (x' : A) (y : A) (x''' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) : (term954 A B x t x'' x' y x''' f x'''' g s) = (term969 A B x t x'' x' y x''' f x'''' g s).
Proof. exact (EQ_MP (@lem3637985 A B x t x'' x' y x''' f x'''' g s) (@lem3637970 A B x t x'' x' y x''' f x'''' g s)). Qed.
Lemma lem3637987 {A B : Type'} (x : B) (t : A -> Prop) (x'' : B) (x' : A) (y : A) (x''' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term956 A B x t x'' x' y x''' f g s) = (term970 A B x t x'' x' y x''' f g s).
Proof. exact (fun_ext (fun x'''' : A => @lem3637986 A B x t x'' x' y x''' f x'''' g s)). Qed.
Lemma lem3637988 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3637989 {A B : Type'} (x : B) (t : A -> Prop) (x'' : B) (x' : A) (y : A) (x''' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term957 A B x t x'' x' y x''' f g s) = (term971 A B x t x'' x' y x''' f g s).
Proof. exact (MK_COMB (@lem3637988 A) (@lem3637987 A B x t x'' x' y x''' f g s)). Qed.
Lemma lem3637990 {A B : Type'} (x : B) (t : A -> Prop) (x'' : B) (x' : A) (y : A) (x''' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term942 A B x t x'' x' y x''' f g s) = (term971 A B x t x'' x' y x''' f g s).
Proof. exact (TRANS (@lem3637966 A B x t x'' x' y x''' f g s) (@lem3637989 A B x t x'' x' y x''' f g s)). Qed.
Lemma lem3637991 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (y : A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term944 A B x t x' y x'' f g s) = (term972 A B x t x' y x'' f g s).
Proof. exact (fun_ext (fun x''' : B => @lem3637990 A B x t x''' x' y x'' f g s)). Qed.
Lemma lem3637992 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637993 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (y : A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term945 A B x t x' y x'' f g s) = (term973 A B x t x' y x'' f g s).
Proof. exact (MK_COMB (@lem3637992 B) (@lem3637991 A B x t x' y x'' f g s)). Qed.
Lemma lem3637994 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (y : A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term930 A B x t x' y x'' f g s) = (term973 A B x t x' y x'' f g s).
Proof. exact (TRANS (@lem3637946 A B x t x' y x'' f g s) (@lem3637993 A B x t x' y x'' f g s)). Qed.
Lemma lem3637995 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (y : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term932 A B x t x' y f g s) = (term974 A B x t x' y f g s).
Proof. exact (fun_ext (fun x'' : B => @lem3637994 A B x t x' y x'' f g s)). Qed.
Lemma lem3637996 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3637997 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (y : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term933 A B x t x' y f g s) = (term975 A B x t x' y f g s).
Proof. exact (MK_COMB (@lem3637996 B) (@lem3637995 A B x t x' y f g s)). Qed.
Lemma lem3637998 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (y : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term918 A B x t x' y f g s) = (term975 A B x t x' y f g s).
Proof. exact (TRANS (@lem3637926 A B x t x' y f g s) (@lem3637997 A B x t x' y f g s)). Qed.
Lemma lem3637999 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term920 A B x t x' f g s) = (term976 A B x t x' f g s).
Proof. exact (fun_ext (fun y : A => @lem3637998 A B x t x' y f g s)). Qed.
Lemma lem3638000 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3638001 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term921 A B x t x' f g s) = (term977 A B x t x' f g s).
Proof. exact (MK_COMB (@lem3638000 A) (@lem3637999 A B x t x' f g s)). Qed.
Lemma lem3638002 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term906 A B x t x' f g s) = (term977 A B x t x' f g s).
Proof. exact (TRANS (@lem3637906 A B x t x' f g s) (@lem3638001 A B x t x' f g s)). Qed.
Lemma lem3638003 {A B : Type'} (t : A -> Prop) (x : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term908 A B t x f g s) = (term978 A B t x f g s).
Proof. exact (fun_ext (fun x' : B => @lem3638002 A B x' t x f g s)). Qed.
Lemma lem3638004 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3638005 {A B : Type'} (t : A -> Prop) (x : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term909 A B t x f g s) = (term979 A B t x f g s).
Proof. exact (MK_COMB (@lem3638004 B) (@lem3638003 A B t x f g s)). Qed.
Lemma lem3638006 {A B : Type'} (t : A -> Prop) (x : A) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term891 A B t x f g s) = (term979 A B t x f g s).
Proof. exact (TRANS (@lem3637886 A B t x f g s) (@lem3638005 A B t x f g s)). Qed.
Lemma lem3638007 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term893 A B t f g s) = (term980 A B t f g s).
Proof. exact (fun_ext (fun x : A => @lem3638006 A B t x f g s)). Qed.
Lemma lem3638008 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3638009 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term894 A B t f g s) = (term981 A B t f g s).
Proof. exact (MK_COMB (@lem3638008 A) (@lem3638007 A B t f g s)). Qed.
Lemma lem3638010 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term876 A B t f g s) = (term981 A B t f g s).
Proof. exact (TRANS (@lem3637860 A B t f g s) (@lem3638009 A B t f g s)). Qed.
Lemma lem3638011 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term620 A B t f g s) = (term981 A B t f g s).
Proof. exact (TRANS (@lem3637833 A B t f g s) (@lem3638010 A B t f g s)). Qed.
Lemma lem3638012 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term596 A B t f g s) = (term981 A B t f g s).
Proof. exact (TRANS (@lem3637372 A B t f g s) (@lem3638011 A B t f g s)). Qed.
Lemma lem3638013 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term459 A B t f g s) = (term981 A B t f g s).
Proof. exact (TRANS (@lem3636893 A B t f g s) (@lem3638012 A B t f g s)). Qed.
Lemma lem3638014 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term459 A B t f g s) : term981 A B t f g s.
Proof. exact (EQ_MP (@lem3638013 A B t f g s) (@lem3636486 A B t f g s h1)). Qed.
Lemma lem3638015 {A B : Type'} (t : A -> Prop) (x : A) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term979 A B t x f g s) : term979 A B t x f g s.
Proof. exact (h1). Qed.
Lemma lem3638016 {A B : Type'} (x' : B) (t : A -> Prop) (x : A) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term977 A B x' t x f g s) : term977 A B x' t x f g s.
Proof. exact (h1). Qed.
Lemma lem3638017 {A B : Type'} (x' : B) (t : A -> Prop) (x : A) (y : A) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term975 A B x' t x y f g s) : term975 A B x' t x y f g s.
Proof. exact (h1). Qed.
Lemma lem3638018 {A B : Type'} (x' : B) (t : A -> Prop) (x : A) (y : A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term973 A B x' t x y x'' f g s) : term973 A B x' t x y x'' f g s.
Proof. exact (h1). Qed.
Lemma lem3638019 {A B : Type'} (x' : B) (t : A -> Prop) (x''' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term971 A B x' t x''' x y x'' f g s) : term971 A B x' t x''' x y x'' f g s.
Proof. exact (h1). Qed.
Lemma lem3638020 {A B : Type'} (x' : B) (t : A -> Prop) (x''' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (h1 : term969 A B x' t x''' x y x'' f x'''' g s) : term969 A B x' t x''' x y x'' f x'''' g s.
Proof. exact (h1). Qed.
Lemma lem3638021 {A B : Type'} (x' : B) (t : A -> Prop) (x''' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term966 A B x' t x''' x y x'' f x'''' g s x''''') : term966 A B x' t x''' x y x'' f x'''' g s x'''''.
Proof. exact (h1). Qed.
Lemma lem3638022 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term518 A B g s f t x''''''.
Proof. exact (h1). Qed.
Lemma lem3638053 {A B : Type'} (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) : (term727 A B x'' f x'''' g s x''''') = (term727 A B x'' f x'''' g s x''''').
Proof. exact (eq_refl (term727 A B x'' f x'''' g s x''''')). Qed.
Lemma lem3638070 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) (x' : B) : (term554 A B x g s x') = (term554 A B x g s x').
Proof. exact (eq_refl (term554 A B x g s x')). Qed.
Lemma lem3638071 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term559 A B x g s) = (term559 A B x g s).
Proof. exact (fun_ext (fun x' : B => @lem3638070 A B x g s x')). Qed.
Lemma lem3638072 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3638073 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term560 A B x g s) = (term560 A B x g s).
Proof. exact (MK_COMB (@lem3638072 B) (@lem3638071 A B x g s)). Qed.
Lemma lem3638084 {A B : Type'} (x'' : B) (f : A -> B) (x : A) : (term561 A B x'' f x) = (term561 A B x'' f x).
Proof. exact (eq_refl (term561 A B x'' f x)). Qed.
Lemma lem3638085 {A B : Type'} (x'' : B) (f : A -> B) (x : A) (g : B -> A) (s : B -> Prop) : (term563 A B x'' f x g s) = (term563 A B x'' f x g s).
Proof. exact (MK_COMB (@lem3638084 A B x'' f x) (@lem3638073 A B x g s)). Qed.
Lemma lem3638086 {A B : Type'} (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term570 A B x'' f g s) = (term570 A B x'' f g s).
Proof. exact (fun_ext (fun x : A => @lem3638085 A B x'' f x g s)). Qed.
Lemma lem3638087 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3638088 {A B : Type'} (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term571 A B x'' f g s) = (term571 A B x'' f g s).
Proof. exact (MK_COMB (@lem3638087 A) (@lem3638086 A B x'' f g s)). Qed.
Lemma lem3638093 {B : Type'} (s : B -> Prop) (x'' : B) : (term32 B s x'') = (term32 B s x'').
Proof. exact (eq_refl (term32 B s x'')). Qed.
Lemma lem3638094 {A B : Type'} (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term575 A B x'' f g s) = (term575 A B x'' f g s).
Proof. exact (MK_COMB (@lem3638093 B s x'') (@lem3638088 A B x'' f g s)). Qed.
Lemma lem3638095 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3638096 {A B : Type'} (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term577 A B x'' f g s) = (term577 A B x'' f g s).
Proof. exact (MK_COMB (@lem3638095) (@lem3638094 A B x'' f g s)). Qed.
Lemma lem3638097 {A B : Type'} (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) : (term768 A B x'' f x'''' g s x''''') = (term768 A B x'' f x'''' g s x''''').
Proof. exact (MK_COMB (@lem3638096 A B x'' f g s) (@lem3638053 A B x'' f x'''' g s x''''')). Qed.
Lemma lem3638172 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) : (term836 A B x'' g s x''' f x y) = (term836 A B x'' g s x''' f x y).
Proof. exact (eq_refl (term836 A B x'' g s x''' f x y)). Qed.
Lemma lem3638173 {A B : Type'} (x''' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) : (term862 A B x''' x y x'' f x'''' g s x''''') = (term862 A B x''' x y x'' f x'''' g s x''''').
Proof. exact (MK_COMB (@lem3638172 A B x'' g s x''' f x y) (@lem3638097 A B x'' f x'''' g s x''''')). Qed.
Lemma lem3638196 {A B : Type'} (g : B -> A) (s : B -> Prop) (x' : B) (t : A -> Prop) (x : A) : (term904 A B g s x' t x) = (term904 A B g s x' t x).
Proof. exact (eq_refl (term904 A B g s x' t x)). Qed.
Lemma lem3638197 {A B : Type'} (x' : B) (t : A -> Prop) (x''' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) : (term966 A B x' t x''' x y x'' f x'''' g s x''''') = (term966 A B x' t x''' x y x'' f x'''' g s x''''').
Proof. exact (MK_COMB (@lem3638196 A B g s x' t x) (@lem3638173 A B x''' x y x'' f x'''' g s x''''')). Qed.
Lemma lem3638198 {A B : Type'} (x' : B) (t : A -> Prop) (x''' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term966 A B x' t x''' x y x'' f x'''' g s x''''') : term966 A B x' t x''' x y x'' f x'''' g s x'''''.
Proof. exact (EQ_MP (@lem3638197 A B x' t x''' x y x'' f x'''' g s x''''') (@lem3638021 A B x' t x''' x y x'' f x'''' g s x''''' h1)). Qed.
Lemma lem3638223 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (x : B) : (term497 A B s f t x'''''' x) = (term497 A B s f t x'''''' x).
Proof. exact (eq_refl (term497 A B s f t x'''''' x)). Qed.
Lemma lem3638224 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) : (term499 A B s f t x'''''') = (term499 A B s f t x'''''').
Proof. exact (fun_ext (fun x : B => @lem3638223 A B s f t x'''''' x)). Qed.
Lemma lem3638225 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3638226 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) : (term501 A B s f t x'''''') = (term501 A B s f t x'''''').
Proof. exact (MK_COMB (@lem3638225 B) (@lem3638224 A B s f t x'''''')). Qed.
Lemma lem3638251 {A B : Type'} (s : B -> Prop) (t : A -> Prop) (f : A -> B) (g : B -> A) (x : B) : (term460 A B s t f g x) = (term460 A B s t f g x).
Proof. exact (eq_refl (term460 A B s t f g x)). Qed.
Lemma lem3638252 {A B : Type'} (s : B -> Prop) (t : A -> Prop) (f : A -> B) (g : B -> A) : (term461 A B s t f g) = (term461 A B s t f g).
Proof. exact (fun_ext (fun x : B => @lem3638251 A B s t f g x)). Qed.
Lemma lem3638253 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3638254 {A B : Type'} (s : B -> Prop) (t : A -> Prop) (f : A -> B) (g : B -> A) : (term462 A B s t f g) = (term462 A B s t f g).
Proof. exact (MK_COMB (@lem3638253 B) (@lem3638252 A B s t f g)). Qed.
Lemma lem3638255 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3638256 {A B : Type'} (s : B -> Prop) (t : A -> Prop) (f : A -> B) (g : B -> A) : (term466 A B s t f g) = (term466 A B s t f g).
Proof. exact (MK_COMB (@lem3638255) (@lem3638254 A B s t f g)). Qed.
Lemma lem3638257 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) : (term518 A B g s f t x'''''') = (term518 A B g s f t x'''''').
Proof. exact (MK_COMB (@lem3638256 A B s t f g) (@lem3638226 A B s f t x'''''')). Qed.
Lemma lem3638258 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term518 A B g s f t x''''''.
Proof. exact (EQ_MP (@lem3638257 A B g s f t x'''''') (@lem3638022 A B g s f t x'''''' h1)). Qed.
Lemma lem3638260 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term462 A B s t f g.
Proof. exact (proj1 (@lem3638258 A B g s f t x'''''' h1)). Qed.
Lemma lem3638261 {A B : Type'} (g : B -> A) (s : B -> Prop) (x' : B) (t : A -> Prop) (x : A) (h1 : term629 A B g s x' t x) : term629 A B g s x' t x.
Proof. exact (h1). Qed.
Lemma lem3638262 {A B : Type'} (x''' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term862 A B x''' x y x'' f x'''' g s x''''') : term862 A B x''' x y x'' f x'''' g s x'''''.
Proof. exact (h1). Qed.
Lemma lem3638264 {A B : Type'} (g : B -> A) (s : B -> Prop) (x' : B) (t : A -> Prop) (x : A) (h1 : term629 A B g s x' t x) : term21 A B x g s x'.
Proof. exact (proj1 (@lem3638261 A B g s x' t x h1)). Qed.
Lemma lem3638267 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term684 A B x'' g s x''' f x y) : term684 A B x'' g s x''' f x y.
Proof. exact (h1). Qed.
Lemma lem3638268 {A B : Type'} (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term768 A B x'' f x'''' g s x''''') : term768 A B x'' f x'''' g s x'''''.
Proof. exact (h1). Qed.
Lemma lem3638269 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term684 A B x'' g s x''' f x y) : term534 A B f x y.
Proof. exact (proj2 (@lem3638267 A B x'' g s x''' f x y h1)). Qed.
Lemma lem3638270 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term684 A B x'' g s x''' f x y) : term650 A B x x'' y g s x'''.
Proof. exact (proj1 (@lem3638267 A B x'' g s x''' f x y h1)). Qed.
Lemma lem3638271 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term684 A B x'' g s x''' f x y) : term21 A B y g s x'''.
Proof. exact (proj2 (@lem3638270 A B x'' g s x''' f x y h1)). Qed.
Lemma lem3638272 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term684 A B x'' g s x''' f x y) : term21 A B x g s x''.
Proof. exact (proj1 (@lem3638270 A B x'' g s x''' f x y h1)). Qed.
Lemma lem3638277 {A B : Type'} (f : A -> B) (x : A) (y : A) (h1 : term982 A B f x y) : term982 A B f x y.
Proof. exact (h1). Qed.
Lemma lem3638278 {A B : Type'} (f : A -> B) (x : A) (y : A) (h1 : term983 A B f x y) : term983 A B f x y.
Proof. exact (h1). Qed.
Lemma lem3638283 {A B : Type'} (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term575 A B x'' f g s) : term575 A B x'' f g s.
Proof. exact (h1). Qed.
Lemma lem3638284 {A B : Type'} (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term727 A B x'' f x'''' g s x''''') : term727 A B x'' f x'''' g s x'''''.
Proof. exact (h1). Qed.
Lemma lem3638285 {A B : Type'} (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term575 A B x'' f g s) : term571 A B x'' f g s.
Proof. exact (proj2 (@lem3638283 A B x'' f g s h1)). Qed.
Lemma lem3638287 {A B : Type'} (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term727 A B x'' f x'''' g s x''''') : term700 A B x'' f x'''' g s x'''''.
Proof. exact (proj2 (@lem3638284 A B x'' f x'''' g s x''''' h1)). Qed.
Lemma lem3638289 {A B : Type'} (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term727 A B x'' f x'''' g s x''''') : term21 A B x'''' g s x'''''.
Proof. exact (proj2 (@lem3638287 A B x'' f x'''' g s x''''' h1)). Qed.
Lemma lem3638310 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (g : B -> A) (x : B) : (term460 A B s t f g x) = (term984 A B t s f g x).
Proof. exact (@lem19490 (term371 A B t g x) (term75 B s x) ((term374 A B f g x) = x)). Qed.
Lemma lem3638311 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (g : B -> A) : (term461 A B s t f g) = (term985 A B t s f g).
Proof. exact (fun_ext (fun x : B => @lem3638310 A B t s f g x)). Qed.
Lemma lem3638312 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3638314 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (g : B -> A) : (term462 A B s t f g) = (term986 A B t s f g).
Proof. exact (MK_COMB (@lem3638312 B) (@lem3638311 A B t s f g)). Qed.
Lemma lem3638315 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term986 A B t s f g.
Proof. exact (EQ_MP (@lem3638314 A B t s f g) (@lem3638260 A B g s f t x'''''' h1)). Qed.
Lemma lem3638368 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (g : B -> A) (x : B) : (term460 A B s t f g x) = (term984 A B t s f g x).
Proof. exact (@lem19490 (term371 A B t g x) (term75 B s x) ((term374 A B f g x) = x)). Qed.
Lemma lem3638369 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (g : B -> A) : (term461 A B s t f g) = (term985 A B t s f g).
Proof. exact (fun_ext (fun x : B => @lem3638368 A B t s f g x)). Qed.
Lemma lem3638370 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3638372 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (g : B -> A) : (term462 A B s t f g) = (term986 A B t s f g).
Proof. exact (MK_COMB (@lem3638370 B) (@lem3638369 A B t s f g)). Qed.
Lemma lem3638373 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term986 A B t s f g.
Proof. exact (EQ_MP (@lem3638372 A B t s f g) (@lem3638260 A B g s f t x'''''' h1)). Qed.
Lemma lem3638508 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (g : B -> A) (x : B) : (term460 A B s t f g x) = (term984 A B t s f g x).
Proof. exact (@lem19490 (term371 A B t g x) (term75 B s x) ((term374 A B f g x) = x)). Qed.
Lemma lem3638509 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (g : B -> A) : (term461 A B s t f g) = (term985 A B t s f g).
Proof. exact (fun_ext (fun x : B => @lem3638508 A B t s f g x)). Qed.
Lemma lem3638510 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3638512 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (g : B -> A) : (term462 A B s t f g) = (term986 A B t s f g).
Proof. exact (MK_COMB (@lem3638510 B) (@lem3638509 A B t s f g)). Qed.
Lemma lem3638513 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term986 A B t s f g.
Proof. exact (EQ_MP (@lem3638512 A B t s f g) (@lem3638260 A B g s f t x'''''' h1)). Qed.
Lemma lem3638542 {A : Type'} (P : Prop) (Q : A -> Prop) : (term987 A P Q) = (term988 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3638543 {B : Type'} (P : Prop) (Q : B -> Prop) : (term987 B P Q) = (term988 B P Q).
Proof. exact (@lem3638542 B P Q). Qed.
Lemma lem3638544 {A B : Type'} (x'' : B) (f : A -> B) (x : A) (g : B -> A) (s : B -> Prop) : (term989 A B x'' f x g s) = (term990 A B x'' f x g s).
Proof. exact (@lem3638543 B (term991 A B x'' f x) (term559 A B x g s)). Qed.
Lemma lem3638545 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) (x' : B) : (term992 A B x g s x') = (term554 A B x g s x').
Proof. exact (eq_refl (term992 A B x g s x')). Qed.
Lemma lem3638546 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term993 A B x g s) = (term559 A B x g s).
Proof. exact (fun_ext (fun x' : B => @lem3638545 A B x g s x')). Qed.
Lemma lem3638547 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3638548 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) : (term994 A B x g s) = (term560 A B x g s).
Proof. exact (MK_COMB (@lem3638547 B) (@lem3638546 A B x g s)). Qed.
Lemma lem3638549 {A B : Type'} (x'' : B) (f : A -> B) (x : A) : (term561 A B x'' f x) = (term561 A B x'' f x).
Proof. exact (eq_refl (term561 A B x'' f x)). Qed.
Lemma lem3638550 {A B : Type'} (x'' : B) (f : A -> B) (x : A) (g : B -> A) (s : B -> Prop) : (term989 A B x'' f x g s) = (term563 A B x'' f x g s).
Proof. exact (MK_COMB (@lem3638549 A B x'' f x) (@lem3638548 A B x g s)). Qed.
Lemma lem3638551 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3638552 {A B : Type'} (x'' : B) (f : A -> B) (x : A) (g : B -> A) (s : B -> Prop) : (term995 A B x'' f x g s) = (term996 A B x'' f x g s).
Proof. exact (MK_COMB (@lem3638551) (@lem3638550 A B x'' f x g s)). Qed.
Lemma lem3638553 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) (x' : B) : (term992 A B x g s x') = (term554 A B x g s x').
Proof. exact (eq_refl (term992 A B x g s x')). Qed.
Lemma lem3638554 {A B : Type'} (x'' : B) (f : A -> B) (x : A) : (term561 A B x'' f x) = (term561 A B x'' f x).
Proof. exact (eq_refl (term561 A B x'' f x)). Qed.
Lemma lem3638555 {A B : Type'} (x'' : B) (f : A -> B) (x : A) (g : B -> A) (s : B -> Prop) (x' : B) : (term997 A B x'' f x g s x') = (term998 A B x'' f x g s x').
Proof. exact (MK_COMB (@lem3638554 A B x'' f x) (@lem3638553 A B x g s x')). Qed.
Lemma lem3638556 {A B : Type'} (x'' : B) (f : A -> B) (x : A) (g : B -> A) (s : B -> Prop) : (term999 A B x'' f x g s) = (term1000 A B x'' f x g s).
Proof. exact (fun_ext (fun x' : B => @lem3638555 A B x'' f x g s x')). Qed.
Lemma lem3638557 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3638558 {A B : Type'} (x'' : B) (f : A -> B) (x : A) (g : B -> A) (s : B -> Prop) : (term990 A B x'' f x g s) = (term1001 A B x'' f x g s).
Proof. exact (MK_COMB (@lem3638557 B) (@lem3638556 A B x'' f x g s)). Qed.
Lemma lem3638559 {A B : Type'} (x'' : B) (f : A -> B) (x : A) (g : B -> A) (s : B -> Prop) : ((term989 A B x'' f x g s) = (term990 A B x'' f x g s)) = ((term563 A B x'' f x g s) = (term1001 A B x'' f x g s)).
Proof. exact (MK_COMB (@lem3638552 A B x'' f x g s) (@lem3638558 A B x'' f x g s)). Qed.
Lemma lem3638560 {A B : Type'} (x'' : B) (f : A -> B) (x : A) (g : B -> A) (s : B -> Prop) : (term563 A B x'' f x g s) = (term1001 A B x'' f x g s).
Proof. exact (EQ_MP (@lem3638559 A B x'' f x g s) (@lem3638544 A B x'' f x g s)). Qed.
Lemma lem3638561 {A B : Type'} (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term570 A B x'' f g s) = (term1002 A B x'' f g s).
Proof. exact (fun_ext (fun x : A => @lem3638560 A B x'' f x g s)). Qed.
Lemma lem3638562 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3638563 {A B : Type'} (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term571 A B x'' f g s) = (term1003 A B x'' f g s).
Proof. exact (MK_COMB (@lem3638562 A) (@lem3638561 A B x'' f g s)). Qed.
Lemma lem3638576 {A B : Type'} (x'' : B) (f : A -> B) (x : A) (g : B -> A) (s : B -> Prop) (x' : B) : (term998 A B x'' f x g s x') = (term998 A B x'' f x g s x').
Proof. exact (eq_refl (term998 A B x'' f x g s x')). Qed.
Lemma lem3638577 {A B : Type'} (x'' : B) (f : A -> B) (x : A) (g : B -> A) (s : B -> Prop) : (term1000 A B x'' f x g s) = (term1000 A B x'' f x g s).
Proof. exact (fun_ext (fun x' : B => @lem3638576 A B x'' f x g s x')). Qed.
Lemma lem3638578 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3638579 {A B : Type'} (x'' : B) (f : A -> B) (x : A) (g : B -> A) (s : B -> Prop) : (term1001 A B x'' f x g s) = (term1001 A B x'' f x g s).
Proof. exact (MK_COMB (@lem3638578 B) (@lem3638577 A B x'' f x g s)). Qed.
Lemma lem3638580 {A B : Type'} (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term1002 A B x'' f g s) = (term1002 A B x'' f g s).
Proof. exact (fun_ext (fun x : A => @lem3638579 A B x'' f x g s)). Qed.
Lemma lem3638581 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3638582 {A B : Type'} (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term1003 A B x'' f g s) = (term1003 A B x'' f g s).
Proof. exact (MK_COMB (@lem3638581 A) (@lem3638580 A B x'' f g s)). Qed.
Lemma lem3638583 {A B : Type'} (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term571 A B x'' f g s) = (term1003 A B x'' f g s).
Proof. exact (TRANS (@lem3638563 A B x'' f g s) (@lem3638582 A B x'' f g s)). Qed.
Lemma lem3638584 {A B : Type'} (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term575 A B x'' f g s) : term1003 A B x'' f g s.
Proof. exact (EQ_MP (@lem3638583 A B x'' f g s) (@lem3638285 A B x'' f g s h1)). Qed.
Lemma lem3638602 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (g : B -> A) (x : B) : (term460 A B s t f g x) = (term984 A B t s f g x).
Proof. exact (@lem19490 (term371 A B t g x) (term75 B s x) ((term374 A B f g x) = x)). Qed.
Lemma lem3638603 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (g : B -> A) : (term461 A B s t f g) = (term985 A B t s f g).
Proof. exact (fun_ext (fun x : B => @lem3638602 A B t s f g x)). Qed.
Lemma lem3638604 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3638606 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (g : B -> A) : (term462 A B s t f g) = (term986 A B t s f g).
Proof. exact (MK_COMB (@lem3638604 B) (@lem3638603 A B t s f g)). Qed.
Lemma lem3638607 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term986 A B t s f g.
Proof. exact (EQ_MP (@lem3638606 A B t s f g) (@lem3638260 A B g s f t x'''''' h1)). Qed.
Lemma lem3638647 {A B : Type'} (_39725 : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term1004 A B t s f g _39725.
Proof. exact (@lem3638315 A B g s f t x'''''' h1 _39725). Qed.
Lemma lem3638648 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (g : B -> A) (_39725 : B) : (term1004 A B t s f g _39725) = (term984 A B t s f g _39725).
Proof. exact (eq_refl (term1004 A B t s f g _39725)). Qed.
Lemma lem3638649 {A B : Type'} (_39725 : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term984 A B t s f g _39725.
Proof. exact (EQ_MP (@lem3638648 A B t s f g _39725) (@lem3638647 A B _39725 g s f t x'''''' h1)). Qed.
Lemma lem3638653 {A B : Type'} (_39727 : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term1004 A B t s f g _39727.
Proof. exact (@lem3638373 A B g s f t x'''''' h1 _39727). Qed.
Lemma lem3638654 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (g : B -> A) (_39727 : B) : (term1004 A B t s f g _39727) = (term984 A B t s f g _39727).
Proof. exact (eq_refl (term1004 A B t s f g _39727)). Qed.
Lemma lem3638655 {A B : Type'} (_39727 : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term984 A B t s f g _39727.
Proof. exact (EQ_MP (@lem3638654 A B t s f g _39727) (@lem3638653 A B _39727 g s f t x'''''' h1)). Qed.
Lemma lem3638665 {A B : Type'} (_39731 : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term1004 A B t s f g _39731.
Proof. exact (@lem3638513 A B g s f t x'''''' h1 _39731). Qed.
Lemma lem3638666 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (g : B -> A) (_39731 : B) : (term1004 A B t s f g _39731) = (term984 A B t s f g _39731).
Proof. exact (eq_refl (term1004 A B t s f g _39731)). Qed.
Lemma lem3638667 {A B : Type'} (_39731 : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term984 A B t s f g _39731.
Proof. exact (EQ_MP (@lem3638666 A B t s f g _39731) (@lem3638665 A B _39731 g s f t x'''''' h1)). Qed.
Lemma lem3638671 {A B : Type'} (_39733 : A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term575 A B x'' f g s) : term1005 A B x'' f g s _39733.
Proof. exact (@lem3638584 A B x'' f g s h1 _39733). Qed.
Lemma lem3638672 {A B : Type'} (x'' : B) (f : A -> B) (_39733 : A) (g : B -> A) (s : B -> Prop) : (term1005 A B x'' f g s _39733) = (term1001 A B x'' f _39733 g s).
Proof. exact (eq_refl (term1005 A B x'' f g s _39733)). Qed.
Lemma lem3638673 {A B : Type'} (_39733 : A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term575 A B x'' f g s) : term1001 A B x'' f _39733 g s.
Proof. exact (EQ_MP (@lem3638672 A B x'' f _39733 g s) (@lem3638671 A B _39733 x'' f g s h1)). Qed.
Lemma lem3638674 {A B : Type'} (_39733 : A) (_39734 : B) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term575 A B x'' f g s) : term1006 A B x'' f _39733 g s _39734.
Proof. exact (@lem3638673 A B _39733 x'' f g s h1 _39734). Qed.
Lemma lem3638675 {A B : Type'} (x'' : B) (f : A -> B) (_39733 : A) (g : B -> A) (s : B -> Prop) (_39734 : B) : (term1006 A B x'' f _39733 g s _39734) = (term998 A B x'' f _39733 g s _39734).
Proof. exact (eq_refl (term1006 A B x'' f _39733 g s _39734)). Qed.
Lemma lem3638677 {A B : Type'} (_39735 : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term1004 A B t s f g _39735.
Proof. exact (@lem3638607 A B g s f t x'''''' h1 _39735). Qed.
Lemma lem3638678 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (g : B -> A) (_39735 : B) : (term1004 A B t s f g _39735) = (term984 A B t s f g _39735).
Proof. exact (eq_refl (term1004 A B t s f g _39735)). Qed.
Lemma lem3638679 {A B : Type'} (_39735 : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term984 A B t s f g _39735.
Proof. exact (EQ_MP (@lem3638678 A B t s f g _39735) (@lem3638677 A B _39735 g s f t x'''''' h1)). Qed.
Lemma lem3638704 {A B : Type'} (g : B -> A) (s : B -> Prop) (x' : B) (t : A -> Prop) (x : A) (h1 : term629 A B g s x' t x) : term75 A t x.
Proof. exact (proj2 (@lem3638261 A B g s x' t x h1)). Qed.
Lemma lem3638706 {A B : Type'} (g : B -> A) (s : B -> Prop) (x' : B) (t : A -> Prop) (x : A) (h1 : term629 A B g s x' t x) : x = (g x').
Proof. exact (proj1 (@lem3638264 A B g s x' t x h1)). Qed.
Lemma lem3638738 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term684 A B x'' g s x''' f x y) : x = (g x'').
Proof. exact (proj1 (@lem3638272 A B x'' g s x''' f x y h1)). Qed.
Lemma lem3638742 {A B : Type'} (f : A -> B) (x : A) (y : A) (h1 : term982 A B f x y) : (f x) = (f y).
Proof. exact (proj1 (@lem3638277 A B f x y h1)). Qed.
Lemma lem3638744 {A B : Type'} (f : A -> B) (x : A) (y : A) (h1 : term982 A B f x y) : term154 A x y.
Proof. exact (proj2 (@lem3638277 A B f x y h1)). Qed.
Lemma lem3638774 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term684 A B x'' g s x''' f x y) : x = (g x'').
Proof. exact (proj1 (@lem3638272 A B x'' g s x''' f x y h1)). Qed.
Lemma lem3638778 {A B : Type'} (f : A -> B) (x : A) (y : A) (h1 : term983 A B f x y) : term298 A B x f y.
Proof. exact (proj1 (@lem3638278 A B f x y h1)). Qed.
Lemma lem3638780 {A B : Type'} (f : A -> B) (x : A) (y : A) (h1 : term983 A B f x y) : x = y.
Proof. exact (proj2 (@lem3638278 A B f x y h1)). Qed.
Lemma lem3638816 {A B : Type'} (_39733 : A) (_39734 : B) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term575 A B x'' f g s) : term998 A B x'' f _39733 g s _39734.
Proof. exact (EQ_MP (@lem3638675 A B x'' f _39733 g s _39734) (@lem3638674 A B _39733 _39734 x'' f g s h1)). Qed.
Lemma lem3638840 {A B : Type'} (_39731 : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term1007 A B s f g _39731.
Proof. exact (proj2 (@lem3638667 A B _39731 g s f t x'''''' h1)). Qed.
Lemma lem3638844 {A B : Type'} (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term727 A B x'' f x'''' g s x''''') : x'' = (f x'''').
Proof. exact (proj1 (@lem3638287 A B x'' f x'''' g s x''''' h1)). Qed.
Lemma lem3638846 {A B : Type'} (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term727 A B x'' f x'''' g s x''''') : x'''' = (g x''''').
Proof. exact (proj1 (@lem3638289 A B x'' f x'''' g s x''''' h1)). Qed.
Lemma lem3638887 {A : Type'} (t : A -> Prop) : (term1008 A t) = (term1008 A t).
Proof. exact (eq_refl (term1008 A t)). Qed.
Lemma lem3638888 {A B : Type'} (g : B -> A) (s : B -> Prop) (x' : B) (t : A -> Prop) (x : A) (h1 : term629 A B g s x' t x) : (term1009 A t x) = (term1010 A B t g x').
Proof. exact (MK_COMB (@lem3638887 A t) (@lem3638706 A B g s x' t x h1)). Qed.
Lemma lem3638889 {A B : Type'} (t : A -> Prop) (g : B -> A) (x' : B) : (term1010 A B t g x') = (term1011 A B t g x').
Proof. exact (eq_refl (term1010 A B t g x')). Qed.
Lemma lem3638890 {A : Type'} (t : A -> Prop) (x : A) : (term1012 A t x) = (term1012 A t x).
Proof. exact (eq_refl (term1012 A t x)). Qed.
Lemma lem3638891 {A B : Type'} (x : A) (t : A -> Prop) (g : B -> A) (x' : B) : ((term1009 A t x) = (term1010 A B t g x')) = ((term1009 A t x) = (term1011 A B t g x')).
Proof. exact (MK_COMB (@lem3638890 A t x) (@lem3638889 A B t g x')). Qed.
Lemma lem3638892 {A : Type'} (t : A -> Prop) (x : A) : (term1009 A t x) = (term75 A t x).
Proof. exact (eq_refl (term1009 A t x)). Qed.
Lemma lem3638893 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3638894 {A : Type'} (t : A -> Prop) (x : A) : (term1012 A t x) = (term1013 A t x).
Proof. exact (MK_COMB (@lem3638893) (@lem3638892 A t x)). Qed.
Lemma lem3638895 {A B : Type'} (t : A -> Prop) (g : B -> A) (x' : B) : (term1011 A B t g x') = (term1011 A B t g x').
Proof. exact (eq_refl (term1011 A B t g x')). Qed.
Lemma lem3638896 {A B : Type'} (x : A) (t : A -> Prop) (g : B -> A) (x' : B) : ((term1009 A t x) = (term1011 A B t g x')) = ((term75 A t x) = (term1011 A B t g x')).
Proof. exact (MK_COMB (@lem3638894 A t x) (@lem3638895 A B t g x')). Qed.
Lemma lem3638897 {A B : Type'} (x : A) (t : A -> Prop) (g : B -> A) (x' : B) : ((term1009 A t x) = (term1010 A B t g x')) = ((term75 A t x) = (term1011 A B t g x')).
Proof. exact (TRANS (@lem3638891 A B x t g x') (@lem3638896 A B x t g x')). Qed.
Lemma lem3638898 {A B : Type'} (g : B -> A) (s : B -> Prop) (x' : B) (t : A -> Prop) (x : A) (h1 : term629 A B g s x' t x) : (term75 A t x) = (term1011 A B t g x').
Proof. exact (EQ_MP (@lem3638897 A B x t g x') (@lem3638888 A B g s x' t x h1)). Qed.
Lemma lem3638899 {A B : Type'} (g : B -> A) (s : B -> Prop) (x' : B) (t : A -> Prop) (x : A) (h1 : term629 A B g s x' t x) : term1011 A B t g x'.
Proof. exact (EQ_MP (@lem3638898 A B g s x' t x h1) (@lem3638704 A B g s x' t x h1)). Qed.
Lemma lem3638955 {A B : Type'} (_39725 : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term1014 A B s t g _39725.
Proof. exact (proj1 (@lem3638649 A B _39725 g s f t x'''''' h1)). Qed.
Lemma lem3638997 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term684 A B x'' g s x''' f x y) : y = (g x''').
Proof. exact (proj1 (@lem3638271 A B x'' g s x''' f x y h1)). Qed.
Lemma lem3639026 {A B : Type'} (f : A -> B) (y : A) : (term1015 A B f y) = (term1015 A B f y).
Proof. exact (eq_refl (term1015 A B f y)). Qed.
Lemma lem3639027 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term684 A B x'' g s x''' f x y) : (term1016 A B f y x) = (term1017 A B f y g x'').
Proof. exact (MK_COMB (@lem3639026 A B f y) (@lem3638738 A B x'' g s x''' f x y h1)). Qed.
Lemma lem3639028 {A B : Type'} (g : B -> A) (x'' : B) (f : A -> B) (y : A) : (term1017 A B f y g x'') = ((term374 A B f g x'') = (f y)).
Proof. exact (eq_refl (term1017 A B f y g x'')). Qed.
Lemma lem3639029 {A B : Type'} (f : A -> B) (y : A) (x : A) : (term1018 A B f y x) = (term1018 A B f y x).
Proof. exact (eq_refl (term1018 A B f y x)). Qed.
Lemma lem3639030 {A B : Type'} (x : A) (g : B -> A) (x'' : B) (f : A -> B) (y : A) : ((term1016 A B f y x) = (term1017 A B f y g x'')) = ((term1016 A B f y x) = ((term374 A B f g x'') = (f y))).
Proof. exact (MK_COMB (@lem3639029 A B f y x) (@lem3639028 A B g x'' f y)). Qed.
Lemma lem3639031 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term1016 A B f y x) = ((f x) = (f y)).
Proof. exact (eq_refl (term1016 A B f y x)). Qed.
Lemma lem3639032 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3639033 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term1018 A B f y x) = (term1019 A B x f y).
Proof. exact (MK_COMB (@lem3639032) (@lem3639031 A B x f y)). Qed.
Lemma lem3639034 {A B : Type'} (g : B -> A) (x'' : B) (f : A -> B) (y : A) : ((term374 A B f g x'') = (f y)) = ((term374 A B f g x'') = (f y)).
Proof. exact (eq_refl ((term374 A B f g x'') = (f y))). Qed.
Lemma lem3639035 {A B : Type'} (x : A) (g : B -> A) (x'' : B) (f : A -> B) (y : A) : ((term1016 A B f y x) = ((term374 A B f g x'') = (f y))) = (((f x) = (f y)) = ((term374 A B f g x'') = (f y))).
Proof. exact (MK_COMB (@lem3639033 A B x f y) (@lem3639034 A B g x'' f y)). Qed.
Lemma lem3639036 {A B : Type'} (x : A) (g : B -> A) (x'' : B) (f : A -> B) (y : A) : ((term1016 A B f y x) = (term1017 A B f y g x'')) = (((f x) = (f y)) = ((term374 A B f g x'') = (f y))).
Proof. exact (TRANS (@lem3639030 A B x g x'' f y) (@lem3639035 A B x g x'' f y)). Qed.
Lemma lem3639037 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term684 A B x'' g s x''' f x y) : ((f x) = (f y)) = ((term374 A B f g x'') = (f y)).
Proof. exact (EQ_MP (@lem3639036 A B x g x'' f y) (@lem3639027 A B x'' g s x''' f x y h1)). Qed.
Lemma lem3639038 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term684 A B x'' g s x''' f x y) (h2 : term982 A B f x y) : (term374 A B f g x'') = (f y).
Proof. exact (EQ_MP (@lem3639037 A B x'' g s x''' f x y h1) (@lem3638742 A B f x y h2)). Qed.
Lemma lem3639039 {A : Type'} (y : A) : (term1020 A y) = (term1020 A y).
Proof. exact (eq_refl (term1020 A y)). Qed.
Lemma lem3639040 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term684 A B x'' g s x''' f x y) : (term1021 A y x) = (term1022 A B y g x'').
Proof. exact (MK_COMB (@lem3639039 A y) (@lem3638738 A B x'' g s x''' f x y h1)). Qed.
Lemma lem3639041 {A B : Type'} (g : B -> A) (x'' : B) (y : A) : (term1022 A B y g x'') = (term1023 A B g x'' y).
Proof. exact (eq_refl (term1022 A B y g x'')). Qed.
Lemma lem3639042 {A : Type'} (y : A) (x : A) : (term1024 A y x) = (term1024 A y x).
Proof. exact (eq_refl (term1024 A y x)). Qed.
Lemma lem3639043 {A B : Type'} (x : A) (g : B -> A) (x'' : B) (y : A) : ((term1021 A y x) = (term1022 A B y g x'')) = ((term1021 A y x) = (term1023 A B g x'' y)).
Proof. exact (MK_COMB (@lem3639042 A y x) (@lem3639041 A B g x'' y)). Qed.
Lemma lem3639044 {A : Type'} (x : A) (y : A) : (term1021 A y x) = (term154 A x y).
Proof. exact (eq_refl (term1021 A y x)). Qed.
Lemma lem3639045 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3639046 {A : Type'} (x : A) (y : A) : (term1024 A y x) = (term1025 A x y).
Proof. exact (MK_COMB (@lem3639045) (@lem3639044 A x y)). Qed.
Lemma lem3639047 {A B : Type'} (g : B -> A) (x'' : B) (y : A) : (term1023 A B g x'' y) = (term1023 A B g x'' y).
Proof. exact (eq_refl (term1023 A B g x'' y)). Qed.
Lemma lem3639048 {A B : Type'} (x : A) (g : B -> A) (x'' : B) (y : A) : ((term1021 A y x) = (term1023 A B g x'' y)) = ((term154 A x y) = (term1023 A B g x'' y)).
Proof. exact (MK_COMB (@lem3639046 A x y) (@lem3639047 A B g x'' y)). Qed.
Lemma lem3639049 {A B : Type'} (x : A) (g : B -> A) (x'' : B) (y : A) : ((term1021 A y x) = (term1022 A B y g x'')) = ((term154 A x y) = (term1023 A B g x'' y)).
Proof. exact (TRANS (@lem3639043 A B x g x'' y) (@lem3639048 A B x g x'' y)). Qed.
Lemma lem3639050 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term684 A B x'' g s x''' f x y) : (term154 A x y) = (term1023 A B g x'' y).
Proof. exact (EQ_MP (@lem3639049 A B x g x'' y) (@lem3639040 A B x'' g s x''' f x y h1)). Qed.
Lemma lem3639051 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term684 A B x'' g s x''' f x y) (h2 : term982 A B f x y) : term1023 A B g x'' y.
Proof. exact (EQ_MP (@lem3639050 A B x'' g s x''' f x y h1) (@lem3638744 A B f x y h2)). Qed.
Lemma lem3639150 {A B : Type'} (g : B -> A) (x'' : B) (f : A -> B) : (term1026 A B g x'' f) = (term1026 A B g x'' f).
Proof. exact (eq_refl (term1026 A B g x'' f)). Qed.
Lemma lem3639151 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term684 A B x'' g s x''' f x y) : (term1027 A B g x'' f y) = (term1028 A B x'' f g x''').
Proof. exact (MK_COMB (@lem3639150 A B g x'' f) (@lem3638997 A B x'' g s x''' f x y h1)). Qed.
Lemma lem3639152 {A B : Type'} (x'' : B) (f : A -> B) (g : B -> A) (x''' : B) : (term1028 A B x'' f g x''') = ((term374 A B f g x'') = (term374 A B f g x''')).
Proof. exact (eq_refl (term1028 A B x'' f g x''')). Qed.
Lemma lem3639153 {A B : Type'} (g : B -> A) (x'' : B) (f : A -> B) (y : A) : (term1029 A B g x'' f y) = (term1029 A B g x'' f y).
Proof. exact (eq_refl (term1029 A B g x'' f y)). Qed.
Lemma lem3639154 {A B : Type'} (y : A) (x'' : B) (f : A -> B) (g : B -> A) (x''' : B) : ((term1027 A B g x'' f y) = (term1028 A B x'' f g x''')) = ((term1027 A B g x'' f y) = ((term374 A B f g x'') = (term374 A B f g x'''))).
Proof. exact (MK_COMB (@lem3639153 A B g x'' f y) (@lem3639152 A B x'' f g x''')). Qed.
Lemma lem3639155 {A B : Type'} (g : B -> A) (x'' : B) (f : A -> B) (y : A) : (term1027 A B g x'' f y) = ((term374 A B f g x'') = (f y)).
Proof. exact (eq_refl (term1027 A B g x'' f y)). Qed.
Lemma lem3639156 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3639157 {A B : Type'} (g : B -> A) (x'' : B) (f : A -> B) (y : A) : (term1029 A B g x'' f y) = (term1030 A B g x'' f y).
Proof. exact (MK_COMB (@lem3639156) (@lem3639155 A B g x'' f y)). Qed.
Lemma lem3639158 {A B : Type'} (x'' : B) (f : A -> B) (g : B -> A) (x''' : B) : ((term374 A B f g x'') = (term374 A B f g x''')) = ((term374 A B f g x'') = (term374 A B f g x''')).
Proof. exact (eq_refl ((term374 A B f g x'') = (term374 A B f g x'''))). Qed.
Lemma lem3639159 {A B : Type'} (y : A) (x'' : B) (f : A -> B) (g : B -> A) (x''' : B) : ((term1027 A B g x'' f y) = ((term374 A B f g x'') = (term374 A B f g x'''))) = (((term374 A B f g x'') = (f y)) = ((term374 A B f g x'') = (term374 A B f g x'''))).
Proof. exact (MK_COMB (@lem3639157 A B g x'' f y) (@lem3639158 A B x'' f g x''')). Qed.
Lemma lem3639160 {A B : Type'} (y : A) (x'' : B) (f : A -> B) (g : B -> A) (x''' : B) : ((term1027 A B g x'' f y) = (term1028 A B x'' f g x''')) = (((term374 A B f g x'') = (f y)) = ((term374 A B f g x'') = (term374 A B f g x'''))).
Proof. exact (TRANS (@lem3639154 A B y x'' f g x''') (@lem3639159 A B y x'' f g x''')). Qed.
Lemma lem3639161 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term684 A B x'' g s x''' f x y) : ((term374 A B f g x'') = (f y)) = ((term374 A B f g x'') = (term374 A B f g x''')).
Proof. exact (EQ_MP (@lem3639160 A B y x'' f g x''') (@lem3639151 A B x'' g s x''' f x y h1)). Qed.
Lemma lem3639163 {A B : Type'} (g : B -> A) (x'' : B) : (term1031 A B g x'') = (term1031 A B g x'').
Proof. exact (eq_refl (term1031 A B g x'')). Qed.
Lemma lem3639164 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term684 A B x'' g s x''' f x y) : (term1032 A B g x'' y) = (term1033 A B x'' g x''').
Proof. exact (MK_COMB (@lem3639163 A B g x'') (@lem3638997 A B x'' g s x''' f x y h1)). Qed.
Lemma lem3639165 {A B : Type'} (x'' : B) (g : B -> A) (x''' : B) : (term1033 A B x'' g x''') = (term1034 A B x'' g x''').
Proof. exact (eq_refl (term1033 A B x'' g x''')). Qed.
Lemma lem3639166 {A B : Type'} (g : B -> A) (x'' : B) (y : A) : (term1035 A B g x'' y) = (term1035 A B g x'' y).
Proof. exact (eq_refl (term1035 A B g x'' y)). Qed.
Lemma lem3639167 {A B : Type'} (y : A) (x'' : B) (g : B -> A) (x''' : B) : ((term1032 A B g x'' y) = (term1033 A B x'' g x''')) = ((term1032 A B g x'' y) = (term1034 A B x'' g x''')).
Proof. exact (MK_COMB (@lem3639166 A B g x'' y) (@lem3639165 A B x'' g x''')). Qed.
Lemma lem3639168 {A B : Type'} (g : B -> A) (x'' : B) (y : A) : (term1032 A B g x'' y) = (term1023 A B g x'' y).
Proof. exact (eq_refl (term1032 A B g x'' y)). Qed.
Lemma lem3639169 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3639170 {A B : Type'} (g : B -> A) (x'' : B) (y : A) : (term1035 A B g x'' y) = (term1036 A B g x'' y).
Proof. exact (MK_COMB (@lem3639169) (@lem3639168 A B g x'' y)). Qed.
Lemma lem3639171 {A B : Type'} (x'' : B) (g : B -> A) (x''' : B) : (term1034 A B x'' g x''') = (term1034 A B x'' g x''').
Proof. exact (eq_refl (term1034 A B x'' g x''')). Qed.
Lemma lem3639172 {A B : Type'} (y : A) (x'' : B) (g : B -> A) (x''' : B) : ((term1032 A B g x'' y) = (term1034 A B x'' g x''')) = ((term1023 A B g x'' y) = (term1034 A B x'' g x''')).
Proof. exact (MK_COMB (@lem3639170 A B g x'' y) (@lem3639171 A B x'' g x''')). Qed.
Lemma lem3639173 {A B : Type'} (y : A) (x'' : B) (g : B -> A) (x''' : B) : ((term1032 A B g x'' y) = (term1033 A B x'' g x''')) = ((term1023 A B g x'' y) = (term1034 A B x'' g x''')).
Proof. exact (TRANS (@lem3639167 A B y x'' g x''') (@lem3639172 A B y x'' g x''')). Qed.
Lemma lem3639174 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term684 A B x'' g s x''' f x y) : (term1023 A B g x'' y) = (term1034 A B x'' g x''').
Proof. exact (EQ_MP (@lem3639173 A B y x'' g x''') (@lem3639164 A B x'' g s x''' f x y h1)). Qed.
Lemma lem3639175 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term684 A B x'' g s x''' f x y) (h2 : term982 A B f x y) : term1034 A B x'' g x'''.
Proof. exact (EQ_MP (@lem3639174 A B x'' g s x''' f x y h1) (@lem3639051 A B x'' g s x''' f x y h1 h2)). Qed.
Lemma lem3639231 {A B : Type'} (_39727 : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term1007 A B s f g _39727.
Proof. exact (proj2 (@lem3638655 A B _39727 g s f t x'''''' h1)). Qed.
Lemma lem3639274 {A B : Type'} (g : B -> A) (x'' : B) : (term1037 A B g x'') = (term1037 A B g x'').
Proof. exact (eq_refl (term1037 A B g x'')). Qed.
Lemma lem3639275 {A B : Type'} (g : B -> A) (x'' : B) (f : A -> B) (x : A) (y : A) (h1 : term983 A B f x y) : (term1038 A B g x'' x) = (term1038 A B g x'' y).
Proof. exact (MK_COMB (@lem3639274 A B g x'') (@lem3638780 A B f x y h1)). Qed.
Lemma lem3639276 {A B : Type'} (y : A) (g : B -> A) (x'' : B) : (term1038 A B g x'' y) = (y = (g x'')).
Proof. exact (eq_refl (term1038 A B g x'' y)). Qed.
Lemma lem3639277 {A B : Type'} (g : B -> A) (x'' : B) (x : A) : (term1039 A B g x'' x) = (term1039 A B g x'' x).
Proof. exact (eq_refl (term1039 A B g x'' x)). Qed.
Lemma lem3639278 {A B : Type'} (x : A) (y : A) (g : B -> A) (x'' : B) : ((term1038 A B g x'' x) = (term1038 A B g x'' y)) = ((term1038 A B g x'' x) = (y = (g x''))).
Proof. exact (MK_COMB (@lem3639277 A B g x'' x) (@lem3639276 A B y g x'')). Qed.
Lemma lem3639279 {A B : Type'} (x : A) (g : B -> A) (x'' : B) : (term1038 A B g x'' x) = (x = (g x'')).
Proof. exact (eq_refl (term1038 A B g x'' x)). Qed.
Lemma lem3639280 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3639281 {A B : Type'} (x : A) (g : B -> A) (x'' : B) : (term1039 A B g x'' x) = (term1040 A B x g x'').
Proof. exact (MK_COMB (@lem3639280) (@lem3639279 A B x g x'')). Qed.
Lemma lem3639282 {A B : Type'} (y : A) (g : B -> A) (x'' : B) : (y = (g x'')) = (y = (g x'')).
Proof. exact (eq_refl (y = (g x''))). Qed.
Lemma lem3639283 {A B : Type'} (x : A) (y : A) (g : B -> A) (x'' : B) : ((term1038 A B g x'' x) = (y = (g x''))) = ((x = (g x'')) = (y = (g x''))).
Proof. exact (MK_COMB (@lem3639281 A B x g x'') (@lem3639282 A B y g x'')). Qed.
Lemma lem3639284 {A B : Type'} (x : A) (y : A) (g : B -> A) (x'' : B) : ((term1038 A B g x'' x) = (term1038 A B g x'' y)) = ((x = (g x'')) = (y = (g x''))).
Proof. exact (TRANS (@lem3639278 A B x y g x'') (@lem3639283 A B x y g x'')). Qed.
Lemma lem3639285 {A B : Type'} (g : B -> A) (x'' : B) (f : A -> B) (x : A) (y : A) (h1 : term983 A B f x y) : (x = (g x'')) = (y = (g x'')).
Proof. exact (EQ_MP (@lem3639284 A B x y g x'') (@lem3639275 A B g x'' f x y h1)). Qed.
Lemma lem3639286 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term983 A B f x y) (h2 : term684 A B x'' g s x''' f x y) : y = (g x'').
Proof. exact (EQ_MP (@lem3639285 A B g x'' f x y h1) (@lem3638774 A B x'' g s x''' f x y h2)). Qed.
Lemma lem3639301 {A B : Type'} (f : A -> B) (y : A) : (term1041 A B f y) = (term1041 A B f y).
Proof. exact (eq_refl (term1041 A B f y)). Qed.
Lemma lem3639302 {A B : Type'} (f : A -> B) (x : A) (y : A) (h1 : term983 A B f x y) : (term1042 A B f y x) = (term1043 A B f y).
Proof. exact (MK_COMB (@lem3639301 A B f y) (@lem3638780 A B f x y h1)). Qed.
Lemma lem3639303 {A B : Type'} (f : A -> B) (y : A) : (term1043 A B f y) = (term1044 A B f y).
Proof. exact (eq_refl (term1043 A B f y)). Qed.
Lemma lem3639304 {A B : Type'} (f : A -> B) (y : A) (x : A) : (term1045 A B f y x) = (term1045 A B f y x).
Proof. exact (eq_refl (term1045 A B f y x)). Qed.
Lemma lem3639305 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((term1042 A B f y x) = (term1043 A B f y)) = ((term1042 A B f y x) = (term1044 A B f y)).
Proof. exact (MK_COMB (@lem3639304 A B f y x) (@lem3639303 A B f y)). Qed.
Lemma lem3639306 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term1042 A B f y x) = (term298 A B x f y).
Proof. exact (eq_refl (term1042 A B f y x)). Qed.
Lemma lem3639307 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3639308 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term1045 A B f y x) = (term1046 A B x f y).
Proof. exact (MK_COMB (@lem3639307) (@lem3639306 A B x f y)). Qed.
Lemma lem3639309 {A B : Type'} (f : A -> B) (y : A) : (term1044 A B f y) = (term1044 A B f y).
Proof. exact (eq_refl (term1044 A B f y)). Qed.
Lemma lem3639310 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((term1042 A B f y x) = (term1044 A B f y)) = ((term298 A B x f y) = (term1044 A B f y)).
Proof. exact (MK_COMB (@lem3639308 A B x f y) (@lem3639309 A B f y)). Qed.
Lemma lem3639311 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((term1042 A B f y x) = (term1043 A B f y)) = ((term298 A B x f y) = (term1044 A B f y)).
Proof. exact (TRANS (@lem3639305 A B x f y) (@lem3639310 A B x f y)). Qed.
Lemma lem3639312 {A B : Type'} (f : A -> B) (x : A) (y : A) (h1 : term983 A B f x y) : (term298 A B x f y) = (term1044 A B f y).
Proof. exact (EQ_MP (@lem3639311 A B x f y) (@lem3639302 A B f x y h1)). Qed.
Lemma lem3639313 {A B : Type'} (f : A -> B) (x : A) (y : A) (h1 : term983 A B f x y) : term1044 A B f y.
Proof. exact (EQ_MP (@lem3639312 A B f x y h1) (@lem3638778 A B f x y h1)). Qed.
Lemma lem3639425 {A B : Type'} (f : A -> B) : (term1047 A B f) = (term1047 A B f).
Proof. exact (eq_refl (term1047 A B f)). Qed.
Lemma lem3639426 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term983 A B f x y) (h2 : term684 A B x'' g s x''' f x y) : (term1048 A B f y) = (term1049 A B f g x'').
Proof. exact (MK_COMB (@lem3639425 A B f) (@lem3639286 A B x'' g s x''' f x y h1 h2)). Qed.
Lemma lem3639427 {A B : Type'} (f : A -> B) (g : B -> A) (x'' : B) : (term1049 A B f g x'') = (term1050 A B f g x'').
Proof. exact (eq_refl (term1049 A B f g x'')). Qed.
Lemma lem3639428 {A B : Type'} (f : A -> B) (y : A) : (term1051 A B f y) = (term1051 A B f y).
Proof. exact (eq_refl (term1051 A B f y)). Qed.
Lemma lem3639429 {A B : Type'} (y : A) (f : A -> B) (g : B -> A) (x'' : B) : ((term1048 A B f y) = (term1049 A B f g x'')) = ((term1048 A B f y) = (term1050 A B f g x'')).
Proof. exact (MK_COMB (@lem3639428 A B f y) (@lem3639427 A B f g x'')). Qed.
Lemma lem3639430 {A B : Type'} (f : A -> B) (y : A) : (term1048 A B f y) = (term1044 A B f y).
Proof. exact (eq_refl (term1048 A B f y)). Qed.
Lemma lem3639431 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3639432 {A B : Type'} (f : A -> B) (y : A) : (term1051 A B f y) = (term1052 A B f y).
Proof. exact (MK_COMB (@lem3639431) (@lem3639430 A B f y)). Qed.
Lemma lem3639433 {A B : Type'} (f : A -> B) (g : B -> A) (x'' : B) : (term1050 A B f g x'') = (term1050 A B f g x'').
Proof. exact (eq_refl (term1050 A B f g x'')). Qed.
Lemma lem3639434 {A B : Type'} (y : A) (f : A -> B) (g : B -> A) (x'' : B) : ((term1048 A B f y) = (term1050 A B f g x'')) = ((term1044 A B f y) = (term1050 A B f g x'')).
Proof. exact (MK_COMB (@lem3639432 A B f y) (@lem3639433 A B f g x'')). Qed.
Lemma lem3639435 {A B : Type'} (y : A) (f : A -> B) (g : B -> A) (x'' : B) : ((term1048 A B f y) = (term1049 A B f g x'')) = ((term1044 A B f y) = (term1050 A B f g x'')).
Proof. exact (TRANS (@lem3639429 A B y f g x'') (@lem3639434 A B y f g x'')). Qed.
Lemma lem3639436 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term983 A B f x y) (h2 : term684 A B x'' g s x''' f x y) : (term1044 A B f y) = (term1050 A B f g x'').
Proof. exact (EQ_MP (@lem3639435 A B y f g x'') (@lem3639426 A B x'' g s x''' f x y h1 h2)). Qed.
Lemma lem3639437 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term983 A B f x y) (h2 : term684 A B x'' g s x''' f x y) : term1050 A B f g x''.
Proof. exact (EQ_MP (@lem3639436 A B x'' g s x''' f x y h1 h2) (@lem3639313 A B f x y h1)). Qed.
Lemma lem3639521 {A B : Type'} (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term727 A B x'' f x'''' g s x''''') : term75 B s x''.
Proof. exact (proj1 (@lem3638284 A B x'' f x'''' g s x''''' h1)). Qed.
Lemma lem3639522 {A B : Type'} (x'' : B) (f : A -> B) : (term1053 A B x'' f) = (term1053 A B x'' f).
Proof. exact (eq_refl (term1053 A B x'' f)). Qed.
Lemma lem3639523 {A B : Type'} (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term727 A B x'' f x'''' g s x''''') : (term1054 A B x'' f x'''') = (term1055 A B x'' f g x''''').
Proof. exact (MK_COMB (@lem3639522 A B x'' f) (@lem3638846 A B x'' f x'''' g s x''''' h1)). Qed.
Lemma lem3639524 {A B : Type'} (x'' : B) (f : A -> B) (g : B -> A) (x''''' : B) : (term1055 A B x'' f g x''''') = (x'' = (term374 A B f g x''''')).
Proof. exact (eq_refl (term1055 A B x'' f g x''''')). Qed.
Lemma lem3639525 {A B : Type'} (x'' : B) (f : A -> B) (x'''' : A) : (term1056 A B x'' f x'''') = (term1056 A B x'' f x'''').
Proof. exact (eq_refl (term1056 A B x'' f x'''')). Qed.
Lemma lem3639526 {A B : Type'} (x'''' : A) (x'' : B) (f : A -> B) (g : B -> A) (x''''' : B) : ((term1054 A B x'' f x'''') = (term1055 A B x'' f g x''''')) = ((term1054 A B x'' f x'''') = (x'' = (term374 A B f g x'''''))).
Proof. exact (MK_COMB (@lem3639525 A B x'' f x'''') (@lem3639524 A B x'' f g x''''')). Qed.
Lemma lem3639527 {A B : Type'} (x'' : B) (f : A -> B) (x'''' : A) : (term1054 A B x'' f x'''') = (x'' = (f x'''')).
Proof. exact (eq_refl (term1054 A B x'' f x'''')). Qed.
Lemma lem3639528 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3639529 {A B : Type'} (x'' : B) (f : A -> B) (x'''' : A) : (term1056 A B x'' f x'''') = (term1057 A B x'' f x'''').
Proof. exact (MK_COMB (@lem3639528) (@lem3639527 A B x'' f x'''')). Qed.
Lemma lem3639530 {A B : Type'} (x'' : B) (f : A -> B) (g : B -> A) (x''''' : B) : (x'' = (term374 A B f g x''''')) = (x'' = (term374 A B f g x''''')).
Proof. exact (eq_refl (x'' = (term374 A B f g x'''''))). Qed.
Lemma lem3639531 {A B : Type'} (x'''' : A) (x'' : B) (f : A -> B) (g : B -> A) (x''''' : B) : ((term1054 A B x'' f x'''') = (x'' = (term374 A B f g x'''''))) = ((x'' = (f x'''')) = (x'' = (term374 A B f g x'''''))).
Proof. exact (MK_COMB (@lem3639529 A B x'' f x'''') (@lem3639530 A B x'' f g x''''')). Qed.
Lemma lem3639532 {A B : Type'} (x'''' : A) (x'' : B) (f : A -> B) (g : B -> A) (x''''' : B) : ((term1054 A B x'' f x'''') = (term1055 A B x'' f g x''''')) = ((x'' = (f x'''')) = (x'' = (term374 A B f g x'''''))).
Proof. exact (TRANS (@lem3639526 A B x'''' x'' f g x''''') (@lem3639531 A B x'''' x'' f g x''''')). Qed.
Lemma lem3639533 {A B : Type'} (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term727 A B x'' f x'''' g s x''''') : (x'' = (f x'''')) = (x'' = (term374 A B f g x''''')).
Proof. exact (EQ_MP (@lem3639532 A B x'''' x'' f g x''''') (@lem3639523 A B x'' f x'''' g s x''''' h1)). Qed.
Lemma lem3639534 {A B : Type'} (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term727 A B x'' f x'''' g s x''''') : x'' = (term374 A B f g x''''').
Proof. exact (EQ_MP (@lem3639533 A B x'' f x'''' g s x''''' h1) (@lem3638844 A B x'' f x'''' g s x''''' h1)). Qed.
Lemma lem3639619 {B : Type'} (s : B -> Prop) : (term1008 B s) = (term1008 B s).
Proof. exact (eq_refl (term1008 B s)). Qed.
Lemma lem3639620 {A B : Type'} (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term727 A B x'' f x'''' g s x''''') : (term1009 B s x'') = (term1058 A B s f g x''''').
Proof. exact (MK_COMB (@lem3639619 B s) (@lem3639534 A B x'' f x'''' g s x''''' h1)). Qed.
Lemma lem3639621 {A B : Type'} (s : B -> Prop) (f : A -> B) (g : B -> A) (x''''' : B) : (term1058 A B s f g x''''') = (term1059 A B s f g x''''').
Proof. exact (eq_refl (term1058 A B s f g x''''')). Qed.
Lemma lem3639622 {B : Type'} (s : B -> Prop) (x'' : B) : (term1012 B s x'') = (term1012 B s x'').
Proof. exact (eq_refl (term1012 B s x'')). Qed.
Lemma lem3639623 {A B : Type'} (x'' : B) (s : B -> Prop) (f : A -> B) (g : B -> A) (x''''' : B) : ((term1009 B s x'') = (term1058 A B s f g x''''')) = ((term1009 B s x'') = (term1059 A B s f g x''''')).
Proof. exact (MK_COMB (@lem3639622 B s x'') (@lem3639621 A B s f g x''''')). Qed.
Lemma lem3639624 {B : Type'} (s : B -> Prop) (x'' : B) : (term1009 B s x'') = (term75 B s x'').
Proof. exact (eq_refl (term1009 B s x'')). Qed.
Lemma lem3639625 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3639626 {B : Type'} (s : B -> Prop) (x'' : B) : (term1012 B s x'') = (term1013 B s x'').
Proof. exact (MK_COMB (@lem3639625) (@lem3639624 B s x'')). Qed.
Lemma lem3639627 {A B : Type'} (s : B -> Prop) (f : A -> B) (g : B -> A) (x''''' : B) : (term1059 A B s f g x''''') = (term1059 A B s f g x''''').
Proof. exact (eq_refl (term1059 A B s f g x''''')). Qed.
Lemma lem3639628 {A B : Type'} (x'' : B) (s : B -> Prop) (f : A -> B) (g : B -> A) (x''''' : B) : ((term1009 B s x'') = (term1059 A B s f g x''''')) = ((term75 B s x'') = (term1059 A B s f g x''''')).
Proof. exact (MK_COMB (@lem3639626 B s x'') (@lem3639627 A B s f g x''''')). Qed.
Lemma lem3639629 {A B : Type'} (x'' : B) (s : B -> Prop) (f : A -> B) (g : B -> A) (x''''' : B) : ((term1009 B s x'') = (term1058 A B s f g x''''')) = ((term75 B s x'') = (term1059 A B s f g x''''')).
Proof. exact (TRANS (@lem3639623 A B x'' s f g x''''') (@lem3639628 A B x'' s f g x''''')). Qed.
Lemma lem3639630 {A B : Type'} (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term727 A B x'' f x'''' g s x''''') : (term75 B s x'') = (term1059 A B s f g x''''').
Proof. exact (EQ_MP (@lem3639629 A B x'' s f g x''''') (@lem3639620 A B x'' f x'''' g s x''''' h1)). Qed.
Lemma lem3639631 {A B : Type'} (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term727 A B x'' f x'''' g s x''''') : term1059 A B s f g x'''''.
Proof. exact (EQ_MP (@lem3639630 A B x'' f x'''' g s x''''' h1) (@lem3639521 A B x'' f x'''' g s x''''' h1)). Qed.
Lemma lem3639701 {A B : Type'} (_39735 : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term1007 A B s f g _39735.
Proof. exact (proj2 (@lem3638679 A B _39735 g s f t x'''''' h1)). Qed.
Lemma lem3639755 {A B : Type'} (g : B -> A) (s : B -> Prop) (x' : B) (t : A -> Prop) (x : A) (h1 : term629 A B g s x' t x) : s x'.
Proof. exact (proj2 (@lem3638264 A B g s x' t x h1)). Qed.
Lemma lem3639756 {A B : Type'} (g : B -> A) (s : B -> Prop) (x' : B) (t : A -> Prop) (x : A) (h1 : term629 A B g s x' t x) : term131 B s x'.
Proof. exact (fun h0 : term75 B s x' => @lem3639755 A B g s x' t x h1). Qed.
Lemma lem3639758 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3639759 {B : Type'} (s : B -> Prop) (x' : B) : (term131 B s x') = (s x').
Proof. exact (@lem3639758 (s x')). Qed.
Lemma lem3639760 {A B : Type'} (g : B -> A) (s : B -> Prop) (x' : B) (t : A -> Prop) (x : A) (h1 : term629 A B g s x' t x) : s x'.
Proof. exact (EQ_MP (@lem3639759 B s x') (@lem3639756 A B g s x' t x h1)). Qed.
Lemma lem3639766 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3639767 {A B : Type'} (t : A -> Prop) (g : B -> A) (s : B -> Prop) (_39725 : B) : (term1014 A B s t g _39725) = (term1060 A B t g s _39725).
Proof. exact (@lem3639766 (term371 A B t g _39725) (term75 B s _39725)). Qed.
Lemma lem3639773 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3639774 {A B : Type'} (t : A -> Prop) (g : B -> A) (s : B -> Prop) (_39725 : B) : (term1061 A B s t g _39725) = (term1062 A B t g s _39725).
Proof. exact (MK_COMB (@lem3639773) (@lem3639767 A B t g s _39725)). Qed.
Lemma lem3639780 {A B : Type'} (t : A -> Prop) (g : B -> A) (s : B -> Prop) (_39725 : B) : (term1060 A B t g s _39725) = (term1060 A B t g s _39725).
Proof. exact (eq_refl (term1060 A B t g s _39725)). Qed.
Lemma lem3639781 {A B : Type'} (t : A -> Prop) (g : B -> A) (s : B -> Prop) (_39725 : B) : ((term1014 A B s t g _39725) = (term1060 A B t g s _39725)) = ((term1060 A B t g s _39725) = (term1060 A B t g s _39725)).
Proof. exact (MK_COMB (@lem3639774 A B t g s _39725) (@lem3639780 A B t g s _39725)). Qed.
Lemma lem3639783 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3639784 (x : Prop) : (x = x) = True.
Proof. exact (@lem3639783 Prop x). Qed.
Lemma lem3639785 {A B : Type'} (t : A -> Prop) (g : B -> A) (s : B -> Prop) (_39725 : B) : ((term1060 A B t g s _39725) = (term1060 A B t g s _39725)) = True.
Proof. exact (@lem3639784 (term1060 A B t g s _39725)). Qed.
Lemma lem3639786 {A B : Type'} (t : A -> Prop) (g : B -> A) (s : B -> Prop) (_39725 : B) : ((term1014 A B s t g _39725) = (term1060 A B t g s _39725)) = True.
Proof. exact (TRANS (@lem3639781 A B t g s _39725) (@lem3639785 A B t g s _39725)). Qed.
Lemma lem3639787 {A B : Type'} (t : A -> Prop) (g : B -> A) (s : B -> Prop) (_39725 : B) : True = ((term1014 A B s t g _39725) = (term1060 A B t g s _39725)).
Proof. exact (SYM (@lem3639786 A B t g s _39725)). Qed.
Lemma lem3639788 {A B : Type'} (t : A -> Prop) (g : B -> A) (s : B -> Prop) (_39725 : B) : (term1014 A B s t g _39725) = (term1060 A B t g s _39725).
Proof. exact (EQ_MP (@lem3639787 A B t g s _39725) (@lem0)). Qed.
Lemma lem3639789 {A B : Type'} (_39725 : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term1060 A B t g s _39725.
Proof. exact (EQ_MP (@lem3639788 A B t g s _39725) (@lem3638955 A B _39725 g s f t x'''''' h1)). Qed.
Lemma lem3639791 (b : Prop) (a : Prop) : (a \/ b) = (term136 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3639792 {A B : Type'} (s : B -> Prop) (t : A -> Prop) (g : B -> A) (_39725 : B) : (term1060 A B t g s _39725) = (term1063 A B s t g _39725).
Proof. exact (@lem3639791 (term75 B s _39725) (term371 A B t g _39725)). Qed.
Lemma lem3639794 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3639795 {B : Type'} (s : B -> Prop) (_39725 : B) : (term138 B s _39725) = (s _39725).
Proof. exact (@lem3639794 (s _39725)). Qed.
Lemma lem3639796 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3639797 {B : Type'} (s : B -> Prop) (_39725 : B) : (term139 B s _39725) = (term14 B s _39725).
Proof. exact (MK_COMB (@lem3639796) (@lem3639795 B s _39725)). Qed.
Lemma lem3639798 {A B : Type'} (t : A -> Prop) (g : B -> A) (_39725 : B) : (term371 A B t g _39725) = (term371 A B t g _39725).
Proof. exact (eq_refl (term371 A B t g _39725)). Qed.
Lemma lem3639799 {A B : Type'} (s : B -> Prop) (t : A -> Prop) (g : B -> A) (_39725 : B) : (term1063 A B s t g _39725) = (term1064 A B s t g _39725).
Proof. exact (MK_COMB (@lem3639797 B s _39725) (@lem3639798 A B t g _39725)). Qed.
Lemma lem3639800 {A B : Type'} (s : B -> Prop) (t : A -> Prop) (g : B -> A) (_39725 : B) : (term1060 A B t g s _39725) = (term1064 A B s t g _39725).
Proof. exact (TRANS (@lem3639792 A B s t g _39725) (@lem3639799 A B s t g _39725)). Qed.
Lemma lem3639803 {A B : Type'} (_39725 : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term1064 A B s t g _39725.
Proof. exact (EQ_MP (@lem3639800 A B s t g _39725) (@lem3639789 A B _39725 g s f t x'''''' h1)). Qed.
Lemma lem3639804 {A B : Type'} (_39725 : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term1064 A B s t g _39725.
Proof. exact (@lem3639803 A B _39725 g s f t x'''''' h1). Qed.
Lemma lem3639805 {A B : Type'} (x' : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term1064 A B s t g x'.
Proof. exact (@lem3639804 A B x' g s f t x'''''' h1). Qed.
Lemma lem3639808 {A B : Type'} (f : A -> B) (x'''''' : B -> A) (g : B -> A) (s : B -> Prop) (x' : B) (t : A -> Prop) (x : A) (h1 : term518 A B g s f t x'''''') (h2 : term629 A B g s x' t x) : term371 A B t g x'.
Proof. exact (@lem3639805 A B x' g s f t x'''''' h1 (@lem3639760 A B g s x' t x h2)). Qed.
Lemma lem3639809 {A B : Type'} (f : A -> B) (x'''''' : B -> A) (g : B -> A) (s : B -> Prop) (x' : B) (t : A -> Prop) (x : A) (h1 : term518 A B g s f t x'''''') (h2 : term629 A B g s x' t x) : term1065 A B t g x'.
Proof. exact (fun h0 : term1011 A B t g x' => @lem3639808 A B f x'''''' g s x' t x h1 h2). Qed.
Lemma lem3639811 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3639812 {A B : Type'} (t : A -> Prop) (g : B -> A) (x' : B) : (term1065 A B t g x') = (term371 A B t g x').
Proof. exact (@lem3639811 (term371 A B t g x')). Qed.
Lemma lem3639813 {A B : Type'} (f : A -> B) (x'''''' : B -> A) (g : B -> A) (s : B -> Prop) (x' : B) (t : A -> Prop) (x : A) (h1 : term518 A B g s f t x'''''') (h2 : term629 A B g s x' t x) : term371 A B t g x'.
Proof. exact (EQ_MP (@lem3639812 A B t g x') (@lem3639809 A B f x'''''' g s x' t x h1 h2)). Qed.
Lemma lem3639816 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3639818 {A B : Type'} (t : A -> Prop) (g : B -> A) (x' : B) : (term1011 A B t g x') = (term1066 A B t g x').
Proof. exact (@lem3639816 (term371 A B t g x')). Qed.
Lemma lem3639821 {A B : Type'} (g : B -> A) (s : B -> Prop) (x' : B) (t : A -> Prop) (x : A) (h1 : term629 A B g s x' t x) : term1066 A B t g x'.
Proof. exact (EQ_MP (@lem3639818 A B t g x') (@lem3638899 A B g s x' t x h1)). Qed.
Lemma lem3639824 {A B : Type'} (f : A -> B) (x'''''' : B -> A) (g : B -> A) (s : B -> Prop) (x' : B) (t : A -> Prop) (x : A) (h1 : term518 A B g s f t x'''''') (h2 : term629 A B g s x' t x) : False.
Proof. exact (@lem3639821 A B g s x' t x h2 (@lem3639813 A B f x'''''' g s x' t x h1 h2)). Qed.
Lemma lem3639825 {A B : Type'} (f : A -> B) (x'''''' : B -> A) (g : B -> A) (s : B -> Prop) (x' : B) (t : A -> Prop) (x : A) (h1 : term518 A B g s f t x'''''') (h2 : term629 A B g s x' t x) : term183.
Proof. exact (fun h0 : ~ False => @lem3639824 A B f x'''''' g s x' t x h1 h2). Qed.
Lemma lem3639827 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3639828 : term183 = False.
Proof. exact (@lem3639827 False). Qed.
Lemma lem3639862 {A B : Type'} (g : B -> A) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem3639863 {B : Type'} (_39873 : B) (_39874 : B) (h1 : _39873 = _39874) : _39873 = _39874.
Proof. exact (h1). Qed.
Lemma lem3639864 {A B : Type'} (g : B -> A) (_39873 : B) (_39874 : B) (h1 : _39873 = _39874) : (g _39873) = (g _39874).
Proof. exact (MK_COMB (@lem3639862 A B g) (@lem3639863 B _39873 _39874 h1)). Qed.
Lemma lem3639865 {A B : Type'} (_39873 : B) (g : B -> A) (_39874 : B) : term1067 A B _39873 g _39874.
Proof. exact (fun h0 : _39873 = _39874 => @lem3639864 A B g _39873 _39874 h0). Qed.
Lemma lem3639867 (a : Prop) (b : Prop) : (a -> b) = (term1068 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3639868 {A B : Type'} (_39873 : B) (g : B -> A) (_39874 : B) : (term1067 A B _39873 g _39874) = (term1069 A B _39873 g _39874).
Proof. exact (@lem3639867 (_39873 = _39874) ((g _39873) = (g _39874))). Qed.
Lemma lem3639869 {A B : Type'} (_39873 : B) (g : B -> A) (_39874 : B) : term1069 A B _39873 g _39874.
Proof. exact (EQ_MP (@lem3639868 A B _39873 g _39874) (@lem3639865 A B _39873 g _39874)). Qed.
Lemma lem3639879 {B : Type'} (x : B) (y : B) (z : B) : term130 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem3639883 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term684 A B x'' g s x''' f x y) (h2 : term982 A B f x y) : (term374 A B f g x'') = (term374 A B f g x''').
Proof. exact (EQ_MP (@lem3639161 A B x'' g s x''' f x y h1) (@lem3639038 A B x'' g s x''' f x y h1 h2)). Qed.
Lemma lem3639884 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term684 A B x'' g s x''' f x y) (h2 : term982 A B f x y) : term1070 A B x'' f g x'''.
Proof. exact (fun h0 : term1071 A B x'' f g x''' => @lem3639883 A B x'' g s x''' f x y h1 h2). Qed.
Lemma lem3639886 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3639887 {A B : Type'} (x'' : B) (f : A -> B) (g : B -> A) (x''' : B) : (term1070 A B x'' f g x''') = ((term374 A B f g x'') = (term374 A B f g x''')).
Proof. exact (@lem3639886 ((term374 A B f g x'') = (term374 A B f g x'''))). Qed.
Lemma lem3639888 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term684 A B x'' g s x''' f x y) (h2 : term982 A B f x y) : (term374 A B f g x'') = (term374 A B f g x''').
Proof. exact (EQ_MP (@lem3639887 A B x'' f g x''') (@lem3639884 A B x'' g s x''' f x y h1 h2)). Qed.
Lemma lem3639890 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term684 A B x'' g s x''' f x y) : s x''.
Proof. exact (proj2 (@lem3638272 A B x'' g s x''' f x y h1)). Qed.
Lemma lem3639891 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term684 A B x'' g s x''' f x y) : term131 B s x''.
Proof. exact (fun h0 : term75 B s x'' => @lem3639890 A B x'' g s x''' f x y h1). Qed.
Lemma lem3639893 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3639894 {B : Type'} (s : B -> Prop) (x'' : B) : (term131 B s x'') = (s x'').
Proof. exact (@lem3639893 (s x'')). Qed.
Lemma lem3639895 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term684 A B x'' g s x''' f x y) : s x''.
Proof. exact (EQ_MP (@lem3639894 B s x'') (@lem3639891 A B x'' g s x''' f x y h1)). Qed.
Lemma lem3639901 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3639902 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) (_39727 : B) : (term1007 A B s f g _39727) = (term1072 A B f g s _39727).
Proof. exact (@lem3639901 ((term374 A B f g _39727) = _39727) (term75 B s _39727)). Qed.
Lemma lem3639910 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3639911 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) (_39727 : B) : (term1073 A B s f g _39727) = (term1074 A B f g s _39727).
Proof. exact (MK_COMB (@lem3639910) (@lem3639902 A B f g s _39727)). Qed.
Lemma lem3639919 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) (_39727 : B) : (term1072 A B f g s _39727) = (term1072 A B f g s _39727).
Proof. exact (eq_refl (term1072 A B f g s _39727)). Qed.
Lemma lem3639920 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) (_39727 : B) : ((term1007 A B s f g _39727) = (term1072 A B f g s _39727)) = ((term1072 A B f g s _39727) = (term1072 A B f g s _39727)).
Proof. exact (MK_COMB (@lem3639911 A B f g s _39727) (@lem3639919 A B f g s _39727)). Qed.
Lemma lem3639922 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3639923 (x : Prop) : (x = x) = True.
Proof. exact (@lem3639922 Prop x). Qed.
Lemma lem3639924 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) (_39727 : B) : ((term1072 A B f g s _39727) = (term1072 A B f g s _39727)) = True.
Proof. exact (@lem3639923 (term1072 A B f g s _39727)). Qed.
Lemma lem3639925 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) (_39727 : B) : ((term1007 A B s f g _39727) = (term1072 A B f g s _39727)) = True.
Proof. exact (TRANS (@lem3639920 A B f g s _39727) (@lem3639924 A B f g s _39727)). Qed.
Lemma lem3639926 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) (_39727 : B) : True = ((term1007 A B s f g _39727) = (term1072 A B f g s _39727)).
Proof. exact (SYM (@lem3639925 A B f g s _39727)). Qed.
Lemma lem3639927 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) (_39727 : B) : (term1007 A B s f g _39727) = (term1072 A B f g s _39727).
Proof. exact (EQ_MP (@lem3639926 A B f g s _39727) (@lem0)). Qed.
Lemma lem3639928 {A B : Type'} (_39727 : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term1072 A B f g s _39727.
Proof. exact (EQ_MP (@lem3639927 A B f g s _39727) (@lem3639231 A B _39727 g s f t x'''''' h1)). Qed.
Lemma lem3639930 (b : Prop) (a : Prop) : (a \/ b) = (term136 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3639931 {A B : Type'} (s : B -> Prop) (f : A -> B) (g : B -> A) (_39727 : B) : (term1072 A B f g s _39727) = (term1075 A B s f g _39727).
Proof. exact (@lem3639930 (term75 B s _39727) ((term374 A B f g _39727) = _39727)). Qed.
Lemma lem3639933 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3639934 {B : Type'} (s : B -> Prop) (_39727 : B) : (term138 B s _39727) = (s _39727).
Proof. exact (@lem3639933 (s _39727)). Qed.
Lemma lem3639935 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3639936 {B : Type'} (s : B -> Prop) (_39727 : B) : (term139 B s _39727) = (term14 B s _39727).
Proof. exact (MK_COMB (@lem3639935) (@lem3639934 B s _39727)). Qed.
Lemma lem3639937 {A B : Type'} (f : A -> B) (g : B -> A) (_39727 : B) : ((term374 A B f g _39727) = _39727) = ((term374 A B f g _39727) = _39727).
Proof. exact (eq_refl ((term374 A B f g _39727) = _39727)). Qed.
Lemma lem3639938 {A B : Type'} (s : B -> Prop) (f : A -> B) (g : B -> A) (_39727 : B) : (term1075 A B s f g _39727) = (term1076 A B s f g _39727).
Proof. exact (MK_COMB (@lem3639936 B s _39727) (@lem3639937 A B f g _39727)). Qed.
Lemma lem3639939 {A B : Type'} (s : B -> Prop) (f : A -> B) (g : B -> A) (_39727 : B) : (term1072 A B f g s _39727) = (term1076 A B s f g _39727).
Proof. exact (TRANS (@lem3639931 A B s f g _39727) (@lem3639938 A B s f g _39727)). Qed.
Lemma lem3639942 {A B : Type'} (_39727 : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term1076 A B s f g _39727.
Proof. exact (EQ_MP (@lem3639939 A B s f g _39727) (@lem3639928 A B _39727 g s f t x'''''' h1)). Qed.
Lemma lem3639943 {A B : Type'} (_39727 : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term1076 A B s f g _39727.
Proof. exact (@lem3639942 A B _39727 g s f t x'''''' h1). Qed.
Lemma lem3639944 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term1076 A B s f g x''.
Proof. exact (@lem3639943 A B x'' g s f t x'''''' h1). Qed.
Lemma lem3639947 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term518 A B g s f t x'''''') (h2 : term684 A B x'' g s x''' f x y) : (term374 A B f g x'') = x''.
Proof. exact (@lem3639944 A B x'' g s f t x'''''' h1 (@lem3639895 A B x'' g s x''' f x y h2)). Qed.
Lemma lem3639948 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term518 A B g s f t x'''''') (h2 : term684 A B x'' g s x''' f x y) : term1077 A B f g x''.
Proof. exact (fun h0 : term1078 A B f g x'' => @lem3639947 A B t x'''''' x'' g s x''' f x y h1 h2). Qed.
Lemma lem3639950 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3639951 {A B : Type'} (f : A -> B) (g : B -> A) (x'' : B) : (term1077 A B f g x'') = ((term374 A B f g x'') = x'').
Proof. exact (@lem3639950 ((term374 A B f g x'') = x'')). Qed.
Lemma lem3639952 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term518 A B g s f t x'''''') (h2 : term684 A B x'' g s x''' f x y) : (term374 A B f g x'') = x''.
Proof. exact (EQ_MP (@lem3639951 A B f g x'') (@lem3639948 A B t x'''''' x'' g s x''' f x y h1 h2)). Qed.
Lemma lem3639970 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3639971 {B : Type'} (y : B) (x : B) (z : B) : (term152 B x y z) = (term153 B y x z).
Proof. exact (@lem3639970 (y = z) (term154 B x z)). Qed.
Lemma lem3639981 {B : Type'} (x : B) (y : B) : (term155 B x y) = (term155 B x y).
Proof. exact (eq_refl (term155 B x y)). Qed.
Lemma lem3639982 {B : Type'} (y : B) (x : B) (z : B) : (term130 B x y z) = (term156 B y x z).
Proof. exact (MK_COMB (@lem3639981 B x y) (@lem3639971 B y x z)). Qed.
Lemma lem3639986 (q : Prop) (p : Prop) (r : Prop) : (term157 p q r) = (term157 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3639987 {B : Type'} (y : B) (x : B) (z : B) : (term156 B y x z) = (term158 B y x z).
Proof. exact (@lem3639986 (y = z) (term154 B x y) (term154 B x z)). Qed.
Lemma lem3640009 {B : Type'} (y : B) (x : B) (z : B) : (term130 B x y z) = (term158 B y x z).
Proof. exact (TRANS (@lem3639982 B y x z) (@lem3639987 B y x z)). Qed.
Lemma lem3640010 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3640011 {B : Type'} (y : B) (x : B) (z : B) : (term159 B x y z) = (term160 B y x z).
Proof. exact (MK_COMB (@lem3640010) (@lem3640009 B y x z)). Qed.
Lemma lem3640033 {B : Type'} (y : B) (x : B) (z : B) : (term158 B y x z) = (term158 B y x z).
Proof. exact (eq_refl (term158 B y x z)). Qed.
Lemma lem3640034 {B : Type'} (y : B) (x : B) (z : B) : ((term130 B x y z) = (term158 B y x z)) = ((term158 B y x z) = (term158 B y x z)).
Proof. exact (MK_COMB (@lem3640011 B y x z) (@lem3640033 B y x z)). Qed.
Lemma lem3640036 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3640037 (x : Prop) : (x = x) = True.
Proof. exact (@lem3640036 Prop x). Qed.
Lemma lem3640038 {B : Type'} (y : B) (x : B) (z : B) : ((term158 B y x z) = (term158 B y x z)) = True.
Proof. exact (@lem3640037 (term158 B y x z)). Qed.
Lemma lem3640039 {B : Type'} (y : B) (x : B) (z : B) : ((term130 B x y z) = (term158 B y x z)) = True.
Proof. exact (TRANS (@lem3640034 B y x z) (@lem3640038 B y x z)). Qed.
Lemma lem3640040 {B : Type'} (y : B) (x : B) (z : B) : True = ((term130 B x y z) = (term158 B y x z)).
Proof. exact (SYM (@lem3640039 B y x z)). Qed.
Lemma lem3640041 {B : Type'} (y : B) (x : B) (z : B) : (term130 B x y z) = (term158 B y x z).
Proof. exact (EQ_MP (@lem3640040 B y x z) (@lem0)). Qed.
Lemma lem3640042 {B : Type'} (y : B) (x : B) (z : B) : term158 B y x z.
Proof. exact (EQ_MP (@lem3640041 B y x z) (@lem3639879 B x y z)). Qed.
Lemma lem3640044 (b : Prop) (a : Prop) : (a \/ b) = (term136 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3640045 {B : Type'} (x : B) (y : B) (z : B) : (term158 B y x z) = (term161 B x y z).
Proof. exact (@lem3640044 (term162 B y x z) (y = z)). Qed.
Lemma lem3640047 (a : Prop) (b : Prop) : (term163 a b) = (term164 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3640048 {B : Type'} (y : B) (x : B) (z : B) : (term165 B y x z) = (term166 B y x z).
Proof. exact (@lem3640047 (term154 B x y) (term154 B x z)). Qed.
Lemma lem3640050 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3640051 {B : Type'} (x : B) (y : B) : (term167 B x y) = (x = y).
Proof. exact (@lem3640050 (x = y)). Qed.
Lemma lem3640052 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3640053 {B : Type'} (x : B) (y : B) : (term168 B x y) = (term169 B x y).
Proof. exact (MK_COMB (@lem3640052) (@lem3640051 B x y)). Qed.
Lemma lem3640055 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3640056 {B : Type'} (x : B) (z : B) : (term167 B x z) = (x = z).
Proof. exact (@lem3640055 (x = z)). Qed.
Lemma lem3640057 {B : Type'} (y : B) (x : B) (z : B) : (term166 B y x z) = (term170 B y x z).
Proof. exact (MK_COMB (@lem3640053 B x y) (@lem3640056 B x z)). Qed.
Lemma lem3640058 {B : Type'} (y : B) (x : B) (z : B) : (term165 B y x z) = (term170 B y x z).
Proof. exact (TRANS (@lem3640048 B y x z) (@lem3640057 B y x z)). Qed.
Lemma lem3640059 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3640060 {B : Type'} (y : B) (x : B) (z : B) : (term171 B y x z) = (term172 B y x z).
Proof. exact (MK_COMB (@lem3640059) (@lem3640058 B y x z)). Qed.
Lemma lem3640061 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3640062 {B : Type'} (x : B) (y : B) (z : B) : (term161 B x y z) = (term173 B x y z).
Proof. exact (MK_COMB (@lem3640060 B y x z) (@lem3640061 B y z)). Qed.
Lemma lem3640063 {B : Type'} (x : B) (y : B) (z : B) : (term158 B y x z) = (term173 B x y z).
Proof. exact (TRANS (@lem3640045 B x y z) (@lem3640062 B x y z)). Qed.
Lemma lem3640065 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term518 A B g s f t x'''''') (h2 : term684 A B x'' g s x''' f x y) (h3 : term982 A B f x y) : term1079 A B x''' f g x''.
Proof. exact (conj (@lem3639888 A B x'' g s x''' f x y h2 h3) (@lem3639952 A B t x'''''' x'' g s x''' f x y h1 h2)). Qed.
Lemma lem3640067 {B : Type'} (x : B) (y : B) (z : B) : term173 B x y z.
Proof. exact (EQ_MP (@lem3640063 B x y z) (@lem3640042 B y x z)). Qed.
Lemma lem3640068 {B : Type'} (x : B) (y : B) (z : B) : term173 B x y z.
Proof. exact (@lem3640067 B x y z). Qed.
Lemma lem3640069 {A B : Type'} (f : A -> B) (g : B -> A) (x''' : B) (x'' : B) : term1080 A B f g x''' x''.
Proof. exact (@lem3640068 B (term374 A B f g x'') (term374 A B f g x''') x''). Qed.
Lemma lem3640072 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term518 A B g s f t x'''''') (h2 : term684 A B x'' g s x''' f x y) (h3 : term982 A B f x y) : (term374 A B f g x''') = x''.
Proof. exact (@lem3640069 A B f g x''' x'' (@lem3640065 A B t x'''''' x'' g s x''' f x y h1 h2 h3)). Qed.
Lemma lem3640073 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term518 A B g s f t x'''''') (h2 : term684 A B x'' g s x''' f x y) (h3 : term982 A B f x y) : term1081 A B f g x''' x''.
Proof. exact (fun h0 : term1082 A B f g x''' x'' => @lem3640072 A B t x'''''' x'' g s x''' f x y h1 h2 h3). Qed.
Lemma lem3640075 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3640076 {A B : Type'} (f : A -> B) (g : B -> A) (x''' : B) (x'' : B) : (term1081 A B f g x''' x'') = ((term374 A B f g x''') = x'').
Proof. exact (@lem3640075 ((term374 A B f g x''') = x'')). Qed.
Lemma lem3640077 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term518 A B g s f t x'''''') (h2 : term684 A B x'' g s x''' f x y) (h3 : term982 A B f x y) : (term374 A B f g x''') = x''.
Proof. exact (EQ_MP (@lem3640076 A B f g x''' x'') (@lem3640073 A B t x'''''' x'' g s x''' f x y h1 h2 h3)). Qed.
Lemma lem3640079 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term684 A B x'' g s x''' f x y) : s x'''.
Proof. exact (proj2 (@lem3638271 A B x'' g s x''' f x y h1)). Qed.
Lemma lem3640080 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term684 A B x'' g s x''' f x y) : term131 B s x'''.
Proof. exact (fun h0 : term75 B s x''' => @lem3640079 A B x'' g s x''' f x y h1). Qed.
Lemma lem3640082 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3640083 {B : Type'} (s : B -> Prop) (x''' : B) : (term131 B s x''') = (s x''').
Proof. exact (@lem3640082 (s x''')). Qed.
Lemma lem3640084 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term684 A B x'' g s x''' f x y) : s x'''.
Proof. exact (EQ_MP (@lem3640083 B s x''') (@lem3640080 A B x'' g s x''' f x y h1)). Qed.
Lemma lem3640086 {A B : Type'} (_39727 : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term1076 A B s f g _39727.
Proof. exact (EQ_MP (@lem3639939 A B s f g _39727) (@lem3639928 A B _39727 g s f t x'''''' h1)). Qed.
Lemma lem3640087 {A B : Type'} (_39727 : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term1076 A B s f g _39727.
Proof. exact (@lem3640086 A B _39727 g s f t x'''''' h1). Qed.
Lemma lem3640088 {A B : Type'} (x''' : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term1076 A B s f g x'''.
Proof. exact (@lem3640087 A B x''' g s f t x'''''' h1). Qed.
Lemma lem3640091 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term518 A B g s f t x'''''') (h2 : term684 A B x'' g s x''' f x y) : (term374 A B f g x''') = x'''.
Proof. exact (@lem3640088 A B x''' g s f t x'''''' h1 (@lem3640084 A B x'' g s x''' f x y h2)). Qed.
Lemma lem3640092 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term518 A B g s f t x'''''') (h2 : term684 A B x'' g s x''' f x y) : term1077 A B f g x'''.
Proof. exact (fun h0 : term1078 A B f g x''' => @lem3640091 A B t x'''''' x'' g s x''' f x y h1 h2). Qed.
Lemma lem3640094 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3640095 {A B : Type'} (f : A -> B) (g : B -> A) (x''' : B) : (term1077 A B f g x''') = ((term374 A B f g x''') = x''').
Proof. exact (@lem3640094 ((term374 A B f g x''') = x''')). Qed.
Lemma lem3640096 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term518 A B g s f t x'''''') (h2 : term684 A B x'' g s x''' f x y) : (term374 A B f g x''') = x'''.
Proof. exact (EQ_MP (@lem3640095 A B f g x''') (@lem3640092 A B t x'''''' x'' g s x''' f x y h1 h2)). Qed.
Lemma lem3640097 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term518 A B g s f t x'''''') (h2 : term684 A B x'' g s x''' f x y) (h3 : term982 A B f x y) : term1083 A B x'' f g x'''.
Proof. exact (conj (@lem3640077 A B t x'''''' x'' g s x''' f x y h1 h2 h3) (@lem3640096 A B t x'''''' x'' g s x''' f x y h1 h2)). Qed.
Lemma lem3640099 {B : Type'} (x : B) (y : B) (z : B) : term173 B x y z.
Proof. exact (EQ_MP (@lem3640063 B x y z) (@lem3640042 B y x z)). Qed.
Lemma lem3640100 {B : Type'} (x : B) (y : B) (z : B) : term173 B x y z.
Proof. exact (@lem3640099 B x y z). Qed.
Lemma lem3640101 {A B : Type'} (f : A -> B) (g : B -> A) (x'' : B) (x''' : B) : term1084 A B f g x'' x'''.
Proof. exact (@lem3640100 B (term374 A B f g x''') x'' x'''). Qed.
Lemma lem3640104 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term518 A B g s f t x'''''') (h2 : term684 A B x'' g s x''' f x y) (h3 : term982 A B f x y) : x'' = x'''.
Proof. exact (@lem3640101 A B f g x'' x''' (@lem3640097 A B t x'''''' x'' g s x''' f x y h1 h2 h3)). Qed.
Lemma lem3640105 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term518 A B g s f t x'''''') (h2 : term684 A B x'' g s x''' f x y) (h3 : term982 A B f x y) : term1085 B x'' x'''.
Proof. exact (fun h0 : term154 B x'' x''' => @lem3640104 A B t x'''''' x'' g s x''' f x y h1 h2 h3). Qed.
Lemma lem3640107 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3640108 {B : Type'} (x'' : B) (x''' : B) : (term1085 B x'' x''') = (x'' = x''').
Proof. exact (@lem3640107 (x'' = x''')). Qed.
Lemma lem3640109 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term518 A B g s f t x'''''') (h2 : term684 A B x'' g s x''' f x y) (h3 : term982 A B f x y) : x'' = x'''.
Proof. exact (EQ_MP (@lem3640108 B x'' x''') (@lem3640105 A B t x'''''' x'' g s x''' f x y h1 h2 h3)). Qed.
Lemma lem3640115 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3640116 {A B : Type'} (g : B -> A) (_39873 : B) (_39874 : B) : (term1069 A B _39873 g _39874) = (term1086 A B g _39873 _39874).
Proof. exact (@lem3640115 ((g _39873) = (g _39874)) (term154 B _39873 _39874)). Qed.
Lemma lem3640126 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3640127 {A B : Type'} (g : B -> A) (_39873 : B) (_39874 : B) : (term1087 A B _39873 g _39874) = (term1088 A B g _39873 _39874).
Proof. exact (MK_COMB (@lem3640126) (@lem3640116 A B g _39873 _39874)). Qed.
Lemma lem3640137 {A B : Type'} (g : B -> A) (_39873 : B) (_39874 : B) : (term1086 A B g _39873 _39874) = (term1086 A B g _39873 _39874).
Proof. exact (eq_refl (term1086 A B g _39873 _39874)). Qed.
Lemma lem3640138 {A B : Type'} (g : B -> A) (_39873 : B) (_39874 : B) : ((term1069 A B _39873 g _39874) = (term1086 A B g _39873 _39874)) = ((term1086 A B g _39873 _39874) = (term1086 A B g _39873 _39874)).
Proof. exact (MK_COMB (@lem3640127 A B g _39873 _39874) (@lem3640137 A B g _39873 _39874)). Qed.
Lemma lem3640140 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3640141 (x : Prop) : (x = x) = True.
Proof. exact (@lem3640140 Prop x). Qed.
Lemma lem3640142 {A B : Type'} (g : B -> A) (_39873 : B) (_39874 : B) : ((term1086 A B g _39873 _39874) = (term1086 A B g _39873 _39874)) = True.
Proof. exact (@lem3640141 (term1086 A B g _39873 _39874)). Qed.
Lemma lem3640143 {A B : Type'} (g : B -> A) (_39873 : B) (_39874 : B) : ((term1069 A B _39873 g _39874) = (term1086 A B g _39873 _39874)) = True.
Proof. exact (TRANS (@lem3640138 A B g _39873 _39874) (@lem3640142 A B g _39873 _39874)). Qed.
Lemma lem3640144 {A B : Type'} (g : B -> A) (_39873 : B) (_39874 : B) : True = ((term1069 A B _39873 g _39874) = (term1086 A B g _39873 _39874)).
Proof. exact (SYM (@lem3640143 A B g _39873 _39874)). Qed.
Lemma lem3640145 {A B : Type'} (g : B -> A) (_39873 : B) (_39874 : B) : (term1069 A B _39873 g _39874) = (term1086 A B g _39873 _39874).
Proof. exact (EQ_MP (@lem3640144 A B g _39873 _39874) (@lem0)). Qed.
Lemma lem3640146 {A B : Type'} (g : B -> A) (_39873 : B) (_39874 : B) : term1086 A B g _39873 _39874.
Proof. exact (EQ_MP (@lem3640145 A B g _39873 _39874) (@lem3639869 A B _39873 g _39874)). Qed.
Lemma lem3640148 (b : Prop) (a : Prop) : (a \/ b) = (term136 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3640149 {A B : Type'} (_39873 : B) (g : B -> A) (_39874 : B) : (term1086 A B g _39873 _39874) = (term1089 A B _39873 g _39874).
Proof. exact (@lem3640148 (term154 B _39873 _39874) ((g _39873) = (g _39874))). Qed.
Lemma lem3640151 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3640152 {B : Type'} (_39873 : B) (_39874 : B) : (term167 B _39873 _39874) = (_39873 = _39874).
Proof. exact (@lem3640151 (_39873 = _39874)). Qed.
Lemma lem3640153 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3640154 {B : Type'} (_39873 : B) (_39874 : B) : (term1090 B _39873 _39874) = (term1091 B _39873 _39874).
Proof. exact (MK_COMB (@lem3640153) (@lem3640152 B _39873 _39874)). Qed.
Lemma lem3640155 {A B : Type'} (_39873 : B) (g : B -> A) (_39874 : B) : ((g _39873) = (g _39874)) = ((g _39873) = (g _39874)).
Proof. exact (eq_refl ((g _39873) = (g _39874))). Qed.
Lemma lem3640156 {A B : Type'} (_39873 : B) (g : B -> A) (_39874 : B) : (term1089 A B _39873 g _39874) = (term1067 A B _39873 g _39874).
Proof. exact (MK_COMB (@lem3640154 B _39873 _39874) (@lem3640155 A B _39873 g _39874)). Qed.
Lemma lem3640157 {A B : Type'} (_39873 : B) (g : B -> A) (_39874 : B) : (term1086 A B g _39873 _39874) = (term1067 A B _39873 g _39874).
Proof. exact (TRANS (@lem3640149 A B _39873 g _39874) (@lem3640156 A B _39873 g _39874)). Qed.
Lemma lem3640160 {A B : Type'} (_39873 : B) (g : B -> A) (_39874 : B) : term1067 A B _39873 g _39874.
Proof. exact (EQ_MP (@lem3640157 A B _39873 g _39874) (@lem3640146 A B g _39873 _39874)). Qed.
Lemma lem3640161 {A B : Type'} (_39873 : B) (g : B -> A) (_39874 : B) : term1067 A B _39873 g _39874.
Proof. exact (@lem3640160 A B _39873 g _39874). Qed.
Lemma lem3640162 {A B : Type'} (x'' : B) (g : B -> A) (x''' : B) : term1067 A B x'' g x'''.
Proof. exact (@lem3640161 A B x'' g x'''). Qed.
Lemma lem3640165 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term518 A B g s f t x'''''') (h2 : term684 A B x'' g s x''' f x y) (h3 : term982 A B f x y) : (g x'') = (g x''').
Proof. exact (@lem3640162 A B x'' g x''' (@lem3640109 A B t x'''''' x'' g s x''' f x y h1 h2 h3)). Qed.
Lemma lem3640166 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term518 A B g s f t x'''''') (h2 : term684 A B x'' g s x''' f x y) (h3 : term982 A B f x y) : term1092 A B x'' g x'''.
Proof. exact (fun h0 : term1034 A B x'' g x''' => @lem3640165 A B t x'''''' x'' g s x''' f x y h1 h2 h3). Qed.
Lemma lem3640168 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3640169 {A B : Type'} (x'' : B) (g : B -> A) (x''' : B) : (term1092 A B x'' g x''') = ((g x'') = (g x''')).
Proof. exact (@lem3640168 ((g x'') = (g x'''))). Qed.
Lemma lem3640170 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term518 A B g s f t x'''''') (h2 : term684 A B x'' g s x''' f x y) (h3 : term982 A B f x y) : (g x'') = (g x''').
Proof. exact (EQ_MP (@lem3640169 A B x'' g x''') (@lem3640166 A B t x'''''' x'' g s x''' f x y h1 h2 h3)). Qed.
Lemma lem3640173 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3640175 {A B : Type'} (x'' : B) (g : B -> A) (x''' : B) : (term1034 A B x'' g x''') = (term1093 A B x'' g x''').
Proof. exact (@lem3640173 ((g x'') = (g x'''))). Qed.
Lemma lem3640178 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term684 A B x'' g s x''' f x y) (h2 : term982 A B f x y) : term1093 A B x'' g x'''.
Proof. exact (EQ_MP (@lem3640175 A B x'' g x''') (@lem3639175 A B x'' g s x''' f x y h1 h2)). Qed.
Lemma lem3640181 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term518 A B g s f t x'''''') (h2 : term684 A B x'' g s x''' f x y) (h3 : term982 A B f x y) : False.
Proof. exact (@lem3640178 A B x'' g s x''' f x y h2 h3 (@lem3640170 A B t x'''''' x'' g s x''' f x y h1 h2 h3)). Qed.
Lemma lem3640182 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term518 A B g s f t x'''''') (h2 : term684 A B x'' g s x''' f x y) (h3 : term982 A B f x y) : term183.
Proof. exact (fun h0 : ~ False => @lem3640181 A B t x'''''' x'' g s x''' f x y h1 h2 h3). Qed.
Lemma lem3640184 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3640185 : term183 = False.
Proof. exact (@lem3640184 False). Qed.
Lemma lem3640240 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3640241 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3640240 B x). Qed.
Lemma lem3640242 {A B : Type'} (f : A -> B) (g : B -> A) (x'' : B) : (term374 A B f g x'') = (term374 A B f g x'').
Proof. exact (@lem3640241 B (term374 A B f g x'')). Qed.
Lemma lem3640243 {A B : Type'} (f : A -> B) (g : B -> A) (x'' : B) : term1094 A B f g x''.
Proof. exact (fun h0 : term1050 A B f g x'' => @lem3640242 A B f g x''). Qed.
Lemma lem3640245 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3640246 {A B : Type'} (f : A -> B) (g : B -> A) (x'' : B) : (term1094 A B f g x'') = ((term374 A B f g x'') = (term374 A B f g x'')).
Proof. exact (@lem3640245 ((term374 A B f g x'') = (term374 A B f g x''))). Qed.
Lemma lem3640247 {A B : Type'} (f : A -> B) (g : B -> A) (x'' : B) : (term374 A B f g x'') = (term374 A B f g x'').
Proof. exact (EQ_MP (@lem3640246 A B f g x'') (@lem3640243 A B f g x'')). Qed.
Lemma lem3640250 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3640252 {A B : Type'} (f : A -> B) (g : B -> A) (x'' : B) : (term1050 A B f g x'') = (term1095 A B f g x'').
Proof. exact (@lem3640250 ((term374 A B f g x'') = (term374 A B f g x''))). Qed.
Lemma lem3640255 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term983 A B f x y) (h2 : term684 A B x'' g s x''' f x y) : term1095 A B f g x''.
Proof. exact (EQ_MP (@lem3640252 A B f g x'') (@lem3639437 A B x'' g s x''' f x y h1 h2)). Qed.
Lemma lem3640258 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term983 A B f x y) (h2 : term684 A B x'' g s x''' f x y) : False.
Proof. exact (@lem3640255 A B x'' g s x''' f x y h1 h2 (@lem3640247 A B f g x'')). Qed.
Lemma lem3640259 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term983 A B f x y) (h2 : term684 A B x'' g s x''' f x y) : term183.
Proof. exact (fun h0 : ~ False => @lem3640258 A B x'' g s x''' f x y h1 h2). Qed.
Lemma lem3640261 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3640262 : term183 = False.
Proof. exact (@lem3640261 False). Qed.
Lemma lem3640315 {B : Type'} (x : B) (y : B) (z : B) : term130 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem3640317 {A B : Type'} (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term575 A B x'' f g s) : s x''.
Proof. exact (proj1 (@lem3638283 A B x'' f g s h1)). Qed.
Lemma lem3640318 {A B : Type'} (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term575 A B x'' f g s) : term131 B s x''.
Proof. exact (fun h0 : term75 B s x'' => @lem3640317 A B x'' f g s h1). Qed.
Lemma lem3640320 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3640321 {B : Type'} (s : B -> Prop) (x'' : B) : (term131 B s x'') = (s x'').
Proof. exact (@lem3640320 (s x'')). Qed.
Lemma lem3640322 {A B : Type'} (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term575 A B x'' f g s) : s x''.
Proof. exact (EQ_MP (@lem3640321 B s x'') (@lem3640318 A B x'' f g s h1)). Qed.
Lemma lem3640328 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3640329 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) (_39731 : B) : (term1007 A B s f g _39731) = (term1072 A B f g s _39731).
Proof. exact (@lem3640328 ((term374 A B f g _39731) = _39731) (term75 B s _39731)). Qed.
Lemma lem3640337 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3640338 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) (_39731 : B) : (term1073 A B s f g _39731) = (term1074 A B f g s _39731).
Proof. exact (MK_COMB (@lem3640337) (@lem3640329 A B f g s _39731)). Qed.
Lemma lem3640346 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) (_39731 : B) : (term1072 A B f g s _39731) = (term1072 A B f g s _39731).
Proof. exact (eq_refl (term1072 A B f g s _39731)). Qed.
Lemma lem3640347 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) (_39731 : B) : ((term1007 A B s f g _39731) = (term1072 A B f g s _39731)) = ((term1072 A B f g s _39731) = (term1072 A B f g s _39731)).
Proof. exact (MK_COMB (@lem3640338 A B f g s _39731) (@lem3640346 A B f g s _39731)). Qed.
Lemma lem3640349 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3640350 (x : Prop) : (x = x) = True.
Proof. exact (@lem3640349 Prop x). Qed.
Lemma lem3640351 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) (_39731 : B) : ((term1072 A B f g s _39731) = (term1072 A B f g s _39731)) = True.
Proof. exact (@lem3640350 (term1072 A B f g s _39731)). Qed.
Lemma lem3640352 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) (_39731 : B) : ((term1007 A B s f g _39731) = (term1072 A B f g s _39731)) = True.
Proof. exact (TRANS (@lem3640347 A B f g s _39731) (@lem3640351 A B f g s _39731)). Qed.
Lemma lem3640353 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) (_39731 : B) : True = ((term1007 A B s f g _39731) = (term1072 A B f g s _39731)).
Proof. exact (SYM (@lem3640352 A B f g s _39731)). Qed.
Lemma lem3640354 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) (_39731 : B) : (term1007 A B s f g _39731) = (term1072 A B f g s _39731).
Proof. exact (EQ_MP (@lem3640353 A B f g s _39731) (@lem0)). Qed.
Lemma lem3640355 {A B : Type'} (_39731 : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term1072 A B f g s _39731.
Proof. exact (EQ_MP (@lem3640354 A B f g s _39731) (@lem3638840 A B _39731 g s f t x'''''' h1)). Qed.
Lemma lem3640357 (b : Prop) (a : Prop) : (a \/ b) = (term136 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3640358 {A B : Type'} (s : B -> Prop) (f : A -> B) (g : B -> A) (_39731 : B) : (term1072 A B f g s _39731) = (term1075 A B s f g _39731).
Proof. exact (@lem3640357 (term75 B s _39731) ((term374 A B f g _39731) = _39731)). Qed.
Lemma lem3640360 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3640361 {B : Type'} (s : B -> Prop) (_39731 : B) : (term138 B s _39731) = (s _39731).
Proof. exact (@lem3640360 (s _39731)). Qed.
Lemma lem3640362 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3640363 {B : Type'} (s : B -> Prop) (_39731 : B) : (term139 B s _39731) = (term14 B s _39731).
Proof. exact (MK_COMB (@lem3640362) (@lem3640361 B s _39731)). Qed.
Lemma lem3640364 {A B : Type'} (f : A -> B) (g : B -> A) (_39731 : B) : ((term374 A B f g _39731) = _39731) = ((term374 A B f g _39731) = _39731).
Proof. exact (eq_refl ((term374 A B f g _39731) = _39731)). Qed.
Lemma lem3640365 {A B : Type'} (s : B -> Prop) (f : A -> B) (g : B -> A) (_39731 : B) : (term1075 A B s f g _39731) = (term1076 A B s f g _39731).
Proof. exact (MK_COMB (@lem3640363 B s _39731) (@lem3640364 A B f g _39731)). Qed.
Lemma lem3640366 {A B : Type'} (s : B -> Prop) (f : A -> B) (g : B -> A) (_39731 : B) : (term1072 A B f g s _39731) = (term1076 A B s f g _39731).
Proof. exact (TRANS (@lem3640358 A B s f g _39731) (@lem3640365 A B s f g _39731)). Qed.
Lemma lem3640369 {A B : Type'} (_39731 : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term1076 A B s f g _39731.
Proof. exact (EQ_MP (@lem3640366 A B s f g _39731) (@lem3640355 A B _39731 g s f t x'''''' h1)). Qed.
Lemma lem3640370 {A B : Type'} (_39731 : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term1076 A B s f g _39731.
Proof. exact (@lem3640369 A B _39731 g s f t x'''''' h1). Qed.
Lemma lem3640371 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term1076 A B s f g x''.
Proof. exact (@lem3640370 A B x'' g s f t x'''''' h1). Qed.
Lemma lem3640374 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term518 A B g s f t x'''''') (h2 : term575 A B x'' f g s) : (term374 A B f g x'') = x''.
Proof. exact (@lem3640371 A B x'' g s f t x'''''' h1 (@lem3640322 A B x'' f g s h2)). Qed.
Lemma lem3640375 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term518 A B g s f t x'''''') (h2 : term575 A B x'' f g s) : term1077 A B f g x''.
Proof. exact (fun h0 : term1078 A B f g x'' => @lem3640374 A B t x'''''' x'' f g s h1 h2). Qed.
Lemma lem3640377 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3640378 {A B : Type'} (f : A -> B) (g : B -> A) (x'' : B) : (term1077 A B f g x'') = ((term374 A B f g x'') = x'').
Proof. exact (@lem3640377 ((term374 A B f g x'') = x'')). Qed.
Lemma lem3640379 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term518 A B g s f t x'''''') (h2 : term575 A B x'' f g s) : (term374 A B f g x'') = x''.
Proof. exact (EQ_MP (@lem3640378 A B f g x'') (@lem3640375 A B t x'''''' x'' f g s h1 h2)). Qed.
Lemma lem3640381 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3640382 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3640381 B x). Qed.
Lemma lem3640383 {A B : Type'} (f : A -> B) (g : B -> A) (x'' : B) : (term374 A B f g x'') = (term374 A B f g x'').
Proof. exact (@lem3640382 B (term374 A B f g x'')). Qed.
Lemma lem3640384 {A B : Type'} (f : A -> B) (g : B -> A) (x'' : B) : term1094 A B f g x''.
Proof. exact (fun h0 : term1050 A B f g x'' => @lem3640383 A B f g x''). Qed.
Lemma lem3640386 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3640387 {A B : Type'} (f : A -> B) (g : B -> A) (x'' : B) : (term1094 A B f g x'') = ((term374 A B f g x'') = (term374 A B f g x'')).
Proof. exact (@lem3640386 ((term374 A B f g x'') = (term374 A B f g x''))). Qed.
Lemma lem3640388 {A B : Type'} (f : A -> B) (g : B -> A) (x'' : B) : (term374 A B f g x'') = (term374 A B f g x'').
Proof. exact (EQ_MP (@lem3640387 A B f g x'') (@lem3640384 A B f g x'')). Qed.
Lemma lem3640406 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3640407 {B : Type'} (y : B) (x : B) (z : B) : (term152 B x y z) = (term153 B y x z).
Proof. exact (@lem3640406 (y = z) (term154 B x z)). Qed.
Lemma lem3640417 {B : Type'} (x : B) (y : B) : (term155 B x y) = (term155 B x y).
Proof. exact (eq_refl (term155 B x y)). Qed.
Lemma lem3640418 {B : Type'} (y : B) (x : B) (z : B) : (term130 B x y z) = (term156 B y x z).
Proof. exact (MK_COMB (@lem3640417 B x y) (@lem3640407 B y x z)). Qed.
Lemma lem3640422 (q : Prop) (p : Prop) (r : Prop) : (term157 p q r) = (term157 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3640423 {B : Type'} (y : B) (x : B) (z : B) : (term156 B y x z) = (term158 B y x z).
Proof. exact (@lem3640422 (y = z) (term154 B x y) (term154 B x z)). Qed.
Lemma lem3640445 {B : Type'} (y : B) (x : B) (z : B) : (term130 B x y z) = (term158 B y x z).
Proof. exact (TRANS (@lem3640418 B y x z) (@lem3640423 B y x z)). Qed.
Lemma lem3640446 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3640447 {B : Type'} (y : B) (x : B) (z : B) : (term159 B x y z) = (term160 B y x z).
Proof. exact (MK_COMB (@lem3640446) (@lem3640445 B y x z)). Qed.
Lemma lem3640469 {B : Type'} (y : B) (x : B) (z : B) : (term158 B y x z) = (term158 B y x z).
Proof. exact (eq_refl (term158 B y x z)). Qed.
Lemma lem3640470 {B : Type'} (y : B) (x : B) (z : B) : ((term130 B x y z) = (term158 B y x z)) = ((term158 B y x z) = (term158 B y x z)).
Proof. exact (MK_COMB (@lem3640447 B y x z) (@lem3640469 B y x z)). Qed.
Lemma lem3640472 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3640473 (x : Prop) : (x = x) = True.
Proof. exact (@lem3640472 Prop x). Qed.
Lemma lem3640474 {B : Type'} (y : B) (x : B) (z : B) : ((term158 B y x z) = (term158 B y x z)) = True.
Proof. exact (@lem3640473 (term158 B y x z)). Qed.
Lemma lem3640475 {B : Type'} (y : B) (x : B) (z : B) : ((term130 B x y z) = (term158 B y x z)) = True.
Proof. exact (TRANS (@lem3640470 B y x z) (@lem3640474 B y x z)). Qed.
Lemma lem3640476 {B : Type'} (y : B) (x : B) (z : B) : True = ((term130 B x y z) = (term158 B y x z)).
Proof. exact (SYM (@lem3640475 B y x z)). Qed.
Lemma lem3640477 {B : Type'} (y : B) (x : B) (z : B) : (term130 B x y z) = (term158 B y x z).
Proof. exact (EQ_MP (@lem3640476 B y x z) (@lem0)). Qed.
Lemma lem3640478 {B : Type'} (y : B) (x : B) (z : B) : term158 B y x z.
Proof. exact (EQ_MP (@lem3640477 B y x z) (@lem3640315 B x y z)). Qed.
Lemma lem3640480 (b : Prop) (a : Prop) : (a \/ b) = (term136 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3640481 {B : Type'} (x : B) (y : B) (z : B) : (term158 B y x z) = (term161 B x y z).
Proof. exact (@lem3640480 (term162 B y x z) (y = z)). Qed.
Lemma lem3640483 (a : Prop) (b : Prop) : (term163 a b) = (term164 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3640484 {B : Type'} (y : B) (x : B) (z : B) : (term165 B y x z) = (term166 B y x z).
Proof. exact (@lem3640483 (term154 B x y) (term154 B x z)). Qed.
Lemma lem3640486 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3640487 {B : Type'} (x : B) (y : B) : (term167 B x y) = (x = y).
Proof. exact (@lem3640486 (x = y)). Qed.
Lemma lem3640488 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3640489 {B : Type'} (x : B) (y : B) : (term168 B x y) = (term169 B x y).
Proof. exact (MK_COMB (@lem3640488) (@lem3640487 B x y)). Qed.
Lemma lem3640491 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3640492 {B : Type'} (x : B) (z : B) : (term167 B x z) = (x = z).
Proof. exact (@lem3640491 (x = z)). Qed.
Lemma lem3640493 {B : Type'} (y : B) (x : B) (z : B) : (term166 B y x z) = (term170 B y x z).
Proof. exact (MK_COMB (@lem3640489 B x y) (@lem3640492 B x z)). Qed.
Lemma lem3640494 {B : Type'} (y : B) (x : B) (z : B) : (term165 B y x z) = (term170 B y x z).
Proof. exact (TRANS (@lem3640484 B y x z) (@lem3640493 B y x z)). Qed.
Lemma lem3640495 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3640496 {B : Type'} (y : B) (x : B) (z : B) : (term171 B y x z) = (term172 B y x z).
Proof. exact (MK_COMB (@lem3640495) (@lem3640494 B y x z)). Qed.
Lemma lem3640497 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3640498 {B : Type'} (x : B) (y : B) (z : B) : (term161 B x y z) = (term173 B x y z).
Proof. exact (MK_COMB (@lem3640496 B y x z) (@lem3640497 B y z)). Qed.
Lemma lem3640499 {B : Type'} (x : B) (y : B) (z : B) : (term158 B y x z) = (term173 B x y z).
Proof. exact (TRANS (@lem3640481 B x y z) (@lem3640498 B x y z)). Qed.
Lemma lem3640501 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term518 A B g s f t x'''''') (h2 : term575 A B x'' f g s) : term1096 A B f g x''.
Proof. exact (conj (@lem3640379 A B t x'''''' x'' f g s h1 h2) (@lem3640388 A B f g x'')). Qed.
Lemma lem3640503 {B : Type'} (x : B) (y : B) (z : B) : term173 B x y z.
Proof. exact (EQ_MP (@lem3640499 B x y z) (@lem3640478 B y x z)). Qed.
Lemma lem3640504 {B : Type'} (x : B) (y : B) (z : B) : term173 B x y z.
Proof. exact (@lem3640503 B x y z). Qed.
Lemma lem3640505 {A B : Type'} (f : A -> B) (g : B -> A) (x'' : B) : term1097 A B f g x''.
Proof. exact (@lem3640504 B (term374 A B f g x'') x'' (term374 A B f g x'')). Qed.
Lemma lem3640508 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term518 A B g s f t x'''''') (h2 : term575 A B x'' f g s) : x'' = (term374 A B f g x'').
Proof. exact (@lem3640505 A B f g x'' (@lem3640501 A B t x'''''' x'' f g s h1 h2)). Qed.
Lemma lem3640509 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term518 A B g s f t x'''''') (h2 : term575 A B x'' f g s) : term1098 A B f g x''.
Proof. exact (fun h0 : term1099 A B f g x'' => @lem3640508 A B t x'''''' x'' f g s h1 h2). Qed.
Lemma lem3640511 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3640512 {A B : Type'} (f : A -> B) (g : B -> A) (x'' : B) : (term1098 A B f g x'') = (x'' = (term374 A B f g x'')).
Proof. exact (@lem3640511 (x'' = (term374 A B f g x''))). Qed.
Lemma lem3640513 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term518 A B g s f t x'''''') (h2 : term575 A B x'' f g s) : x'' = (term374 A B f g x'').
Proof. exact (EQ_MP (@lem3640512 A B f g x'') (@lem3640509 A B t x'''''' x'' f g s h1 h2)). Qed.
Lemma lem3640515 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3640516 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3640515 A x). Qed.
Lemma lem3640517 {A B : Type'} (g : B -> A) (x'' : B) : (g x'') = (g x'').
Proof. exact (@lem3640516 A (g x'')). Qed.
Lemma lem3640518 {A B : Type'} (g : B -> A) (x'' : B) : term1100 A B g x''.
Proof. exact (fun h0 : term1101 A B g x'' => @lem3640517 A B g x''). Qed.
Lemma lem3640520 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3640521 {A B : Type'} (g : B -> A) (x'' : B) : (term1100 A B g x'') = ((g x'') = (g x'')).
Proof. exact (@lem3640520 ((g x'') = (g x''))). Qed.
Lemma lem3640522 {A B : Type'} (g : B -> A) (x'' : B) : (g x'') = (g x'').
Proof. exact (EQ_MP (@lem3640521 A B g x'') (@lem3640518 A B g x'')). Qed.
Lemma lem3640524 {A B : Type'} (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term575 A B x'' f g s) : s x''.
Proof. exact (proj1 (@lem3638283 A B x'' f g s h1)). Qed.
Lemma lem3640525 {A B : Type'} (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term575 A B x'' f g s) : term131 B s x''.
Proof. exact (fun h0 : term75 B s x'' => @lem3640524 A B x'' f g s h1). Qed.
Lemma lem3640527 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3640528 {B : Type'} (s : B -> Prop) (x'' : B) : (term131 B s x'') = (s x'').
Proof. exact (@lem3640527 (s x'')). Qed.
Lemma lem3640529 {A B : Type'} (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term575 A B x'' f g s) : s x''.
Proof. exact (EQ_MP (@lem3640528 B s x'') (@lem3640525 A B x'' f g s h1)). Qed.
Lemma lem3640531 (a : Prop) (b : Prop) : (term178 a b) = (term179 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3640532 {A B : Type'} (_39733 : A) (g : B -> A) (s : B -> Prop) (_39734 : B) : (term554 A B _39733 g s _39734) = (term553 A B _39733 g s _39734).
Proof. exact (@lem3640531 (_39733 = (g _39734)) (s _39734)). Qed.
Lemma lem3640533 {A B : Type'} (x'' : B) (f : A -> B) (_39733 : A) : (term561 A B x'' f _39733) = (term561 A B x'' f _39733).
Proof. exact (eq_refl (term561 A B x'' f _39733)). Qed.
Lemma lem3640534 {A B : Type'} (x'' : B) (f : A -> B) (_39733 : A) (g : B -> A) (s : B -> Prop) (_39734 : B) : (term998 A B x'' f _39733 g s _39734) = (term1102 A B x'' f _39733 g s _39734).
Proof. exact (MK_COMB (@lem3640533 A B x'' f _39733) (@lem3640532 A B _39733 g s _39734)). Qed.
Lemma lem3640536 (a : Prop) (b : Prop) : (term178 a b) = (term179 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3640537 {A B : Type'} (x'' : B) (f : A -> B) (_39733 : A) (g : B -> A) (s : B -> Prop) (_39734 : B) : (term1102 A B x'' f _39733 g s _39734) = (term1103 A B x'' f _39733 g s _39734).
Proof. exact (@lem3640536 (x'' = (f _39733)) (term21 A B _39733 g s _39734)). Qed.
Lemma lem3640538 {A B : Type'} (x'' : B) (f : A -> B) (_39733 : A) (g : B -> A) (s : B -> Prop) (_39734 : B) : (term998 A B x'' f _39733 g s _39734) = (term1103 A B x'' f _39733 g s _39734).
Proof. exact (TRANS (@lem3640534 A B x'' f _39733 g s _39734) (@lem3640537 A B x'' f _39733 g s _39734)). Qed.
Lemma lem3640540 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3640541 {A B : Type'} (x'' : B) (f : A -> B) (_39733 : A) (g : B -> A) (s : B -> Prop) (_39734 : B) : (term1103 A B x'' f _39733 g s _39734) = (term1104 A B x'' f _39733 g s _39734).
Proof. exact (@lem3640540 (term700 A B x'' f _39733 g s _39734)). Qed.
Lemma lem3640542 {A B : Type'} (x'' : B) (f : A -> B) (_39733 : A) (g : B -> A) (s : B -> Prop) (_39734 : B) : (term998 A B x'' f _39733 g s _39734) = (term1104 A B x'' f _39733 g s _39734).
Proof. exact (TRANS (@lem3640538 A B x'' f _39733 g s _39734) (@lem3640541 A B x'' f _39733 g s _39734)). Qed.
Lemma lem3640544 {A B : Type'} (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term575 A B x'' f g s) : term1105 A B g s x''.
Proof. exact (conj (@lem3640522 A B g x'') (@lem3640529 A B x'' f g s h1)). Qed.
Lemma lem3640545 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term518 A B g s f t x'''''') (h2 : term575 A B x'' f g s) : term1106 A B f g s x''.
Proof. exact (conj (@lem3640513 A B t x'''''' x'' f g s h1 h2) (@lem3640544 A B x'' f g s h2)). Qed.
Lemma lem3640547 {A B : Type'} (_39733 : A) (_39734 : B) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term575 A B x'' f g s) : term1104 A B x'' f _39733 g s _39734.
Proof. exact (EQ_MP (@lem3640542 A B x'' f _39733 g s _39734) (@lem3638816 A B _39733 _39734 x'' f g s h1)). Qed.
Lemma lem3640548 {A B : Type'} (_39733 : A) (_39734 : B) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term575 A B x'' f g s) : term1104 A B x'' f _39733 g s _39734.
Proof. exact (@lem3640547 A B _39733 _39734 x'' f g s h1). Qed.
Lemma lem3640549 {A B : Type'} (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term575 A B x'' f g s) : term1107 A B f g s x''.
Proof. exact (@lem3640548 A B (g x'') x'' x'' f g s h1). Qed.
Lemma lem3640552 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term518 A B g s f t x'''''') (h2 : term575 A B x'' f g s) : False.
Proof. exact (@lem3640549 A B x'' f g s h2 (@lem3640545 A B t x'''''' x'' f g s h1 h2)). Qed.
Lemma lem3640553 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term518 A B g s f t x'''''') (h2 : term575 A B x'' f g s) : term183.
Proof. exact (fun h0 : ~ False => @lem3640552 A B t x'''''' x'' f g s h1 h2). Qed.
Lemma lem3640555 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3640556 : term183 = False.
Proof. exact (@lem3640555 False). Qed.
Lemma lem3640557 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term518 A B g s f t x'''''') (h2 : term575 A B x'' f g s) : False.
Proof. exact (EQ_MP (@lem3640556) (@lem3640553 A B t x'''''' x'' f g s h1 h2)). Qed.
Lemma lem3640570 {B : Type'} (s : B -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3640571 {B : Type'} (_39899 : B) (_39900 : B) (h1 : _39899 = _39900) : _39899 = _39900.
Proof. exact (h1). Qed.
Lemma lem3640572 {B : Type'} (s : B -> Prop) (_39899 : B) (_39900 : B) (h1 : _39899 = _39900) : (s _39899) = (s _39900).
Proof. exact (MK_COMB (@lem3640570 B s) (@lem3640571 B _39899 _39900 h1)). Qed.
Lemma lem3640574 (b : Prop) (a : Prop) : term1108 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem3640575 {B : Type'} (_39900 : B) (s : B -> Prop) (_39899 : B) : term1109 B _39900 s _39899.
Proof. exact (@lem3640574 (s _39900) (s _39899)). Qed.
Lemma lem3640576 {B : Type'} (s : B -> Prop) (_39899 : B) (_39900 : B) (h1 : _39899 = _39900) : term1110 B _39900 s _39899.
Proof. exact (@lem3640575 B _39900 s _39899 (@lem3640572 B s _39899 _39900 h1)). Qed.
Lemma lem3640577 {B : Type'} (_39900 : B) (s : B -> Prop) (_39899 : B) : term1111 B _39900 s _39899.
Proof. exact (fun h0 : _39899 = _39900 => @lem3640576 B s _39899 _39900 h0). Qed.
Lemma lem3640579 (a : Prop) (b : Prop) : (a -> b) = (term1068 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3640580 {B : Type'} (_39900 : B) (s : B -> Prop) (_39899 : B) : (term1111 B _39900 s _39899) = (term1112 B _39900 s _39899).
Proof. exact (@lem3640579 (_39899 = _39900) (term1110 B _39900 s _39899)). Qed.
Lemma lem3640581 {B : Type'} (_39900 : B) (s : B -> Prop) (_39899 : B) : term1112 B _39900 s _39899.
Proof. exact (EQ_MP (@lem3640580 B _39900 s _39899) (@lem3640577 B _39900 s _39899)). Qed.
Lemma lem3640607 {B : Type'} (x : B) (y : B) (z : B) : term130 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem3640611 {A B : Type'} (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term727 A B x'' f x'''' g s x''''') : s x'''''.
Proof. exact (proj2 (@lem3638289 A B x'' f x'''' g s x''''' h1)). Qed.
Lemma lem3640612 {A B : Type'} (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term727 A B x'' f x'''' g s x''''') : term131 B s x'''''.
Proof. exact (fun h0 : term75 B s x''''' => @lem3640611 A B x'' f x'''' g s x''''' h1). Qed.
Lemma lem3640614 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3640615 {B : Type'} (s : B -> Prop) (x''''' : B) : (term131 B s x''''') = (s x''''').
Proof. exact (@lem3640614 (s x''''')). Qed.
Lemma lem3640616 {A B : Type'} (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term727 A B x'' f x'''' g s x''''') : s x'''''.
Proof. exact (EQ_MP (@lem3640615 B s x''''') (@lem3640612 A B x'' f x'''' g s x''''' h1)). Qed.
Lemma lem3640622 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3640623 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) (_39735 : B) : (term1007 A B s f g _39735) = (term1072 A B f g s _39735).
Proof. exact (@lem3640622 ((term374 A B f g _39735) = _39735) (term75 B s _39735)). Qed.
Lemma lem3640631 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3640632 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) (_39735 : B) : (term1073 A B s f g _39735) = (term1074 A B f g s _39735).
Proof. exact (MK_COMB (@lem3640631) (@lem3640623 A B f g s _39735)). Qed.
Lemma lem3640640 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) (_39735 : B) : (term1072 A B f g s _39735) = (term1072 A B f g s _39735).
Proof. exact (eq_refl (term1072 A B f g s _39735)). Qed.
Lemma lem3640641 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) (_39735 : B) : ((term1007 A B s f g _39735) = (term1072 A B f g s _39735)) = ((term1072 A B f g s _39735) = (term1072 A B f g s _39735)).
Proof. exact (MK_COMB (@lem3640632 A B f g s _39735) (@lem3640640 A B f g s _39735)). Qed.
Lemma lem3640643 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3640644 (x : Prop) : (x = x) = True.
Proof. exact (@lem3640643 Prop x). Qed.
Lemma lem3640645 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) (_39735 : B) : ((term1072 A B f g s _39735) = (term1072 A B f g s _39735)) = True.
Proof. exact (@lem3640644 (term1072 A B f g s _39735)). Qed.
Lemma lem3640646 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) (_39735 : B) : ((term1007 A B s f g _39735) = (term1072 A B f g s _39735)) = True.
Proof. exact (TRANS (@lem3640641 A B f g s _39735) (@lem3640645 A B f g s _39735)). Qed.
Lemma lem3640647 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) (_39735 : B) : True = ((term1007 A B s f g _39735) = (term1072 A B f g s _39735)).
Proof. exact (SYM (@lem3640646 A B f g s _39735)). Qed.
Lemma lem3640648 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) (_39735 : B) : (term1007 A B s f g _39735) = (term1072 A B f g s _39735).
Proof. exact (EQ_MP (@lem3640647 A B f g s _39735) (@lem0)). Qed.
Lemma lem3640649 {A B : Type'} (_39735 : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term1072 A B f g s _39735.
Proof. exact (EQ_MP (@lem3640648 A B f g s _39735) (@lem3639701 A B _39735 g s f t x'''''' h1)). Qed.
Lemma lem3640651 (b : Prop) (a : Prop) : (a \/ b) = (term136 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3640652 {A B : Type'} (s : B -> Prop) (f : A -> B) (g : B -> A) (_39735 : B) : (term1072 A B f g s _39735) = (term1075 A B s f g _39735).
Proof. exact (@lem3640651 (term75 B s _39735) ((term374 A B f g _39735) = _39735)). Qed.
Lemma lem3640654 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3640655 {B : Type'} (s : B -> Prop) (_39735 : B) : (term138 B s _39735) = (s _39735).
Proof. exact (@lem3640654 (s _39735)). Qed.
Lemma lem3640656 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3640657 {B : Type'} (s : B -> Prop) (_39735 : B) : (term139 B s _39735) = (term14 B s _39735).
Proof. exact (MK_COMB (@lem3640656) (@lem3640655 B s _39735)). Qed.
Lemma lem3640658 {A B : Type'} (f : A -> B) (g : B -> A) (_39735 : B) : ((term374 A B f g _39735) = _39735) = ((term374 A B f g _39735) = _39735).
Proof. exact (eq_refl ((term374 A B f g _39735) = _39735)). Qed.
Lemma lem3640659 {A B : Type'} (s : B -> Prop) (f : A -> B) (g : B -> A) (_39735 : B) : (term1075 A B s f g _39735) = (term1076 A B s f g _39735).
Proof. exact (MK_COMB (@lem3640657 B s _39735) (@lem3640658 A B f g _39735)). Qed.
Lemma lem3640660 {A B : Type'} (s : B -> Prop) (f : A -> B) (g : B -> A) (_39735 : B) : (term1072 A B f g s _39735) = (term1076 A B s f g _39735).
Proof. exact (TRANS (@lem3640652 A B s f g _39735) (@lem3640659 A B s f g _39735)). Qed.
Lemma lem3640663 {A B : Type'} (_39735 : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term1076 A B s f g _39735.
Proof. exact (EQ_MP (@lem3640660 A B s f g _39735) (@lem3640649 A B _39735 g s f t x'''''' h1)). Qed.
Lemma lem3640664 {A B : Type'} (_39735 : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term1076 A B s f g _39735.
Proof. exact (@lem3640663 A B _39735 g s f t x'''''' h1). Qed.
Lemma lem3640665 {A B : Type'} (x''''' : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (x'''''' : B -> A) (h1 : term518 A B g s f t x'''''') : term1076 A B s f g x'''''.
Proof. exact (@lem3640664 A B x''''' g s f t x'''''' h1). Qed.
Lemma lem3640668 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term518 A B g s f t x'''''') (h2 : term727 A B x'' f x'''' g s x''''') : (term374 A B f g x''''') = x'''''.
Proof. exact (@lem3640665 A B x''''' g s f t x'''''' h1 (@lem3640616 A B x'' f x'''' g s x''''' h2)). Qed.
Lemma lem3640669 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term518 A B g s f t x'''''') (h2 : term727 A B x'' f x'''' g s x''''') : term1077 A B f g x'''''.
Proof. exact (fun h0 : term1078 A B f g x''''' => @lem3640668 A B t x'''''' x'' f x'''' g s x''''' h1 h2). Qed.
Lemma lem3640671 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3640672 {A B : Type'} (f : A -> B) (g : B -> A) (x''''' : B) : (term1077 A B f g x''''') = ((term374 A B f g x''''') = x''''').
Proof. exact (@lem3640671 ((term374 A B f g x''''') = x''''')). Qed.
Lemma lem3640673 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term518 A B g s f t x'''''') (h2 : term727 A B x'' f x'''' g s x''''') : (term374 A B f g x''''') = x'''''.
Proof. exact (EQ_MP (@lem3640672 A B f g x''''') (@lem3640669 A B t x'''''' x'' f x'''' g s x''''' h1 h2)). Qed.
Lemma lem3640675 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3640676 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3640675 B x). Qed.
Lemma lem3640677 {A B : Type'} (f : A -> B) (g : B -> A) (x''''' : B) : (term374 A B f g x''''') = (term374 A B f g x''''').
Proof. exact (@lem3640676 B (term374 A B f g x''''')). Qed.
Lemma lem3640678 {A B : Type'} (f : A -> B) (g : B -> A) (x''''' : B) : term1094 A B f g x'''''.
Proof. exact (fun h0 : term1050 A B f g x''''' => @lem3640677 A B f g x'''''). Qed.
Lemma lem3640680 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3640681 {A B : Type'} (f : A -> B) (g : B -> A) (x''''' : B) : (term1094 A B f g x''''') = ((term374 A B f g x''''') = (term374 A B f g x''''')).
Proof. exact (@lem3640680 ((term374 A B f g x''''') = (term374 A B f g x'''''))). Qed.
Lemma lem3640682 {A B : Type'} (f : A -> B) (g : B -> A) (x''''' : B) : (term374 A B f g x''''') = (term374 A B f g x''''').
Proof. exact (EQ_MP (@lem3640681 A B f g x''''') (@lem3640678 A B f g x''''')). Qed.
Lemma lem3640700 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3640701 {B : Type'} (y : B) (x : B) (z : B) : (term152 B x y z) = (term153 B y x z).
Proof. exact (@lem3640700 (y = z) (term154 B x z)). Qed.
Lemma lem3640711 {B : Type'} (x : B) (y : B) : (term155 B x y) = (term155 B x y).
Proof. exact (eq_refl (term155 B x y)). Qed.
Lemma lem3640712 {B : Type'} (y : B) (x : B) (z : B) : (term130 B x y z) = (term156 B y x z).
Proof. exact (MK_COMB (@lem3640711 B x y) (@lem3640701 B y x z)). Qed.
Lemma lem3640716 (q : Prop) (p : Prop) (r : Prop) : (term157 p q r) = (term157 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3640717 {B : Type'} (y : B) (x : B) (z : B) : (term156 B y x z) = (term158 B y x z).
Proof. exact (@lem3640716 (y = z) (term154 B x y) (term154 B x z)). Qed.
Lemma lem3640739 {B : Type'} (y : B) (x : B) (z : B) : (term130 B x y z) = (term158 B y x z).
Proof. exact (TRANS (@lem3640712 B y x z) (@lem3640717 B y x z)). Qed.
Lemma lem3640740 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3640741 {B : Type'} (y : B) (x : B) (z : B) : (term159 B x y z) = (term160 B y x z).
Proof. exact (MK_COMB (@lem3640740) (@lem3640739 B y x z)). Qed.
Lemma lem3640763 {B : Type'} (y : B) (x : B) (z : B) : (term158 B y x z) = (term158 B y x z).
Proof. exact (eq_refl (term158 B y x z)). Qed.
Lemma lem3640764 {B : Type'} (y : B) (x : B) (z : B) : ((term130 B x y z) = (term158 B y x z)) = ((term158 B y x z) = (term158 B y x z)).
Proof. exact (MK_COMB (@lem3640741 B y x z) (@lem3640763 B y x z)). Qed.
Lemma lem3640766 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3640767 (x : Prop) : (x = x) = True.
Proof. exact (@lem3640766 Prop x). Qed.
Lemma lem3640768 {B : Type'} (y : B) (x : B) (z : B) : ((term158 B y x z) = (term158 B y x z)) = True.
Proof. exact (@lem3640767 (term158 B y x z)). Qed.
Lemma lem3640769 {B : Type'} (y : B) (x : B) (z : B) : ((term130 B x y z) = (term158 B y x z)) = True.
Proof. exact (TRANS (@lem3640764 B y x z) (@lem3640768 B y x z)). Qed.
Lemma lem3640770 {B : Type'} (y : B) (x : B) (z : B) : True = ((term130 B x y z) = (term158 B y x z)).
Proof. exact (SYM (@lem3640769 B y x z)). Qed.
Lemma lem3640771 {B : Type'} (y : B) (x : B) (z : B) : (term130 B x y z) = (term158 B y x z).
Proof. exact (EQ_MP (@lem3640770 B y x z) (@lem0)). Qed.
Lemma lem3640772 {B : Type'} (y : B) (x : B) (z : B) : term158 B y x z.
Proof. exact (EQ_MP (@lem3640771 B y x z) (@lem3640607 B x y z)). Qed.
Lemma lem3640774 (b : Prop) (a : Prop) : (a \/ b) = (term136 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3640775 {B : Type'} (x : B) (y : B) (z : B) : (term158 B y x z) = (term161 B x y z).
Proof. exact (@lem3640774 (term162 B y x z) (y = z)). Qed.
Lemma lem3640777 (a : Prop) (b : Prop) : (term163 a b) = (term164 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3640778 {B : Type'} (y : B) (x : B) (z : B) : (term165 B y x z) = (term166 B y x z).
Proof. exact (@lem3640777 (term154 B x y) (term154 B x z)). Qed.
Lemma lem3640780 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3640781 {B : Type'} (x : B) (y : B) : (term167 B x y) = (x = y).
Proof. exact (@lem3640780 (x = y)). Qed.
Lemma lem3640782 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3640783 {B : Type'} (x : B) (y : B) : (term168 B x y) = (term169 B x y).
Proof. exact (MK_COMB (@lem3640782) (@lem3640781 B x y)). Qed.
Lemma lem3640785 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3640786 {B : Type'} (x : B) (z : B) : (term167 B x z) = (x = z).
Proof. exact (@lem3640785 (x = z)). Qed.
Lemma lem3640787 {B : Type'} (y : B) (x : B) (z : B) : (term166 B y x z) = (term170 B y x z).
Proof. exact (MK_COMB (@lem3640783 B x y) (@lem3640786 B x z)). Qed.
Lemma lem3640788 {B : Type'} (y : B) (x : B) (z : B) : (term165 B y x z) = (term170 B y x z).
Proof. exact (TRANS (@lem3640778 B y x z) (@lem3640787 B y x z)). Qed.
Lemma lem3640789 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3640790 {B : Type'} (y : B) (x : B) (z : B) : (term171 B y x z) = (term172 B y x z).
Proof. exact (MK_COMB (@lem3640789) (@lem3640788 B y x z)). Qed.
Lemma lem3640791 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3640792 {B : Type'} (x : B) (y : B) (z : B) : (term161 B x y z) = (term173 B x y z).
Proof. exact (MK_COMB (@lem3640790 B y x z) (@lem3640791 B y z)). Qed.
Lemma lem3640793 {B : Type'} (x : B) (y : B) (z : B) : (term158 B y x z) = (term173 B x y z).
Proof. exact (TRANS (@lem3640775 B x y z) (@lem3640792 B x y z)). Qed.
Lemma lem3640795 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term518 A B g s f t x'''''') (h2 : term727 A B x'' f x'''' g s x''''') : term1096 A B f g x'''''.
Proof. exact (conj (@lem3640673 A B t x'''''' x'' f x'''' g s x''''' h1 h2) (@lem3640682 A B f g x''''')). Qed.
Lemma lem3640797 {B : Type'} (x : B) (y : B) (z : B) : term173 B x y z.
Proof. exact (EQ_MP (@lem3640793 B x y z) (@lem3640772 B y x z)). Qed.
Lemma lem3640798 {B : Type'} (x : B) (y : B) (z : B) : term173 B x y z.
Proof. exact (@lem3640797 B x y z). Qed.
Lemma lem3640799 {A B : Type'} (f : A -> B) (g : B -> A) (x''''' : B) : term1097 A B f g x'''''.
Proof. exact (@lem3640798 B (term374 A B f g x''''') x''''' (term374 A B f g x''''')). Qed.
Lemma lem3640802 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term518 A B g s f t x'''''') (h2 : term727 A B x'' f x'''' g s x''''') : x''''' = (term374 A B f g x''''').
Proof. exact (@lem3640799 A B f g x''''' (@lem3640795 A B t x'''''' x'' f x'''' g s x''''' h1 h2)). Qed.
Lemma lem3640803 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term518 A B g s f t x'''''') (h2 : term727 A B x'' f x'''' g s x''''') : term1098 A B f g x'''''.
Proof. exact (fun h0 : term1099 A B f g x''''' => @lem3640802 A B t x'''''' x'' f x'''' g s x''''' h1 h2). Qed.
Lemma lem3640805 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3640806 {A B : Type'} (f : A -> B) (g : B -> A) (x''''' : B) : (term1098 A B f g x''''') = (x''''' = (term374 A B f g x''''')).
Proof. exact (@lem3640805 (x''''' = (term374 A B f g x'''''))). Qed.
Lemma lem3640807 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term518 A B g s f t x'''''') (h2 : term727 A B x'' f x'''' g s x''''') : x''''' = (term374 A B f g x''''').
Proof. exact (EQ_MP (@lem3640806 A B f g x''''') (@lem3640803 A B t x'''''' x'' f x'''' g s x''''' h1 h2)). Qed.
Lemma lem3640809 {A B : Type'} (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term727 A B x'' f x'''' g s x''''') : s x'''''.
Proof. exact (proj2 (@lem3638289 A B x'' f x'''' g s x''''' h1)). Qed.
Lemma lem3640810 {A B : Type'} (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term727 A B x'' f x'''' g s x''''') : term131 B s x'''''.
Proof. exact (fun h0 : term75 B s x''''' => @lem3640809 A B x'' f x'''' g s x''''' h1). Qed.
Lemma lem3640812 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3640813 {B : Type'} (s : B -> Prop) (x''''' : B) : (term131 B s x''''') = (s x''''').
Proof. exact (@lem3640812 (s x''''')). Qed.
Lemma lem3640814 {A B : Type'} (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term727 A B x'' f x'''' g s x''''') : s x'''''.
Proof. exact (EQ_MP (@lem3640813 B s x''''') (@lem3640810 A B x'' f x'''' g s x''''' h1)). Qed.
Lemma lem3640820 (q : Prop) (p : Prop) (r : Prop) : (term157 p q r) = (term157 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3640821 {B : Type'} (_39900 : B) (s : B -> Prop) (_39899 : B) : (term1112 B _39900 s _39899) = (term1113 B _39900 s _39899).
Proof. exact (@lem3640820 (s _39900) (term154 B _39899 _39900) (term75 B s _39899)). Qed.
Lemma lem3640835 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3640836 {B : Type'} (s : B -> Prop) (_39899 : B) (_39900 : B) : (term1114 B _39900 s _39899) = (term1115 B s _39899 _39900).
Proof. exact (@lem3640835 (term75 B s _39899) (term154 B _39899 _39900)). Qed.
Lemma lem3640844 {B : Type'} (s : B -> Prop) (_39900 : B) : (term1116 B s _39900) = (term1116 B s _39900).
Proof. exact (eq_refl (term1116 B s _39900)). Qed.
Lemma lem3640845 {B : Type'} (s : B -> Prop) (_39899 : B) (_39900 : B) : (term1113 B _39900 s _39899) = (term1117 B s _39899 _39900).
Proof. exact (MK_COMB (@lem3640844 B s _39900) (@lem3640836 B s _39899 _39900)). Qed.
Lemma lem3640856 {B : Type'} (s : B -> Prop) (_39899 : B) (_39900 : B) : (term1112 B _39900 s _39899) = (term1117 B s _39899 _39900).
Proof. exact (TRANS (@lem3640821 B _39900 s _39899) (@lem3640845 B s _39899 _39900)). Qed.
Lemma lem3640857 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3640858 {B : Type'} (s : B -> Prop) (_39899 : B) (_39900 : B) : (term1118 B _39900 s _39899) = (term1119 B s _39899 _39900).
Proof. exact (MK_COMB (@lem3640857) (@lem3640856 B s _39899 _39900)). Qed.
Lemma lem3640872 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3640873 {B : Type'} (s : B -> Prop) (_39899 : B) (_39900 : B) : (term1114 B _39900 s _39899) = (term1115 B s _39899 _39900).
Proof. exact (@lem3640872 (term75 B s _39899) (term154 B _39899 _39900)). Qed.
Lemma lem3640881 {B : Type'} (s : B -> Prop) (_39900 : B) : (term1116 B s _39900) = (term1116 B s _39900).
Proof. exact (eq_refl (term1116 B s _39900)). Qed.
Lemma lem3640882 {B : Type'} (s : B -> Prop) (_39899 : B) (_39900 : B) : (term1113 B _39900 s _39899) = (term1117 B s _39899 _39900).
Proof. exact (MK_COMB (@lem3640881 B s _39900) (@lem3640873 B s _39899 _39900)). Qed.
Lemma lem3640893 {B : Type'} (s : B -> Prop) (_39899 : B) (_39900 : B) : ((term1112 B _39900 s _39899) = (term1113 B _39900 s _39899)) = ((term1117 B s _39899 _39900) = (term1117 B s _39899 _39900)).
Proof. exact (MK_COMB (@lem3640858 B s _39899 _39900) (@lem3640882 B s _39899 _39900)). Qed.
Lemma lem3640895 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3640896 (x : Prop) : (x = x) = True.
Proof. exact (@lem3640895 Prop x). Qed.
Lemma lem3640897 {B : Type'} (s : B -> Prop) (_39899 : B) (_39900 : B) : ((term1117 B s _39899 _39900) = (term1117 B s _39899 _39900)) = True.
Proof. exact (@lem3640896 (term1117 B s _39899 _39900)). Qed.
Lemma lem3640898 {B : Type'} (_39900 : B) (s : B -> Prop) (_39899 : B) : ((term1112 B _39900 s _39899) = (term1113 B _39900 s _39899)) = True.
Proof. exact (TRANS (@lem3640893 B s _39899 _39900) (@lem3640897 B s _39899 _39900)). Qed.
Lemma lem3640899 {B : Type'} (_39900 : B) (s : B -> Prop) (_39899 : B) : True = ((term1112 B _39900 s _39899) = (term1113 B _39900 s _39899)).
Proof. exact (SYM (@lem3640898 B _39900 s _39899)). Qed.
Lemma lem3640900 {B : Type'} (_39900 : B) (s : B -> Prop) (_39899 : B) : (term1112 B _39900 s _39899) = (term1113 B _39900 s _39899).
Proof. exact (EQ_MP (@lem3640899 B _39900 s _39899) (@lem0)). Qed.
Lemma lem3640901 {B : Type'} (_39900 : B) (s : B -> Prop) (_39899 : B) : term1113 B _39900 s _39899.
Proof. exact (EQ_MP (@lem3640900 B _39900 s _39899) (@lem3640581 B _39900 s _39899)). Qed.
Lemma lem3640903 (b : Prop) (a : Prop) : (a \/ b) = (term136 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3640904 {B : Type'} (_39899 : B) (s : B -> Prop) (_39900 : B) : (term1113 B _39900 s _39899) = (term1120 B _39899 s _39900).
Proof. exact (@lem3640903 (term1114 B _39900 s _39899) (s _39900)). Qed.
Lemma lem3640906 (a : Prop) (b : Prop) : (term163 a b) = (term164 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3640907 {B : Type'} (_39900 : B) (s : B -> Prop) (_39899 : B) : (term1121 B _39900 s _39899) = (term1122 B _39900 s _39899).
Proof. exact (@lem3640906 (term154 B _39899 _39900) (term75 B s _39899)). Qed.
Lemma lem3640909 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3640910 {B : Type'} (_39899 : B) (_39900 : B) : (term167 B _39899 _39900) = (_39899 = _39900).
Proof. exact (@lem3640909 (_39899 = _39900)). Qed.
Lemma lem3640911 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3640912 {B : Type'} (_39899 : B) (_39900 : B) : (term168 B _39899 _39900) = (term169 B _39899 _39900).
Proof. exact (MK_COMB (@lem3640911) (@lem3640910 B _39899 _39900)). Qed.
Lemma lem3640914 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3640915 {B : Type'} (s : B -> Prop) (_39899 : B) : (term138 B s _39899) = (s _39899).
Proof. exact (@lem3640914 (s _39899)). Qed.
Lemma lem3640916 {B : Type'} (_39900 : B) (s : B -> Prop) (_39899 : B) : (term1122 B _39900 s _39899) = (term1123 B _39900 s _39899).
Proof. exact (MK_COMB (@lem3640912 B _39899 _39900) (@lem3640915 B s _39899)). Qed.
Lemma lem3640917 {B : Type'} (_39900 : B) (s : B -> Prop) (_39899 : B) : (term1121 B _39900 s _39899) = (term1123 B _39900 s _39899).
Proof. exact (TRANS (@lem3640907 B _39900 s _39899) (@lem3640916 B _39900 s _39899)). Qed.
Lemma lem3640918 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3640919 {B : Type'} (_39900 : B) (s : B -> Prop) (_39899 : B) : (term1124 B _39900 s _39899) = (term1125 B _39900 s _39899).
Proof. exact (MK_COMB (@lem3640918) (@lem3640917 B _39900 s _39899)). Qed.
Lemma lem3640920 {B : Type'} (s : B -> Prop) (_39900 : B) : (s _39900) = (s _39900).
Proof. exact (eq_refl (s _39900)). Qed.
Lemma lem3640921 {B : Type'} (_39899 : B) (s : B -> Prop) (_39900 : B) : (term1120 B _39899 s _39900) = (term1126 B _39899 s _39900).
Proof. exact (MK_COMB (@lem3640919 B _39900 s _39899) (@lem3640920 B s _39900)). Qed.
Lemma lem3640922 {B : Type'} (_39899 : B) (s : B -> Prop) (_39900 : B) : (term1113 B _39900 s _39899) = (term1126 B _39899 s _39900).
Proof. exact (TRANS (@lem3640904 B _39899 s _39900) (@lem3640921 B _39899 s _39900)). Qed.
Lemma lem3640924 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term518 A B g s f t x'''''') (h2 : term727 A B x'' f x'''' g s x''''') : term1127 A B f g s x'''''.
Proof. exact (conj (@lem3640807 A B t x'''''' x'' f x'''' g s x''''' h1 h2) (@lem3640814 A B x'' f x'''' g s x''''' h2)). Qed.
Lemma lem3640926 {B : Type'} (_39899 : B) (s : B -> Prop) (_39900 : B) : term1126 B _39899 s _39900.
Proof. exact (EQ_MP (@lem3640922 B _39899 s _39900) (@lem3640901 B _39900 s _39899)). Qed.
Lemma lem3640927 {B : Type'} (_39899 : B) (s : B -> Prop) (_39900 : B) : term1126 B _39899 s _39900.
Proof. exact (@lem3640926 B _39899 s _39900). Qed.
Lemma lem3640928 {A B : Type'} (s : B -> Prop) (f : A -> B) (g : B -> A) (x''''' : B) : term1128 A B s f g x'''''.
Proof. exact (@lem3640927 B x''''' s (term374 A B f g x''''')). Qed.
Lemma lem3640931 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term518 A B g s f t x'''''') (h2 : term727 A B x'' f x'''' g s x''''') : term1129 A B s f g x'''''.
Proof. exact (@lem3640928 A B s f g x''''' (@lem3640924 A B t x'''''' x'' f x'''' g s x''''' h1 h2)). Qed.
Lemma lem3640932 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term518 A B g s f t x'''''') (h2 : term727 A B x'' f x'''' g s x''''') : term1130 A B s f g x'''''.
Proof. exact (fun h0 : term1059 A B s f g x''''' => @lem3640931 A B t x'''''' x'' f x'''' g s x''''' h1 h2). Qed.
Lemma lem3640934 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3640935 {A B : Type'} (s : B -> Prop) (f : A -> B) (g : B -> A) (x''''' : B) : (term1130 A B s f g x''''') = (term1129 A B s f g x''''').
Proof. exact (@lem3640934 (term1129 A B s f g x''''')). Qed.
Lemma lem3640936 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term518 A B g s f t x'''''') (h2 : term727 A B x'' f x'''' g s x''''') : term1129 A B s f g x'''''.
Proof. exact (EQ_MP (@lem3640935 A B s f g x''''') (@lem3640932 A B t x'''''' x'' f x'''' g s x''''' h1 h2)). Qed.
Lemma lem3640939 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3640941 {A B : Type'} (s : B -> Prop) (f : A -> B) (g : B -> A) (x''''' : B) : (term1059 A B s f g x''''') = (term1131 A B s f g x''''').
Proof. exact (@lem3640939 (term1129 A B s f g x''''')). Qed.
Lemma lem3640944 {A B : Type'} (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term727 A B x'' f x'''' g s x''''') : term1131 A B s f g x'''''.
Proof. exact (EQ_MP (@lem3640941 A B s f g x''''') (@lem3639631 A B x'' f x'''' g s x''''' h1)). Qed.
Lemma lem3640947 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term518 A B g s f t x'''''') (h2 : term727 A B x'' f x'''' g s x''''') : False.
Proof. exact (@lem3640944 A B x'' f x'''' g s x''''' h2 (@lem3640936 A B t x'''''' x'' f x'''' g s x''''' h1 h2)). Qed.
Lemma lem3640948 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term518 A B g s f t x'''''') (h2 : term727 A B x'' f x'''' g s x''''') : term183.
Proof. exact (fun h0 : ~ False => @lem3640947 A B t x'''''' x'' f x'''' g s x''''' h1 h2). Qed.
Lemma lem3640950 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3640951 : term183 = False.
Proof. exact (@lem3640950 False). Qed.
Lemma lem3640954 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term518 A B g s f t x'''''') (h2 : term727 A B x'' f x'''' g s x''''') : False.
Proof. exact (EQ_MP (@lem3640951) (@lem3640948 A B t x'''''' x'' f x'''' g s x''''' h1 h2)). Qed.
Lemma lem3640956 {A B : Type'} (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term983 A B f x y) (h2 : term684 A B x'' g s x''' f x y) : False.
Proof. exact (EQ_MP (@lem3640262) (@lem3640259 A B x'' g s x''' f x y h1 h2)). Qed.
Lemma lem3640958 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term518 A B g s f t x'''''') (h2 : term684 A B x'' g s x''' f x y) (h3 : term982 A B f x y) : False.
Proof. exact (EQ_MP (@lem3640185) (@lem3640182 A B t x'''''' x'' g s x''' f x y h1 h2 h3)). Qed.
Lemma lem3640959 {A B : Type'} (f : A -> B) (x'''''' : B -> A) (g : B -> A) (s : B -> Prop) (x' : B) (t : A -> Prop) (x : A) (h1 : term518 A B g s f t x'''''') (h2 : term629 A B g s x' t x) : False.
Proof. exact (EQ_MP (@lem3639828) (@lem3639825 A B f x'''''' g s x' t x h1 h2)). Qed.
Lemma lem3640960 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term518 A B g s f t x'''''') (h2 : term768 A B x'' f x'''' g s x''''') : False.
Proof. exact (or_elim (@lem3638268 A B x'' f x'''' g s x''''' h2) (fun h0 : term575 A B x'' f g s => @lem3640557 A B t x'''''' x'' f g s h1 h0) (fun h0 : term727 A B x'' f x'''' g s x''''' => @lem3640954 A B t x'''''' x'' f x'''' g s x''''' h1 h0)). Qed.
Lemma lem3640961 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x'' : B) (g : B -> A) (s : B -> Prop) (x''' : B) (f : A -> B) (x : A) (y : A) (h1 : term518 A B g s f t x'''''') (h2 : term684 A B x'' g s x''' f x y) : False.
Proof. exact (or_elim (@lem3638269 A B x'' g s x''' f x y h2) (fun h0 : term982 A B f x y => @lem3640958 A B t x'''''' x'' g s x''' f x y h1 h2 h0) (fun h0 : term983 A B f x y => @lem3640956 A B x'' g s x''' f x y h0 h2)). Qed.
Lemma lem3640962 {A B : Type'} (t : A -> Prop) (x'''''' : B -> A) (x''' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term518 A B g s f t x'''''') (h2 : term862 A B x''' x y x'' f x'''' g s x''''') : False.
Proof. exact (or_elim (@lem3638262 A B x''' x y x'' f x'''' g s x''''' h2) (fun h0 : term684 A B x'' g s x''' f x y => @lem3640961 A B t x'''''' x'' g s x''' f x y h1 h0) (fun h0 : term768 A B x'' f x'''' g s x''''' => @lem3640960 A B t x'''''' x'' f x'''' g s x''''' h1 h0)). Qed.
Lemma lem3640963 {A B : Type'} (x'''''' : B -> A) (x' : B) (t : A -> Prop) (x''' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term518 A B g s f t x'''''') (h2 : term966 A B x' t x''' x y x'' f x'''' g s x''''') : False.
Proof. exact (or_elim (@lem3638198 A B x' t x''' x y x'' f x'''' g s x''''' h2) (fun h0 : term629 A B g s x' t x => @lem3640959 A B f x'''''' g s x' t x h1 h0) (fun h0 : term862 A B x''' x y x'' f x'''' g s x''''' => @lem3640962 A B t x'''''' x''' x y x'' f x'''' g s x''''' h1 h0)). Qed.
Lemma lem3640964 {A B : Type'} (x'''''' : B -> A) (x' : B) (t : A -> Prop) (x''' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term518 A B g s f t x'''''') (h2 : term966 A B x' t x''' x y x'' f x'''' g s x''''') : (term518 A B g s f t x'''''') = False.
Proof. exact (prop_ext (fun h3 : term518 A B g s f t x'''''' => @lem3640963 A B x'''''' x' t x''' x y x'' f x'''' g s x''''' h1 h2) (fun h3 : False => @lem3638258 A B g s f t x'''''' h1)). Qed.
Lemma lem3640965 {A B : Type'} (x'''''' : B -> A) (x' : B) (t : A -> Prop) (x''' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term518 A B g s f t x'''''') (h2 : term966 A B x' t x''' x y x'' f x'''' g s x''''') : False.
Proof. exact (EQ_MP (@lem3640964 A B x'''''' x' t x''' x y x'' f x'''' g s x''''' h1 h2) (@lem3638258 A B g s f t x'''''' h1)). Qed.
Lemma lem3640966 {A B : Type'} (x'''''' : B -> A) (x' : B) (t : A -> Prop) (x''' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term518 A B g s f t x'''''') (h2 : term966 A B x' t x''' x y x'' f x'''' g s x''''') : (term966 A B x' t x''' x y x'' f x'''' g s x''''') = False.
Proof. exact (prop_ext (fun h3 : term966 A B x' t x''' x y x'' f x'''' g s x''''' => @lem3640965 A B x'''''' x' t x''' x y x'' f x'''' g s x''''' h1 h2) (fun h3 : False => @lem3638198 A B x' t x''' x y x'' f x'''' g s x''''' h2)). Qed.
Lemma lem3640967 {A B : Type'} (x'''''' : B -> A) (x' : B) (t : A -> Prop) (x''' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term518 A B g s f t x'''''') (h2 : term966 A B x' t x''' x y x'' f x'''' g s x''''') : False.
Proof. exact (EQ_MP (@lem3640966 A B x'''''' x' t x''' x y x'' f x'''' g s x''''' h1 h2) (@lem3638198 A B x' t x''' x y x'' f x'''' g s x''''' h2)). Qed.
Lemma lem3640968 {A B : Type'} (x' : B) (t : A -> Prop) (x''' : B) (x : A) (y : A) (x'' : B) (f : A -> B) (x'''' : A) (g : B -> A) (s : B -> Prop) (x''''' : B) (h1 : term394 A B g s f t) (h2 : term966 A B x' t x''' x y x'' f x'''' g s x''''') : False.
Proof. exact (ex_elim (@lem3636729 A B g s f t h1) (fun x'''''' : B -> A => fun h0 : term520 A B g s f t x'''''' => @lem3640967 A B x'''''' x' t x''' x y x'' f x'''' g s x''''' h0 h2)). Qed.
Lemma lem3640969 {A B : Type'} (x' : B) (x''' : B) (x : A) (y : A) (x'' : B) (x'''' : A) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term969 A B x' t x''' x y x'' f x'''' g s) (h2 : term394 A B g s f t) : False.
Proof. exact (ex_elim (@lem3638020 A B x' t x''' x y x'' f x'''' g s h1) (fun x''''' : B => fun h0 : term968 A B x' t x''' x y x'' f x'''' g s x''''' => @lem3640968 A B x' t x''' x y x'' f x'''' g s x''''' h2 h0)). Qed.
Lemma lem3640970 {A B : Type'} (x' : B) (x''' : B) (x : A) (y : A) (x'' : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term971 A B x' t x''' x y x'' f g s) (h2 : term394 A B g s f t) : False.
Proof. exact (ex_elim (@lem3638019 A B x' t x''' x y x'' f g s h1) (fun x'''' : A => fun h0 : term970 A B x' t x''' x y x'' f g s x'''' => @lem3640969 A B x' x''' x y x'' x'''' g s f t h0 h2)). Qed.
Lemma lem3640971 {A B : Type'} (x' : B) (x : A) (y : A) (x'' : B) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term973 A B x' t x y x'' f g s) (h2 : term394 A B g s f t) : False.
Proof. exact (ex_elim (@lem3638018 A B x' t x y x'' f g s h1) (fun x''' : B => fun h0 : term972 A B x' t x y x'' f g s x''' => @lem3640970 A B x' x''' x y x'' g s f t h0 h2)). Qed.
Lemma lem3640972 {A B : Type'} (x' : B) (x : A) (y : A) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term975 A B x' t x y f g s) (h2 : term394 A B g s f t) : False.
Proof. exact (ex_elim (@lem3638017 A B x' t x y f g s h1) (fun x'' : B => fun h0 : term974 A B x' t x y f g s x'' => @lem3640971 A B x' x y x'' g s f t h0 h2)). Qed.
Lemma lem3640973 {A B : Type'} (x' : B) (x : A) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term977 A B x' t x f g s) (h2 : term394 A B g s f t) : False.
Proof. exact (ex_elim (@lem3638016 A B x' t x f g s h1) (fun y : A => fun h0 : term976 A B x' t x f g s y => @lem3640972 A B x' x y g s f t h0 h2)). Qed.
Lemma lem3640974 {A B : Type'} (x : A) (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term979 A B t x f g s) (h2 : term394 A B g s f t) : False.
Proof. exact (ex_elim (@lem3638015 A B t x f g s h1) (fun x' : B => fun h0 : term978 A B t x f g s x' => @lem3640973 A B x' x g s f t h0 h2)). Qed.
Lemma lem3640975 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term459 A B t f g s) (h2 : term394 A B g s f t) : False.
Proof. exact (ex_elim (@lem3638014 A B t f g s h1) (fun x : A => fun h0 : term980 A B t f g s x => @lem3640974 A B x g s f t h0 h2)). Qed.
Lemma lem3640976 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term459 A B t f g s) (h2 : term394 A B g s f t) : (term459 A B t f g s) = False.
Proof. exact (prop_ext (fun h3 : term459 A B t f g s => @lem3640975 A B g s f t h1 h2) (fun h3 : False => @lem3636486 A B t f g s h1)). Qed.
Lemma lem3640977 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term459 A B t f g s) (h2 : term394 A B g s f t) : False.
Proof. exact (EQ_MP (@lem3640976 A B g s f t h1 h2) (@lem3636486 A B t f g s h1)). Qed.
Lemma lem3640978 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term394 A B g s f t) : term458 A B t f g s.
Proof. exact (fun h0 : term459 A B t f g s => @lem3640977 A B g s f t h0 h1). Qed.
Lemma lem3640979 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term394 A B g s f t) : term434 A B t f g s.
Proof. exact (EQ_MP (@lem3636485 A B t f g s) (@lem3640978 A B g s f t h1)). Qed.
Lemma lem3640980 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : term435 A B t f g s.
Proof. exact (fun h0 : term394 A B g s f t => @lem3640979 A B g s f t h0). Qed.
Lemma lem3640985 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : term445 A B f g s.
Proof. exact (fun t : A -> Prop => @lem3640980 A B t f g s). Qed.
Lemma lem3640990 {A B : Type'} (g : B -> A) (s : B -> Prop) : term449 A B g s.
Proof. exact (fun f : A -> B => @lem3640985 A B f g s). Qed.
Lemma lem3640995 {A B : Type'} (s : B -> Prop) : term453 A B s.
Proof. exact (fun g : B -> A => @lem3640990 A B g s). Qed.
Lemma lem3641000 {A B : Type'} : term457 A B.
Proof. exact (fun s : B -> Prop => @lem3640995 A B s). Qed.
Lemma lem3641001 {A B : Type'} : term456 A B.
Proof. exact (EQ_MP (@lem3636480 A B) (@lem3641000 A B)). Qed.
Lemma lem3641002 {A B : Type'} (s : B -> Prop) : term1132 A B s.
Proof. exact (@lem3641001 A B s). Qed.
Lemma lem3641003 {A B : Type'} (s : B -> Prop) : (term1132 A B s) = (term452 A B s).
Proof. exact (eq_refl (term1132 A B s)). Qed.
Lemma lem3641004 {A B : Type'} (s : B -> Prop) : term452 A B s.
Proof. exact (EQ_MP (@lem3641003 A B s) (@lem3641002 A B s)). Qed.
Lemma lem3641005 {A B : Type'} (s : B -> Prop) (g : B -> A) : term1133 A B s g.
Proof. exact (@lem3641004 A B s g). Qed.
Lemma lem3641006 {A B : Type'} (g : B -> A) (s : B -> Prop) : (term1133 A B s g) = (term448 A B g s).
Proof. exact (eq_refl (term1133 A B s g)). Qed.
Lemma lem3641007 {A B : Type'} (g : B -> A) (s : B -> Prop) : term448 A B g s.
Proof. exact (EQ_MP (@lem3641006 A B g s) (@lem3641005 A B s g)). Qed.
Lemma lem3641008 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) : term1134 A B g s f.
Proof. exact (@lem3641007 A B g s f). Qed.
Lemma lem3641009 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : (term1134 A B g s f) = (term444 A B f g s).
Proof. exact (eq_refl (term1134 A B g s f)). Qed.
Lemma lem3641010 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) : term444 A B f g s.
Proof. exact (EQ_MP (@lem3641009 A B f g s) (@lem3641008 A B g s f)). Qed.
Lemma lem3641011 {A B : Type'} (f : A -> B) (g : B -> A) (s : B -> Prop) (t : A -> Prop) : term1135 A B f g s t.
Proof. exact (@lem3641010 A B f g s t). Qed.
Lemma lem3641012 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : (term1135 A B f g s t) = (term436 A B t f g s).
Proof. exact (eq_refl (term1135 A B f g s t)). Qed.
Lemma lem3641013 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : term436 A B t f g s.
Proof. exact (EQ_MP (@lem3641012 A B t f g s) (@lem3641011 A B f g s t)). Qed.
Lemma lem3641015 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : term436 A B t f g s.
Proof. exact (@lem3635908 A B t f g s (@lem3641013 A B t f g s)). Qed.
Lemma lem3641016 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term437 A B t f g s) : False.
Proof. exact (@lem3641015 A B t f g s (@lem3635892 A B t f g s h1)). Qed.
Lemma lem3641017 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term437 A B t f g s) : (term437 A B t f g s) = False.
Proof. exact (prop_ext (fun h2 : term437 A B t f g s => @lem3641016 A B t f g s h1) (fun h2 : False => @lem3635892 A B t f g s h1)). Qed.
Lemma lem3641018 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) (h1 : term437 A B t f g s) : False.
Proof. exact (EQ_MP (@lem3641017 A B t f g s h1) (@lem3635892 A B t f g s h1)). Qed.
Lemma lem3641019 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : term436 A B t f g s.
Proof. exact (fun h0 : term437 A B t f g s => @lem3641018 A B t f g s h0). Qed.
Lemma lem3641020 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : term435 A B t f g s.
Proof. exact (EQ_MP (@lem3635891 A B t f g s) (@lem3641019 A B t f g s)). Qed.
Lemma lem3641021 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : term369 A B t f g s.
Proof. exact (EQ_MP (@lem3635887 A B t f g s) (@lem3641020 A B t f g s)). Qed.
Lemma lem3641022 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : B -> A) (s : B -> Prop) : term368 A B t f g s.
Proof. exact (EQ_MP (@lem3635549 A B t f g s) (@lem3641021 A B t f g s)). Qed.
Lemma lem3641023 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term349 A B s t f g) (h2 : term234 A B s f t) : term366 A B t f g s.
Proof. exact (@lem3641022 A B t f g s (@lem3635452 A B g s f t h1 h2)). Qed.
Lemma lem3641024 {A B : Type'} (g : B -> A) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term349 A B s t f g) (h2 : term234 A B s f t) : term245 A B t s f.
Proof. exact (ex_intro (term244 A B t s f) (@IMAGE B A g s) (@lem3641023 A B g s f t h1 h2)). Qed.
Lemma lem3641025 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term4 A B s t f) (h2 : term234 A B s f t) : term245 A B t s f.
Proof. exact (ex_elim (@lem3635440 A B s t f h1) (fun g : B -> A => fun h0 : term1136 A B s t f g => @lem3641024 A B g s f t h0 h2)). Qed.
Lemma lem3641026 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term234 A B s f t) : term348 A B t s f.
Proof. exact (fun h0 : term4 A B s t f => @lem3641025 A B s f t h0 h1). Qed.
Lemma lem3641027 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term234 A B s f t) : term347 A B t s f.
Proof. exact (EQ_MP (@lem3635439 A B t s f) (@lem3641026 A B s f t h1)). Qed.
Lemma lem3641028 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term234 A B s f t) : term245 A B t s f.
Proof. exact (@lem3641027 A B s f t h1 (@lem3635384 A B s f t h1)). Qed.
Lemma lem3641029 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : term1137 A B t s f.
Proof. exact (fun h0 : term234 A B s f t => @lem3641028 A B s f t h0). Qed.
Lemma lem3641030 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : term1138 A B s f t.
Proof. exact (conj (@lem3641029 A B t s f) (@lem3635379 A B s f t)). Qed.
Lemma lem3641031 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term1138 A B s f t) = ((term234 A B s f t) = (term245 A B t s f)).
Proof. exact (@lem32 (term234 A B s f t) (term245 A B t s f)). Qed.
Lemma lem3641032 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term234 A B s f t) = (term245 A B t s f).
Proof. exact (EQ_MP (@lem3641031 A B t s f) (@lem3641030 A B s f t)). Qed.
Lemma lem3641037 {A B : Type'} (s : B -> Prop) (f : A -> B) : term1139 A B s f.
Proof. exact (fun t : A -> Prop => @lem3641032 A B t s f). Qed.
Lemma lem3641042 {A B : Type'} (f : A -> B) : term1140 A B f.
Proof. exact (fun s : B -> Prop => @lem3641037 A B s f). Qed.
Lemma lem3641047 {A B : Type'} : term1141 A B.
Proof. exact (fun f : A -> B => @lem3641042 A B f). Qed.
